#!/usr/bin/env python3
"""Drives build/kernel over the frame protocol (docs/spec/milestone-1.md).

Starts `build/kernel 7000`, connects, sends Config (the capture's network and
subscriber), NgapAssocUp and the captured NG Setup Request, and checks that the
reply to the last holds one NgapSend carrying the captured NG Setup Response.
Prints PASS or FAIL and always kills the kernel. Run with python3 -I from the
repository root.
"""
import json
import os
import socket
import struct
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
KERNEL = ROOT / "build/kernel"
PORT = 7000
ENTROPY = bytes(range(32))

CONFIG = [
    (0x0001, bytes.fromhex("00f110")), (0x0002, b"\x02"), (0x0003, b"\x00\x01"), (0x0004, b"\x00"),
    (0x0005, bytes.fromhex("000001")), (0x0006, b"speck-amf0"), (0x0007, b"\x01"), (0x0008, b"internet"),
    (0x0009, bytes([10, 45, 0, 0])), (0x000A, b"\x10"), (0x000B, bytes([8, 8, 8, 8])),
    (0x000C, bytes([10, 33, 0, 12])), (0x000D, bytes([10, 33, 0, 20])), (0x000E, bytes([10, 33, 0, 20])),
    (0x000F, bytes.fromhex("582f931fcf8f2b7f911debb6224f71e72b9d4a62eed38d129ffd778c3016d36a")),
    (0x0010, b"\x01"), (0x0011, b"\x00"), (0x0012, b"\x02"),
]
SUBSCRIBER = (0x0020, bytes([15]) + b"001010000000001" + bytes.fromhex("465b5ce8b199b49faa5f0a2ee238a6bc")
              + bytes.fromhex("e8ed289deba952e4283b54e88e6183ca") + bytes.fromhex("8000") + bytes.fromhex("000000000040"))


def tlvs(items):
    return b"".join(struct.pack(">HH", tag, len(value)) + value for tag, value in items)


def frame(body):
    return struct.pack(">I", len(body)) + body


def event(kind, payload):
    return frame(bytes([kind]) + ENTROPY + payload)


def config_event():
    body = tlvs(CONFIG + [SUBSCRIBER])
    return event(0x01, struct.pack(">I", len(body)) + body)


def ngap_data(assoc, stream, pdu):
    return event(0x04, struct.pack(">IHI", assoc, stream, len(pdu)) + pdu)


def read_frame(sock):
    header = recv_exactly(sock, 4)
    (length,) = struct.unpack(">I", header)
    return recv_exactly(sock, length)


def recv_exactly(sock, n):
    data = b""
    while len(data) < n:
        chunk = sock.recv(n - len(data))
        if not chunk:
            raise EOFError("kernel closed the connection")
        data += chunk
    return data


def actions(body):
    """The actions of an Actions frame as (kind, payload bytes) pairs."""
    assert body[0] == 0x80, f"not an Actions frame: {body[:1].hex()}"
    (count,) = struct.unpack(">H", body[1:3])
    out, pos = [], 3
    for _ in range(count):
        kind = body[pos]
        pos += 1
        if kind == 0x81:
            assoc, stream, length = struct.unpack(">IHI", body[pos:pos + 10])
            out.append((kind, (assoc, stream, body[pos + 10:pos + 10 + length])))
            pos += 10 + length
        elif kind == 0x82:
            out.append((kind, struct.unpack(">I", body[pos:pos + 4])[0]))
            pos += 4
        elif kind == 0x83:
            (length,) = struct.unpack(">I", body[pos:pos + 4])
            out.append((kind, body[pos + 4:pos + 4 + length]))
            pos += 4 + length
        elif kind == 0x84:
            out.append((kind, struct.unpack(">II", body[pos:pos + 8])))
            pos += 8
        elif kind == 0x85:
            out.append((kind, struct.unpack(">I", body[pos:pos + 4])[0]))
            pos += 4
        elif kind == 0x86:
            level, length = struct.unpack(">BI", body[pos:pos + 5])
            out.append((kind, (level, body[pos + 5:pos + 5 + length].decode())))
            pos += 5 + length
        else:
            raise ValueError(f"unknown action kind {kind:#x}")
    assert pos == len(body), "trailing bytes in the Actions frame"
    return out


def connect():
    deadline = time.time() + 10
    while True:
        try:
            return socket.create_connection(("127.0.0.1", PORT), timeout=5)
        except OSError:
            if time.time() > deadline:
                raise
            time.sleep(0.1)


def main():
    messages = {m["index"]: m for m in json.loads((ROOT / "test-vectors/capture/vectors.json").read_text())["messages"]}
    request = bytes.fromhex(messages[8]["hex"])
    response = bytes.fromhex(messages[9]["hex"])
    kernel = subprocess.Popen([str(KERNEL), str(PORT)], stderr=subprocess.PIPE)
    try:
        sock = connect()
        sock.sendall(config_event())
        first = actions(read_frame(sock))
        sock.sendall(event(0x02, struct.pack(">I", 1)))
        actions(read_frame(sock))
        sock.sendall(ngap_data(1, 0, request))
        reply = actions(read_frame(sock))
        sock.close()
    finally:
        kernel.kill()
        stderr = kernel.communicate(timeout=5)[1].decode(errors="replace")
    sends = [payload for kind, payload in reply if kind == 0x81]
    ok_config = any(kind == 0x83 for kind, _ in first)
    ok = ok_config and len(sends) == 1 and sends[0] == (1, 0, response)
    print("kernel stderr:", stderr.strip().replace("\n", " | ") or "(none)")
    print("PASS frame-client: Config answered with a PFCP send; NG Setup Request answered with the captured NG Setup Response" if ok
          else f"FAIL frame-client: config pfcp={ok_config} sends={len(sends)} match={bool(sends) and sends[0] == (1, 0, response)}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
