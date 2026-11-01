#!/usr/bin/env python3
"""Probe eUPF v0.7.2 behaviours the spec kernel depends on.

Runs inside a netshoot container that shares the Open5GS SMF's network
namespace (source IP 10.33.0.12, the associated PFCP peer). Usage:

    pfcp_probe.py <capture.pcap>   (JSON report on stdout)

Probes, in order (the last one may crash eUPF):
  1. retransmit: resend the captured Session Establishment Request verbatim
     (same sequence number, same CP F-SEID) and count eUPF sessions.
  2. no_ohr: establish a hand-built session whose uplink PDR has no Outer
     Header Removal IE, then send one uplink G-PDU and let the caller check
     whether the decapsulated packet reached the data network.
  3. issue_637: Session Modification on that session adding Create PDR
     (Source Interface Core, UE IPv4, SDF filter) + Create FAR (Access, FORW,
     Outer Header Creation GTP-U/UDP/IPv4), as in edgecomllc/eupf#637.
  4. ohc_zero_addr_establishment: Session Establishment carrying an extra
     Create FAR whose Outer Header Creation IPv4 is 0.0.0.0 (#637's other trigger).
"""
import json
import socket
import struct
import sys
import time
import urllib.request

from scapy.all import IP, UDP, ICMP, rdpcap  # netshoot ships scapy

UPF = "10.33.0.20"
SMF = "10.33.0.12"
DN = "10.33.0.40"
GNB = "10.33.0.30"
API = f"http://{UPF}:8080/api/v1"


def ie(t, v):
    return struct.pack("!HH", t, len(v)) + v


def hdr(msg_type, seid, seq, body):
    # version 1, S=1; length counts everything after the first 4 octets
    return struct.pack("!BBHQ", 0x21, msg_type, len(body) + 12, seid) + seq.to_bytes(3, "big") + b"\x00" + body


def parse_ies(b):
    out = []
    while len(b) >= 4:
        t, l = struct.unpack("!HH", b[:4])
        out.append((t, b[4:4 + l]))
        b = b[4 + l:]
    return out


def parse_msg(b):
    flags, mtype, length = struct.unpack("!BBH", b[:4])
    if flags & 1:
        seid = struct.unpack("!Q", b[4:12])[0]
        seq = int.from_bytes(b[12:15], "big")
        ies = b[16:4 + length]
    else:
        seid = None
        seq = int.from_bytes(b[4:7], "big")
        ies = b[8:4 + length]
    return {"type": mtype, "seid": seid, "seq": seq, "ies": parse_ies(ies)}


def summarize(m):
    d = {"type": m["type"], "seid": m["seid"], "seq": m["seq"]}
    for t, v in m["ies"]:
        if t == 19:
            d["cause"] = v[0]
        if t == 57:
            d["up_fseid"] = {"flags": v[0], "seid": hex(struct.unpack("!Q", v[1:9])[0]),
                             "ipv4": socket.inet_ntoa(v[9:13]) if v[0] & 2 else None}
        if t == 76:
            d["offending_ie"] = struct.unpack("!H", v[:2])[0]
    return d


def sessions():
    try:
        with urllib.request.urlopen(f"{API}/pfcp_sessions", timeout=3) as r:
            data = json.load(r)
        return len(data) if isinstance(data, list) else data
    except Exception as e:  # eUPF dead or API shape differs
        return f"error: {e}"


def xchg(sock, msg, wait=3.0):
    sock.sendto(msg, (UPF, 8805))
    sock.settimeout(wait)
    try:
        data, _ = sock.recvfrom(65535)
        return data
    except socket.timeout:
        return None


def main():
    pcap = sys.argv[1]
    report = {}
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind((SMF, 0))  # SMF itself holds :8805; eUPF replies to the source port

    est_req = None
    for p in rdpcap(pcap):
        if UDP in p and p[UDP].dport == 8805 and p[IP].src == SMF:
            raw = bytes(p[UDP].payload)
            if raw[1] == 50:
                est_req = raw
                break
    assert est_req, "no Session Establishment Request in capture"

    # 1. verbatim retransmission
    before = sessions()
    resp = xchg(sock, est_req)
    time.sleep(1)
    after = sessions()
    report["retransmit"] = {
        "request_hex": est_req.hex(),
        "sessions_before": before, "sessions_after": after,
        "response": summarize(parse_msg(resp)) if resp else None,
        "response_hex": resp.hex() if resp else None,
    }

    # 2. hand-built session, uplink PDR without Outer Header Removal
    teid = 0x0000ABCD
    ue_ip = "10.45.0.99"
    cp_seid = 0x5EED000000000001
    pdi_ul = ie(2, ie(20, b"\x00") +                                   # Source Interface Access
                ie(21, b"\x01" + struct.pack("!I", teid) + socket.inet_aton(UPF)) +  # F-TEID V4
                ie(22, b"\x08internet") +
                ie(93, b"\x02" + socket.inet_aton(ue_ip)))             # UE IP (V4, source)
    pdr_ul = ie(1, ie(56, struct.pack("!H", 1)) + ie(29, struct.pack("!I", 255)) + pdi_ul +
                ie(108, struct.pack("!I", 1)) + ie(109, struct.pack("!I", 1)))   # no IE 95
    pdi_dl = ie(2, ie(20, b"\x01") + ie(22, b"\x08internet") +
                ie(93, b"\x06" + socket.inet_aton(ue_ip)))             # UE IP (V4, S/D=1)
    pdr_dl = ie(1, ie(56, struct.pack("!H", 2)) + ie(29, struct.pack("!I", 255)) + pdi_dl +
                ie(108, struct.pack("!I", 2)) + ie(109, struct.pack("!I", 1)))
    far_ul = ie(3, ie(108, struct.pack("!I", 1)) + ie(44, b"\x02") +
                ie(4, ie(42, b"\x01") + ie(22, b"\x08internet")))      # FORW to Core
    far_dl = ie(3, ie(108, struct.pack("!I", 2)) + ie(44, b"\x04"))   # BUFF
    qer = ie(7, ie(109, struct.pack("!I", 1)) + ie(25, b"\x00") +
             ie(26, b"\x00\x00\x00\x03\xe8\x00\x00\x00\x03\xe8") + ie(124, b"\x09"))
    body = (ie(60, b"\x00" + socket.inet_aton(SMF)) +
            ie(57, b"\x02" + struct.pack("!Q", cp_seid) + socket.inet_aton(SMF)) +
            pdr_ul + pdr_dl + far_ul + far_dl + qer + ie(113, b"\x01"))  # PDN Type IPv4
    msg = hdr(50, 0, 0x7F0001, body)
    before = sessions()
    resp = xchg(sock, msg)
    after = sessions()
    r = summarize(parse_msg(resp)) if resp else None
    report["no_ohr"] = {"request_hex": msg.hex(), "response_hex": resp.hex() if resp else None,
                        "response": r, "sessions_before": before, "sessions_after": after,
                        "gpdu": {"teid": hex(teid), "inner": f"ICMP echo {ue_ip} -> {DN} id 0x5eed"}}
    up_seid = int(r["up_fseid"]["seid"], 16) if r and "up_fseid" in r else None

    # one uplink G-PDU (GTPv1-U, T-PDU) to eUPF N3; inner ICMP echo to the DN
    inner = bytes(IP(src=ue_ip, dst=DN) / ICMP(id=0x5EED, seq=1) / (b"no-ohr-probe" * 2))
    gtpu = struct.pack("!BBHI", 0x30, 0xFF, len(inner), teid) + inner
    u = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    u.bind((SMF, 0))
    for _ in range(3):
        u.sendto(gtpu, (UPF, 2152))
        time.sleep(0.3)
    time.sleep(1)

    # 3. edgecomllc/eupf#637: Session Modification with Create PDR + Create FAR + OHC
    if up_seid is not None:
        sdf = b"permit out ip from any to assigned"
        pdi = ie(2, ie(20, b"\x01") + ie(22, b"\x08internet") +
                 ie(93, b"\x06" + socket.inet_aton(ue_ip)) +
                 ie(23, b"\x01\x00" + struct.pack("!H", len(sdf)) + sdf))
        cpdr = ie(1, ie(56, struct.pack("!H", 3)) + ie(29, struct.pack("!I", 100)) + pdi +
                  ie(108, struct.pack("!I", 3)) + ie(109, struct.pack("!I", 1)))
        ohc = ie(84, b"\x01\x00" + struct.pack("!I", 0x00000777) + socket.inet_aton(GNB))
        cfar = ie(3, ie(108, struct.pack("!I", 3)) + ie(44, b"\x02") +
                  ie(4, ie(42, b"\x00") + ie(22, b"\x08internet") + ohc))
        msg = hdr(52, up_seid, 0x7F0002, cpdr + cfar)
        resp = xchg(sock, msg, wait=4.0)
        time.sleep(2)
        report["issue_637"] = {"request_hex": msg.hex(), "response_hex": resp.hex() if resp else None,
                               "response": summarize(parse_msg(resp)) if resp else None,
                               "sessions_after": sessions()}

    # 4. #637's second trigger: Session Establishment with an extra Create FAR whose
    #    Outer Header Creation IPv4 is 0.0.0.0 (same PDRs/FARs as probe 2 otherwise).
    ue_ip4, teid4 = "10.45.0.98", 0x0000ABCE
    body4 = body.replace(struct.pack("!Q", cp_seid), struct.pack("!Q", cp_seid + 1))
    body4 = body4.replace(struct.pack("!I", teid), struct.pack("!I", teid4))
    body4 = body4.replace(socket.inet_aton(ue_ip), socket.inet_aton(ue_ip4))
    ohc0 = ie(84, b"\x01\x00" + struct.pack("!I", 0x00000778) + socket.inet_aton("0.0.0.0"))
    body4 += ie(3, ie(108, struct.pack("!I", 9)) + ie(44, b"\x02") +
                ie(4, ie(42, b"\x00") + ie(22, b"\x08internet") + ohc0))
    msg = hdr(50, 0, 0x7F0003, body4)
    resp = xchg(sock, msg, wait=4.0)
    time.sleep(2)
    report["ohc_zero_addr_establishment"] = {
        "request_hex": msg.hex(), "response_hex": resp.hex() if resp else None,
        "response": summarize(parse_msg(resp)) if resp else None, "sessions_after": sessions()}
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
