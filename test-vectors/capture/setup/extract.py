#!/usr/bin/env python3
"""Turn the capture into vectors.json.

    extract.py <registration-pdu.pcapng> <setup-dir> <vectors.json>

Needs `tshark` (Wireshark 4.6) on PATH and the Python `cryptography` package.

Bytes come from this script's own parsing of pcapng, Ethernet, IPv4, SCTP DATA
chunks and UDP, plus the top level of NGAP APER, the NAS security header and PFCP
TLVs. tshark only supplies human-readable names (NGAP message and IE names, NAS IE
labels, PFCP IE names) and the location of NAS-PDUs nested deep inside NGAP. The
script checks every tshark-located NAS-PDU against the NGAP bytes it parsed itself.

The crypto chain (Milenage, RES*, KAUSF..KAMF, K_NASint, K_gNB, NIA2 MACs, SUCI
Profile A) is recomputed here from K/OPc/the home-network key and checked against
the captured bytes: AUTN's MAC-A, the UE's RES*, every NAS MAC, the K_gNB in
InitialContextSetupRequest and the SUCI MAC tag. A mismatch aborts the script.
"""
import hashlib
import hmac
import json
import re
import struct
import subprocess
import sys
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PublicKey
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.cmac import CMAC

GNB, AMF_IP, SMF, UPF = "10.33.0.30", "10.33.0.11", "10.33.0.12", "10.33.0.20"
PLMN = ("001", "01")
SNN = "5G:mnc001.mcc001.3gppnetwork.org"

MM_TYPES = {
    0x41: "Registration request", 0x42: "Registration accept", 0x43: "Registration complete",
    0x44: "Registration reject", 0x45: "Deregistration request (UE originating)",
    0x46: "Deregistration accept (UE originating)", 0x4c: "Service request",
    0x54: "Configuration update command", 0x55: "Configuration update complete",
    0x56: "Authentication request", 0x57: "Authentication response",
    0x58: "Authentication reject", 0x59: "Authentication failure", 0x5a: "Authentication result",
    0x5b: "Identity request", 0x5c: "Identity response", 0x5d: "Security mode command",
    0x5e: "Security mode complete", 0x5f: "Security mode reject", 0x64: "5GMM status",
    0x67: "UL NAS transport", 0x68: "DL NAS transport",
}
SM_TYPES = {
    0xc1: "PDU session establishment request", 0xc2: "PDU session establishment accept",
    0xc3: "PDU session establishment reject", 0xc9: "PDU session modification request",
    0xcb: "PDU session modification command", 0xd1: "PDU session release request",
    0xd3: "PDU session release command", 0xd6: "5GSM status",
}
PFCP_TYPES = {
    1: "Heartbeat Request", 2: "Heartbeat Response", 5: "Association Setup Request",
    6: "Association Setup Response", 50: "Session Establishment Request",
    51: "Session Establishment Response", 52: "Session Modification Request",
    53: "Session Modification Response", 54: "Session Deletion Request",
    55: "Session Deletion Response", 56: "Session Report Request", 57: "Session Report Response",
}
SHT = {0: "plain", 1: "integrity protected", 2: "integrity protected and ciphered",
       3: "integrity protected with new 5G NAS security context",
       4: "integrity protected and ciphered with new 5G NAS security context"}


def fail(msg):
    sys.exit(f"extract.py: CHECK FAILED: {msg}")


# ---------------------------------------------------------------- framing

def read_pcapng(path):
    data = Path(path).read_bytes()
    off, frames, ts_res = 0, [], 1e-6
    while off < len(data):
        btype, blen = struct.unpack_from("<II", data, off)
        body = data[off + 8: off + blen - 4]
        if btype == 1:
            linktype = struct.unpack_from("<H", body, 0)[0]
            if linktype != 1:
                fail(f"unexpected linktype {linktype}")
        elif btype == 6:
            _, hi, lo, caplen, _ = struct.unpack_from("<IIIII", body, 0)
            frames.append((((hi << 32) | lo) * ts_res, body[20:20 + caplen]))
        off += blen
    return frames


def ip4(b):
    return ".".join(str(x) for x in b)


def parse_frame(raw):
    """Yield (proto, src, dst, payload, extra) for every SCTP DATA chunk / UDP payload."""
    if struct.unpack_from("!H", raw, 12)[0] != 0x0800:
        return
    ip = raw[14:]
    ihl = (ip[0] & 0x0f) * 4
    total = struct.unpack_from("!H", ip, 2)[0]
    proto, src, dst = ip[9], ip4(ip[12:16]), ip4(ip[16:20])
    l4 = ip[ihl:total]
    if proto == 132:
        off = 12
        while off + 4 <= len(l4):
            ctype, cflags, clen = struct.unpack_from("!BBH", l4, off)
            if ctype == 0:
                tsn, sid, ssn, ppid = struct.unpack_from("!IHHI", l4, off + 4)
                if cflags & 3 != 3:
                    fail("fragmented SCTP DATA chunk")
                yield ("sctp", src, dst, l4[off + 16: off + clen],
                       {"sctp_stream": sid, "sctp_ppid": ppid, "sctp_tsn": tsn})
            off += (clen + 3) & ~3
    elif proto == 17:
        sport, dport = struct.unpack_from("!HH", l4, 0)
        yield ("udp", src, dst, l4[8:], {"sport": sport, "dport": dport})


# ---------------------------------------------------------------- NGAP (APER, top level only)

def aper_len(b, off):
    if b[off] < 0x80:
        return b[off], off + 1
    if b[off] & 0xc0 == 0x80:
        return ((b[off] & 0x3f) << 8) | b[off + 1], off + 2
    fail("fragmented APER length")


def parse_ngap(b):
    pdu = ["initiatingMessage", "successfulOutcome", "unsuccessfulOutcome"][(b[0] >> 5) & 3]
    proc = b[1]
    crit = ["reject", "ignore", "notify"][b[2] >> 6]
    vlen, off = aper_len(b, 3)
    if off + vlen != len(b):
        fail("NGAP open type length mismatch")
    off += 1
    count = struct.unpack_from("!H", b, off)[0]
    off += 2
    ies = []
    for _ in range(count):
        iid = struct.unpack_from("!H", b, off)[0]
        icrit = ["reject", "ignore", "notify"][b[off + 2] >> 6]
        ilen, off = aper_len(b, off + 3)
        ies.append({"id": iid, "criticality": icrit, "value": b[off: off + ilen]})
        off += ilen
    if off != len(b):
        fail("trailing bytes after NGAP IEs")
    return pdu, proc, crit, ies


# ---------------------------------------------------------------- tshark helpers

def tshark_json(pcap):
    out = subprocess.run(["tshark", "-r", pcap, "-o", "nas-5gs.null_decipher:TRUE",
                          "-T", "json", "-x", "--no-duplicate-keys"],
                         check=True, capture_output=True, text=True).stdout
    return [p["_source"]["layers"] for p in json.loads(out)]


def as_list(v):
    return v if isinstance(v, list) else [v]


def walk(o, fn):
    if isinstance(o, dict):
        fn(o)
        for v in o.values():
            walk(v, fn)
    elif isinstance(o, list):
        for x in o:
            walk(x, fn)


def ngap_names(tree):
    """Message name and IE names (in order) from one tshark ngap layer."""
    root = tree["ngap.NGAP_PDU_tree"]
    msg = next(iter(v for k, v in root.items() if k.endswith("_element")))
    val = next(v for k, v in msg.items() if k.endswith("value_element"))
    name_key = next(k for k in val if k.endswith("_element"))
    name = name_key[len("ngap."):-len("_element")]
    items = val[name_key]["ngap.protocolIEs_tree"]
    ie_names = [k.split(": ", 1)[1].strip() for k in items]
    nas = []

    def grab(d):
        for k, v in d.items():
            if k.endswith("NAS_PDU_raw"):
                tk = k[:-4] + "_tree"
                for raw, t in zip(as_list(v) if isinstance(v[0], list) else [v],
                                  as_list(d.get(tk, {}))):
                    nas.append((bytes.fromhex(raw[0]), t.get("nas-5gs", {})))
    walk(items, grab)
    return name, ie_names, nas


def nas_labels(plain):
    """Top-level IE labels (with IEI when tshark shows one) of a 'Plain NAS 5GS Message' tree."""
    out = []
    if not isinstance(plain, dict):
        return out
    for k, v in plain.items():
        if k.startswith(("nas-5gs.", "gsm_a.")) or k.endswith("_raw"):
            continue
        for item in as_list(v):
            iei = None
            if isinstance(item, dict):
                iei = item.get("nas-5gs.mm.elem_id") or item.get("nas-5gs.sm.elem_id")
                if iei is None:
                    for kk, vv in item.items():
                        if kk.endswith("elem_id") and isinstance(vv, str):
                            iei = vv
            out.append({"name": k.strip(), **({"iei": iei} if iei else {})})
    return out


def pfcp_name_map(layers):
    names, grouped = {}, set()

    def grab(d):
        for k, v in d.items():
            for item in as_list(v):
                if isinstance(item, dict) and "pfcp.ie_type" in item:
                    t = int(as_list(item["pfcp.ie_type"])[0])
                    names.setdefault(t, k.split(" : ")[0].strip())
                    if "[Grouped IE]" in k:
                        grouped.add(t)
    for l in layers:
        if "pfcp" in l:
            walk(l["pfcp"], grab)
    return names, grouped


# ---------------------------------------------------------------- PFCP

def parse_pfcp_ies(b, names, grouped):
    out = []
    while len(b) >= 4:
        t, l = struct.unpack_from("!HH", b, 0)
        v = b[4:4 + l]
        ie = {"type": t, "name": names.get(t, f"IE {t}"), "len": l}
        if t in grouped:
            ie["children"] = parse_pfcp_ies(v, names, grouped)
        out.append(ie)
        b = b[4 + l:]
    if b:
        fail("trailing PFCP bytes")
    return out


def parse_pfcp(b, names, grouped):
    flags, mtype, length = struct.unpack_from("!BBH", b, 0)
    if length + 4 != len(b):
        fail("PFCP length mismatch")
    h = {"version": flags >> 5, "s": flags & 1, "message_type": mtype}
    if flags & 1:
        h["seid"] = "%016x" % struct.unpack_from("!Q", b, 4)[0]
        h["sequence"] = int.from_bytes(b[12:15], "big")
        body = b[16:]
    else:
        h["sequence"] = int.from_bytes(b[4:7], "big")
        body = b[8:]
    return h, parse_pfcp_ies(body, names, grouped)


def parse_gtpu(p):
    flags, gtype, glen, teid = struct.unpack_from("!BBHI", p, 0)
    off, ext = 8, {}
    if flags & 0x07:
        off, nxt = 12, p[11]
        while nxt:
            l = p[off] * 4
            nxt = p[off + l - 1]
            off += l
        ext = {"extension_headers_hex": p[12:off].hex()}
    inner = p[off:]
    return {"message": "G-PDU" if gtype == 0xff else str(gtype), "flags": flags, "teid": "%08x" % teid,
            "length": glen, **ext,
            "inner": {"src": ip4(inner[12:16]), "dst": ip4(inner[16:20]), "ip_proto": inner[9]}}


# ---------------------------------------------------------------- crypto

def aes(k, x):
    e = Cipher(algorithms.AES(k), modes.ECB()).encryptor()
    return e.update(x) + e.finalize()


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


def rot(x, r):
    n = int.from_bytes(x, "big")
    r %= 128
    return (((n << r) | (n >> (128 - r))) & ((1 << 128) - 1)).to_bytes(16, "big")


def milenage(k, opc, rand, sqn, amf):
    temp = aes(k, xor(rand, opc))
    in1 = sqn + amf + sqn + amf
    out1 = xor(aes(k, xor(temp, rot(xor(in1, opc), 64))), opc)
    c = lambda i: (i).to_bytes(16, "big")
    out = lambda r, ci: xor(aes(k, xor(rot(xor(temp, opc), r), c(ci))), opc)
    o2, o3, o4, o5 = out(0, 1), out(32, 2), out(64, 4), out(96, 8)
    return {"mac_a": out1[:8], "mac_s": out1[8:], "res": o2[8:], "ak": o2[:6],
            "ck": o3, "ik": o4, "ak_star": o5[:6]}


def kdf(key, fc, *params):
    s = bytes([fc])
    for p in params:
        s += p + len(p).to_bytes(2, "big")
    return hmac.new(key, s, hashlib.sha256).digest()


def nia2(key, count, bearer, direction, msg):
    c = CMAC(algorithms.AES(key))
    c.update(count.to_bytes(4, "big") + bytes([(bearer << 3) | (direction << 2), 0, 0, 0]) + msg)
    return c.finalize()[:4]


def x963_kdf(z, shared_info, n):
    out, i = b"", 1
    while len(out) < n:
        out += hashlib.sha256(z + i.to_bytes(4, "big") + shared_info).digest()
        i += 1
    return out[:n]


def aes_ctr(k, icb, x):
    d = Cipher(algorithms.AES(k), modes.CTR(icb)).decryptor()
    return d.update(x) + d.finalize()


def bcd(b):
    s = ""
    for x in b:
        for n in (x & 0x0f, x >> 4):
            if n != 0x0f:
                s += str(n)
    return s


TLV_E = (0x70, 0x71, 0x74, 0x77, 0x78, 0x7a, 0x7b, 0x7c, 0x7d)


def tlv_e_ies(b, off, tv_len=None):
    """Optional NAS IEs from off as {iei: value}: fixed-length TV IEs given in
    tv_len, TLV-E IEIs in TLV_E, everything else TLV. Enough for the messages
    this script reads (Authentication request/response, Security mode complete)."""
    tv_len = tv_len or {}
    out = {}
    while off < len(b):
        iei = b[off]
        if iei in tv_len:
            out[iei] = b[off + 1: off + 1 + tv_len[iei]]
            off += 1 + tv_len[iei]
        elif iei in TLV_E:
            l = struct.unpack_from("!H", b, off + 1)[0]
            out[iei] = b[off + 3: off + 3 + l]
            off += 3 + l
        else:
            l = b[off + 1]
            out[iei] = b[off + 2: off + 2 + l]
            off += 2 + l
    return out


# ---------------------------------------------------------------- main

def main():
    pcap, setup, out_path = sys.argv[1], Path(sys.argv[2]), sys.argv[3]
    ue_cfg = (setup / "ueransim" / "ue.yaml").read_text()
    cfg = lambda key: re.search(rf"^{key}:\s*'?([0-9A-Za-z-]+)'?", ue_cfg, re.M).group(1)
    K, OPC, AMF_FIELD = bytes.fromhex(cfg("key")), bytes.fromhex(cfg("op")), bytes.fromhex(cfg("amf"))
    SUPI = cfg("supi")
    hn_pem = (setup / "hnet" / "curve25519-1.key").read_bytes()
    hn_priv = serialization.load_pem_private_key(hn_pem, None)
    hn_priv_raw = hn_priv.private_bytes(serialization.Encoding.Raw, serialization.PrivateFormat.Raw,
                                        serialization.NoEncryption())
    hn_pub_raw = hn_priv.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
    if hn_pub_raw.hex() != cfg("homeNetworkPublicKey").lower():
        fail("UE homeNetworkPublicKey does not match the UDM private key")

    frames = read_pcapng(pcap)
    layers = tshark_json(pcap)
    if len(frames) != len(layers):
        fail("frame count differs from tshark")
    pf_names, pf_grouped = pfcp_name_map(layers)
    t0 = frames[0][0]

    msgs = []

    def add(entry):
        entry = {"index": len(msgs), **entry}
        msgs.append(entry)
        return entry

    for fno, ((ts, raw), lay) in enumerate(zip(frames, layers), start=1):
        ngap_trees = as_list(lay.get("ngap", []))
        ngap_i = 0
        for proto, src, dst, payload, extra in parse_frame(raw):
            base = {"frame": fno, "time": round(ts - t0, 6), "src": src, "dst": dst}
            if proto == "sctp" and extra["sctp_ppid"] == 60:
                pdu, proc, crit, ies = parse_ngap(payload)
                name, ie_names, nas_pdus = ngap_names(ngap_trees[ngap_i])
                ngap_i += 1
                if len(ie_names) != len(ies):
                    fail(f"frame {fno}: IE count {len(ies)} vs tshark {len(ie_names)}")
                e = add({**base, "protocol": "NGAP",
                         "direction": "gNB->AMF" if src == GNB else "AMF->gNB",
                         "message": name, "pdu": pdu, "procedure_code": proc, "criticality": crit,
                         "sctp_stream": extra["sctp_stream"], "hex": payload.hex(),
                         "ies": [{"id": ie["id"], "name": n, "criticality": ie["criticality"]}
                                 for ie, n in zip(ies, ie_names)]})
                e["_ies"] = ies
                for nb, ntree in nas_pdus:
                    if nb not in payload:
                        fail(f"frame {fno}: tshark NAS-PDU not inside NGAP bytes")
                    handle_nas(add, e, nb, ntree, base)
            elif proto == "udp" and 8805 in (extra["sport"], extra["dport"]):
                h, ies = parse_pfcp(payload, pf_names, pf_grouped)
                add({**base, "protocol": "PFCP",
                         "direction": "SMF->UPF" if src == SMF else "UPF->SMF",
                         "message": PFCP_TYPES.get(h["message_type"], str(h["message_type"])),
                         **h, "hex": payload.hex(), "ies": ies})
            elif proto == "udp" and 2152 in (extra["sport"], extra["dport"]):
                add({**base, "protocol": "GTP-U",
                     "direction": "gNB->UPF" if src == GNB else "UPF->gNB", **parse_gtpu(payload),
                     "hex": payload.hex()})
        if ngap_i != len(ngap_trees):
            fail(f"frame {fno}: tshark NGAP count mismatch")

    secrets, checks = crypto(msgs, K, OPC, AMF_FIELD, SUPI, hn_priv, hn_priv_raw, hn_pub_raw)
    for e in msgs:
        e.pop("_ies", None)
    out = {
        "description": "UERANSIM 3.3.0 UE registration + IPv4 PDU session against Open5GS 2.8.0 "
                       "(AMF/SMF) and eUPF v0.7.2, captured on the Docker bridge. NAS ciphering NEA0, "
                       "integrity NIA2, SUCI Profile A. See NOTES.md and INVENTORY.md.",
        "pcapng": Path(pcap).name,
        "pcapng_sha256": hashlib.sha256(Path(pcap).read_bytes()).hexdigest(),
        "network": {"plmn": {"mcc": PLMN[0], "mnc": PLMN[1]}, "tac": 1,
                    "amf": {"region_id": 2, "set_id": 1, "pointer": 0, "name": "speck-amf0", "ngap_ip": AMF_IP},
                    "gnb": {"ip": GNB, "gnb_id": "0x000001", "gnb_id_bits": 32, "nci": "0x000000010"},
                    "smf_n4_ip": SMF, "upf_n4_ip": UPF, "upf_n3_ip": UPF, "data_network_ip": "10.33.0.40",
                    "dnn": "internet", "s_nssai": {"sst": 1}, "ue_pool": "10.45.0.0/16"},
        "conventions": {
            "direction": "sender->receiver at the interface (gNB, AMF, SMF, UPF); NAS direction is "
                         "'UL' (UE->network) or 'DL'.",
            "hex": "lowercase, no separators; NGAP 'hex' is the whole NGAP-PDU (one SCTP DATA chunk, PPID 60); "
                   "PFCP and GTP-U 'hex' is the UDP payload.",
            "nas": "Every NAS message gets its own entry after the NGAP message that carries it ('carried_in'). "
                   "Protected messages give 'outer_hex' (whole security-protected message) and "
                   "'plaintext_hex' (the inner plain 5GMM message). 5GSM messages and the Registration request "
                   "inside the NAS message container are separate entries with 'carried_in' pointing at "
                   "their 5GMM container.",
            "ies": "NGAP: top-level ProtocolIE ids in wire order. NAS: top-level IE labels as Wireshark 4.6 names "
                   "them, with the IEI for optional IEs. PFCP: every IE with its type, nested for grouped IEs.",
        },
        "messages": msgs,
        "secrets": secrets,
        "checks": checks,
    }
    Path(out_path).write_text(json.dumps(out, indent=1) + "\n")
    print(f"{len(msgs)} messages; checks: " + ", ".join(f"{k}={v}" for k, v in checks.items()))


def handle_nas(add, ngap_e, nb, ntree, base, parent=None):
    """Add one entry per NAS message (5GMM, nested 5GSM / Registration request)."""
    ul = ngap_e["direction"] == "gNB->AMF"
    trees = ntree if isinstance(ntree, dict) else {}
    plain_tree = trees.get("Plain NAS 5GS Message")
    sht = nb[1] & 0x0f
    e = {**base, "protocol": "NAS-5GMM", "direction": "UL" if ul else "DL",
         "carried_in": ngap_e["index"], "security_header_type": sht,
         "security_header": SHT.get(sht, str(sht))}
    if sht:
        plain = nb[7:]
        e.update({"outer_hex": nb.hex(), "mac": nb[2:6].hex(), "nas_sequence_number": nb[6],
                  "plaintext_hex": plain.hex()})
    else:
        plain = nb
        e["plaintext_hex"] = plain.hex()
    e["message_type"] = plain[2]
    e["message"] = MM_TYPES.get(plain[2], hex(plain[2]))
    e["ies"] = nas_labels(plain_tree)
    e = add(e)
    t = plain[2]
    if t in (0x67, 0x68):
        ptype = plain[3] & 0x0f
        plen = struct.unpack_from("!H", plain, 4)[0]
        payload = plain[6:6 + plen]
        e["payload_container_type"] = ptype
        if ptype == 1:
            sm_tree = (plain_tree or {}).get("Payload container", {})
            sm_tree = as_list(sm_tree)[0].get("Plain NAS 5GS Message") if isinstance(sm_tree, (dict, list)) else None
            add({**base, "protocol": "NAS-5GSM", "direction": e["direction"], "carried_in": e["index"],
                 "hex": payload.hex(), "pdu_session_id": payload[1], "pti": payload[2],
                 "message_type": payload[3], "message": SM_TYPES.get(payload[3], hex(payload[3])),
                 "ies": nas_labels(sm_tree)})
    if t == 0x5e:
        opt = tlv_e_ies(plain, 3)
        if 0x71 in opt:
            inner = opt[0x71]
            sub = (plain_tree or {}).get("NAS message container", {})
            sub = sub.get("nas-5gs", {}).get("Plain NAS 5GS Message") if isinstance(sub, dict) else None
            add({**base, "protocol": "NAS-5GMM", "direction": "UL", "carried_in": e["index"],
                 "security_header_type": 0, "security_header": "plain (inside NAS message container)",
                 "plaintext_hex": inner.hex(), "message_type": inner[2],
                 "message": MM_TYPES.get(inner[2], hex(inner[2])), "ies": nas_labels(sub)})


def crypto(msgs, K, OPC, AMF_FIELD, SUPI, hn_priv, hn_priv_raw, hn_pub_raw):
    nas = [m for m in msgs if m["protocol"] == "NAS-5GMM"]
    by_type = lambda t: [m for m in nas if m["message_type"] == t]
    checks = {}

    reg = by_type(0x41)[0]
    p = bytes.fromhex(reg["plaintext_hex"])
    ngksi = p[3] >> 4
    l = struct.unpack_from("!H", p, 4)[0]
    mi = p[6:6 + l]
    if mi[0] & 0x07 != 1:
        fail("initial Registration request does not carry a SUCI")
    scheme, hnkid, out = mi[6] & 0x0f, mi[7], mi[8:]
    eph, ct, tag = out[:32], out[32:-8], out[-8:]
    z = hn_priv.exchange(X25519PublicKey.from_public_bytes(eph))
    ks = x963_kdf(z, eph, 64)
    enc_key, icb, mac_key = ks[:16], ks[16:32], ks[32:]
    if hmac.new(mac_key, ct, hashlib.sha256).digest()[:8] != tag:
        fail("SUCI MAC tag")
    msin = bcd(aes_ctr(enc_key, icb, ct))
    supi_from_suci = "imsi-" + PLMN[0] + PLMN[1] + msin
    if supi_from_suci != SUPI:
        fail(f"SUCI decrypts to {supi_from_suci}, expected {SUPI}")
    checks["suci_profile_a_mac_and_decrypt"] = "ok"

    ar = bytes.fromhex(by_type(0x56)[0]["plaintext_hex"])
    abba_len = ar[4]
    abba = ar[5:5 + abba_len]
    opt = tlv_e_ies(ar, 5 + abba_len, tv_len={0x21: 16})
    rand, autn = opt[0x21], opt[0x20]
    m0 = milenage(K, OPC, rand, b"\0" * 6, AMF_FIELD)
    sqn = xor(autn[:6], m0["ak"])
    m = milenage(K, OPC, rand, sqn, autn[6:8])
    if m["mac_a"] != autn[8:]:
        fail("AUTN MAC-A")
    if autn[6:8] != AMF_FIELD:
        fail("AUTN AMF field")
    checks["autn_mac_a"] = "ok"
    ck_ik = m["ck"] + m["ik"]
    res_star = kdf(ck_ik, 0x6B, SNN.encode(), rand, m["res"])[16:]
    resp = bytes.fromhex(by_type(0x57)[0]["plaintext_hex"])
    ue_res_star = tlv_e_ies(resp, 3)[0x2d]
    if ue_res_star != res_star:
        fail("RES*")
    checks["res_star"] = "ok"
    hres_star = hashlib.sha256(rand + res_star).digest()[16:]
    kausf = kdf(ck_ik, 0x6A, SNN.encode(), autn[:6])
    kseaf = kdf(kausf, 0x6C, SNN.encode())
    kamf = kdf(kseaf, 0x6D, SUPI.split("-", 1)[1].encode(), abba)

    smc = bytes.fromhex(by_type(0x5d)[0]["plaintext_hex"])
    nea, nia = smc[3] >> 4, smc[3] & 0x0f
    knasenc = kdf(kamf, 0x69, b"\x01", bytes([nea]))[16:]
    knasint = kdf(kamf, 0x69, b"\x02", bytes([nia]))[16:]
    if nia != 2:
        fail("selected NIA is not NIA2")

    counts, bearer_ok = [], None
    for bearer in (1, 0):
        good = True
        for msg in nas:
            if msg.get("security_header_type", 0) == 0 or "outer_hex" not in msg:
                continue
            ob = bytes.fromhex(msg["outer_hex"])
            d = 0 if msg["direction"] == "UL" else 1
            if nia2(knasint, ob[6], bearer, d, ob[6:]) != ob[2:6]:
                good = False
                break
        if good:
            bearer_ok = bearer
            break
    if bearer_ok is None:
        fail("NAS MAC (NIA2) did not verify with BEARER 0 or 1")
    for msg in nas:
        if "outer_hex" in msg:
            msg["nas_count"] = msg["nas_sequence_number"]
            msg["mac_verified"] = True
            counts.append({"index": msg["index"], "direction": msg["direction"],
                           "message": msg["message"], "count": msg["nas_count"]})
    checks["nas_mac_nia2"] = f"ok ({len(counts)} messages, BEARER={bearer_ok})"

    ics = next(x for x in msgs if x["protocol"] == "NGAP" and x["procedure_code"] == 14
               and x["pdu"] == "initiatingMessage")
    kgnb_wire = next(ie["value"] for ie in ics["_ies"] if ie["id"] == 94)
    kgnb_count = None
    for c in range(0, 4):
        if kdf(kamf, 0x6E, c.to_bytes(4, "big"), b"\x01") == kgnb_wire:
            kgnb_count = c
            break
    if kgnb_count is None:
        fail("K_gNB")
    checks["kgnb_from_kamf"] = f"ok (UL NAS COUNT {kgnb_count})"

    pdu_accept = next((x for x in msgs if x["protocol"] == "NAS-5GSM" and x["message_type"] == 0xc2), None)
    secrets = {
        "note": "Values marked 'captured' are on the wire in this capture. 'configured' values come from the "
                "setup files. 'derived' values were computed by setup/extract.py (an independent Python "
                "implementation of TS 35.206 Milenage and TS 33.501 Annex A) and confirmed against captured bytes "
                "as listed under 'checks'. None of them came from the kernel's own code.",
        "supi": {"value": SUPI, "source": "configured; also the decrypted SUCI"},
        "k": {"value": K.hex(), "source": "configured"},
        "opc": {"value": OPC.hex(), "source": "configured"},
        "amf_field": {"value": AMF_FIELD.hex(), "source": "configured; equals AUTN octets 7-8"},
        "sqn": {"value": sqn.hex(), "source": "derived: AUTN[0:6] xor AK; equals the Open5GS subscriber's "
                                              "provisioned SQN (64)",
                "sqn_xor_ak": autn[:6].hex()},
        "rand": {"value": rand.hex(), "source": "captured (Authentication request)"},
        "autn": {"value": autn.hex(), "source": "captured (Authentication request)"},
        "abba": {"value": abba.hex(), "source": "captured (Authentication request)"},
        "ngksi": {"value": by_type(0x56)[0]["plaintext_hex"][6:8], "source": "captured (Authentication request octet 4)"},
        "milenage": {"source": "derived", "mac_a": m["mac_a"].hex(), "res": m["res"].hex(), "ck": m["ck"].hex(),
                     "ik": m["ik"].hex(), "ak": m["ak"].hex(), "ak_star": m["ak_star"].hex(),
                     "mac_s": m["mac_s"].hex()},
        "res_star": {"value": res_star.hex(), "source": "captured (Authentication response) and derived; equal"},
        "hres_star": {"value": hres_star.hex(), "source": "derived; HRES*/HXRES* travel only on SBI, not captured"},
        "serving_network_name": SNN,
        "k_ausf": {"value": kausf.hex(), "source": "derived"},
        "k_seaf": {"value": kseaf.hex(), "source": "derived"},
        "k_amf": {"value": kamf.hex(), "source": "derived; confirmed by NAS MACs and K_gNB"},
        "k_nas_int": {"value": knasint.hex(), "source": "derived; verifies every NAS MAC in the capture"},
        "k_nas_enc": {"value": knasenc.hex(), "source": "derived (unused on the wire: NEA0)"},
        "k_gnb": {"value": kgnb_wire.hex(), "source": f"captured (InitialContextSetupRequest Security Key) and "
                                                     f"derived from K_AMF with UL NAS COUNT {kgnb_count}"},
        "nas_algorithms": {"ciphering": f"NEA{nea}", "integrity": f"NIA{nia}",
                           "source": "captured (Security mode command)"},
        "nas_bearer_for_mac": bearer_ok,
        "nas_counts": counts,
        "nas_count_overflow": 0,
        "home_network_key": {"scheme": "Profile A (X25519)", "key_id": 1,
                             "private": hn_priv_raw.hex(), "public": hn_pub_raw.hex(),
                             "source": "configured (setup/hnet/curve25519-1.key; UE homeNetworkPublicKey)"},
        "suci": {"mobile_identity_hex": mi.hex(), "routing_indicator": bcd(mi[4:6]), "protection_scheme": scheme,
                 "home_network_public_key_id": hnkid, "ue_ephemeral_public_key": eph.hex(),
                 "ciphertext": ct.hex(), "mac_tag": tag.hex(), "decrypted_msin": msin,
                 "ecies": {"shared_secret": z.hex(), "enc_key": enc_key.hex(), "icb": icb.hex(),
                           "mac_key": mac_key.hex()},
                 "ue_ephemeral_private_key": "not recoverable (UERANSIM generates it per SUCI and does not log it)",
                 "source": "captured; ECIES values derived with the home-network private key"},
        "pdu_session": {"pdu_session_id": pdu_accept["pdu_session_id"] if pdu_accept else None,
                        "ue_ipv4": "10.45.0.2", "dnn": "internet", "sst": 1},
        "not_recoverable": ["UE ephemeral X25519 private key for the SUCI",
                            "SBI (HTTP/2) messages between AMF, AUSF, UDM, SMF: not captured by design",
                            "RRC: UERANSIM's radio link is simulated over UDP 4997 and was not captured"],
    }
    return secrets, checks


if __name__ == "__main__":
    main()
