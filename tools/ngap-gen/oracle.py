#!/usr/bin/env python3
"""Differential oracle: pycrate's APER runtime against our codec on the NGAP vectors.

Every NGAP message in VECTORS is decoded by pycrate (from the pinned ASN.1,
compiled to a runtime module in a temporary directory) and by our codec
(tools/ngap-gen/oracle.bend, built with bend, which reads the same files in
the same order); both are printed in the normal form gen_show.py defines and
must agree. pycrate must also re-encode each message to its octets, and a
hand-made message's octets must be pycrate's encoding of its `jer` value.
Run with python -I from the repository root; exits 1 on any difference.
"""
import json
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/ngap-gen"))
import gen  # noqa: E402
import gen_show  # noqa: E402
from pycrate_asn1c.asnproc import generate_modules  # noqa: E402
from pycrate_asn1c.generator import PycrateGenerator  # noqa: E402

VECTORS = ["test-vectors/capture/vectors.json", "test-vectors/capture/handover.json", "test-vectors/hand/ngap-handover.json"]
CRIT = {"reject": 0, "ignore": 1, "notify": 2}
KIND = {"initiatingMessage": 0, "successfulOutcome": 1, "unsuccessfulOutcome": 2}


def runtime(tmp):
    """pycrate's runtime objects for the pinned ASN.1, by type name."""
    path = pathlib.Path(tmp) / "ngap_rt.py"
    generate_modules(PycrateGenerator, str(path))
    sys.path.insert(0, tmp)
    import ngap_rt
    objs = {}
    for mod in (ngap_rt.NGAP_CommonDataTypes, ngap_rt.NGAP_IEs, ngap_rt.NGAP_PDU_Contents, ngap_rt.NGAP_PDU_Descriptions):
        for name in mod._all_:
            objs[name._name] = name
    return objs


class Normal:
    """The normal form of pycrate values, mirroring gen_show.py."""

    def __init__(self, g, objs):
        self.g, self.objs = g, objs

    def octets(self, val):
        """Octets of a value pycrate decoded inside an open or containing type."""
        if isinstance(val, tuple) and isinstance(val[0], str):
            obj = self.objs[val[0]]
            obj.set_val(val[1])
            return obj.to_aper()
        return val

    def raw_ie(self, d, key):
        return f"{d['id']}/{CRIT[d['criticality']]}/{self.octets(d[key]).hex()}"

    def show(self, val, t):
        return getattr(self, t.kind)(t, val)

    def exts(self, t, val):
        return "[" + "".join("," + self.raw_ie(d, "extensionValue") for d in val) + "]"

    def ie(self, t, val):
        return self.raw_ie(val, "value")

    def record(self, t, val):
        return "{" + ",".join(self.show(val[asn], ft) if asn in val else "-" for asn, (_, ft, _) in zip(t.asn_fields, t.fields)) + "}"

    def choice(self, t, val):
        j = t.asn_alts.index(val[0])
        return f"{j}:" + self.show(val[1], t.alts[j][1])

    def list(self, t, val):
        return "[" + "".join("," + self.show(x, t.item) for x in val) + "]"

    def message(self, t, val):
        known = {iid: tn for iid, _, tn, _ in self.g.view_rows(t.name)}
        out = []
        for d in val["protocolIEs"]:
            tn, v = d["value"]
            shown = self.show(v, known[d["id"]]) if d["id"] in known and known[d["id"]].name == tn else self.octets(d["value"]).hex()
            out.append(f",{d['id']}/{CRIT[d['criticality']]}/{shown}")
        return "[" + "".join(out) + "]"

    def alias(self, t, val):
        p = t.prim
        if t.contains is not None:
            return self.show(val[1], self.g.types[t.contains])
        if p in ("Int", "AInt"):
            return str(val)
        if p in ("XInt", "XBig"):
            if t.lb <= val <= t.ub:
                return str(val) if p == "XInt" else unsigned(val).hex()
            return "x" + signed(val).hex()
        if p == "Big":
            return unsigned(val).hex()
        if p == "Enum":
            i = t.values.index(val)
            return str(i) if i < t.root_count else f"x{i - t.root_count}"
        if p in gen_show.BITS:
            n, width = val
            return "b" + (format(n, f"0{width}b") if width else "")
        if p in ("Str", "XStr", "UStr"):
            return val.encode("ascii").hex()
        return self.octets(val).hex()


def unsigned(n):
    return n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")


def signed(n):
    length = (n.bit_length() + 8) // 8
    return n.to_bytes(max(1, length), "big", signed=True)


def ours(tmp):
    binary = pathlib.Path(tmp) / "oracle"
    subprocess.run(["bend", str(ROOT / "tools/ngap-gen/oracle.bend"), "-o", str(binary)], check=True, stdout=subprocess.DEVNULL)
    out = subprocess.run([str(binary)], check=True, capture_output=True, text=True).stdout
    return [line.split(": ", 1) for line in out.splitlines() if line]


def main():
    g = gen.build(str(ROOT / "tools/ngap-gen/asn"))
    messages = [m for f in VECTORS for m in json.loads((ROOT / f).read_text())["messages"] if m["protocol"] == "NGAP"]
    with tempfile.TemporaryDirectory() as tmp:
        objs = runtime(tmp)
        bend = ours(tmp)
    normal = Normal(g, objs)
    pdu = objs["NGAP-PDU"]
    status = 0
    if len(bend) != len(messages):
        print(f"FAIL our codec printed {len(bend)} messages, the vectors have {len(messages)}")
        return 1
    for m, (name, theirs_line) in zip(messages, bend):
        raw = bytes.fromhex(m["hex"])
        where = f"frame {m['frame']}" if "frame" in m else "hand-made"
        pdu.from_aper(raw)
        kind, body = pdu.get_val()
        if pdu.to_aper() != raw:
            print(f"FAIL {m['message']}: pycrate does not re-encode the octets")
            status = 1
        if "jer" in m:
            pdu.from_jer(json.dumps(m["jer"]))
            if pdu.to_aper() != raw:
                print(f"FAIL {m['message']}: the octets are not pycrate's encoding of its jer value")
                status = 1
        expected = f"{KIND[kind]}/{body['procedureCode']}/{CRIT[body['criticality']]}/" + normal.show(body["value"][1], g.types[body["value"][0]])
        if name != m["message"] or theirs_line != expected:
            status = 1
            print(f"FAIL {m['message']} ({where})\n  pycrate: {expected}\n  ours:    {theirs_line}")
        else:
            print(f"ok   {m['message']} ({where})")
    print("oracle agrees" if status == 0 else "oracle disagrees")
    return status


if __name__ == "__main__":
    sys.exit(main())
