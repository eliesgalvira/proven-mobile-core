#!/usr/bin/env python3
"""Walk the NGAP ASN.1 model built by pycrate_asn1c (asnproc).

  ngap_model.py ASN_DIR ies MESSAGE...   IEs of each message (id, criticality, presence, type)
                                         and every named type they reach, down to primitives
  ngap_model.py ASN_DIR closure          type closure of the milestone message set, by tier,
                                         and what each optional IE would add to it

Needs pycrate (tested with 0.8.1). Run with python -I.
"""
import pathlib
import sys

from pycrate_asn1c.asnproc import GLOBAL, compile_text

MESSAGES = [
    "NGSetupRequest", "NGSetupResponse", "NGSetupFailure",
    "InitialUEMessage", "DownlinkNASTransport", "UplinkNASTransport",
    "InitialContextSetupRequest", "InitialContextSetupResponse", "InitialContextSetupFailure",
    "UEContextReleaseRequest", "UEContextReleaseCommand", "UEContextReleaseComplete",
    "PDUSessionResourceSetupRequest", "PDUSessionResourceSetupResponse",
    "ErrorIndication",
]
TRANSFERS = ["PDUSessionResourceSetupRequestTransfer", "PDUSessionResourceSetupResponseTransfer"]
# Sent by the gNB, so decoded by the AMF. ErrorIndication goes both ways.
INBOUND = {"NGSetupRequest", "InitialUEMessage", "UplinkNASTransport", "InitialContextSetupResponse",
           "InitialContextSetupFailure", "UEContextReleaseRequest", "UEContextReleaseComplete",
           "PDUSessionResourceSetupResponse", "ErrorIndication", "PDUSessionResourceSetupResponseTransfer"}
EXT_CONTAINERS = {"iE-Extensions", "choice-Extensions"}
CONTAINER_TYPES = {"ProtocolIE-Container", "ProtocolIE-SingleContainer", "ProtocolIE-Field",
                   "ProtocolExtensionContainer", "ProtocolExtensionField"}
TIERS = {"M": "reached from mandatory IEs (and from the fixed components of the types reached)",
         "R": "also reached from optional IEs with criticality reject in messages the AMF receives;\n"
              "#   an AMF that does not comprehend such an IE must reject the procedure (TS 38.413 10.3.4-10.3.5)",
         "O": "also reached from the remaining optional IEs",
         "X": "also reached through iE-Extensions / choice-Extensions rows"}
TIER_ORDER = "MROX"


def compile_dir(d):
    files = sorted(pathlib.Path(d).glob("*.asn"))
    compile_text([f.read_text() for f in files], filenames=[f.name for f in files])


def find(name):
    for mod_name, mod in GLOBAL.MOD.items():
        if not mod_name.startswith("_") and name in mod:
            return mod[name]
    raise KeyError(name)


def procedures():
    """(PDU kind index, procedure code) -> message type name, from NGAP-ELEMENTARY-PROCEDURES."""
    val = GLOBAL.MOD["NGAP-PDU-Descriptions"]["NGAP-ELEMENTARY-PROCEDURES"]._val
    out = {}
    for row in list(val["root"]) + list(val["ext"] or []):
        for kind, key in enumerate(("InitiatingMessage", "SuccessfulOutcome", "UnsuccessfulOutcome")):
            if key in row:
                out[(kind, row["procedureCode"])] = ref_name(row[key])
    return out


def ie_names():
    """ProtocolIE-ID value -> constant name, from NGAP-Constants."""
    names = {}
    for name, obj in GLOBAL.MOD["NGAP-Constants"].items():
        if name.startswith("id-") and obj._typeref is not None and obj._typeref.called[1] == "ProtocolIE-ID":
            names[obj._val] = name
    return names


def ref_name(obj):
    """Name of the NGAP type assignment obj refers to, or None for an inline type."""
    called = getattr(obj._typeref, "called", None)
    if isinstance(called, tuple) and called[0].startswith("NGAP"):
        return called[1]
    return None


def deref(obj):
    """A reference to a constructed type carries no content; return the referenced definition."""
    while obj._type in ("SEQUENCE", "CHOICE", "SEQUENCE OF") and obj._cont is None:
        mod, name = obj._typeref.called
        obj = GLOBAL.MOD[mod][name]
    return obj


def table_rows(obj):
    """Rows of the object set constraining an open type (IE or extension value)."""
    for c in obj._const:
        if c["type"] == "TABLE":
            val = c["tab"]._val
            return list(val["root"]) + list(val["ext"] or [])
    return []


def container_rows(component):
    """Rows of a ProtocolIE-Container / -SingleContainer / ProtocolExtensionContainer component."""
    component = deref(component)
    field = deref(component._cont) if component._type == "SEQUENCE OF" else component
    open_type = field._cont["value"] if "value" in field._cont else field._cont["extensionValue"]
    return table_rows(open_type)


def row_type(row):
    return row["Value"] if "Value" in row else row["Extension"]


def bound(r):
    lb, ub = getattr(r, "lb", r), getattr(r, "ub", r)
    if lb == ub:
        return str(lb)
    return f"{'MIN' if lb is None else lb}..{'MAX' if ub is None else ub}"


def constraints(obj):
    out = []
    for c in obj._const:
        if c["type"] in ("VAL", "SIZE"):
            body = ", ".join(bound(r) for r in c["root"]) + (", ..." if c["ext"] is not None else "")
            out.append(f"(SIZE({body}))" if c["type"] == "SIZE" else f"({body})")
        elif c["type"] == "CONTAINING":
            out.append(f"(CONTAINING {ref_name(c['obj']) or render(c['obj'])})")
        elif c["type"] == "ALPHABET":
            out.append(f"(FROM {c['text']})")
    return " ".join(out)


def render_ref_or_inline(obj):
    name = ref_name(obj)
    if name is None or name in CONTAINER_TYPES:
        return render(obj)
    extra = constraints(obj)
    return f"{name} {extra}".rstrip()


def render(obj):
    """One-line resolved definition of obj, naming referenced types instead of expanding them."""
    obj = deref(obj)
    t = obj._type
    if ref_name(obj) in CONTAINER_TYPES:
        return f"<{' '.join(filter(None, [ref_name(obj), constraints(obj)]))}: {len(container_rows(obj))} known rows>"
    if t in ("SEQUENCE", "CHOICE"):
        parts = []
        for n in obj._root:
            c = obj._cont[n]
            opt = " OPTIONAL" if c._flag and "OPTIONAL" in c._flag else ""
            parts.append(f"{n} {render_ref_or_inline(c)}{opt}")
        if obj._ext is not None:
            parts.append("...")
            parts.extend(f"{n} {render_ref_or_inline(obj._cont[n])}" for n in obj._ext)
        return f"{t} {{ " + ", ".join(parts) + " }"
    if t == "SEQUENCE OF":
        return f"SEQUENCE {constraints(obj)} OF {render_ref_or_inline(obj._cont)}"
    if t == "ENUMERATED":
        body = ", ".join(obj._root) + (", ..." if obj._ext is not None else "")
        body += "".join(f", {n}" for n in obj._ext or [])
        return f"ENUMERATED {{ {body} }}"
    return f"{t} {constraints(obj)}".rstrip()


def wanted(row, tier, inbound):
    if row["presence"] == "mandatory" or tier in "OX":
        return True
    return tier == "R" and inbound and row["criticality"] == "reject"


def children(obj, tier, inbound):
    """The types obj's encoding directly contains, as far as the tier follows open types."""
    for c in obj._const:
        if c["type"] == "CONTAINING":
            yield c["obj"]
    if ref_name(obj) == "ProtocolIE-Container":
        for row in container_rows(obj):
            if wanted(row, tier, inbound):
                yield row_type(row)
        return
    obj = deref(obj)
    if obj._type == "SEQUENCE OF":
        yield obj._cont
    elif obj._type in ("SEQUENCE", "CHOICE"):
        for n, c in obj._cont.items():
            if n not in EXT_CONTAINERS:
                yield c
            elif tier == "X":
                yield from (row_type(row) for row in container_rows(c))


def closure(roots, tier):
    """Named NGAP types reachable from the named roots, skipping the generic container types."""
    seen = {}
    for root in roots:
        seen[root] = find(root)
        walk(seen[root], tier, root in INBOUND, seen)
    return seen


def walk(start, tier, inbound, seen):
    stack = [start]
    while stack:
        obj = stack.pop()
        name = ref_name(obj)
        if name in CONTAINER_TYPES:
            name = None
        if name is not None:
            if name in seen:
                continue
            seen[name] = obj
        stack.extend(children(obj, tier, inbound))


def message_ies(msg):
    return container_rows(find(msg)._cont["protocolIEs"])


def cmd_ies(msgs):
    names = ie_names()
    for msg in msgs:
        print(f"== {msg}")
        ies = message_ies(msg)
        for row in ies:
            print(f"  IE {row['id']:>3} {names.get(row['id'], '?'):<45} {row['criticality']:<7} "
                  f"{row['presence']:<11} {ref_name(row_type(row)) or render(row_type(row))}")
        reached = closure([msg], "O")
        print(f"  -- {len(reached)} named types reached, the message included (all IEs, CONTAINING followed,"
              " extension containers not followed):")
        for name in sorted(reached, key=str.lower):
            print(f"  {name} ::= {render(find(name))}")


def cmd_closure():
    tiers = {t: closure(MESSAGES + TRANSFERS, t) for t in TIER_ORDER}
    tier_of = {}
    for t in reversed(TIER_ORDER):
        for name in tiers[t]:
            tier_of[name] = t
    kinds = {}
    for name in tiers["O"]:
        kinds[find(name)._type] = kinds.get(find(name)._type, 0) + 1
    print("# NGAP type closure for the milestone message set")
    print(f"# messages ({len(MESSAGES)}): {' '.join(MESSAGES)}")
    print(f"# transfers ({len(TRANSFERS)}): {' '.join(TRANSFERS)}")
    print("# Counted: named NGAP type assignments, including the messages and transfers themselves.")
    print("# Not counted: the generic containers " + ", ".join(sorted(CONTAINER_TYPES)) + ",")
    print("#   which are parameterised framing handled once by the codec library.")
    print("# CONTAINING is followed (an OCTET STRING that holds a transfer pulls in that transfer).")
    for t, desc in TIERS.items():
        print(f"# tier {t}: {desc}")
    print("# counts (cumulative): " + "  ".join(f"{'+'.join(TIER_ORDER[:i + 1])}={len(tiers[t])}"
                                              for i, t in enumerate(TIER_ORDER)))
    print("# M+R+O by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items(), key=lambda kv: -kv[1])))
    print("#")
    print("# tier  name  ::=  resolved definition")
    for name in sorted(tier_of, key=lambda n: (TIER_ORDER.index(tier_of[n]), n.lower())):
        print(f"{tier_of[name]}  {name} ::= {render(find(name))}")
    print("#")
    print("# IE rows. 'adds' = named types the IE's value reaches beyond tier M+R")
    print("# (root only, CONTAINING followed), i.e. the cost of comprehending that optional IE.")
    names = ie_names()
    for msg in MESSAGES + TRANSFERS:
        if "protocolIEs" not in deref(find(msg))._cont:
            continue
        print(f"# {msg} ({'gNB->AMF' if msg in INBOUND else 'AMF->gNB'}{', both ways' if msg == 'ErrorIndication' else ''})")
        for row in message_ies(msg):
            extra = {}
            walk(row_type(row), "O", msg in INBOUND, extra)
            adds = len(set(extra) - set(tiers["R"]))
            print(f"#   {row['id']:>3} {names.get(row['id'], '?'):<48} {row['criticality']:<7} "
                  f"{row['presence']:<10} {ref_name(row_type(row)) or render(row_type(row)):<44} adds {adds}")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    compile_dir(sys.argv[1])
    cmd = sys.argv[2]
    if cmd == "ies":
        cmd_ies(sys.argv[3:])
    elif cmd == "closure":
        cmd_closure()
    else:
        sys.exit(__doc__)
