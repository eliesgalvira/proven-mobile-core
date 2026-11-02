#!/usr/bin/env python3
"""Emit the Bend NGAP codec for the milestone message set from the pinned ASN.1.

  gen.py ASN_DIR OUT_DIR

Writes OUT_DIR/types.bend: for every type in the tier M+R closure a datatype
(or alias), `T.read`, `T.write`, `T.after` and `T.valid`, built on
kernel/aper.bend and kernel/ngap/frame.bend; plus `T.roundtrips` and the
per-message IE dispatch used by the tests. views.bend holds one view per
message; laws.bend and proofs.bend (gen_proofs.py) the codec laws of every
type with their proofs; show.bend (gen_show.py) the normal form oracle.py
compares with pycrate. The generator is untrusted: the checker judges what
it emits. Needs pycrate 0.8.1; run with python -I.
"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import gen_proofs  # noqa: E402
import gen_show  # noqa: E402
import ngap_model as M  # noqa: E402

KEYWORDS = {"def", "type", "match", "case", "import", "as", "is", "for", "law", "return",
            "if", "else", "do", "with", "true", "false", "lambda", "let", "in", "fn", "use"}
EXTS = "iE-Extensions"
SINGLE = "ProtocolIE-SingleContainer"


def bname(name):
    out = name.replace("-", "_")
    return out + "_" if out in KEYWORDS else out


def bitlen(n):
    return n.bit_length() if n > 0 else 0


def rng(c):
    r = c["root"][0]
    lb, ub = getattr(r, "lb", r), getattr(r, "ub", r)
    return lb, ub, c["ext"] is not None


def const(obj, kind):
    for c in obj._const:
        if c["type"] == kind:
            return c
    return None


def size_params(lb, ub):
    """(al, nbits, lo, diff) for a constrained length or count."""
    diff = ub - lb
    if diff + 1 <= 255:
        return "False{}", bitlen(diff), lb, diff
    if diff + 1 == 256:
        return "True{}", 8, lb, diff
    if diff + 1 <= 65536:
        return "True{}", 16, lb, diff
    raise ValueError(f"size range {lb}..{ub} needs an unconstrained length")


def int_params(lb, ub):
    diff = ub - lb
    if diff + 1 <= 255:
        return "Int", "False{}", bitlen(diff), diff
    if diff + 1 == 256:
        return "AInt", "True{}", 8, diff
    if diff + 1 <= 65536:
        return "AInt", "True{}", 16, diff
    if lb != 0:
        raise ValueError(f"indefinite-length range {lb}..{ub} with a non-zero lower bound")
    maxl = (bitlen(diff) + 7) // 8
    return "Big", None, bitlen(maxl - 1), maxl - 1


class Type:
    """One emitted type: kind in alias|record|choice|list|message, with its codec expressions."""

    def __init__(self, name):
        self.name = name
        self.bend = bname(name)
        self.deps = []


class Gen:
    def __init__(self):
        self.types = {}
        self.order = []
        self.lines = []
        self.messages = {}

    # -- model walking -------------------------------------------------------

    def type_of(self, obj, inline_name):
        """Name of the type to emit for obj, synthesising one for inline types."""
        ref = M.ref_name(obj)
        if ref == "ProtocolExtensionContainer":
            return "EXTS"
        if ref == SINGLE:
            return "IE"
        if ref is not None:
            self.visit(ref, M.find(ref))
            return ref
        self.visit(inline_name, obj)
        return inline_name

    def visit(self, name, obj):
        if name in self.types:
            return
        t = Type(name)
        self.types[name] = t
        self.describe(t, obj)
        self.order.append(name)

    def describe(self, t, obj):
        obj = M.deref(obj)
        kind = obj._type
        if kind == "INTEGER":
            lb, ub, ext = rng(const(obj, "VAL"))
            prim, al, n, diff = int_params(lb, ub)
            t.lb, t.ub = lb, ub
            if ext:
                t.kind = "alias"
                if prim == "Big":
                    t.data, t.prim, t.args = "Ap.XBig", "XBig", (n, diff)
                else:
                    t.data, t.prim, t.args = "Ap.XInt", "XInt", (al, n, diff)
            elif prim == "Big":
                t.kind, t.data, t.prim, t.args = "alias", "B.Bytes()", "Big", (n, diff)
            else:
                t.kind, t.data, t.prim, t.args = "alias", "U32", prim, (n, diff)
        elif kind == "ENUMERATED":
            count = len(obj._root)
            t.kind, t.data, t.prim = "alias", "Ap.Enum", "Enum"
            t.args = (bitlen(count - 1), count - 1, "True{}" if obj._ext is not None else "False{}")
            t.values = list(obj._root) + list(obj._ext or [])
            t.root_count = count
        elif kind == "BIT STRING":
            t.kind, t.data = "alias", "Ap.Bits()"
            c = const(obj, "SIZE")
            if c is None:
                t.prim, t.args = "UBitStr", ()
            else:
                lb, ub, ext = rng(c)
                if lb == ub and ext:
                    if lb > 16:
                        raise ValueError(f"{t.name}: extensible fixed bit string above 16 bits")
                    t.prim, t.args = "XBits", (lb,)
                elif lb == ub:
                    t.prim, t.args = ("Bits" if lb <= 16 else "ABits"), (lb,)
                else:
                    t.prim, t.args = ("XBitStr" if ext else "BitStr"), size_params(lb, ub)
        elif kind == "OCTET STRING":
            t.kind, t.data = "alias", "B.Bytes()"
            c = const(obj, "SIZE")
            if c is None:
                t.prim, t.args = "Open", ()
            else:
                lb, ub, ext = rng(c)
                if ext:
                    raise ValueError(f"{t.name}: extensible octet string size")
                if lb == ub:
                    t.prim, t.args = ("Octets" if lb <= 2 else "AOctets"), (lb,)
                else:
                    t.prim, t.args = "OctStr", size_params(lb, ub)
        elif kind == "PrintableString":
            t.kind, t.data = "alias", "B.Bytes()"
            c = const(obj, "SIZE")
            if c is None:
                t.prim, t.args = "UStr", ()
            else:
                lb, ub, ext = rng(c)
                t.prim, t.args = ("XStr" if ext else "Str"), size_params(lb, ub)
        elif kind == "SEQUENCE":
            if list(obj._root) == ["protocolIEs"]:
                t.kind, t.data, t.ext = "message", "List<&2, Fr.Ie>", obj._ext is not None
                self.messages[t.name] = M.container_rows(obj._cont["protocolIEs"])
                return
            t.kind, t.ext = "record", obj._ext is not None
            t.fields = []
            t.asn_fields = list(obj._root)
            for n in obj._root:
                comp = obj._cont[n]
                optional = bool(comp._flag) and "OPTIONAL" in comp._flag
                ftype = self.type_of(comp, f"{t.name}-{n}")
                t.fields.append((bname(n), ftype, optional))
                if ftype not in ("EXTS", "IE"):
                    t.deps.append(ftype)
        elif kind == "CHOICE":
            t.kind, t.ext = "choice", obj._ext is not None
            t.alts = []
            t.asn_alts = list(obj._root)
            for n in obj._root:
                atype = self.type_of(obj._cont[n], f"{t.name}-{n}")
                t.alts.append((bname(n), atype))
                if atype not in ("EXTS", "IE"):
                    t.deps.append(atype)
        elif kind == "SEQUENCE OF":
            lb, ub, ext = rng(const(obj, "SIZE"))
            if ext:
                raise ValueError(f"{t.name}: extensible sequence-of size")
            t.kind = "list"
            t.item = self.type_of(obj._cont, f"{t.name}-Item")
            t.deps.append(t.item)
            t.args = size_params(lb, ub)
            t.data = f"List<&2, {self.data(t.item)}>"
        else:
            raise ValueError(f"{t.name}: unsupported kind {kind}")

    # -- codec expressions for a type name ------------------------------------

    def data(self, name):
        if name == "EXTS":
            return "List<&2, Fr.Ie>"
        if name == "IE":
            return "Fr.Ie"
        t = self.types[name]
        if t.kind in ("record", "choice"):
            return t.bend
        return f"{t.bend}()"

    def read(self, name, c):
        if name == "EXTS":
            return f"Fr.Exts.read({c})"
        if name == "IE":
            return f"Fr.Ie.read({c})"
        return f"{self.types[name].bend}.read({c})"

    def write(self, name, v, rem, rest):
        if name == "EXTS":
            return f"Fr.Exts.write({v}, {rem}, {rest})"
        if name == "IE":
            return f"Fr.Ie.write({v}, {rem}, {rest})"
        return f"{self.types[name].bend}.write({v}, {rem}, {rest})"

    def after(self, name, v, rem):
        if name == "EXTS":
            return f"Fr.Exts.after({rem})"
        if name == "IE":
            return f"Fr.Ie.after({rem})"
        return f"{self.types[name].bend}.after({v}, {rem})"

    def valid(self, name, v):
        if name == "EXTS":
            return f"Fr.Exts.valid({v})"
        if name == "IE":
            return f"Fr.Ie.valid({v})"
        return f"{self.types[name].bend}.valid({v})"

    # -- emission --------------------------------------------------------------

    def out(self, text=""):
        self.lines.append(text)

    def emit_all(self):
        done = set()

        def emit(name):
            if name in done:
                return
            done.add(name)
            for d in self.types[name].deps:
                emit(d)
            getattr(self, "emit_" + self.types[name].kind)(self.types[name])
            self.emit_roundtrips(self.types[name])

        for name in self.order:
            emit(name)

    def emit_roundtrips(self, t):
        b, d = t.bend, self.data(t.name)
        self.out(f"def {b}.roundtrips.end(+bs: B.Bytes(), r: Ap.Rd({d})) -> Bool:")
        self.out("  match r:")
        self.out("    case Fail{e}:")
        self.out("      False{}")
        self.out("    case Done{(+v, c)}:")
        self.out("      match c:")
        self.out("        case Ap.Cur{rem, bits}:")
        self.out(f"          Bool.and(Ap.Tail.zero(bits), Bool.and({self.valid(t.name, 'v')}, B.bytes_eq(Ap.pack({self.write(t.name, 'v', '0n', '[]')}), bs)))")
        self.out()
        self.out(f"def {b}.roundtrips(+bs: B.Bytes()) -> Bool:")
        self.out(f"  {b}.roundtrips.end(bs, {self.read(t.name, 'Ap.Cur{0n, Ap.unpack(bs)}')})")
        self.out()

    def prim_exprs(self, t):
        a = t.args
        p = t.prim
        if p in ("Int", "AInt"):
            n, diff = a
            return (f"Ap.{p}.read({n}n, {diff}, c)", f"Ap.{p}.write({n}n, v, rem, rest)",
                    f"Ap.{p}.after({n}n, rem)", f"Ap.Int.valid({n}n, {diff}, v)")
        if p == "Big":
            n, diff = a
            return (f"Ap.Big.read({n}n, {diff}n, c)", f"Ap.Big.write({n}n, v, rem, rest)",
                    "Ap.Big.after(rem)", f"Ap.Big.valid({diff}n, v)")
        if p == "XInt":
            al, n, diff = a
            return (f"Ap.XInt.read({al}, {n}n, {diff}, c)", f"Ap.XInt.write({al}, {n}n, v, rem, rest)",
                    f"Ap.XInt.after({al}, {n}n, v, rem)", f"Ap.XInt.valid({n}n, {diff}, v)")
        if p == "XBig":
            n, diff = a
            return (f"Ap.XBig.read({n}n, {diff}n, c)", f"Ap.XBig.write({n}n, v, rem, rest)",
                    "Ap.XBig.after(v, rem)", f"Ap.XBig.valid({diff}n, v)")
        if p == "Enum":
            n, diff, ext = a
            return (f"Ap.Enum.read({n}n, {diff}, {ext}, c)", f"Ap.Enum.write({n}n, {ext}, v, rem, rest)",
                    f"Ap.Enum.after({n}n, {ext}, v, rem)", f"Ap.Enum.valid({n}n, {diff}, {ext}, v)")
        if p in ("Bits", "ABits"):
            (n,) = a
            return (f"Ap.{p}.read({n}n, c)", f"Ap.{p}.write(v, rem, rest)",
                    f"Ap.{p}.after({n}n, rem)", f"Nat.is_eq(List.length(&2, Bool, v), {n}n)")
        if p == "XBits":
            (n,) = a
            return (f"Ap.XBits.read({n}n, c)", f"Ap.XBits.write({n}n, v, rem, rest)",
                    f"Ap.XBits.after({n}n, v, rem)", f"Ap.XBits.valid({n}n, v)")
        if p == "BitStr":
            al, n, lo, diff = a
            return (f"Ap.BitStr.read({al}, {n}n, {lo}n, {diff}n, c)", f"Ap.BitStr.write({al}, {n}n, {lo}n, v, rem, rest)",
                    "Ap.BitStr.after(v, rem)", f"Ap.BitStr.valid({lo}n, {diff}n, v)")
        if p == "XBitStr":
            al, n, lo, diff = a
            return (f"Ap.XBitStr.read({al}, {n}n, {lo}n, {diff}n, c)", f"Ap.XBitStr.write({al}, {n}n, {lo}n, {diff}n, v, rem, rest)",
                    "Ap.XBitStr.after(v, rem)", f"Ap.XBitStr.valid({lo}n, {diff}n, v)")
        if p == "UBitStr":
            return ("Ap.UBitStr.read(c)", "Ap.UBitStr.write(v, rem, rest)", "Ap.UBitStr.after(v, rem)", "Ap.UBitStr.valid(v)")
        if p in ("Octets", "AOctets"):
            (n,) = a
            return (f"Ap.{p}.read({n}n, c)", f"Ap.{p}.write(v, rem, rest)",
                    f"Ap.{p}.after(rem)", f"Bool.and(Nat.is_eq(List.length(&2, U32, v), {n}n), B.all_bytes(v))")
        if p == "OctStr":
            al, n, lo, diff = a
            return (f"Ap.OctStr.read({al}, {n}n, {lo}n, {diff}n, c)", f"Ap.OctStr.write({al}, {n}n, {lo}n, v, rem, rest)",
                    "Ap.OctStr.after(rem)", f"Ap.OctStr.valid({lo}n, {diff}n, v)")
        if p == "Open":
            return ("Ap.Open.read(c)", "Ap.Open.write(v, rem, rest)", "Ap.Open.after(rem)", "Ap.Open.valid(v)")
        if p == "Str":
            al, n, lo, diff = a
            return (f"Ap.Str.read({al}, {n}n, {lo}n, {diff}n, c)", f"Ap.Str.write({al}, {n}n, {lo}n, v, rem, rest)",
                    "Ap.Str.after(rem)", f"Ap.Str.valid({lo}n, {diff}n, v)")
        if p == "XStr":
            al, n, lo, diff = a
            return (f"Ap.XStr.read({al}, {n}n, {lo}n, {diff}n, c)", f"Ap.XStr.write({al}, {n}n, {lo}n, {diff}n, v, rem, rest)",
                    "Ap.XStr.after(rem)", f"Ap.XStr.valid({lo}n, {diff}n, v)")
        if p == "UStr":
            return ("Ap.UStr.read(c)", "Ap.UStr.write(v, rem, rest)", "Ap.UStr.after(rem)", "Ap.UStr.valid(v)")
        raise ValueError(p)

    def emit_alias(self, t):
        b = t.bend
        r, w, a, v = self.prim_exprs(t)
        self.out(f"# {t.name} ::= {M.render(M.find(t.name)) if self.is_named(t.name) else t.prim}")
        self.out(f"def {b}() -> Data:")
        self.out(f"  {t.data}")
        self.out()
        if t.prim == "Enum":
            for i, name in enumerate(t.values):
                self.out(f"def {b}.{bname(name)}() -> U32:")
                self.out(f"  {i}")
                self.out()
        if t.prim in ("Int", "AInt") and t.lb != 0:
            self.out(f"# The value is its offset from the lower bound {t.lb}.")
            self.out(f"def {b}.value(v: {b}()) -> U32:")
            self.out(f"  U32.add({t.lb}, v)")
            self.out()
        self.out(f"def {b}.read(c: Ap.Cur) -> Ap.Rd({b}()):")
        self.out(f"  {r}")
        self.out()
        self.out(f"def {b}.write(+v: {b}(), +rem: Nat, +rest: Ap.Bits()) -> Ap.Bits():")
        self.out(f"  {w}")
        self.out()
        self.out(f"def {b}.after(+v: {b}(), +rem: Nat) -> Nat:")
        self.out(f"  {a}")
        self.out()
        self.out(f"def {b}.valid(+v: {b}()) -> Bool:")
        self.out(f"  {v}")
        self.out()

    def is_named(self, name):
        try:
            M.find(name)
            return True
        except KeyError:
            return False

    def emit_message(self, t):
        b = t.bend
        self.out(f"# {t.name}: a protocol IE container (TS 38.413 §9.2).")
        self.out(f"def {b}() -> Data:")
        self.out("  List<&2, Fr.Ie>")
        self.out()
        self.out(f"def {b}.r_ext(r: Ap.Rd(Bool)) -> Ap.Rd({b}()):")
        self.out("  match r:")
        self.out("    case Fail{e}:")
        self.out("      Fail{e}")
        self.out("    case Done{(ext, c)}:")
        self.out("      match ext:")
        self.out("        case True{}:")
        self.out("          Fail{B.Unsupported{1}}")
        self.out("        case False{}:")
        self.out("          Fr.Ies.read(c)")
        self.out()
        self.out(f"def {b}.read(c: Ap.Cur) -> Ap.Rd({b}()):")
        self.out(f"  {b}.r_ext(Ap.Bit.read(c))")
        self.out()
        self.out(f"def {b}.write(+v: {b}(), +rem: Nat, +rest: Ap.Bits()) -> Ap.Bits():")
        self.out("  Ap.Bit.write(False{}, rem, Fr.Ies.write(v, Ap.Bit.after(rem), rest))")
        self.out()
        self.out(f"def {b}.after(+v: {b}(), +rem: Nat) -> Nat:")
        self.out("  0n")
        self.out()
        self.out(f"def {b}.valid(+v: {b}()) -> Bool:")
        self.out("  Fr.Ies.valid(v)")
        self.out()

    def emit_record(self, t):
        b = t.bend
        fields = t.fields
        opts = [i for i, (_, _, o) in enumerate(fields) if o]
        k = len(opts)
        self.out(f"# {t.name} ::= {M.render(M.find(t.name)) if self.is_named(t.name) else 'SEQUENCE'}")
        self.out(f"type {b} is Data:")
        self.out("  " + b + "{" + ", ".join(f"{fn}: {self.ftype(ft, o)}" for fn, ft, o in fields) + "}")
        self.out()
        for i in opts:
            fn, ft, _ = fields[i]
            d = self.data(ft)
            self.out(f"def {b}.v_{fn}(m: Maybe<&2, {d}>) -> Bool:")
            self.out("  match m:")
            self.out("    case None{}:")
            self.out("      True{}")
            self.out("    case Some{v}:")
            self.out(f"      {self.valid(ft, 'v')}")
            self.out()
            self.out(f"def {b}.w_{fn}(m: Maybe<&2, {d}>, +rem: Nat, +rest: Ap.Bits()) -> Ap.Bits():")
            self.out("  match m:")
            self.out("    case None{}:")
            self.out("      rest")
            self.out("    case Some{v}:")
            self.out(f"      {self.write(ft, 'v', 'rem', 'rest')}")
            self.out()
            self.out(f"def {b}.a_{fn}(m: Maybe<&2, {d}>, +rem: Nat) -> Nat:")
            self.out("  match m:")
            self.out("    case None{}:")
            self.out("      rem")
            self.out("    case Some{v}:")
            self.out(f"      {self.after(ft, 'v', 'rem')}")
            self.out()
            self.out(f"def {b}.s_{fn}(r: Ap.Rd({d})) -> Ap.Rd(Maybe<&2, {d}>):")
            self.out("  match r:")
            self.out("    case Fail{e}:")
            self.out("      Fail{e}")
            self.out("    case Done{(v, c)}:")
            self.out("      Done{(Some{v}, c)}")
            self.out()
            self.out(f"def {b}.o_{fn}(p: Bool, c: Ap.Cur) -> Ap.Rd(Maybe<&2, {d}>):")
            self.out("  match p:")
            self.out("    case False{}:")
            self.out("      Done{(None{}, c)}")
            self.out("    case True{}:")
            self.out(f"      {b}.s_{fn}({self.read(ft, 'c')})")
            self.out()
        # validity
        self.out(f"def {b}.valid(x: {b}) -> Bool:")
        self.out("  match x:")
        self.out("    case " + b + "{" + ", ".join(fn for fn, _, _ in fields) + "}:")
        conj = [f"{b}.v_{fn}({fn})" if o else self.valid(ft, fn) for fn, ft, o in fields]
        self.out("      " + self.conj(conj))
        self.out()
        # reader chain, last to first so each helper's callee precedes it
        m = len(fields)
        names = [fn for fn, _, _ in fields]
        for i in reversed(range(m)):
            fn, ft, o = fields[i]
            later_opts = [fields[j][0] for j in range(i + 1, m) if fields[j][2]]
            params = [f"p_{p}: Bool" for p in later_opts] + [f"{names[j]}: {self.ftype(fields[j][1], fields[j][2])}" for j in range(i)]
            d = self.ftype(ft, o)
            self.out(f"def {b}.r_{fn}({', '.join(params + [f'r: Ap.Rd({d})'])}) -> Ap.Rd({b}):")
            self.out("  match r:")
            self.out("    case Fail{e}:")
            self.out("      Fail{e}")
            self.out(f"    case Done{{({fn}, c)}}:")
            if i == m - 1:
                self.out("      Done{(" + b + "{" + ", ".join(names) + "}, c)}")
            else:
                nfn, nft, no = fields[i + 1]
                rest_opts = [fields[j][0] for j in range(i + 2, m) if fields[j][2]]
                args = [f"p_{p}" for p in rest_opts] + names[: i + 1]
                nxt = f"{b}.o_{nfn}(p_{nfn}, c)" if no else self.read(nft, "c")
                self.out(f"      {b}.r_{nfn}({', '.join(args + [nxt])})")
            self.out()
        first = fields[0]
        first_call = (f"{b}.o_{first[0]}(p_{first[0]}, c)" if first[2] else self.read(first[1], "c"))
        first_args = [f"p_{fields[j][0]}" for j in range(1, m) if fields[j][2]]
        start = f"{b}.r_{first[0]}({', '.join(first_args + [first_call])})"
        if k > 0:
            self.out(f"def {b}.r_bm(r: Ap.Rd(Ap.Bits())) -> Ap.Rd({b}):")
            self.out("  match r:")
            self.out("    case Fail{e}:")
            self.out("      Fail{e}")
            self.out("    case Done{(bm, c)}:")
            self.out("      match bm:")
            self.out("        case " + " <> ".join(f"p_{fields[i][0]}" for i in opts) + " <> Nil{}:")
            self.out(f"          {start}")
            self.out("        case _:")
            self.out("          Fail{B.Short{}}")
            self.out()
            body = f"{b}.r_bm(Ap.Bits.read({k}n, c))"
        else:
            body = start
        if t.ext:
            self.out(f"def {b}.r_ext(r: Ap.Rd(Bool)) -> Ap.Rd({b}):")
            self.out("  match r:")
            self.out("    case Fail{e}:")
            self.out("      Fail{e}")
            self.out("    case Done{(ext, c)}:")
            self.out("      match ext:")
            self.out("        case True{}:")
            self.out("          Fail{B.Unsupported{1}}")
            self.out("        case False{}:")
            self.out(f"          {body}")
            self.out()
            body = f"{b}.r_ext(Ap.Bit.read(c))"
        self.out(f"def {b}.read(c: Ap.Cur) -> Ap.Rd({b}):")
        self.out(f"  {body}")
        self.out()
        # writer and after
        self.out(f"def {b}.write(x: {b}, +rem: Nat, +rest: Ap.Bits()) -> Ap.Bits():")
        self.out("  match x:")
        self.out("    case " + b + "{" + ", ".join(f"+{fn}" for fn in names) + "}:")
        r0 = "Ap.Bit.after(rem)" if t.ext else "rem"
        if k > 0:
            self.out(f"      +r0 = Ap.Bits.after({k}n, {r0})")
        else:
            self.out(f"      +r0 = {r0}")
        for i in range(m - 1):
            fn, ft, o = fields[i]
            aft = f"{b}.a_{fn}({fn}, r{i})" if o else self.after(ft, fn, f"r{i}")
            self.out(f"      +r{i + 1} = {aft}")
        inner = "rest"
        for i in reversed(range(m)):
            fn, ft, o = fields[i]
            inner = f"{b}.w_{fn}({fn}, r{i}, {inner})" if o else self.write(ft, fn, f"r{i}", inner)
        if k > 0:
            bm = "[" + ", ".join(f"Fr.Present({self.data(fields[i][1])}, {fields[i][0]})" for i in opts) + "]"
            inner = f"Ap.Bits.write({bm}, {r0}, {inner})"
        if t.ext:
            inner = f"Ap.Bit.write(False{{}}, rem, {inner})"
        self.out(f"      {inner}")
        self.out()
        self.out(f"def {b}.after(x: {b}, +rem: Nat) -> Nat:")
        self.out("  match x:")
        self.out("    case " + b + "{" + ", ".join(names) + "}:")
        if k > 0:
            self.out(f"      +r0 = Ap.Bits.after({k}n, {r0})")
        else:
            self.out(f"      +r0 = {r0}")
        for i in range(m):
            fn, ft, o = fields[i]
            aft = f"{b}.a_{fn}({fn}, r{i})" if o else self.after(ft, fn, f"r{i}")
            self.out(f"      +r{i + 1} = {aft}")
        self.out(f"      r{m}")
        self.out()

    def ftype(self, ft, optional):
        d = self.data(ft)
        return f"Maybe<&2, {d}>" if optional else d

    def conj(self, terms):
        if not terms:
            return "True{}"
        if len(terms) == 1:
            return terms[0]
        return f"Bool.and({terms[0]}, {self.conj(terms[1:])})"

    def emit_choice(self, t):
        b = t.bend
        alts = t.alts
        count = len(alts)
        n, diff = bitlen(count - 1), count - 1
        self.out(f"# {t.name} ::= {M.render(M.find(t.name)) if self.is_named(t.name) else 'CHOICE'}")
        self.out(f"type {b} is Data:")
        for an, at in alts:
            self.out(f"  {b}_{an}{{v: {self.data(at)}}}")
        self.out()
        self.out(f"def {b}.valid(x: {b}) -> Bool:")
        self.out("  match x:")
        for an, at in alts:
            self.out(f"    case {b}_{an}{{v}}:")
            self.out(f"      {self.valid(at, 'v')}")
        self.out()
        for an, at in alts:
            self.out(f"def {b}.c_{an}(r: Ap.Rd({self.data(at)})) -> Ap.Rd({b}):")
            self.out("  match r:")
            self.out("    case Fail{e}:")
            self.out("      Fail{e}")
            self.out("    case Done{(v, c)}:")
            self.out(f"      Done{{({b}_{an}{{v}}, c)}}")
            self.out()
        self.out(f"def {b}.alt(i: Nat, c: Ap.Cur) -> Ap.Rd({b}):")
        self.out("  match i:")
        for j, (an, at) in enumerate(alts):
            self.out(f"    case {j}n:")
            self.out(f"      {b}.c_{an}({self.read(at, 'c')})")
        self.out(f"    case {count}n+p:")
        self.out("      Fail{B.Invalid{0}}")
        self.out()
        self.out(f"def {b}.r_idx(r: Ap.Rd(U32)) -> Ap.Rd({b}):")
        self.out("  match r:")
        self.out("    case Fail{e}:")
        self.out("      Fail{e}")
        self.out("    case Done{(i, c)}:")
        self.out(f"      {b}.alt(U32.to_nat(i), c)")
        self.out()
        body = f"{b}.r_idx(Ap.Int.read({n}n, {diff}, c))"
        if t.ext:
            self.out(f"def {b}.r_ext(r: Ap.Rd(Bool)) -> Ap.Rd({b}):")
            self.out("  match r:")
            self.out("    case Fail{e}:")
            self.out("      Fail{e}")
            self.out("    case Done{(ext, c)}:")
            self.out("      match ext:")
            self.out("        case True{}:")
            self.out("          Fail{B.Unsupported{1}}")
            self.out("        case False{}:")
            self.out(f"          {body}")
            self.out()
            body = f"{b}.r_ext(Ap.Bit.read(c))"
        self.out(f"def {b}.read(c: Ap.Cur) -> Ap.Rd({b}):")
        self.out(f"  {body}")
        self.out()
        r0 = "Ap.Bit.after(rem)" if t.ext else "rem"
        self.out(f"def {b}.write(x: {b}, +rem: Nat, +rest: Ap.Bits()) -> Ap.Bits():")
        self.out("  match x:")
        for j, (an, at) in enumerate(alts):
            self.out(f"    case {b}_{an}{{+v}}:")
            inner = f"Ap.Int.write({n}n, {j}, {r0}, {self.write(at, 'v', f'Ap.Int.after({n}n, {r0})', 'rest')})"
            if t.ext:
                inner = f"Ap.Bit.write(False{{}}, rem, {inner})"
            self.out(f"      {inner}")
        self.out()
        self.out(f"def {b}.after(x: {b}, +rem: Nat) -> Nat:")
        self.out("  match x:")
        for an, at in alts:
            self.out(f"    case {b}_{an}{{v}}:")
            self.out(f"      {self.after(at, 'v', f'Ap.Int.after({n}n, {r0})')}")
        self.out()

    def emit_list(self, t):
        b, item = t.bend, t.item
        al, n, lo, diff = t.args
        d = self.data(item)
        self.out(f"# {t.name} ::= {M.render(M.find(t.name)) if self.is_named(t.name) else 'SEQUENCE OF'}")
        self.out(f"def {b}() -> Data:")
        self.out(f"  List<&2, {d}>")
        self.out()
        self.out(f"def {b}.all_valid(xs: {b}()) -> Bool:")
        self.out("  match xs:")
        self.out("    case Nil{}:")
        self.out("      True{}")
        self.out("    case x <> more:")
        self.out(f"      Bool.and({self.valid(item, 'x')}, {b}.all_valid(more))")
        self.out()
        self.out(f"def {b}.valid(+xs: {b}()) -> Bool:")
        self.out(f"  Bool.and(Ap.Size.valid({lo}n, {diff}n, List.length(&2, {d}, xs)), {b}.all_valid(xs))")
        self.out()
        self.out(f"def {b}.cons(x: {d}, r: Ap.Rd({b}())) -> Ap.Rd({b}()):")
        self.out("  match r:")
        self.out("    case Fail{e}:")
        self.out("      Fail{e}")
        self.out("    case Done{(xs, c)}:")
        self.out("      Done{(x <> xs, c)}")
        self.out()
        self.out(f"def {b}.next(r: Ap.Rd({d}), more: Ap.Cur -> Ap.Rd({b}())) -> Ap.Rd({b}()):")
        self.out("  match r:")
        self.out("    case Fail{e}:")
        self.out("      Fail{e}")
        self.out("    case Done{(x, c)}:")
        self.out(f"      {b}.cons(x, more(c))")
        self.out()
        self.out(f"def {b}.items(n: Nat, c: Ap.Cur) -> Ap.Rd({b}()):")
        self.out("  match n:")
        self.out("    case 0n:")
        self.out("      Done{([], c)}")
        self.out("    case 1n+p:")
        self.out(f"      {b}.next({self.read(item, 'c')}, c2 => {b}.items(p, c2))")
        self.out()
        self.out(f"def {b}.count(r: Ap.Rd(Nat)) -> Ap.Rd({b}()):")
        self.out("  match r:")
        self.out("    case Fail{e}:")
        self.out("      Fail{e}")
        self.out("    case Done{(n, c)}:")
        self.out(f"      {b}.items(n, c)")
        self.out()
        self.out(f"def {b}.read(c: Ap.Cur) -> Ap.Rd({b}()):")
        self.out(f"  {b}.count(Ap.Size.read({al}, {n}n, {lo}n, {diff}n, c))")
        self.out()
        self.out(f"def {b}.items_write(xs: {b}(), +rem: Nat, +rest: Ap.Bits()) -> Ap.Bits():")
        self.out("  match xs:")
        self.out("    case Nil{}:")
        self.out("      rest")
        self.out("    case +x <> more:")
        self.out(f"      {self.write(item, 'x', 'rem', f'{b}.items_write(more, {self.after(item, 'x', 'rem')}, rest)')}")
        self.out()
        self.out(f"def {b}.write(+xs: {b}(), +rem: Nat, +rest: Ap.Bits()) -> Ap.Bits():")
        self.out(f"  Ap.Size.write({al}, {n}n, {lo}n, List.length(&2, {d}, xs), rem, {b}.items_write(xs, Ap.Size.after({al}, {n}n, rem), rest))")
        self.out()
        self.out(f"def {b}.items_after(xs: {b}(), +rem: Nat) -> Nat:")
        self.out("  match xs:")
        self.out("    case Nil{}:")
        self.out("      rem")
        self.out("    case x <> more:")
        self.out(f"      {b}.items_after(more, {self.after(item, 'x', 'rem')})")
        self.out()
        self.out(f"def {b}.after(+xs: {b}(), +rem: Nat) -> Nat:")
        self.out(f"  {b}.items_after(xs, Ap.Size.after({al}, {n}n, rem))")
        self.out()

    def emit_dispatch(self):
        """Per-message IE check used by the tests: does the value of a known IE id roundtrip?"""
        names = M.ie_names()
        for msg, rows in sorted(self.messages.items()):
            b = self.types[msg].bend
            self.out(f"def {b}.ie_check(id: Nat, +value: B.Bytes()) -> Maybe<&2, Bool>:")
            self.out("  match id:")
            seen = set()
            for row in rows:
                tname = M.ref_name(M.row_type(row))
                if tname is None or tname not in self.types or row["id"] in seen:
                    continue
                seen.add(row["id"])
                self.out(f"    case {row['id']}n:")
                self.out(f"      Some{{{self.types[tname].bend}.roundtrips(value)}}")
            self.out("    case _:")
            self.out("      None{}")
            self.out()
        self.out("def Ie.check(msg: String, id: Nat, +value: B.Bytes()) -> Maybe<&2, Bool>:")
        self.out("  match msg:")
        for msg in sorted(self.messages):
            self.out(f'    case "{msg}":')
            self.out(f"      {self.types[msg].bend}.ie_check(id, value)")
        self.out("    case _:")
        self.out("      None{}")
        self.out()


    # -- message views ----------------------------------------------------------

    def field_name(self, names, row):
        base = names.get(row["id"], f"ie{row['id']}")
        base = base[3:] if base.startswith("id-") else base
        return bname(base).lower()

    def view_rows(self, msg):
        names = M.ie_names()
        rows = []
        for row in self.messages[msg]:
            tname = M.ref_name(M.row_type(row))
            if tname is None or tname not in self.types:
                continue
            rows.append((row["id"], self.field_name(names, row), tname, row["presence"] == "mandatory"))
        return rows

    def emit_views(self):
        self.lines = []
        o = self.out
        o("import Base")
        o("import ../../bytes.bend as B")
        o("import ../../aper.bend as Ap")
        o("import ../frame.bend as Fr")
        o("import ./types.bend as G")
        o()
        o("# GENERATED by tools/ngap-gen/gen.py from TS 38.413 V17.15.0; do not edit.")
        o("# One view per message (its object set): mandatory IEs are plain fields,")
        o("# optional ones Maybe. A view succeeds only past Fr.View.prelude (no")
        o("# duplicate id, every reject IE comprehended) and with every mandatory IE")
        o("# present, each value a complete encoding of its type.")
        o()
        for msg in sorted(self.messages):
            mb = self.types[msg].bend
            rows = self.view_rows(msg)
            n = len(rows)
            o(f"# {msg}")
            o(f"type {mb}.View is Data:")
            o(f"  {mb}.View{{" + ", ".join(f"{fn}: {self.gdata(tn, mand)}" for _, fn, tn, mand in rows) + "}")
            o()
            o(f"def {mb}.known() -> List<&2, U32>:")
            o("  [" + ", ".join(str(i) for i, _, _, _ in rows) + "]")
            o()
            fields = [fn for _, fn, _, _ in rows]

            def nxt(i, exprs):
                if i == n:
                    return f"Done{{{mb}.View{{" + ", ".join(exprs) + "}}"
                return f"{mb}.v_{fields[i]}({', '.join(['ies'] + exprs + [f'Fr.Ies.lookup({rows[i][0]}, ies)'])})"

            for i in reversed(range(n)):
                iid, fn, tn, mand = rows[i]
                d = self.gdata(tn, True)
                prev = [f"{fields[j]}: {self.gdata(rows[j][2], rows[j][3])}" for j in range(i)]
                o(f"def {mb}.d_{fn}({', '.join(['+ies: List<&2, Fr.Ie>'] + prev + [f'r: Result<&2, &2, B.Err, {d}>'])}) -> Result<&2, &2, B.Err, {mb}.View>:")
                o("  match r:")
                o("    case Fail{e}:")
                o("      Fail{e}")
                o(f"    case Done{{{fn}}}:")
                o(f"      {nxt(i + 1, fields[:i] + [fn if mand else 'Some{' + fn + '}'])}")
                o()
                o(f"def {mb}.v_{fn}({', '.join(['+ies: List<&2, Fr.Ie>'] + prev + ['m: Maybe<&2, B.Bytes()>'])}) -> Result<&2, &2, B.Err, {mb}.View>:")
                o("  match m:")
                o("    case None{}:")
                if mand:
                    o(f"      Fail{{B.Invalid{{{iid}}}}}")
                else:
                    o(f"      {nxt(i + 1, fields[:i] + ['None{}'])}")
                o("    case Some{bs}:")
                o(f"      {mb}.d_{fn}({', '.join(['ies'] + fields[:i] + [f'Fr.View.exact({d}, G.{self.types[tn].bend}.read(Ap.Cur{{0n, Ap.unpack(bs)}}))'])})")
                o()
            o(f"def {mb}.v_prelude(r: Result<&2, &2, B.Err, List<&2, Fr.Ie>>) -> Result<&2, &2, B.Err, {mb}.View>:")
            o("  match r:")
            o("    case Fail{e}:")
            o("      Fail{e}")
            o("    case Done{+ies}:")
            o(f"      {nxt(0, [])}")
            o()
            o(f"def {mb}.view(ies: List<&2, Fr.Ie>) -> Result<&2, &2, B.Err, {mb}.View>:")
            o(f"  {mb}.v_prelude(Fr.View.prelude({mb}.known(), ies))")
            o()
        o("# Whether the named message's view accepts a container (for the tests).")
        o("def View.check(msg: String, ies: List<&2, Fr.Ie>) -> Maybe<&2, Bool>:")
        o("  match msg:")
        for msg in sorted(self.messages):
            mb = self.types[msg].bend
            o(f'    case "{msg}":')
            o(f"      Some{{Bool.not(Result.is_fail(&2, &2, B.Err, {mb}.View, {mb}.view(ies)))}}")
        o("    case _:")
        o("      None{}")
        return "\n".join(self.lines).rstrip() + "\n"

    def gdata(self, tname, mandatory):
        t = self.types[tname]
        d = f"G.{t.bend}" if t.kind in ("record", "choice") else f"G.{t.bend}()"
        return d if mandatory else f"Maybe<&2, {d}>"


def main():
    asn, out = sys.argv[1], pathlib.Path(sys.argv[2])
    M.compile_dir(asn)
    g = Gen()
    for name in M.closure(M.MESSAGES + M.TRANSFERS, "R"):
        g.visit(name, M.find(name))
    g.out("import Base")
    g.out("import ../../bytes.bend as B")
    g.out("import ../../aper.bend as Ap")
    g.out("import ../frame.bend as Fr")
    g.out()
    g.out("# GENERATED by tools/ngap-gen/gen.py from TS 38.413 V17.15.0; do not edit.")
    g.out("# Every type of the milestone message set (tiers M and R): its datatype,")
    g.out("# `read`, `write`, `after` and `valid`, on the APER primitives.")
    g.out()
    g.emit_all()
    g.emit_dispatch()
    out.mkdir(parents=True, exist_ok=True)
    (out / "types.bend").write_text("\n".join(g.lines).rstrip() + "\n")
    (out / "views.bend").write_text(g.emit_views())
    proofs = gen_proofs.Proofs(g)
    (out / "laws.bend").write_text(proofs.laws())
    (out / "proofs.bend").write_text(proofs.proofs())
    (out / "show.bend").write_text(gen_show.Show(g).show())
    print(f"{len(g.types)} types, {len(g.messages)} views, laws, proofs and show -> {out}")


if __name__ == "__main__":
    main()
