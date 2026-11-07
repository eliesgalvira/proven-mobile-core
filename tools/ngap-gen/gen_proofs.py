"""Emit the laws and proof terms for every generated NGAP type.

laws.bend states ngap.<T>.roundtrip, ngap.<T>.decode_valid and ngap.<T>.suffix
for each type; proofs.bend fills them by composing the APER primitive laws
(kernel/LAWS.bend, proven in kernel/proofs/aper.bend and canon.bend) along
the shape of the generated codec: aliases defer to one primitive law, records
go field by field, choices by alternative, lists by induction on the items.
"""

HEADER = """import Base
import ../../bytes.bend as B
import ../../aper.bend as Ap
import ../frame.bend as Fr
import ./types.bend as G
"""

PROOF_HEADER = HEADER + """import ./laws.bend as GL
import ../../LAWS.bend as L
import ../../proofs/lib.bend as P
import ../../proofs/aper.bend as PA
import ../../proofs/canon.bend as PC
import ../../proofs/ngap_frame.bend as PF
"""

PRIM_LAWS = {
    "Int": "int", "AInt": "aint", "Big": "big", "XInt": "xint", "XBig": "xbig", "Enum": "enum",
    "XBits": "xbits", "BitStr": "bitstr", "XBitStr": "xbitstr", "UBitStr": "ubitstr",
    "OctStr": "octstr", "Open": "open", "Str": "str", "XStr": "xstr", "UStr": "ustr",
}
NEEDS_WIDTH = {"Big", "XBig", "BitStr", "XBitStr", "OctStr", "Str", "XStr"}
FIXED = {"Bits", "ABits", "Octets", "AOctets"}
WORD = {"Int", "AInt", "XInt", "Enum"}
CUR_ARGS = "rem, bits, v, rem2, bits2, e"


def prim_prefix(t):
    a, p = t.args, t.prim
    if p in ("Int", "AInt"):
        return f"{a[0]}n, {a[1]}"
    if p in ("Big", "XBig"):
        return f"{a[0]}n, {a[1]}n"
    if p == "XInt":
        return f"{a[0]}, {a[1]}n, {a[2]}"
    if p == "Enum":
        return f"{a[0]}n, {a[1]}, {a[2]}"
    if p in ("XBits", "Bits", "ABits", "Octets", "AOctets"):
        return f"{a[0]}n"
    if p in ("BitStr", "XBitStr", "OctStr", "Str", "XStr"):
        return f"{a[0]}, {a[1]}n, {a[2]}n, {a[3]}n"
    return ""


def cur_eq(d, read, v="v"):
    """The hypothesis of a suffix law: a reader answered v and a cursor."""
    return f"{{{read} == Done{{({v}, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({d})}}"


class Proofs:
    def __init__(self, g):
        self.g = g
        self.lines = []

    def out(self, text=""):
        self.lines.append(text)

    # -- names on the proof side ----------------------------------------------

    def data(self, name):
        if name == "EXTS":
            return "List<&2, Fr.Ie>"
        if name == "IE":
            return "Fr.Ie"
        return "G." + self.g.data(name)

    def read(self, name, c):
        return self.pre(name) + self.g.read(name, c)

    def write(self, name, v, rem, rest):
        return self.pre(name) + self.g.write(name, v, rem, rest)

    def after(self, name, v, rem):
        return self.pre(name) + self.g.after(name, v, rem)

    def valid(self, name, v):
        return self.pre(name) + self.g.valid(name, v)

    def pre(self, name):
        return "" if name in ("EXTS", "IE") else "G."

    def law(self, name):
        if name in ("EXTS", "IE"):
            return "L.ngap." + name.lower()
        return f"GL.ngap.{self.g.types[name].bend}"

    def rt_law(self, name, v, rem, rest, ok):
        return f"{self.law(name)}.roundtrip({v}, {rem}, {rest}, {ok})"

    def dv_law(self, name, c, v, c2, e):
        return f"{self.law(name)}.decode_valid({c}, {v}, {c2}, {e})"

    def sx_law(self, name, r, b, v, r3, b3, e):
        if name in ("EXTS", "IE"):
            return f"PF.{'Exts' if name == 'EXTS' else 'Ie'}.sx({r}, {b}, {v}, {r3}, {b3}, {e})"
        return f"{self.law(name)}.suffix({r}, {b}, {v}, {r3}, {b3}, {e})"

    def canon(self, name, b, v, r, b3, r3):
        """The type a suffix law gives: bits b are the value's wire form before b3, and r3 follows."""
        return f"{{{b} == {self.write(name, v, r, b3)} : Ap.Bits()}} & {{{r3} == {self.after(name, v, r)} : Nat}}"

    def absurd(self, d, goal, err):
        return f"PA.Rd.absurd({d}, {goal}, {err}, v, c2, e)"

    def absurd_sx(self, d, goal, err):
        return f"PA.Rd.absurd({d}, {goal}, {err}, v, Ap.Cur{{rem2, bits2}}, e)"

    def value_eq(self, d, found):
        """ev: the value a reader answered equals the one the hypothesis names."""
        return f"Equal.cong(Ap.Rd({d}), {d}, y => PA.Rd.value({d}, y, v), Done{{({found}, c3)}}, Done{{(v, c2)}}, e)"

    def cursor_eqs(self, d, found):
        """ev, ec, eb, er from e: Done{(found, Cur{r3, b3})} == Done{(v, Cur{rem2, bits2})}."""
        pair = f"Done{{({found}, Ap.Cur{{r3, b3}})}}, Done{{(v, Ap.Cur{{rem2, bits2}})}}, e"
        return [
            f"ev = Equal.cong(Ap.Rd({d}), {d}, y => PA.Rd.value({d}, y, v), {pair})",
            f"+ec = Equal.cong(Ap.Rd({d}), Ap.Cur, y => PA.Rd.cur({d}, y, Ap.Cur{{rem2, bits2}}), {pair})",
            "eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)",
            "er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)",
        ]

    # -- laws ------------------------------------------------------------------

    def laws(self):
        self.lines = [HEADER]
        self.out("# GENERATED by tools/ngap-gen/gen.py from TS 38.413 V17.15.0; do not edit.")
        self.out("# The standard codec laws (docs/spec/milestone-1.md § Laws) for every")
        self.out("# generated type; kernel/ngap/gen/proofs.bend proves them. `suffix` is")
        self.out("# canonical decoding: the bits a value was read from are its encoding.")
        self.out()
        for name in self.g.order:
            t = self.g.types[name]
            b, d = t.bend, self.data(name)
            self.out(f"law ngap.{b}.roundtrip:")
            self.out(f"  for +v: {d}")
            self.out("  for +rem: Nat")
            self.out("  for +rest: Ap.Bits()")
            self.out(f"  for +ok: {{G.{b}.valid(v) == True{{}} : Bool}}")
            self.out(f"  {{G.{b}.read(Ap.Cur{{rem, G.{b}.write(v, rem, rest)}}) == Done{{(v, Ap.Cur{{G.{b}.after(v, rem), rest}})}} : Ap.Rd({d})}}")
            self.out()
            self.out(f"law ngap.{b}.decode_valid:")
            self.out("  for +c: Ap.Cur")
            self.out(f"  for +v: {d}")
            self.out("  for +c2: Ap.Cur")
            self.out(f"  for +e: {{G.{b}.read(c) == Done{{(v, c2)}} : Ap.Rd({d})}}")
            self.out(f"  {{G.{b}.valid(v) == True{{}} : Bool}}")
            self.out()
            self.out(f"law ngap.{b}.suffix:")
            self.out("  for +rem: Nat")
            self.out("  for +bits: Ap.Bits()")
            self.out(f"  for +v: {d}")
            self.out("  for +rem2: Nat")
            self.out("  for +bits2: Ap.Bits()")
            self.out(f"  for +e: {cur_eq(d, f'G.{b}.read(Ap.Cur{{rem, bits}})')}")
            self.out(f"  {self.canon(name, 'bits', 'v', 'rem', 'bits2', 'rem2')}")
            self.out()
        return "\n".join(self.lines).rstrip() + "\n"

    # -- proofs ----------------------------------------------------------------

    def proofs(self):
        self.lines = [PROOF_HEADER]
        self.out("# GENERATED by tools/ngap-gen/gen.py from TS 38.413 V17.15.0; do not edit.")
        self.out("# Proofs of kernel/ngap/gen/laws.bend, composed from the APER primitive laws.")
        self.out()
        done = set()

        def emit(name):
            if name in done:
                return
            done.add(name)
            t = self.g.types[name]
            for d in t.deps:
                emit(d)
            self.emit_sx_type(t)
            getattr(self, "emit_" + t.kind)(t)

        for name in self.g.order:
            emit(name)
        return "\n".join(self.lines).rstrip() + "\n"

    def emit_sx_type(self, t):
        self.out(f"def {t.bend}.Sx(+bits: Ap.Bits(), +v: {self.data(t.name)}, +rem: Nat, rem2: Nat, bits2: Ap.Bits()) -> Type:")
        self.out(f"  {self.canon(t.name, 'bits', 'v', 'rem', 'bits2', 'rem2')}")
        self.out()

    def emit_alias(self, t):
        b = t.bend
        pre = prim_prefix(t)
        pre = pre + ", " if pre else ""
        if t.prim in FIXED:
            rt = f"PA.{t.prim}.rt_n({pre}v, rem, rest, ok)"
            dv = f"PA.{t.prim}.dv_n({pre}c, v, c2, e)"
            sx = f"PC.{t.prim}.sx_n({pre}{CUR_ARGS})"
        else:
            width = ", {==}" if t.prim in NEEDS_WIDTH else ""
            rt = f"L.aper.{PRIM_LAWS[t.prim]}.roundtrip({pre}v, rem, rest, ok{width})"
            dv = f"L.aper.{PRIM_LAWS[t.prim]}.decode_valid({pre}c, v, c2, e)"
            sx = f"PC.{t.prim}.sx({pre}{CUR_ARGS}{', {==}' if t.prim in WORD else ''})"
        self.out(f"def GL.ngap.{b}.roundtrip(v, rem, rest, ok):")
        self.out(f"  {rt}")
        self.out()
        self.out(f"def GL.ngap.{b}.decode_valid(c, v, c2, e):")
        self.out(f"  {dv}")
        self.out()
        self.out(f"def GL.ngap.{b}.suffix({CUR_ARGS}):")
        self.out(f"  {sx}")
        self.out()

    def emit_message(self, t):
        b = t.bend
        gb = f"G.{b}"
        d = f"{gb}()"
        goal = f"{{{gb}.valid(v) == True{{}} : Bool}}"
        self.out(f"def GL.ngap.{b}.roundtrip(v, rem, rest, ok):")
        self.out("  L.ngap.ies.roundtrip(v, Ap.Bit.after(rem), rest, ok)")
        self.out()
        self.out(f"def {b}.dv(rb: Ap.Rd(Bool), +v: {d}, +c2: Ap.Cur, +e: {{{gb}.r_ext(rb) == Done{{(v, c2)}} : Ap.Rd({d})}}) -> {goal}:")
        self.out("  match rb:")
        self.out("    case Fail{err}:")
        self.out(f"      {self.absurd(d, goal, 'err')}")
        self.out("    case Done{(ext, c)}:")
        self.out("      match ext:")
        self.out("        case True{}:")
        self.out(f"          {self.absurd(d, goal, 'B.Unsupported{1}')}")
        self.out("        case False{}:")
        self.out("          L.ngap.ies.decode_valid(c, v, c2, e)")
        self.out()
        self.out(f"def GL.ngap.{b}.decode_valid(c, v, c2, e):")
        self.out(f"  {b}.dv(Ap.Bit.read(c), v, c2, e)")
        self.out()
        sx = f"{b}.Sx"
        self.out(f"def {b}.sx.go(+rem: Nat, +rest: Ap.Bits(), +v: {d}, +rem2: Nat, +bits2: Ap.Bits(), s: PC.Canon(rest, Fr.Ies.write(v, Ap.Bit.after(rem), bits2), rem2, 0n)) -> {sx}(False{{}} <> rest, v, rem, rem2, bits2):")
        self.out("  (s1, s2) = s")
        self.out("  (Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, rest, Fr.Ies.write(v, Ap.Bit.after(rem), bits2), s1), s2)")
        self.out()
        self.out(f"def {b}.sx(+rem: Nat, bits: Ap.Bits(), +v: {d}, +rem2: Nat, +bits2: Ap.Bits(), +e: {cur_eq(d, f'{gb}.read(Ap.Cur{{rem, bits}})')}) -> {sx}(bits, v, rem, rem2, bits2):")
        self.out("  match bits:")
        self.out("    case Nil{}:")
        self.out(f"      {self.absurd_sx(d, f'{sx}([], v, rem, rem2, bits2)', 'B.Short{}')}")
        self.out("    case b <> +rest:")
        self.out("      match b:")
        self.out("        case True{}:")
        self.out(f"          {self.absurd_sx(d, f'{sx}(True{{}} <> rest, v, rem, rem2, bits2)', 'B.Unsupported{1}')}")
        self.out("        case False{}:")
        self.out(f"          {b}.sx.go(rem, rest, v, rem2, bits2, PF.Ies.sx(Ap.Bit.after(rem), rest, v, rem2, bits2, e))")
        self.out()
        self.out(f"def GL.ngap.{b}.suffix({CUR_ARGS}):")
        self.out(f"  {b}.sx({CUR_ARGS})")
        self.out()

    def emit_ext(self, b, gb, body):
        """The extension-bit step of a record or choice reader, for decode_valid."""
        goal = f"{{{gb}.valid(v) == True{{}} : Bool}}"
        self.out(f"def {b}.dv_ext(rb: Ap.Rd(Bool), +v: {gb}, +c2: Ap.Cur, +e: {{{gb}.r_ext(rb) == Done{{(v, c2)}} : Ap.Rd({gb})}}) -> {goal}:")
        self.out("  match rb:")
        self.out("    case Fail{err}:")
        self.out(f"      {self.absurd(gb, goal, 'err')}")
        self.out("    case Done{(ext, +c)}:")
        self.out("      match ext:")
        self.out("        case True{}:")
        self.out(f"          {self.absurd(gb, goal, 'B.Unsupported{1}')}")
        self.out("        case False{}:")
        self.out(f"          {body}")
        self.out()

    def emit_sx_entry(self, t, body):
        """`T.sx` and the suffix filler: past the extension bit (if any), `body(r0, b0, bits)` continues
        at cursor (r0, b0) with the original bits named by `bits`."""
        b, gb = t.bend, f"G.{t.bend}"
        sx = f"{b}.Sx"
        if t.ext:
            self.out(f"def {b}.sx(+rem: Nat, bits: Ap.Bits(), +v: {gb}, +rem2: Nat, +bits2: Ap.Bits(), +e: {cur_eq(gb, f'{gb}.read(Ap.Cur{{rem, bits}})')}) -> {sx}(bits, v, rem, rem2, bits2):")
            self.out("  match bits:")
            self.out("    case Nil{}:")
            self.out(f"      {self.absurd_sx(gb, f'{sx}([], v, rem, rem2, bits2)', 'B.Short{}')}")
            self.out("    case b <> +rest:")
            self.out("      match b:")
            self.out("        case True{}:")
            self.out(f"          {self.absurd_sx(gb, f'{sx}(True{{}} <> rest, v, rem, rem2, bits2)', 'B.Unsupported{1}')}")
            self.out("        case False{}:")
            self.out(f"          {body('Ap.Bit.after(rem)', 'rest', 'False{} <> rest')}")
            self.out()
            self.out(f"def GL.ngap.{b}.suffix({CUR_ARGS}):")
            self.out(f"  {b}.sx({CUR_ARGS})")
        else:
            self.out(f"def GL.ngap.{b}.suffix({CUR_ARGS}):")
            self.out(f"  {body('rem', 'bits', 'bits')}")
        self.out()

    def emit_record(self, t):
        g = self.g
        b, fields = t.bend, t.fields
        gb = f"G.{b}"
        m = len(fields)
        names = [fn for fn, _, _ in fields]
        ctor = gb + "{" + ", ".join(names) + "}"
        opts = [i for i, (_, _, o) in enumerate(fields) if o]
        k = len(opts)
        goal = f"{{{gb}.valid(v) == True{{}} : Bool}}"

        def D(i):
            fn, ft, o = fields[i]
            return f"Maybe<&2, {self.data(ft)}>" if o else self.data(ft)

        def PF(i):
            fn, ft, o = fields[i]
            return f"Fr.Present({self.data(ft)}, {fn})"

        def READ(i, c, flag):
            fn, ft, o = fields[i]
            return f"{gb}.o_{fn}({flag(i)}, {c})" if o else self.read(ft, c)

        def WRITE(i, r, inner):
            fn, ft, o = fields[i]
            return f"{gb}.w_{fn}({fn}, {r}, {inner})" if o else self.write(ft, fn, r, inner)

        def AFTER(i, r):
            fn, ft, o = fields[i]
            return f"{gb}.a_{fn}({fn}, {r})" if o else self.after(ft, fn, r)

        def V(i):
            fn, ft, o = fields[i]
            return f"{gb}.v_{fn}({fn})" if o else self.valid(ft, fn)

        def REST(i):
            return g.conj([V(j) for j in range(i + 1, m)])

        def RT(i, r, inner, ok):
            fn, ft, o = fields[i]
            return f"{b}.o_rt_{fn}({fn}, {r}, {inner}, {ok})" if o else self.rt_law(ft, fn, r, inner, ok)

        def DV(i, c, c3, er):
            fn, ft, o = fields[i]
            return f"{b}.o_dv_{fn}(p_{fn}, {c}, {fn}, {c3}, {er})" if o else self.dv_law(ft, c, fn, c3, er)

        def SX(i, r, bi, r3, b3, er):
            fn, ft, o = fields[i]
            return f"{b}.o_sx_{fn}(p_{fn}, {r}, {bi}, {fn}, {r3}, {b3}, {er})" if o else self.sx_law(ft, r, bi, fn, r3, b3, er)

        pvar = lambda i: f"p_{fields[i][0]}"

        # optional fields: their own roundtrip, decode_valid and suffix
        for i in opts:
            fn, ft, _ = fields[i]
            d = self.data(ft)
            md = f"Maybe<&2, {d}>"
            vgoal = f"{{{gb}.v_{fn}(m) == True{{}} : Bool}}"
            self.out(f"def {b}.o_rt_{fn}(m: {md}, +r: Nat, +inner: Ap.Bits(), ok: {vgoal}) -> {{{gb}.o_{fn}(Fr.Present({d}, m), Ap.Cur{{r, {gb}.w_{fn}(m, r, inner)}}) == Done{{(m, Ap.Cur{{{gb}.a_{fn}(m, r), inner}})}} : Ap.Rd({md})}}:")
            self.out("  match m:")
            self.out("    case None{}:")
            self.out("      {==}")
            self.out("    case Some{+x}:")
            self.out(f"      e1 = Equal.sym(Ap.Rd({d}), {self.read(ft, f'Ap.Cur{{r, {self.write(ft, 'x', 'r', 'inner')}}}')}, Done{{(x, Ap.Cur{{{self.after(ft, 'x', 'r')}, inner}})}}, {self.rt_law(ft, 'x', 'r', 'inner', 'ok')})")
            self.out(f"      %e1 : {{{gb}.s_{fn}(_) == Done{{(Some{{x}}, Ap.Cur{{{self.after(ft, 'x', 'r')}, inner}})}} : Ap.Rd({md})}}")
            self.out("      {==}")
            self.out()
            self.out(f"def {b}.o_dv_{fn}.some(+c: Ap.Cur, r: Ap.Rd({d}), +er: {{{self.read(ft, 'c')} == r : Ap.Rd({d})}}, +m: {md}, +c2: Ap.Cur, +e: {{{gb}.s_{fn}(r) == Done{{(m, c2)}} : Ap.Rd({md})}}) -> {vgoal}:")
            self.out("  match r:")
            self.out("    case Fail{err}:")
            self.out(f"      PA.Rd.absurd({md}, {vgoal}, err, m, c2, e)")
            self.out("    case Done{(+x, +c3)}:")
            self.out(f"      ev = Equal.cong(Ap.Rd({md}), {md}, y => PA.Rd.value({md}, y, m), Done{{(Some{{x}}, c3)}}, Done{{(m, c2)}}, e)")
            self.out(f"      %ev : {{{gb}.v_{fn}(_) == True{{}} : Bool}}")
            self.out(f"      {self.dv_law(ft, 'c', 'x', 'c3', 'er')}")
            self.out()
            self.out(f"def {b}.o_dv_{fn}(p: Bool, +c: Ap.Cur, +m: {md}, +c2: Ap.Cur, +e: {{{gb}.o_{fn}(p, c) == Done{{(m, c2)}} : Ap.Rd({md})}}) -> {vgoal}:")
            self.out("  match p:")
            self.out("    case False{}:")
            self.out(f"      ev = Equal.cong(Ap.Rd({md}), {md}, y => PA.Rd.value({md}, y, m), Done{{(None{{}}, c)}}, Done{{(m, c2)}}, e)")
            self.out(f"      %ev : {{{gb}.v_{fn}(_) == True{{}} : Bool}}")
            self.out("      {==}")
            self.out("    case True{}:")
            self.out(f"      {b}.o_dv_{fn}.some(c, {self.read(ft, 'c')}, {{==}}, m, c2, e)")
            self.out()
            # suffix of an optional field: canon of w/a, and the presence bit is the one read
            ocanon = lambda pres: f"({{b == {gb}.w_{fn}(m, r, b3) : Ap.Bits()}} & {{r3 == {gb}.a_{fn}(m, r) : Nat}}) & {{{pres} == Fr.Present({d}, m) : Bool}}"
            self.out(f"def {b}.o_sx_{fn}.go(+r: Nat, +b: Ap.Bits(), +x: {d}, +r4: Nat, +b4: Ap.Bits(), +m: {md}, +r3: Nat, +b3: Ap.Bits(), +e: {{Done{{(Some{{x}}, Ap.Cur{{r4, b4}})}} == Done{{(m, Ap.Cur{{r3, b3}})}} : Ap.Rd({md})}}, s: {{b == {self.write(ft, 'x', 'r', 'b4')} : Ap.Bits()}} & {{r4 == {self.after(ft, 'x', 'r')} : Nat}}) -> {ocanon('True{}')}:")
            self.out("  (s1, s2) = s")
            self.out(f"  ev = Equal.cong(Ap.Rd({md}), {md}, y => PA.Rd.value({md}, y, m), Done{{(Some{{x}}, Ap.Cur{{r4, b4}})}}, Done{{(m, Ap.Cur{{r3, b3}})}}, e)")
            self.out(f"  +ec = Equal.cong(Ap.Rd({md}), Ap.Cur, y => PA.Rd.cur({md}, y, Ap.Cur{{r3, b3}}), Done{{(Some{{x}}, Ap.Cur{{r4, b4}})}}, Done{{(m, Ap.Cur{{r3, b3}})}}, e)")
            self.out("  eb = Equal.cong(Ap.Cur, Ap.Bits(), y => PA.Cur.bits(y), Ap.Cur{r4, b4}, Ap.Cur{r3, b3}, ec)")
            self.out("  er = Equal.cong(Ap.Cur, Nat, y => PA.Cur.rem(y), Ap.Cur{r4, b4}, Ap.Cur{r3, b3}, ec)")
            self.out(f"  %ev : ({{b == {gb}.w_{fn}(_, r, b3) : Ap.Bits()}} & {{r3 == {gb}.a_{fn}(_, r) : Nat}}) & {{True{{}} == Fr.Present({d}, _) : Bool}}")
            self.out(f"  (((%eb : {{b == {self.write(ft, 'x', 'r', '_')} : Ap.Bits()}}; s1), (%er : {{_ == {self.after(ft, 'x', 'r')} : Nat}}; s2)), {{==}})")
            self.out()
            self.out(f"def {b}.o_sx_{fn}.some(+r: Nat, +b: Ap.Bits(), rd: Ap.Rd({d}), +erd: {{{self.read(ft, 'Ap.Cur{r, b}')} == rd : Ap.Rd({d})}}, +m: {md}, +r3: Nat, +b3: Ap.Bits(), +e: {{{gb}.s_{fn}(rd) == Done{{(m, Ap.Cur{{r3, b3}})}} : Ap.Rd({md})}}) -> {ocanon('True{}')}:")
            self.out("  match rd:")
            self.out("    case Fail{err}:")
            self.out(f"      PA.Rd.absurd({md}, {ocanon('True{}')}, err, m, Ap.Cur{{r3, b3}}, e)")
            self.out("    case Done{(+x, c4)}:")
            self.out("      match c4:")
            self.out("        case Ap.Cur{+r4, +b4}:")
            self.out(f"          {b}.o_sx_{fn}.go(r, b, x, r4, b4, m, r3, b3, e, {self.sx_law(ft, 'r', 'b', 'x', 'r4', 'b4', 'erd')})")
            self.out()
            self.out(f"def {b}.o_sx_{fn}(p: Bool, +r: Nat, +b: Ap.Bits(), +m: {md}, +r3: Nat, +b3: Ap.Bits(), +e: {{{gb}.o_{fn}(p, Ap.Cur{{r, b}}) == Done{{(m, Ap.Cur{{r3, b3}})}} : Ap.Rd({md})}}) -> {ocanon('p')}:")
            self.out("  match p:")
            self.out("    case False{}:")
            self.out(f"      ev = Equal.cong(Ap.Rd({md}), {md}, y => PA.Rd.value({md}, y, m), Done{{(None{{}}, Ap.Cur{{r, b}})}}, Done{{(m, Ap.Cur{{r3, b3}})}}, e)")
            self.out(f"      +ec = Equal.cong(Ap.Rd({md}), Ap.Cur, y => PA.Rd.cur({md}, y, Ap.Cur{{r3, b3}}), Done{{(None{{}}, Ap.Cur{{r, b}})}}, Done{{(m, Ap.Cur{{r3, b3}})}}, e)")
            self.out(f"      %ev : ({{b == {gb}.w_{fn}(_, r, b3) : Ap.Bits()}} & {{r3 == {gb}.a_{fn}(_, r) : Nat}}) & {{False{{}} == Fr.Present({d}, _) : Bool}}")
            self.out("      ((Equal.cong(Ap.Cur, Ap.Bits(), y => PA.Cur.bits(y), Ap.Cur{r, b}, Ap.Cur{r3, b3}, ec), Equal.sym(Nat, r, r3, Equal.cong(Ap.Cur, Nat, y => PA.Cur.rem(y), Ap.Cur{r, b}, Ap.Cur{r3, b3}, ec))), {==})")
            self.out("    case True{}:")
            self.out(f"      {b}.o_sx_{fn}.some(r, b, {self.read(ft, 'Ap.Cur{r, b}')}, {{==}}, m, r3, b3, e)")
            self.out()

        # roundtrip: one rewrite per field along the reader chain
        r0 = "Ap.Bit.after(rem)" if t.ext else "rem"
        rems = [f"Ap.Bits.after({k}n, {r0})" if k else r0]
        for i in range(m):
            rems.append(AFTER(i, rems[i]))
        inner = ["rest"] * (m + 1)
        for i in reversed(range(m)):
            inner[i] = WRITE(i, rems[i], inner[i + 1])
        rhs = f"Done{{({ctor}, Ap.Cur{{{gb}.after({ctor}, rem), rest}})}}"
        params = [f"+{names[i]}: {D(i)}" for i in range(m)] + ["+rem: Nat", "+rest: Ap.Bits()", f"+ok: {{{gb}.valid({ctor}) == True{{}} : Bool}}"]
        self.out(f"def {b}.rt({', '.join(params)}) -> {{{gb}.read(Ap.Cur{{rem, {gb}.write({ctor}, rem, rest)}}) == {rhs} : Ap.Rd({gb})}}:")
        oks = []
        cur = "ok"
        for i in range(m - 1):
            self.out(f"  ok{i} = P.Bool.and_true_l({V(i)}, {REST(i)}, {cur})")
            self.out(f"  +okr{i} = P.Bool.and_true_r({V(i)}, {REST(i)}, {cur})")
            oks.append(f"ok{i}")
            cur = f"okr{i}"
        oks.append(cur)
        for i in range(m):
            fn = names[i]
            flags = [PF(j) for j in range(i + 1, m) if fields[j][2]]
            self.out(f"  e{i} = Equal.sym(Ap.Rd({D(i)}), {READ(i, f'Ap.Cur{{{rems[i]}, {inner[i]}}}', PF)}, Done{{({fn}, Ap.Cur{{{rems[i + 1]}, {inner[i + 1]}}})}}, {RT(i, rems[i], inner[i + 1], oks[i])})")
            self.out(f"  %e{i} : {{{gb}.r_{fn}({', '.join(flags + names[:i] + ['_'])}) == {rhs} : Ap.Rd({gb})}}")
        self.out("  {==}")
        self.out()
        self.out(f"def GL.ngap.{b}.roundtrip(v, rem, rest, ok):")
        self.out("  match v:")
        self.out(f"    case {ctor}:")
        self.out(f"      {b}.rt({', '.join(names + ['rem', 'rest', 'ok'])})")
        self.out()

        # decode_valid: evidence threaded through the reader chain, last field first
        def pflags(i):
            return [pvar(j) for j in range(i, m) if fields[j][2]]

        for i in reversed(range(m)):
            fn = names[i]
            params = [f"+{p}: Bool" for p in pflags(i)] + [f"+{names[j]}: {D(j)}" for j in range(i)]
            params += ["+c: Ap.Cur", f"r: Ap.Rd({D(i)})", f"+er: {{{READ(i, 'c', pvar)} == r : Ap.Rd({D(i)})}}", f"+v: {gb}", "+c2: Ap.Cur"]
            params.append(f"+e: {{{gb}.r_{fn}({', '.join(pflags(i + 1) + names[:i] + ['r'])}) == Done{{(v, c2)}} : Ap.Rd({gb})}}")
            params += [f"ok{j}: {{{V(j)} == True{{}} : Bool}}" for j in range(i)]
            self.out(f"def {b}.dv_{fn}({', '.join(params)}) -> {goal}:")
            self.out("  match r:")
            self.out("    case Fail{err}:")
            self.out(f"      {self.absurd(gb, goal, 'err')}")
            self.out(f"    case Done{{(+{fn}, +c3)}}:")
            if i < m - 1:
                args = pflags(i + 1) + names[: i + 1] + ["c3", READ(i + 1, "c3", pvar), "{==}", "v", "c2", "e"] + [f"ok{j}" for j in range(i)] + [DV(i, "c", "c3", "er")]
                self.out(f"      {b}.dv_{names[i + 1]}({', '.join(args)})")
            else:
                self.out(f"      ev = {self.value_eq(gb, ctor)}")
                self.out(f"      %ev : {{{gb}.valid(_) == True{{}} : Bool}}")
                terms = [f"ok{j}" for j in range(i)] + [DV(i, "c", "c3", "er")]
                conj = terms[-1]
                for j in reversed(range(m - 1)):
                    conj = f"P.Bool.and_intro({V(j)}, {REST(j)}, {terms[j]}, {conj})"
                self.out(f"      {conj}")
            self.out()

        def first(c):
            return f"{b}.dv_{names[0]}({', '.join(pflags(0) + [c, READ(0, c, pvar), '{==}', 'v', 'c2', 'e'])})"

        # The first field's presence bit is both passed on and read with when that field is optional.
        bm_pat = " <> ".join(("+" if i == 0 else "") + pvar(i) for i in opts) + " <> Nil{}"
        if k:
            self.out(f"def {b}.dv_bm(r: Ap.Rd(Ap.Bits()), +v: {gb}, +c2: Ap.Cur, +e: {{{gb}.r_bm(r) == Done{{(v, c2)}} : Ap.Rd({gb})}}) -> {goal}:")
            self.out("  match r:")
            self.out("    case Fail{err}:")
            self.out(f"      {self.absurd(gb, goal, 'err')}")
            self.out("    case Done{(bm, +c3)}:")
            self.out("      match bm:")
            self.out(f"        case {bm_pat}:")
            self.out(f"          {first('c3')}")
            for n in range(k):
                self.out("        case " + "".join(f"q{j} <> " for j in range(n)) + "Nil{}:")
                self.out(f"          {self.absurd(gb, goal, 'B.Short{}')}")
            self.out("        case " + "".join(f"q{j} <> " for j in range(k + 1)) + "more:")
            self.out(f"          {self.absurd(gb, goal, 'B.Short{}')}")
            self.out()
            body = f"{b}.dv_bm(Ap.Bits.read({k}n, c), v, c2, e)"
        else:
            body = first("c")
        if t.ext:
            self.emit_ext(b, gb, body)
            body = f"{b}.dv_ext(Ap.Bit.read(c), v, c2, e)"
        self.out(f"def GL.ngap.{b}.decode_valid(c, v, c2, e):")
        self.out(f"  {body}")
        self.out()

        # suffix: the bits before each field are the writes of the fields before it
        sx = f"{b}.Sx"
        sxgoal = f"{sx}(bits, v, rem, rem2, bits2)"
        r0p = "Ap.Bit.after(rem)" if t.ext else "rem"
        R = [f"Ap.Bits.after({k}n, {r0p})" if k else r0p]
        for i in range(m):
            R.append(AFTER(i, R[i]))

        def flag_at(i):
            """The preamble flag of optional field j as helper i knows it: read bit before, value after."""
            return lambda j: PF(j) if j < i else pvar(j)

        def prefix0(hole):
            return f"Ap.Bit.write(False{{}}, rem, {hole})" if t.ext else hole

        def prefix(i, hole, flag):
            """The original bits as the writes of fields before i around `hole` (the bits before field i)."""
            for j in reversed(range(i)):
                hole = WRITE(j, R[j], hole)
            if k:
                hole = f"Ap.Bits.write([{', '.join(flag(j) for j in opts)}], {r0p}, {hole})"
            return prefix0(hole)

        def sxparams(i):
            return [f"+{p}: Bool" for p in pflags(i)] + [f"+{names[j]}: {D(j)}" for j in range(i)] + ["+rem: Nat", "+bits: Ap.Bits()"]

        tail = f"+v: {gb}, +rem2: Nat, +bits2: Ap.Bits()"
        for i in reversed(range(m)):
            fn, ft, o = fields[i]
            flag = flag_at(i)
            pre_t = f"{{bits == {prefix(i, 'bi', flag)} : Ap.Bits()}}"
            pr_t = f"{{ri == {R[i]} : Nat}}"
            if i < m - 1:
                e_go = f"{{{gb}.r_{names[i + 1]}({', '.join(pflags(i + 2) + names[:i + 1] + [READ(i + 1, 'Ap.Cur{r3, b3}', pvar)])}) == Done{{(v, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({gb})}}"
            else:
                e_go = f"{{Done{{({ctor}, Ap.Cur{{r3, b3}})}} == Done{{(v, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({gb})}}"
            s_t = f"{{bi == {WRITE(i, 'ri', 'b3')} : Ap.Bits()}} & {{r3 == {AFTER(i, 'ri')} : Nat}}"
            if o:
                s_t = f"({s_t}) & {{p_{fn} == Fr.Present({self.data(ft)}, {fn}) : Bool}}"
            params = sxparams(i) + ["+ri: Nat", "+bi: Ap.Bits()", f"+{fn}: {D(i)}", "+r3: Nat", "+b3: Ap.Bits()", tail, f"+e: {e_go}", f"pre: {pre_t}", f"+pr: {pr_t}", f"s: {s_t}"]
            self.out(f"def {b}.sx_{fn}.go({', '.join(params)}) -> {sxgoal}:")
            if o:
                self.out("  (s12, s3) = s")
                self.out("  (s1, s2) = s12")
            else:
                self.out("  (s1, s2) = s")
            pre2 = f"(%pr : {{bits == {prefix(i, WRITE(i, '_', 'b3'), flag)} : Ap.Bits()}}; (%s1 : {{bits == {prefix(i, '_', flag)} : Ap.Bits()}}; pre))"
            if o:
                hole_flag = lambda j, i=i: PF(j) if j < i else ("_" if j == i else pvar(j))
                pre2 = f"(%s3 : {{bits == {prefix(i + 1, 'b3', hole_flag)} : Ap.Bits()}}; {pre2})"
            pr2 = f"(%pr : {{r3 == {AFTER(i, '_')} : Nat}}; s2)"
            if i < m - 1:
                args = pflags(i + 1) + names[: i + 1] + ["rem", "bits", "r3", "b3", READ(i + 1, "Ap.Cur{r3, b3}", pvar), "{==}", "v", "rem2", "bits2", "e", pre2, pr2]
                self.out(f"  {b}.sx_{names[i + 1]}({', '.join(args)})")
            else:
                for line in self.cursor_eqs(gb, ctor):
                    self.out(f"  {line}")
                self.out(f"  %ev : {sx}(bits, _, rem, rem2, bits2)")
                self.out(f"  ((%eb : {{bits == {prefix(m, '_', flag_at(m))} : Ap.Bits()}}; {pre2}), (%er : {{_ == {R[m]} : Nat}}; {pr2}))")
            self.out()
            params = sxparams(i) + ["+ri: Nat", "+bi: Ap.Bits()", f"r: Ap.Rd({D(i)})", f"+er: {{{READ(i, 'Ap.Cur{ri, bi}', pvar)} == r : Ap.Rd({D(i)})}}", tail]
            params.append(f"+e: {{{gb}.r_{fn}({', '.join(pflags(i + 1) + names[:i] + ['r'])}) == Done{{(v, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({gb})}}")
            params += [f"pre: {pre_t}", f"pr: {pr_t}"]
            self.out(f"def {b}.sx_{fn}({', '.join(params)}) -> {sxgoal}:")
            self.out("  match r:")
            self.out("    case Fail{err}:")
            self.out(f"      {self.absurd_sx(gb, sxgoal, 'err')}")
            self.out(f"    case Done{{(+{fn}, c3)}}:")
            self.out("      match c3:")
            self.out("        case Ap.Cur{+r3, +b3}:")
            args = pflags(i) + names[:i] + ["rem", "bits", "ri", "bi", fn, "r3", "b3", "v", "rem2", "bits2", "e", "pre", "pr", SX(i, "ri", "bi", "r3", "b3", "er")]
            self.out(f"          {b}.sx_{fn}.go({', '.join(args)})")
            self.out()

        def start(r1, b1, pre, pr):
            return f"{b}.sx_{names[0]}({', '.join(pflags(0) + ['rem', 'bits', r1, b1, READ(0, f'Ap.Cur{{{r1}, {b1}}}', pvar), '{==}', 'v', 'rem2', 'bits2', 'e', pre, pr])})"

        if k:
            flags = [pvar(i) for i in opts]
            bm = "[" + ", ".join(flags) + "]"
            s_t = f"PC.Canon(b0, Ap.Bits.write({bm}, r0, b1), r1, Ap.Bits.after({k}n, r0)) & {{List.length(&2, Bool, {bm}) == {k}n : Nat}}"
            e_go = f"{{{gb}.r_{names[0]}({', '.join(pflags(1) + [READ(0, 'Ap.Cur{r1, b1}', pvar)])}) == Done{{(v, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({gb})}}"
            params = ["+rem: Nat", "+bits: Ap.Bits()", "+r0: Nat", "+b0: Ap.Bits()"] + [f"+{p}: Bool" for p in flags] + ["+r1: Nat", "+b1: Ap.Bits()", tail, f"+e: {e_go}", f"pre: {{bits == {prefix0('b0')} : Ap.Bits()}}", f"+pr: {{r0 == {r0p} : Nat}}", f"s: {s_t}"]
            self.out(f"def {b}.sx_bm.go({', '.join(params)}) -> {sxgoal}:")
            self.out("  (cn, len) = s")
            self.out("  (s1, s2) = cn")
            pre2 = f"(%pr : {{bits == {prefix0(f'Ap.Bits.write({bm}, _, b1)')} : Ap.Bits()}}; (%s1 : {{bits == {prefix0('_')} : Ap.Bits()}}; pre))"
            pr2 = f"(%pr : {{r1 == Ap.Bits.after({k}n, _) : Nat}}; s2)"
            self.out(f"  {start('r1', 'b1', pre2, pr2)}")
            self.out()
            params = ["+rem: Nat", "+bits: Ap.Bits()", "+r0: Nat", "+b0: Ap.Bits()", "r: Ap.Rd(Ap.Bits())", f"+er: {{Ap.Bits.read({k}n, Ap.Cur{{r0, b0}}) == r : Ap.Rd(Ap.Bits())}}", tail, f"+e: {{{gb}.r_bm(r) == Done{{(v, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({gb})}}", f"pre: {{bits == {prefix0('b0')} : Ap.Bits()}}", f"pr: {{r0 == {r0p} : Nat}}"]
            self.out(f"def {b}.sx_bm({', '.join(params)}) -> {sxgoal}:")
            self.out("  match r:")
            self.out("    case Fail{err}:")
            self.out(f"      {self.absurd_sx(gb, sxgoal, 'err')}")
            self.out("    case Done{(bm, c1)}:")
            self.out("      match bm:")
            self.out("        case " + " <> ".join("+" + pvar(i) for i in opts) + " <> Nil{}:")
            self.out("          match c1:")
            self.out("            case Ap.Cur{+r1, +b1}:")
            self.out(f"              {b}.sx_bm.go({', '.join(['rem', 'bits', 'r0', 'b0'] + flags + ['r1', 'b1', 'v', 'rem2', 'bits2', 'e', 'pre', 'pr', f'PC.Bits.sx({k}n, r0, b0, {bm}, r1, b1, er)'])})")
            for n in range(k):
                self.out("        case " + "".join(f"q{j} <> " for j in range(n)) + "Nil{}:")
                self.out(f"          {self.absurd_sx(gb, sxgoal, 'B.Short{}')}")
            self.out("        case " + "".join(f"q{j} <> " for j in range(k + 1)) + "more:")
            self.out(f"          {self.absurd_sx(gb, sxgoal, 'B.Short{}')}")
            self.out()
            body = lambda r0, b0, bits: f"{b}.sx_bm(rem, {bits}, {r0}, {b0}, Ap.Bits.read({k}n, Ap.Cur{{{r0}, {b0}}}), {{==}}, v, rem2, bits2, e, {{==}}, {{==}})"
        else:
            body = lambda r0, b0, bits: f"{b}.sx_{names[0]}(rem, {bits}, {r0}, {b0}, {READ(0, f'Ap.Cur{{{r0}, {b0}}}', pvar)}, {{==}}, v, rem2, bits2, e, {{==}}, {{==}})"
        self.emit_sx_entry(t, body)

    def emit_choice(self, t):
        b, alts = t.bend, t.alts
        gb = f"G.{b}"
        count = len(alts)
        n, diff = (count - 1).bit_length(), count - 1
        goal = f"{{{gb}.valid(v) == True{{}} : Bool}}"
        r0 = "Ap.Bit.after(rem)" if t.ext else "rem"
        r1 = f"Ap.Size.after(False{{}}, {n}n, {r0})"
        size = f"False{{}}, {n}n, 0n, {diff}n"
        for j, (an, at) in enumerate(alts):
            d = self.data(at)
            val = f"{gb}_{an}{{x}}"
            rhs = f"Done{{({val}, Ap.Cur{{{gb}.after({val}, rem), rest}})}}"
            inner = self.write(at, "x", r1, "rest")
            self.out(f"def {b}.rt_{an}(+x: {d}, +rem: Nat, +rest: Ap.Bits(), +ok: {{{self.valid(at, 'x')} == True{{}} : Bool}}) -> {{{gb}.read(Ap.Cur{{rem, {gb}.write({val}, rem, rest)}}) == {rhs} : Ap.Rd({gb})}}:")
            self.out(f"  e1 = Equal.sym(Ap.Rd(Nat), Ap.Size.read({size}, Ap.Cur{{{r0}, Ap.Size.write(False{{}}, {n}n, 0n, {j}n, {r0}, {inner})}}), Done{{({j}n, Ap.Cur{{{r1}, {inner}}})}}, L.aper.size.roundtrip({size}, {j}n, {r0}, {inner}, {{==}}, {{==}}))")
            self.out(f"  %e1 : {{{gb}.r_idx(_) == {rhs} : Ap.Rd({gb})}}")
            self.out(f"  e2 = Equal.sym(Ap.Rd({d}), {self.read(at, f'Ap.Cur{{{r1}, {inner}}}')}, Done{{(x, Ap.Cur{{{self.after(at, 'x', r1)}, rest}})}}, {self.rt_law(at, 'x', r1, 'rest', 'ok')})")
            self.out(f"  %e2 : {{{gb}.c_{an}(_) == {rhs} : Ap.Rd({gb})}}")
            self.out("  {==}")
            self.out()
        self.out(f"def GL.ngap.{b}.roundtrip(v, rem, rest, ok):")
        self.out("  match v:")
        for an, at in alts:
            self.out(f"    case {gb}_{an}{{x}}:")
            self.out(f"      {b}.rt_{an}(x, rem, rest, ok)")
        self.out()
        for an, at in alts:
            d = self.data(at)
            self.out(f"def {b}.dv_{an}(+c: Ap.Cur, r: Ap.Rd({d}), +er: {{{self.read(at, 'c')} == r : Ap.Rd({d})}}, +v: {gb}, +c2: Ap.Cur, +e: {{{gb}.c_{an}(r) == Done{{(v, c2)}} : Ap.Rd({gb})}}) -> {goal}:")
            self.out("  match r:")
            self.out("    case Fail{err}:")
            self.out(f"      {self.absurd(gb, goal, 'err')}")
            self.out("    case Done{(+x, +c3)}:")
            self.out(f"      ev = {self.value_eq(gb, f'{gb}_{an}{{x}}')}")
            self.out(f"      %ev : {{{gb}.valid(_) == True{{}} : Bool}}")
            self.out(f"      {self.dv_law(at, 'c', 'x', 'c3', 'er')}")
            self.out()
        self.out(f"def {b}.dv_alt(i: Nat, +c: Ap.Cur, +v: {gb}, +c2: Ap.Cur, +e: {{{gb}.alt(i, c) == Done{{(v, c2)}} : Ap.Rd({gb})}}) -> {goal}:")
        self.out("  match i:")
        for j, (an, at) in enumerate(alts):
            self.out(f"    case {j}n:")
            self.out(f"      {b}.dv_{an}(c, {self.read(at, 'c')}, {{==}}, v, c2, e)")
        self.out(f"    case {count}n+p:")
        self.out(f"      {self.absurd(gb, goal, 'B.Invalid{0}')}")
        self.out()
        self.out(f"def {b}.dv_idx(r: Ap.Rd(Nat), +v: {gb}, +c2: Ap.Cur, +e: {{{gb}.r_idx(r) == Done{{(v, c2)}} : Ap.Rd({gb})}}) -> {goal}:")
        self.out("  match r:")
        self.out("    case Fail{err}:")
        self.out(f"      {self.absurd(gb, goal, 'err')}")
        self.out("    case Done{(i, c)}:")
        self.out(f"      {b}.dv_alt(i, c, v, c2, e)")
        self.out()
        body = f"{b}.dv_idx(Ap.Size.read({size}, c), v, c2, e)"
        if t.ext:
            self.emit_ext(b, gb, body)
            body = f"{b}.dv_ext(Ap.Bit.read(c), v, c2, e)"
        self.out(f"def GL.ngap.{b}.decode_valid(c, v, c2, e):")
        self.out(f"  {body}")
        self.out()

        # suffix
        sx = f"{b}.Sx"
        sxgoal = f"{sx}(bits, v, rem, rem2, bits2)"
        prefix0 = (lambda h: f"Ap.Bit.write(False{{}}, rem, {h})") if t.ext else (lambda h: h)
        tail = f"+v: {gb}, +rem2: Nat, +bits2: Ap.Bits()"
        pre_t = f"pre: {{bits == {prefix0('b0')} : Ap.Bits()}}"
        pr_t = f"pr: {{r0 == {r0} : Nat}}"
        for j, (an, at) in enumerate(alts):
            d = self.data(at)
            val = f"{gb}_{an}{{x}}"
            ss_t = f"ss: PC.Canon(b0, Ap.Size.write(False{{}}, {n}n, 0n, {j}n, r0, b1), r1, Ap.Size.after(False{{}}, {n}n, r0))"
            w = lambda r, rest: self.write(at, "x", r, rest)
            sw = lambda r, inner: f"Ap.Size.write(False{{}}, {n}n, 0n, {j}n, {r}, {inner})"
            sa = lambda r: f"Ap.Size.after(False{{}}, {n}n, {r})"
            self.out(f"def {b}.sx_{an}.go(+rem: Nat, +bits: Ap.Bits(), +r0: Nat, +b0: Ap.Bits(), +r1: Nat, +b1: Ap.Bits(), +x: {d}, +r3: Nat, +b3: Ap.Bits(), {tail}, +e: {{Done{{({val}, Ap.Cur{{r3, b3}})}} == Done{{(v, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({gb})}}, {pre_t}, +{pr_t}, {ss_t}, s: {{b1 == {w('r1', 'b3')} : Ap.Bits()}} & {{r3 == {self.after(at, 'x', 'r1')} : Nat}}) -> {sxgoal}:")
            self.out("  (ss1, +ss2) = ss")
            self.out("  (s1, s2) = s")
            for line in self.cursor_eqs(gb, val):
                self.out(f"  {line}")
            self.out(f"  %ev : {sx}(bits, _, rem, rem2, bits2)")
            steps = f"(%ss1 : {{bits == {prefix0('_')} : Ap.Bits()}}; pre)"
            steps = f"(%s1 : {{bits == {prefix0(sw('r0', '_'))} : Ap.Bits()}}; {steps})"
            steps = f"(%eb : {{bits == {prefix0(sw('r0', w('r1', '_')))} : Ap.Bits()}}; {steps})"
            steps = f"(%ss2 : {{bits == {prefix0(sw('r0', w('_', 'bits2')))} : Ap.Bits()}}; {steps})"
            steps = f"(%pr : {{bits == {prefix0(sw('_', w(sa('_'), 'bits2')))} : Ap.Bits()}}; {steps})"
            rsteps = f"(%ss2 : {{r3 == {self.after(at, 'x', '_')} : Nat}}; s2)"
            rsteps = f"(%pr : {{r3 == {self.after(at, 'x', sa('_'))} : Nat}}; {rsteps})"
            rsteps = f"(%er : {{_ == {self.after(at, 'x', sa(r0))} : Nat}}; {rsteps})"
            self.out(f"  ({steps}, {rsteps})")
            self.out()
            self.out(f"def {b}.sx_{an}(+rem: Nat, +bits: Ap.Bits(), +r0: Nat, +b0: Ap.Bits(), +r1: Nat, +b1: Ap.Bits(), rd: Ap.Rd({d}), +erd: {{{self.read(at, 'Ap.Cur{r1, b1}')} == rd : Ap.Rd({d})}}, {tail}, +e: {{{gb}.c_{an}(rd) == Done{{(v, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({gb})}}, {pre_t}, {pr_t}, {ss_t}) -> {sxgoal}:")
            self.out("  match rd:")
            self.out("    case Fail{err}:")
            self.out(f"      {self.absurd_sx(gb, sxgoal, 'err')}")
            self.out("    case Done{(+x, c3)}:")
            self.out("      match c3:")
            self.out("        case Ap.Cur{+r3, +b3}:")
            self.out(f"          {b}.sx_{an}.go(rem, bits, r0, b0, r1, b1, x, r3, b3, v, rem2, bits2, e, pre, pr, ss, {self.sx_law(at, 'r1', 'b1', 'x', 'r3', 'b3', 'erd')})")
            self.out()
        self.out(f"def {b}.sx_alt(i: Nat, +rem: Nat, +bits: Ap.Bits(), +r0: Nat, +b0: Ap.Bits(), +r1: Nat, +b1: Ap.Bits(), {tail}, +e: {{{gb}.alt(i, Ap.Cur{{r1, b1}}) == Done{{(v, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({gb})}}, {pre_t}, {pr_t}, ss: PC.Canon(b0, Ap.Size.write(False{{}}, {n}n, 0n, i, r0, b1), r1, Ap.Size.after(False{{}}, {n}n, r0))) -> {sxgoal}:")
        self.out("  match i:")
        for j, (an, at) in enumerate(alts):
            self.out(f"    case {j}n:")
            self.out(f"      {b}.sx_{an}(rem, bits, r0, b0, r1, b1, {self.read(at, 'Ap.Cur{r1, b1}')}, {{==}}, v, rem2, bits2, e, pre, pr, ss)")
        self.out(f"    case {count}n+p:")
        self.out(f"      {self.absurd_sx(gb, sxgoal, 'B.Invalid{0}')}")
        self.out()
        self.out(f"def {b}.sx_idx(+rem: Nat, +bits: Ap.Bits(), +r0: Nat, +b0: Ap.Bits(), r: Ap.Rd(Nat), +er: {{Ap.Size.read({size}, Ap.Cur{{r0, b0}}) == r : Ap.Rd(Nat)}}, {tail}, +e: {{{gb}.r_idx(r) == Done{{(v, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({gb})}}, {pre_t}, {pr_t}) -> {sxgoal}:")
        self.out("  match r:")
        self.out("    case Fail{err}:")
        self.out(f"      {self.absurd_sx(gb, sxgoal, 'err')}")
        self.out("    case Done{(+i, c1)}:")
        self.out("      match c1:")
        self.out("        case Ap.Cur{+r1, +b1}:")
        self.out(f"          {b}.sx_alt(i, rem, bits, r0, b0, r1, b1, v, rem2, bits2, e, pre, pr, PC.Size.sx({size}, r0, b0, i, r1, b1, er))")
        self.out()
        self.emit_sx_entry(t, lambda r0e, b0e, bits: f"{b}.sx_idx(rem, {bits}, {r0e}, {b0e}, Ap.Size.read({size}, Ap.Cur{{{r0e}, {b0e}}}), {{==}}, v, rem2, bits2, e, {{==}}, {{==}})")

    def emit_list(self, t):
        b, item = t.bend, t.item
        gb = f"G.{b}"
        al, n, lo, diff = t.args
        d = self.data(item)
        ls = f"List<&2, {d}>"
        size = f"{al}, {n}n, {lo}n, {diff}n"
        ln = f"List.length(&2, {d}, xs)"
        sa = f"Ap.Size.after({al}, {n}n, rem)"
        self.out(f"def {b}.items_rt(xs: {ls}, +rem: Nat, +rest: Ap.Bits(), +av: {{{gb}.all_valid(xs) == True{{}} : Bool}}) -> {{Done{{(xs, Ap.Cur{{{gb}.items_after(xs, rem), rest}})}} == {gb}.items({ln}, Ap.Cur{{rem, {gb}.items_write(xs, rem, rest)}}) : Ap.Rd({ls})}}:")
        self.out("  match xs:")
        self.out("    case Nil{}:")
        self.out("      {==}")
        self.out("    case +x <> +more:")
        iw = f"{gb}.items_write(more, {self.after(item, 'x', 'rem')}, rest)"
        self.out(f"      ir = Equal.sym(Ap.Rd({d}), {self.read(item, f'Ap.Cur{{rem, {self.write(item, 'x', 'rem', iw)}}}')}, Done{{(x, Ap.Cur{{{self.after(item, 'x', 'rem')}, {iw}}})}}, {self.rt_law(item, 'x', 'rem', iw, f'P.Bool.and_true_l({self.valid(item, 'x')}, {gb}.all_valid(more), av)')})")
        self.out(f"      %ir : {{Done{{(x <> more, Ap.Cur{{{gb}.items_after(x <> more, rem), rest}})}} == {gb}.next(_, c2 => {gb}.items(List.length(&2, {d}, more), c2)) : Ap.Rd({ls})}}")
        self.out(f"      ih = {b}.items_rt(more, {self.after(item, 'x', 'rem')}, rest, P.Bool.and_true_r({self.valid(item, 'x')}, {gb}.all_valid(more), av))")
        self.out(f"      %ih : {{Done{{(x <> more, Ap.Cur{{{gb}.items_after(x <> more, rem), rest}})}} == {gb}.cons(x, _) : Ap.Rd({ls})}}")
        self.out("      {==}")
        self.out()
        iw = f"{gb}.items_write(xs, {sa}, rest)"
        sv = f"Ap.Size.valid({lo}n, {diff}n, {ln})"
        self.out(f"def {b}.rt(+xs: {ls}, +rem: Nat, +rest: Ap.Bits(), +ok: {{{gb}.valid(xs) == True{{}} : Bool}}) -> {{{gb}.read(Ap.Cur{{rem, {gb}.write(xs, rem, rest)}}) == Done{{(xs, Ap.Cur{{{gb}.after(xs, rem), rest}})}} : Ap.Rd({ls})}}:")
        self.out(f"  sr = Equal.sym(Ap.Rd(Nat), Ap.Size.read({size}, Ap.Cur{{rem, Ap.Size.write({al}, {n}n, {lo}n, {ln}, rem, {iw})}}), Done{{({ln}, Ap.Cur{{{sa}, {iw}}})}}, L.aper.size.roundtrip({size}, {ln}, rem, {iw}, P.Bool.and_true_l({sv}, {gb}.all_valid(xs), ok), {{==}}))")
        self.out(f"  %sr : {{{gb}.count(_) == Done{{(xs, Ap.Cur{{{gb}.after(xs, rem), rest}})}} : Ap.Rd({ls})}}")
        self.out(f"  Equal.sym(Ap.Rd({ls}), Done{{(xs, Ap.Cur{{{gb}.items_after(xs, {sa}), rest}})}}, {gb}.items({ln}, Ap.Cur{{{sa}, {iw}}}), {b}.items_rt(xs, {sa}, rest, P.Bool.and_true_r({sv}, {gb}.all_valid(xs), ok)))")
        self.out()
        self.out(f"def GL.ngap.{b}.roundtrip(v, rem, rest, ok):")
        self.out(f"  {b}.rt(v, rem, rest, ok)")
        self.out()
        spec = f"{b}.Spec"
        ih = f"ih: @c4: Ap.Cur -> @xs2: {ls} -> @c5: Ap.Cur -> {{{gb}.items(p, c4) == Done{{(xs2, c5)}} : Ap.Rd({ls})}} -> {spec}(xs2, p)"
        self.out(f"def {spec}(xs: {ls}, n: Nat) -> Type:")
        self.out(f"  {{{gb}.all_valid(xs) == True{{}} : Bool}} & {{{ln} == n : Nat}}")
        self.out()
        self.out(f"def {b}.spec.finish(+p: Nat, +x: {d}, +xs2: {ls}, vi: {{{self.valid(item, 'x')} == True{{}} : Bool}}, s: {spec}(xs2, p)) -> {spec}(x <> xs2, 1n+p):")
        self.out("  (av, len) = s")
        self.out(f"  (P.Bool.and_intro({self.valid(item, 'x')}, {gb}.all_valid(xs2), vi, av), Equal.cong(Nat, Nat, m => 1n+m, List.length(&2, {d}, xs2), p, len))")
        self.out()
        self.out(f"def {b}.spec.cons(+p: Nat, +x: {d}, +c3: Ap.Cur, rl: Ap.Rd({ls}), +erl: {{{gb}.items(p, c3) == rl : Ap.Rd({ls})}}, {ih}, +xs: {ls}, +c2: Ap.Cur, +e: {{{gb}.cons(x, rl) == Done{{(xs, c2)}} : Ap.Rd({ls})}}, vi: {{{self.valid(item, 'x')} == True{{}} : Bool}}) -> {spec}(xs, 1n+p):")
        self.out("  match rl:")
        self.out("    case Fail{err}:")
        self.out(f"      PA.Rd.absurd({ls}, {spec}(xs, 1n+p), err, xs, c2, e)")
        self.out("    case Done{(+xs2, +c5)}:")
        self.out(f"      ev = Equal.cong(Ap.Rd({ls}), {ls}, y => PA.Rd.value({ls}, y, xs), Done{{(x <> xs2, c5)}}, Done{{(xs, c2)}}, e)")
        self.out(f"      %ev : {spec}(_, 1n+p)")
        self.out(f"      {b}.spec.finish(p, x, xs2, vi, ih(c3, xs2, c5, erl))")
        self.out()
        self.out(f"def {b}.spec.step(+p: Nat, +c: Ap.Cur, ri: Ap.Rd({d}), +eri: {{{self.read(item, 'c')} == ri : Ap.Rd({d})}}, {ih}, +xs: {ls}, +c2: Ap.Cur, +e: {{{gb}.next(ri, c4 => {gb}.items(p, c4)) == Done{{(xs, c2)}} : Ap.Rd({ls})}}) -> {spec}(xs, 1n+p):")
        self.out("  match ri:")
        self.out("    case Fail{err}:")
        self.out(f"      PA.Rd.absurd({ls}, {spec}(xs, 1n+p), err, xs, c2, e)")
        self.out("    case Done{(+x, +c3)}:")
        self.out(f"      {b}.spec.cons(p, x, c3, {gb}.items(p, c3), {{==}}, ih, xs, c2, e, {self.dv_law(item, 'c', 'x', 'c3', 'eri')})")
        self.out()
        self.out(f"def {b}.spec(n: Nat, +c: Ap.Cur, +xs: {ls}, +c2: Ap.Cur, +e: {{{gb}.items(n, c) == Done{{(xs, c2)}} : Ap.Rd({ls})}}) -> {spec}(xs, n):")
        self.out("  match n:")
        self.out("    case 0n:")
        self.out(f"      ev = Equal.cong(Ap.Rd({ls}), {ls}, y => PA.Rd.value({ls}, y, xs), Done{{([], c)}}, Done{{(xs, c2)}}, e)")
        self.out(f"      %ev : {spec}(_, 0n)")
        self.out("      ({==}, {==})")
        self.out("    case 1n++p:")
        self.out(f"      {b}.spec.step(p, c, {self.read(item, 'c')}, {{==}}, c4 => xs2 => c5 => e2 => {b}.spec(p, c4, xs2, c5, e2), xs, c2, e)")
        self.out()
        goal = f"{{{gb}.valid(xs) == True{{}} : Bool}}"
        self.out(f"def {b}.dv.finish(+n: Nat, +xs: {ls}, sv: {{Ap.Size.valid({lo}n, {diff}n, n) == True{{}} : Bool}}, s: {spec}(xs, n)) -> {goal}:")
        self.out("  (av, len) = s")
        self.out(f"  slen = Equal.sym(Nat, {ln}, n, len)")
        self.out(f"  P.Bool.and_intro({sv}, {gb}.all_valid(xs), (%slen : {{Ap.Size.valid({lo}n, {diff}n, _) == True{{}} : Bool}}; sv), av)")
        self.out()
        self.out(f"def {b}.dv(+c0: Ap.Cur, rn: Ap.Rd(Nat), +ern: {{Ap.Size.read({size}, c0) == rn : Ap.Rd(Nat)}}, +xs: {ls}, +c2: Ap.Cur, +e: {{{gb}.count(rn) == Done{{(xs, c2)}} : Ap.Rd({ls})}}) -> {goal}:")
        self.out("  match rn:")
        self.out("    case Fail{err}:")
        self.out(f"      PA.Rd.absurd({ls}, {goal}, err, xs, c2, e)")
        self.out("    case Done{(+n, +c)}:")
        self.out(f"      {b}.dv.finish(n, xs, L.aper.size.decode_valid({size}, c0, n, c, ern), {b}.spec(n, c, xs, c2, e))")
        self.out()
        self.out(f"def GL.ngap.{b}.decode_valid(c, v, c2, e):")
        self.out(f"  {b}.dv(c, Ap.Size.read({size}, c), {{==}}, v, c2, e)")
        self.out()

        # suffix: by induction on the items, then the count
        sxi = f"{b}.Sxi"
        sx = f"{b}.Sx"
        w = lambda r, rest: self.write(item, "x", r, rest)
        a = lambda r: self.after(item, "x", r)
        self.out(f"def {sxi}(+bits: Ap.Bits(), +xs: {ls}, +rem: Nat, rem2: Nat, +bits2: Ap.Bits(), k: Nat) -> Type:")
        self.out(f"  ({{bits == {gb}.items_write(xs, rem, bits2) : Ap.Bits()}} & {{rem2 == {gb}.items_after(xs, rem) : Nat}}) & {{{ln} == k : Nat}}")
        self.out()
        ihx = f"ih: @b4: Ap.Bits() -> @r4: Nat -> @xs2: {ls} -> @r5: Nat -> @b5: Ap.Bits() -> {{{gb}.items(p, Ap.Cur{{r4, b4}}) == Done{{(xs2, Ap.Cur{{r5, b5}})}} : Ap.Rd({ls})}} -> {sxi}(b4, xs2, r4, r5, b5, p)"
        self.out(f"def {b}.sx.finish(+p: Nat, +rem: Nat, +bits: Ap.Bits(), +x: {d}, +r3: Nat, +b3: Ap.Bits(), +xs2: {ls}, +r5: Nat, +b5: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), si: {{bits == {w('rem', 'b3')} : Ap.Bits()}} & {{r3 == {a('rem')} : Nat}}, s: {sxi}(b3, xs2, r3, r5, b5, p), eb: {{b5 == bits2 : Ap.Bits()}}, er: {{r5 == rem2 : Nat}}) -> {sxi}(bits, x <> xs2, rem, rem2, bits2, 1n+p):")
        self.out("  (i1, +i2) = si")
        self.out("  (cn, len) = s")
        self.out("  (h1, h2) = cn")
        self.out(f"  (((%i2 : {{bits == {w('rem', f'{gb}.items_write(xs2, _, bits2)')} : Ap.Bits()}}; (%eb : {{bits == {w('rem', f'{gb}.items_write(xs2, r3, _)')} : Ap.Bits()}}; (%h1 : {{bits == {w('rem', '_')} : Ap.Bits()}}; i1))), (%er : {{_ == {gb}.items_after(xs2, {a('rem')}) : Nat}}; (%i2 : {{r5 == {gb}.items_after(xs2, _) : Nat}}; h2))), Equal.cong(Nat, Nat, m => 1n+m, List.length(&2, {d}, xs2), p, len))")
        self.out()
        self.out(f"def {b}.sx.cons(+p: Nat, +rem: Nat, +bits: Ap.Bits(), +x: {d}, +r3: Nat, +b3: Ap.Bits(), rl: Ap.Rd({ls}), +erl: {{{gb}.items(p, Ap.Cur{{r3, b3}}) == rl : Ap.Rd({ls})}}, {ihx}, +xs: {ls}, +rem2: Nat, +bits2: Ap.Bits(), +e: {{{gb}.cons(x, rl) == Done{{(xs, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({ls})}}, si: {{bits == {w('rem', 'b3')} : Ap.Bits()}} & {{r3 == {a('rem')} : Nat}}) -> {sxi}(bits, xs, rem, rem2, bits2, 1n+p):")
        self.out("  match rl:")
        self.out("    case Fail{err}:")
        self.out(f"      PA.Rd.absurd({ls}, {sxi}(bits, xs, rem, rem2, bits2, 1n+p), err, xs, Ap.Cur{{rem2, bits2}}, e)")
        self.out("    case Done{(+xs2, c5)}:")
        self.out("      match c5:")
        self.out("        case Ap.Cur{+r5, +b5}:")
        self.out(f"          ev = Equal.cong(Ap.Rd({ls}), {ls}, y => PA.Rd.value({ls}, y, xs), Done{{(x <> xs2, Ap.Cur{{r5, b5}})}}, Done{{(xs, Ap.Cur{{rem2, bits2}})}}, e)")
        self.out(f"          +ec = Equal.cong(Ap.Rd({ls}), Ap.Cur, y => PA.Rd.cur({ls}, y, Ap.Cur{{rem2, bits2}}), Done{{(x <> xs2, Ap.Cur{{r5, b5}})}}, Done{{(xs, Ap.Cur{{rem2, bits2}})}}, e)")
        self.out(f"          %ev : {sxi}(bits, _, rem, rem2, bits2, 1n+p)")
        self.out(f"          {b}.sx.finish(p, rem, bits, x, r3, b3, xs2, r5, b5, rem2, bits2, si, ih(b3, r3, xs2, r5, b5, erl), Equal.cong(Ap.Cur, Ap.Bits(), y => PA.Cur.bits(y), Ap.Cur{{r5, b5}}, Ap.Cur{{rem2, bits2}}, ec), Equal.cong(Ap.Cur, Nat, y => PA.Cur.rem(y), Ap.Cur{{r5, b5}}, Ap.Cur{{rem2, bits2}}, ec))")
        self.out()
        self.out(f"def {b}.sx.step(+p: Nat, +rem: Nat, +bits: Ap.Bits(), ri: Ap.Rd({d}), +eri: {{{self.read(item, 'Ap.Cur{rem, bits}')} == ri : Ap.Rd({d})}}, {ihx}, +xs: {ls}, +rem2: Nat, +bits2: Ap.Bits(), +e: {{{gb}.next(ri, c4 => {gb}.items(p, c4)) == Done{{(xs, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({ls})}}) -> {sxi}(bits, xs, rem, rem2, bits2, 1n+p):")
        self.out("  match ri:")
        self.out("    case Fail{err}:")
        self.out(f"      PA.Rd.absurd({ls}, {sxi}(bits, xs, rem, rem2, bits2, 1n+p), err, xs, Ap.Cur{{rem2, bits2}}, e)")
        self.out("    case Done{(+x, c3)}:")
        self.out("      match c3:")
        self.out("        case Ap.Cur{+r3, +b3}:")
        self.out(f"          {b}.sx.cons(p, rem, bits, x, r3, b3, {gb}.items(p, Ap.Cur{{r3, b3}}), {{==}}, ih, xs, rem2, bits2, e, {self.sx_law(item, 'rem', 'bits', 'x', 'r3', 'b3', 'eri')})")
        self.out()
        self.out(f"def {b}.sx.items(k: Nat, +rem: Nat, +bits: Ap.Bits(), +xs: {ls}, +rem2: Nat, +bits2: Ap.Bits(), +e: {{{gb}.items(k, Ap.Cur{{rem, bits}}) == Done{{(xs, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({ls})}}) -> {sxi}(bits, xs, rem, rem2, bits2, k):")
        self.out("  match k:")
        self.out("    case 0n:")
        self.out(f"      ev = Equal.cong(Ap.Rd({ls}), {ls}, y => PA.Rd.value({ls}, y, xs), Done{{([], Ap.Cur{{rem, bits}})}}, Done{{(xs, Ap.Cur{{rem2, bits2}})}}, e)")
        self.out(f"      +ec = Equal.cong(Ap.Rd({ls}), Ap.Cur, y => PA.Rd.cur({ls}, y, Ap.Cur{{rem2, bits2}}), Done{{([], Ap.Cur{{rem, bits}})}}, Done{{(xs, Ap.Cur{{rem2, bits2}})}}, e)")
        self.out(f"      %ev : {sxi}(bits, _, rem, rem2, bits2, 0n)")
        self.out("      ((Equal.cong(Ap.Cur, Ap.Bits(), y => PA.Cur.bits(y), Ap.Cur{rem, bits}, Ap.Cur{rem2, bits2}, ec), Equal.sym(Nat, rem, rem2, Equal.cong(Ap.Cur, Nat, y => PA.Cur.rem(y), Ap.Cur{rem, bits}, Ap.Cur{rem2, bits2}, ec))), {==})")
        self.out("    case 1n++p:")
        self.out(f"      {b}.sx.step(p, rem, bits, {self.read(item, 'Ap.Cur{rem, bits}')}, {{==}}, b4 => r4 => xs2 => r5 => b5 => e2 => {b}.sx.items(p, r4, b4, xs2, r5, b5, e2), xs, rem2, bits2, e)")
        self.out()
        sxgoal = f"{sx}(bits, xs, rem, rem2, bits2)"
        self.out(f"def {b}.sx.go(+rem: Nat, +bits: Ap.Bits(), +k: Nat, +r1: Nat, +b1: Ap.Bits(), +xs: {ls}, +rem2: Nat, +bits2: Ap.Bits(), ss: PC.Canon(bits, Ap.Size.write({al}, {n}n, {lo}n, k, rem, b1), r1, {sa}), s: {sxi}(b1, xs, r1, rem2, bits2, k)) -> {sxgoal}:")
        self.out("  (s1, +s2) = ss")
        self.out("  (cn, len) = s")
        self.out("  (h1, h2) = cn")
        self.out(f"  slen = Equal.sym(Nat, {ln}, k, len)")
        self.out(f"  ((%slen : {{bits == Ap.Size.write({al}, {n}n, {lo}n, _, rem, {gb}.items_write(xs, {sa}, bits2)) : Ap.Bits()}}; (%s2 : {{bits == Ap.Size.write({al}, {n}n, {lo}n, k, rem, {gb}.items_write(xs, _, bits2)) : Ap.Bits()}}; (%h1 : {{bits == Ap.Size.write({al}, {n}n, {lo}n, k, rem, _) : Ap.Bits()}}; s1))), (%s2 : {{rem2 == {gb}.items_after(xs, _) : Nat}}; h2))")
        self.out()
        self.out(f"def {b}.sx.count(+rem: Nat, +bits: Ap.Bits(), rl: Ap.Rd(Nat), +erl: {{Ap.Size.read({size}, Ap.Cur{{rem, bits}}) == rl : Ap.Rd(Nat)}}, +xs: {ls}, +rem2: Nat, +bits2: Ap.Bits(), +e: {{{gb}.count(rl) == Done{{(xs, Ap.Cur{{rem2, bits2}})}} : Ap.Rd({ls})}}) -> {sxgoal}:")
        self.out("  match rl:")
        self.out("    case Fail{err}:")
        self.out(f"      PA.Rd.absurd({ls}, {sxgoal}, err, xs, Ap.Cur{{rem2, bits2}}, e)")
        self.out("    case Done{(+k, c1)}:")
        self.out("      match c1:")
        self.out("        case Ap.Cur{+r1, +b1}:")
        self.out(f"          {b}.sx.go(rem, bits, k, r1, b1, xs, rem2, bits2, PC.Size.sx({size}, rem, bits, k, r1, b1, erl), {b}.sx.items(k, r1, b1, xs, rem2, bits2, e))")
        self.out()
        self.out(f"def GL.ngap.{b}.suffix({CUR_ARGS}):")
        self.out(f"  {b}.sx.count(rem, bits, Ap.Size.read({size}, Ap.Cur{{rem, bits}}), {{==}}, v, rem2, bits2, e)")
        self.out()
