import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../LAWS.bend as L
import ./lib.bend as P
import ./aper.bend as PA

# Canonical decoding: what a reader accepted is exactly what the writer makes
# of the value it answered, and the cursor ends where `after` says. These are
# the `suffix` laws of the generated types (kernel/ngap/gen/proofs.bend).

def Canon(bits: Ap.Bits(), w: Ap.Bits(), rem2: Nat, a: Nat) -> Type:
  {bits == w : Ap.Bits()} & {rem2 == a : Nat}

def Fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def Bool.false_of_not(x: Bool, e: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.Refute.bool(e))
    case False{}:
      {==}

def Nat.not_lt_of_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, P.Refute.bool(e))
    case 1n+p 1n+q:
      Nat.not_lt_of_le(p, q, e)

def Nat.sub_add(lo: Nat, +x: Nat) -> {Nat.sub(Nat.add(lo, x), lo) == x : Nat}:
  match lo:
    case 0n:
      Equal.sym(Nat, x, Nat.sub(x, 0n), PA.Nat.sub_zero(x))
    case 1n+l:
      Nat.sub_add(l, x)

# Bits
# ----

def Bits.exact.step(+p: Nat, +b: Bool, +r: Nat, +t: Ap.Bits(), rb: Ap.Rd(Ap.Bits()), ih: @bs2: Ap.Bits() -> @c2: Ap.Cur -> {rb == Done{(bs2, c2)} : Ap.Rd(Ap.Bits())} -> {t == List.append(&2, Bool, bs2, PA.Cur.bits(c2)) : Ap.Bits()}, +bs: Ap.Bits(), +c: Ap.Cur, +e: {Ap.Bits.cons(b, rb) == Done{(bs, c)} : Ap.Rd(Ap.Bits())}) -> {b <> t == List.append(&2, Bool, bs, PA.Cur.bits(c)) : Ap.Bits()}:
  match rb:
    case Fail{err}:
      PA.Rd.absurd(Ap.Bits(), {b <> t == List.append(&2, Bool, bs, PA.Cur.bits(c)) : Ap.Bits()}, err, bs, c, e)
    case Done{(+bs2, +c2)}:
      ev = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Bits(), x => PA.Rd.value(Ap.Bits(), x, bs), Done{(b <> bs2, c2)}, Done{(bs, c)}, e)
      ec = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Cur, x => PA.Rd.cur(Ap.Bits(), x, c), Done{(b <> bs2, c2)}, Done{(bs, c)}, e)
      %ev : {b <> t == List.append(&2, Bool, _, PA.Cur.bits(c)) : Ap.Bits()}
      %ec : {b <> t == List.append(&2, Bool, b <> bs2, PA.Cur.bits(_)) : Ap.Bits()}
      Equal.cong(Ap.Bits(), Ap.Bits(), l => b <> l, t, List.append(&2, Bool, bs2, PA.Cur.bits(c2)), ih(bs2, c2, {==}))

# What Bits.go read is a prefix of its input, and the cursor holds the rest.
def Bits.exact(n: Nat, +r: Nat, bits: Ap.Bits(), +bs: Ap.Bits(), +c: Ap.Cur, +e: {Ap.Bits.go(n, r, bits) == Done{(bs, c)} : Ap.Rd(Ap.Bits())}) -> {bits == List.append(&2, Bool, bs, PA.Cur.bits(c)) : Ap.Bits()}:
  match n bits:
    case 0n rest:
      ev = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Bits(), x => PA.Rd.value(Ap.Bits(), x, bs), Done{([], Ap.Cur{r, rest})}, Done{(bs, c)}, e)
      ec = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Cur, x => PA.Rd.cur(Ap.Bits(), x, c), Done{([], Ap.Cur{r, rest})}, Done{(bs, c)}, e)
      %ev : {rest == List.append(&2, Bool, _, PA.Cur.bits(c)) : Ap.Bits()}
      %ec : {rest == List.append(&2, Bool, [], PA.Cur.bits(_)) : Ap.Bits()}
      {==}
    case 1n+p Nil{}:
      PA.Rd.absurd(Ap.Bits(), {[] == List.append(&2, Bool, bs, PA.Cur.bits(c)) : Ap.Bits()}, B.Short{}, bs, c, e)
    case 1n++p b <> +t:
      Bits.exact.step(p, b, r, t, Ap.Bits.go(p, r, t), bs2 => c2 => e2 => Bits.exact(p, r, t, bs2, c2, e2), bs, c, e)

def Bits.sx.fin(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), ex: {bits == List.append(&2, Bool, bs, bits2) : Ap.Bits()}, s: PA.Bits.Spec(bs, Ap.Cur{rem2, bits2}, n, Ap.Rem.add(n, rem))) -> Canon(bits, Ap.Bits.write(bs, rem, bits2), rem2, Ap.Bits.after(n, rem)) & {List.length(&2, Bool, bs) == n : Nat}:
  (len, rm) = s
  ((ex, Equal.sym(Nat, Ap.Rem.add(n, rem), rem2, rm)), len)

def Bits.sx(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Bits.read(n, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.Bits.write(bs, rem, bits2), rem2, Ap.Bits.after(n, rem)) & {List.length(&2, Bool, bs) == n : Nat}:
  Bits.sx.fin(n, rem, bits, bs, rem2, bits2, Bits.exact(n, Ap.Rem.add(n, rem), bits, bs, Ap.Cur{rem2, bits2}, e), PA.Bits.spec(n, Ap.Rem.add(n, rem), bits, bs, Ap.Cur{rem2, bits2}, e))

def Bits.sx_n(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.Bits.read(n, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.Bits.write(bs, rem, bits2), rem2, Ap.Bits.after(n, rem)):
  Fst(Canon(bits, Ap.Bits.write(bs, rem, bits2), rem2, Ap.Bits.after(n, rem)), {List.length(&2, Bool, bs) == n : Nat}, Bits.sx(n, rem, bits, bs, rem2, bits2, e))

# Alignment
# ---------

def Align.sx.cons(+p: Nat, +t: Ap.Bits(), +rem2: Nat, +rest: Ap.Bits(), s: Canon(t, Ap.Align.write(p, rest), rem2, 0n)) -> Canon(False{} <> t, Ap.Align.write(1n+p, rest), rem2, 0n):
  (eb, er) = s
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, t, Ap.Align.write(p, rest), eb), er)

def Align.sx(rem: Nat, bits: Ap.Bits(), +u: Unit, +rem2: Nat, +rest: Ap.Bits(), +e: {Ap.Align.go(rem, bits) == Done{(u, Ap.Cur{rem2, rest})} : Ap.Rd(Unit)}) -> Canon(bits, Ap.Align.write(rem, rest), rem2, 0n):
  match rem bits:
    case 0n bs:
      +ec = Equal.cong(Ap.Rd(Unit), Ap.Cur, x => PA.Rd.cur(Unit, x, Ap.Cur{0n, []}), Done{(Unit{}, Ap.Cur{0n, bs})}, Done{(u, Ap.Cur{rem2, rest})}, e)
      (Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{0n, bs}, Ap.Cur{rem2, rest}, ec), Equal.sym(Nat, 0n, rem2, Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{0n, bs}, Ap.Cur{rem2, rest}, ec)))
    case 1n++p Nil{}:
      PA.Rd.absurd(Unit, Canon([], Ap.Align.write(1n+p, rest), rem2, 0n), B.Short{}, u, Ap.Cur{rem2, rest}, e)
    case 1n++p b <> +t:
      match b:
        case True{}:
          PA.Rd.absurd(Unit, Canon(True{} <> t, Ap.Align.write(1n+p, rest), rem2, 0n), B.Invalid{0}, u, Ap.Cur{rem2, rest}, e)
        case False{}:
          Align.sx.cons(p, t, rem2, rest, Align.sx(p, t, u, rem2, rest, e))

# Numbers
# -------

def Nat.odd_double(x: Nat) -> {Ap.Nat.is_odd(Nat.double(x)) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Nat.odd_double(p)

def Nat.odd_double1(x: Nat) -> {Ap.Nat.is_odd(1n+Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Nat.odd_double1(p)

def Nat.half_double(x: Nat) -> {Ap.Nat.half(Nat.double(x)) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Ap.Nat.half(Nat.double(p)), p, Nat.half_double(p))

def Nat.half_double1(x: Nat) -> {Ap.Nat.half(1n+Nat.double(x)) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Ap.Nat.half(1n+Nat.double(p)), p, Nat.half_double1(p))

def Nat.to_of_lsb(xs: Ap.Bits()) -> {Ap.Nat.to_lsb(List.length(&2, Bool, xs), Ap.Nat.of_lsb(xs)) == xs : Ap.Bits()}:
  match xs:
    case Nil{}:
      {==}
    case b <> +t:
      match b:
        case False{}:
          sod = Equal.sym(Bool, Ap.Nat.is_odd(Nat.double(Ap.Nat.of_lsb(t))), False{}, Nat.odd_double(Ap.Nat.of_lsb(t)))
          %sod : {_ <> Ap.Nat.to_lsb(List.length(&2, Bool, t), Ap.Nat.half(Nat.double(Ap.Nat.of_lsb(t)))) == False{} <> t : Ap.Bits()}
          shd = Equal.sym(Nat, Ap.Nat.half(Nat.double(Ap.Nat.of_lsb(t))), Ap.Nat.of_lsb(t), Nat.half_double(Ap.Nat.of_lsb(t)))
          %shd : {False{} <> Ap.Nat.to_lsb(List.length(&2, Bool, t), _) == False{} <> t : Ap.Bits()}
          Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, Ap.Nat.to_lsb(List.length(&2, Bool, t), Ap.Nat.of_lsb(t)), t, Nat.to_of_lsb(t))
        case True{}:
          sod = Equal.sym(Bool, Ap.Nat.is_odd(1n+Nat.double(Ap.Nat.of_lsb(t))), True{}, Nat.odd_double1(Ap.Nat.of_lsb(t)))
          %sod : {_ <> Ap.Nat.to_lsb(List.length(&2, Bool, t), Ap.Nat.half(1n+Nat.double(Ap.Nat.of_lsb(t)))) == True{} <> t : Ap.Bits()}
          shd = Equal.sym(Nat, Ap.Nat.half(1n+Nat.double(Ap.Nat.of_lsb(t))), Ap.Nat.of_lsb(t), Nat.half_double1(Ap.Nat.of_lsb(t)))
          %shd : {True{} <> Ap.Nat.to_lsb(List.length(&2, Bool, t), _) == True{} <> t : Ap.Bits()}
          Equal.cong(Ap.Bits(), Ap.Bits(), l => True{} <> l, Ap.Nat.to_lsb(List.length(&2, Bool, t), Ap.Nat.of_lsb(t)), t, Nat.to_of_lsb(t))

# The bits a number was read from are the number's wire form.
def Nat.to_of_bits(+bs: Ap.Bits(), +w: Nat, len: {List.length(&2, Bool, bs) == w : Nat}) -> {Ap.Nat.to_bits(w, Ap.Nat.of_bits(bs)) == bs : Ap.Bits()}:
  srl = Equal.sym(Nat, List.length(&2, Bool, bs), List.length(&2, Bool, List.reverse(&2, Bool, bs)), PA.Bits.rev_len(bs))
  %len : {Ap.Nat.to_bits(_, Ap.Nat.of_bits(bs)) == bs : Ap.Bits()}
  %srl : {Ap.Nat.to_bits(_, Ap.Nat.of_bits(bs)) == bs : Ap.Bits()}
  stl = Equal.sym(Ap.Bits(), Ap.Nat.to_lsb(List.length(&2, Bool, List.reverse(&2, Bool, bs)), Ap.Nat.of_lsb(List.reverse(&2, Bool, bs))), List.reverse(&2, Bool, bs), Nat.to_of_lsb(List.reverse(&2, Bool, bs)))
  %stl : {List.reverse(&2, Bool, _) == bs : Ap.Bits()}
  Equal.sym(Ap.Bits(), bs, List.reverse(&2, Bool, List.reverse(&2, Bool, bs)), PA.Bits.rev_rev(bs))

def U32.to_of(+n: Nat, +bs: Ap.Bits(), +len: {List.length(&2, Bool, bs) == n : Nat}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> {Ap.U32.to_bits(n, Ap.U32.of_bits(bs)) == bs : Ap.Bits()}:
  +rl = PA.Bits.rev_len(bs)
  le : {Nat.is_le(List.length(&2, Bool, List.reverse(&2, Bool, bs)), 32n) == True{} : Bool} = (%rl : {Nat.is_le(_, 32n) == True{} : Bool}; (%(Equal.sym(Nat, List.length(&2, Bool, bs), n, len)) : {Nat.is_le(_, 32n) == True{} : Bool}; w))
  %len : {Ap.U32.to_bits(_, Ap.U32.of_bits(bs)) == bs : Ap.Bits()}
  srl = Equal.sym(Nat, List.length(&2, Bool, bs), List.length(&2, Bool, List.reverse(&2, Bool, bs)), rl)
  %srl : {Ap.U32.to_bits(_, Ap.U32.of_bits(bs)) == bs : Ap.Bits()}
  po = PA.Word.prefix_of(32n, List.reverse(&2, Bool, bs), le)
  %po : {List.reverse(&2, Bool, _) == bs : Ap.Bits()}
  Equal.sym(Ap.Bits(), bs, List.reverse(&2, Bool, List.reverse(&2, Bool, bs)), PA.Bits.rev_rev(bs))

def Int.sx.ok(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: Ap.Bits(), +c: Ap.Cur, ok: Bool, +v: U32, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Int.of(Ap.U32.of_bits(bs), c, ok) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(U32)}, ex: {bits == List.append(&2, Bool, bs, PA.Cur.bits(c)) : Ap.Bits()}, s: PA.Bits.Spec(bs, c, n, Ap.Rem.add(n, rem)), w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(bits, Ap.Int.write(n, v, rem, bits2), rem2, Ap.Int.after(n, rem)):
  match ok:
    case False{}:
      PA.Rd.absurd(U32, Canon(bits, Ap.Int.write(n, v, rem, bits2), rem2, Ap.Int.after(n, rem)), B.Invalid{Ap.U32.of_bits(bs)}, v, Ap.Cur{rem2, bits2}, e)
    case True{}:
      (len, rm) = s
      ev = Equal.cong(Ap.Rd(U32), U32, x => PA.Rd.value(U32, x, v), Done{(Ap.U32.of_bits(bs), c)}, Done{(v, Ap.Cur{rem2, bits2})}, e)
      +ec = Equal.cong(Ap.Rd(U32), Ap.Cur, x => PA.Rd.cur(U32, x, c), Done{(Ap.U32.of_bits(bs), c)}, Done{(v, Ap.Cur{rem2, bits2})}, e)
      %ev : Canon(bits, Ap.Int.write(n, _, rem, bits2), rem2, Ap.Int.after(n, rem))
      sto = Equal.sym(Ap.Bits(), Ap.U32.to_bits(n, Ap.U32.of_bits(bs)), bs, U32.to_of(n, bs, len, w))
      %sto : Canon(bits, List.append(&2, Bool, _, bits2), rem2, Ap.Int.after(n, rem))
      ((%ec : {bits == List.append(&2, Bool, bs, PA.Cur.bits(_)) : Ap.Bits()}; ex), Equal.sym(Nat, Ap.Rem.add(n, rem), rem2, (%ec : {Ap.Rem.add(n, rem) == PA.Cur.rem(_) : Nat}; rm)))

def Int.sx.bits(+n: Nat, +diff: U32, +rem: Nat, +bits: Ap.Bits(), rb: Ap.Rd(Ap.Bits()), +erb: {Ap.Bits.go(n, Ap.Rem.add(n, rem), bits) == rb : Ap.Rd(Ap.Bits())}, +v: U32, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Int.bits(diff, rb) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(U32)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(bits, Ap.Int.write(n, v, rem, bits2), rem2, Ap.Int.after(n, rem)):
  match rb:
    case Fail{err}:
      PA.Rd.absurd(U32, Canon(bits, Ap.Int.write(n, v, rem, bits2), rem2, Ap.Int.after(n, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+bs, +c)}:
      Int.sx.ok(n, rem, bits, bs, c, U32.is_le(Ap.U32.of_bits(bs), diff), v, rem2, bits2, e, Bits.exact(n, Ap.Rem.add(n, rem), bits, bs, c, erb), PA.Bits.spec(n, Ap.Rem.add(n, rem), bits, bs, c, erb), w)

def Int.sx(+n: Nat, +diff: U32, +rem: Nat, +bits: Ap.Bits(), +v: U32, +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.Int.read(n, diff, Ap.Cur{rem, bits}) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(U32)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(bits, Ap.Int.write(n, v, rem, bits2), rem2, Ap.Int.after(n, rem)):
  Int.sx.bits(n, diff, rem, bits, Ap.Bits.go(n, Ap.Rem.add(n, rem), bits), {==}, v, rem2, bits2, e, w)

def AInt.sx.go(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +r1: Nat, +b1: Ap.Bits(), +v: U32, +rem2: Nat, +bits2: Ap.Bits(), sa: Canon(bits, Ap.Align.write(rem, b1), r1, 0n), si: Canon(b1, Ap.Int.write(n, v, r1, bits2), rem2, Ap.Int.after(n, r1))) -> Canon(bits, Ap.AInt.write(n, v, rem, bits2), rem2, Ap.AInt.after(n, rem)):
  (a1, a2) = sa
  (i1, i2) = si
  ((%i1 : {bits == Ap.Align.write(rem, _) : Ap.Bits()}; a1), (%a2 : {rem2 == Ap.Rem.add(n, _) : Nat}; i2))

def AInt.sx.al(+n: Nat, +diff: U32, +rem: Nat, +bits: Ap.Bits(), ra: Ap.Rd(Unit), +era: {Ap.Align.go(rem, bits) == ra : Ap.Rd(Unit)}, +v: U32, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.AInt.aligned(n, diff, ra) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(U32)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(bits, Ap.AInt.write(n, v, rem, bits2), rem2, Ap.AInt.after(n, rem)):
  match ra:
    case Fail{err}:
      PA.Rd.absurd(U32, Canon(bits, Ap.AInt.write(n, v, rem, bits2), rem2, Ap.AInt.after(n, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(u, c)}:
      match c:
        case Ap.Cur{+r1, +b1}:
          AInt.sx.go(n, rem, bits, r1, b1, v, rem2, bits2, Align.sx(rem, bits, u, r1, b1, era), Int.sx(n, diff, r1, b1, v, rem2, bits2, e, w))

def AInt.sx(+n: Nat, +diff: U32, +rem: Nat, +bits: Ap.Bits(), +v: U32, +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.AInt.read(n, diff, Ap.Cur{rem, bits}) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(U32)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(bits, Ap.AInt.write(n, v, rem, bits2), rem2, Ap.AInt.after(n, rem)):
  AInt.sx.al(n, diff, rem, bits, Ap.Align.go(rem, bits), {==}, v, rem2, bits2, e, w)

# Length determinants
# -------------------

def Len.Body(b1: Ap.Bits(), +n: Nat, rem2: Nat, bits2: Ap.Bits()) -> Type:
  Canon(b1, Ap.Len.body(n, Nat.is_lt(n, 128n), bits2), rem2, 0n)

def Len.sx.short.go(+b1: Ap.Bits(), +bs: Ap.Bits(), +c: Ap.Cur, +n: Nat, +rem2: Nat, +bits2: Ap.Bits(), +e: {Done{(Ap.Nat.of_bits(bs), c)} == Done{(n, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}, ex: {b1 == List.append(&2, Bool, bs, PA.Cur.bits(c)) : Ap.Bits()}, s: PA.Bits.Spec(bs, c, 7n, 0n)) -> Len.Body(False{} <> b1, n, rem2, bits2):
  (+len, rm) = s
  ev = Equal.cong(Ap.Rd(Nat), Nat, x => PA.Rd.value(Nat, x, n), Done{(Ap.Nat.of_bits(bs), c)}, Done{(n, Ap.Cur{rem2, bits2})}, e)
  +ec = Equal.cong(Ap.Rd(Nat), Ap.Cur, x => PA.Rd.cur(Nat, x, c), Done{(Ap.Nat.of_bits(bs), c)}, Done{(n, Ap.Cur{rem2, bits2})}, e)
  %ev : Len.Body(False{} <> b1, _, rem2, bits2)
  slt = Equal.sym(Bool, Nat.is_lt(Ap.Nat.of_bits(bs), 128n), True{}, PA.Nat.lt_le_trans(Ap.Nat.of_bits(bs), Ap.Nat.pow2(7n), 128n, PA.Len.bound(bs, 7n, len), {==}))
  %slt : Canon(False{} <> b1, Ap.Len.body(Ap.Nat.of_bits(bs), _, bits2), rem2, 0n)
  sto = Equal.sym(Ap.Bits(), Ap.Nat.to_bits(7n, Ap.Nat.of_bits(bs)), bs, Nat.to_of_bits(bs, 7n, len))
  %sto : Canon(False{} <> b1, False{} <> List.append(&2, Bool, _, bits2), rem2, 0n)
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, b1, List.append(&2, Bool, bs, bits2), (%ec : {b1 == List.append(&2, Bool, bs, PA.Cur.bits(_)) : Ap.Bits()}; ex)), Equal.sym(Nat, 0n, rem2, (%ec : {0n == PA.Cur.rem(_) : Nat}; rm)))

def Len.sx.short(+b1: Ap.Bits(), rb: Ap.Rd(Ap.Bits()), +erb: {Ap.Bits.go(7n, 0n, b1) == rb : Ap.Rd(Ap.Bits())}, +n: Nat, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Len.short(rb) == Done{(n, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}) -> Len.Body(False{} <> b1, n, rem2, bits2):
  match rb:
    case Fail{err}:
      PA.Rd.absurd(Nat, Len.Body(False{} <> b1, n, rem2, bits2), err, n, Ap.Cur{rem2, bits2}, e)
    case Done{(+bs, +c)}:
      Len.sx.short.go(b1, bs, c, n, rem2, bits2, e, Bits.exact(7n, 0n, b1, bs, c, erb), PA.Bits.spec(7n, 0n, b1, bs, c, erb))

def Len.sx.long.ok(+b2: Ap.Bits(), +bs: Ap.Bits(), +c: Ap.Cur, ok: Bool, +eok: {Nat.is_le(128n, Ap.Nat.of_bits(bs)) == ok : Bool}, +n: Nat, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Len.of(Ap.Nat.of_bits(bs), c, ok) == Done{(n, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}, ex: {b2 == List.append(&2, Bool, bs, PA.Cur.bits(c)) : Ap.Bits()}, s: PA.Bits.Spec(bs, c, 14n, 0n)) -> Len.Body(True{} <> False{} <> b2, n, rem2, bits2):
  match ok:
    case False{}:
      PA.Rd.absurd(Nat, Len.Body(True{} <> False{} <> b2, n, rem2, bits2), B.Invalid{128}, n, Ap.Cur{rem2, bits2}, e)
    case True{}:
      (len, rm) = s
      ev = Equal.cong(Ap.Rd(Nat), Nat, x => PA.Rd.value(Nat, x, n), Done{(Ap.Nat.of_bits(bs), c)}, Done{(n, Ap.Cur{rem2, bits2})}, e)
      +ec = Equal.cong(Ap.Rd(Nat), Ap.Cur, x => PA.Rd.cur(Nat, x, c), Done{(Ap.Nat.of_bits(bs), c)}, Done{(n, Ap.Cur{rem2, bits2})}, e)
      %ev : Len.Body(True{} <> False{} <> b2, _, rem2, bits2)
      snl = Equal.sym(Bool, Nat.is_lt(Ap.Nat.of_bits(bs), 128n), False{}, Nat.not_lt_of_le(128n, Ap.Nat.of_bits(bs), eok))
      %snl : Canon(True{} <> False{} <> b2, Ap.Len.body(Ap.Nat.of_bits(bs), _, bits2), rem2, 0n)
      sto = Equal.sym(Ap.Bits(), Ap.Nat.to_bits(14n, Ap.Nat.of_bits(bs)), bs, Nat.to_of_bits(bs, 14n, len))
      %sto : Canon(True{} <> False{} <> b2, True{} <> False{} <> List.append(&2, Bool, _, bits2), rem2, 0n)
      (Equal.cong(Ap.Bits(), Ap.Bits(), l => True{} <> False{} <> l, b2, List.append(&2, Bool, bs, bits2), (%ec : {b2 == List.append(&2, Bool, bs, PA.Cur.bits(_)) : Ap.Bits()}; ex)), Equal.sym(Nat, 0n, rem2, (%ec : {0n == PA.Cur.rem(_) : Nat}; rm)))

def Len.sx.long(+b2: Ap.Bits(), rb: Ap.Rd(Ap.Bits()), +erb: {Ap.Bits.go(14n, 0n, b2) == rb : Ap.Rd(Ap.Bits())}, +n: Nat, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Len.long(rb) == Done{(n, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}) -> Len.Body(True{} <> False{} <> b2, n, rem2, bits2):
  match rb:
    case Fail{err}:
      PA.Rd.absurd(Nat, Len.Body(True{} <> False{} <> b2, n, rem2, bits2), err, n, Ap.Cur{rem2, bits2}, e)
    case Done{(+bs, +c)}:
      Len.sx.long.ok(b2, bs, c, Nat.is_le(128n, Ap.Nat.of_bits(bs)), {==}, n, rem2, bits2, e, Bits.exact(14n, 0n, b2, bs, c, erb), PA.Bits.spec(14n, 0n, b2, bs, c, erb))

def Len.sx.second(b1: Ap.Bits(), +n: Nat, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Len.second(b1) == Done{(n, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}) -> Len.Body(True{} <> b1, n, rem2, bits2):
  match b1:
    case Nil{}:
      PA.Rd.absurd(Nat, Len.Body(True{} <> [], n, rem2, bits2), B.Short{}, n, Ap.Cur{rem2, bits2}, e)
    case b <> +rest:
      match b:
        case True{}:
          PA.Rd.absurd(Nat, Len.Body(True{} <> True{} <> rest, n, rem2, bits2), B.Unsupported{192}, n, Ap.Cur{rem2, bits2}, e)
        case False{}:
          Len.sx.long(rest, Ap.Bits.go(14n, 0n, rest), {==}, n, rem2, bits2, e)

def Len.sx.first(b1: Ap.Bits(), +n: Nat, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Len.first(b1) == Done{(n, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}) -> Len.Body(b1, n, rem2, bits2):
  match b1:
    case Nil{}:
      PA.Rd.absurd(Nat, Len.Body([], n, rem2, bits2), B.Short{}, n, Ap.Cur{rem2, bits2}, e)
    case b <> +rest:
      match b:
        case False{}:
          Len.sx.short(rest, Ap.Bits.go(7n, 0n, rest), {==}, n, rem2, bits2, e)
        case True{}:
          Len.sx.second(rest, n, rem2, bits2, e)

def Len.sx.go(+rem: Nat, +bits: Ap.Bits(), +r1: Nat, +b1: Ap.Bits(), +n: Nat, +rem2: Nat, +bits2: Ap.Bits(), sa: Canon(bits, Ap.Align.write(rem, b1), r1, 0n), sb: Len.Body(b1, n, rem2, bits2)) -> Canon(bits, Ap.Len.write(n, rem, bits2), rem2, Ap.Len.after(rem)):
  (a1, a2) = sa
  (l1, l2) = sb
  ((%l1 : {bits == Ap.Align.write(rem, _) : Ap.Bits()}; a1), l2)

def Len.sx.al(+rem: Nat, +bits: Ap.Bits(), ra: Ap.Rd(Unit), +era: {Ap.Align.go(rem, bits) == ra : Ap.Rd(Unit)}, +n: Nat, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Len.aligned(ra) == Done{(n, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}) -> Canon(bits, Ap.Len.write(n, rem, bits2), rem2, Ap.Len.after(rem)):
  match ra:
    case Fail{err}:
      PA.Rd.absurd(Nat, Canon(bits, Ap.Len.write(n, rem, bits2), rem2, Ap.Len.after(rem)), err, n, Ap.Cur{rem2, bits2}, e)
    case Done{(u, c)}:
      match c:
        case Ap.Cur{+r1, +b1}:
          Len.sx.go(rem, bits, r1, b1, n, rem2, bits2, Align.sx(rem, bits, u, r1, b1, era), Len.sx.first(b1, n, rem2, bits2, e))

def Len.sx(+rem: Nat, +bits: Ap.Bits(), +n: Nat, +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.Len.read(Ap.Cur{rem, bits}) == Done{(n, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}) -> Canon(bits, Ap.Len.write(n, rem, bits2), rem2, Ap.Len.after(rem)):
  Len.sx.al(rem, bits, Ap.Align.go(rem, bits), {==}, n, rem2, bits2, e)

# Constrained lengths
# -------------------

def Size.sx.ok(+n: Nat, +lo: Nat, +r: Nat, +bits: Ap.Bits(), +bs: Ap.Bits(), +c: Ap.Cur, ok: Bool, +k: Nat, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Size.of(lo, Ap.Nat.of_bits(bs), c, ok) == Done{(k, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}, ex: {bits == List.append(&2, Bool, bs, PA.Cur.bits(c)) : Ap.Bits()}, s: PA.Bits.Spec(bs, c, n, r)) -> Canon(bits, List.append(&2, Bool, Ap.Nat.to_bits(n, Nat.sub(k, lo)), bits2), rem2, r):
  match ok:
    case False{}:
      PA.Rd.absurd(Nat, Canon(bits, List.append(&2, Bool, Ap.Nat.to_bits(n, Nat.sub(k, lo)), bits2), rem2, r), B.Invalid{U32.from_nat(Ap.Nat.of_bits(bs))}, k, Ap.Cur{rem2, bits2}, e)
    case True{}:
      (len, rm) = s
      ev = Equal.cong(Ap.Rd(Nat), Nat, x => PA.Rd.value(Nat, x, k), Done{(Nat.add(lo, Ap.Nat.of_bits(bs)), c)}, Done{(k, Ap.Cur{rem2, bits2})}, e)
      +ec = Equal.cong(Ap.Rd(Nat), Ap.Cur, x => PA.Rd.cur(Nat, x, c), Done{(Nat.add(lo, Ap.Nat.of_bits(bs)), c)}, Done{(k, Ap.Cur{rem2, bits2})}, e)
      %ev : Canon(bits, List.append(&2, Bool, Ap.Nat.to_bits(n, Nat.sub(_, lo)), bits2), rem2, r)
      ssa = Equal.sym(Nat, Nat.sub(Nat.add(lo, Ap.Nat.of_bits(bs)), lo), Ap.Nat.of_bits(bs), Nat.sub_add(lo, Ap.Nat.of_bits(bs)))
      %ssa : Canon(bits, List.append(&2, Bool, Ap.Nat.to_bits(n, _), bits2), rem2, r)
      sto = Equal.sym(Ap.Bits(), Ap.Nat.to_bits(n, Ap.Nat.of_bits(bs)), bs, Nat.to_of_bits(bs, n, len))
      %sto : Canon(bits, List.append(&2, Bool, _, bits2), rem2, r)
      ((%ec : {bits == List.append(&2, Bool, bs, PA.Cur.bits(_)) : Ap.Bits()}; ex), Equal.sym(Nat, r, rem2, (%ec : {r == PA.Cur.rem(_) : Nat}; rm)))

def Size.sx.bits(+n: Nat, +lo: Nat, +diff: Nat, +r: Nat, +bits: Ap.Bits(), rb: Ap.Rd(Ap.Bits()), +erb: {Ap.Bits.go(n, r, bits) == rb : Ap.Rd(Ap.Bits())}, +k: Nat, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Size.bits(lo, diff, rb) == Done{(k, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}) -> Canon(bits, List.append(&2, Bool, Ap.Nat.to_bits(n, Nat.sub(k, lo)), bits2), rem2, r):
  match rb:
    case Fail{err}:
      PA.Rd.absurd(Nat, Canon(bits, List.append(&2, Bool, Ap.Nat.to_bits(n, Nat.sub(k, lo)), bits2), rem2, r), err, k, Ap.Cur{rem2, bits2}, e)
    case Done{(+bs, +c)}:
      Size.sx.ok(n, lo, r, bits, bs, c, Nat.is_le(Ap.Nat.of_bits(bs), diff), k, rem2, bits2, e, Bits.exact(n, r, bits, bs, c, erb), PA.Bits.spec(n, r, bits, bs, c, erb))

def Size.sx.al.go(+n: Nat, +lo: Nat, +rem: Nat, +bits: Ap.Bits(), +r1: Nat, +b1: Ap.Bits(), +k: Nat, +rem2: Nat, +bits2: Ap.Bits(), sa: Canon(bits, Ap.Align.write(rem, b1), r1, 0n), sb: Canon(b1, List.append(&2, Bool, Ap.Nat.to_bits(n, Nat.sub(k, lo)), bits2), rem2, Ap.Rem.add(n, r1))) -> Canon(bits, Ap.Size.write(True{}, n, lo, k, rem, bits2), rem2, Ap.Size.after(True{}, n, rem)):
  (a1, a2) = sa
  (s1, s2) = sb
  ((%s1 : {bits == Ap.Align.write(rem, _) : Ap.Bits()}; a1), (%a2 : {rem2 == Ap.Rem.add(n, _) : Nat}; s2))

def Size.sx.al(+n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), ra: Ap.Rd(Unit), +era: {Ap.Align.go(rem, bits) == ra : Ap.Rd(Unit)}, +k: Nat, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Size.aligned(n, lo, diff, ra) == Done{(k, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}) -> Canon(bits, Ap.Size.write(True{}, n, lo, k, rem, bits2), rem2, Ap.Size.after(True{}, n, rem)):
  match ra:
    case Fail{err}:
      PA.Rd.absurd(Nat, Canon(bits, Ap.Size.write(True{}, n, lo, k, rem, bits2), rem2, Ap.Size.after(True{}, n, rem)), err, k, Ap.Cur{rem2, bits2}, e)
    case Done{(u, c)}:
      match c:
        case Ap.Cur{+r1, +b1}:
          Size.sx.al.go(n, lo, rem, bits, r1, b1, k, rem2, bits2, Align.sx(rem, bits, u, r1, b1, era), Size.sx.bits(n, lo, diff, Ap.Rem.add(n, r1), b1, Ap.Bits.go(n, Ap.Rem.add(n, r1), b1), {==}, k, rem2, bits2, e))

def Size.sx(al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), +k: Nat, +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.Size.read(al, n, lo, diff, Ap.Cur{rem, bits}) == Done{(k, Ap.Cur{rem2, bits2})} : Ap.Rd(Nat)}) -> Canon(bits, Ap.Size.write(al, n, lo, k, rem, bits2), rem2, Ap.Size.after(al, n, rem)):
  match al:
    case False{}:
      Size.sx.bits(n, lo, diff, Ap.Rem.add(n, rem), bits, Ap.Bits.go(n, Ap.Rem.add(n, rem), bits), {==}, k, rem2, bits2, e)
    case True{}:
      Size.sx.al(n, lo, diff, rem, bits, Ap.Align.go(rem, bits), {==}, k, rem2, bits2, e)

# Octets
# ------

def Octets.rem.step(+b: U32, +r: Nat, ro: Ap.Rd(B.Bytes()), ih: @bs2: B.Bytes() -> @c2: Ap.Cur -> {ro == Done{(bs2, c2)} : Ap.Rd(B.Bytes())} -> {r == PA.Cur.rem(c2) : Nat}, +bs: B.Bytes(), +c: Ap.Cur, +e: {Ap.Octets.cons(b, ro) == Done{(bs, c)} : Ap.Rd(B.Bytes())}) -> {r == PA.Cur.rem(c) : Nat}:
  match ro:
    case Fail{err}:
      PA.Rd.absurd(B.Bytes(), {r == PA.Cur.rem(c) : Nat}, err, bs, c, e)
    case Done{(+bs2, +c2)}:
      ec = Equal.cong(Ap.Rd(B.Bytes()), Ap.Cur, x => PA.Rd.cur(B.Bytes(), x, c), Done{(b <> bs2, c2)}, Done{(bs, c)}, e)
      %ec : {r == PA.Cur.rem(_) : Nat}
      ih(bs2, c2, {==})

# Octets.go leaves the rem it was given.
def Octets.rem(n: Nat, +r: Nat, bits: Ap.Bits(), +bs: B.Bytes(), +c: Ap.Cur, +e: {Ap.Octets.go(n, r, bits) == Done{(bs, c)} : Ap.Rd(B.Bytes())}) -> {r == PA.Cur.rem(c) : Nat}:
  match n bits:
    case 0n rest:
      ec = Equal.cong(Ap.Rd(B.Bytes()), Ap.Cur, x => PA.Rd.cur(B.Bytes(), x, c), Done{([], Ap.Cur{r, rest})}, Done{(bs, c)}, e)
      %ec : {r == PA.Cur.rem(_) : Nat}
      {==}
    case 1n++p b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> +rest:
      Octets.rem.step(Ap.U32.of_bits([b7, b6, b5, b4, b3, b2, b1, b0]), r, Ap.Octets.go(p, r, rest), bs2 => c2 => e2 => Octets.rem(p, r, rest, bs2, c2, e2), bs, c, e)
    case 1n+p Nil{}:
      PA.Rd.absurd(B.Bytes(), {r == PA.Cur.rem(c) : Nat}, B.Short{}, bs, c, e)
    case 1n+p b7 <> Nil{}:
      PA.Rd.absurd(B.Bytes(), {r == PA.Cur.rem(c) : Nat}, B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> Nil{}:
      PA.Rd.absurd(B.Bytes(), {r == PA.Cur.rem(c) : Nat}, B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> b5 <> Nil{}:
      PA.Rd.absurd(B.Bytes(), {r == PA.Cur.rem(c) : Nat}, B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> b5 <> b4 <> Nil{}:
      PA.Rd.absurd(B.Bytes(), {r == PA.Cur.rem(c) : Nat}, B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> b5 <> b4 <> b3 <> Nil{}:
      PA.Rd.absurd(B.Bytes(), {r == PA.Cur.rem(c) : Nat}, B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> Nil{}:
      PA.Rd.absurd(B.Bytes(), {r == PA.Cur.rem(c) : Nat}, B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> Nil{}:
      PA.Rd.absurd(B.Bytes(), {r == PA.Cur.rem(c) : Nat}, B.Short{}, bs, c, e)

def Octets.sx.go(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), s: PA.Octets.Spec(bs, Ap.Cur{rem2, bits2}, n, rem, bits), rm: {rem == PA.Cur.rem(Ap.Cur{rem2, bits2}) : Nat}) -> Canon(bits, Ap.Octets.write(bs, rem, bits2), rem2, Ap.Octets.after(rem)) & {List.length(&2, U32, bs) == n : Nat}:
  (al, s2) = s
  (len, be) = s2
  ((be, Equal.sym(Nat, rem, rem2, rm)), len)

def Octets.sx(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Octets.read(n, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.Octets.write(bs, rem, bits2), rem2, Ap.Octets.after(rem)) & {List.length(&2, U32, bs) == n : Nat}:
  Octets.sx.go(n, rem, bits, bs, rem2, bits2, PA.Octets.spec(n, rem, bits, bs, Ap.Cur{rem2, bits2}, e), Octets.rem(n, rem, bits, bs, Ap.Cur{rem2, bits2}, e))

def Octets.sx_n(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.Octets.read(n, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.Octets.write(bs, rem, bits2), rem2, Ap.Octets.after(rem)):
  Fst(Canon(bits, Ap.Octets.write(bs, rem, bits2), rem2, Ap.Octets.after(rem)), {List.length(&2, U32, bs) == n : Nat}, Octets.sx(n, rem, bits, bs, rem2, bits2, e))

# Octets after alignment: `n` octets at rem 0.
def AOctets.sx.go(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +r1: Nat, +b1: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), sa: Canon(bits, Ap.Align.write(rem, b1), r1, 0n), so: Canon(b1, Ap.Octets.write(bs, r1, bits2), rem2, r1) & {List.length(&2, U32, bs) == n : Nat}) -> Canon(bits, Ap.AOctets.write(bs, rem, bits2), rem2, Ap.AOctets.after(rem)) & {List.length(&2, U32, bs) == n : Nat}:
  (a1, +a2) = sa
  (so2, len) = so
  (o1, o2) = so2
  (((%a2 : {bits == Ap.Align.write(rem, Ap.Octets.write(bs, _, bits2)) : Ap.Bits()}; (%o1 : {bits == Ap.Align.write(rem, _) : Ap.Bits()}; a1)), (%a2 : {rem2 == _ : Nat}; o2)), len)

def AOctets.sx.al(+n: Nat, +rem: Nat, +bits: Ap.Bits(), ra: Ap.Rd(Unit), +era: {Ap.Align.go(rem, bits) == ra : Ap.Rd(Unit)}, +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.AOctets.aligned(n, ra) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.AOctets.write(bs, rem, bits2), rem2, Ap.AOctets.after(rem)) & {List.length(&2, U32, bs) == n : Nat}:
  match ra:
    case Fail{err}:
      PA.Rd.absurd(B.Bytes(), Canon(bits, Ap.AOctets.write(bs, rem, bits2), rem2, Ap.AOctets.after(rem)) & {List.length(&2, U32, bs) == n : Nat}, err, bs, Ap.Cur{rem2, bits2}, e)
    case Done{(u, c)}:
      match c:
        case Ap.Cur{+r1, +b1}:
          AOctets.sx.go(n, rem, bits, r1, b1, bs, rem2, bits2, Align.sx(rem, bits, u, r1, b1, era), Octets.sx(n, r1, b1, bs, rem2, bits2, e))

def AOctets.sx(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.AOctets.read(n, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.AOctets.write(bs, rem, bits2), rem2, Ap.AOctets.after(rem)) & {List.length(&2, U32, bs) == n : Nat}:
  AOctets.sx.al(n, rem, bits, Ap.Align.go(rem, bits), {==}, bs, rem2, bits2, e)

def AOctets.sx_n(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.AOctets.read(n, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.AOctets.write(bs, rem, bits2), rem2, Ap.AOctets.after(rem)):
  Fst(Canon(bits, Ap.AOctets.write(bs, rem, bits2), rem2, Ap.AOctets.after(rem)), {List.length(&2, U32, bs) == n : Nat}, AOctets.sx(n, rem, bits, bs, rem2, bits2, e))

def ABits.sx.go(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +r1: Nat, +b1: Ap.Bits(), +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), sa: Canon(bits, Ap.Align.write(rem, b1), r1, 0n), sb: Canon(b1, Ap.Bits.write(bs, r1, bits2), rem2, Ap.Bits.after(n, r1)) & {List.length(&2, Bool, bs) == n : Nat}) -> Canon(bits, Ap.ABits.write(bs, rem, bits2), rem2, Ap.ABits.after(n, rem)) & {List.length(&2, Bool, bs) == n : Nat}:
  (a1, a2) = sa
  (sb2, len) = sb
  (b1e, b2e) = sb2
  (((%b1e : {bits == Ap.Align.write(rem, _) : Ap.Bits()}; a1), (%a2 : {rem2 == Ap.Rem.add(n, _) : Nat}; b2e)), len)

def ABits.sx.al(+n: Nat, +rem: Nat, +bits: Ap.Bits(), ra: Ap.Rd(Unit), +era: {Ap.Align.go(rem, bits) == ra : Ap.Rd(Unit)}, +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.ABits.aligned(n, ra) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.ABits.write(bs, rem, bits2), rem2, Ap.ABits.after(n, rem)) & {List.length(&2, Bool, bs) == n : Nat}:
  match ra:
    case Fail{err}:
      PA.Rd.absurd(Ap.Bits(), Canon(bits, Ap.ABits.write(bs, rem, bits2), rem2, Ap.ABits.after(n, rem)) & {List.length(&2, Bool, bs) == n : Nat}, err, bs, Ap.Cur{rem2, bits2}, e)
    case Done{(u, c)}:
      match c:
        case Ap.Cur{+r1, +b1}:
          ABits.sx.go(n, rem, bits, r1, b1, bs, rem2, bits2, Align.sx(rem, bits, u, r1, b1, era), Bits.sx(n, r1, b1, bs, rem2, bits2, e))

def ABits.sx(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.ABits.read(n, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.ABits.write(bs, rem, bits2), rem2, Ap.ABits.after(n, rem)) & {List.length(&2, Bool, bs) == n : Nat}:
  ABits.sx.al(n, rem, bits, Ap.Align.go(rem, bits), {==}, bs, rem2, bits2, e)

def ABits.sx_n(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.ABits.read(n, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.ABits.write(bs, rem, bits2), rem2, Ap.ABits.after(n, rem)):
  Fst(Canon(bits, Ap.ABits.write(bs, rem, bits2), rem2, Ap.ABits.after(n, rem)), {List.length(&2, Bool, bs) == n : Nat}, ABits.sx(n, rem, bits, bs, rem2, bits2, e))

# Open types and unconstrained strings
# ------------------------------------

def Open.sx.go(+rem: Nat, +bits: Ap.Bits(), +l: Nat, +r1: Nat, +b1: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), sl: Canon(bits, Ap.Len.write(l, rem, b1), r1, 0n), so: Canon(b1, Ap.Octets.write(bs, r1, bits2), rem2, r1) & {List.length(&2, U32, bs) == l : Nat}) -> Canon(bits, Ap.Open.write(bs, rem, bits2), rem2, Ap.Open.after(rem)):
  (l1, +l2) = sl
  (so2, len) = so
  (o1, o2) = so2
  slen = Equal.sym(Nat, List.length(&2, U32, bs), l, len)
  ((%slen : {bits == Ap.Len.write(_, rem, Ap.Octets.write(bs, 0n, bits2)) : Ap.Bits()}; (%l2 : {bits == Ap.Len.write(l, rem, Ap.Octets.write(bs, _, bits2)) : Ap.Bits()}; (%o1 : {bits == Ap.Len.write(l, rem, _) : Ap.Bits()}; l1))), (%l2 : {rem2 == _ : Nat}; o2))

def Open.sx.len(+rem: Nat, +bits: Ap.Bits(), rl: Ap.Rd(Nat), +erl: {Ap.Len.read(Ap.Cur{rem, bits}) == rl : Ap.Rd(Nat)}, +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Open.count(rl) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.Open.write(bs, rem, bits2), rem2, Ap.Open.after(rem)):
  match rl:
    case Fail{err}:
      PA.Rd.absurd(B.Bytes(), Canon(bits, Ap.Open.write(bs, rem, bits2), rem2, Ap.Open.after(rem)), err, bs, Ap.Cur{rem2, bits2}, e)
    case Done{(+l, c)}:
      match c:
        case Ap.Cur{+r1, +b1}:
          Open.sx.go(rem, bits, l, r1, b1, bs, rem2, bits2, Len.sx(rem, bits, l, r1, b1, erl), Octets.sx(l, r1, b1, bs, rem2, bits2, e))

def Open.sx(+rem: Nat, +bits: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.Open.read(Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.Open.write(bs, rem, bits2), rem2, Ap.Open.after(rem)):
  Open.sx.len(rem, bits, Ap.Len.read(Ap.Cur{rem, bits}), {==}, bs, rem2, bits2, e)

def UBitStr.sx.go(+rem: Nat, +bits: Ap.Bits(), +l: Nat, +r1: Nat, +b1: Ap.Bits(), +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), sl: Canon(bits, Ap.Len.write(l, rem, b1), r1, 0n), sb: Canon(b1, Ap.Bits.write(bs, r1, bits2), rem2, Ap.Bits.after(l, r1)) & {List.length(&2, Bool, bs) == l : Nat}) -> Canon(bits, Ap.UBitStr.write(bs, rem, bits2), rem2, Ap.UBitStr.after(bs, rem)):
  (l1, +l2) = sl
  (sb2, len) = sb
  (b1e, b2e) = sb2
  +slen = Equal.sym(Nat, List.length(&2, Bool, bs), l, len)
  ((%slen : {bits == Ap.Len.write(_, rem, List.append(&2, Bool, bs, bits2)) : Ap.Bits()}; (%b1e : {bits == Ap.Len.write(l, rem, _) : Ap.Bits()}; l1)), (%slen : {rem2 == Ap.Rem.add(_, 0n) : Nat}; (%l2 : {rem2 == Ap.Rem.add(l, _) : Nat}; b2e)))

def UBitStr.sx.len(+rem: Nat, +bits: Ap.Bits(), rl: Ap.Rd(Nat), +erl: {Ap.Len.read(Ap.Cur{rem, bits}) == rl : Ap.Rd(Nat)}, +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.UBitStr.count(rl) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.UBitStr.write(bs, rem, bits2), rem2, Ap.UBitStr.after(bs, rem)):
  match rl:
    case Fail{err}:
      PA.Rd.absurd(Ap.Bits(), Canon(bits, Ap.UBitStr.write(bs, rem, bits2), rem2, Ap.UBitStr.after(bs, rem)), err, bs, Ap.Cur{rem2, bits2}, e)
    case Done{(+l, c)}:
      match c:
        case Ap.Cur{+r1, +b1}:
          UBitStr.sx.go(rem, bits, l, r1, b1, bs, rem2, bits2, Len.sx(rem, bits, l, r1, b1, erl), Bits.sx(l, r1, b1, bs, rem2, bits2, e))

def UBitStr.sx(+rem: Nat, +bits: Ap.Bits(), +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.UBitStr.read(Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.UBitStr.write(bs, rem, bits2), rem2, Ap.UBitStr.after(bs, rem)):
  UBitStr.sx.len(rem, bits, Ap.Len.read(Ap.Cur{rem, bits}), {==}, bs, rem2, bits2, e)

# Constrained strings
# -------------------

def OctStr.sx.go(+al: Bool, +n: Nat, +lo: Nat, +rem: Nat, +bits: Ap.Bits(), +l: Nat, +r1: Nat, +b1: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), ss: Canon(bits, Ap.Size.write(al, n, lo, l, rem, b1), r1, Ap.Size.after(al, n, rem)), so: Canon(b1, Ap.AOctets.write(bs, r1, bits2), rem2, 0n) & {List.length(&2, U32, bs) == l : Nat}) -> Canon(bits, Ap.OctStr.write(al, n, lo, bs, rem, bits2), rem2, Ap.OctStr.after(rem)):
  (s1, s2) = ss
  (so2, len) = so
  (o1, o2) = so2
  slen = Equal.sym(Nat, List.length(&2, U32, bs), l, len)
  ((%slen : {bits == Ap.Size.write(al, n, lo, _, rem, Ap.AOctets.write(bs, Ap.Size.after(al, n, rem), bits2)) : Ap.Bits()}; (%s2 : {bits == Ap.Size.write(al, n, lo, l, rem, Ap.AOctets.write(bs, _, bits2)) : Ap.Bits()}; (%o1 : {bits == Ap.Size.write(al, n, lo, l, rem, _) : Ap.Bits()}; s1))), o2)

def OctStr.sx.count(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), rl: Ap.Rd(Nat), +erl: {Ap.Size.read(al, n, lo, diff, Ap.Cur{rem, bits}) == rl : Ap.Rd(Nat)}, +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.OctStr.count(rl) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.OctStr.write(al, n, lo, bs, rem, bits2), rem2, Ap.OctStr.after(rem)):
  match rl:
    case Fail{err}:
      PA.Rd.absurd(B.Bytes(), Canon(bits, Ap.OctStr.write(al, n, lo, bs, rem, bits2), rem2, Ap.OctStr.after(rem)), err, bs, Ap.Cur{rem2, bits2}, e)
    case Done{(+l, c)}:
      match c:
        case Ap.Cur{+r1, +b1}:
          OctStr.sx.go(al, n, lo, rem, bits, l, r1, b1, bs, rem2, bits2, Size.sx(al, n, lo, diff, rem, bits, l, r1, b1, erl), AOctets.sx(l, r1, b1, bs, rem2, bits2, e))

def OctStr.sx(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.OctStr.read(al, n, lo, diff, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.OctStr.write(al, n, lo, bs, rem, bits2), rem2, Ap.OctStr.after(rem)):
  OctStr.sx.count(al, n, lo, diff, rem, bits, Ap.Size.read(al, n, lo, diff, Ap.Cur{rem, bits}), {==}, bs, rem2, bits2, e)

def BitStr.sx.go(+al: Bool, +n: Nat, +lo: Nat, +rem: Nat, +bits: Ap.Bits(), +l: Nat, +r1: Nat, +b1: Ap.Bits(), +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), ss: Canon(bits, Ap.Size.write(al, n, lo, l, rem, b1), r1, Ap.Size.after(al, n, rem)), sb: Canon(b1, Ap.ABits.write(bs, r1, bits2), rem2, Ap.ABits.after(l, r1)) & {List.length(&2, Bool, bs) == l : Nat}) -> Canon(bits, Ap.BitStr.write(al, n, lo, bs, rem, bits2), rem2, Ap.BitStr.after(bs, rem)):
  (s1, s2) = ss
  (sb2, len) = sb
  (b1e, b2e) = sb2
  +slen = Equal.sym(Nat, List.length(&2, Bool, bs), l, len)
  ((%slen : {bits == Ap.Size.write(al, n, lo, _, rem, Ap.ABits.write(bs, Ap.Size.after(al, n, rem), bits2)) : Ap.Bits()}; (%s2 : {bits == Ap.Size.write(al, n, lo, l, rem, Ap.ABits.write(bs, _, bits2)) : Ap.Bits()}; (%b1e : {bits == Ap.Size.write(al, n, lo, l, rem, _) : Ap.Bits()}; s1))), (%slen : {rem2 == Ap.Rem.add(_, 0n) : Nat}; b2e))

def BitStr.sx.count(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), rl: Ap.Rd(Nat), +erl: {Ap.Size.read(al, n, lo, diff, Ap.Cur{rem, bits}) == rl : Ap.Rd(Nat)}, +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.BitStr.count(rl) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.BitStr.write(al, n, lo, bs, rem, bits2), rem2, Ap.BitStr.after(bs, rem)):
  match rl:
    case Fail{err}:
      PA.Rd.absurd(Ap.Bits(), Canon(bits, Ap.BitStr.write(al, n, lo, bs, rem, bits2), rem2, Ap.BitStr.after(bs, rem)), err, bs, Ap.Cur{rem2, bits2}, e)
    case Done{(+l, c)}:
      match c:
        case Ap.Cur{+r1, +b1}:
          BitStr.sx.go(al, n, lo, rem, bits, l, r1, b1, bs, rem2, bits2, Size.sx(al, n, lo, diff, rem, bits, l, r1, b1, erl), ABits.sx(l, r1, b1, bs, rem2, bits2, e))

def BitStr.sx(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.BitStr.read(al, n, lo, diff, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.BitStr.write(al, n, lo, bs, rem, bits2), rem2, Ap.BitStr.after(bs, rem)):
  BitStr.sx.count(al, n, lo, diff, rem, bits, Ap.Size.read(al, n, lo, diff, Ap.Cur{rem, bits}), {==}, bs, rem2, bits2, e)

# Indefinite-length numbers
# -------------------------

def Big.sx.ok(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +l: Nat, +r1: Nat, +b1: Ap.Bits(), +bs0: B.Bytes(), +r3: Nat, +b3: Ap.Bits(), ok: Bool, +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Big.of(bs0, Ap.Cur{r3, b3}, ok) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}, ss: Canon(bits, Ap.Size.write(False{}, n, 1n, l, rem, b1), r1, Ap.Size.after(False{}, n, rem)), so: Canon(b1, Ap.AOctets.write(bs0, r1, b3), r3, 0n) & {List.length(&2, U32, bs0) == l : Nat}) -> Canon(bits, Ap.Big.write(n, bs, rem, bits2), rem2, Ap.Big.after(rem)):
  match ok:
    case False{}:
      PA.Rd.absurd(B.Bytes(), Canon(bits, Ap.Big.write(n, bs, rem, bits2), rem2, Ap.Big.after(rem)), B.Invalid{0}, bs, Ap.Cur{rem2, bits2}, e)
    case True{}:
      (s1, s2) = ss
      (so2, len) = so
      (o1, o2) = so2
      ev = Equal.cong(Ap.Rd(B.Bytes()), B.Bytes(), x => PA.Rd.value(B.Bytes(), x, bs), Done{(bs0, Ap.Cur{r3, b3})}, Done{(bs, Ap.Cur{rem2, bits2})}, e)
      +ec = Equal.cong(Ap.Rd(B.Bytes()), Ap.Cur, x => PA.Rd.cur(B.Bytes(), x, Ap.Cur{rem2, bits2}), Done{(bs0, Ap.Cur{r3, b3})}, Done{(bs, Ap.Cur{rem2, bits2})}, e)
      eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      slen = Equal.sym(Nat, List.length(&2, U32, bs0), l, len)
      ((%ev : {bits == Ap.Size.write(False{}, n, 1n, List.length(&2, U32, _), rem, Ap.AOctets.write(_, Ap.Size.after(False{}, n, rem), bits2)) : Ap.Bits()}; (%slen : {bits == Ap.Size.write(False{}, n, 1n, _, rem, Ap.AOctets.write(bs0, Ap.Size.after(False{}, n, rem), bits2)) : Ap.Bits()}; (%eb : {bits == Ap.Size.write(False{}, n, 1n, l, rem, Ap.AOctets.write(bs0, Ap.Size.after(False{}, n, rem), _)) : Ap.Bits()}; (%s2 : {bits == Ap.Size.write(False{}, n, 1n, l, rem, Ap.AOctets.write(bs0, _, b3)) : Ap.Bits()}; (%o1 : {bits == Ap.Size.write(False{}, n, 1n, l, rem, _) : Ap.Bits()}; s1))))), (%er : {_ == 0n : Nat}; o2))

def Big.sx.oct(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +l: Nat, +r1: Nat, +b1: Ap.Bits(), ro: Ap.Rd(B.Bytes()), +ero: {Ap.AOctets.read(l, Ap.Cur{r1, b1}) == ro : Ap.Rd(B.Bytes())}, +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Big.octets(ro) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}, ss: Canon(bits, Ap.Size.write(False{}, n, 1n, l, rem, b1), r1, Ap.Size.after(False{}, n, rem))) -> Canon(bits, Ap.Big.write(n, bs, rem, bits2), rem2, Ap.Big.after(rem)):
  match ro:
    case Fail{err}:
      PA.Rd.absurd(B.Bytes(), Canon(bits, Ap.Big.write(n, bs, rem, bits2), rem2, Ap.Big.after(rem)), err, bs, Ap.Cur{rem2, bits2}, e)
    case Done{(+bs0, c3)}:
      match c3:
        case Ap.Cur{+r3, +b3}:
          Big.sx.ok(n, rem, bits, l, r1, b1, bs0, r3, b3, Ap.Big.canonical(bs0), bs, rem2, bits2, e, ss, AOctets.sx(l, r1, b1, bs0, r3, b3, ero))

def Big.sx.count(+n: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), rl: Ap.Rd(Nat), +erl: {Ap.Size.read(False{}, n, 1n, diff, Ap.Cur{rem, bits}) == rl : Ap.Rd(Nat)}, +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Big.count(rl) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.Big.write(n, bs, rem, bits2), rem2, Ap.Big.after(rem)):
  match rl:
    case Fail{err}:
      PA.Rd.absurd(B.Bytes(), Canon(bits, Ap.Big.write(n, bs, rem, bits2), rem2, Ap.Big.after(rem)), err, bs, Ap.Cur{rem2, bits2}, e)
    case Done{(+l, c)}:
      match c:
        case Ap.Cur{+r1, +b1}:
          Big.sx.oct(n, rem, bits, l, r1, b1, Ap.AOctets.read(l, Ap.Cur{r1, b1}), {==}, bs, rem2, bits2, e, Size.sx(False{}, n, 1n, diff, rem, bits, l, r1, b1, erl))

def Big.sx(+n: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), +bs: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.Big.read(n, diff, Ap.Cur{rem, bits}) == Done{(bs, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.Big.write(n, bs, rem, bits2), rem2, Ap.Big.after(rem)):
  Big.sx.count(n, diff, rem, bits, Ap.Size.read(False{}, n, 1n, diff, Ap.Cur{rem, bits}), {==}, bs, rem2, bits2, e)

# Printable strings
# -----------------

def Str.sx.ok(+al: Bool, +n: Nat, +lo: Nat, +rem: Nat, +bits: Ap.Bits(), +s0: B.Bytes(), +r3: Nat, +b3: Ap.Bits(), ok: Bool, +s: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Str.of(s0, Ap.Cur{r3, b3}, ok) == Done{(s, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}, so: Canon(bits, Ap.OctStr.write(al, n, lo, s0, rem, b3), r3, 0n)) -> Canon(bits, Ap.Str.write(al, n, lo, s, rem, bits2), rem2, Ap.Str.after(rem)):
  match ok:
    case False{}:
      PA.Rd.absurd(B.Bytes(), Canon(bits, Ap.Str.write(al, n, lo, s, rem, bits2), rem2, Ap.Str.after(rem)), B.Invalid{1}, s, Ap.Cur{rem2, bits2}, e)
    case True{}:
      (o1, o2) = so
      ev = Equal.cong(Ap.Rd(B.Bytes()), B.Bytes(), x => PA.Rd.value(B.Bytes(), x, s), Done{(s0, Ap.Cur{r3, b3})}, Done{(s, Ap.Cur{rem2, bits2})}, e)
      +ec = Equal.cong(Ap.Rd(B.Bytes()), Ap.Cur, x => PA.Rd.cur(B.Bytes(), x, Ap.Cur{rem2, bits2}), Done{(s0, Ap.Cur{r3, b3})}, Done{(s, Ap.Cur{rem2, bits2})}, e)
      eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      ((%ev : {bits == Ap.OctStr.write(al, n, lo, _, rem, bits2) : Ap.Bits()}; (%eb : {bits == Ap.OctStr.write(al, n, lo, s0, rem, _) : Ap.Bits()}; o1)), (%er : {_ == 0n : Nat}; o2))

def Str.sx.check(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), ro: Ap.Rd(B.Bytes()), +ero: {Ap.OctStr.read(al, n, lo, diff, Ap.Cur{rem, bits}) == ro : Ap.Rd(B.Bytes())}, +s: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Str.check(ro) == Done{(s, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.Str.write(al, n, lo, s, rem, bits2), rem2, Ap.Str.after(rem)):
  match ro:
    case Fail{err}:
      PA.Rd.absurd(B.Bytes(), Canon(bits, Ap.Str.write(al, n, lo, s, rem, bits2), rem2, Ap.Str.after(rem)), err, s, Ap.Cur{rem2, bits2}, e)
    case Done{(+s0, c3)}:
      match c3:
        case Ap.Cur{+r3, +b3}:
          Str.sx.ok(al, n, lo, rem, bits, s0, r3, b3, Ap.Str.all(s0), s, rem2, bits2, e, OctStr.sx(al, n, lo, diff, rem, bits, s0, r3, b3, ero))

def Str.sx(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), +s: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.Str.read(al, n, lo, diff, Ap.Cur{rem, bits}) == Done{(s, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.Str.write(al, n, lo, s, rem, bits2), rem2, Ap.Str.after(rem)):
  Str.sx.check(al, n, lo, diff, rem, bits, Ap.OctStr.read(al, n, lo, diff, Ap.Cur{rem, bits}), {==}, s, rem2, bits2, e)

def UStr.sx.ok(+rem: Nat, +bits: Ap.Bits(), +s0: B.Bytes(), +r3: Nat, +b3: Ap.Bits(), ok: Bool, +s: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Str.of(s0, Ap.Cur{r3, b3}, ok) == Done{(s, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}, so: Canon(bits, Ap.Open.write(s0, rem, b3), r3, 0n)) -> Canon(bits, Ap.UStr.write(s, rem, bits2), rem2, Ap.UStr.after(rem)):
  match ok:
    case False{}:
      PA.Rd.absurd(B.Bytes(), Canon(bits, Ap.UStr.write(s, rem, bits2), rem2, Ap.UStr.after(rem)), B.Invalid{1}, s, Ap.Cur{rem2, bits2}, e)
    case True{}:
      (o1, o2) = so
      ev = Equal.cong(Ap.Rd(B.Bytes()), B.Bytes(), x => PA.Rd.value(B.Bytes(), x, s), Done{(s0, Ap.Cur{r3, b3})}, Done{(s, Ap.Cur{rem2, bits2})}, e)
      +ec = Equal.cong(Ap.Rd(B.Bytes()), Ap.Cur, x => PA.Rd.cur(B.Bytes(), x, Ap.Cur{rem2, bits2}), Done{(s0, Ap.Cur{r3, b3})}, Done{(s, Ap.Cur{rem2, bits2})}, e)
      eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      ((%ev : {bits == Ap.Open.write(_, rem, bits2) : Ap.Bits()}; (%eb : {bits == Ap.Open.write(s0, rem, _) : Ap.Bits()}; o1)), (%er : {_ == 0n : Nat}; o2))

def UStr.sx.check(+rem: Nat, +bits: Ap.Bits(), ro: Ap.Rd(B.Bytes()), +ero: {Ap.Open.read(Ap.Cur{rem, bits}) == ro : Ap.Rd(B.Bytes())}, +s: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Str.check(ro) == Done{(s, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.UStr.write(s, rem, bits2), rem2, Ap.UStr.after(rem)):
  match ro:
    case Fail{err}:
      PA.Rd.absurd(B.Bytes(), Canon(bits, Ap.UStr.write(s, rem, bits2), rem2, Ap.UStr.after(rem)), err, s, Ap.Cur{rem2, bits2}, e)
    case Done{(+s0, c3)}:
      match c3:
        case Ap.Cur{+r3, +b3}:
          UStr.sx.ok(rem, bits, s0, r3, b3, Ap.Str.all(s0), s, rem2, bits2, e, Open.sx(rem, bits, s0, r3, b3, ero))

def UStr.sx(+rem: Nat, +bits: Ap.Bits(), +s: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.UStr.read(Ap.Cur{rem, bits}) == Done{(s, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.UStr.write(s, rem, bits2), rem2, Ap.UStr.after(rem)):
  UStr.sx.check(rem, bits, Ap.Open.read(Ap.Cur{rem, bits}), {==}, s, rem2, bits2, e)

# Small numbers and enumerations
# ------------------------------

def Small.sx.go(+rem: Nat, +rest: Ap.Bits(), +v: U32, +rem2: Nat, +bits2: Ap.Bits(), si: Canon(rest, Ap.Int.write(6n, v, Ap.Rem.next(rem), bits2), rem2, Ap.Int.after(6n, Ap.Rem.next(rem)))) -> Canon(False{} <> rest, Ap.Small.write(v, rem, bits2), rem2, Ap.Small.after(rem)):
  (i1, i2) = si
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, rest, Ap.Int.write(6n, v, Ap.Rem.next(rem), bits2), i1), i2)

def Small.sx(+rem: Nat, bits: Ap.Bits(), +v: U32, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Small.read(Ap.Cur{rem, bits}) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(U32)}) -> Canon(bits, Ap.Small.write(v, rem, bits2), rem2, Ap.Small.after(rem)):
  match bits:
    case Nil{}:
      PA.Rd.absurd(U32, Canon([], Ap.Small.write(v, rem, bits2), rem2, Ap.Small.after(rem)), B.Short{}, v, Ap.Cur{rem2, bits2}, e)
    case b <> +rest:
      match b:
        case True{}:
          PA.Rd.absurd(U32, Canon(True{} <> rest, Ap.Small.write(v, rem, bits2), rem2, Ap.Small.after(rem)), B.Unsupported{64}, v, Ap.Cur{rem2, bits2}, e)
        case False{}:
          Small.sx.go(rem, rest, v, rem2, bits2, Int.sx(6n, 63, Ap.Rem.next(rem), rest, v, rem2, bits2, e, {==}))

def Enum.sx.root0.go(+n: Nat, +rem: Nat, +bits: Ap.Bits(), +i: U32, +r3: Nat, +b3: Ap.Bits(), +v: Ap.Enum, +rem2: Nat, +bits2: Ap.Bits(), +e: {Done{(Ap.Root{i}, Ap.Cur{r3, b3})} == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Enum)}, si: Canon(bits, Ap.Int.write(n, i, rem, b3), r3, Ap.Int.after(n, rem))) -> Canon(bits, Ap.Enum.write(n, False{}, v, rem, bits2), rem2, Ap.Enum.after(n, False{}, v, rem)):
  (i1, i2) = si
  ev = Equal.cong(Ap.Rd(Ap.Enum), Ap.Enum, x => PA.Rd.value(Ap.Enum, x, v), Done{(Ap.Root{i}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  +ec = Equal.cong(Ap.Rd(Ap.Enum), Ap.Cur, x => PA.Rd.cur(Ap.Enum, x, Ap.Cur{rem2, bits2}), Done{(Ap.Root{i}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  %ev : Canon(bits, Ap.Enum.write(n, False{}, _, rem, bits2), rem2, Ap.Enum.after(n, False{}, _, rem))
  ((%eb : {bits == Ap.Int.write(n, i, rem, _) : Ap.Bits()}; i1), (%er : {_ == Ap.Rem.add(n, rem) : Nat}; i2))

def Enum.sx.root0(+n: Nat, +diff: U32, +rem: Nat, +bits: Ap.Bits(), ri: Ap.Rd(U32), +eri: {Ap.Int.read(n, diff, Ap.Cur{rem, bits}) == ri : Ap.Rd(U32)}, +v: Ap.Enum, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Enum.root(ri) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Enum)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(bits, Ap.Enum.write(n, False{}, v, rem, bits2), rem2, Ap.Enum.after(n, False{}, v, rem)):
  match ri:
    case Fail{err}:
      PA.Rd.absurd(Ap.Enum, Canon(bits, Ap.Enum.write(n, False{}, v, rem, bits2), rem2, Ap.Enum.after(n, False{}, v, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+i, c)}:
      match c:
        case Ap.Cur{+r3, +b3}:
          Enum.sx.root0.go(n, rem, bits, i, r3, b3, v, rem2, bits2, e, Int.sx(n, diff, rem, bits, i, r3, b3, eri, w))

def Enum.sx.root1.go(+n: Nat, +rem: Nat, +rest: Ap.Bits(), +i: U32, +r3: Nat, +b3: Ap.Bits(), +v: Ap.Enum, +rem2: Nat, +bits2: Ap.Bits(), +e: {Done{(Ap.Root{i}, Ap.Cur{r3, b3})} == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Enum)}, si: Canon(rest, Ap.Int.write(n, i, Ap.Rem.next(rem), b3), r3, Ap.Int.after(n, Ap.Rem.next(rem)))) -> Canon(False{} <> rest, Ap.Enum.write(n, True{}, v, rem, bits2), rem2, Ap.Enum.after(n, True{}, v, rem)):
  (i1, i2) = si
  ev = Equal.cong(Ap.Rd(Ap.Enum), Ap.Enum, x => PA.Rd.value(Ap.Enum, x, v), Done{(Ap.Root{i}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  +ec = Equal.cong(Ap.Rd(Ap.Enum), Ap.Cur, x => PA.Rd.cur(Ap.Enum, x, Ap.Cur{rem2, bits2}), Done{(Ap.Root{i}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  %ev : Canon(False{} <> rest, Ap.Enum.write(n, True{}, _, rem, bits2), rem2, Ap.Enum.after(n, True{}, _, rem))
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, rest, Ap.Int.write(n, i, Ap.Rem.next(rem), bits2), (%eb : {rest == Ap.Int.write(n, i, Ap.Rem.next(rem), _) : Ap.Bits()}; i1)), (%er : {_ == Ap.Rem.add(n, Ap.Rem.next(rem)) : Nat}; i2))

def Enum.sx.root1(+n: Nat, +diff: U32, +rem: Nat, +rest: Ap.Bits(), ri: Ap.Rd(U32), +eri: {Ap.Int.read(n, diff, Ap.Cur{Ap.Rem.next(rem), rest}) == ri : Ap.Rd(U32)}, +v: Ap.Enum, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Enum.root(ri) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Enum)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(False{} <> rest, Ap.Enum.write(n, True{}, v, rem, bits2), rem2, Ap.Enum.after(n, True{}, v, rem)):
  match ri:
    case Fail{err}:
      PA.Rd.absurd(Ap.Enum, Canon(False{} <> rest, Ap.Enum.write(n, True{}, v, rem, bits2), rem2, Ap.Enum.after(n, True{}, v, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+i, c)}:
      match c:
        case Ap.Cur{+r3, +b3}:
          Enum.sx.root1.go(n, rem, rest, i, r3, b3, v, rem2, bits2, e, Int.sx(n, diff, Ap.Rem.next(rem), rest, i, r3, b3, eri, w))

def Enum.sx.ext.go(+n: Nat, +rem: Nat, +rest: Ap.Bits(), +i: U32, +r3: Nat, +b3: Ap.Bits(), +v: Ap.Enum, +rem2: Nat, +bits2: Ap.Bits(), +e: {Done{(Ap.Ext{i}, Ap.Cur{r3, b3})} == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Enum)}, ss: Canon(rest, Ap.Small.write(i, Ap.Rem.next(rem), b3), r3, Ap.Small.after(Ap.Rem.next(rem)))) -> Canon(True{} <> rest, Ap.Enum.write(n, True{}, v, rem, bits2), rem2, Ap.Enum.after(n, True{}, v, rem)):
  (s1, s2) = ss
  ev = Equal.cong(Ap.Rd(Ap.Enum), Ap.Enum, x => PA.Rd.value(Ap.Enum, x, v), Done{(Ap.Ext{i}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  +ec = Equal.cong(Ap.Rd(Ap.Enum), Ap.Cur, x => PA.Rd.cur(Ap.Enum, x, Ap.Cur{rem2, bits2}), Done{(Ap.Ext{i}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  %ev : Canon(True{} <> rest, Ap.Enum.write(n, True{}, _, rem, bits2), rem2, Ap.Enum.after(n, True{}, _, rem))
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => True{} <> l, rest, Ap.Small.write(i, Ap.Rem.next(rem), bits2), (%eb : {rest == Ap.Small.write(i, Ap.Rem.next(rem), _) : Ap.Bits()}; s1)), (%er : {_ == Ap.Rem.add(7n, Ap.Rem.next(rem)) : Nat}; s2))

def Enum.sx.ext(+n: Nat, +rem: Nat, +rest: Ap.Bits(), rs: Ap.Rd(U32), +ers: {Ap.Small.read(Ap.Cur{Ap.Rem.next(rem), rest}) == rs : Ap.Rd(U32)}, +v: Ap.Enum, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Enum.ext(rs) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Enum)}) -> Canon(True{} <> rest, Ap.Enum.write(n, True{}, v, rem, bits2), rem2, Ap.Enum.after(n, True{}, v, rem)):
  match rs:
    case Fail{err}:
      PA.Rd.absurd(Ap.Enum, Canon(True{} <> rest, Ap.Enum.write(n, True{}, v, rem, bits2), rem2, Ap.Enum.after(n, True{}, v, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+i, c)}:
      match c:
        case Ap.Cur{+r3, +b3}:
          Enum.sx.ext.go(n, rem, rest, i, r3, b3, v, rem2, bits2, e, Small.sx(Ap.Rem.next(rem), rest, i, r3, b3, ers))

def Enum.sx.bit(+n: Nat, +diff: U32, +rem: Nat, bits: Ap.Bits(), +v: Ap.Enum, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.Enum.bit(n, diff, Ap.Bit.read(Ap.Cur{rem, bits})) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Enum)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(bits, Ap.Enum.write(n, True{}, v, rem, bits2), rem2, Ap.Enum.after(n, True{}, v, rem)):
  match bits:
    case Nil{}:
      PA.Rd.absurd(Ap.Enum, Canon([], Ap.Enum.write(n, True{}, v, rem, bits2), rem2, Ap.Enum.after(n, True{}, v, rem)), B.Short{}, v, Ap.Cur{rem2, bits2}, e)
    case b <> +rest:
      match b:
        case False{}:
          Enum.sx.root1(n, diff, rem, rest, Ap.Int.read(n, diff, Ap.Cur{Ap.Rem.next(rem), rest}), {==}, v, rem2, bits2, e, w)
        case True{}:
          Enum.sx.ext(n, rem, rest, Ap.Small.read(Ap.Cur{Ap.Rem.next(rem), rest}), {==}, v, rem2, bits2, e)

def Enum.sx(+n: Nat, +diff: U32, ext: Bool, +rem: Nat, +bits: Ap.Bits(), +v: Ap.Enum, +rem2: Nat, +bits2: Ap.Bits(), e: {Ap.Enum.read(n, diff, ext, Ap.Cur{rem, bits}) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Enum)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(bits, Ap.Enum.write(n, ext, v, rem, bits2), rem2, Ap.Enum.after(n, ext, v, rem)):
  match ext:
    case False{}:
      Enum.sx.root0(n, diff, rem, bits, Ap.Int.read(n, diff, Ap.Cur{rem, bits}), {==}, v, rem2, bits2, e, w)
    case True{}:
      Enum.sx.bit(n, diff, rem, bits, v, rem2, bits2, e, w)

# Extensible values
# -----------------

def XInt.root_sx(al: Bool, +n: Nat, +diff: U32, +r: Nat, +b: Ap.Bits(), +i: U32, +r3: Nat, +b3: Ap.Bits(), e: {Ap.XInt.root_read(al, n, diff, Ap.Cur{r, b}) == Done{(i, Ap.Cur{r3, b3})} : Ap.Rd(U32)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(b, Ap.XInt.root_write(al, n, i, r, b3), r3, Ap.XInt.root_after(al, n, r)):
  match al:
    case False{}:
      Int.sx(n, diff, r, b, i, r3, b3, e, w)
    case True{}:
      AInt.sx(n, diff, r, b, i, r3, b3, e, w)

def XInt.sx.root.go(+al: Bool, +n: Nat, +rem: Nat, +rest: Ap.Bits(), +i: U32, +r3: Nat, +b3: Ap.Bits(), +v: Ap.XInt, +rem2: Nat, +bits2: Ap.Bits(), +e: {Done{(Ap.IRoot{i}, Ap.Cur{r3, b3})} == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.XInt)}, si: Canon(rest, Ap.XInt.root_write(al, n, i, Ap.Rem.next(rem), b3), r3, Ap.XInt.root_after(al, n, Ap.Rem.next(rem)))) -> Canon(False{} <> rest, Ap.XInt.write(al, n, v, rem, bits2), rem2, Ap.XInt.after(al, n, v, rem)):
  (i1, i2) = si
  ev = Equal.cong(Ap.Rd(Ap.XInt), Ap.XInt, x => PA.Rd.value(Ap.XInt, x, v), Done{(Ap.IRoot{i}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  +ec = Equal.cong(Ap.Rd(Ap.XInt), Ap.Cur, x => PA.Rd.cur(Ap.XInt, x, Ap.Cur{rem2, bits2}), Done{(Ap.IRoot{i}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  %ev : Canon(False{} <> rest, Ap.XInt.write(al, n, _, rem, bits2), rem2, Ap.XInt.after(al, n, _, rem))
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, rest, Ap.XInt.root_write(al, n, i, Ap.Rem.next(rem), bits2), (%eb : {rest == Ap.XInt.root_write(al, n, i, Ap.Rem.next(rem), _) : Ap.Bits()}; i1)), (%er : {_ == Ap.XInt.root_after(al, n, Ap.Rem.next(rem)) : Nat}; i2))

def XInt.sx.root(+al: Bool, +n: Nat, +diff: U32, +rem: Nat, +rest: Ap.Bits(), ri: Ap.Rd(U32), +eri: {Ap.XInt.root_read(al, n, diff, Ap.Cur{Ap.Rem.next(rem), rest}) == ri : Ap.Rd(U32)}, +v: Ap.XInt, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XInt.root(ri) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.XInt)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(False{} <> rest, Ap.XInt.write(al, n, v, rem, bits2), rem2, Ap.XInt.after(al, n, v, rem)):
  match ri:
    case Fail{err}:
      PA.Rd.absurd(Ap.XInt, Canon(False{} <> rest, Ap.XInt.write(al, n, v, rem, bits2), rem2, Ap.XInt.after(al, n, v, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+i, c)}:
      match c:
        case Ap.Cur{+r3, +b3}:
          XInt.sx.root.go(al, n, rem, rest, i, r3, b3, v, rem2, bits2, e, XInt.root_sx(al, n, diff, Ap.Rem.next(rem), rest, i, r3, b3, eri, w))

def XInt.sx.ext.go(+al: Bool, +n: Nat, +rem: Nat, +rest: Ap.Bits(), +bs: B.Bytes(), +r3: Nat, +b3: Ap.Bits(), +v: Ap.XInt, +rem2: Nat, +bits2: Ap.Bits(), +e: {Done{(Ap.IExt{bs}, Ap.Cur{r3, b3})} == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.XInt)}, so: Canon(rest, Ap.Open.write(bs, Ap.Rem.next(rem), b3), r3, 0n)) -> Canon(True{} <> rest, Ap.XInt.write(al, n, v, rem, bits2), rem2, Ap.XInt.after(al, n, v, rem)):
  (o1, o2) = so
  ev = Equal.cong(Ap.Rd(Ap.XInt), Ap.XInt, x => PA.Rd.value(Ap.XInt, x, v), Done{(Ap.IExt{bs}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  +ec = Equal.cong(Ap.Rd(Ap.XInt), Ap.Cur, x => PA.Rd.cur(Ap.XInt, x, Ap.Cur{rem2, bits2}), Done{(Ap.IExt{bs}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  %ev : Canon(True{} <> rest, Ap.XInt.write(al, n, _, rem, bits2), rem2, Ap.XInt.after(al, n, _, rem))
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => True{} <> l, rest, Ap.Open.write(bs, Ap.Rem.next(rem), bits2), (%eb : {rest == Ap.Open.write(bs, Ap.Rem.next(rem), _) : Ap.Bits()}; o1)), (%er : {_ == 0n : Nat}; o2))

def XInt.sx.ext(+al: Bool, +n: Nat, +rem: Nat, +rest: Ap.Bits(), ro: Ap.Rd(B.Bytes()), +ero: {Ap.Open.read(Ap.Cur{Ap.Rem.next(rem), rest}) == ro : Ap.Rd(B.Bytes())}, +v: Ap.XInt, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XInt.ext(ro) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.XInt)}) -> Canon(True{} <> rest, Ap.XInt.write(al, n, v, rem, bits2), rem2, Ap.XInt.after(al, n, v, rem)):
  match ro:
    case Fail{err}:
      PA.Rd.absurd(Ap.XInt, Canon(True{} <> rest, Ap.XInt.write(al, n, v, rem, bits2), rem2, Ap.XInt.after(al, n, v, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+bs, c)}:
      match c:
        case Ap.Cur{+r3, +b3}:
          XInt.sx.ext.go(al, n, rem, rest, bs, r3, b3, v, rem2, bits2, e, Open.sx(Ap.Rem.next(rem), rest, bs, r3, b3, ero))

def XInt.sx(+al: Bool, +n: Nat, +diff: U32, +rem: Nat, bits: Ap.Bits(), +v: Ap.XInt, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XInt.read(al, n, diff, Ap.Cur{rem, bits}) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.XInt)}, w: {Nat.is_le(n, 32n) == True{} : Bool}) -> Canon(bits, Ap.XInt.write(al, n, v, rem, bits2), rem2, Ap.XInt.after(al, n, v, rem)):
  match bits:
    case Nil{}:
      PA.Rd.absurd(Ap.XInt, Canon([], Ap.XInt.write(al, n, v, rem, bits2), rem2, Ap.XInt.after(al, n, v, rem)), B.Short{}, v, Ap.Cur{rem2, bits2}, e)
    case b <> +rest:
      match b:
        case False{}:
          XInt.sx.root(al, n, diff, rem, rest, Ap.XInt.root_read(al, n, diff, Ap.Cur{Ap.Rem.next(rem), rest}), {==}, v, rem2, bits2, e, w)
        case True{}:
          XInt.sx.ext(al, n, rem, rest, Ap.Open.read(Ap.Cur{Ap.Rem.next(rem), rest}), {==}, v, rem2, bits2, e)

def XBig.sx.root.go(+n: Nat, +rem: Nat, +rest: Ap.Bits(), +bs: B.Bytes(), +r3: Nat, +b3: Ap.Bits(), +v: Ap.XBig, +rem2: Nat, +bits2: Ap.Bits(), +e: {Done{(Ap.BRoot{bs}, Ap.Cur{r3, b3})} == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.XBig)}, sb: Canon(rest, Ap.Big.write(n, bs, Ap.Rem.next(rem), b3), r3, 0n)) -> Canon(False{} <> rest, Ap.XBig.write(n, v, rem, bits2), rem2, Ap.XBig.after(v, rem)):
  (b1e, b2e) = sb
  ev = Equal.cong(Ap.Rd(Ap.XBig), Ap.XBig, x => PA.Rd.value(Ap.XBig, x, v), Done{(Ap.BRoot{bs}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  +ec = Equal.cong(Ap.Rd(Ap.XBig), Ap.Cur, x => PA.Rd.cur(Ap.XBig, x, Ap.Cur{rem2, bits2}), Done{(Ap.BRoot{bs}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  %ev : Canon(False{} <> rest, Ap.XBig.write(n, _, rem, bits2), rem2, Ap.XBig.after(_, rem))
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, rest, Ap.Big.write(n, bs, Ap.Rem.next(rem), bits2), (%eb : {rest == Ap.Big.write(n, bs, Ap.Rem.next(rem), _) : Ap.Bits()}; b1e)), (%er : {_ == 0n : Nat}; b2e))

def XBig.sx.root(+n: Nat, +diff: Nat, +rem: Nat, +rest: Ap.Bits(), rb: Ap.Rd(B.Bytes()), +erb: {Ap.Big.read(n, diff, Ap.Cur{Ap.Rem.next(rem), rest}) == rb : Ap.Rd(B.Bytes())}, +v: Ap.XBig, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XBig.root(rb) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.XBig)}) -> Canon(False{} <> rest, Ap.XBig.write(n, v, rem, bits2), rem2, Ap.XBig.after(v, rem)):
  match rb:
    case Fail{err}:
      PA.Rd.absurd(Ap.XBig, Canon(False{} <> rest, Ap.XBig.write(n, v, rem, bits2), rem2, Ap.XBig.after(v, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+bs, c)}:
      match c:
        case Ap.Cur{+r3, +b3}:
          XBig.sx.root.go(n, rem, rest, bs, r3, b3, v, rem2, bits2, e, Big.sx(n, diff, Ap.Rem.next(rem), rest, bs, r3, b3, erb))

def XBig.sx.ext.go(+n: Nat, +rem: Nat, +rest: Ap.Bits(), +bs: B.Bytes(), +r3: Nat, +b3: Ap.Bits(), +v: Ap.XBig, +rem2: Nat, +bits2: Ap.Bits(), +e: {Done{(Ap.BExt{bs}, Ap.Cur{r3, b3})} == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.XBig)}, so: Canon(rest, Ap.Open.write(bs, Ap.Rem.next(rem), b3), r3, 0n)) -> Canon(True{} <> rest, Ap.XBig.write(n, v, rem, bits2), rem2, Ap.XBig.after(v, rem)):
  (o1, o2) = so
  ev = Equal.cong(Ap.Rd(Ap.XBig), Ap.XBig, x => PA.Rd.value(Ap.XBig, x, v), Done{(Ap.BExt{bs}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  +ec = Equal.cong(Ap.Rd(Ap.XBig), Ap.Cur, x => PA.Rd.cur(Ap.XBig, x, Ap.Cur{rem2, bits2}), Done{(Ap.BExt{bs}, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
  eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  %ev : Canon(True{} <> rest, Ap.XBig.write(n, _, rem, bits2), rem2, Ap.XBig.after(_, rem))
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => True{} <> l, rest, Ap.Open.write(bs, Ap.Rem.next(rem), bits2), (%eb : {rest == Ap.Open.write(bs, Ap.Rem.next(rem), _) : Ap.Bits()}; o1)), (%er : {_ == 0n : Nat}; o2))

def XBig.sx.ext(+n: Nat, +rem: Nat, +rest: Ap.Bits(), ro: Ap.Rd(B.Bytes()), +ero: {Ap.Open.read(Ap.Cur{Ap.Rem.next(rem), rest}) == ro : Ap.Rd(B.Bytes())}, +v: Ap.XBig, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XBig.ext(ro) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.XBig)}) -> Canon(True{} <> rest, Ap.XBig.write(n, v, rem, bits2), rem2, Ap.XBig.after(v, rem)):
  match ro:
    case Fail{err}:
      PA.Rd.absurd(Ap.XBig, Canon(True{} <> rest, Ap.XBig.write(n, v, rem, bits2), rem2, Ap.XBig.after(v, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+bs, c)}:
      match c:
        case Ap.Cur{+r3, +b3}:
          XBig.sx.ext.go(n, rem, rest, bs, r3, b3, v, rem2, bits2, e, Open.sx(Ap.Rem.next(rem), rest, bs, r3, b3, ero))

def XBig.sx(+n: Nat, +diff: Nat, +rem: Nat, bits: Ap.Bits(), +v: Ap.XBig, +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XBig.read(n, diff, Ap.Cur{rem, bits}) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.XBig)}) -> Canon(bits, Ap.XBig.write(n, v, rem, bits2), rem2, Ap.XBig.after(v, rem)):
  match bits:
    case Nil{}:
      PA.Rd.absurd(Ap.XBig, Canon([], Ap.XBig.write(n, v, rem, bits2), rem2, Ap.XBig.after(v, rem)), B.Short{}, v, Ap.Cur{rem2, bits2}, e)
    case b <> +rest:
      match b:
        case False{}:
          XBig.sx.root(n, diff, rem, rest, Ap.Big.read(n, diff, Ap.Cur{Ap.Rem.next(rem), rest}), {==}, v, rem2, bits2, e)
        case True{}:
          XBig.sx.ext(n, rem, rest, Ap.Open.read(Ap.Cur{Ap.Rem.next(rem), rest}), {==}, v, rem2, bits2, e)

def XBits.sx.root(+n: Nat, +rem: Nat, +rest: Ap.Bits(), +v: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), sb: Canon(rest, Ap.Bits.write(v, Ap.Rem.next(rem), bits2), rem2, Ap.Bits.after(n, Ap.Rem.next(rem))) & {List.length(&2, Bool, v) == n : Nat}) -> Canon(False{} <> rest, Ap.XBits.write(n, v, rem, bits2), rem2, Ap.XBits.after(n, v, rem)):
  (sb2, len) = sb
  (b1e, b2e) = sb2
  +slen = Equal.sym(Nat, List.length(&2, Bool, v), n, len)
  seq = Equal.sym(Bool, Nat.is_eq(List.length(&2, Bool, v), n), True{}, (%slen : {Nat.is_eq(_, n) == True{} : Bool}; P.Nat.is_eq_refl(n)))
  %seq : Canon(False{} <> rest, Ap.XBits.body(v, rem, bits2, _), rem2, Ap.XBits.rem(v, rem, _))
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, rest, List.append(&2, Bool, v, bits2), b1e), (%slen : {rem2 == Ap.Rem.add(_, Ap.Rem.next(rem)) : Nat}; b2e))

def XBits.sx.out(+n: Nat, +rem: Nat, +rest: Ap.Bits(), +bs: Ap.Bits(), +r3: Nat, +b3: Ap.Bits(), ok: Bool, +eok: {Bool.not(Nat.is_eq(List.length(&2, Bool, bs), n)) == ok : Bool}, +v: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XBits.of(bs, Ap.Cur{r3, b3}, ok) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}, su: Canon(rest, Ap.UBitStr.write(bs, Ap.Rem.next(rem), b3), r3, Ap.UBitStr.after(bs, Ap.Rem.next(rem)))) -> Canon(True{} <> rest, Ap.XBits.write(n, v, rem, bits2), rem2, Ap.XBits.after(n, v, rem)):
  match ok:
    case False{}:
      PA.Rd.absurd(Ap.Bits(), Canon(True{} <> rest, Ap.XBits.write(n, v, rem, bits2), rem2, Ap.XBits.after(n, v, rem)), B.Invalid{2}, v, Ap.Cur{rem2, bits2}, e)
    case True{}:
      (u1, u2) = su
      ev = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Bits(), x => PA.Rd.value(Ap.Bits(), x, v), Done{(bs, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
      +ec = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Cur, x => PA.Rd.cur(Ap.Bits(), x, Ap.Cur{rem2, bits2}), Done{(bs, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
      eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      %ev : Canon(True{} <> rest, Ap.XBits.write(n, _, rem, bits2), rem2, Ap.XBits.after(n, _, rem))
      sne = Equal.sym(Bool, Nat.is_eq(List.length(&2, Bool, bs), n), False{}, Bool.false_of_not(Nat.is_eq(List.length(&2, Bool, bs), n), eok))
      %sne : Canon(True{} <> rest, Ap.XBits.body(bs, rem, bits2, _), rem2, Ap.XBits.rem(bs, rem, _))
      (Equal.cong(Ap.Bits(), Ap.Bits(), l => True{} <> l, rest, Ap.UBitStr.write(bs, Ap.Rem.next(rem), bits2), (%eb : {rest == Ap.UBitStr.write(bs, Ap.Rem.next(rem), _) : Ap.Bits()}; u1)), (%er : {_ == Ap.Rem.add(List.length(&2, Bool, bs), 0n) : Nat}; u2))

def XBits.sx.outside(+n: Nat, +rem: Nat, +rest: Ap.Bits(), ru: Ap.Rd(Ap.Bits()), +eru: {Ap.UBitStr.read(Ap.Cur{Ap.Rem.next(rem), rest}) == ru : Ap.Rd(Ap.Bits())}, +v: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XBits.outside(n, ru) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(True{} <> rest, Ap.XBits.write(n, v, rem, bits2), rem2, Ap.XBits.after(n, v, rem)):
  match ru:
    case Fail{err}:
      PA.Rd.absurd(Ap.Bits(), Canon(True{} <> rest, Ap.XBits.write(n, v, rem, bits2), rem2, Ap.XBits.after(n, v, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+bs, c)}:
      match c:
        case Ap.Cur{+r3, +b3}:
          XBits.sx.out(n, rem, rest, bs, r3, b3, Bool.not(Nat.is_eq(List.length(&2, Bool, bs), n)), {==}, v, rem2, bits2, e, UBitStr.sx(Ap.Rem.next(rem), rest, bs, r3, b3, eru))

def XBits.sx(+n: Nat, +rem: Nat, bits: Ap.Bits(), +v: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XBits.read(n, Ap.Cur{rem, bits}) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.XBits.write(n, v, rem, bits2), rem2, Ap.XBits.after(n, v, rem)):
  match bits:
    case Nil{}:
      PA.Rd.absurd(Ap.Bits(), Canon([], Ap.XBits.write(n, v, rem, bits2), rem2, Ap.XBits.after(n, v, rem)), B.Short{}, v, Ap.Cur{rem2, bits2}, e)
    case b <> +rest:
      match b:
        case False{}:
          XBits.sx.root(n, rem, rest, v, rem2, bits2, Bits.sx(n, Ap.Rem.next(rem), rest, v, rem2, bits2, e))
        case True{}:
          XBits.sx.outside(n, rem, rest, Ap.UBitStr.read(Ap.Cur{Ap.Rem.next(rem), rest}), {==}, v, rem2, bits2, e)

def XBitStr.sx.root(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +rest: Ap.Bits(), +v: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), sb: Canon(rest, Ap.BitStr.write(al, n, lo, v, Ap.Rem.next(rem), bits2), rem2, Ap.BitStr.after(v, Ap.Rem.next(rem))), sv: {Ap.Size.valid(lo, diff, List.length(&2, Bool, v)) == True{} : Bool}) -> Canon(False{} <> rest, Ap.XBitStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XBitStr.after(v, rem)):
  (b1e, b2e) = sb
  ssv = Equal.sym(Bool, Ap.Size.valid(lo, diff, List.length(&2, Bool, v)), True{}, sv)
  %ssv : Canon(False{} <> rest, Ap.XBitStr.body(al, n, lo, v, rem, bits2, _), rem2, Ap.XBitStr.after(v, rem))
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, rest, Ap.BitStr.write(al, n, lo, v, Ap.Rem.next(rem), bits2), b1e), b2e)

def XBitStr.sx.out(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +rest: Ap.Bits(), +bs: Ap.Bits(), +r3: Nat, +b3: Ap.Bits(), ok: Bool, +eok: {Bool.not(Ap.Size.valid(lo, diff, List.length(&2, Bool, bs))) == ok : Bool}, +v: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XBits.of(bs, Ap.Cur{r3, b3}, ok) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}, su: Canon(rest, Ap.UBitStr.write(bs, Ap.Rem.next(rem), b3), r3, Ap.UBitStr.after(bs, Ap.Rem.next(rem)))) -> Canon(True{} <> rest, Ap.XBitStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XBitStr.after(v, rem)):
  match ok:
    case False{}:
      PA.Rd.absurd(Ap.Bits(), Canon(True{} <> rest, Ap.XBitStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XBitStr.after(v, rem)), B.Invalid{2}, v, Ap.Cur{rem2, bits2}, e)
    case True{}:
      (u1, u2) = su
      ev = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Bits(), x => PA.Rd.value(Ap.Bits(), x, v), Done{(bs, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
      +ec = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Cur, x => PA.Rd.cur(Ap.Bits(), x, Ap.Cur{rem2, bits2}), Done{(bs, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
      eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      %ev : Canon(True{} <> rest, Ap.XBitStr.write(al, n, lo, diff, _, rem, bits2), rem2, Ap.XBitStr.after(_, rem))
      sne = Equal.sym(Bool, Ap.Size.valid(lo, diff, List.length(&2, Bool, bs)), False{}, Bool.false_of_not(Ap.Size.valid(lo, diff, List.length(&2, Bool, bs)), eok))
      %sne : Canon(True{} <> rest, Ap.XBitStr.body(al, n, lo, bs, rem, bits2, _), rem2, Ap.XBitStr.after(bs, rem))
      (Equal.cong(Ap.Bits(), Ap.Bits(), l => True{} <> l, rest, Ap.UBitStr.write(bs, Ap.Rem.next(rem), bits2), (%eb : {rest == Ap.UBitStr.write(bs, Ap.Rem.next(rem), _) : Ap.Bits()}; u1)), (%er : {_ == Ap.Rem.add(List.length(&2, Bool, bs), 0n) : Nat}; u2))

def XBitStr.sx.outside(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +rest: Ap.Bits(), ru: Ap.Rd(Ap.Bits()), +eru: {Ap.UBitStr.read(Ap.Cur{Ap.Rem.next(rem), rest}) == ru : Ap.Rd(Ap.Bits())}, +v: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XBitStr.outside(lo, diff, ru) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(True{} <> rest, Ap.XBitStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XBitStr.after(v, rem)):
  match ru:
    case Fail{err}:
      PA.Rd.absurd(Ap.Bits(), Canon(True{} <> rest, Ap.XBitStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XBitStr.after(v, rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+bs, c)}:
      match c:
        case Ap.Cur{+r3, +b3}:
          XBitStr.sx.out(al, n, lo, diff, rem, rest, bs, r3, b3, Bool.not(Ap.Size.valid(lo, diff, List.length(&2, Bool, bs))), {==}, v, rem2, bits2, e, UBitStr.sx(Ap.Rem.next(rem), rest, bs, r3, b3, eru))

def XBitStr.sx(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, bits: Ap.Bits(), +v: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XBitStr.read(al, n, lo, diff, Ap.Cur{rem, bits}) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(Ap.Bits())}) -> Canon(bits, Ap.XBitStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XBitStr.after(v, rem)):
  match bits:
    case Nil{}:
      PA.Rd.absurd(Ap.Bits(), Canon([], Ap.XBitStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XBitStr.after(v, rem)), B.Short{}, v, Ap.Cur{rem2, bits2}, e)
    case b <> +rest:
      match b:
        case False{}:
          XBitStr.sx.root(al, n, lo, diff, rem, rest, v, rem2, bits2, BitStr.sx(al, n, lo, diff, Ap.Rem.next(rem), rest, v, rem2, bits2, e), L.aper.bitstr.decode_valid(al, n, lo, diff, Ap.Cur{Ap.Rem.next(rem), rest}, v, Ap.Cur{rem2, bits2}, e))
        case True{}:
          XBitStr.sx.outside(al, n, lo, diff, rem, rest, Ap.UBitStr.read(Ap.Cur{Ap.Rem.next(rem), rest}), {==}, v, rem2, bits2, e)

def XStr.sx.root(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +rest: Ap.Bits(), +v: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), ss: Canon(rest, Ap.Str.write(al, n, lo, v, Ap.Rem.next(rem), bits2), rem2, 0n), sv: {Ap.Size.valid(lo, diff, List.length(&2, U32, v)) == True{} : Bool}) -> Canon(False{} <> rest, Ap.XStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XStr.after(rem)):
  (s1, s2) = ss
  ssv = Equal.sym(Bool, Ap.Size.valid(lo, diff, List.length(&2, U32, v)), True{}, sv)
  %ssv : Canon(False{} <> rest, Ap.XStr.body(al, n, lo, v, rem, bits2, _), rem2, Ap.XStr.after(rem))
  (Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, rest, Ap.Str.write(al, n, lo, v, Ap.Rem.next(rem), bits2), s1), s2)

def XStr.sx.out(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +rest: Ap.Bits(), +s: B.Bytes(), +r3: Nat, +b3: Ap.Bits(), ok: Bool, +eok: {Bool.not(Ap.Size.valid(lo, diff, List.length(&2, U32, s))) == ok : Bool}, +v: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XStr.of(s, Ap.Cur{r3, b3}, ok) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}, su: Canon(rest, Ap.UStr.write(s, Ap.Rem.next(rem), b3), r3, 0n)) -> Canon(True{} <> rest, Ap.XStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XStr.after(rem)):
  match ok:
    case False{}:
      PA.Rd.absurd(B.Bytes(), Canon(True{} <> rest, Ap.XStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XStr.after(rem)), B.Invalid{2}, v, Ap.Cur{rem2, bits2}, e)
    case True{}:
      (u1, u2) = su
      ev = Equal.cong(Ap.Rd(B.Bytes()), B.Bytes(), x => PA.Rd.value(B.Bytes(), x, v), Done{(s, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
      +ec = Equal.cong(Ap.Rd(B.Bytes()), Ap.Cur, x => PA.Rd.cur(B.Bytes(), x, Ap.Cur{rem2, bits2}), Done{(s, Ap.Cur{r3, b3})}, Done{(v, Ap.Cur{rem2, bits2})}, e)
      eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
      %ev : Canon(True{} <> rest, Ap.XStr.write(al, n, lo, diff, _, rem, bits2), rem2, Ap.XStr.after(rem))
      sne = Equal.sym(Bool, Ap.Size.valid(lo, diff, List.length(&2, U32, s)), False{}, Bool.false_of_not(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), eok))
      %sne : Canon(True{} <> rest, Ap.XStr.body(al, n, lo, s, rem, bits2, _), rem2, Ap.XStr.after(rem))
      (Equal.cong(Ap.Bits(), Ap.Bits(), l => True{} <> l, rest, Ap.UStr.write(s, Ap.Rem.next(rem), bits2), (%eb : {rest == Ap.UStr.write(s, Ap.Rem.next(rem), _) : Ap.Bits()}; u1)), (%er : {_ == 0n : Nat}; u2))

def XStr.sx.outside(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, +rest: Ap.Bits(), ru: Ap.Rd(B.Bytes()), +eru: {Ap.UStr.read(Ap.Cur{Ap.Rem.next(rem), rest}) == ru : Ap.Rd(B.Bytes())}, +v: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XStr.outside(lo, diff, ru) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(True{} <> rest, Ap.XStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XStr.after(rem)):
  match ru:
    case Fail{err}:
      PA.Rd.absurd(B.Bytes(), Canon(True{} <> rest, Ap.XStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XStr.after(rem)), err, v, Ap.Cur{rem2, bits2}, e)
    case Done{(+s, c)}:
      match c:
        case Ap.Cur{+r3, +b3}:
          XStr.sx.out(al, n, lo, diff, rem, rest, s, r3, b3, Bool.not(Ap.Size.valid(lo, diff, List.length(&2, U32, s))), {==}, v, rem2, bits2, e, UStr.sx(Ap.Rem.next(rem), rest, s, r3, b3, eru))

def XStr.sx(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +rem: Nat, bits: Ap.Bits(), +v: B.Bytes(), +rem2: Nat, +bits2: Ap.Bits(), +e: {Ap.XStr.read(al, n, lo, diff, Ap.Cur{rem, bits}) == Done{(v, Ap.Cur{rem2, bits2})} : Ap.Rd(B.Bytes())}) -> Canon(bits, Ap.XStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XStr.after(rem)):
  match bits:
    case Nil{}:
      PA.Rd.absurd(B.Bytes(), Canon([], Ap.XStr.write(al, n, lo, diff, v, rem, bits2), rem2, Ap.XStr.after(rem)), B.Short{}, v, Ap.Cur{rem2, bits2}, e)
    case b <> +rest:
      match b:
        case False{}:
          XStr.sx.root(al, n, lo, diff, rem, rest, v, rem2, bits2, Str.sx(al, n, lo, diff, Ap.Rem.next(rem), rest, v, rem2, bits2, e), P.Bool.and_true_l(Ap.Size.valid(lo, diff, List.length(&2, U32, v)), Ap.Str.all(v), L.aper.str.decode_valid(al, n, lo, diff, Ap.Cur{Ap.Rem.next(rem), rest}, v, Ap.Cur{rem2, bits2}, e)))
        case True{}:
          XStr.sx.outside(al, n, lo, diff, rem, rest, Ap.UStr.read(Ap.Cur{Ap.Rem.next(rem), rest}), {==}, v, rem2, bits2, e)
