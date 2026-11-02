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
  (cn, len) = Bits.sx(n, rem, bits, bs, rem2, bits2, e)
  cn

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
  le = (%rl : {Nat.is_le(_, 32n) == True{} : Bool}; (%(Equal.sym(Nat, List.length(&2, Bool, bs), n, len)) : {Nat.is_le(_, 32n) == True{} : Bool}; w))
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
