import Base
import ../bytes.bend as B
import ../pfcp.bend as Pf
import ../LAWS.bend as L
import ./lib.bend as P
import ./bytes.bend as PB

# Proofs of the PFCP laws (ticket 14).

def Ies.Res() -> Data:
  Result<&2, &2, B.Err, List<&2, Pf.Ie>>

def Msg.Res() -> Data:
  Result<&2, &2, B.Err, Pf.Msg>

def Hdr.kind(h: Pf.Hdr) -> U32:
  match h:
    case Pf.Hdr{kind, len}:
      kind

def Hdr.len(h: Pf.Hdr) -> U32:
  match h:
    case Pf.Hdr{kind, len}:
      len

# Lists
# -----

def Drop.zero(ys: B.Bytes()) -> {List.drop(&2, U32, ys, 0n) == ys : B.Bytes()}:
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      {==}

def Drop.app(xs: B.Bytes(), +ys: B.Bytes()) -> {List.drop(&2, U32, List.append(&2, U32, xs, ys), List.length(&2, U32, xs)) == ys : B.Bytes()}:
  match xs:
    case Nil{}:
      Drop.zero(ys)
    case x <> t:
      Drop.app(t, ys)

def Bytes.app_assoc(xs: B.Bytes(), +ys: B.Bytes(), +zs: B.Bytes()) -> {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : B.Bytes()}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      Equal.cong(B.Bytes(), B.Bytes(), l => x <> l, List.append(&2, U32, List.append(&2, U32, t, ys), zs), List.append(&2, U32, t, List.append(&2, U32, ys, zs)), Bytes.app_assoc(t, ys, zs))

# Two bytes make a value that fits sixteen bits.
def Fits16.of_bytes(+b0: U32, +b1: U32, m0: {U32.and(255, b0) == b0 : U32}, m1: {U32.and(255, b1) == b1 : U32}) -> {B.fits16(B.cat8(b0, b1)) == True{} : Bool}:
  sc = Equal.sym(U32, U32.and(65535, B.cat8(b0, b1)), B.cat8(b0, b1), P.U32.cat8_fits16(b0, b1, m0, m1))
  %sc : {U32.is_eq(_, B.cat8(b0, b1)) == True{} : Bool}
  P.U32.is_eq_refl(B.cat8(b0, b1))

# Information elements
# --------------------

def Ie.rt(+kind: U32, +len: U32, +body: B.Bytes(), +W: B.Bytes(), +v: {Pf.Ie.valid(Pf.Ie{kind, len, body}) == True{} : Bool}) -> {Pf.Ie.read(Pf.Ie.write(Pf.Ie{kind, len, body}, W)) == Done{(Pf.Ie{kind, len, body}, W)} : B.Read(Pf.Ie)}:
  +fk = P.Bool.and_true_l(B.fits16(kind), Bool.and(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body))), v)
  +v2 = P.Bool.and_true_r(B.fits16(kind), Bool.and(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body))), v)
  +fl = P.Bool.and_true_l(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v2)
  tn = P.Bool.and_true_r(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v2)
  su1 = Equal.sym(B.Read(U32), B.u16(B.write_u16(kind, B.write_u16(len, List.append(&2, U32, body, W)))), Done{(U32.and(65535, kind), B.write_u16(len, List.append(&2, U32, body, W)))}, PB.Bits.u16(kind, B.write_u16(len, List.append(&2, U32, body, W))))
  %su1 : {Pf.Ie.of_header(Pf.Ie.hdr_type(_)) == Done{(Pf.Ie{kind, len, body}, W)} : B.Read(Pf.Ie)}
  sek = Equal.sym(U32, U32.and(65535, kind), kind, P.U32.eq_of_is_eq(U32.and(65535, kind), kind, fk))
  %sek : {Pf.Ie.of_header(Pf.Ie.hdr_len(_, B.u16(B.write_u16(len, List.append(&2, U32, body, W))))) == Done{(Pf.Ie{kind, len, body}, W)} : B.Read(Pf.Ie)}
  su2 = Equal.sym(B.Read(U32), B.u16(B.write_u16(len, List.append(&2, U32, body, W))), Done{(U32.and(65535, len), List.append(&2, U32, body, W))}, PB.Bits.u16(len, List.append(&2, U32, body, W)))
  %su2 : {Pf.Ie.of_header(Pf.Ie.hdr_len(kind, _)) == Done{(Pf.Ie{kind, len, body}, W)} : B.Read(Pf.Ie)}
  sel = Equal.sym(U32, U32.and(65535, len), len, P.U32.eq_of_is_eq(U32.and(65535, len), len, fl))
  %sel : {Pf.Ie.of_header(Pf.Ie.hdr_len(kind, Done{(_, List.append(&2, U32, body, W))})) == Done{(Pf.Ie{kind, len, body}, W)} : B.Read(Pf.Ie)}
  sfk = Equal.sym(Bool, B.fits16(kind), True{}, fk)
  %sfk : {Pf.Ie.checked(kind, len, List.append(&2, U32, body, W), Bool.and(_, B.fits16(len))) == Done{(Pf.Ie{kind, len, body}, W)} : B.Read(Pf.Ie)}
  sfl = Equal.sym(Bool, B.fits16(len), True{}, fl)
  %sfl : {Pf.Ie.checked(kind, len, List.append(&2, U32, body, W), Bool.and(True{}, _)) == Done{(Pf.Ie{kind, len, body}, W)} : B.Read(Pf.Ie)}
  stn = Equal.sym(Nat, U32.to_nat(len), List.length(&2, U32, body), P.Nat.eq_of_is_eq(U32.to_nat(len), List.length(&2, U32, body), tn))
  %stn : {Pf.Ie.of_body(kind, len, B.take(_, List.append(&2, U32, body, W))) == Done{(Pf.Ie{kind, len, body}, W)} : B.Read(Pf.Ie)}
  ta = Equal.sym(B.Read(B.Bytes()), B.take(List.length(&2, U32, body), List.append(&2, U32, body, W)), Done{(body, W)}, P.Take.append(body, W))
  %ta : {Pf.Ie.of_body(kind, len, _) == Done{(Pf.Ie{kind, len, body}, W)} : B.Read(Pf.Ie)}
  {==}

# What an IE reader answered: a valid IE, whose body is its declared length,
# that consumed exactly four octets plus that length of the input.
def Ie.Spec(bs: B.Bytes(), ie: Pf.Ie, rest: B.Bytes()) -> Type:
  {Pf.Ie.valid(ie) == True{} : Bool} & ({List.drop(&2, U32, bs, Nat.add(4n, U32.to_nat(Pf.Ie.len(ie)))) == rest : B.Bytes()} & ({List.length(&2, U32, Pf.Ie.body(ie)) == U32.to_nat(Pf.Ie.len(ie)) : Nat} & {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(List.length(&2, U32, Pf.Ie.body(ie)), List.length(&2, U32, rest))) : Nat}))

def Ie.spec.fin(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), +kind: U32, +len: U32, +body: B.Bytes(), +rest: B.Bytes(), fk: {B.fits16(kind) == True{} : Bool}, fl: {B.fits16(len) == True{} : Bool}, la: {List.length(&2, U32, body) == U32.to_nat(len) : Nat} & {List.append(&2, U32, body, rest) == t : B.Bytes()}) -> Ie.Spec(a <> b <> c <> d <> t, Pf.Ie{kind, len, body}, rest):
  (+ln, +ap) = la
  (P.Bool.and_intro(B.fits16(kind), Bool.and(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body))), fk, P.Bool.and_intro(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), fl, (%ln : {Nat.is_eq(_, List.length(&2, U32, body)) == True{} : Bool}; P.Nat.is_eq_refl(List.length(&2, U32, body))))), ((%ln : {List.drop(&2, U32, t, _) == rest : B.Bytes()}; (%ap : {List.drop(&2, U32, _, List.length(&2, U32, body)) == rest : B.Bytes()}; Drop.app(body, rest))), (ln, (%ap : {List.length(&2, U32, a <> b <> c <> d <> _) == Nat.add(4n, Nat.add(List.length(&2, U32, body), List.length(&2, U32, rest))) : Nat}; Equal.cong(Nat, Nat, n => 1n+1n+1n+1n+n, List.length(&2, U32, List.append(&2, U32, body, rest)), Nat.add(List.length(&2, U32, body), List.length(&2, U32, rest)), P.List.append_len(body, rest))))))

def Ie.spec.body(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), +kind: U32, +len: U32, rt: B.Read(B.Bytes()), +ert: {B.take(U32.to_nat(len), t) == rt : B.Read(B.Bytes())}, +ie: Pf.Ie, +rest: B.Bytes(), +e: {Pf.Ie.of_body(kind, len, rt) == Done{(ie, rest)} : B.Read(Pf.Ie)}, fk: {B.fits16(kind) == True{} : Bool}, fl: {B.fits16(len) == True{} : Bool}) -> Ie.Spec(a <> b <> c <> d <> t, ie, rest):
  match rt:
    case Fail{err}:
      Empty.absurd(Ie.Spec(a <> b <> c <> d <> t, ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), err, (ie, rest), e))
    case Done{(+body, +rest2)}:
      ev = Equal.cong(B.Read(Pf.Ie), Pf.Ie, x => P.Read.value(Pf.Ie, x, ie), Done{(Pf.Ie{kind, len, body}, rest2)}, Done{(ie, rest)}, e)
      er = Equal.cong(B.Read(Pf.Ie), B.Bytes(), x => P.Read.rest(Pf.Ie, x, rest), Done{(Pf.Ie{kind, len, body}, rest2)}, Done{(ie, rest)}, e)
      %ev : Ie.Spec(a <> b <> c <> d <> t, _, rest)
      %er : Ie.Spec(a <> b <> c <> d <> t, Pf.Ie{kind, len, body}, _)
      Ie.spec.fin(a, b, c, d, t, kind, len, body, rest2, fk, fl, L.bytes.take.length(U32.to_nat(len), t, body, rest2, ert))

def Ie.spec.checked(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), ok: Bool, +eok: {Bool.and(B.fits16(B.cat8(b, a)), B.fits16(B.cat8(d, c))) == ok : Bool}, +ie: Pf.Ie, +rest: B.Bytes(), +e: {Pf.Ie.checked(B.cat8(b, a), B.cat8(d, c), t, ok) == Done{(ie, rest)} : B.Read(Pf.Ie)}) -> Ie.Spec(a <> b <> c <> d <> t, ie, rest):
  match ok:
    case False{}:
      Empty.absurd(Ie.Spec(a <> b <> c <> d <> t, ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), B.Invalid{B.cat8(d, c)}, (ie, rest), e))
    case True{}:
      Ie.spec.body(a, b, c, d, t, B.cat8(b, a), B.cat8(d, c), B.take(U32.to_nat(B.cat8(d, c)), t), {==}, ie, rest, e, P.Bool.and_true_l(B.fits16(B.cat8(b, a)), B.fits16(B.cat8(d, c)), eok), P.Bool.and_true_r(B.fits16(B.cat8(b, a)), B.fits16(B.cat8(d, c)), eok))

def Ie.spec(bs: B.Bytes(), +ie: Pf.Ie, +rest: B.Bytes(), +e: {Pf.Ie.read(bs) == Done{(ie, rest)} : B.Read(Pf.Ie)}) -> Ie.Spec(bs, ie, rest):
  match bs:
    case Nil{}:
      Empty.absurd(Ie.Spec([], ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), B.Short{}, (ie, rest), e))
    case a <> Nil{}:
      Empty.absurd(Ie.Spec([a], ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), B.Short{}, (ie, rest), e))
    case a <> b <> Nil{}:
      Empty.absurd(Ie.Spec([a, b], ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), B.Short{}, (ie, rest), e))
    case a <> b <> c <> Nil{}:
      Empty.absurd(Ie.Spec([a, b, c], ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), B.Short{}, (ie, rest), e))
    case +a <> +b <> +c <> +d <> +t:
      Ie.spec.checked(a, b, c, d, t, Bool.and(B.fits16(B.cat8(b, a)), B.fits16(B.cat8(d, c))), {==}, ie, rest, e)

def Ie.Spec.valid(+bs: B.Bytes(), +ie: Pf.Ie, +rest: B.Bytes(), s: Ie.Spec(bs, ie, rest)) -> {Pf.Ie.valid(ie) == True{} : Bool}:
  (v, s2) = s
  v

def Ie.Spec.consumed(+bs: B.Bytes(), +ie: Pf.Ie, +rest: B.Bytes(), s: Ie.Spec(bs, ie, rest)) -> {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(List.length(&2, U32, Pf.Ie.body(ie)), List.length(&2, U32, rest))) : Nat}:
  (v, s2) = s
  (dr, s3) = s2
  (ln, cn) = s3
  cn

def Ie.dv(+bs: B.Bytes(), +ie: Pf.Ie, +rest: B.Bytes(), +e: {Pf.Ie.read(bs) == Done{(ie, rest)} : B.Read(Pf.Ie)}) -> {Pf.Ie.valid(ie) == True{} : Bool}:
  Ie.Spec.valid(bs, ie, rest, Ie.spec(bs, ie, rest, e))

def Ie.consumed(+bs: B.Bytes(), +ie: Pf.Ie, +rest: B.Bytes(), +e: {Pf.Ie.read(bs) == Done{(ie, rest)} : B.Read(Pf.Ie)}) -> {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(List.length(&2, U32, Pf.Ie.body(ie)), List.length(&2, U32, rest))) : Nat}:
  Ie.Spec.consumed(bs, ie, rest, Ie.spec(bs, ie, rest, e))

# The bytes an IE was read from, before any tail, are its encoding.
def Ie.sx.fin(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), +body: B.Bytes(), +rest: B.Bytes(), +tail: B.Bytes(), la: {List.length(&2, U32, body) == U32.to_nat(B.cat8(d, c)) : Nat} & {List.append(&2, U32, body, rest) == t : B.Bytes()}, ma: {U32.and(255, a) == a : U32}, mb: {U32.and(255, b) == b : U32}, mc: {U32.and(255, c) == c : U32}, md: {U32.and(255, d) == d : U32}) -> {Pf.Ie.write(Pf.Ie{B.cat8(b, a), B.cat8(d, c), body}, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}:
  (ln, ap) = la
  +X : B.Bytes() = List.append(&2, U32, body, List.append(&2, U32, rest, tail))
  w1 = Equal.sym(B.Bytes(), B.write_u16(B.cat8(b, a), B.write_u16(B.cat8(d, c), X)), a <> b <> B.write_u16(B.cat8(d, c), X), P.Bytes.u16_sx(a, b, ma, mb, B.write_u16(B.cat8(d, c), X)))
  %w1 : {_ == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}
  w2 = Equal.sym(B.Bytes(), B.write_u16(B.cat8(d, c), X), c <> d <> X, P.Bytes.u16_sx(c, d, mc, md, X))
  %w2 : {a <> b <> _ == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}
  %ap : {a <> b <> c <> d <> X == a <> b <> c <> d <> List.append(&2, U32, _, tail) : B.Bytes()}
  Equal.cong(B.Bytes(), B.Bytes(), l => a <> b <> c <> d <> l, List.append(&2, U32, body, List.append(&2, U32, rest, tail)), List.append(&2, U32, List.append(&2, U32, body, rest), tail), Equal.sym(B.Bytes(), List.append(&2, U32, List.append(&2, U32, body, rest), tail), List.append(&2, U32, body, List.append(&2, U32, rest, tail)), Bytes.app_assoc(body, rest, tail)))

def Ie.sx.body(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), rt: B.Read(B.Bytes()), +ert: {B.take(U32.to_nat(B.cat8(d, c)), t) == rt : B.Read(B.Bytes())}, +ie: Pf.Ie, +rest: B.Bytes(), +e: {Pf.Ie.of_body(B.cat8(b, a), B.cat8(d, c), rt) == Done{(ie, rest)} : B.Read(Pf.Ie)}, +tail: B.Bytes(), ma: {U32.and(255, a) == a : U32}, mb: {U32.and(255, b) == b : U32}, mc: {U32.and(255, c) == c : U32}, md: {U32.and(255, d) == d : U32}) -> {Pf.Ie.write(ie, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}:
  match rt:
    case Fail{err}:
      Empty.absurd({Pf.Ie.write(ie, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), err, (ie, rest), e))
    case Done{(+body, +rest2)}:
      ev = Equal.cong(B.Read(Pf.Ie), Pf.Ie, x => P.Read.value(Pf.Ie, x, ie), Done{(Pf.Ie{B.cat8(b, a), B.cat8(d, c), body}, rest2)}, Done{(ie, rest)}, e)
      er = Equal.cong(B.Read(Pf.Ie), B.Bytes(), x => P.Read.rest(Pf.Ie, x, rest), Done{(Pf.Ie{B.cat8(b, a), B.cat8(d, c), body}, rest2)}, Done{(ie, rest)}, e)
      %ev : {Pf.Ie.write(_, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}
      %er : {Pf.Ie.write(Pf.Ie{B.cat8(b, a), B.cat8(d, c), body}, List.append(&2, U32, _, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}
      Ie.sx.fin(a, b, c, d, t, body, rest2, tail, L.bytes.take.length(U32.to_nat(B.cat8(d, c)), t, body, rest2, ert), ma, mb, mc, md)

def Ie.sx.checked(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), ok: Bool, +ie: Pf.Ie, +rest: B.Bytes(), +e: {Pf.Ie.checked(B.cat8(b, a), B.cat8(d, c), t, ok) == Done{(ie, rest)} : B.Read(Pf.Ie)}, +tail: B.Bytes(), ma: {U32.and(255, a) == a : U32}, mb: {U32.and(255, b) == b : U32}, mc: {U32.and(255, c) == c : U32}, md: {U32.and(255, d) == d : U32}) -> {Pf.Ie.write(ie, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}:
  match ok:
    case False{}:
      Empty.absurd({Pf.Ie.write(ie, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), B.Invalid{B.cat8(d, c)}, (ie, rest), e))
    case True{}:
      Ie.sx.body(a, b, c, d, t, B.take(U32.to_nat(B.cat8(d, c)), t), {==}, ie, rest, e, tail, ma, mb, mc, md)

def Ie.sx(bs: B.Bytes(), +ie: Pf.Ie, +rest: B.Bytes(), +e: {Pf.Ie.read(bs) == Done{(ie, rest)} : B.Read(Pf.Ie)}, +ab: {B.all_bytes(bs) == True{} : Bool}, +tail: B.Bytes()) -> {Pf.Ie.write(ie, List.append(&2, U32, rest, tail)) == List.append(&2, U32, bs, tail) : B.Bytes()}:
  match bs:
    case Nil{}:
      Empty.absurd({Pf.Ie.write(ie, List.append(&2, U32, rest, tail)) == List.append(&2, U32, [], tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), B.Short{}, (ie, rest), e))
    case a <> Nil{}:
      Empty.absurd({Pf.Ie.write(ie, List.append(&2, U32, rest, tail)) == List.append(&2, U32, [a], tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), B.Short{}, (ie, rest), e))
    case a <> b <> Nil{}:
      Empty.absurd({Pf.Ie.write(ie, List.append(&2, U32, rest, tail)) == List.append(&2, U32, [a, b], tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), B.Short{}, (ie, rest), e))
    case a <> b <> c <> Nil{}:
      Empty.absurd({Pf.Ie.write(ie, List.append(&2, U32, rest, tail)) == List.append(&2, U32, [a, b, c], tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(Pf.Ie), B.Short{}, (ie, rest), e))
    case +a <> +b <> +c <> +d <> +t:
      +ab2 = P.Bool.and_true_r(B.is_byte(a), B.all_bytes(b <> c <> d <> t), ab)
      +ab3 = P.Bool.and_true_r(B.is_byte(b), B.all_bytes(c <> d <> t), ab2)
      +ab4 = P.Bool.and_true_r(B.is_byte(c), B.all_bytes(d <> t), ab3)
      Ie.sx.checked(a, b, c, d, t, Bool.and(B.fits16(B.cat8(b, a)), B.fits16(B.cat8(d, c))), ie, rest, e, tail, P.U32.lt256_mask8(a, P.Bool.and_true_l(B.is_byte(a), B.all_bytes(b <> c <> d <> t), ab)), P.U32.lt256_mask8(b, P.Bool.and_true_l(B.is_byte(b), B.all_bytes(c <> d <> t), ab2)), P.U32.lt256_mask8(c, P.Bool.and_true_l(B.is_byte(c), B.all_bytes(d <> t), ab3)), P.U32.lt256_mask8(d, P.Bool.and_true_l(B.is_byte(d), B.all_bytes(t), ab4)))

# GHSA-4x7x-2p8x-jwrq
def L.pfcp.ie_header.short_input_fails(bs, e):
  match bs:
    case Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case a <> b <> Nil{}:
      {==}
    case a <> b <> c <> Nil{}:
      {==}
    case a <> b <> c <> d <> t:
      P.Nat.not_lt_zero({Pf.Ie.read(a <> b <> c <> d <> t) == Fail{B.Short{}} : B.Read(Pf.Ie)}, List.length(&2, U32, t), e)

# GHSA-37c3-hv4f-688p: the two halves of pfcp.ie.suffix.
def Ie.Spec.exact(+bs: B.Bytes(), +ie: Pf.Ie, +rest: B.Bytes(), s: Ie.Spec(bs, ie, rest)) -> {List.drop(&2, U32, bs, Nat.add(4n, U32.to_nat(Pf.Ie.len(ie)))) == rest : B.Bytes()} & {List.length(&2, U32, Pf.Ie.body(ie)) == U32.to_nat(Pf.Ie.len(ie)) : Nat}:
  (v, s2) = s
  (dr, s3) = s2
  (ln, cn) = s3
  (dr, ln)

def Ie.exact(+bs: B.Bytes(), +ie: Pf.Ie, +rest: B.Bytes(), +e: {Pf.Ie.read(bs) == Done{(ie, rest)} : B.Read(Pf.Ie)}) -> {List.drop(&2, U32, bs, Nat.add(4n, U32.to_nat(Pf.Ie.len(ie)))) == rest : B.Bytes()} & {List.length(&2, U32, Pf.Ie.body(ie)) == U32.to_nat(Pf.Ie.len(ie)) : Nat}:
  Ie.Spec.exact(bs, ie, rest, Ie.spec(bs, ie, rest, e))

def Ie.short.go(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), +len: U32, +tail: B.Bytes(), el: {B.cat8(d, c) == len : U32}, et: {t == tail : B.Bytes()}, +ab: {B.all_bytes(a <> b <> c <> d <> t) == True{} : Bool}, lt: {Nat.is_lt(List.length(&2, U32, tail), U32.to_nat(len)) == True{} : Bool}) -> {Pf.Ie.read(a <> b <> c <> d <> t) == Fail{B.Short{}} : B.Read(Pf.Ie)}:
  +ab2 = P.Bool.and_true_r(B.is_byte(a), B.all_bytes(b <> c <> d <> t), ab)
  +ab3 = P.Bool.and_true_r(B.is_byte(b), B.all_bytes(c <> d <> t), ab2)
  +ab4 = P.Bool.and_true_r(B.is_byte(c), B.all_bytes(d <> t), ab3)
  sfk = Equal.sym(Bool, B.fits16(B.cat8(b, a)), True{}, Fits16.of_bytes(b, a, P.U32.lt256_mask8(b, P.Bool.and_true_l(B.is_byte(b), B.all_bytes(c <> d <> t), ab2)), P.U32.lt256_mask8(a, P.Bool.and_true_l(B.is_byte(a), B.all_bytes(b <> c <> d <> t), ab))))
  %sfk : {Pf.Ie.checked(B.cat8(b, a), B.cat8(d, c), t, Bool.and(_, B.fits16(B.cat8(d, c)))) == Fail{B.Short{}} : B.Read(Pf.Ie)}
  sfl = Equal.sym(Bool, B.fits16(B.cat8(d, c)), True{}, Fits16.of_bytes(d, c, P.U32.lt256_mask8(d, P.Bool.and_true_l(B.is_byte(d), B.all_bytes(t), ab4)), P.U32.lt256_mask8(c, P.Bool.and_true_l(B.is_byte(c), B.all_bytes(d <> t), ab3))))
  %sfl : {Pf.Ie.checked(B.cat8(b, a), B.cat8(d, c), t, Bool.and(True{}, _)) == Fail{B.Short{}} : B.Read(Pf.Ie)}
  set = Equal.sym(B.Bytes(), t, tail, et)
  sel = Equal.sym(U32, B.cat8(d, c), len, el)
  st = Equal.sym(B.Read(B.Bytes()), B.take(U32.to_nat(B.cat8(d, c)), t), Fail{B.Short{}}, PB.Short.take(U32.to_nat(B.cat8(d, c)), t, (%sel : {Nat.is_lt(List.length(&2, U32, t), U32.to_nat(_)) == True{} : Bool}; (%set : {Nat.is_lt(List.length(&2, U32, _), U32.to_nat(len)) == True{} : Bool}; lt))))
  %st : {Pf.Ie.of_body(B.cat8(b, a), B.cat8(d, c), _) == Fail{B.Short{}} : B.Read(Pf.Ie)}
  {==}

def Ie.short(bs: B.Bytes(), +kind: U32, +len: U32, +tail: B.Bytes(), +eh: {Pf.Ie.header(bs) == Done{(Pf.Hdr{kind, len}, tail)} : B.Read(Pf.Hdr)}, +ab: {B.all_bytes(bs) == True{} : Bool}, lt: {Nat.is_lt(List.length(&2, U32, tail), U32.to_nat(len)) == True{} : Bool}) -> {Pf.Ie.read(bs) == Fail{B.Short{}} : B.Read(Pf.Ie)}:
  match bs:
    case Nil{}:
      Empty.absurd({Pf.Ie.read([]) == Fail{B.Short{}} : B.Read(Pf.Ie)}, P.Refute.fail_done(B.Err, B.ReadValue(Pf.Hdr), B.Short{}, (Pf.Hdr{kind, len}, tail), eh))
    case a <> Nil{}:
      Empty.absurd({Pf.Ie.read([a]) == Fail{B.Short{}} : B.Read(Pf.Ie)}, P.Refute.fail_done(B.Err, B.ReadValue(Pf.Hdr), B.Short{}, (Pf.Hdr{kind, len}, tail), eh))
    case a <> b <> Nil{}:
      Empty.absurd({Pf.Ie.read([a, b]) == Fail{B.Short{}} : B.Read(Pf.Ie)}, P.Refute.fail_done(B.Err, B.ReadValue(Pf.Hdr), B.Short{}, (Pf.Hdr{kind, len}, tail), eh))
    case a <> b <> c <> Nil{}:
      Empty.absurd({Pf.Ie.read([a, b, c]) == Fail{B.Short{}} : B.Read(Pf.Ie)}, P.Refute.fail_done(B.Err, B.ReadValue(Pf.Hdr), B.Short{}, (Pf.Hdr{kind, len}, tail), eh))
    case +a <> +b <> +c <> +d <> +t:
      Ie.short.go(a, b, c, d, t, len, tail, Equal.cong(B.Read(Pf.Hdr), U32, x => Hdr.len(P.Read.value(Pf.Hdr, x, Pf.Hdr{kind, len})), Done{(Pf.Hdr{B.cat8(b, a), B.cat8(d, c)}, t)}, Done{(Pf.Hdr{kind, len}, tail)}, eh), Equal.cong(B.Read(Pf.Hdr), B.Bytes(), x => P.Read.rest(Pf.Hdr, x, tail), Done{(Pf.Hdr{B.cat8(b, a), B.cat8(d, c)}, t)}, Done{(Pf.Hdr{kind, len}, tail)}, eh), ab, lt)

def L.pfcp.ie.suffix(bs):
  (ie => rest => e => Ie.exact(bs, ie, rest, e), kind => len => tail => eh => ab => lt => Ie.short(bs, kind, len, tail, eh, ab, lt))
