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

# Lists of IEs
# ------------

def Bytes.all_drop(n: Nat, bs: B.Bytes(), ab: {B.all_bytes(bs) == True{} : Bool}) -> {B.all_bytes(List.drop(&2, U32, bs, n)) == True{} : Bool}:
  match n bs:
    case 0n Nil{}:
      ab
    case 0n b <> t:
      ab
    case 1n+p Nil{}:
      {==}
    case 1n+p +b <> +t:
      Bytes.all_drop(p, t, P.Bool.and_true_r(B.is_byte(b), B.all_bytes(t), ab))

def Ie.rest_bytes.go(+bs: B.Bytes(), +ie: Pf.Ie, +rest: B.Bytes(), s: {List.drop(&2, U32, bs, Nat.add(4n, U32.to_nat(Pf.Ie.len(ie)))) == rest : B.Bytes()} & {List.length(&2, U32, Pf.Ie.body(ie)) == U32.to_nat(Pf.Ie.len(ie)) : Nat}, ab: {B.all_bytes(bs) == True{} : Bool}) -> {B.all_bytes(rest) == True{} : Bool}:
  (dr, ln) = s
  %dr : {B.all_bytes(_) == True{} : Bool}
  Bytes.all_drop(Nat.add(4n, U32.to_nat(Pf.Ie.len(ie))), bs, ab)

def Ie.rest_bytes(+bs: B.Bytes(), +ie: Pf.Ie, +rest: B.Bytes(), +e: {Pf.Ie.read(bs) == Done{(ie, rest)} : B.Read(Pf.Ie)}, ab: {B.all_bytes(bs) == True{} : Bool}) -> {B.all_bytes(rest) == True{} : Bool}:
  Ie.rest_bytes.go(bs, ie, rest, Ie.exact(bs, ie, rest, e), ab)

def Ies.rt(ies: List<&2, Pf.Ie>, fuel: Nat, +v: {Pf.Ies.valid(ies) == True{} : Bool}, +bound: {Nat.is_le(List.length(&2, U32, Pf.Ies.write(ies, [])), fuel) == True{} : Bool}) -> {Pf.Ies.read(fuel, Pf.Ies.write(ies, [])) == Done{ies} : Ies.Res()}:
  match ies fuel:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+f:
      {==}
    case Pf.Ie{+kind, +len, +body} <> +more 0n:
      Empty.absurd({Pf.Ies.read(0n, Pf.Ies.write(Pf.Ie{kind, len, body} <> more, [])) == Done{Pf.Ie{kind, len, body} <> more} : Ies.Res()}, P.Refute.bool(bound))
    case Pf.Ie{+kind, +len, +body} <> +more 1n++f:
      +W = Pf.Ies.write(more, [])
      sr = Equal.sym(B.Read(Pf.Ie), Pf.Ie.read(Pf.Ie.write(Pf.Ie{kind, len, body}, W)), Done{(Pf.Ie{kind, len, body}, W)}, Ie.rt(kind, len, body, W, P.Bool.and_true_l(Pf.Ie.valid(Pf.Ie{kind, len, body}), Pf.Ies.valid(more), v)))
      %sr : {Pf.Ies.next(_, left => Pf.Ies.read(f, left)) == Done{Pf.Ie{kind, len, body} <> more} : Ies.Res()}
      ih = Equal.sym(Ies.Res(), Pf.Ies.read(f, W), Done{more}, Ies.rt(more, f, P.Bool.and_true_r(Pf.Ie.valid(Pf.Ie{kind, len, body}), Pf.Ies.valid(more), v), P.Nat.le_of_append(body, W, 3n, f, bound)))
      %ih : {Pf.Ies.cons(Pf.Ie{kind, len, body}, _) == Done{Pf.Ie{kind, len, body} <> more} : Ies.Res()}
      {==}

def Ies.dv_cons(+ie: Pf.Ie, +ro: Ies.Res(), +ies: List<&2, Pf.Ie>, e: {Pf.Ies.cons(ie, ro) == Done{ies} : Ies.Res()}, hv: {Pf.Ie.valid(ie) == True{} : Bool}, ho: @ies2: List<&2, Pf.Ie> -> {ro == Done{ies2} : Ies.Res()} -> {Pf.Ies.valid(ies2) == True{} : Bool}) -> {Pf.Ies.valid(ies) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Empty.absurd({Pf.Ies.valid(ies) == True{} : Bool}, P.Refute.fail_done(B.Err, List<&2, Pf.Ie>, err, ies, e))
    case Done{+ies2}:
      eo = Equal.cong(Ies.Res(), List<&2, Pf.Ie>, x => P.Res.value(B.Err, List<&2, Pf.Ie>, x, ies), Done{ie <> ies2}, Done{ies}, e)
      %eo : {Pf.Ies.valid(_) == True{} : Bool}
      P.Bool.and_intro(Pf.Ie.valid(ie), Pf.Ies.valid(ies2), hv, ho(ies2, {==}))

def Ies.dv_next(+f: Nat, +bs: B.Bytes(), +rb: B.Read(Pf.Ie), erb: {Pf.Ie.read(bs) == rb : B.Read(Pf.Ie)}, +ies: List<&2, Pf.Ie>, e: {Pf.Ies.next(rb, left => Pf.Ies.read(f, left)) == Done{ies} : Ies.Res()}, ih: @left: B.Bytes() -> @ies2: List<&2, Pf.Ie> -> {Pf.Ies.read(f, left) == Done{ies2} : Ies.Res()} -> {Pf.Ies.valid(ies2) == True{} : Bool}) -> {Pf.Ies.valid(ies) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Empty.absurd({Pf.Ies.valid(ies) == True{} : Bool}, P.Refute.fail_done(B.Err, List<&2, Pf.Ie>, err, ies, e))
    case Done{(+ie, +r2)}:
      Ies.dv_cons(ie, Pf.Ies.read(f, r2), ies, e, Ie.dv(bs, ie, r2, erb), ies2 => e2 => ih(r2, ies2, e2))

def Ies.dv(+fuel: Nat, +bs: B.Bytes(), +ies: List<&2, Pf.Ie>, e: {Pf.Ies.read(fuel, bs) == Done{ies} : Ies.Res()}) -> {Pf.Ies.valid(ies) == True{} : Bool}:
  match fuel bs:
    case 0n Nil{}:
      eo = Equal.cong(Ies.Res(), List<&2, Pf.Ie>, x => P.Res.value(B.Err, List<&2, Pf.Ie>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {Pf.Ies.valid(_) == True{} : Bool}
      {==}
    case 1n+f Nil{}:
      eo = Equal.cong(Ies.Res(), List<&2, Pf.Ie>, x => P.Res.value(B.Err, List<&2, Pf.Ie>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {Pf.Ies.valid(_) == True{} : Bool}
      {==}
    case 0n b <> r:
      Empty.absurd({Pf.Ies.valid(ies) == True{} : Bool}, P.Refute.fail_done(B.Err, List<&2, Pf.Ie>, B.Invalid{b}, ies, e))
    case 1n++f +b <> +r:
      Ies.dv_next(f, b <> r, Pf.Ie.read(b <> r), {==}, ies, e, left => ies2 => e2 => Ies.dv(f, left, ies2, e2))

# The IEs read from some bytes measure exactly those bytes.
def Ies.len_cons(+bs: B.Bytes(), +ie: Pf.Ie, +r2: B.Bytes(), +ro: Ies.Res(), +ies: List<&2, Pf.Ie>, e: {Pf.Ies.cons(ie, ro) == Done{ies} : Ies.Res()}, cn: {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(List.length(&2, U32, Pf.Ie.body(ie)), List.length(&2, U32, r2))) : Nat}, ih: @ies2: List<&2, Pf.Ie> -> {ro == Done{ies2} : Ies.Res()} -> {Pf.Ies.size(ies2) == List.length(&2, U32, r2) : Nat}) -> {Pf.Ies.size(ies) == List.length(&2, U32, bs) : Nat}:
  match ro:
    case Fail{err}:
      Empty.absurd({Pf.Ies.size(ies) == List.length(&2, U32, bs) : Nat}, P.Refute.fail_done(B.Err, List<&2, Pf.Ie>, err, ies, e))
    case Done{+ies2}:
      eo = Equal.cong(Ies.Res(), List<&2, Pf.Ie>, x => P.Res.value(B.Err, List<&2, Pf.Ie>, x, ies), Done{ie <> ies2}, Done{ies}, e)
      %eo : {Pf.Ies.size(_) == List.length(&2, U32, bs) : Nat}
      scn = Equal.sym(Nat, List.length(&2, U32, bs), Nat.add(4n, Nat.add(List.length(&2, U32, Pf.Ie.body(ie)), List.length(&2, U32, r2))), cn)
      %scn : {Pf.Ies.size(ie <> ies2) == _ : Nat}
      Equal.cong(Nat, Nat, n => Nat.add(4n, Nat.add(List.length(&2, U32, Pf.Ie.body(ie)), n)), Pf.Ies.size(ies2), List.length(&2, U32, r2), ih(ies2, {==}))

def Ies.len_next(+f: Nat, +bs: B.Bytes(), +rb: B.Read(Pf.Ie), erb: {Pf.Ie.read(bs) == rb : B.Read(Pf.Ie)}, +ies: List<&2, Pf.Ie>, e: {Pf.Ies.next(rb, left => Pf.Ies.read(f, left)) == Done{ies} : Ies.Res()}, ih: @left: B.Bytes() -> @ies2: List<&2, Pf.Ie> -> {Pf.Ies.read(f, left) == Done{ies2} : Ies.Res()} -> {Pf.Ies.size(ies2) == List.length(&2, U32, left) : Nat}) -> {Pf.Ies.size(ies) == List.length(&2, U32, bs) : Nat}:
  match rb:
    case Fail{err}:
      Empty.absurd({Pf.Ies.size(ies) == List.length(&2, U32, bs) : Nat}, P.Refute.fail_done(B.Err, List<&2, Pf.Ie>, err, ies, e))
    case Done{(+ie, +r2)}:
      Ies.len_cons(bs, ie, r2, Pf.Ies.read(f, r2), ies, e, Ie.consumed(bs, ie, r2, erb), ies2 => e2 => ih(r2, ies2, e2))

def Ies.len(+fuel: Nat, +bs: B.Bytes(), +ies: List<&2, Pf.Ie>, e: {Pf.Ies.read(fuel, bs) == Done{ies} : Ies.Res()}) -> {Pf.Ies.size(ies) == List.length(&2, U32, bs) : Nat}:
  match fuel bs:
    case 0n Nil{}:
      eo = Equal.cong(Ies.Res(), List<&2, Pf.Ie>, x => P.Res.value(B.Err, List<&2, Pf.Ie>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {Pf.Ies.size(_) == 0n : Nat}
      {==}
    case 1n+f Nil{}:
      eo = Equal.cong(Ies.Res(), List<&2, Pf.Ie>, x => P.Res.value(B.Err, List<&2, Pf.Ie>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {Pf.Ies.size(_) == 0n : Nat}
      {==}
    case 0n b <> r:
      Empty.absurd({Pf.Ies.size(ies) == 1n+List.length(&2, U32, r) : Nat}, P.Refute.fail_done(B.Err, List<&2, Pf.Ie>, B.Invalid{b}, ies, e))
    case 1n++f +b <> +r:
      Ies.len_next(f, b <> r, Pf.Ie.read(b <> r), {==}, ies, e, left => ies2 => e2 => Ies.len(f, left, ies2, e2))

# The bytes a list of IEs was read from, before any tail, are its encoding.
def Ies.sx_cons(+bs: B.Bytes(), +ie: Pf.Ie, +r2: B.Bytes(), +ro: Ies.Res(), +ies: List<&2, Pf.Ie>, +e: {Pf.Ies.cons(ie, ro) == Done{ies} : Ies.Res()}, +tail: B.Bytes(), w: {Pf.Ie.write(ie, List.append(&2, U32, r2, tail)) == List.append(&2, U32, bs, tail) : B.Bytes()}, ab2: {B.all_bytes(r2) == True{} : Bool}, ih: @ies2: List<&2, Pf.Ie> -> {ro == Done{ies2} : Ies.Res()} -> {B.all_bytes(r2) == True{} : Bool} -> {Pf.Ies.write(ies2, tail) == List.append(&2, U32, r2, tail) : B.Bytes()}) -> {Pf.Ies.write(ies, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}:
  match ro:
    case Fail{err}:
      Empty.absurd({Pf.Ies.write(ies, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, Pf.Ie>, err, ies, e))
    case Done{+ies2}:
      eo = Equal.cong(Ies.Res(), List<&2, Pf.Ie>, x => P.Res.value(B.Err, List<&2, Pf.Ie>, x, ies), Done{ie <> ies2}, Done{ies}, e)
      %eo : {Pf.Ies.write(_, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}
      sw = Equal.sym(B.Bytes(), Pf.Ies.write(ies2, tail), List.append(&2, U32, r2, tail), ih(ies2, {==}, ab2))
      %sw : {Pf.Ie.write(ie, _) == List.append(&2, U32, bs, tail) : B.Bytes()}
      w

def Ies.sx_next(+f: Nat, +bs: B.Bytes(), +rb: B.Read(Pf.Ie), +erb: {Pf.Ie.read(bs) == rb : B.Read(Pf.Ie)}, +ies: List<&2, Pf.Ie>, +e: {Pf.Ies.next(rb, left => Pf.Ies.read(f, left)) == Done{ies} : Ies.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}, +tail: B.Bytes(), ih: @left: B.Bytes() -> @ies2: List<&2, Pf.Ie> -> {Pf.Ies.read(f, left) == Done{ies2} : Ies.Res()} -> {B.all_bytes(left) == True{} : Bool} -> {Pf.Ies.write(ies2, tail) == List.append(&2, U32, left, tail) : B.Bytes()}) -> {Pf.Ies.write(ies, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}:
  match rb:
    case Fail{err}:
      Empty.absurd({Pf.Ies.write(ies, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, Pf.Ie>, err, ies, e))
    case Done{(+ie, +r2)}:
      Ies.sx_cons(bs, ie, r2, Pf.Ies.read(f, r2), ies, e, tail, Ie.sx(bs, ie, r2, erb, ab, tail), Ie.rest_bytes(bs, ie, r2, erb, ab), ies2 => e2 => ab2 => ih(r2, ies2, e2, ab2))

def Ies.sx(+fuel: Nat, +bs: B.Bytes(), +ies: List<&2, Pf.Ie>, +e: {Pf.Ies.read(fuel, bs) == Done{ies} : Ies.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}, +tail: B.Bytes()) -> {Pf.Ies.write(ies, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}:
  match fuel bs:
    case 0n Nil{}:
      eo = Equal.cong(Ies.Res(), List<&2, Pf.Ie>, x => P.Res.value(B.Err, List<&2, Pf.Ie>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {Pf.Ies.write(_, tail) == tail : B.Bytes()}
      {==}
    case 1n+f Nil{}:
      eo = Equal.cong(Ies.Res(), List<&2, Pf.Ie>, x => P.Res.value(B.Err, List<&2, Pf.Ie>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {Pf.Ies.write(_, tail) == tail : B.Bytes()}
      {==}
    case 0n b <> r:
      Empty.absurd({Pf.Ies.write(ies, tail) == b <> List.append(&2, U32, r, tail) : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, Pf.Ie>, B.Invalid{b}, ies, e))
    case 1n++f +b <> +r:
      Ies.sx_next(f, b <> r, Pf.Ie.read(b <> r), {==}, ies, e, ab, tail, left => ies2 => e2 => ab2 => Ies.sx(f, left, ies2, e2, ab2, tail))

# F-TEID
# ------
# GHSA-3mxx-vq7h-x8ff

def Fteid.Res() -> Data:
  Result<&2, &2, B.Err, Pf.Fteid>

def Addr.Dv(a: Maybe<&2, B.Bytes()>, n: Nat, flag: Bool) -> Type:
  {Pf.Addr.valid(a, n) == True{} : Bool} & {Pf.Addr.present(a) == flag : Bool}

def Addr.dv_some(+n: Nat, +bs: B.Bytes(), r: B.Read(B.Bytes()), +ert: {B.take(n, bs) == r : B.Read(B.Bytes())}, +a: Maybe<&2, B.Bytes()>, +rest: B.Bytes(), e: {Pf.Addr.some(r) == Done{(a, rest)} : B.Read(Maybe<&2, B.Bytes()>)}) -> Addr.Dv(a, n, True{}):
  match r:
    case Fail{err}:
      Empty.absurd(Addr.Dv(a, n, True{}), P.Refute.fail_done(B.Err, B.ReadValue(Maybe<&2, B.Bytes()>), err, (a, rest), e))
    case Done{(+tk, +rest2)}:
      ev = Equal.cong(B.Read(Maybe<&2, B.Bytes()>), Maybe<&2, B.Bytes()>, x => P.Read.value(Maybe<&2, B.Bytes()>, x, a), Done{(Some{tk}, rest2)}, Done{(a, rest)}, e)
      %ev : Addr.Dv(_, n, True{})
      (PB.Take.len_eq(n, bs, tk, rest2, ert), {==})

def Addr.dv(flag: Bool, +n: Nat, +bs: B.Bytes(), +a: Maybe<&2, B.Bytes()>, +rest: B.Bytes(), e: {Pf.Addr.read(flag, n, bs) == Done{(a, rest)} : B.Read(Maybe<&2, B.Bytes()>)}) -> Addr.Dv(a, n, flag):
  match flag:
    case False{}:
      ev = Equal.cong(B.Read(Maybe<&2, B.Bytes()>), Maybe<&2, B.Bytes()>, x => P.Read.value(Maybe<&2, B.Bytes()>, x, a), Done{(None{}, bs)}, Done{(a, rest)}, e)
      %ev : Addr.Dv(_, n, False{})
      ({==}, {==})
    case True{}:
      Addr.dv_some(n, bs, B.take(n, bs), {==}, a, rest, e)

def Fteid.named(+flags: U32, fv: {Pf.Fteid.flags_valid(flags) == True{} : Bool}) -> {Bool.or(Pf.bit(flags, 1), Pf.bit(flags, 2)) == True{} : Bool}:
  P.Bool.and_true_l(Bool.or(Pf.bit(flags, 1), Pf.bit(flags, 2)), Bool.or(Pf.bit(flags, 4), Bool.not(Pf.bit(flags, 8))), P.Bool.and_true_r(U32.is_lt(flags, 16), Bool.and(Bool.or(Pf.bit(flags, 1), Pf.bit(flags, 2)), Bool.or(Pf.bit(flags, 4), Bool.not(Pf.bit(flags, 8)))), fv))

def Fteid.dv_end(+x: Pf.Fteid, rest: B.Bytes(), +f: Pf.Fteid, e: {Pf.Exact.end(Pf.Fteid, x, rest) == Done{f} : Fteid.Res()}, v: {Pf.Fteid.valid(x) == True{} : Bool}) -> {Pf.Fteid.valid(f) == True{} : Bool}:
  match rest:
    case Nil{}:
      ev = Equal.cong(Fteid.Res(), Pf.Fteid, y => P.Res.value(B.Err, Pf.Fteid, y, f), Done{x}, Done{f}, e)
      %ev : {Pf.Fteid.valid(_) == True{} : Bool}
      v
    case b <> more:
      Empty.absurd({Pf.Fteid.valid(f) == True{} : Bool}, P.Refute.fail_done(B.Err, Pf.Fteid, B.Invalid{b}, f, e))

def Fteid.teid_valid(+flags: U32, +teid: U32, +v4: Maybe<&2, B.Bytes()>, +v6: Maybe<&2, B.Bytes()>, fv: {Pf.Fteid.flags_valid(flags) == True{} : Bool}, h4: Addr.Dv(v4, 4n, Pf.bit(flags, 1)), h6: Addr.Dv(v6, 16n, Pf.bit(flags, 2))) -> {Pf.Fteid.valid(Pf.Teid{teid, v4, v6}) == True{} : Bool}:
  (ok4, p4) = h4
  (ok6, p6) = h6
  sp4 = Equal.sym(Bool, Pf.Addr.present(v4), Pf.bit(flags, 1), p4)
  %sp4 : {Bool.and(Bool.or(_, Pf.Addr.present(v6)), Bool.and(Pf.Addr.valid(v4, 4n), Pf.Addr.valid(v6, 16n))) == True{} : Bool}
  sp6 = Equal.sym(Bool, Pf.Addr.present(v6), Pf.bit(flags, 2), p6)
  %sp6 : {Bool.and(Bool.or(Pf.bit(flags, 1), _), Bool.and(Pf.Addr.valid(v4, 4n), Pf.Addr.valid(v6, 16n))) == True{} : Bool}
  P.Bool.and_intro(Bool.or(Pf.bit(flags, 1), Pf.bit(flags, 2)), Bool.and(Pf.Addr.valid(v4, 4n), Pf.Addr.valid(v6, 16n)), Fteid.named(flags, fv), P.Bool.and_intro(Pf.Addr.valid(v4, 4n), Pf.Addr.valid(v6, 16n), ok4, ok6))

def Fteid.dv_v6(+flags: U32, +teid: U32, +v4: Maybe<&2, B.Bytes()>, +rest: B.Bytes(), r: B.Read(Maybe<&2, B.Bytes()>), +er: {Pf.Addr.read(Pf.bit(flags, 2), 16n, rest) == r : B.Read(Maybe<&2, B.Bytes()>)}, +f: Pf.Fteid, e: {Pf.Fteid.of_v6(teid, v4, r) == Done{f} : Fteid.Res()}, fv: {Pf.Fteid.flags_valid(flags) == True{} : Bool}, h4: Addr.Dv(v4, 4n, Pf.bit(flags, 1))) -> {Pf.Fteid.valid(f) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({Pf.Fteid.valid(f) == True{} : Bool}, P.Refute.fail_done(B.Err, Pf.Fteid, err, f, e))
    case Done{(+v6, +rest2)}:
      Fteid.dv_end(Pf.Teid{teid, v4, v6}, rest2, f, e, Fteid.teid_valid(flags, teid, v4, v6, fv, h4, Addr.dv(Pf.bit(flags, 2), 16n, rest, v6, rest2, er)))

def Fteid.dv_v4(+flags: U32, +teid: U32, +rest: B.Bytes(), r: B.Read(Maybe<&2, B.Bytes()>), +er: {Pf.Addr.read(Pf.bit(flags, 1), 4n, rest) == r : B.Read(Maybe<&2, B.Bytes()>)}, +f: Pf.Fteid, e: {Pf.Fteid.of_v4(flags, teid, r) == Done{f} : Fteid.Res()}, fv: {Pf.Fteid.flags_valid(flags) == True{} : Bool}) -> {Pf.Fteid.valid(f) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({Pf.Fteid.valid(f) == True{} : Bool}, P.Refute.fail_done(B.Err, Pf.Fteid, err, f, e))
    case Done{(+v4, +rest2)}:
      Fteid.dv_v6(flags, teid, v4, rest2, Pf.Addr.read(Pf.bit(flags, 2), 16n, rest2), {==}, f, e, fv, Addr.dv(Pf.bit(flags, 1), 4n, rest, v4, rest2, er))

def Fteid.dv_teid(+flags: U32, r: B.Read(U32), +f: Pf.Fteid, e: {Pf.Fteid.of_teid(flags, r) == Done{f} : Fteid.Res()}, fv: {Pf.Fteid.flags_valid(flags) == True{} : Bool}) -> {Pf.Fteid.valid(f) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({Pf.Fteid.valid(f) == True{} : Bool}, P.Refute.fail_done(B.Err, Pf.Fteid, err, f, e))
    case Done{(+teid, +rest)}:
      Fteid.dv_v4(flags, teid, rest, Pf.Addr.read(Pf.bit(flags, 1), 4n, rest), {==}, f, e, fv)

def Fteid.dv_chid(+flags: U32, r: B.Read(U32), +f: Pf.Fteid, e: {Pf.Fteid.of_chid(Pf.bit(flags, 1), Pf.bit(flags, 2), r) == Done{f} : Fteid.Res()}, fv: {Pf.Fteid.flags_valid(flags) == True{} : Bool}) -> {Pf.Fteid.valid(f) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({Pf.Fteid.valid(f) == True{} : Bool}, P.Refute.fail_done(B.Err, Pf.Fteid, err, f, e))
    case Done{(+chid, rest)}:
      Fteid.dv_end(Pf.Choose{Pf.bit(flags, 1), Pf.bit(flags, 2), Some{chid}}, rest, f, e, Fteid.named(flags, fv))

def Fteid.dv_choose(+flags: U32, rest: B.Bytes(), chid: Bool, +f: Pf.Fteid, e: {Pf.Fteid.choose(flags, rest, chid) == Done{f} : Fteid.Res()}, fv: {Pf.Fteid.flags_valid(flags) == True{} : Bool}) -> {Pf.Fteid.valid(f) == True{} : Bool}:
  match chid:
    case True{}:
      Fteid.dv_chid(flags, B.u8(rest), f, e, fv)
    case False{}:
      Fteid.dv_end(Pf.Choose{Pf.bit(flags, 1), Pf.bit(flags, 2), None{}}, rest, f, e, Fteid.named(flags, fv))

def Fteid.dv_form(+flags: U32, rest: B.Bytes(), ch: Bool, +f: Pf.Fteid, e: {Pf.Fteid.form(flags, rest, ch) == Done{f} : Fteid.Res()}, fv: {Pf.Fteid.flags_valid(flags) == True{} : Bool}) -> {Pf.Fteid.valid(f) == True{} : Bool}:
  match ch:
    case True{}:
      Fteid.dv_choose(flags, rest, Pf.bit(flags, 8), f, e, fv)
    case False{}:
      Fteid.dv_teid(flags, B.u32(rest), f, e, fv)

def Fteid.dv_ok(+flags: U32, rest: B.Bytes(), ok: Bool, eok: {Pf.Fteid.flags_valid(flags) == ok : Bool}, +f: Pf.Fteid, e: {Pf.Fteid.flags_ok(flags, rest, ok) == Done{f} : Fteid.Res()}) -> {Pf.Fteid.valid(f) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Pf.Fteid.valid(f) == True{} : Bool}, P.Refute.fail_done(B.Err, Pf.Fteid, B.Invalid{flags}, f, e))
    case True{}:
      Fteid.dv_form(flags, rest, Pf.bit(flags, 4), f, e, eok)

def L.pfcp.fteid.decode_valid(body, f, e):
  match body:
    case Nil{}:
      Empty.absurd({Pf.Fteid.valid(f) == True{} : Bool}, P.Refute.fail_done(B.Err, Pf.Fteid, B.Short{}, f, e))
    case +flags <> rest:
      Fteid.dv_ok(flags, rest, Pf.Fteid.flags_valid(flags), {==}, f, e)

# Messages
# --------

def Flags.of(s: Bool) -> U32:
  match s:
    case False{}:
      32
    case True{}:
      33

def Flags.mask(s: Bool) -> {U32.and(255, Flags.of(s)) == Flags.of(s) : U32}:
  match s:
    case False{}:
      {==}
    case True{}:
      {==}

def Bytes.all_app_l(xs: B.Bytes(), +ys: B.Bytes(), +e: {B.all_bytes(List.append(&2, U32, xs, ys)) == True{} : Bool}) -> {B.all_bytes(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      P.Bool.and_intro(B.is_byte(x), B.all_bytes(t), P.Bool.and_true_l(B.is_byte(x), B.all_bytes(List.append(&2, U32, t, ys)), e), Bytes.all_app_l(t, ys, P.Bool.and_true_r(B.is_byte(x), B.all_bytes(List.append(&2, U32, t, ys)), e)))

def Ies.write_app(ies: List<&2, Pf.Ie>, +rest: B.Bytes()) -> {Pf.Ies.write(ies, rest) == List.append(&2, U32, Pf.Ies.write(ies, []), rest) : B.Bytes()}:
  match ies:
    case Nil{}:
      {==}
    case Pf.Ie{+kind, +len, +body} <> +more:
      +W = Pf.Ies.write(more, [])
      ih = Equal.sym(B.Bytes(), Pf.Ies.write(more, rest), List.append(&2, U32, W, rest), Ies.write_app(more, rest))
      %ih : {Pf.Ie.write(Pf.Ie{kind, len, body}, _) == List.append(&2, U32, Pf.Ie.write(Pf.Ie{kind, len, body}, W), rest) : B.Bytes()}
      Equal.cong(B.Bytes(), B.Bytes(), l => B.write_u16(kind, B.write_u16(len, l)), List.append(&2, U32, body, List.append(&2, U32, W, rest)), List.append(&2, U32, List.append(&2, U32, body, W), rest), Equal.sym(B.Bytes(), List.append(&2, U32, List.append(&2, U32, body, W), rest), List.append(&2, U32, body, List.append(&2, U32, W, rest)), Bytes.app_assoc(body, W, rest)))

def Ies.size_len(ies: List<&2, Pf.Ie>) -> {Pf.Ies.size(ies) == List.length(&2, U32, Pf.Ies.write(ies, [])) : Nat}:
  match ies:
    case Nil{}:
      {==}
    case Pf.Ie{+kind, +len, +body} <> +more:
      +W = Pf.Ies.write(more, [])
      sih = Equal.sym(Nat, Pf.Ies.size(more), List.length(&2, U32, W), Ies.size_len(more))
      %sih : {Nat.add(4n, Nat.add(List.length(&2, U32, body), _)) == List.length(&2, U32, Pf.Ie.write(Pf.Ie{kind, len, body}, W)) : Nat}
      Equal.cong(Nat, Nat, n => 1n+1n+1n+1n+n, Nat.add(List.length(&2, U32, body), List.length(&2, U32, W)), List.length(&2, U32, List.append(&2, U32, body, W)), Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, body, W)), Nat.add(List.length(&2, U32, body), List.length(&2, U32, W)), P.List.append_len(body, W)))

# What follows the length field, before any tail.
def Msg.body(seid: Maybe<&2, B.Bytes()>, seq: U32, ies: List<&2, Pf.Ie>) -> B.Bytes():
  Pf.Seid.write(seid, B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, []))))

def Msg.take_body(seid: Maybe<&2, B.Bytes()>, +ies: List<&2, Pf.Ie>, +seq: U32, +rest: B.Bytes()) -> {B.take(Pf.Msg.body_size(seid, ies), Pf.Seid.write(seid, B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, rest))))) == Done{(Msg.body(seid, seq, ies), rest)} : B.Read(B.Bytes())}:
  match seid:
    case None{}:
      wa = Equal.sym(B.Bytes(), Pf.Ies.write(ies, rest), List.append(&2, U32, Pf.Ies.write(ies, []), rest), Ies.write_app(ies, rest))
      %wa : {B.take(Pf.Msg.body_size(None{}, ies), Pf.Seid.write(None{}, B.write_u24(seq, B.write_u8(0, _)))) == Done{(Msg.body(None{}, seq, ies), rest)} : B.Read(B.Bytes())}
      sl = Equal.sym(Nat, Pf.Ies.size(ies), List.length(&2, U32, Pf.Ies.write(ies, [])), Ies.size_len(ies))
      %sl : {B.take(Nat.add(Pf.Seid.size(None{}), Nat.add(4n, _)), Pf.Seid.write(None{}, B.write_u24(seq, B.write_u8(0, List.append(&2, U32, Pf.Ies.write(ies, []), rest))))) == Done{(Msg.body(None{}, seq, ies), rest)} : B.Read(B.Bytes())}
      P.Take.append(B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, []))), rest)
    case Some{+sb}:
      wa = Equal.sym(B.Bytes(), Pf.Ies.write(ies, rest), List.append(&2, U32, Pf.Ies.write(ies, []), rest), Ies.write_app(ies, rest))
      %wa : {B.take(Pf.Msg.body_size(Some{sb}, ies), Pf.Seid.write(Some{sb}, B.write_u24(seq, B.write_u8(0, _)))) == Done{(Msg.body(Some{sb}, seq, ies), rest)} : B.Read(B.Bytes())}
      sl = Equal.sym(Nat, Pf.Ies.size(ies), List.length(&2, U32, Pf.Ies.write(ies, [])), Ies.size_len(ies))
      %sl : {B.take(Nat.add(Pf.Seid.size(Some{sb}), Nat.add(4n, _)), Pf.Seid.write(Some{sb}, B.write_u24(seq, B.write_u8(0, List.append(&2, U32, Pf.Ies.write(ies, []), rest))))) == Done{(Msg.body(Some{sb}, seq, ies), rest)} : B.Read(B.Bytes())}
      +Zb = B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, [])))
      al = P.List.append_len(sb, Zb)
      %al : {B.take(_, Pf.Seid.write(Some{sb}, B.write_u24(seq, B.write_u8(0, List.append(&2, U32, Pf.Ies.write(ies, []), rest))))) == Done{(Msg.body(Some{sb}, seq, ies), rest)} : B.Read(B.Bytes())}
      as = Bytes.app_assoc(sb, Zb, rest)
      %as : {B.take(List.length(&2, U32, List.append(&2, U32, sb, Zb)), _) == Done{(Msg.body(Some{sb}, seq, ies), rest)} : B.Read(B.Bytes())}
      P.Take.append(List.append(&2, U32, sb, Zb), rest)

# Roundtrip

def Msg.rt_hdr(+s: Bool, +kind: U32, +len: U32, +Z: B.Bytes(), +fk: {B.fits8(kind) == True{} : Bool}, +fl: {B.fits16(len) == True{} : Bool}) -> {Pf.Msg.of_type(s, B.u8(B.write_u8(kind, B.write_u16(len, Z)))) == Pf.Msg.of_body(s, kind, len, B.take(U32.to_nat(len), Z)) : B.Read(Pf.Msg)}:
  sk = Equal.sym(U32, U32.and(255, kind), kind, P.U32.eq_of_is_eq(U32.and(255, kind), kind, fk))
  %sk : {Pf.Msg.type_ok(s, _, B.write_u16(len, Z), B.fits8(_)) == Pf.Msg.of_body(s, kind, len, B.take(U32.to_nat(len), Z)) : B.Read(Pf.Msg)}
  sfk = Equal.sym(Bool, B.fits8(kind), True{}, fk)
  %sfk : {Pf.Msg.type_ok(s, kind, B.write_u16(len, Z), _) == Pf.Msg.of_body(s, kind, len, B.take(U32.to_nat(len), Z)) : B.Read(Pf.Msg)}
  su = Equal.sym(B.Read(U32), B.u16(B.write_u16(len, Z)), Done{(U32.and(65535, len), Z)}, PB.Bits.u16(len, Z))
  %su : {Pf.Msg.of_len(s, kind, _) == Pf.Msg.of_body(s, kind, len, B.take(U32.to_nat(len), Z)) : B.Read(Pf.Msg)}
  sl = Equal.sym(U32, U32.and(65535, len), len, P.U32.eq_of_is_eq(U32.and(65535, len), len, fl))
  %sl : {Pf.Msg.len_ok(s, kind, _, Z, B.fits16(_)) == Pf.Msg.of_body(s, kind, len, B.take(U32.to_nat(len), Z)) : B.Read(Pf.Msg)}
  sfl = Equal.sym(Bool, B.fits16(len), True{}, fl)
  %sfl : {Pf.Msg.len_ok(s, kind, len, Z, _) == Pf.Msg.of_body(s, kind, len, B.take(U32.to_nat(len), Z)) : B.Read(Pf.Msg)}
  {==}

def Msg.rt_seq(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, Pf.Ie>, +rest: B.Bytes(), +f24: {Pf.fits24(seq) == True{} : Bool}, iv: {Pf.Ies.valid(ies) == True{} : Bool}) -> {Pf.Msg.with_rest(Pf.Msg.of_seq(kind, len, seid, B.u24(B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, []))))), rest) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}:
  +W = Pf.Ies.write(ies, [])
  +X = B.write_u8(0, W)
  su = Equal.sym(B.Read(U32), B.u24(B.write_u24(seq, X)), Done{(U32.and(16777215, seq), X)}, PB.Bits.u24(seq, X))
  %su : {Pf.Msg.with_rest(Pf.Msg.of_seq(kind, len, seid, _), rest) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}
  ss = Equal.sym(U32, U32.and(16777215, seq), seq, P.U32.eq_of_is_eq(U32.and(16777215, seq), seq, f24))
  %ss : {Pf.Msg.with_rest(Pf.Msg.seq_ok(kind, len, seid, _, X, Pf.fits24(_)), rest) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}
  sf24 = Equal.sym(Bool, Pf.fits24(seq), True{}, f24)
  %sf24 : {Pf.Msg.with_rest(Pf.Msg.seq_ok(kind, len, seid, seq, X, _), rest) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}
  ir = Equal.sym(Ies.Res(), Pf.Ies.read(List.length(&2, U32, W), W), Done{ies}, Ies.rt(ies, List.length(&2, U32, W), iv, P.Nat.le_refl(List.length(&2, U32, W))))
  %ir : {Pf.Msg.with_rest(Pf.Msg.of_ies(kind, len, seid, seq, _), rest) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}
  {==}

def Msg.rt_go(+kind: U32, +len: U32, seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, Pf.Ie>, +rest: B.Bytes(), fk: {B.fits8(kind) == True{} : Bool}, fl: {B.fits16(len) == True{} : Bool}, sv: {Pf.Seid.valid(seid) == True{} : Bool}, f24: {Pf.fits24(seq) == True{} : Bool}, tn: {Nat.is_eq(U32.to_nat(len), Pf.Msg.body_size(seid, ies)) == True{} : Bool}, iv: {Pf.Ies.valid(ies) == True{} : Bool}) -> {Pf.Msg.read(Pf.Msg.write(Pf.Msg{kind, len, seid, seq, ies}, rest)) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}:
  match seid:
    case None{}:
      +Zr = B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, rest)))
      hdr = Equal.sym(B.Read(Pf.Msg), Pf.Msg.of_type(False{}, B.u8(B.write_u8(kind, B.write_u16(len, Zr)))), Pf.Msg.of_body(False{}, kind, len, B.take(U32.to_nat(len), Zr)), Msg.rt_hdr(False{}, kind, len, Zr, fk, fl))
      %hdr : {_ == Done{(Pf.Msg{kind, len, None{}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      stn = Equal.sym(Nat, U32.to_nat(len), Pf.Msg.body_size(None{}, ies), P.Nat.eq_of_is_eq(U32.to_nat(len), Pf.Msg.body_size(None{}, ies), tn))
      %stn : {Pf.Msg.of_body(False{}, kind, len, B.take(_, Zr)) == Done{(Pf.Msg{kind, len, None{}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      tb = Equal.sym(B.Read(B.Bytes()), B.take(Pf.Msg.body_size(None{}, ies), Zr), Done{(Msg.body(None{}, seq, ies), rest)}, Msg.take_body(None{}, ies, seq, rest))
      %tb : {Pf.Msg.of_body(False{}, kind, len, _) == Done{(Pf.Msg{kind, len, None{}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      Msg.rt_seq(kind, len, None{}, seq, ies, rest, f24, iv)
    case Some{+sb}:
      +Zr = B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, rest)))
      +Z = List.append(&2, U32, sb, Zr)
      hdr = Equal.sym(B.Read(Pf.Msg), Pf.Msg.of_type(True{}, B.u8(B.write_u8(kind, B.write_u16(len, Z)))), Pf.Msg.of_body(True{}, kind, len, B.take(U32.to_nat(len), Z)), Msg.rt_hdr(True{}, kind, len, Z, fk, fl))
      %hdr : {_ == Done{(Pf.Msg{kind, len, Some{sb}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      stn = Equal.sym(Nat, U32.to_nat(len), Pf.Msg.body_size(Some{sb}, ies), P.Nat.eq_of_is_eq(U32.to_nat(len), Pf.Msg.body_size(Some{sb}, ies), tn))
      %stn : {Pf.Msg.of_body(True{}, kind, len, B.take(_, Z)) == Done{(Pf.Msg{kind, len, Some{sb}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      tb = Equal.sym(B.Read(B.Bytes()), B.take(Pf.Msg.body_size(Some{sb}, ies), Z), Done{(Msg.body(Some{sb}, seq, ies), rest)}, Msg.take_body(Some{sb}, ies, seq, rest))
      %tb : {Pf.Msg.of_body(True{}, kind, len, _) == Done{(Pf.Msg{kind, len, Some{sb}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      +Zb = B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, [])))
      s8 = P.Nat.eq_of_is_eq(List.length(&2, U32, sb), 8n, sv)
      %s8 : {Pf.Msg.with_rest(Pf.Msg.of_seid(kind, len, B.take(_, List.append(&2, U32, sb, Zb))), rest) == Done{(Pf.Msg{kind, len, Some{sb}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      ta = Equal.sym(B.Read(B.Bytes()), B.take(List.length(&2, U32, sb), List.append(&2, U32, sb, Zb)), Done{(sb, Zb)}, P.Take.append(sb, Zb))
      %ta : {Pf.Msg.with_rest(Pf.Msg.of_seid(kind, len, _), rest) == Done{(Pf.Msg{kind, len, Some{sb}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      Msg.rt_seq(kind, len, Some{sb}, seq, ies, rest, f24, iv)

def Msg.rt(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, Pf.Ie>, +rest: B.Bytes(), +v: {Pf.Msg.valid(Pf.Msg{kind, len, seid, seq, ies}) == True{} : Bool}) -> {Pf.Msg.read(Pf.Msg.write(Pf.Msg{kind, len, seid, seq, ies}, rest)) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}:
  +R4 = Bool.and(Nat.is_eq(U32.to_nat(len), Pf.Msg.body_size(seid, ies)), Pf.Ies.valid(ies))
  +R3 = Bool.and(Pf.fits24(seq), R4)
  +R2 = Bool.and(Pf.Seid.valid(seid), R3)
  +R1 = Bool.and(B.fits16(len), R2)
  +v2 = P.Bool.and_true_r(B.fits8(kind), R1, v)
  +v3 = P.Bool.and_true_r(B.fits16(len), R2, v2)
  +v4 = P.Bool.and_true_r(Pf.Seid.valid(seid), R3, v3)
  +v5 = P.Bool.and_true_r(Pf.fits24(seq), R4, v4)
  Msg.rt_go(kind, len, seid, seq, ies, rest, P.Bool.and_true_l(B.fits8(kind), R1, v), P.Bool.and_true_l(B.fits16(len), R2, v2), P.Bool.and_true_l(Pf.Seid.valid(seid), R3, v3), P.Bool.and_true_l(Pf.fits24(seq), R4, v4), P.Bool.and_true_l(Nat.is_eq(U32.to_nat(len), Pf.Msg.body_size(seid, ies)), Pf.Ies.valid(ies), v5), P.Bool.and_true_r(Nat.is_eq(U32.to_nat(len), Pf.Msg.body_size(seid, ies)), Pf.Ies.valid(ies), v5))

def L.pfcp.roundtrip(m, rest, v):
  match m:
    case Pf.Msg{+kind, +len, +seid, +seq, +ies}:
      Msg.rt(kind, len, seid, seq, ies, rest, v)

# Reading: what a message reader answered. One chain yields decode_valid,
# suffix and length_consistent.

# The octets after the SEID: sequence number, spare, IEs.
def Tail.Spec(body: B.Bytes(), seq: U32, ies: List<&2, Pf.Ie>) -> Type:
  {Pf.fits24(seq) == True{} : Bool} & ({Pf.Ies.valid(ies) == True{} : Bool} & ({Nat.add(4n, Pf.Ies.size(ies)) == List.length(&2, U32, body) : Nat} & ({B.all_bytes(body) == True{} : Bool} -> @tail: B.Bytes() -> {B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, tail))) == List.append(&2, U32, body, tail) : B.Bytes()})))

# The octets after the length field.
def Body.Spec(body: B.Bytes(), seid: Maybe<&2, B.Bytes()>, seq: U32, ies: List<&2, Pf.Ie>) -> Type:
  {Pf.Seid.valid(seid) == True{} : Bool} & ({Pf.fits24(seq) == True{} : Bool} & ({Pf.Ies.valid(ies) == True{} : Bool} & ({Pf.Msg.body_size(seid, ies) == List.length(&2, U32, body) : Nat} & ({B.all_bytes(body) == True{} : Bool} -> @tail: B.Bytes() -> {Pf.Seid.write(seid, B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, tail)))) == List.append(&2, U32, body, tail) : B.Bytes()}))))

def Msg.Spec(bs: B.Bytes(), m: Pf.Msg, rest: B.Bytes()) -> Type:
  {Pf.Msg.valid(m) == True{} : Bool} & (({B.all_bytes(bs) == True{} : Bool} -> {Pf.Msg.write(m, rest) == bs : B.Bytes()}) & {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(U32.to_nat(Pf.Msg.len(m)), List.length(&2, U32, rest))) : Nat})

def Tail.write(+b2: U32, +b1: U32, +b0: U32, +sp: U32, +iesb: B.Bytes(), +ies: List<&2, Pf.Ie>, +eri: {Pf.Ies.read(List.length(&2, U32, iesb), iesb) == Done{ies} : Ies.Res()}, e0: {sp == 0 : U32}, +ab: {B.all_bytes(b2 <> b1 <> b0 <> sp <> iesb) == True{} : Bool}, +tail: B.Bytes()) -> {B.write_u24(B.cat8(b0, B.cat8(b1, b2)), B.write_u8(0, Pf.Ies.write(ies, tail))) == List.append(&2, U32, b2 <> b1 <> b0 <> sp <> iesb, tail) : B.Bytes()}:
  +ab2 = P.Bool.and_true_r(B.is_byte(b2), B.all_bytes(b1 <> b0 <> sp <> iesb), ab)
  +ab3 = P.Bool.and_true_r(B.is_byte(b1), B.all_bytes(b0 <> sp <> iesb), ab2)
  +ab4 = P.Bool.and_true_r(B.is_byte(b0), B.all_bytes(sp <> iesb), ab3)
  +X = B.write_u8(0, Pf.Ies.write(ies, tail))
  w = Equal.sym(B.Bytes(), B.write_u24(B.cat8(b0, B.cat8(b1, b2)), X), b2 <> b1 <> b0 <> X, P.Bytes.u24_sx(b2, b1, b0, P.U32.lt256_mask8(b2, P.Bool.and_true_l(B.is_byte(b2), B.all_bytes(b1 <> b0 <> sp <> iesb), ab)), P.U32.lt256_mask8(b1, P.Bool.and_true_l(B.is_byte(b1), B.all_bytes(b0 <> sp <> iesb), ab2)), P.U32.lt256_mask8(b0, P.Bool.and_true_l(B.is_byte(b0), B.all_bytes(sp <> iesb), ab3)), X))
  %w : {_ == List.append(&2, U32, b2 <> b1 <> b0 <> sp <> iesb, tail) : B.Bytes()}
  se0 = Equal.sym(U32, sp, 0, e0)
  %se0 : {b2 <> b1 <> b0 <> X == List.append(&2, U32, b2 <> b1 <> b0 <> _ <> iesb, tail) : B.Bytes()}
  Equal.cong(B.Bytes(), B.Bytes(), l => b2 <> b1 <> b0 <> B.write_u8(0, l), Pf.Ies.write(ies, tail), List.append(&2, U32, iesb, tail), Ies.sx(List.length(&2, U32, iesb), iesb, ies, eri, P.Bool.and_true_r(B.is_byte(sp), B.all_bytes(iesb), ab4), tail))

def Tail.fin(+b2: U32, +b1: U32, +b0: U32, +sp: U32, +iesb: B.Bytes(), +ies: List<&2, Pf.Ie>, +eri: {Pf.Ies.read(List.length(&2, U32, iesb), iesb) == Done{ies} : Ies.Res()}, f24: {Pf.fits24(B.cat8(b0, B.cat8(b1, b2))) == True{} : Bool}, e0: {sp == 0 : U32}) -> Tail.Spec(b2 <> b1 <> b0 <> sp <> iesb, B.cat8(b0, B.cat8(b1, b2)), ies):
  (f24, (Ies.dv(List.length(&2, U32, iesb), iesb, ies, eri), (Equal.cong(Nat, Nat, n => 1n+1n+1n+1n+n, Pf.Ies.size(ies), List.length(&2, U32, iesb), Ies.len(List.length(&2, U32, iesb), iesb, ies, eri)), ab => tail => Tail.write(b2, b1, b0, sp, iesb, ies, eri, e0, ab, tail))))

def Body.none(+body: B.Bytes(), +seq: U32, +ies: List<&2, Pf.Ie>, tsp: Tail.Spec(body, seq, ies)) -> Body.Spec(body, None{}, seq, ies):
  (f24, t1) = tsp
  (iv, t2) = t1
  (tsz, tw) = t2
  ({==}, (f24, (iv, (tsz, tw))))

def Body.some.write(+sb: B.Bytes(), +r5: B.Bytes(), +body: B.Bytes(), +seq: U32, +ies: List<&2, Pf.Ie>, +ap: {List.append(&2, U32, sb, r5) == body : B.Bytes()}, tw: {B.all_bytes(r5) == True{} : Bool} -> @tail: B.Bytes() -> {B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, tail))) == List.append(&2, U32, r5, tail) : B.Bytes()}, ab: {B.all_bytes(body) == True{} : Bool}, +tail: B.Bytes()) -> {Pf.Seid.write(Some{sb}, B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, tail)))) == List.append(&2, U32, body, tail) : B.Bytes()}:
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, sb, r5), body, ap)
  %ap : {Pf.Seid.write(Some{sb}, B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, tail)))) == List.append(&2, U32, _, tail) : B.Bytes()}
  as = Equal.sym(B.Bytes(), List.append(&2, U32, List.append(&2, U32, sb, r5), tail), List.append(&2, U32, sb, List.append(&2, U32, r5, tail)), Bytes.app_assoc(sb, r5, tail))
  %as : {List.append(&2, U32, sb, B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, tail)))) == _ : B.Bytes()}
  Equal.cong(B.Bytes(), B.Bytes(), l => List.append(&2, U32, sb, l), B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, tail))), List.append(&2, U32, r5, tail), tw(PB.Bytes.all_app(sb, r5, (%sap : {B.all_bytes(_) == True{} : Bool}; ab)), tail))

def Body.some(+sb: B.Bytes(), +r5: B.Bytes(), +body: B.Bytes(), +seq: U32, +ies: List<&2, Pf.Ie>, la: {List.length(&2, U32, sb) == 8n : Nat} & {List.append(&2, U32, sb, r5) == body : B.Bytes()}, tsp: Tail.Spec(r5, seq, ies)) -> Body.Spec(body, Some{sb}, seq, ies):
  (l8, +ap) = la
  (f24, t1) = tsp
  (iv, t2) = t1
  (tsz, tw) = t2
  sl8 = Equal.sym(Nat, List.length(&2, U32, sb), 8n, l8)
  stsz = Equal.sym(Nat, Nat.add(4n, Pf.Ies.size(ies)), List.length(&2, U32, r5), tsz)
  ((%sl8 : {Nat.is_eq(_, 8n) == True{} : Bool}; P.Nat.is_eq_refl(8n)), (f24, (iv, ((%ap : {Pf.Msg.body_size(Some{sb}, ies) == List.length(&2, U32, _) : Nat}; (%stsz : {Nat.add(List.length(&2, U32, sb), _) == List.length(&2, U32, List.append(&2, U32, sb, r5)) : Nat}; Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, sb, r5)), Nat.add(List.length(&2, U32, sb), List.length(&2, U32, r5)), P.List.append_len(sb, r5)))), ab => tail => Body.some.write(sb, r5, body, seq, ies, ap, tw, ab, tail)))))

def Body.spec.ies(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, +b2: U32, +b1: U32, +b0: U32, +sp: U32, +iesb: B.Bytes(), ri: Ies.Res(), +eri: {Pf.Ies.read(List.length(&2, U32, iesb), iesb) == ri : Ies.Res()}, +m: Pf.Msg, e: {Pf.Msg.of_ies(kind, len, seid, B.cat8(b0, B.cat8(b1, b2)), ri) == Done{m} : Msg.Res()}, -G: Type, k: @seq: U32 -> @ies: List<&2, Pf.Ie> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> Tail.Spec(b2 <> b1 <> b0 <> sp <> iesb, seq, ies) -> G, f24: {Pf.fits24(B.cat8(b0, B.cat8(b1, b2))) == True{} : Bool}, e0: {sp == 0 : U32}) -> G:
  match ri:
    case Fail{err}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, err, m, e))
    case Done{+ies}:
      k(B.cat8(b0, B.cat8(b1, b2)), ies, Equal.cong(Msg.Res(), Pf.Msg, x => P.Res.value(B.Err, Pf.Msg, x, m), Done{Pf.Msg{kind, len, seid, B.cat8(b0, B.cat8(b1, b2)), ies}}, Done{m}, e), Tail.fin(b2, b1, b0, sp, iesb, ies, eri, f24, e0))

def Body.spec.spare(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, +b2: U32, +b1: U32, +b0: U32, +sp: U32, +iesb: B.Bytes(), ok: Bool, eok: {U32.is_eq(sp, 0) == ok : Bool}, +m: Pf.Msg, e: {Pf.Msg.spare_ok(kind, len, seid, B.cat8(b0, B.cat8(b1, b2)), sp, iesb, ok) == Done{m} : Msg.Res()}, -G: Type, k: @seq: U32 -> @ies: List<&2, Pf.Ie> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> Tail.Spec(b2 <> b1 <> b0 <> sp <> iesb, seq, ies) -> G, f24: {Pf.fits24(B.cat8(b0, B.cat8(b1, b2))) == True{} : Bool}) -> G:
  match ok:
    case False{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Invalid{sp}, m, e))
    case True{}:
      Body.spec.ies(kind, len, seid, b2, b1, b0, sp, iesb, Pf.Ies.read(List.length(&2, U32, iesb), iesb), {==}, m, e, G, k, f24, P.U32.eq_of_is_eq(sp, 0, eok))

def Body.spec.seq(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, +b2: U32, +b1: U32, +b0: U32, ok: Bool, eok: {Pf.fits24(B.cat8(b0, B.cat8(b1, b2))) == ok : Bool}, r6: B.Bytes(), +m: Pf.Msg, e: {Pf.Msg.seq_ok(kind, len, seid, B.cat8(b0, B.cat8(b1, b2)), r6, ok) == Done{m} : Msg.Res()}, -G: Type, k: @seq: U32 -> @ies: List<&2, Pf.Ie> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> Tail.Spec(b2 <> b1 <> b0 <> r6, seq, ies) -> G) -> G:
  match ok:
    case False{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Invalid{B.cat8(b0, B.cat8(b1, b2))}, m, e))
    case True{}:
      match r6:
        case Nil{}:
          Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Short{}, m, e))
        case +sp <> +iesb:
          Body.spec.spare(kind, len, seid, b2, b1, b0, sp, iesb, U32.is_eq(sp, 0), {==}, m, e, G, k, eok)

def Body.spec.u24(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, body: B.Bytes(), +m: Pf.Msg, e: {Pf.Msg.of_seq(kind, len, seid, B.u24(body)) == Done{m} : Msg.Res()}, -G: Type, k: @seq: U32 -> @ies: List<&2, Pf.Ie> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> Tail.Spec(body, seq, ies) -> G) -> G:
  match body:
    case Nil{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Short{}, m, e))
    case a <> Nil{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Short{}, m, e))
    case a <> b <> Nil{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Short{}, m, e))
    case +b2 <> +b1 <> +b0 <> +r6:
      Body.spec.seq(kind, len, seid, b2, b1, b0, Pf.fits24(B.cat8(b0, B.cat8(b1, b2))), {==}, r6, m, e, G, k)

def Body.spec.seid(+kind: U32, +len: U32, +body: B.Bytes(), rt: B.Read(B.Bytes()), +ert: {B.take(8n, body) == rt : B.Read(B.Bytes())}, +m: Pf.Msg, e: {Pf.Msg.of_seid(kind, len, rt) == Done{m} : Msg.Res()}, -G: Type, k: @seid: Maybe<&2, B.Bytes()> -> @seq: U32 -> @ies: List<&2, Pf.Ie> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> {Pf.Seid.flags(seid) == Flags.of(True{}) : U32} -> Body.Spec(body, seid, seq, ies) -> G) -> G:
  match rt:
    case Fail{err}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, err, m, e))
    case Done{(+sb, +r5)}:
      Body.spec.u24(kind, len, Some{sb}, r5, m, e, G, +seq => +ies => em => tsp => k(Some{sb}, seq, ies, em, {==}, Body.some(sb, r5, body, seq, ies, L.bytes.take.length(8n, body, sb, r5, ert), tsp)))

def Body.spec(s: Bool, +kind: U32, +len: U32, +body: B.Bytes(), +m: Pf.Msg, e: {Pf.Msg.parse(s, kind, len, body) == Done{m} : Msg.Res()}, -G: Type, k: @seid: Maybe<&2, B.Bytes()> -> @seq: U32 -> @ies: List<&2, Pf.Ie> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> {Pf.Seid.flags(seid) == Flags.of(s) : U32} -> Body.Spec(body, seid, seq, ies) -> G) -> G:
  match s:
    case False{}:
      Body.spec.u24(kind, len, None{}, body, m, e, G, +seq => +ies => em => tsp => k(None{}, seq, ies, em, {==}, Body.none(body, seq, ies, tsp)))
    case True{}:
      Body.spec.seid(kind, len, body, B.take(8n, body), {==}, m, e, G, k)

def Msg.spec.valid(+kind: U32, +b0: U32, +b1: U32, +seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, Pf.Ie>, +body: B.Bytes(), fk: {B.fits8(kind) == True{} : Bool}, fl: {B.fits16(B.cat8(b0, b1)) == True{} : Bool}, sv: {Pf.Seid.valid(seid) == True{} : Bool}, f24: {Pf.fits24(seq) == True{} : Bool}, iv: {Pf.Ies.valid(ies) == True{} : Bool}, bsz: {Pf.Msg.body_size(seid, ies) == List.length(&2, U32, body) : Nat}, ln: {List.length(&2, U32, body) == U32.to_nat(B.cat8(b0, b1)) : Nat}) -> {Pf.Msg.valid(Pf.Msg{kind, B.cat8(b0, b1), seid, seq, ies}) == True{} : Bool}:
  sbsz = Equal.sym(Nat, Pf.Msg.body_size(seid, ies), List.length(&2, U32, body), bsz)
  tn : {Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)) == True{} : Bool} = (%ln : {Nat.is_eq(_, Pf.Msg.body_size(seid, ies)) == True{} : Bool}; (%sbsz : {Nat.is_eq(List.length(&2, U32, body), _) == True{} : Bool}; P.Nat.is_eq_refl(List.length(&2, U32, body))))
  P.Bool.and_intro(B.fits8(kind), Bool.and(B.fits16(B.cat8(b0, b1)), Bool.and(Pf.Seid.valid(seid), Bool.and(Pf.fits24(seq), Bool.and(Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)), Pf.Ies.valid(ies))))), fk, P.Bool.and_intro(B.fits16(B.cat8(b0, b1)), Bool.and(Pf.Seid.valid(seid), Bool.and(Pf.fits24(seq), Bool.and(Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)), Pf.Ies.valid(ies)))), fl, P.Bool.and_intro(Pf.Seid.valid(seid), Bool.and(Pf.fits24(seq), Bool.and(Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)), Pf.Ies.valid(ies))), sv, P.Bool.and_intro(Pf.fits24(seq), Bool.and(Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)), Pf.Ies.valid(ies)), f24, P.Bool.and_intro(Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)), Pf.Ies.valid(ies), tn, iv)))))

def Msg.spec.write(+s: Bool, +flags: U32, +kind: U32, +b1: U32, +b0: U32, +r3: B.Bytes(), +body: B.Bytes(), +r4: B.Bytes(), +seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, Pf.Ie>, sf: {Pf.Seid.flags(seid) == Flags.of(s) : U32}, ef: {flags == Flags.of(s) : U32}, fk: {B.fits8(kind) == True{} : Bool}, +ap: {List.append(&2, U32, body, r4) == r3 : B.Bytes()}, wb: {B.all_bytes(body) == True{} : Bool} -> @tail: B.Bytes() -> {Pf.Seid.write(seid, B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, tail)))) == List.append(&2, U32, body, tail) : B.Bytes()}, +ab: {B.all_bytes(flags <> kind <> b1 <> b0 <> r3) == True{} : Bool}) -> {Pf.Msg.write(Pf.Msg{kind, B.cat8(b0, b1), seid, seq, ies}, r4) == flags <> kind <> b1 <> b0 <> r3 : B.Bytes()}:
  +Z = Pf.Seid.write(seid, B.write_u24(seq, B.write_u8(0, Pf.Ies.write(ies, r4))))
  ssf = Equal.sym(U32, Pf.Seid.flags(seid), Flags.of(s), sf)
  %ssf : {B.write_u8(_, B.write_u8(kind, B.write_u16(B.cat8(b0, b1), Z))) == flags <> kind <> b1 <> b0 <> r3 : B.Bytes()}
  sef = Equal.sym(U32, flags, Flags.of(s), ef)
  %sef : {B.write_u8(Flags.of(s), B.write_u8(kind, B.write_u16(B.cat8(b0, b1), Z))) == _ <> kind <> b1 <> b0 <> r3 : B.Bytes()}
  sm = Equal.sym(U32, U32.and(255, Flags.of(s)), Flags.of(s), Flags.mask(s))
  %sm : {_ <> B.write_u8(kind, B.write_u16(B.cat8(b0, b1), Z)) == Flags.of(s) <> kind <> b1 <> b0 <> r3 : B.Bytes()}
  sk = Equal.sym(U32, U32.and(255, kind), kind, P.U32.eq_of_is_eq(U32.and(255, kind), kind, fk))
  %sk : {Flags.of(s) <> _ <> B.write_u16(B.cat8(b0, b1), Z) == Flags.of(s) <> kind <> b1 <> b0 <> r3 : B.Bytes()}
  +ab2 = P.Bool.and_true_r(B.is_byte(flags), B.all_bytes(kind <> b1 <> b0 <> r3), ab)
  +ab3 = P.Bool.and_true_r(B.is_byte(kind), B.all_bytes(b1 <> b0 <> r3), ab2)
  +ab4 = P.Bool.and_true_r(B.is_byte(b1), B.all_bytes(b0 <> r3), ab3)
  w16 = Equal.sym(B.Bytes(), B.write_u16(B.cat8(b0, b1), Z), b1 <> b0 <> Z, P.Bytes.u16_sx(b1, b0, P.U32.lt256_mask8(b1, P.Bool.and_true_l(B.is_byte(b1), B.all_bytes(b0 <> r3), ab3)), P.U32.lt256_mask8(b0, P.Bool.and_true_l(B.is_byte(b0), B.all_bytes(r3), ab4)), Z))
  %w16 : {Flags.of(s) <> kind <> _ == Flags.of(s) <> kind <> b1 <> b0 <> r3 : B.Bytes()}
  %ap : {Flags.of(s) <> kind <> b1 <> b0 <> Z == Flags.of(s) <> kind <> b1 <> b0 <> _ : B.Bytes()}
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, body, r4), r3, ap)
  Equal.cong(B.Bytes(), B.Bytes(), l => Flags.of(s) <> kind <> b1 <> b0 <> l, Z, List.append(&2, U32, body, r4), wb(Bytes.all_app_l(body, r4, (%sap : {B.all_bytes(_) == True{} : Bool}; P.Bool.and_true_r(B.is_byte(b0), B.all_bytes(r3), ab4))), r4))

def Msg.spec.len(+flags: U32, +kind: U32, +b1: U32, +b0: U32, +r3: B.Bytes(), +body: B.Bytes(), +r4: B.Bytes(), ln: {List.length(&2, U32, body) == U32.to_nat(B.cat8(b0, b1)) : Nat}, ap: {List.append(&2, U32, body, r4) == r3 : B.Bytes()}) -> {List.length(&2, U32, flags <> kind <> b1 <> b0 <> r3) == Nat.add(4n, Nat.add(U32.to_nat(B.cat8(b0, b1)), List.length(&2, U32, r4))) : Nat}:
  %ap : {List.length(&2, U32, flags <> kind <> b1 <> b0 <> _) == Nat.add(4n, Nat.add(U32.to_nat(B.cat8(b0, b1)), List.length(&2, U32, r4))) : Nat}
  %ln : {List.length(&2, U32, flags <> kind <> b1 <> b0 <> List.append(&2, U32, body, r4)) == Nat.add(4n, Nat.add(_, List.length(&2, U32, r4))) : Nat}
  Equal.cong(Nat, Nat, n => 1n+1n+1n+1n+n, List.length(&2, U32, List.append(&2, U32, body, r4)), Nat.add(List.length(&2, U32, body), List.length(&2, U32, r4)), P.List.append_len(body, r4))

def Msg.spec.fin(+s: Bool, +flags: U32, +kind: U32, +b1: U32, +b0: U32, +r3: B.Bytes(), +body: B.Bytes(), +r4: B.Bytes(), +seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, Pf.Ie>, +m: Pf.Msg, em: {Pf.Msg{kind, B.cat8(b0, b1), seid, seq, ies} == m : Pf.Msg}, sf: {Pf.Seid.flags(seid) == Flags.of(s) : U32}, bsp: Body.Spec(body, seid, seq, ies), ef: {flags == Flags.of(s) : U32}, +fk: {B.fits8(kind) == True{} : Bool}, fl: {B.fits16(B.cat8(b0, b1)) == True{} : Bool}, la: {List.length(&2, U32, body) == U32.to_nat(B.cat8(b0, b1)) : Nat} & {List.append(&2, U32, body, r4) == r3 : B.Bytes()}) -> Msg.Spec(flags <> kind <> b1 <> b0 <> r3, m, r4):
  (sv, s1) = bsp
  (f24, s2) = s1
  (iv, s3) = s2
  (bsz, wb) = s3
  (+ln, +ap) = la
  %em : Msg.Spec(flags <> kind <> b1 <> b0 <> r3, _, r4)
  (Msg.spec.valid(kind, b0, b1, seid, seq, ies, body, fk, fl, sv, f24, iv, bsz, ln), (ab => Msg.spec.write(s, flags, kind, b1, b0, r3, body, r4, seid, seq, ies, sf, ef, fk, ap, wb, ab), Msg.spec.len(flags, kind, b1, b0, r3, body, r4, ln, ap)))

def Msg.spec.with(+s: Bool, +flags: U32, +kind: U32, +b1: U32, +b0: U32, +r3: B.Bytes(), +body: B.Bytes(), +r4: B.Bytes(), rp: Msg.Res(), +erp: {Pf.Msg.parse(s, kind, B.cat8(b0, b1), body) == rp : Msg.Res()}, +m: Pf.Msg, +rest: B.Bytes(), +e: {Pf.Msg.with_rest(rp, r4) == Done{(m, rest)} : B.Read(Pf.Msg)}, ef: {flags == Flags.of(s) : U32}, fk: {B.fits8(kind) == True{} : Bool}, fl: {B.fits16(B.cat8(b0, b1)) == True{} : Bool}, la: {List.length(&2, U32, body) == U32.to_nat(B.cat8(b0, b1)) : Nat} & {List.append(&2, U32, body, r4) == r3 : B.Bytes()}) -> Msg.Spec(flags <> kind <> b1 <> b0 <> r3, m, rest):
  match rp:
    case Fail{err}:
      Empty.absurd(Msg.Spec(flags <> kind <> b1 <> b0 <> r3, m, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Msg), err, (m, rest), e))
    case Done{+m2}:
      ev = Equal.cong(B.Read(Pf.Msg), Pf.Msg, x => P.Read.value(Pf.Msg, x, m), Done{(m2, r4)}, Done{(m, rest)}, e)
      er = Equal.cong(B.Read(Pf.Msg), B.Bytes(), x => P.Read.rest(Pf.Msg, x, rest), Done{(m2, r4)}, Done{(m, rest)}, e)
      %ev : Msg.Spec(flags <> kind <> b1 <> b0 <> r3, _, rest)
      %er : Msg.Spec(flags <> kind <> b1 <> b0 <> r3, m2, _)
      Body.spec(s, kind, B.cat8(b0, b1), body, m2, erp, Msg.Spec(flags <> kind <> b1 <> b0 <> r3, m2, r4), seid => seq => ies => em => sf => bsp => Msg.spec.fin(s, flags, kind, b1, b0, r3, body, r4, seid, seq, ies, m2, em, sf, bsp, ef, fk, fl, la))

def Msg.spec.body(+s: Bool, +flags: U32, +kind: U32, +b1: U32, +b0: U32, +r3: B.Bytes(), rt: B.Read(B.Bytes()), +ert: {B.take(U32.to_nat(B.cat8(b0, b1)), r3) == rt : B.Read(B.Bytes())}, +m: Pf.Msg, +rest: B.Bytes(), e: {Pf.Msg.of_body(s, kind, B.cat8(b0, b1), rt) == Done{(m, rest)} : B.Read(Pf.Msg)}, ef: {flags == Flags.of(s) : U32}, fk: {B.fits8(kind) == True{} : Bool}, fl: {B.fits16(B.cat8(b0, b1)) == True{} : Bool}) -> Msg.Spec(flags <> kind <> b1 <> b0 <> r3, m, rest):
  match rt:
    case Fail{err}:
      Empty.absurd(Msg.Spec(flags <> kind <> b1 <> b0 <> r3, m, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Msg), err, (m, rest), e))
    case Done{(+body, +r4)}:
      Msg.spec.with(s, flags, kind, b1, b0, r3, body, r4, Pf.Msg.parse(s, kind, B.cat8(b0, b1), body), {==}, m, rest, e, ef, fk, fl, L.bytes.take.length(U32.to_nat(B.cat8(b0, b1)), r3, body, r4, ert))

def Msg.spec.len_ok(+s: Bool, +flags: U32, +kind: U32, +b1: U32, +b0: U32, +r3: B.Bytes(), ok: Bool, eok: {B.fits16(B.cat8(b0, b1)) == ok : Bool}, +m: Pf.Msg, +rest: B.Bytes(), e: {Pf.Msg.len_ok(s, kind, B.cat8(b0, b1), r3, ok) == Done{(m, rest)} : B.Read(Pf.Msg)}, ef: {flags == Flags.of(s) : U32}, fk: {B.fits8(kind) == True{} : Bool}) -> Msg.Spec(flags <> kind <> b1 <> b0 <> r3, m, rest):
  match ok:
    case False{}:
      Empty.absurd(Msg.Spec(flags <> kind <> b1 <> b0 <> r3, m, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Msg), B.Invalid{B.cat8(b0, b1)}, (m, rest), e))
    case True{}:
      Msg.spec.body(s, flags, kind, b1, b0, r3, B.take(U32.to_nat(B.cat8(b0, b1)), r3), {==}, m, rest, e, ef, fk, eok)

def Msg.spec.kind(+s: Bool, +flags: U32, +kind: U32, ok: Bool, eok: {B.fits8(kind) == ok : Bool}, r2: B.Bytes(), +m: Pf.Msg, +rest: B.Bytes(), e: {Pf.Msg.type_ok(s, kind, r2, ok) == Done{(m, rest)} : B.Read(Pf.Msg)}, ef: {flags == Flags.of(s) : U32}) -> Msg.Spec(flags <> kind <> r2, m, rest):
  match ok:
    case False{}:
      Empty.absurd(Msg.Spec(flags <> kind <> r2, m, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Msg), B.Invalid{kind}, (m, rest), e))
    case True{}:
      match r2:
        case Nil{}:
          Empty.absurd(Msg.Spec(flags <> kind <> [], m, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Msg), B.Short{}, (m, rest), e))
        case x <> Nil{}:
          Empty.absurd(Msg.Spec(flags <> kind <> [x], m, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Msg), B.Short{}, (m, rest), e))
        case +b1 <> +b0 <> +r3:
          Msg.spec.len_ok(s, flags, kind, b1, b0, r3, B.fits16(B.cat8(b0, b1)), {==}, m, rest, e, ef, eok)

def Msg.spec.type(+s: Bool, +flags: U32, r: B.Bytes(), +m: Pf.Msg, +rest: B.Bytes(), e: {Pf.Msg.of_type(s, B.u8(r)) == Done{(m, rest)} : B.Read(Pf.Msg)}, ef: {flags == Flags.of(s) : U32}) -> Msg.Spec(flags <> r, m, rest):
  match r:
    case Nil{}:
      Empty.absurd(Msg.Spec(flags <> [], m, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Msg), B.Short{}, (m, rest), e))
    case +kind <> +r2:
      Msg.spec.kind(s, flags, kind, B.fits8(kind), {==}, r2, m, rest, e, ef)

def Msg.spec.flags(+flags: U32, +r: B.Bytes(), plain: Bool, with_seid: Bool, ep: {U32.is_eq(flags, 32) == plain : Bool}, es: {U32.is_eq(flags, 33) == with_seid : Bool}, +m: Pf.Msg, +rest: B.Bytes(), e: {Pf.Msg.flags_ok(flags, r, plain, with_seid) == Done{(m, rest)} : B.Read(Pf.Msg)}) -> Msg.Spec(flags <> r, m, rest):
  match plain:
    case True{}:
      Msg.spec.type(False{}, flags, r, m, rest, e, P.U32.eq_of_is_eq(flags, 32, ep))
    case False{}:
      match with_seid:
        case True{}:
          Msg.spec.type(True{}, flags, r, m, rest, e, P.U32.eq_of_is_eq(flags, 33, es))
        case False{}:
          Empty.absurd(Msg.Spec(flags <> r, m, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Msg), B.Unsupported{flags}, (m, rest), e))

def Msg.spec(bs: B.Bytes(), +m: Pf.Msg, +rest: B.Bytes(), e: {Pf.Msg.read(bs) == Done{(m, rest)} : B.Read(Pf.Msg)}) -> Msg.Spec(bs, m, rest):
  match bs:
    case Nil{}:
      Empty.absurd(Msg.Spec([], m, rest), P.Refute.fail_done(B.Err, B.ReadValue(Pf.Msg), B.Short{}, (m, rest), e))
    case +flags <> +r:
      Msg.spec.flags(flags, r, U32.is_eq(flags, 32), U32.is_eq(flags, 33), {==}, {==}, m, rest, e)

def Msg.Spec.valid(+bs: B.Bytes(), +m: Pf.Msg, +rest: B.Bytes(), s: Msg.Spec(bs, m, rest)) -> {Pf.Msg.valid(m) == True{} : Bool}:
  (v, s2) = s
  v

def Msg.Spec.write(+bs: B.Bytes(), +m: Pf.Msg, +rest: B.Bytes(), s: Msg.Spec(bs, m, rest), ab: {B.all_bytes(bs) == True{} : Bool}) -> {Pf.Msg.write(m, rest) == bs : B.Bytes()}:
  (v, s2) = s
  (w, l) = s2
  w(ab)

def Msg.Spec.len(+bs: B.Bytes(), +m: Pf.Msg, +rest: B.Bytes(), s: Msg.Spec(bs, m, rest)) -> {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(U32.to_nat(Pf.Msg.len(m)), List.length(&2, U32, rest))) : Nat}:
  (v, s2) = s
  (w, l) = s2
  l

def L.pfcp.decode_valid(bs, m, rest, e):
  Msg.Spec.valid(bs, m, rest, Msg.spec(bs, m, rest, e))

def L.pfcp.suffix(bs, m, rest, e, ab):
  Msg.Spec.write(bs, m, rest, Msg.spec(bs, m, rest, e), ab)

def L.pfcp.header.length_consistent(bs, m, rest, e):
  Msg.Spec.len(bs, m, rest, Msg.spec(bs, m, rest, e))
