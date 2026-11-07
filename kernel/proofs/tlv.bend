import Base
import ../bytes.bend as B
import ../tlv.bend as T
import ../LAWS.bend as L
import ./lib.bend as P
import ./bytes.bend as PB

# Proofs about TLVs: roundtrip, validity, exact consumption and canonical
# bytes, for one TLV and for a list; PFCP and the frame Config build on them.

def Tlvs.Res() -> Data:
  Result<&2, &2, B.Err, List<&2, T.Tlv>>

def Hdr.len(h: T.Hdr) -> U32:
  match h:
    case T.Hdr{kind, len}:
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

def Tlv.rt(+kind: U32, +len: U32, +body: B.Bytes(), +W: B.Bytes(), +v: {T.Tlv.valid(T.Tlv{kind, len, body}) == True{} : Bool}) -> {T.Tlv.read(T.Tlv.write(T.Tlv{kind, len, body}, W)) == Done{(T.Tlv{kind, len, body}, W)} : B.Read(T.Tlv)}:
  +fk = P.Bool.and_true_l(B.fits16(kind), Bool.and(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body))), v)
  +v2 = P.Bool.and_true_r(B.fits16(kind), Bool.and(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body))), v)
  +fl = P.Bool.and_true_l(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v2)
  tn = P.Bool.and_true_r(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v2)
  su1 = Equal.sym(B.Read(U32), B.u16(B.write_u16(kind, B.write_u16(len, List.append(&2, U32, body, W)))), Done{(U32.and(65535, kind), B.write_u16(len, List.append(&2, U32, body, W)))}, PB.Bits.u16(kind, B.write_u16(len, List.append(&2, U32, body, W))))
  %su1 : {T.Tlv.of_header(T.Tlv.hdr_type(_)) == Done{(T.Tlv{kind, len, body}, W)} : B.Read(T.Tlv)}
  sek = Equal.sym(U32, U32.and(65535, kind), kind, P.U32.eq_of_is_eq(U32.and(65535, kind), kind, fk))
  %sek : {T.Tlv.of_header(T.Tlv.hdr_len(_, B.u16(B.write_u16(len, List.append(&2, U32, body, W))))) == Done{(T.Tlv{kind, len, body}, W)} : B.Read(T.Tlv)}
  su2 = Equal.sym(B.Read(U32), B.u16(B.write_u16(len, List.append(&2, U32, body, W))), Done{(U32.and(65535, len), List.append(&2, U32, body, W))}, PB.Bits.u16(len, List.append(&2, U32, body, W)))
  %su2 : {T.Tlv.of_header(T.Tlv.hdr_len(kind, _)) == Done{(T.Tlv{kind, len, body}, W)} : B.Read(T.Tlv)}
  sel = Equal.sym(U32, U32.and(65535, len), len, P.U32.eq_of_is_eq(U32.and(65535, len), len, fl))
  %sel : {T.Tlv.of_header(T.Tlv.hdr_len(kind, Done{(_, List.append(&2, U32, body, W))})) == Done{(T.Tlv{kind, len, body}, W)} : B.Read(T.Tlv)}
  sfk = Equal.sym(Bool, B.fits16(kind), True{}, fk)
  %sfk : {T.Tlv.checked(kind, len, List.append(&2, U32, body, W), Bool.and(_, B.fits16(len))) == Done{(T.Tlv{kind, len, body}, W)} : B.Read(T.Tlv)}
  sfl = Equal.sym(Bool, B.fits16(len), True{}, fl)
  %sfl : {T.Tlv.checked(kind, len, List.append(&2, U32, body, W), Bool.and(True{}, _)) == Done{(T.Tlv{kind, len, body}, W)} : B.Read(T.Tlv)}
  stn = Equal.sym(Nat, U32.to_nat(len), List.length(&2, U32, body), P.Nat.eq_of_is_eq(U32.to_nat(len), List.length(&2, U32, body), tn))
  %stn : {T.Tlv.of_body(kind, len, B.take(_, List.append(&2, U32, body, W))) == Done{(T.Tlv{kind, len, body}, W)} : B.Read(T.Tlv)}
  ta = Equal.sym(B.Read(B.Bytes()), B.take(List.length(&2, U32, body), List.append(&2, U32, body, W)), Done{(body, W)}, P.Take.append(body, W))
  %ta : {T.Tlv.of_body(kind, len, _) == Done{(T.Tlv{kind, len, body}, W)} : B.Read(T.Tlv)}
  {==}

# What an TLV reader answered: a valid TLV, whose body is its declared length,
# that consumed exactly four octets plus that length of the input.
def Tlv.Spec(bs: B.Bytes(), ie: T.Tlv, rest: B.Bytes()) -> Type:
  {T.Tlv.valid(ie) == True{} : Bool} & ({List.drop(&2, U32, bs, Nat.add(4n, U32.to_nat(T.Tlv.len(ie)))) == rest : B.Bytes()} & ({List.length(&2, U32, T.Tlv.body(ie)) == U32.to_nat(T.Tlv.len(ie)) : Nat} & {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(List.length(&2, U32, T.Tlv.body(ie)), List.length(&2, U32, rest))) : Nat}))

def Tlv.spec.fin(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), +kind: U32, +len: U32, +body: B.Bytes(), +rest: B.Bytes(), fk: {B.fits16(kind) == True{} : Bool}, fl: {B.fits16(len) == True{} : Bool}, la: {List.length(&2, U32, body) == U32.to_nat(len) : Nat} & {List.append(&2, U32, body, rest) == t : B.Bytes()}) -> Tlv.Spec(a <> b <> c <> d <> t, T.Tlv{kind, len, body}, rest):
  (+ln, +ap) = la
  (P.Bool.and_intro(B.fits16(kind), Bool.and(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body))), fk, P.Bool.and_intro(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), fl, (%ln : {Nat.is_eq(_, List.length(&2, U32, body)) == True{} : Bool}; P.Nat.is_eq_refl(List.length(&2, U32, body))))), ((%ln : {List.drop(&2, U32, t, _) == rest : B.Bytes()}; (%ap : {List.drop(&2, U32, _, List.length(&2, U32, body)) == rest : B.Bytes()}; Drop.app(body, rest))), (ln, (%ap : {List.length(&2, U32, a <> b <> c <> d <> _) == Nat.add(4n, Nat.add(List.length(&2, U32, body), List.length(&2, U32, rest))) : Nat}; Equal.cong(Nat, Nat, n => 1n+1n+1n+1n+n, List.length(&2, U32, List.append(&2, U32, body, rest)), Nat.add(List.length(&2, U32, body), List.length(&2, U32, rest)), P.List.append_len(body, rest))))))

def Tlv.spec.body(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), +kind: U32, +len: U32, rt: B.Read(B.Bytes()), +ert: {B.take(U32.to_nat(len), t) == rt : B.Read(B.Bytes())}, +ie: T.Tlv, +rest: B.Bytes(), +e: {T.Tlv.of_body(kind, len, rt) == Done{(ie, rest)} : B.Read(T.Tlv)}, fk: {B.fits16(kind) == True{} : Bool}, fl: {B.fits16(len) == True{} : Bool}) -> Tlv.Spec(a <> b <> c <> d <> t, ie, rest):
  match rt:
    case Fail{err}:
      Empty.absurd(Tlv.Spec(a <> b <> c <> d <> t, ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), err, (ie, rest), e))
    case Done{(+body, +rest2)}:
      ev = Equal.cong(B.Read(T.Tlv), T.Tlv, x => P.Read.value(T.Tlv, x, ie), Done{(T.Tlv{kind, len, body}, rest2)}, Done{(ie, rest)}, e)
      er = Equal.cong(B.Read(T.Tlv), B.Bytes(), x => P.Read.rest(T.Tlv, x, rest), Done{(T.Tlv{kind, len, body}, rest2)}, Done{(ie, rest)}, e)
      %ev : Tlv.Spec(a <> b <> c <> d <> t, _, rest)
      %er : Tlv.Spec(a <> b <> c <> d <> t, T.Tlv{kind, len, body}, _)
      Tlv.spec.fin(a, b, c, d, t, kind, len, body, rest2, fk, fl, L.bytes.take.length(U32.to_nat(len), t, body, rest2, ert))

def Tlv.spec.checked(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), ok: Bool, +eok: {Bool.and(B.fits16(B.cat8(b, a)), B.fits16(B.cat8(d, c))) == ok : Bool}, +ie: T.Tlv, +rest: B.Bytes(), +e: {T.Tlv.checked(B.cat8(b, a), B.cat8(d, c), t, ok) == Done{(ie, rest)} : B.Read(T.Tlv)}) -> Tlv.Spec(a <> b <> c <> d <> t, ie, rest):
  match ok:
    case False{}:
      Empty.absurd(Tlv.Spec(a <> b <> c <> d <> t, ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), B.Invalid{B.cat8(d, c)}, (ie, rest), e))
    case True{}:
      Tlv.spec.body(a, b, c, d, t, B.cat8(b, a), B.cat8(d, c), B.take(U32.to_nat(B.cat8(d, c)), t), {==}, ie, rest, e, P.Bool.and_true_l(B.fits16(B.cat8(b, a)), B.fits16(B.cat8(d, c)), eok), P.Bool.and_true_r(B.fits16(B.cat8(b, a)), B.fits16(B.cat8(d, c)), eok))

def Tlv.spec(bs: B.Bytes(), +ie: T.Tlv, +rest: B.Bytes(), +e: {T.Tlv.read(bs) == Done{(ie, rest)} : B.Read(T.Tlv)}) -> Tlv.Spec(bs, ie, rest):
  match bs:
    case Nil{}:
      Empty.absurd(Tlv.Spec([], ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), B.Short{}, (ie, rest), e))
    case a <> Nil{}:
      Empty.absurd(Tlv.Spec([a], ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), B.Short{}, (ie, rest), e))
    case a <> b <> Nil{}:
      Empty.absurd(Tlv.Spec([a, b], ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), B.Short{}, (ie, rest), e))
    case a <> b <> c <> Nil{}:
      Empty.absurd(Tlv.Spec([a, b, c], ie, rest), P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), B.Short{}, (ie, rest), e))
    case +a <> +b <> +c <> +d <> +t:
      Tlv.spec.checked(a, b, c, d, t, Bool.and(B.fits16(B.cat8(b, a)), B.fits16(B.cat8(d, c))), {==}, ie, rest, e)

def Tlv.Spec.valid(+bs: B.Bytes(), +ie: T.Tlv, +rest: B.Bytes(), s: Tlv.Spec(bs, ie, rest)) -> {T.Tlv.valid(ie) == True{} : Bool}:
  (v, s2) = s
  v

def Tlv.Spec.consumed(+bs: B.Bytes(), +ie: T.Tlv, +rest: B.Bytes(), s: Tlv.Spec(bs, ie, rest)) -> {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(List.length(&2, U32, T.Tlv.body(ie)), List.length(&2, U32, rest))) : Nat}:
  (v, s2) = s
  (dr, s3) = s2
  (ln, cn) = s3
  cn

def Tlv.dv(+bs: B.Bytes(), +ie: T.Tlv, +rest: B.Bytes(), +e: {T.Tlv.read(bs) == Done{(ie, rest)} : B.Read(T.Tlv)}) -> {T.Tlv.valid(ie) == True{} : Bool}:
  Tlv.Spec.valid(bs, ie, rest, Tlv.spec(bs, ie, rest, e))

def Tlv.consumed(+bs: B.Bytes(), +ie: T.Tlv, +rest: B.Bytes(), +e: {T.Tlv.read(bs) == Done{(ie, rest)} : B.Read(T.Tlv)}) -> {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(List.length(&2, U32, T.Tlv.body(ie)), List.length(&2, U32, rest))) : Nat}:
  Tlv.Spec.consumed(bs, ie, rest, Tlv.spec(bs, ie, rest, e))

# The bytes an TLV was read from, before any tail, are its encoding.
def Tlv.sx.fin(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), +body: B.Bytes(), +rest: B.Bytes(), +tail: B.Bytes(), la: {List.length(&2, U32, body) == U32.to_nat(B.cat8(d, c)) : Nat} & {List.append(&2, U32, body, rest) == t : B.Bytes()}, ma: {U32.and(255, a) == a : U32}, mb: {U32.and(255, b) == b : U32}, mc: {U32.and(255, c) == c : U32}, md: {U32.and(255, d) == d : U32}) -> {T.Tlv.write(T.Tlv{B.cat8(b, a), B.cat8(d, c), body}, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}:
  (ln, ap) = la
  +X : B.Bytes() = List.append(&2, U32, body, List.append(&2, U32, rest, tail))
  w1 = Equal.sym(B.Bytes(), B.write_u16(B.cat8(b, a), B.write_u16(B.cat8(d, c), X)), a <> b <> B.write_u16(B.cat8(d, c), X), P.Bytes.u16_sx(a, b, ma, mb, B.write_u16(B.cat8(d, c), X)))
  %w1 : {_ == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}
  w2 = Equal.sym(B.Bytes(), B.write_u16(B.cat8(d, c), X), c <> d <> X, P.Bytes.u16_sx(c, d, mc, md, X))
  %w2 : {a <> b <> _ == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}
  %ap : {a <> b <> c <> d <> X == a <> b <> c <> d <> List.append(&2, U32, _, tail) : B.Bytes()}
  Equal.cong(B.Bytes(), B.Bytes(), l => a <> b <> c <> d <> l, List.append(&2, U32, body, List.append(&2, U32, rest, tail)), List.append(&2, U32, List.append(&2, U32, body, rest), tail), Equal.sym(B.Bytes(), List.append(&2, U32, List.append(&2, U32, body, rest), tail), List.append(&2, U32, body, List.append(&2, U32, rest, tail)), Bytes.app_assoc(body, rest, tail)))

def Tlv.sx.body(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), rt: B.Read(B.Bytes()), +ert: {B.take(U32.to_nat(B.cat8(d, c)), t) == rt : B.Read(B.Bytes())}, +ie: T.Tlv, +rest: B.Bytes(), +e: {T.Tlv.of_body(B.cat8(b, a), B.cat8(d, c), rt) == Done{(ie, rest)} : B.Read(T.Tlv)}, +tail: B.Bytes(), ma: {U32.and(255, a) == a : U32}, mb: {U32.and(255, b) == b : U32}, mc: {U32.and(255, c) == c : U32}, md: {U32.and(255, d) == d : U32}) -> {T.Tlv.write(ie, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}:
  match rt:
    case Fail{err}:
      Empty.absurd({T.Tlv.write(ie, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), err, (ie, rest), e))
    case Done{(+body, +rest2)}:
      ev = Equal.cong(B.Read(T.Tlv), T.Tlv, x => P.Read.value(T.Tlv, x, ie), Done{(T.Tlv{B.cat8(b, a), B.cat8(d, c), body}, rest2)}, Done{(ie, rest)}, e)
      er = Equal.cong(B.Read(T.Tlv), B.Bytes(), x => P.Read.rest(T.Tlv, x, rest), Done{(T.Tlv{B.cat8(b, a), B.cat8(d, c), body}, rest2)}, Done{(ie, rest)}, e)
      %ev : {T.Tlv.write(_, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}
      %er : {T.Tlv.write(T.Tlv{B.cat8(b, a), B.cat8(d, c), body}, List.append(&2, U32, _, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}
      Tlv.sx.fin(a, b, c, d, t, body, rest2, tail, L.bytes.take.length(U32.to_nat(B.cat8(d, c)), t, body, rest2, ert), ma, mb, mc, md)

def Tlv.sx.checked(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), ok: Bool, +ie: T.Tlv, +rest: B.Bytes(), +e: {T.Tlv.checked(B.cat8(b, a), B.cat8(d, c), t, ok) == Done{(ie, rest)} : B.Read(T.Tlv)}, +tail: B.Bytes(), ma: {U32.and(255, a) == a : U32}, mb: {U32.and(255, b) == b : U32}, mc: {U32.and(255, c) == c : U32}, md: {U32.and(255, d) == d : U32}) -> {T.Tlv.write(ie, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}:
  match ok:
    case False{}:
      Empty.absurd({T.Tlv.write(ie, List.append(&2, U32, rest, tail)) == a <> b <> c <> d <> List.append(&2, U32, t, tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), B.Invalid{B.cat8(d, c)}, (ie, rest), e))
    case True{}:
      Tlv.sx.body(a, b, c, d, t, B.take(U32.to_nat(B.cat8(d, c)), t), {==}, ie, rest, e, tail, ma, mb, mc, md)

def Tlv.sx(bs: B.Bytes(), +ie: T.Tlv, +rest: B.Bytes(), +e: {T.Tlv.read(bs) == Done{(ie, rest)} : B.Read(T.Tlv)}, +ab: {B.all_bytes(bs) == True{} : Bool}, +tail: B.Bytes()) -> {T.Tlv.write(ie, List.append(&2, U32, rest, tail)) == List.append(&2, U32, bs, tail) : B.Bytes()}:
  match bs:
    case Nil{}:
      Empty.absurd({T.Tlv.write(ie, List.append(&2, U32, rest, tail)) == List.append(&2, U32, [], tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), B.Short{}, (ie, rest), e))
    case a <> Nil{}:
      Empty.absurd({T.Tlv.write(ie, List.append(&2, U32, rest, tail)) == List.append(&2, U32, [a], tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), B.Short{}, (ie, rest), e))
    case a <> b <> Nil{}:
      Empty.absurd({T.Tlv.write(ie, List.append(&2, U32, rest, tail)) == List.append(&2, U32, [a, b], tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), B.Short{}, (ie, rest), e))
    case a <> b <> c <> Nil{}:
      Empty.absurd({T.Tlv.write(ie, List.append(&2, U32, rest, tail)) == List.append(&2, U32, [a, b, c], tail) : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(T.Tlv), B.Short{}, (ie, rest), e))
    case +a <> +b <> +c <> +d <> +t:
      +ab2 = P.Bool.and_true_r(B.is_byte(a), B.all_bytes(b <> c <> d <> t), ab)
      +ab3 = P.Bool.and_true_r(B.is_byte(b), B.all_bytes(c <> d <> t), ab2)
      +ab4 = P.Bool.and_true_r(B.is_byte(c), B.all_bytes(d <> t), ab3)
      Tlv.sx.checked(a, b, c, d, t, Bool.and(B.fits16(B.cat8(b, a)), B.fits16(B.cat8(d, c))), ie, rest, e, tail, P.U32.lt256_mask8(a, P.Bool.and_true_l(B.is_byte(a), B.all_bytes(b <> c <> d <> t), ab)), P.U32.lt256_mask8(b, P.Bool.and_true_l(B.is_byte(b), B.all_bytes(c <> d <> t), ab2)), P.U32.lt256_mask8(c, P.Bool.and_true_l(B.is_byte(c), B.all_bytes(d <> t), ab3)), P.U32.lt256_mask8(d, P.Bool.and_true_l(B.is_byte(d), B.all_bytes(t), ab4)))

def Tlv.Spec.exact(+bs: B.Bytes(), +ie: T.Tlv, +rest: B.Bytes(), s: Tlv.Spec(bs, ie, rest)) -> {List.drop(&2, U32, bs, Nat.add(4n, U32.to_nat(T.Tlv.len(ie)))) == rest : B.Bytes()} & {List.length(&2, U32, T.Tlv.body(ie)) == U32.to_nat(T.Tlv.len(ie)) : Nat}:
  (v, s2) = s
  (dr, s3) = s2
  (ln, cn) = s3
  (dr, ln)

def Tlv.exact(+bs: B.Bytes(), +ie: T.Tlv, +rest: B.Bytes(), +e: {T.Tlv.read(bs) == Done{(ie, rest)} : B.Read(T.Tlv)}) -> {List.drop(&2, U32, bs, Nat.add(4n, U32.to_nat(T.Tlv.len(ie)))) == rest : B.Bytes()} & {List.length(&2, U32, T.Tlv.body(ie)) == U32.to_nat(T.Tlv.len(ie)) : Nat}:
  Tlv.Spec.exact(bs, ie, rest, Tlv.spec(bs, ie, rest, e))

def Tlv.short.go(+a: U32, +b: U32, +c: U32, +d: U32, +t: B.Bytes(), +len: U32, +tail: B.Bytes(), el: {B.cat8(d, c) == len : U32}, et: {t == tail : B.Bytes()}, +ab: {B.all_bytes(a <> b <> c <> d <> t) == True{} : Bool}, lt: {Nat.is_lt(List.length(&2, U32, tail), U32.to_nat(len)) == True{} : Bool}) -> {T.Tlv.read(a <> b <> c <> d <> t) == Fail{B.Short{}} : B.Read(T.Tlv)}:
  +ab2 = P.Bool.and_true_r(B.is_byte(a), B.all_bytes(b <> c <> d <> t), ab)
  +ab3 = P.Bool.and_true_r(B.is_byte(b), B.all_bytes(c <> d <> t), ab2)
  +ab4 = P.Bool.and_true_r(B.is_byte(c), B.all_bytes(d <> t), ab3)
  sfk = Equal.sym(Bool, B.fits16(B.cat8(b, a)), True{}, Fits16.of_bytes(b, a, P.U32.lt256_mask8(b, P.Bool.and_true_l(B.is_byte(b), B.all_bytes(c <> d <> t), ab2)), P.U32.lt256_mask8(a, P.Bool.and_true_l(B.is_byte(a), B.all_bytes(b <> c <> d <> t), ab))))
  %sfk : {T.Tlv.checked(B.cat8(b, a), B.cat8(d, c), t, Bool.and(_, B.fits16(B.cat8(d, c)))) == Fail{B.Short{}} : B.Read(T.Tlv)}
  sfl = Equal.sym(Bool, B.fits16(B.cat8(d, c)), True{}, Fits16.of_bytes(d, c, P.U32.lt256_mask8(d, P.Bool.and_true_l(B.is_byte(d), B.all_bytes(t), ab4)), P.U32.lt256_mask8(c, P.Bool.and_true_l(B.is_byte(c), B.all_bytes(d <> t), ab3))))
  %sfl : {T.Tlv.checked(B.cat8(b, a), B.cat8(d, c), t, Bool.and(True{}, _)) == Fail{B.Short{}} : B.Read(T.Tlv)}
  set = Equal.sym(B.Bytes(), t, tail, et)
  sel = Equal.sym(U32, B.cat8(d, c), len, el)
  st = Equal.sym(B.Read(B.Bytes()), B.take(U32.to_nat(B.cat8(d, c)), t), Fail{B.Short{}}, PB.Short.take(U32.to_nat(B.cat8(d, c)), t, (%sel : {Nat.is_lt(List.length(&2, U32, t), U32.to_nat(_)) == True{} : Bool}; (%set : {Nat.is_lt(List.length(&2, U32, _), U32.to_nat(len)) == True{} : Bool}; lt))))
  %st : {T.Tlv.of_body(B.cat8(b, a), B.cat8(d, c), _) == Fail{B.Short{}} : B.Read(T.Tlv)}
  {==}

def Tlv.short(bs: B.Bytes(), +kind: U32, +len: U32, +tail: B.Bytes(), +eh: {T.Tlv.header(bs) == Done{(T.Hdr{kind, len}, tail)} : B.Read(T.Hdr)}, +ab: {B.all_bytes(bs) == True{} : Bool}, lt: {Nat.is_lt(List.length(&2, U32, tail), U32.to_nat(len)) == True{} : Bool}) -> {T.Tlv.read(bs) == Fail{B.Short{}} : B.Read(T.Tlv)}:
  match bs:
    case Nil{}:
      Empty.absurd({T.Tlv.read([]) == Fail{B.Short{}} : B.Read(T.Tlv)}, P.Refute.fail_done(B.Err, B.ReadValue(T.Hdr), B.Short{}, (T.Hdr{kind, len}, tail), eh))
    case a <> Nil{}:
      Empty.absurd({T.Tlv.read([a]) == Fail{B.Short{}} : B.Read(T.Tlv)}, P.Refute.fail_done(B.Err, B.ReadValue(T.Hdr), B.Short{}, (T.Hdr{kind, len}, tail), eh))
    case a <> b <> Nil{}:
      Empty.absurd({T.Tlv.read([a, b]) == Fail{B.Short{}} : B.Read(T.Tlv)}, P.Refute.fail_done(B.Err, B.ReadValue(T.Hdr), B.Short{}, (T.Hdr{kind, len}, tail), eh))
    case a <> b <> c <> Nil{}:
      Empty.absurd({T.Tlv.read([a, b, c]) == Fail{B.Short{}} : B.Read(T.Tlv)}, P.Refute.fail_done(B.Err, B.ReadValue(T.Hdr), B.Short{}, (T.Hdr{kind, len}, tail), eh))
    case +a <> +b <> +c <> +d <> +t:
      Tlv.short.go(a, b, c, d, t, len, tail, Equal.cong(B.Read(T.Hdr), U32, x => Hdr.len(P.Read.value(T.Hdr, x, T.Hdr{kind, len})), Done{(T.Hdr{B.cat8(b, a), B.cat8(d, c)}, t)}, Done{(T.Hdr{kind, len}, tail)}, eh), Equal.cong(B.Read(T.Hdr), B.Bytes(), x => P.Read.rest(T.Hdr, x, tail), Done{(T.Hdr{B.cat8(b, a), B.cat8(d, c)}, t)}, Done{(T.Hdr{kind, len}, tail)}, eh), ab, lt)

# Lists of TLVs
# -------------

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

def Tlv.rest_bytes.go(+bs: B.Bytes(), +ie: T.Tlv, +rest: B.Bytes(), s: {List.drop(&2, U32, bs, Nat.add(4n, U32.to_nat(T.Tlv.len(ie)))) == rest : B.Bytes()} & {List.length(&2, U32, T.Tlv.body(ie)) == U32.to_nat(T.Tlv.len(ie)) : Nat}, ab: {B.all_bytes(bs) == True{} : Bool}) -> {B.all_bytes(rest) == True{} : Bool}:
  (dr, ln) = s
  %dr : {B.all_bytes(_) == True{} : Bool}
  Bytes.all_drop(Nat.add(4n, U32.to_nat(T.Tlv.len(ie))), bs, ab)

def Tlv.rest_bytes(+bs: B.Bytes(), +ie: T.Tlv, +rest: B.Bytes(), +e: {T.Tlv.read(bs) == Done{(ie, rest)} : B.Read(T.Tlv)}, ab: {B.all_bytes(bs) == True{} : Bool}) -> {B.all_bytes(rest) == True{} : Bool}:
  Tlv.rest_bytes.go(bs, ie, rest, Tlv.exact(bs, ie, rest, e), ab)

def Tlvs.rt(ies: List<&2, T.Tlv>, fuel: Nat, +v: {T.Tlvs.valid(ies) == True{} : Bool}, +bound: {Nat.is_le(List.length(&2, U32, T.Tlvs.write(ies, [])), fuel) == True{} : Bool}) -> {T.Tlvs.read(fuel, T.Tlvs.write(ies, [])) == Done{ies} : Tlvs.Res()}:
  match ies fuel:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+f:
      {==}
    case T.Tlv{+kind, +len, +body} <> +more 0n:
      Empty.absurd({T.Tlvs.read(0n, T.Tlvs.write(T.Tlv{kind, len, body} <> more, [])) == Done{T.Tlv{kind, len, body} <> more} : Tlvs.Res()}, P.Refute.bool(bound))
    case T.Tlv{+kind, +len, +body} <> +more 1n++f:
      +W = T.Tlvs.write(more, [])
      sr = Equal.sym(B.Read(T.Tlv), T.Tlv.read(T.Tlv.write(T.Tlv{kind, len, body}, W)), Done{(T.Tlv{kind, len, body}, W)}, Tlv.rt(kind, len, body, W, P.Bool.and_true_l(T.Tlv.valid(T.Tlv{kind, len, body}), T.Tlvs.valid(more), v)))
      %sr : {T.Tlvs.next(_, left => T.Tlvs.read(f, left)) == Done{T.Tlv{kind, len, body} <> more} : Tlvs.Res()}
      ih = Equal.sym(Tlvs.Res(), T.Tlvs.read(f, W), Done{more}, Tlvs.rt(more, f, P.Bool.and_true_r(T.Tlv.valid(T.Tlv{kind, len, body}), T.Tlvs.valid(more), v), P.Nat.le_of_append(body, W, 3n, f, bound)))
      %ih : {T.Tlvs.cons(T.Tlv{kind, len, body}, _) == Done{T.Tlv{kind, len, body} <> more} : Tlvs.Res()}
      {==}

def Tlvs.dv_cons(+ie: T.Tlv, +ro: Tlvs.Res(), +ies: List<&2, T.Tlv>, e: {T.Tlvs.cons(ie, ro) == Done{ies} : Tlvs.Res()}, hv: {T.Tlv.valid(ie) == True{} : Bool}, ho: @ies2: List<&2, T.Tlv> -> {ro == Done{ies2} : Tlvs.Res()} -> {T.Tlvs.valid(ies2) == True{} : Bool}) -> {T.Tlvs.valid(ies) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Empty.absurd({T.Tlvs.valid(ies) == True{} : Bool}, P.Refute.fail_done(B.Err, List<&2, T.Tlv>, err, ies, e))
    case Done{+ies2}:
      eo = Equal.cong(Tlvs.Res(), List<&2, T.Tlv>, x => P.Res.value(B.Err, List<&2, T.Tlv>, x, ies), Done{ie <> ies2}, Done{ies}, e)
      %eo : {T.Tlvs.valid(_) == True{} : Bool}
      P.Bool.and_intro(T.Tlv.valid(ie), T.Tlvs.valid(ies2), hv, ho(ies2, {==}))

def Tlvs.dv_next(+f: Nat, +bs: B.Bytes(), +rb: B.Read(T.Tlv), erb: {T.Tlv.read(bs) == rb : B.Read(T.Tlv)}, +ies: List<&2, T.Tlv>, e: {T.Tlvs.next(rb, left => T.Tlvs.read(f, left)) == Done{ies} : Tlvs.Res()}, ih: @left: B.Bytes() -> @ies2: List<&2, T.Tlv> -> {T.Tlvs.read(f, left) == Done{ies2} : Tlvs.Res()} -> {T.Tlvs.valid(ies2) == True{} : Bool}) -> {T.Tlvs.valid(ies) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Empty.absurd({T.Tlvs.valid(ies) == True{} : Bool}, P.Refute.fail_done(B.Err, List<&2, T.Tlv>, err, ies, e))
    case Done{(+ie, +r2)}:
      Tlvs.dv_cons(ie, T.Tlvs.read(f, r2), ies, e, Tlv.dv(bs, ie, r2, erb), ies2 => e2 => ih(r2, ies2, e2))

def Tlvs.dv(+fuel: Nat, +bs: B.Bytes(), +ies: List<&2, T.Tlv>, e: {T.Tlvs.read(fuel, bs) == Done{ies} : Tlvs.Res()}) -> {T.Tlvs.valid(ies) == True{} : Bool}:
  match fuel bs:
    case 0n Nil{}:
      eo = Equal.cong(Tlvs.Res(), List<&2, T.Tlv>, x => P.Res.value(B.Err, List<&2, T.Tlv>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {T.Tlvs.valid(_) == True{} : Bool}
      {==}
    case 1n+f Nil{}:
      eo = Equal.cong(Tlvs.Res(), List<&2, T.Tlv>, x => P.Res.value(B.Err, List<&2, T.Tlv>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {T.Tlvs.valid(_) == True{} : Bool}
      {==}
    case 0n b <> r:
      Empty.absurd({T.Tlvs.valid(ies) == True{} : Bool}, P.Refute.fail_done(B.Err, List<&2, T.Tlv>, B.Invalid{b}, ies, e))
    case 1n++f +b <> +r:
      Tlvs.dv_next(f, b <> r, T.Tlv.read(b <> r), {==}, ies, e, left => ies2 => e2 => Tlvs.dv(f, left, ies2, e2))

# The TLVs read from some bytes measure exactly those bytes.
def Tlvs.len_cons(+bs: B.Bytes(), +ie: T.Tlv, +r2: B.Bytes(), +ro: Tlvs.Res(), +ies: List<&2, T.Tlv>, e: {T.Tlvs.cons(ie, ro) == Done{ies} : Tlvs.Res()}, cn: {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(List.length(&2, U32, T.Tlv.body(ie)), List.length(&2, U32, r2))) : Nat}, ih: @ies2: List<&2, T.Tlv> -> {ro == Done{ies2} : Tlvs.Res()} -> {T.Tlvs.size(ies2) == List.length(&2, U32, r2) : Nat}) -> {T.Tlvs.size(ies) == List.length(&2, U32, bs) : Nat}:
  match ro:
    case Fail{err}:
      Empty.absurd({T.Tlvs.size(ies) == List.length(&2, U32, bs) : Nat}, P.Refute.fail_done(B.Err, List<&2, T.Tlv>, err, ies, e))
    case Done{+ies2}:
      eo = Equal.cong(Tlvs.Res(), List<&2, T.Tlv>, x => P.Res.value(B.Err, List<&2, T.Tlv>, x, ies), Done{ie <> ies2}, Done{ies}, e)
      %eo : {T.Tlvs.size(_) == List.length(&2, U32, bs) : Nat}
      scn = Equal.sym(Nat, List.length(&2, U32, bs), Nat.add(4n, Nat.add(List.length(&2, U32, T.Tlv.body(ie)), List.length(&2, U32, r2))), cn)
      %scn : {T.Tlvs.size(ie <> ies2) == _ : Nat}
      Equal.cong(Nat, Nat, n => Nat.add(4n, Nat.add(List.length(&2, U32, T.Tlv.body(ie)), n)), T.Tlvs.size(ies2), List.length(&2, U32, r2), ih(ies2, {==}))

def Tlvs.len_next(+f: Nat, +bs: B.Bytes(), +rb: B.Read(T.Tlv), erb: {T.Tlv.read(bs) == rb : B.Read(T.Tlv)}, +ies: List<&2, T.Tlv>, e: {T.Tlvs.next(rb, left => T.Tlvs.read(f, left)) == Done{ies} : Tlvs.Res()}, ih: @left: B.Bytes() -> @ies2: List<&2, T.Tlv> -> {T.Tlvs.read(f, left) == Done{ies2} : Tlvs.Res()} -> {T.Tlvs.size(ies2) == List.length(&2, U32, left) : Nat}) -> {T.Tlvs.size(ies) == List.length(&2, U32, bs) : Nat}:
  match rb:
    case Fail{err}:
      Empty.absurd({T.Tlvs.size(ies) == List.length(&2, U32, bs) : Nat}, P.Refute.fail_done(B.Err, List<&2, T.Tlv>, err, ies, e))
    case Done{(+ie, +r2)}:
      Tlvs.len_cons(bs, ie, r2, T.Tlvs.read(f, r2), ies, e, Tlv.consumed(bs, ie, r2, erb), ies2 => e2 => ih(r2, ies2, e2))

def Tlvs.len(+fuel: Nat, +bs: B.Bytes(), +ies: List<&2, T.Tlv>, e: {T.Tlvs.read(fuel, bs) == Done{ies} : Tlvs.Res()}) -> {T.Tlvs.size(ies) == List.length(&2, U32, bs) : Nat}:
  match fuel bs:
    case 0n Nil{}:
      eo = Equal.cong(Tlvs.Res(), List<&2, T.Tlv>, x => P.Res.value(B.Err, List<&2, T.Tlv>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {T.Tlvs.size(_) == 0n : Nat}
      {==}
    case 1n+f Nil{}:
      eo = Equal.cong(Tlvs.Res(), List<&2, T.Tlv>, x => P.Res.value(B.Err, List<&2, T.Tlv>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {T.Tlvs.size(_) == 0n : Nat}
      {==}
    case 0n b <> r:
      Empty.absurd({T.Tlvs.size(ies) == 1n+List.length(&2, U32, r) : Nat}, P.Refute.fail_done(B.Err, List<&2, T.Tlv>, B.Invalid{b}, ies, e))
    case 1n++f +b <> +r:
      Tlvs.len_next(f, b <> r, T.Tlv.read(b <> r), {==}, ies, e, left => ies2 => e2 => Tlvs.len(f, left, ies2, e2))

# The bytes a list of TLVs was read from, before any tail, are its encoding.
def Tlvs.sx_cons(+bs: B.Bytes(), +ie: T.Tlv, +r2: B.Bytes(), +ro: Tlvs.Res(), +ies: List<&2, T.Tlv>, +e: {T.Tlvs.cons(ie, ro) == Done{ies} : Tlvs.Res()}, +tail: B.Bytes(), w: {T.Tlv.write(ie, List.append(&2, U32, r2, tail)) == List.append(&2, U32, bs, tail) : B.Bytes()}, ab2: {B.all_bytes(r2) == True{} : Bool}, ih: @ies2: List<&2, T.Tlv> -> {ro == Done{ies2} : Tlvs.Res()} -> {B.all_bytes(r2) == True{} : Bool} -> {T.Tlvs.write(ies2, tail) == List.append(&2, U32, r2, tail) : B.Bytes()}) -> {T.Tlvs.write(ies, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}:
  match ro:
    case Fail{err}:
      Empty.absurd({T.Tlvs.write(ies, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, T.Tlv>, err, ies, e))
    case Done{+ies2}:
      eo = Equal.cong(Tlvs.Res(), List<&2, T.Tlv>, x => P.Res.value(B.Err, List<&2, T.Tlv>, x, ies), Done{ie <> ies2}, Done{ies}, e)
      %eo : {T.Tlvs.write(_, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}
      sw = Equal.sym(B.Bytes(), T.Tlvs.write(ies2, tail), List.append(&2, U32, r2, tail), ih(ies2, {==}, ab2))
      %sw : {T.Tlv.write(ie, _) == List.append(&2, U32, bs, tail) : B.Bytes()}
      w

def Tlvs.sx_next(+f: Nat, +bs: B.Bytes(), +rb: B.Read(T.Tlv), +erb: {T.Tlv.read(bs) == rb : B.Read(T.Tlv)}, +ies: List<&2, T.Tlv>, +e: {T.Tlvs.next(rb, left => T.Tlvs.read(f, left)) == Done{ies} : Tlvs.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}, +tail: B.Bytes(), ih: @left: B.Bytes() -> @ies2: List<&2, T.Tlv> -> {T.Tlvs.read(f, left) == Done{ies2} : Tlvs.Res()} -> {B.all_bytes(left) == True{} : Bool} -> {T.Tlvs.write(ies2, tail) == List.append(&2, U32, left, tail) : B.Bytes()}) -> {T.Tlvs.write(ies, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}:
  match rb:
    case Fail{err}:
      Empty.absurd({T.Tlvs.write(ies, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, T.Tlv>, err, ies, e))
    case Done{(+ie, +r2)}:
      Tlvs.sx_cons(bs, ie, r2, T.Tlvs.read(f, r2), ies, e, tail, Tlv.sx(bs, ie, r2, erb, ab, tail), Tlv.rest_bytes(bs, ie, r2, erb, ab), ies2 => e2 => ab2 => ih(r2, ies2, e2, ab2))

def Tlvs.sx(+fuel: Nat, +bs: B.Bytes(), +ies: List<&2, T.Tlv>, +e: {T.Tlvs.read(fuel, bs) == Done{ies} : Tlvs.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}, +tail: B.Bytes()) -> {T.Tlvs.write(ies, tail) == List.append(&2, U32, bs, tail) : B.Bytes()}:
  match fuel bs:
    case 0n Nil{}:
      eo = Equal.cong(Tlvs.Res(), List<&2, T.Tlv>, x => P.Res.value(B.Err, List<&2, T.Tlv>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {T.Tlvs.write(_, tail) == tail : B.Bytes()}
      {==}
    case 1n+f Nil{}:
      eo = Equal.cong(Tlvs.Res(), List<&2, T.Tlv>, x => P.Res.value(B.Err, List<&2, T.Tlv>, x, ies), Done{[]}, Done{ies}, e)
      %eo : {T.Tlvs.write(_, tail) == tail : B.Bytes()}
      {==}
    case 0n b <> r:
      Empty.absurd({T.Tlvs.write(ies, tail) == b <> List.append(&2, U32, r, tail) : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, T.Tlv>, B.Invalid{b}, ies, e))
    case 1n++f +b <> +r:
      Tlvs.sx_next(f, b <> r, T.Tlv.read(b <> r), {==}, ies, e, ab, tail, left => ies2 => e2 => ab2 => Tlvs.sx(f, left, ies2, e2, ab2, tail))

def Tlvs.write_app(ies: List<&2, T.Tlv>, +rest: B.Bytes()) -> {T.Tlvs.write(ies, rest) == List.append(&2, U32, T.Tlvs.write(ies, []), rest) : B.Bytes()}:
  match ies:
    case Nil{}:
      {==}
    case T.Tlv{+kind, +len, +body} <> +more:
      +W = T.Tlvs.write(more, [])
      ih = Equal.sym(B.Bytes(), T.Tlvs.write(more, rest), List.append(&2, U32, W, rest), Tlvs.write_app(more, rest))
      %ih : {T.Tlv.write(T.Tlv{kind, len, body}, _) == List.append(&2, U32, T.Tlv.write(T.Tlv{kind, len, body}, W), rest) : B.Bytes()}
      Equal.cong(B.Bytes(), B.Bytes(), l => B.write_u16(kind, B.write_u16(len, l)), List.append(&2, U32, body, List.append(&2, U32, W, rest)), List.append(&2, U32, List.append(&2, U32, body, W), rest), Equal.sym(B.Bytes(), List.append(&2, U32, List.append(&2, U32, body, W), rest), List.append(&2, U32, body, List.append(&2, U32, W, rest)), Bytes.app_assoc(body, W, rest)))

def Tlvs.size_len(ies: List<&2, T.Tlv>) -> {T.Tlvs.size(ies) == List.length(&2, U32, T.Tlvs.write(ies, [])) : Nat}:
  match ies:
    case Nil{}:
      {==}
    case T.Tlv{+kind, +len, +body} <> +more:
      +W = T.Tlvs.write(more, [])
      sih = Equal.sym(Nat, T.Tlvs.size(more), List.length(&2, U32, W), Tlvs.size_len(more))
      %sih : {Nat.add(4n, Nat.add(List.length(&2, U32, body), _)) == List.length(&2, U32, T.Tlv.write(T.Tlv{kind, len, body}, W)) : Nat}
      Equal.cong(Nat, Nat, n => 1n+1n+1n+1n+n, Nat.add(List.length(&2, U32, body), List.length(&2, U32, W)), List.length(&2, U32, List.append(&2, U32, body, W)), Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, body, W)), Nat.add(List.length(&2, U32, body), List.length(&2, U32, W)), P.List.append_len(body, W)))
