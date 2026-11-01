import Base
import ../LAWS.bend as L
import ../bytes.bend as B
import ../plmn.bend as PL
import ../crypto/hmac.bend as H
import ../crypto/x25519.bend as X
import ../suci.bend as Su
import ./lib.bend as P

# Proofs of the X25519 and SUCI laws (ticket 08).

# X25519
# ------

def Fe.to_bytes_len(fe: B.Bytes()) -> {List.length(&2, U32, X.Fe.to_bytes(fe)) == 32n : Nat}:
  match fe:
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> l8 <> l9 <> l10 <> l11 <> l12 <> l13 <> l14 <> l15 <> rest:
      {==}
    case Nil{}:
      {==}
    case l0 <> Nil{}:
      {==}
    case l0 <> l1 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> l8 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> l8 <> l9 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> l8 <> l9 <> l10 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> l8 <> l9 <> l10 <> l11 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> l8 <> l9 <> l10 <> l11 <> l12 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> l8 <> l9 <> l10 <> l11 <> l12 <> l13 <> Nil{}:
      {==}
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> l8 <> l9 <> l10 <> l11 <> l12 <> l13 <> l14 <> Nil{}:
      {==}

def X25519.finish_len(st: X.X25519.State) -> {List.length(&2, U32, X.X25519.finish(st)) == 32n : Nat}:
  match st:
    case X.St{x2, z2, x3, z3, +swap}:
      Fe.to_bytes_len(X.Fe.freeze(X.Fe.mul(X.Fe.cswap(x2, x3, U32.sub(0, swap)), X.Fe.inv(X.Fe.cswap(z2, z3, U32.sub(0, swap))))))

def L.x25519.length(k, u):
  X25519.finish_len(X.X25519.ladder(X.X25519.bits(X.X25519.clamp(k)), X.St{X.Fe.one(), X.Fe.zero(), X.Fe.from_bytes(u), X.Fe.one(), 0}, X.Fe.from_bytes(u)))

# SUCI: length and MAC checks
# ---------------------------

def Suci.Res() -> Data:
  Result<&2, &2, B.Err, B.Digits()>

def Suci.short(+key: B.Bytes(), +output: B.Bytes(), e: {Nat.is_lt(List.length(&2, U32, output), 41n) == True{} : Bool}) -> {Su.Suci.deconceal_a(key, output) == Fail{B.Short{}} : Suci.Res()}:
  ge = Equal.sym(Bool, Nat.is_ge(List.length(&2, U32, output), 41n), False{}, P.Nat.ge_false_of_lt(List.length(&2, U32, output), 41n, e))
  %ge : {Su.Suci.a_len(key, output, _) == Fail{B.Short{}} : Suci.Res()}
  {==}

def Suci.MacSpec(key: B.Bytes(), output: B.Bytes()) -> Type:
  {Su.Suci.tag(key, output) == Su.Suci.mac(output) : B.Bytes()} & {List.length(&2, U32, Su.Suci.tag(key, output)) == 8n : Nat}

def Suci.tag_len(+key: B.Bytes(), +output: B.Bytes()) -> {List.length(&2, U32, Su.Suci.tag(key, output)) == 8n : Nat}:
  tl = Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, H.hmac(List.drop(&2, U32, Su.Suci.keys(key, output), 32n), Su.Suci.cipher(output)), 8n)), Nat.min(List.length(&2, U32, H.hmac(List.drop(&2, U32, Su.Suci.keys(key, output), 32n), Su.Suci.cipher(output))), 8n), P.List.take_len(H.hmac(List.drop(&2, U32, Su.Suci.keys(key, output), 32n), Su.Suci.cipher(output)), 8n))
  hl = Equal.sym(Nat, List.length(&2, U32, H.hmac(List.drop(&2, U32, Su.Suci.keys(key, output), 32n), Su.Suci.cipher(output))), 32n, L.hmac.length(List.drop(&2, U32, Su.Suci.keys(key, output), 32n), Su.Suci.cipher(output)))
  %tl : {_ == 8n : Nat}
  %hl : {Nat.min(_, 8n) == 8n : Nat}
  {==}

def Suci.mac_spec(+key: B.Bytes(), +output: B.Bytes(), msin: B.Digits(), ok: Bool, ev: {B.bytes_eq(Su.Suci.tag(key, output), Su.Suci.mac(output)) == ok : Bool},
  e: {Su.Suci.a_mac(output, Su.Suci.keys(key, output), ok) == Done{msin} : Suci.Res()}) -> Suci.MacSpec(key, output):
  match ok:
    case True{}:
      (P.Bytes.eq_of_bytes_eq(Su.Suci.tag(key, output), Su.Suci.mac(output), ev), Suci.tag_len(key, output))
    case False{}:
      Empty.absurd(Suci.MacSpec(key, output), P.Refute.fail_done(B.Err, B.Digits(), B.Invalid{2}, msin, e))

def Suci.len_spec(+key: B.Bytes(), +output: B.Bytes(), +msin: B.Digits(), ok: Bool, e: {Su.Suci.a_len(key, output, ok) == Done{msin} : Suci.Res()}) -> Suci.MacSpec(key, output):
  match ok:
    case True{}:
      Suci.mac_spec(key, output, msin, B.bytes_eq(Su.Suci.tag(key, output), Su.Suci.mac(output)), {==}, e)
    case False{}:
      Empty.absurd(Suci.MacSpec(key, output), P.Refute.fail_done(B.Err, B.Digits(), B.Short{}, msin, e))

def Suci.mismatch(+key: B.Bytes(), +output: B.Bytes(), ok: Bool, e: {B.bytes_eq(Su.Suci.tag(key, output), Su.Suci.mac(output)) == False{} : Bool}) -> {Result.is_fail(&2, &2, B.Err, B.Digits(), Su.Suci.a_len(key, output, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      se = Equal.sym(Bool, B.bytes_eq(Su.Suci.tag(key, output), Su.Suci.mac(output)), False{}, e)
      %se : {Result.is_fail(&2, &2, B.Err, B.Digits(), Su.Suci.a_mac(output, Su.Suci.keys(key, output), _)) == True{} : Bool}
      {==}
    case False{}:
      {==}

def L.suci.deconceal.length_checked(key, output, msin):
  (e => Suci.short(key, output, e), (e => Suci.len_spec(key, output, msin, Nat.is_ge(List.length(&2, U32, output), 41n), e), e => Suci.mismatch(key, output, Nat.is_ge(List.length(&2, U32, output), 41n), e)))

# SUCI: null scheme roundtrip
# ---------------------------

# TBCD digits survive encoding.
def Tbcd.rt1(+d: U32, xl: U32, xh: U32, el: {xl == d : U32}, eh: {xh == 15 : U32}, dd: {B.Tbcd.is_digit(d) == True{} : Bool}) -> {B.Tbcd.low(xl, xh, [], u => B.Tbcd.decode([]), B.Tbcd.is_digit(xl)) == Done{[d]} : Result<&2, &2, B.Err, B.Digits()>}:
  sl = Equal.sym(U32, xl, d, el)
  sh = Equal.sym(U32, xh, 15, eh)
  %sl : {B.Tbcd.low(_, xh, [], u => B.Tbcd.decode([]), B.Tbcd.is_digit(_)) == Done{[d]} : Result<&2, &2, B.Err, B.Digits()>}
  %sh : {B.Tbcd.low(d, _, [], u => B.Tbcd.decode([]), B.Tbcd.is_digit(d)) == Done{[d]} : Result<&2, &2, B.Err, B.Digits()>}
  sd = Equal.sym(Bool, B.Tbcd.is_digit(d), True{}, dd)
  %sd : {B.Tbcd.low(d, 15, [], u => B.Tbcd.decode([]), _) == Done{[d]} : Result<&2, &2, B.Err, B.Digits()>}
  {==}

def Tbcd.rt2(+d1: U32, +d2: U32, +rest: B.Bytes(), +more: B.Digits(), xl: U32, xh: U32, el: {xl == d1 : U32}, eh: {xh == d2 : U32}, dd1: {B.Tbcd.is_digit(d1) == True{} : Bool}, dd2: {B.Tbcd.is_digit(d2) == True{} : Bool}, ih: {B.Tbcd.decode(rest) == Done{more} : Result<&2, &2, B.Err, B.Digits()>}) -> {B.Tbcd.low(xl, xh, rest, u => B.Tbcd.decode(rest), B.Tbcd.is_digit(xl)) == Done{d1 <> d2 <> more} : Result<&2, &2, B.Err, B.Digits()>}:
  sl = Equal.sym(U32, xl, d1, el)
  sh = Equal.sym(U32, xh, d2, eh)
  %sl : {B.Tbcd.low(_, xh, rest, u => B.Tbcd.decode(rest), B.Tbcd.is_digit(_)) == Done{d1 <> d2 <> more} : Result<&2, &2, B.Err, B.Digits()>}
  %sh : {B.Tbcd.low(d1, _, rest, u => B.Tbcd.decode(rest), B.Tbcd.is_digit(d1)) == Done{d1 <> d2 <> more} : Result<&2, &2, B.Err, B.Digits()>}
  s1 = Equal.sym(Bool, B.Tbcd.is_digit(d1), True{}, dd1)
  %s1 : {B.Tbcd.low(d1, d2, rest, u => B.Tbcd.decode(rest), _) == Done{d1 <> d2 <> more} : Result<&2, &2, B.Err, B.Digits()>}
  s2 = Equal.sym(Bool, B.Tbcd.is_digit(d2), True{}, dd2)
  %s2 : {B.Tbcd.high(d1, d2, rest, u => B.Tbcd.decode(rest), _, U32.is_eq(d2, 15)) == Done{d1 <> d2 <> more} : Result<&2, &2, B.Err, B.Digits()>}
  si = Equal.sym(Result<&2, &2, B.Err, B.Digits()>, B.Tbcd.decode(rest), Done{more}, ih)
  %si : {B.Tbcd.cons2(d1, d2, _) == Done{d1 <> d2 <> more} : Result<&2, &2, B.Err, B.Digits()>}
  {==}

def Tbcd.rt(ds: B.Digits(), +m: {B.Tbcd.all_digits(ds) == True{} : Bool}) -> {B.Tbcd.decode(B.write_tbcd(ds, [])) == Done{ds} : Result<&2, &2, B.Err, B.Digits()>}:
  match ds:
    case Nil{}:
      {==}
    case +d <> Nil{}:
      Tbcd.rt1(d, U32.and(15, B.cat4(d, 15)), U32.and(15, U32.shrn(B.cat4(d, 15), 4n)), P.U32.cat4_lo(d, 15, P.U32.lt10_mask4(d, P.Bool.and_true_l(B.Tbcd.is_digit(d), True{}, m))), P.U32.cat4_hi(d, 15, {==}), P.Bool.and_true_l(B.Tbcd.is_digit(d), True{}, m))
    case +d1 <> +d2 <> +more:
      +dd1 = P.Bool.and_true_l(B.Tbcd.is_digit(d1), Bool.and(B.Tbcd.is_digit(d2), B.Tbcd.all_digits(more)), m)
      +r1 = P.Bool.and_true_r(B.Tbcd.is_digit(d1), Bool.and(B.Tbcd.is_digit(d2), B.Tbcd.all_digits(more)), m)
      +dd2 = P.Bool.and_true_l(B.Tbcd.is_digit(d2), B.Tbcd.all_digits(more), r1)
      Tbcd.rt2(d1, d2, B.write_tbcd(more, []), more, U32.and(15, B.cat4(d1, U32.and(15, d2))), U32.and(15, U32.shrn(B.cat4(d1, U32.and(15, d2)), 4n)), P.U32.cat4_lo(d1, d2, P.U32.lt10_mask4(d1, dd1)), P.U32.cat4_hi(d1, d2, P.U32.lt10_mask4(d2, dd2)), dd1, dd2, Tbcd.rt(more, P.Bool.and_true_r(B.Tbcd.is_digit(d2), B.Tbcd.all_digits(more), r1)))

# The routing indicator survives encoding, for one to four digits.
def Routing.core1(+a: U32, xa: U32, xb: U32, xc: U32, xd: U32, ea: {xa == a : U32}, eb: {xb == 15 : U32}, ec: {xc == 15 : U32}, ed: {xd == 15 : U32}, da: {B.Tbcd.is_digit(a) == True{} : Bool}) -> {Su.Routing.nonempty(Su.Routing.digits([xa, xb, xc, xd])) == Done{[a]} : Result<&2, &2, B.Err, B.Digits()>}:
  sa = Equal.sym(U32, xa, a, ea)
  %sa : {Su.Routing.nonempty(Su.Routing.digits([_, xb, xc, xd])) == Done{[a]} : Result<&2, &2, B.Err, B.Digits()>}
  sb = Equal.sym(U32, xb, 15, eb)
  %sb : {Su.Routing.nonempty(Su.Routing.digits([a, _, xc, xd])) == Done{[a]} : Result<&2, &2, B.Err, B.Digits()>}
  sc = Equal.sym(U32, xc, 15, ec)
  %sc : {Su.Routing.nonempty(Su.Routing.digits([a, 15, _, xd])) == Done{[a]} : Result<&2, &2, B.Err, B.Digits()>}
  sd = Equal.sym(U32, xd, 15, ed)
  %sd : {Su.Routing.nonempty(Su.Routing.digits([a, 15, 15, _])) == Done{[a]} : Result<&2, &2, B.Err, B.Digits()>}
  sda = Equal.sym(Bool, B.Tbcd.is_digit(a), True{}, da)
  %sda : {Su.Routing.nonempty(Su.Routing.step(a, [15, 15, 15], u => Su.Routing.digits([15, 15, 15]), _, U32.is_eq(a, 15))) == Done{[a]} : Result<&2, &2, B.Err, B.Digits()>}
  {==}

def Routing.core2(+a: U32, +b: U32, xa: U32, xb: U32, xc: U32, xd: U32, ea: {xa == a : U32}, eb: {xb == b : U32}, ec: {xc == 15 : U32}, ed: {xd == 15 : U32}, da: {B.Tbcd.is_digit(a) == True{} : Bool}, db: {B.Tbcd.is_digit(b) == True{} : Bool}) -> {Su.Routing.nonempty(Su.Routing.digits([xa, xb, xc, xd])) == Done{[a, b]} : Result<&2, &2, B.Err, B.Digits()>}:
  sa = Equal.sym(U32, xa, a, ea)
  %sa : {Su.Routing.nonempty(Su.Routing.digits([_, xb, xc, xd])) == Done{[a, b]} : Result<&2, &2, B.Err, B.Digits()>}
  sb = Equal.sym(U32, xb, b, eb)
  %sb : {Su.Routing.nonempty(Su.Routing.digits([a, _, xc, xd])) == Done{[a, b]} : Result<&2, &2, B.Err, B.Digits()>}
  sc = Equal.sym(U32, xc, 15, ec)
  %sc : {Su.Routing.nonempty(Su.Routing.digits([a, b, _, xd])) == Done{[a, b]} : Result<&2, &2, B.Err, B.Digits()>}
  sd = Equal.sym(U32, xd, 15, ed)
  %sd : {Su.Routing.nonempty(Su.Routing.digits([a, b, 15, _])) == Done{[a, b]} : Result<&2, &2, B.Err, B.Digits()>}
  sda = Equal.sym(Bool, B.Tbcd.is_digit(a), True{}, da)
  %sda : {Su.Routing.nonempty(Su.Routing.step(a, [b, 15, 15], u => Su.Routing.digits([b, 15, 15]), _, U32.is_eq(a, 15))) == Done{[a, b]} : Result<&2, &2, B.Err, B.Digits()>}
  sdb = Equal.sym(Bool, B.Tbcd.is_digit(b), True{}, db)
  %sdb : {Su.Routing.nonempty(Su.Routing.cons(a, Su.Routing.step(b, [15, 15], u => Su.Routing.digits([15, 15]), _, U32.is_eq(b, 15)))) == Done{[a, b]} : Result<&2, &2, B.Err, B.Digits()>}
  {==}

def Routing.core3(+a: U32, +b: U32, +c: U32, xa: U32, xb: U32, xc: U32, xd: U32, ea: {xa == a : U32}, eb: {xb == b : U32}, ec: {xc == c : U32}, ed: {xd == 15 : U32}, da: {B.Tbcd.is_digit(a) == True{} : Bool}, db: {B.Tbcd.is_digit(b) == True{} : Bool}, dc: {B.Tbcd.is_digit(c) == True{} : Bool}) -> {Su.Routing.nonempty(Su.Routing.digits([xa, xb, xc, xd])) == Done{[a, b, c]} : Result<&2, &2, B.Err, B.Digits()>}:
  sa = Equal.sym(U32, xa, a, ea)
  %sa : {Su.Routing.nonempty(Su.Routing.digits([_, xb, xc, xd])) == Done{[a, b, c]} : Result<&2, &2, B.Err, B.Digits()>}
  sb = Equal.sym(U32, xb, b, eb)
  %sb : {Su.Routing.nonempty(Su.Routing.digits([a, _, xc, xd])) == Done{[a, b, c]} : Result<&2, &2, B.Err, B.Digits()>}
  sc = Equal.sym(U32, xc, c, ec)
  %sc : {Su.Routing.nonempty(Su.Routing.digits([a, b, _, xd])) == Done{[a, b, c]} : Result<&2, &2, B.Err, B.Digits()>}
  sd = Equal.sym(U32, xd, 15, ed)
  %sd : {Su.Routing.nonempty(Su.Routing.digits([a, b, c, _])) == Done{[a, b, c]} : Result<&2, &2, B.Err, B.Digits()>}
  sda = Equal.sym(Bool, B.Tbcd.is_digit(a), True{}, da)
  %sda : {Su.Routing.nonempty(Su.Routing.step(a, [b, c, 15], u => Su.Routing.digits([b, c, 15]), _, U32.is_eq(a, 15))) == Done{[a, b, c]} : Result<&2, &2, B.Err, B.Digits()>}
  sdb = Equal.sym(Bool, B.Tbcd.is_digit(b), True{}, db)
  %sdb : {Su.Routing.nonempty(Su.Routing.cons(a, Su.Routing.step(b, [c, 15], u => Su.Routing.digits([c, 15]), _, U32.is_eq(b, 15)))) == Done{[a, b, c]} : Result<&2, &2, B.Err, B.Digits()>}
  sdc = Equal.sym(Bool, B.Tbcd.is_digit(c), True{}, dc)
  %sdc : {Su.Routing.nonempty(Su.Routing.cons(a, Su.Routing.cons(b, Su.Routing.step(c, [15], u => Su.Routing.digits([15]), _, U32.is_eq(c, 15))))) == Done{[a, b, c]} : Result<&2, &2, B.Err, B.Digits()>}
  {==}

def Routing.core4(+a: U32, +b: U32, +c: U32, +d: U32, xa: U32, xb: U32, xc: U32, xd: U32, ea: {xa == a : U32}, eb: {xb == b : U32}, ec: {xc == c : U32}, ed: {xd == d : U32}, da: {B.Tbcd.is_digit(a) == True{} : Bool}, db: {B.Tbcd.is_digit(b) == True{} : Bool}, dc: {B.Tbcd.is_digit(c) == True{} : Bool}, dd: {B.Tbcd.is_digit(d) == True{} : Bool}) -> {Su.Routing.nonempty(Su.Routing.digits([xa, xb, xc, xd])) == Done{[a, b, c, d]} : Result<&2, &2, B.Err, B.Digits()>}:
  sa = Equal.sym(U32, xa, a, ea)
  %sa : {Su.Routing.nonempty(Su.Routing.digits([_, xb, xc, xd])) == Done{[a, b, c, d]} : Result<&2, &2, B.Err, B.Digits()>}
  sb = Equal.sym(U32, xb, b, eb)
  %sb : {Su.Routing.nonempty(Su.Routing.digits([a, _, xc, xd])) == Done{[a, b, c, d]} : Result<&2, &2, B.Err, B.Digits()>}
  sc = Equal.sym(U32, xc, c, ec)
  %sc : {Su.Routing.nonempty(Su.Routing.digits([a, b, _, xd])) == Done{[a, b, c, d]} : Result<&2, &2, B.Err, B.Digits()>}
  sd = Equal.sym(U32, xd, d, ed)
  %sd : {Su.Routing.nonempty(Su.Routing.digits([a, b, c, _])) == Done{[a, b, c, d]} : Result<&2, &2, B.Err, B.Digits()>}
  sda = Equal.sym(Bool, B.Tbcd.is_digit(a), True{}, da)
  %sda : {Su.Routing.nonempty(Su.Routing.step(a, [b, c, d], u => Su.Routing.digits([b, c, d]), _, U32.is_eq(a, 15))) == Done{[a, b, c, d]} : Result<&2, &2, B.Err, B.Digits()>}
  sdb = Equal.sym(Bool, B.Tbcd.is_digit(b), True{}, db)
  %sdb : {Su.Routing.nonempty(Su.Routing.cons(a, Su.Routing.step(b, [c, d], u => Su.Routing.digits([c, d]), _, U32.is_eq(b, 15)))) == Done{[a, b, c, d]} : Result<&2, &2, B.Err, B.Digits()>}
  sdc = Equal.sym(Bool, B.Tbcd.is_digit(c), True{}, dc)
  %sdc : {Su.Routing.nonempty(Su.Routing.cons(a, Su.Routing.cons(b, Su.Routing.step(c, [d], u => Su.Routing.digits([d]), _, U32.is_eq(c, 15))))) == Done{[a, b, c, d]} : Result<&2, &2, B.Err, B.Digits()>}
  sdd = Equal.sym(Bool, B.Tbcd.is_digit(d), True{}, dd)
  %sdd : {Su.Routing.nonempty(Su.Routing.cons(a, Su.Routing.cons(b, Su.Routing.cons(c, Su.Routing.step(d, [], u => Su.Routing.digits([]), _, U32.is_eq(d, 15)))))) == Done{[a, b, c, d]} : Result<&2, &2, B.Err, B.Digits()>}
  {==}

def Suci.null_shape1(+plmn: PL.Plmn, +a: U32, +msin: B.Digits(), v: {PL.Plmn.valid(plmn) == True{} : Bool}, +da: {B.Tbcd.is_digit(a) == True{} : Bool}) -> {Su.Suci.read(Su.Suci.write(Su.Suci.null(plmn, [a], msin))) == Done{Su.Suci.null(plmn, [a], msin)} : Result<&2, &2, B.Err, Su.Suci>}:
  pr = Equal.sym(B.Read(PL.Plmn), PL.Plmn.read(PL.Plmn.write(plmn, Su.Routing.write([a], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))))), Done{(plmn, Su.Routing.write([a], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))))}, L.plmn.roundtrip(plmn, Su.Routing.write([a], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))), v))
  %pr : {Su.Suci.r_plmn(_) == Done{Su.Suci.null(plmn, [a], msin)} : Result<&2, &2, B.Err, Su.Suci>}
  rc = Equal.sym(Result<&2, &2, B.Err, B.Digits()>, Su.Routing.nonempty(Su.Routing.digits([U32.and(15, B.cat4(a, U32.and(15, 15))), U32.and(15, U32.shrn(B.cat4(a, U32.and(15, 15)), 4n)), U32.and(15, B.cat4(15, U32.and(15, 15))), U32.and(15, U32.shrn(B.cat4(15, U32.and(15, 15)), 4n))])), Done{[a]}, Routing.core1(a, U32.and(15, B.cat4(a, U32.and(15, 15))), U32.and(15, U32.shrn(B.cat4(a, U32.and(15, 15)), 4n)), U32.and(15, B.cat4(15, U32.and(15, 15))), U32.and(15, U32.shrn(B.cat4(15, U32.and(15, 15)), 4n)), P.U32.cat4_lo(a, 15, P.U32.lt10_mask4(a, da)), P.U32.cat4_hi(a, 15, {==}), P.U32.cat4_lo(15, 15, {==}), P.U32.cat4_hi(15, 15, {==}), da))
  %rc : {Su.Suci.r_routing(plmn, _, B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))) == Done{Su.Suci.null(plmn, [a], msin)} : Result<&2, &2, B.Err, Su.Suci>}
  {==}

def Suci.null_shape2(+plmn: PL.Plmn, +a: U32, +b: U32, +msin: B.Digits(), v: {PL.Plmn.valid(plmn) == True{} : Bool}, +da: {B.Tbcd.is_digit(a) == True{} : Bool}, +db: {B.Tbcd.is_digit(b) == True{} : Bool}) -> {Su.Suci.read(Su.Suci.write(Su.Suci.null(plmn, [a, b], msin))) == Done{Su.Suci.null(plmn, [a, b], msin)} : Result<&2, &2, B.Err, Su.Suci>}:
  pr = Equal.sym(B.Read(PL.Plmn), PL.Plmn.read(PL.Plmn.write(plmn, Su.Routing.write([a, b], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))))), Done{(plmn, Su.Routing.write([a, b], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))))}, L.plmn.roundtrip(plmn, Su.Routing.write([a, b], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))), v))
  %pr : {Su.Suci.r_plmn(_) == Done{Su.Suci.null(plmn, [a, b], msin)} : Result<&2, &2, B.Err, Su.Suci>}
  rc = Equal.sym(Result<&2, &2, B.Err, B.Digits()>, Su.Routing.nonempty(Su.Routing.digits([U32.and(15, B.cat4(a, U32.and(15, b))), U32.and(15, U32.shrn(B.cat4(a, U32.and(15, b)), 4n)), U32.and(15, B.cat4(15, U32.and(15, 15))), U32.and(15, U32.shrn(B.cat4(15, U32.and(15, 15)), 4n))])), Done{[a, b]}, Routing.core2(a, b, U32.and(15, B.cat4(a, U32.and(15, b))), U32.and(15, U32.shrn(B.cat4(a, U32.and(15, b)), 4n)), U32.and(15, B.cat4(15, U32.and(15, 15))), U32.and(15, U32.shrn(B.cat4(15, U32.and(15, 15)), 4n)), P.U32.cat4_lo(a, b, P.U32.lt10_mask4(a, da)), P.U32.cat4_hi(a, b, P.U32.lt10_mask4(b, db)), P.U32.cat4_lo(15, 15, {==}), P.U32.cat4_hi(15, 15, {==}), da, db))
  %rc : {Su.Suci.r_routing(plmn, _, B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))) == Done{Su.Suci.null(plmn, [a, b], msin)} : Result<&2, &2, B.Err, Su.Suci>}
  {==}

def Suci.null_shape3(+plmn: PL.Plmn, +a: U32, +b: U32, +c: U32, +msin: B.Digits(), v: {PL.Plmn.valid(plmn) == True{} : Bool}, +da: {B.Tbcd.is_digit(a) == True{} : Bool}, +db: {B.Tbcd.is_digit(b) == True{} : Bool}, +dc: {B.Tbcd.is_digit(c) == True{} : Bool}) -> {Su.Suci.read(Su.Suci.write(Su.Suci.null(plmn, [a, b, c], msin))) == Done{Su.Suci.null(plmn, [a, b, c], msin)} : Result<&2, &2, B.Err, Su.Suci>}:
  pr = Equal.sym(B.Read(PL.Plmn), PL.Plmn.read(PL.Plmn.write(plmn, Su.Routing.write([a, b, c], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))))), Done{(plmn, Su.Routing.write([a, b, c], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))))}, L.plmn.roundtrip(plmn, Su.Routing.write([a, b, c], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))), v))
  %pr : {Su.Suci.r_plmn(_) == Done{Su.Suci.null(plmn, [a, b, c], msin)} : Result<&2, &2, B.Err, Su.Suci>}
  rc = Equal.sym(Result<&2, &2, B.Err, B.Digits()>, Su.Routing.nonempty(Su.Routing.digits([U32.and(15, B.cat4(a, U32.and(15, b))), U32.and(15, U32.shrn(B.cat4(a, U32.and(15, b)), 4n)), U32.and(15, B.cat4(c, U32.and(15, 15))), U32.and(15, U32.shrn(B.cat4(c, U32.and(15, 15)), 4n))])), Done{[a, b, c]}, Routing.core3(a, b, c, U32.and(15, B.cat4(a, U32.and(15, b))), U32.and(15, U32.shrn(B.cat4(a, U32.and(15, b)), 4n)), U32.and(15, B.cat4(c, U32.and(15, 15))), U32.and(15, U32.shrn(B.cat4(c, U32.and(15, 15)), 4n)), P.U32.cat4_lo(a, b, P.U32.lt10_mask4(a, da)), P.U32.cat4_hi(a, b, P.U32.lt10_mask4(b, db)), P.U32.cat4_lo(c, 15, P.U32.lt10_mask4(c, dc)), P.U32.cat4_hi(c, 15, {==}), da, db, dc))
  %rc : {Su.Suci.r_routing(plmn, _, B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))) == Done{Su.Suci.null(plmn, [a, b, c], msin)} : Result<&2, &2, B.Err, Su.Suci>}
  {==}

def Suci.null_shape4(+plmn: PL.Plmn, +a: U32, +b: U32, +c: U32, +d: U32, +msin: B.Digits(), v: {PL.Plmn.valid(plmn) == True{} : Bool}, +da: {B.Tbcd.is_digit(a) == True{} : Bool}, +db: {B.Tbcd.is_digit(b) == True{} : Bool}, +dc: {B.Tbcd.is_digit(c) == True{} : Bool}, +dd: {B.Tbcd.is_digit(d) == True{} : Bool}) -> {Su.Suci.read(Su.Suci.write(Su.Suci.null(plmn, [a, b, c, d], msin))) == Done{Su.Suci.null(plmn, [a, b, c, d], msin)} : Result<&2, &2, B.Err, Su.Suci>}:
  pr = Equal.sym(B.Read(PL.Plmn), PL.Plmn.read(PL.Plmn.write(plmn, Su.Routing.write([a, b, c, d], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))))), Done{(plmn, Su.Routing.write([a, b, c, d], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))))}, L.plmn.roundtrip(plmn, Su.Routing.write([a, b, c, d], B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))), v))
  %pr : {Su.Suci.r_plmn(_) == Done{Su.Suci.null(plmn, [a, b, c, d], msin)} : Result<&2, &2, B.Err, Su.Suci>}
  rc = Equal.sym(Result<&2, &2, B.Err, B.Digits()>, Su.Routing.nonempty(Su.Routing.digits([U32.and(15, B.cat4(a, U32.and(15, b))), U32.and(15, U32.shrn(B.cat4(a, U32.and(15, b)), 4n)), U32.and(15, B.cat4(c, U32.and(15, d))), U32.and(15, U32.shrn(B.cat4(c, U32.and(15, d)), 4n))])), Done{[a, b, c, d]}, Routing.core4(a, b, c, d, U32.and(15, B.cat4(a, U32.and(15, b))), U32.and(15, U32.shrn(B.cat4(a, U32.and(15, b)), 4n)), U32.and(15, B.cat4(c, U32.and(15, d))), U32.and(15, U32.shrn(B.cat4(c, U32.and(15, d)), 4n)), P.U32.cat4_lo(a, b, P.U32.lt10_mask4(a, da)), P.U32.cat4_hi(a, b, P.U32.lt10_mask4(b, db)), P.U32.cat4_lo(c, d, P.U32.lt10_mask4(c, dc)), P.U32.cat4_hi(c, d, P.U32.lt10_mask4(d, dd)), da, db, dc, dd))
  %rc : {Su.Suci.r_routing(plmn, _, B.write_u8(0, B.write_u8(0, B.write_tbcd(msin, [])))) == Done{Su.Suci.null(plmn, [a, b, c, d], msin)} : Result<&2, &2, B.Err, Su.Suci>}
  {==}

def Suci.null_rt_read(+plmn: PL.Plmn, routing: B.Digits(), +msin: B.Digits(), +v: {PL.Plmn.valid(plmn) == True{} : Bool}, +r: {Su.Routing.valid(routing) == True{} : Bool}) -> {Su.Suci.read(Su.Suci.write(Su.Suci.null(plmn, routing, msin))) == Done{Su.Suci.null(plmn, routing, msin)} : Result<&2, &2, B.Err, Su.Suci>}:
  match routing:
    case Nil{}:
      Empty.absurd({Su.Suci.read(Su.Suci.write(Su.Suci.null(plmn, [], msin))) == Done{Su.Suci.null(plmn, [], msin)} : Result<&2, &2, B.Err, Su.Suci>}, P.Refute.bool(r))
    case +a <> Nil{}:
      Suci.null_shape1(plmn, a, msin, v, P.Bool.and_true_l(B.Tbcd.is_digit(a), True{}, r))
    case +a <> +b <> Nil{}:
      +r1 = P.Bool.and_true_r(B.Tbcd.is_digit(a), Bool.and(B.Tbcd.is_digit(b), True{}), r)
      Suci.null_shape2(plmn, a, b, msin, v, P.Bool.and_true_l(B.Tbcd.is_digit(a), Bool.and(B.Tbcd.is_digit(b), True{}), r), P.Bool.and_true_l(B.Tbcd.is_digit(b), True{}, r1))
    case +a <> +b <> +c <> Nil{}:
      +r1 = P.Bool.and_true_r(B.Tbcd.is_digit(a), Bool.and(B.Tbcd.is_digit(b), Bool.and(B.Tbcd.is_digit(c), True{})), r)
      +r2 = P.Bool.and_true_r(B.Tbcd.is_digit(b), Bool.and(B.Tbcd.is_digit(c), True{}), r1)
      Suci.null_shape3(plmn, a, b, c, msin, v, P.Bool.and_true_l(B.Tbcd.is_digit(a), Bool.and(B.Tbcd.is_digit(b), Bool.and(B.Tbcd.is_digit(c), True{})), r), P.Bool.and_true_l(B.Tbcd.is_digit(b), Bool.and(B.Tbcd.is_digit(c), True{}), r1), P.Bool.and_true_l(B.Tbcd.is_digit(c), True{}, r2))
    case +a <> +b <> +c <> +d <> Nil{}:
      +r1 = P.Bool.and_true_r(B.Tbcd.is_digit(a), Bool.and(B.Tbcd.is_digit(b), Bool.and(B.Tbcd.is_digit(c), Bool.and(B.Tbcd.is_digit(d), True{}))), r)
      +r2 = P.Bool.and_true_r(B.Tbcd.is_digit(b), Bool.and(B.Tbcd.is_digit(c), Bool.and(B.Tbcd.is_digit(d), True{})), r1)
      +r3 = P.Bool.and_true_r(B.Tbcd.is_digit(c), Bool.and(B.Tbcd.is_digit(d), True{}), r2)
      Suci.null_shape4(plmn, a, b, c, d, msin, v, P.Bool.and_true_l(B.Tbcd.is_digit(a), Bool.and(B.Tbcd.is_digit(b), Bool.and(B.Tbcd.is_digit(c), Bool.and(B.Tbcd.is_digit(d), True{}))), r), P.Bool.and_true_l(B.Tbcd.is_digit(b), Bool.and(B.Tbcd.is_digit(c), Bool.and(B.Tbcd.is_digit(d), True{})), r1), P.Bool.and_true_l(B.Tbcd.is_digit(c), Bool.and(B.Tbcd.is_digit(d), True{}), r2), P.Bool.and_true_l(B.Tbcd.is_digit(d), True{}, r3))
    case a <> b <> c <> d <> e <> more:
      Empty.absurd({Su.Suci.read(Su.Suci.write(Su.Suci.null(plmn, a <> b <> c <> d <> e <> more, msin))) == Done{Su.Suci.null(plmn, a <> b <> c <> d <> e <> more, msin)} : Result<&2, &2, B.Err, Su.Suci>}, P.Refute.bool(r))

def L.suci.null_scheme.roundtrip(plmn, routing, msin, v, r, m):
  (Suci.null_rt_read(plmn, routing, msin, v, r), Tbcd.rt(msin, m))
