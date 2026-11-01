import Base
import ../LAWS.bend as L
import ../bytes.bend as B
import ../plmn.bend as PL
import ./lib.bend as P

# Proofs of the PLMN laws (ticket 08).

# The decoder answers Done only through Plmn.check with ok = valid(p).
def Plmn.check_spec(-G: Type, +p: PL.Plmn, +rest: B.Bytes(), +q: PL.Plmn, +rest2: B.Bytes(), ok: Bool, ev: {PL.Plmn.valid(p) == ok : Bool},
  e: {PL.Plmn.check(p, rest, ok) == Done{(q, rest2)} : B.Read(PL.Plmn)},
  k: {PL.Plmn.valid(p) == True{} : Bool} -> {Done{(p, rest)} == Done{(q, rest2)} : B.Read(PL.Plmn)} -> G) -> G:
  match ok:
    case True{}:
      k(ev, e)
    case False{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, B.ReadValue(PL.Plmn), B.Invalid{1}, (q, rest2), e))

def Plmn.read_shape(-G: Type, bs: B.Bytes(), +q: PL.Plmn, +rest2: B.Bytes(), e: {PL.Plmn.read(bs) == Done{(q, rest2)} : B.Read(PL.Plmn)},
  k: @b0: U32 -> @b1: U32 -> @b2: U32 -> @t: B.Bytes() -> {bs == b0 <> b1 <> b2 <> t : B.Bytes()} ->
     {PL.Plmn.read(b0 <> b1 <> b2 <> t) == Done{(q, rest2)} : B.Read(PL.Plmn)} -> G) -> G:
  match bs:
    case Nil{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, B.ReadValue(PL.Plmn), B.Short{}, (q, rest2), e))
    case b0 <> Nil{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, B.ReadValue(PL.Plmn), B.Short{}, (q, rest2), e))
    case b0 <> b1 <> Nil{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, B.ReadValue(PL.Plmn), B.Short{}, (q, rest2), e))
    case b0 <> b1 <> b2 <> t:
      k(b0, b1, b2, t, {==}, e)

def Plmn.valid_of_done(+p: PL.Plmn, +rest: B.Bytes(), +q: PL.Plmn, +rest2: B.Bytes(), v: {PL.Plmn.valid(p) == True{} : Bool}, e: {Done{(p, rest)} == Done{(q, rest2)} : B.Read(PL.Plmn)}) -> {PL.Plmn.valid(q) == True{} : Bool}:
  eq = Equal.cong(B.Read(PL.Plmn), PL.Plmn, x => P.Read.value(PL.Plmn, x, q), Done{(p, rest)}, Done{(q, rest2)}, e)
  %eq : {PL.Plmn.valid(_) == True{} : Bool}
  v

def Plmn.decode_valid.body(+b0: U32, +b1: U32, +b2: U32, +t: B.Bytes(), +q: PL.Plmn, +rest2: B.Bytes(), e: {PL.Plmn.read(b0 <> b1 <> b2 <> t) == Done{(q, rest2)} : B.Read(PL.Plmn)}) -> {PL.Plmn.valid(q) == True{} : Bool}:
  Plmn.check_spec({PL.Plmn.valid(q) == True{} : Bool}, PL.Plmn{U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, b2), U32.and(15, U32.shrn(b2, 4n)), U32.and(15, U32.shrn(b1, 4n))}, t, q, rest2,
    PL.Plmn.valid(PL.Plmn{U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, b2), U32.and(15, U32.shrn(b2, 4n)), U32.and(15, U32.shrn(b1, 4n))}), {==}, e,
    v => e2 => Plmn.valid_of_done(PL.Plmn{U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, b2), U32.and(15, U32.shrn(b2, 4n)), U32.and(15, U32.shrn(b1, 4n))}, t, q, rest2, v, e2))

def L.plmn.decode_valid(bs, p, rest, e):
  Plmn.read_shape({PL.Plmn.valid(p) == True{} : Bool}, bs, p, rest, e, b0 => b1 => b2 => t => shape => e2 => Plmn.decode_valid.body(b0, b1, b2, t, p, rest, e2))

def Plmn.rest_of_done(p: PL.Plmn, +rest: B.Bytes(), +q: PL.Plmn, +rest2: B.Bytes(), e: {Done{(p, rest)} == Done{(q, rest2)} : B.Read(PL.Plmn)}) -> {rest == rest2 : B.Bytes()}:
  Equal.cong(B.Read(PL.Plmn), B.Bytes(), x => P.Read.rest(PL.Plmn, x, rest), Done{(p, rest)}, Done{(q, rest2)}, e)

def Plmn.suffix.finish(p: PL.Plmn, +t: B.Bytes(), q: PL.Plmn, rest2: B.Bytes(), e: {Done{(p, t)} == Done{(q, rest2)} : B.Read(PL.Plmn)}) -> {List.drop(&2, U32, t, 0n) == rest2 : B.Bytes()}:
  d0 = Equal.sym(B.Bytes(), List.drop(&2, U32, t, 0n), t, P.List.drop0(t))
  %d0 : {_ == rest2 : B.Bytes()}
  Plmn.rest_of_done(p, t, q, rest2, e)

def Plmn.suffix.body(+b0: U32, +b1: U32, +b2: U32, +t: B.Bytes(), +q: PL.Plmn, +rest2: B.Bytes(), e: {PL.Plmn.read(b0 <> b1 <> b2 <> t) == Done{(q, rest2)} : B.Read(PL.Plmn)}) -> {List.drop(&2, U32, b0 <> b1 <> b2 <> t, 3n) == rest2 : B.Bytes()}:
  Plmn.check_spec({List.drop(&2, U32, b0 <> b1 <> b2 <> t, 3n) == rest2 : B.Bytes()}, PL.Plmn{U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, b2), U32.and(15, U32.shrn(b2, 4n)), U32.and(15, U32.shrn(b1, 4n))}, t, q, rest2,
    PL.Plmn.valid(PL.Plmn{U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, b2), U32.and(15, U32.shrn(b2, 4n)), U32.and(15, U32.shrn(b1, 4n))}), {==}, e,
    v => e2 => Plmn.suffix.finish(PL.Plmn{U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, b2), U32.and(15, U32.shrn(b2, 4n)), U32.and(15, U32.shrn(b1, 4n))}, t, q, rest2, e2))

def Plmn.suffix.rewrite(bs: B.Bytes(), b0: U32, b1: U32, b2: U32, t: B.Bytes(), p: PL.Plmn, rest: B.Bytes(), shape: {bs == b0 <> b1 <> b2 <> t : B.Bytes()}, r: {List.drop(&2, U32, b0 <> b1 <> b2 <> t, 3n) == rest : B.Bytes()}) -> {List.drop(&2, U32, bs, 3n) == rest : B.Bytes()}:
  sh = Equal.sym(B.Bytes(), bs, b0 <> b1 <> b2 <> t, shape)
  %sh : {List.drop(&2, U32, _, 3n) == rest : B.Bytes()}
  r

def Plmn.suffix.all(bs: B.Bytes(), +b0: U32, +b1: U32, +b2: U32, +t: B.Bytes(), +p: PL.Plmn, +rest: B.Bytes(), shape: {bs == b0 <> b1 <> b2 <> t : B.Bytes()}, e: {PL.Plmn.read(b0 <> b1 <> b2 <> t) == Done{(p, rest)} : B.Read(PL.Plmn)}) -> {List.drop(&2, U32, bs, 3n) == rest : B.Bytes()}:
  Plmn.suffix.rewrite(bs, b0, b1, b2, t, p, rest, shape, Plmn.suffix.body(b0, b1, b2, t, p, rest, e))

def L.plmn.suffix(bs, p, rest, e):
  Plmn.read_shape({List.drop(&2, U32, bs, 3n) == rest : B.Bytes()}, bs, p, rest, e,
    b0 => b1 => b2 => t => shape => e2 => Plmn.suffix.all(bs, b0, b1, b2, t, p, rest, shape, e2))

# Roundtrip: each digit of a valid PLMN fits its nibble, so the three
# nibble roundtrips return the fields unchanged.

def Plmn.mnc3_mask(+f: U32, lt: Bool, ev: {PL.Plmn.digit(f) == lt : Bool}, ok: {Bool.or(lt, U32.is_eq(f, 15)) == True{} : Bool}) -> {U32.and(15, f) == f : U32}:
  match lt:
    case True{}:
      P.U32.lt10_mask4(f, ev)
    case False{}:
      fe = Equal.sym(U32, f, 15, P.U32.eq_of_is_eq(f, 15, ok))
      %fe : {U32.and(15, _) == _ : U32}
      {==}

# The decoder's fields equal the written ones, so check answers Done.
def Plmn.rt_core(+a: U32, +b: U32, +c: U32, +d: U32, +e: U32, +f: U32, xa: U32, xb: U32, xc: U32, xd: U32, xe: U32, xf: U32, +rest: B.Bytes(),
  ea: {xa == a : U32}, eb: {xb == b : U32}, ec: {xc == c : U32}, ed: {xd == d : U32}, ee: {xe == e : U32}, ef: {xf == f : U32},
  v: {PL.Plmn.valid(PL.Plmn{a, b, c, d, e, f}) == True{} : Bool}) -> {PL.Plmn.check(PL.Plmn{xa, xb, xc, xd, xe, xf}, rest, PL.Plmn.valid(PL.Plmn{xa, xb, xc, xd, xe, xf})) == Done{(PL.Plmn{a, b, c, d, e, f}, rest)} : B.Read(PL.Plmn)}:
  sa = Equal.sym(U32, xa, a, ea)
  sb = Equal.sym(U32, xb, b, eb)
  sc = Equal.sym(U32, xc, c, ec)
  sd = Equal.sym(U32, xd, d, ed)
  se = Equal.sym(U32, xe, e, ee)
  sf = Equal.sym(U32, xf, f, ef)
  %sa : {PL.Plmn.check(PL.Plmn{_, xb, xc, xd, xe, xf}, rest, PL.Plmn.valid(PL.Plmn{_, xb, xc, xd, xe, xf})) == Done{(PL.Plmn{a, b, c, d, e, f}, rest)} : B.Read(PL.Plmn)}
  %sb : {PL.Plmn.check(PL.Plmn{a, _, xc, xd, xe, xf}, rest, PL.Plmn.valid(PL.Plmn{a, _, xc, xd, xe, xf})) == Done{(PL.Plmn{a, b, c, d, e, f}, rest)} : B.Read(PL.Plmn)}
  %sc : {PL.Plmn.check(PL.Plmn{a, b, _, xd, xe, xf}, rest, PL.Plmn.valid(PL.Plmn{a, b, _, xd, xe, xf})) == Done{(PL.Plmn{a, b, c, d, e, f}, rest)} : B.Read(PL.Plmn)}
  %sd : {PL.Plmn.check(PL.Plmn{a, b, c, _, xe, xf}, rest, PL.Plmn.valid(PL.Plmn{a, b, c, _, xe, xf})) == Done{(PL.Plmn{a, b, c, d, e, f}, rest)} : B.Read(PL.Plmn)}
  %se : {PL.Plmn.check(PL.Plmn{a, b, c, d, _, xf}, rest, PL.Plmn.valid(PL.Plmn{a, b, c, d, _, xf})) == Done{(PL.Plmn{a, b, c, d, e, f}, rest)} : B.Read(PL.Plmn)}
  %sf : {PL.Plmn.check(PL.Plmn{a, b, c, d, e, _}, rest, PL.Plmn.valid(PL.Plmn{a, b, c, d, e, _})) == Done{(PL.Plmn{a, b, c, d, e, f}, rest)} : B.Read(PL.Plmn)}
  sv = Equal.sym(Bool, PL.Plmn.valid(PL.Plmn{a, b, c, d, e, f}), True{}, v)
  %sv : {PL.Plmn.check(PL.Plmn{a, b, c, d, e, f}, rest, _) == Done{(PL.Plmn{a, b, c, d, e, f}, rest)} : B.Read(PL.Plmn)}
  {==}

def Plmn.roundtrip.body(+a: U32, +b: U32, +c: U32, +d: U32, +e: U32, +f: U32, +rest: B.Bytes(), +v: {PL.Plmn.valid(PL.Plmn{a, b, c, d, e, f}) == True{} : Bool}) -> {PL.Plmn.read(PL.Plmn.write(PL.Plmn{a, b, c, d, e, f}, rest)) == Done{(PL.Plmn{a, b, c, d, e, f}, rest)} : B.Read(PL.Plmn)}:
  va = P.Bool.and_true_l(PL.Plmn.digit(a), Bool.and(PL.Plmn.digit(b), Bool.and(PL.Plmn.digit(c), Bool.and(PL.Plmn.digit(d), Bool.and(PL.Plmn.digit(e), Bool.or(PL.Plmn.digit(f), U32.is_eq(f, 15)))))), v)
  +v1 = P.Bool.and_true_r(PL.Plmn.digit(a), Bool.and(PL.Plmn.digit(b), Bool.and(PL.Plmn.digit(c), Bool.and(PL.Plmn.digit(d), Bool.and(PL.Plmn.digit(e), Bool.or(PL.Plmn.digit(f), U32.is_eq(f, 15)))))), v)
  vb = P.Bool.and_true_l(PL.Plmn.digit(b), Bool.and(PL.Plmn.digit(c), Bool.and(PL.Plmn.digit(d), Bool.and(PL.Plmn.digit(e), Bool.or(PL.Plmn.digit(f), U32.is_eq(f, 15))))), v1)
  +v2 = P.Bool.and_true_r(PL.Plmn.digit(b), Bool.and(PL.Plmn.digit(c), Bool.and(PL.Plmn.digit(d), Bool.and(PL.Plmn.digit(e), Bool.or(PL.Plmn.digit(f), U32.is_eq(f, 15))))), v1)
  vc = P.Bool.and_true_l(PL.Plmn.digit(c), Bool.and(PL.Plmn.digit(d), Bool.and(PL.Plmn.digit(e), Bool.or(PL.Plmn.digit(f), U32.is_eq(f, 15)))), v2)
  +v3 = P.Bool.and_true_r(PL.Plmn.digit(c), Bool.and(PL.Plmn.digit(d), Bool.and(PL.Plmn.digit(e), Bool.or(PL.Plmn.digit(f), U32.is_eq(f, 15)))), v2)
  vd = P.Bool.and_true_l(PL.Plmn.digit(d), Bool.and(PL.Plmn.digit(e), Bool.or(PL.Plmn.digit(f), U32.is_eq(f, 15))), v3)
  +v4 = P.Bool.and_true_r(PL.Plmn.digit(d), Bool.and(PL.Plmn.digit(e), Bool.or(PL.Plmn.digit(f), U32.is_eq(f, 15))), v3)
  ve = P.Bool.and_true_l(PL.Plmn.digit(e), Bool.or(PL.Plmn.digit(f), U32.is_eq(f, 15)), v4)
  vf = P.Bool.and_true_r(PL.Plmn.digit(e), Bool.or(PL.Plmn.digit(f), U32.is_eq(f, 15)), v4)
  ma = P.U32.lt10_mask4(a, va)
  mb = P.U32.lt10_mask4(b, vb)
  mc = P.U32.lt10_mask4(c, vc)
  md = P.U32.lt10_mask4(d, vd)
  me = P.U32.lt10_mask4(e, ve)
  mf = Plmn.mnc3_mask(f, PL.Plmn.digit(f), {==}, vf)
  Plmn.rt_core(a, b, c, d, e, f, U32.and(15, B.cat4(a, U32.and(15, b))), U32.and(15, U32.shrn(B.cat4(a, U32.and(15, b)), 4n)), U32.and(15, B.cat4(c, U32.and(15, f))), U32.and(15, B.cat4(d, U32.and(15, e))), U32.and(15, U32.shrn(B.cat4(d, U32.and(15, e)), 4n)), U32.and(15, U32.shrn(B.cat4(c, U32.and(15, f)), 4n)), rest,
    P.U32.cat4_lo(a, b, ma), P.U32.cat4_hi(a, b, mb), P.U32.cat4_lo(c, f, mc), P.U32.cat4_lo(d, e, md), P.U32.cat4_hi(d, e, me), P.U32.cat4_hi(c, f, mf), v)

def L.plmn.roundtrip(p, rest, v):
  match p:
    case PL.Plmn{a, b, c, d, e, f}:
      Plmn.roundtrip.body(a, b, c, d, e, f, rest, v)
