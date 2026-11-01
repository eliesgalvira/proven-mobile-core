import Base
import ../LAWS.bend as L
import ../bytes.bend as B
import ../nas/ie.bend as I
import ../nas/sm_ies.bend as Q
import ./lib.bend as P
import ./bytes.bend as PB
import ./mm.bend as PM

# Proofs of the 5GSM information element laws (ticket 11).

def Comp.Rd() -> Data:
  B.Read(Q.Comp)

def Comp.payload(c: Q.Comp) -> Q.Payload:
  match c:
    case Q.Comp{kind, p}:
      p

def Payload.not_ipv4(p: Q.Payload) -> Type:
  match p:
    case Q.PIpv4{addr, mask}:
      Empty
    case Q.PNone{}:
      Unit
    case Q.PIpv6{addr, prefix}:
      Unit
    case Q.POne{v}:
      Unit
    case Q.PTwo{v}:
      Unit
    case Q.PThree{v}:
      Unit
    case Q.PFour{v}:
      Unit
    case Q.PSix{bytes}:
      Unit

def Payload.mask(p: Q.Payload, d: U32) -> U32:
  match p:
    case Q.PIpv4{addr, mask}:
      mask
    case _:
      d

# The mask of an IPv4 component is contiguous
# -------------------------------------------

def Mask.Goal(mask: U32) -> Type:
  {Q.Mask.contiguous(mask) == True{} : Bool}

def Mask.target(kind: U32, addr: U32, mask: U32, rest: B.Bytes()) -> Comp.Rd():
  Done{(Q.Comp{kind, Q.PIpv4{addr, mask}}, rest)}

# The payload the reader produced is the IPv4 payload of the statement.
def Mask.payload_eq(+kind: U32, +addr: U32, +mask: U32, +rest: B.Bytes(), +k2: U32, +p2: Q.Payload, +r2: B.Bytes(), e: {Done{(Q.Comp{k2, p2}, r2)} == Mask.target(kind, addr, mask, rest) : Comp.Rd()}) -> {p2 == Q.PIpv4{addr, mask} : Q.Payload}:
  Equal.cong(Comp.Rd(), Q.Payload, x => Comp.payload(P.Read.value(Q.Comp, x, Q.Comp{kind, Q.PIpv4{addr, mask}})), Done{(Q.Comp{k2, p2}, r2)}, Mask.target(kind, addr, mask, rest), e)

def Mask.absurd(+kind: U32, +addr: U32, +mask: U32, +rest: B.Bytes(), err: B.Err, e: {Fail{err} == Mask.target(kind, addr, mask, rest) : Comp.Rd()}) -> Mask.Goal(mask):
  Empty.absurd(Mask.Goal(mask), P.Refute.fail_done(B.Err, B.ReadValue(Q.Comp), err, (Q.Comp{kind, Q.PIpv4{addr, mask}}, rest), e))

def Mask.ipv4_ok(+kind: U32, +addr: U32, +mask: U32, +rest: B.Bytes(), +k2: U32, +a2: U32, +m2: U32, +r2: B.Bytes(), ok: Bool, ev: {Q.Mask.contiguous(m2) == ok : Bool}, e: {Q.Comp.of(k2, Q.Ok(B.ReadValue(Q.Payload), (Q.PIpv4{a2, m2}, r2), m2, ok)) == Mask.target(kind, addr, mask, rest) : Comp.Rd()}) -> Mask.Goal(mask):
  match ok:
    case False{}:
      Mask.absurd(kind, addr, mask, rest, B.Invalid{m2}, e)
    case True{}:
      em = Equal.cong(Q.Payload, U32, x => Payload.mask(x, m2), Q.PIpv4{a2, m2}, Q.PIpv4{addr, mask}, Mask.payload_eq(kind, addr, mask, rest, k2, Q.PIpv4{a2, m2}, r2, e))
      %em : Mask.Goal(_)
      ev

def Mask.ipv4_mask(+kind: U32, +addr: U32, +mask: U32, +rest: B.Bytes(), +k2: U32, +a2: U32, r1: B.Bytes(), e: {Q.Comp.of(k2, Q.Payload.ipv4(a2, B.u32(r1))) == Mask.target(kind, addr, mask, rest) : Comp.Rd()}) -> Mask.Goal(mask):
  match r1:
    case Nil{}:
      Mask.absurd(kind, addr, mask, rest, B.Short{}, e)
    case x <> Nil{}:
      Mask.absurd(kind, addr, mask, rest, B.Short{}, e)
    case x <> y <> Nil{}:
      Mask.absurd(kind, addr, mask, rest, B.Short{}, e)
    case x <> y <> z <> Nil{}:
      Mask.absurd(kind, addr, mask, rest, B.Short{}, e)
    case +m3 <> +m2 <> +m1 <> +m0 <> +r2:
      Mask.ipv4_ok(kind, addr, mask, rest, k2, a2, B.cat8(m0, B.cat8(m1, B.cat8(m2, m3))), r2, Q.Mask.contiguous(B.cat8(m0, B.cat8(m1, B.cat8(m2, m3)))), {==}, e)

def Mask.ipv4(+kind: U32, +addr: U32, +mask: U32, +rest: B.Bytes(), +k2: U32, r: B.Bytes(), e: {Q.Comp.of(k2, Q.Payload.read(Q.SIpv4{}, r)) == Mask.target(kind, addr, mask, rest) : Comp.Rd()}) -> Mask.Goal(mask):
  match r:
    case Nil{}:
      Mask.absurd(kind, addr, mask, rest, B.Short{}, e)
    case x <> Nil{}:
      Mask.absurd(kind, addr, mask, rest, B.Short{}, e)
    case x <> y <> Nil{}:
      Mask.absurd(kind, addr, mask, rest, B.Short{}, e)
    case x <> y <> z <> Nil{}:
      Mask.absurd(kind, addr, mask, rest, B.Short{}, e)
    case +a3 <> +a2 <> +a1 <> +a0 <> +r1:
      Mask.ipv4_mask(kind, addr, mask, rest, k2, B.cat8(a0, B.cat8(a1, B.cat8(a2, a3))), r1, e)

# Any other payload is not an IPv4 one.
def Mask.other(+kind: U32, +addr: U32, +mask: U32, +rest: B.Bytes(), +k2: U32, rp: B.Read(Q.Payload), e: {Q.Comp.of(k2, rp) == Mask.target(kind, addr, mask, rest) : Comp.Rd()}, ni: @p: Q.Payload -> @r: B.Bytes() -> {rp == Done{(p, r)} : B.Read(Q.Payload)} -> Payload.not_ipv4(p)) -> Mask.Goal(mask):
  match rp:
    case Fail{err}:
      Mask.absurd(kind, addr, mask, rest, err, e)
    case Done{(+p, +r)}:
      +eq = Mask.payload_eq(kind, addr, mask, rest, k2, p, r, e)
      Empty.absurd(Mask.Goal(mask), (%eq : Payload.not_ipv4(_); ni(p, r, {==})))

def Payload.one_not(bs: B.Bytes(), p: Q.Payload, r: B.Bytes(), e: {Q.Payload.one(B.u8(bs)) == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.not_ipv4(p):
  match bs:
    case Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case b <> t:
      ep = Equal.cong(B.Read(Q.Payload), Q.Payload, x => P.Read.value(Q.Payload, x, p), Done{(Q.POne{b}, t)}, Done{(p, r)}, e)
      %ep : Payload.not_ipv4(_)
      Unit{}

def Payload.two_not(bs: B.Bytes(), p: Q.Payload, r: B.Bytes(), e: {Q.Payload.two(B.u16(bs)) == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.not_ipv4(p):
  match bs:
    case Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case x <> Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case x <> y <> t:
      ep = Equal.cong(B.Read(Q.Payload), Q.Payload, x2 => P.Read.value(Q.Payload, x2, p), Done{(Q.PTwo{B.cat8(y, x)}, t)}, Done{(p, r)}, e)
      %ep : Payload.not_ipv4(_)
      Unit{}

def Payload.three_not(bs: B.Bytes(), p: Q.Payload, r: B.Bytes(), e: {Q.Payload.three(B.u24(bs)) == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.not_ipv4(p):
  match bs:
    case Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case x <> Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case x <> y <> Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case x <> y <> z <> t:
      ep = Equal.cong(B.Read(Q.Payload), Q.Payload, x2 => P.Read.value(Q.Payload, x2, p), Done{(Q.PThree{B.cat8(z, B.cat8(y, x))}, t)}, Done{(p, r)}, e)
      %ep : Payload.not_ipv4(_)
      Unit{}

def Payload.four_not(bs: B.Bytes(), p: Q.Payload, r: B.Bytes(), e: {Q.Payload.four(B.u32(bs)) == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.not_ipv4(p):
  match bs:
    case Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case x <> Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case x <> y <> Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case x <> y <> z <> Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case x <> y <> z <> w <> t:
      ep = Equal.cong(B.Read(Q.Payload), Q.Payload, x2 => P.Read.value(Q.Payload, x2, p), Done{(Q.PFour{B.cat8(w, B.cat8(z, B.cat8(y, x)))}, t)}, Done{(p, r)}, e)
      %ep : Payload.not_ipv4(_)
      Unit{}

def Payload.six_not(rt: B.Read(B.Bytes()), p: Q.Payload, r: B.Bytes(), e: {Q.Payload.six(rt) == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.not_ipv4(p):
  match rt:
    case Fail{err}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), err, (p, r), e))
    case Done{(bytes, t)}:
      ep = Equal.cong(B.Read(Q.Payload), Q.Payload, x => P.Read.value(Q.Payload, x, p), Done{(Q.PSix{bytes}, t)}, Done{(p, r)}, e)
      %ep : Payload.not_ipv4(_)
      Unit{}

def Payload.ipv6_ok(+addr: B.Bytes(), +prefix: U32, +t: B.Bytes(), p: Q.Payload, r: B.Bytes(), ok: Bool, e: {Q.Ok(B.ReadValue(Q.Payload), (Q.PIpv6{addr, prefix}, t), prefix, ok) == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.not_ipv4(p):
  match ok:
    case False{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Invalid{prefix}, (p, r), e))
    case True{}:
      ep = Equal.cong(B.Read(Q.Payload), Q.Payload, x => P.Read.value(Q.Payload, x, p), Done{(Q.PIpv6{addr, prefix}, t)}, Done{(p, r)}, e)
      %ep : Payload.not_ipv4(_)
      Unit{}

def Payload.ipv6_prefix_not(+addr: B.Bytes(), r1: B.Bytes(), p: Q.Payload, r: B.Bytes(), e: {Q.Payload.ipv6_prefix(addr, B.u8(r1)) == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.not_ipv4(p):
  match r1:
    case Nil{}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), B.Short{}, (p, r), e))
    case +prefix <> +t:
      Payload.ipv6_ok(addr, prefix, t, p, r, U32.is_le(prefix, 128), e)

def Payload.ipv6_not(rt: B.Read(B.Bytes()), p: Q.Payload, r: B.Bytes(), e: {Q.Payload.ipv6(rt) == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.not_ipv4(p):
  match rt:
    case Fail{err}:
      Empty.absurd(Payload.not_ipv4(p), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), err, (p, r), e))
    case Done{(+addr, +r1)}:
      Payload.ipv6_prefix_not(addr, r1, p, r, e)

def Payload.none_not(bs: B.Bytes(), p: Q.Payload, r: B.Bytes(), e: {Done{(Q.PNone{}, bs)} == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.not_ipv4(p):
  ep = Equal.cong(B.Read(Q.Payload), Q.Payload, x => P.Read.value(Q.Payload, x, p), Done{(Q.PNone{}, bs)}, Done{(p, r)}, e)
  %ep : Payload.not_ipv4(_)
  Unit{}

def Mask.shape(+kind: U32, +addr: U32, +mask: U32, +rest: B.Bytes(), +k2: U32, +r: B.Bytes(), shape: Q.Shape, e: {Q.Comp.of(k2, Q.Payload.read(shape, r)) == Mask.target(kind, addr, mask, rest) : Comp.Rd()}) -> Mask.Goal(mask):
  match shape:
    case Q.SNone{}:
      Mask.other(kind, addr, mask, rest, k2, Q.Payload.read(Q.SNone{}, r), e, p => r2 => e2 => Payload.none_not(r, p, r2, e2))
    case Q.SIpv4{}:
      Mask.ipv4(kind, addr, mask, rest, k2, r, e)
    case Q.SIpv6{}:
      Mask.other(kind, addr, mask, rest, k2, Q.Payload.read(Q.SIpv6{}, r), e, p => r2 => e2 => Payload.ipv6_not(B.take(16n, r), p, r2, e2))
    case Q.SOne{}:
      Mask.other(kind, addr, mask, rest, k2, Q.Payload.read(Q.SOne{}, r), e, p => r2 => e2 => Payload.one_not(r, p, r2, e2))
    case Q.STwo{}:
      Mask.other(kind, addr, mask, rest, k2, Q.Payload.read(Q.STwo{}, r), e, p => r2 => e2 => Payload.two_not(r, p, r2, e2))
    case Q.SThree{}:
      Mask.other(kind, addr, mask, rest, k2, Q.Payload.read(Q.SThree{}, r), e, p => r2 => e2 => Payload.three_not(r, p, r2, e2))
    case Q.SFour{}:
      Mask.other(kind, addr, mask, rest, k2, Q.Payload.read(Q.SFour{}, r), e, p => r2 => e2 => Payload.four_not(r, p, r2, e2))
    case Q.SSix{}:
      Mask.other(kind, addr, mask, rest, k2, Q.Payload.read(Q.SSix{}, r), e, p => r2 => e2 => Payload.six_not(B.take(6n, r), p, r2, e2))

def Mask.kind(+kind: U32, +addr: U32, +mask: U32, +rest: B.Bytes(), +k2: U32, +r: B.Bytes(), ms: Maybe<&2, Q.Shape>, e: {Q.Comp.kind(k2, r, ms) == Mask.target(kind, addr, mask, rest) : Comp.Rd()}) -> Mask.Goal(mask):
  match ms:
    case None{}:
      Mask.absurd(kind, addr, mask, rest, B.Unsupported{k2}, e)
    case Some{shape}:
      Mask.shape(kind, addr, mask, rest, k2, r, shape, e)

def L.nas.packet_filter.mask_contiguous(bs, kind, addr, mask, rest, e):
  match bs:
    case Nil{}:
      Mask.absurd(kind, addr, mask, rest, B.Short{}, e)
    case +k2 <> +r:
      Mask.kind(kind, addr, mask, rest, k2, r, Q.Comp.shape(k2), e)

# Session-AMBR: six bytes, defined units
# --------------------------------------

def Ambr.Goal(bs: B.Bytes(), a: Q.Ambr) -> Type:
  {List.length(&2, U32, bs) == 6n : Nat} & {Q.Ambr.valid(a) == True{} : Bool}

def Ambr.absurd(+bs: B.Bytes(), +a: Q.Ambr, err: B.Err, e: {Fail{err} == Done{a} : Result<&2, &2, B.Err, Q.Ambr>}) -> Ambr.Goal(bs, a):
  Empty.absurd(Ambr.Goal(bs, a), P.Refute.fail_done(B.Err, Q.Ambr, err, a, e))

def Ambr.six(+du: U32, +d1: U32, +d0: U32, +uu: U32, +u1: U32, +u0: U32, +a: Q.Ambr, ok: Bool, ev: {Bool.and(Q.Ambr.unit_ok(du), Q.Ambr.unit_ok(uu)) == ok : Bool}, e: {Q.Ok(Q.Ambr, Q.Ambr{du, B.cat8(d0, d1), uu, B.cat8(u0, u1)}, du, ok) == Done{a} : Result<&2, &2, B.Err, Q.Ambr>}) -> Ambr.Goal([du, d1, d0, uu, u1, u0], a):
  match ok:
    case False{}:
      Ambr.absurd([du, d1, d0, uu, u1, u0], a, B.Invalid{du}, e)
    case True{}:
      ea = Equal.cong(Result<&2, &2, B.Err, Q.Ambr>, Q.Ambr, x => P.Res.value(B.Err, Q.Ambr, x, a), Done{Q.Ambr{du, B.cat8(d0, d1), uu, B.cat8(u0, u1)}}, Done{a}, e)
      %ea : Ambr.Goal([du, d1, d0, uu, u1, u0], _)
      ({==}, ev)

def L.nas.session_ambr.decode_valid(bs, a, e):
  match bs:
    case Nil{}:
      Ambr.absurd([], a, B.Invalid{0}, e)
    case x0 <> Nil{}:
      Ambr.absurd([x0], a, B.Invalid{0}, e)
    case x0 <> x1 <> Nil{}:
      Ambr.absurd([x0, x1], a, B.Invalid{0}, e)
    case x0 <> x1 <> x2 <> Nil{}:
      Ambr.absurd([x0, x1, x2], a, B.Invalid{0}, e)
    case x0 <> x1 <> x2 <> x3 <> Nil{}:
      Ambr.absurd([x0, x1, x2, x3], a, B.Invalid{0}, e)
    case x0 <> x1 <> x2 <> x3 <> x4 <> Nil{}:
      Ambr.absurd([x0, x1, x2, x3, x4], a, B.Invalid{0}, e)
    case +du <> +d1 <> +d0 <> +uu <> +u1 <> +u0 <> Nil{}:
      Ambr.six(du, d1, d0, uu, u1, u0, a, Bool.and(Q.Ambr.unit_ok(du), Q.Ambr.unit_ok(uu)), {==}, e)
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> t:
      Ambr.absurd(x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> t, a, B.Invalid{0}, e)
