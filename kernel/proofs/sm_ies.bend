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

def Mask.ipv4_ok(+kind: U32, +addr: U32, +mask: U32, +rest: B.Bytes(), +k2: U32, +a2: U32, +m2: U32, +r2: B.Bytes(), ok: Bool, ev: {Q.Mask.contiguous(m2) == ok : Bool}, e: {Q.Comp.of(k2, B.guard(B.ReadValue(Q.Payload), (Q.PIpv4{a2, m2}, r2), m2, ok)) == Mask.target(kind, addr, mask, rest) : Comp.Rd()}) -> Mask.Goal(mask):
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

def Payload.ipv6_ok(+addr: B.Bytes(), +prefix: U32, +t: B.Bytes(), p: Q.Payload, r: B.Bytes(), ok: Bool, e: {B.guard(B.ReadValue(Q.Payload), (Q.PIpv6{addr, prefix}, t), prefix, ok) == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.not_ipv4(p):
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

def Ambr.six(+du: U32, +d1: U32, +d0: U32, +uu: U32, +u1: U32, +u0: U32, +a: Q.Ambr, ok: Bool, ev: {Bool.and(Q.Ambr.unit_ok(du), Q.Ambr.unit_ok(uu)) == ok : Bool}, e: {B.guard(Q.Ambr, Q.Ambr{du, B.cat8(d0, d1), uu, B.cat8(u0, u1)}, du, ok) == Done{a} : Result<&2, &2, B.Err, Q.Ambr>}) -> Ambr.Goal([du, d1, d0, uu, u1, u0], a):
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

# Extended protocol configuration options
# ---------------------------------------

def Cont.Res() -> Data:
  Result<&2, &2, B.Err, List<&2, Q.Container>>

def Epco.Res() -> Data:
  Result<&2, &2, B.Err, Q.Epco>

# An LV field spans one byte more than its content and what follows.
def Lv.len_fin(+l: U32, +tail: B.Bytes(), +body2: B.Bytes(), +r2: B.Bytes(), la: {List.length(&2, U32, body2) == U32.to_nat(l) : Nat} & {List.append(&2, U32, body2, r2) == tail : B.Bytes()}) -> {List.length(&2, U32, l <> tail) == 1n+Nat.add(List.length(&2, U32, body2), List.length(&2, U32, r2)) : Nat}:
  (ln, ap) = la
  %ap : {List.length(&2, U32, l <> _) == 1n+Nat.add(List.length(&2, U32, body2), List.length(&2, U32, r2)) : Nat}
  al = P.List.append_len(body2, r2)
  %al : {List.length(&2, U32, l <> List.append(&2, U32, body2, r2)) == 1n+_ : Nat}
  {==}

def Lv.len_join(+l: U32, +tail: B.Bytes(), +len: U32, +body: B.Bytes(), +r3: B.Bytes(), rt: B.Read(B.Bytes()), ert: {B.take(U32.to_nat(l), tail) == rt : B.Read(B.Bytes())}, +e: {I.Len.join(l, rt) == Done{(I.LenBody{len, body}, r3)} : B.Read(I.LenBody)}) -> {List.length(&2, U32, l <> tail) == 1n+Nat.add(List.length(&2, U32, body), List.length(&2, U32, r3)) : Nat}:
  match rt:
    case Fail{err}:
      Empty.absurd({List.length(&2, U32, l <> tail) == 1n+Nat.add(List.length(&2, U32, body), List.length(&2, U32, r3)) : Nat}, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), err, (I.LenBody{len, body}, r3), e))
    case Done{(+body2, +r2)}:
      +elb = Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, I.LenBody{len, body}), Done{(I.LenBody{l, body2}, r2)}, Done{(I.LenBody{len, body}, r3)}, e)
      eb = Equal.cong(I.LenBody, B.Bytes(), x => P.Lb.body(x), I.LenBody{l, body2}, I.LenBody{len, body}, elb)
      er = Equal.cong(B.Read(I.LenBody), B.Bytes(), x => P.Read.rest(I.LenBody, x, r3), Done{(I.LenBody{l, body2}, r2)}, Done{(I.LenBody{len, body}, r3)}, e)
      %eb : {List.length(&2, U32, l <> tail) == 1n+Nat.add(List.length(&2, U32, _), List.length(&2, U32, r3)) : Nat}
      %er : {List.length(&2, U32, l <> tail) == 1n+Nat.add(List.length(&2, U32, body2), List.length(&2, U32, _)) : Nat}
      Lv.len_fin(l, tail, body2, r2, L.bytes.take.length(U32.to_nat(l), tail, body2, r2, ert))

def Lv.len_ok(+l: U32, +tail: B.Bytes(), +len: U32, +body: B.Bytes(), +r3: B.Bytes(), ok: Bool, +e: {I.Len.take(l, tail, ok) == Done{(I.LenBody{len, body}, r3)} : B.Read(I.LenBody)}) -> {List.length(&2, U32, l <> tail) == 1n+Nat.add(List.length(&2, U32, body), List.length(&2, U32, r3)) : Nat}:
  match ok:
    case False{}:
      Empty.absurd({List.length(&2, U32, l <> tail) == 1n+Nat.add(List.length(&2, U32, body), List.length(&2, U32, r3)) : Nat}, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Invalid{l}, (I.LenBody{len, body}, r3), e))
    case True{}:
      Lv.len_join(l, tail, len, body, r3, B.take(U32.to_nat(l), tail), {==}, e)

def Lv.len(r2: B.Bytes(), +len: U32, +body: B.Bytes(), +r3: B.Bytes(), +e: {I.lv(r2) == Done{(I.LenBody{len, body}, r3)} : B.Read(I.LenBody)}) -> {List.length(&2, U32, r2) == 1n+Nat.add(List.length(&2, U32, body), List.length(&2, U32, r3)) : Nat}:
  match r2:
    case Nil{}:
      Empty.absurd({List.length(&2, U32, []) == 1n+Nat.add(List.length(&2, U32, body), List.length(&2, U32, r3)) : Nat}, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Short{}, (I.LenBody{len, body}, r3), e))
    case +l <> +tail:
      Lv.len_ok(l, tail, len, body, r3, B.fits8(l), e)

# What the container loop establishes: a count within the budget, valid
# containers, and a size equal to the bytes read.
def Cont.Inv(budget: Nat, bs: B.Bytes(), cs: List<&2, Q.Container>) -> Type:
  {Nat.is_le(List.length(&2, Q.Container, cs), budget) == True{} : Bool} & ({Q.Containers.valid(cs) == True{} : Bool} & {Q.Containers.size(cs) == List.length(&2, U32, bs) : Nat})

def Cont.absurd(+budget: Nat, +bs: B.Bytes(), +cs: List<&2, Q.Container>, err: B.Err, e: {Fail{err} == Done{cs} : Cont.Res()}) -> Cont.Inv(budget, bs, cs):
  Empty.absurd(Cont.Inv(budget, bs, cs), P.Refute.fail_done(B.Err, List<&2, Q.Container>, err, cs, e))

def Cont.dv_step(+k: Nat, +b: U32, +b0: U32, +r2: B.Bytes(), +id: U32, +len: U32, +body: B.Bytes(), +r3: B.Bytes(), +cs2: List<&2, Q.Container>, f16: {B.fits16(id) == True{} : Bool}, v8: {I.LenBody.valid8(I.LenBody{len, body}) == True{} : Bool}, ll: {List.length(&2, U32, r2) == 1n+Nat.add(List.length(&2, U32, body), List.length(&2, U32, r3)) : Nat}, ih: Cont.Inv(k, r3, cs2)) -> Cont.Inv(1n+k, b <> b0 <> r2, Q.Container{id, I.LenBody{len, body}} <> cs2):
  (le, rest) = ih
  (va, sz) = rest
  ssz = Equal.sym(Nat, Q.Containers.size(cs2), List.length(&2, U32, r3), sz)
  %ssz : {Nat.is_le(1n+List.length(&2, Q.Container, cs2), 1n+k) == True{} : Bool} & ({Bool.and(Bool.and(B.fits16(id), I.LenBody.valid8(I.LenBody{len, body})), Q.Containers.valid(cs2)) == True{} : Bool} & {Nat.add(3n, Nat.add(List.length(&2, U32, body), _)) == List.length(&2, U32, b <> b0 <> r2) : Nat})
  sll = Equal.sym(Nat, List.length(&2, U32, r2), 1n+Nat.add(List.length(&2, U32, body), List.length(&2, U32, r3)), ll)
  %sll : {Nat.is_le(1n+List.length(&2, Q.Container, cs2), 1n+k) == True{} : Bool} & ({Bool.and(Bool.and(B.fits16(id), I.LenBody.valid8(I.LenBody{len, body})), Q.Containers.valid(cs2)) == True{} : Bool} & {Nat.add(3n, Nat.add(List.length(&2, U32, body), List.length(&2, U32, r3))) == 1n+1n+_ : Nat})
  (le, (P.Bool.and_intro(Bool.and(B.fits16(id), I.LenBody.valid8(I.LenBody{len, body})), Q.Containers.valid(cs2), P.Bool.and_intro(B.fits16(id), I.LenBody.valid8(I.LenBody{len, body}), f16, v8), va), {==}))

def Cont.dv_more(+f: Nat, +k: Nat, +b: U32, +b0: U32, +r2: B.Bytes(), +id: U32, +len: U32, +body: B.Bytes(), +r3: B.Bytes(), +cs: List<&2, Q.Container>, ro: Cont.Res(), ero: {Q.Containers.go(f, k, r3) == ro : Cont.Res()}, +e: {B.Res.cons(Q.Container, Q.Container{id, I.LenBody{len, body}}, ro) == Done{cs} : Cont.Res()}, f16: {B.fits16(id) == True{} : Bool}, v8: {I.LenBody.valid8(I.LenBody{len, body}) == True{} : Bool}, ll: {List.length(&2, U32, r2) == 1n+Nat.add(List.length(&2, U32, body), List.length(&2, U32, r3)) : Nat}, ih: @cs2: List<&2, Q.Container> -> {Q.Containers.go(f, k, r3) == Done{cs2} : Cont.Res()} -> Cont.Inv(k, r3, cs2)) -> Cont.Inv(1n+k, b <> b0 <> r2, cs):
  match ro:
    case Fail{err}:
      Cont.absurd(1n+k, b <> b0 <> r2, cs, err, e)
    case Done{+cs2}:
      ec = Equal.cong(Cont.Res(), List<&2, Q.Container>, x => P.Res.value(B.Err, List<&2, Q.Container>, x, cs), Done{Q.Container{id, I.LenBody{len, body}} <> cs2}, Done{cs}, e)
      %ec : Cont.Inv(1n+k, b <> b0 <> r2, _)
      Cont.dv_step(k, b, b0, r2, id, len, body, r3, cs2, f16, v8, ll, ih(cs2, ero))

def Cont.dv_body(+f: Nat, +k: Nat, +b: U32, +b0: U32, +r2: B.Bytes(), +id: U32, +cs: List<&2, Q.Container>, rl: B.Read(I.LenBody), +erl: {I.lv(r2) == rl : B.Read(I.LenBody)}, +e: {Q.Container.body(id, rl, left => Q.Containers.go(f, k, left)) == Done{cs} : Cont.Res()}, f16: {B.fits16(id) == True{} : Bool}, ih: @cs2: List<&2, Q.Container> -> @r3: B.Bytes() -> {Q.Containers.go(f, k, r3) == Done{cs2} : Cont.Res()} -> Cont.Inv(k, r3, cs2)) -> Cont.Inv(1n+k, b <> b0 <> r2, cs):
  match rl:
    case Fail{err}:
      Cont.absurd(1n+k, b <> b0 <> r2, cs, err, e)
    case Done{(I.LenBody{+len, +body}, +r3)}:
      Cont.dv_more(f, k, b, b0, r2, id, len, body, r3, cs, Q.Containers.go(f, k, r3), {==}, e, f16, PM.Lv.dv(r2, I.LenBody{len, body}, r3, erl), Lv.len(r2, len, body, r3, erl), cs2 => e2 => ih(cs2, r3, e2))

def Cont.dv_ok(+f: Nat, +k: Nat, +b: U32, +b0: U32, +r2: B.Bytes(), +cs: List<&2, Q.Container>, ok: Bool, ev: {B.fits16(B.cat8(b0, b)) == ok : Bool}, +e: {Q.Container.id_ok(B.cat8(b0, b), r2, left => Q.Containers.go(f, k, left), ok) == Done{cs} : Cont.Res()}, ih: @cs2: List<&2, Q.Container> -> @r3: B.Bytes() -> {Q.Containers.go(f, k, r3) == Done{cs2} : Cont.Res()} -> Cont.Inv(k, r3, cs2)) -> Cont.Inv(1n+k, b <> b0 <> r2, cs):
  match ok:
    case False{}:
      Cont.absurd(1n+k, b <> b0 <> r2, cs, B.Invalid{B.cat8(b0, b)}, e)
    case True{}:
      Cont.dv_body(f, k, b, b0, r2, B.cat8(b0, b), cs, I.lv(r2), {==}, e, ev, ih)

def Cont.dv(fuel: Nat, budget: Nat, bs: B.Bytes(), +cs: List<&2, Q.Container>, +e: {Q.Containers.go(fuel, budget, bs) == Done{cs} : Cont.Res()}) -> Cont.Inv(budget, bs, cs):
  match fuel budget bs:
    case 0n 0n Nil{}:
      ec = Equal.cong(Cont.Res(), List<&2, Q.Container>, x => P.Res.value(B.Err, List<&2, Q.Container>, x, cs), Done{[]}, Done{cs}, e)
      %ec : Cont.Inv(0n, [], _)
      ({==}, ({==}, {==}))
    case 0n 1n+k Nil{}:
      ec = Equal.cong(Cont.Res(), List<&2, Q.Container>, x => P.Res.value(B.Err, List<&2, Q.Container>, x, cs), Done{[]}, Done{cs}, e)
      %ec : Cont.Inv(1n+k, [], _)
      ({==}, ({==}, {==}))
    case 1n+f 0n Nil{}:
      ec = Equal.cong(Cont.Res(), List<&2, Q.Container>, x => P.Res.value(B.Err, List<&2, Q.Container>, x, cs), Done{[]}, Done{cs}, e)
      %ec : Cont.Inv(0n, [], _)
      ({==}, ({==}, {==}))
    case 1n+f 1n+k Nil{}:
      ec = Equal.cong(Cont.Res(), List<&2, Q.Container>, x => P.Res.value(B.Err, List<&2, Q.Container>, x, cs), Done{[]}, Done{cs}, e)
      %ec : Cont.Inv(1n+k, [], _)
      ({==}, ({==}, {==}))
    case 0n 0n +b <> +rest:
      Cont.absurd(0n, b <> rest, cs, B.Invalid{b}, e)
    case 0n 1n+k +b <> +rest:
      Cont.absurd(1n+k, b <> rest, cs, B.Invalid{b}, e)
    case 1n+f 0n +b <> +rest:
      Cont.absurd(0n, b <> rest, cs, B.Invalid{b}, e)
    case 1n++f 1n++k +b <> Nil{}:
      Cont.absurd(1n+k, [b], cs, B.Short{}, e)
    case 1n++f 1n++k +b <> +b0 <> +r2:
      Cont.dv_ok(f, k, b, b0, r2, cs, B.fits16(B.cat8(b0, b)), {==}, e, cs2 => r3 => e2 => Cont.dv(f, k, r3, cs2, e2))

def Epco.Goal(bs: B.Bytes(), e: Q.Epco) -> Type:
  {Nat.is_le(List.length(&2, Q.Container, Q.Epco.containers(e)), 255n) == True{} : Bool} & ({Q.Epco.valid(e) == True{} : Bool} & {Q.Epco.size(e) == List.length(&2, U32, bs) : Nat})

def Epco.absurd(+bs: B.Bytes(), +e: Q.Epco, err: B.Err, d: {Fail{err} == Done{e} : Epco.Res()}) -> Epco.Goal(bs, e):
  Empty.absurd(Epco.Goal(bs, e), P.Refute.fail_done(B.Err, Q.Epco, err, e, d))

def Epco.dv_fin2(+h: U32, +rest: B.Bytes(), +cs: List<&2, Q.Container>, +le: {Nat.is_le(List.length(&2, Q.Container, cs), 255n) == True{} : Bool}, va: {Q.Containers.valid(cs) == True{} : Bool}, sz: {Q.Containers.size(cs) == List.length(&2, U32, rest) : Nat}, small: {Nat.is_le(List.length(&2, U32, rest), 65534n) == True{} : Bool}) -> Epco.Goal(h <> rest, Q.Epco{cs}):
  ssz = Equal.sym(Nat, Q.Containers.size(cs), List.length(&2, U32, rest), sz)
  %ssz : {Nat.is_le(List.length(&2, Q.Container, cs), 255n) == True{} : Bool} & ({Bool.and(Nat.is_le(List.length(&2, Q.Container, cs), 255n), Bool.and(Q.Containers.valid(cs), Nat.is_le(_, 65534n))) == True{} : Bool} & {1n+_ == 1n+List.length(&2, U32, rest) : Nat})
  (le, (P.Bool.and_intro(Nat.is_le(List.length(&2, Q.Container, cs), 255n), Bool.and(Q.Containers.valid(cs), Nat.is_le(List.length(&2, U32, rest), 65534n)), le, P.Bool.and_intro(Q.Containers.valid(cs), Nat.is_le(List.length(&2, U32, rest), 65534n), va, small)), {==}))

def Epco.dv_fin(+h: U32, +rest: B.Bytes(), +cs: List<&2, Q.Container>, inv: Cont.Inv(255n, rest, cs), small: {Nat.is_le(List.length(&2, U32, rest), 65534n) == True{} : Bool}) -> Epco.Goal(h <> rest, Q.Epco{cs}):
  (le, more) = inv
  (va, sz) = more
  Epco.dv_fin2(h, rest, cs, le, va, sz, small)

def Epco.dv_of(+h: U32, +rest: B.Bytes(), +e: Q.Epco, rc: Cont.Res(), erc: {Q.Containers.go(List.length(&2, U32, rest), 255n, rest) == rc : Cont.Res()}, +d: {Q.Epco.of(rc) == Done{e} : Epco.Res()}, small: {Nat.is_le(List.length(&2, U32, rest), 65534n) == True{} : Bool}) -> Epco.Goal(h <> rest, e):
  match rc:
    case Fail{err}:
      Epco.absurd(h <> rest, e, err, d)
    case Done{+cs}:
      ee = Equal.cong(Epco.Res(), Q.Epco, x => P.Res.value(B.Err, Q.Epco, x, e), Done{Q.Epco{cs}}, Done{e}, d)
      %ee : Epco.Goal(h <> rest, _)
      Epco.dv_fin(h, rest, cs, Cont.dv(List.length(&2, U32, rest), 255n, rest, cs, erc), small)

def Epco.dv_hdr(+h: U32, +rest: B.Bytes(), +e: Q.Epco, ok: Bool, +ev: {Bool.and(U32.is_eq(h, Q.Epco.header()), Nat.is_le(List.length(&2, U32, rest), 65534n)) == ok : Bool}, +d: {Q.Epco.hdr(h, rest, ok) == Done{e} : Epco.Res()}) -> Epco.Goal(h <> rest, e):
  match ok:
    case False{}:
      Epco.absurd(h <> rest, e, B.Invalid{h}, d)
    case True{}:
      Epco.dv_of(h, rest, e, Q.Containers.go(List.length(&2, U32, rest), 255n, rest), {==}, d, P.Bool.and_true_r(U32.is_eq(h, Q.Epco.header()), Nat.is_le(List.length(&2, U32, rest), 65534n), ev))

def L.nas.epco.decode_bounded(bs, e, d):
  match bs:
    case Nil{}:
      Epco.absurd([], e, B.Short{}, d)
    case +h <> +rest:
      Epco.dv_hdr(h, rest, e, Bool.and(U32.is_eq(h, Q.Epco.header()), Nat.is_le(List.length(&2, U32, rest), 65534n)), {==}, d)

# A valid ePCO encodes within its length field and reads back.
def Cont.write_len(cs: List<&2, Q.Container>) -> {List.length(&2, U32, Q.Containers.write(cs)) == Q.Containers.size(cs) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case Q.Container{id, I.LenBody{len, +body}} <> +more:
      al = Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, body, Q.Containers.write(more))), Nat.add(List.length(&2, U32, body), List.length(&2, U32, Q.Containers.write(more))), P.List.append_len(body, Q.Containers.write(more)))
      %al : {1n+1n+1n+_ == Nat.add(3n, Nat.add(List.length(&2, U32, body), Q.Containers.size(more))) : Nat}
      ih = Equal.sym(Nat, List.length(&2, U32, Q.Containers.write(more)), Q.Containers.size(more), Cont.write_len(more))
      %ih : {1n+1n+1n+Nat.add(List.length(&2, U32, body), _) == Nat.add(3n, Nat.add(List.length(&2, U32, body), Q.Containers.size(more))) : Nat}
      {==}

def Lv.rt(+len: U32, +body: B.Bytes(), +W: B.Bytes(), +v8: {I.LenBody.valid8(I.LenBody{len, body}) == True{} : Bool}) -> {I.lv(I.write_lv(I.LenBody{len, body}, W)) == Done{(I.LenBody{len, body}, W)} : B.Read(I.LenBody)}:
  +fl = P.Bool.and_true_l(B.fits8(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v8)
  tn = P.Nat.eq_of_is_eq(U32.to_nat(len), List.length(&2, U32, body), P.Bool.and_true_r(B.fits8(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v8))
  ml = Equal.sym(U32, U32.and(255, len), len, P.U32.eq_of_is_eq(U32.and(255, len), len, fl))
  %ml : {I.Len.take(_, List.append(&2, U32, body, W), B.fits8(_)) == Done{(I.LenBody{len, body}, W)} : B.Read(I.LenBody)}
  PM.Len.rt(len, body, W, B.fits8(len), fl, tn)

def Cont.rt(cs: List<&2, Q.Container>, fuel: Nat, budget: Nat, +v: {Q.Containers.valid(cs) == True{} : Bool}, +bound: {Nat.is_le(List.length(&2, U32, Q.Containers.write(cs)), fuel) == True{} : Bool}, +cnt: {Nat.is_le(List.length(&2, Q.Container, cs), budget) == True{} : Bool}) -> {Q.Containers.go(fuel, budget, Q.Containers.write(cs)) == Done{cs} : Cont.Res()}:
  match cs fuel budget:
    case Nil{} 0n 0n:
      {==}
    case Nil{} 0n 1n+k:
      {==}
    case Nil{} 1n+f 0n:
      {==}
    case Nil{} 1n+f 1n+k:
      {==}
    case Q.Container{id, I.LenBody{len, body}} <> more 0n 0n:
      Empty.absurd({Q.Containers.go(0n, 0n, Q.Containers.write(Q.Container{id, I.LenBody{len, body}} <> more)) == Done{Q.Container{id, I.LenBody{len, body}} <> more} : Cont.Res()}, P.Refute.bool(bound))
    case Q.Container{id, I.LenBody{len, body}} <> more 0n 1n+k:
      Empty.absurd({Q.Containers.go(0n, 1n+k, Q.Containers.write(Q.Container{id, I.LenBody{len, body}} <> more)) == Done{Q.Container{id, I.LenBody{len, body}} <> more} : Cont.Res()}, P.Refute.bool(bound))
    case Q.Container{id, I.LenBody{len, body}} <> more 1n+f 0n:
      Empty.absurd({Q.Containers.go(1n+f, 0n, Q.Containers.write(Q.Container{id, I.LenBody{len, body}} <> more)) == Done{Q.Container{id, I.LenBody{len, body}} <> more} : Cont.Res()}, P.Refute.bool(cnt))
    case Q.Container{+id, I.LenBody{+len, +body}} <> +more 1n++f 1n++k:
      +W = Q.Containers.write(more)
      +cv = P.Bool.and_true_l(Bool.and(B.fits16(id), I.LenBody.valid8(I.LenBody{len, body})), Q.Containers.valid(more), v)
      +f16 = P.Bool.and_true_l(B.fits16(id), I.LenBody.valid8(I.LenBody{len, body}), cv)
      ru = Equal.sym(B.Read(U32), B.u16(B.write_u16(id, I.write_lv(I.LenBody{len, body}, W))), Done{(id, I.write_lv(I.LenBody{len, body}, W))}, L.bytes.u16.roundtrip(id, I.write_lv(I.LenBody{len, body}, W), P.U32.eq_of_is_eq(U32.and(65535, id), id, f16)))
      %ru : {Q.Container.id(_, left => Q.Containers.go(f, k, left)) == Done{Q.Container{id, I.LenBody{len, body}} <> more} : Cont.Res()}
      sf = Equal.sym(Bool, B.fits16(id), True{}, f16)
      %sf : {Q.Container.id_ok(id, I.write_lv(I.LenBody{len, body}, W), left => Q.Containers.go(f, k, left), _) == Done{Q.Container{id, I.LenBody{len, body}} <> more} : Cont.Res()}
      lr = Equal.sym(B.Read(I.LenBody), I.lv(I.write_lv(I.LenBody{len, body}, W)), Done{(I.LenBody{len, body}, W)}, Lv.rt(len, body, W, P.Bool.and_true_r(B.fits16(id), I.LenBody.valid8(I.LenBody{len, body}), cv)))
      %lr : {Q.Container.body(id, _, left => Q.Containers.go(f, k, left)) == Done{Q.Container{id, I.LenBody{len, body}} <> more} : Cont.Res()}
      ih = Equal.sym(Cont.Res(), Q.Containers.go(f, k, W), Done{more}, Cont.rt(more, f, k, P.Bool.and_true_r(Bool.and(B.fits16(id), I.LenBody.valid8(I.LenBody{len, body})), Q.Containers.valid(more), v), P.Nat.le_of_append(body, W, 2n, f, bound), cnt))
      %ih : {B.Res.cons(Q.Container, Q.Container{id, I.LenBody{len, body}}, _) == Done{Q.Container{id, I.LenBody{len, body}} <> more} : Cont.Res()}
      {==}

def Epco.rt(+cs: List<&2, Q.Container>, +v: {Q.Epco.valid(Q.Epco{cs}) == True{} : Bool}) -> {Nat.is_le(List.length(&2, U32, Q.Epco.write(Q.Epco{cs})), 65535n) == True{} : Bool} & {Q.Epco.read(Q.Epco.write(Q.Epco{cs})) == Done{Q.Epco{cs}} : Epco.Res()}:
  +W = Q.Containers.write(cs)
  +v1 = P.Bool.and_true_l(Nat.is_le(List.length(&2, Q.Container, cs), 255n), Bool.and(Q.Containers.valid(cs), Nat.is_le(Q.Containers.size(cs), 65534n)), v)
  +r1 = P.Bool.and_true_r(Nat.is_le(List.length(&2, Q.Container, cs), 255n), Bool.and(Q.Containers.valid(cs), Nat.is_le(Q.Containers.size(cs), 65534n)), v)
  +v2 = P.Bool.and_true_l(Q.Containers.valid(cs), Nat.is_le(Q.Containers.size(cs), 65534n), r1)
  +v3 = P.Bool.and_true_r(Q.Containers.valid(cs), Nat.is_le(Q.Containers.size(cs), 65534n), r1)
  swl = Equal.sym(Nat, List.length(&2, U32, W), Q.Containers.size(cs), Cont.write_len(cs))
  %swl : {Nat.is_le(1n+_, 65535n) == True{} : Bool} & {Q.Epco.hdr(128, W, Bool.and(U32.is_eq(128, 128), Nat.is_le(_, 65534n))) == Done{Q.Epco{cs}} : Epco.Res()}
  sv3 = Equal.sym(Bool, Nat.is_le(Q.Containers.size(cs), 65534n), True{}, v3)
  %sv3 : {Nat.is_le(1n+Q.Containers.size(cs), 65535n) == True{} : Bool} & {Q.Epco.hdr(128, W, _) == Done{Q.Epco{cs}} : Epco.Res()}
  rt = Equal.sym(Cont.Res(), Q.Containers.go(List.length(&2, U32, W), 255n, W), Done{cs}, Cont.rt(cs, List.length(&2, U32, W), 255n, v2, P.Nat.le_refl(List.length(&2, U32, W)), v1))
  %rt : {Nat.is_le(1n+Q.Containers.size(cs), 65535n) == True{} : Bool} & {Q.Epco.of(_) == Done{Q.Epco{cs}} : Epco.Res()}
  (v3, {==})

def L.nas.epco.encode_bounded(e, v):
  match e:
    case Q.Epco{+cs}:
      Epco.rt(cs, v)

# QoS rules write back to their bytes
# -----------------------------------

def Payload.Sx(p: Q.Payload, r: B.Bytes(), bs: B.Bytes()) -> Type:
  {Q.Payload.write(p, r) == bs : B.Bytes()} & {B.all_bytes(r) == True{} : Bool}

def Payload.absurd(+p: Q.Payload, +r: B.Bytes(), +bs: B.Bytes(), err: B.Err, e: {Fail{err} == Done{(p, r)} : B.Read(Q.Payload)}) -> Payload.Sx(p, r, bs):
  Empty.absurd(Payload.Sx(p, r, bs), P.Refute.fail_done(B.Err, B.ReadValue(Q.Payload), err, (p, r), e))

# The payload read is `p0` and the rest is `r0`.
def Payload.eqs(-G: Type, +p: Q.Payload, +r: B.Bytes(), +p0: Q.Payload, +r0: B.Bytes(), +e: {Done{(p0, r0)} == Done{(p, r)} : B.Read(Q.Payload)}, k: {p0 == p : Q.Payload} -> {r0 == r : B.Bytes()} -> G) -> G:
  k(Equal.cong(B.Read(Q.Payload), Q.Payload, x => P.Read.value(Q.Payload, x, p), Done{(p0, r0)}, Done{(p, r)}, e), Equal.cong(B.Read(Q.Payload), B.Bytes(), x => P.Read.rest(Q.Payload, x, r), Done{(p0, r0)}, Done{(p, r)}, e))

def Bytes.all_prefix(xs: B.Bytes(), +ys: B.Bytes(), +e: {B.all_bytes(List.append(&2, U32, xs, ys)) == True{} : Bool}) -> {B.all_bytes(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xt:
      P.Bool.and_intro(B.is_byte(x), B.all_bytes(xt), P.Bool.and_true_l(B.is_byte(x), B.all_bytes(List.append(&2, U32, xt, ys)), e), Bytes.all_prefix(xt, ys, P.Bool.and_true_r(B.is_byte(x), B.all_bytes(List.append(&2, U32, xt, ys)), e)))

def Payload.sx_none(+bs: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), ep: {Q.PNone{} == p : Q.Payload}, er: {bs == r : B.Bytes()}, ab: {B.all_bytes(bs) == True{} : Bool}) -> Payload.Sx(p, r, bs):
  %ep : Payload.Sx(_, r, bs)
  %er : Payload.Sx(Q.PNone{}, _, bs)
  ({==}, ab)

def Payload.sx_one(+v: U32, +r1: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), ep: {Q.POne{v} == p : Q.Payload}, er: {r1 == r : B.Bytes()}, +ab: {B.all_bytes(v <> r1) == True{} : Bool}) -> Payload.Sx(p, r, v <> r1):
  %ep : Payload.Sx(_, r, v <> r1)
  %er : Payload.Sx(Q.POne{v}, _, v <> r1)
  mv = Equal.sym(U32, U32.and(255, v), v, P.U32.lt256_mask8(v, P.Bool.and_true_l(B.is_byte(v), B.all_bytes(r1), ab)))
  %mv : {_ <> r1 == v <> r1 : B.Bytes()} & {B.all_bytes(r1) == True{} : Bool}
  ({==}, P.Bool.and_true_r(B.is_byte(v), B.all_bytes(r1), ab))

def Payload.sx_two(+x: U32, +y: U32, +r1: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), ep: {Q.PTwo{B.cat8(y, x)} == p : Q.Payload}, er: {r1 == r : B.Bytes()}, +ab: {B.all_bytes(x <> y <> r1) == True{} : Bool}) -> Payload.Sx(p, r, x <> y <> r1):
  %ep : Payload.Sx(_, r, x <> y <> r1)
  %er : Payload.Sx(Q.PTwo{B.cat8(y, x)}, _, x <> y <> r1)
  +ab1 = P.Bool.and_true_r(B.is_byte(x), B.all_bytes(y <> r1), ab)
  s16 = Equal.sym(B.Bytes(), B.write_u16(B.cat8(y, x), r1), x <> y <> r1, P.Bytes.u16_sx(x, y, P.U32.lt256_mask8(x, P.Bool.and_true_l(B.is_byte(x), B.all_bytes(y <> r1), ab)), P.U32.lt256_mask8(y, P.Bool.and_true_l(B.is_byte(y), B.all_bytes(r1), ab1)), r1))
  %s16 : {_ == x <> y <> r1 : B.Bytes()} & {B.all_bytes(r1) == True{} : Bool}
  ({==}, P.Bool.and_true_r(B.is_byte(y), B.all_bytes(r1), ab1))

def Payload.sx_three(+x: U32, +y: U32, +z: U32, +r1: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), ep: {Q.PThree{B.cat8(z, B.cat8(y, x))} == p : Q.Payload}, er: {r1 == r : B.Bytes()}, +ab: {B.all_bytes(x <> y <> z <> r1) == True{} : Bool}) -> Payload.Sx(p, r, x <> y <> z <> r1):
  %ep : Payload.Sx(_, r, x <> y <> z <> r1)
  %er : Payload.Sx(Q.PThree{B.cat8(z, B.cat8(y, x))}, _, x <> y <> z <> r1)
  +ab1 = P.Bool.and_true_r(B.is_byte(x), B.all_bytes(y <> z <> r1), ab)
  +ab2 = P.Bool.and_true_r(B.is_byte(y), B.all_bytes(z <> r1), ab1)
  s24 = Equal.sym(B.Bytes(), B.write_u24(B.cat8(z, B.cat8(y, x)), r1), x <> y <> z <> r1, P.Bytes.u24_sx(x, y, z, P.U32.lt256_mask8(x, P.Bool.and_true_l(B.is_byte(x), B.all_bytes(y <> z <> r1), ab)), P.U32.lt256_mask8(y, P.Bool.and_true_l(B.is_byte(y), B.all_bytes(z <> r1), ab1)), P.U32.lt256_mask8(z, P.Bool.and_true_l(B.is_byte(z), B.all_bytes(r1), ab2)), r1))
  %s24 : {_ == x <> y <> z <> r1 : B.Bytes()} & {B.all_bytes(r1) == True{} : Bool}
  ({==}, P.Bool.and_true_r(B.is_byte(z), B.all_bytes(r1), ab2))

def Bytes4.masks(-G: Type, +a3: U32, +a2: U32, +a1: U32, +a0: U32, +r1: B.Bytes(), +ab: {B.all_bytes(a3 <> a2 <> a1 <> a0 <> r1) == True{} : Bool}, k: {U32.and(255, a3) == a3 : U32} -> {U32.and(255, a2) == a2 : U32} -> {U32.and(255, a1) == a1 : U32} -> {U32.and(255, a0) == a0 : U32} -> {B.all_bytes(r1) == True{} : Bool} -> G) -> G:
  +ab1 = P.Bool.and_true_r(B.is_byte(a3), B.all_bytes(a2 <> a1 <> a0 <> r1), ab)
  +ab2 = P.Bool.and_true_r(B.is_byte(a2), B.all_bytes(a1 <> a0 <> r1), ab1)
  +ab3 = P.Bool.and_true_r(B.is_byte(a1), B.all_bytes(a0 <> r1), ab2)
  k(P.U32.lt256_mask8(a3, P.Bool.and_true_l(B.is_byte(a3), B.all_bytes(a2 <> a1 <> a0 <> r1), ab)), P.U32.lt256_mask8(a2, P.Bool.and_true_l(B.is_byte(a2), B.all_bytes(a1 <> a0 <> r1), ab1)), P.U32.lt256_mask8(a1, P.Bool.and_true_l(B.is_byte(a1), B.all_bytes(a0 <> r1), ab2)), P.U32.lt256_mask8(a0, P.Bool.and_true_l(B.is_byte(a0), B.all_bytes(r1), ab3)), P.Bool.and_true_r(B.is_byte(a0), B.all_bytes(r1), ab3))

def Payload.sx_four(+a3: U32, +a2: U32, +a1: U32, +a0: U32, +r1: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), ep: {Q.PFour{B.cat8(a0, B.cat8(a1, B.cat8(a2, a3)))} == p : Q.Payload}, er: {r1 == r : B.Bytes()}, m3: {U32.and(255, a3) == a3 : U32}, m2: {U32.and(255, a2) == a2 : U32}, m1: {U32.and(255, a1) == a1 : U32}, m0: {U32.and(255, a0) == a0 : U32}, ab1: {B.all_bytes(r1) == True{} : Bool}) -> Payload.Sx(p, r, a3 <> a2 <> a1 <> a0 <> r1):
  %ep : Payload.Sx(_, r, a3 <> a2 <> a1 <> a0 <> r1)
  %er : Payload.Sx(Q.PFour{B.cat8(a0, B.cat8(a1, B.cat8(a2, a3)))}, _, a3 <> a2 <> a1 <> a0 <> r1)
  s32 = Equal.sym(B.Bytes(), B.write_u32(B.cat8(a0, B.cat8(a1, B.cat8(a2, a3))), r1), a3 <> a2 <> a1 <> a0 <> r1, P.Bytes.u32_sx(a3, a2, a1, a0, m3, m2, m1, m0, r1))
  %s32 : {_ == a3 <> a2 <> a1 <> a0 <> r1 : B.Bytes()} & {B.all_bytes(r1) == True{} : Bool}
  ({==}, ab1)

def Payload.sx_ipv4_fin(+a3: U32, +a2: U32, +a1: U32, +a0: U32, +m3: U32, +m2: U32, +m1: U32, +m0: U32, +r2: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), ep: {Q.PIpv4{B.cat8(a0, B.cat8(a1, B.cat8(a2, a3))), B.cat8(m0, B.cat8(m1, B.cat8(m2, m3)))} == p : Q.Payload}, er: {r2 == r : B.Bytes()}, ka3: {U32.and(255, a3) == a3 : U32}, ka2: {U32.and(255, a2) == a2 : U32}, ka1: {U32.and(255, a1) == a1 : U32}, ka0: {U32.and(255, a0) == a0 : U32}, km3: {U32.and(255, m3) == m3 : U32}, km2: {U32.and(255, m2) == m2 : U32}, km1: {U32.and(255, m1) == m1 : U32}, km0: {U32.and(255, m0) == m0 : U32}, ab2: {B.all_bytes(r2) == True{} : Bool}) -> Payload.Sx(p, r, a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2):
  %ep : Payload.Sx(_, r, a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2)
  %er : Payload.Sx(Q.PIpv4{B.cat8(a0, B.cat8(a1, B.cat8(a2, a3))), B.cat8(m0, B.cat8(m1, B.cat8(m2, m3)))}, _, a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2)
  sm = Equal.sym(B.Bytes(), B.write_u32(B.cat8(m0, B.cat8(m1, B.cat8(m2, m3))), r2), m3 <> m2 <> m1 <> m0 <> r2, P.Bytes.u32_sx(m3, m2, m1, m0, km3, km2, km1, km0, r2))
  %sm : {B.write_u32(B.cat8(a0, B.cat8(a1, B.cat8(a2, a3))), _) == a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2 : B.Bytes()} & {B.all_bytes(r2) == True{} : Bool}
  sa = Equal.sym(B.Bytes(), B.write_u32(B.cat8(a0, B.cat8(a1, B.cat8(a2, a3))), m3 <> m2 <> m1 <> m0 <> r2), a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2, P.Bytes.u32_sx(a3, a2, a1, a0, ka3, ka2, ka1, ka0, m3 <> m2 <> m1 <> m0 <> r2))
  %sa : {_ == a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2 : B.Bytes()} & {B.all_bytes(r2) == True{} : Bool}
  ({==}, ab2)

def Payload.sx_ipv4_ok(+a3: U32, +a2: U32, +a1: U32, +a0: U32, +m3: U32, +m2: U32, +m1: U32, +m0: U32, +r2: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), ok: Bool, +e: {B.guard(B.ReadValue(Q.Payload), (Q.PIpv4{B.cat8(a0, B.cat8(a1, B.cat8(a2, a3))), B.cat8(m0, B.cat8(m1, B.cat8(m2, m3)))}, r2), B.cat8(m0, B.cat8(m1, B.cat8(m2, m3))), ok) == Done{(p, r)} : B.Read(Q.Payload)}, +ab: {B.all_bytes(a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2) == True{} : Bool}) -> Payload.Sx(p, r, a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2):
  match ok:
    case False{}:
      Payload.absurd(p, r, a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2, B.Invalid{B.cat8(m0, B.cat8(m1, B.cat8(m2, m3)))}, e)
    case True{}:
      Payload.eqs(Payload.Sx(p, r, a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2), p, r, Q.PIpv4{B.cat8(a0, B.cat8(a1, B.cat8(a2, a3))), B.cat8(m0, B.cat8(m1, B.cat8(m2, m3)))}, r2, e, ep => er => Bytes4.masks(Payload.Sx(p, r, a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2), a3, a2, a1, a0, m3 <> m2 <> m1 <> m0 <> r2, ab, ka3 => ka2 => ka1 => ka0 => abm => Bytes4.masks(Payload.Sx(p, r, a3 <> a2 <> a1 <> a0 <> m3 <> m2 <> m1 <> m0 <> r2), m3, m2, m1, m0, r2, abm, km3 => km2 => km1 => km0 => ab2 => Payload.sx_ipv4_fin(a3, a2, a1, a0, m3, m2, m1, m0, r2, p, r, ep, er, ka3, ka2, ka1, ka0, km3, km2, km1, km0, ab2))))

def Payload.sx_ipv4_mask(+a3: U32, +a2: U32, +a1: U32, +a0: U32, r1: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), +e: {Q.Payload.ipv4(B.cat8(a0, B.cat8(a1, B.cat8(a2, a3))), B.u32(r1)) == Done{(p, r)} : B.Read(Q.Payload)}, +ab: {B.all_bytes(a3 <> a2 <> a1 <> a0 <> r1) == True{} : Bool}) -> Payload.Sx(p, r, a3 <> a2 <> a1 <> a0 <> r1):
  match r1:
    case Nil{}:
      Payload.absurd(p, r, a3 <> a2 <> a1 <> a0 <> [], B.Short{}, e)
    case x <> Nil{}:
      Payload.absurd(p, r, a3 <> a2 <> a1 <> a0 <> [x], B.Short{}, e)
    case x <> y <> Nil{}:
      Payload.absurd(p, r, a3 <> a2 <> a1 <> a0 <> [x, y], B.Short{}, e)
    case x <> y <> z <> Nil{}:
      Payload.absurd(p, r, a3 <> a2 <> a1 <> a0 <> [x, y, z], B.Short{}, e)
    case +m3 <> +m2 <> +m1 <> +m0 <> +r2:
      Payload.sx_ipv4_ok(a3, a2, a1, a0, m3, m2, m1, m0, r2, p, r, Q.Mask.contiguous(B.cat8(m0, B.cat8(m1, B.cat8(m2, m3)))), e, ab)

def Payload.sx_ipv6_fin(+addr: B.Bytes(), +pre: U32, +r2: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), +bs: B.Bytes(), ep: {Q.PIpv6{addr, pre} == p : Q.Payload}, er: {r2 == r : B.Bytes()}, ap: {List.append(&2, U32, addr, pre <> r2) == bs : B.Bytes()}, mp: {U32.and(255, pre) == pre : U32}, ab2: {B.all_bytes(r2) == True{} : Bool}) -> Payload.Sx(p, r, bs):
  %ep : Payload.Sx(_, r, bs)
  %er : Payload.Sx(Q.PIpv6{addr, pre}, _, bs)
  smp = Equal.sym(U32, U32.and(255, pre), pre, mp)
  %smp : {List.append(&2, U32, addr, _ <> r2) == bs : B.Bytes()} & {B.all_bytes(r2) == True{} : Bool}
  (ap, ab2)

def Payload.sx_ipv6_ok(+addr: B.Bytes(), +pre: U32, +r2: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), +bs: B.Bytes(), ok: Bool, +e: {B.guard(B.ReadValue(Q.Payload), (Q.PIpv6{addr, pre}, r2), pre, ok) == Done{(p, r)} : B.Read(Q.Payload)}, ap: {List.append(&2, U32, addr, pre <> r2) == bs : B.Bytes()}, +al: {B.all_bytes(pre <> r2) == True{} : Bool}) -> Payload.Sx(p, r, bs):
  match ok:
    case False{}:
      Payload.absurd(p, r, bs, B.Invalid{pre}, e)
    case True{}:
      Payload.eqs(Payload.Sx(p, r, bs), p, r, Q.PIpv6{addr, pre}, r2, e, ep => er => Payload.sx_ipv6_fin(addr, pre, r2, p, r, bs, ep, er, ap, P.U32.lt256_mask8(pre, P.Bool.and_true_l(B.is_byte(pre), B.all_bytes(r2), al)), P.Bool.and_true_r(B.is_byte(pre), B.all_bytes(r2), al)))

def Payload.sx_ipv6_prefix(+addr: B.Bytes(), r1: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), +bs: B.Bytes(), +e: {Q.Payload.ipv6_prefix(addr, B.u8(r1)) == Done{(p, r)} : B.Read(Q.Payload)}, ap: {List.append(&2, U32, addr, r1) == bs : B.Bytes()}, +al: {B.all_bytes(r1) == True{} : Bool}) -> Payload.Sx(p, r, bs):
  match r1:
    case Nil{}:
      Payload.absurd(p, r, bs, B.Short{}, e)
    case +pre <> +r2:
      Payload.sx_ipv6_ok(addr, pre, r2, p, r, bs, U32.is_le(pre, 128), e, ap, al)

def Payload.sx_ipv6(+bs: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), rt: B.Read(B.Bytes()), ert: {B.take(16n, bs) == rt : B.Read(B.Bytes())}, +e: {Q.Payload.ipv6(rt) == Done{(p, r)} : B.Read(Q.Payload)}, ab: {B.all_bytes(bs) == True{} : Bool}) -> Payload.Sx(p, r, bs):
  match rt:
    case Fail{err}:
      Payload.absurd(p, r, bs, err, e)
    case Done{(+addr, +r1)}:
      PB.Take.sx(Payload.Sx(p, r, bs), 16n, bs, addr, r1, ert, ab, ap => al => Payload.sx_ipv6_prefix(addr, r1, p, r, bs, e, ap, al))

def Payload.sx_six_fin(+bytes: B.Bytes(), +r1: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), +bs: B.Bytes(), ep: {Q.PSix{bytes} == p : Q.Payload}, er: {r1 == r : B.Bytes()}, ap: {List.append(&2, U32, bytes, r1) == bs : B.Bytes()}, al: {B.all_bytes(r1) == True{} : Bool}) -> Payload.Sx(p, r, bs):
  %ep : Payload.Sx(_, r, bs)
  %er : Payload.Sx(Q.PSix{bytes}, _, bs)
  (ap, al)

def Payload.sx_six(+bs: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), rt: B.Read(B.Bytes()), ert: {B.take(6n, bs) == rt : B.Read(B.Bytes())}, +e: {Q.Payload.six(rt) == Done{(p, r)} : B.Read(Q.Payload)}, ab: {B.all_bytes(bs) == True{} : Bool}) -> Payload.Sx(p, r, bs):
  match rt:
    case Fail{err}:
      Payload.absurd(p, r, bs, err, e)
    case Done{(+bytes, +r1)}:
      Payload.eqs(Payload.Sx(p, r, bs), p, r, Q.PSix{bytes}, r1, e, ep => er => PB.Take.sx(Payload.Sx(p, r, bs), 6n, bs, bytes, r1, ert, ab, ap => al => Payload.sx_six_fin(bytes, r1, p, r, bs, ep, er, ap, al)))

def Payload.sx(shape: Q.Shape, +bs: B.Bytes(), +p: Q.Payload, +r: B.Bytes(), +e: {Q.Payload.read(shape, bs) == Done{(p, r)} : B.Read(Q.Payload)}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> Payload.Sx(p, r, bs):
  match shape:
    case Q.SNone{}:
      Payload.eqs(Payload.Sx(p, r, bs), p, r, Q.PNone{}, bs, e, ep => er => Payload.sx_none(bs, p, r, ep, er, ab))
    case Q.SIpv4{}:
      match bs:
        case Nil{}:
          Payload.absurd(p, r, [], B.Short{}, e)
        case x <> Nil{}:
          Payload.absurd(p, r, [x], B.Short{}, e)
        case x <> y <> Nil{}:
          Payload.absurd(p, r, [x, y], B.Short{}, e)
        case x <> y <> z <> Nil{}:
          Payload.absurd(p, r, [x, y, z], B.Short{}, e)
        case +a3 <> +a2 <> +a1 <> +a0 <> +r1:
          Payload.sx_ipv4_mask(a3, a2, a1, a0, r1, p, r, e, ab)
    case Q.SIpv6{}:
      Payload.sx_ipv6(bs, p, r, B.take(16n, bs), {==}, e, ab)
    case Q.SOne{}:
      match bs:
        case Nil{}:
          Payload.absurd(p, r, [], B.Short{}, e)
        case +v <> +r1:
          Payload.eqs(Payload.Sx(p, r, v <> r1), p, r, Q.POne{v}, r1, e, ep => er => Payload.sx_one(v, r1, p, r, ep, er, ab))
    case Q.STwo{}:
      match bs:
        case Nil{}:
          Payload.absurd(p, r, [], B.Short{}, e)
        case x <> Nil{}:
          Payload.absurd(p, r, [x], B.Short{}, e)
        case +x <> +y <> +r1:
          Payload.eqs(Payload.Sx(p, r, x <> y <> r1), p, r, Q.PTwo{B.cat8(y, x)}, r1, e, ep => er => Payload.sx_two(x, y, r1, p, r, ep, er, ab))
    case Q.SThree{}:
      match bs:
        case Nil{}:
          Payload.absurd(p, r, [], B.Short{}, e)
        case x <> Nil{}:
          Payload.absurd(p, r, [x], B.Short{}, e)
        case x <> y <> Nil{}:
          Payload.absurd(p, r, [x, y], B.Short{}, e)
        case +x <> +y <> +z <> +r1:
          Payload.eqs(Payload.Sx(p, r, x <> y <> z <> r1), p, r, Q.PThree{B.cat8(z, B.cat8(y, x))}, r1, e, ep => er => Payload.sx_three(x, y, z, r1, p, r, ep, er, ab))
    case Q.SFour{}:
      match bs:
        case Nil{}:
          Payload.absurd(p, r, [], B.Short{}, e)
        case x <> Nil{}:
          Payload.absurd(p, r, [x], B.Short{}, e)
        case x <> y <> Nil{}:
          Payload.absurd(p, r, [x, y], B.Short{}, e)
        case x <> y <> z <> Nil{}:
          Payload.absurd(p, r, [x, y, z], B.Short{}, e)
        case +a3 <> +a2 <> +a1 <> +a0 <> +r1:
          Payload.eqs(Payload.Sx(p, r, a3 <> a2 <> a1 <> a0 <> r1), p, r, Q.PFour{B.cat8(a0, B.cat8(a1, B.cat8(a2, a3)))}, r1, e, ep => er => Bytes4.masks(Payload.Sx(p, r, a3 <> a2 <> a1 <> a0 <> r1), a3, a2, a1, a0, r1, ab, m3 => m2 => m1 => m0 => ab1 => Payload.sx_four(a3, a2, a1, a0, r1, p, r, ep, er, m3, m2, m1, m0, ab1)))
    case Q.SSix{}:
      Payload.sx_six(bs, p, r, B.take(6n, bs), {==}, e, ab)

# Components
def Comp.Sx(c: Q.Comp, r: B.Bytes(), bs: B.Bytes()) -> Type:
  {Q.Comp.write(c, r) == bs : B.Bytes()} & {B.all_bytes(r) == True{} : Bool}

def Comp.absurd(+c: Q.Comp, +r: B.Bytes(), +bs: B.Bytes(), err: B.Err, e: {Fail{err} == Done{(c, r)} : B.Read(Q.Comp)}) -> Comp.Sx(c, r, bs):
  Empty.absurd(Comp.Sx(c, r, bs), P.Refute.fail_done(B.Err, B.ReadValue(Q.Comp), err, (c, r), e))

def Comp.sx_fin(+k: U32, +rest: B.Bytes(), +c: Q.Comp, +r: B.Bytes(), +p: Q.Payload, +r2: B.Bytes(), ec: {Q.Comp{k, p} == c : Q.Comp}, er: {r2 == r : B.Bytes()}, s: Payload.Sx(p, r2, rest)) -> Comp.Sx(c, r, k <> rest):
  (w, a) = s
  %ec : Comp.Sx(_, r, k <> rest)
  %er : Comp.Sx(Q.Comp{k, p}, _, k <> rest)
  sw = Equal.sym(B.Bytes(), Q.Payload.write(p, r2), rest, w)
  %sw : {k <> _ == k <> rest : B.Bytes()} & {B.all_bytes(r2) == True{} : Bool}
  ({==}, a)

def Comp.sx_of(+k: U32, +rest: B.Bytes(), +c: Q.Comp, +r: B.Bytes(), shape: Q.Shape, rp: B.Read(Q.Payload), erp: {Q.Payload.read(shape, rest) == rp : B.Read(Q.Payload)}, +e: {Q.Comp.of(k, rp) == Done{(c, r)} : B.Read(Q.Comp)}, ab: {B.all_bytes(rest) == True{} : Bool}) -> Comp.Sx(c, r, k <> rest):
  match rp:
    case Fail{err}:
      Comp.absurd(c, r, k <> rest, err, e)
    case Done{(+p, +r2)}:
      Comp.sx_fin(k, rest, c, r, p, r2, Equal.cong(B.Read(Q.Comp), Q.Comp, x => P.Read.value(Q.Comp, x, c), Done{(Q.Comp{k, p}, r2)}, Done{(c, r)}, e), Equal.cong(B.Read(Q.Comp), B.Bytes(), x => P.Read.rest(Q.Comp, x, r), Done{(Q.Comp{k, p}, r2)}, Done{(c, r)}, e), Payload.sx(shape, rest, p, r2, erp, ab))

def Comp.sx_kind(+k: U32, +rest: B.Bytes(), +c: Q.Comp, +r: B.Bytes(), ms: Maybe<&2, Q.Shape>, +e: {Q.Comp.kind(k, rest, ms) == Done{(c, r)} : B.Read(Q.Comp)}, ab: {B.all_bytes(rest) == True{} : Bool}) -> Comp.Sx(c, r, k <> rest):
  match ms:
    case None{}:
      Comp.absurd(c, r, k <> rest, B.Unsupported{k}, e)
    case Some{+shape}:
      Comp.sx_of(k, rest, c, r, shape, Q.Payload.read(shape, rest), {==}, e, ab)

def Comp.sx(bs: B.Bytes(), +c: Q.Comp, +r: B.Bytes(), +e: {Q.Comp.read(bs) == Done{(c, r)} : B.Read(Q.Comp)}, ab: {B.all_bytes(bs) == True{} : Bool}) -> Comp.Sx(c, r, bs):
  match bs:
    case Nil{}:
      Comp.absurd(c, r, [], B.Short{}, e)
    case +k <> +rest:
      Comp.sx_kind(k, rest, c, r, Q.Comp.shape(k), e, P.Bool.and_true_r(B.is_byte(k), B.all_bytes(rest), ab))

def Comps.Res() -> Data:
  Result<&2, &2, B.Err, List<&2, Q.Comp>>

def Comps.absurd(+cs: List<&2, Q.Comp>, +bs: B.Bytes(), err: B.Err, e: {Fail{err} == Done{cs} : Comps.Res()}) -> {Q.Comps.write(cs, []) == bs : B.Bytes()}:
  Empty.absurd({Q.Comps.write(cs, []) == bs : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, Q.Comp>, err, cs, e))

def Comps.sx_cons(+f: Nat, +b: U32, +rest: B.Bytes(), +c: Q.Comp, +r1: B.Bytes(), +cs: List<&2, Q.Comp>, ro: Comps.Res(), ero: {Q.Comps.go(f, r1) == ro : Comps.Res()}, +e: {B.Res.cons(Q.Comp, c, ro) == Done{cs} : Comps.Res()}, s: Comp.Sx(c, r1, b <> rest), ih: @cs2: List<&2, Q.Comp> -> {Q.Comps.go(f, r1) == Done{cs2} : Comps.Res()} -> {B.all_bytes(r1) == True{} : Bool} -> {Q.Comps.write(cs2, []) == r1 : B.Bytes()}) -> {Q.Comps.write(cs, []) == b <> rest : B.Bytes()}:
  match ro:
    case Fail{err}:
      Comps.absurd(cs, b <> rest, err, e)
    case Done{+cs2}:
      (w, a) = s
      ec = Equal.cong(Comps.Res(), List<&2, Q.Comp>, x => P.Res.value(B.Err, List<&2, Q.Comp>, x, cs), Done{c <> cs2}, Done{cs}, e)
      %ec : {Q.Comps.write(_, []) == b <> rest : B.Bytes()}
      sw = Equal.sym(B.Bytes(), Q.Comps.write(cs2, []), r1, ih(cs2, ero, a))
      %sw : {Q.Comp.write(c, _) == b <> rest : B.Bytes()}
      w

def Comps.sx_next(+f: Nat, +b: U32, +rest: B.Bytes(), +cs: List<&2, Q.Comp>, rc: B.Read(Q.Comp), erc: {Q.Comp.read(b <> rest) == rc : B.Read(Q.Comp)}, +e: {Q.Comps.next(rc, left => Q.Comps.go(f, left)) == Done{cs} : Comps.Res()}, ab: {B.all_bytes(b <> rest) == True{} : Bool}, ih: @cs2: List<&2, Q.Comp> -> @r1: B.Bytes() -> {Q.Comps.go(f, r1) == Done{cs2} : Comps.Res()} -> {B.all_bytes(r1) == True{} : Bool} -> {Q.Comps.write(cs2, []) == r1 : B.Bytes()}) -> {Q.Comps.write(cs, []) == b <> rest : B.Bytes()}:
  match rc:
    case Fail{err}:
      Comps.absurd(cs, b <> rest, err, e)
    case Done{(+c, +r1)}:
      Comps.sx_cons(f, b, rest, c, r1, cs, Q.Comps.go(f, r1), {==}, e, Comp.sx(b <> rest, c, r1, erc, ab), cs2 => e2 => ab2 => ih(cs2, r1, e2, ab2))

def Comps.sx(fuel: Nat, bs: B.Bytes(), +cs: List<&2, Q.Comp>, +e: {Q.Comps.go(fuel, bs) == Done{cs} : Comps.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> {Q.Comps.write(cs, []) == bs : B.Bytes()}:
  match fuel bs:
    case 0n Nil{}:
      ec = Equal.cong(Comps.Res(), List<&2, Q.Comp>, x => P.Res.value(B.Err, List<&2, Q.Comp>, x, cs), Done{[]}, Done{cs}, e)
      %ec : {Q.Comps.write(_, []) == [] : B.Bytes()}
      {==}
    case 1n+f Nil{}:
      ec = Equal.cong(Comps.Res(), List<&2, Q.Comp>, x => P.Res.value(B.Err, List<&2, Q.Comp>, x, cs), Done{[]}, Done{cs}, e)
      %ec : {Q.Comps.write(_, []) == [] : B.Bytes()}
      {==}
    case 0n +b <> +rest:
      Comps.absurd(cs, b <> rest, B.Invalid{b}, e)
    case 1n++f +b <> +rest:
      Comps.sx_next(f, b, rest, cs, Q.Comp.read(b <> rest), {==}, e, ab, cs2 => r1 => e2 => ab2 => Comps.sx(f, r1, cs2, e2, ab2))

# Packet filters
def Filter.Sx(f: Q.Filter, r: B.Bytes(), bs: B.Bytes()) -> Type:
  {Q.Filter.write(f, r) == bs : B.Bytes()} & {B.all_bytes(r) == True{} : Bool}

def Filter.absurd(+f: Q.Filter, +r: B.Bytes(), +bs: B.Bytes(), err: B.Err, e: {Fail{err} == Done{(f, r)} : B.Read(Q.Filter)}) -> Filter.Sx(f, r, bs):
  Empty.absurd(Filter.Sx(f, r, bs), P.Refute.fail_done(B.Err, B.ReadValue(Q.Filter), err, (f, r), e))

def Filter.sx_fin(+hdr: U32, +l: U32, +tail: B.Bytes(), +f: Q.Filter, +r: B.Bytes(), +len: U32, +body: B.Bytes(), +comps: List<&2, Q.Comp>, +r2: B.Bytes(), ef: {Q.Filter{hdr, len, comps} == f : Q.Filter}, er: {r2 == r : B.Bytes()}, wc: {Q.Comps.write(comps, []) == body : B.Bytes()}, f8: {B.fits8(l) == True{} : Bool}, +body2: B.Bytes(), +r3: B.Bytes(), +e2: {Done{(I.LenBody{l, body2}, r3)} == Done{(I.LenBody{len, body}, r2)} : B.Read(I.LenBody)}, ap: {List.append(&2, U32, body2, r3) == tail : B.Bytes()}, al: {B.all_bytes(r3) == True{} : Bool}) -> Filter.Sx(f, r, hdr <> l <> tail):
  %ef : Filter.Sx(_, r, hdr <> l <> tail)
  %er : Filter.Sx(Q.Filter{hdr, len, comps}, _, hdr <> l <> tail)
  +elb = Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, I.LenBody{len, body}), Done{(I.LenBody{l, body2}, r3)}, Done{(I.LenBody{len, body}, r2)}, e2)
  el = Equal.cong(I.LenBody, U32, x => P.Lb.len(x), I.LenBody{l, body2}, I.LenBody{len, body}, elb)
  eb = Equal.cong(I.LenBody, B.Bytes(), x => P.Lb.body(x), I.LenBody{l, body2}, I.LenBody{len, body}, elb)
  er3 = Equal.cong(B.Read(I.LenBody), B.Bytes(), x => P.Read.rest(I.LenBody, x, r2), Done{(I.LenBody{l, body2}, r3)}, Done{(I.LenBody{len, body}, r2)}, e2)
  %el : Filter.Sx(Q.Filter{hdr, _, comps}, r2, hdr <> l <> tail)
  %er3 : Filter.Sx(Q.Filter{hdr, l, comps}, _, hdr <> l <> tail)
  swc = Equal.sym(B.Bytes(), Q.Comps.write(comps, []), body, wc)
  %swc : {hdr <> U32.and(255, l) <> List.append(&2, U32, _, r3) == hdr <> l <> tail : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  %eb : {hdr <> U32.and(255, l) <> List.append(&2, U32, _, r3) == hdr <> l <> tail : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, body2, r3), tail, ap)
  %sap : {hdr <> U32.and(255, l) <> _ == hdr <> l <> tail : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  ml = Equal.sym(U32, U32.and(255, l), l, P.U32.eq_of_is_eq(U32.and(255, l), l, f8))
  %ml : {hdr <> _ <> tail == hdr <> l <> tail : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  ({==}, al)

def Filter.sx_comps(+hdr: U32, +l: U32, +tail: B.Bytes(), +f: Q.Filter, +r: B.Bytes(), +len: U32, +body: B.Bytes(), +r2: B.Bytes(), +body2: B.Bytes(), +r3: B.Bytes(), rc: Comps.Res(), erc: {Q.Comps.read(body) == rc : Comps.Res()}, +e: {Q.Filter.of(hdr, len, rc, r2) == Done{(f, r)} : B.Read(Q.Filter)}, f8: {B.fits8(l) == True{} : Bool}, +e2: {Done{(I.LenBody{l, body2}, r3)} == Done{(I.LenBody{len, body}, r2)} : B.Read(I.LenBody)}, +ap: {List.append(&2, U32, body2, r3) == tail : B.Bytes()}, al: {B.all_bytes(r3) == True{} : Bool}, abt: {B.all_bytes(tail) == True{} : Bool}) -> Filter.Sx(f, r, hdr <> l <> tail):
  match rc:
    case Fail{err}:
      Filter.absurd(f, r, hdr <> l <> tail, err, e)
    case Done{+comps}:
      eb = Equal.cong(I.LenBody, B.Bytes(), x => P.Lb.body(x), I.LenBody{l, body2}, I.LenBody{len, body}, Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, I.LenBody{len, body}), Done{(I.LenBody{l, body2}, r3)}, Done{(I.LenBody{len, body}, r2)}, e2))
      sap = Equal.sym(B.Bytes(), List.append(&2, U32, body2, r3), tail, ap)
      +abb : {B.all_bytes(body) == True{} : Bool} = (%eb : {B.all_bytes(_) == True{} : Bool}; Bytes.all_prefix(body2, r3, (%sap : {B.all_bytes(_) == True{} : Bool}; abt)))
      Filter.sx_fin(hdr, l, tail, f, r, len, body, comps, r2, Equal.cong(B.Read(Q.Filter), Q.Filter, x => P.Read.value(Q.Filter, x, f), Done{(Q.Filter{hdr, len, comps}, r2)}, Done{(f, r)}, e), Equal.cong(B.Read(Q.Filter), B.Bytes(), x => P.Read.rest(Q.Filter, x, r), Done{(Q.Filter{hdr, len, comps}, r2)}, Done{(f, r)}, e), Comps.sx(List.length(&2, U32, body), body, comps, erc, abb), f8, body2, r3, e2, ap, al)

def Filter.sx_lv(+hdr: U32, +l: U32, +tail: B.Bytes(), +f: Q.Filter, +r: B.Bytes(), rl: B.Read(I.LenBody), erl: {I.Len.take(l, tail, B.fits8(l)) == rl : B.Read(I.LenBody)}, +e: {Q.Filter.body(hdr, rl) == Done{(f, r)} : B.Read(Q.Filter)}, +abt: {B.all_bytes(tail) == True{} : Bool}) -> Filter.Sx(f, r, hdr <> l <> tail):
  match rl:
    case Fail{err}:
      Filter.absurd(f, r, hdr <> l <> tail, err, e)
    case Done{(I.LenBody{+len, +body}, +r2)}:
      PM.Len.sx(Filter.Sx(f, r, hdr <> l <> tail), l, tail, I.LenBody{len, body}, r2, B.fits8(l), B.fits8(l), {==}, erl, abt, f8 => body2 => r3 => e2 => ap => al => Filter.sx_comps(hdr, l, tail, f, r, len, body, r2, body2, r3, Q.Comps.read(body), {==}, e, f8, e2, ap, al, abt))

def Filter.sx_ok(ok: Bool, +hdr: U32, rest: B.Bytes(), +f: Q.Filter, +r: B.Bytes(), +e: {Q.Filter.hdr_ok(hdr, rest, ok) == Done{(f, r)} : B.Read(Q.Filter)}, +ab: {B.all_bytes(rest) == True{} : Bool}) -> Filter.Sx(f, r, hdr <> rest):
  match ok:
    case False{}:
      Filter.absurd(f, r, hdr <> rest, B.Invalid{hdr}, e)
    case True{}:
      match rest:
        case Nil{}:
          Filter.absurd(f, r, [hdr], B.Short{}, e)
        case +l <> +tail:
          Filter.sx_lv(hdr, l, tail, f, r, I.Len.take(l, tail, B.fits8(l)), {==}, e, P.Bool.and_true_r(B.is_byte(l), B.all_bytes(tail), ab))

def Filter.sx(bs: B.Bytes(), +f: Q.Filter, +r: B.Bytes(), +e: {Q.Filter.read(bs) == Done{(f, r)} : B.Read(Q.Filter)}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> Filter.Sx(f, r, bs):
  match bs:
    case Nil{}:
      Filter.absurd(f, r, [], B.Short{}, e)
    case +hdr <> +rest:
      Filter.sx_ok(Bool.and(B.fits8(hdr), U32.is_eq(U32.and(192, hdr), 0)), hdr, rest, f, r, e, P.Bool.and_true_r(B.is_byte(hdr), B.all_bytes(rest), ab))

def Filters.Sx(fs: List<&2, Q.Filter>, r: B.Bytes(), bs: B.Bytes()) -> Type:
  {Q.Filters.write(fs, r) == bs : B.Bytes()} & {B.all_bytes(r) == True{} : Bool}

def Filters.absurd(+fs: List<&2, Q.Filter>, +r: B.Bytes(), +bs: B.Bytes(), err: B.Err, e: {Fail{err} == Done{(fs, r)} : B.Read(List<&2, Q.Filter>)}) -> Filters.Sx(fs, r, bs):
  Empty.absurd(Filters.Sx(fs, r, bs), P.Refute.fail_done(B.Err, B.ReadValue(List<&2, Q.Filter>), err, (fs, r), e))

def Filters.sx_fin(+bs: B.Bytes(), +f: Q.Filter, +r1: B.Bytes(), +fs2: List<&2, Q.Filter>, +r3: B.Bytes(), w1: {Q.Filter.write(f, r1) == bs : B.Bytes()}, s2: Filters.Sx(fs2, r3, r1)) -> Filters.Sx(f <> fs2, r3, bs):
  (w2, a2) = s2
  sw2 = Equal.sym(B.Bytes(), Q.Filters.write(fs2, r3), r1, w2)
  %sw2 : {Q.Filter.write(f, _) == bs : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  (w1, a2)

def Filters.sx_cons(+p: Nat, +bs: B.Bytes(), +f: Q.Filter, +r1: B.Bytes(), r2: B.Read(List<&2, Q.Filter>), er2: {Q.Filters.read(p, r1) == r2 : B.Read(List<&2, Q.Filter>)}, +fs: List<&2, Q.Filter>, +rest: B.Bytes(), +e: {B.Read.cons(Q.Filter, f, r2) == Done{(fs, rest)} : B.Read(List<&2, Q.Filter>)}, s1: Filter.Sx(f, r1, bs), ih: @fs2: List<&2, Q.Filter> -> @r3: B.Bytes() -> {Q.Filters.read(p, r1) == Done{(fs2, r3)} : B.Read(List<&2, Q.Filter>)} -> {B.all_bytes(r1) == True{} : Bool} -> Filters.Sx(fs2, r3, r1)) -> Filters.Sx(fs, rest, bs):
  match r2:
    case Fail{err}:
      Filters.absurd(fs, rest, bs, err, e)
    case Done{(+fs2, +r3)}:
      (w1, a1) = s1
      et = Equal.cong(B.Read(List<&2, Q.Filter>), List<&2, Q.Filter>, x => P.Read.value(List<&2, Q.Filter>, x, fs), Done{(f <> fs2, r3)}, Done{(fs, rest)}, e)
      er = Equal.cong(B.Read(List<&2, Q.Filter>), B.Bytes(), x => P.Read.rest(List<&2, Q.Filter>, x, rest), Done{(f <> fs2, r3)}, Done{(fs, rest)}, e)
      %et : Filters.Sx(_, rest, bs)
      %er : Filters.Sx(f <> fs2, _, bs)
      Filters.sx_fin(bs, f, r1, fs2, r3, w1, ih(fs2, r3, er2, a1))

def Filters.sx_next(+p: Nat, +bs: B.Bytes(), rf: B.Read(Q.Filter), erf: {Q.Filter.read(bs) == rf : B.Read(Q.Filter)}, +fs: List<&2, Q.Filter>, +rest: B.Bytes(), +e: {Q.Filters.next(rf, r => Q.Filters.read(p, r)) == Done{(fs, rest)} : B.Read(List<&2, Q.Filter>)}, ab: {B.all_bytes(bs) == True{} : Bool}, ih: @r1: B.Bytes() -> @fs2: List<&2, Q.Filter> -> @r3: B.Bytes() -> {Q.Filters.read(p, r1) == Done{(fs2, r3)} : B.Read(List<&2, Q.Filter>)} -> {B.all_bytes(r1) == True{} : Bool} -> Filters.Sx(fs2, r3, r1)) -> Filters.Sx(fs, rest, bs):
  match rf:
    case Fail{err}:
      Filters.absurd(fs, rest, bs, err, e)
    case Done{(+f, +r1)}:
      Filters.sx_cons(p, bs, f, r1, Q.Filters.read(p, r1), {==}, fs, rest, e, Filter.sx(bs, f, r1, erf, ab), fs2 => r3 => e2 => ab2 => ih(r1, fs2, r3, e2, ab2))

def Filters.sx(n: Nat, +bs: B.Bytes(), +fs: List<&2, Q.Filter>, +rest: B.Bytes(), +e: {Q.Filters.read(n, bs) == Done{(fs, rest)} : B.Read(List<&2, Q.Filter>)}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> Filters.Sx(fs, rest, bs):
  match n:
    case 0n:
      et = Equal.cong(B.Read(List<&2, Q.Filter>), List<&2, Q.Filter>, x => P.Read.value(List<&2, Q.Filter>, x, fs), Done{([], bs)}, Done{(fs, rest)}, e)
      er = Equal.cong(B.Read(List<&2, Q.Filter>), B.Bytes(), x => P.Read.rest(List<&2, Q.Filter>, x, rest), Done{([], bs)}, Done{(fs, rest)}, e)
      %et : Filters.Sx(_, rest, bs)
      %er : Filters.Sx([], _, bs)
      ({==}, ab)
    case 1n++p:
      Filters.sx_next(p, bs, Q.Filter.read(bs), {==}, fs, rest, e, ab, r1 => fs2 => r3 => e2 => ab2 => Filters.sx(p, r1, fs2, r3, e2, ab2))

# Rule bodies
def Rule.absurd_body(-G: Type, +rule: Q.Rule, err: B.Err, e: {Fail{err} == Done{rule} : Result<&2, &2, B.Err, Q.Rule>}) -> G:
  Empty.absurd(G, P.Refute.fail_done(B.Err, Q.Rule, err, rule, e))

# The two tail bytes: precedence and QFI, then nothing.
def Rule.tail_sx(-G: Type, +qri: U32, +len: U32, +op: U32, +fs: Q.RuleFilters, r1: B.Bytes(), +rule: Q.Rule, +e: {Q.Rule.tail(qri, len, op, fs, B.u8(r1)) == Done{rule} : Result<&2, &2, B.Err, Q.Rule>}, +ab1: {B.all_bytes(r1) == True{} : Bool}, k: @p: U32 -> @q: U32 -> {Q.Rule{qri, len, op, fs, Q.Tail{p, q}} == rule : Q.Rule} -> {B.write_u8(p, B.write_u8(q, [])) == r1 : B.Bytes()} -> G) -> G:
  match r1:
    case Nil{}:
      Rule.absurd_body(G, rule, B.Short{}, e)
    case +p <> +r2:
      match r2:
        case Nil{}:
          Rule.absurd_body(G, rule, B.Short{}, e)
        case +q <> +r3:
          match r3:
            case x <> more:
              Rule.absurd_body(G, rule, B.Invalid{x}, e)
            case Nil{}:
              +abq = P.Bool.and_true_r(B.is_byte(p), B.all_bytes(q <> []), ab1)
              k(p, q, Equal.cong(Result<&2, &2, B.Err, Q.Rule>, Q.Rule, x => P.Res.value(B.Err, Q.Rule, x, rule), Done{Q.Rule{qri, len, op, fs, Q.Tail{p, q}}}, Done{rule}, e), P.List.cons_eq(U32.and(255, p), p, U32.and(255, q) <> [], q <> [], P.U32.lt256_mask8(p, P.Bool.and_true_l(B.is_byte(p), B.all_bytes(q <> []), ab1)), P.List.cons_eq(U32.and(255, q), q, [], [], P.U32.lt256_mask8(q, P.Bool.and_true_l(B.is_byte(q), B.all_bytes([]), abq)), {==})))

def Rule.bw_none(+op: U32, +p: U32, +q: U32, +rest: B.Bytes(), w: {B.write_u8(p, B.write_u8(q, [])) == rest : B.Bytes()}) -> {Q.Rule.body_write(op, Q.NoFilters{}, Q.Tail{p, q}) == op <> rest : B.Bytes()}:
  Equal.cong(B.Bytes(), B.Bytes(), x => op <> x, B.write_u8(p, B.write_u8(q, [])), rest, w)

def Rule.bw_whole(+op: U32, +filters: List<&2, Q.Filter>, +p: U32, +q: U32, +r1: B.Bytes(), +rest: B.Bytes(), w: {B.write_u8(p, B.write_u8(q, [])) == r1 : B.Bytes()}, w1: {Q.Filters.write(filters, r1) == rest : B.Bytes()}) -> {Q.Rule.body_write(op, Q.Whole{filters}, Q.Tail{p, q}) == op <> rest : B.Bytes()}:
  sw = Equal.sym(B.Bytes(), B.write_u8(p, B.write_u8(q, [])), r1, w)
  %sw : {op <> Q.Filters.write(filters, _) == op <> rest : B.Bytes()}
  sw1 = Equal.sym(B.Bytes(), Q.Filters.write(filters, r1), rest, w1)
  %sw1 : {op <> _ == op <> rest : B.Bytes()}
  {==}

def Rule.bw_only(+op: U32, +ids: B.Bytes(), +p: U32, +q: U32, +r1: B.Bytes(), +rest: B.Bytes(), w: {B.write_u8(p, B.write_u8(q, [])) == r1 : B.Bytes()}, ap: {List.append(&2, U32, ids, r1) == rest : B.Bytes()}) -> {Q.Rule.body_write(op, Q.Only{ids}, Q.Tail{p, q}) == op <> rest : B.Bytes()}:
  sw = Equal.sym(B.Bytes(), B.write_u8(p, B.write_u8(q, [])), r1, w)
  %sw : {op <> List.append(&2, U32, ids, _) == op <> rest : B.Bytes()}
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, ids, r1), rest, ap)
  %sap : {op <> _ == op <> rest : B.Bytes()}
  {==}

def Rule.whole_fin(-G: Type, +qri: U32, +len: U32, +op0: U32, +rest: B.Bytes(), +rule: Q.Rule, +filters: List<&2, Q.Filter>, +r1: B.Bytes(), +e: {Q.Rule.tail(qri, len, op0, Q.Whole{filters}, B.u8(r1)) == Done{rule} : Result<&2, &2, B.Err, Q.Rule>}, s: Filters.Sx(filters, r1, rest), k: @op: U32 -> @fs: Q.RuleFilters -> @t: Q.RuleTail -> {Q.Rule{qri, len, op, fs, t} == rule : Q.Rule} -> {Q.Rule.body_write(op, fs, t) == op0 <> rest : B.Bytes()} -> G) -> G:
  (w1, a1) = s
  Rule.tail_sx(G, qri, len, op0, Q.Whole{filters}, r1, rule, e, a1, +p => +q => eq => w => k(op0, Q.Whole{filters}, Q.Tail{p, q}, eq, Rule.bw_whole(op0, filters, p, q, r1, rest, w, w1)))

def Rule.whole_sx(-G: Type, +qri: U32, +len: U32, +op0: U32, +rest: B.Bytes(), +rule: Q.Rule, rf: B.Read(List<&2, Q.Filter>), erf: {Q.Filters.read(Q.Rule.count(op0), rest) == rf : B.Read(List<&2, Q.Filter>)}, +e: {Q.Rule.whole(qri, len, op0, rf) == Done{rule} : Result<&2, &2, B.Err, Q.Rule>}, abr: {B.all_bytes(rest) == True{} : Bool}, k: @op: U32 -> @fs: Q.RuleFilters -> @t: Q.RuleTail -> {Q.Rule{qri, len, op, fs, t} == rule : Q.Rule} -> {Q.Rule.body_write(op, fs, t) == op0 <> rest : B.Bytes()} -> G) -> G:
  match rf:
    case Fail{err}:
      Rule.absurd_body(G, rule, err, e)
    case Done{(+filters, +r1)}:
      Rule.whole_fin(G, qri, len, op0, rest, rule, filters, r1, e, Filters.sx(Q.Rule.count(op0), rest, filters, r1, erf, abr), k)

def Rule.only_sx(-G: Type, +qri: U32, +len: U32, +op0: U32, +rest: B.Bytes(), +rule: Q.Rule, rt: B.Read(B.Bytes()), ert: {B.take(Q.Rule.count(op0), rest) == rt : B.Read(B.Bytes())}, +e: {Q.Rule.only(qri, len, op0, rt) == Done{rule} : Result<&2, &2, B.Err, Q.Rule>}, abr: {B.all_bytes(rest) == True{} : Bool}, k: @op: U32 -> @fs: Q.RuleFilters -> @t: Q.RuleTail -> {Q.Rule{qri, len, op, fs, t} == rule : Q.Rule} -> {Q.Rule.body_write(op, fs, t) == op0 <> rest : B.Bytes()} -> G) -> G:
  match rt:
    case Fail{err}:
      Rule.absurd_body(G, rule, err, e)
    case Done{(+ids, +r1)}:
      PB.Take.sx(G, Q.Rule.count(op0), rest, ids, r1, ert, abr, ap => al => Rule.tail_sx(G, qri, len, op0, Q.Only{ids}, r1, rule, e, al, +p => +q => eq => w => k(op0, Q.Only{ids}, Q.Tail{p, q}, eq, Rule.bw_only(op0, ids, p, q, r1, rest, w, ap))))

def Rule.none_sx(-G: Type, +qri: U32, +len: U32, +op0: U32, rest: B.Bytes(), +rule: Q.Rule, +e: {Q.Rule.end(qri, len, op0, Q.NoFilters{}, Q.NoTail{}, rest) == Done{rule} : Result<&2, &2, B.Err, Q.Rule>}, k: @op: U32 -> @fs: Q.RuleFilters -> @t: Q.RuleTail -> {Q.Rule{qri, len, op, fs, t} == rule : Q.Rule} -> {Q.Rule.body_write(op, fs, t) == op0 <> rest : B.Bytes()} -> G) -> G:
  match rest:
    case x <> more:
      Rule.absurd_body(G, rule, B.Invalid{x}, e)
    case Nil{}:
      k(op0, Q.NoFilters{}, Q.NoTail{}, Equal.cong(Result<&2, &2, B.Err, Q.Rule>, Q.Rule, x => P.Res.value(B.Err, Q.Rule, x, rule), Done{Q.Rule{qri, len, op0, Q.NoFilters{}, Q.NoTail{}}}, Done{rule}, e), {==})

def Rule.code_sx(-G: Type, +qri: U32, +len: U32, +op0: U32, +rest: B.Bytes(), +rule: Q.Rule, code: Nat, +e: {Q.Rule.by_code(qri, len, op0, rest, code) == Done{rule} : Result<&2, &2, B.Err, Q.Rule>}, +abr: {B.all_bytes(rest) == True{} : Bool}, k: @op: U32 -> @fs: Q.RuleFilters -> @t: Q.RuleTail -> {Q.Rule{qri, len, op, fs, t} == rule : Q.Rule} -> {Q.Rule.body_write(op, fs, t) == op0 <> rest : B.Bytes()} -> G) -> G:
  match code:
    case 0n:
      Rule.absurd_body(G, rule, B.Unsupported{op0}, e)
    case 1n:
      Rule.whole_sx(G, qri, len, op0, rest, rule, Q.Filters.read(Q.Rule.count(op0), rest), {==}, e, abr, k)
    case 2n:
      Rule.none_sx(G, qri, len, op0, rest, rule, e, k)
    case 3n:
      Rule.whole_sx(G, qri, len, op0, rest, rule, Q.Filters.read(Q.Rule.count(op0), rest), {==}, e, abr, k)
    case 4n:
      Rule.whole_sx(G, qri, len, op0, rest, rule, Q.Filters.read(Q.Rule.count(op0), rest), {==}, e, abr, k)
    case 5n:
      Rule.only_sx(G, qri, len, op0, rest, rule, B.take(Q.Rule.count(op0), rest), {==}, e, abr, k)
    case 6n:
      Rule.tail_sx(G, qri, len, op0, Q.NoFilters{}, rest, rule, e, abr, +p => +q => eq => w => k(op0, Q.NoFilters{}, Q.Tail{p, q}, eq, Rule.bw_none(op0, p, q, rest, w)))
    case 7n+x:
      Rule.absurd_body(G, rule, B.Unsupported{op0}, e)

def Rule.body_sx(-G: Type, +qri: U32, +len: U32, body: B.Bytes(), +rule: Q.Rule, +e: {Q.Rule.body(qri, len, body) == Done{rule} : Result<&2, &2, B.Err, Q.Rule>}, +ab: {B.all_bytes(body) == True{} : Bool}, k: @op: U32 -> @fs: Q.RuleFilters -> @t: Q.RuleTail -> {Q.Rule{qri, len, op, fs, t} == rule : Q.Rule} -> {Q.Rule.body_write(op, fs, t) == body : B.Bytes()} -> G) -> G:
  match body:
    case Nil{}:
      Rule.absurd_body(G, rule, B.Short{}, e)
    case +op0 <> +rest:
      Rule.code_sx(G, qri, len, op0, rest, rule, Q.Rule.code(op0), e, P.Bool.and_true_r(B.is_byte(op0), B.all_bytes(rest), ab), k)

# Rules
def Rule.Sx(rule: Q.Rule, r: B.Bytes(), bs: B.Bytes()) -> Type:
  {Q.Rule.write(rule, r) == bs : B.Bytes()} & {B.all_bytes(r) == True{} : Bool}

def Rule.absurd(+rule: Q.Rule, +r: B.Bytes(), +bs: B.Bytes(), err: B.Err, e: {Fail{err} == Done{(rule, r)} : B.Read(Q.Rule)}) -> Rule.Sx(rule, r, bs):
  Empty.absurd(Rule.Sx(rule, r, bs), P.Refute.fail_done(B.Err, B.ReadValue(Q.Rule), err, (rule, r), e))

def Rule.sx_fin(+qri: U32, +l1: U32, +l0: U32, +tail: B.Bytes(), +rule: Q.Rule, +r: B.Bytes(), +len: U32, +body: B.Bytes(), +r1: B.Bytes(), +rule2: Q.Rule, +op: U32, +fs: Q.RuleFilters, +t: Q.RuleTail, +body2: B.Bytes(), +r3: B.Bytes(), erule2: {rule2 == rule : Q.Rule}, eq: {Q.Rule{qri, len, op, fs, t} == rule2 : Q.Rule}, er: {r1 == r : B.Bytes()}, bw: {Q.Rule.body_write(op, fs, t) == body : B.Bytes()}, +e2: {Done{(I.LenBody{B.cat8(l0, l1), body2}, r3)} == Done{(I.LenBody{len, body}, r1)} : B.Read(I.LenBody)}, ap: {List.append(&2, U32, body2, r3) == tail : B.Bytes()}, al: {B.all_bytes(r3) == True{} : Bool}, m1: {U32.and(255, l1) == l1 : U32}, m0: {U32.and(255, l0) == l0 : U32}) -> Rule.Sx(rule, r, qri <> l1 <> l0 <> tail):
  %erule2 : Rule.Sx(_, r, qri <> l1 <> l0 <> tail)
  %eq : Rule.Sx(_, r, qri <> l1 <> l0 <> tail)
  %er : Rule.Sx(Q.Rule{qri, len, op, fs, t}, _, qri <> l1 <> l0 <> tail)
  +elb = Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, I.LenBody{len, body}), Done{(I.LenBody{B.cat8(l0, l1), body2}, r3)}, Done{(I.LenBody{len, body}, r1)}, e2)
  el = Equal.cong(I.LenBody, U32, x => P.Lb.len(x), I.LenBody{B.cat8(l0, l1), body2}, I.LenBody{len, body}, elb)
  eb = Equal.cong(I.LenBody, B.Bytes(), x => P.Lb.body(x), I.LenBody{B.cat8(l0, l1), body2}, I.LenBody{len, body}, elb)
  er3 = Equal.cong(B.Read(I.LenBody), B.Bytes(), x => P.Read.rest(I.LenBody, x, r1), Done{(I.LenBody{B.cat8(l0, l1), body2}, r3)}, Done{(I.LenBody{len, body}, r1)}, e2)
  %el : Rule.Sx(Q.Rule{qri, _, op, fs, t}, r1, qri <> l1 <> l0 <> tail)
  %er3 : Rule.Sx(Q.Rule{qri, B.cat8(l0, l1), op, fs, t}, _, qri <> l1 <> l0 <> tail)
  sbw = Equal.sym(B.Bytes(), Q.Rule.body_write(op, fs, t), body, bw)
  %sbw : {qri <> B.write_u16(B.cat8(l0, l1), List.append(&2, U32, _, r3)) == qri <> l1 <> l0 <> tail : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  %eb : {qri <> B.write_u16(B.cat8(l0, l1), List.append(&2, U32, _, r3)) == qri <> l1 <> l0 <> tail : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, body2, r3), tail, ap)
  %sap : {qri <> B.write_u16(B.cat8(l0, l1), _) == qri <> l1 <> l0 <> tail : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  s16 = Equal.sym(B.Bytes(), B.write_u16(B.cat8(l0, l1), tail), l1 <> l0 <> tail, P.Bytes.u16_sx(l1, l0, m1, m0, tail))
  %s16 : {qri <> _ == qri <> l1 <> l0 <> tail : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  ({==}, al)

def Rule.sx_body(+qri: U32, +l1: U32, +l0: U32, +tail: B.Bytes(), +rule: Q.Rule, +r: B.Bytes(), +len: U32, +body: B.Bytes(), +r1: B.Bytes(), rb: Result<&2, &2, B.Err, Q.Rule>, erb: {Q.Rule.body(qri, len, body) == rb : Result<&2, &2, B.Err, Q.Rule>}, +e: {Q.Rule.cons(rb, r1) == Done{(rule, r)} : B.Read(Q.Rule)}, +body2: B.Bytes(), +r3: B.Bytes(), +e2: {Done{(I.LenBody{B.cat8(l0, l1), body2}, r3)} == Done{(I.LenBody{len, body}, r1)} : B.Read(I.LenBody)}, +ap: {List.append(&2, U32, body2, r3) == tail : B.Bytes()}, al: {B.all_bytes(r3) == True{} : Bool}, m1: {U32.and(255, l1) == l1 : U32}, m0: {U32.and(255, l0) == l0 : U32}, abt: {B.all_bytes(tail) == True{} : Bool}) -> Rule.Sx(rule, r, qri <> l1 <> l0 <> tail):
  match rb:
    case Fail{err}:
      Rule.absurd(rule, r, qri <> l1 <> l0 <> tail, err, e)
    case Done{+rule2}:
      eb = Equal.cong(I.LenBody, B.Bytes(), x => P.Lb.body(x), I.LenBody{B.cat8(l0, l1), body2}, I.LenBody{len, body}, Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, I.LenBody{len, body}), Done{(I.LenBody{B.cat8(l0, l1), body2}, r3)}, Done{(I.LenBody{len, body}, r1)}, e2))
      sap = Equal.sym(B.Bytes(), List.append(&2, U32, body2, r3), tail, ap)
      +abb : {B.all_bytes(body) == True{} : Bool} = (%eb : {B.all_bytes(_) == True{} : Bool}; Bytes.all_prefix(body2, r3, (%sap : {B.all_bytes(_) == True{} : Bool}; abt)))
      Rule.body_sx(Rule.Sx(rule, r, qri <> l1 <> l0 <> tail), qri, len, body, rule2, erb, abb, op => fs => t => eq => bw => Rule.sx_fin(qri, l1, l0, tail, rule, r, len, body, r1, rule2, op, fs, t, body2, r3, Equal.cong(B.Read(Q.Rule), Q.Rule, x => P.Read.value(Q.Rule, x, rule), Done{(rule2, r1)}, Done{(rule, r)}, e), eq, Equal.cong(B.Read(Q.Rule), B.Bytes(), x => P.Read.rest(Q.Rule, x, r), Done{(rule2, r1)}, Done{(rule, r)}, e), bw, e2, ap, al, m1, m0))

def Rule.sx_lve(+qri: U32, +l1: U32, +l0: U32, +tail: B.Bytes(), +rule: Q.Rule, +r: B.Bytes(), rl: B.Read(I.LenBody), erl: {I.Len.take(B.cat8(l0, l1), tail, B.fits16(B.cat8(l0, l1))) == rl : B.Read(I.LenBody)}, +e: {Q.Rule.len(qri, rl) == Done{(rule, r)} : B.Read(Q.Rule)}, m1: {U32.and(255, l1) == l1 : U32}, m0: {U32.and(255, l0) == l0 : U32}, +abt: {B.all_bytes(tail) == True{} : Bool}) -> Rule.Sx(rule, r, qri <> l1 <> l0 <> tail):
  match rl:
    case Fail{err}:
      Rule.absurd(rule, r, qri <> l1 <> l0 <> tail, err, e)
    case Done{(I.LenBody{+len, +body}, +r1)}:
      PM.Len.sx(Rule.Sx(rule, r, qri <> l1 <> l0 <> tail), B.cat8(l0, l1), tail, I.LenBody{len, body}, r1, B.fits16(B.cat8(l0, l1)), B.fits16(B.cat8(l0, l1)), {==}, erl, abt, f16 => body2 => r3 => e2 => ap => al => Rule.sx_body(qri, l1, l0, tail, rule, r, len, body, r1, Q.Rule.body(qri, len, body), {==}, e, body2, r3, e2, ap, al, m1, m0, abt))

def Rule.sx(bs: B.Bytes(), +rule: Q.Rule, +r: B.Bytes(), +e: {Q.Rule.read(bs) == Done{(rule, r)} : B.Read(Q.Rule)}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> Rule.Sx(rule, r, bs):
  match bs:
    case Nil{}:
      Rule.absurd(rule, r, [], B.Short{}, e)
    case qri <> Nil{}:
      Rule.absurd(rule, r, [qri], B.Short{}, e)
    case qri <> l1 <> Nil{}:
      Rule.absurd(rule, r, [qri, l1], B.Short{}, e)
    case +qri <> +l1 <> +l0 <> +tail:
      +ab1 = P.Bool.and_true_r(B.is_byte(qri), B.all_bytes(l1 <> l0 <> tail), ab)
      +ab0 = P.Bool.and_true_r(B.is_byte(l1), B.all_bytes(l0 <> tail), ab1)
      Rule.sx_lve(qri, l1, l0, tail, rule, r, I.Len.take(B.cat8(l0, l1), tail, B.fits16(B.cat8(l0, l1))), {==}, e, P.U32.lt256_mask8(l1, P.Bool.and_true_l(B.is_byte(l1), B.all_bytes(l0 <> tail), ab1)), P.U32.lt256_mask8(l0, P.Bool.and_true_l(B.is_byte(l0), B.all_bytes(tail), ab0)), P.Bool.and_true_r(B.is_byte(l0), B.all_bytes(tail), ab0))

def Rules.Res() -> Data:
  Result<&2, &2, B.Err, List<&2, Q.Rule>>

def Rules.absurd(+rs: List<&2, Q.Rule>, +bs: B.Bytes(), err: B.Err, e: {Fail{err} == Done{rs} : Rules.Res()}) -> {Q.Rules.write(rs) == bs : B.Bytes()}:
  Empty.absurd({Q.Rules.write(rs) == bs : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, Q.Rule>, err, rs, e))

def Rules.sx_cons(+f: Nat, +b: U32, +rest: B.Bytes(), +rule: Q.Rule, +r1: B.Bytes(), +rs: List<&2, Q.Rule>, ro: Rules.Res(), ero: {Q.Rules.go(f, r1) == ro : Rules.Res()}, +e: {B.Res.cons(Q.Rule, rule, ro) == Done{rs} : Rules.Res()}, s: Rule.Sx(rule, r1, b <> rest), ih: @rs2: List<&2, Q.Rule> -> {Q.Rules.go(f, r1) == Done{rs2} : Rules.Res()} -> {B.all_bytes(r1) == True{} : Bool} -> {Q.Rules.write(rs2) == r1 : B.Bytes()}) -> {Q.Rules.write(rs) == b <> rest : B.Bytes()}:
  match ro:
    case Fail{err}:
      Rules.absurd(rs, b <> rest, err, e)
    case Done{+rs2}:
      (w, a) = s
      ec = Equal.cong(Rules.Res(), List<&2, Q.Rule>, x => P.Res.value(B.Err, List<&2, Q.Rule>, x, rs), Done{rule <> rs2}, Done{rs}, e)
      %ec : {Q.Rules.write(_) == b <> rest : B.Bytes()}
      sw = Equal.sym(B.Bytes(), Q.Rules.write(rs2), r1, ih(rs2, ero, a))
      %sw : {Q.Rule.write(rule, _) == b <> rest : B.Bytes()}
      w

def Rules.sx_next(+f: Nat, +b: U32, +rest: B.Bytes(), +rs: List<&2, Q.Rule>, rr: B.Read(Q.Rule), err: {Q.Rule.read(b <> rest) == rr : B.Read(Q.Rule)}, +e: {Q.Rules.next(rr, left => Q.Rules.go(f, left)) == Done{rs} : Rules.Res()}, ab: {B.all_bytes(b <> rest) == True{} : Bool}, ih: @rs2: List<&2, Q.Rule> -> @r1: B.Bytes() -> {Q.Rules.go(f, r1) == Done{rs2} : Rules.Res()} -> {B.all_bytes(r1) == True{} : Bool} -> {Q.Rules.write(rs2) == r1 : B.Bytes()}) -> {Q.Rules.write(rs) == b <> rest : B.Bytes()}:
  match rr:
    case Fail{x}:
      Rules.absurd(rs, b <> rest, x, e)
    case Done{(+rule, +r1)}:
      Rules.sx_cons(f, b, rest, rule, r1, rs, Q.Rules.go(f, r1), {==}, e, Rule.sx(b <> rest, rule, r1, err, ab), rs2 => e2 => ab2 => ih(rs2, r1, e2, ab2))

def Rules.sx(fuel: Nat, bs: B.Bytes(), +rs: List<&2, Q.Rule>, +e: {Q.Rules.go(fuel, bs) == Done{rs} : Rules.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> {Q.Rules.write(rs) == bs : B.Bytes()}:
  match fuel bs:
    case 0n Nil{}:
      ec = Equal.cong(Rules.Res(), List<&2, Q.Rule>, x => P.Res.value(B.Err, List<&2, Q.Rule>, x, rs), Done{[]}, Done{rs}, e)
      %ec : {Q.Rules.write(_) == [] : B.Bytes()}
      {==}
    case 1n+f Nil{}:
      ec = Equal.cong(Rules.Res(), List<&2, Q.Rule>, x => P.Res.value(B.Err, List<&2, Q.Rule>, x, rs), Done{[]}, Done{rs}, e)
      %ec : {Q.Rules.write(_) == [] : B.Bytes()}
      {==}
    case 0n +b <> +rest:
      Rules.absurd(rs, b <> rest, B.Invalid{b}, e)
    case 1n++f +b <> +rest:
      Rules.sx_next(f, b, rest, rs, Q.Rule.read(b <> rest), {==}, e, ab, rs2 => r1 => e2 => ab2 => Rules.sx(f, r1, rs2, e2, ab2))

def L.nas.qos_rules.suffix(bs, rs, e, ab):
  Rules.sx(List.length(&2, U32, bs), bs, rs, e, ab)
