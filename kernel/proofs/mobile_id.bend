import Base
import ../LAWS.bend as L
import ../bytes.bend as B
import ../plmn.bend as PL
import ../suci.bend as Su
import ../nas/ie.bend as I
import ../nas/mobile_id.bend as Mi
import ./lib.bend as P
import ./bytes.bend as PB
import ./plmn.bend as PP

# Proofs of the mobile identity and payload container laws (ticket 10).

def Tbcd.Res() -> Data:
  Result<&2, &2, B.Err, B.Digits()>

def Id.Res() -> Data:
  Result<&2, &2, B.Err, Mi.MobileId>

# TBCD digits write back to the bytes they were read from
# ------------------------------------------------------

def Tbcd.sx_filler(+b: U32, rest: B.Bytes(), +ds: B.Digits(), +e: {B.Tbcd.filler(U32.and(15, b), rest) == Done{ds} : Tbcd.Res()}, m8: {U32.and(255, b) == b : U32}, hf: {U32.and(15, U32.shrn(b, 4n)) == 15 : U32}) -> {B.write_tbcd(ds, []) == b <> rest : B.Bytes()}:
  match rest:
    case Nil{}:
      ed = Equal.cong(Tbcd.Res(), B.Digits(), x => P.Res.value(B.Err, B.Digits(), x, ds), Done{[U32.and(15, b)]}, Done{ds}, e)
      %ed : {B.write_tbcd(_, []) == [b] : B.Bytes()}
      f15 = Equal.cong(U32, U32, x => U32.and(15, x), U32.and(15, U32.shrn(b, 4n)), 15, hf)
      %f15 : {B.cat4(U32.and(15, b), _) <> [] == [b] : B.Bytes()}
      nj = Equal.sym(U32, B.cat4(U32.and(15, b), U32.and(15, U32.and(15, U32.shrn(b, 4n)))), b, P.U32.nibbles_join(b, m8))
      %nj : {_ <> [] == [b] : B.Bytes()}
      {==}
    case x <> more:
      Empty.absurd({B.write_tbcd(ds, []) == b <> x <> more : B.Bytes()}, P.Refute.fail_done(B.Err, B.Digits(), B.Invalid{15}, ds, e))

def Tbcd.sx_cons2(+b: U32, +rest: B.Bytes(), +ds: B.Digits(), r: Tbcd.Res(), er: {B.Tbcd.decode(rest) == r : Tbcd.Res()}, +e: {B.Tbcd.cons2(U32.and(15, b), U32.and(15, U32.shrn(b, 4n)), r) == Done{ds} : Tbcd.Res()}, m8: {U32.and(255, b) == b : U32}, ih: @ds2: B.Digits() -> {B.Tbcd.decode(rest) == Done{ds2} : Tbcd.Res()} -> {B.write_tbcd(ds2, []) == rest : B.Bytes()}) -> {B.write_tbcd(ds, []) == b <> rest : B.Bytes()}:
  match r:
    case Fail{err}:
      Empty.absurd({B.write_tbcd(ds, []) == b <> rest : B.Bytes()}, P.Refute.fail_done(B.Err, B.Digits(), err, ds, e))
    case Done{+ds2}:
      ed = Equal.cong(Tbcd.Res(), B.Digits(), x => P.Res.value(B.Err, B.Digits(), x, ds), Done{U32.and(15, b) <> U32.and(15, U32.shrn(b, 4n)) <> ds2}, Done{ds}, e)
      %ed : {B.write_tbcd(_, []) == b <> rest : B.Bytes()}
      sih = Equal.sym(B.Bytes(), B.write_tbcd(ds2, []), rest, ih(ds2, er))
      %sih : {B.cat4(U32.and(15, b), U32.and(15, U32.and(15, U32.shrn(b, 4n)))) <> _ == b <> rest : B.Bytes()}
      nj = Equal.sym(U32, B.cat4(U32.and(15, b), U32.and(15, U32.and(15, U32.shrn(b, 4n)))), b, P.U32.nibbles_join(b, m8))
      %nj : {_ <> rest == b <> rest : B.Bytes()}
      {==}

def Tbcd.sx_high(+b: U32, +rest: B.Bytes(), +ds: B.Digits(), dg: Bool, fl: Bool, efl: {U32.is_eq(U32.and(15, U32.shrn(b, 4n)), 15) == fl : Bool}, +e: {B.Tbcd.high(U32.and(15, b), U32.and(15, U32.shrn(b, 4n)), rest, u => B.Tbcd.decode(rest), dg, fl) == Done{ds} : Tbcd.Res()}, m8: {U32.and(255, b) == b : U32}, ih: @ds2: B.Digits() -> {B.Tbcd.decode(rest) == Done{ds2} : Tbcd.Res()} -> {B.write_tbcd(ds2, []) == rest : B.Bytes()}) -> {B.write_tbcd(ds, []) == b <> rest : B.Bytes()}:
  match dg:
    case True{}:
      Tbcd.sx_cons2(b, rest, ds, B.Tbcd.decode(rest), {==}, e, m8, ih)
    case False{}:
      match fl:
        case True{}:
          Tbcd.sx_filler(b, rest, ds, e, m8, P.U32.eq_of_is_eq(U32.and(15, U32.shrn(b, 4n)), 15, efl))
        case False{}:
          Empty.absurd({B.write_tbcd(ds, []) == b <> rest : B.Bytes()}, P.Refute.fail_done(B.Err, B.Digits(), B.Invalid{U32.and(15, U32.shrn(b, 4n))}, ds, e))

def Tbcd.sx_low(+b: U32, +rest: B.Bytes(), +ds: B.Digits(), dg: Bool, +e: {B.Tbcd.low(U32.and(15, b), U32.and(15, U32.shrn(b, 4n)), rest, u => B.Tbcd.decode(rest), dg) == Done{ds} : Tbcd.Res()}, m8: {U32.and(255, b) == b : U32}, ih: @ds2: B.Digits() -> {B.Tbcd.decode(rest) == Done{ds2} : Tbcd.Res()} -> {B.write_tbcd(ds2, []) == rest : B.Bytes()}) -> {B.write_tbcd(ds, []) == b <> rest : B.Bytes()}:
  match dg:
    case True{}:
      Tbcd.sx_high(b, rest, ds, B.Tbcd.is_digit(U32.and(15, U32.shrn(b, 4n))), U32.is_eq(U32.and(15, U32.shrn(b, 4n)), 15), {==}, e, m8, ih)
    case False{}:
      Empty.absurd({B.write_tbcd(ds, []) == b <> rest : B.Bytes()}, P.Refute.fail_done(B.Err, B.Digits(), B.Invalid{U32.and(15, b)}, ds, e))

def Tbcd.sx(bs: B.Bytes(), +ds: B.Digits(), +e: {B.Tbcd.decode(bs) == Done{ds} : Tbcd.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> {B.write_tbcd(ds, []) == bs : B.Bytes()}:
  match bs:
    case Nil{}:
      ed = Equal.cong(Tbcd.Res(), B.Digits(), x => P.Res.value(B.Err, B.Digits(), x, ds), Done{[]}, Done{ds}, e)
      %ed : {B.write_tbcd(_, []) == [] : B.Bytes()}
      {==}
    case +b <> +rest:
      Tbcd.sx_low(b, rest, ds, B.Tbcd.is_digit(U32.and(15, b)), e, P.U32.lt256_mask8(b, P.Bool.and_true_l(B.is_byte(b), B.all_bytes(rest), ab)), ds2 => e2 => Tbcd.sx(rest, ds2, e2, P.Bool.and_true_r(B.is_byte(b), B.all_bytes(rest), ab)))

# A PLMN writes back to its three bytes
# -------------------------------------

def Plmn.sx_check(+x: U32, +y: U32, +z: U32, +t: B.Bytes(), +p: PL.Plmn, +rest: B.Bytes(), ok: Bool, +e: {PL.Plmn.check(PL.Plmn{U32.and(15, x), U32.and(15, U32.shrn(x, 4n)), U32.and(15, y), U32.and(15, z), U32.and(15, U32.shrn(z, 4n)), U32.and(15, U32.shrn(y, 4n))}, t, ok) == Done{(p, rest)} : B.Read(PL.Plmn)}, mx: {U32.and(255, x) == x : U32}, my: {U32.and(255, y) == y : U32}, mz: {U32.and(255, z) == z : U32}) -> {PL.Plmn.write(p, rest) == x <> y <> z <> t : B.Bytes()}:
  match ok:
    case False{}:
      Empty.absurd({PL.Plmn.write(p, rest) == x <> y <> z <> t : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(PL.Plmn), B.Invalid{1}, (p, rest), e))
    case True{}:
      ep = Equal.cong(B.Read(PL.Plmn), PL.Plmn, w => P.Read.value(PL.Plmn, w, p), Done{(PL.Plmn{U32.and(15, x), U32.and(15, U32.shrn(x, 4n)), U32.and(15, y), U32.and(15, z), U32.and(15, U32.shrn(z, 4n)), U32.and(15, U32.shrn(y, 4n))}, t)}, Done{(p, rest)}, e)
      er = Equal.cong(B.Read(PL.Plmn), B.Bytes(), w => P.Read.rest(PL.Plmn, w, rest), Done{(PL.Plmn{U32.and(15, x), U32.and(15, U32.shrn(x, 4n)), U32.and(15, y), U32.and(15, z), U32.and(15, U32.shrn(z, 4n)), U32.and(15, U32.shrn(y, 4n))}, t)}, Done{(p, rest)}, e)
      %ep : {PL.Plmn.write(_, rest) == x <> y <> z <> t : B.Bytes()}
      %er : {PL.Plmn.write(PL.Plmn{U32.and(15, x), U32.and(15, U32.shrn(x, 4n)), U32.and(15, y), U32.and(15, z), U32.and(15, U32.shrn(z, 4n)), U32.and(15, U32.shrn(y, 4n))}, _) == x <> y <> z <> t : B.Bytes()}
      jx = Equal.sym(U32, B.cat4(U32.and(15, x), U32.and(15, U32.and(15, U32.shrn(x, 4n)))), x, P.U32.nibbles_join(x, mx))
      jy = Equal.sym(U32, B.cat4(U32.and(15, y), U32.and(15, U32.and(15, U32.shrn(y, 4n)))), y, P.U32.nibbles_join(y, my))
      jz = Equal.sym(U32, B.cat4(U32.and(15, z), U32.and(15, U32.and(15, U32.shrn(z, 4n)))), z, P.U32.nibbles_join(z, mz))
      %jx : {_ <> B.cat4(U32.and(15, y), U32.and(15, U32.and(15, U32.shrn(y, 4n)))) <> B.cat4(U32.and(15, z), U32.and(15, U32.and(15, U32.shrn(z, 4n)))) <> t == x <> y <> z <> t : B.Bytes()}
      %jy : {x <> _ <> B.cat4(U32.and(15, z), U32.and(15, U32.and(15, U32.shrn(z, 4n)))) <> t == x <> y <> z <> t : B.Bytes()}
      %jz : {x <> y <> _ <> t == x <> y <> z <> t : B.Bytes()}
      {==}

def Plmn.sx(bs: B.Bytes(), +p: PL.Plmn, +rest: B.Bytes(), +e: {PL.Plmn.read(bs) == Done{(p, rest)} : B.Read(PL.Plmn)}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> {PL.Plmn.write(p, rest) == bs : B.Bytes()}:
  match bs:
    case Nil{}:
      Empty.absurd({PL.Plmn.write(p, rest) == [] : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(PL.Plmn), B.Short{}, (p, rest), e))
    case x <> Nil{}:
      Empty.absurd({PL.Plmn.write(p, rest) == [x] : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(PL.Plmn), B.Short{}, (p, rest), e))
    case x <> y <> Nil{}:
      Empty.absurd({PL.Plmn.write(p, rest) == [x, y] : B.Bytes()}, P.Refute.fail_done(B.Err, B.ReadValue(PL.Plmn), B.Short{}, (p, rest), e))
    case +x <> +y <> +z <> +t:
      +aby = P.Bool.and_true_r(B.is_byte(x), B.all_bytes(y <> z <> t), ab)
      Plmn.sx_check(x, y, z, t, p, rest, PL.Plmn.valid(PL.Plmn{U32.and(15, x), U32.and(15, U32.shrn(x, 4n)), U32.and(15, y), U32.and(15, z), U32.and(15, U32.shrn(z, 4n)), U32.and(15, U32.shrn(y, 4n))}), e, P.U32.lt256_mask8(x, P.Bool.and_true_l(B.is_byte(x), B.all_bytes(y <> z <> t), ab)), P.U32.lt256_mask8(y, P.Bool.and_true_l(B.is_byte(y), B.all_bytes(z <> t), aby)), P.U32.lt256_mask8(z, P.Bool.and_true_l(B.is_byte(z), B.all_bytes(t), P.Bool.and_true_r(B.is_byte(y), B.all_bytes(z <> t), aby))))

# The routing indicator writes back to its two bytes
# --------------------------------------------------

def Routing.fills(k: Nat) -> B.Bytes():
  match k:
    case 0n:
      []
    case 1n+p:
      15 <> Routing.fills(p)

def Routing.FillInv(ns: B.Bytes(), ds: B.Digits()) -> Type:
  {ds == [] : B.Digits()} & {ns == Routing.fills(List.length(&2, U32, ns)) : B.Bytes()}

def Routing.fill_fin(+n: U32, +rest: B.Bytes(), +ds: B.Digits(), n15: {n == 15 : U32}, inv: Routing.FillInv(rest, ds)) -> Routing.FillInv(n <> rest, ds):
  (d0, r0) = inv
  (d0, P.List.cons_eq(n, 15, rest, Routing.fills(List.length(&2, U32, rest)), n15, r0))

def Routing.fill_step(+n: U32, +rest: B.Bytes(), +ds: B.Digits(), ok: Bool, ev: {U32.is_eq(n, 15) == ok : Bool}, +e: {Su.Routing.filler(n, u => Su.Routing.fillers(rest), ok) == Done{ds} : Tbcd.Res()}, ih: @ds2: B.Digits() -> {Su.Routing.fillers(rest) == Done{ds2} : Tbcd.Res()} -> Routing.FillInv(rest, ds2)) -> Routing.FillInv(n <> rest, ds):
  match ok:
    case False{}:
      Empty.absurd(Routing.FillInv(n <> rest, ds), P.Refute.fail_done(B.Err, B.Digits(), B.Invalid{n}, ds, e))
    case True{}:
      Routing.fill_fin(n, rest, ds, P.U32.eq_of_is_eq(n, 15, ev), ih(ds, e))

def Routing.fill_inv(ns: B.Bytes(), +ds: B.Digits(), +e: {Su.Routing.fillers(ns) == Done{ds} : Tbcd.Res()}) -> Routing.FillInv(ns, ds):
  match ns:
    case Nil{}:
      ed = Equal.cong(Tbcd.Res(), B.Digits(), x => P.Res.value(B.Err, B.Digits(), x, ds), Done{[]}, Done{ds}, e)
      (Equal.sym(B.Digits(), [], ds, ed), {==})
    case +n <> +rest:
      Routing.fill_step(n, rest, ds, U32.is_eq(n, 15), {==}, e, ds2 => e2 => Routing.fill_inv(rest, ds2, e2))

# The digits read are the nibbles up to the first filler, and only fillers follow.
def Routing.DigInv(ns: B.Bytes(), ds: B.Digits()) -> Type:
  {List.append(&2, U32, ds, Routing.fills(Nat.sub(List.length(&2, U32, ns), List.length(&2, U32, ds)))) == ns : B.Bytes()} & ({B.Tbcd.all_digits(ds) == True{} : Bool} & {Nat.is_le(List.length(&2, U32, ds), List.length(&2, U32, ns)) == True{} : Bool})

def Routing.dig_fill(+n: U32, +rest: B.Bytes(), +ds: B.Digits(), n15: {n == 15 : U32}, inv: Routing.FillInv(rest, ds)) -> Routing.DigInv(n <> rest, ds):
  (d0, r0) = inv
  sd = Equal.sym(B.Digits(), ds, [], d0)
  %sd : Routing.DigInv(n <> rest, _)
  (P.List.cons_eq(15, n, Routing.fills(List.length(&2, U32, rest)), rest, Equal.sym(U32, n, 15, n15), Equal.sym(B.Bytes(), rest, Routing.fills(List.length(&2, U32, rest)), r0)), ({==}, {==}))

def Routing.dig_cons_fin(+n: U32, +rest: B.Bytes(), +ds2: B.Digits(), dgn: {B.Tbcd.is_digit(n) == True{} : Bool}, inv: Routing.DigInv(rest, ds2)) -> Routing.DigInv(n <> rest, n <> ds2):
  (a0, t0) = inv
  (dg0, le0) = t0
  (P.List.cons_eq(n, n, List.append(&2, U32, ds2, Routing.fills(Nat.sub(List.length(&2, U32, rest), List.length(&2, U32, ds2)))), rest, {==}, a0), (P.Bool.and_intro(B.Tbcd.is_digit(n), B.Tbcd.all_digits(ds2), dgn, dg0), le0))

def Routing.dig_cons(+n: U32, +rest: B.Bytes(), +ds: B.Digits(), r: Tbcd.Res(), er: {Su.Routing.digits(rest) == r : Tbcd.Res()}, +e: {Su.Routing.cons(n, r) == Done{ds} : Tbcd.Res()}, dgn: {B.Tbcd.is_digit(n) == True{} : Bool}, ih: @ds2: B.Digits() -> {Su.Routing.digits(rest) == Done{ds2} : Tbcd.Res()} -> Routing.DigInv(rest, ds2)) -> Routing.DigInv(n <> rest, ds):
  match r:
    case Fail{err}:
      Empty.absurd(Routing.DigInv(n <> rest, ds), P.Refute.fail_done(B.Err, B.Digits(), err, ds, e))
    case Done{+ds2}:
      ed = Equal.cong(Tbcd.Res(), B.Digits(), x => P.Res.value(B.Err, B.Digits(), x, ds), Done{n <> ds2}, Done{ds}, e)
      %ed : Routing.DigInv(n <> rest, _)
      Routing.dig_cons_fin(n, rest, ds2, dgn, ih(ds2, er))

def Routing.dig_step(+n: U32, +rest: B.Bytes(), +ds: B.Digits(), dg: Bool, fl: Bool, edg: {B.Tbcd.is_digit(n) == dg : Bool}, efl: {U32.is_eq(n, 15) == fl : Bool}, +e: {Su.Routing.step(n, rest, u => Su.Routing.digits(rest), dg, fl) == Done{ds} : Tbcd.Res()}, ih: @ds2: B.Digits() -> {Su.Routing.digits(rest) == Done{ds2} : Tbcd.Res()} -> Routing.DigInv(rest, ds2)) -> Routing.DigInv(n <> rest, ds):
  match dg:
    case True{}:
      Routing.dig_cons(n, rest, ds, Su.Routing.digits(rest), {==}, e, edg, ih)
    case False{}:
      match fl:
        case True{}:
          Routing.dig_fill(n, rest, ds, P.U32.eq_of_is_eq(n, 15, efl), Routing.fill_inv(rest, ds, e))
        case False{}:
          Empty.absurd(Routing.DigInv(n <> rest, ds), P.Refute.fail_done(B.Err, B.Digits(), B.Invalid{n}, ds, e))

def Routing.dig_inv(ns: B.Bytes(), +ds: B.Digits(), +e: {Su.Routing.digits(ns) == Done{ds} : Tbcd.Res()}) -> Routing.DigInv(ns, ds):
  match ns:
    case Nil{}:
      ed = Equal.cong(Tbcd.Res(), B.Digits(), x => P.Res.value(B.Err, B.Digits(), x, ds), Done{[]}, Done{ds}, e)
      %ed : Routing.DigInv([], _)
      ({==}, ({==}, {==}))
    case +n <> +rest:
      Routing.dig_step(n, rest, ds, B.Tbcd.is_digit(n), U32.is_eq(n, 15), {==}, {==}, e, ds2 => e2 => Routing.dig_inv(rest, ds2, e2))

def Routing.ne_inv(r: Tbcd.Res(), +ds: B.Digits(), +e: {Su.Routing.nonempty(r) == Done{ds} : Tbcd.Res()}) -> {r == Done{ds} : Tbcd.Res()} & P.List.nonnil(ds):
  match r:
    case Fail{err}:
      Empty.absurd({Fail{err} == Done{ds} : Tbcd.Res()} & P.List.nonnil(ds), P.Refute.fail_done(B.Err, B.Digits(), err, ds, e))
    case Done{Nil{}}:
      Empty.absurd({Done{[]} == Done{ds} : Tbcd.Res()} & P.List.nonnil(ds), P.Refute.fail_done(B.Err, B.Digits(), B.Invalid{15}, ds, e))
    case Done{d <> t}:
      ed = Equal.cong(Tbcd.Res(), B.Digits(), x => P.Res.value(B.Err, B.Digits(), x, ds), Done{d <> t}, Done{ds}, e)
      (e, (%ed : P.List.nonnil(_); Unit{}))

def Routing.Inv(b0: U32, b1: U32, ds: B.Digits()) -> Type:
  {Su.Routing.pad4(ds) == [U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, U32.shrn(b1, 4n))] : B.Bytes()} & {Su.Routing.valid(ds) == True{} : Bool}

def Routing.inv4(+n1: U32, +n2: U32, +n3: U32, +n4: U32, ds: B.Digits(), inv: Routing.DigInv([n1, n2, n3, n4], ds), nn: P.List.nonnil(ds)) -> {Su.Routing.pad4(ds) == [n1, n2, n3, n4] : B.Bytes()} & {Su.Routing.valid(ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({Su.Routing.pad4([]) == [n1, n2, n3, n4] : B.Bytes()} & {Su.Routing.valid([]) == True{} : Bool}, nn)
    case a <> Nil{}:
      (a0, t0) = inv
      (dg0, le0) = t0
      (a0, dg0)
    case a <> b <> Nil{}:
      (a0, t0) = inv
      (dg0, le0) = t0
      (a0, dg0)
    case a <> b <> c <> Nil{}:
      (a0, t0) = inv
      (dg0, le0) = t0
      (a0, dg0)
    case a <> b <> c <> d <> Nil{}:
      (a0, t0) = inv
      (dg0, le0) = t0
      (a0, dg0)
    case a <> b <> c <> d <> x <> more:
      (a0, t0) = inv
      (dg0, le0) = t0
      Empty.absurd({Su.Routing.pad4(a <> b <> c <> d <> x <> more) == [n1, n2, n3, n4] : B.Bytes()} & {Su.Routing.valid(a <> b <> c <> d <> x <> more) == True{} : Bool}, P.Refute.bool(le0))

def Routing.inv_ne(+b0: U32, +b1: U32, +ds: B.Digits(), pr: {Su.Routing.digits([U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, U32.shrn(b1, 4n))]) == Done{ds} : Tbcd.Res()} & P.List.nonnil(ds)) -> Routing.Inv(b0, b1, ds):
  (ed, nn) = pr
  Routing.inv4(U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, U32.shrn(b1, 4n)), ds, Routing.dig_inv([U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, U32.shrn(b1, 4n))], ds, ed), nn)

def Routing.inv(+b0: U32, +b1: U32, +ds: B.Digits(), +e: {Su.Routing.read(b0, b1) == Done{ds} : Tbcd.Res()}) -> Routing.Inv(b0, b1, ds):
  Routing.inv_ne(b0, b1, ds, Routing.ne_inv(Su.Routing.digits([U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, U32.shrn(b1, 4n))]), ds, e))

def Routing.sx_fin(+b0: U32, +b1: U32, +ds: B.Digits(), +R: B.Bytes(), inv: Routing.Inv(b0, b1, ds), m0: {U32.and(255, b0) == b0 : U32}, m1: {U32.and(255, b1) == b1 : U32}) -> {Su.Routing.write(ds, R) == b0 <> b1 <> R : B.Bytes()}:
  (pd, v) = inv
  spd = Equal.sym(B.Bytes(), Su.Routing.pad4(ds), [U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, U32.shrn(b1, 4n))], pd)
  %spd : {Su.Routing.write4(_, R) == b0 <> b1 <> R : B.Bytes()}
  j0 = Equal.sym(U32, B.cat4(U32.and(15, b0), U32.and(15, U32.and(15, U32.shrn(b0, 4n)))), b0, P.U32.nibbles_join(b0, m0))
  %j0 : {_ <> B.cat4(U32.and(15, b1), U32.and(15, U32.and(15, U32.shrn(b1, 4n)))) <> R == b0 <> b1 <> R : B.Bytes()}
  j1 = Equal.sym(U32, B.cat4(U32.and(15, b1), U32.and(15, U32.and(15, U32.shrn(b1, 4n)))), b1, P.U32.nibbles_join(b1, m1))
  %j1 : {b0 <> _ <> R == b0 <> b1 <> R : B.Bytes()}
  {==}

def Routing.sx(+b0: U32, +b1: U32, +ds: B.Digits(), +R: B.Bytes(), +e: {Su.Routing.read(b0, b1) == Done{ds} : Tbcd.Res()}, m0: {U32.and(255, b0) == b0 : U32}, m1: {U32.and(255, b1) == b1 : U32}) -> {Su.Routing.write(ds, R) == b0 <> b1 <> R : B.Bytes()}:
  Routing.sx_fin(b0, b1, ds, R, Routing.inv(b0, b1, ds, e), m0, m1)

# A SUCI writes back to its bytes
# -------------------------------

def Suci.Res() -> Data:
  Result<&2, &2, B.Err, Su.Suci>

def Plmn.tail_bytes(plmn: PL.Plmn, +X: B.Bytes(), +rest: B.Bytes(), +wp: {PL.Plmn.write(plmn, X) == rest : B.Bytes()}, ab: {B.all_bytes(rest) == True{} : Bool}) -> {B.all_bytes(X) == True{} : Bool}:
  match plmn:
    case PL.Plmn{+a, +b, +c, +d, +e, +f}:
      swp = Equal.sym(B.Bytes(), PL.Plmn.write(PL.Plmn{a, b, c, d, e, f}, X), rest, wp)
      +abw : {B.all_bytes(PL.Plmn.write(PL.Plmn{a, b, c, d, e, f}, X)) == True{} : Bool} = (%swp : {B.all_bytes(_) == True{} : Bool}; ab)
      P.Bool.and_true_r(B.is_byte(B.cat4(d, U32.and(15, e))), B.all_bytes(X), P.Bool.and_true_r(B.is_byte(B.cat4(c, U32.and(15, f))), Bool.and(B.is_byte(B.cat4(d, U32.and(15, e))), B.all_bytes(X)), P.Bool.and_true_r(B.is_byte(B.cat4(a, U32.and(15, b))), Bool.and(B.is_byte(B.cat4(c, U32.and(15, f))), Bool.and(B.is_byte(B.cat4(d, U32.and(15, e))), B.all_bytes(X))), abw)))

def Suci.sx_fin(+h: U32, +rest: B.Bytes(), +plmn: PL.Plmn, +routing: B.Digits(), +b0: U32, +b1: U32, +sc: U32, +key: U32, +output: B.Bytes(), +s: Su.Suci, eh: {h == 1 : U32}, es: {Su.Suci{plmn, routing, sc, key, output} == s : Su.Suci}, wp: {PL.Plmn.write(plmn, b0 <> b1 <> sc <> key <> output) == rest : B.Bytes()}, wr: {Su.Routing.write(routing, sc <> key <> output) == b0 <> b1 <> sc <> key <> output : B.Bytes()}, msc: {U32.and(255, sc) == sc : U32}, mk: {U32.and(255, key) == key : U32}) -> {Su.Suci.write(s) == h <> rest : B.Bytes()}:
  %es : {Su.Suci.write(_) == h <> rest : B.Bytes()}
  sh = Equal.sym(U32, h, 1, eh)
  %sh : {Su.Suci.write(Su.Suci{plmn, routing, sc, key, output}) == _ <> rest : B.Bytes()}
  ssc = Equal.sym(U32, U32.and(255, sc), sc, msc)
  %ssc : {1 <> PL.Plmn.write(plmn, Su.Routing.write(routing, _ <> U32.and(255, key) <> output)) == 1 <> rest : B.Bytes()}
  sk = Equal.sym(U32, U32.and(255, key), key, mk)
  %sk : {1 <> PL.Plmn.write(plmn, Su.Routing.write(routing, sc <> _ <> output)) == 1 <> rest : B.Bytes()}
  swr = Equal.sym(B.Bytes(), Su.Routing.write(routing, sc <> key <> output), b0 <> b1 <> sc <> key <> output, wr)
  %swr : {1 <> PL.Plmn.write(plmn, _) == 1 <> rest : B.Bytes()}
  swp = Equal.sym(B.Bytes(), PL.Plmn.write(plmn, b0 <> b1 <> sc <> key <> output), rest, wp)
  %swp : {1 <> _ == 1 <> rest : B.Bytes()}
  {==}

def Suci.sx_key(+h: U32, +rest: B.Bytes(), +plmn: PL.Plmn, +routing: B.Digits(), +b0: U32, +b1: U32, +sc: U32, rest3: B.Bytes(), +s: Su.Suci, +e: {Su.Suci.r_key(plmn, routing, sc, B.u8(rest3)) == Done{s} : Suci.Res()}, eh: {h == 1 : U32}, wp: {PL.Plmn.write(plmn, b0 <> b1 <> sc <> rest3) == rest : B.Bytes()}, wr: {Su.Routing.write(routing, sc <> rest3) == b0 <> b1 <> sc <> rest3 : B.Bytes()}, msc: {U32.and(255, sc) == sc : U32}, ab3: {B.all_bytes(rest3) == True{} : Bool}) -> {Su.Suci.write(s) == h <> rest : B.Bytes()}:
  match rest3:
    case Nil{}:
      Empty.absurd({Su.Suci.write(s) == h <> rest : B.Bytes()}, P.Refute.fail_done(B.Err, Su.Suci, B.Short{}, s, e))
    case +key <> +output:
      Suci.sx_fin(h, rest, plmn, routing, b0, b1, sc, key, output, s, eh, Equal.cong(Suci.Res(), Su.Suci, x => P.Res.value(B.Err, Su.Suci, x, s), Done{Su.Suci{plmn, routing, sc, key, output}}, Done{s}, e), wp, wr, msc, P.U32.lt256_mask8(key, P.Bool.and_true_l(B.is_byte(key), B.all_bytes(output), ab3)))

def Suci.sx_scheme(+h: U32, +rest: B.Bytes(), +plmn: PL.Plmn, +routing: B.Digits(), +b0: U32, +b1: U32, rest2: B.Bytes(), +s: Su.Suci, +e: {Su.Suci.r_scheme(plmn, routing, B.u8(rest2)) == Done{s} : Suci.Res()}, eh: {h == 1 : U32}, wp: {PL.Plmn.write(plmn, b0 <> b1 <> rest2) == rest : B.Bytes()}, wr: {Su.Routing.write(routing, rest2) == b0 <> b1 <> rest2 : B.Bytes()}, +ab2: {B.all_bytes(rest2) == True{} : Bool}) -> {Su.Suci.write(s) == h <> rest : B.Bytes()}:
  match rest2:
    case Nil{}:
      Empty.absurd({Su.Suci.write(s) == h <> rest : B.Bytes()}, P.Refute.fail_done(B.Err, Su.Suci, B.Short{}, s, e))
    case +sc <> +rest3:
      Suci.sx_key(h, rest, plmn, routing, b0, b1, sc, rest3, s, e, eh, wp, wr, P.U32.lt256_mask8(sc, P.Bool.and_true_l(B.is_byte(sc), B.all_bytes(rest3), ab2)), P.Bool.and_true_r(B.is_byte(sc), B.all_bytes(rest3), ab2))

def Suci.sx_routing(+h: U32, +rest: B.Bytes(), +plmn: PL.Plmn, +b0: U32, +b1: U32, +rest2: B.Bytes(), +s: Su.Suci, rr: Tbcd.Res(), err: {Su.Routing.read(b0, b1) == rr : Tbcd.Res()}, +e: {Su.Suci.r_routing(plmn, rr, rest2) == Done{s} : Suci.Res()}, eh: {h == 1 : U32}, wp: {PL.Plmn.write(plmn, b0 <> b1 <> rest2) == rest : B.Bytes()}, m0: {U32.and(255, b0) == b0 : U32}, m1: {U32.and(255, b1) == b1 : U32}, ab2: {B.all_bytes(rest2) == True{} : Bool}) -> {Su.Suci.write(s) == h <> rest : B.Bytes()}:
  match rr:
    case Fail{x}:
      Empty.absurd({Su.Suci.write(s) == h <> rest : B.Bytes()}, P.Refute.fail_done(B.Err, Su.Suci, x, s, e))
    case Done{+routing}:
      Suci.sx_scheme(h, rest, plmn, routing, b0, b1, rest2, s, e, eh, wp, Routing.sx(b0, b1, routing, rest2, err, m0, m1), ab2)

def Suci.sx_plmn(+h: U32, +rest: B.Bytes(), +s: Su.Suci, rp: B.Read(PL.Plmn), erp: {PL.Plmn.read(rest) == rp : B.Read(PL.Plmn)}, +e: {Su.Suci.r_plmn(rp) == Done{s} : Suci.Res()}, eh: {h == 1 : U32}, +ab: {B.all_bytes(rest) == True{} : Bool}) -> {Su.Suci.write(s) == h <> rest : B.Bytes()}:
  match rp:
    case Fail{x}:
      Empty.absurd({Su.Suci.write(s) == h <> rest : B.Bytes()}, P.Refute.fail_done(B.Err, Su.Suci, x, s, e))
    case Done{(plmn, Nil{})}:
      Empty.absurd({Su.Suci.write(s) == h <> rest : B.Bytes()}, P.Refute.fail_done(B.Err, Su.Suci, B.Short{}, s, e))
    case Done{(plmn, b0 <> Nil{})}:
      Empty.absurd({Su.Suci.write(s) == h <> rest : B.Bytes()}, P.Refute.fail_done(B.Err, Su.Suci, B.Short{}, s, e))
    case Done{(+plmn, +b0 <> +b1 <> +rest2)}:
      +wp = Plmn.sx(rest, plmn, b0 <> b1 <> rest2, erp, ab)
      +abt = Plmn.tail_bytes(plmn, b0 <> b1 <> rest2, rest, wp, ab)
      +ab1 = P.Bool.and_true_r(B.is_byte(b0), B.all_bytes(b1 <> rest2), abt)
      Suci.sx_routing(h, rest, plmn, b0, b1, rest2, s, Su.Routing.read(b0, b1), {==}, e, eh, wp, P.U32.lt256_mask8(b0, P.Bool.and_true_l(B.is_byte(b0), B.all_bytes(b1 <> rest2), abt)), P.U32.lt256_mask8(b1, P.Bool.and_true_l(B.is_byte(b1), B.all_bytes(rest2), ab1)), P.Bool.and_true_r(B.is_byte(b1), B.all_bytes(rest2), ab1))

def Suci.sx_type(+h: U32, +rest: B.Bytes(), +s: Su.Suci, ok: Bool, ev: {U32.is_eq(h, Su.Suci.header()) == ok : Bool}, +e: {Su.Suci.r_type(h, rest, ok) == Done{s} : Suci.Res()}, +ab: {B.all_bytes(rest) == True{} : Bool}) -> {Su.Suci.write(s) == h <> rest : B.Bytes()}:
  match ok:
    case False{}:
      Empty.absurd({Su.Suci.write(s) == h <> rest : B.Bytes()}, P.Refute.fail_done(B.Err, Su.Suci, B.Unsupported{h}, s, e))
    case True{}:
      Suci.sx_plmn(h, rest, s, PL.Plmn.read(rest), {==}, e, P.U32.eq_of_is_eq(h, 1, ev), ab)

def Suci.sx(bs: B.Bytes(), +s: Su.Suci, +e: {Su.Suci.read(bs) == Done{s} : Suci.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> {Su.Suci.write(s) == bs : B.Bytes()}:
  match bs:
    case Nil{}:
      Empty.absurd({Su.Suci.write(s) == [] : B.Bytes()}, P.Refute.fail_done(B.Err, Su.Suci, B.Short{}, s, e))
    case +h <> +rest:
      Suci.sx_type(h, rest, s, U32.is_eq(h, Su.Suci.header()), {==}, e, P.Bool.and_true_r(B.is_byte(h), B.all_bytes(rest), ab))

# Mobile identity: write-back
# ---------------------------

def Id.Sx(id: Mi.MobileId, bs: B.Bytes()) -> Type:
  {Mi.MobileId.write(id) == bs : B.Bytes()}

def Id.Dv(id: Mi.MobileId) -> Type:
  {Mi.MobileId.valid(id) == True{} : Bool}

def Id.ok_inv(-G: Type, +tag: U32, +id0: Mi.MobileId, +id: Mi.MobileId, ok: Bool, +e: {Mi.MobileId.ok(tag, id0, ok) == Done{id} : Id.Res()}, k: {id0 == id : Mi.MobileId} -> {ok == True{} : Bool} -> G) -> G:
  match ok:
    case True{}:
      k(Equal.cong(Id.Res(), Mi.MobileId, x => P.Res.value(B.Err, Mi.MobileId, x, id), Done{id0}, Done{id}, e), {==})
    case False{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{tag}, id, e))

def Tbcd.all_of(+ds: B.Digits(), +bs: B.Bytes(), sp: PB.Tbcd.Spec(ds, List.length(&2, U32, bs))) -> {B.Tbcd.all_digits(ds) == True{} : Bool}:
  (le, all) = sp
  all

def Id.sx_imeisv_fin(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, +ds: B.Digits(), ei: {Mi.Imeisv{U32.and(15, U32.shrn(h, 4n)) <> ds} == id : Mi.MobileId}, hit: {U32.and(15, h) == 5 : U32}, m8: {U32.and(255, h) == h : U32}, wt: {B.write_tbcd(ds, []) == rest : B.Bytes()}) -> Id.Sx(id, h <> rest):
  %ei : Id.Sx(_, h <> rest)
  %hit : {B.cat4(_, U32.and(15, U32.and(15, U32.shrn(h, 4n)))) <> B.write_tbcd(ds, []) == h <> rest : B.Bytes()}
  nj = Equal.sym(U32, B.cat4(U32.and(15, h), U32.and(15, U32.and(15, U32.shrn(h, 4n)))), h, P.U32.nibbles_join(h, m8))
  %nj : {_ <> B.write_tbcd(ds, []) == h <> rest : B.Bytes()}
  swt = Equal.sym(B.Bytes(), B.write_tbcd(ds, []), rest, wt)
  %swt : {h <> _ == h <> rest : B.Bytes()}
  {==}

def Id.sx_imeisv(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, r: Tbcd.Res(), er: {B.Tbcd.decode(rest) == r : Tbcd.Res()}, +e: {Mi.MobileId.imeisv_of(h, r) == Done{id} : Id.Res()}, hit: {U32.and(15, h) == 5 : U32}, m8: {U32.and(255, h) == h : U32}, abr: {B.all_bytes(rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match r:
    case Fail{x}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{+ds}:
      Id.ok_inv(Id.Sx(id, h <> rest), h, Mi.Imeisv{U32.and(15, U32.shrn(h, 4n)) <> ds}, id, Bool.and(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), Nat.is_eq(List.length(&2, U32, ds), 15n)), e, ei => ok => Id.sx_imeisv_fin(h, rest, id, ds, ei, hit, m8, Tbcd.sx(rest, ds, er, abr)))

def Id.sx_imei_fin(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, +ds: B.Digits(), ei: {Mi.Imei{U32.and(15, U32.shrn(h, 4n)) <> ds} == id : Mi.MobileId}, hit: {U32.and(15, h) == 11 : U32}, m8: {U32.and(255, h) == h : U32}, wt: {B.write_tbcd(ds, []) == rest : B.Bytes()}) -> Id.Sx(id, h <> rest):
  %ei : Id.Sx(_, h <> rest)
  %hit : {B.cat4(_, U32.and(15, U32.and(15, U32.shrn(h, 4n)))) <> B.write_tbcd(ds, []) == h <> rest : B.Bytes()}
  nj = Equal.sym(U32, B.cat4(U32.and(15, h), U32.and(15, U32.and(15, U32.shrn(h, 4n)))), h, P.U32.nibbles_join(h, m8))
  %nj : {_ <> B.write_tbcd(ds, []) == h <> rest : B.Bytes()}
  swt = Equal.sym(B.Bytes(), B.write_tbcd(ds, []), rest, wt)
  %swt : {h <> _ == h <> rest : B.Bytes()}
  {==}

def Id.sx_imei(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, r: Tbcd.Res(), er: {B.Tbcd.decode(rest) == r : Tbcd.Res()}, +e: {Mi.MobileId.imei_of(h, r) == Done{id} : Id.Res()}, hit: {U32.and(15, h) == 11 : U32}, m8: {U32.and(255, h) == h : U32}, abr: {B.all_bytes(rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match r:
    case Fail{x}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{+ds}:
      Id.ok_inv(Id.Sx(id, h <> rest), h, Mi.Imei{U32.and(15, U32.shrn(h, 4n)) <> ds}, id, Bool.and(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), Nat.is_eq(List.length(&2, U32, ds), 14n)), e, ei => ok => Id.sx_imei_fin(h, rest, id, ds, ei, hit, m8, Tbcd.sx(rest, ds, er, abr)))

def Id.sx_guti_fin(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, +a1: U32, +a0: U32, +t3: U32, +t2: U32, +t1: U32, +t0: U32, ei: {Mi.Guti{plmn, region, B.cat8(a0, a1), B.cat8(t0, B.cat8(t1, B.cat8(t2, t3)))} == id : Mi.MobileId}, eh: {h == 242 : U32}, wp: {PL.Plmn.write(plmn, region <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> []) == rest : B.Bytes()}, mr: {U32.and(255, region) == region : U32}, ma1: {U32.and(255, a1) == a1 : U32}, ma0: {U32.and(255, a0) == a0 : U32}, mt3: {U32.and(255, t3) == t3 : U32}, mt2: {U32.and(255, t2) == t2 : U32}, mt1: {U32.and(255, t1) == t1 : U32}, mt0: {U32.and(255, t0) == t0 : U32}) -> Id.Sx(id, h <> rest):
  %ei : Id.Sx(_, h <> rest)
  sh = Equal.sym(U32, h, 242, eh)
  %sh : {Mi.MobileId.write(Mi.Guti{plmn, region, B.cat8(a0, a1), B.cat8(t0, B.cat8(t1, B.cat8(t2, t3)))}) == _ <> rest : B.Bytes()}
  sr = Equal.sym(U32, U32.and(255, region), region, mr)
  %sr : {242 <> PL.Plmn.write(plmn, _ <> B.write_u16(B.cat8(a0, a1), B.write_u32(B.cat8(t0, B.cat8(t1, B.cat8(t2, t3))), []))) == 242 <> rest : B.Bytes()}
  s16 = Equal.sym(B.Bytes(), B.write_u16(B.cat8(a0, a1), B.write_u32(B.cat8(t0, B.cat8(t1, B.cat8(t2, t3))), [])), a1 <> a0 <> B.write_u32(B.cat8(t0, B.cat8(t1, B.cat8(t2, t3))), []), P.Bytes.u16_sx(a1, a0, ma1, ma0, B.write_u32(B.cat8(t0, B.cat8(t1, B.cat8(t2, t3))), [])))
  %s16 : {242 <> PL.Plmn.write(plmn, region <> _) == 242 <> rest : B.Bytes()}
  s32 = Equal.sym(B.Bytes(), B.write_u32(B.cat8(t0, B.cat8(t1, B.cat8(t2, t3))), []), t3 <> t2 <> t1 <> t0 <> [], P.Bytes.u32_sx(t3, t2, t1, t0, mt3, mt2, mt1, mt0, []))
  %s32 : {242 <> PL.Plmn.write(plmn, region <> a1 <> a0 <> _) == 242 <> rest : B.Bytes()}
  swp = Equal.sym(B.Bytes(), PL.Plmn.write(plmn, region <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> []), rest, wp)
  %swp : {242 <> _ == 242 <> rest : B.Bytes()}
  {==}

def Id.sx_guti_bytes(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, +a1: U32, +a0: U32, +t3: U32, +t2: U32, +t1: U32, +t0: U32, r4: B.Bytes(), +e: {Mi.MobileId.end(Mi.Guti{plmn, region, B.cat8(a0, a1), B.cat8(t0, B.cat8(t1, B.cat8(t2, t3)))}, r4) == Done{id} : Id.Res()}, eh: {h == 242 : U32}, wp: {PL.Plmn.write(plmn, region <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> r4) == rest : B.Bytes()}, +ab1: {B.all_bytes(region <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> r4) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match r4:
    case x <> more:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{x}, id, e))
    case Nil{}:
      +abA = P.Bool.and_true_r(B.is_byte(region), B.all_bytes(a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> []), ab1)
      +abB = P.Bool.and_true_r(B.is_byte(a1), B.all_bytes(a0 <> t3 <> t2 <> t1 <> t0 <> []), abA)
      +abC = P.Bool.and_true_r(B.is_byte(a0), B.all_bytes(t3 <> t2 <> t1 <> t0 <> []), abB)
      +abD = P.Bool.and_true_r(B.is_byte(t3), B.all_bytes(t2 <> t1 <> t0 <> []), abC)
      +abE = P.Bool.and_true_r(B.is_byte(t2), B.all_bytes(t1 <> t0 <> []), abD)
      +abF = P.Bool.and_true_r(B.is_byte(t1), B.all_bytes(t0 <> []), abE)
      Id.sx_guti_fin(h, rest, id, plmn, region, a1, a0, t3, t2, t1, t0, Equal.cong(Id.Res(), Mi.MobileId, x => P.Res.value(B.Err, Mi.MobileId, x, id), Done{Mi.Guti{plmn, region, B.cat8(a0, a1), B.cat8(t0, B.cat8(t1, B.cat8(t2, t3)))}}, Done{id}, e), eh, wp, P.U32.lt256_mask8(region, P.Bool.and_true_l(B.is_byte(region), B.all_bytes(a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> []), ab1)), P.U32.lt256_mask8(a1, P.Bool.and_true_l(B.is_byte(a1), B.all_bytes(a0 <> t3 <> t2 <> t1 <> t0 <> []), abA)), P.U32.lt256_mask8(a0, P.Bool.and_true_l(B.is_byte(a0), B.all_bytes(t3 <> t2 <> t1 <> t0 <> []), abB)), P.U32.lt256_mask8(t3, P.Bool.and_true_l(B.is_byte(t3), B.all_bytes(t2 <> t1 <> t0 <> []), abC)), P.U32.lt256_mask8(t2, P.Bool.and_true_l(B.is_byte(t2), B.all_bytes(t1 <> t0 <> []), abD)), P.U32.lt256_mask8(t1, P.Bool.and_true_l(B.is_byte(t1), B.all_bytes(t0 <> []), abE)), P.U32.lt256_mask8(t0, P.Bool.and_true_l(B.is_byte(t0), B.all_bytes([]), abF)))

def Id.sx_guti_tmsi(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, +a1: U32, +a0: U32, r3: B.Bytes(), +e: {Mi.MobileId.guti_tmsi(plmn, region, B.cat8(a0, a1), B.u32(r3)) == Done{id} : Id.Res()}, eh: {h == 242 : U32}, wp: {PL.Plmn.write(plmn, region <> a1 <> a0 <> r3) == rest : B.Bytes()}, +ab1: {B.all_bytes(region <> a1 <> a0 <> r3) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match r3:
    case Nil{}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case x <> Nil{}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case x <> y <> Nil{}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case x <> y <> z <> Nil{}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case +t3 <> +t2 <> +t1 <> +t0 <> +r4:
      Id.sx_guti_bytes(h, rest, id, plmn, region, a1, a0, t3, t2, t1, t0, r4, e, eh, wp, ab1)

def Id.sx_guti_amf_ok(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, +a1: U32, +a0: U32, +r3: B.Bytes(), ok: Bool, +e: {Mi.MobileId.guti_amf_ok(plmn, region, B.cat8(a0, a1), r3, ok) == Done{id} : Id.Res()}, eh: {h == 242 : U32}, wp: {PL.Plmn.write(plmn, region <> a1 <> a0 <> r3) == rest : B.Bytes()}, +ab1: {B.all_bytes(region <> a1 <> a0 <> r3) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match ok:
    case False{}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{B.cat8(a0, a1)}, id, e))
    case True{}:
      Id.sx_guti_tmsi(h, rest, id, plmn, region, a1, a0, r3, e, eh, wp, ab1)

def Id.sx_guti_amf(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, r2: B.Bytes(), +e: {Mi.MobileId.guti_amf(plmn, region, B.u16(r2)) == Done{id} : Id.Res()}, eh: {h == 242 : U32}, wp: {PL.Plmn.write(plmn, region <> r2) == rest : B.Bytes()}, +ab1: {B.all_bytes(region <> r2) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match r2:
    case Nil{}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case x <> Nil{}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case +a1 <> +a0 <> +r3:
      Id.sx_guti_amf_ok(h, rest, id, plmn, region, a1, a0, r3, I.fits16(B.cat8(a0, a1)), e, eh, wp, ab1)

def Id.sx_guti_region_ok(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, +r2: B.Bytes(), ok: Bool, +e: {Mi.MobileId.guti_region_ok(plmn, region, r2, ok) == Done{id} : Id.Res()}, eh: {h == 242 : U32}, wp: {PL.Plmn.write(plmn, region <> r2) == rest : B.Bytes()}, +ab1: {B.all_bytes(region <> r2) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match ok:
    case False{}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{region}, id, e))
    case True{}:
      Id.sx_guti_amf(h, rest, id, plmn, region, r2, e, eh, wp, ab1)

def Id.sx_guti_region(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, +plmn: PL.Plmn, r1: B.Bytes(), +e: {Mi.MobileId.guti_region(plmn, B.u8(r1)) == Done{id} : Id.Res()}, eh: {h == 242 : U32}, wp: {PL.Plmn.write(plmn, r1) == rest : B.Bytes()}, +ab1: {B.all_bytes(r1) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match r1:
    case Nil{}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case +region <> +r2:
      Id.sx_guti_region_ok(h, rest, id, plmn, region, r2, I.fits8(region), e, eh, wp, ab1)

def Id.sx_guti(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, rp: B.Read(PL.Plmn), erp: {PL.Plmn.read(rest) == rp : B.Read(PL.Plmn)}, +e: {Mi.MobileId.guti_plmn(rp) == Done{id} : Id.Res()}, eh: {h == 242 : U32}, +ab: {B.all_bytes(rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match rp:
    case Fail{x}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{(+plmn, +r1)}:
      +wp = Plmn.sx(rest, plmn, r1, erp, ab)
      Id.sx_guti_region(h, rest, id, plmn, r1, e, eh, wp, Plmn.tail_bytes(plmn, r1, rest, wp, ab))

def Id.sx_stmsi_fin(+h: U32, +id: Mi.MobileId, +a1: U32, +a0: U32, +t3: U32, +t2: U32, +t1: U32, +t0: U32, ei: {Mi.STmsi{B.cat8(a0, a1), B.cat8(t0, B.cat8(t1, B.cat8(t2, t3)))} == id : Mi.MobileId}, eh: {h == 244 : U32}, ma1: {U32.and(255, a1) == a1 : U32}, ma0: {U32.and(255, a0) == a0 : U32}, mt3: {U32.and(255, t3) == t3 : U32}, mt2: {U32.and(255, t2) == t2 : U32}, mt1: {U32.and(255, t1) == t1 : U32}, mt0: {U32.and(255, t0) == t0 : U32}) -> Id.Sx(id, h <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> []):
  %ei : Id.Sx(_, h <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> [])
  sh = Equal.sym(U32, h, 244, eh)
  %sh : {Mi.MobileId.write(Mi.STmsi{B.cat8(a0, a1), B.cat8(t0, B.cat8(t1, B.cat8(t2, t3)))}) == _ <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> [] : B.Bytes()}
  s16 = Equal.sym(B.Bytes(), B.write_u16(B.cat8(a0, a1), B.write_u32(B.cat8(t0, B.cat8(t1, B.cat8(t2, t3))), [])), a1 <> a0 <> B.write_u32(B.cat8(t0, B.cat8(t1, B.cat8(t2, t3))), []), P.Bytes.u16_sx(a1, a0, ma1, ma0, B.write_u32(B.cat8(t0, B.cat8(t1, B.cat8(t2, t3))), [])))
  %s16 : {244 <> _ == 244 <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> [] : B.Bytes()}
  s32 = Equal.sym(B.Bytes(), B.write_u32(B.cat8(t0, B.cat8(t1, B.cat8(t2, t3))), []), t3 <> t2 <> t1 <> t0 <> [], P.Bytes.u32_sx(t3, t2, t1, t0, mt3, mt2, mt1, mt0, []))
  %s32 : {244 <> a1 <> a0 <> _ == 244 <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> [] : B.Bytes()}
  {==}

def Id.sx_stmsi_bytes(+h: U32, +id: Mi.MobileId, +a1: U32, +a0: U32, +t3: U32, +t2: U32, +t1: U32, +t0: U32, r4: B.Bytes(), +e: {Mi.MobileId.end(Mi.STmsi{B.cat8(a0, a1), B.cat8(t0, B.cat8(t1, B.cat8(t2, t3)))}, r4) == Done{id} : Id.Res()}, eh: {h == 244 : U32}, +abr: {B.all_bytes(a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> r4) == True{} : Bool}) -> Id.Sx(id, h <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> r4):
  match r4:
    case x <> more:
      Empty.absurd(Id.Sx(id, h <> a1 <> a0 <> t3 <> t2 <> t1 <> t0 <> x <> more), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{x}, id, e))
    case Nil{}:
      +abB = P.Bool.and_true_r(B.is_byte(a1), B.all_bytes(a0 <> t3 <> t2 <> t1 <> t0 <> []), abr)
      +abC = P.Bool.and_true_r(B.is_byte(a0), B.all_bytes(t3 <> t2 <> t1 <> t0 <> []), abB)
      +abD = P.Bool.and_true_r(B.is_byte(t3), B.all_bytes(t2 <> t1 <> t0 <> []), abC)
      +abE = P.Bool.and_true_r(B.is_byte(t2), B.all_bytes(t1 <> t0 <> []), abD)
      +abF = P.Bool.and_true_r(B.is_byte(t1), B.all_bytes(t0 <> []), abE)
      Id.sx_stmsi_fin(h, id, a1, a0, t3, t2, t1, t0, Equal.cong(Id.Res(), Mi.MobileId, x => P.Res.value(B.Err, Mi.MobileId, x, id), Done{Mi.STmsi{B.cat8(a0, a1), B.cat8(t0, B.cat8(t1, B.cat8(t2, t3)))}}, Done{id}, e), eh, P.U32.lt256_mask8(a1, P.Bool.and_true_l(B.is_byte(a1), B.all_bytes(a0 <> t3 <> t2 <> t1 <> t0 <> []), abr)), P.U32.lt256_mask8(a0, P.Bool.and_true_l(B.is_byte(a0), B.all_bytes(t3 <> t2 <> t1 <> t0 <> []), abB)), P.U32.lt256_mask8(t3, P.Bool.and_true_l(B.is_byte(t3), B.all_bytes(t2 <> t1 <> t0 <> []), abC)), P.U32.lt256_mask8(t2, P.Bool.and_true_l(B.is_byte(t2), B.all_bytes(t1 <> t0 <> []), abD)), P.U32.lt256_mask8(t1, P.Bool.and_true_l(B.is_byte(t1), B.all_bytes(t0 <> []), abE)), P.U32.lt256_mask8(t0, P.Bool.and_true_l(B.is_byte(t0), B.all_bytes([]), abF)))

def Id.sx_stmsi_tmsi(+h: U32, +id: Mi.MobileId, +a1: U32, +a0: U32, r3: B.Bytes(), +e: {Mi.MobileId.s_tmsi_tmsi(B.cat8(a0, a1), B.u32(r3)) == Done{id} : Id.Res()}, eh: {h == 244 : U32}, +abr: {B.all_bytes(a1 <> a0 <> r3) == True{} : Bool}) -> Id.Sx(id, h <> a1 <> a0 <> r3):
  match r3:
    case Nil{}:
      Empty.absurd(Id.Sx(id, h <> a1 <> a0 <> []), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case x <> Nil{}:
      Empty.absurd(Id.Sx(id, h <> a1 <> a0 <> [x]), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case x <> y <> Nil{}:
      Empty.absurd(Id.Sx(id, h <> a1 <> a0 <> [x, y]), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case x <> y <> z <> Nil{}:
      Empty.absurd(Id.Sx(id, h <> a1 <> a0 <> [x, y, z]), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case +t3 <> +t2 <> +t1 <> +t0 <> +r4:
      Id.sx_stmsi_bytes(h, id, a1, a0, t3, t2, t1, t0, r4, e, eh, abr)

def Id.sx_stmsi_ok(+h: U32, +id: Mi.MobileId, +a1: U32, +a0: U32, +r3: B.Bytes(), ok: Bool, +e: {Mi.MobileId.s_tmsi_ok(B.cat8(a0, a1), r3, ok) == Done{id} : Id.Res()}, eh: {h == 244 : U32}, +abr: {B.all_bytes(a1 <> a0 <> r3) == True{} : Bool}) -> Id.Sx(id, h <> a1 <> a0 <> r3):
  match ok:
    case False{}:
      Empty.absurd(Id.Sx(id, h <> a1 <> a0 <> r3), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{B.cat8(a0, a1)}, id, e))
    case True{}:
      Id.sx_stmsi_tmsi(h, id, a1, a0, r3, e, eh, abr)

def Id.sx_stmsi(+h: U32, +id: Mi.MobileId, rest: B.Bytes(), +e: {Mi.MobileId.s_tmsi_amf(B.u16(rest)) == Done{id} : Id.Res()}, eh: {h == 244 : U32}, +abr: {B.all_bytes(rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match rest:
    case Nil{}:
      Empty.absurd(Id.Sx(id, h <> []), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case x <> Nil{}:
      Empty.absurd(Id.Sx(id, h <> [x]), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case +a1 <> +a0 <> +r3:
      Id.sx_stmsi_ok(h, id, a1, a0, r3, I.fits16(B.cat8(a0, a1)), e, eh, abr)

def Id.sx_noid(+h: U32, rest: B.Bytes(), +id: Mi.MobileId, +e: {Mi.MobileId.end(Mi.NoId{}, rest) == Done{id} : Id.Res()}, eh: {h == 0 : U32}) -> Id.Sx(id, h <> rest):
  match rest:
    case b <> more:
      Empty.absurd(Id.Sx(id, h <> b <> more), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{b}, id, e))
    case Nil{}:
      ei = Equal.cong(Id.Res(), Mi.MobileId, x => P.Res.value(B.Err, Mi.MobileId, x, id), Done{Mi.NoId{}}, Done{id}, e)
      %ei : Id.Sx(_, h <> [])
      sh = Equal.sym(U32, h, 0, eh)
      %sh : {[0] == _ <> [] : B.Bytes()}
      {==}

def Id.sx_suci(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, rs: Suci.Res(), ers: {Su.Suci.read(h <> rest) == rs : Suci.Res()}, +e: {Mi.MobileId.suci_of(rs) == Done{id} : Id.Res()}, +ab: {B.all_bytes(h <> rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match rs:
    case Fail{x}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{+s}:
      ei = Equal.cong(Id.Res(), Mi.MobileId, x => P.Res.value(B.Err, Mi.MobileId, x, id), Done{Mi.Suci{s}}, Done{id}, e)
      %ei : Id.Sx(_, h <> rest)
      Suci.sx(h <> rest, s, ers, ab)

def Id.sx_r5(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, ev: {U32.is_eq(U32.and(15, h), Mi.MobileId.imeisv()) == hit : Bool}, +e: {Mi.MobileId.r5(h, rest, hit) == Done{id} : Id.Res()}, m8: {U32.and(255, h) == h : U32}, abr: {B.all_bytes(rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match hit:
    case False{}:
      Empty.absurd(Id.Sx(id, h <> rest), P.Refute.fail_done(B.Err, Mi.MobileId, B.Unsupported{h}, id, e))
    case True{}:
      Id.sx_imeisv(h, rest, id, B.Tbcd.decode(rest), {==}, e, P.U32.eq_of_is_eq(U32.and(15, h), 5, ev), m8, abr)

def Id.sx_r3(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, ev: {U32.is_eq(U32.and(15, h), Mi.MobileId.imei()) == hit : Bool}, +e: {Mi.MobileId.r3(h, rest, hit) == Done{id} : Id.Res()}, m8: {U32.and(255, h) == h : U32}, abr: {B.all_bytes(rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match hit:
    case True{}:
      Id.sx_imei(h, rest, id, B.Tbcd.decode(rest), {==}, e, P.U32.eq_of_is_eq(U32.and(15, h), 11, ev), m8, abr)
    case False{}:
      Id.sx_r5(h, rest, id, U32.is_eq(U32.and(15, h), Mi.MobileId.imeisv()), {==}, e, m8, abr)

def Id.sx_r4(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, ev: {U32.is_eq(h, Mi.MobileId.s_tmsi()) == hit : Bool}, +e: {Mi.MobileId.r4(h, rest, hit) == Done{id} : Id.Res()}, m8: {U32.and(255, h) == h : U32}, abr: {B.all_bytes(rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match hit:
    case True{}:
      Id.sx_stmsi(h, id, rest, e, P.U32.eq_of_is_eq(h, 244, ev), abr)
    case False{}:
      Id.sx_r3(h, rest, id, U32.is_eq(U32.and(15, h), Mi.MobileId.imei()), {==}, e, m8, abr)

def Id.sx_r2(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, ev: {U32.is_eq(h, Mi.MobileId.guti()) == hit : Bool}, +e: {Mi.MobileId.r2(h, rest, hit) == Done{id} : Id.Res()}, m8: {U32.and(255, h) == h : U32}, abr: {B.all_bytes(rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match hit:
    case True{}:
      Id.sx_guti(h, rest, id, PL.Plmn.read(rest), {==}, e, P.U32.eq_of_is_eq(h, 242, ev), abr)
    case False{}:
      Id.sx_r4(h, rest, id, U32.is_eq(h, Mi.MobileId.s_tmsi()), {==}, e, m8, abr)

def Id.sx_r1(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, ev: {U32.is_eq(h, Su.Suci.header()) == hit : Bool}, +e: {Mi.MobileId.r1(h, rest, hit) == Done{id} : Id.Res()}, m8: {U32.and(255, h) == h : U32}, +ab: {B.all_bytes(h <> rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match hit:
    case True{}:
      Id.sx_suci(h, rest, id, Su.Suci.read(h <> rest), {==}, e, ab)
    case False{}:
      Id.sx_r2(h, rest, id, U32.is_eq(h, Mi.MobileId.guti()), {==}, e, m8, P.Bool.and_true_r(B.is_byte(h), B.all_bytes(rest), ab))

def Id.sx_r0(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, ev: {U32.is_eq(h, 0) == hit : Bool}, +e: {Mi.MobileId.r0(h, rest, hit) == Done{id} : Id.Res()}, +ab: {B.all_bytes(h <> rest) == True{} : Bool}) -> Id.Sx(id, h <> rest):
  match hit:
    case True{}:
      Id.sx_noid(h, rest, id, e, P.U32.eq_of_is_eq(h, 0, ev))
    case False{}:
      Id.sx_r1(h, rest, id, U32.is_eq(h, Su.Suci.header()), {==}, e, P.U32.lt256_mask8(h, P.Bool.and_true_l(B.is_byte(h), B.all_bytes(rest), ab)), ab)

def Id.sx(bs: B.Bytes(), +id: Mi.MobileId, +e: {Mi.MobileId.read(bs) == Done{id} : Id.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> Id.Sx(id, bs):
  match bs:
    case Nil{}:
      Empty.absurd(Id.Sx(id, []), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case +h <> +rest:
      Id.sx_r0(h, rest, id, U32.is_eq(h, 0), {==}, e, ab)

def L.nas.mobile_identity.suffix(bs, id, e, ab):
  Id.sx(bs, id, e, ab)

# Mobile identity: validity
# -------------------------

def Id.dv_imeisv_fin(+h: U32, +id: Mi.MobileId, +ds: B.Digits(), ei: {Mi.Imeisv{U32.and(15, U32.shrn(h, 4n)) <> ds} == id : Mi.MobileId}, +ok: {Bool.and(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), Nat.is_eq(List.length(&2, U32, ds), 15n)) == True{} : Bool}, alld: {B.Tbcd.all_digits(ds) == True{} : Bool}) -> Id.Dv(id):
  %ei : Id.Dv(_)
  P.Bool.and_intro(Bool.and(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), B.Tbcd.all_digits(ds)), Nat.is_eq(List.length(&2, U32, ds), 15n), P.Bool.and_intro(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), B.Tbcd.all_digits(ds), P.Bool.and_true_l(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), Nat.is_eq(List.length(&2, U32, ds), 15n), ok), alld), P.Bool.and_true_r(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), Nat.is_eq(List.length(&2, U32, ds), 15n), ok))

def Id.dv_imeisv(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, r: Tbcd.Res(), er: {B.Tbcd.decode(rest) == r : Tbcd.Res()}, +e: {Mi.MobileId.imeisv_of(h, r) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match r:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{+ds}:
      Id.ok_inv(Id.Dv(id), h, Mi.Imeisv{U32.and(15, U32.shrn(h, 4n)) <> ds}, id, Bool.and(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), Nat.is_eq(List.length(&2, U32, ds), 15n)), e, ei => ok => Id.dv_imeisv_fin(h, id, ds, ei, ok, Tbcd.all_of(ds, rest, PB.Tbcd.decode_len(rest, ds, er))))

def Id.dv_imei_fin(+h: U32, +id: Mi.MobileId, +ds: B.Digits(), ei: {Mi.Imei{U32.and(15, U32.shrn(h, 4n)) <> ds} == id : Mi.MobileId}, +ok: {Bool.and(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), Nat.is_eq(List.length(&2, U32, ds), 14n)) == True{} : Bool}, alld: {B.Tbcd.all_digits(ds) == True{} : Bool}) -> Id.Dv(id):
  %ei : Id.Dv(_)
  P.Bool.and_intro(Bool.and(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), B.Tbcd.all_digits(ds)), Nat.is_eq(List.length(&2, U32, ds), 14n), P.Bool.and_intro(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), B.Tbcd.all_digits(ds), P.Bool.and_true_l(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), Nat.is_eq(List.length(&2, U32, ds), 14n), ok), alld), P.Bool.and_true_r(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), Nat.is_eq(List.length(&2, U32, ds), 14n), ok))

def Id.dv_imei(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, r: Tbcd.Res(), er: {B.Tbcd.decode(rest) == r : Tbcd.Res()}, +e: {Mi.MobileId.imei_of(h, r) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match r:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{+ds}:
      Id.ok_inv(Id.Dv(id), h, Mi.Imei{U32.and(15, U32.shrn(h, 4n)) <> ds}, id, Bool.and(B.Tbcd.is_digit(U32.and(15, U32.shrn(h, 4n))), Nat.is_eq(List.length(&2, U32, ds), 14n)), e, ei => ok => Id.dv_imei_fin(h, id, ds, ei, ok, Tbcd.all_of(ds, rest, PB.Tbcd.decode_len(rest, ds, er))))

def Id.dv_guti_fin(+id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, +amf: U32, +tmsi: U32, ei: {Mi.Guti{plmn, region, amf, tmsi} == id : Mi.MobileId}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}, f8: {I.fits8(region) == True{} : Bool}, f16: {I.fits16(amf) == True{} : Bool}) -> Id.Dv(id):
  %ei : Id.Dv(_)
  P.Bool.and_intro(PL.Plmn.valid(plmn), Bool.and(I.fits8(region), I.fits16(amf)), pv, P.Bool.and_intro(I.fits8(region), I.fits16(amf), f8, f16))

def Id.dv_guti_end(+id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, +amf: U32, +tmsi: U32, r4: B.Bytes(), +e: {Mi.MobileId.end(Mi.Guti{plmn, region, amf, tmsi}, r4) == Done{id} : Id.Res()}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}, f8: {I.fits8(region) == True{} : Bool}, f16: {I.fits16(amf) == True{} : Bool}) -> Id.Dv(id):
  match r4:
    case x <> more:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{x}, id, e))
    case Nil{}:
      Id.dv_guti_fin(id, plmn, region, amf, tmsi, Equal.cong(Id.Res(), Mi.MobileId, x => P.Res.value(B.Err, Mi.MobileId, x, id), Done{Mi.Guti{plmn, region, amf, tmsi}}, Done{id}, e), pv, f8, f16)

def Id.dv_guti_tmsi(+id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, +amf: U32, rt: B.Read(U32), +e: {Mi.MobileId.guti_tmsi(plmn, region, amf, rt) == Done{id} : Id.Res()}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}, f8: {I.fits8(region) == True{} : Bool}, f16: {I.fits16(amf) == True{} : Bool}) -> Id.Dv(id):
  match rt:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{(+tmsi, +r4)}:
      Id.dv_guti_end(id, plmn, region, amf, tmsi, r4, e, pv, f8, f16)

def Id.dv_guti_amf_ok(+id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, +amf: U32, +r3: B.Bytes(), ok: Bool, ev: {I.fits16(amf) == ok : Bool}, +e: {Mi.MobileId.guti_amf_ok(plmn, region, amf, r3, ok) == Done{id} : Id.Res()}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}, f8: {I.fits8(region) == True{} : Bool}) -> Id.Dv(id):
  match ok:
    case False{}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{amf}, id, e))
    case True{}:
      Id.dv_guti_tmsi(id, plmn, region, amf, B.u32(r3), e, pv, f8, ev)

def Id.dv_guti_amf(+id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, ra: B.Read(U32), +e: {Mi.MobileId.guti_amf(plmn, region, ra) == Done{id} : Id.Res()}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}, f8: {I.fits8(region) == True{} : Bool}) -> Id.Dv(id):
  match ra:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{(+amf, +r3)}:
      Id.dv_guti_amf_ok(id, plmn, region, amf, r3, I.fits16(amf), {==}, e, pv, f8)

def Id.dv_guti_region_ok(+id: Mi.MobileId, +plmn: PL.Plmn, +region: U32, +r2: B.Bytes(), ok: Bool, ev: {I.fits8(region) == ok : Bool}, +e: {Mi.MobileId.guti_region_ok(plmn, region, r2, ok) == Done{id} : Id.Res()}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}) -> Id.Dv(id):
  match ok:
    case False{}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{region}, id, e))
    case True{}:
      Id.dv_guti_amf(id, plmn, region, B.u16(r2), e, pv, ev)

def Id.dv_guti_region(+id: Mi.MobileId, +plmn: PL.Plmn, rr: B.Read(U32), +e: {Mi.MobileId.guti_region(plmn, rr) == Done{id} : Id.Res()}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}) -> Id.Dv(id):
  match rr:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{(+region, +r2)}:
      Id.dv_guti_region_ok(id, plmn, region, r2, I.fits8(region), {==}, e, pv)

def Id.dv_guti(+rest: B.Bytes(), +id: Mi.MobileId, rp: B.Read(PL.Plmn), erp: {PL.Plmn.read(rest) == rp : B.Read(PL.Plmn)}, +e: {Mi.MobileId.guti_plmn(rp) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match rp:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{(+plmn, +r1)}:
      Id.dv_guti_region(id, plmn, B.u8(r1), e, L.plmn.decode_valid(rest, plmn, r1, erp))

def Id.dv_stmsi_fin(+id: Mi.MobileId, +amf: U32, +tmsi: U32, ei: {Mi.STmsi{amf, tmsi} == id : Mi.MobileId}, f16: {I.fits16(amf) == True{} : Bool}) -> Id.Dv(id):
  %ei : Id.Dv(_)
  f16

def Id.dv_stmsi_end(+id: Mi.MobileId, +amf: U32, +tmsi: U32, r4: B.Bytes(), +e: {Mi.MobileId.end(Mi.STmsi{amf, tmsi}, r4) == Done{id} : Id.Res()}, f16: {I.fits16(amf) == True{} : Bool}) -> Id.Dv(id):
  match r4:
    case x <> more:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{x}, id, e))
    case Nil{}:
      Id.dv_stmsi_fin(id, amf, tmsi, Equal.cong(Id.Res(), Mi.MobileId, x => P.Res.value(B.Err, Mi.MobileId, x, id), Done{Mi.STmsi{amf, tmsi}}, Done{id}, e), f16)

def Id.dv_stmsi_tmsi(+id: Mi.MobileId, +amf: U32, rt: B.Read(U32), +e: {Mi.MobileId.s_tmsi_tmsi(amf, rt) == Done{id} : Id.Res()}, f16: {I.fits16(amf) == True{} : Bool}) -> Id.Dv(id):
  match rt:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{(+tmsi, +r4)}:
      Id.dv_stmsi_end(id, amf, tmsi, r4, e, f16)

def Id.dv_stmsi_ok(+id: Mi.MobileId, +amf: U32, +r3: B.Bytes(), ok: Bool, ev: {I.fits16(amf) == ok : Bool}, +e: {Mi.MobileId.s_tmsi_ok(amf, r3, ok) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match ok:
    case False{}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{amf}, id, e))
    case True{}:
      Id.dv_stmsi_tmsi(id, amf, B.u32(r3), e, ev)

def Id.dv_stmsi(+id: Mi.MobileId, ra: B.Read(U32), +e: {Mi.MobileId.s_tmsi_amf(ra) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match ra:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{(+amf, +r3)}:
      Id.dv_stmsi_ok(id, amf, r3, I.fits16(amf), {==}, e)

def Id.dv_noid(rest: B.Bytes(), +id: Mi.MobileId, +e: {Mi.MobileId.end(Mi.NoId{}, rest) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match rest:
    case b <> more:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, B.Invalid{b}, id, e))
    case Nil{}:
      ei = Equal.cong(Id.Res(), Mi.MobileId, x => P.Res.value(B.Err, Mi.MobileId, x, id), Done{Mi.NoId{}}, Done{id}, e)
      %ei : Id.Dv(_)
      {==}

def Routing.valid_of(+b0: U32, +b1: U32, +ds: B.Digits(), inv: Routing.Inv(b0, b1, ds)) -> {Su.Routing.valid(ds) == True{} : Bool}:
  (pd, v) = inv
  v

def Suci.dv_fin(+id: Mi.MobileId, +plmn: PL.Plmn, +routing: B.Digits(), +sc: U32, +key: U32, +output: B.Bytes(), +s: Su.Suci, ei: {Mi.Suci{s} == id : Mi.MobileId}, es: {Su.Suci{plmn, routing, sc, key, output} == s : Su.Suci}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}, rv: {Su.Routing.valid(routing) == True{} : Bool}) -> Id.Dv(id):
  %ei : Id.Dv(_)
  %es : {Mi.MobileId.valid(Mi.Suci{_}) == True{} : Bool}
  P.Bool.and_intro(PL.Plmn.valid(plmn), Su.Routing.valid(routing), pv, rv)

def Suci.dv_key(+id: Mi.MobileId, +plmn: PL.Plmn, +routing: B.Digits(), +sc: U32, +s: Su.Suci, rk: B.Read(U32), +e: {Su.Suci.r_key(plmn, routing, sc, rk) == Done{s} : Suci.Res()}, ei: {Mi.Suci{s} == id : Mi.MobileId}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}, rv: {Su.Routing.valid(routing) == True{} : Bool}) -> Id.Dv(id):
  match rk:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Su.Suci, x, s, e))
    case Done{(+key, +output)}:
      Suci.dv_fin(id, plmn, routing, sc, key, output, s, ei, Equal.cong(Suci.Res(), Su.Suci, x => P.Res.value(B.Err, Su.Suci, x, s), Done{Su.Suci{plmn, routing, sc, key, output}}, Done{s}, e), pv, rv)

def Suci.dv_scheme(+id: Mi.MobileId, +plmn: PL.Plmn, +routing: B.Digits(), +s: Su.Suci, rs: B.Read(U32), +e: {Su.Suci.r_scheme(plmn, routing, rs) == Done{s} : Suci.Res()}, ei: {Mi.Suci{s} == id : Mi.MobileId}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}, rv: {Su.Routing.valid(routing) == True{} : Bool}) -> Id.Dv(id):
  match rs:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Su.Suci, x, s, e))
    case Done{(+sc, +rest3)}:
      Suci.dv_key(id, plmn, routing, sc, s, B.u8(rest3), e, ei, pv, rv)

def Suci.dv_routing(+id: Mi.MobileId, +plmn: PL.Plmn, +b0: U32, +b1: U32, +rest2: B.Bytes(), +s: Su.Suci, rr: Tbcd.Res(), err: {Su.Routing.read(b0, b1) == rr : Tbcd.Res()}, +e: {Su.Suci.r_routing(plmn, rr, rest2) == Done{s} : Suci.Res()}, ei: {Mi.Suci{s} == id : Mi.MobileId}, pv: {PL.Plmn.valid(plmn) == True{} : Bool}) -> Id.Dv(id):
  match rr:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Su.Suci, x, s, e))
    case Done{+routing}:
      Suci.dv_scheme(id, plmn, routing, s, B.u8(rest2), e, ei, pv, Routing.valid_of(b0, b1, routing, Routing.inv(b0, b1, routing, err)))

def Suci.dv_plmn(+rest: B.Bytes(), +id: Mi.MobileId, +s: Su.Suci, rp: B.Read(PL.Plmn), erp: {PL.Plmn.read(rest) == rp : B.Read(PL.Plmn)}, +e: {Su.Suci.r_plmn(rp) == Done{s} : Suci.Res()}, ei: {Mi.Suci{s} == id : Mi.MobileId}) -> Id.Dv(id):
  match rp:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Su.Suci, x, s, e))
    case Done{(plmn, Nil{})}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Su.Suci, B.Short{}, s, e))
    case Done{(plmn, b0 <> Nil{})}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Su.Suci, B.Short{}, s, e))
    case Done{(+plmn, +b0 <> +b1 <> +rest2)}:
      Suci.dv_routing(id, plmn, b0, b1, rest2, s, Su.Routing.read(b0, b1), {==}, e, ei, L.plmn.decode_valid(rest, plmn, b0 <> b1 <> rest2, erp))

def Suci.dv_type(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, +s: Su.Suci, ok: Bool, +e: {Su.Suci.r_type(h, rest, ok) == Done{s} : Suci.Res()}, ei: {Mi.Suci{s} == id : Mi.MobileId}) -> Id.Dv(id):
  match ok:
    case False{}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Su.Suci, B.Unsupported{h}, s, e))
    case True{}:
      Suci.dv_plmn(rest, id, s, PL.Plmn.read(rest), {==}, e, ei)

def Suci.dv(bs: B.Bytes(), +id: Mi.MobileId, +s: Su.Suci, +e: {Su.Suci.read(bs) == Done{s} : Suci.Res()}, ei: {Mi.Suci{s} == id : Mi.MobileId}) -> Id.Dv(id):
  match bs:
    case Nil{}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Su.Suci, B.Short{}, s, e))
    case +h <> +rest:
      Suci.dv_type(h, rest, id, s, U32.is_eq(h, Su.Suci.header()), e, ei)

def Id.dv_suci(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, rs: Suci.Res(), ers: {Su.Suci.read(h <> rest) == rs : Suci.Res()}, +e: {Mi.MobileId.suci_of(rs) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match rs:
    case Fail{x}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, x, id, e))
    case Done{+s}:
      Suci.dv(h <> rest, id, s, ers, Equal.cong(Id.Res(), Mi.MobileId, x => P.Res.value(B.Err, Mi.MobileId, x, id), Done{Mi.Suci{s}}, Done{id}, e))

def Id.dv_r5(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, +e: {Mi.MobileId.r5(h, rest, hit) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match hit:
    case False{}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, B.Unsupported{h}, id, e))
    case True{}:
      Id.dv_imeisv(h, rest, id, B.Tbcd.decode(rest), {==}, e)

def Id.dv_r3(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, +e: {Mi.MobileId.r3(h, rest, hit) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match hit:
    case True{}:
      Id.dv_imei(h, rest, id, B.Tbcd.decode(rest), {==}, e)
    case False{}:
      Id.dv_r5(h, rest, id, U32.is_eq(U32.and(15, h), Mi.MobileId.imeisv()), e)

def Id.dv_r4(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, +e: {Mi.MobileId.r4(h, rest, hit) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match hit:
    case True{}:
      Id.dv_stmsi(id, B.u16(rest), e)
    case False{}:
      Id.dv_r3(h, rest, id, U32.is_eq(U32.and(15, h), Mi.MobileId.imei()), e)

def Id.dv_r2(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, +e: {Mi.MobileId.r2(h, rest, hit) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match hit:
    case True{}:
      Id.dv_guti(rest, id, PL.Plmn.read(rest), {==}, e)
    case False{}:
      Id.dv_r4(h, rest, id, U32.is_eq(h, Mi.MobileId.s_tmsi()), e)

def Id.dv_r1(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, +e: {Mi.MobileId.r1(h, rest, hit) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match hit:
    case True{}:
      Id.dv_suci(h, rest, id, Su.Suci.read(h <> rest), {==}, e)
    case False{}:
      Id.dv_r2(h, rest, id, U32.is_eq(h, Mi.MobileId.guti()), e)

def Id.dv_r0(+h: U32, +rest: B.Bytes(), +id: Mi.MobileId, hit: Bool, +e: {Mi.MobileId.r0(h, rest, hit) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match hit:
    case True{}:
      Id.dv_noid(rest, id, e)
    case False{}:
      Id.dv_r1(h, rest, id, U32.is_eq(h, Su.Suci.header()), e)

def Id.dv(bs: B.Bytes(), +id: Mi.MobileId, +e: {Mi.MobileId.read(bs) == Done{id} : Id.Res()}) -> Id.Dv(id):
  match bs:
    case Nil{}:
      Empty.absurd(Id.Dv(id), P.Refute.fail_done(B.Err, Mi.MobileId, B.Short{}, id, e))
    case +h <> +rest:
      Id.dv_r0(h, rest, id, U32.is_eq(h, 0), e)

def L.nas.mobile_identity.decode_valid(bs, id, e):
  Id.dv(bs, id, e)

def L.nas.mobile_identity.guti_length(bs, plmn, region, amf, tmsi, e, ab):
  match plmn:
    case PL.Plmn{a, b, c, d, f, g}:
      sx = L.nas.mobile_identity.suffix(bs, Mi.Guti{PL.Plmn{a, b, c, d, f, g}, region, amf, tmsi}, e, ab)
      %sx : {List.length(&2, U32, _) == 11n : Nat}
      {==}

def L.nas.imeisv.decode_valid(bs, ds, e):
  +v = L.nas.mobile_identity.decode_valid(bs, Mi.Imeisv{ds}, e)
  (P.Nat.eq_of_is_eq(List.length(&2, U32, ds), 16n, P.Bool.and_true_r(B.Tbcd.all_digits(ds), Nat.is_eq(List.length(&2, U32, ds), 16n), v)), P.Bool.and_true_l(B.Tbcd.all_digits(ds), Nat.is_eq(List.length(&2, U32, ds), 16n), v))

# Payload container
# -----------------

def Len.len_of(lb: I.LenBody) -> U32:
  match lb:
    case I.LenBody{len, body}:
      len

def Len.body_of(lb: I.LenBody) -> B.Bytes():
  match lb:
    case I.LenBody{len, body}:
      body

def L.nas.payload_container.short(b1, b0, tail, e1, e0, short):
  sf = Equal.sym(U32, U32.and(65535, B.cat8(b0, b1)), B.cat8(b0, b1), P.U32.cat8_fits16(b0, b1, P.U32.lt256_mask8(b0, e0), P.U32.lt256_mask8(b1, e1)))
  %sf : {I.Len.take(B.cat8(b0, b1), tail, U32.is_eq(_, B.cat8(b0, b1))) == Fail{B.Short{}} : B.Read(I.LenBody)}
  sr = Equal.sym(Bool, U32.is_eq(B.cat8(b0, b1), B.cat8(b0, b1)), True{}, P.U32.is_eq_refl(B.cat8(b0, b1)))
  %sr : {I.Len.take(B.cat8(b0, b1), tail, _) == Fail{B.Short{}} : B.Read(I.LenBody)}
  st = Equal.sym(B.Read(B.Bytes()), B.take(U32.to_nat(B.cat8(b0, b1)), tail), Fail{B.Short{}}, PB.Short.take(U32.to_nat(B.cat8(b0, b1)), tail, short))
  %st : {I.Len.join(B.cat8(b0, b1), _) == Fail{B.Short{}} : B.Read(I.LenBody)}
  {==}

def Lve.Sx(len: U32, body: B.Bytes(), rest: B.Bytes(), tail: B.Bytes()) -> Type:
  {List.length(&2, U32, body) == U32.to_nat(len) : Nat} & {tail == List.append(&2, U32, body, rest) : B.Bytes()}

def Lve.sx_fin(+c: U32, +tail: B.Bytes(), +body2: B.Bytes(), +rest2: B.Bytes(), la: {List.length(&2, U32, body2) == U32.to_nat(c) : Nat} & {List.append(&2, U32, body2, rest2) == tail : B.Bytes()}) -> Lve.Sx(c, body2, rest2, tail):
  (l, a) = la
  (l, Equal.sym(B.Bytes(), List.append(&2, U32, body2, rest2), tail, a))

def Lve.sx_join(+c: U32, +tail: B.Bytes(), +len: U32, +body: B.Bytes(), +rest: B.Bytes(), rt: B.Read(B.Bytes()), ert: {B.take(U32.to_nat(c), tail) == rt : B.Read(B.Bytes())}, +e: {I.Len.join(c, rt) == Done{(I.LenBody{len, body}, rest)} : B.Read(I.LenBody)}) -> Lve.Sx(len, body, rest, tail):
  match rt:
    case Fail{x}:
      Empty.absurd(Lve.Sx(len, body, rest, tail), P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), x, (I.LenBody{len, body}, rest), e))
    case Done{(+body2, +rest2)}:
      +elb = Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, I.LenBody{len, body}), Done{(I.LenBody{c, body2}, rest2)}, Done{(I.LenBody{len, body}, rest)}, e)
      el = Equal.cong(I.LenBody, U32, x => Len.len_of(x), I.LenBody{c, body2}, I.LenBody{len, body}, elb)
      eb = Equal.cong(I.LenBody, B.Bytes(), x => Len.body_of(x), I.LenBody{c, body2}, I.LenBody{len, body}, elb)
      er = Equal.cong(B.Read(I.LenBody), B.Bytes(), x => P.Read.rest(I.LenBody, x, rest), Done{(I.LenBody{c, body2}, rest2)}, Done{(I.LenBody{len, body}, rest)}, e)
      %el : Lve.Sx(_, body, rest, tail)
      %eb : Lve.Sx(c, _, rest, tail)
      %er : Lve.Sx(c, body2, _, tail)
      Lve.sx_fin(c, tail, body2, rest2, L.bytes.take.length(U32.to_nat(c), tail, body2, rest2, ert))

def Lve.sx_take(+c: U32, +tail: B.Bytes(), +len: U32, +body: B.Bytes(), +rest: B.Bytes(), ok: Bool, +e: {I.Len.take(c, tail, ok) == Done{(I.LenBody{len, body}, rest)} : B.Read(I.LenBody)}) -> Lve.Sx(len, body, rest, tail):
  match ok:
    case False{}:
      Empty.absurd(Lve.Sx(len, body, rest, tail), P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Invalid{c}, (I.LenBody{len, body}, rest), e))
    case True{}:
      Lve.sx_join(c, tail, len, body, rest, B.take(U32.to_nat(c), tail), {==}, e)

def L.nas.payload_container.suffix(bs, len, body, rest, e):
  match bs:
    case Nil{}:
      Empty.absurd(Lve.Sx(len, body, rest, []), P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Short{}, (I.LenBody{len, body}, rest), e))
    case b <> Nil{}:
      Empty.absurd(Lve.Sx(len, body, rest, []), P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Short{}, (I.LenBody{len, body}, rest), e))
    case +b1 <> +b0 <> +tail:
      sd = Equal.sym(B.Bytes(), List.drop(&2, U32, tail, 0n), tail, P.List.drop0(tail))
      %sd : {List.length(&2, U32, body) == U32.to_nat(len) : Nat} & {_ == List.append(&2, U32, body, rest) : B.Bytes()}
      Lve.sx_take(B.cat8(b0, b1), tail, len, body, rest, I.fits16(B.cat8(b0, b1)), e)
