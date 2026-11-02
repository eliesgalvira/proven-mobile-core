import Base
import ../bytes.bend as B
import ../pfcp.bend as Pf
import ../tlv.bend as T
import ../LAWS.bend as L
import ./lib.bend as P
import ./bytes.bend as PB
import ./tlv.bend as PT

# Proofs of the PFCP laws (ticket 14).

def Msg.Res() -> Data:
  Result<&2, &2, B.Err, Pf.Msg>

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
      P.Nat.not_lt_zero({T.Tlv.read(a <> b <> c <> d <> t) == Fail{B.Short{}} : B.Read(T.Tlv)}, List.length(&2, U32, t), e)

# GHSA-37c3-hv4f-688p: the two halves of pfcp.ie.suffix.
def L.pfcp.ie.suffix(bs):
  (ie => rest => e => PT.Tlv.exact(bs, ie, rest, e), kind => len => tail => eh => ab => lt => PT.Tlv.short(bs, kind, len, tail, eh, ab, lt))

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

# What follows the length field, before any tail.
def Msg.body(seid: Maybe<&2, B.Bytes()>, seq: U32, ies: List<&2, T.Tlv>) -> B.Bytes():
  Pf.Seid.write(seid, B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, []))))

def Msg.take_body(seid: Maybe<&2, B.Bytes()>, +ies: List<&2, T.Tlv>, +seq: U32, +rest: B.Bytes()) -> {B.take(Pf.Msg.body_size(seid, ies), Pf.Seid.write(seid, B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, rest))))) == Done{(Msg.body(seid, seq, ies), rest)} : B.Read(B.Bytes())}:
  match seid:
    case None{}:
      wa = Equal.sym(B.Bytes(), T.Tlvs.write(ies, rest), List.append(&2, U32, T.Tlvs.write(ies, []), rest), PT.Tlvs.write_app(ies, rest))
      %wa : {B.take(Pf.Msg.body_size(None{}, ies), Pf.Seid.write(None{}, B.write_u24(seq, B.write_u8(0, _)))) == Done{(Msg.body(None{}, seq, ies), rest)} : B.Read(B.Bytes())}
      sl = Equal.sym(Nat, T.Tlvs.size(ies), List.length(&2, U32, T.Tlvs.write(ies, [])), PT.Tlvs.size_len(ies))
      %sl : {B.take(Nat.add(Pf.Seid.size(None{}), Nat.add(4n, _)), Pf.Seid.write(None{}, B.write_u24(seq, B.write_u8(0, List.append(&2, U32, T.Tlvs.write(ies, []), rest))))) == Done{(Msg.body(None{}, seq, ies), rest)} : B.Read(B.Bytes())}
      P.Take.append(B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, []))), rest)
    case Some{+sb}:
      wa = Equal.sym(B.Bytes(), T.Tlvs.write(ies, rest), List.append(&2, U32, T.Tlvs.write(ies, []), rest), PT.Tlvs.write_app(ies, rest))
      %wa : {B.take(Pf.Msg.body_size(Some{sb}, ies), Pf.Seid.write(Some{sb}, B.write_u24(seq, B.write_u8(0, _)))) == Done{(Msg.body(Some{sb}, seq, ies), rest)} : B.Read(B.Bytes())}
      sl = Equal.sym(Nat, T.Tlvs.size(ies), List.length(&2, U32, T.Tlvs.write(ies, [])), PT.Tlvs.size_len(ies))
      %sl : {B.take(Nat.add(Pf.Seid.size(Some{sb}), Nat.add(4n, _)), Pf.Seid.write(Some{sb}, B.write_u24(seq, B.write_u8(0, List.append(&2, U32, T.Tlvs.write(ies, []), rest))))) == Done{(Msg.body(Some{sb}, seq, ies), rest)} : B.Read(B.Bytes())}
      +Zb = B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, [])))
      al = P.List.append_len(sb, Zb)
      %al : {B.take(_, Pf.Seid.write(Some{sb}, B.write_u24(seq, B.write_u8(0, List.append(&2, U32, T.Tlvs.write(ies, []), rest))))) == Done{(Msg.body(Some{sb}, seq, ies), rest)} : B.Read(B.Bytes())}
      as = PT.Bytes.app_assoc(sb, Zb, rest)
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

def Msg.rt_seq(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, T.Tlv>, +rest: B.Bytes(), +f24: {Pf.fits24(seq) == True{} : Bool}, iv: {T.Tlvs.valid(ies) == True{} : Bool}) -> {Pf.Msg.with_rest(Pf.Msg.of_seq(kind, len, seid, B.u24(B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, []))))), rest) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}:
  +W = T.Tlvs.write(ies, [])
  +X = B.write_u8(0, W)
  su = Equal.sym(B.Read(U32), B.u24(B.write_u24(seq, X)), Done{(U32.and(16777215, seq), X)}, PB.Bits.u24(seq, X))
  %su : {Pf.Msg.with_rest(Pf.Msg.of_seq(kind, len, seid, _), rest) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}
  ss = Equal.sym(U32, U32.and(16777215, seq), seq, P.U32.eq_of_is_eq(U32.and(16777215, seq), seq, f24))
  %ss : {Pf.Msg.with_rest(Pf.Msg.seq_ok(kind, len, seid, _, X, Pf.fits24(_)), rest) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}
  sf24 = Equal.sym(Bool, Pf.fits24(seq), True{}, f24)
  %sf24 : {Pf.Msg.with_rest(Pf.Msg.seq_ok(kind, len, seid, seq, X, _), rest) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}
  ir = Equal.sym(PT.Tlvs.Res(), T.Tlvs.read(List.length(&2, U32, W), W), Done{ies}, PT.Tlvs.rt(ies, List.length(&2, U32, W), iv, P.Nat.le_refl(List.length(&2, U32, W))))
  %ir : {Pf.Msg.with_rest(Pf.Msg.of_ies(kind, len, seid, seq, _), rest) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}
  {==}

def Msg.rt_go(+kind: U32, +len: U32, seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, T.Tlv>, +rest: B.Bytes(), fk: {B.fits8(kind) == True{} : Bool}, fl: {B.fits16(len) == True{} : Bool}, sv: {Pf.Seid.valid(seid) == True{} : Bool}, f24: {Pf.fits24(seq) == True{} : Bool}, tn: {Nat.is_eq(U32.to_nat(len), Pf.Msg.body_size(seid, ies)) == True{} : Bool}, iv: {T.Tlvs.valid(ies) == True{} : Bool}) -> {Pf.Msg.read(Pf.Msg.write(Pf.Msg{kind, len, seid, seq, ies}, rest)) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}:
  match seid:
    case None{}:
      +Zr = B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, rest)))
      hdr = Equal.sym(B.Read(Pf.Msg), Pf.Msg.of_type(False{}, B.u8(B.write_u8(kind, B.write_u16(len, Zr)))), Pf.Msg.of_body(False{}, kind, len, B.take(U32.to_nat(len), Zr)), Msg.rt_hdr(False{}, kind, len, Zr, fk, fl))
      %hdr : {_ == Done{(Pf.Msg{kind, len, None{}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      stn = Equal.sym(Nat, U32.to_nat(len), Pf.Msg.body_size(None{}, ies), P.Nat.eq_of_is_eq(U32.to_nat(len), Pf.Msg.body_size(None{}, ies), tn))
      %stn : {Pf.Msg.of_body(False{}, kind, len, B.take(_, Zr)) == Done{(Pf.Msg{kind, len, None{}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      tb = Equal.sym(B.Read(B.Bytes()), B.take(Pf.Msg.body_size(None{}, ies), Zr), Done{(Msg.body(None{}, seq, ies), rest)}, Msg.take_body(None{}, ies, seq, rest))
      %tb : {Pf.Msg.of_body(False{}, kind, len, _) == Done{(Pf.Msg{kind, len, None{}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      Msg.rt_seq(kind, len, None{}, seq, ies, rest, f24, iv)
    case Some{+sb}:
      +Zr = B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, rest)))
      +Z = List.append(&2, U32, sb, Zr)
      hdr = Equal.sym(B.Read(Pf.Msg), Pf.Msg.of_type(True{}, B.u8(B.write_u8(kind, B.write_u16(len, Z)))), Pf.Msg.of_body(True{}, kind, len, B.take(U32.to_nat(len), Z)), Msg.rt_hdr(True{}, kind, len, Z, fk, fl))
      %hdr : {_ == Done{(Pf.Msg{kind, len, Some{sb}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      stn = Equal.sym(Nat, U32.to_nat(len), Pf.Msg.body_size(Some{sb}, ies), P.Nat.eq_of_is_eq(U32.to_nat(len), Pf.Msg.body_size(Some{sb}, ies), tn))
      %stn : {Pf.Msg.of_body(True{}, kind, len, B.take(_, Z)) == Done{(Pf.Msg{kind, len, Some{sb}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      tb = Equal.sym(B.Read(B.Bytes()), B.take(Pf.Msg.body_size(Some{sb}, ies), Z), Done{(Msg.body(Some{sb}, seq, ies), rest)}, Msg.take_body(Some{sb}, ies, seq, rest))
      %tb : {Pf.Msg.of_body(True{}, kind, len, _) == Done{(Pf.Msg{kind, len, Some{sb}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      +Zb = B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, [])))
      s8 = P.Nat.eq_of_is_eq(List.length(&2, U32, sb), 8n, sv)
      %s8 : {Pf.Msg.with_rest(Pf.Msg.of_seid(kind, len, B.take(_, List.append(&2, U32, sb, Zb))), rest) == Done{(Pf.Msg{kind, len, Some{sb}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      ta = Equal.sym(B.Read(B.Bytes()), B.take(List.length(&2, U32, sb), List.append(&2, U32, sb, Zb)), Done{(sb, Zb)}, P.Take.append(sb, Zb))
      %ta : {Pf.Msg.with_rest(Pf.Msg.of_seid(kind, len, _), rest) == Done{(Pf.Msg{kind, len, Some{sb}, seq, ies}, rest)} : B.Read(Pf.Msg)}
      Msg.rt_seq(kind, len, Some{sb}, seq, ies, rest, f24, iv)

def Msg.rt(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, T.Tlv>, +rest: B.Bytes(), +v: {Pf.Msg.valid(Pf.Msg{kind, len, seid, seq, ies}) == True{} : Bool}) -> {Pf.Msg.read(Pf.Msg.write(Pf.Msg{kind, len, seid, seq, ies}, rest)) == Done{(Pf.Msg{kind, len, seid, seq, ies}, rest)} : B.Read(Pf.Msg)}:
  +R4 = Bool.and(Nat.is_eq(U32.to_nat(len), Pf.Msg.body_size(seid, ies)), T.Tlvs.valid(ies))
  +R3 = Bool.and(Pf.fits24(seq), R4)
  +R2 = Bool.and(Pf.Seid.valid(seid), R3)
  +R1 = Bool.and(B.fits16(len), R2)
  +v2 = P.Bool.and_true_r(B.fits8(kind), R1, v)
  +v3 = P.Bool.and_true_r(B.fits16(len), R2, v2)
  +v4 = P.Bool.and_true_r(Pf.Seid.valid(seid), R3, v3)
  +v5 = P.Bool.and_true_r(Pf.fits24(seq), R4, v4)
  Msg.rt_go(kind, len, seid, seq, ies, rest, P.Bool.and_true_l(B.fits8(kind), R1, v), P.Bool.and_true_l(B.fits16(len), R2, v2), P.Bool.and_true_l(Pf.Seid.valid(seid), R3, v3), P.Bool.and_true_l(Pf.fits24(seq), R4, v4), P.Bool.and_true_l(Nat.is_eq(U32.to_nat(len), Pf.Msg.body_size(seid, ies)), T.Tlvs.valid(ies), v5), P.Bool.and_true_r(Nat.is_eq(U32.to_nat(len), Pf.Msg.body_size(seid, ies)), T.Tlvs.valid(ies), v5))

def L.pfcp.roundtrip(m, rest, v):
  match m:
    case Pf.Msg{+kind, +len, +seid, +seq, +ies}:
      Msg.rt(kind, len, seid, seq, ies, rest, v)

# Reading: what a message reader answered. One chain yields decode_valid,
# suffix and length_consistent.

# The octets after the SEID: sequence number, spare, IEs.
def Tail.Spec(body: B.Bytes(), seq: U32, ies: List<&2, T.Tlv>) -> Type:
  {Pf.fits24(seq) == True{} : Bool} & ({T.Tlvs.valid(ies) == True{} : Bool} & ({Nat.add(4n, T.Tlvs.size(ies)) == List.length(&2, U32, body) : Nat} & ({B.all_bytes(body) == True{} : Bool} -> @tail: B.Bytes() -> {B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, tail))) == List.append(&2, U32, body, tail) : B.Bytes()})))

# The octets after the length field.
def Body.Spec(body: B.Bytes(), seid: Maybe<&2, B.Bytes()>, seq: U32, ies: List<&2, T.Tlv>) -> Type:
  {Pf.Seid.valid(seid) == True{} : Bool} & ({Pf.fits24(seq) == True{} : Bool} & ({T.Tlvs.valid(ies) == True{} : Bool} & ({Pf.Msg.body_size(seid, ies) == List.length(&2, U32, body) : Nat} & ({B.all_bytes(body) == True{} : Bool} -> @tail: B.Bytes() -> {Pf.Seid.write(seid, B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, tail)))) == List.append(&2, U32, body, tail) : B.Bytes()}))))

def Msg.Spec(bs: B.Bytes(), m: Pf.Msg, rest: B.Bytes()) -> Type:
  {Pf.Msg.valid(m) == True{} : Bool} & (({B.all_bytes(bs) == True{} : Bool} -> {Pf.Msg.write(m, rest) == bs : B.Bytes()}) & {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(U32.to_nat(Pf.Msg.len(m)), List.length(&2, U32, rest))) : Nat})

def Tail.write(+b2: U32, +b1: U32, +b0: U32, +sp: U32, +iesb: B.Bytes(), +ies: List<&2, T.Tlv>, +eri: {T.Tlvs.read(List.length(&2, U32, iesb), iesb) == Done{ies} : PT.Tlvs.Res()}, e0: {sp == 0 : U32}, +ab: {B.all_bytes(b2 <> b1 <> b0 <> sp <> iesb) == True{} : Bool}, +tail: B.Bytes()) -> {B.write_u24(B.cat8(b0, B.cat8(b1, b2)), B.write_u8(0, T.Tlvs.write(ies, tail))) == List.append(&2, U32, b2 <> b1 <> b0 <> sp <> iesb, tail) : B.Bytes()}:
  +ab2 = P.Bool.and_true_r(B.is_byte(b2), B.all_bytes(b1 <> b0 <> sp <> iesb), ab)
  +ab3 = P.Bool.and_true_r(B.is_byte(b1), B.all_bytes(b0 <> sp <> iesb), ab2)
  +ab4 = P.Bool.and_true_r(B.is_byte(b0), B.all_bytes(sp <> iesb), ab3)
  +X = B.write_u8(0, T.Tlvs.write(ies, tail))
  w = Equal.sym(B.Bytes(), B.write_u24(B.cat8(b0, B.cat8(b1, b2)), X), b2 <> b1 <> b0 <> X, P.Bytes.u24_sx(b2, b1, b0, P.U32.lt256_mask8(b2, P.Bool.and_true_l(B.is_byte(b2), B.all_bytes(b1 <> b0 <> sp <> iesb), ab)), P.U32.lt256_mask8(b1, P.Bool.and_true_l(B.is_byte(b1), B.all_bytes(b0 <> sp <> iesb), ab2)), P.U32.lt256_mask8(b0, P.Bool.and_true_l(B.is_byte(b0), B.all_bytes(sp <> iesb), ab3)), X))
  %w : {_ == List.append(&2, U32, b2 <> b1 <> b0 <> sp <> iesb, tail) : B.Bytes()}
  se0 = Equal.sym(U32, sp, 0, e0)
  %se0 : {b2 <> b1 <> b0 <> X == List.append(&2, U32, b2 <> b1 <> b0 <> _ <> iesb, tail) : B.Bytes()}
  Equal.cong(B.Bytes(), B.Bytes(), l => b2 <> b1 <> b0 <> B.write_u8(0, l), T.Tlvs.write(ies, tail), List.append(&2, U32, iesb, tail), PT.Tlvs.sx(List.length(&2, U32, iesb), iesb, ies, eri, P.Bool.and_true_r(B.is_byte(sp), B.all_bytes(iesb), ab4), tail))

def Tail.fin(+b2: U32, +b1: U32, +b0: U32, +sp: U32, +iesb: B.Bytes(), +ies: List<&2, T.Tlv>, +eri: {T.Tlvs.read(List.length(&2, U32, iesb), iesb) == Done{ies} : PT.Tlvs.Res()}, f24: {Pf.fits24(B.cat8(b0, B.cat8(b1, b2))) == True{} : Bool}, e0: {sp == 0 : U32}) -> Tail.Spec(b2 <> b1 <> b0 <> sp <> iesb, B.cat8(b0, B.cat8(b1, b2)), ies):
  (f24, (PT.Tlvs.dv(List.length(&2, U32, iesb), iesb, ies, eri), (Equal.cong(Nat, Nat, n => 1n+1n+1n+1n+n, T.Tlvs.size(ies), List.length(&2, U32, iesb), PT.Tlvs.len(List.length(&2, U32, iesb), iesb, ies, eri)), ab => tail => Tail.write(b2, b1, b0, sp, iesb, ies, eri, e0, ab, tail))))

def Body.none(+body: B.Bytes(), +seq: U32, +ies: List<&2, T.Tlv>, tsp: Tail.Spec(body, seq, ies)) -> Body.Spec(body, None{}, seq, ies):
  (f24, t1) = tsp
  (iv, t2) = t1
  (tsz, tw) = t2
  ({==}, (f24, (iv, (tsz, tw))))

def Body.some.write(+sb: B.Bytes(), +r5: B.Bytes(), +body: B.Bytes(), +seq: U32, +ies: List<&2, T.Tlv>, +ap: {List.append(&2, U32, sb, r5) == body : B.Bytes()}, tw: {B.all_bytes(r5) == True{} : Bool} -> @tail: B.Bytes() -> {B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, tail))) == List.append(&2, U32, r5, tail) : B.Bytes()}, ab: {B.all_bytes(body) == True{} : Bool}, +tail: B.Bytes()) -> {Pf.Seid.write(Some{sb}, B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, tail)))) == List.append(&2, U32, body, tail) : B.Bytes()}:
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, sb, r5), body, ap)
  %ap : {Pf.Seid.write(Some{sb}, B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, tail)))) == List.append(&2, U32, _, tail) : B.Bytes()}
  as = Equal.sym(B.Bytes(), List.append(&2, U32, List.append(&2, U32, sb, r5), tail), List.append(&2, U32, sb, List.append(&2, U32, r5, tail)), PT.Bytes.app_assoc(sb, r5, tail))
  %as : {List.append(&2, U32, sb, B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, tail)))) == _ : B.Bytes()}
  Equal.cong(B.Bytes(), B.Bytes(), l => List.append(&2, U32, sb, l), B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, tail))), List.append(&2, U32, r5, tail), tw(PB.Bytes.all_app(sb, r5, (%sap : {B.all_bytes(_) == True{} : Bool}; ab)), tail))

def Body.some(+sb: B.Bytes(), +r5: B.Bytes(), +body: B.Bytes(), +seq: U32, +ies: List<&2, T.Tlv>, la: {List.length(&2, U32, sb) == 8n : Nat} & {List.append(&2, U32, sb, r5) == body : B.Bytes()}, tsp: Tail.Spec(r5, seq, ies)) -> Body.Spec(body, Some{sb}, seq, ies):
  (l8, +ap) = la
  (f24, t1) = tsp
  (iv, t2) = t1
  (tsz, tw) = t2
  sl8 = Equal.sym(Nat, List.length(&2, U32, sb), 8n, l8)
  stsz = Equal.sym(Nat, Nat.add(4n, T.Tlvs.size(ies)), List.length(&2, U32, r5), tsz)
  ((%sl8 : {Nat.is_eq(_, 8n) == True{} : Bool}; P.Nat.is_eq_refl(8n)), (f24, (iv, ((%ap : {Pf.Msg.body_size(Some{sb}, ies) == List.length(&2, U32, _) : Nat}; (%stsz : {Nat.add(List.length(&2, U32, sb), _) == List.length(&2, U32, List.append(&2, U32, sb, r5)) : Nat}; Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, sb, r5)), Nat.add(List.length(&2, U32, sb), List.length(&2, U32, r5)), P.List.append_len(sb, r5)))), ab => tail => Body.some.write(sb, r5, body, seq, ies, ap, tw, ab, tail)))))

def Body.spec.ies(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, +b2: U32, +b1: U32, +b0: U32, +sp: U32, +iesb: B.Bytes(), ri: PT.Tlvs.Res(), +eri: {T.Tlvs.read(List.length(&2, U32, iesb), iesb) == ri : PT.Tlvs.Res()}, +m: Pf.Msg, e: {Pf.Msg.of_ies(kind, len, seid, B.cat8(b0, B.cat8(b1, b2)), ri) == Done{m} : Msg.Res()}, -G: Type, k: @seq: U32 -> @ies: List<&2, T.Tlv> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> Tail.Spec(b2 <> b1 <> b0 <> sp <> iesb, seq, ies) -> G, f24: {Pf.fits24(B.cat8(b0, B.cat8(b1, b2))) == True{} : Bool}, e0: {sp == 0 : U32}) -> G:
  match ri:
    case Fail{err}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, err, m, e))
    case Done{+ies}:
      k(B.cat8(b0, B.cat8(b1, b2)), ies, Equal.cong(Msg.Res(), Pf.Msg, x => P.Res.value(B.Err, Pf.Msg, x, m), Done{Pf.Msg{kind, len, seid, B.cat8(b0, B.cat8(b1, b2)), ies}}, Done{m}, e), Tail.fin(b2, b1, b0, sp, iesb, ies, eri, f24, e0))

def Body.spec.spare(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, +b2: U32, +b1: U32, +b0: U32, +sp: U32, +iesb: B.Bytes(), ok: Bool, eok: {U32.is_eq(sp, 0) == ok : Bool}, +m: Pf.Msg, e: {Pf.Msg.spare_ok(kind, len, seid, B.cat8(b0, B.cat8(b1, b2)), sp, iesb, ok) == Done{m} : Msg.Res()}, -G: Type, k: @seq: U32 -> @ies: List<&2, T.Tlv> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> Tail.Spec(b2 <> b1 <> b0 <> sp <> iesb, seq, ies) -> G, f24: {Pf.fits24(B.cat8(b0, B.cat8(b1, b2))) == True{} : Bool}) -> G:
  match ok:
    case False{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Invalid{sp}, m, e))
    case True{}:
      Body.spec.ies(kind, len, seid, b2, b1, b0, sp, iesb, T.Tlvs.read(List.length(&2, U32, iesb), iesb), {==}, m, e, G, k, f24, P.U32.eq_of_is_eq(sp, 0, eok))

def Body.spec.seq(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, +b2: U32, +b1: U32, +b0: U32, ok: Bool, eok: {Pf.fits24(B.cat8(b0, B.cat8(b1, b2))) == ok : Bool}, r6: B.Bytes(), +m: Pf.Msg, e: {Pf.Msg.seq_ok(kind, len, seid, B.cat8(b0, B.cat8(b1, b2)), r6, ok) == Done{m} : Msg.Res()}, -G: Type, k: @seq: U32 -> @ies: List<&2, T.Tlv> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> Tail.Spec(b2 <> b1 <> b0 <> r6, seq, ies) -> G) -> G:
  match ok:
    case False{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Invalid{B.cat8(b0, B.cat8(b1, b2))}, m, e))
    case True{}:
      match r6:
        case Nil{}:
          Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Short{}, m, e))
        case +sp <> +iesb:
          Body.spec.spare(kind, len, seid, b2, b1, b0, sp, iesb, U32.is_eq(sp, 0), {==}, m, e, G, k, eok)

def Body.spec.u24(+kind: U32, +len: U32, +seid: Maybe<&2, B.Bytes()>, body: B.Bytes(), +m: Pf.Msg, e: {Pf.Msg.of_seq(kind, len, seid, B.u24(body)) == Done{m} : Msg.Res()}, -G: Type, k: @seq: U32 -> @ies: List<&2, T.Tlv> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> Tail.Spec(body, seq, ies) -> G) -> G:
  match body:
    case Nil{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Short{}, m, e))
    case a <> Nil{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Short{}, m, e))
    case a <> b <> Nil{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, B.Short{}, m, e))
    case +b2 <> +b1 <> +b0 <> +r6:
      Body.spec.seq(kind, len, seid, b2, b1, b0, Pf.fits24(B.cat8(b0, B.cat8(b1, b2))), {==}, r6, m, e, G, k)

def Body.spec.seid(+kind: U32, +len: U32, +body: B.Bytes(), rt: B.Read(B.Bytes()), +ert: {B.take(8n, body) == rt : B.Read(B.Bytes())}, +m: Pf.Msg, e: {Pf.Msg.of_seid(kind, len, rt) == Done{m} : Msg.Res()}, -G: Type, k: @seid: Maybe<&2, B.Bytes()> -> @seq: U32 -> @ies: List<&2, T.Tlv> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> {Pf.Seid.flags(seid) == Flags.of(True{}) : U32} -> Body.Spec(body, seid, seq, ies) -> G) -> G:
  match rt:
    case Fail{err}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, Pf.Msg, err, m, e))
    case Done{(+sb, +r5)}:
      Body.spec.u24(kind, len, Some{sb}, r5, m, e, G, +seq => +ies => em => tsp => k(Some{sb}, seq, ies, em, {==}, Body.some(sb, r5, body, seq, ies, L.bytes.take.length(8n, body, sb, r5, ert), tsp)))

def Body.spec(s: Bool, +kind: U32, +len: U32, +body: B.Bytes(), +m: Pf.Msg, e: {Pf.Msg.parse(s, kind, len, body) == Done{m} : Msg.Res()}, -G: Type, k: @seid: Maybe<&2, B.Bytes()> -> @seq: U32 -> @ies: List<&2, T.Tlv> -> {Pf.Msg{kind, len, seid, seq, ies} == m : Pf.Msg} -> {Pf.Seid.flags(seid) == Flags.of(s) : U32} -> Body.Spec(body, seid, seq, ies) -> G) -> G:
  match s:
    case False{}:
      Body.spec.u24(kind, len, None{}, body, m, e, G, +seq => +ies => em => tsp => k(None{}, seq, ies, em, {==}, Body.none(body, seq, ies, tsp)))
    case True{}:
      Body.spec.seid(kind, len, body, B.take(8n, body), {==}, m, e, G, k)

def Msg.spec.valid(+kind: U32, +b0: U32, +b1: U32, +seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, T.Tlv>, +body: B.Bytes(), fk: {B.fits8(kind) == True{} : Bool}, fl: {B.fits16(B.cat8(b0, b1)) == True{} : Bool}, sv: {Pf.Seid.valid(seid) == True{} : Bool}, f24: {Pf.fits24(seq) == True{} : Bool}, iv: {T.Tlvs.valid(ies) == True{} : Bool}, bsz: {Pf.Msg.body_size(seid, ies) == List.length(&2, U32, body) : Nat}, ln: {List.length(&2, U32, body) == U32.to_nat(B.cat8(b0, b1)) : Nat}) -> {Pf.Msg.valid(Pf.Msg{kind, B.cat8(b0, b1), seid, seq, ies}) == True{} : Bool}:
  sbsz = Equal.sym(Nat, Pf.Msg.body_size(seid, ies), List.length(&2, U32, body), bsz)
  tn : {Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)) == True{} : Bool} = (%ln : {Nat.is_eq(_, Pf.Msg.body_size(seid, ies)) == True{} : Bool}; (%sbsz : {Nat.is_eq(List.length(&2, U32, body), _) == True{} : Bool}; P.Nat.is_eq_refl(List.length(&2, U32, body))))
  P.Bool.and_intro(B.fits8(kind), Bool.and(B.fits16(B.cat8(b0, b1)), Bool.and(Pf.Seid.valid(seid), Bool.and(Pf.fits24(seq), Bool.and(Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)), T.Tlvs.valid(ies))))), fk, P.Bool.and_intro(B.fits16(B.cat8(b0, b1)), Bool.and(Pf.Seid.valid(seid), Bool.and(Pf.fits24(seq), Bool.and(Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)), T.Tlvs.valid(ies)))), fl, P.Bool.and_intro(Pf.Seid.valid(seid), Bool.and(Pf.fits24(seq), Bool.and(Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)), T.Tlvs.valid(ies))), sv, P.Bool.and_intro(Pf.fits24(seq), Bool.and(Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)), T.Tlvs.valid(ies)), f24, P.Bool.and_intro(Nat.is_eq(U32.to_nat(B.cat8(b0, b1)), Pf.Msg.body_size(seid, ies)), T.Tlvs.valid(ies), tn, iv)))))

def Msg.spec.write(+s: Bool, +flags: U32, +kind: U32, +b1: U32, +b0: U32, +r3: B.Bytes(), +body: B.Bytes(), +r4: B.Bytes(), +seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, T.Tlv>, sf: {Pf.Seid.flags(seid) == Flags.of(s) : U32}, ef: {flags == Flags.of(s) : U32}, fk: {B.fits8(kind) == True{} : Bool}, +ap: {List.append(&2, U32, body, r4) == r3 : B.Bytes()}, wb: {B.all_bytes(body) == True{} : Bool} -> @tail: B.Bytes() -> {Pf.Seid.write(seid, B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, tail)))) == List.append(&2, U32, body, tail) : B.Bytes()}, +ab: {B.all_bytes(flags <> kind <> b1 <> b0 <> r3) == True{} : Bool}) -> {Pf.Msg.write(Pf.Msg{kind, B.cat8(b0, b1), seid, seq, ies}, r4) == flags <> kind <> b1 <> b0 <> r3 : B.Bytes()}:
  +Z = Pf.Seid.write(seid, B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, r4))))
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

def Msg.spec.fin(+s: Bool, +flags: U32, +kind: U32, +b1: U32, +b0: U32, +r3: B.Bytes(), +body: B.Bytes(), +r4: B.Bytes(), +seid: Maybe<&2, B.Bytes()>, +seq: U32, +ies: List<&2, T.Tlv>, +m: Pf.Msg, em: {Pf.Msg{kind, B.cat8(b0, b1), seid, seq, ies} == m : Pf.Msg}, sf: {Pf.Seid.flags(seid) == Flags.of(s) : U32}, bsp: Body.Spec(body, seid, seq, ies), ef: {flags == Flags.of(s) : U32}, +fk: {B.fits8(kind) == True{} : Bool}, fl: {B.fits16(B.cat8(b0, b1)) == True{} : Bool}, la: {List.length(&2, U32, body) == U32.to_nat(B.cat8(b0, b1)) : Nat} & {List.append(&2, U32, body, r4) == r3 : B.Bytes()}) -> Msg.Spec(flags <> kind <> b1 <> b0 <> r3, m, r4):
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
