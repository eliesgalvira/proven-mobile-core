import Base
import ../bytes.bend as B
import ../tlv.bend as T
import ../frame.bend as F
import ../LAWS.bend as L
import ./lib.bend as P
import ./bytes.bend as PB
import ./tlv.bend as PT

# Proofs of the frame laws (ticket 15).

# Envelope
# --------

def L.frame.max_length(b3, b2, b1, b0, rest, e):
  se = Equal.sym(Bool, Nat.is_lt(262144n, U32.to_nat(B.cat8(b0, B.cat8(b1, B.cat8(b2, b3))))), True{}, e)
  %se : {F.Frame.body(B.cat8(b0, B.cat8(b1, B.cat8(b2, b3))), rest, _) == Fail{B.Invalid{B.cat8(b0, B.cat8(b1, B.cat8(b2, b3)))}} : B.Read(B.Bytes())}
  {==}

# Config
# ------

def L.frame.config.repeat_replaces(tl, tag, len, v):
  match tl:
    case Nil{}:
      sr = Equal.sym(Bool, U32.is_eq(tag, tag), True{}, P.U32.is_eq_refl(tag))
      %sr : {F.Config.pick(v, None{}, _) == Some{v} : Maybe<&2, B.Bytes()>}
      {==}
    case T.Tlv{kind, l, w} <> +more:
      ih = Equal.sym(Maybe<&2, B.Bytes()>, F.Config.get(tag, List.append(&2, T.Tlv, more, [T.Tlv{tag, len, v}])), Some{v}, L.frame.config.repeat_replaces(more, tag, len, v))
      %ih : {F.Config.pick(w, _, U32.is_eq(kind, tag)) == Some{v} : Maybe<&2, B.Bytes()>}
      {==}

# Roundtrip
# ---------

def U32.rt(+v: U32, +rest: B.Bytes()) -> {Done{(v, rest)} == B.u32(B.write_u32(v, rest)) : B.Read(U32)}:
  Equal.sym(B.Read(U32), B.u32(B.write_u32(v, rest)), Done{(v, rest)}, L.bytes.u32.roundtrip(v, rest))

def U16.rt(+v: U32, +rest: B.Bytes(), f: {B.fits16(v) == True{} : Bool}) -> {Done{(v, rest)} == B.u16(B.write_u16(v, rest)) : B.Read(U32)}:
  ev = P.U32.eq_of_is_eq(U32.and(65535, v), v, f)
  %ev : {Done{(_, rest)} == B.u16(B.write_u16(v, rest)) : B.Read(U32)}
  Equal.sym(B.Read(U32), B.u16(B.write_u16(v, rest)), Done{(U32.and(65535, v), rest)}, PB.Bits.u16(v, rest))

def Take.rt(+len: U32, +bytes: B.Bytes(), +W: B.Bytes(), el: {Nat.is_eq(U32.to_nat(len), List.length(&2, U32, bytes)) == True{} : Bool}) -> {Done{(bytes, W)} == B.take(U32.to_nat(len), List.append(&2, U32, bytes, W)) : B.Read(B.Bytes())}:
  sl = Equal.sym(Nat, U32.to_nat(len), List.length(&2, U32, bytes), P.Nat.eq_of_is_eq(U32.to_nat(len), List.length(&2, U32, bytes), el))
  %sl : {Done{(bytes, W)} == B.take(_, List.append(&2, U32, bytes, W)) : B.Read(B.Bytes())}
  Equal.sym(B.Read(B.Bytes()), B.take(List.length(&2, U32, bytes), List.append(&2, U32, bytes, W)), Done{(bytes, W)}, P.Take.append(bytes, W))

def Level.rt(level: F.Level) -> {F.Level.of(U32.to_nat(U32.and(255, F.Level.byte(level)))) == Some{level} : Maybe<&2, F.Level>}:
  match level:
    case F.Debug{}:
      {==}
    case F.Info{}:
      {==}
    case F.Warn{}:
      {==}
    case F.Error{}:
      {==}

def Action.rt(a: F.Action, +W: B.Bytes(), +v: {F.Action.valid(a) == True{} : Bool}) -> {F.Action.read(F.Action.write(a, W)) == Done{(a, W)} : B.Read(F.Action)}:
  match a:
    case F.NgapSend{+assoc, +stream, +len, +bytes}:
      +D : B.Read(F.Action) = Done{(F.NgapSend{assoc, stream, len, bytes}, W)}
      +Y = B.write_u32(len, List.append(&2, U32, bytes, W))
      r1 = U32.rt(assoc, B.write_u16(stream, Y))
      %r1 : {F.Action.send(_) == D : B.Read(F.Action)}
      +fs = P.Bool.and_true_l(B.fits16(stream), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, bytes)), v)
      r2 = U16.rt(stream, Y, fs)
      %r2 : {F.Action.send_of_stream(assoc, _) == D : B.Read(F.Action)}
      sfs = Equal.sym(Bool, B.fits16(stream), True{}, fs)
      %sfs : {F.Action.send_stream_ok(assoc, stream, Y, _) == D : B.Read(F.Action)}
      r3 = U32.rt(len, List.append(&2, U32, bytes, W))
      %r3 : {F.Action.send_of_len(assoc, stream, _) == D : B.Read(F.Action)}
      tk = Take.rt(len, bytes, W, P.Bool.and_true_r(B.fits16(stream), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, bytes)), v))
      %tk : {F.Action.send_of_bytes(assoc, stream, len, _) == D : B.Read(F.Action)}
      {==}
    case F.NgapClose{+assoc}:
      r1 = U32.rt(assoc, W)
      %r1 : {F.Action.close(_) == Done{(F.NgapClose{assoc}, W)} : B.Read(F.Action)}
      {==}
    case F.PfcpSend{+len, +bytes}:
      r1 = U32.rt(len, List.append(&2, U32, bytes, W))
      %r1 : {F.Action.pfcp(_) == Done{(F.PfcpSend{len, bytes}, W)} : B.Read(F.Action)}
      tk = Take.rt(len, bytes, W, v)
      %tk : {F.Action.pfcp_of_bytes(len, _) == Done{(F.PfcpSend{len, bytes}, W)} : B.Read(F.Action)}
      {==}
    case F.TimerStart{+timer, +ms}:
      r1 = U32.rt(timer, B.write_u32(ms, W))
      %r1 : {F.Action.start(_) == Done{(F.TimerStart{timer, ms}, W)} : B.Read(F.Action)}
      r2 = U32.rt(ms, W)
      %r2 : {F.Action.start_of_ms(timer, _) == Done{(F.TimerStart{timer, ms}, W)} : B.Read(F.Action)}
      {==}
    case F.TimerCancel{+timer}:
      r1 = U32.rt(timer, W)
      %r1 : {F.Action.cancel(_) == Done{(F.TimerCancel{timer}, W)} : B.Read(F.Action)}
      {==}
    case F.Log{+level, +len, +text}:
      +D : B.Read(F.Action) = Done{(F.Log{level, len, text}, W)}
      +Z = B.write_u32(len, List.append(&2, U32, text, W))
      lr = Equal.sym(Maybe<&2, F.Level>, F.Level.of(U32.to_nat(U32.and(255, F.Level.byte(level)))), Some{level}, Level.rt(level))
      %lr : {F.Action.log_level(_, U32.and(255, F.Level.byte(level)), Z) == D : B.Read(F.Action)}
      r1 = U32.rt(len, List.append(&2, U32, text, W))
      %r1 : {F.Action.log_of_len(level, _) == D : B.Read(F.Action)}
      tk = Take.rt(len, text, W, v)
      %tk : {F.Action.log_of_text(level, len, _) == D : B.Read(F.Action)}
      {==}

def Items.rt(items: List<&2, F.Action>, +W: B.Bytes(), +v: {F.Items.valid(items) == True{} : Bool}) -> {F.Items.read(List.length(&2, F.Action, items), F.Items.write(items, W)) == Done{(items, W)} : B.Read(List<&2, F.Action>)}:
  match items:
    case Nil{}:
      {==}
    case +a <> +more:
      +W2 = F.Items.write(more, W)
      ar = Equal.sym(B.Read(F.Action), F.Action.read(F.Action.write(a, W2)), Done{(a, W2)}, Action.rt(a, W2, P.Bool.and_true_l(F.Action.valid(a), F.Items.valid(more), v)))
      %ar : {F.Items.next(_, left => F.Items.read(List.length(&2, F.Action, more), left)) == Done{(a <> more, W)} : B.Read(List<&2, F.Action>)}
      ih = Equal.sym(B.Read(List<&2, F.Action>), F.Items.read(List.length(&2, F.Action, more), W2), Done{(more, W)}, Items.rt(more, W, P.Bool.and_true_r(F.Action.valid(a), F.Items.valid(more), v)))
      %ih : {B.Read.cons(F.Action, a, _) == Done{(a <> more, W)} : B.Read(List<&2, F.Action>)}
      {==}

def Actions.rt(+count: U32, +items: List<&2, F.Action>, +rest: B.Bytes(), +v: {F.Actions.valid(F.Actions{count, items}) == True{} : Bool}) -> {F.Actions.read(F.Actions.write(F.Actions{count, items}, rest)) == Done{(F.Actions{count, items}, rest)} : B.Read(F.Actions)}:
  +D : B.Read(F.Actions) = Done{(F.Actions{count, items}, rest)}
  +W = F.Items.write(items, rest)
  +C = Nat.is_eq(U32.to_nat(count), List.length(&2, F.Action, items))
  +v2 = P.Bool.and_true_r(B.fits16(count), Bool.and(C, F.Items.valid(items)), v)
  r1 = U16.rt(count, W, P.Bool.and_true_l(B.fits16(count), Bool.and(C, F.Items.valid(items)), v))
  %r1 : {F.Actions.of_count(_) == D : B.Read(F.Actions)}
  sc = Equal.sym(Nat, U32.to_nat(count), List.length(&2, F.Action, items), P.Nat.eq_of_is_eq(U32.to_nat(count), List.length(&2, F.Action, items), P.Bool.and_true_l(C, F.Items.valid(items), v2)))
  %sc : {F.Actions.of_items(count, F.Items.read(_, W)) == D : B.Read(F.Actions)}
  ir = Equal.sym(B.Read(List<&2, F.Action>), F.Items.read(List.length(&2, F.Action, items), W), Done{(items, rest)}, Items.rt(items, rest, P.Bool.and_true_r(C, F.Items.valid(items), v2)))
  %ir : {F.Actions.of_items(count, _) == D : B.Read(F.Actions)}
  {==}

def L.frame.actions.roundtrip(as, rest, v):
  match as:
    case F.Actions{+count, +items}:
      Actions.rt(count, items, rest, v)

def Evt.rt(ev: F.Evt, +en: B.Bytes(), +rest: B.Bytes(), +v: {F.Evt.valid(ev) == True{} : Bool}) -> {F.Input.of_event(en, F.Evt.payload(U32.and(255, F.Evt.kind(ev)), F.Evt.write(ev, rest))) == Done{(F.Input{en, ev}, rest)} : B.Read(F.Input)}:
  match ev:
    case F.Config{+len, +tlvs}:
      +D : B.Read(F.Input) = Done{(F.Input{en, F.Config{len, tlvs}}, rest)}
      +W = T.Tlvs.write(tlvs, [])
      +sz = Nat.is_eq(U32.to_nat(len), T.Tlvs.size(tlvs))
      +R = Bool.and(T.Tlvs.valid(tlvs), F.Tags.valid(tlvs))
      r1 = U32.rt(len, T.Tlvs.write(tlvs, rest))
      %r1 : {F.Input.of_event(en, F.Evt.config(_)) == D : B.Read(F.Input)}
      wa = Equal.sym(B.Bytes(), T.Tlvs.write(tlvs, rest), List.append(&2, U32, W, rest), PT.Tlvs.write_app(tlvs, rest))
      %wa : {F.Input.of_event(en, F.Evt.config_of_body(len, B.take(U32.to_nat(len), _))) == D : B.Read(F.Input)}
      sl = PT.Tlvs.size_len(tlvs)
      el : {Nat.is_eq(U32.to_nat(len), List.length(&2, U32, W)) == True{} : Bool} = (%sl : {Nat.is_eq(U32.to_nat(len), _) == True{} : Bool}; P.Bool.and_true_l(sz, R, v))
      tk = Take.rt(len, W, rest, el)
      %tk : {F.Input.of_event(en, F.Evt.config_of_body(len, _)) == D : B.Read(F.Input)}
      +v2 = P.Bool.and_true_r(sz, R, v)
      tr = Equal.sym(PT.Tlvs.Res(), T.Tlvs.read(List.length(&2, U32, W), W), Done{tlvs}, PT.Tlvs.rt(tlvs, List.length(&2, U32, W), P.Bool.and_true_l(T.Tlvs.valid(tlvs), F.Tags.valid(tlvs), v2), P.Nat.le_refl(List.length(&2, U32, W))))
      %tr : {F.Input.of_event(en, F.Evt.config_of_tlvs(len, rest, _)) == D : B.Read(F.Input)}
      st = Equal.sym(Bool, F.Tags.valid(tlvs), True{}, P.Bool.and_true_r(T.Tlvs.valid(tlvs), F.Tags.valid(tlvs), v2))
      %st : {F.Input.of_event(en, F.Evt.config_tags(len, rest, tlvs, _)) == D : B.Read(F.Input)}
      {==}
    case F.NgapAssocUp{+assoc}:
      r1 = U32.rt(assoc, rest)
      %r1 : {F.Input.of_event(en, F.Evt.assoc_up(_)) == Done{(F.Input{en, F.NgapAssocUp{assoc}}, rest)} : B.Read(F.Input)}
      {==}
    case F.NgapAssocDown{+assoc}:
      r1 = U32.rt(assoc, rest)
      %r1 : {F.Input.of_event(en, F.Evt.assoc_down(_)) == Done{(F.Input{en, F.NgapAssocDown{assoc}}, rest)} : B.Read(F.Input)}
      {==}
    case F.NgapData{+assoc, +stream, +len, +bytes}:
      +D : B.Read(F.Input) = Done{(F.Input{en, F.NgapData{assoc, stream, len, bytes}}, rest)}
      +Y = B.write_u32(len, List.append(&2, U32, bytes, rest))
      r1 = U32.rt(assoc, B.write_u16(stream, Y))
      %r1 : {F.Input.of_event(en, F.Evt.data(_)) == D : B.Read(F.Input)}
      +fs = P.Bool.and_true_l(B.fits16(stream), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, bytes)), v)
      r2 = U16.rt(stream, Y, fs)
      %r2 : {F.Input.of_event(en, F.Evt.data_of_stream(assoc, _)) == D : B.Read(F.Input)}
      sfs = Equal.sym(Bool, B.fits16(stream), True{}, fs)
      %sfs : {F.Input.of_event(en, F.Evt.data_stream_ok(assoc, stream, Y, _)) == D : B.Read(F.Input)}
      r3 = U32.rt(len, List.append(&2, U32, bytes, rest))
      %r3 : {F.Input.of_event(en, F.Evt.data_of_len(assoc, stream, _)) == D : B.Read(F.Input)}
      tk = Take.rt(len, bytes, rest, P.Bool.and_true_r(B.fits16(stream), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, bytes)), v))
      %tk : {F.Input.of_event(en, F.Evt.data_of_bytes(assoc, stream, len, _)) == D : B.Read(F.Input)}
      {==}
    case F.PfcpData{+len, +bytes}:
      +D : B.Read(F.Input) = Done{(F.Input{en, F.PfcpData{len, bytes}}, rest)}
      r1 = U32.rt(len, List.append(&2, U32, bytes, rest))
      %r1 : {F.Input.of_event(en, F.Evt.pfcp(_)) == D : B.Read(F.Input)}
      tk = Take.rt(len, bytes, rest, v)
      %tk : {F.Input.of_event(en, F.Evt.pfcp_of_bytes(len, _)) == D : B.Read(F.Input)}
      {==}
    case F.TimerFired{+timer}:
      r1 = U32.rt(timer, rest)
      %r1 : {F.Input.of_event(en, F.Evt.timer(_)) == Done{(F.Input{en, F.TimerFired{timer}}, rest)} : B.Read(F.Input)}
      {==}

def Input.rt(+en: B.Bytes(), +ev: F.Evt, +rest: B.Bytes(), +v: {F.Input.valid(F.Input{en, ev}) == True{} : Bool}) -> {F.Input.read(F.Input.write(F.Input{en, ev}, rest)) == Done{(F.Input{en, ev}, rest)} : B.Read(F.Input)}:
  +Y = F.Evt.write(ev, rest)
  e32 = P.Nat.eq_of_is_eq(List.length(&2, U32, en), 32n, P.Bool.and_true_l(Nat.is_eq(List.length(&2, U32, en), 32n), F.Evt.valid(ev), v))
  %e32 : {F.Input.of_entropy(U32.and(255, F.Evt.kind(ev)), B.take(_, List.append(&2, U32, en, Y))) == Done{(F.Input{en, ev}, rest)} : B.Read(F.Input)}
  ta = Equal.sym(B.Read(B.Bytes()), B.take(List.length(&2, U32, en), List.append(&2, U32, en, Y)), Done{(en, Y)}, P.Take.append(en, Y))
  %ta : {F.Input.of_entropy(U32.and(255, F.Evt.kind(ev)), _) == Done{(F.Input{en, ev}, rest)} : B.Read(F.Input)}
  Evt.rt(ev, en, rest, P.Bool.and_true_r(Nat.is_eq(List.length(&2, U32, en), 32n), F.Evt.valid(ev), v))

def L.frame.event.roundtrip(i, rest, v):
  match i:
    case F.Input{+entropy, +event}:
      Input.rt(entropy, event, rest, v)

# Reading: what the event reader answered. One chain yields decode_valid and suffix.
# --------------------------------------------------------------------------------

def Evt.Spec(bs: B.Bytes(), ev: F.Evt, rest: B.Bytes()) -> Type:
  {F.Evt.valid(ev) == True{} : Bool} & ({B.all_bytes(bs) == True{} : Bool} -> {F.Evt.write(ev, rest) == bs : B.Bytes()})

# The payload spec, with the kind byte it was read under.
def Evt.Goal(kind: U32, bs: B.Bytes(), ev: F.Evt, rest: B.Bytes()) -> Type:
  Evt.Spec(bs, ev, rest) & {kind == F.Evt.kind(ev) : U32}

def Input.Spec(bs: B.Bytes(), i: F.Input, rest: B.Bytes()) -> Type:
  {F.Input.valid(i) == True{} : Bool} & ({B.all_bytes(bs) == True{} : Bool} -> {F.Input.write(i, rest) == bs : B.Bytes()})

# One 32-bit word: NgapAssocUp, NgapAssocDown, TimerFired.

def Evt.spec.up.fin(+kind: U32, +bs: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, +v: U32, +t: B.Bytes(), ebs: {bs == a <> b <> c <> d <> t : B.Bytes()}, evv: {B.cat8(d, B.cat8(c, B.cat8(b, a))) == v : U32}, ek: {kind == 2 : U32}) -> Evt.Goal(kind, bs, F.NgapAssocUp{v}, t):
  sbs = Equal.sym(B.Bytes(), bs, a <> b <> c <> d <> t, ebs)
  %sbs : Evt.Goal(kind, _, F.NgapAssocUp{v}, t)
  %evv : Evt.Goal(kind, a <> b <> c <> d <> t, F.NgapAssocUp{_}, t)
  (({==}, ab => PB.U32.sx(a, b, c, d, t, ab, t)), ek)

def Evt.spec.up(+kind: U32, +bs: B.Bytes(), rr: B.Read(U32), +err: {B.u32(bs) == rr : B.Read(U32)}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.assoc_up(rr) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 2 : U32}) -> Evt.Goal(kind, bs, ev, rest):
  match rr:
    case Fail{err}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err, (ev, rest), e))
    case Done{(+v, +t)}:
      ev2 = Equal.cong(B.Read(F.Evt), F.Evt, x => P.Read.value(F.Evt, x, ev), Done{(F.NgapAssocUp{v}, t)}, Done{(ev, rest)}, e)
      er = Equal.cong(B.Read(F.Evt), B.Bytes(), x => P.Read.rest(F.Evt, x, rest), Done{(F.NgapAssocUp{v}, t)}, Done{(ev, rest)}, e)
      %ev2 : Evt.Goal(kind, bs, _, rest)
      %er : Evt.Goal(kind, bs, F.NgapAssocUp{v}, _)
      PB.U32.rd(Evt.Goal(kind, bs, F.NgapAssocUp{v}, t), bs, v, t, err, a => b => c => d => ebs => evv => Evt.spec.up.fin(kind, bs, a, b, c, d, v, t, ebs, evv, ek))

def Evt.spec.down.fin(+kind: U32, +bs: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, +v: U32, +t: B.Bytes(), ebs: {bs == a <> b <> c <> d <> t : B.Bytes()}, evv: {B.cat8(d, B.cat8(c, B.cat8(b, a))) == v : U32}, ek: {kind == 3 : U32}) -> Evt.Goal(kind, bs, F.NgapAssocDown{v}, t):
  sbs = Equal.sym(B.Bytes(), bs, a <> b <> c <> d <> t, ebs)
  %sbs : Evt.Goal(kind, _, F.NgapAssocDown{v}, t)
  %evv : Evt.Goal(kind, a <> b <> c <> d <> t, F.NgapAssocDown{_}, t)
  (({==}, ab => PB.U32.sx(a, b, c, d, t, ab, t)), ek)

def Evt.spec.down(+kind: U32, +bs: B.Bytes(), rr: B.Read(U32), +err: {B.u32(bs) == rr : B.Read(U32)}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.assoc_down(rr) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 3 : U32}) -> Evt.Goal(kind, bs, ev, rest):
  match rr:
    case Fail{err}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err, (ev, rest), e))
    case Done{(+v, +t)}:
      ev2 = Equal.cong(B.Read(F.Evt), F.Evt, x => P.Read.value(F.Evt, x, ev), Done{(F.NgapAssocDown{v}, t)}, Done{(ev, rest)}, e)
      er = Equal.cong(B.Read(F.Evt), B.Bytes(), x => P.Read.rest(F.Evt, x, rest), Done{(F.NgapAssocDown{v}, t)}, Done{(ev, rest)}, e)
      %ev2 : Evt.Goal(kind, bs, _, rest)
      %er : Evt.Goal(kind, bs, F.NgapAssocDown{v}, _)
      PB.U32.rd(Evt.Goal(kind, bs, F.NgapAssocDown{v}, t), bs, v, t, err, a => b => c => d => ebs => evv => Evt.spec.down.fin(kind, bs, a, b, c, d, v, t, ebs, evv, ek))

def Evt.spec.timer.fin(+kind: U32, +bs: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, +v: U32, +t: B.Bytes(), ebs: {bs == a <> b <> c <> d <> t : B.Bytes()}, evv: {B.cat8(d, B.cat8(c, B.cat8(b, a))) == v : U32}, ek: {kind == 6 : U32}) -> Evt.Goal(kind, bs, F.TimerFired{v}, t):
  sbs = Equal.sym(B.Bytes(), bs, a <> b <> c <> d <> t, ebs)
  %sbs : Evt.Goal(kind, _, F.TimerFired{v}, t)
  %evv : Evt.Goal(kind, a <> b <> c <> d <> t, F.TimerFired{_}, t)
  (({==}, ab => PB.U32.sx(a, b, c, d, t, ab, t)), ek)

def Evt.spec.timer(+kind: U32, +bs: B.Bytes(), rr: B.Read(U32), +err: {B.u32(bs) == rr : B.Read(U32)}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.timer(rr) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 6 : U32}) -> Evt.Goal(kind, bs, ev, rest):
  match rr:
    case Fail{err}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err, (ev, rest), e))
    case Done{(+v, +t)}:
      ev2 = Equal.cong(B.Read(F.Evt), F.Evt, x => P.Read.value(F.Evt, x, ev), Done{(F.TimerFired{v}, t)}, Done{(ev, rest)}, e)
      er = Equal.cong(B.Read(F.Evt), B.Bytes(), x => P.Read.rest(F.Evt, x, rest), Done{(F.TimerFired{v}, t)}, Done{(ev, rest)}, e)
      %ev2 : Evt.Goal(kind, bs, _, rest)
      %er : Evt.Goal(kind, bs, F.TimerFired{v}, _)
      PB.U32.rd(Evt.Goal(kind, bs, F.TimerFired{v}, t), bs, v, t, err, a => b => c => d => ebs => evv => Evt.spec.timer.fin(kind, bs, a, b, c, d, v, t, ebs, evv, ek))

# PfcpData: a length word and that many octets.

def Evt.spec.pfcp.fin(+kind: U32, +bs: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, +len: U32, +t1: B.Bytes(), +bytes: B.Bytes(), +t2: B.Bytes(), ebs: {bs == a <> b <> c <> d <> t1 : B.Bytes()}, eln: {B.cat8(d, B.cat8(c, B.cat8(b, a))) == len : U32}, la: {List.length(&2, U32, bytes) == U32.to_nat(len) : Nat} & {List.append(&2, U32, bytes, t2) == t1 : B.Bytes()}, ek: {kind == 5 : U32}) -> Evt.Goal(kind, bs, F.PfcpData{len, bytes}, t2):
  (ln, ap) = la
  sbs = Equal.sym(B.Bytes(), bs, a <> b <> c <> d <> t1, ebs)
  %sbs : Evt.Goal(kind, _, F.PfcpData{len, bytes}, t2)
  %ap : Evt.Goal(kind, a <> b <> c <> d <> _, F.PfcpData{len, bytes}, t2)
  +X = List.append(&2, U32, bytes, t2)
  (((%ln : {Nat.is_eq(_, List.length(&2, U32, bytes)) == True{} : Bool}; P.Nat.is_eq_refl(List.length(&2, U32, bytes))), ab => (%eln : {B.write_u32(_, X) == a <> b <> c <> d <> X : B.Bytes()}; PB.U32.sx(a, b, c, d, X, ab, X))), ek)

def Evt.spec.pfcp.body(+kind: U32, +bs: B.Bytes(), +len: U32, +t1: B.Bytes(), rt: B.Read(B.Bytes()), +ert: {B.take(U32.to_nat(len), t1) == rt : B.Read(B.Bytes())}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.pfcp_of_bytes(len, rt) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 5 : U32}, +err: {B.u32(bs) == Done{(len, t1)} : B.Read(U32)}) -> Evt.Goal(kind, bs, ev, rest):
  match rt:
    case Fail{err2}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err2, (ev, rest), e))
    case Done{(+bytes, +t2)}:
      ev2 = Equal.cong(B.Read(F.Evt), F.Evt, x => P.Read.value(F.Evt, x, ev), Done{(F.PfcpData{len, bytes}, t2)}, Done{(ev, rest)}, e)
      er = Equal.cong(B.Read(F.Evt), B.Bytes(), x => P.Read.rest(F.Evt, x, rest), Done{(F.PfcpData{len, bytes}, t2)}, Done{(ev, rest)}, e)
      %ev2 : Evt.Goal(kind, bs, _, rest)
      %er : Evt.Goal(kind, bs, F.PfcpData{len, bytes}, _)
      PB.U32.rd(Evt.Goal(kind, bs, F.PfcpData{len, bytes}, t2), bs, len, t1, err, a => b => c => d => ebs => eln => Evt.spec.pfcp.fin(kind, bs, a, b, c, d, len, t1, bytes, t2, ebs, eln, L.bytes.take.length(U32.to_nat(len), t1, bytes, t2, ert), ek))

def Evt.spec.pfcp(+kind: U32, +bs: B.Bytes(), rr: B.Read(U32), +err: {B.u32(bs) == rr : B.Read(U32)}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.pfcp(rr) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 5 : U32}) -> Evt.Goal(kind, bs, ev, rest):
  match rr:
    case Fail{err2}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err2, (ev, rest), e))
    case Done{(+len, +t1)}:
      Evt.spec.pfcp.body(kind, bs, len, t1, B.take(U32.to_nat(len), t1), {==}, ev, rest, e, ek, err)

# NgapData: association, stream, length, octets.

def Evt.spec.data.write(+a1: U32, +a2: U32, +a3: U32, +a4: U32, +s1: U32, +s2: U32, +l1: U32, +l2: U32, +l3: U32, +l4: U32, +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +t4: B.Bytes(), eas: {B.cat8(a4, B.cat8(a3, B.cat8(a2, a1))) == assoc : U32}, est: {B.cat8(s2, s1) == stream : U32}, eln: {B.cat8(l4, B.cat8(l3, B.cat8(l2, l1))) == len : U32}, +ab: {B.all_bytes(a1 <> a2 <> a3 <> a4 <> s1 <> s2 <> l1 <> l2 <> l3 <> l4 <> List.append(&2, U32, bytes, t4)) == True{} : Bool}) -> {F.Evt.write(F.NgapData{assoc, stream, len, bytes}, t4) == a1 <> a2 <> a3 <> a4 <> s1 <> s2 <> l1 <> l2 <> l3 <> l4 <> List.append(&2, U32, bytes, t4) : B.Bytes()}:
  +X3 = List.append(&2, U32, bytes, t4)
  +X2 = B.write_u32(len, X3)
  +X1 = B.write_u16(stream, X2)
  +T2 : B.Bytes() = l1 <> l2 <> l3 <> l4 <> X3
  +T1 : B.Bytes() = s1 <> s2 <> T2
  +ab1 = PB.Bytes.all_tail4(a1, a2, a3, a4, T1, ab)
  w1 = Equal.sym(B.Bytes(), B.write_u32(assoc, X1), a1 <> a2 <> a3 <> a4 <> X1, (%eas : {B.write_u32(_, X1) == a1 <> a2 <> a3 <> a4 <> X1 : B.Bytes()}; PB.U32.sx(a1, a2, a3, a4, T1, ab, X1)))
  %w1 : {_ == a1 <> a2 <> a3 <> a4 <> T1 : B.Bytes()}
  w2 = Equal.sym(B.Bytes(), B.write_u16(stream, X2), s1 <> s2 <> X2, (%est : {B.write_u16(_, X2) == s1 <> s2 <> X2 : B.Bytes()}; PB.U16.sx(s1, s2, T2, ab1, X2)))
  %w2 : {a1 <> a2 <> a3 <> a4 <> _ == a1 <> a2 <> a3 <> a4 <> T1 : B.Bytes()}
  w3 = Equal.sym(B.Bytes(), B.write_u32(len, X3), l1 <> l2 <> l3 <> l4 <> X3, (%eln : {B.write_u32(_, X3) == l1 <> l2 <> l3 <> l4 <> X3 : B.Bytes()}; PB.U32.sx(l1, l2, l3, l4, X3, PB.Bytes.all_tail2(s1, s2, T2, ab1), X3)))
  %w3 : {a1 <> a2 <> a3 <> a4 <> s1 <> s2 <> _ == a1 <> a2 <> a3 <> a4 <> T1 : B.Bytes()}
  {==}

def Evt.spec.data.fin(+kind: U32, +bs: B.Bytes(), +a1: U32, +a2: U32, +a3: U32, +a4: U32, +t1: B.Bytes(), +s1: U32, +s2: U32, +t2: B.Bytes(), +l1: U32, +l2: U32, +l3: U32, +l4: U32, +t3: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +t4: B.Bytes(), ebs: {bs == a1 <> a2 <> a3 <> a4 <> t1 : B.Bytes()}, eas: {B.cat8(a4, B.cat8(a3, B.cat8(a2, a1))) == assoc : U32}, et1: {t1 == s1 <> s2 <> t2 : B.Bytes()}, est: {B.cat8(s2, s1) == stream : U32}, et2: {t2 == l1 <> l2 <> l3 <> l4 <> t3 : B.Bytes()}, eln: {B.cat8(l4, B.cat8(l3, B.cat8(l2, l1))) == len : U32}, la: {List.length(&2, U32, bytes) == U32.to_nat(len) : Nat} & {List.append(&2, U32, bytes, t4) == t3 : B.Bytes()}, fs: {B.fits16(stream) == True{} : Bool}, ek: {kind == 4 : U32}) -> Evt.Goal(kind, bs, F.NgapData{assoc, stream, len, bytes}, t4):
  (ln, ap) = la
  sbs = Equal.sym(B.Bytes(), bs, a1 <> a2 <> a3 <> a4 <> t1, ebs)
  %sbs : Evt.Goal(kind, _, F.NgapData{assoc, stream, len, bytes}, t4)
  st1 = Equal.sym(B.Bytes(), t1, s1 <> s2 <> t2, et1)
  %st1 : Evt.Goal(kind, a1 <> a2 <> a3 <> a4 <> _, F.NgapData{assoc, stream, len, bytes}, t4)
  st2 = Equal.sym(B.Bytes(), t2, l1 <> l2 <> l3 <> l4 <> t3, et2)
  %st2 : Evt.Goal(kind, a1 <> a2 <> a3 <> a4 <> s1 <> s2 <> _, F.NgapData{assoc, stream, len, bytes}, t4)
  %ap : Evt.Goal(kind, a1 <> a2 <> a3 <> a4 <> s1 <> s2 <> l1 <> l2 <> l3 <> l4 <> _, F.NgapData{assoc, stream, len, bytes}, t4)
  ((P.Bool.and_intro(B.fits16(stream), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, bytes)), fs, (%ln : {Nat.is_eq(_, List.length(&2, U32, bytes)) == True{} : Bool}; P.Nat.is_eq_refl(List.length(&2, U32, bytes)))), ab => Evt.spec.data.write(a1, a2, a3, a4, s1, s2, l1, l2, l3, l4, assoc, stream, len, bytes, t4, eas, est, eln, ab)), ek)

def Evt.spec.data.body(+kind: U32, +bs: B.Bytes(), +assoc: U32, +t1: B.Bytes(), +stream: U32, +t2: B.Bytes(), +len: U32, +t3: B.Bytes(), rt: B.Read(B.Bytes()), +ert: {B.take(U32.to_nat(len), t3) == rt : B.Read(B.Bytes())}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.data_of_bytes(assoc, stream, len, rt) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 4 : U32}, +err: {B.u32(bs) == Done{(assoc, t1)} : B.Read(U32)}, +ers: {B.u16(t1) == Done{(stream, t2)} : B.Read(U32)}, fs: {B.fits16(stream) == True{} : Bool}, +erl: {B.u32(t2) == Done{(len, t3)} : B.Read(U32)}) -> Evt.Goal(kind, bs, ev, rest):
  match rt:
    case Fail{err2}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err2, (ev, rest), e))
    case Done{(+bytes, +t4)}:
      ev2 = Equal.cong(B.Read(F.Evt), F.Evt, x => P.Read.value(F.Evt, x, ev), Done{(F.NgapData{assoc, stream, len, bytes}, t4)}, Done{(ev, rest)}, e)
      er = Equal.cong(B.Read(F.Evt), B.Bytes(), x => P.Read.rest(F.Evt, x, rest), Done{(F.NgapData{assoc, stream, len, bytes}, t4)}, Done{(ev, rest)}, e)
      %ev2 : Evt.Goal(kind, bs, _, rest)
      %er : Evt.Goal(kind, bs, F.NgapData{assoc, stream, len, bytes}, _)
      PB.U32.rd(Evt.Goal(kind, bs, F.NgapData{assoc, stream, len, bytes}, t4), bs, assoc, t1, err, a1 => a2 => a3 => a4 => ebs => eas => PB.U16.rd(Evt.Goal(kind, bs, F.NgapData{assoc, stream, len, bytes}, t4), t1, stream, t2, ers, s1 => s2 => et1 => est => PB.U32.rd(Evt.Goal(kind, bs, F.NgapData{assoc, stream, len, bytes}, t4), t2, len, t3, erl, l1 => l2 => l3 => l4 => et2 => eln => Evt.spec.data.fin(kind, bs, a1, a2, a3, a4, t1, s1, s2, t2, l1, l2, l3, l4, t3, assoc, stream, len, bytes, t4, ebs, eas, et1, est, et2, eln, L.bytes.take.length(U32.to_nat(len), t3, bytes, t4, ert), fs, ek))))

def Evt.spec.data.len(+kind: U32, +bs: B.Bytes(), +assoc: U32, +t1: B.Bytes(), +stream: U32, +t2: B.Bytes(), rl: B.Read(U32), +erl: {B.u32(t2) == rl : B.Read(U32)}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.data_of_len(assoc, stream, rl) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 4 : U32}, +err: {B.u32(bs) == Done{(assoc, t1)} : B.Read(U32)}, +ers: {B.u16(t1) == Done{(stream, t2)} : B.Read(U32)}, fs: {B.fits16(stream) == True{} : Bool}) -> Evt.Goal(kind, bs, ev, rest):
  match rl:
    case Fail{err2}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err2, (ev, rest), e))
    case Done{(+len, +t3)}:
      Evt.spec.data.body(kind, bs, assoc, t1, stream, t2, len, t3, B.take(U32.to_nat(len), t3), {==}, ev, rest, e, ek, err, ers, fs, erl)

def Evt.spec.data.ok(+kind: U32, +bs: B.Bytes(), +assoc: U32, +t1: B.Bytes(), +stream: U32, +t2: B.Bytes(), ok: Bool, eok: {B.fits16(stream) == ok : Bool}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.data_stream_ok(assoc, stream, t2, ok) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 4 : U32}, +err: {B.u32(bs) == Done{(assoc, t1)} : B.Read(U32)}, +ers: {B.u16(t1) == Done{(stream, t2)} : B.Read(U32)}) -> Evt.Goal(kind, bs, ev, rest):
  match ok:
    case False{}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), B.Invalid{stream}, (ev, rest), e))
    case True{}:
      Evt.spec.data.len(kind, bs, assoc, t1, stream, t2, B.u32(t2), {==}, ev, rest, e, ek, err, ers, eok)

def Evt.spec.data.stream(+kind: U32, +bs: B.Bytes(), +assoc: U32, +t1: B.Bytes(), rs: B.Read(U32), +ers: {B.u16(t1) == rs : B.Read(U32)}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.data_of_stream(assoc, rs) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 4 : U32}, +err: {B.u32(bs) == Done{(assoc, t1)} : B.Read(U32)}) -> Evt.Goal(kind, bs, ev, rest):
  match rs:
    case Fail{err2}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err2, (ev, rest), e))
    case Done{(+stream, +t2)}:
      Evt.spec.data.ok(kind, bs, assoc, t1, stream, t2, B.fits16(stream), {==}, ev, rest, e, ek, err, ers)

def Evt.spec.data(+kind: U32, +bs: B.Bytes(), rr: B.Read(U32), +err: {B.u32(bs) == rr : B.Read(U32)}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.data(rr) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 4 : U32}) -> Evt.Goal(kind, bs, ev, rest):
  match rr:
    case Fail{err2}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err2, (ev, rest), e))
    case Done{(+assoc, +t1)}:
      Evt.spec.data.stream(kind, bs, assoc, t1, B.u16(t1), {==}, ev, rest, e, ek, err)

# Config: a length word, that many octets of TLVs, every known tag's value checked.

def Evt.spec.config.write(+a: U32, +b: U32, +c: U32, +d: U32, +len: U32, +body: B.Bytes(), +t2: B.Bytes(), +tlvs: List<&2, T.Tlv>, eln: {B.cat8(d, B.cat8(c, B.cat8(b, a))) == len : U32}, +eri: {T.Tlvs.decode(body) == Done{tlvs} : PT.Tlvs.Res()}, +ab: {B.all_bytes(a <> b <> c <> d <> List.append(&2, U32, body, t2)) == True{} : Bool}) -> {F.Evt.write(F.Config{len, tlvs}, t2) == a <> b <> c <> d <> List.append(&2, U32, body, t2) : B.Bytes()}:
  +X = List.append(&2, U32, body, t2)
  ws = Equal.sym(B.Bytes(), T.Tlvs.write(tlvs, t2), X, PT.Tlvs.sx(List.length(&2, U32, body), body, tlvs, eri, PB.Bytes.all_app_l(body, t2, PB.Bytes.all_tail4(a, b, c, d, X, ab)), t2))
  %ws : {B.write_u32(len, _) == a <> b <> c <> d <> X : B.Bytes()}
  (%eln : {B.write_u32(_, X) == a <> b <> c <> d <> X : B.Bytes()}; PB.U32.sx(a, b, c, d, X, ab, X))

def Evt.spec.config.fin(+kind: U32, +bs: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, +len: U32, +t1: B.Bytes(), +body: B.Bytes(), +t2: B.Bytes(), +tlvs: List<&2, T.Tlv>, ebs: {bs == a <> b <> c <> d <> t1 : B.Bytes()}, eln: {B.cat8(d, B.cat8(c, B.cat8(b, a))) == len : U32}, la: {List.length(&2, U32, body) == U32.to_nat(len) : Nat} & {List.append(&2, U32, body, t2) == t1 : B.Bytes()}, +eri: {T.Tlvs.decode(body) == Done{tlvs} : PT.Tlvs.Res()}, tg: {F.Tags.valid(tlvs) == True{} : Bool}, ek: {kind == 1 : U32}) -> Evt.Goal(kind, bs, F.Config{len, tlvs}, t2):
  (ln, ap) = la
  sbs = Equal.sym(B.Bytes(), bs, a <> b <> c <> d <> t1, ebs)
  %sbs : Evt.Goal(kind, _, F.Config{len, tlvs}, t2)
  %ap : Evt.Goal(kind, a <> b <> c <> d <> _, F.Config{len, tlvs}, t2)
  ssz = Equal.sym(Nat, T.Tlvs.size(tlvs), List.length(&2, U32, body), PT.Tlvs.len(List.length(&2, U32, body), body, tlvs, eri))
  ((P.Bool.and_intro(Nat.is_eq(U32.to_nat(len), T.Tlvs.size(tlvs)), Bool.and(T.Tlvs.valid(tlvs), F.Tags.valid(tlvs)), (%ln : {Nat.is_eq(_, T.Tlvs.size(tlvs)) == True{} : Bool}; (%ssz : {Nat.is_eq(List.length(&2, U32, body), _) == True{} : Bool}; P.Nat.is_eq_refl(List.length(&2, U32, body)))), P.Bool.and_intro(T.Tlvs.valid(tlvs), F.Tags.valid(tlvs), PT.Tlvs.dv(List.length(&2, U32, body), body, tlvs, eri), tg)), ab => Evt.spec.config.write(a, b, c, d, len, body, t2, tlvs, eln, eri, ab)), ek)

def Evt.spec.config.tags(+kind: U32, +bs: B.Bytes(), +len: U32, +t1: B.Bytes(), +body: B.Bytes(), +t2: B.Bytes(), +tlvs: List<&2, T.Tlv>, ok: Bool, eok: {F.Tags.valid(tlvs) == ok : Bool}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.config_tags(len, t2, tlvs, ok) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 1 : U32}, +err: {B.u32(bs) == Done{(len, t1)} : B.Read(U32)}, la: {List.length(&2, U32, body) == U32.to_nat(len) : Nat} & {List.append(&2, U32, body, t2) == t1 : B.Bytes()}, +eri: {T.Tlvs.decode(body) == Done{tlvs} : PT.Tlvs.Res()}) -> Evt.Goal(kind, bs, ev, rest):
  match ok:
    case False{}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), B.Invalid{1}, (ev, rest), e))
    case True{}:
      ev2 = Equal.cong(B.Read(F.Evt), F.Evt, x => P.Read.value(F.Evt, x, ev), Done{(F.Config{len, tlvs}, t2)}, Done{(ev, rest)}, e)
      er = Equal.cong(B.Read(F.Evt), B.Bytes(), x => P.Read.rest(F.Evt, x, rest), Done{(F.Config{len, tlvs}, t2)}, Done{(ev, rest)}, e)
      %ev2 : Evt.Goal(kind, bs, _, rest)
      %er : Evt.Goal(kind, bs, F.Config{len, tlvs}, _)
      PB.U32.rd(Evt.Goal(kind, bs, F.Config{len, tlvs}, t2), bs, len, t1, err, a => b => c => d => ebs => eln => Evt.spec.config.fin(kind, bs, a, b, c, d, len, t1, body, t2, tlvs, ebs, eln, la, eri, eok, ek))

def Evt.spec.config.tlvs(+kind: U32, +bs: B.Bytes(), +len: U32, +t1: B.Bytes(), +body: B.Bytes(), +t2: B.Bytes(), ri: PT.Tlvs.Res(), +eri: {T.Tlvs.decode(body) == ri : PT.Tlvs.Res()}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.config_of_tlvs(len, t2, ri) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 1 : U32}, +err: {B.u32(bs) == Done{(len, t1)} : B.Read(U32)}, la: {List.length(&2, U32, body) == U32.to_nat(len) : Nat} & {List.append(&2, U32, body, t2) == t1 : B.Bytes()}) -> Evt.Goal(kind, bs, ev, rest):
  match ri:
    case Fail{err2}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err2, (ev, rest), e))
    case Done{+tlvs}:
      Evt.spec.config.tags(kind, bs, len, t1, body, t2, tlvs, F.Tags.valid(tlvs), {==}, ev, rest, e, ek, err, la, eri)

def Evt.spec.config.body(+kind: U32, +bs: B.Bytes(), +len: U32, +t1: B.Bytes(), rt: B.Read(B.Bytes()), +ert: {B.take(U32.to_nat(len), t1) == rt : B.Read(B.Bytes())}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.config_of_body(len, rt) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 1 : U32}, +err: {B.u32(bs) == Done{(len, t1)} : B.Read(U32)}) -> Evt.Goal(kind, bs, ev, rest):
  match rt:
    case Fail{err2}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err2, (ev, rest), e))
    case Done{(+body, +t2)}:
      Evt.spec.config.tlvs(kind, bs, len, t1, body, t2, T.Tlvs.decode(body), {==}, ev, rest, e, ek, err, L.bytes.take.length(U32.to_nat(len), t1, body, t2, ert))

def Evt.spec.config(+kind: U32, +bs: B.Bytes(), rr: B.Read(U32), +err: {B.u32(bs) == rr : B.Read(U32)}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.config(rr) == Done{(ev, rest)} : F.Evt.Res()}, ek: {kind == 1 : U32}) -> Evt.Goal(kind, bs, ev, rest):
  match rr:
    case Fail{err2}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), err2, (ev, rest), e))
    case Done{(+len, +t1)}:
      Evt.spec.config.body(kind, bs, len, t1, B.take(U32.to_nat(len), t1), {==}, ev, rest, e, ek, err)

# The kind byte, compared in turn.

def Evt.spec.k6(+kind: U32, +bs: B.Bytes(), ok: Bool, eok: {U32.is_eq(kind, 6) == ok : Bool}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.k6(kind, bs, ok) == Done{(ev, rest)} : F.Evt.Res()}) -> Evt.Goal(kind, bs, ev, rest):
  match ok:
    case True{}:
      Evt.spec.timer(kind, bs, B.u32(bs), {==}, ev, rest, e, P.U32.eq_of_is_eq(kind, 6, eok))
    case False{}:
      Empty.absurd(Evt.Goal(kind, bs, ev, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Evt), B.Unsupported{kind}, (ev, rest), e))

def Evt.spec.k5(+kind: U32, +bs: B.Bytes(), ok: Bool, eok: {U32.is_eq(kind, 5) == ok : Bool}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.k5(kind, bs, ok) == Done{(ev, rest)} : F.Evt.Res()}) -> Evt.Goal(kind, bs, ev, rest):
  match ok:
    case True{}:
      Evt.spec.pfcp(kind, bs, B.u32(bs), {==}, ev, rest, e, P.U32.eq_of_is_eq(kind, 5, eok))
    case False{}:
      Evt.spec.k6(kind, bs, U32.is_eq(kind, 6), {==}, ev, rest, e)

def Evt.spec.k4(+kind: U32, +bs: B.Bytes(), ok: Bool, eok: {U32.is_eq(kind, 4) == ok : Bool}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.k4(kind, bs, ok) == Done{(ev, rest)} : F.Evt.Res()}) -> Evt.Goal(kind, bs, ev, rest):
  match ok:
    case True{}:
      Evt.spec.data(kind, bs, B.u32(bs), {==}, ev, rest, e, P.U32.eq_of_is_eq(kind, 4, eok))
    case False{}:
      Evt.spec.k5(kind, bs, U32.is_eq(kind, 5), {==}, ev, rest, e)

def Evt.spec.k3(+kind: U32, +bs: B.Bytes(), ok: Bool, eok: {U32.is_eq(kind, 3) == ok : Bool}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.k3(kind, bs, ok) == Done{(ev, rest)} : F.Evt.Res()}) -> Evt.Goal(kind, bs, ev, rest):
  match ok:
    case True{}:
      Evt.spec.down(kind, bs, B.u32(bs), {==}, ev, rest, e, P.U32.eq_of_is_eq(kind, 3, eok))
    case False{}:
      Evt.spec.k4(kind, bs, U32.is_eq(kind, 4), {==}, ev, rest, e)

def Evt.spec.k2(+kind: U32, +bs: B.Bytes(), ok: Bool, eok: {U32.is_eq(kind, 2) == ok : Bool}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.k2(kind, bs, ok) == Done{(ev, rest)} : F.Evt.Res()}) -> Evt.Goal(kind, bs, ev, rest):
  match ok:
    case True{}:
      Evt.spec.up(kind, bs, B.u32(bs), {==}, ev, rest, e, P.U32.eq_of_is_eq(kind, 2, eok))
    case False{}:
      Evt.spec.k3(kind, bs, U32.is_eq(kind, 3), {==}, ev, rest, e)

def Evt.spec.k1(+kind: U32, +bs: B.Bytes(), ok: Bool, eok: {U32.is_eq(kind, 1) == ok : Bool}, +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.k1(kind, bs, ok) == Done{(ev, rest)} : F.Evt.Res()}) -> Evt.Goal(kind, bs, ev, rest):
  match ok:
    case True{}:
      Evt.spec.config(kind, bs, B.u32(bs), {==}, ev, rest, e, P.U32.eq_of_is_eq(kind, 1, eok))
    case False{}:
      Evt.spec.k2(kind, bs, U32.is_eq(kind, 2), {==}, ev, rest, e)

def Evt.spec(+kind: U32, +bs: B.Bytes(), +ev: F.Evt, +rest: B.Bytes(), +e: {F.Evt.payload(kind, bs) == Done{(ev, rest)} : F.Evt.Res()}) -> Evt.Goal(kind, bs, ev, rest):
  Evt.spec.k1(kind, bs, U32.is_eq(kind, 1), {==}, ev, rest, e)

# The input: a kind byte, 32 octets of entropy, the payload.

def Input.spec.write(+kind: U32, +r: B.Bytes(), +en: B.Bytes(), +r2: B.Bytes(), +ev: F.Evt, +r3: B.Bytes(), +ap: {List.append(&2, U32, en, r2) == r : B.Bytes()}, ek: {kind == F.Evt.kind(ev) : U32}, w: {B.all_bytes(r2) == True{} : Bool} -> {F.Evt.write(ev, r3) == r2 : B.Bytes()}, +ab: {B.all_bytes(kind <> r) == True{} : Bool}) -> {F.Input.write(F.Input{en, ev}, r3) == kind <> r : B.Bytes()}:
  %ek : {B.write_u8(_, List.append(&2, U32, en, F.Evt.write(ev, r3))) == kind <> r : B.Bytes()}
  sm = Equal.sym(U32, U32.and(255, kind), kind, PB.Bytes.mask(kind, r, ab))
  %sm : {_ <> List.append(&2, U32, en, F.Evt.write(ev, r3)) == kind <> r : B.Bytes()}
  %ap : {kind <> List.append(&2, U32, en, F.Evt.write(ev, r3)) == kind <> _ : B.Bytes()}
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, en, r2), r, ap)
  Equal.cong(B.Bytes(), B.Bytes(), l => kind <> List.append(&2, U32, en, l), F.Evt.write(ev, r3), r2, w(PB.Bytes.all_app(en, r2, (%sap : {B.all_bytes(_) == True{} : Bool}; PB.Bytes.all_tail(kind, r, ab)))))

def Input.spec.fin(+kind: U32, +r: B.Bytes(), +en: B.Bytes(), +r2: B.Bytes(), +ev: F.Evt, +r3: B.Bytes(), la: {List.length(&2, U32, en) == 32n : Nat} & {List.append(&2, U32, en, r2) == r : B.Bytes()}, g: Evt.Goal(kind, r2, ev, r3)) -> Input.Spec(kind <> r, F.Input{en, ev}, r3):
  (l32, +ap) = la
  (sp, ek) = g
  (vv, w) = sp
  sl = Equal.sym(Nat, List.length(&2, U32, en), 32n, l32)
  (P.Bool.and_intro(Nat.is_eq(List.length(&2, U32, en), 32n), F.Evt.valid(ev), (%sl : {Nat.is_eq(_, 32n) == True{} : Bool}; P.Nat.is_eq_refl(32n)), vv), ab => Input.spec.write(kind, r, en, r2, ev, r3, ap, ek, w, ab))

def Input.spec.ev(+kind: U32, +r: B.Bytes(), +en: B.Bytes(), +r2: B.Bytes(), rp: F.Evt.Res(), +erp: {F.Evt.payload(kind, r2) == rp : F.Evt.Res()}, +i: F.Input, +rest: B.Bytes(), +e: {F.Input.of_event(en, rp) == Done{(i, rest)} : B.Read(F.Input)}, la: {List.length(&2, U32, en) == 32n : Nat} & {List.append(&2, U32, en, r2) == r : B.Bytes()}) -> Input.Spec(kind <> r, i, rest):
  match rp:
    case Fail{err}:
      Empty.absurd(Input.Spec(kind <> r, i, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Input), err, (i, rest), e))
    case Done{(+ev, +r3)}:
      ev2 = Equal.cong(B.Read(F.Input), F.Input, x => P.Read.value(F.Input, x, i), Done{(F.Input{en, ev}, r3)}, Done{(i, rest)}, e)
      er = Equal.cong(B.Read(F.Input), B.Bytes(), x => P.Read.rest(F.Input, x, rest), Done{(F.Input{en, ev}, r3)}, Done{(i, rest)}, e)
      %ev2 : Input.Spec(kind <> r, _, rest)
      %er : Input.Spec(kind <> r, F.Input{en, ev}, _)
      Input.spec.fin(kind, r, en, r2, ev, r3, la, Evt.spec(kind, r2, ev, r3, erp))

def Input.spec.en(+kind: U32, +r: B.Bytes(), rt: B.Read(B.Bytes()), +ert: {B.take(32n, r) == rt : B.Read(B.Bytes())}, +i: F.Input, +rest: B.Bytes(), e: {F.Input.of_entropy(kind, rt) == Done{(i, rest)} : B.Read(F.Input)}) -> Input.Spec(kind <> r, i, rest):
  match rt:
    case Fail{err}:
      Empty.absurd(Input.Spec(kind <> r, i, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Input), err, (i, rest), e))
    case Done{(+en, +r2)}:
      Input.spec.ev(kind, r, en, r2, F.Evt.payload(kind, r2), {==}, i, rest, e, L.bytes.take.length(32n, r, en, r2, ert))

def Input.spec(bs: B.Bytes(), +i: F.Input, +rest: B.Bytes(), e: {F.Input.read(bs) == Done{(i, rest)} : B.Read(F.Input)}) -> Input.Spec(bs, i, rest):
  match bs:
    case Nil{}:
      Empty.absurd(Input.Spec([], i, rest), P.Refute.fail_done(B.Err, B.ReadValue(F.Input), B.Short{}, (i, rest), e))
    case +kind <> +r:
      Input.spec.en(kind, r, B.take(32n, r), {==}, i, rest, e)

def Input.Spec.valid(+bs: B.Bytes(), +i: F.Input, +rest: B.Bytes(), s: Input.Spec(bs, i, rest)) -> {F.Input.valid(i) == True{} : Bool}:
  (v, w) = s
  v

def Input.Spec.write(+bs: B.Bytes(), +i: F.Input, +rest: B.Bytes(), s: Input.Spec(bs, i, rest), ab: {B.all_bytes(bs) == True{} : Bool}) -> {F.Input.write(i, rest) == bs : B.Bytes()}:
  (v, w) = s
  w(ab)

def L.frame.event.decode_valid(bs, i, rest, e):
  Input.Spec.valid(bs, i, rest, Input.spec(bs, i, rest, e))

def L.frame.event.suffix(bs, i, rest, e, ab):
  Input.Spec.write(bs, i, rest, Input.spec(bs, i, rest, e), ab)
