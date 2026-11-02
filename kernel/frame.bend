import Base
import ./bytes.bend as B
import ./tlv.bend as T

# The edge ⇄ kernel frame protocol (docs/spec/milestone-1.md § The frame
# protocol): `length: u32be` then `length` octets holding one event or one
# list of actions. Length words are kept as read, like NAS and PFCP, and tied
# to their content by `valid`; `make` fills them.

# Envelope
# --------

def Frame.max() -> Nat:
  262144n

def Frame.body(+len: U32, rest: B.Bytes(), big: Bool) -> B.Read(B.Bytes()):
  match big:
    case True{}:
      Fail{B.Invalid{len}}
    case False{}:
      B.take(U32.to_nat(len), rest)

def Frame.of_len(r: B.Read(U32)) -> B.Read(B.Bytes()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+len, rest)}:
      Frame.body(len, rest, Nat.is_lt(Frame.max(), U32.to_nat(len)))

# One frame's body, refusing an oversize length before reading any of it.
def Frame.read(bs: B.Bytes()) -> B.Read(B.Bytes()):
  Frame.of_len(B.u32(bs))

def Frame.write(+body: B.Bytes(), rest: B.Bytes()) -> B.Bytes():
  B.write_u32(U32.from_nat(List.length(&2, U32, body)), List.append(&2, U32, body, rest))

# Config TLVs
# -----------
# `tag: u16`, `len: u16`, value. Kept in wire order; a getter answers the last
# occurrence of a tag, so a repeated tag replaces the earlier one, and unknown
# tags are carried but never asked for.

# A subscriber (tag 0x0020): SUPI digits with their count, K, OPc, AMF, SQN.
type Sub is Data:
  Sub{supi: B.Bytes(), k: B.Bytes(), opc: B.Bytes(), amf: B.Bytes(), sqn: B.Bytes()}

def Len.is(bs: B.Bytes(), n: Nat) -> Bool:
  Nat.is_eq(List.length(&2, U32, bs), n)

# ASCII digits.
def Sub.digits(bs: B.Bytes()) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case +b <> rest:
      Bool.and(Bool.and(U32.is_lt(47, b), U32.is_lt(b, 58)), Sub.digits(rest))

def Sub.valid(s: Sub) -> Bool:
  match s:
    case Sub{+supi, k, opc, amf, sqn}:
      Bool.and(Nat.is_lt(List.length(&2, U32, supi), 256n), Bool.and(Sub.digits(supi), Bool.and(Len.is(k, 16n), Bool.and(Len.is(opc, 16n), Bool.and(Len.is(amf, 2n), Len.is(sqn, 6n))))))

def Exact.end(-A: Data, x: A, rest: B.Bytes()) -> Result<&2, &2, B.Err, A>:
  match rest:
    case Nil{}:
      Done{x}
    case b <> more:
      Fail{B.Invalid{b}}

def Sub.of_sqn(supi: B.Bytes(), k: B.Bytes(), opc: B.Bytes(), amf: B.Bytes(), r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, Sub>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(sqn, rest)}:
      Exact.end(Sub, Sub{supi, k, opc, amf, sqn}, rest)

def Sub.of_amf(supi: B.Bytes(), k: B.Bytes(), opc: B.Bytes(), r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, Sub>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(amf, rest)}:
      Sub.of_sqn(supi, k, opc, amf, B.take(6n, rest))

def Sub.of_opc(supi: B.Bytes(), k: B.Bytes(), r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, Sub>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(opc, rest)}:
      Sub.of_amf(supi, k, opc, B.take(2n, rest))

def Sub.of_k(supi: B.Bytes(), r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, Sub>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(k, rest)}:
      Sub.of_opc(supi, k, B.take(16n, rest))

def Sub.digits_ok(+supi: B.Bytes(), rest: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, Sub>:
  match ok:
    case True{}:
      Sub.of_k(supi, B.take(16n, rest))
    case False{}:
      Fail{B.Invalid{32}}

def Sub.of_supi(r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, Sub>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+supi, rest)}:
      Sub.digits_ok(supi, rest, Sub.digits(supi))

def Sub.of_count(r: B.Read(U32)) -> Result<&2, &2, B.Err, Sub>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(n, rest)}:
      Sub.of_supi(B.take(U32.to_nat(n), rest))

def Sub.read(value: B.Bytes()) -> Result<&2, &2, B.Err, Sub>:
  Sub.of_count(B.u8(value))

def Sub.write(s: Sub) -> B.Bytes():
  match s:
    case Sub{+supi, k, opc, amf, sqn}:
      B.write_u8(U32.from_nat(List.length(&2, U32, supi)), List.append(&2, U32, supi, List.append(&2, U32, k, List.append(&2, U32, opc, List.append(&2, U32, amf, sqn)))))

def Result.ok(-A: Data, r: Result<&2, &2, B.Err, A>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      True{}

# What a known tag's value must be (§ The frame protocol); unknown tags carry anything.
def Tag.valid(tag: Nat, value: B.Bytes()) -> Bool:
  match tag:
    case 1n:
      Len.is(value, 3n)
    case 2n:
      Len.is(value, 1n)
    case 3n:
      Len.is(value, 2n)
    case 4n:
      Len.is(value, 1n)
    case 5n:
      Len.is(value, 3n)
    case 7n:
      Len.is(value, 1n)
    case 9n:
      Len.is(value, 4n)
    case 10n:
      Len.is(value, 1n)
    case 11n:
      Len.is(value, 4n)
    case 12n:
      Len.is(value, 4n)
    case 13n:
      Len.is(value, 4n)
    case 14n:
      Len.is(value, 4n)
    case 15n:
      Len.is(value, 32n)
    case 16n:
      Len.is(value, 1n)
    case 32n:
      Result.ok(Sub, Sub.read(value))
    case _:
      True{}

def Tags.valid(tl: List<&2, T.Tlv>) -> Bool:
  match tl:
    case Nil{}:
      True{}
    case T.Tlv{+kind, len, +body} <> more:
      Bool.and(Tag.valid(U32.to_nat(kind), body), Tags.valid(more))

def Config.pick(v: B.Bytes(), later: Maybe<&2, B.Bytes()>, hit: Bool) -> Maybe<&2, B.Bytes()>:
  match later:
    case Some{w}:
      Some{w}
    case None{}:
      match hit:
        case True{}:
          Some{v}
        case False{}:
          None{}

# The last value given for a tag.
def Config.get(+tag: U32, tl: List<&2, T.Tlv>) -> Maybe<&2, B.Bytes()>:
  match tl:
    case Nil{}:
      None{}
    case T.Tlv{kind, len, body} <> more:
      Config.pick(body, Config.get(tag, more), U32.is_eq(kind, tag))

def Config.keep(v: B.Bytes(), more: List<&2, B.Bytes()>, hit: Bool) -> List<&2, B.Bytes()>:
  match hit:
    case True{}:
      v <> more
    case False{}:
      more

# Every subscriber, in order.
def Config.subscribers(tl: List<&2, T.Tlv>) -> List<&2, B.Bytes()>:
  match tl:
    case Nil{}:
      []
    case T.Tlv{kind, len, body} <> more:
      Config.keep(body, Config.subscribers(more), U32.is_eq(kind, 32))

# Events
# ------

type Evt is Data:
  Config{len: U32, tlvs: List<&2, T.Tlv>}
  NgapAssocUp{assoc: U32}
  NgapAssocDown{assoc: U32}
  NgapData{assoc: U32, stream: U32, len: U32, bytes: B.Bytes()}
  PfcpData{len: U32, bytes: B.Bytes()}
  TimerFired{timer: U32}

# An event with the entropy the edge attached to it.
type Input is Data:
  Input{entropy: B.Bytes(), event: Evt}

def Input.entropy(i: Input) -> B.Bytes():
  match i:
    case Input{entropy, event}:
      entropy

def Input.event(i: Input) -> Evt:
  match i:
    case Input{entropy, event}:
      event

def Evt.kind(e: Evt) -> U32:
  match e:
    case Config{len, tlvs}:
      1
    case NgapAssocUp{assoc}:
      2
    case NgapAssocDown{assoc}:
      3
    case NgapData{assoc, stream, len, bytes}:
      4
    case PfcpData{len, bytes}:
      5
    case TimerFired{timer}:
      6

def Evt.valid(e: Evt) -> Bool:
  match e:
    case Config{+len, +tlvs}:
      Bool.and(Nat.is_eq(U32.to_nat(len), T.Tlvs.size(tlvs)), Bool.and(T.Tlvs.valid(tlvs), Tags.valid(tlvs)))
    case NgapAssocUp{assoc}:
      True{}
    case NgapAssocDown{assoc}:
      True{}
    case NgapData{assoc, +stream, +len, +bytes}:
      Bool.and(B.fits16(stream), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, bytes)))
    case PfcpData{+len, +bytes}:
      Nat.is_eq(U32.to_nat(len), List.length(&2, U32, bytes))
    case TimerFired{timer}:
      True{}

def Input.valid(i: Input) -> Bool:
  match i:
    case Input{entropy, event}:
      Bool.and(Nat.is_eq(List.length(&2, U32, entropy), 32n), Evt.valid(event))

def Evt.Res() -> Data:
  B.Read(Evt)

def Evt.config_tags(+len: U32, rest: B.Bytes(), tlvs: List<&2, T.Tlv>, ok: Bool) -> Evt.Res():
  match ok:
    case True{}:
      Done{(Config{len, tlvs}, rest)}
    case False{}:
      Fail{B.Invalid{1}}

def Evt.config_of_tlvs(+len: U32, rest: B.Bytes(), r: Result<&2, &2, B.Err, List<&2, T.Tlv>>) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+tlvs}:
      Evt.config_tags(len, rest, tlvs, Tags.valid(tlvs))

def Evt.config_of_body(+len: U32, r: B.Read(B.Bytes())) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+body, rest)}:
      Evt.config_of_tlvs(len, rest, T.Tlvs.decode(body))

def Evt.config(r: B.Read(U32)) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+len, rest)}:
      Evt.config_of_body(len, B.take(U32.to_nat(len), rest))

def Evt.assoc_up(r: B.Read(U32)) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(assoc, rest)}:
      Done{(NgapAssocUp{assoc}, rest)}

def Evt.assoc_down(r: B.Read(U32)) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(assoc, rest)}:
      Done{(NgapAssocDown{assoc}, rest)}

def Evt.data_of_bytes(assoc: U32, stream: U32, +len: U32, r: B.Read(B.Bytes())) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bytes, rest)}:
      Done{(NgapData{assoc, stream, len, bytes}, rest)}

def Evt.data_of_len(assoc: U32, stream: U32, r: B.Read(U32)) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+len, rest)}:
      Evt.data_of_bytes(assoc, stream, len, B.take(U32.to_nat(len), rest))

def Evt.data_of_stream(assoc: U32, r: B.Read(U32)) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(stream, rest)}:
      Evt.data_of_len(assoc, stream, B.u32(rest))

def Evt.data(r: B.Read(U32)) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(assoc, rest)}:
      Evt.data_of_stream(assoc, B.u16(rest))

def Evt.pfcp_of_bytes(+len: U32, r: B.Read(B.Bytes())) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bytes, rest)}:
      Done{(PfcpData{len, bytes}, rest)}

def Evt.pfcp(r: B.Read(U32)) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+len, rest)}:
      Evt.pfcp_of_bytes(len, B.take(U32.to_nat(len), rest))

def Evt.timer(r: B.Read(U32)) -> Evt.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(timer, rest)}:
      Done{(TimerFired{timer}, rest)}

def Evt.payload(kind: Nat, +raw: U32, bs: B.Bytes()) -> Evt.Res():
  match kind:
    case 1n:
      Evt.config(B.u32(bs))
    case 2n:
      Evt.assoc_up(B.u32(bs))
    case 3n:
      Evt.assoc_down(B.u32(bs))
    case 4n:
      Evt.data(B.u32(bs))
    case 5n:
      Evt.pfcp(B.u32(bs))
    case 6n:
      Evt.timer(B.u32(bs))
    case _:
      Fail{B.Unsupported{raw}}

def Evt.write(e: Evt, rest: B.Bytes()) -> B.Bytes():
  match e:
    case Config{len, tlvs}:
      B.write_u32(len, T.Tlvs.write(tlvs, rest))
    case NgapAssocUp{assoc}:
      B.write_u32(assoc, rest)
    case NgapAssocDown{assoc}:
      B.write_u32(assoc, rest)
    case NgapData{assoc, stream, len, bytes}:
      B.write_u32(assoc, B.write_u16(stream, B.write_u32(len, List.append(&2, U32, bytes, rest))))
    case PfcpData{len, bytes}:
      B.write_u32(len, List.append(&2, U32, bytes, rest))
    case TimerFired{timer}:
      B.write_u32(timer, rest)

def Input.of_event(entropy: B.Bytes(), r: Evt.Res()) -> B.Read(Input):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(event, rest)}:
      Done{(Input{entropy, event}, rest)}

def Input.of_entropy(+kind: U32, r: B.Read(B.Bytes())) -> B.Read(Input):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(entropy, rest)}:
      Input.of_event(entropy, Evt.payload(U32.to_nat(kind), kind, rest))

def Input.of_kind(r: B.Read(U32)) -> B.Read(Input):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+kind, rest)}:
      Input.of_entropy(kind, B.take(32n, rest))

def Input.read(bs: B.Bytes()) -> B.Read(Input):
  Input.of_kind(B.u8(bs))

def Input.write(i: Input, rest: B.Bytes()) -> B.Bytes():
  match i:
    case Input{entropy, +event}:
      B.write_u8(Evt.kind(event), List.append(&2, U32, entropy, Evt.write(event, rest)))

def Evt.config_make(+tlvs: List<&2, T.Tlv>) -> Evt:
  Config{U32.from_nat(T.Tlvs.size(tlvs)), tlvs}

def Evt.data_make(assoc: U32, stream: U32, +bytes: B.Bytes()) -> Evt:
  NgapData{assoc, stream, U32.from_nat(List.length(&2, U32, bytes)), bytes}

def Evt.pfcp_make(+bytes: B.Bytes()) -> Evt:
  PfcpData{U32.from_nat(List.length(&2, U32, bytes)), bytes}

# Actions
# -------

type Action is Data:
  NgapSend{assoc: U32, stream: U32, len: U32, bytes: B.Bytes()}
  NgapClose{assoc: U32}
  PfcpSend{len: U32, bytes: B.Bytes()}
  TimerStart{timer: U32, ms: U32}
  TimerCancel{timer: U32}
  Log{level: U32, len: U32, text: B.Bytes()}

# The actions answering one event, with their count word.
type Actions is Data:
  Actions{count: U32, items: List<&2, Action>}

def Action.kind(a: Action) -> U32:
  match a:
    case NgapSend{assoc, stream, len, bytes}:
      129
    case NgapClose{assoc}:
      130
    case PfcpSend{len, bytes}:
      131
    case TimerStart{timer, ms}:
      132
    case TimerCancel{timer}:
      133
    case Log{level, len, text}:
      134

def Action.valid(a: Action) -> Bool:
  match a:
    case NgapSend{assoc, +stream, +len, +bytes}:
      Bool.and(B.fits16(stream), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, bytes)))
    case NgapClose{assoc}:
      True{}
    case PfcpSend{+len, +bytes}:
      Nat.is_eq(U32.to_nat(len), List.length(&2, U32, bytes))
    case TimerStart{timer, ms}:
      True{}
    case TimerCancel{timer}:
      True{}
    case Log{+level, +len, +text}:
      Bool.and(U32.is_lt(level, 4), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, text)))

def Items.valid(items: List<&2, Action>) -> Bool:
  match items:
    case Nil{}:
      True{}
    case a <> more:
      Bool.and(Action.valid(a), Items.valid(more))

def Actions.valid(as: Actions) -> Bool:
  match as:
    case Actions{+count, +items}:
      Bool.and(B.fits16(count), Bool.and(Nat.is_eq(U32.to_nat(count), List.length(&2, Action, items)), Items.valid(items)))

def Action.Res() -> Data:
  B.Read(Action)

def Action.send_of_bytes(assoc: U32, stream: U32, +len: U32, r: B.Read(B.Bytes())) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bytes, rest)}:
      Done{(NgapSend{assoc, stream, len, bytes}, rest)}

def Action.send_of_len(assoc: U32, stream: U32, r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+len, rest)}:
      Action.send_of_bytes(assoc, stream, len, B.take(U32.to_nat(len), rest))

def Action.send_of_stream(assoc: U32, r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(stream, rest)}:
      Action.send_of_len(assoc, stream, B.u32(rest))

def Action.send(r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(assoc, rest)}:
      Action.send_of_stream(assoc, B.u16(rest))

def Action.close(r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(assoc, rest)}:
      Done{(NgapClose{assoc}, rest)}

def Action.pfcp_of_bytes(+len: U32, r: B.Read(B.Bytes())) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bytes, rest)}:
      Done{(PfcpSend{len, bytes}, rest)}

def Action.pfcp(r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+len, rest)}:
      Action.pfcp_of_bytes(len, B.take(U32.to_nat(len), rest))

def Action.start_of_ms(timer: U32, r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(ms, rest)}:
      Done{(TimerStart{timer, ms}, rest)}

def Action.start(r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(timer, rest)}:
      Action.start_of_ms(timer, B.u32(rest))

def Action.cancel(r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(timer, rest)}:
      Done{(TimerCancel{timer}, rest)}

def Action.log_of_text(level: U32, +len: U32, r: B.Read(B.Bytes())) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(text, rest)}:
      Done{(Log{level, len, text}, rest)}

def Action.log_of_len(level: U32, r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+len, rest)}:
      Action.log_of_text(level, len, B.take(U32.to_nat(len), rest))

def Action.log_level(+level: U32, rest: B.Bytes(), ok: Bool) -> Action.Res():
  match ok:
    case True{}:
      Action.log_of_len(level, B.u32(rest))
    case False{}:
      Fail{B.Invalid{level}}

def Action.log(r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+level, rest)}:
      Action.log_level(level, rest, U32.is_lt(level, 4))

def Action.payload(kind: Nat, +raw: U32, bs: B.Bytes()) -> Action.Res():
  match kind:
    case 129n:
      Action.send(B.u32(bs))
    case 130n:
      Action.close(B.u32(bs))
    case 131n:
      Action.pfcp(B.u32(bs))
    case 132n:
      Action.start(B.u32(bs))
    case 133n:
      Action.cancel(B.u32(bs))
    case 134n:
      Action.log(B.u8(bs))
    case _:
      Fail{B.Unsupported{raw}}

def Action.of_kind(r: B.Read(U32)) -> Action.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+kind, rest)}:
      Action.payload(U32.to_nat(kind), kind, rest)

def Action.read(bs: B.Bytes()) -> Action.Res():
  Action.of_kind(B.u8(bs))

def Action.write(a: Action, rest: B.Bytes()) -> B.Bytes():
  match a:
    case NgapSend{assoc, stream, len, bytes}:
      B.write_u8(129, B.write_u32(assoc, B.write_u16(stream, B.write_u32(len, List.append(&2, U32, bytes, rest)))))
    case NgapClose{assoc}:
      B.write_u8(130, B.write_u32(assoc, rest))
    case PfcpSend{len, bytes}:
      B.write_u8(131, B.write_u32(len, List.append(&2, U32, bytes, rest)))
    case TimerStart{timer, ms}:
      B.write_u8(132, B.write_u32(timer, B.write_u32(ms, rest)))
    case TimerCancel{timer}:
      B.write_u8(133, B.write_u32(timer, rest))
    case Log{level, len, text}:
      B.write_u8(134, B.write_u8(level, B.write_u32(len, List.append(&2, U32, text, rest))))

def Items.cons(a: Action, r: B.Read(List<&2, Action>)) -> B.Read(List<&2, Action>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(items, rest)}:
      Done{(a <> items, rest)}

def Items.next(r: Action.Res(), more: B.Bytes() -> B.Read(List<&2, Action>)) -> B.Read(List<&2, Action>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(a, rest)}:
      Items.cons(a, more(rest))

# Exactly n actions.
def Items.read(n: Nat, bs: B.Bytes()) -> B.Read(List<&2, Action>):
  match n:
    case 0n:
      Done{([], bs)}
    case 1n+p:
      Items.next(Action.read(bs), left => Items.read(p, left))

def Items.write(items: List<&2, Action>, rest: B.Bytes()) -> B.Bytes():
  match items:
    case Nil{}:
      rest
    case a <> more:
      Action.write(a, Items.write(more, rest))

def Actions.of_items(+count: U32, r: B.Read(List<&2, Action>)) -> B.Read(Actions):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(items, rest)}:
      Done{(Actions{count, items}, rest)}

def Actions.of_count(r: B.Read(U32)) -> B.Read(Actions):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+count, rest)}:
      Actions.of_items(count, Items.read(U32.to_nat(count), rest))

def Actions.of_kind(+kind: U32, rest: B.Bytes(), ok: Bool) -> B.Read(Actions):
  match ok:
    case True{}:
      Actions.of_count(B.u16(rest))
    case False{}:
      Fail{B.Unsupported{kind}}

def Actions.of_byte(r: B.Read(U32)) -> B.Read(Actions):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+kind, rest)}:
      Actions.of_kind(kind, rest, U32.is_eq(kind, 128))

def Actions.read(bs: B.Bytes()) -> B.Read(Actions):
  Actions.of_byte(B.u8(bs))

def Actions.write(as: Actions, rest: B.Bytes()) -> B.Bytes():
  match as:
    case Actions{count, items}:
      B.write_u8(128, B.write_u16(count, Items.write(items, rest)))

def Actions.make(+items: List<&2, Action>) -> Actions:
  Actions{U32.from_nat(List.length(&2, Action, items)), items}
