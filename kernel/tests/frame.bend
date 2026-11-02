import Base
import ../bytes.bend as B
import ../frame.bend as F
import ../tlv.bend as T
import ./lib/check.bend as C

# Hand-made frames of every kind read back and are valid; a truncated frame,
# an oversize one, an unknown kind and malformed Config values fail.

def entropy() -> B.Bytes():
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

def cat(xs: B.Bytes(), ys: B.Bytes()) -> B.Bytes():
  List.append(&2, U32, xs, ys)

def fails(-A: Data, r: Result<&2, &2, B.Err, A>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{x}:
      False{}

def body_is(r: B.Read(B.Bytes()), body: B.Bytes(), rest: B.Bytes()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(b, r2)}:
      Bool.and(B.bytes_eq(b, body), B.bytes_eq(r2, rest))

def reads_back_as(r: B.Read(F.Input), bs: B.Bytes()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(+i, rest)}:
      Bool.and(F.Input.valid(i), Bool.and(B.bytes_eq(F.Input.write(i, []), bs), B.bytes_eq(rest, [9, 9])))

# An input reads back from its own encoding, valid, with the rest untouched.
def reads_back(+i: F.Input) -> Bool:
  reads_back_as(F.Input.read(F.Input.write(i, [9, 9])), F.Input.write(i, []))

def event_of(r: B.Read(F.Input)) -> Maybe<&2, F.Evt>:
  match r:
    case Fail{e}:
      None{}
    case Done{(i, rest)}:
      Some{F.Input.event(i)}

def timer_is(e: Maybe<&2, F.Evt>, n: U32) -> Bool:
  match e:
    case Some{F.TimerFired{timer}}:
      U32.is_eq(timer, n)
    case _:
      False{}

def tlvs_of(e: Maybe<&2, F.Evt>) -> List<&2, T.Tlv>:
  match e:
    case Some{F.Config{len, tlvs}}:
      tlvs
    case _:
      []

def get_is(m: Maybe<&2, B.Bytes()>, v: B.Bytes()) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{w}:
      B.bytes_eq(w, v)

def sub_ok(r: Result<&2, &2, B.Err, F.Sub>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{F.Sub{supi, k, opc, amf, sqn}}:
      Bool.and(B.bytes_eq(supi, [48, 48, 49, 48, 49]), Bool.and(Nat.is_eq(List.length(&2, U32, k), 16n), B.bytes_eq(sqn, [0, 0, 0, 0, 0, 33])))

def actions_back_as(r: B.Read(F.Actions), bs: B.Bytes()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(+as, rest)}:
      Bool.and(F.Actions.valid(as), Bool.and(B.bytes_eq(F.Actions.write(as, []), bs), B.bytes_eq(rest, [7])))

def actions_back(+as: F.Actions) -> Bool:
  actions_back_as(F.Actions.read(F.Actions.write(as, [7])), F.Actions.write(as, []))

def sixteen() -> B.Bytes():
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

def subscriber() -> B.Bytes():
  F.Sub.write(F.Sub{[48, 48, 49, 48, 49], sixteen(), sixteen(), [128, 0], [0, 0, 0, 0, 0, 33]})

def config() -> List<&2, T.Tlv>:
  [T.Tlv.make(1, [2, 241, 16]), T.Tlv.make(5, [0, 0, 1]), T.Tlv.make(8, [105, 110, 116, 101, 114, 110, 101, 116]), T.Tlv.make(255, [1, 2, 3]), T.Tlv.make(5, [0, 0, 7]), T.Tlv.make(32, subscriber())]

def timer_frame() -> B.Bytes():
  F.Frame.write(F.Input.write(F.Input{entropy(), F.TimerFired{7}}, []), [])

def main() -> IO(Unit):
  do IO<Unit>:
    +cfg : F.Input = F.Input{entropy(), F.Evt.config_make(config())}
    +decoded : Maybe<&2, F.Evt> = event_of(F.Input.read(F.Input.write(cfg, [])))
    C.Check.report("a frame yields its body and the bytes after it", body_is(F.Frame.read([0, 0, 0, 3, 1, 2, 3, 4, 5]), [1, 2, 3], [4, 5]))
    C.Check.report("a frame short of its body is Short", fails(B.ReadValue(B.Bytes()), F.Frame.read([0, 0, 0, 3, 1, 2])))
    C.Check.report("a frame short of its length word is Short", fails(B.ReadValue(B.Bytes()), F.Frame.read([0, 0, 0])))
    C.Check.report("a body of 262144 octets is allowed by its length word", Bool.not(fails(B.ReadValue(U32), B.u32([0, 4, 0, 0]))))
    C.Check.report("a body over 262144 octets is refused on its length word alone", fails(B.ReadValue(B.Bytes()), F.Frame.read([0, 4, 0, 1])))
    C.Check.report("a TimerFired frame is 1 + 32 + 4 octets", B.bytes_eq(timer_frame(), cat([0, 0, 0, 37, 6], cat(entropy(), [0, 0, 0, 7]))))
    C.Check.report("TimerFired reads from hand-made bytes", timer_is(event_of(F.Input.read(cat([6], cat(entropy(), [0, 0, 0, 7, 9, 9])))), 7))
    C.Check.report("NgapAssocUp reads back", reads_back(F.Input{entropy(), F.NgapAssocUp{3}}))
    C.Check.report("NgapAssocDown reads back", reads_back(F.Input{entropy(), F.NgapAssocDown{3}}))
    C.Check.report("NgapData reads back", reads_back(F.Input{entropy(), F.Evt.data_make(3, 1, [0, 21, 0, 61])}))
    C.Check.report("PfcpData reads back", reads_back(F.Input{entropy(), F.Evt.pfcp_make([32, 1, 0, 12])}))
    C.Check.report("TimerFired reads back", reads_back(F.Input{entropy(), F.TimerFired{7}}))
    C.Check.report("Config reads back", reads_back(cfg))
    C.Check.report("an event short of its entropy is Short", fails(B.ReadValue(F.Input), F.Input.read([6, 1, 2, 3])))
    C.Check.report("an event of unknown kind is Unsupported", fails(B.ReadValue(F.Input), F.Input.read(cat([7], cat(entropy(), [0, 0, 0, 7])))))
    C.Check.report("NgapData short of its bytes is Short", fails(B.ReadValue(F.Input), F.Input.read(cat([4], cat(entropy(), [0, 0, 0, 3, 0, 1, 0, 0, 0, 4, 1, 2])))))
    C.Check.report("Config: the PLMN is read", get_is(F.Config.get(1, tlvs_of(decoded)), [2, 241, 16]))
    C.Check.report("Config: a repeated TAC yields the later value", get_is(F.Config.get(5, tlvs_of(decoded)), [0, 0, 7]))
    C.Check.report("Config: an unknown tag is carried and never asked for", Bool.and(Nat.is_eq(List.length(&2, T.Tlv, tlvs_of(decoded)), 6n), get_is(F.Config.get(255, tlvs_of(decoded)), [1, 2, 3])))
    C.Check.report("Config: an absent tag is None", Bool.not(get_is(F.Config.get(2, tlvs_of(decoded)), [])))
    C.Check.report("Config: the subscriber decodes", sub_ok(F.Sub.read(subscriber())))
    C.Check.report("Config: one subscriber is listed", Nat.is_eq(List.length(&2, B.Bytes(), F.Config.subscribers(tlvs_of(decoded))), 1n))
    C.Check.report("Config: a PLMN of two octets is rejected", fails(B.ReadValue(F.Input), F.Input.read(F.Input.write(F.Input{entropy(), F.Evt.config_make([T.Tlv.make(1, [2, 241])])}, []))))
    C.Check.report("Config: a subscriber with a non-digit SUPI is rejected", fails(B.ReadValue(F.Input), F.Input.read(F.Input.write(F.Input{entropy(), F.Evt.config_make([T.Tlv.make(32, cat([1, 65], cat(sixteen(), cat(sixteen(), [128, 0, 0, 0, 0, 0, 0, 33]))))])}, []))))
    C.Check.report("Config: a TLV short of its value is Short", fails(B.ReadValue(T.Tlv), T.Tlv.read([0, 1, 0, 3, 2, 241])))
    C.Check.report("Config: a TLV list with a trailing byte is Invalid", fails(List<&2, T.Tlv>, T.Tlvs.decode([0, 2, 0, 1, 5, 9])))
    C.Check.report("Actions: every kind reads back", actions_back(F.Actions.make([F.NgapSend{3, 1, 4, [0, 21, 0, 61]}, F.NgapClose{3}, F.PfcpSend{2, [32, 1]}, F.TimerStart{5, 3000}, F.TimerCancel{5}, F.Log{1, 2, [104, 105]}])))
    C.Check.report("Actions: an empty list is 0x80 0000", B.bytes_eq(F.Actions.write(F.Actions.make([]), []), [128, 0, 0]))
    C.Check.report("Actions: a wrong body kind is Unsupported", fails(B.ReadValue(F.Actions), F.Actions.read([1, 0, 0])))
    C.Check.report("Actions: a log level above 3 is Invalid", fails(B.ReadValue(F.Actions), F.Actions.read([128, 0, 1, 134, 4, 0, 0, 0, 0])))
    C.Check.report("Actions: a count beyond the actions present is Short", fails(B.ReadValue(F.Actions), F.Actions.read([128, 0, 2, 130, 0, 0, 0, 3])))
