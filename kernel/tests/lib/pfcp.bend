import Base
import ../../bytes.bend as B
import ../../tlv.bend as T
import ../../pfcp.bend as Pf
import ../../frame.bend as F
import ../../table.bend as Tb
import ../../state.bend as S

# Helpers for the SMF tests: the PFCP messages a step sends, their IEs, the
# UPF's captured answers made ours, and the sessions a state holds.

def pfcp_sends(actions: List<&2, F.Action>) -> List<&2, B.Bytes()>:
  match actions:
    case Nil{}:
      []
    case F.PfcpSend{len, bytes} <> more:
      bytes <> pfcp_sends(more)
    case a <> more:
      pfcp_sends(more)

def head_or_empty(bs: List<&2, B.Bytes()>) -> B.Bytes():
  match bs:
    case Nil{}:
      []
    case b <> more:
      b

def first_pfcp(actions: List<&2, F.Action>) -> B.Bytes():
  head_or_empty(pfcp_sends(actions))

def msg_of(r: B.Read(Pf.Msg)) -> Maybe<&2, Pf.Msg>:
  match r:
    case Fail{e}:
      None{}
    case Done{(m, rest)}:
      Some{m}

def kind_of(m: Maybe<&2, Pf.Msg>) -> U32:
  match m:
    case None{}:
      0
    case Some{m}:
      Pf.Msg.kind(m)

def seq_of(m: Maybe<&2, Pf.Msg>) -> U32:
  match m:
    case None{}:
      0
    case Some{m}:
      Pf.Msg.seq(m)

def ies_in(m: Maybe<&2, Pf.Msg>) -> List<&2, T.Tlv>:
  match m:
    case None{}:
      []
    case Some{m}:
      Pf.Msg.ies(m)

def pfcp_kind(bytes: B.Bytes()) -> U32:
  kind_of(msg_of(Pf.Msg.read(bytes)))

def pfcp_seq(bytes: B.Bytes()) -> U32:
  seq_of(msg_of(Pf.Msg.read(bytes)))

def pfcp_ies(bytes: B.Bytes()) -> List<&2, T.Tlv>:
  ies_in(msg_of(Pf.Msg.read(bytes)))

def body_of(m: Maybe<&2, T.Tlv>) -> B.Bytes():
  match m:
    case None{}:
      []
    case Some{t}:
      T.Tlv.body(t)

def tlvs_or(r: Result<&2, &2, B.Err, List<&2, T.Tlv>>) -> List<&2, T.Tlv>:
  match r:
    case Fail{e}:
      []
    case Done{tl}:
      tl

# The body of the first IE of a kind, and the IEs inside it.
def body(kind: U32, ies: List<&2, T.Tlv>) -> B.Bytes():
  body_of(T.Tlvs.find(kind, ies))

def inside(kind: U32, ies: List<&2, T.Tlv>) -> List<&2, T.Tlv>:
  tlvs_or(T.Tlvs.decode(body(kind, ies)))

def Bool.to_nat(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# A captured PFCP response, its sequence number made ours.
def with_seq(+bytes: B.Bytes(), seq: U32) -> B.Bytes():
  List.append(&2, U32, List.take(&2, U32, bytes, 12n), List.append(&2, U32, List.drop(&2, U32, B.write_u32(seq, []), 1n), List.drop(&2, U32, bytes, 15n)))

# The captured Session Establishment Response with another cause (its Cause IE sits after the header and the Node ID).
def with_cause(+bytes: B.Bytes(), cause: U32) -> B.Bytes():
  List.append(&2, U32, List.take(&2, U32, bytes, 29n), cause <> List.drop(&2, U32, bytes, 30n))

def pfcp_event(+bytes: B.Bytes()) -> F.Evt:
  F.PfcpData{U32.from_nat(List.length(&2, U32, bytes)), bytes}

def sphase_of(p: S.SPhase) -> String:
  match p:
    case S.Creating{g, pti, accept, request}:
      "creating"
    case S.Setting{g, pti}:
      "setting"
    case S.Modifying{g, request}:
      "modifying"
    case S.Repointing{g, request}:
      "repointing"
    case S.Deleting{g, request}:
      "deleting"
    case S.Active{}:
      "active"

def sphase_name(m: Maybe<&2, S.Session>) -> String:
  match m:
    case None{}:
      "none"
    case Some{s}:
      sphase_of(S.Session.phase(s))

def session1(t: Tb.Table(S.Session)) -> Maybe<&2, S.Session>:
  match t:
    case (key, s) <> more:
      Some{s}
    case _:
      None{}

def session_count(st: S.State) -> Nat:
  List.length(&2, Sigma<&2, &2, U32, _ => S.Session>, S.State.sessions(st))

def first_ms(actions: List<&2, F.Action>) -> U32:
  match actions:
    case Nil{}:
      0
    case F.TimerStart{timer, ms} <> more:
      ms
    case a <> more:
      first_ms(more)

# A step stops the timer with this id, how often.
def cancel_count(actions: List<&2, F.Action>, +id: U32) -> Nat:
  match actions:
    case Nil{}:
      0n
    case F.TimerCancel{timer} <> more:
      Nat.add(Bool.to_nat(U32.is_eq(timer, id)), cancel_count(more, id))
    case a <> more:
      cancel_count(more, id)

def cancels(actions: List<&2, F.Action>, +id: U32) -> Bool:
  Bool.not(Nat.is_eq(cancel_count(actions, id), 0n))

def sphase_is(st: S.State, name: String) -> Bool:
  String.eq(sphase_name(session1(S.State.sessions(st))), name)

# The phase of the session under a key, "none" when there is none.
def sphase_at(st: S.State, +key: U32, name: String) -> Bool:
  String.eq(sphase_name(Tb.Table.get(S.Session, key, S.State.sessions(st))), name)

# A session's guard timer is its key, the first session's here.
def key1(t: Tb.Table(S.Session)) -> U32:
  match t:
    case (key, s) <> more:
      key
    case _:
      0

def session_timer(st: S.State) -> U32:
  key1(S.State.sessions(st))
