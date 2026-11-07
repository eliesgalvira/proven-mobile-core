import Base
import ../../bytes.bend as B
import ../../aper.bend as Ap
import ../../tlv.bend as T
import ../../ngap/frame.bend as Fr
import ../../frame.bend as F
import ../../state.bend as S
import ../../step.bend as K
import ../../amf/ngap.bend as N
import ./vec.bend as V
import ./amf.bend as A
import ./pfcp.bend as Pc

# Helpers for the replays of the handover capture (ticket 24): its messages
# by index, the hand-built ones by name, the capture as far as an active PDU
# session on gNB 1, and ways to look at what a step sends.

# Entropy with the captured RAND, the captured uplink TEID at 20 and the local SEID 2 at 24.
def entropy() -> B.Bytes():
  [241, 242, 186, 93, 34, 185, 229, 167, 11, 146, 225, 106, 25, 144, 34, 79, 0, 0, 0, 7, 0, 0, 104, 224, 0, 0, 0, 2, 0, 0, 0, 0]

def step(st: S.State, ev: F.Evt) -> N.Step():
  K.Kernel.step(st, ev, entropy())

def after(st: S.State, ev: F.Evt) -> S.State:
  K.Kernel.state(step(st, ev))

def on(assoc: U32, +bytes: B.Bytes()) -> F.Evt:
  F.NgapData{assoc, 0, U32.from_nat(List.length(&2, U32, bytes)), bytes}

def hex(+msgs: List<&2, V.Vec>, +index: Nat) -> B.Bytes():
  A.hex_of(A.entry(index, msgs), "hex")

def hand_of(+name: String, msgs: List<&2, V.Vec>) -> Maybe<&2, B.Bytes()>:
  match msgs:
    case Nil{}:
      None{}
    case +m <> rest:
      V.Vec.hex_if(m, String.eq(V.Vec.text(V.Vec.field(m, "message")), name), hand_of(name, rest))

# A hand-built message by name.
def hand(+name: String, msgs: List<&2, V.Vec>) -> B.Bytes():
  A.ie_or_empty(hand_of(name, msgs))

# The capture as far as the active PDU session on gNB 1 (association 1),
# both gNBs set up; gNB 2 is association 2.
def active(+msgs: List<&2, V.Vec>) -> S.State:
  +st0 : S.State = after(after(after(S.State.initial(), F.Evt.config_make(A.config([T.Tlv.make(32, A.subscriber([0, 0, 0, 0, 0, 32]))]))), Pc.pfcp_event(hex(msgs, 1n))), F.NgapAssocUp{1})
  +st1 : S.State = after(after(after(st0, F.NgapAssocUp{2}), on(1, hex(msgs, 8n))), on(2, hex(msgs, 10n)))
  +st2 : S.State = after(after(after(after(after(st1, on(1, hex(msgs, 12n))), on(1, hex(msgs, 16n))), on(1, hex(msgs, 20n))), on(1, hex(msgs, 25n))), on(1, hex(msgs, 26n)))
  +o3 : N.Step() = step(st2, on(1, hex(msgs, 28n)))
  +st4 : S.State = after(K.Kernel.state(o3), Pc.pfcp_event(Pc.with_seq(hex(msgs, 36n), Pc.pfcp_seq(Pc.first_pfcp(K.Kernel.frames(o3))))))
  +o5 : N.Step() = step(st4, on(1, hex(msgs, 40n)))
  after(K.Kernel.state(o5), Pc.pfcp_event(Pc.with_seq(hex(msgs, 42n), Pc.pfcp_seq(Pc.first_pfcp(K.Kernel.frames(o5))))))

# An NGAP PDU with one IE's value replaced.
def swap_if(+i: U32, crit: U32, v: B.Bytes(), value: B.Bytes(), hit: Bool) -> Fr.Ie:
  match hit:
    case True{}:
      Fr.Ie{i, crit, value}
    case False{}:
      Fr.Ie{i, crit, v}

def swap(+id: U32, +value: B.Bytes(), ies: List<&2, Fr.Ie>) -> List<&2, Fr.Ie>:
  match ies:
    case Nil{}:
      []
    case Fr.Ie{+i, crit, v} <> more:
      swap_if(i, crit, v, value, U32.is_eq(i, id)) <> swap(id, value, more)

def with_of(+id: U32, +bits: Ap.Bits(), +pdu: B.Bytes(), r: Result<&2, &2, B.Err, Fr.Pdu>) -> B.Bytes():
  match r:
    case Fail{e}:
      []
    case Done{Fr.Pdu{kind, code, crit, value}}:
      N.Ngap.pdu(kind, code, crit, swap(id, Ap.pack(bits), A.ies_of(Fr.Pdu.read(pdu))))

def with_ie(+id: U32, +bits: Ap.Bits(), +pdu: B.Bytes()) -> B.Bytes():
  with_of(id, bits, pdu, Fr.Pdu.read(pdu))

def sent_pick(bytes: B.Bytes(), later: B.Bytes(), hit: Bool) -> B.Bytes():
  match hit:
    case True{}:
      bytes
    case False{}:
      later

# The first NGAP PDU a step sends on an association.
def sent_on(+assoc: U32, actions: List<&2, F.Action>) -> B.Bytes():
  match actions:
    case Nil{}:
      []
    case F.NgapSend{a, stream, len, bytes} <> more:
      sent_pick(bytes, sent_on(assoc, more), U32.is_eq(a, assoc))
    case x <> more:
      sent_on(assoc, more)

def is_pdu(+bytes: B.Bytes(), +kind: U32, +code: U32) -> Bool:
  A.pdu_is(Fr.Pdu.read(bytes), kind, code)

def ie(+id: U32, +pdu: B.Bytes()) -> B.Bytes():
  A.ie_or_empty(Fr.Ies.lookup(id, A.ies_of(Fr.Pdu.read(pdu))))

def warns(actions: List<&2, F.Action>) -> Nat:
  match actions:
    case Nil{}:
      0n
    case F.Log{F.Warn{}, len, text} <> more:
      1n+warns(more)
    case a <> more:
      warns(more)

def assoc_of(m: Maybe<&2, S.Ue>) -> U32:
  match m:
    case None{}:
      0
    case Some{u}:
      S.Ue.assoc(u)

def ue_on(+st: S.State) -> U32:
  assoc_of(A.ue1(st))

def ran_of(m: Maybe<&2, S.Ue>) -> B.Bytes():
  match m:
    case None{}:
      []
    case Some{u}:
      S.Ue.ran_id(u)

def ran_is(+st: S.State, ran: B.Bytes()) -> Bool:
  B.bytes_eq(ran_of(A.ue1(st)), ran)

# The UE where it was, in the same phase, the same sessions, no PFCP message.
def unchanged(+st: S.State, +o: N.Step()) -> Bool:
  Bool.and(Bool.and(U32.is_eq(ue_on(K.Kernel.state(o)), ue_on(st)), A.phase_is(K.Kernel.state(o), A.phase_name(A.ue1(st)))), Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o)), Pc.session_count(st)), Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o))), 0n)))
