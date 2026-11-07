import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../tlv.bend as T
import ../pfcp.bend as Pf
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as W
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./lib/amf.bend as A
import ./lib/pfcp.bend as Pc
import ./vectors/capture-handover.bend as Capture
import ./vectors/hand-ngap-handover.bend as Hand

# Replays the Xn handover of the handover capture: registration and a PDU
# session on gNB 1, then gNB 2's Path Switch Request, one PFCP Session
# Modification to gNB 2's tunnel, the UPF's captured answer, and the Path
# Switch Request Acknowledge with the captured NH and NCC. Then the hand-made
# cases: an unknown UE, a gNB without NG Setup, mismatched UE security
# capabilities, nothing to switch, the UPF refusing, and timers.

# Entropy with the captured RAND, a TEID at 20 and the local SEID 2 at 24.
def entropy() -> B.Bytes():
  [241, 242, 186, 93, 34, 185, 229, 167, 11, 146, 225, 106, 25, 144, 34, 79, 0, 0, 0, 7, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0]

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

# A Path Switch Request with one IE's value replaced.
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

def request_with(+id: U32, +bits: Ap.Bits(), +psr: B.Bytes()) -> B.Bytes():
  N.Ngap.pdu(Fr.Pdu.initiating(), 25, Fr.Criticality.reject(), swap(id, Ap.pack(bits), A.ies_of(Fr.Pdu.read(psr))))

def assoc_of(m: Maybe<&2, S.Ue>) -> U32:
  match m:
    case None{}:
      0
    case Some{u}:
      S.Ue.assoc(u)

# The RAN-UE-NGAP-ID a Path Switch Request gives.
def psr_ran(r: Result<&2, &2, B.Err, W.PathSwitchRequest.View>) -> B.Bytes():
  match r:
    case Done{W.PathSwitchRequest.View{ran, amf, uli, caps, items, failed, rrc}}:
      ran
    case _:
      []

# A Session Modification Response refusing, cause 73.
def refusal(seq: U32) -> F.Evt:
  Pc.pfcp_event(Pf.Msg.write(Pf.Msg.make(53, Some{[0, 0, 0, 0, 0, 0, 9, 45]}, seq, [T.Tlv.make(19, [73])]), []))

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

# The UE security capabilities stored for UE 1, as NGAP carries them.
def stored(m: Maybe<&2, S.Ue>) -> B.Bytes():
  match m:
    case None{}:
      []
    case Some{u}:
      Ap.pack(G.UESecurityCapabilities.write(N.Ngap.ue_caps(N.Ue.caps(u)), 0n, []))

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

def unchanged(+st: S.State, +o: N.Step()) -> Bool:
  Bool.and(Bool.and(U32.is_eq(ue_on(K.Kernel.state(o)), ue_on(st)), A.phase_is(K.Kernel.state(o), A.phase_name(A.ue1(st)))), Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o)), Pc.session_count(st)), Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o))), 0n)))

# The first session's guard fired n + 1 times in a row.
def expire(n: Nat, +timer: U32, st: S.State) -> N.Step():
  match n:
    case 0n:
      step(st, F.TimerFired{timer})
    case 1n+p:
      expire(p, timer, K.Kernel.state(step(st, F.TimerFired{timer})))

def main() -> IO(Unit):
  do IO<Unit>:
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    +hands : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Hand.data(), "messages"))
    +st : S.State = active(msgs)
    C.Check.report("the capture replayed: the UE registered on gNB 1 with an active PDU session", Bool.and(A.phase_is(st, "registered"), Bool.and(U32.is_eq(ue_on(st), 1), Pc.sphase_is(st, "active"))))
    +psr : B.Bytes() = hex(msgs, 51n)
    +o1 : N.Step() = step(st, on(2, psr))
    +st1 : S.State = K.Kernel.state(o1)
    +mod : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(o1))
    C.Check.report("Path Switch Request: the UE is owned by gNB 2 under its RAN-UE-NGAP-ID, switching", Bool.and(U32.is_eq(ue_on(st1), 2), Bool.and(ran_is(st1, psr_ran(W.PathSwitchRequest.view(A.ies_of(Fr.Pdu.read(psr))))), A.phase_is(st1, "switching"))))
    C.Check.report("Path Switch Request: one PFCP Session Modification repointing the downlink FAR to gNB 2's captured tunnel, under the session's guard", Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o1))), 1n), Bool.and(U32.is_eq(Pc.pfcp_kind(mod), 52), Bool.and(B.bytes_eq(Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(mod)))), Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(hex(msgs, 52n)))))), Pc.sphase_is(st1, "repointing")))))
    C.Check.report("Path Switch Request: nothing is answered before the UPF", Nat.is_eq(List.length(&2, F.Action, A.sends(K.Kernel.frames(o1))), 0n))
    +o2 : N.Step() = step(st1, Pc.pfcp_event(Pc.with_seq(hex(msgs, 53n), Pc.pfcp_seq(mod))))
    +st2 : S.State = K.Kernel.state(o2)
    +ack : B.Bytes() = sent_on(2, K.Kernel.frames(o2))
    +cap : B.Bytes() = hex(msgs, 54n)
    C.Check.report("Session Modification Response: Path Switch Request Acknowledge to gNB 2, the UE registered, its session active", Bool.and(is_pdu(ack, 1, 25), Bool.and(A.phase_is(st2, "registered"), Pc.sphase_is(st2, "active"))))
    C.Check.report("Path Switch Request Acknowledge: the captured NH and NCC (NCC 2) from the captured KAMF and KgNB", A.same_ie(93, ack, cap))
    C.Check.report("Path Switch Request Acknowledge: the captured AMF-UE-NGAP-ID, RAN-UE-NGAP-ID, switched session list and Allowed NSSAI", Bool.and(A.same_ie(10, ack, cap), Bool.and(A.same_ie(85, ack, cap), Bool.and(A.same_ie(77, ack, cap), A.same_ie(0, ack, cap)))))
    C.Check.report("Path Switch Request Acknowledge: the stored UE security capabilities, besides the captured IEs", Bool.and(B.bytes_eq(ie(119, ack), stored(A.ue1(st))), Nat.is_eq(List.length(&2, Fr.Ie, A.ies_of(Fr.Pdu.read(ack))), 6n)))
    C.Check.report("Session Modification Response: the switch's guard and the session's stopped", Nat.is_eq(A.timer_cancels(K.Kernel.frames(o2)), 2n))
    +o_src : N.Step() = step(st2, on(1, A.release_request(A.ran_of(W.InitialUEMessage.view(A.ies_of(Fr.Pdu.read(hex(msgs, 12n))))))))
    C.Check.report("gNB 1's UE Context Release Request afterwards: Error Indication, the UE stays with gNB 2", Bool.and(is_pdu(sent_on(1, K.Kernel.frames(o_src)), 0, 9), Bool.and(U32.is_eq(ue_on(K.Kernel.state(o_src)), 2), A.phase_is(K.Kernel.state(o_src), "registered"))))
    +o_unknown : N.Step() = step(st, on(2, request_with(100, G.AMF_UE_NGAP_ID.write([3], 0n, []), psr)))
    C.Check.report("an unknown UE: Path Switch Request Failure, no state change", Bool.and(is_pdu(sent_on(2, K.Kernel.frames(o_unknown)), 2, 25), unchanged(st, o_unknown)))
    +st_three : S.State = after(st, F.NgapAssocUp{3})
    +o_bare : N.Step() = step(st_three, on(3, psr))
    C.Check.report("a gNB without NG Setup: Path Switch Request Failure, no state change", Bool.and(is_pdu(sent_on(3, K.Kernel.frames(o_bare)), 2, 25), unchanged(st_three, o_bare)))
    +o_caps : N.Step() = step(st, on(2, request_with(119, G.UESecurityCapabilities.write(N.Ngap.ue_caps([128, 128, 0, 0]), 0n, []), psr)))
    +o_caps2 : N.Step() = step(K.Kernel.state(o_caps), Pc.pfcp_event(Pc.with_seq(hex(msgs, 53n), Pc.pfcp_seq(Pc.first_pfcp(K.Kernel.frames(o_caps))))))
    C.Check.report("mismatched UE security capabilities: logged, and the acknowledgement carries the stored ones", Bool.and(Nat.is_eq(warns(K.Kernel.frames(o_caps)), 1n), Bool.and(Nat.is_eq(warns(K.Kernel.frames(o1)), 0n), B.bytes_eq(ie(119, sent_on(2, K.Kernel.frames(o_caps2))), ie(119, ack)))))
    +st_reg : S.State = after(after(after(after(after(after(after(after(after(after(S.State.initial(), F.Evt.config_make(A.config([T.Tlv.make(32, A.subscriber([0, 0, 0, 0, 0, 32]))]))), Pc.pfcp_event(hex(msgs, 1n))), F.NgapAssocUp{1}), F.NgapAssocUp{2}), on(2, hex(msgs, 10n))), on(1, hex(msgs, 12n))), on(1, hex(msgs, 16n))), on(1, hex(msgs, 20n))), on(1, hex(msgs, 25n))), on(1, hex(msgs, 26n)))
    +o_none : N.Step() = step(st_reg, on(2, hand("PathSwitchRequest", hands)))
    C.Check.report("no PDU session to switch: the hand-built Path Switch Request Failure byte for byte, no state change", Bool.and(B.bytes_eq(sent_on(2, K.Kernel.frames(o_none)), hand("PathSwitchRequestFailure", hands)), unchanged(st_reg, o_none)))
    +o_hand : N.Step() = step(st, on(2, hand("PathSwitchRequest", hands)))
    +hmod : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(o_hand))
    +hack : B.Bytes() = sent_on(2, K.Kernel.frames(step(K.Kernel.state(o_hand), Pc.pfcp_event(Pc.with_seq(hex(msgs, 53n), Pc.pfcp_seq(hmod))))))
    C.Check.report("the hand-built Path Switch Request: its tunnel, session 1 switched and session 2, failed at gNB 2, not ours to release", Bool.and(B.bytes_eq(Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(hmod)))), [1, 0, 0, 0, 0, 2, 10, 33, 0, 31]), Bool.and(A.same_ie(77, hack, cap), B.bytes_eq(ie(68, hack), []))))
    +o_no : N.Step() = step(st1, refusal(Pc.pfcp_seq(mod)))
    +fail : B.Bytes() = sent_on(2, K.Kernel.frames(o_no))
    C.Check.report("the UPF refuses: the session deleted there, Path Switch Request Failure naming it, the UE released", Bool.and(is_pdu(fail, 2, 25), Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_no)), 0n), Bool.and(U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_no))), 54), Bool.and(A.phase_is(K.Kernel.state(o_no), "releasing"), is_pdu(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_no)), 1n)), 0, 41))))))
    +skey : U32 = Pc.session_timer(st1)
    C.Check.report("no Session Modification Response: the same request three times again, the UE still switching", Bool.and(B.bytes_eq(Pc.first_pfcp(K.Kernel.frames(expire(0n, skey, st1))), mod), Bool.and(B.bytes_eq(Pc.first_pfcp(K.Kernel.frames(expire(2n, skey, st1))), mod), A.phase_is(K.Kernel.state(expire(2n, skey, st1)), "switching"))))
    +o_late : N.Step() = expire(3n, skey, st1)
    C.Check.report("no Session Modification Response after the third retransmission: as refused", Bool.and(is_pdu(sent_on(2, K.Kernel.frames(o_late)), 2, 25), Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_late)), 0n), A.phase_is(K.Kernel.state(o_late), "releasing"))))
    +o_guard : N.Step() = step(st1, F.TimerFired{1})
    C.Check.report("the switch's guard fires: the UE released by gNB 2", Bool.and(A.phase_is(K.Kernel.state(o_guard), "releasing"), is_pdu(sent_on(2, K.Kernel.frames(o_guard)), 0, 41)))
