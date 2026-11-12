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
import ./lib/handover.bend as H
import ./vectors/capture-handover.bend as Capture
import ./vectors/hand-ngap-handover.bend as Hand

# Replays the Xn handover of the handover capture: registration and a PDU
# session on gNB 1, then gNB 2's Path Switch Request, one PFCP Session
# Modification to gNB 2's tunnel, the UPF's captured answer, and the Path
# Switch Request Acknowledge with the captured NH and NCC. Then the hand-made
# cases: an unknown UE, a gNB without NG Setup, mismatched UE security
# capabilities, nothing to switch, the UPF refusing, and timers.

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

# The UE security capabilities stored for UE 1, as NGAP carries them.
def stored(m: Maybe<&2, S.Ue>) -> B.Bytes():
  match m:
    case None{}:
      []
    case Some{u}:
      Ap.pack(G.UESecurityCapabilities.write(N.Ngap.ue_caps(N.Ue.caps(u)), 0n, []))

# The first session's guard fired n + 1 times in a row.
def expire(n: Nat, +timer: U32, st: S.State) -> N.Step():
  match n:
    case 0n:
      H.step(st, F.TimerFired{timer})
    case 1n+p:
      expire(p, timer, K.Kernel.state(H.step(st, F.TimerFired{timer})))

def main() -> IO(Unit):
  do IO<Unit>:
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    +hands : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Hand.data(), "messages"))
    +st : S.State = H.active(msgs)
    C.Check.report("the capture replayed: the UE registered on gNB 1 with an active PDU session", Bool.and(A.phase_is(st, "registered"), Bool.and(U32.is_eq(H.ue_on(st), 1), Pc.sphase_is(st, "active"))))
    +psr : B.Bytes() = H.hex(msgs, 51n)
    +o1 : N.Step() = H.step(st, H.on(2, psr))
    +st1 : S.State = K.Kernel.state(o1)
    +mod : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(o1))
    C.Check.report("Path Switch Request: the UE is owned by gNB 2 under its RAN-UE-NGAP-ID, switching", Bool.and(U32.is_eq(H.ue_on(st1), 2), Bool.and(H.ran_is(st1, psr_ran(W.PathSwitchRequest.view(A.ies_of(Fr.Pdu.read(psr))))), A.phase_is(st1, "switching"))))
    C.Check.report("Path Switch Request: one PFCP Session Modification repointing the downlink FAR to gNB 2's captured tunnel, under the session's guard", Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o1))), 1n), Bool.and(U32.is_eq(Pc.pfcp_kind(mod), 52), Bool.and(B.bytes_eq(Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(mod)))), Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(H.hex(msgs, 52n)))))), Pc.sphase_is(st1, "repointing")))))
    C.Check.report("Path Switch Request: nothing is answered before the UPF", Nat.is_eq(List.length(&2, F.Action, A.sends(K.Kernel.frames(o1))), 0n))
    +o2 : N.Step() = H.step(st1, Pc.pfcp_event(Pc.with_seq(H.hex(msgs, 53n), Pc.pfcp_seq(mod))))
    +st2 : S.State = K.Kernel.state(o2)
    +ack : B.Bytes() = H.sent_on(2, K.Kernel.frames(o2))
    +cap : B.Bytes() = H.hex(msgs, 54n)
    C.Check.report("Session Modification Response: Path Switch Request Acknowledge to gNB 2, the UE registered, its session active", Bool.and(H.is_pdu(ack, 1, 25), Bool.and(A.phase_is(st2, "registered"), Pc.sphase_is(st2, "active"))))
    C.Check.report("Path Switch Request Acknowledge: the captured NH and NCC (NCC 2) from the captured KAMF and KgNB", A.same_ie(93, ack, cap))
    C.Check.report("Path Switch Request Acknowledge: the captured AMF-UE-NGAP-ID, RAN-UE-NGAP-ID, switched session list and Allowed NSSAI", Bool.and(A.same_ie(10, ack, cap), Bool.and(A.same_ie(85, ack, cap), Bool.and(A.same_ie(77, ack, cap), A.same_ie(0, ack, cap)))))
    C.Check.report("Path Switch Request Acknowledge: the stored UE security capabilities, besides the captured IEs", Bool.and(B.bytes_eq(H.ie(119, ack), stored(A.ue1(st))), Nat.is_eq(List.length(&2, Fr.Ie, A.ies_of(Fr.Pdu.read(ack))), 6n)))
    C.Check.report("Session Modification Response: the switch's guard and the session's stopped", Nat.is_eq(A.timer_cancels(K.Kernel.frames(o2)), 2n))
    +o_src : N.Step() = H.step(st2, H.on(1, A.release_request(A.ran_of(W.InitialUEMessage.view(A.ies_of(Fr.Pdu.read(H.hex(msgs, 12n))))))))
    C.Check.report("gNB 1's UE Context Release Request afterwards: Error Indication, the UE stays with gNB 2", Bool.and(H.is_pdu(H.sent_on(1, K.Kernel.frames(o_src)), 0, 9), Bool.and(U32.is_eq(H.ue_on(K.Kernel.state(o_src)), 2), A.phase_is(K.Kernel.state(o_src), "registered"))))
    +o_unknown : N.Step() = H.step(st, H.on(2, H.with_ie(100, G.AMF_UE_NGAP_ID.write([3], 0n, []), psr)))
    C.Check.report("an unknown UE: Path Switch Request Failure, no state change", Bool.and(H.is_pdu(H.sent_on(2, K.Kernel.frames(o_unknown)), 2, 25), H.unchanged(st, o_unknown)))
    +st_three : S.State = H.after(st, F.NgapAssocUp{3})
    +o_bare : N.Step() = H.step(st_three, H.on(3, psr))
    C.Check.report("a gNB without NG Setup: Error Indication, no state change", Bool.and(H.is_pdu(H.sent_on(3, K.Kernel.frames(o_bare)), 0, 9), H.unchanged(st_three, o_bare)))
    +o_caps : N.Step() = H.step(st, H.on(2, H.with_ie(119, G.UESecurityCapabilities.write(N.Ngap.ue_caps([128, 128, 0, 0]), 0n, []), psr)))
    +o_caps2 : N.Step() = H.step(K.Kernel.state(o_caps), Pc.pfcp_event(Pc.with_seq(H.hex(msgs, 53n), Pc.pfcp_seq(Pc.first_pfcp(K.Kernel.frames(o_caps))))))
    C.Check.report("mismatched UE security capabilities: logged, and the acknowledgement carries the stored ones", Bool.and(Nat.is_eq(H.warns(K.Kernel.frames(o_caps)), 1n), Bool.and(Nat.is_eq(H.warns(K.Kernel.frames(o1)), 0n), B.bytes_eq(H.ie(119, H.sent_on(2, K.Kernel.frames(o_caps2))), H.ie(119, ack)))))
    +st_reg : S.State = H.after(H.after(H.after(H.after(H.after(H.after(H.after(H.after(H.after(H.after(H.after(S.State.initial(), F.Evt.config_make(A.config([T.Tlv.make(32, A.subscriber([0, 0, 0, 0, 0, 32]))]))), Pc.pfcp_event(H.hex(msgs, 1n))), F.NgapAssocUp{1}), F.NgapAssocUp{2}), H.on(1, H.hex(msgs, 8n))), H.on(2, H.hex(msgs, 10n))), H.on(1, H.hex(msgs, 12n))), H.on(1, H.hex(msgs, 16n))), H.on(1, H.hex(msgs, 20n))), H.on(1, H.hex(msgs, 25n))), H.on(1, H.hex(msgs, 26n)))
    +o_none : N.Step() = H.step(st_reg, H.on(2, H.hand("PathSwitchRequest", hands)))
    C.Check.report("no PDU session to switch: the hand-built Path Switch Request Failure byte for byte, no state change", Bool.and(B.bytes_eq(H.sent_on(2, K.Kernel.frames(o_none)), H.hand("PathSwitchRequestFailure", hands)), H.unchanged(st_reg, o_none)))
    +o_hand : N.Step() = H.step(st, H.on(2, H.hand("PathSwitchRequest", hands)))
    +hmod : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(o_hand))
    +hack : B.Bytes() = H.sent_on(2, K.Kernel.frames(H.step(K.Kernel.state(o_hand), Pc.pfcp_event(Pc.with_seq(H.hex(msgs, 53n), Pc.pfcp_seq(hmod))))))
    C.Check.report("the hand-built Path Switch Request: its tunnel, session 1 switched and session 2, failed at gNB 2, not ours to release", Bool.and(B.bytes_eq(Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(hmod)))), [1, 0, 0, 0, 0, 2, 10, 33, 0, 31]), Bool.and(A.same_ie(77, hack, cap), B.bytes_eq(H.ie(68, hack), []))))
    +o_no : N.Step() = H.step(st1, refusal(Pc.pfcp_seq(mod)))
    +fail : B.Bytes() = H.sent_on(2, K.Kernel.frames(o_no))
    C.Check.report("the UPF refuses: the session being deleted there, Path Switch Request Failure naming it, the UE released", Bool.and(H.is_pdu(fail, 2, 25), Bool.and(Pc.sphase_is(K.Kernel.state(o_no), "deleting"), Bool.and(U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_no))), 54), Bool.and(A.phase_is(K.Kernel.state(o_no), "releasing"), H.is_pdu(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_no)), 1n)), 0, 41))))))
    +skey : U32 = Pc.session_timer(st1)
    C.Check.report("no Session Modification Response: the same request three times again, the UE still switching", Bool.and(B.bytes_eq(Pc.first_pfcp(K.Kernel.frames(expire(0n, skey, st1))), mod), Bool.and(B.bytes_eq(Pc.first_pfcp(K.Kernel.frames(expire(2n, skey, st1))), mod), A.phase_is(K.Kernel.state(expire(2n, skey, st1)), "switching"))))
    +o_late : N.Step() = expire(3n, skey, st1)
    C.Check.report("no Session Modification Response after the third retransmission: as refused", Bool.and(H.is_pdu(H.sent_on(2, K.Kernel.frames(o_late)), 2, 25), Bool.and(Pc.sphase_is(K.Kernel.state(o_late), "deleting"), A.phase_is(K.Kernel.state(o_late), "releasing"))))
    +o_guard : N.Step() = H.step(st1, F.TimerFired{1})
    C.Check.report("the switch's guard fires: the UE released by gNB 2", Bool.and(A.phase_is(K.Kernel.state(o_guard), "releasing"), H.is_pdu(H.sent_on(2, K.Kernel.frames(o_guard)), 0, 41)))
