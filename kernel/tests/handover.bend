import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as W
import ../frame.bend as F
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

# Replays the N2 handovers of the handover capture, after its Xn handover
# put the UE on gNB 2 (association 2): one to gNB 1 (association 1)
# cancelled after the Handover Command, then one completed. The target knows
# the UE by the AMF-UE-NGAP-ID the kernel gave it, 1, where Open5GS gave the
# target 2, so the target's captured messages are replayed with 1. Then the
# hand-made cases and the hand-built vectors.

# The target's captured message, naming our AMF-UE-NGAP-ID.
def ours(+pdu: B.Bytes()) -> B.Bytes():
  H.with_ie(10, G.AMF_UE_NGAP_ID.write([1], 0n, []), pdu)

# The same IE value, IE by IE.
def same_ies(ids: List<&2, U32>, +a: B.Bytes(), +b: B.Bytes()) -> Bool:
  match ids:
    case Nil{}:
      True{}
    case +i <> more:
      Bool.and(A.same_ie(i, a, b), same_ies(more, a, b))

def nh_ncc(n: S.Nh) -> U32:
  match n:
    case S.Nh{k_amf, nh, ncc}:
      ncc

def nh_phase(p: S.Phase) -> U32:
  match p:
    case S.Registered{ctx, nh, released}:
      nh_ncc(nh)
    case S.Handover{ctx, nh, source, leg}:
      nh_ncc(nh)
    case _:
      99

def nh_of(m: Maybe<&2, S.Ue>) -> U32:
  match m:
    case Some{u}:
      nh_phase(S.Ue.phase(u))
    case None{}:
      99

def sends(o: N.Step()) -> Nat:
  List.length(&2, F.Action, A.sends(K.Kernel.frames(o)))

def pfcps(o: N.Step()) -> Nat:
  List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o)))

# Nothing changed, and the target is told it named an unknown UE.
def ignored(+st: S.State, +assoc: U32, +o: N.Step()) -> Bool:
  Bool.and(H.unchanged(st, o), Bool.and(Nat.is_eq(sends(o), 1n), H.is_pdu(H.sent_on(assoc, K.Kernel.frames(o)), 0, 9)))

# Nothing changed and nothing sent: no Error Indication.
def accepted(+st: S.State, +o: N.Step()) -> Bool:
  Bool.and(H.unchanged(st, o), Nat.is_eq(sends(o), 0n))

# The RAN-UE-NGAP-ID a Handover Request Acknowledge gives.
def ack_ran(r: Result<&2, &2, B.Err, W.HandoverRequestAcknowledge.View>) -> B.Bytes():
  match r:
    case Done{W.HandoverRequestAcknowledge.View{amf, ran, admitted, failed, back, diag, npn}}:
      ran
    case _:
      []

# How many UE Context Release Commands a step sends on an association.
def releases_on(+assoc: U32, actions: List<&2, F.Action>) -> Nat:
  match actions:
    case Nil{}:
      0n
    case F.NgapSend{+a, stream, len, +bytes} <> more:
      Nat.add(Pc.Bool.to_nat(Bool.and(U32.is_eq(a, assoc), H.is_pdu(bytes, 0, 41))), releases_on(assoc, more))
    case x <> more:
      releases_on(assoc, more)

# The hand-built Handover Request Acknowledge names target RAN-UE-NGAP-ID 3.
def hand_ran() -> B.Bytes():
  [3]

def main() -> IO(Unit):
  do IO<Unit>:
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    +hands : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Hand.data(), "messages"))
    +o_ps : N.Step() = H.step(H.active(msgs), H.on(2, H.hex(msgs, 51n)))
    +st : S.State = H.after(K.Kernel.state(o_ps), Pc.pfcp_event(Pc.with_seq(H.hex(msgs, 53n), Pc.pfcp_seq(Pc.first_pfcp(K.Kernel.frames(o_ps))))))
    C.Check.report("the capture replayed through its Xn handover: the UE registered on gNB 2 with NCC 2", Bool.and(A.phase_is(st, "registered"), Bool.and(U32.is_eq(H.ue_on(st), 2), U32.is_eq(nh_of(A.ue1(st)), 2))))
    +o1 : N.Step() = H.step(st, H.on(2, H.hex(msgs, 59n)))
    +st1 : S.State = K.Kernel.state(o1)
    +req : B.Bytes() = H.sent_on(1, K.Kernel.frames(o1))
    C.Check.report("Handover Required from gNB 2: Handover Request to gNB 1, the UE still owned by gNB 2, in handover", Bool.and(H.is_pdu(req, 0, 13), Bool.and(U32.is_eq(H.ue_on(st1), 2), Bool.and(A.phase_is(st1, "handover"), Nat.is_eq(sends(o1), 1n)))))
    C.Check.report("Handover Request: the captured NH and NCC (NCC 3), and the captured handover type, cause, AMBR, UE security capabilities, sessions with their transfer, Allowed NSSAI, container and GUAMI", same_ies([93, 29, 15, 110, 119, 73, 0, 101, 28], req, H.hex(msgs, 60n)))
    C.Check.report("Handover Request: the preparation guard started, no PFCP message", Bool.and(U32.is_eq(A.first_timer(K.Kernel.frames(o1)), 1), Nat.is_eq(pfcps(o1), 0n)))
    +o2 : N.Step() = H.step(st1, H.on(1, ours(H.hex(msgs, 61n))))
    +st2 : S.State = K.Kernel.state(o2)
    C.Check.report("Handover Request Acknowledge from gNB 1: the captured Handover Command to gNB 2 byte for byte, the completion guard started", Bool.and(B.bytes_eq(H.sent_on(2, K.Kernel.frames(o2)), H.hex(msgs, 62n)), Bool.and(U32.is_eq(A.first_timer(K.Kernel.frames(o2)), 1), Bool.and(U32.is_eq(H.ue_on(st2), 2), Nat.is_eq(pfcps(o2), 0n)))))
    +o3 : N.Step() = H.step(st2, H.on(2, H.hex(msgs, 63n)))
    +st3 : S.State = K.Kernel.state(o3)
    +rel : B.Bytes() = H.sent_on(1, K.Kernel.frames(o3))
    C.Check.report("Handover Cancel from gNB 2: the captured Handover Cancel Acknowledge byte for byte, gNB 1 told to release the UE, the UE registered on gNB 2 keeping NCC 3", Bool.and(B.bytes_eq(H.sent_on(2, K.Kernel.frames(o3)), H.hex(msgs, 66n)), Bool.and(H.is_pdu(rel, 0, 41), Bool.and(A.phase_is(st3, "registered"), Bool.and(U32.is_eq(H.ue_on(st3), 2), U32.is_eq(nh_of(A.ue1(st3)), 3))))))
    C.Check.report("Handover Cancel: the guard stopped, no PFCP message", Bool.and(Nat.is_eq(A.timer_cancels(K.Kernel.frames(o3)), 1n), Nat.is_eq(pfcps(o3), 0n)))
    C.Check.report("gNB 1's UE Context Release Complete after the cancel: accepted, nothing sent, nothing changed", accepted(st3, H.step(st3, H.on(1, ours(H.hex(msgs, 65n))))))
    C.Check.report("a UE Context Release Complete from gNB 1 under another RAN-UE-NGAP-ID after the cancel: Error Indication, nothing changed", ignored(st3, 1, H.step(st3, H.on(1, H.with_ie(85, G.RAN_UE_NGAP_ID.write([9], 0n, []), ours(H.hex(msgs, 65n)))))))
    C.Check.report("a UE Context Release Complete from a third gNB after the cancel: Error Indication, nothing changed", ignored(st3, 3, H.step(st3, H.on(3, ours(H.hex(msgs, 65n))))))
    C.Check.report("an acknowledgement after the cancel: ignored, no PFCP message", ignored(st3, 1, H.step(st3, H.on(1, ours(H.hex(msgs, 61n))))))
    C.Check.report("a Handover Notify after the cancel: ignored", ignored(st3, 1, H.step(st3, H.on(1, ours(H.hex(msgs, 77n))))))
    +o4 : N.Step() = H.step(st3, H.on(2, H.hex(msgs, 73n)))
    +st4 : S.State = K.Kernel.state(o4)
    C.Check.report("the second Handover Required: the captured NH and NCC (NCC 4) and the rest of the captured Handover Request", same_ies([93, 29, 15, 110, 119, 73, 0, 101, 28], H.sent_on(1, K.Kernel.frames(o4)), H.hex(msgs, 74n)))
    +o5 : N.Step() = H.step(st4, H.on(1, ours(H.hex(msgs, 75n))))
    +st5 : S.State = K.Kernel.state(o5)
    C.Check.report("its acknowledgement: the captured Handover Command byte for byte", B.bytes_eq(H.sent_on(2, K.Kernel.frames(o5)), H.hex(msgs, 76n)))
    C.Check.report("a Handover Notify from gNB 2, the source: ignored", ignored(st5, 2, H.step(st5, H.on(2, ours(H.hex(msgs, 77n))))))
    +o6 : N.Step() = H.step(st5, H.on(1, ours(H.hex(msgs, 77n))))
    +st6 : S.State = K.Kernel.state(o6)
    +mod : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(o6))
    C.Check.report("Handover Notify from gNB 1: the UE owned by gNB 1 under the RAN-UE-NGAP-ID it acknowledged with, registered", Bool.and(U32.is_eq(H.ue_on(st6), 1), Bool.and(H.ran_is(st6, ack_ran(W.HandoverRequestAcknowledge.view(A.ies_of(Fr.Pdu.read(H.hex(msgs, 75n)))))), A.phase_is(st6, "registered"))))
    C.Check.report("Handover Notify: one PFCP Session Modification repointing the downlink FAR to gNB 1's captured tunnel", Bool.and(Nat.is_eq(pfcps(o6), 1n), Bool.and(U32.is_eq(Pc.pfcp_kind(mod), 52), Bool.and(B.bytes_eq(Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(mod)))), Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(H.hex(msgs, 78n)))))), Pc.sphase_is(st6, "repointing")))))
    C.Check.report("Handover Notify: the captured UE Context Release Command to gNB 2 byte for byte, the guard stopped", Bool.and(B.bytes_eq(H.sent_on(2, K.Kernel.frames(o6)), H.hex(msgs, 80n)), Bool.and(Nat.is_eq(sends(o6), 1n), Pc.cancels(K.Kernel.frames(o6), 1))))
    +o_hn2 : N.Step() = H.step(H.with_session(st5, 2), H.on(1, ours(H.hex(msgs, 77n))))
    +dl2 : B.Bytes() = H.sent_on(1, K.Kernel.frames(o_hn2))
    C.Check.report("Handover Notify with a second session the target was not asked for: deleted at the UPF, PDU Session Release Command #26 for it to the UE in DL NAS Transport through gNB 1, under the RAN-UE-NGAP-ID it acknowledged with", Bool.and(Nat.is_eq(pfcps(o_hn2), 2n), Bool.and(Nat.is_eq(sends(o_hn2), 2n), Bool.and(H.is_pdu(dl2, 0, 4), Bool.and(A.same_ie(85, dl2, H.hex(msgs, 75n)), B.bytes_eq(H.dl_plain(dl2), H.release_plain(2)))))))
    +st7 : S.State = H.after(st6, Pc.pfcp_event(Pc.with_seq(H.hex(msgs, 79n), Pc.pfcp_seq(mod))))
    C.Check.report("Session Modification Response: the session active, nothing sent", Bool.and(Pc.sphase_is(st7, "active"), A.phase_is(st7, "registered")))
    C.Check.report("gNB 2's UE Context Release Complete after Handover Notify: accepted, nothing sent, nothing changed", accepted(st7, H.step(st7, H.on(2, H.hex(msgs, 81n)))))
    C.Check.report("an acknowledgement from a third gNB: ignored", ignored(st1, 3, H.step(st1, H.on(3, ours(H.hex(msgs, 61n))))))
    C.Check.report("an acknowledgement when the target already acknowledged: ignored", ignored(st2, 1, H.step(st2, H.on(1, ours(H.hex(msgs, 61n))))))
    C.Check.report("Handover Notify before the acknowledgement: ignored", ignored(st1, 1, H.step(st1, H.on(1, ours(H.hex(msgs, 77n))))))
    C.Check.report("Handover Notify under another RAN-UE-NGAP-ID: ignored", ignored(st5, 1, H.step(st5, H.on(1, H.with_ie(85, G.RAN_UE_NGAP_ID.write([9], 0n, []), ours(H.hex(msgs, 77n)))))))
    C.Check.report("Handover Required from gNB 1, not the owner: Error Indication, nothing changed", Bool.and(H.unchanged(st, H.step(st, H.on(1, H.hex(msgs, 59n)))), H.is_pdu(H.sent_on(1, K.Kernel.frames(H.step(st, H.on(1, H.hex(msgs, 59n))))), 0, 9)))
    C.Check.report("Handover Cancel from gNB 1, not the owner: nothing changed", H.unchanged(st2, H.step(st2, H.on(1, H.hex(msgs, 63n)))))
    +o_far : N.Step() = H.step(K.Kernel.state(H.step(st, F.NgapAssocDown{1})), H.on(2, H.hex(msgs, 59n)))
    C.Check.report("Handover Required for a gNB not set up: Handover Preparation Failure, nothing changed", Bool.and(H.is_pdu(H.sent_on(2, K.Kernel.frames(o_far)), 2, 12), Bool.and(A.phase_is(K.Kernel.state(o_far), "registered"), Nat.is_eq(sends(o_far), 1n))))
    +o_prep : N.Step() = H.step(st1, F.TimerFired{1})
    C.Check.report("the preparation guard fires: Handover Preparation Failure to gNB 2, gNB 1 told to release, the UE registered on gNB 2", Bool.and(H.is_pdu(H.sent_on(2, K.Kernel.frames(o_prep)), 2, 12), Bool.and(H.is_pdu(H.sent_on(1, K.Kernel.frames(o_prep)), 0, 41), Bool.and(A.phase_is(K.Kernel.state(o_prep), "registered"), U32.is_eq(H.ue_on(K.Kernel.state(o_prep)), 2)))))
    C.Check.report("an acknowledgement after the preparation guard fired: ignored", ignored(K.Kernel.state(o_prep), 1, H.step(K.Kernel.state(o_prep), H.on(1, ours(H.hex(msgs, 61n))))))
    C.Check.report("gNB 1's UE Context Release Complete after the preparation guard fired, under the RAN-UE-NGAP-ID it never gave: accepted, nothing sent", accepted(K.Kernel.state(o_prep), H.step(K.Kernel.state(o_prep), H.on(1, ours(H.hex(msgs, 65n))))))
    +o_done : N.Step() = H.step(st2, F.TimerFired{1})
    C.Check.report("the completion guard fires: gNB 1 told to release, the UE registered on gNB 2", Bool.and(H.is_pdu(H.sent_on(1, K.Kernel.frames(o_done)), 0, 41), Bool.and(Nat.is_eq(sends(o_done), 1n), Bool.and(A.phase_is(K.Kernel.state(o_done), "registered"), U32.is_eq(H.ue_on(K.Kernel.state(o_done)), 2)))))
    C.Check.report("gNB 1's UE Context Release Complete after the completion guard fired: accepted, nothing sent", accepted(K.Kernel.state(o_done), H.step(K.Kernel.state(o_done), H.on(1, ours(H.hex(msgs, 65n))))))
    +o_early : N.Step() = H.step(st1, H.on(2, H.hex(msgs, 63n)))
    C.Check.report("Handover Cancel before the Handover Command: acknowledged, gNB 1 told to release by AMF-UE-NGAP-ID, the UE registered", Bool.and(B.bytes_eq(H.sent_on(2, K.Kernel.frames(o_early)), H.hex(msgs, 66n)), Bool.and(H.is_pdu(H.sent_on(1, K.Kernel.frames(o_early)), 0, 41), A.phase_is(K.Kernel.state(o_early), "registered"))))
    +st_early : S.State = K.Kernel.state(o_early)
    C.Check.report("an acknowledgement crossing a cancel before the Handover Command: ignored", ignored(st_early, 1, H.step(st_early, H.on(1, ours(H.hex(msgs, 61n))))))
    +o_again : N.Step() = H.step(st_early, H.on(2, H.hex(msgs, 73n)))
    C.Check.report("a new Handover Required to the target that never answered the cancelled one: Handover Preparation Failure, nothing changed, no Handover Request", Bool.and(H.is_pdu(H.sent_on(2, K.Kernel.frames(o_again)), 2, 12), Bool.and(H.unchanged(st_early, o_again), Nat.is_eq(sends(o_again), 1n))))
    +o_fail : N.Step() = H.step(st1, H.on(1, H.hand("HandoverFailure", hands)))
    C.Check.report("the hand-built Handover Failure: the hand-built Handover Preparation Failure to gNB 2 byte for byte, the UE registered, the guard stopped", Bool.and(B.bytes_eq(H.sent_on(2, K.Kernel.frames(o_fail)), H.hand("HandoverPreparationFailure", hands)), Bool.and(A.phase_is(K.Kernel.state(o_fail), "registered"), Bool.and(Nat.is_eq(sends(o_fail), 1n), Nat.is_eq(A.timer_cancels(K.Kernel.frames(o_fail)), 1n)))))
    C.Check.report("the hand-built Handover Failure from gNB 2, the source: ignored", ignored(st1, 2, H.step(st1, H.on(2, H.hand("HandoverFailure", hands)))))
    +o_hack : N.Step() = H.step(st1, H.on(1, H.hand("HandoverRequestAcknowledge", hands)))
    +st_hack : S.State = K.Kernel.state(o_hack)
    C.Check.report("the hand-built acknowledgement, one session admitted and one failed: Handover Command naming the admitted session", Bool.and(H.is_pdu(H.sent_on(2, K.Kernel.frames(o_hack)), 1, 12), A.same_ie(59, H.sent_on(2, K.Kernel.frames(o_hack)), H.hex(msgs, 62n))))
    +o_up : N.Step() = H.step(st_hack, H.on(2, H.hand("UplinkRANStatusTransfer", hands)))
    C.Check.report("the hand-built Uplink RAN Status Transfer from gNB 2: the hand-built Downlink RAN Status Transfer to gNB 1 byte for byte, nothing changed", Bool.and(B.bytes_eq(H.sent_on(1, K.Kernel.frames(o_up)), H.hand("DownlinkRANStatusTransfer", hands)), H.unchanged(st_hack, o_up)))
    C.Check.report("the hand-built Uplink RAN Status Transfer before the acknowledgement: nothing sent, nothing changed", Bool.and(Nat.is_eq(sends(H.step(st1, H.on(2, H.hand("UplinkRANStatusTransfer", hands)))), 0n), H.unchanged(st1, H.step(st1, H.on(2, H.hand("UplinkRANStatusTransfer", hands))))))
    +o_hn : N.Step() = H.step(st_hack, H.on(1, H.with_ie(85, G.RAN_UE_NGAP_ID.write(hand_ran(), 0n, []), ours(H.hex(msgs, 77n)))))
    C.Check.report("Handover Notify after the hand-built acknowledgement: the UE on gNB 1, its session repointed to the admitted tunnel", Bool.and(U32.is_eq(H.ue_on(K.Kernel.state(o_hn)), 1), B.bytes_eq(Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(Pc.first_pfcp(K.Kernel.frames(o_hn)))))), [1, 0, 0, 0, 0, 3, 10, 33, 0, 30])))
    C.Check.report("a Path Switch Request from gNB 1 for the UE in handover: Path Switch Request Failure, nothing changed", Bool.and(H.is_pdu(H.sent_on(1, K.Kernel.frames(H.step(st1, H.on(1, H.hex(msgs, 51n))))), 2, 25), Bool.and(H.unchanged(st1, H.step(st1, H.on(1, H.hex(msgs, 51n)))), A.phase_is(K.Kernel.state(H.step(st1, H.on(1, H.hex(msgs, 51n)))), "handover"))))
    +ran2 : B.Bytes() = H.ran_of(A.ue1(st))
    +nas : B.Bytes() = H.with_ie(85, G.RAN_UE_NGAP_ID.write(ran2, 0n, []), H.hex(msgs, 33n))
    C.Check.report("an Uplink NAS Transport from the owner during the handover: ignored, nothing sent", Bool.and(H.unchanged(st1, H.step(st1, H.on(2, nas))), Nat.is_eq(sends(H.step(st1, H.on(2, nas))), 0n)))
    +o_tdown : N.Step() = H.step(st1, F.NgapAssocDown{1})
    +st_tdown : S.State = K.Kernel.state(o_tdown)
    C.Check.report("the target's association goes down before its acknowledgement: Handover Preparation Failure to gNB 2, the UE registered there, the guard stopped", Bool.and(H.is_pdu(H.sent_on(2, K.Kernel.frames(o_tdown)), 2, 12), Bool.and(A.phase_is(st_tdown, "registered"), Bool.and(U32.is_eq(H.ue_on(st_tdown), 2), Pc.cancels(K.Kernel.frames(o_tdown), 1)))))
    +st_back : S.State = H.after(H.after(st_tdown, F.NgapAssocUp{1}), H.on(1, H.hex(msgs, 8n)))
    C.Check.report("a new association under the target's id afterwards: its acknowledgement ignored", ignored(st_back, 1, H.step(st_back, H.on(1, ours(H.hex(msgs, 61n))))))
    +o_tdown2 : N.Step() = H.step(st2, F.NgapAssocDown{1})
    C.Check.report("the target's association goes down after its acknowledgement: the UE registered on gNB 2, the guard stopped", Bool.and(A.phase_is(K.Kernel.state(o_tdown2), "registered"), Bool.and(U32.is_eq(H.ue_on(K.Kernel.state(o_tdown2)), 2), Pc.cancels(K.Kernel.frames(o_tdown2), 1))))
    +o_sdown : N.Step() = H.step(st2, F.NgapAssocDown{2})
    C.Check.report("the source's association goes down during the handover: the UE gone, gNB 1 told to release it", Bool.and(Nat.is_eq(A.ue_count(K.Kernel.state(o_sdown)), 0n), Nat.is_eq(releases_on(1, K.Kernel.frames(o_sdown)), 1n)))
    +o_tsetup : N.Step() = H.step(st1, H.on(1, H.hex(msgs, 8n)))
    +st_tsetup : S.State = K.Kernel.state(o_tsetup)
    C.Check.report("NG Setup from the target before its acknowledgement, as its association going down: Handover Preparation Failure to gNB 2, the UE registered there, the guard stopped; then NG Setup Response to gNB 1", Bool.and(H.is_pdu(H.sent_on(2, K.Kernel.frames(o_tsetup)), 2, 12), Bool.and(A.phase_is(st_tsetup, "registered"), Bool.and(U32.is_eq(H.ue_on(st_tsetup), 2), Bool.and(Pc.cancels(K.Kernel.frames(o_tsetup), 1), H.is_pdu(H.sent_on(1, K.Kernel.frames(o_tsetup)), 1, 21))))))
    C.Check.report("after NG Setup from the target: its acknowledgement ignored", ignored(st_tsetup, 1, H.step(st_tsetup, H.on(1, ours(H.hex(msgs, 61n))))))
    +o_tsetup2 : N.Step() = H.step(st2, H.on(1, H.hex(msgs, 8n)))
    C.Check.report("NG Setup from the target after its acknowledgement, as its association going down: the UE registered on gNB 2, the guard stopped, NG Setup Response to gNB 1", Bool.and(A.phase_is(K.Kernel.state(o_tsetup2), "registered"), Bool.and(U32.is_eq(H.ue_on(K.Kernel.state(o_tsetup2)), 2), Bool.and(Pc.cancels(K.Kernel.frames(o_tsetup2), 1), Bool.and(H.is_pdu(H.sent_on(1, K.Kernel.frames(o_tsetup2)), 1, 21), Nat.is_eq(sends(o_tsetup2), 1n))))))
    +o_ssetup : N.Step() = H.step(st2, H.on(2, H.hex(msgs, 10n)))
    C.Check.report("NG Setup from the source during the handover, as its association going down: the UE gone, gNB 1 told to release it", Bool.and(Nat.is_eq(A.ue_count(K.Kernel.state(o_ssetup)), 0n), Bool.and(Nat.is_eq(releases_on(1, K.Kernel.frames(o_ssetup)), 1n), H.is_pdu(H.sent_on(2, K.Kernel.frames(o_ssetup)), 1, 21))))
    +o_rel : N.Step() = H.step(st2, H.on(2, A.release_request(ran2)))
    C.Check.report("the owner releases the UE during the handover: Release Command to gNB 2 and to gNB 1, the UE releasing", Bool.and(Nat.is_eq(releases_on(2, K.Kernel.frames(o_rel)), 1n), Bool.and(Nat.is_eq(releases_on(1, K.Kernel.frames(o_rel)), 1n), A.phase_is(K.Kernel.state(o_rel), "releasing"))))
    +o_rel1 : N.Step() = H.step(st1, H.on(2, A.release_request(ran2)))
    C.Check.report("the owner releases the UE before the acknowledgement: gNB 1 told to release by AMF-UE-NGAP-ID", Bool.and(Nat.is_eq(releases_on(1, K.Kernel.frames(o_rel1)), 1n), A.phase_is(K.Kernel.state(o_rel1), "releasing")))
