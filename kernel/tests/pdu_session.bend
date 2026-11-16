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
import ../smf/n4.bend as Up
import ../smf/gsm.bend as Gs
import ../amf/ngap.bend as N
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture
import ./lib/amf.bend as A
import ./lib/pfcp.bend as Pc

# Replays the captured PDU session establishment after the captured
# registration: the UL NAS Transport opens a session whose PFCP Session
# Establishment Request names the captured F-SEID, TEID, UE address and bit
# rates; the UPF's captured answer brings the PDU Session Resource Setup Request
# with the captured transfer; the gNB's captured answer brings the Session
# Modification with the captured tunnel; the UPF's answer makes the session
# active. Then the association, the failure paths and release.

# Entropy with the captured RAND, the captured TEID at 20 and CP SEID at 24.
def entropy() -> B.Bytes():
  [45, 202, 228, 29, 52, 210, 168, 148, 210, 151, 160, 24, 229, 85, 66, 153, 0, 0, 0, 0, 0, 0, 199, 196, 0, 0, 1, 210, 0, 0, 0, 0]

def step(st: S.State, ev: F.Evt) -> N.Step():
  K.Kernel.step(st, ev, entropy())

def count_kind(+kind: U32, ies: List<&2, T.Tlv>) -> Nat:
  match ies:
    case Nil{}:
      0n
    case +t <> more:
      Nat.add(Pc.Bool.to_nat(U32.is_eq(T.Tlv.kind(t), kind)), count_kind(kind, more))

# The first item of a PDU Session Resource Setup Request: its transfer and NAS-PDU.
def item_transfer(items: G.PDUSessionResourceSetupListSUReq()) -> B.Bytes():
  match items:
    case G.PDUSessionResourceSetupItemSUReq{psi, nas, snssai, transfer, x} <> more:
      transfer
    case _:
      []

def item_nas(items: G.PDUSessionResourceSetupListSUReq()) -> B.Bytes():
  match items:
    case G.PDUSessionResourceSetupItemSUReq{psi, Some{nas}, snssai, transfer, x} <> more:
      nas
    case _:
      []

def items_of(r: Result<&2, &2, B.Err, W.PDUSessionResourceSetupRequest.View>) -> G.PDUSessionResourceSetupListSUReq():
  match r:
    case Done{W.PDUSessionResourceSetupRequest.View{amf, ran, nas, items, ambr}}:
      items
    case _:
      []

def setup_items(bytes: B.Bytes()) -> G.PDUSessionResourceSetupListSUReq():
  items_of(W.PDUSessionResourceSetupRequest.view(A.ies_of(Fr.Pdu.read(bytes))))

# A PDU Session Resource Setup Response from the gNB that failed the session.
def setup_failure(ran: B.Bytes()) -> B.Bytes():
  N.Ngap.pdu(Fr.Pdu.successful(), 29, Fr.Criticality.reject(), [N.Ngap.ie(10, Fr.Criticality.ignore(), G.AMF_UE_NGAP_ID.write([1], 0n, [])), N.Ngap.ie(85, Fr.Criticality.ignore(), G.RAN_UE_NGAP_ID.write(ran, 0n, [])), N.Ngap.ie(58, Fr.Criticality.ignore(), G.PDUSessionResourceFailedToSetupListSURes.write([G.PDUSessionResourceFailedToSetupItemSURes{1, Ap.pack(G.PDUSessionResourceSetupUnsuccessfulTransfer.write(G.PDUSessionResourceSetupUnsuccessfulTransfer{N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified()), None{}, None{}}, 0n, [])), None{}}], 0n, []))])

# Warning log lines among the actions.
def warns(actions: List<&2, F.Action>) -> Nat:
  match actions:
    case Nil{}:
      0n
    case F.Log{F.Warn{}, len, text} <> more:
      1n+warns(more)
    case a <> more:
      warns(more)

def oks_of(r: Result<&2, &2, B.Err, W.PDUSessionResourceSetupResponse.View>) -> G.PDUSessionResourceSetupListSURes():
  match r:
    case Done{W.PDUSessionResourceSetupResponse.View{amf, ran, Some{oks}, fails, diag, uli}}:
      oks
    case _:
      []

# A PDU Session Resource Setup Response naming the session set up twice: first
# with a transfer that does not decode, then with the captured one.
def setup_twice(ran: B.Bytes(), oks: G.PDUSessionResourceSetupListSURes()) -> B.Bytes():
  match oks:
    case G.PDUSessionResourceSetupItemSURes{+psi, transfer, x} <> more:
      N.Ngap.pdu(Fr.Pdu.successful(), 29, Fr.Criticality.reject(), [N.Ngap.ie(10, Fr.Criticality.ignore(), G.AMF_UE_NGAP_ID.write([1], 0n, [])), N.Ngap.ie(85, Fr.Criticality.ignore(), G.RAN_UE_NGAP_ID.write(ran, 0n, [])), N.Ngap.ie(75, Fr.Criticality.ignore(), G.PDUSessionResourceSetupListSURes.write([G.PDUSessionResourceSetupItemSURes{psi, [], None{}}, G.PDUSessionResourceSetupItemSURes{psi, transfer, None{}}], 0n, []))])
    case _:
      []

# UL NAS Transport with an N1 SM message, the PDU session identity, request type initial, and more IEs.
def ul_transport(+sm: B.Bytes(), more: B.Bytes()) -> B.Bytes():
  List.append(&2, U32, [126, 0, 103, 1, 0, U32.from_nat(List.length(&2, U32, sm))], List.append(&2, U32, sm, List.append(&2, U32, [18, 1, 129], more)))

# The plaintext inside a protected DL NAS Transport (NEA0).
def inner(nas: B.Bytes()) -> B.Bytes():
  List.drop(&2, U32, nas, 7n)

# The first session's guard, 466, fired n + 1 times in a row.
def expire(n: Nat, st: S.State) -> N.Step():
  match n:
    case 0n:
      step(st, F.TimerFired{466})
    case 1n+p:
      expire(p, K.Kernel.state(step(st, F.TimerFired{466})))

# A session request sent again unchanged, its guard started again.
def again(+o: N.Step(), +req: B.Bytes()) -> Bool:
  Bool.and(B.bytes_eq(Pc.first_pfcp(K.Kernel.frames(o)), req), U32.is_eq(Pc.first_ms(K.Kernel.frames(o)), 3000))

# Whatever forgets a session stops its guard, so no stale timer meets a later session under the same SEID.
def stale_guards(+msgs: List<&2, V.Vec>) -> IO(Unit):
  do IO<Unit>:
    +ran : B.Bytes() = A.ran_of(W.InitialUEMessage.view(A.ies_of(Fr.Pdu.read(A.hex_of(A.entry(14n, msgs), "hex")))))
    +st1 : S.State = K.Kernel.state(step(A.registered(msgs), A.data(1, A.hex_of(A.entry(30n, msgs), "hex"))))
    +req : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(step(A.registered(msgs), A.data(1, A.hex_of(A.entry(30n, msgs), "hex")))))
    +st2 : S.State = K.Kernel.state(step(st1, Pc.pfcp_event(Pc.with_seq(A.hex_of(A.entry(36n, msgs), "hex"), Pc.pfcp_seq(req)))))
    +refused : N.Step() = step(st1, Pc.pfcp_event(Pc.with_cause(Pc.with_seq(A.hex_of(A.entry(36n, msgs), "hex"), Pc.pfcp_seq(req)), 73)))
    +cpl : B.Bytes() = N.Ngap.pdu(Fr.Pdu.successful(), 41, Fr.Criticality.reject(), [N.Ngap.ie(10, Fr.Criticality.ignore(), G.AMF_UE_NGAP_ID.write([1], 0n, [])), N.Ngap.ie(85, Fr.Criticality.ignore(), G.RAN_UE_NGAP_ID.write(ran, 0n, []))])
    +o_gone : N.Step() = step(K.Kernel.state(step(st1, A.data(1, A.release_request(ran)))), A.data(1, cpl))
    C.Check.report("the UE released while its session is being created: the session's guard, 466, is stopped", Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_gone)), 0n), Pc.cancels(K.Kernel.frames(o_gone), 466)))
    C.Check.report("the association down while a session is being set up: its guard is not stopped but started again for the Session Deletion Request", Bool.and(Bool.not(Pc.cancels(K.Kernel.frames(step(st2, F.NgapAssocDown{1})), 466)), U32.is_eq(A.first_timer(K.Kernel.frames(step(st2, F.NgapAssocDown{1}))), 466)))
    C.Check.report("The UPF refuses the Session Establishment: the session's guard is stopped once", Nat.is_eq(Pc.cancel_count(K.Kernel.frames(refused), 466), 1n))

# TS 29.244 §6.4: a session the UPF refused to modify is deleted there. Until
# the UPF answers, its row keeps its address, TEID and SEID, so a new session
# of the UE under the same PDU session identity takes others, and its Session
# Deletion Request goes again unchanged, up to N1 times; the Session Deletion
# Response, or the last retry, removes the row and stops its guard.
def deleting(+ran: B.Bytes(), +uli: Maybe<&2, G.UserLocationInformation>, +st3: S.State, +req: B.Bytes(), +mod: B.Bytes()) -> IO(Unit):
  do IO<Unit>:
    +o_del : N.Step() = step(st3, Pc.pfcp_event(Pf.Msg.write(Pf.Msg.make(53, Some{[0, 0, 0, 0, 0, 0, 0, 1]}, Pc.pfcp_seq(mod), [T.Tlv.make(19, [73])]), [])))
    +deletion : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(o_del))
    +st_d : S.State = K.Kernel.state(o_del)
    C.Check.report("the UPF refuses the Session Modification: the session is being deleted, its row kept, its guard 466 started again for T1", Bool.and(Pc.sphase_at(st_d, 466, "deleting"), Bool.and(U32.is_eq(Pc.pfcp_kind(deletion), 54), Bool.and(U32.is_eq(A.first_timer(K.Kernel.frames(o_del)), 466), Bool.and(U32.is_eq(Pc.first_ms(K.Kernel.frames(o_del)), 3000), Nat.is_eq(Pc.cancel_count(K.Kernel.frames(o_del), 466), 0n))))))
    +o_new : N.Step() = step(st_d, A.data(1, A.uplink(ran, uli, A.ue_protect(3, ul_transport([46, 1, 3, 193, 255, 255], [])))))
    +new_ies : List<&2, T.Tlv> = Pc.pfcp_ies(Pc.first_pfcp(K.Kernel.frames(o_new)))
    +old_ies : List<&2, T.Tlv> = Pc.pfcp_ies(req)
    +st_n : S.State = K.Kernel.state(o_new)
    C.Check.report("a new session under the same PDU session identity while the old one is being deleted: both rows kept", Bool.and(Nat.is_eq(Pc.session_count(st_n), 2n), Bool.and(Pc.sphase_at(st_n, 466, "deleting"), Pc.sphase_is(st_n, "creating"))))
    C.Check.report("the new session takes another UE address, 10.45.0.3, another TEID and another SEID", Bool.and(B.bytes_eq(Pc.body(93, Pc.inside(2, Pc.inside(1, List.drop(&2, T.Tlv, new_ies, 3n)))), [6, 10, 45, 0, 3]), Bool.and(Bool.not(B.bytes_eq(Pc.body(21, Pc.inside(2, Pc.inside(1, new_ies))), Pc.body(21, Pc.inside(2, Pc.inside(1, old_ies))))), Bool.not(B.bytes_eq(Pc.body(57, new_ies), Pc.body(57, old_ies))))))
    +o_r1 : N.Step() = step(st_n, F.TimerFired{466})
    C.Check.report("no Session Deletion Response: the request goes again unchanged, its sequence number included, the row still being deleted", Bool.and(again(o_r1, deletion), Bool.and(Pc.sphase_at(K.Kernel.state(o_r1), 466, "deleting"), Nat.is_eq(Pc.session_count(K.Kernel.state(o_r1)), 2n))))
    C.Check.report("three retransmissions, each the request unchanged", Bool.and(again(expire(0n, st_d), deletion), Bool.and(again(expire(1n, st_d), deletion), again(expire(2n, st_d), deletion))))
    +answer : B.Bytes() = Up.N4.msg(Pf.Type.session_deletion_response(), Some{[0, 0, 0, 0, 0, 0, 0, 0]}, Pc.pfcp_seq(deletion), [Up.N4.byte(Pf.Ie.cause(), 1)])
    +o_ok : N.Step() = step(K.Kernel.state(o_r1), Pc.pfcp_event(answer))
    C.Check.report("the Session Deletion Response: the row gone, its guard stopped, the new session kept", Bool.and(Pc.sphase_at(K.Kernel.state(o_ok), 466, "none"), Bool.and(Pc.cancels(K.Kernel.frames(o_ok), 466), Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_ok)), 1n), Nat.is_eq(List.length(&2, F.Action, K.Kernel.frames(step(K.Kernel.state(o_ok), F.TimerFired{466}))), 0n)))))
    C.Check.report("a Session Deletion Response accepting the deletion logs no warning", Nat.is_eq(warns(K.Kernel.frames(o_ok)), 0n))
    +o_dup : N.Step() = step(K.Kernel.state(o_ok), Pc.pfcp_event(answer))
    C.Check.report("the same Session Deletion Response again, its row gone: the sessions as they were, nothing sent, no guard stopped, one warning", Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_dup)), 1n), Bool.and(Pc.sphase_is(K.Kernel.state(o_dup), "creating"), Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o_dup))), 0n), Bool.and(Nat.is_eq(A.timer_cancels(K.Kernel.frames(o_dup)), 0n), Nat.is_eq(warns(K.Kernel.frames(o_dup)), 1n))))))
    +refusal : B.Bytes() = Up.N4.msg(Pf.Type.session_deletion_response(), Some{[0, 0, 0, 0, 0, 0, 0, 0]}, Pc.pfcp_seq(deletion), [Up.N4.byte(Pf.Ie.cause(), 65)])
    +o_err : N.Step() = step(K.Kernel.state(o_r1), Pc.pfcp_event(refusal))
    C.Check.report("a Session Deletion Response with cause 65: the row gone all the same, its guard stopped, one warning", Bool.and(Pc.sphase_at(K.Kernel.state(o_err), 466, "none"), Bool.and(Pc.cancels(K.Kernel.frames(o_err), 466), Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_err)), 1n), Nat.is_eq(warns(K.Kernel.frames(o_err)), 1n)))))
    +new_seq : U32 = Pc.pfcp_seq(Pc.first_pfcp(K.Kernel.frames(o_new)))
    +o_other : N.Step() = step(st_n, Pc.pfcp_event(Up.N4.msg(Pf.Type.session_deletion_response(), Some{[0, 0, 0, 0, 0, 0, 0, 0]}, new_seq, [Up.N4.byte(Pf.Ie.cause(), 1)])))
    C.Check.report("a Session Deletion Response with the sequence number of a session being created: both rows as they were, nothing sent, no guard stopped, one warning", Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_other)), 2n), Bool.and(Pc.sphase_at(K.Kernel.state(o_other), 466, "deleting"), Bool.and(Pc.sphase_is(K.Kernel.state(o_other), "creating"), Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o_other))), 0n), Bool.and(Nat.is_eq(A.timer_cancels(K.Kernel.frames(o_other)), 0n), Nat.is_eq(warns(K.Kernel.frames(o_other)), 1n)))))))
    +o_last : N.Step() = expire(3n, st_d)
    C.Check.report("no Session Deletion Response after the third retransmission: the row gone, its guard stopped, nothing sent", Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_last)), 0n), Bool.and(Pc.cancels(K.Kernel.frames(o_last), 466), Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o_last))), 0n), Nat.is_eq(List.length(&2, F.Action, K.Kernel.frames(step(K.Kernel.state(o_last), F.TimerFired{466}))), 0n)))))

# The PFCP association: its setup retransmitted and paused, its heartbeats.
def association(+msgs: List<&2, V.Vec>, +st_reg: S.State, +o_tick: N.Step()) -> IO(Unit):
  do IO<Unit>:
    +o_cfg : N.Step() = step(S.State.initial(), F.Evt.config_make(A.config([])))
    +req0 : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(o_cfg))
    +seq0 : U32 = Pc.pfcp_seq(req0)
    +o_t1 : N.Step() = step(K.Kernel.state(o_cfg), F.TimerFired{0})
    +o_t2 : N.Step() = step(K.Kernel.state(o_t1), F.TimerFired{0})
    +o_t3 : N.Step() = step(K.Kernel.state(o_t2), F.TimerFired{0})
    +o_t4 : N.Step() = step(K.Kernel.state(o_t3), F.TimerFired{0})
    C.Check.report("no Association Setup Response: the first request sent again unchanged three times", Bool.and(again(o_t1, req0), Bool.and(again(o_t2, req0), again(o_t3, req0))))
    C.Check.report("no Association Setup Response after the third retransmission: a pause", Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o_t4))), 0n), Nat.is_eq(A.timer_starts(K.Kernel.frames(o_t4)), 1n)))
    +st_t4 : S.State = K.Kernel.state(o_t4)
    C.Check.report("the pause over: the association is asked for again", U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(step(st_t4, F.TimerFired{0})))), 5))
    +o_late_answer : N.Step() = step(st_t4, Pc.pfcp_event(Pc.with_seq(A.hex_of(A.entry(1n, msgs), "hex"), seq0)))
    C.Check.report("an Association Setup Response during the pause: ignored", Bool.not(Up.N4.up(K.Kernel.state(o_late_answer))))
    +req_hb : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(o_tick))
    +hb : U32 = Pc.pfcp_seq(req_hb)
    +st_b0 : S.State = K.Kernel.state(o_tick)
    +o_b1 : N.Step() = step(st_b0, F.TimerFired{0})
    +o_b2 : N.Step() = step(K.Kernel.state(o_b1), F.TimerFired{0})
    +o_b3 : N.Step() = step(K.Kernel.state(o_b2), F.TimerFired{0})
    C.Check.report("no Heartbeat Response: the request sent again unchanged three times, the link still up", Bool.and(again(o_b1, req_hb), Bool.and(again(o_b2, req_hb), Bool.and(again(o_b3, req_hb), Up.N4.up(K.Kernel.state(o_b3))))))
    +o_lost : N.Step() = step(K.Kernel.state(o_b3), F.TimerFired{0})
    +st_lost : S.State = K.Kernel.state(o_lost)
    C.Check.report("no Heartbeat Response after the third retransmission: the link is down and the association asked for again", Bool.and(Bool.not(Up.N4.up(st_lost)), U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_lost))), 5)))
    +o_wrong : N.Step() = step(st_b0, Pc.pfcp_event(Up.N4.heartbeat(2, [0, 0, 0, 1], U32.add(hb, 1))))
    C.Check.report("a Heartbeat Response with another sequence number: ignored", again(step(K.Kernel.state(o_wrong), F.TimerFired{0}), req_hb))
    +o_alive : N.Step() = step(st_b0, Pc.pfcp_event(Up.N4.heartbeat(2, [0, 0, 0, 1], hb)))
    C.Check.report("the Heartbeat Response: the link up, the next Heartbeat Request in 30 s with a new sequence number", Bool.and(Up.N4.up(K.Kernel.state(o_alive)), Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o_alive))), 0n), Bool.and(U32.is_eq(Pc.first_ms(K.Kernel.frames(o_alive)), 30000), Bool.not(U32.is_eq(Pc.pfcp_seq(Pc.first_pfcp(K.Kernel.frames(step(K.Kernel.state(o_alive), F.TimerFired{0})))), hb))))))
    +st_lost_reg : S.State = K.Kernel.state(step(K.Kernel.state(step(K.Kernel.state(step(K.Kernel.state(step(K.Kernel.state(step(st_reg, F.TimerFired{0})), F.TimerFired{0})), F.TimerFired{0})), F.TimerFired{0})), F.TimerFired{0}))
    +o_refuse : N.Step() = step(st_lost_reg, A.data(1, A.hex_of(A.entry(30n, msgs), "hex")))
    C.Check.report("with the link down: a new session is refused, Establishment Reject #38", Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_refuse)), 0n), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_refuse))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 38, 18, 1])))

def main() -> IO(Unit):
  do IO<Unit>:
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    stale_guards(msgs)
    +view : Result<&2, &2, B.Err, W.InitialUEMessage.View> = W.InitialUEMessage.view(A.ies_of(Fr.Pdu.read(A.hex_of(A.entry(14n, msgs), "hex"))))
    +ran : B.Bytes() = A.ran_of(view)
    +uli : Maybe<&2, G.UserLocationInformation> = A.uli_of(view)
    +st_reg : S.State = A.registered(msgs)
    C.Check.report("the captured Association Setup Response brings the N4 link up", Bool.and(Up.N4.up(st_reg), A.phase_is(st_reg, "registered")))
    +o1 : N.Step() = step(st_reg, A.data(1, A.hex_of(A.entry(30n, msgs), "hex")))
    +st1 : S.State = K.Kernel.state(o1)
    +req : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(o1))
    +req_ies : List<&2, T.Tlv> = Pc.pfcp_ies(req)
    +cap_ies : List<&2, T.Tlv> = Pc.pfcp_ies(A.hex_of(A.entry(35n, msgs), "hex"))
    C.Check.report("UL NAS Transport: one session creating, one PFCP Session Establishment Request, one guard", Bool.and(Nat.is_eq(Pc.session_count(st1), 1n), Bool.and(Pc.sphase_is(st1, "creating"), Bool.and(U32.is_eq(Pc.pfcp_kind(req), 50), Nat.is_eq(A.timer_starts(K.Kernel.frames(o1)), 1n)))))
    C.Check.report("UL NAS Transport: the session's guard timer is its local SEID, the captured 466", U32.is_eq(A.first_timer(K.Kernel.frames(o1)), 466))
    C.Check.report("UL NAS Transport: the Accept the creating session holds has QoS rules within sixteen packet filters", Gs.Gsm.bounded(S.State.sessions(st1)))
    C.Check.report("Session Establishment Request: the captured F-SEID, two PDRs, two FARs, one QER", Bool.and(B.bytes_eq(Pc.body(57, req_ies), Pc.body(57, cap_ies)), Bool.and(Nat.is_eq(count_kind(1, req_ies), 2n), Bool.and(Nat.is_eq(count_kind(3, req_ies), 2n), Nat.is_eq(count_kind(7, req_ies), 1n)))))
    C.Check.report("Session Establishment Request: the uplink PDR has the captured N3 F-TEID, the downlink one the captured UE address", Bool.and(B.bytes_eq(Pc.body(21, Pc.inside(2, Pc.inside(1, req_ies))), [1, 0, 0, 199, 196, 10, 33, 0, 20]), B.bytes_eq(Pc.body(93, Pc.inside(2, Pc.inside(1, List.drop(&2, T.Tlv, req_ies, 3n)))), [6, 10, 45, 0, 2])))
    C.Check.report("Session Establishment Request: the QER carries QFI 1 and the captured MBR", Bool.and(B.bytes_eq(Pc.body(124, Pc.inside(7, req_ies)), [1]), B.bytes_eq(Pc.body(26, Pc.inside(7, req_ies)), [0, 0, 15, 66, 64, 0, 0, 15, 66, 64])))
    +o2 : N.Step() = step(st1, Pc.pfcp_event(Pc.with_seq(A.hex_of(A.entry(36n, msgs), "hex"), Pc.pfcp_seq(req))))
    +st2 : S.State = K.Kernel.state(o2)
    +setup : B.Bytes() = A.first_bytes(A.sends(K.Kernel.frames(o2)))
    +cap_setup : B.Bytes() = A.hex_of(A.entry(37n, msgs), "hex")
    C.Check.report("Session Establishment Response: the session is being set up; PDU Session Resource Setup Request", Bool.and(Pc.sphase_is(st2, "setting"), A.pdu_is(Fr.Pdu.read(setup), Fr.Pdu.initiating(), 29)))
    C.Check.report("PDU Session Resource Setup Request: the captured transfer and UE aggregate bit rate", Bool.and(B.bytes_eq(item_transfer(setup_items(setup)), item_transfer(setup_items(cap_setup))), A.same_ie(110, setup, cap_setup)))
    C.Check.report("PDU Session Establishment Accept: IPv4, SSC 1, the default rule, 1 Gbit/s, 10.45.0.2, the DNS server", B.bytes_eq(inner(item_nas(setup_items(setup))), [126, 0, 104, 1, 0, 41, 46, 1, 1, 194, 17, 0, 9, 1, 0, 6, 49, 49, 1, 1, 255, 1, 6, 6, 3, 232, 6, 3, 232, 41, 5, 1, 10, 45, 0, 2, 123, 0, 8, 128, 0, 13, 4, 8, 8, 8, 8, 18, 1]))
    +o3 : N.Step() = step(st2, A.data(1, A.hex_of(A.entry(40n, msgs), "hex")))
    +st3 : S.State = K.Kernel.state(o3)
    +mod : B.Bytes() = Pc.first_pfcp(K.Kernel.frames(o3))
    C.Check.report("PDU Session Resource Setup Response: Session Modification with the captured gNB tunnel", Bool.and(Pc.sphase_is(st3, "modifying"), Bool.and(U32.is_eq(Pc.pfcp_kind(mod), 52), B.bytes_eq(Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(mod)))), Pc.body(84, Pc.inside(11, Pc.inside(10, Pc.pfcp_ies(A.hex_of(A.entry(41n, msgs), "hex")))))))))
    +o4 : N.Step() = step(st3, Pc.pfcp_event(Pc.with_seq(A.hex_of(A.entry(42n, msgs), "hex"), Pc.pfcp_seq(mod))))
    +st4 : S.State = K.Kernel.state(o4)
    C.Check.report("Session Modification Response: the session is active, its guard stopped", Bool.and(Pc.sphase_is(st4, "active"), Nat.is_eq(A.timer_cancels(K.Kernel.frames(o4)), 1n)))
    +o_heart : N.Step() = step(st4, Pc.pfcp_event(A.hex_of(A.entry(2n, msgs), "hex")))
    C.Check.report("Heartbeat Request from the UPF: Heartbeat Response with its sequence number", Bool.and(U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_heart))), 2), U32.is_eq(Pc.pfcp_seq(Pc.first_pfcp(K.Kernel.frames(o_heart))), 2)))
    +o_tick : N.Step() = step(st4, F.TimerFired{0})
    C.Check.report("the N4 timer: a Heartbeat Request and the timer again", Bool.and(U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_tick))), 1), Nat.is_eq(A.timer_starts(K.Kernel.frames(o_tick)), 1n)))
    association(msgs, st_reg, o_tick)
    +o_two : N.Step() = step(st4, A.data(1, A.uplink(ran, uli, A.ue_protect(3, ul_transport([46, 2, 3, 193, 255, 255], [])))))
    +two_ies : List<&2, T.Tlv> = Pc.pfcp_ies(Pc.first_pfcp(K.Kernel.frames(o_two)))
    C.Check.report("a TEID and a SEID drawn that a live session holds are drawn again, never evicting it", Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_two)), 2n), Bool.and(B.bytes_eq(Pc.body(21, Pc.inside(2, Pc.inside(1, two_ies))), [1, 0, 0, 1, 210, 10, 33, 0, 20]), B.bytes_eq(List.take(&2, U32, Pc.body(57, two_ies), 9n), [2, 0, 0, 0, 0, 45, 202, 228, 28]))))
    +o_mod : N.Step() = step(st4, A.data(1, A.uplink(ran, uli, A.ue_protect(3, ul_transport([46, 1, 2, 201], [])))))
    C.Check.report("PDU Session Modification Request: Modification Reject #31, the session as it was", Bool.and(Pc.sphase_is(K.Kernel.state(o_mod), "active"), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_mod))))), [126, 0, 104, 1, 0, 5, 46, 1, 2, 202, 31, 18, 1])))
    +o_refused : N.Step() = step(st1, Pc.pfcp_event(Pc.with_cause(Pc.with_seq(A.hex_of(A.entry(36n, msgs), "hex"), Pc.pfcp_seq(req)), 73)))
    C.Check.report("Session Establishment refused by the UPF: Establishment Reject #38, no session left", Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_refused)), 0n), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_refused))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 38, 18, 1])))
    C.Check.report("no Session Establishment Response: three retransmissions of the same request, its sequence number included, the session still being created", Bool.and(again(expire(0n, st1), req), Bool.and(again(expire(1n, st1), req), Bool.and(again(expire(2n, st1), req), Pc.sphase_is(K.Kernel.state(expire(2n, st1)), "creating")))))
    +o_late : N.Step() = expire(3n, st1)
    C.Check.report("no Session Establishment Response after the third retransmission: Establishment Reject #38, no session left", Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_late)), 0n), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_late))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 38, 18, 1])))
    +rel_cmd : B.Bytes() = [126, 0, 104, 1, 0, 5, 46, 1, 0, 211, 26, 18, 1]
    +o_set_late : N.Step() = step(st2, F.TimerFired{Pc.session_timer(st2)})
    C.Check.report("no answer from the gNB in time, after the Accept: PDU Session Release Command #26, Session Deletion at the UPF, the session being deleted", Bool.and(Pc.sphase_is(K.Kernel.state(o_set_late), "deleting"), Bool.and(U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_set_late))), 54), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_set_late))))), rel_cmd))))
    +o_mod_no : N.Step() = step(st3, Pc.pfcp_event(Pf.Msg.write(Pf.Msg.make(53, Some{[0, 0, 0, 0, 0, 0, 0, 1]}, Pc.pfcp_seq(mod), [T.Tlv.make(19, [73])]), [])))
    C.Check.report("Session Modification refused by the UPF: PDU Session Release Command #26, Session Deletion, the session being deleted", Bool.and(Pc.sphase_is(K.Kernel.state(o_mod_no), "deleting"), Bool.and(U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_mod_no))), 54), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_mod_no))))), rel_cmd))))
    C.Check.report("no Session Modification Response: three retransmissions of the same request, the session still being modified", Bool.and(again(expire(0n, st3), mod), Bool.and(again(expire(1n, st3), mod), Bool.and(again(expire(2n, st3), mod), Pc.sphase_is(K.Kernel.state(expire(2n, st3)), "modifying")))))
    +o_mod_late : N.Step() = expire(3n, st3)
    C.Check.report("no Session Modification Response after the third retransmission: PDU Session Release Command #26, Session Deletion, the session being deleted", Bool.and(Pc.sphase_is(K.Kernel.state(o_mod_late), "deleting"), Bool.and(U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_mod_late))), 54), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_mod_late))))), rel_cmd))))
    +o_twice : N.Step() = step(st2, A.data(1, setup_twice(ran, oks_of(W.PDUSessionResourceSetupResponse.view(A.ies_of(Fr.Pdu.read(A.hex_of(A.entry(40n, msgs), "hex"))))))))
    C.Check.report("the gNB names the session set up twice, first with a transfer that does not decode: only the last naming counts, one Session Modification, one warning", Bool.and(Pc.sphase_is(K.Kernel.state(o_twice), "modifying"), Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o_twice))), 1n), Bool.and(U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_twice))), 52), Nat.is_eq(warns(K.Kernel.frames(o_twice)), 1n)))))
    +o_gnb : N.Step() = step(st2, A.data(1, setup_failure(ran)))
    C.Check.report("the gNB fails the setup: Session Deletion at the UPF, Establishment Reject #26, the session being deleted", Bool.and(Pc.sphase_is(K.Kernel.state(o_gnb), "deleting"), Bool.and(U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_gnb))), 54), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_gnb))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 26, 18, 1]))))
    +o_dnn : N.Step() = step(st_reg, A.data(1, A.uplink(ran, uli, A.ue_protect(2, ul_transport(A.hex_of(A.entry(32n, msgs), "hex"), [37, 4, 3, 102, 111, 111])))))
    C.Check.report("an unknown DNN: Establishment Reject #27, no session, no PFCP", Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_dnn)), 0n), Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), Pc.pfcp_sends(K.Kernel.frames(o_dnn))), 0n), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_dnn))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 27, 18, 1]))))
    +st_small : S.State = A.registered_with(List.append(&2, T.Tlv, A.config([T.Tlv.make(32, A.subscriber([0, 0, 0, 0, 0, 32]))]), [T.Tlv.make(10, [31])]), msgs)
    +o_pool : N.Step() = step(st_small, A.data(1, A.hex_of(A.entry(30n, msgs), "hex")))
    C.Check.report("the pool exhausted: Establishment Reject #26, no session", Bool.and(Nat.is_eq(Pc.session_count(K.Kernel.state(o_pool)), 0n), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_pool))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 26, 18, 1])))
    +o_down : N.Step() = step(st4, F.NgapAssocDown{1})
    C.Check.report("the association down: the active session is being deleted at the UPF", Bool.and(Pc.sphase_is(K.Kernel.state(o_down), "deleting"), U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_down))), 54)))
    deleting(ran, uli, st3, req, mod)
    +o_rel : N.Step() = step(K.Kernel.state(step(st4, A.data(1, A.release_request(ran)))), A.data(1, N.Ngap.pdu(Fr.Pdu.successful(), 41, Fr.Criticality.reject(), [N.Ngap.ie(10, Fr.Criticality.ignore(), G.AMF_UE_NGAP_ID.write([1], 0n, [])), N.Ngap.ie(85, Fr.Criticality.ignore(), G.RAN_UE_NGAP_ID.write(ran, 0n, []))])))
    C.Check.report("the UE released: its session is being deleted at the UPF", Bool.and(Pc.sphase_is(K.Kernel.state(o_rel), "deleting"), Bool.and(Nat.is_eq(A.ue_count(K.Kernel.state(o_rel)), 0n), U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_rel))), 54))))
    +st_releasing : S.State = K.Kernel.state(step(st4, A.data(1, A.release_request(ran))))
    +o_silent : N.Step() = step(st_releasing, F.TimerFired{1})
    C.Check.report("the gNB never sends Release Complete: when the guard fires, the UE is forgotten and its session is being deleted at the UPF", Bool.and(Nat.is_eq(A.ue_count(K.Kernel.state(o_silent)), 0n), Bool.and(Pc.sphase_is(K.Kernel.state(o_silent), "deleting"), U32.is_eq(Pc.pfcp_kind(Pc.first_pfcp(K.Kernel.frames(o_silent))), 54))))
