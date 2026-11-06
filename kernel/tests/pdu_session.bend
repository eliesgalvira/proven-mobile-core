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
import ../amf/ngap.bend as N
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture
import ./lib/amf.bend as A

# Replays the captured PDU session establishment after the captured
# registration: the UL NAS Transport opens a session whose PFCP Session
# Establishment Request names the captured F-SEID, TEID, UE address and bit
# rates; eUPF's captured answer brings the PDU Session Resource Setup Request
# with the captured transfer; the gNB's captured answer brings the Session
# Modification with the captured tunnel; eUPF's answer makes the session
# active. Then the association, the failure paths and release.

# Entropy with the captured RAND, the captured TEID at 20 and CP SEID at 24.
def entropy() -> B.Bytes():
  [45, 202, 228, 29, 52, 210, 168, 148, 210, 151, 160, 24, 229, 85, 66, 153, 0, 0, 0, 0, 0, 0, 199, 196, 0, 0, 1, 210, 0, 0, 0, 0]

def step(st: S.State, ev: F.Evt) -> S.Out():
  K.Kernel.step(st, ev, entropy())

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

def count_kind(+kind: U32, ies: List<&2, T.Tlv>) -> Nat:
  match ies:
    case Nil{}:
      0n
    case +t <> more:
      Nat.add(Bool.to_nat(U32.is_eq(T.Tlv.kind(t), kind)), count_kind(kind, more))

# A captured PFCP response, its sequence number made ours.
def with_seq(+bytes: B.Bytes(), seq: U32) -> B.Bytes():
  List.append(&2, U32, List.take(&2, U32, bytes, 12n), List.append(&2, U32, List.drop(&2, U32, B.write_u32(seq, []), 1n), List.drop(&2, U32, bytes, 15n)))

# The captured Session Establishment Response with another cause (its Cause IE sits after the header and the Node ID).
def with_cause(+bytes: B.Bytes(), cause: U32) -> B.Bytes():
  List.append(&2, U32, List.take(&2, U32, bytes, 29n), cause <> List.drop(&2, U32, bytes, 30n))

def pfcp_event(+bytes: B.Bytes()) -> F.Evt:
  F.PfcpData{U32.from_nat(List.length(&2, U32, bytes)), bytes}

def session1(t: Tb.Table(S.Session)) -> Maybe<&2, S.Session>:
  match t:
    case (key, s) <> more:
      Some{s}
    case _:
      None{}

def sphase_of(p: S.SPhase) -> String:
  match p:
    case S.Creating{g, pti, accept}:
      "creating"
    case S.Setting{g, pti}:
      "setting"
    case S.Modifying{g}:
      "modifying"
    case S.Active{}:
      "active"

def sphase_name(m: Maybe<&2, S.Session>) -> String:
  match m:
    case None{}:
      "none"
    case Some{s}:
      sphase_of(S.Session.phase(s))

def sphase_is(st: S.State, name: String) -> Bool:
  String.eq(sphase_name(session1(S.State.sessions(st))), name)

def guard_timer(g: Maybe<&2, S.Guard>) -> U32:
  match g:
    case None{}:
      0
    case Some{guard}:
      S.Guard.timer(guard)

def timer_of(m: Maybe<&2, S.Session>) -> U32:
  match m:
    case None{}:
      0
    case Some{s}:
      guard_timer(S.SPhase.guard(S.Session.phase(s)))

def session_count(st: S.State) -> Nat:
  List.length(&2, Sigma<&2, &2, U32, _ => S.Session>, S.State.sessions(st))

def session_timer(st: S.State) -> U32:
  timer_of(session1(S.State.sessions(st)))

def ue_guard(m: Maybe<&2, S.Ue>) -> Maybe<&2, S.Guard>:
  match m:
    case None{}:
      None{}
    case Some{u}:
      S.Ue.guard(u)

def ue_timer(st: S.State) -> U32:
  guard_timer(ue_guard(A.ue1(st)))

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

# UL NAS Transport with an N1 SM message, the PDU session identity, request type initial, and more IEs.
def ul_transport(+sm: B.Bytes(), more: B.Bytes()) -> B.Bytes():
  List.append(&2, U32, [126, 0, 103, 1, 0, U32.from_nat(List.length(&2, U32, sm))], List.append(&2, U32, sm, List.append(&2, U32, [18, 1, 129], more)))

# The plaintext inside a protected DL NAS Transport (NEA0).
def inner(nas: B.Bytes()) -> B.Bytes():
  List.drop(&2, U32, nas, 7n)

def main() -> IO(Unit):
  do IO<Unit>:
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    +view : Result<&2, &2, B.Err, W.InitialUEMessage.View> = W.InitialUEMessage.view(A.ies_of(Fr.Pdu.read(A.hex_of(A.entry(14n, msgs), "hex"))))
    +ran : B.Bytes() = A.ran_of(view)
    +uli : Maybe<&2, G.UserLocationInformation> = A.uli_of(view)
    +st_reg : S.State = A.registered(msgs)
    C.Check.report("the captured Association Setup Response brings the N4 link up", Bool.and(Up.N4.up(st_reg), A.phase_is(st_reg, "registered")))
    +o1 : S.Out() = step(st_reg, A.data(1, A.hex_of(A.entry(30n, msgs), "hex")))
    +st1 : S.State = K.Kernel.state(o1)
    +req : B.Bytes() = first_pfcp(K.Kernel.actions(o1))
    +req_ies : List<&2, T.Tlv> = pfcp_ies(req)
    +cap_ies : List<&2, T.Tlv> = pfcp_ies(A.hex_of(A.entry(35n, msgs), "hex"))
    C.Check.report("UL NAS Transport: one session creating, one PFCP Session Establishment Request, one guard", Bool.and(Nat.is_eq(session_count(st1), 1n), Bool.and(sphase_is(st1, "creating"), Bool.and(U32.is_eq(pfcp_kind(req), 50), Nat.is_eq(A.timer_starts(K.Kernel.actions(o1)), 1n)))))
    C.Check.report("Session Establishment Request: the captured F-SEID, two PDRs, two FARs, one QER", Bool.and(B.bytes_eq(body(57, req_ies), body(57, cap_ies)), Bool.and(Nat.is_eq(count_kind(1, req_ies), 2n), Bool.and(Nat.is_eq(count_kind(3, req_ies), 2n), Nat.is_eq(count_kind(7, req_ies), 1n)))))
    C.Check.report("Session Establishment Request: the uplink PDR has the captured N3 F-TEID, the downlink one the captured UE address", Bool.and(B.bytes_eq(body(21, inside(2, inside(1, req_ies))), [1, 0, 0, 199, 196, 10, 33, 0, 20]), B.bytes_eq(body(93, inside(2, inside(1, List.drop(&2, T.Tlv, req_ies, 3n)))), [6, 10, 45, 0, 2])))
    C.Check.report("Session Establishment Request: the QER carries QFI 1 and the captured MBR", Bool.and(B.bytes_eq(body(124, inside(7, req_ies)), [1]), B.bytes_eq(body(26, inside(7, req_ies)), [0, 0, 15, 66, 64, 0, 0, 15, 66, 64])))
    +o2 : S.Out() = step(st1, pfcp_event(with_seq(A.hex_of(A.entry(36n, msgs), "hex"), pfcp_seq(req))))
    +st2 : S.State = K.Kernel.state(o2)
    +setup : B.Bytes() = A.first_bytes(A.sends(K.Kernel.actions(o2)))
    +cap_setup : B.Bytes() = A.hex_of(A.entry(37n, msgs), "hex")
    C.Check.report("Session Establishment Response: the session is being set up; PDU Session Resource Setup Request", Bool.and(sphase_is(st2, "setting"), A.pdu_is(Fr.Pdu.read(setup), Fr.Pdu.initiating(), 29)))
    C.Check.report("PDU Session Resource Setup Request: the captured transfer and UE aggregate bit rate", Bool.and(B.bytes_eq(item_transfer(setup_items(setup)), item_transfer(setup_items(cap_setup))), A.same_ie(110, setup, cap_setup)))
    C.Check.report("PDU Session Establishment Accept: IPv4, SSC 1, the default rule, 1 Gbit/s, 10.45.0.2, the DNS server", B.bytes_eq(inner(item_nas(setup_items(setup))), [126, 0, 104, 1, 0, 41, 46, 1, 1, 194, 17, 0, 9, 1, 0, 6, 49, 49, 1, 1, 255, 1, 6, 6, 3, 232, 6, 3, 232, 41, 5, 1, 10, 45, 0, 2, 123, 0, 8, 128, 0, 13, 4, 8, 8, 8, 8, 18, 1]))
    +o3 : S.Out() = step(st2, A.data(1, A.hex_of(A.entry(40n, msgs), "hex")))
    +st3 : S.State = K.Kernel.state(o3)
    +mod : B.Bytes() = first_pfcp(K.Kernel.actions(o3))
    C.Check.report("PDU Session Resource Setup Response: Session Modification with the captured gNB tunnel", Bool.and(sphase_is(st3, "modifying"), Bool.and(U32.is_eq(pfcp_kind(mod), 52), B.bytes_eq(body(84, inside(11, inside(10, pfcp_ies(mod)))), body(84, inside(11, inside(10, pfcp_ies(A.hex_of(A.entry(41n, msgs), "hex")))))))))
    +o4 : S.Out() = step(st3, pfcp_event(with_seq(A.hex_of(A.entry(42n, msgs), "hex"), pfcp_seq(mod))))
    +st4 : S.State = K.Kernel.state(o4)
    C.Check.report("Session Modification Response: the session is active, its guard stopped", Bool.and(sphase_is(st4, "active"), Nat.is_eq(A.timer_cancels(K.Kernel.actions(o4)), 1n)))
    +o_heart : S.Out() = step(st4, pfcp_event(A.hex_of(A.entry(2n, msgs), "hex")))
    C.Check.report("Heartbeat Request from eUPF: Heartbeat Response with its sequence number", Bool.and(U32.is_eq(pfcp_kind(first_pfcp(K.Kernel.actions(o_heart))), 2), U32.is_eq(pfcp_seq(first_pfcp(K.Kernel.actions(o_heart))), 2)))
    +o_tick : S.Out() = step(st4, F.TimerFired{0})
    C.Check.report("the N4 timer: a Heartbeat Request and the timer again", Bool.and(U32.is_eq(pfcp_kind(first_pfcp(K.Kernel.actions(o_tick))), 1), Nat.is_eq(A.timer_starts(K.Kernel.actions(o_tick)), 1n)))
    +o_mod : S.Out() = step(st4, A.data(1, A.uplink(ran, uli, A.ue_protect(3, ul_transport([46, 1, 2, 201], [])))))
    C.Check.report("PDU Session Modification Request: Modification Reject #31, the session as it was", Bool.and(sphase_is(K.Kernel.state(o_mod), "active"), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.actions(o_mod))))), [126, 0, 104, 1, 0, 5, 46, 1, 2, 202, 31, 18, 1])))
    +o_refused : S.Out() = step(st1, pfcp_event(with_cause(with_seq(A.hex_of(A.entry(36n, msgs), "hex"), pfcp_seq(req)), 73)))
    C.Check.report("Session Establishment refused by eUPF: Establishment Reject #38, no session left", Bool.and(Nat.is_eq(session_count(K.Kernel.state(o_refused)), 0n), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.actions(o_refused))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 38, 18, 1])))
    +o_late : S.Out() = step(st1, F.TimerFired{session_timer(st1)})
    C.Check.report("no Session Establishment Response in time: Establishment Reject #38, no session left", Bool.and(Nat.is_eq(session_count(K.Kernel.state(o_late)), 0n), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.actions(o_late))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 38, 18, 1])))
    +o_gnb : S.Out() = step(st2, A.data(1, setup_failure(ran)))
    C.Check.report("the gNB fails the setup: Session Deletion at eUPF, Establishment Reject #26, no session left", Bool.and(Nat.is_eq(session_count(K.Kernel.state(o_gnb)), 0n), Bool.and(U32.is_eq(pfcp_kind(first_pfcp(K.Kernel.actions(o_gnb))), 54), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.actions(o_gnb))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 26, 18, 1]))))
    +o_dnn : S.Out() = step(st_reg, A.data(1, A.uplink(ran, uli, A.ue_protect(2, ul_transport(A.hex_of(A.entry(32n, msgs), "hex"), [37, 4, 3, 102, 111, 111])))))
    C.Check.report("an unknown DNN: Establishment Reject #27, no session, no PFCP", Bool.and(Nat.is_eq(session_count(K.Kernel.state(o_dnn)), 0n), Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), pfcp_sends(K.Kernel.actions(o_dnn))), 0n), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.actions(o_dnn))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 27, 18, 1]))))
    +st_small : S.State = A.registered_with(List.append(&2, T.Tlv, A.config([T.Tlv.make(32, A.subscriber([0, 0, 0, 0, 0, 32]))]), [T.Tlv.make(10, [31])]), msgs)
    +o_pool : S.Out() = step(st_small, A.data(1, A.hex_of(A.entry(30n, msgs), "hex")))
    C.Check.report("the pool exhausted: Establishment Reject #26, no session", Bool.and(Nat.is_eq(session_count(K.Kernel.state(o_pool)), 0n), B.bytes_eq(inner(A.nas_of(A.first_bytes(A.sends(K.Kernel.actions(o_pool))))), [126, 0, 104, 1, 0, 5, 46, 1, 1, 195, 26, 18, 1])))
    +o_down : S.Out() = step(st4, F.NgapAssocDown{1})
    C.Check.report("the association down: the active session is deleted at eUPF", Bool.and(Nat.is_eq(session_count(K.Kernel.state(o_down)), 0n), U32.is_eq(pfcp_kind(first_pfcp(K.Kernel.actions(o_down))), 54)))
    +o_rel : S.Out() = step(K.Kernel.state(step(st4, A.data(1, A.release_request(ran)))), A.data(1, N.Ngap.pdu(Fr.Pdu.successful(), 41, Fr.Criticality.reject(), [N.Ngap.ie(10, Fr.Criticality.ignore(), G.AMF_UE_NGAP_ID.write([1], 0n, [])), N.Ngap.ie(85, Fr.Criticality.ignore(), G.RAN_UE_NGAP_ID.write(ran, 0n, []))])))
    C.Check.report("the UE released: its session is deleted at eUPF with it", Bool.and(Nat.is_eq(session_count(K.Kernel.state(o_rel)), 0n), Bool.and(Nat.is_eq(A.ue_count(K.Kernel.state(o_rel)), 0n), U32.is_eq(pfcp_kind(first_pfcp(K.Kernel.actions(o_rel))), 54))))
    +st_releasing : S.State = K.Kernel.state(step(st4, A.data(1, A.release_request(ran))))
    +o_silent : S.Out() = step(st_releasing, F.TimerFired{ue_timer(st_releasing)})
    C.Check.report("the gNB never sends Release Complete: when the guard fires, the UE and its session are forgotten and the session deleted at eUPF", Bool.and(Nat.is_eq(A.ue_count(K.Kernel.state(o_silent)), 0n), Bool.and(Nat.is_eq(session_count(K.Kernel.state(o_silent)), 0n), U32.is_eq(pfcp_kind(first_pfcp(K.Kernel.actions(o_silent))), 54))))
    +st_cfg : S.State = K.Kernel.state(step(S.State.initial(), F.Evt.config_make(A.config([]))))
    +st_t3 : S.State = K.Kernel.state(step(K.Kernel.state(step(st_cfg, F.TimerFired{0})), F.TimerFired{0}))
    +o_t4 : S.Out() = step(st_t3, F.TimerFired{0})
    C.Check.report("no Association Setup Response: three tries, then a pause", Bool.and(U32.is_eq(pfcp_kind(first_pfcp(K.Kernel.actions(step(st_cfg, F.TimerFired{0})))), 5), Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), pfcp_sends(K.Kernel.actions(o_t4))), 0n), Nat.is_eq(A.timer_starts(K.Kernel.actions(o_t4)), 1n))))
    C.Check.report("the pause over: the association is asked for again", U32.is_eq(pfcp_kind(first_pfcp(K.Kernel.actions(step(K.Kernel.state(o_t4), F.TimerFired{0})))), 5))
