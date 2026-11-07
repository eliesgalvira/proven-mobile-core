import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../tlv.bend as T
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as W
import ../nas/mm.bend as Mm
import ../nas/ie.bend as I
import ../crypto/milenage.bend as Mil
import ../nas/security.bend as Sec
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture
import ./lib/amf.bend as A

def ics_nas(r: Result<&2, &2, B.Err, W.InitialContextSetupRequest.View>) -> B.Bytes():
  match r:
    case Done{W.InitialContextSetupRequest.View{amf, ran, old, ambr, guami, nssai, caps, key, Some{nas}}}:
      nas
    case _:
      []

def release_complete(ran: B.Bytes()) -> B.Bytes():
  N.Ngap.pdu(Fr.Pdu.successful(), 41, Fr.Criticality.reject(), [N.Ngap.ie(10, Fr.Criticality.ignore(), G.AMF_UE_NGAP_ID.write([1], 0n, [])), N.Ngap.ie(85, Fr.Criticality.ignore(), G.RAN_UE_NGAP_ID.write(ran, 0n, []))])

# Deregistration Request (TS 24.501 §8.2.12): type in the low nibble, our 5G-GUTI.
def deregistration(kind: U32) -> B.Bytes():
  [126, 0, 69, kind, 0, 11, 242, 0, 241, 16, 2, 0, 64, 0, 0, 0, 0]

def k_amf_phase(p: S.Phase) -> B.Bytes():
  match p:
    case S.SecurityMode{g, ctx, kamf}:
      kamf
    case _:
      []

def k_amf_of(m: Maybe<&2, S.Ue>) -> B.Bytes():
  match m:
    case Some{u}:
      k_amf_phase(S.Ue.phase(u))
    case None{}:
      []

def fire(times: Nat, st: S.State) -> S.State:
  match times:
    case 0n:
      st
    case 1n+n:
      fire(n, K.Kernel.state(K.Kernel.step(st, F.TimerFired{1}, A.entropy())))

def flip_last(bs: B.Bytes()) -> B.Bytes():
  match bs:
    case Nil{}:
      []
    case b <> Nil{}:
      [U32.xor(b, 1)]
    case b <> rest:
      b <> flip_last(rest)

# A Registration Request with a 5G-GUTI (TS 24.501 §9.11.3.4): PLMN 00f110, AMF region 2, set 1, pointer 0, TMSI 1.
def guti_registration() -> B.Bytes():
  [126, 0, 65, 121, 0, 11, 242, 0, 241, 16, 2, 0, 64, 0, 0, 0, 1, 46, 4, 240, 240, 240, 240]

def identity_response(+suci: B.Bytes()) -> B.Bytes():
  Mm.Mm.write(Mm.Mm{Mm.IdentityResponse{}, [I.FLvE{I.LenBody{U32.from_nat(List.length(&2, U32, suci)), suci}}], []})

def mobile_identity(reg: B.Bytes()) -> B.Bytes():
  List.take(&2, U32, List.drop(&2, U32, reg, 6n), 53n)

# Authentication Failure, synch failure, with the AUTS a UE holding sqn_ms would compute.
def xor(xs: B.Bytes(), ys: B.Bytes()) -> B.Bytes():
  match xs ys:
    case x <> xt y <> yt:
      U32.xor(x, y) <> xor(xt, yt)
    case _ _:
      []

def synch_failure(+rand: B.Bytes(), +sqn_ms: B.Bytes()) -> B.Bytes():
  Mm.Mm.write(Mm.Mm{Mm.AuthenticationFailure{}, [I.FByte{21}], [I.Ie{48, I.Tlv{}, 14, List.append(&2, U32, xor(sqn_ms, Mil.milenage.f5_star(A.k(), A.opc(), rand)), Mil.milenage.f1_star(A.k(), A.opc(), rand, sqn_ms, [0, 0]))}]})

def rand_of(nas: B.Bytes()) -> B.Bytes():
  List.take(&2, U32, List.drop(&2, U32, nas, 8n), 16n)

def phase_at(st: S.State, +key: U32) -> String:
  A.phase_name(Tb.Table.get(S.Ue, key, S.State.ues(st)))

def timer_of(g: Maybe<&2, S.Guard>) -> U32:
  match g:
    case Some{guard}:
      S.Guard.timer(guard)
    case None{}:
      0

def guard_of(m: Maybe<&2, S.Ue>) -> U32:
  match m:
    case Some{u}:
      timer_of(S.Ue.guard(u))
    case None{}:
      0

def timer_at(st: S.State, +key: U32) -> U32:
  guard_of(Tb.Table.get(S.Ue, key, S.State.ues(st)))

# The id counters set where they will be after counting through 2^32 ids.
def rewound(st: S.State, ue: U32, timer: U32) -> S.State:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      S.State{config, subs, assocs, ues, sessions, pfcp_seq, ue, timer, n4}

def main() -> IO(Unit):
  do IO<Unit>:
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    +initial : B.Bytes() = A.hex_of(A.entry(14n, msgs), "hex")
    +auth_req : B.Bytes() = A.hex_of(A.entry(17n, msgs), "plaintext_hex")
    +auth_resp : B.Bytes() = A.hex_of(A.entry(19n, msgs), "plaintext_hex")
    +reg_req : B.Bytes() = A.hex_of(A.entry(15n, msgs), "plaintext_hex")
    +view : Result<&2, &2, B.Err, W.InitialUEMessage.View> = W.InitialUEMessage.view(A.ies_of(Fr.Pdu.read(initial)))
    +ran : B.Bytes() = A.ran_of(view)
    +uli : Maybe<&2, G.UserLocationInformation> = A.uli_of(view)
    +st0 : S.State = K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(S.State.initial(), F.Evt.config_make(A.config([T.Tlv.make(32, A.subscriber([0, 0, 0, 0, 0, 32]))])), A.entropy())), F.NgapAssocUp{1}, A.entropy()))
    +o1 : N.Step() = K.Kernel.step(st0, A.data(1, initial), A.entropy())
    +st1 : S.State = K.Kernel.state(o1)
    +a1 : List<&2, F.Action> = K.Kernel.frames(o1)
    C.Check.report("InitialUEMessage: one UE context, authenticating", Bool.and(Nat.is_eq(A.ue_count(st1), 1n), A.phase_is(st1, "authenticating")))
    C.Check.report("InitialUEMessage: one DownlinkNASTransport on the UE's stream and one guard timer", Bool.and(Nat.is_eq(List.length(&2, F.Action, A.sends(a1)), 1n), Bool.and(U32.is_eq(A.first_stream(A.sends(a1)), 1), Bool.and(A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(a1))), Fr.Pdu.initiating(), 4), Nat.is_eq(A.timer_starts(a1), 1n)))))
    C.Check.report("Authentication Request: the captured one, byte for byte", B.bytes_eq(A.nas_of(A.first_bytes(A.sends(a1))), auth_req))
    +o2 : N.Step() = K.Kernel.step(st1, A.data(1, A.uplink(ran, uli, auth_resp)), A.entropy())
    +st2 : S.State = K.Kernel.state(o2)
    C.Check.report("Authentication Response: the captured RES* verifies, Security Mode follows", A.phase_is(st2, "security_mode"))
    C.Check.report("Authentication Response: KAMF is the captured one", B.bytes_eq(k_amf_of(A.ue1(st2)), [93, 194, 173, 250, 24, 107, 233, 224, 236, 148, 189, 209, 44, 197, 234, 73, 132, 137, 104, 192, 200, 252, 106, 232, 87, 136, 168, 246, 148, 7, 4, 117]))
    C.Check.report("Security Mode Command: the captured one, byte for byte, MAC included", B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o2)))), A.hex_of(A.entry(21n, msgs), "outer_hex")))
    +o3 : N.Step() = K.Kernel.step(st2, A.data(1, A.hex_of(A.entry(22n, msgs), "hex")), A.entropy())
    +st3 : S.State = K.Kernel.state(o3)
    +ics : B.Bytes() = A.first_bytes(A.sends(K.Kernel.frames(o3)))
    +ics_cap : B.Bytes() = A.hex_of(A.entry(25n, msgs), "hex")
    C.Check.report("Security Mode Complete: the captured one verifies; Initial Context Setup Request follows", Bool.and(A.phase_is(st3, "context_setup"), Bool.and(A.pdu_is(Fr.Pdu.read(ics), Fr.Pdu.initiating(), 14), Nat.is_eq(A.timer_starts(K.Kernel.frames(o3)), 1n))))
    C.Check.report("Initial Context Setup Request: the captured KgNB, GUAMI, Allowed NSSAI and UE security capabilities", Bool.and(A.same_ie(94, ics, ics_cap), Bool.and(A.same_ie(28, ics, ics_cap), Bool.and(A.same_ie(0, ics, ics_cap), A.same_ie(119, ics, ics_cap)))))
    C.Check.report("Registration Accept: ciphered, with the 5G-GUTI from entropy, the TAI, the slice and T3512", B.bytes_eq(List.drop(&2, U32, ics_nas(W.InitialContextSetupRequest.view(A.ies_of(Fr.Pdu.read(ics)))), 7n), [126, 0, 66, 1, 1, 119, 0, 11, 242, 0, 241, 16, 2, 0, 64, 0, 0, 0, 0, 84, 7, 0, 0, 241, 16, 0, 0, 1, 21, 2, 1, 1, 94, 1, 5]))
    +o_replay : N.Step() = K.Kernel.step(st3, A.data(1, A.hex_of(A.entry(22n, msgs), "hex")), A.entropy())
    C.Check.report("Security Mode Complete replayed: ignored", Bool.and(A.phase_is(K.Kernel.state(o_replay), "context_setup"), Nat.is_eq(List.length(&2, F.Action, A.sends(K.Kernel.frames(o_replay))), 0n)))
    +o_plain : N.Step() = K.Kernel.step(st2, A.data(1, A.uplink(ran, uli, auth_resp)), A.entropy())
    C.Check.report("plaintext after security: a plain message is ignored", Bool.and(A.phase_is(K.Kernel.state(o_plain), "security_mode"), Nat.is_eq(List.length(&2, F.Action, A.sends(K.Kernel.frames(o_plain))), 0n)))
    +o4 : N.Step() = K.Kernel.step(st3, A.data(1, A.hex_of(A.entry(27n, msgs), "hex")), A.entropy())
    +o5 : N.Step() = K.Kernel.step(K.Kernel.state(o4), A.data(1, A.hex_of(A.entry(28n, msgs), "hex")), A.entropy())
    +st5 : S.State = K.Kernel.state(o5)
    C.Check.report("Initial Context Setup Response, then the captured Registration Complete: registered, T3550 stopped", Bool.and(A.phase_is(K.Kernel.state(o4), "context_setup"), Bool.and(A.phase_is(st5, "registered"), Nat.is_eq(A.timer_cancels(K.Kernel.frames(o5)), 1n))))
    +o5b : N.Step() = K.Kernel.step(K.Kernel.state(K.Kernel.step(st3, A.data(1, A.hex_of(A.entry(28n, msgs), "hex")), A.entropy())), A.data(1, A.hex_of(A.entry(27n, msgs), "hex")), A.entropy())
    C.Check.report("Registration Complete, then Initial Context Setup Response: registered", A.phase_is(K.Kernel.state(o5b), "registered"))
    +o_rel2 : N.Step() = K.Kernel.step(st5, A.data_on(2, A.release_request(ran)), A.entropy())
    C.Check.report("UE Context Release Request from another association: Error Indication, state unchanged", Bool.and(A.phase_is(K.Kernel.state(o_rel2), "registered"), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_rel2)))), Fr.Pdu.initiating(), 7)))
    +o_rel : N.Step() = K.Kernel.step(st5, A.data(1, A.release_request(ran)), A.entropy())
    C.Check.report("UE Context Release Request from the owner: Release Command", Bool.and(A.phase_is(K.Kernel.state(o_rel), "releasing"), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_rel)))), Fr.Pdu.initiating(), 41)))
    +o_cpl2 : N.Step() = K.Kernel.step(K.Kernel.state(o_rel), A.data_on(2, release_complete(ran)), A.entropy())
    C.Check.report("UE Context Release Complete from another association: Error Indication, context kept", Bool.and(Nat.is_eq(A.ue_count(K.Kernel.state(o_cpl2)), 1n), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_cpl2)))), Fr.Pdu.initiating(), 7)))
    +o_cpl : N.Step() = K.Kernel.step(K.Kernel.state(o_rel), A.data(1, release_complete(ran)), A.entropy())
    C.Check.report("UE Context Release Complete from the owner: the context is forgotten", Nat.is_eq(A.ue_count(K.Kernel.state(o_cpl)), 0n))
    +o_replay2 : N.Step() = K.Kernel.step(st5, A.data_on(2, initial), A.entropy())
    +st_r : S.State = K.Kernel.state(o_replay2)
    C.Check.report("a captured SUCI replayed from another gNB: the registered UE stays, the newcomer is only challenged", Bool.and(String.eq(phase_at(st_r, 1), "registered"), Bool.and(Nat.is_eq(A.ue_count(st_r), 2n), Bool.and(Nat.is_eq(List.length(&2, F.Action, A.sends(K.Kernel.frames(o_replay2))), 1n), U32.is_eq(A.nas_type(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_replay2))))), 86)))))
    +st_w1 : S.State = K.Kernel.state(K.Kernel.step(rewound(st1, 0, 4294967295), A.data_on(2, initial), A.entropy()))
    +st_w2 : S.State = K.Kernel.state(K.Kernel.step(st_w1, A.data_on(3, initial), A.entropy()))
    C.Check.report("the id counters wrap: AMF-UE-NGAP-ID 1 and guard timers 0 (N4) and 1, still live, are skipped", Bool.and(Nat.is_eq(A.ue_count(st_w2), 3n), Bool.and(String.eq(phase_at(st_w2, 1), "authenticating"), Bool.and(String.eq(phase_at(st_w2, 2), "authenticating"), Bool.and(U32.is_eq(timer_at(st_w2, 1), 1), Bool.and(U32.is_eq(timer_at(st_w2, 0), 4294967295), U32.is_eq(timer_at(st_w2, 2), 2)))))))
    +o_fail2 : N.Step() = K.Kernel.step(st_r, A.data_on(2, A.uplink_as([2], ran, uli, flip_last(auth_resp))), A.entropy())
    C.Check.report("the newcomer fails 5G-AKA: the registered UE is untouched", Bool.and(String.eq(phase_at(K.Kernel.state(o_fail2), 1), "registered"), String.eq(phase_at(K.Kernel.state(o_fail2), 2), "releasing")))
    +o_take : N.Step() = K.Kernel.step(st_r, A.data_on(2, A.uplink_as([2], ran, uli, auth_resp)), A.entropy())
    +st_t : S.State = K.Kernel.state(o_take)
    C.Check.report("the newcomer passes 5G-AKA: only then is the old context released", Bool.and(Nat.is_eq(A.ue_count(st_t), 1n), Bool.and(String.eq(phase_at(st_t, 2), "security_mode"), Bool.and(A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_take)))), Fr.Pdu.initiating(), 41), A.pdu_is(Fr.Pdu.read(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_take)), 1n))), Fr.Pdu.initiating(), 4)))))
    +o_dereg : N.Step() = K.Kernel.step(st5, A.data(1, A.uplink(ran, uli, A.ue_protect(2, deregistration(1)))), A.entropy())
    C.Check.report("Deregistration Request: Deregistration Accept, then Release Command", Bool.and(A.phase_is(K.Kernel.state(o_dereg), "releasing"), Bool.and(B.bytes_eq(List.drop(&2, U32, A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_dereg)))), 7n), [126, 0, 70]), A.pdu_is(Fr.Pdu.read(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_dereg)), 1n))), Fr.Pdu.initiating(), 41))))
    +o_off : N.Step() = K.Kernel.step(st5, A.data(1, A.uplink(ran, uli, A.ue_protect(2, deregistration(9)))), A.entropy())
    C.Check.report("Deregistration Request, switch off: Release Command only", Bool.and(A.phase_is(K.Kernel.state(o_off), "releasing"), Bool.and(Nat.is_eq(List.length(&2, F.Action, A.sends(K.Kernel.frames(o_off))), 1n), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_off)))), Fr.Pdu.initiating(), 41))))
    +st_nia1 : S.State = K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(S.State.initial(), F.Evt.config_make(A.config_nia([1], [T.Tlv.make(32, A.subscriber([0, 0, 0, 0, 0, 32]))])), A.entropy())), F.NgapAssocUp{1}, A.entropy())), A.data(1, initial), A.entropy()))
    +o_nia1 : N.Step() = K.Kernel.step(st_nia1, A.data(1, A.uplink(ran, uli, auth_resp)), A.entropy())
    C.Check.report("no integrity algorithm in common: Registration Reject #23, then release", Bool.and(A.phase_is(K.Kernel.state(o_nia1), "releasing"), B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_nia1)))), [126, 0, 68, 23])))
    +o_bad : N.Step() = K.Kernel.step(st1, A.data(1, A.uplink(ran, uli, flip_last(auth_resp))), A.entropy())
    C.Check.report("a wrong RES*: Authentication Reject, then UE Context Release Command", Bool.and(A.phase_is(K.Kernel.state(o_bad), "releasing"), Bool.and(U32.is_eq(A.nas_type(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_bad))))), 88), A.pdu_is(Fr.Pdu.read(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_bad)), 1n))), Fr.Pdu.initiating(), 41))))
    +o_other : N.Step() = K.Kernel.step(st1, F.NgapData{2, 1, U32.from_nat(List.length(&2, U32, A.uplink(ran, uli, auth_resp))), A.uplink(ran, uli, auth_resp)}, A.entropy())
    C.Check.report("an Authentication Response over another association: Error Indication, state unchanged", Bool.and(A.phase_is(K.Kernel.state(o_other), "authenticating"), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_other)))), Fr.Pdu.initiating(), 7)))
    +st_retry : S.State = fire(4n, st1)
    +o_retry : N.Step() = K.Kernel.step(st1, F.TimerFired{1}, A.entropy())
    C.Check.report("T3560: the Authentication Request is retransmitted", Bool.and(B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_retry)))), auth_req), Bool.and(Nat.is_eq(A.timer_starts(K.Kernel.frames(o_retry)), 1n), A.phase_is(st_retry, "authenticating"))))
    +o_giveup : N.Step() = K.Kernel.step(st_retry, F.TimerFired{1}, A.entropy())
    C.Check.report("T3560: after four retransmissions the UE context is released", Bool.and(A.phase_is(K.Kernel.state(o_giveup), "releasing"), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_giveup)))), Fr.Pdu.initiating(), 41)))
    +st_nosub : S.State = K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(S.State.initial(), F.Evt.config_make(A.config([])), A.entropy())), F.NgapAssocUp{1}, A.entropy()))
    +o_nosub : N.Step() = K.Kernel.step(st_nosub, A.data(1, initial), A.entropy())
    C.Check.report("an unknown subscriber: Registration Reject #7, then release", Bool.and(A.phase_is(K.Kernel.state(o_nosub), "releasing"), Bool.and(B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_nosub)))), [126, 0, 68, 7]), A.pdu_is(Fr.Pdu.read(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_nosub)), 1n))), Fr.Pdu.initiating(), 41))))
    +o_bad_view : N.Step() = K.Kernel.step(st0, A.data(1, N.Ngap.pdu(Fr.Pdu.initiating(), 15, Fr.Criticality.ignore(), [N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write([1], 0n, []))])), A.entropy())
    C.Check.report("an InitialUEMessage missing its NAS-PDU: Error Indication and no context", Bool.and(Nat.is_eq(A.ue_count(K.Kernel.state(o_bad_view)), 0n), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_bad_view)))), Fr.Pdu.initiating(), 7)))
    +guti_pdu : B.Bytes() = N.Ngap.pdu(Fr.Pdu.initiating(), 15, Fr.Criticality.ignore(), [N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran, 0n, [])), N.Ngap.ie(38, Fr.Criticality.reject(), G.NAS_PDU.write(guti_registration(), 0n, [])), N.Ngap.ie(121, Fr.Criticality.reject(), A.uli_bits(uli)), N.Ngap.ie(90, Fr.Criticality.ignore(), G.RRCEstablishmentCause.write(Ap.Root{3}, 0n, []))])
    +o_guti : N.Step() = K.Kernel.step(st0, A.data(1, guti_pdu), A.entropy())
    C.Check.report("a Registration Request with an unknown 5G-GUTI: Identity Request", Bool.and(A.phase_is(K.Kernel.state(o_guti), "identifying"), B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_guti)))), [126, 0, 91, 1])))
    +o_ident : N.Step() = K.Kernel.step(K.Kernel.state(o_guti), A.data(1, A.uplink(ran, uli, identity_response(mobile_identity(reg_req)))), A.entropy())
    C.Check.report("Identity Response with the SUCI: the captured Authentication Request follows", Bool.and(A.phase_is(K.Kernel.state(o_ident), "authenticating"), B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_ident)))), auth_req)))
    +o_sync : N.Step() = K.Kernel.step(st1, A.data(1, A.uplink(ran, uli, synch_failure(rand_of(auth_req), [0, 0, 0, 0, 1, 0]))), A.entropy())
    C.Check.report("synch failure with a valid AUTS: a new Authentication Request from the UE's SQN", Bool.and(A.phase_is(K.Kernel.state(o_sync), "authenticating"), Bool.and(U32.is_eq(A.nas_type(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_sync))))), 86), Bool.not(B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_sync)))), auth_req)))))
    +o_sync2 : N.Step() = K.Kernel.step(K.Kernel.state(o_sync), A.data(1, A.uplink(ran, uli, synch_failure(rand_of(auth_req), [0, 0, 0, 0, 2, 0]))), A.entropy())
    C.Check.report("a second synch failure: Authentication Reject and release", Bool.and(A.phase_is(K.Kernel.state(o_sync2), "releasing"), U32.is_eq(A.nas_type(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_sync2))))), 88)))
    +o_mac : N.Step() = K.Kernel.step(st1, A.data(1, A.uplink(ran, uli, Mm.Mm.write(Mm.Mm{Mm.AuthenticationFailure{}, [I.FByte{20}], []}))), A.entropy())
    C.Check.report("MAC failure: Authentication Reject and release", Bool.and(A.phase_is(K.Kernel.state(o_mac), "releasing"), U32.is_eq(A.nas_type(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_mac))))), 88)))
