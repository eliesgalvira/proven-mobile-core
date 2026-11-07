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
import ../crypto/kdf.bend as Kd
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

# The UE's stored {NH, NCC} is the first NH from this KAMF and KgNB, NCC 1.
def nh_is_first(c: S.Nh, +k_amf: B.Bytes(), +k_gnb: B.Bytes()) -> Bool:
  match c:
    case S.Nh{k, nh, ncc}:
      Bool.and(B.bytes_eq(k, k_amf), Bool.and(B.bytes_eq(nh, Kd.kdf.nh(k_amf, k_gnb)), U32.is_eq(ncc, 1)))

def nh_first(p: S.Phase, +k_amf: B.Bytes(), +k_gnb: B.Bytes()) -> Bool:
  match p:
    case S.ContextSetup{g, ctx, nh, response, complete}:
      nh_is_first(nh, k_amf, k_gnb)
    case S.Registered{ctx, nh, released}:
      nh_is_first(nh, k_amf, k_gnb)
    case _:
      False{}

def nh_first_of(m: Maybe<&2, S.Ue>, +k_amf: B.Bytes(), +k_gnb: B.Bytes()) -> Bool:
  match m:
    case Some{u}:
      nh_first(S.Ue.phase(u), k_amf, k_gnb)
    case None{}:
      False{}

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

# The AMF-UE-NGAP-ID search set to start at an id.
def rewound(st: S.State, ue: U32) -> S.State:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      S.State{config, subs, assocs, ues, sessions, pfcp_seq, ue, n4}

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
    +s : V.Vec = V.Vec.field(Capture.data(), "secrets")
    C.Check.report("Initial Context Setup: the UE keeps NH 1 from KAMF and the KgNB sent, with NCC 1", nh_first_of(A.ue1(st3), V.Vec.secret(s, "k_amf"), V.Vec.secret(s, "k_gnb")))
    +o_replay : N.Step() = K.Kernel.step(st3, A.data(1, A.hex_of(A.entry(22n, msgs), "hex")), A.entropy())
    C.Check.report("Security Mode Complete replayed: ignored", Bool.and(A.phase_is(K.Kernel.state(o_replay), "context_setup"), Nat.is_eq(List.length(&2, F.Action, A.sends(K.Kernel.frames(o_replay))), 0n)))
    +o_plain : N.Step() = K.Kernel.step(st2, A.data(1, A.uplink(ran, uli, auth_resp)), A.entropy())
    C.Check.report("plaintext after security: a plain message is ignored", Bool.and(A.phase_is(K.Kernel.state(o_plain), "security_mode"), Nat.is_eq(List.length(&2, F.Action, A.sends(K.Kernel.frames(o_plain))), 0n)))
    +o4 : N.Step() = K.Kernel.step(st3, A.data(1, A.hex_of(A.entry(27n, msgs), "hex")), A.entropy())
    +o5 : N.Step() = K.Kernel.step(K.Kernel.state(o4), A.data(1, A.hex_of(A.entry(28n, msgs), "hex")), A.entropy())
    +st5 : S.State = K.Kernel.state(o5)
    C.Check.report("Initial Context Setup Response, then the captured Registration Complete: registered, T3550 stopped", Bool.and(A.phase_is(K.Kernel.state(o4), "context_setup"), Bool.and(A.phase_is(st5, "registered"), Nat.is_eq(A.timer_cancels(K.Kernel.frames(o5)), 1n))))
    +o5b : N.Step() = K.Kernel.step(K.Kernel.state(K.Kernel.step(st3, A.data(1, A.hex_of(A.entry(28n, msgs), "hex")), A.entropy())), A.data(1, A.hex_of(A.entry(27n, msgs), "hex")), A.entropy())
    C.Check.report("Registered: the UE still keeps NH 1, NCC 1", nh_first_of(A.ue1(st5), V.Vec.secret(s, "k_amf"), V.Vec.secret(s, "k_gnb")))
    C.Check.report("Registration Complete, then Initial Context Setup Response: registered", A.phase_is(K.Kernel.state(o5b), "registered"))
    +o_rel2 : N.Step() = K.Kernel.step(st5, A.data_on(2, A.release_request(ran)), A.entropy())
    C.Check.report("UE Context Release Request from another association: Error Indication, state unchanged", Bool.and(A.phase_is(K.Kernel.state(o_rel2), "registered"), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_rel2)))), Fr.Pdu.initiating(), 9)))
    +o_rel : N.Step() = K.Kernel.step(st5, A.data(1, A.release_request(ran)), A.entropy())
    C.Check.report("UE Context Release Request from the owner: Release Command", Bool.and(A.phase_is(K.Kernel.state(o_rel), "releasing"), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_rel)))), Fr.Pdu.initiating(), 41)))
    +o_cpl2 : N.Step() = K.Kernel.step(K.Kernel.state(o_rel), A.data_on(2, release_complete(ran)), A.entropy())
    C.Check.report("UE Context Release Complete from another association: Error Indication, context kept", Bool.and(Nat.is_eq(A.ue_count(K.Kernel.state(o_cpl2)), 1n), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_cpl2)))), Fr.Pdu.initiating(), 9)))
    +o_cpl : N.Step() = K.Kernel.step(K.Kernel.state(o_rel), A.data(1, release_complete(ran)), A.entropy())
    C.Check.report("UE Context Release Complete from the owner: the context is forgotten", Nat.is_eq(A.ue_count(K.Kernel.state(o_cpl)), 0n))
    +o_replay2 : N.Step() = K.Kernel.step(st5, A.data_on(2, initial), A.entropy())
    +st_r : S.State = K.Kernel.state(o_replay2)
    C.Check.report("a captured SUCI replayed from another gNB: the registered UE stays, the newcomer is only challenged", Bool.and(String.eq(phase_at(st_r, 1), "registered"), Bool.and(Nat.is_eq(A.ue_count(st_r), 2n), Bool.and(Nat.is_eq(List.length(&2, F.Action, A.sends(K.Kernel.frames(o_replay2))), 1n), U32.is_eq(A.nas_type(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_replay2))))), 86)))))
    C.Check.report("a second context: the next odd AMF-UE-NGAP-ID, 3, whose guard timer is 3", Bool.and(String.eq(phase_at(st_r, 3), "authenticating"), U32.is_eq(A.first_timer(K.Kernel.frames(o_replay2)), 3)))
    +st_w : S.State = K.Kernel.state(K.Kernel.step(rewound(st1, 1), A.data_on(2, initial), A.entropy()))
    C.Check.report("the AMF-UE-NGAP-ID search skips an id a context holds", Bool.and(Nat.is_eq(A.ue_count(st_w), 2n), Bool.and(String.eq(phase_at(st_w, 1), "authenticating"), String.eq(phase_at(st_w, 3), "authenticating"))))
    +o_fail2 : N.Step() = K.Kernel.step(st_r, A.data_on(2, A.uplink_as([3], ran, uli, flip_last(auth_resp))), A.entropy())
    C.Check.report("the newcomer fails 5G-AKA: the registered UE is untouched", Bool.and(String.eq(phase_at(K.Kernel.state(o_fail2), 1), "registered"), String.eq(phase_at(K.Kernel.state(o_fail2), 3), "releasing")))
    +o_take : N.Step() = K.Kernel.step(st_r, A.data_on(2, A.uplink_as([3], ran, uli, auth_resp)), A.entropy())
    +st_t : S.State = K.Kernel.state(o_take)
    C.Check.report("the newcomer passes 5G-AKA: only then is the old context released", Bool.and(Nat.is_eq(A.ue_count(st_t), 1n), Bool.and(String.eq(phase_at(st_t, 3), "security_mode"), Bool.and(A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_take)))), Fr.Pdu.initiating(), 41), A.pdu_is(Fr.Pdu.read(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_take)), 1n))), Fr.Pdu.initiating(), 4)))))
    +o_dereg : N.Step() = K.Kernel.step(st5, A.data(1, A.uplink(ran, uli, A.ue_protect(2, deregistration(1)))), A.entropy())
    C.Check.report("Deregistration Request: Deregistration Accept, then Release Command", Bool.and(A.phase_is(K.Kernel.state(o_dereg), "releasing"), Bool.and(B.bytes_eq(List.drop(&2, U32, A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_dereg)))), 7n), [126, 0, 70]), A.pdu_is(Fr.Pdu.read(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_dereg)), 1n))), Fr.Pdu.initiating(), 41))))
    +o_big : N.Step() = K.Kernel.step(st5, A.data(1, A.uplink_as([1, 0, 0, 0, 1], ran, uli, A.ue_protect(2, deregistration(1)))), A.entropy())
    C.Check.report("an AMF-UE-NGAP-ID of 2^32 + 1: an unknown UE, never UE 1", Bool.and(A.phase_is(K.Kernel.state(o_big), "registered"), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_big)))), Fr.Pdu.initiating(), 9)))
    +o_off : N.Step() = K.Kernel.step(st5, A.data(1, A.uplink(ran, uli, A.ue_protect(2, deregistration(9)))), A.entropy())
    C.Check.report("Deregistration Request, switch off: Release Command only", Bool.and(A.phase_is(K.Kernel.state(o_off), "releasing"), Bool.and(Nat.is_eq(List.length(&2, F.Action, A.sends(K.Kernel.frames(o_off))), 1n), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_off)))), Fr.Pdu.initiating(), 41))))
    +st_nia1 : S.State = K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(S.State.initial(), F.Evt.config_make(A.config_nia([1], [T.Tlv.make(32, A.subscriber([0, 0, 0, 0, 0, 32]))])), A.entropy())), F.NgapAssocUp{1}, A.entropy())), A.data(1, initial), A.entropy()))
    +o_nia1 : N.Step() = K.Kernel.step(st_nia1, A.data(1, A.uplink(ran, uli, auth_resp)), A.entropy())
    C.Check.report("no integrity algorithm in common: Registration Reject #23, then release", Bool.and(A.phase_is(K.Kernel.state(o_nia1), "releasing"), B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_nia1)))), [126, 0, 68, 23])))
    +o_bad : N.Step() = K.Kernel.step(st1, A.data(1, A.uplink(ran, uli, flip_last(auth_resp))), A.entropy())
    C.Check.report("a wrong RES*: Authentication Reject, then UE Context Release Command", Bool.and(A.phase_is(K.Kernel.state(o_bad), "releasing"), Bool.and(U32.is_eq(A.nas_type(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_bad))))), 88), A.pdu_is(Fr.Pdu.read(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_bad)), 1n))), Fr.Pdu.initiating(), 41))))
    +o_other : N.Step() = K.Kernel.step(st1, F.NgapData{2, 1, U32.from_nat(List.length(&2, U32, A.uplink(ran, uli, auth_resp))), A.uplink(ran, uli, auth_resp)}, A.entropy())
    C.Check.report("an Authentication Response over another association: Error Indication, state unchanged", Bool.and(A.phase_is(K.Kernel.state(o_other), "authenticating"), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_other)))), Fr.Pdu.initiating(), 9)))
    +st_retry : S.State = fire(4n, st1)
    +o_retry : N.Step() = K.Kernel.step(st1, F.TimerFired{1}, A.entropy())
    C.Check.report("T3560: the Authentication Request is retransmitted", Bool.and(B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_retry)))), auth_req), Bool.and(Nat.is_eq(A.timer_starts(K.Kernel.frames(o_retry)), 1n), A.phase_is(st_retry, "authenticating"))))
    +o_giveup : N.Step() = K.Kernel.step(st_retry, F.TimerFired{1}, A.entropy())
    C.Check.report("T3560: after four retransmissions the UE context is released", Bool.and(A.phase_is(K.Kernel.state(o_giveup), "releasing"), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_giveup)))), Fr.Pdu.initiating(), 41)))
    +st_nosub : S.State = K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(S.State.initial(), F.Evt.config_make(A.config([])), A.entropy())), F.NgapAssocUp{1}, A.entropy()))
    +o_nosub : N.Step() = K.Kernel.step(st_nosub, A.data(1, initial), A.entropy())
    C.Check.report("an unknown subscriber: Registration Reject #7, then release", Bool.and(A.phase_is(K.Kernel.state(o_nosub), "releasing"), Bool.and(B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_nosub)))), [126, 0, 68, 7]), A.pdu_is(Fr.Pdu.read(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_nosub)), 1n))), Fr.Pdu.initiating(), 41))))
    +o_bad_view : N.Step() = K.Kernel.step(st0, A.data(1, N.Ngap.pdu(Fr.Pdu.initiating(), 15, Fr.Criticality.ignore(), [N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write([1], 0n, []))])), A.entropy())
    C.Check.report("an InitialUEMessage missing its NAS-PDU: Error Indication and no context", Bool.and(Nat.is_eq(A.ue_count(K.Kernel.state(o_bad_view)), 0n), A.pdu_is(Fr.Pdu.read(A.first_bytes(A.sends(K.Kernel.frames(o_bad_view)))), Fr.Pdu.initiating(), 9)))
    +guti_pdu : B.Bytes() = N.Ngap.pdu(Fr.Pdu.initiating(), 15, Fr.Criticality.ignore(), [N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran, 0n, [])), N.Ngap.ie(38, Fr.Criticality.reject(), G.NAS_PDU.write(guti_registration(), 0n, [])), N.Ngap.ie(121, Fr.Criticality.reject(), A.uli_bits(uli)), N.Ngap.ie(90, Fr.Criticality.ignore(), G.RRCEstablishmentCause.write(Ap.Root{3}, 0n, []))])
    +o_guti : N.Step() = K.Kernel.step(st0, A.data(1, guti_pdu), A.entropy())
    C.Check.report("a Registration Request with an unknown 5G-GUTI: Identity Request", Bool.and(A.phase_is(K.Kernel.state(o_guti), "identifying"), B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_guti)))), [126, 0, 91, 1])))
    +sht1_pdu : B.Bytes() = N.Ngap.pdu(Fr.Pdu.initiating(), 15, Fr.Criticality.ignore(), [N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran, 0n, [])), N.Ngap.ie(38, Fr.Criticality.reject(), G.NAS_PDU.write(List.append(&2, U32, [126, 1, 9, 9, 9, 9, 3], guti_registration()), 0n, [])), N.Ngap.ie(121, Fr.Criticality.reject(), A.uli_bits(uli)), N.Ngap.ie(90, Fr.Criticality.ignore(), G.RRCEstablishmentCause.write(Ap.Root{3}, 0n, []))])
    +o_sht1 : N.Step() = K.Kernel.step(st0, A.data(1, sht1_pdu), A.entropy())
    C.Check.report("a returning UE's integrity-protected Registration Request, read unverified: Identity Request", Bool.and(A.phase_is(K.Kernel.state(o_sht1), "identifying"), B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_sht1)))), [126, 0, 91, 1])))
    +service_pdu : B.Bytes() = N.Ngap.pdu(Fr.Pdu.initiating(), 15, Fr.Criticality.ignore(), [N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran, 0n, [])), N.Ngap.ie(38, Fr.Criticality.reject(), G.NAS_PDU.write([126, 1, 9, 9, 9, 9, 3, 126, 0, 76, 0, 0, 7, 244, 0, 64, 1, 2, 3, 4], 0n, [])), N.Ngap.ie(121, Fr.Criticality.reject(), A.uli_bits(uli)), N.Ngap.ie(90, Fr.Criticality.ignore(), G.RRCEstablishmentCause.write(Ap.Root{3}, 0n, []))])
    +o_service : N.Step() = K.Kernel.step(st0, A.data(1, service_pdu), A.entropy())
    C.Check.report("a returning UE's Service Request: Service Reject #9, then UE Context Release Command", Bool.and(A.phase_is(K.Kernel.state(o_service), "releasing"), Bool.and(B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_service)))), [126, 0, 77, 9]), A.pdu_is(Fr.Pdu.read(A.first_bytes(List.drop(&2, F.Action, A.sends(K.Kernel.frames(o_service)), 1n))), Fr.Pdu.initiating(), 41))))
    +o_ident : N.Step() = K.Kernel.step(K.Kernel.state(o_guti), A.data(1, A.uplink(ran, uli, identity_response(mobile_identity(reg_req)))), A.entropy())
    C.Check.report("Identity Response with the SUCI: the captured Authentication Request follows", Bool.and(A.phase_is(K.Kernel.state(o_ident), "authenticating"), B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_ident)))), auth_req)))
    +o_sync : N.Step() = K.Kernel.step(st1, A.data(1, A.uplink(ran, uli, synch_failure(rand_of(auth_req), [0, 0, 0, 0, 1, 0]))), A.entropy())
    C.Check.report("synch failure with a valid AUTS: a new Authentication Request from the UE's SQN", Bool.and(A.phase_is(K.Kernel.state(o_sync), "authenticating"), Bool.and(U32.is_eq(A.nas_type(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_sync))))), 86), Bool.not(B.bytes_eq(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_sync)))), auth_req)))))
    +o_sync2 : N.Step() = K.Kernel.step(K.Kernel.state(o_sync), A.data(1, A.uplink(ran, uli, synch_failure(rand_of(auth_req), [0, 0, 0, 0, 2, 0]))), A.entropy())
    C.Check.report("a second synch failure: Authentication Reject and release", Bool.and(A.phase_is(K.Kernel.state(o_sync2), "releasing"), U32.is_eq(A.nas_type(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_sync2))))), 88)))
    +o_mac : N.Step() = K.Kernel.step(st1, A.data(1, A.uplink(ran, uli, Mm.Mm.write(Mm.Mm{Mm.AuthenticationFailure{}, [I.FByte{20}], []}))), A.entropy())
    C.Check.report("MAC failure: Authentication Reject and release", Bool.and(A.phase_is(K.Kernel.state(o_mac), "releasing"), U32.is_eq(A.nas_type(A.nas_of(A.first_bytes(A.sends(K.Kernel.frames(o_mac))))), 88)))
