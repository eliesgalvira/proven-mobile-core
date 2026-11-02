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
import ../frame.bend as F
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture

# Replays the captured registration up to authentication: with the captured
# RAND as entropy and the subscriber's SQN one step before the captured one,
# the Authentication Request is the captured one byte for byte and the
# captured Authentication Response verifies. Then the failure paths.

def entropy() -> B.Bytes():
  [45, 202, 228, 29, 52, 210, 168, 148, 210, 151, 160, 24, 229, 85, 66, 153, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def k() -> B.Bytes():
  [70, 91, 92, 232, 177, 153, 180, 159, 170, 95, 10, 46, 226, 56, 166, 188]

def opc() -> B.Bytes():
  [232, 237, 40, 157, 235, 169, 82, 228, 40, 59, 84, 232, 142, 97, 131, 202]

def supi_ascii() -> B.Bytes():
  [48, 48, 49, 48, 49, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49]

def subscriber(sqn: B.Bytes()) -> B.Bytes():
  F.Sub.write(F.Sub{supi_ascii(), k(), opc(), [128, 0], sqn})

def key32() -> B.Bytes():
  [88, 47, 147, 31, 207, 143, 43, 127, 145, 29, 235, 182, 34, 79, 113, 231, 43, 157, 74, 98, 238, 211, 141, 18, 159, 253, 119, 140, 48, 22, 211, 106]

def config(subs: List<&2, T.Tlv>) -> List<&2, T.Tlv>:
  List.append(&2, T.Tlv, [T.Tlv.make(1, [0, 241, 16]), T.Tlv.make(2, [2]), T.Tlv.make(3, [0, 1]), T.Tlv.make(4, [0]), T.Tlv.make(5, [0, 0, 1]), T.Tlv.make(6, [115, 112, 101, 99, 107, 45, 97, 109, 102, 48]), T.Tlv.make(7, [1]), T.Tlv.make(8, [105, 110, 116, 101, 114, 110, 101, 116]), T.Tlv.make(9, [10, 45, 0, 0]), T.Tlv.make(10, [16]), T.Tlv.make(11, [8, 8, 8, 8]), T.Tlv.make(12, [10, 33, 0, 12]), T.Tlv.make(13, [10, 33, 0, 20]), T.Tlv.make(14, [10, 33, 0, 20]), T.Tlv.make(15, key32()), T.Tlv.make(16, [1]), T.Tlv.make(17, [0]), T.Tlv.make(18, [2])], subs)

# The capture
# -----------

def keep(+m: V.Vec, hit: Bool, rest: Maybe<&2, V.Vec>) -> Maybe<&2, V.Vec>:
  match hit:
    case True{}:
      Some{m}
    case False{}:
      rest

def entry(+index: Nat, msgs: List<&2, V.Vec>) -> Maybe<&2, V.Vec>:
  match msgs:
    case Nil{}:
      None{}
    case +m <> rest:
      keep(m, Nat.is_eq(V.Vec.nat(V.Vec.field(m, "index")), index), entry(index, rest))

def hex_of(m: Maybe<&2, V.Vec>, +field: String) -> B.Bytes():
  match m:
    case None{}:
      []
    case Some{v}:
      V.Vec.bytes(V.Vec.field(v, field))

# Looking at outcomes
# -------------------

def sends(actions: List<&2, F.Action>) -> List<&2, F.Action>:
  match actions:
    case Nil{}:
      []
    case F.NgapSend{assoc, stream, len, bytes} <> more:
      F.NgapSend{assoc, stream, len, bytes} <> sends(more)
    case a <> more:
      sends(more)

def timer_starts(actions: List<&2, F.Action>) -> Nat:
  match actions:
    case Nil{}:
      0n
    case F.TimerStart{timer, ms} <> more:
      1n+timer_starts(more)
    case a <> more:
      timer_starts(more)

def first_bytes(ss: List<&2, F.Action>) -> B.Bytes():
  match ss:
    case F.NgapSend{assoc, stream, len, bytes} <> more:
      bytes
    case _:
      []

def first_stream(ss: List<&2, F.Action>) -> U32:
  match ss:
    case F.NgapSend{assoc, stream, len, bytes} <> more:
      stream
    case _:
      999

def ies_rd(r: Ap.Rd(List<&2, Fr.Ie>)) -> List<&2, Fr.Ie>:
  match r:
    case Fail{e}:
      []
    case Done{(ies, c)}:
      ies

def ies_of(r: Result<&2, &2, B.Err, Fr.Pdu>) -> List<&2, Fr.Ie>:
  match r:
    case Fail{e}:
      []
    case Done{p}:
      ies_rd(Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(Fr.Pdu.value(p)), 1n)}))

def pdu_is(r: Result<&2, &2, B.Err, Fr.Pdu>, +kind: U32, +code: U32) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{+p}:
      Bool.and(U32.is_eq(Fr.Pdu.kind(p), kind), U32.is_eq(Fr.Pdu.code(p), code))

# The NAS-PDU of a DownlinkNASTransport.
def dl_nas(r: Result<&2, &2, B.Err, W.DownlinkNASTransport.View>) -> B.Bytes():
  match r:
    case Done{W.DownlinkNASTransport.View{amf, ran, old, nas, allowed}}:
      nas
    case _:
      []

def nas_of(bytes: B.Bytes()) -> B.Bytes():
  dl_nas(W.DownlinkNASTransport.view(ies_of(Fr.Pdu.read(bytes))))

def uli_of(r: Result<&2, &2, B.Err, W.InitialUEMessage.View>) -> Maybe<&2, G.UserLocationInformation>:
  match r:
    case Done{W.InitialUEMessage.View{ran, nas, uli, cause, a, b, c, d, e, f, g}}:
      Some{uli}
    case _:
      None{}

def ran_of(r: Result<&2, &2, B.Err, W.InitialUEMessage.View>) -> B.Bytes():
  match r:
    case Done{W.InitialUEMessage.View{ran, nas, uli, cause, a, b, c, d, e, f, g}}:
      ran
    case _:
      []

def uli_bits(m: Maybe<&2, G.UserLocationInformation>) -> Ap.Bits():
  match m:
    case None{}:
      []
    case Some{uli}:
      G.UserLocationInformation.write(uli, 0n, [])

# An UplinkNASTransport with our AMF id, the captured RAN id and location, and a NAS message.
def uplink(ran: B.Bytes(), uli: Maybe<&2, G.UserLocationInformation>, nas: B.Bytes()) -> B.Bytes():
  N.Ngap.pdu(Fr.Pdu.initiating(), 46, Fr.Criticality.ignore(), [N.Ngap.ie(10, Fr.Criticality.reject(), G.AMF_UE_NGAP_ID.write([1], 0n, [])), N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran, 0n, [])), N.Ngap.ie(38, Fr.Criticality.reject(), G.NAS_PDU.write(nas, 0n, [])), N.Ngap.ie(121, Fr.Criticality.ignore(), uli_bits(uli))])

def data(stream: U32, +bytes: B.Bytes()) -> F.Evt:
  F.NgapData{1, stream, U32.from_nat(List.length(&2, U32, bytes)), bytes}

def Tb_get(t: List<&2, Sigma<&2, &2, U32, _ => S.Ue>>) -> Maybe<&2, S.Ue>:
  match t:
    case (1, u) <> more:
      Some{u}
    case _:
      None{}

def ue1(st: S.State) -> Maybe<&2, S.Ue>:
  Tb_get(S.State.ues(st))

def phase_of(p: S.Phase) -> String:
  match p:
    case S.Identifying{g}:
      "identifying"
    case S.Authenticating{g, av, r}:
      "authenticating"
    case S.Authenticated{g, kamf}:
      "authenticated"
    case S.Releasing{}:
      "releasing"

def phase_name(m: Maybe<&2, S.Ue>) -> String:
  match m:
    case None{}:
      "none"
    case Some{u}:
      phase_of(S.Ue.phase(u))

def k_amf_phase(p: S.Phase) -> B.Bytes():
  match p:
    case S.Authenticated{g, kamf}:
      kamf
    case _:
      []

def k_amf_of(m: Maybe<&2, S.Ue>) -> B.Bytes():
  match m:
    case Some{u}:
      k_amf_phase(S.Ue.phase(u))
    case None{}:
      []

def ue_count(st: S.State) -> Nat:
  List.length(&2, Sigma<&2, &2, U32, _ => S.Ue>, S.State.ues(st))

def phase_is(st: S.State, name: String) -> Bool:
  String.eq(phase_name(ue1(st)), name)

def nas_type(nas: B.Bytes()) -> U32:
  match nas:
    case 126 <> 0 <> t <> rest:
      t
    case _:
      0

def fire(times: Nat, st: S.State) -> S.State:
  match times:
    case 0n:
      st
    case 1n+n:
      fire(n, K.Kernel.state(K.Kernel.step(st, F.TimerFired{1}, entropy())))

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
  Mm.Mm.write(Mm.Mm{Mm.AuthenticationFailure{}, [I.FByte{21}], [I.Ie{48, I.Tlv{}, 14, List.append(&2, U32, xor(sqn_ms, Mil.milenage.f5_star(k(), opc(), rand)), Mil.milenage.f1_star(k(), opc(), rand, sqn_ms, [0, 0]))}]})

def rand_of(nas: B.Bytes()) -> B.Bytes():
  List.take(&2, U32, List.drop(&2, U32, nas, 8n), 16n)

def main() -> IO(Unit):
  do IO<Unit>:
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    +initial : B.Bytes() = hex_of(entry(14n, msgs), "hex")
    +auth_req : B.Bytes() = hex_of(entry(17n, msgs), "plaintext_hex")
    +auth_resp : B.Bytes() = hex_of(entry(19n, msgs), "plaintext_hex")
    +reg_req : B.Bytes() = hex_of(entry(15n, msgs), "plaintext_hex")
    +view : Result<&2, &2, B.Err, W.InitialUEMessage.View> = W.InitialUEMessage.view(ies_of(Fr.Pdu.read(initial)))
    +ran : B.Bytes() = ran_of(view)
    +uli : Maybe<&2, G.UserLocationInformation> = uli_of(view)
    +st0 : S.State = K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(S.State.initial(), F.Evt.config_make(config([T.Tlv.make(32, subscriber([0, 0, 0, 0, 0, 32]))])), entropy())), F.NgapAssocUp{1}, entropy()))
    +o1 : S.Out() = K.Kernel.step(st0, data(1, initial), entropy())
    +st1 : S.State = K.Kernel.state(o1)
    +a1 : List<&2, F.Action> = K.Kernel.actions(o1)
    C.Check.report("InitialUEMessage: one UE context, authenticating", Bool.and(Nat.is_eq(ue_count(st1), 1n), phase_is(st1, "authenticating")))
    C.Check.report("InitialUEMessage: one DownlinkNASTransport on the UE's stream and one guard timer", Bool.and(Nat.is_eq(List.length(&2, F.Action, sends(a1)), 1n), Bool.and(U32.is_eq(first_stream(sends(a1)), 1), Bool.and(pdu_is(Fr.Pdu.read(first_bytes(sends(a1))), Fr.Pdu.initiating(), 4), Nat.is_eq(timer_starts(a1), 1n)))))
    C.Check.report("Authentication Request: the captured one, byte for byte", B.bytes_eq(nas_of(first_bytes(sends(a1))), auth_req))
    +o2 : S.Out() = K.Kernel.step(st1, data(1, uplink(ran, uli, auth_resp)), entropy())
    +st2 : S.State = K.Kernel.state(o2)
    C.Check.report("Authentication Response: the captured RES* verifies", phase_is(st2, "authenticated"))
    C.Check.report("Authentication Response: KAMF is the captured one", B.bytes_eq(k_amf_of(ue1(st2)), [93, 194, 173, 250, 24, 107, 233, 224, 236, 148, 189, 209, 44, 197, 234, 73, 132, 137, 104, 192, 200, 252, 106, 232, 87, 136, 168, 246, 148, 7, 4, 117]))
    +o_bad : S.Out() = K.Kernel.step(st1, data(1, uplink(ran, uli, flip_last(auth_resp))), entropy())
    C.Check.report("a wrong RES*: Authentication Reject, then UE Context Release Command", Bool.and(phase_is(K.Kernel.state(o_bad), "releasing"), Bool.and(U32.is_eq(nas_type(nas_of(first_bytes(sends(K.Kernel.actions(o_bad))))), 88), pdu_is(Fr.Pdu.read(first_bytes(List.drop(&2, F.Action, sends(K.Kernel.actions(o_bad)), 1n))), Fr.Pdu.initiating(), 41))))
    +o_other : S.Out() = K.Kernel.step(st1, F.NgapData{2, 1, U32.from_nat(List.length(&2, U32, uplink(ran, uli, auth_resp))), uplink(ran, uli, auth_resp)}, entropy())
    C.Check.report("an Authentication Response over another association: Error Indication, state unchanged", Bool.and(phase_is(K.Kernel.state(o_other), "authenticating"), pdu_is(Fr.Pdu.read(first_bytes(sends(K.Kernel.actions(o_other)))), Fr.Pdu.initiating(), 7)))
    +st_retry : S.State = fire(4n, st1)
    +o_retry : S.Out() = K.Kernel.step(st1, F.TimerFired{1}, entropy())
    C.Check.report("T3560: the Authentication Request is retransmitted", Bool.and(B.bytes_eq(nas_of(first_bytes(sends(K.Kernel.actions(o_retry)))), auth_req), Bool.and(Nat.is_eq(timer_starts(K.Kernel.actions(o_retry)), 1n), phase_is(st_retry, "authenticating"))))
    +o_giveup : S.Out() = K.Kernel.step(st_retry, F.TimerFired{1}, entropy())
    C.Check.report("T3560: after four retransmissions the UE context is released", Bool.and(phase_is(K.Kernel.state(o_giveup), "releasing"), pdu_is(Fr.Pdu.read(first_bytes(sends(K.Kernel.actions(o_giveup)))), Fr.Pdu.initiating(), 41)))
    +st_nosub : S.State = K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(S.State.initial(), F.Evt.config_make(config([])), entropy())), F.NgapAssocUp{1}, entropy()))
    +o_nosub : S.Out() = K.Kernel.step(st_nosub, data(1, initial), entropy())
    C.Check.report("an unknown subscriber: Registration Reject #7, then release", Bool.and(phase_is(K.Kernel.state(o_nosub), "releasing"), Bool.and(B.bytes_eq(nas_of(first_bytes(sends(K.Kernel.actions(o_nosub)))), [126, 0, 68, 7]), pdu_is(Fr.Pdu.read(first_bytes(List.drop(&2, F.Action, sends(K.Kernel.actions(o_nosub)), 1n))), Fr.Pdu.initiating(), 41))))
    +o_bad_view : S.Out() = K.Kernel.step(st0, data(1, N.Ngap.pdu(Fr.Pdu.initiating(), 15, Fr.Criticality.ignore(), [N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write([1], 0n, []))])), entropy())
    C.Check.report("an InitialUEMessage missing its NAS-PDU: Error Indication and no context", Bool.and(Nat.is_eq(ue_count(K.Kernel.state(o_bad_view)), 0n), pdu_is(Fr.Pdu.read(first_bytes(sends(K.Kernel.actions(o_bad_view)))), Fr.Pdu.initiating(), 7)))
    +guti_pdu : B.Bytes() = N.Ngap.pdu(Fr.Pdu.initiating(), 15, Fr.Criticality.ignore(), [N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran, 0n, [])), N.Ngap.ie(38, Fr.Criticality.reject(), G.NAS_PDU.write(guti_registration(), 0n, [])), N.Ngap.ie(121, Fr.Criticality.reject(), uli_bits(uli)), N.Ngap.ie(90, Fr.Criticality.ignore(), G.RRCEstablishmentCause.write(Ap.Root{3}, 0n, []))])
    +o_guti : S.Out() = K.Kernel.step(st0, data(1, guti_pdu), entropy())
    C.Check.report("a Registration Request with an unknown 5G-GUTI: Identity Request", Bool.and(phase_is(K.Kernel.state(o_guti), "identifying"), B.bytes_eq(nas_of(first_bytes(sends(K.Kernel.actions(o_guti)))), [126, 0, 91, 1])))
    +o_ident : S.Out() = K.Kernel.step(K.Kernel.state(o_guti), data(1, uplink(ran, uli, identity_response(mobile_identity(reg_req)))), entropy())
    C.Check.report("Identity Response with the SUCI: the captured Authentication Request follows", Bool.and(phase_is(K.Kernel.state(o_ident), "authenticating"), B.bytes_eq(nas_of(first_bytes(sends(K.Kernel.actions(o_ident)))), auth_req)))
    +o_sync : S.Out() = K.Kernel.step(st1, data(1, uplink(ran, uli, synch_failure(rand_of(auth_req), [0, 0, 0, 0, 1, 0]))), entropy())
    C.Check.report("synch failure with a valid AUTS: a new Authentication Request from the UE's SQN", Bool.and(phase_is(K.Kernel.state(o_sync), "authenticating"), Bool.and(U32.is_eq(nas_type(nas_of(first_bytes(sends(K.Kernel.actions(o_sync))))), 86), Bool.not(B.bytes_eq(nas_of(first_bytes(sends(K.Kernel.actions(o_sync)))), auth_req)))))
    +o_sync2 : S.Out() = K.Kernel.step(K.Kernel.state(o_sync), data(1, uplink(ran, uli, synch_failure(rand_of(auth_req), [0, 0, 0, 0, 2, 0]))), entropy())
    C.Check.report("a second synch failure: Authentication Reject and release", Bool.and(phase_is(K.Kernel.state(o_sync2), "releasing"), U32.is_eq(nas_type(nas_of(first_bytes(sends(K.Kernel.actions(o_sync2))))), 88)))
    +o_mac : S.Out() = K.Kernel.step(st1, data(1, uplink(ran, uli, Mm.Mm.write(Mm.Mm{Mm.AuthenticationFailure{}, [I.FByte{20}], []}))), entropy())
    C.Check.report("MAC failure: Authentication Reject and release", Bool.and(phase_is(K.Kernel.state(o_mac), "releasing"), U32.is_eq(nas_type(nas_of(first_bytes(sends(K.Kernel.actions(o_mac))))), 88)))
