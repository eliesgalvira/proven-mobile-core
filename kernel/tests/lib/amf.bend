import Base
import ../../bytes.bend as B
import ../../aper.bend as Ap
import ../../tlv.bend as T
import ../../ngap/frame.bend as Fr
import ../../ngap/gen/types.bend as G
import ../../ngap/gen/views.bend as W
import ../../nas/mm.bend as Mm
import ../../nas/ie.bend as I
import ../../crypto/milenage.bend as Mil
import ../../nas/security.bend as Sec
import ../../frame.bend as F
import ../../table.bend as Tb
import ../../state.bend as S
import ../../step.bend as K
import ../../amf/ngap.bend as N
import ./check.bend as C
import ./vec.bend as V
import ../vectors/capture-vectors.bend as Capture

# Helpers for the AMF tests: the capture's network and subscriber as Config
# TLVs, the captured messages by index, and ways to look at a step's outcome.

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

def config_nia(nia: B.Bytes(), subs: List<&2, T.Tlv>) -> List<&2, T.Tlv>:
  List.append(&2, T.Tlv, [T.Tlv.make(1, [0, 241, 16]), T.Tlv.make(2, [2]), T.Tlv.make(3, [0, 1]), T.Tlv.make(4, [0]), T.Tlv.make(5, [0, 0, 1]), T.Tlv.make(6, [115, 112, 101, 99, 107, 45, 97, 109, 102, 48]), T.Tlv.make(7, [1]), T.Tlv.make(8, [105, 110, 116, 101, 114, 110, 101, 116]), T.Tlv.make(9, [10, 45, 0, 0]), T.Tlv.make(10, [16]), T.Tlv.make(11, [8, 8, 8, 8]), T.Tlv.make(12, [10, 33, 0, 12]), T.Tlv.make(13, [10, 33, 0, 20]), T.Tlv.make(14, [10, 33, 0, 20]), T.Tlv.make(15, key32()), T.Tlv.make(16, [1]), T.Tlv.make(17, [0]), T.Tlv.make(18, nia)], subs)

def config(subs: List<&2, T.Tlv>) -> List<&2, T.Tlv>:
  config_nia([2], subs)

# The NAS keys the capture derived (vectors.json § secrets), for messages the UE would protect.
def k_nas_int() -> B.Bytes():
  [30, 181, 142, 160, 186, 204, 48, 183, 70, 200, 96, 117, 204, 30, 215, 58]

def k_nas_enc() -> B.Bytes():
  [160, 149, 110, 6, 153, 86, 201, 196, 101, 124, 194, 7, 42, 69, 81, 175]

def ue_protect(sqn: U32, plain: B.Bytes()) -> B.Bytes():
  Sec.Nas.seal(Sec.Keys{k_nas_int(), k_nas_enc(), Sec.Nea0{}, Sec.Nia2{}, 1}, Sec.Ciphered{}, Sec.Nas.uplink(), Sec.Count{0, sqn}, plain)

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

# The id of the first timer started.
def first_timer(actions: List<&2, F.Action>) -> U32:
  match actions:
    case Nil{}:
      0
    case F.TimerStart{timer, ms} <> more:
      timer
    case a <> more:
      first_timer(more)

def timer_cancels(actions: List<&2, F.Action>) -> Nat:
  match actions:
    case Nil{}:
      0n
    case F.TimerCancel{timer} <> more:
      1n+timer_cancels(more)
    case a <> more:
      timer_cancels(more)

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
    case Done{W.DownlinkNASTransport.View{amf, ran, old, nas, ambr, allowed}}:
      nas
    case _:
      []

def nas_of(bytes: B.Bytes()) -> B.Bytes():
  dl_nas(W.DownlinkNASTransport.view(ies_of(Fr.Pdu.read(bytes))))

def ie_or_empty(m: Maybe<&2, B.Bytes()>) -> B.Bytes():
  match m:
    case None{}:
      []
    case Some{v}:
      v

# The same IE value in two NGAP PDUs.
def same_ie(+id: U32, +a: B.Bytes(), +b: B.Bytes()) -> Bool:
  B.bytes_eq(ie_or_empty(Fr.Ies.lookup(id, ies_of(Fr.Pdu.read(a)))), ie_or_empty(Fr.Ies.lookup(id, ies_of(Fr.Pdu.read(b)))))

# UEContextReleaseRequest and Complete for our UE 1 with the captured RAN id.
def release_request(ran: B.Bytes()) -> B.Bytes():
  N.Ngap.pdu(Fr.Pdu.initiating(), 42, Fr.Criticality.ignore(), [N.Ngap.ie(10, Fr.Criticality.reject(), G.AMF_UE_NGAP_ID.write([1], 0n, [])), N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran, 0n, [])), N.Ngap.ie(15, Fr.Criticality.ignore(), G.Cause.write(N.Ngap.radio_cause(G.CauseRadioNetwork.user_inactivity()), 0n, []))])

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

# An UplinkNASTransport with an AMF id, the captured RAN id and location, and a NAS message.
def uplink_as(amf: B.Bytes(), ran: B.Bytes(), uli: Maybe<&2, G.UserLocationInformation>, nas: B.Bytes()) -> B.Bytes():
  N.Ngap.pdu(Fr.Pdu.initiating(), 46, Fr.Criticality.ignore(), [N.Ngap.ie(10, Fr.Criticality.reject(), G.AMF_UE_NGAP_ID.write(amf, 0n, [])), N.Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran, 0n, [])), N.Ngap.ie(38, Fr.Criticality.reject(), G.NAS_PDU.write(nas, 0n, [])), N.Ngap.ie(121, Fr.Criticality.ignore(), uli_bits(uli))])

def uplink(ran: B.Bytes(), uli: Maybe<&2, G.UserLocationInformation>, nas: B.Bytes()) -> B.Bytes():
  uplink_as([1], ran, uli, nas)

def data(stream: U32, +bytes: B.Bytes()) -> F.Evt:
  F.NgapData{1, stream, U32.from_nat(List.length(&2, U32, bytes)), bytes}

def data_on(assoc: U32, +bytes: B.Bytes()) -> F.Evt:
  F.NgapData{assoc, 1, U32.from_nat(List.length(&2, U32, bytes)), bytes}

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
    case S.Authenticating{g, av, r, s}:
      "authenticating"
    case S.SecurityMode{g, ctx, kamf}:
      "security_mode"
    case S.ContextSetup{g, ctx, nh, response, complete}:
      "context_setup"
    case S.Registered{ctx, nh}:
      "registered"
    case S.Switching{g, ctx, nh, released}:
      "switching"
    case S.Created{}:
      "created"
    case S.Releasing{g}:
      "releasing"

def phase_name(m: Maybe<&2, S.Ue>) -> String:
  match m:
    case None{}:
      "none"
    case Some{u}:
      phase_of(S.Ue.phase(u))

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

# The capture replayed up to registration: Config, the association, the
# InitialUEMessage, the Authentication Response, the Security Mode Complete,
# the Initial Context Setup Response and the Registration Complete.
def after(st: S.State, ev: F.Evt) -> S.State:
  K.Kernel.state(K.Kernel.step(st, ev, entropy()))

def registered_with(cfg: List<&2, T.Tlv>, +msgs: List<&2, V.Vec>) -> S.State:
  +initial : B.Bytes() = hex_of(entry(14n, msgs), "hex")
  +view : Result<&2, &2, B.Err, W.InitialUEMessage.View> = W.InitialUEMessage.view(ies_of(Fr.Pdu.read(initial)))
  +st0 : S.State = after(after(after(S.State.initial(), F.Evt.config_make(cfg)), F.Evt.pfcp_make(hex_of(entry(1n, msgs), "hex"))), F.NgapAssocUp{1})
  +st2 : S.State = after(after(st0, data(1, initial)), data(1, uplink(ran_of(view), uli_of(view), hex_of(entry(19n, msgs), "plaintext_hex"))))
  after(after(after(st2, data(1, hex_of(entry(22n, msgs), "hex"))), data(1, hex_of(entry(27n, msgs), "hex"))), data(1, hex_of(entry(28n, msgs), "hex")))

def registered(msgs: List<&2, V.Vec>) -> S.State:
  registered_with(config([T.Tlv.make(32, subscriber([0, 0, 0, 0, 0, 32]))]), msgs)
