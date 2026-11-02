import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../state.bend as S
import ../table.bend as Tb

# The AMF's NGAP side: PDUs in, PDUs out. Non-UE-associated signalling uses
# stream 0 (TS 38.412 §7).

# Building PDUs
# -------------

def Ngap.ie(id: U32, crit: U32, bits: Ap.Bits()) -> Fr.Ie:
  Fr.Ie{id, crit, Ap.pack(bits)}

# A message is a SEQUENCE whose extension bit is clear, then its IE container.
def Ngap.pdu(kind: U32, code: U32, crit: U32, ies: List<&2, Fr.Ie>) -> B.Bytes():
  Fr.Pdu.write(Fr.Pdu{kind, code, crit, Ap.pack(Ap.Bit.write(False{}, 0n, Fr.Ies.write(ies, 7n, [])))})

def Ngap.send(assoc: U32, stream: U32, bytes: B.Bytes()) -> F.Action:
  F.Action.send_make(assoc, stream, bytes)

# Error Indication (§9.2.7.1) over the association, cause only.
def Ngap.error_indication(assoc: U32, cause: G.Cause) -> F.Action:
  Ngap.send(assoc, 0, Ngap.pdu(Fr.Pdu.initiating(), 7, Fr.Criticality.ignore(), [Ngap.ie(15, Fr.Criticality.ignore(), G.Cause.write(cause, 0n, []))]))

def Ngap.protocol(index: U32) -> G.Cause:
  G.Cause_protocol{Ap.Root{index}}

def Ngap.misc(index: U32) -> G.Cause:
  G.Cause_misc{Ap.Root{index}}

# An undecodable PDU: Error Indication and a log line, nothing else.
# NG Setup (§8.7.1)
# -----------------

def Ta.plmn_in(+plmn: B.Bytes(), bl: G.BroadcastPLMNList()) -> Bool:
  match bl:
    case Nil{}:
      False{}
    case G.BroadcastPLMNItem{pLMNIdentity, tAISliceSupportList, iE_Extensions} <> more:
      Bool.or(B.bytes_eq(pLMNIdentity, plmn), Ta.plmn_in(plmn, more))

# The supported TA list names the configured TAC with the configured PLMN.
def Ta.supported(+plmn: B.Bytes(), +tac: B.Bytes(), items: G.SupportedTAList()) -> Bool:
  match items:
    case Nil{}:
      False{}
    case G.SupportedTAItem{tAC, broadcastPLMNList, iE_Extensions} <> more:
      Bool.or(Bool.and(B.bytes_eq(tAC, tac), Ta.plmn_in(plmn, broadcastPLMNList)), Ta.supported(plmn, tac, more))

def NgSetup.guami(+cfg: S.Cfg) -> G.GUAMI:
  G.GUAMI{S.Cfg.plmn(cfg), Ap.unpack(S.Cfg.region(cfg)), List.drop(&2, Bool, Ap.unpack(S.Cfg.set_id(cfg)), 6n), List.drop(&2, Bool, Ap.unpack(S.Cfg.pointer(cfg)), 2n), None{}}

def NgSetup.slices(cfg: S.Cfg) -> G.SliceSupportList():
  [G.SliceSupportItem{G.S_NSSAI{S.Cfg.sst(cfg), None{}, None{}}, None{}}]

# NG Setup Response: AMF name, served GUAMI, relative capacity 255, PLMN support.
def NgSetup.response(+cfg: S.Cfg) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.successful(), 21, Fr.Criticality.reject(), [Ngap.ie(1, Fr.Criticality.reject(), G.AMFName.write(S.Cfg.name(cfg), 0n, [])), Ngap.ie(96, Fr.Criticality.reject(), G.ServedGUAMIList.write([G.ServedGUAMIItem{NgSetup.guami(cfg), None{}, None{}}], 0n, [])), Ngap.ie(86, Fr.Criticality.ignore(), G.RelativeAMFCapacity.write(255, 0n, [])), Ngap.ie(80, Fr.Criticality.reject(), G.PLMNSupportList.write([G.PLMNSupportItem{S.Cfg.plmn(cfg), NgSetup.slices(cfg), None{}}], 0n, []))])

def NgSetup.failure(misc: U32) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.unsuccessful(), 21, Fr.Criticality.reject(), [Ngap.ie(15, Fr.Criticality.ignore(), G.Cause.write(Ngap.misc(misc), 0n, []))])

def NgSetup.answer(cfg: S.Cfg, supported: Bool) -> B.Bytes():
  match supported:
    case True{}:
      NgSetup.response(cfg)
    case False{}:
      NgSetup.failure(G.CauseMisc.unknown_PLMN_or_SNPN())

def NgSetup.reply(config: Maybe<&2, S.Cfg>, v: V.NGSetupRequest.View) -> B.Bytes():
  match config:
    case None{}:
      NgSetup.failure(G.CauseMisc.unspecified())
    case Some{+cfg}:
      match v:
        case V.NGSetupRequest.View{globalrannodeid, supportedtalist, defaultpagingdrx}:
          NgSetup.answer(cfg, Ta.supported(S.Cfg.plmn(cfg), S.Cfg.tac(cfg), supportedtalist))

def Ngap.is_procedure(kind: Nat, code: Nat, k: Nat, c: Nat) -> Bool:
  Bool.and(Nat.is_eq(kind, k), Nat.is_eq(code, c))

# What the laws ask of a reply: whether an action carries an NG Setup Response,
# and whether a request's supported TA list names the configured PLMN and TAC.
# A PDU's first two octets are its kind (in the top bits) and procedure code.
def Ngap.header_is(bs: B.Bytes(), +k: U32, +c: U32) -> Bool:
  match bs:
    case b0 <> b1 <> rest:
      Bool.and(U32.is_eq(b0, k), U32.is_eq(b1, c))
    case _:
      False{}

def Ngap.is_ng_setup_response(a: F.Action) -> Bool:
  match a:
    case F.NgapSend{assoc, stream, len, bytes}:
      Ngap.header_is(bytes, 32, 21)
    case _:
      False{}

def Ngap.any_ng_setup_response(actions: List<&2, F.Action>) -> Bool:
  match actions:
    case Nil{}:
      False{}
    case a <> more:
      Bool.or(Ngap.is_ng_setup_response(a), Ngap.any_ng_setup_response(more))

def NgSetup.supported_view(config: Maybe<&2, S.Cfg>, v: V.NGSetupRequest.View) -> Bool:
  match config:
    case None{}:
      False{}
    case Some{+cfg}:
      match v:
        case V.NGSetupRequest.View{globalrannodeid, supportedtalist, defaultpagingdrx}:
          Ta.supported(S.Cfg.plmn(cfg), S.Cfg.tac(cfg), supportedtalist)

def NgSetup.supported_of_view(config: Maybe<&2, S.Cfg>, r: Result<&2, &2, B.Err, V.NGSetupRequest.View>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{v}:
      NgSetup.supported_view(config, v)

def NgSetup.supported_d1(config: Maybe<&2, S.Cfg>, ies: List<&2, Fr.Ie>, ok: Bool) -> Bool:
  match ok:
    case True{}:
      NgSetup.supported_of_view(config, V.NGSetupRequest.view(ies))
    case False{}:
      False{}

def NgSetup.supported_dispatch(config: Maybe<&2, S.Cfg>, kind: Nat, code: Nat, ies: List<&2, Fr.Ie>) -> Bool:
  NgSetup.supported_d1(config, ies, Ngap.is_procedure(kind, code, 0n, 21n))

def NgSetup.supported_ies(config: Maybe<&2, S.Cfg>, kind: Nat, code: Nat, r: Ap.Rd(List<&2, Fr.Ie>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(ies, c)}:
      NgSetup.supported_dispatch(config, kind, code, ies)

def NgSetup.supported_pdu(config: Maybe<&2, S.Cfg>, r: Result<&2, &2, B.Err, Fr.Pdu>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{Fr.Pdu{kind, code, crit, value}}:
      NgSetup.supported_ies(config, U32.to_nat(kind), U32.to_nat(code), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}))

def NgSetup.supported_request(config: Maybe<&2, S.Cfg>, bytes: B.Bytes()) -> Bool:
  NgSetup.supported_pdu(config, Fr.Pdu.read(bytes))

# UE-associated signalling
# ------------------------

def Ngap.nas_cause(index: U32) -> G.Cause:
  G.Cause_nas{Ap.Root{index}}

def Ngap.radio_cause(index: U32) -> G.Cause:
  G.Cause_radioNetwork{Ap.Root{index}}

# An NGAP id below 2^32 as the minimal octets its INTEGER type carries, and back.
def Ngap.strip(bs: B.Bytes()) -> B.Bytes():
  match bs:
    case 0 <> b <> rest:
      Ngap.strip(b <> rest)
    case _:
      bs

def Ngap.big(v: U32) -> B.Bytes():
  Ngap.strip(B.write_u32(v, []))

def Ngap.of_big_go(bs: B.Bytes(), acc: U32) -> U32:
  match bs:
    case Nil{}:
      acc
    case b <> rest:
      Ngap.of_big_go(rest, B.cat8(b, acc))

def Ngap.of_big(bs: B.Bytes()) -> U32:
  Ngap.of_big_go(bs, 0)

def Ngap.dl_nas_transport(key: U32, ran_id: B.Bytes(), nas: B.Bytes()) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.initiating(), 4, Fr.Criticality.ignore(), [Ngap.ie(10, Fr.Criticality.reject(), G.AMF_UE_NGAP_ID.write(Ngap.big(key), 0n, [])), Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran_id, 0n, [])), Ngap.ie(38, Fr.Criticality.reject(), G.NAS_PDU.write(nas, 0n, []))])

def Ngap.release_command(key: U32, ran_id: B.Bytes(), cause: G.Cause) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.initiating(), 41, Fr.Criticality.reject(), [Ngap.ie(114, Fr.Criticality.reject(), G.UE_NGAP_IDs.write(G.UE_NGAP_IDs_uE_NGAP_ID_pair{G.UE_NGAP_ID_pair{Ngap.big(key), ran_id, None{}}}, 0n, [])), Ngap.ie(15, Fr.Criticality.ignore(), G.Cause.write(cause, 0n, []))])

# The UE security capability IE (TS 24.501 §9.11.3.54: 5G EA, 5G IA, EPS EEA,
# EPS EIA octets, the first bit algorithm 0) as NGAP bit strings, whose first
# bit is algorithm 1 (TS 38.413 §9.3.1.86).
def Ngap.head0(bs: B.Bytes()) -> U32:
  match bs:
    case Nil{}:
      0
    case b <> rest:
      b

def Ngap.cap_byte(caps: B.Bytes(), n: Nat) -> U32:
  Ngap.head0(List.drop(&2, U32, caps, n))

def Ngap.alg_bits(b: U32) -> Ap.Bits():
  Ap.unpack([U32.and(224, U32.shln(b, 1n)), 0])

def Ngap.ue_caps(+caps: B.Bytes()) -> G.UESecurityCapabilities:
  G.UESecurityCapabilities{Ngap.alg_bits(Ngap.cap_byte(caps, 0n)), Ngap.alg_bits(Ngap.cap_byte(caps, 1n)), Ngap.alg_bits(Ngap.cap_byte(caps, 2n)), Ngap.alg_bits(Ngap.cap_byte(caps, 3n)), None{}}

def Ngap.ics_request(key: U32, ran_id: B.Bytes(), +cfg: S.Cfg, caps: B.Bytes(), k_gnb: B.Bytes(), nas: B.Bytes()) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.initiating(), 14, Fr.Criticality.reject(), [Ngap.ie(10, Fr.Criticality.reject(), G.AMF_UE_NGAP_ID.write(Ngap.big(key), 0n, [])), Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran_id, 0n, [])), Ngap.ie(28, Fr.Criticality.reject(), G.GUAMI.write(NgSetup.guami(cfg), 0n, [])), Ngap.ie(0, Fr.Criticality.reject(), G.AllowedNSSAI.write([G.AllowedNSSAI_Item{G.S_NSSAI{S.Cfg.sst(cfg), None{}, None{}}, None{}}], 0n, [])), Ngap.ie(119, Fr.Criticality.reject(), G.UESecurityCapabilities.write(Ngap.ue_caps(caps), 0n, [])), Ngap.ie(94, Fr.Criticality.reject(), G.SecurityKey.write(Ap.unpack(k_gnb), 0n, [])), Ngap.ie(38, Fr.Criticality.ignore(), G.NAS_PDU.write(nas, 0n, []))])

# What a UE procedure asks for, rendered to frame actions at the boundary.
type Act is Data:
  DlNas{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), nas: B.Bytes()}
  Ics{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), cfg: S.Cfg, caps: B.Bytes(), k_gnb: B.Bytes(), nas: B.Bytes()}
  Release{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), cause: G.Cause}
  ErrInd{assoc: U32, cause: G.Cause}
  Pfcp{bytes: B.Bytes()}
  Note{level: F.Level, text: String}
  TimerStart{timer: U32, ms: U32}
  TimerCancel{timer: U32}

# A procedure answers with a transaction on the state and its actions.
def GOut() -> Data:
  Sigma<&2, &2, S.Tx, _ => List<&2, Act>>

def Act.render(a: Act) -> F.Action:
  match a:
    case DlNas{assoc, stream, key, ran_id, nas}:
      Ngap.send(assoc, stream, Ngap.dl_nas_transport(key, ran_id, nas))
    case Ics{assoc, stream, key, ran_id, cfg, caps, k_gnb, nas}:
      Ngap.send(assoc, stream, Ngap.ics_request(key, ran_id, cfg, caps, k_gnb, nas))
    case Release{assoc, stream, key, ran_id, cause}:
      Ngap.send(assoc, stream, Ngap.release_command(key, ran_id, cause))
    case ErrInd{assoc, cause}:
      Ngap.error_indication(assoc, cause)
    case Pfcp{bytes}:
      F.Action.pfcp_make(bytes)
    case Note{level, text}:
      F.Action.log_make(level, text)
    case TimerStart{timer, ms}:
      F.TimerStart{timer, ms}
    case TimerCancel{timer}:
      F.TimerCancel{timer}

def Acts.render(acts: List<&2, Act>) -> List<&2, F.Action>:
  match acts:
    case Nil{}:
      []
    case a <> more:
      Act.render(a) <> Acts.render(more)

def render_out(st: S.State, o: GOut()) -> S.Out():
  match o:
    case (tx, acts):
      (S.Tx.apply(tx, st), Acts.render(acts))

def Ngap.bad_pdu(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.protocol(G.CauseProtocol.transfer_syntax_error())}, Note{F.Warn{}, "NGAP: PDU rejected, transfer syntax error"}]

def Ngap.bad_view(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.protocol(G.CauseProtocol.abstract_syntax_error_reject())}, Note{F.Warn{}, "NGAP: message rejected, abstract syntax error"}]

def Ngap.unhandled(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())}, Note{F.Warn{}, "NGAP: message not handled"}]

def Ngap.bad_nas(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.protocol(G.CauseProtocol.semantic_error())}, Note{F.Warn{}, "NGAP: NAS message not understood, no context created"}]

def Ngap.unknown_ue(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.radio_cause(G.CauseRadioNetwork.unknown_local_UE_NGAP_ID())}, Note{F.Warn{}, "NGAP: UE-associated message for a UE this association does not own"}]

def NgSetup.of_view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.NGSetupRequest.View>) -> S.Out():
  match r:
    case Fail{e}:
      (st, Acts.render(Ngap.bad_view(assoc)))
    case Done{v}:
      (st, [Ngap.send(assoc, 0, NgSetup.reply(S.State.config(st), v))])
