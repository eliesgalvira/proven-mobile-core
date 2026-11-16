import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../nas/security.bend as Sec
import ../nas/ie.bend as I
import ../nas/mm.bend as Mm
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
  Ngap.send(assoc, 0, Ngap.pdu(Fr.Pdu.initiating(), G.Proc.ErrorIndication(), Fr.Criticality.ignore(), [Ngap.ie(G.Id.Cause(), Fr.Criticality.ignore(), G.Cause.write(cause, 0n, []))]))

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
  Ngap.pdu(Fr.Pdu.successful(), G.Proc.NGSetup(), Fr.Criticality.reject(), [Ngap.ie(G.Id.AMFName(), Fr.Criticality.reject(), G.AMFName.write(S.Cfg.name(cfg), 0n, [])), Ngap.ie(G.Id.ServedGUAMIList(), Fr.Criticality.reject(), G.ServedGUAMIList.write([G.ServedGUAMIItem{NgSetup.guami(cfg), None{}, None{}}], 0n, [])), Ngap.ie(G.Id.RelativeAMFCapacity(), Fr.Criticality.ignore(), G.RelativeAMFCapacity.write(255, 0n, [])), Ngap.ie(G.Id.PLMNSupportList(), Fr.Criticality.reject(), G.PLMNSupportList.write([G.PLMNSupportItem{S.Cfg.plmn(cfg), NgSetup.slices(cfg), None{}}], 0n, []))])

def NgSetup.failure(misc: U32) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.unsuccessful(), G.Proc.NGSetup(), Fr.Criticality.reject(), [Ngap.ie(G.Id.Cause(), Fr.Criticality.ignore(), G.Cause.write(Ngap.misc(misc), 0n, []))])

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

def Ngap.is_procedure(kind: Nat, code: Nat, k: U32, c: U32) -> Bool:
  Bool.and(Nat.is_eq(kind, U32.to_nat(k)), Nat.is_eq(code, U32.to_nat(c)))

# The messages Route tells apart, by PDU kind and procedure code.
def Ngap.is_ng_setup(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.initiating(), G.Proc.NGSetup())

def Ngap.is_initial_ue_message(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.initiating(), G.Proc.InitialUEMessage())

def Ngap.is_uplink_nas_transport(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.initiating(), G.Proc.UplinkNASTransport())

def Ngap.is_initial_context_setup_response(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.successful(), G.Proc.InitialContextSetup())

def Ngap.is_ue_context_release_request(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.initiating(), G.Proc.UEContextReleaseRequest())

def Ngap.is_ue_context_release_complete(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.successful(), G.Proc.UEContextRelease())

def Ngap.is_pdu_session_resource_setup_response(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.successful(), G.Proc.PDUSessionResourceSetup())

def Ngap.is_path_switch_request(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.initiating(), G.Proc.PathSwitchRequest())

def Ngap.is_handover_required(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.initiating(), G.Proc.HandoverPreparation())

def Ngap.is_handover_request_acknowledge(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.successful(), G.Proc.HandoverResourceAllocation())

def Ngap.is_handover_failure(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.unsuccessful(), G.Proc.HandoverResourceAllocation())

def Ngap.is_handover_notify(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.initiating(), G.Proc.HandoverNotification())

def Ngap.is_handover_cancel(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.initiating(), G.Proc.HandoverCancel())

def Ngap.is_uplink_ran_status_transfer(+kind: Nat, +code: Nat) -> Bool:
  Ngap.is_procedure(kind, code, Fr.Pdu.initiating(), G.Proc.UplinkRANStatusTransfer())

# What the laws ask of a reply: whether an action carries an NG Setup Response,
# and whether a request's supported TA list names the configured PLMN and TAC.
# A PDU's first two octets are its kind (in the top bits) and procedure code.
def Ngap.header_is(bs: B.Bytes(), +k: U32, +c: U32) -> Bool:
  match bs:
    case b0 <> b1 <> rest:
      Bool.and(U32.is_eq(b0, k), U32.is_eq(b1, c))
    case _:
      False{}

# The gNB's Global RAN Node ID, as NGAP encodes it.
def NgSetup.node(v: V.NGSetupRequest.View) -> B.Bytes():
  match v:
    case V.NGSetupRequest.View{globalrannodeid, supportedtalist, defaultpagingdrx}:
      Ap.pack(G.GlobalRANNodeID.write(globalrannodeid, 0n, []))

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
  NgSetup.supported_d1(config, ies, Ngap.is_ng_setup(kind, code))

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

def Ngap.key_if(bs: B.Bytes(), fits: Bool) -> Maybe<&2, U32>:
  match fits:
    case True{}:
      Some{Ngap.of_big(bs)}
    case False{}:
      None{}

# The context key an AMF-UE-NGAP-ID names: none at 2^32 or above (five
# octets, ngap.no_big_nat), which is never folded into 32 bits.
def Ngap.ue_key(+bs: B.Bytes()) -> Maybe<&2, U32>:
  Ngap.key_if(bs, Nat.is_le(List.length(&2, U32, bs), 4n))

def Ngap.dl_nas_transport(key: U32, ran_id: B.Bytes(), nas: B.Bytes()) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.initiating(), G.Proc.DownlinkNASTransport(), Fr.Criticality.ignore(), [Ngap.ie(G.Id.AMF_UE_NGAP_ID(), Fr.Criticality.reject(), G.AMF_UE_NGAP_ID.write(Ngap.big(key), 0n, [])), Ngap.ie(G.Id.RAN_UE_NGAP_ID(), Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran_id, 0n, [])), Ngap.ie(G.Id.NAS_PDU(), Fr.Criticality.reject(), G.NAS_PDU.write(nas, 0n, []))])

# UE Context Release Command, naming the UE by both IDs or, to a gNB that has
# not given its RAN-UE-NGAP-ID, by AMF-UE-NGAP-ID alone.
def Ngap.release_command(ids: G.UE_NGAP_IDs, cause: G.Cause) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.initiating(), G.Proc.UEContextRelease(), Fr.Criticality.reject(), [Ngap.ie(G.Id.UE_NGAP_IDs(), Fr.Criticality.reject(), G.UE_NGAP_IDs.write(ids, 0n, [])), Ngap.ie(G.Id.Cause(), Fr.Criticality.ignore(), G.Cause.write(cause, 0n, []))])

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

# T3570, T3560 and T3550 all default to 6 s; the wait for UE Context Release
# Complete is bounded the same way.
def Ue.guard_ms() -> U32:
  6000

# The UE security capability of the Registration Request held for the UE.
def Ue.caps_of(r: Result<&2, &2, B.Err, Mm.Mm>) -> B.Bytes():
  match r:
    case Fail{e}:
      []
    case Done{Mm.Mm{mt, fields, opts}}:
      I.Bytes.or(I.Opts.find(I.Iei.ue_security_capability(), opts), [])

def Ue.caps(ue: S.Ue) -> B.Bytes():
  Ue.caps_of(Mm.Mm.read(S.Ue.reg(ue)))

def Ngap.ics_request(key: U32, ran_id: B.Bytes(), +cfg: S.Cfg, caps: B.Bytes(), k_gnb: B.Bytes(), nas: B.Bytes()) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.initiating(), G.Proc.InitialContextSetup(), Fr.Criticality.reject(), [Ngap.ie(G.Id.AMF_UE_NGAP_ID(), Fr.Criticality.reject(), G.AMF_UE_NGAP_ID.write(Ngap.big(key), 0n, [])), Ngap.ie(G.Id.RAN_UE_NGAP_ID(), Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran_id, 0n, [])), Ngap.ie(G.Id.GUAMI(), Fr.Criticality.reject(), G.GUAMI.write(NgSetup.guami(cfg), 0n, [])), Ngap.ie(G.Id.AllowedNSSAI(), Fr.Criticality.reject(), G.AllowedNSSAI.write([G.AllowedNSSAI_Item{G.S_NSSAI{S.Cfg.sst(cfg), None{}, None{}}, None{}}], 0n, [])), Ngap.ie(G.Id.UESecurityCapabilities(), Fr.Criticality.reject(), G.UESecurityCapabilities.write(Ngap.ue_caps(caps), 0n, [])), Ngap.ie(G.Id.SecurityKey(), Fr.Criticality.reject(), G.SecurityKey.write(Ap.unpack(k_gnb), 0n, [])), Ngap.ie(G.Id.NAS_PDU(), Fr.Criticality.ignore(), G.NAS_PDU.write(nas, 0n, []))])

# 1 Gbit/s, the aggregate maximum bit rate of a UE and of its one session.
def Ngap.gbps() -> G.BitRate():
  Ap.BRoot{[59, 154, 202, 0]}

def Ngap.ue_ambr() -> Ap.Bits():
  G.UEAggregateMaximumBitRate.write(G.UEAggregateMaximumBitRate{Ngap.gbps(), Ngap.gbps(), None{}}, 0n, [])

# PDU Session Resource Setup Request: one session, its NAS-PDU and transfer, the UE's AMBR.
def Ngap.pdu_setup(key: U32, ran_id: B.Bytes(), psi: U32, sst: B.Bytes(), nas: B.Bytes(), transfer: B.Bytes()) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.initiating(), G.Proc.PDUSessionResourceSetup(), Fr.Criticality.reject(), [Ngap.ie(G.Id.AMF_UE_NGAP_ID(), Fr.Criticality.reject(), G.AMF_UE_NGAP_ID.write(Ngap.big(key), 0n, [])), Ngap.ie(G.Id.RAN_UE_NGAP_ID(), Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran_id, 0n, [])), Ngap.ie(G.Id.PDUSessionResourceSetupListSUReq(), Fr.Criticality.reject(), G.PDUSessionResourceSetupListSUReq.write([G.PDUSessionResourceSetupItemSUReq{psi, Some{nas}, G.S_NSSAI{sst, None{}, None{}}, transfer, None{}}], 0n, [])), Ngap.ie(G.Id.UEAggregateMaximumBitRate(), Fr.Criticality.ignore(), Ngap.ue_ambr())])

# Path Switch (§8.4.4)
# --------------------

# The PDU sessions a Path Switch Request Acknowledge or Failure releases, each
# with its cause.
def Ngap.unsuccessful(cause: G.Cause) -> B.Bytes():
  Ap.pack(G.PathSwitchRequestUnsuccessfulTransfer.write(G.PathSwitchRequestUnsuccessfulTransfer{cause, None{}}, 0n, []))

def Ngap.released_ack(psis: List<&2, U32>, +cause: G.Cause) -> G.PDUSessionResourceReleasedListPSAck():
  match psis:
    case Nil{}:
      []
    case p <> more:
      G.PDUSessionResourceReleasedItemPSAck{p, Ngap.unsuccessful(cause), None{}} <> Ngap.released_ack(more, cause)

def Ngap.released_fail(psis: List<&2, U32>, +cause: G.Cause) -> G.PDUSessionResourceReleasedListPSFail():
  match psis:
    case Nil{}:
      []
    case p <> more:
      G.PDUSessionResourceReleasedItemPSFail{p, Ngap.unsuccessful(cause), None{}} <> Ngap.released_fail(more, cause)

# The uplink tunnel stays, so each switched session's transfer is empty.
def Ngap.switched(psis: List<&2, U32>) -> G.PDUSessionResourceSwitchedList():
  match psis:
    case Nil{}:
      []
    case p <> more:
      G.PDUSessionResourceSwitchedItem{p, Ap.pack(G.PathSwitchRequestAcknowledgeTransfer.write(G.PathSwitchRequestAcknowledgeTransfer{None{}, None{}, None{}}, 0n, [])), None{}} <> Ngap.switched(more)

def Ngap.released_ies(psis: List<&2, U32>) -> List<&2, Fr.Ie>:
  match psis:
    case Nil{}:
      []
    case p <> more:
      [Ngap.ie(G.Id.PDUSessionResourceReleasedListPSAck(), Fr.Criticality.ignore(), G.PDUSessionResourceReleasedListPSAck.write(Ngap.released_ack(p <> more, Ngap.radio_cause(G.CauseRadioNetwork.unspecified())), 0n, []))]

def Ngap.security_context(c: S.Nh) -> G.SecurityContext:
  match c:
    case S.Nh{k_amf, nh, ncc}:
      G.SecurityContext{ncc, Ap.unpack(nh), None{}}

def Ngap.allowed_nssai(sst: B.Bytes()) -> Ap.Bits():
  G.AllowedNSSAI.write([G.AllowedNSSAI_Item{G.S_NSSAI{sst, None{}, None{}}, None{}}], 0n, [])

# Path Switch Request Acknowledge: the UE security capabilities the AMF holds,
# the next {NH, NCC}, the sessions switched and those released, the slice.
def Ngap.path_switch_ack(key: U32, ran_id: B.Bytes(), +caps: B.Bytes(), nh: S.Nh, switched: List<&2, U32>, released: List<&2, U32>, sst: B.Bytes()) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.successful(), G.Proc.PathSwitchRequest(), Fr.Criticality.reject(), List.append(&2, Fr.Ie, [Ngap.ie(G.Id.AMF_UE_NGAP_ID(), Fr.Criticality.ignore(), G.AMF_UE_NGAP_ID.write(Ngap.big(key), 0n, [])), Ngap.ie(G.Id.RAN_UE_NGAP_ID(), Fr.Criticality.ignore(), G.RAN_UE_NGAP_ID.write(ran_id, 0n, [])), Ngap.ie(G.Id.UESecurityCapabilities(), Fr.Criticality.reject(), G.UESecurityCapabilities.write(Ngap.ue_caps(caps), 0n, [])), Ngap.ie(G.Id.SecurityContext(), Fr.Criticality.reject(), G.SecurityContext.write(Ngap.security_context(nh), 0n, [])), Ngap.ie(G.Id.PDUSessionResourceSwitchedList(), Fr.Criticality.ignore(), G.PDUSessionResourceSwitchedList.write(Ngap.switched(switched), 0n, []))], List.append(&2, Fr.Ie, Ngap.released_ies(released), [Ngap.ie(G.Id.AllowedNSSAI(), Fr.Criticality.reject(), Ngap.allowed_nssai(sst))])))

# Path Switch Request Failure: the PDU sessions named, released with a cause.
def Ngap.path_switch_failure(amf: B.Bytes(), ran_id: B.Bytes(), psis: List<&2, U32>, cause: G.Cause) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.unsuccessful(), G.Proc.PathSwitchRequest(), Fr.Criticality.reject(), [Ngap.ie(G.Id.AMF_UE_NGAP_ID(), Fr.Criticality.ignore(), G.AMF_UE_NGAP_ID.write(amf, 0n, [])), Ngap.ie(G.Id.RAN_UE_NGAP_ID(), Fr.Criticality.ignore(), G.RAN_UE_NGAP_ID.write(ran_id, 0n, [])), Ngap.ie(G.Id.PDUSessionResourceReleasedListPSFail(), Fr.Criticality.ignore(), G.PDUSessionResourceReleasedListPSFail.write(Ngap.released_fail(psis, cause), 0n, []))])

# What a step asks for, rendered to frame actions for the edge (Kernel.frames). Each
# action names the UE context it is built from, if any: the AMF-UE-NGAP-ID of
# a UE-associated NGAP message, the UE of a PFCP session message or a guard. A
# Path Switch Request Failure that echoes the request's IDs names none. A
# UE-associated message of the N2 handover goes out built (UeSend).
type Act is Data:
  DlNas{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), nas: B.Bytes()}
  Ics{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), cfg: S.Cfg, caps: B.Bytes(), k_gnb: B.Bytes(), nas: B.Bytes()}
  PduSetup{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), psi: U32, sst: B.Bytes(), nas: B.Bytes(), transfer: B.Bytes()}
  Release{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), cause: G.Cause}
  SwitchAck{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), caps: B.Bytes(), nh: S.Nh, switched: List<&2, U32>, released: List<&2, U32>, sst: B.Bytes()}
  SwitchFail{assoc: U32, stream: U32, ue: Maybe<&2, U32>, amf: B.Bytes(), ran_id: B.Bytes(), psis: List<&2, U32>, cause: G.Cause}
  UeSend{assoc: U32, stream: U32, key: U32, bytes: B.Bytes()}
  ErrInd{assoc: U32, cause: G.Cause}
  Setup{assoc: U32, answer: B.Bytes()}
  Pfcp{ue: Maybe<&2, U32>, bytes: B.Bytes()}
  Note{level: F.Level, text: String}
  TimerStart{ue: Maybe<&2, U32>, timer: U32, ms: U32}
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
    case PduSetup{assoc, stream, key, ran_id, psi, sst, nas, transfer}:
      Ngap.send(assoc, stream, Ngap.pdu_setup(key, ran_id, psi, sst, nas, transfer))
    case Release{assoc, stream, key, ran_id, cause}:
      Ngap.send(assoc, stream, Ngap.release_command(G.UE_NGAP_IDs_uE_NGAP_ID_pair{G.UE_NGAP_ID_pair{Ngap.big(key), ran_id, None{}}}, cause))
    case SwitchAck{assoc, stream, key, ran_id, caps, nh, switched, released, sst}:
      Ngap.send(assoc, stream, Ngap.path_switch_ack(key, ran_id, caps, nh, switched, released, sst))
    case SwitchFail{assoc, stream, ue, amf, ran_id, psis, cause}:
      Ngap.send(assoc, stream, Ngap.path_switch_failure(amf, ran_id, psis, cause))
    case UeSend{assoc, stream, key, bytes}:
      Ngap.send(assoc, stream, bytes)
    case ErrInd{assoc, cause}:
      Ngap.error_indication(assoc, cause)
    case Setup{assoc, answer}:
      Ngap.send(assoc, 0, answer)
    case Pfcp{ue, bytes}:
      F.Action.pfcp_make(bytes)
    case Note{level, text}:
      F.Action.log_make(level, text)
    case TimerStart{ue, timer, ms}:
      F.TimerStart{timer, ms}
    case TimerCancel{timer}:
      F.TimerCancel{timer}

def Act.ue(a: Act) -> Maybe<&2, U32>:
  match a:
    case DlNas{assoc, stream, key, ran_id, nas}:
      Some{key}
    case Ics{assoc, stream, key, ran_id, cfg, caps, k_gnb, nas}:
      Some{key}
    case PduSetup{assoc, stream, key, ran_id, psi, sst, nas, transfer}:
      Some{key}
    case Release{assoc, stream, key, ran_id, cause}:
      Some{key}
    case SwitchAck{assoc, stream, key, ran_id, caps, nh, switched, released, sst}:
      Some{key}
    case SwitchFail{assoc, stream, ue, amf, ran_id, psis, cause}:
      ue
    case UeSend{assoc, stream, key, bytes}:
      Some{key}
    case Pfcp{ue, bytes}:
      ue
    case TimerStart{ue, timer, ms}:
      ue
    case _:
      None{}

# Some action stops the timer k.
def Act.stops(+k: U32, a: Act) -> Bool:
  match a:
    case TimerCancel{t}:
      U32.is_eq(t, k)
    case _:
      False{}

# Some action starts the timer k.
def Act.starts(+k: U32, a: Act) -> Bool:
  match a:
    case TimerStart{ue, t, ms}:
      U32.is_eq(t, k)
    case _:
      False{}

def Acts.starts(+k: U32, acts: List<&2, Act>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case a <> more:
      Bool.or(Act.starts(k, a), Acts.starts(k, more))

def Acts.stops(+k: U32, acts: List<&2, Act>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case a <> more:
      Bool.or(Act.stops(k, a), Acts.stops(k, more))

# Timer k runs once the actions are done: the last of them that starts or
# stops it starts it.
def Acts.runs(+k: U32, acts: List<&2, Act>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case a <> +more:
      Bool.or(Acts.runs(k, more), Bool.and(Act.starts(k, a), Bool.not(Acts.stops(k, more))))

# Some action sends the PFCP message bytes.
def Act.sends(+bytes: B.Bytes(), a: Act) -> Bool:
  match a:
    case Pfcp{ue, b}:
      B.bytes_eq(b, bytes)
    case _:
      False{}

def Acts.sends(+bytes: B.Bytes(), acts: List<&2, Act>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case a <> more:
      Bool.or(Act.sends(bytes, a), Acts.sends(bytes, more))

# No action is built from the UE context keyed k.
def Acts.spare(+k: U32, acts: List<&2, Act>) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case a <> more:
      Bool.and(Bool.not(S.Maybe.same_u32(Act.ue(a), Some{k})), Acts.spare(k, more))

def Acts.render(acts: List<&2, Act>) -> List<&2, F.Action>:
  match acts:
    case Nil{}:
      []
    case a <> more:
      Act.render(a) <> Acts.render(more)

def Ngap.is_ng_setup_response(a: Act) -> Bool:
  match a:
    case Setup{assoc, answer}:
      Ngap.header_is(answer, 32, G.Proc.NGSetup())
    case _:
      False{}

def Ngap.any_ng_setup_response(actions: List<&2, Act>) -> Bool:
  match actions:
    case Nil{}:
      False{}
    case a <> more:
      Bool.or(Ngap.is_ng_setup_response(a), Ngap.any_ng_setup_response(more))

def Ngap.is_switch_failure(a: Act) -> Bool:
  match a:
    case SwitchFail{assoc, stream, ue, amf, ran_id, psis, cause}:
      True{}
    case _:
      False{}

def Ngap.any_switch_failure(actions: List<&2, Act>) -> Bool:
  match actions:
    case Nil{}:
      False{}
    case a <> more:
      Bool.or(Ngap.is_switch_failure(a), Ngap.any_switch_failure(more))

# What one step answers: the next state and the actions to perform.
def Step() -> Data:
  Sigma<&2, &2, S.State, _ => List<&2, Act>>

def Step.state(o: Step()) -> S.State:
  match o:
    case (st, acts):
      st

def Step.acts(o: Step()) -> List<&2, Act>:
  match o:
    case (st, acts):
      acts

# Combining outcomes: an action in front, actions after, two outcomes in order, a note alone.
def Out.prepend(a: Act, o: GOut()) -> GOut():
  match o:
    case (tx, acts):
      (tx, a <> acts)

def Out.also(o: GOut(), more: List<&2, Act>) -> GOut():
  match o:
    case (tx, acts):
      (tx, List.append(&2, Act, acts, more))

def Out.join_go(ta: S.Tx, aa: List<&2, Act>, b: GOut()) -> GOut():
  match b:
    case (tb, ab):
      (S.Both{ta, tb}, List.append(&2, Act, aa, ab))

def Out.join(a: GOut(), b: GOut()) -> GOut():
  match a:
    case (ta, aa):
      Out.join_go(ta, aa, b)

def Out.tx(o: GOut()) -> S.Tx:
  match o:
    case (tx, acts):
      tx

def Out.acts(o: GOut()) -> List<&2, Act>:
  match o:
    case (tx, acts):
      acts

def Out.warn(why: String) -> GOut():
  (S.Keep{}, [Note{F.Warn{}, why}])

# The guard of the row keyed key stopped, if it has one.
def Guard.cancel(key: U32, g: Maybe<&2, S.Guard>) -> List<&2, Act>:
  match g:
    case None{}:
      []
    case Some{guard}:
      [TimerCancel{key}]

# The guard of every row a step removes from the session table stopped, its
# timer the row's key: whatever forgets a session, no stale timer can reach a
# later session under the same SEID.
def Gone.row(+k: U32, +s: S.Session, kept: Bool) -> List<&2, Act>:
  match kept:
    case True{}:
      []
    case False{}:
      Guard.cancel(k, S.SPhase.guard(S.Session.phase(s)))

def Gone.cancels(before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> List<&2, Act>:
  match before:
    case Nil{}:
      []
    case (+k, +s) <> more:
      List.append(&2, Act, Gone.row(k, s, Tb.Table.has(S.Session, k, after)), Gone.cancels(more, after))

# A transaction that keeps the session table removes no row: nothing to compare.
def Gone.when(keeps: Bool, before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> List<&2, Act>:
  match keeps:
    case True{}:
      []
    case False{}:
      Gone.cancels(before, after)

# The step a procedure's outcome makes from st.
def Step.of(+st: S.State, o: GOut()) -> Step():
  match o:
    case (+tx, acts):
      +st2 = S.Tx.apply(tx, st)
      (st2, List.append(&2, Act, acts, Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(st2))))

# The UE under an AMF-UE-NGAP-ID, if the association owns it under that RAN-UE-NGAP-ID.
def Owner.check(ue: S.Ue, ok: Bool) -> Maybe<&2, S.Ue>:
  match ok:
    case True{}:
      Some{ue}
    case False{}:
      None{}

def Owner.of(m: Maybe<&2, S.Ue>, assoc: U32, ran: B.Bytes()) -> Maybe<&2, S.Ue>:
  match m:
    case None{}:
      None{}
    case Some{+ue}:
      Owner.check(ue, Bool.and(U32.is_eq(S.Ue.assoc(ue), assoc), B.bytes_eq(S.Ue.ran_id(ue), ran)))

# A UE context with its key.
def Keyed() -> Data:
  Sigma<&2, &2, U32, _ => S.Ue>

def Ue.with_key(key: U32, m: Maybe<&2, S.Ue>) -> Maybe<&2, Keyed()>:
  match m:
    case None{}:
      None{}
    case Some{ue}:
      Some{(key, ue)}

# The context under the key an AMF-UE-NGAP-ID names, as find gives it.
def Ue.keyed(m: Maybe<&2, U32>, find: U32 -> Maybe<&2, S.Ue>) -> Maybe<&2, Keyed()>:
  match m:
    case None{}:
      None{}
    case Some{+key}:
      Ue.with_key(key, find(key))

# The outcome for the context found, or none.
def Ue.found(m: Maybe<&2, Keyed()>, none: GOut(), go: U32 -> S.Ue -> GOut()) -> GOut():
  match m:
    case None{}:
      none
    case Some{(key, ue)}:
      go(key, ue)

# A verified NAS message not acted on still moves the uplink COUNT on, so it
# cannot be replayed; the context's phase keeps its shape.
def Out.verified(key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, why: String) -> GOut():
  (S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), ctx)}, [Note{F.Warn{}, why}])

# A protected downlink NAS message to a UE, its context moved on.
def Out.dl(+key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, plain: B.Bytes()) -> GOut():
  +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.Ciphered{}, plain)
  (S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))}, [DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), Sec.Nas.Protected.msg(p)}])

def Ngap.bad_pdu(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.protocol(G.CauseProtocol.transfer_syntax_error())}, Note{F.Warn{}, "NGAP: PDU rejected, transfer syntax error"}]

def Ngap.bad_view(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.protocol(G.CauseProtocol.abstract_syntax_error_reject())}, Note{F.Warn{}, "NGAP: message rejected, abstract syntax error"}]

def Ngap.unhandled(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())}, Note{F.Warn{}, "NGAP: message not handled"}]

def Ngap.bad_nas(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.protocol(G.CauseProtocol.semantic_error())}, Note{F.Warn{}, "NGAP: NAS message not understood, no context created"}]

def Ngap.no_key(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.misc(G.CauseMisc.control_processing_overload())}, Note{F.Warn{}, "NGAP: no AMF-UE-NGAP-ID free, InitialUEMessage refused"}]

def Ngap.unknown_ue(assoc: U32) -> List<&2, Act>:
  [ErrInd{assoc, Ngap.radio_cause(G.CauseRadioNetwork.unknown_local_UE_NGAP_ID())}, Note{F.Warn{}, "NGAP: UE-associated message for a UE this association does not own"}]
