import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../state.bend as S

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
def Ngap.bad_pdu(assoc: U32) -> List<&2, F.Action>:
  [Ngap.error_indication(assoc, Ngap.protocol(G.CauseProtocol.transfer_syntax_error())), F.Action.log_make(F.Warn{}, "NGAP: PDU rejected, transfer syntax error")]

def Ngap.bad_view(assoc: U32) -> List<&2, F.Action>:
  [Ngap.error_indication(assoc, Ngap.protocol(G.CauseProtocol.abstract_syntax_error_reject())), F.Action.log_make(F.Warn{}, "NGAP: message rejected, abstract syntax error")]

def Ngap.unhandled(assoc: U32) -> List<&2, F.Action>:
  [Ngap.error_indication(assoc, Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())), F.Action.log_make(F.Warn{}, "NGAP: message not handled")]

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

def NgSetup.of_view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.NGSetupRequest.View>) -> S.Out():
  match r:
    case Fail{e}:
      (st, Ngap.bad_view(assoc))
    case Done{v}:
      (st, [Ngap.send(assoc, 0, NgSetup.reply(S.State.config(st), v))])

def Ngap.is_procedure(kind: Nat, code: Nat, k: Nat, c: Nat) -> Bool:
  Bool.and(Nat.is_eq(kind, k), Nat.is_eq(code, c))

# What the laws ask of a reply: whether an action carries an NG Setup Response,
# and whether a request's supported TA list names the configured PLMN and TAC.
def Ngap.pdu_is(kind: Nat, code: Nat, r: Result<&2, &2, B.Err, Fr.Pdu>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{Fr.Pdu{k, c, crit, value}}:
      Bool.and(Nat.is_eq(U32.to_nat(k), kind), Nat.is_eq(U32.to_nat(c), code))

def Ngap.is_ng_setup_response(a: F.Action) -> Bool:
  match a:
    case F.NgapSend{assoc, stream, len, bytes}:
      Ngap.pdu_is(1n, 21n, Fr.Pdu.read(bytes))
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

# Incoming PDUs
# -------------

# Procedures are told apart by comparing the PDU kind and procedure code in
# turn, so that a proof can follow each branch.
def Ngap.d1(st: S.State, +assoc: U32, stream: U32, ies: List<&2, Fr.Ie>, ok: Bool) -> S.Out():
  match ok:
    case True{}:
      NgSetup.of_view(st, assoc, V.NGSetupRequest.view(ies))
    case False{}:
      (st, Ngap.unhandled(assoc))

def Ngap.dispatch(st: S.State, +assoc: U32, stream: U32, kind: Nat, code: Nat, ies: List<&2, Fr.Ie>) -> S.Out():
  Ngap.d1(st, assoc, stream, ies, Ngap.is_procedure(kind, code, 0n, 21n))

def Ngap.of_ies(st: S.State, +assoc: U32, stream: U32, kind: Nat, code: Nat, r: Ap.Rd(List<&2, Fr.Ie>)) -> S.Out():
  match r:
    case Fail{e}:
      (st, Ngap.bad_pdu(assoc))
    case Done{(ies, c)}:
      Ngap.dispatch(st, assoc, stream, kind, code, ies)

def Ngap.of_pdu(st: S.State, +assoc: U32, stream: U32, r: Result<&2, &2, B.Err, Fr.Pdu>) -> S.Out():
  match r:
    case Fail{e}:
      (st, Ngap.bad_pdu(assoc))
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Ngap.of_ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}))

def Ngap.data(st: S.State, +assoc: U32, stream: U32, bytes: B.Bytes()) -> S.Out():
  Ngap.of_pdu(st, assoc, stream, Fr.Pdu.read(bytes))
