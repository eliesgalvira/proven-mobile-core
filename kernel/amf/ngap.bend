import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../nas/security.bend as Sec
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

# 1 Gbit/s, the aggregate maximum bit rate of a UE and of its one session.
def Ngap.gbps() -> G.BitRate():
  Ap.BRoot{[59, 154, 202, 0]}

def Ngap.ue_ambr() -> Ap.Bits():
  G.UEAggregateMaximumBitRate.write(G.UEAggregateMaximumBitRate{Ngap.gbps(), Ngap.gbps(), None{}}, 0n, [])

# PDU Session Resource Setup Request: one session, its NAS-PDU and transfer, the UE's AMBR.
def Ngap.pdu_setup(key: U32, ran_id: B.Bytes(), psi: U32, sst: B.Bytes(), nas: B.Bytes(), transfer: B.Bytes()) -> B.Bytes():
  Ngap.pdu(Fr.Pdu.initiating(), 29, Fr.Criticality.reject(), [Ngap.ie(10, Fr.Criticality.reject(), G.AMF_UE_NGAP_ID.write(Ngap.big(key), 0n, [])), Ngap.ie(85, Fr.Criticality.reject(), G.RAN_UE_NGAP_ID.write(ran_id, 0n, [])), Ngap.ie(74, Fr.Criticality.reject(), G.PDUSessionResourceSetupListSUReq.write([G.PDUSessionResourceSetupItemSUReq{psi, Some{nas}, G.S_NSSAI{sst, None{}, None{}}, transfer, None{}}], 0n, [])), Ngap.ie(110, Fr.Criticality.ignore(), Ngap.ue_ambr())])

# What a step asks for, rendered to frame actions for the edge (Kernel.frames). Each
# action names the UE context it is built from, if any: the AMF-UE-NGAP-ID of
# a UE-associated NGAP message, the UE of a PFCP session message or a guard.
type Act is Data:
  DlNas{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), nas: B.Bytes()}
  Ics{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), cfg: S.Cfg, caps: B.Bytes(), k_gnb: B.Bytes(), nas: B.Bytes()}
  PduSetup{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), psi: U32, sst: B.Bytes(), nas: B.Bytes(), transfer: B.Bytes()}
  Release{assoc: U32, stream: U32, key: U32, ran_id: B.Bytes(), cause: G.Cause}
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
      Ngap.send(assoc, stream, Ngap.release_command(key, ran_id, cause))
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

def Acts.stops(+k: U32, acts: List<&2, Act>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case a <> more:
      Bool.or(Act.stops(k, a), Acts.stops(k, more))

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
      Ngap.header_is(answer, 32, 21)
    case _:
      False{}

def Ngap.any_ng_setup_response(actions: List<&2, Act>) -> Bool:
  match actions:
    case Nil{}:
      False{}
    case a <> more:
      Bool.or(Ngap.is_ng_setup_response(a), Ngap.any_ng_setup_response(more))

# What one step answers: the next state and the actions to perform.
def Step() -> Data:
  Sigma<&2, &2, S.State, _ => List<&2, Act>>

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

# The step a procedure's outcome makes from st.
def Step.of(+st: S.State, o: GOut()) -> Step():
  match o:
    case (tx, acts):
      +st2 = S.Tx.apply(tx, st)
      (st2, List.append(&2, Act, acts, Gone.cancels(S.State.sessions(st), S.State.sessions(st2))))

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

def NgSetup.of_view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.NGSetupRequest.View>) -> Step():
  match r:
    case Fail{e}:
      (st, Ngap.bad_view(assoc))
    case Done{v}:
      (st, [Setup{assoc, NgSetup.reply(S.State.config(st), v)}])
