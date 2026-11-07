import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../nas/security.bend as Sec
import ../smf/gsm.bend as Gsm
import ../smf/switch.bend as Sw
import ./ngap.bend as N

# N2 handover within one AMF and one UPF (TS 23.502 §4.9.1.3, TS 38.413
# §8.4.1 to §8.4.3 and §8.4.5 to §8.4.7). The target gNB knows the UE by its
# AMF-UE-NGAP-ID too. The UE stays with its owner, the source, until the
# target's Handover Notify. The source speaks for the UE under its owner
# check; the target only for the handover pending to it, and anything else
# it sends names an unknown UE.

# UE-associated signalling to a target that has not answered yet goes on
# stream 1, the first one for it (TS 38.412 §7).
def Ho.stream() -> U32:
  1

def Ho.radio(index: U32) -> G.Cause:
  N.Ngap.radio_cause(index)

# Messages
# --------

def Ho.ids(key: U32, ran: B.Bytes(), +crit: U32) -> List<&2, Fr.Ie>:
  [N.Ngap.ie(G.Id.AMF_UE_NGAP_ID(), crit, G.AMF_UE_NGAP_ID.write(N.Ngap.big(key), 0n, [])), N.Ngap.ie(G.Id.RAN_UE_NGAP_ID(), crit, G.RAN_UE_NGAP_ID.write(ran, 0n, []))]

def Ho.intra() -> Ap.Bits():
  G.HandoverType.write(Ap.Root{G.HandoverType.intra5gs()}, 0n, [])

# DataForwardingNotPossible (id 127): no forwarding tunnel is offered, as
# indirect forwarding is out of scope.
def Ho.no_forwarding() -> Fr.Ie:
  Fr.Ie{127, Fr.Criticality.reject(), [0]}

# Handover Request (§9.2.3.4): the next {NH, NCC}, each session handed over
# with its uplink tunnel, the source's container.
def Ho.request(key: U32, +cfg: S.Cfg, cause: G.Cause, +caps: B.Bytes(), nh: S.Nh, items: G.PDUSessionResourceSetupListHOReq(), container: B.Bytes()) -> B.Bytes():
  N.Ngap.pdu(Fr.Pdu.initiating(), G.Proc.HandoverResourceAllocation(), Fr.Criticality.reject(), [N.Ngap.ie(G.Id.AMF_UE_NGAP_ID(), Fr.Criticality.reject(), G.AMF_UE_NGAP_ID.write(N.Ngap.big(key), 0n, [])), N.Ngap.ie(G.Id.HandoverType(), Fr.Criticality.reject(), Ho.intra()), N.Ngap.ie(G.Id.Cause(), Fr.Criticality.ignore(), G.Cause.write(cause, 0n, [])), N.Ngap.ie(G.Id.UEAggregateMaximumBitRate(), Fr.Criticality.reject(), N.Ngap.ue_ambr()), N.Ngap.ie(G.Id.UESecurityCapabilities(), Fr.Criticality.reject(), G.UESecurityCapabilities.write(N.Ngap.ue_caps(caps), 0n, [])), N.Ngap.ie(G.Id.SecurityContext(), Fr.Criticality.reject(), G.SecurityContext.write(N.Ngap.security_context(nh), 0n, [])), N.Ngap.ie(G.Id.PDUSessionResourceSetupListHOReq(), Fr.Criticality.reject(), G.PDUSessionResourceSetupListHOReq.write(items, 0n, [])), N.Ngap.ie(G.Id.AllowedNSSAI(), Fr.Criticality.reject(), N.Ngap.allowed_nssai(S.Cfg.sst(cfg))), N.Ngap.ie(G.Id.SourceToTarget_TransparentContainer(), Fr.Criticality.reject(), G.SourceToTarget_TransparentContainer.write(container, 0n, [])), N.Ngap.ie(G.Id.GUAMI(), Fr.Criticality.reject(), G.GUAMI.write(N.NgSetup.guami(cfg), 0n, []))])

# The sessions handed over: no forwarding tunnel, so each transfer is empty.
def Ho.handed(ts: List<&2, S.Tunnel>) -> G.PDUSessionResourceHandoverList():
  match ts:
    case Nil{}:
      []
    case S.Tunnel{psi, teid, addr} <> more:
      G.PDUSessionResourceHandoverItem{psi, Ap.pack(G.HandoverCommandTransfer.write(G.HandoverCommandTransfer{None{}, None{}, None{}, None{}}, 0n, [])), None{}} <> Ho.handed(more)

def Ho.handed_ies(ts: List<&2, S.Tunnel>) -> List<&2, Fr.Ie>:
  match ts:
    case Nil{}:
      []
    case t <> more:
      [N.Ngap.ie(G.Id.PDUSessionResourceHandoverList(), Fr.Criticality.ignore(), G.PDUSessionResourceHandoverList.write(Ho.handed(t <> more), 0n, []))]

# Handover Command (§9.2.3.2): the sessions the target admitted, its container.
def Ho.command(key: U32, ran: B.Bytes(), ts: List<&2, S.Tunnel>, container: B.Bytes()) -> B.Bytes():
  N.Ngap.pdu(Fr.Pdu.successful(), G.Proc.HandoverPreparation(), Fr.Criticality.reject(), List.append(&2, Fr.Ie, Ho.ids(key, ran, Fr.Criticality.reject()), N.Ngap.ie(G.Id.HandoverType(), Fr.Criticality.reject(), Ho.intra()) <> List.append(&2, Fr.Ie, Ho.handed_ies(ts), [N.Ngap.ie(G.Id.TargetToSource_TransparentContainer(), Fr.Criticality.reject(), G.TargetToSource_TransparentContainer.write(container, 0n, []))])))

# Handover Preparation Failure (§9.2.3.3) to the UE's owner, the source.
def Ho.preparation_failure(+key: U32, +ue: S.Ue, cause: G.Cause) -> N.Act:
  N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, N.Ngap.pdu(Fr.Pdu.unsuccessful(), G.Proc.HandoverPreparation(), Fr.Criticality.reject(), List.append(&2, Fr.Ie, Ho.ids(key, S.Ue.ran_id(ue), Fr.Criticality.ignore()), [N.Ngap.ie(G.Id.Cause(), Fr.Criticality.ignore(), G.Cause.write(cause, 0n, []))]))}

# Handover Cancel Acknowledge (§9.2.3.12).
def Ho.cancel_ack(key: U32, ran: B.Bytes()) -> B.Bytes():
  N.Ngap.pdu(Fr.Pdu.successful(), G.Proc.HandoverCancel(), Fr.Criticality.reject(), Ho.ids(key, ran, Fr.Criticality.ignore()))

# Downlink RAN Status Transfer (§9.2.3.14): the source's container, relayed.
def Ho.dl_status(key: U32, ran: B.Bytes(), container: G.RANStatusTransfer_TransparentContainer) -> B.Bytes():
  N.Ngap.pdu(Fr.Pdu.initiating(), G.Proc.DownlinkRANStatusTransfer(), Fr.Criticality.ignore(), List.append(&2, Fr.Ie, Ho.ids(key, ran, Fr.Criticality.reject()), [N.Ngap.ie(G.Id.RANStatusTransfer_TransparentContainer(), Fr.Criticality.reject(), G.RANStatusTransfer_TransparentContainer.write(container, 0n, []))]))

# The target released: by AMF-UE-NGAP-ID before it answered, by both IDs after.
def Ho.drop(+key: U32, leg: S.Leg, cause: G.Cause) -> List<&2, N.Act>:
  match leg:
    case S.Asked{t}:
      [N.UeSend{t, Ho.stream(), key, N.Ngap.release_command(G.UE_NGAP_IDs_aMF_UE_NGAP_ID{N.Ngap.big(key)}, cause)}]
    case S.Acked{t, r, s, ts}:
      [N.Release{t, s, key, r, cause}]

# The target of a handover pending, released when the UE is.
def Ho.leg_drop(+key: U32, p: S.Phase, cause: G.Cause) -> List<&2, N.Act>:
  match p:
    case S.Handover{ctx, nh, source, leg}:
      Ho.drop(key, leg, cause)
    case _:
      []

# The UE a message names
# ----------------------

# The UE an AMF-UE-NGAP-ID names, if the association owns it under that RAN-UE-NGAP-ID.
def Ho.by_owner(+st: S.State, +assoc: U32, +ran: B.Bytes(), +amf: B.Bytes()) -> Maybe<&2, N.Keyed()>:
  N.Ue.keyed(N.Ngap.ue_key(amf), k => N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran))

# The UE whose handover is pending to assoc, not its owner, with its SUPI verified.
def Ho.aimed(+ue: S.Ue, +assoc: U32) -> Bool:
  Bool.and(S.Maybe.same_u32(S.Phase.pending(S.Ue.phase(ue)), Some{assoc}), Bool.and(Tb.Table.present(B.Digits(), S.Ue.supi(ue)), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc))))

def Ho.pending(m: Maybe<&2, S.Ue>, +assoc: U32) -> Maybe<&2, S.Ue>:
  match m:
    case None{}:
      None{}
    case Some{+ue}:
      N.Owner.check(ue, Ho.aimed(ue, assoc))

# The UE an AMF-UE-NGAP-ID names, if its handover is pending to the association.
def Ho.by_target(+st: S.State, +assoc: U32, +amf: B.Bytes()) -> Maybe<&2, N.Keyed()>:
  N.Ue.keyed(N.Ngap.ue_key(amf), k => Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc))

# Preparation
# -----------

def Ho.fail(+key: U32, +ue: S.Ue, cause: G.Cause) -> N.GOut():
  (S.Keep{}, [Ho.preparation_failure(key, ue, cause), N.Note{F.Warn{}, "NGAP: Handover Required refused"}])

def Ho.listed(+psi: U32, items: G.PDUSessionResourceListHORqd()) -> Bool:
  match items:
    case Nil{}:
      False{}
    case G.PDUSessionResourceItemHORqd{p, transfer, x} <> more:
      Bool.or(U32.is_eq(p, psi), Ho.listed(psi, more))

def Ho.item_if(+cfg: S.Cfg, +s: S.Session, more: G.PDUSessionResourceSetupListHOReq(), ok: Bool) -> G.PDUSessionResourceSetupListHOReq():
  match ok:
    case True{}:
      G.PDUSessionResourceSetupItemHOReq{S.Session.psi(s), G.S_NSSAI{S.Cfg.sst(cfg), None{}, None{}}, Gsm.Gsm.transfer_with(cfg, S.Session.teid(s), [Ho.no_forwarding()]), None{}} <> more
    case False{}:
      more

# Each active session the source lists, with its uplink tunnel.
def Ho.setup_items(+cfg: S.Cfg, +items: G.PDUSessionResourceListHORqd(), rows: Tb.Table(S.Session)) -> G.PDUSessionResourceSetupListHOReq():
  match rows:
    case Nil{}:
      []
    case (skey, +s) <> more:
      Ho.item_if(cfg, s, Ho.setup_items(cfg, items, more), Bool.and(Gsm.Gsm.active(S.Session.phase(s)), Ho.listed(S.Session.psi(s), items)))

# The target asked, under the preparation guard, with the next {NH, NCC},
# which the UE keeps whatever the outcome (TS 33.501 §6.9.2.3.3).
def Ho.prepare(+key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, +t: U32, +cfg: S.Cfg, cause: G.Cause, container: B.Bytes(), items: G.PDUSessionResourceSetupListHOReq()) -> N.GOut():
  match items:
    case Nil{}:
      Ho.fail(key, ue, Ho.radio(G.CauseRadioNetwork.unknown_PDU_session_ID()))
    case i <> more:
      +next = S.Nh.next(nh)
      (S.Rephase{key, S.Handover{ctx, next, S.Ue.assoc(ue), S.Asked{t}}}, [N.UeSend{t, Ho.stream(), key, Ho.request(key, cfg, cause, N.Ue.caps(ue), next, i <> more, container)}, N.TimerStart{Some{key}, key, N.Ue.guard_ms()}, N.Note{F.Info{}, "NGAP: Handover Required; Handover Request sent to the target"}])

def Ho.required_cfg(+st: S.State, +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, +t: U32, cause: G.Cause, items: G.PDUSessionResourceListHORqd(), container: B.Bytes(), m: Maybe<&2, S.Cfg>) -> N.GOut():
  match m:
    case None{}:
      Ho.fail(key, ue, Ho.radio(G.CauseRadioNetwork.unspecified()))
    case Some{+cfg}:
      Ho.prepare(key, ue, ctx, nh, t, cfg, cause, container, Ho.setup_items(cfg, items, S.Sessions.of_ue(key, S.State.sessions(st))))

# The target is not the source.
def Ho.required_other(+st: S.State, +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, +t: U32, cause: G.Cause, items: G.PDUSessionResourceListHORqd(), container: B.Bytes(), same: Bool) -> N.GOut():
  match same:
    case True{}:
      Ho.fail(key, ue, Ho.radio(G.CauseRadioNetwork.unknown_targetID()))
    case False{}:
      Ho.required_cfg(st, key, ue, ctx, nh, t, cause, items, container, S.State.config(st))

def Ho.required_target(+st: S.State, +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, cause: G.Cause, items: G.PDUSessionResourceListHORqd(), container: B.Bytes(), m: Maybe<&2, U32>) -> N.GOut():
  match m:
    case None{}:
      Ho.fail(key, ue, Ho.radio(G.CauseRadioNetwork.unknown_targetID()))
    case Some{+t}:
      Ho.required_other(st, key, ue, ctx, nh, t, cause, items, container, U32.is_eq(t, S.Ue.assoc(ue)))

def Ho.intra_type(t: G.HandoverType()) -> Bool:
  match t:
    case Ap.Root{i}:
      U32.is_eq(i, G.HandoverType.intra5gs())
    case Ap.Ext{i}:
      False{}

def Ho.node(id: G.TargetID) -> Maybe<&2, B.Bytes()>:
  match id:
    case G.TargetID_targetRANNodeID{G.TargetRANNodeID{node, tai, x}}:
      Some{Ap.pack(G.GlobalRANNodeID.write(node, 0n, []))}
    case _:
      None{}

# An intra-5GS handover to the gNB NG Setup knows by the Global RAN Node ID
# the request names.
def Ho.target(+st: S.State, intra: Bool, m: Maybe<&2, B.Bytes()>) -> Maybe<&2, U32>:
  match intra m:
    case True{} Some{node}:
      S.Assocs.of(node, S.State.assocs(st))
    case _ _:
      None{}

def Ho.required_phase(+st: S.State, +key: U32, +ue: S.Ue, kind: G.HandoverType(), cause: G.Cause, id: G.TargetID, items: G.PDUSessionResourceListHORqd(), container: B.Bytes(), p: S.Phase) -> N.GOut():
  match p:
    case S.Registered{ctx, nh, released}:
      Ho.required_target(st, key, ue, ctx, nh, cause, items, container, Ho.target(st, Ho.intra_type(kind), Ho.node(id)))
    case _:
      Ho.fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()))

# The target's answers
# --------------------

# Handover Request Acknowledge: Handover Command to the source, under the completion guard.
def Ho.ack_phase(+assoc: U32, +stream: U32, +key: U32, +ue: S.Ue, +ran: B.Bytes(), admitted: G.PDUSessionResourceAdmittedList(), container: B.Bytes(), p: S.Phase) -> N.GOut():
  match p:
    case S.Handover{ctx, nh, source, S.Asked{t}}:
      +ts = Sw.Sw.admitted(admitted)
      (S.Rephase{key, S.Handover{ctx, nh, S.Ue.assoc(ue), S.Acked{assoc, ran, stream, ts}}}, [N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.command(key, S.Ue.ran_id(ue), ts, container)}, N.TimerStart{Some{key}, key, N.Ue.guard_ms()}, N.Note{F.Info{}, "NGAP: Handover Request Acknowledge; Handover Command sent to the source"}])
    case _:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))

# Handover Failure: Handover Preparation Failure to the source with the
# target's cause; the target holds nothing to release.
def Ho.failure_phase(+assoc: U32, +key: U32, +ue: S.Ue, cause: G.Cause, p: S.Phase) -> N.GOut():
  match p:
    case S.Handover{ctx, nh, source, S.Asked{t}}:
      (S.Rephase{key, S.Registered{ctx, nh, None{}}}, [Ho.preparation_failure(key, ue, cause), N.TimerCancel{key}, N.Note{F.Warn{}, "NGAP: Handover Failure; Handover Preparation Failure sent to the source"}])
    case _:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))

# Handover Notify from the target, under the RAN-UE-NGAP-ID it acknowledged
# with, still free on it: the UE moves to the target, each session the target
# admitted has its downlink repointed and the others are released, and the
# source is told to release the UE.
def Ho.complete(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, ok: Bool) -> N.GOut():
  match ok:
    case False{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case True{}:
      +rows = S.Sessions.of_ue(key, S.State.sessions(st))
      N.Out.also(N.Out.join(Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st)), (S.Put{key, S.Ue.moved(ue, assoc, r, s, S.Registered{ctx, nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}})}, [])), [N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), Ho.radio(G.CauseRadioNetwork.successful_handover())}, N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Handover Notify; the UE moved to the target"}])

def Ho.notify_phase(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ran: B.Bytes(), p: S.Phase) -> N.GOut():
  match p:
    case S.Handover{ctx, nh, source, S.Acked{t, +r, s, ts}}:
      Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, Bool.and(B.bytes_eq(r, ran), S.Ues.ran_free(key, assoc, r, S.State.ues(st))))
    case _:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))

# The source's messages
# ---------------------

# Handover Cancel: acknowledged, the target released; with no handover
# pending, acknowledged alone (§8.4.6.2).
def Ho.cancel_phase(+key: U32, +ue: S.Ue, p: S.Phase) -> N.GOut():
  match p:
    case S.Handover{ctx, nh, source, +leg}:
      (S.Rephase{key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}}, N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.cancel_ack(key, S.Ue.ran_id(ue))} <> List.append(&2, N.Act, Ho.drop(key, leg, Ho.radio(G.CauseRadioNetwork.handover_cancelled())), [N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Handover Cancel; the target released"}]))
    case _:
      (S.Keep{}, [N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.cancel_ack(key, S.Ue.ran_id(ue))}, N.Note{F.Warn{}, "NGAP: Handover Cancel with no handover pending"}])

# Uplink RAN Status Transfer: relayed to the ready target as Downlink RAN Status Transfer.
def Ho.status_phase(+key: U32, container: G.RANStatusTransfer_TransparentContainer, p: S.Phase) -> N.GOut():
  match p:
    case S.Handover{ctx, nh, source, S.Acked{t, r, s, ts}}:
      (S.Keep{}, [N.UeSend{t, s, key, Ho.dl_status(key, r, container)}])
    case _:
      N.Out.warn("NGAP: Uplink RAN Status Transfer with no target ready")

# The guard
# ---------

# The guard fired: the handover ends and the UE stays with its owner. Before
# the target answered, the source gets Handover Preparation Failure and the
# target is released by AMF-UE-NGAP-ID; after it, the target is released.
def Ho.expiry(+key: U32, +ue: S.Ue, leg: S.Leg) -> List<&2, N.Act>:
  match leg:
    case S.Asked{t}:
      Ho.preparation_failure(key, ue, Ho.radio(G.CauseRadioNetwork.tngrelocprep_expiry())) <> Ho.drop(key, S.Asked{t}, Ho.radio(G.CauseRadioNetwork.tngrelocprep_expiry()))
    case S.Acked{t, r, s, ts}:
      Ho.drop(key, S.Acked{t, r, s, ts}, Ho.radio(G.CauseRadioNetwork.tngrelocoverall_expiry()))

def Ho.expired(+key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, +leg: S.Leg) -> N.GOut():
  (S.Rephase{key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}}, List.append(&2, N.Act, Ho.expiry(key, ue, leg), [N.Note{F.Warn{}, "NGAP: N2 handover guard expired; the UE stays with its owner"}]))

# An association going down
# -------------------------
# A handover pending to it ends, the UE staying with its owner, which gets
# Handover Preparation Failure if the target never answered; the target of a
# handover its own UE had pending is released.

def Ho.lost(+k: U32, +u: S.Ue, leg: S.Leg) -> List<&2, N.Act>:
  match leg:
    case S.Asked{t}:
      [Ho.preparation_failure(k, u, Ho.radio(G.CauseRadioNetwork.ho_failure_in_target_5GC_ngran_node_or_target_system()))]
    case S.Acked{t, r, s, ts}:
      []

def Ho.down_leg(+k: U32, +u: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, +leg: S.Leg, target: Bool, source: Bool) -> N.GOut():
  match target source:
    case True{} _:
      (S.Rephase{k, S.Registered{ctx, nh, None{}}}, List.append(&2, N.Act, Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's association went down; N2 handover ended"}]))
    case False{} True{}:
      (S.Keep{}, Ho.drop(k, leg, Ho.radio(G.CauseRadioNetwork.unspecified())))
    case False{} False{}:
      (S.Keep{}, [])

def Ho.down_row(+assoc: U32, +k: U32, +u: S.Ue, p: S.Phase) -> N.GOut():
  match p:
    case S.Handover{ctx, nh, source, +leg}:
      Ho.down_leg(k, u, ctx, nh, leg, U32.is_eq(S.Leg.target(leg), assoc), U32.is_eq(S.Ue.assoc(u), assoc))
    case _:
      (S.Keep{}, [])

def Ho.downs(+assoc: U32, rows: Tb.Table(S.Ue)) -> N.GOut():
  match rows:
    case Nil{}:
      (S.Keep{}, [])
    case (+k, +u) <> more:
      N.Out.join(Ho.down_row(assoc, k, u, S.Ue.phase(u)), Ho.downs(assoc, more))

def Ho.down(+st: S.State, +assoc: U32) -> N.GOut():
  Ho.downs(assoc, S.State.ues(st))

# Routing
# -------

def Ho.required_of_view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.HandoverRequired.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{V.HandoverRequired.View{+amf, +ran, kind, cause, id, direct, items, container}}:
      N.Ue.found(Ho.by_owner(st, assoc, ran, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.required_phase(st, key, ue, kind, cause, id, items, container, S.Ue.phase(ue)))

def Ho.ack_of_view(+st: S.State, +assoc: U32, +stream: U32, r: Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{V.HandoverRequestAcknowledge.View{+amf, +ran, admitted, failed, container, diag, npn}}:
      N.Ue.found(Ho.by_target(st, assoc, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.ack_phase(assoc, stream, key, ue, ran, admitted, container, S.Ue.phase(ue)))

def Ho.failure_of_view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.HandoverFailure.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{V.HandoverFailure.View{+amf, cause, diag}}:
      N.Ue.found(Ho.by_target(st, assoc, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.failure_phase(assoc, key, ue, cause, S.Ue.phase(ue)))

def Ho.notify_of_view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.HandoverNotify.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{V.HandoverNotify.View{+amf, +ran, uli}}:
      N.Ue.found(Ho.by_target(st, assoc, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.notify_phase(st, assoc, key, ue, ran, S.Ue.phase(ue)))

def Ho.cancel_of_view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.HandoverCancel.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{V.HandoverCancel.View{+amf, +ran, cause}}:
      N.Ue.found(Ho.by_owner(st, assoc, ran, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.cancel_phase(key, ue, S.Ue.phase(ue)))

def Ho.status_of_view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{V.UplinkRANStatusTransfer.View{+amf, +ran, container}}:
      N.Ue.found(Ho.by_owner(st, assoc, ran, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.status_phase(key, container, S.Ue.phase(ue)))

def Ho.r6(+st: S.State, +assoc: U32, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Ho.status_of_view(st, assoc, V.UplinkRANStatusTransfer.view(ies))
    case False{}:
      (S.Keep{}, N.Ngap.unhandled(assoc))

def Ho.r5(+st: S.State, +assoc: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Ho.cancel_of_view(st, assoc, V.HandoverCancel.view(ies))
    case False{}:
      Ho.r6(st, assoc, ies, N.Ngap.is_uplink_ran_status_transfer(kind, code))

def Ho.r4(+st: S.State, +assoc: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Ho.notify_of_view(st, assoc, V.HandoverNotify.view(ies))
    case False{}:
      Ho.r5(st, assoc, kind, code, ies, N.Ngap.is_handover_cancel(kind, code))

def Ho.r3(+st: S.State, +assoc: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Ho.failure_of_view(st, assoc, V.HandoverFailure.view(ies))
    case False{}:
      Ho.r4(st, assoc, kind, code, ies, N.Ngap.is_handover_notify(kind, code))

def Ho.r2(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Ho.ack_of_view(st, assoc, stream, V.HandoverRequestAcknowledge.view(ies))
    case False{}:
      Ho.r3(st, assoc, kind, code, ies, N.Ngap.is_handover_failure(kind, code))

def Ho.r1(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Ho.required_of_view(st, assoc, V.HandoverRequired.view(ies))
    case False{}:
      Ho.r2(st, assoc, stream, kind, code, ies, N.Ngap.is_handover_request_acknowledge(kind, code))

# The N2 handover messages, told apart like Route's; anything else is not handled.
def Ho.route(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>) -> N.GOut():
  Ho.r1(st, assoc, stream, kind, code, ies, N.Ngap.is_handover_required(kind, code))
