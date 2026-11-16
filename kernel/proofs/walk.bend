import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../tlv.bend as T
import ../table.bend as Tb
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/route.bend as R
import ../amf/gmm.bend as Gmm
import ../amf/path_switch.bend as Ps
import ../amf/handover.bend as Ho
import ./lib.bend as P
import ../smf/gsm.bend as Gsm
import ../smf/n4.bend as Up
import ../smf/switch.bend as Sw
import ../nas/security.bend as Sec

# The step function, walked once
# ------------------------------
# A step ends in one of five ways: the state as it was, with actions that
# name no UE context, start or stop no timer and answer no NG Setup (an NGAP
# PDU or IE list that does not decode, a message from an association without
# NG Setup, an incomplete Config, an association coming up); an association's
# UE contexts released and the associations set up changed (NG Setup); a
# procedure's outcome o rendered by N.Step.of (a routed NGAP message, a PFCP
# message, a timer); a new configuration; or an association going down. A property Q of steps holds after every step
# when it holds after each of them, the outcomes known only by a property ok
# that each of them has.

def Walk.Keep(-Q: N.Step() -> Type, +st: S.State) -> Type:
  @acts:List<&2, N.Act> -> (@k:U32 -> {N.Acts.spare(k, acts) == True{} : Bool}) -> (@k:U32 -> {N.Acts.touches(k, acts) == False{} : Bool}) -> {N.Ngap.any_ng_setup_response(acts) == False{} : Bool} -> Q((st, acts))

# NG Setup: the association's UE-related contexts re-initialised, then the
# associations set up changed, with actions that name no UE context and
# start or stop no timer; among them an NG Setup Response when the request,
# from the bytes, supports a tracking area of ours (s, N.NgSetup.supported_*).
def Walk.Ready(-Q: N.Step() -> Type, +st: S.State, +assoc: U32, +s: Bool) -> Type:
  @id:B.Bytes() -> @ok:Bool -> @acts:List<&2, N.Act> -> (@k:U32 -> {N.Acts.spare(k, acts) == True{} : Bool}) -> (@k:U32 -> {N.Acts.touches(k, acts) == False{} : Bool}) -> {N.Ngap.any_ng_setup_response(acts) == s : Bool} -> Q((S.State.ready(N.Step.state(R.Route.drop(st, assoc)), assoc, id, ok), List.append(&2, N.Act, N.Step.acts(R.Route.drop(st, assoc)), acts)))

def Walk.Out(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State) -> Type:
  @o:N.GOut() -> ok(o) -> Q(N.Step.of(st, o))

# The outcome of every NGAP message that is not NG Setup.
def Walk.Routed(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes()) -> Type:
  @kind:Nat -> @code:Nat -> @ies:List<&2, Fr.Ie> -> {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool} -> ok(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code)))

# The routed outcomes: each UE procedure's on any view of its message, and
# the N2 handover messages, which Ho.Ho.route tells apart from the rest.
def Walk.d8(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, handover: ok(Ho.Ho.route(st, assoc, stream, kind, code, ies)), path_switch: @r:Result<&2, &2, B.Err, V.PathSwitchRequest.View> -> ok(Ps.Ps.of_view(st, assoc, stream, r))) -> ok(R.Route.d8(st, assoc, stream, kind, code, ies, b)):
  match b:
    case True{}:
      path_switch(V.PathSwitchRequest.view(ies))
    case False{}:
      handover

def Walk.d7(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, handover: ok(Ho.Ho.route(st, assoc, stream, kind, code, ies)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r)), path_switch: @r:Result<&2, &2, B.Err, V.PathSwitchRequest.View> -> ok(Ps.Ps.of_view(st, assoc, stream, r))) -> ok(R.Route.d7(st, assoc, stream, kind, code, ies, b)):
  match b:
    case True{}:
      setup_response(V.PDUSessionResourceSetupResponse.view(ies))
    case False{}:
      Walk.d8(ok, st, assoc, stream, kind, code, ies, N.Ngap.is_path_switch_request(kind, code), handover, path_switch)

def Walk.d6(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, handover: ok(Ho.Ho.route(st, assoc, stream, kind, code, ies)), release_complete: @r:Result<&2, &2, B.Err, V.UEContextReleaseComplete.View> -> ok(Gmm.Gmm.release_complete_of_view(st, assoc, r)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r)), path_switch: @r:Result<&2, &2, B.Err, V.PathSwitchRequest.View> -> ok(Ps.Ps.of_view(st, assoc, stream, r))) -> ok(R.Route.d6(st, assoc, stream, kind, code, ies, b)):
  match b:
    case True{}:
      release_complete(V.UEContextReleaseComplete.view(ies))
    case False{}:
      Walk.d7(ok, st, assoc, stream, kind, code, ies, N.Ngap.is_pdu_session_resource_setup_response(kind, code), handover, setup_response, path_switch)

def Walk.d5(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, handover: ok(Ho.Ho.route(st, assoc, stream, kind, code, ies)), release_request: @r:Result<&2, &2, B.Err, V.UEContextReleaseRequest.View> -> ok(Gmm.Gmm.release_request_of_view(st, assoc, r)), release_complete: @r:Result<&2, &2, B.Err, V.UEContextReleaseComplete.View> -> ok(Gmm.Gmm.release_complete_of_view(st, assoc, r)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r)), path_switch: @r:Result<&2, &2, B.Err, V.PathSwitchRequest.View> -> ok(Ps.Ps.of_view(st, assoc, stream, r))) -> ok(R.Route.d5(st, assoc, stream, kind, code, ies, b)):
  match b:
    case True{}:
      release_request(V.UEContextReleaseRequest.view(ies))
    case False{}:
      Walk.d6(ok, st, assoc, stream, kind, code, ies, N.Ngap.is_ue_context_release_complete(kind, code), handover, release_complete, setup_response, path_switch)

def Walk.d4(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, handover: ok(Ho.Ho.route(st, assoc, stream, kind, code, ies)), ics: @r:Result<&2, &2, B.Err, V.InitialContextSetupResponse.View> -> ok(Gmm.Gmm.ics_response_of_view(st, assoc, r)), release_request: @r:Result<&2, &2, B.Err, V.UEContextReleaseRequest.View> -> ok(Gmm.Gmm.release_request_of_view(st, assoc, r)), release_complete: @r:Result<&2, &2, B.Err, V.UEContextReleaseComplete.View> -> ok(Gmm.Gmm.release_complete_of_view(st, assoc, r)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r)), path_switch: @r:Result<&2, &2, B.Err, V.PathSwitchRequest.View> -> ok(Ps.Ps.of_view(st, assoc, stream, r))) -> ok(R.Route.d4(st, assoc, stream, kind, code, ies, b)):
  match b:
    case True{}:
      ics(V.InitialContextSetupResponse.view(ies))
    case False{}:
      Walk.d5(ok, st, assoc, stream, kind, code, ies, N.Ngap.is_ue_context_release_request(kind, code), handover, release_request, release_complete, setup_response, path_switch)

def Walk.d3(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, handover: ok(Ho.Ho.route(st, assoc, stream, kind, code, ies)), uplink: @r:Result<&2, &2, B.Err, V.UplinkNASTransport.View> -> ok(Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, r)), ics: @r:Result<&2, &2, B.Err, V.InitialContextSetupResponse.View> -> ok(Gmm.Gmm.ics_response_of_view(st, assoc, r)), release_request: @r:Result<&2, &2, B.Err, V.UEContextReleaseRequest.View> -> ok(Gmm.Gmm.release_request_of_view(st, assoc, r)), release_complete: @r:Result<&2, &2, B.Err, V.UEContextReleaseComplete.View> -> ok(Gmm.Gmm.release_complete_of_view(st, assoc, r)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r)), path_switch: @r:Result<&2, &2, B.Err, V.PathSwitchRequest.View> -> ok(Ps.Ps.of_view(st, assoc, stream, r))) -> ok(R.Route.d3(st, assoc, stream, kind, code, ies, entropy, b)):
  match b:
    case True{}:
      uplink(V.UplinkNASTransport.view(ies))
    case False{}:
      Walk.d4(ok, st, assoc, stream, kind, code, ies, N.Ngap.is_initial_context_setup_response(kind, code), handover, ics, release_request, release_complete, setup_response, path_switch)

def Walk.d2(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, handover: ok(Ho.Ho.route(st, assoc, stream, kind, code, ies)), initial: @r:Result<&2, &2, B.Err, V.InitialUEMessage.View> -> ok(Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, r)), uplink: @r:Result<&2, &2, B.Err, V.UplinkNASTransport.View> -> ok(Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, r)), ics: @r:Result<&2, &2, B.Err, V.InitialContextSetupResponse.View> -> ok(Gmm.Gmm.ics_response_of_view(st, assoc, r)), release_request: @r:Result<&2, &2, B.Err, V.UEContextReleaseRequest.View> -> ok(Gmm.Gmm.release_request_of_view(st, assoc, r)), release_complete: @r:Result<&2, &2, B.Err, V.UEContextReleaseComplete.View> -> ok(Gmm.Gmm.release_complete_of_view(st, assoc, r)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r)), path_switch: @r:Result<&2, &2, B.Err, V.PathSwitchRequest.View> -> ok(Ps.Ps.of_view(st, assoc, stream, r))) -> ok(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, b)):
  match b:
    case True{}:
      initial(V.InitialUEMessage.view(ies))
    case False{}:
      Walk.d3(ok, st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_uplink_nas_transport(kind, code), handover, uplink, ics, release_request, release_complete, setup_response, path_switch)

# NG Setup is answered with NG Setup Response exactly when the request
# supports a tracking area of ours.
def Walk.answer_if(cfg: S.Cfg, +assoc: U32, +b: Bool) -> {N.Ngap.any_ng_setup_response([N.Setup{assoc, N.NgSetup.answer(cfg, b)}]) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Walk.answer(+config: Maybe<&2, S.Cfg>, +assoc: U32, +v: V.NGSetupRequest.View) -> {N.Ngap.any_ng_setup_response([N.Setup{assoc, N.NgSetup.reply(config, v)}]) == N.NgSetup.supported_view(config, v) : Bool}:
  match config:
    case None{}:
      {==}
    case Some{+cfg}:
      match v:
        case V.NGSetupRequest.View{g, +tas, d}:
          Walk.answer_if(cfg, assoc, N.Ta.supported(S.Cfg.plmn(cfg), S.Cfg.tac(cfg), tas))

def Walk.setup(-Q: N.Step() -> Type, +st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.NGSetupRequest.View>, keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st, assoc, N.NgSetup.supported_of_view(S.State.config(st), r))) -> Q(R.Route.setup(st, assoc, r)):
  match r:
    case Fail{e}:
      keep(N.Ngap.bad_view(assoc), k => {==}, k => {==}, {==})
    case Done{+v}:
      ready(N.NgSetup.node(v), N.NgSetup.supported_view(S.State.config(st), v), [N.Setup{assoc, N.NgSetup.reply(S.State.config(st), v)}], k => {==}, k => {==}, Walk.answer(S.State.config(st), assoc, v))

def Walk.ready(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, +eb: {S.Assocs.has(assoc, S.State.assocs(st)) == b : Bool}, keep: Walk.Keep(Q, st), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.ready(st, assoc, stream, kind, code, ies, entropy, b)):
  match b:
    case True{}:
      out(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code)), routed(kind, code, ies, eb))
    case False{}:
      keep(N.Ngap.unhandled(assoc), k => {==}, k => {==}, {==})

def Walk.d1(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st, assoc, N.NgSetup.supported_d1(S.State.config(st), ies, b)), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, b)):
  match b:
    case True{}:
      Walk.setup(Q, st, assoc, V.NGSetupRequest.view(ies), keep, ready)
    case False{}:
      Walk.ready(Q, ok, st, assoc, stream, kind, code, ies, entropy, S.Assocs.has(assoc, S.State.assocs(st)), {==}, keep, out, routed)

def Walk.ies(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +entropy: B.Bytes(), +r: Ap.Rd(List<&2, Fr.Ie>), keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st, assoc, N.NgSetup.supported_ies(S.State.config(st), kind, code, r)), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r)):
  match r:
    case Fail{err}:
      keep(N.Ngap.bad_pdu(assoc), k => {==}, k => {==}, {==})
    case Done{(+ies, c)}:
      Walk.d1(Q, ok, st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_ng_setup(kind, code), keep, ready, out, routed)

def Walk.pdu(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Fr.Pdu>, keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st, assoc, N.NgSetup.supported_pdu(S.State.config(st), r)), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.of_pdu(st, assoc, stream, entropy, r)):
  match r:
    case Fail{err}:
      keep(N.Ngap.bad_pdu(assoc), k => {==}, k => {==}, {==})
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Walk.ies(Q, ok, st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), keep, ready, out, routed)

def Walk.step(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: Walk.Keep(Q, st), ready: @assoc:U32 -> @s:Bool -> Walk.Ready(Q, st, assoc, s), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), down: @assoc:U32 -> Q(R.Route.down(st, assoc)), out: Walk.Out(Q, ok, st), routed: @assoc:U32 -> @stream:U32 -> Walk.Routed(ok, st, assoc, stream, entropy), pfcp: @bytes:B.Bytes() -> ok(Gsm.Gsm.pfcp_data(st, bytes)), fired: @timer:U32 -> ok(K.Kernel.fired(st, timer))) -> Q(K.Kernel.step(st, ev, entropy)):
  match ev:
    case F.Config{len, +tlvs}:
      config(tlvs)
    case F.NgapAssocUp{assoc}:
      keep([], k => {==}, k => {==}, {==})
    case F.NgapAssocDown{assoc}:
      down(assoc)
    case F.NgapData{+assoc, +stream, len, +bytes}:
      Walk.pdu(Q, ok, st, assoc, stream, entropy, Fr.Pdu.read(bytes), keep, ready(assoc, N.NgSetup.supported_request(S.State.config(st), bytes)), out, routed(assoc, stream))
    case F.PfcpData{len, +bytes}:
      out(Gsm.Gsm.pfcp_data(st, bytes), pfcp(bytes))
    case F.TimerFired{+timer}:
      out(K.Kernel.fired(st, timer), fired(timer))

# A property that holds after any outcome.
def Walk.any(-Q: N.Step() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: Walk.Keep(Q, st), ready: @assoc:U32 -> @s:Bool -> Walk.Ready(Q, st, assoc, s), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), down: @assoc:U32 -> Q(R.Route.down(st, assoc)), out: @o:N.GOut() -> Q(N.Step.of(st, o))) -> Q(K.Kernel.step(st, ev, entropy)):
  Walk.step(Q, o => Unit, st, ev, entropy, keep, ready, config, down, o => u => out(o), a => s => kind => code => ies => ea => Unit{}, bytes => Unit{}, timer => Unit{})

# The N2 handover messages, walked
# --------------------------------
# Ho.Ho.route ends in each handover procedure on any view of its message, or
# in the message not handled.

def Walk.h6(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +ies: List<&2, Fr.Ie>, +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), status: @r:Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View> -> ok(Ho.Ho.status_of_view(st, assoc, r))) -> ok(Ho.Ho.r6(st, assoc, ies, b)):
  match b:
    case True{}:
      status(V.UplinkRANStatusTransfer.view(ies))
    case False{}:
      unhandled

def Walk.h5(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), cancel: @r:Result<&2, &2, B.Err, V.HandoverCancel.View> -> ok(Ho.Ho.cancel_of_view(st, assoc, r)), status: @r:Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View> -> ok(Ho.Ho.status_of_view(st, assoc, r))) -> ok(Ho.Ho.r5(st, assoc, kind, code, ies, b)):
  match b:
    case True{}:
      cancel(V.HandoverCancel.view(ies))
    case False{}:
      Walk.h6(ok, st, assoc, ies, N.Ngap.is_uplink_ran_status_transfer(kind, code), unhandled, status)

def Walk.h4(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), notify: @r:Result<&2, &2, B.Err, V.HandoverNotify.View> -> ok(Ho.Ho.notify_of_view(st, assoc, r)), cancel: @r:Result<&2, &2, B.Err, V.HandoverCancel.View> -> ok(Ho.Ho.cancel_of_view(st, assoc, r)), status: @r:Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View> -> ok(Ho.Ho.status_of_view(st, assoc, r))) -> ok(Ho.Ho.r4(st, assoc, kind, code, ies, b)):
  match b:
    case True{}:
      notify(V.HandoverNotify.view(ies))
    case False{}:
      Walk.h5(ok, st, assoc, kind, code, ies, N.Ngap.is_handover_cancel(kind, code), unhandled, cancel, status)

def Walk.h3(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), failure: @r:Result<&2, &2, B.Err, V.HandoverFailure.View> -> ok(Ho.Ho.failure_of_view(st, assoc, r)), notify: @r:Result<&2, &2, B.Err, V.HandoverNotify.View> -> ok(Ho.Ho.notify_of_view(st, assoc, r)), cancel: @r:Result<&2, &2, B.Err, V.HandoverCancel.View> -> ok(Ho.Ho.cancel_of_view(st, assoc, r)), status: @r:Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View> -> ok(Ho.Ho.status_of_view(st, assoc, r))) -> ok(Ho.Ho.r3(st, assoc, kind, code, ies, b)):
  match b:
    case True{}:
      failure(V.HandoverFailure.view(ies))
    case False{}:
      Walk.h4(ok, st, assoc, kind, code, ies, N.Ngap.is_handover_notify(kind, code), unhandled, notify, cancel, status)

def Walk.h2(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), ack: @r:Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View> -> ok(Ho.Ho.ack_of_view(st, assoc, stream, r)), failure: @r:Result<&2, &2, B.Err, V.HandoverFailure.View> -> ok(Ho.Ho.failure_of_view(st, assoc, r)), notify: @r:Result<&2, &2, B.Err, V.HandoverNotify.View> -> ok(Ho.Ho.notify_of_view(st, assoc, r)), cancel: @r:Result<&2, &2, B.Err, V.HandoverCancel.View> -> ok(Ho.Ho.cancel_of_view(st, assoc, r)), status: @r:Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View> -> ok(Ho.Ho.status_of_view(st, assoc, r))) -> ok(Ho.Ho.r2(st, assoc, stream, kind, code, ies, b)):
  match b:
    case True{}:
      ack(V.HandoverRequestAcknowledge.view(ies))
    case False{}:
      Walk.h3(ok, st, assoc, kind, code, ies, N.Ngap.is_handover_failure(kind, code), unhandled, failure, notify, cancel, status)

def Walk.h1(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), required: @r:Result<&2, &2, B.Err, V.HandoverRequired.View> -> ok(Ho.Ho.required_of_view(st, assoc, r)), ack: @r:Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View> -> ok(Ho.Ho.ack_of_view(st, assoc, stream, r)), failure: @r:Result<&2, &2, B.Err, V.HandoverFailure.View> -> ok(Ho.Ho.failure_of_view(st, assoc, r)), notify: @r:Result<&2, &2, B.Err, V.HandoverNotify.View> -> ok(Ho.Ho.notify_of_view(st, assoc, r)), cancel: @r:Result<&2, &2, B.Err, V.HandoverCancel.View> -> ok(Ho.Ho.cancel_of_view(st, assoc, r)), status: @r:Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View> -> ok(Ho.Ho.status_of_view(st, assoc, r))) -> ok(Ho.Ho.r1(st, assoc, stream, kind, code, ies, b)):
  match b:
    case True{}:
      required(V.HandoverRequired.view(ies))
    case False{}:
      Walk.h2(ok, st, assoc, stream, kind, code, ies, N.Ngap.is_handover_request_acknowledge(kind, code), unhandled, ack, failure, notify, cancel, status)

def Walk.ho(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), required: @r:Result<&2, &2, B.Err, V.HandoverRequired.View> -> ok(Ho.Ho.required_of_view(st, assoc, r)), ack: @r:Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View> -> ok(Ho.Ho.ack_of_view(st, assoc, stream, r)), failure: @r:Result<&2, &2, B.Err, V.HandoverFailure.View> -> ok(Ho.Ho.failure_of_view(st, assoc, r)), notify: @r:Result<&2, &2, B.Err, V.HandoverNotify.View> -> ok(Ho.Ho.notify_of_view(st, assoc, r)), cancel: @r:Result<&2, &2, B.Err, V.HandoverCancel.View> -> ok(Ho.Ho.cancel_of_view(st, assoc, r)), status: @r:Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View> -> ok(Ho.Ho.status_of_view(st, assoc, r))) -> ok(Ho.Ho.route(st, assoc, stream, kind, code, ies)):
  Walk.h1(ok, st, assoc, stream, kind, code, ies, N.Ngap.is_handover_required(kind, code), unhandled, required, ack, failure, notify, cancel, status)

def Walk.aimed(+w: S.Ue, +assoc: U32, +ue: S.Ue, +b: Bool, +eb: {Ho.Ho.aimed(w, assoc) == b : Bool}, +e: {N.Owner.check(w, b) == Some{ue} : Maybe<&2, S.Ue>}) -> {Some{w} == Some{ue} : Maybe<&2, S.Ue>} & {Ho.Ho.aimed(ue, assoc) == True{} : Bool}:
  match b:
    case True{}:
      ew = P.Some.inj(S.Ue, w, ue, e)
      (e, (%ew : {Ho.Ho.aimed(_, assoc) == True{} : Bool}; eb))
    case False{}:
      Empty.absurd({Some{w} == Some{ue} : Maybe<&2, S.Ue>} & {Ho.Ho.aimed(ue, assoc) == True{} : Bool}, P.Refute.none_some(S.Ue, ue, e))

# The context a target's answer is for: the one under the key, with a
# handover pending to that target and its SUPI verified.
def Walk.pending(+m: Maybe<&2, S.Ue>, +assoc: U32, +ue: S.Ue, +e: {Ho.Ho.pending(m, assoc) == Some{ue} : Maybe<&2, S.Ue>}) -> {m == Some{ue} : Maybe<&2, S.Ue>} & {Ho.Ho.aimed(ue, assoc) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{ue} : Maybe<&2, S.Ue>} & {Ho.Ho.aimed(ue, assoc) == True{} : Bool}, P.Refute.none_some(S.Ue, ue, e))
    case Some{+w}:
      Walk.aimed(w, assoc, ue, Ho.Ho.aimed(w, assoc), {==}, e)

# A property of the context and session tables: Config and every step that
# keeps the state leave both tables as they were.

def Walk.Tables(-inv: Tb.Table(S.Ue) -> Tb.Table(S.Session) -> Bool, o: N.Step()) -> Data:
  {inv(S.State.ues(K.Kernel.state(o)), S.State.sessions(K.Kernel.state(o))) == True{} : Bool}

def Walk.config(-inv: Tb.Table(S.Ue) -> Tb.Table(S.Session) -> Bool, +complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), +e: {inv(S.State.ues(st), S.State.sessions(st)) == True{} : Bool}) -> Walk.Tables(inv, K.Kernel.config(complete, st, tlvs, entropy)):
  match complete:
    case False{}:
      e
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          e

def Walk.assocs(-inv: Tb.Table(S.Ue) -> Tb.Table(S.Session) -> Bool, +st: S.State, +as: Tb.Table(B.Bytes()), +acts: List<&2, N.Act>, +e: {inv(S.State.ues(st), S.State.sessions(st)) == True{} : Bool}) -> Walk.Tables(inv, (S.State.with_assocs(st, as), acts)):
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      e

# The route, from the bytes
# -------------------------
# A message other than NG Setup whose PDU and IE list read is refused when its
# association has not completed NG Setup (amf.ng_setup.first) and routed by
# its kind and procedure code when it has.

def Rt.refused(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == False{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unhandled(assoc)) : N.Step()}:
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{kind, code, crit, value}}, ep)
  %sep : {R.Route.of_pdu(st, assoc, stream, entropy, _) == (st, N.Ngap.unhandled(assoc)) : N.Step()}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {R.Route.of_ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, _) == (st, N.Ngap.unhandled(assoc)) : N.Step()}
  sen = Equal.sym(Bool, N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)), False{}, en)
  %sen : {R.Route.d1(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, _) == (st, N.Ngap.unhandled(assoc)) : N.Step()}
  sea = Equal.sym(Bool, S.Assocs.has(assoc, S.State.assocs(st)), False{}, ea)
  %sea : {R.Route.ready(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, _) == (st, N.Ngap.unhandled(assoc)) : N.Step()}
  {==}

def Rt.routed(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(kind), U32.to_nat(code)))) : N.Step()}:
  +T = N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(kind), U32.to_nat(code))))
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{kind, code, crit, value}}, ep)
  %sep : {R.Route.of_pdu(st, assoc, stream, entropy, _) == T : N.Step()}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {R.Route.of_ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, _) == T : N.Step()}
  sen = Equal.sym(Bool, N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)), False{}, en)
  %sen : {R.Route.d1(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, _) == T : N.Step()}
  sea = Equal.sym(Bool, S.Assocs.has(assoc, S.State.assocs(st)), True{}, ea)
  %sea : {R.Route.ready(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, _) == T : N.Step()}
  {==}

def Rt.split_if(-P: Type, +assoc: U32, +as: Tb.Table(B.Bytes()), +b: Bool, +eb: {S.Assocs.has(assoc, as) == b : Bool}, refused: {S.Assocs.has(assoc, as) == False{} : Bool} -> P, routed: {S.Assocs.has(assoc, as) == True{} : Bool} -> P) -> P:
  match b:
    case True{}:
      routed(eb)
    case False{}:
      refused(eb)

# Whether the association has completed NG Setup or not.
def Rt.split(-P: Type, +assoc: U32, +as: Tb.Table(B.Bytes()), refused: {S.Assocs.has(assoc, as) == False{} : Bool} -> P, routed: {S.Assocs.has(assoc, as) == True{} : Bool} -> P) -> P:
  Rt.split_if(P, assoc, as, S.Assocs.has(assoc, as), {==}, refused, routed)

def Rt.at(-Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == False{} : Bool}, refused: Q((st, N.Ngap.unhandled(assoc)))) -> Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)):
  e = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), (st, N.Ngap.unhandled(assoc)), Rt.refused(st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, ep, ei, en, ea))
  %e : Q(_)
  refused

# What holds of the refusal, and of the step when routed, holds of the step.
def Rt.cases(-Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, refused: Q((st, N.Ngap.unhandled(assoc))), routed: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool} -> Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) -> Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)):
  Rt.split(Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)), assoc, S.State.assocs(st), ea => Rt.at(Q, st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, ep, ei, en, ea, refused), routed)

def Rt.keeps(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, routed: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool} -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  Rt.cases(x => {K.Kernel.state(x) == st : S.State}, st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, ep, ei, en, {==}, routed)

# What holds when the IE list does not read, when the association lacks NG
# Setup, and of every routed outcome, holds of the step.
def Rt.Routed(-Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +kind: U32, +code: U32) -> Type:
  @ies:List<&2, Fr.Ie> -> Q(N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(kind), U32.to_nat(code)))))

def Rt.go(-Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}, routed: Rt.Routed(Q, st, entropy, assoc, stream, kind, code)) -> Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)):
  e = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(kind), U32.to_nat(code)))), Rt.routed(st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, ep, ei, en, ea))
  %e : Q(_)
  routed(ies)

def Rt.read_if(-Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +r: Ap.Rd(List<&2, Fr.Ie>), +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == r : Ap.Rd(List<&2, Fr.Ie>)}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, bad: Q((st, N.Ngap.bad_pdu(assoc))), refused: Q((st, N.Ngap.unhandled(assoc))), routed: Rt.Routed(Q, st, entropy, assoc, stream, kind, code)) -> Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)):
  match r:
    case Fail{err}:
      sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{kind, code, crit, value}}, ep)
      %sep : Q(R.Route.of_pdu(st, assoc, stream, entropy, _))
      sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Fail{err}, ei)
      %sei : Q(R.Route.of_ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, _))
      bad
    case Done{(+ies, +c)}:
      Rt.cases(Q, st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, ep, ei, en, refused, ea => Rt.go(Q, st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, ep, ei, en, ea, routed))

def Rt.read(-Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, bad: Q((st, N.Ngap.bad_pdu(assoc))), refused: Q((st, N.Ngap.unhandled(assoc))), routed: Rt.Routed(Q, st, entropy, assoc, stream, kind, code)) -> Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)):
  Rt.read_if(Q, st, entropy, assoc, stream, len, bytes, kind, code, crit, value, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), ep, {==}, en, bad, refused, routed)

# A UE message, routed: its procedure f takes the view of its IEs (ed: {==}
# for a given message). What holds of f's outcome on the view r holds of the
# step.
def Rt.view(-A: Data, -Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, -view: List<&2, Fr.Ie> -> Result<&2, &2, B.Err, A>, -f: Result<&2, &2, B.Err, A> -> N.GOut(), +r: Result<&2, &2, B.Err, A>, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}, ed: {f(view(ies)) == R.Route.d2(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(kind), U32.to_nat(code))) : N.GOut()}, ev: {view(ies) == r : Result<&2, &2, B.Err, A>}, h: Q(N.Step.of(st, f(r)))) -> Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)):
  e = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(kind), U32.to_nat(code)))), Rt.routed(st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, ep, ei, en, ea))
  %e : Q(_)
  %ed : Q(N.Step.of(st, _))
  sv = Equal.sym(Result<&2, &2, B.Err, A>, view(ies), r, ev)
  %sv : Q(N.Step.of(st, f(_)))
  h

# The view read as v, f goes on as g on the key its AMF-UE-NGAP-ID amf gives
# (ef: {==} for a given message); what holds of g's outcome for that key m
# holds of the step.
def Rt.ue(-A: Data, -Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, -view: List<&2, Fr.Ie> -> Result<&2, &2, B.Err, A>, -f: Result<&2, &2, B.Err, A> -> N.GOut(), -g: Maybe<&2, U32> -> N.GOut(), +v: A, +amf: B.Bytes(), +m: Maybe<&2, U32>, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}, ed: {f(view(ies)) == R.Route.d2(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(kind), U32.to_nat(code))) : N.GOut()}, ev: {view(ies) == Done{v} : Result<&2, &2, B.Err, A>}, ef: {g(N.Ngap.ue_key(amf)) == f(Done{v}) : N.GOut()}, em: {N.Ngap.ue_key(amf) == m : Maybe<&2, U32>}, h: Q(N.Step.of(st, g(m)))) -> Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)):
  sm = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), m, em)
  Rt.view(A, Q, st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, view, f, Done{v}, ep, ei, en, ea, ed, ev, (%ef : Q(N.Step.of(st, _)); (%sm : Q(N.Step.of(st, g(_))); h)))

# The key named, g goes on as h on the context the association owns under
# that key and its RAN-UE-NGAP-ID ran (eg: {==} for a given message).
def Rt.owned(-A: Data, -Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, -view: List<&2, Fr.Ie> -> Result<&2, &2, B.Err, A>, -f: Result<&2, &2, B.Err, A> -> N.GOut(), -g: Maybe<&2, U32> -> N.GOut(), -h: Maybe<&2, S.Ue> -> N.GOut(), +v: A, +amf: B.Bytes(), +k: U32, +ran: B.Bytes(), +o: Maybe<&2, S.Ue>, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {N.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}, ed: {f(view(ies)) == R.Route.d2(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(kind), U32.to_nat(code))) : N.GOut()}, ev: {view(ies) == Done{v} : Result<&2, &2, B.Err, A>}, ef: {g(N.Ngap.ue_key(amf)) == f(Done{v}) : N.GOut()}, eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, eg: {h(Gmm.Gmm.owner(st, assoc, k, ran)) == g(Some{k}) : N.GOut()}, eo: {Gmm.Gmm.owner(st, assoc, k, ran) == o : Maybe<&2, S.Ue>}, h0: Q(N.Step.of(st, h(o)))) -> Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)):
  so = Equal.sym(Maybe<&2, S.Ue>, Gmm.Gmm.owner(st, assoc, k, ran), o, eo)
  Rt.ue(A, Q, st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, view, f, g, v, amf, Some{k}, ep, ei, en, ea, ed, ev, ef, eid, (%eg : Q(N.Step.of(st, _)); (%so : Q(N.Step.of(st, h(_))); h0)))

# A context another association has is not the association's.
def Rt.other(+st: S.State, +assoc: U32, +k: U32, +ran: B.Bytes(), +ue: S.Ue, eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, ea: {U32.is_eq(S.Ue.assoc(ue), assoc) == False{} : Bool}) -> {Gmm.Gmm.owner(st, assoc, k, ran) == None{} : Maybe<&2, S.Ue>}:
  seu = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{ue}, eu)
  %seu : {N.Owner.of(_, assoc, ran) == None{} : Maybe<&2, S.Ue>}
  sea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, ea)
  %sea : {N.Owner.check(ue, Bool.and(_, B.bytes_eq(S.Ue.ran_id(ue), ran))) == None{} : Maybe<&2, S.Ue>}
  {==}

# The session side
# ----------------
# A transaction that changes no context (sessions changed in place or
# forgotten, the N4 link, the sequence numbers) keeps the context table;
# Up.N4.deletions gives one.

def Sx.only(tx: S.Tx) -> Bool:
  match tx:
    case S.Keep{}:
      True{}
    case S.SetLink{link}:
      True{}
    case S.Revar{key, v}:
      True{}
    case S.DelSession{key}:
      True{}
    case S.BumpSeq{n}:
      True{}
    case S.Both{first, second}:
      Bool.and(Sx.only(first), Sx.only(second))
    case _:
      False{}

def Out.tx_join(+a: N.GOut(), +b: N.GOut()) -> {N.Out.tx(N.Out.join(a, b)) == S.Both{N.Out.tx(a), N.Out.tx(b)} : S.Tx}:
  match a:
    case (ta, aa):
      match b:
        case (tb, ab):
          {==}

def Sx.join(+a: N.GOut(), +b: N.GOut(), +ea: {Sx.only(N.Out.tx(a)) == True{} : Bool}, +eb: {Sx.only(N.Out.tx(b)) == True{} : Bool}) -> {Sx.only(N.Out.tx(N.Out.join(a, b))) == True{} : Bool}:
  e = Equal.sym(S.Tx, N.Out.tx(N.Out.join(a, b)), S.Both{N.Out.tx(a), N.Out.tx(b)}, Out.tx_join(a, b))
  (%e : {Sx.only(_) == True{} : Bool}; P.Bool.and_intro(Sx.only(N.Out.tx(a)), Sx.only(N.Out.tx(b)), ea, eb))

def Sx.delete_if(+key: U32, +s: S.Session, +seq: U32, +more: Tb.Table(S.Session), +known: Bool, h0: {Sx.only(N.Out.tx(Up.N4.deletions(more, seq))) == True{} : Bool}, h1: {Sx.only(N.Out.tx(Up.N4.deletions(more, U32.add(seq, 1)))) == True{} : Bool}) -> {Sx.only(N.Out.tx(Up.N4.delete_if(key, s, seq, q => Up.N4.deletions(more, q), known))) == True{} : Bool}:
  match known:
    case True{}:
      +request = Up.N4.delete(S.Session.up_seid(s), seq)
      Sx.join((S.Both{S.Revar{key, S.SVar{S.Session.up_seid(s), seq, S.Deleting{S.Guard{0}, request}}}, S.BumpSeq{1}}, [N.Pfcp{S.Session.tag(s), request}, N.TimerStart{None{}, key, Up.N4.t1_ms()}]), Up.N4.deletions(more, U32.add(seq, 1)), {==}, h1)
    case False{}:
      Sx.join((S.DelSession{key}, []), Up.N4.deletions(more, seq), {==}, h0)

def Sx.deletions(+rows: Tb.Table(S.Session), +seq: U32) -> {Sx.only(N.Out.tx(Up.N4.deletions(rows, seq))) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +s) <> +more:
      Sx.delete_if(key, s, seq, more, S.Session.known(s), Sx.deletions(more, seq), Sx.deletions(more, U32.add(seq, 1)))

# Sessions changed in place
# -------------------------
# A change in place keeps a session's identity, and keeps its tag or drops it
# when the session goes on to be deleted (S.SVar.follows): a session being
# deleted never belongs to a UE again.

def Tg.Moved(+t: S.Session, +t2: S.Session) -> Data:
  Either<&2, &2, {S.Session.tag(t2) == S.Session.tag(t) : Maybe<&2, U32>}, {S.Session.tag(t2) == None{} : Maybe<&2, U32>}>

def Tg.go(+id: S.SId, +var: S.SVar, +v: S.SVar, +a: Bool, +ea: {S.SPhase.live(S.SVar.phase(var)) == a : Bool}, +b: Bool, +eb: {S.SPhase.live(S.SVar.phase(v)) == b : Bool}) -> Either<&2, &2, {S.Session.tag(S.Session.revar_if(S.Session{id, var}, v, Bool.or(Bool.not(b), a))) == Tb.Table.hit(U32, S.SId.ue(id), None{}, a) : Maybe<&2, U32>}, {S.Session.tag(S.Session.revar_if(S.Session{id, var}, v, Bool.or(Bool.not(b), a))) == None{} : Maybe<&2, U32>}>:
  match a:
    case True{}:
      match b:
        case True{}:
          seb = Equal.sym(Bool, S.SPhase.live(S.SVar.phase(v)), True{}, eb)
          Inl{(%seb : {Tb.Table.hit(U32, S.SId.ue(id), None{}, _) == Some{S.SId.ue(id)} : Maybe<&2, U32>}; {==})}
        case False{}:
          seb = Equal.sym(Bool, S.SPhase.live(S.SVar.phase(v)), False{}, eb)
          Inr{(%seb : {Tb.Table.hit(U32, S.SId.ue(id), None{}, _) == None{} : Maybe<&2, U32>}; {==})}
    case False{}:
      match b:
        case True{}:
          sea = Equal.sym(Bool, S.SPhase.live(S.SVar.phase(var)), False{}, ea)
          Inl{(%sea : {Tb.Table.hit(U32, S.SId.ue(id), None{}, _) == None{} : Maybe<&2, U32>}; {==})}
        case False{}:
          seb = Equal.sym(Bool, S.SPhase.live(S.SVar.phase(v)), False{}, eb)
          Inr{(%seb : {Tb.Table.hit(U32, S.SId.ue(id), None{}, _) == None{} : Maybe<&2, U32>}; {==})}

def Tg.revar(+t: S.Session, +v: S.SVar, +c: Bool) -> Tg.Moved(t, S.Session.revar_if(t, v, Bool.and(c, S.SVar.follows(v, t)))):
  match t:
    case S.Session{+id, +var}:
      match c:
        case False{}:
          Inl{{==}}
        case True{}:
          Tg.go(id, var, v, S.SPhase.live(S.SVar.phase(var)), {==}, S.SPhase.live(S.SVar.phase(v)), {==})

def Tg.id(+t: S.Session, +v: S.SVar, +hit: Bool) -> {S.Session.id(S.Session.revar_if(t, v, hit)) == S.Session.id(t) : S.SId}:
  match t:
    case S.Session{id, var}:
      match hit:
        case False{}:
          {==}
        case True{}:
          {==}

def Tg.same_none(+m: Maybe<&2, U32>) -> {S.Maybe.same_u32(m, None{}) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# What told a session apart from m by its tag still does.
def Tg.same_r(+m: Maybe<&2, U32>, +t: S.Session, +t2: S.Session, h: Tg.Moved(t, t2), +e: {S.Maybe.same_u32(m, S.Session.tag(t)) == False{} : Bool}) -> {S.Maybe.same_u32(m, S.Session.tag(t2)) == False{} : Bool}:
  match h:
    case Inl{ee}:
      se = Equal.sym(Maybe<&2, U32>, S.Session.tag(t2), S.Session.tag(t), ee)
      (%se : {S.Maybe.same_u32(m, _) == False{} : Bool}; e)
    case Inr{en}:
      se = Equal.sym(Maybe<&2, U32>, S.Session.tag(t2), None{}, en)
      (%se : {S.Maybe.same_u32(m, _) == False{} : Bool}; Tg.same_none(m))

# A session tagged with a UE is that UE's.
def Tg.ue_go(+u: U32, +x: U32, +h: Bool, +e: {S.Maybe.same_u32(Tb.Table.hit(U32, u, None{}, h), Some{x}) == True{} : Bool}) -> {U32.is_eq(u, x) == True{} : Bool}:
  match h:
    case True{}:
      e
    case False{}:
      Empty.absurd({U32.is_eq(u, x) == True{} : Bool}, P.Refute.bool(e))

def Tg.ue(+s: S.Session, +x: U32, +e: {S.Maybe.same_u32(S.Session.tag(s), Some{x}) == True{} : Bool}) -> {U32.is_eq(S.Session.ue(s), x) == True{} : Bool}:
  Tg.ue_go(S.Session.ue(s), x, S.SPhase.live(S.Session.phase(s)), e)

# An owned session tagged with a UE has that UE's context.
def Tg.has_go(+u: U32, +x: U32, +h: Bool, +ues: Tb.Table(S.Ue), +e1: {S.Maybe.same_u32(Tb.Table.hit(U32, u, None{}, h), Some{x}) == True{} : Bool}, +e2: {Bool.or(Bool.not(Tb.Table.present(U32, Tb.Table.hit(U32, u, None{}, h))), Tb.Table.has(S.Ue, u, ues)) == True{} : Bool}) -> {Tb.Table.has(S.Ue, x, ues) == True{} : Bool}:
  match h:
    case True{}:
      ex = P.U32.eq_of_is_eq(u, x, e1)
      (%ex : {Tb.Table.has(S.Ue, _, ues) == True{} : Bool}; e2)
    case False{}:
      Empty.absurd({Tb.Table.has(S.Ue, x, ues) == True{} : Bool}, P.Refute.bool(e1))

def Tg.has(+t: S.Session, +x: U32, +ues: Tb.Table(S.Ue), +e1: {S.Maybe.same_u32(S.Session.tag(t), Some{x}) == True{} : Bool}, +e2: {S.Session.owned(t, ues) == True{} : Bool}) -> {Tb.Table.has(S.Ue, x, ues) == True{} : Bool}:
  Tg.has_go(S.Session.ue(t), x, S.SPhase.live(S.Session.phase(t)), ues, e1, e2)

# A context looked up by key
# --------------------------
# N.Ue.found on N.Ue.keyed ends in its none outcome, or in go for a key m
# names and the context find gives under it.

def Walk.with_key(-Q: N.GOut() -> Type, -C: Type, +key: U32, +r: Maybe<&2, S.Ue>, +none: N.GOut(), go: U32 -> S.Ue -> N.GOut(), c: C, hn: C -> Q(none), hg: C -> @ue:S.Ue -> {r == Some{ue} : Maybe<&2, S.Ue>} -> Q(go(key, ue))) -> Q(N.Ue.found(N.Ue.with_key(key, r), none, go)):
  match r:
    case None{}:
      hn(c)
    case Some{+ue}:
      hg(c, ue, {==})

# c is what both outcomes need, handed to the one taken.
def Walk.keyed(-Q: N.GOut() -> Type, -C: Type, +m: Maybe<&2, U32>, find: U32 -> Maybe<&2, S.Ue>, +none: N.GOut(), go: U32 -> S.Ue -> N.GOut(), c: C, hn: C -> Q(none), hg: C -> @key:U32 -> @ue:S.Ue -> {m == Some{key} : Maybe<&2, U32>} -> {find(key) == Some{ue} : Maybe<&2, S.Ue>} -> Q(go(key, ue))) -> Q(N.Ue.found(N.Ue.keyed(m, find), none, go)):
  match m:
    case None{}:
      hn(c)
    case Some{+key}:
      Walk.with_key(Q, C, key, find(key), none, go, c, hn, x => +ue => ef => hg(x, key, ue, {==}, ef))

# Known to name a context, the lookup takes go for it.
def Walk.with_key_eq(+key: U32, +r: Maybe<&2, S.Ue>, none: N.GOut(), go: U32 -> S.Ue -> N.GOut(), +ue: S.Ue, +er: {r == Some{ue} : Maybe<&2, S.Ue>}) -> {N.Ue.found(N.Ue.with_key(key, r), none, go) == go(key, ue) : N.GOut()}:
  ser = Equal.sym(Maybe<&2, S.Ue>, r, Some{ue}, er)
  (%ser : {N.Ue.found(N.Ue.with_key(key, _), none, go) == go(key, ue) : N.GOut()}; {==})

def Walk.keyed_eq(+m: Maybe<&2, U32>, find: U32 -> Maybe<&2, S.Ue>, +key: U32, +ue: S.Ue, none: N.GOut(), go: U32 -> S.Ue -> N.GOut(), +em: {m == Some{key} : Maybe<&2, U32>}, +ef: {find(key) == Some{ue} : Maybe<&2, S.Ue>}) -> {N.Ue.found(N.Ue.keyed(m, find), none, go) == go(key, ue) : N.GOut()}:
  sem = Equal.sym(Maybe<&2, U32>, m, Some{key}, em)
  (%sem : {N.Ue.found(N.Ue.keyed(_, find), none, go) == go(key, ue) : N.GOut()}; Walk.with_key_eq(key, find(key), none, go, ue, ef))

# A Path Switch Request, walked
# -----------------------------
# A Path Switch Request ends in Ps.Ps.fail, which keeps the state, or in the
# switch of a registered context its AMF-UE-NGAP-ID names, whose SUPI 5G-AKA
# verified.

def Pw.Fail(-Q: N.GOut() -> Type, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList()) -> Type:
  @cause:G.Cause -> Q(Ps.Ps.fail(assoc, stream, amf, ran, items, cause))

def Pw.Go(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>) -> Type:
  @key:U32 -> @ue:S.Ue -> @ctx:Sec.Nas.Ctx -> @nh:S.Nh -> @sp:B.Digits() -> {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>} -> {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>} -> {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>} -> Q(Ps.Ps.go(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, S.Sessions.of_ue(key, S.State.sessions(st)), True{}))

def Pw.go(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +sp: B.Digits(), +ok: Bool, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +es: {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>}, fail: Pw.Fail(Q, assoc, stream, amf, ran, items), go: Pw.Go(Q, st, assoc, stream, amf, ran, items, ts)) -> Q(Ps.Ps.go(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, S.Sessions.of_ue(key, S.State.sessions(st)), ok)):
  match ok:
    case False{}:
      fail(N.Ngap.radio_cause(G.CauseRadioNetwork.unknown_PDU_session_ID()))
    case True{}:
      go(key, ue, ctx, nh, sp, ek, eg, es)

def Pw.free(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +sp: B.Digits(), +ok: Bool, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +es: {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>}, fail: Pw.Fail(Q, assoc, stream, amf, ran, items), go: Pw.Go(Q, st, assoc, stream, amf, ran, items, ts)) -> Q(Ps.Ps.free(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, ok)):
  match ok:
    case False{}:
      fail(N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified()))
    case True{}:
      Pw.go(Q, st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, sp, Sw.Sw.any(ts, S.Sessions.of_ue(key, S.State.sessions(st))), ek, eg, es, fail, go)

def Pw.identified(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +supi: Maybe<&2, B.Digits()>, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +es: {S.Ue.supi(ue) == supi : Maybe<&2, B.Digits()>}, fail: Pw.Fail(Q, assoc, stream, amf, ran, items), go: Pw.Go(Q, st, assoc, stream, amf, ran, items, ts)) -> Q(Ps.Ps.identified(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, supi)):
  match supi:
    case None{}:
      fail(Ps.Ps.unknown())
    case Some{+sp}:
      Pw.free(Q, st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, sp, S.Ues.ran_free(key, assoc, ran, S.State.ues(st)), ek, eg, es, fail, go)

def Pw.phase(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, +p: S.Phase, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, fail: Pw.Fail(Q, assoc, stream, amf, ran, items), go: Pw.Go(Q, st, assoc, stream, amf, ran, items, ts)) -> Q(Ps.Ps.phase(st, assoc, stream, amf, ran, items, ts, key, ue, p)):
  match p:
    case S.Created{}:
      fail(Ps.Ps.unknown())
    case S.Identifying{guard}:
      fail(Ps.Ps.unknown())
    case S.Authenticating{guard, av, resynced, supi}:
      fail(Ps.Ps.unknown())
    case S.SecurityMode{guard, ctx, k_amf}:
      fail(Ps.Ps.unknown())
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      fail(Ps.Ps.unknown())
    case S.Registered{+ctx, +nh, released}:
      Pw.identified(Q, st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, S.Ue.supi(ue), ek, eg, {==}, fail, go)
    case S.Switching{guard, ctx, nh, released}:
      fail(Ps.Ps.unknown())
    case S.Handover{ctx, nh, source, leg}:
      fail(Ps.Ps.unknown())
    case S.Releasing{guard}:
      fail(Ps.Ps.unknown())

def Pw.claim(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, fail: Pw.Fail(Q, assoc, stream, amf, ran, items), go: Pw.Go(Q, st, assoc, stream, amf, ran, items, ts)) -> Q(Ps.Ps.claim(st, assoc, stream, amf, ran, items, ts, Ps.Ps.named(st, amf))):
  Walk.keyed(Q, Pw.Fail(Q, assoc, stream, amf, ran, items), N.Ngap.ue_key(amf), k => Tb.Table.get(S.Ue, k, S.State.ues(st)), Ps.Ps.fail(assoc, stream, amf, ran, items, Ps.Ps.unknown()), +key => +ue => Ps.Ps.phase(st, assoc, stream, amf, ran, items, ts, key, ue, S.Ue.phase(ue)), fail, f => f(Ps.Ps.unknown()), f => +key => +ue => ek => eg => Pw.phase(Q, st, assoc, stream, amf, ran, items, ts, key, ue, S.Ue.phase(ue), ek, eg, f, go))

# The N2 handover messages' checks, walked once
# ---------------------------------------------
# Each message from the source ends with the view not read, the UE unknown
# (Hw.Unknown), or in a leaf for a context its AMF-UE-NGAP-ID names that the
# association owns under its RAN-UE-NGAP-ID; each answer from the target, in
# a leaf for the context whose handover is pending to the association. Every
# leaf gets the context's key and phase.

def Hw.Bad(Q: N.GOut() -> Type, +assoc: U32) -> Type:
  Q((S.Keep{}, N.Ngap.bad_view(assoc)))

def Hw.Unknown(Q: N.GOut() -> Type, +assoc: U32) -> Type:
  Q((S.Keep{}, N.Ngap.unknown_ue(assoc)))

# Handover Required: refused, or the target asked.

def Hw.RFail(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes()) -> Type:
  @key:U32 -> @ue:S.Ue -> @c:G.Cause -> {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>} -> {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>} -> Q(Ho.Ho.fail(key, ue, c))

def Hw.RGo(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes()) -> Type:
  @key:U32 -> @ue:S.Ue -> @ctx:Sec.Nas.Ctx -> @nh:S.Nh -> @t:U32 -> @cfg:S.Cfg -> @cause:G.Cause -> @container:B.Bytes() -> @i:G.PDUSessionResourceSetupItemHOReq -> @more:G.PDUSessionResourceSetupListHOReq() -> {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>} -> {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>} -> {U32.is_eq(t, S.Ue.assoc(ue)) == False{} : Bool} -> Q(Ho.Ho.prepare(key, ue, ctx, nh, t, cfg, cause, container, i <> more))

def Hw.prepare(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +t: U32, +cfg: S.Cfg, +cause: G.Cause, +container: B.Bytes(), +items: G.PDUSessionResourceSetupListHOReq(), +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(t, S.Ue.assoc(ue)) == False{} : Bool}, fail: Hw.RFail(Q, st, assoc, amf, ran), go: Hw.RGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.prepare(key, ue, ctx, nh, t, cfg, cause, container, items)):
  match items:
    case Nil{}:
      fail(key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unknown_PDU_session_ID()), ek, eo)
    case +i <> +more:
      go(key, ue, ctx, nh, t, cfg, cause, container, i, more, ek, eo, ne)

def Hw.cfg(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +t: U32, +cause: G.Cause, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +m: Maybe<&2, S.Cfg>, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(t, S.Ue.assoc(ue)) == False{} : Bool}, fail: Hw.RFail(Q, st, assoc, amf, ran), go: Hw.RGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.required_cfg(st, key, ue, ctx, nh, t, cause, items, container, m)):
  match m:
    case None{}:
      fail(key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unspecified()), ek, eo)
    case Some{+cfg}:
      Hw.prepare(Q, st, assoc, amf, ran, key, ue, ctx, nh, t, cfg, cause, container, Ho.Ho.setup_items(cfg, items, S.Sessions.of_ue(key, S.State.sessions(st))), ek, eo, ne, fail, go)

def Hw.other(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +released: Maybe<&2, S.Side>, +t: U32, +cause: G.Cause, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +same: Bool, +es: {Bool.or(S.Side.unanswered(released, t), U32.is_eq(t, S.Ue.assoc(ue))) == same : Bool}, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}, fail: Hw.RFail(Q, st, assoc, amf, ran), go: Hw.RGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.required_other(st, key, ue, ctx, nh, t, cause, items, container, same)):
  match same:
    case True{}:
      fail(key, ue, Ho.Ho.radio(G.CauseRadioNetwork.ho_target_not_allowed()), ek, eo)
    case False{}:
      Hw.cfg(Q, st, assoc, amf, ran, key, ue, ctx, nh, t, cause, items, container, S.State.config(st), ek, eo, P.Bool.or_false_r(S.Side.unanswered(released, t), U32.is_eq(t, S.Ue.assoc(ue)), es), fail, go)

def Hw.target(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +released: Maybe<&2, S.Side>, +cause: G.Cause, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +m: Maybe<&2, U32>, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}, fail: Hw.RFail(Q, st, assoc, amf, ran), go: Hw.RGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.required_target(st, key, ue, ctx, nh, released, cause, items, container, m)):
  match m:
    case None{}:
      fail(key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unknown_targetID()), ek, eo)
    case Some{+t}:
      Hw.other(Q, st, assoc, amf, ran, key, ue, ctx, nh, released, t, cause, items, container, Bool.or(S.Side.unanswered(released, t), U32.is_eq(t, S.Ue.assoc(ue))), {==}, ek, eo, fail, go)

def Hw.required_phase(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +key: U32, +ue: S.Ue, +kind: G.HandoverType(), +cause: G.Cause, +id: G.TargetID, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +p: S.Phase, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}, fail: Hw.RFail(Q, st, assoc, amf, ran), go: Hw.RGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.required_phase(st, key, ue, kind, cause, id, items, container, p)):
  match p:
    case S.Registered{+ctx, +nh, +released}:
      Hw.target(Q, st, assoc, amf, ran, key, ue, ctx, nh, released, cause, items, container, Ho.Ho.target(st, Ho.Ho.intra_type(kind), Ho.Ho.node(id)), ek, eo, fail, go)
    case S.Created{}:
      fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), ek, eo)
    case S.Identifying{guard}:
      fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), ek, eo)
    case S.Authenticating{guard, av, resynced, supi}:
      fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), ek, eo)
    case S.SecurityMode{guard, ctx, k_amf}:
      fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), ek, eo)
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), ek, eo)
    case S.Switching{guard, ctx, nh, released}:
      fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), ek, eo)
    case S.Releasing{guard}:
      fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), ek, eo)
    case S.Handover{ctx, nh, source, leg}:
      fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), ek, eo)

def Hw.required_found(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +kind: G.HandoverType(), +cause: G.Cause, +id: G.TargetID, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), none: Hw.Unknown(Q, assoc), fail: Hw.RFail(Q, st, assoc, amf, ran), go: Hw.RGo(Q, st, assoc, amf, ran)) -> Q(N.Ue.found(Ho.Ho.by_owner(st, assoc, ran, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.required_phase(st, key, ue, kind, cause, id, items, container, S.Ue.phase(ue)))):
  Walk.keyed(Q, Hw.Unknown(Q, assoc), N.Ngap.ue_key(amf), k => N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.required_phase(st, key, ue, kind, cause, id, items, container, S.Ue.phase(ue)), none, n => n, n => +key => +ue => ek => eo => Hw.required_phase(Q, st, assoc, amf, ran, key, ue, kind, cause, id, items, container, S.Ue.phase(ue), ek, eo, fail, go))

def Hw.required(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverRequired.View>, bad: Hw.Bad(Q, assoc), none: Hw.Unknown(Q, assoc), fail: @amf:B.Bytes() -> @ran:B.Bytes() -> Hw.RFail(Q, st, assoc, amf, ran), go: @amf:B.Bytes() -> @ran:B.Bytes() -> Hw.RGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.required_of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      bad
    case Done{V.HandoverRequired.View{+amf, +ran, +kind, +cause, +id, direct, +items, +container}}:
      Hw.required_found(Q, st, assoc, amf, ran, kind, cause, id, items, container, none, fail(amf, ran), go(amf, ran))

# Handover Cancel: acknowledged with no handover pending, or the target released.

def Hw.CIdle(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes()) -> Type:
  @key:U32 -> @ue:S.Ue -> {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>} -> {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>} -> {S.Phase.pending(S.Ue.phase(ue)) == None{} : Maybe<&2, U32>} -> Q((S.Keep{}, [N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.cancel_ack(key, S.Ue.ran_id(ue))}, N.Note{F.Warn{}, "NGAP: Handover Cancel with no handover pending"}]))

def Hw.CGo(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes()) -> Type:
  @key:U32 -> @ue:S.Ue -> @ctx:Sec.Nas.Ctx -> @nh:S.Nh -> @source:U32 -> @leg:S.Leg -> {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>} -> {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>} -> {S.Ue.phase(ue) == S.Handover{ctx, nh, source, leg} : S.Phase} -> Q(Ho.Ho.cancel_phase(key, ue, S.Handover{ctx, nh, source, leg}))

# A phase with no handover pending, the context's.
def Hw.idle(+ue: S.Ue, +p: S.Phase, +eph: {S.Ue.phase(ue) == p : S.Phase}, +en: {S.Phase.pending(p) == None{} : Maybe<&2, U32>}) -> {S.Phase.pending(S.Ue.phase(ue)) == None{} : Maybe<&2, U32>}:
  sp = Equal.sym(S.Phase, S.Ue.phase(ue), p, eph)
  (%sp : {S.Phase.pending(_) == None{} : Maybe<&2, U32>}; en)

def Hw.cancel_phase(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +key: U32, +ue: S.Ue, +p: S.Phase, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == p : S.Phase}, idle: Hw.CIdle(Q, st, assoc, amf, ran), go: Hw.CGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.cancel_phase(key, ue, p)):
  match p:
    case S.Handover{+ctx, +nh, +source, +leg}:
      go(key, ue, ctx, nh, source, leg, ek, eo, eph)
    case S.Created{}:
      idle(key, ue, ek, eo, Hw.idle(ue, S.Created{}, eph, {==}))
    case S.Identifying{guard}:
      idle(key, ue, ek, eo, Hw.idle(ue, S.Identifying{guard}, eph, {==}))
    case S.Authenticating{guard, av, resynced, supi}:
      idle(key, ue, ek, eo, Hw.idle(ue, S.Authenticating{guard, av, resynced, supi}, eph, {==}))
    case S.SecurityMode{guard, ctx, k_amf}:
      idle(key, ue, ek, eo, Hw.idle(ue, S.SecurityMode{guard, ctx, k_amf}, eph, {==}))
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      idle(key, ue, ek, eo, Hw.idle(ue, S.ContextSetup{guard, ctx, nh, response, complete}, eph, {==}))
    case S.Registered{ctx, nh, released}:
      idle(key, ue, ek, eo, Hw.idle(ue, S.Registered{ctx, nh, released}, eph, {==}))
    case S.Switching{guard, ctx, nh, released}:
      idle(key, ue, ek, eo, Hw.idle(ue, S.Switching{guard, ctx, nh, released}, eph, {==}))
    case S.Releasing{guard}:
      idle(key, ue, ek, eo, Hw.idle(ue, S.Releasing{guard}, eph, {==}))

def Hw.cancel_found(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), none: Hw.Unknown(Q, assoc), idle: Hw.CIdle(Q, st, assoc, amf, ran), go: Hw.CGo(Q, st, assoc, amf, ran)) -> Q(N.Ue.found(Ho.Ho.by_owner(st, assoc, ran, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.cancel_phase(key, ue, S.Ue.phase(ue)))):
  Walk.keyed(Q, Hw.Unknown(Q, assoc), N.Ngap.ue_key(amf), k => N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.cancel_phase(key, ue, S.Ue.phase(ue)), none, n => n, n => +key => +ue => ek => eo => Hw.cancel_phase(Q, st, assoc, amf, ran, key, ue, S.Ue.phase(ue), ek, eo, {==}, idle, go))

def Hw.cancel(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverCancel.View>, bad: Hw.Bad(Q, assoc), none: Hw.Unknown(Q, assoc), idle: @amf:B.Bytes() -> @ran:B.Bytes() -> Hw.CIdle(Q, st, assoc, amf, ran), go: @amf:B.Bytes() -> @ran:B.Bytes() -> Hw.CGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.cancel_of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      bad
    case Done{V.HandoverCancel.View{+amf, +ran, cause}}:
      Hw.cancel_found(Q, st, assoc, amf, ran, none, idle(amf, ran), go(amf, ran))

# Uplink RAN Status Transfer: dropped with no target ready, or relayed.

def Hw.Warn(Q: N.GOut() -> Type) -> Type:
  Q(N.Out.warn("NGAP: Uplink RAN Status Transfer with no target ready"))

def Hw.SGo(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +container: G.RANStatusTransfer_TransparentContainer) -> Type:
  @key:U32 -> @ue:S.Ue -> @t:U32 -> @r:B.Bytes() -> @s:U32 -> {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>} -> {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>} -> Q((S.Keep{}, [N.UeSend{t, s, key, Ho.Ho.dl_status(key, r, container)}]))

def Hw.status_phase(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +container: G.RANStatusTransfer_TransparentContainer, +key: U32, +ue: S.Ue, +p: S.Phase, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}, warn: Hw.Warn(Q), go: Hw.SGo(Q, st, assoc, amf, ran, container)) -> Q(Ho.Ho.status_phase(key, container, p)):
  match p:
    case S.Handover{ctx, nh, source, leg}:
      match leg:
        case S.Asked{t}:
          warn
        case S.Acked{+t, +r, +s, ts}:
          go(key, ue, t, r, s, ek, eo)
    case S.Created{}:
      warn
    case S.Identifying{guard}:
      warn
    case S.Authenticating{guard, av, resynced, supi}:
      warn
    case S.SecurityMode{guard, ctx, k_amf}:
      warn
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      warn
    case S.Registered{ctx, nh, released}:
      warn
    case S.Switching{guard, ctx, nh, released}:
      warn
    case S.Releasing{guard}:
      warn

def Hw.status_found(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +container: G.RANStatusTransfer_TransparentContainer, none: Hw.Unknown(Q, assoc), warn: Hw.Warn(Q), go: Hw.SGo(Q, st, assoc, amf, ran, container)) -> Q(N.Ue.found(Ho.Ho.by_owner(st, assoc, ran, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.status_phase(key, container, S.Ue.phase(ue)))):
  Walk.keyed(Q, Hw.Unknown(Q, assoc), N.Ngap.ue_key(amf), k => N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.status_phase(key, container, S.Ue.phase(ue)), none, n => n, n => +key => +ue => ek => eo => Hw.status_phase(Q, st, assoc, amf, ran, container, key, ue, S.Ue.phase(ue), ek, eo, warn, go))

def Hw.status(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View>, bad: Hw.Bad(Q, assoc), none: Hw.Unknown(Q, assoc), warn: Hw.Warn(Q), go: @amf:B.Bytes() -> @ran:B.Bytes() -> @container:G.RANStatusTransfer_TransparentContainer -> Hw.SGo(Q, st, assoc, amf, ran, container)) -> Q(Ho.Ho.status_of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      bad
    case Done{V.UplinkRANStatusTransfer.View{+amf, +ran, +container}}:
      Hw.status_found(Q, st, assoc, amf, ran, container, none, warn, go(amf, ran, container))

# Handover Request Acknowledge to a target asked: Handover Command.

def Hw.AGo(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes()) -> Type:
  @key:U32 -> @ue:S.Ue -> @ctx:Sec.Nas.Ctx -> @nh:S.Nh -> @source:U32 -> @t:U32 -> {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>} -> {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>} -> {S.Ue.phase(ue) == S.Handover{ctx, nh, source, S.Asked{t}} : S.Phase} -> Q(Ho.Ho.ack_phase(assoc, stream, key, ue, ran, admitted, container, S.Handover{ctx, nh, source, S.Asked{t}}))

def Hw.ack_phase(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes(), +key: U32, +ue: S.Ue, +p: S.Phase, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == p : S.Phase}, none: Hw.Unknown(Q, assoc), go: Hw.AGo(Q, st, assoc, stream, amf, ran, admitted, container)) -> Q(Ho.Ho.ack_phase(assoc, stream, key, ue, ran, admitted, container, p)):
  match p:
    case S.Handover{+ctx, +nh, +source, leg}:
      match leg:
        case S.Asked{+t}:
          go(key, ue, ctx, nh, source, t, ek, ep, eph)
        case S.Acked{t, r, s, ts}:
          none
    case S.Created{}:
      none
    case S.Identifying{guard}:
      none
    case S.Authenticating{guard, av, resynced, supi}:
      none
    case S.SecurityMode{guard, ctx, k_amf}:
      none
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      none
    case S.Registered{ctx, nh, released}:
      none
    case S.Switching{guard, ctx, nh, released}:
      none
    case S.Releasing{guard}:
      none

def Hw.ack_found(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes(), none: Hw.Unknown(Q, assoc), go: Hw.AGo(Q, st, assoc, stream, amf, ran, admitted, container)) -> Q(N.Ue.found(Ho.Ho.by_target(st, assoc, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.ack_phase(assoc, stream, key, ue, ran, admitted, container, S.Ue.phase(ue)))):
  Walk.keyed(Q, Hw.Unknown(Q, assoc), N.Ngap.ue_key(amf), k => Ho.Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.ack_phase(assoc, stream, key, ue, ran, admitted, container, S.Ue.phase(ue)), none, n => n, n => +key => +ue => ek => ep => Hw.ack_phase(Q, st, assoc, stream, amf, ran, admitted, container, key, ue, S.Ue.phase(ue), ek, ep, {==}, n, go))

def Hw.ack(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +r: Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View>, bad: Hw.Bad(Q, assoc), none: Hw.Unknown(Q, assoc), go: @amf:B.Bytes() -> @ran:B.Bytes() -> @admitted:G.PDUSessionResourceAdmittedList() -> @container:B.Bytes() -> Hw.AGo(Q, st, assoc, stream, amf, ran, admitted, container)) -> Q(Ho.Ho.ack_of_view(st, assoc, stream, r)):
  match r:
    case Fail{e}:
      bad
    case Done{V.HandoverRequestAcknowledge.View{+amf, +ran, +admitted, failed, +container, diag, npn}}:
      Hw.ack_found(Q, st, assoc, stream, amf, ran, admitted, container, none, go(amf, ran, admitted, container))

# Handover Failure from a target asked: Handover Preparation Failure.

def Hw.FGo(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +cause: G.Cause) -> Type:
  @key:U32 -> @ue:S.Ue -> @ctx:Sec.Nas.Ctx -> @nh:S.Nh -> @source:U32 -> @t:U32 -> {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>} -> {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>} -> {S.Ue.phase(ue) == S.Handover{ctx, nh, source, S.Asked{t}} : S.Phase} -> Q(Ho.Ho.failure_phase(assoc, key, ue, cause, S.Handover{ctx, nh, source, S.Asked{t}}))

def Hw.failure_phase(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +cause: G.Cause, +key: U32, +ue: S.Ue, +p: S.Phase, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == p : S.Phase}, none: Hw.Unknown(Q, assoc), go: Hw.FGo(Q, st, assoc, amf, cause)) -> Q(Ho.Ho.failure_phase(assoc, key, ue, cause, p)):
  match p:
    case S.Handover{+ctx, +nh, +source, leg}:
      match leg:
        case S.Asked{+t}:
          go(key, ue, ctx, nh, source, t, ek, ep, eph)
        case S.Acked{t, r, s, ts}:
          none
    case S.Created{}:
      none
    case S.Identifying{guard}:
      none
    case S.Authenticating{guard, av, resynced, supi}:
      none
    case S.SecurityMode{guard, ctx, k_amf}:
      none
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      none
    case S.Registered{ctx, nh, released}:
      none
    case S.Switching{guard, ctx, nh, released}:
      none
    case S.Releasing{guard}:
      none

def Hw.failure_found(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +cause: G.Cause, none: Hw.Unknown(Q, assoc), go: Hw.FGo(Q, st, assoc, amf, cause)) -> Q(N.Ue.found(Ho.Ho.by_target(st, assoc, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.failure_phase(assoc, key, ue, cause, S.Ue.phase(ue)))):
  Walk.keyed(Q, Hw.Unknown(Q, assoc), N.Ngap.ue_key(amf), k => Ho.Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.failure_phase(assoc, key, ue, cause, S.Ue.phase(ue)), none, n => n, n => +key => +ue => ek => ep => Hw.failure_phase(Q, st, assoc, amf, cause, key, ue, S.Ue.phase(ue), ek, ep, {==}, n, go))

def Hw.failure(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverFailure.View>, bad: Hw.Bad(Q, assoc), none: Hw.Unknown(Q, assoc), go: @amf:B.Bytes() -> @cause:G.Cause -> Hw.FGo(Q, st, assoc, amf, cause)) -> Q(Ho.Ho.failure_of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      bad
    case Done{V.HandoverFailure.View{+amf, +cause, diag}}:
      Hw.failure_found(Q, st, assoc, amf, cause, none, go(amf, cause))

# Handover Notify from the target acknowledged, under the RAN-UE-NGAP-ID it
# gave, still free on it: the UE, its SUPI verified, moves.

def Hw.NGo(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes()) -> Type:
  @key:U32 -> @ue:S.Ue -> @ctx:Sec.Nas.Ctx -> @nh:S.Nh -> @source:U32 -> @t:U32 -> @r:B.Bytes() -> @s:U32 -> @ts:List<&2, S.Tunnel> -> @sp:B.Digits() -> {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>} -> {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>} -> {S.Ue.phase(ue) == S.Handover{ctx, nh, source, S.Acked{t, r, s, ts}} : S.Phase} -> {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>} -> Q(Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, True{}))

def Hw.complete(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +source: U32, +t: U32, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +sp: B.Digits(), +ok: Bool, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == S.Handover{ctx, nh, source, S.Acked{t, r, s, ts}} : S.Phase}, +es: {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>}, none: Hw.Unknown(Q, assoc), go: Hw.NGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, ok)):
  match ok:
    case False{}:
      none
    case True{}:
      go(key, ue, ctx, nh, source, t, r, s, ts, sp, ek, ep, eph, es)

# The context a target's answer is for has its SUPI verified.
def Walk.aimed_supi(+ue: S.Ue, +assoc: U32, +e: {Ho.Ho.aimed(ue, assoc) == True{} : Bool}) -> {Tb.Table.present(B.Digits(), S.Ue.supi(ue)) == True{} : Bool}:
  +rest = Bool.and(Tb.Table.present(B.Digits(), S.Ue.supi(ue)), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc)))
  P.Bool.and_true_l(Tb.Table.present(B.Digits(), S.Ue.supi(ue)), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc)), P.Bool.and_true_r(S.Maybe.same_u32(S.Phase.pending(S.Ue.phase(ue)), Some{assoc}), rest, e))

def Walk.first(-A: Type, -B: Type, pr: A & B) -> A:
  match pr:
    case (a, b):
      a

def Walk.second(-A: Type, -B: Type, pr: A & B) -> B:
  match pr:
    case (a, b):
      b

def Hw.notify_supi(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +source: U32, +t: U32, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +supi: Maybe<&2, B.Digits()>, +es: {S.Ue.supi(ue) == supi : Maybe<&2, B.Digits()>}, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == S.Handover{ctx, nh, source, S.Acked{t, r, s, ts}} : S.Phase}, none: Hw.Unknown(Q, assoc), go: Hw.NGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, Bool.and(B.bytes_eq(r, ran), S.Ues.ran_free(key, assoc, r, S.State.ues(st))))):
  match supi:
    case None{}:
      ea = Walk.second({Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, {Ho.Ho.aimed(ue, assoc) == True{} : Bool}, Walk.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ue, ep))
      en : {Tb.Table.present(B.Digits(), None{}) == True{} : Bool} = (%es : {Tb.Table.present(B.Digits(), _) == True{} : Bool}; Walk.aimed_supi(ue, assoc, ea))
      Empty.absurd(Q(Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, Bool.and(B.bytes_eq(r, ran), S.Ues.ran_free(key, assoc, r, S.State.ues(st))))), P.Refute.bool(en))
    case Some{+sp}:
      Hw.complete(Q, st, assoc, amf, ran, key, ue, ctx, nh, source, t, r, s, ts, sp, Bool.and(B.bytes_eq(r, ran), S.Ues.ran_free(key, assoc, r, S.State.ues(st))), ek, ep, eph, es, none, go)

def Hw.notify_phase(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +key: U32, +ue: S.Ue, +p: S.Phase, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == p : S.Phase}, none: Hw.Unknown(Q, assoc), go: Hw.NGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.notify_phase(st, assoc, key, ue, ran, p)):
  match p:
    case S.Handover{+ctx, +nh, +source, leg}:
      match leg:
        case S.Asked{t}:
          none
        case S.Acked{+t, +r, +s, +ts}:
          Hw.notify_supi(Q, st, assoc, amf, ran, key, ue, ctx, nh, source, t, r, s, ts, S.Ue.supi(ue), {==}, ek, ep, eph, none, go)
    case S.Created{}:
      none
    case S.Identifying{guard}:
      none
    case S.Authenticating{guard, av, resynced, supi}:
      none
    case S.SecurityMode{guard, ctx, k_amf}:
      none
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      none
    case S.Registered{ctx, nh, released}:
      none
    case S.Switching{guard, ctx, nh, released}:
      none
    case S.Releasing{guard}:
      none

def Hw.notify_found(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), none: Hw.Unknown(Q, assoc), go: Hw.NGo(Q, st, assoc, amf, ran)) -> Q(N.Ue.found(Ho.Ho.by_target(st, assoc, amf), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.notify_phase(st, assoc, key, ue, ran, S.Ue.phase(ue)))):
  Walk.keyed(Q, Hw.Unknown(Q, assoc), N.Ngap.ue_key(amf), k => Ho.Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc), (S.Keep{}, N.Ngap.unknown_ue(assoc)), +key => +ue => Ho.Ho.notify_phase(st, assoc, key, ue, ran, S.Ue.phase(ue)), none, n => n, n => +key => +ue => ek => ep => Hw.notify_phase(Q, st, assoc, amf, ran, key, ue, S.Ue.phase(ue), ek, ep, {==}, n, go))

def Hw.notify(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverNotify.View>, bad: Hw.Bad(Q, assoc), none: Hw.Unknown(Q, assoc), go: @amf:B.Bytes() -> @ran:B.Bytes() -> Hw.NGo(Q, st, assoc, amf, ran)) -> Q(Ho.Ho.notify_of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      bad
    case Done{V.HandoverNotify.View{+amf, +ran, uli}}:
      Hw.notify_found(Q, st, assoc, amf, ran, none, go(amf, ran))
