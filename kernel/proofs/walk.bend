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
import ../smf/switch.bend as Sw
import ../nas/security.bend as Sec

# The step function, walked once
# ------------------------------
# A step ends in one of four ways: the state as it was, with actions that
# name no UE context (an NGAP PDU or IE list that does not decode, an
# incomplete Config, an association coming up); the same with the
# associations set up changed (NG Setup); a procedure's outcome o rendered by
# N.Step.of (a routed NGAP message, a PFCP message, a timer); or a new
# configuration or an association going down. A property Q of steps holds after every step
# when it holds after each of them, the outcomes known only by a property ok
# that each of them has.

def Walk.Keep(-Q: N.Step() -> Type, +st: S.State) -> Type:
  @acts:List<&2, N.Act> -> (@k:U32 -> {N.Acts.spare(k, acts) == True{} : Bool}) -> Q((st, acts))

# NG Setup: the associations set up change, nothing else, and the actions name no UE context.
def Walk.Ready(-Q: N.Step() -> Type, +st: S.State) -> Type:
  @as:Tb.Table(B.Bytes()) -> @acts:List<&2, N.Act> -> (@k:U32 -> {N.Acts.spare(k, acts) == True{} : Bool}) -> Q((S.State.with_assocs(st, as), acts))

def Walk.Out(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State) -> Type:
  @o:N.GOut() -> ok(o) -> Q(N.Step.of(st, o))

# The outcome of every NGAP message that is not NG Setup.
def Walk.Routed(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes()) -> Type:
  @kind:Nat -> @code:Nat -> @ies:List<&2, Fr.Ie> -> ok(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code)))

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

def Walk.setup(-Q: N.Step() -> Type, +st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.NGSetupRequest.View>, keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st)) -> Q(N.NgSetup.of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      keep(N.Ngap.bad_view(assoc), k => {==})
    case Done{+v}:
      ready(S.Assocs.set(assoc, N.NgSetup.node(v), S.State.assocs(st), N.NgSetup.supported_view(S.State.config(st), v)), [N.Setup{assoc, N.NgSetup.reply(S.State.config(st), v)}], k => {==})

def Walk.d1(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, b)):
  match b:
    case True{}:
      Walk.setup(Q, st, assoc, V.NGSetupRequest.view(ies), keep, ready)
    case False{}:
      out(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code)), routed(kind, code, ies))

def Walk.ies(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +entropy: B.Bytes(), +r: Ap.Rd(List<&2, Fr.Ie>), keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r)):
  match r:
    case Fail{err}:
      keep(N.Ngap.bad_pdu(assoc), k => {==})
    case Done{(+ies, c)}:
      Walk.d1(Q, ok, st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_ng_setup(kind, code), keep, ready, out, routed)

def Walk.pdu(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Fr.Pdu>, keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.of_pdu(st, assoc, stream, entropy, r)):
  match r:
    case Fail{err}:
      keep(N.Ngap.bad_pdu(assoc), k => {==})
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Walk.ies(Q, ok, st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), keep, ready, out, routed)

def Walk.step(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), down: @assoc:U32 -> Q(K.Kernel.assoc_down(st, assoc)), out: Walk.Out(Q, ok, st), routed: @assoc:U32 -> @stream:U32 -> Walk.Routed(ok, st, assoc, stream, entropy), pfcp: @bytes:B.Bytes() -> ok(Gsm.Gsm.pfcp_data(st, bytes)), fired: @timer:U32 -> ok(K.Kernel.fired(st, timer))) -> Q(K.Kernel.step(st, ev, entropy)):
  match ev:
    case F.Config{len, +tlvs}:
      config(tlvs)
    case F.NgapAssocUp{assoc}:
      keep([], k => {==})
    case F.NgapAssocDown{assoc}:
      down(assoc)
    case F.NgapData{+assoc, +stream, len, +bytes}:
      Walk.pdu(Q, ok, st, assoc, stream, entropy, Fr.Pdu.read(bytes), keep, ready, out, routed(assoc, stream))
    case F.PfcpData{len, +bytes}:
      out(Gsm.Gsm.pfcp_data(st, bytes), pfcp(bytes))
    case F.TimerFired{+timer}:
      out(K.Kernel.fired(st, timer), fired(timer))

# A property that holds after any outcome.
def Walk.any(-Q: N.Step() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), down: @assoc:U32 -> Q(K.Kernel.assoc_down(st, assoc)), out: @o:N.GOut() -> Q(N.Step.of(st, o))) -> Q(K.Kernel.step(st, ev, entropy)):
  Walk.step(Q, o => Unit, st, ev, entropy, keep, ready, config, down, o => u => out(o), a => s => kind => code => ies => Unit{}, bytes => Unit{}, timer => Unit{})

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

def Pw.ready(-Q: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +ok: Bool, fail: Pw.Fail(Q, assoc, stream, amf, ran, items), go: Pw.Go(Q, st, assoc, stream, amf, ran, items, ts)) -> Q(Ps.Ps.ready(st, assoc, stream, amf, ran, items, ts, Ps.Ps.named(st, amf), ok)):
  match ok:
    case False{}:
      fail(N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()))
    case True{}:
      Walk.keyed(Q, Pw.Fail(Q, assoc, stream, amf, ran, items), N.Ngap.ue_key(amf), k => Tb.Table.get(S.Ue, k, S.State.ues(st)), Ps.Ps.fail(assoc, stream, amf, ran, items, Ps.Ps.unknown()), +key => +ue => Ps.Ps.phase(st, assoc, stream, amf, ran, items, ts, key, ue, S.Ue.phase(ue)), fail, f => f(Ps.Ps.unknown()), f => +key => +ue => ek => eg => Pw.phase(Q, st, assoc, stream, amf, ran, items, ts, key, ue, S.Ue.phase(ue), ek, eg, f, go))
