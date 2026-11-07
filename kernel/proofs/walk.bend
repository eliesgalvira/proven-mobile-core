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
# name no UE context (an NGAP PDU or IE list that does not decode, a message
# from an association without NG Setup, an incomplete Config, an association
# coming up); an association's UE contexts released and the associations set
# up changed (NG Setup); a procedure's outcome o rendered by N.Step.of (a
# routed NGAP message, a PFCP message, a timer); a new configuration; or an
# association going down. A property Q of steps holds after every step
# when it holds after each of them, the outcomes known only by a property ok
# that each of them has.

def Walk.Keep(-Q: N.Step() -> Type, +st: S.State) -> Type:
  @acts:List<&2, N.Act> -> (@k:U32 -> {N.Acts.spare(k, acts) == True{} : Bool}) -> Q((st, acts))

# NG Setup: the association's UE-related contexts re-initialised, then the
# associations set up changed, with actions that name no UE context.
def Walk.Ready(-Q: N.Step() -> Type, +st: S.State, +assoc: U32) -> Type:
  @as:Tb.Table(B.Bytes()) -> @acts:List<&2, N.Act> -> (@k:U32 -> {N.Acts.spare(k, acts) == True{} : Bool}) -> Q((S.State.with_assocs(N.Step.state(R.Route.drop(st, assoc)), as), List.append(&2, N.Act, N.Step.acts(R.Route.drop(st, assoc)), acts)))

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

def Walk.setup(-Q: N.Step() -> Type, +st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.NGSetupRequest.View>, keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st, assoc)) -> Q(R.Route.setup(st, assoc, r)):
  match r:
    case Fail{e}:
      keep(N.Ngap.bad_view(assoc), k => {==})
    case Done{+v}:
      ready(S.Assocs.set(assoc, N.NgSetup.node(v), S.State.assocs(N.Step.state(R.Route.drop(st, assoc))), N.NgSetup.supported_view(S.State.config(st), v)), [N.Setup{assoc, N.NgSetup.reply(S.State.config(st), v)}], k => {==})

def Walk.ready(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, keep: Walk.Keep(Q, st), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.ready(st, assoc, stream, kind, code, ies, entropy, b)):
  match b:
    case True{}:
      out(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code)), routed(kind, code, ies))
    case False{}:
      keep(N.Ngap.unhandled(assoc), k => {==})

def Walk.d1(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st, assoc), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, b)):
  match b:
    case True{}:
      Walk.setup(Q, st, assoc, V.NGSetupRequest.view(ies), keep, ready)
    case False{}:
      Walk.ready(Q, ok, st, assoc, stream, kind, code, ies, entropy, S.Assocs.has(assoc, S.State.assocs(st)), keep, out, routed)

def Walk.ies(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +entropy: B.Bytes(), +r: Ap.Rd(List<&2, Fr.Ie>), keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st, assoc), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r)):
  match r:
    case Fail{err}:
      keep(N.Ngap.bad_pdu(assoc), k => {==})
    case Done{(+ies, c)}:
      Walk.d1(Q, ok, st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_ng_setup(kind, code), keep, ready, out, routed)

def Walk.pdu(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Fr.Pdu>, keep: Walk.Keep(Q, st), ready: Walk.Ready(Q, st, assoc), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.of_pdu(st, assoc, stream, entropy, r)):
  match r:
    case Fail{err}:
      keep(N.Ngap.bad_pdu(assoc), k => {==})
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Walk.ies(Q, ok, st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), keep, ready, out, routed)

def Walk.step(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: Walk.Keep(Q, st), ready: @assoc:U32 -> Walk.Ready(Q, st, assoc), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), down: @assoc:U32 -> Q(R.Route.down(st, assoc)), out: Walk.Out(Q, ok, st), routed: @assoc:U32 -> @stream:U32 -> Walk.Routed(ok, st, assoc, stream, entropy), pfcp: @bytes:B.Bytes() -> ok(Gsm.Gsm.pfcp_data(st, bytes)), fired: @timer:U32 -> ok(K.Kernel.fired(st, timer))) -> Q(K.Kernel.step(st, ev, entropy)):
  match ev:
    case F.Config{len, +tlvs}:
      config(tlvs)
    case F.NgapAssocUp{assoc}:
      keep([], k => {==})
    case F.NgapAssocDown{assoc}:
      down(assoc)
    case F.NgapData{+assoc, +stream, len, +bytes}:
      Walk.pdu(Q, ok, st, assoc, stream, entropy, Fr.Pdu.read(bytes), keep, ready(assoc), out, routed(assoc, stream))
    case F.PfcpData{len, +bytes}:
      out(Gsm.Gsm.pfcp_data(st, bytes), pfcp(bytes))
    case F.TimerFired{+timer}:
      out(K.Kernel.fired(st, timer), fired(timer))

# A property that holds after any outcome.
def Walk.any(-Q: N.Step() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: Walk.Keep(Q, st), ready: @assoc:U32 -> Walk.Ready(Q, st, assoc), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), down: @assoc:U32 -> Q(R.Route.down(st, assoc)), out: @o:N.GOut() -> Q(N.Step.of(st, o))) -> Q(K.Kernel.step(st, ev, entropy)):
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

# The N4 side
# -----------
# A transaction that moves only the N4 side (the link, the pending Session
# Deletion Requests) and the sequence numbers keeps every context and session;
# Up.N4.deletions gives one.

def N4s.only(tx: S.Tx) -> Bool:
  match tx:
    case S.Keep{}:
      True{}
    case S.SetLink{link}:
      True{}
    case S.Pend{key, d}:
      True{}
    case S.BumpSeq{n}:
      True{}
    case S.Both{first, second}:
      Bool.and(N4s.only(first), N4s.only(second))
    case _:
      False{}

def N4s.Same(+a: S.State, +b: S.State) -> Type:
  {S.State.ues(a) == S.State.ues(b) : Tb.Table(S.Ue)} & {S.State.sessions(a) == S.State.sessions(b) : Tb.Table(S.Session)}

def N4s.trans(+a: S.State, +b: S.State, +c: S.State, ab: N4s.Same(a, b), bc: N4s.Same(b, c)) -> N4s.Same(a, c):
  match ab:
    case (u1, s1):
      match bc:
        case (u2, s2):
          (Equal.trans(Tb.Table(S.Ue), S.State.ues(a), S.State.ues(b), S.State.ues(c), u1, u2), Equal.trans(Tb.Table(S.Session), S.State.sessions(a), S.State.sessions(b), S.State.sessions(c), s1, s2))

def N4s.keeps(+tx: S.Tx, +st: S.State, +e: {N4s.only(tx) == True{} : Bool}) -> N4s.Same(S.Tx.apply(tx, st), st):
  match tx:
    case S.Keep{}:
      ({==}, {==})
    case S.SetLink{link}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          ({==}, {==})
    case S.Pend{key, d}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          ({==}, {==})
    case S.BumpSeq{n}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          ({==}, {==})
    case S.Both{+first, +second}:
      +s1 = S.Tx.apply(first, st)
      N4s.trans(S.Tx.apply(second, s1), s1, st, N4s.keeps(second, s1, P.Bool.and_true_r(N4s.only(first), N4s.only(second), e)), N4s.keeps(first, st, P.Bool.and_true_l(N4s.only(first), N4s.only(second), e)))
    case S.Put{key, ue}:
      Empty.absurd(N4s.Same(S.Tx.apply(S.Put{key, ue}, st), st), P.Refute.bool(e))
    case S.Rephase{key, phase}:
      Empty.absurd(N4s.Same(S.Tx.apply(S.Rephase{key, phase}, st), st), P.Refute.bool(e))
    case S.Del{key}:
      Empty.absurd(N4s.Same(S.Tx.apply(S.Del{key}, st), st), P.Refute.bool(e))
    case S.PutSession{key, s}:
      Empty.absurd(N4s.Same(S.Tx.apply(S.PutSession{key, s}, st), st), P.Refute.bool(e))
    case S.Revar{key, v}:
      Empty.absurd(N4s.Same(S.Tx.apply(S.Revar{key, v}, st), st), P.Refute.bool(e))
    case S.DelSession{key}:
      Empty.absurd(N4s.Same(S.Tx.apply(S.DelSession{key}, st), st), P.Refute.bool(e))
    case S.Subs{new}:
      Empty.absurd(N4s.Same(S.Tx.apply(S.Subs{new}, st), st), P.Refute.bool(e))
    case S.BumpUe{key}:
      Empty.absurd(N4s.Same(S.Tx.apply(S.BumpUe{key}, st), st), P.Refute.bool(e))

def Out.tx_join(+a: N.GOut(), +b: N.GOut()) -> {N.Out.tx(N.Out.join(a, b)) == S.Both{N.Out.tx(a), N.Out.tx(b)} : S.Tx}:
  match a:
    case (ta, aa):
      match b:
        case (tb, ab):
          {==}

def N4s.join(+a: N.GOut(), +b: N.GOut(), +ea: {N4s.only(N.Out.tx(a)) == True{} : Bool}, +eb: {N4s.only(N.Out.tx(b)) == True{} : Bool}) -> {N4s.only(N.Out.tx(N.Out.join(a, b))) == True{} : Bool}:
  e = Equal.sym(S.Tx, N.Out.tx(N.Out.join(a, b)), S.Both{N.Out.tx(a), N.Out.tx(b)}, Out.tx_join(a, b))
  (%e : {N4s.only(_) == True{} : Bool}; P.Bool.and_intro(N4s.only(N.Out.tx(a)), N4s.only(N.Out.tx(b)), ea, eb))

def N4s.delete_if(+key: U32, +s: S.Session, +seq: U32, +more: Tb.Table(S.Session), +known: Bool, h0: {N4s.only(N.Out.tx(Up.N4.deletions(more, seq))) == True{} : Bool}, h1: {N4s.only(N.Out.tx(Up.N4.deletions(more, U32.add(seq, 1)))) == True{} : Bool}) -> {N4s.only(N.Out.tx(Up.N4.delete_if(key, s, seq, q => Up.N4.deletions(more, q), known))) == True{} : Bool}:
  match known:
    case True{}:
      +request = Up.N4.delete(S.Session.up_seid(s), seq)
      N4s.join((S.Both{S.Pend{key, Some{S.Deletion{request, seq, S.Guard{0}}}}, S.BumpSeq{1}}, [N.Pfcp{Some{S.Session.ue(s)}, request}, N.TimerStart{None{}, S.Ids.deletion(key), Up.N4.t1_ms()}]), Up.N4.deletions(more, U32.add(seq, 1)), {==}, h1)
    case False{}:
      h0

def N4s.deletions(+rows: Tb.Table(S.Session), +seq: U32) -> {N4s.only(N.Out.tx(Up.N4.deletions(rows, seq))) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +s) <> +more:
      N4s.delete_if(key, s, seq, more, S.Session.known(s), N4s.deletions(more, seq), N4s.deletions(more, U32.add(seq, 1)))

# The state a procedure's outcome leaves is its transaction applied.
def N4s.render(+st: S.State, +o: N.GOut()) -> {K.Kernel.state(N.Step.of(st, o)) == S.Tx.apply(N.Out.tx(o), st) : S.State}:
  match o:
    case (tx, acts):
      {==}

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
