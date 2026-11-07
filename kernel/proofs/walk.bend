import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../tlv.bend as T
import ../table.bend as Tb
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/route.bend as R
import ../amf/gmm.bend as Gmm
import ../smf/gsm.bend as Gsm

# The step function, walked once
# ------------------------------
# A step ends in one of three ways: the state as it was, with actions that
# name no UE context (an NGAP PDU or IE list that does not decode, NG Setup,
# an incomplete Config); a procedure's outcome o rendered by N.Step.of (a
# routed NGAP message, a PFCP message, a timer); or a new configuration or a
# change of the associations. A property Q of steps holds after every step
# when it holds after each of them, the outcomes known only by a property ok
# that each of them has.

def Walk.Keep(-Q: N.Step() -> Type, +st: S.State) -> Type:
  @acts:List<&2, N.Act> -> (@k:U32 -> {N.Acts.spare(k, acts) == True{} : Bool}) -> Q((st, acts))

def Walk.Out(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State) -> Type:
  @o:N.GOut() -> ok(o) -> Q(N.Step.of(st, o))

# The outcome of every NGAP message that is not NG Setup.
def Walk.Routed(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes()) -> Type:
  @kind:Nat -> @code:Nat -> @ies:List<&2, Fr.Ie> -> ok(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n)))

# The routed outcomes: each UE procedure's on any view of its message, and
# the message not handled.
def Walk.d7(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +ies: List<&2, Fr.Ie>, +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r))) -> ok(R.Route.d7(st, assoc, ies, b)):
  match b:
    case True{}:
      setup_response(V.PDUSessionResourceSetupResponse.view(ies))
    case False{}:
      unhandled

def Walk.d6(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), release_complete: @r:Result<&2, &2, B.Err, V.UEContextReleaseComplete.View> -> ok(Gmm.Gmm.release_complete_of_view(st, assoc, r)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r))) -> ok(R.Route.d6(st, assoc, kind, code, ies, b)):
  match b:
    case True{}:
      release_complete(V.UEContextReleaseComplete.view(ies))
    case False{}:
      Walk.d7(ok, st, assoc, ies, N.Ngap.is_procedure(kind, code, 1n, 29n), unhandled, setup_response)

def Walk.d5(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), release_request: @r:Result<&2, &2, B.Err, V.UEContextReleaseRequest.View> -> ok(Gmm.Gmm.release_request_of_view(st, assoc, r)), release_complete: @r:Result<&2, &2, B.Err, V.UEContextReleaseComplete.View> -> ok(Gmm.Gmm.release_complete_of_view(st, assoc, r)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r))) -> ok(R.Route.d5(st, assoc, kind, code, ies, b)):
  match b:
    case True{}:
      release_request(V.UEContextReleaseRequest.view(ies))
    case False{}:
      Walk.d6(ok, st, assoc, kind, code, ies, N.Ngap.is_procedure(kind, code, 1n, 41n), unhandled, release_complete, setup_response)

def Walk.d4(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), ics: @r:Result<&2, &2, B.Err, V.InitialContextSetupResponse.View> -> ok(Gmm.Gmm.ics_response_of_view(st, assoc, r)), release_request: @r:Result<&2, &2, B.Err, V.UEContextReleaseRequest.View> -> ok(Gmm.Gmm.release_request_of_view(st, assoc, r)), release_complete: @r:Result<&2, &2, B.Err, V.UEContextReleaseComplete.View> -> ok(Gmm.Gmm.release_complete_of_view(st, assoc, r)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r))) -> ok(R.Route.d4(st, assoc, kind, code, ies, b)):
  match b:
    case True{}:
      ics(V.InitialContextSetupResponse.view(ies))
    case False{}:
      Walk.d5(ok, st, assoc, kind, code, ies, N.Ngap.is_procedure(kind, code, 0n, 42n), unhandled, release_request, release_complete, setup_response)

def Walk.d3(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), uplink: @r:Result<&2, &2, B.Err, V.UplinkNASTransport.View> -> ok(Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, r)), ics: @r:Result<&2, &2, B.Err, V.InitialContextSetupResponse.View> -> ok(Gmm.Gmm.ics_response_of_view(st, assoc, r)), release_request: @r:Result<&2, &2, B.Err, V.UEContextReleaseRequest.View> -> ok(Gmm.Gmm.release_request_of_view(st, assoc, r)), release_complete: @r:Result<&2, &2, B.Err, V.UEContextReleaseComplete.View> -> ok(Gmm.Gmm.release_complete_of_view(st, assoc, r)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r))) -> ok(R.Route.d3(st, assoc, stream, kind, code, ies, entropy, b)):
  match b:
    case True{}:
      uplink(V.UplinkNASTransport.view(ies))
    case False{}:
      Walk.d4(ok, st, assoc, kind, code, ies, N.Ngap.is_procedure(kind, code, 1n, 14n), unhandled, ics, release_request, release_complete, setup_response)

def Walk.d2(-ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, unhandled: ok((S.Keep{}, N.Ngap.unhandled(assoc))), initial: @r:Result<&2, &2, B.Err, V.InitialUEMessage.View> -> ok(Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, r)), uplink: @r:Result<&2, &2, B.Err, V.UplinkNASTransport.View> -> ok(Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, r)), ics: @r:Result<&2, &2, B.Err, V.InitialContextSetupResponse.View> -> ok(Gmm.Gmm.ics_response_of_view(st, assoc, r)), release_request: @r:Result<&2, &2, B.Err, V.UEContextReleaseRequest.View> -> ok(Gmm.Gmm.release_request_of_view(st, assoc, r)), release_complete: @r:Result<&2, &2, B.Err, V.UEContextReleaseComplete.View> -> ok(Gmm.Gmm.release_complete_of_view(st, assoc, r)), setup_response: @r:Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View> -> ok(Gsm.Gsm.setup_response_of_view(st, assoc, r))) -> ok(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, b)):
  match b:
    case True{}:
      initial(V.InitialUEMessage.view(ies))
    case False{}:
      Walk.d3(ok, st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 46n), unhandled, uplink, ics, release_request, release_complete, setup_response)

def Walk.setup(-Q: N.Step() -> Type, +st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.NGSetupRequest.View>, keep: Walk.Keep(Q, st)) -> Q(N.NgSetup.of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      keep(N.Ngap.bad_view(assoc), k => {==})
    case Done{v}:
      keep([N.Setup{assoc, N.NgSetup.reply(S.State.config(st), v)}], k => {==})

def Walk.d1(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, keep: Walk.Keep(Q, st), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, b)):
  match b:
    case True{}:
      Walk.setup(Q, st, assoc, V.NGSetupRequest.view(ies), keep)
    case False{}:
      out(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n)), routed(kind, code, ies))

def Walk.ies(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +entropy: B.Bytes(), +r: Ap.Rd(List<&2, Fr.Ie>), keep: Walk.Keep(Q, st), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r)):
  match r:
    case Fail{err}:
      keep(N.Ngap.bad_pdu(assoc), k => {==})
    case Done{(+ies, c)}:
      Walk.d1(Q, ok, st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 21n), keep, out, routed)

def Walk.pdu(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Fr.Pdu>, keep: Walk.Keep(Q, st), out: Walk.Out(Q, ok, st), routed: Walk.Routed(ok, st, assoc, stream, entropy)) -> Q(R.Route.of_pdu(st, assoc, stream, entropy, r)):
  match r:
    case Fail{err}:
      keep(N.Ngap.bad_pdu(assoc), k => {==})
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Walk.ies(Q, ok, st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), keep, out, routed)

def Walk.step(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: Walk.Keep(Q, st), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), up: @assoc:U32 -> Q(K.Kernel.assoc_up(st, assoc)), down: @assoc:U32 -> Q(K.Kernel.assoc_down(st, assoc)), out: Walk.Out(Q, ok, st), routed: @assoc:U32 -> @stream:U32 -> Walk.Routed(ok, st, assoc, stream, entropy), pfcp: @bytes:B.Bytes() -> ok(Gsm.Gsm.pfcp_data(st, bytes)), fired: @timer:U32 -> ok(K.Kernel.fired(st, timer))) -> Q(K.Kernel.step(st, ev, entropy)):
  match ev:
    case F.Config{len, +tlvs}:
      config(tlvs)
    case F.NgapAssocUp{assoc}:
      up(assoc)
    case F.NgapAssocDown{assoc}:
      down(assoc)
    case F.NgapData{+assoc, +stream, len, +bytes}:
      Walk.pdu(Q, ok, st, assoc, stream, entropy, Fr.Pdu.read(bytes), keep, out, routed(assoc, stream))
    case F.PfcpData{len, +bytes}:
      out(Gsm.Gsm.pfcp_data(st, bytes), pfcp(bytes))
    case F.TimerFired{+timer}:
      out(K.Kernel.fired(st, timer), fired(timer))

# A property that holds after any outcome.
def Walk.any(-Q: N.Step() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: Walk.Keep(Q, st), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), up: @assoc:U32 -> Q(K.Kernel.assoc_up(st, assoc)), down: @assoc:U32 -> Q(K.Kernel.assoc_down(st, assoc)), out: @o:N.GOut() -> Q(N.Step.of(st, o))) -> Q(K.Kernel.step(st, ev, entropy)):
  Walk.step(Q, o => Unit, st, ev, entropy, keep, config, up, down, o => u => out(o), a => s => kind => code => ies => Unit{}, bytes => Unit{}, timer => Unit{})

# A property of the context and session tables: Config, an association going
# up and every step that keeps the state leave both tables as they were.

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

def Walk.up(-inv: Tb.Table(S.Ue) -> Tb.Table(S.Session) -> Bool, +st: S.State, +assoc: U32, +e: {inv(S.State.ues(st), S.State.sessions(st)) == True{} : Bool}) -> Walk.Tables(inv, K.Kernel.assoc_up(st, assoc)):
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      e
