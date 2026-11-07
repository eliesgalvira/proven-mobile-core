import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../state.bend as S
import ../smf/n4.bend as Up
import ./ngap.bend as N
import ./gmm.bend as Gmm
import ../smf/gsm.bend as Gsm
import ./path_switch.bend as Ps
import ./handover.bend as Ho

# Incoming NGAP PDUs: decode, then tell the procedures apart by comparing the
# PDU kind and procedure code in turn, so that a proof can follow each branch.
# Every UE procedure answers with a transaction; NG Setup alone answers directly.

# An association's UEs released, with their sessions, deleted at the UPF,
# and the guards of the sessions gone stopped; it is no longer set up.
def Route.drop(st: S.State, +assoc: U32) -> N.Step():
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +left = S.Ues.drop_assoc(assoc, ues)
      +gone = S.Sessions.sift(S.SOrphan{left}, sessions)
      +o = Up.N4.deletions(gone, pfcp_seq)
      +st1 = S.Tx.apply(N.Out.tx(o), S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4})
      (S.State{config, subs, S.Assocs.drop(assoc, assocs), left, S.Sessions.sift(S.SOwned{left}, sessions), S.State.pfcp_seq(st1), next_ue, S.State.n4(st1)}, List.append(&2, N.Act, N.Out.acts(o), N.Gone.cancels(gone, [])))

# An association going down: first the N2 handovers it takes part in end
# (Ho.Ho.down), then its UEs go.
def Route.down(+st: S.State, +assoc: U32) -> N.Step():
  +s1 = N.Step.of(st, Ho.Ho.down(st, assoc))
  +s2 = Route.drop(N.Step.state(s1), assoc)
  (N.Step.state(s2), List.append(&2, N.Act, N.Step.acts(s1), N.Note{F.Info{}, "NGAP: association down; its UE contexts and sessions released"} <> N.Step.acts(s2)))

# NG Setup re-initialises the association's UE-related contexts, as NG Reset
# does (TS 38.413 §8.7.1.1): its UEs go; then it is set up when the answer is
# a Response.
def Route.setup(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.NGSetupRequest.View>) -> N.Step():
  match r:
    case Fail{e}:
      (st, N.Ngap.bad_view(assoc))
    case Done{+v}:
      +s = Route.drop(st, assoc)
      (S.State.ready(N.Step.state(s), assoc, N.NgSetup.node(v), N.NgSetup.supported_view(S.State.config(st), v)), List.append(&2, N.Act, N.Step.acts(s), [N.Setup{assoc, N.NgSetup.reply(S.State.config(st), v)}]))

def Route.d8(st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Ps.Ps.of_view(st, assoc, stream, V.PathSwitchRequest.view(ies))
    case False{}:
      Ho.Ho.route(st, assoc, stream, kind, code, ies)

def Route.d7(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gsm.Gsm.setup_response_of_view(st, assoc, V.PDUSessionResourceSetupResponse.view(ies))
    case False{}:
      Route.d8(st, assoc, stream, kind, code, ies, N.Ngap.is_path_switch_request(kind, code))

def Route.d6(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.Gmm.release_complete_of_view(st, assoc, V.UEContextReleaseComplete.view(ies))
    case False{}:
      Route.d7(st, assoc, stream, kind, code, ies, N.Ngap.is_pdu_session_resource_setup_response(kind, code))

def Route.d5(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.Gmm.release_request_of_view(st, assoc, V.UEContextReleaseRequest.view(ies))
    case False{}:
      Route.d6(st, assoc, stream, kind, code, ies, N.Ngap.is_ue_context_release_complete(kind, code))

def Route.d4(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.Gmm.ics_response_of_view(st, assoc, V.InitialContextSetupResponse.view(ies))
    case False{}:
      Route.d5(st, assoc, stream, kind, code, ies, N.Ngap.is_ue_context_release_request(kind, code))

def Route.d3(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, V.UplinkNASTransport.view(ies))
    case False{}:
      Route.d4(st, assoc, stream, kind, code, ies, N.Ngap.is_initial_context_setup_response(kind, code))

def Route.d2(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, V.InitialUEMessage.view(ies))
    case False{}:
      Route.d3(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_uplink_nas_transport(kind, code))

# NG Setup is the first procedure on an association (TS 38.413 §8.7.1.1):
# until it has succeeded, every other message is refused.
def Route.ready(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool) -> N.Step():
  match ok:
    case True{}:
      N.Step.of(st, Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code)))
    case False{}:
      (st, N.Ngap.unhandled(assoc))

def Route.d1(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool) -> N.Step():
  match ok:
    case True{}:
      Route.setup(st, assoc, V.NGSetupRequest.view(ies))
    case False{}:
      Route.ready(st, assoc, stream, kind, code, ies, entropy, S.Assocs.has(assoc, S.State.assocs(st)))

def Route.dispatch(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes()) -> N.Step():
  Route.d1(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_ng_setup(kind, code))

def Route.of_ies(st: S.State, +assoc: U32, stream: U32, kind: Nat, code: Nat, entropy: B.Bytes(), r: Ap.Rd(List<&2, Fr.Ie>)) -> N.Step():
  match r:
    case Fail{e}:
      (st, N.Ngap.bad_pdu(assoc))
    case Done{(ies, c)}:
      Route.dispatch(st, assoc, stream, kind, code, ies, entropy)

def Route.of_pdu(st: S.State, +assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Fr.Pdu>) -> N.Step():
  match r:
    case Fail{e}:
      (st, N.Ngap.bad_pdu(assoc))
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Route.of_ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}))

def Route.data(st: S.State, +assoc: U32, stream: U32, bytes: B.Bytes(), entropy: B.Bytes()) -> N.Step():
  Route.of_pdu(st, assoc, stream, entropy, Fr.Pdu.read(bytes))
