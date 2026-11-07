import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../state.bend as S
import ./ngap.bend as N
import ./gmm.bend as Gmm
import ../smf/gsm.bend as Gsm

# Incoming NGAP PDUs: decode, then tell the procedures apart by comparing the
# PDU kind and procedure code in turn, so that a proof can follow each branch.
# Every UE procedure answers with a transaction; NG Setup alone answers directly.

def Route.d7(st: S.State, +assoc: U32, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gsm.Gsm.setup_response_of_view(st, assoc, V.PDUSessionResourceSetupResponse.view(ies))
    case False{}:
      (S.Keep{}, N.Ngap.unhandled(assoc))

def Route.d6(st: S.State, +assoc: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.Gmm.release_complete_of_view(st, assoc, V.UEContextReleaseComplete.view(ies))
    case False{}:
      Route.d7(st, assoc, ies, N.Ngap.is_pdu_session_resource_setup_response(kind, code))

def Route.d5(st: S.State, +assoc: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.Gmm.release_request_of_view(st, assoc, V.UEContextReleaseRequest.view(ies))
    case False{}:
      Route.d6(st, assoc, kind, code, ies, N.Ngap.is_ue_context_release_complete(kind, code))

def Route.d4(st: S.State, +assoc: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.Gmm.ics_response_of_view(st, assoc, V.InitialContextSetupResponse.view(ies))
    case False{}:
      Route.d5(st, assoc, kind, code, ies, N.Ngap.is_ue_context_release_request(kind, code))

def Route.d3(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, V.UplinkNASTransport.view(ies))
    case False{}:
      Route.d4(st, assoc, kind, code, ies, N.Ngap.is_initial_context_setup_response(kind, code))

def Route.d2(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, V.InitialUEMessage.view(ies))
    case False{}:
      Route.d3(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_uplink_nas_transport(kind, code))

def Route.d1(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool) -> N.Step():
  match ok:
    case True{}:
      N.NgSetup.of_view(st, assoc, V.NGSetupRequest.view(ies))
    case False{}:
      N.Step.of(st, Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code)))

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
