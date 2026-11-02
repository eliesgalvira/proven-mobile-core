import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../state.bend as S
import ./ngap.bend as N
import ./gmm.bend as Gmm

# Incoming NGAP PDUs: decode, then tell the procedures apart by comparing the
# PDU kind and procedure code in turn, so that a proof can follow each branch.

def Route.d3(st: S.State, +assoc: U32, stream: U32, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool) -> S.Out():
  match ok:
    case True{}:
      N.render_out(Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, V.UplinkNASTransport.view(ies)))
    case False{}:
      (st, N.Ngap.unhandled(assoc))

def Route.d2(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool) -> S.Out():
  match ok:
    case True{}:
      N.render_out(Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, V.InitialUEMessage.view(ies)))
    case False{}:
      Route.d3(st, assoc, stream, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 46n))

def Route.d1(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool) -> S.Out():
  match ok:
    case True{}:
      N.NgSetup.of_view(st, assoc, V.NGSetupRequest.view(ies))
    case False{}:
      Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n))

def Route.dispatch(st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes()) -> S.Out():
  Route.d1(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 21n))

def Route.of_ies(st: S.State, +assoc: U32, stream: U32, kind: Nat, code: Nat, entropy: B.Bytes(), r: Ap.Rd(List<&2, Fr.Ie>)) -> S.Out():
  match r:
    case Fail{e}:
      (st, N.Ngap.bad_pdu(assoc))
    case Done{(ies, c)}:
      Route.dispatch(st, assoc, stream, kind, code, ies, entropy)

def Route.of_pdu(st: S.State, +assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Fr.Pdu>) -> S.Out():
  match r:
    case Fail{e}:
      (st, N.Ngap.bad_pdu(assoc))
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Route.of_ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}))

def Route.data(st: S.State, +assoc: U32, stream: U32, bytes: B.Bytes(), entropy: B.Bytes()) -> S.Out():
  Route.of_pdu(st, assoc, stream, entropy, Fr.Pdu.read(bytes))
