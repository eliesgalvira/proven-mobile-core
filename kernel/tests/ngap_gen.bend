import Base
import ../bytes.bend as B
import ../aper.bend as A
import ../ngap/frame.bend as F
import ../ngap/gen/types.bend as G
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./lib/ngap_vectors.bend as N

# Every NGAP PDU of the vectors re-encodes to its bytes, and each of its IEs
# whose type the generated codec knows decodes with that type, is valid, and
# re-encodes to the same octets with only zero padding left; the IEs the
# codec does not know are counted.

type Tally is Data:
  Tally{known: Nat, unknown: Nat, failed: Nat}

def step(t: Tally, r: Maybe<&2, Bool>) -> Tally:
  match t:
    case Tally{known, unknown, failed}:
      match r:
        case None{}:
          Tally{known, 1n+unknown, failed}
        case Some{ok}:
          match ok:
            case True{}:
              Tally{1n+known, unknown, failed}
            case False{}:
              Tally{known, unknown, 1n+failed}

def tally(+kind: Nat, +code: Nat, ies: List<&2, F.Ie>, t: Tally) -> Tally:
  match ies:
    case Nil{}:
      t
    case +ie <> more:
      tally(kind, code, more, step(t, G.Ie.check(kind, code, U32.to_nat(F.Ie.id(ie)), F.Ie.value(ie))))

def report(+name: String, t: Tally) -> IO(Unit):
  match t:
    case Tally{+known, unknown, failed}:
      do IO<Unit>:
        C.Check.report(name ++ ": " ++ Nat.show(known) ++ " known IEs decode, validate and re-encode (" ++ Nat.show(unknown) ++ " outside tiers M+R)", Bool.and(Nat.is_eq(failed, 0n), Nat.is_lt(0n, known)))

def container(+name: String, kind: Nat, code: Nat, r: A.Rd(List<&2, F.Ie>)) -> IO(Unit):
  match r:
    case Fail{e}:
      C.Check.report(name ++ ": IE container decodes", False{})
    case Done{(ies, c)}:
      report(name, tally(kind, code, ies, Tally{0n, 0n, 0n}))

def pdu(+name: String, +bytes: B.Bytes(), r: Result<&2, &2, B.Err, F.Pdu>) -> IO(Unit):
  match r:
    case Fail{e}:
      C.Check.report(name ++ ": PDU decodes", False{})
    case Done{+p}:
      do IO<Unit>:
        C.Check.report(name ++ ": PDU re-encodes to its bytes", B.bytes_eq(F.Pdu.write(p), bytes))
        container(name, U32.to_nat(F.Pdu.kind(p)), U32.to_nat(F.Pdu.code(p)), F.Ies.read(A.Cur{7n, List.drop(&2, Bool, A.unpack(F.Pdu.value(p)), 1n)}))

def one(+m: V.Vec, protocol: String) -> IO(Unit):
  match protocol:
    case "NGAP":
      +bytes : B.Bytes() = V.Vec.bytes(V.Vec.field(m, "hex"))
      pdu(V.Vec.text(V.Vec.field(m, "message")), bytes, F.Pdu.read(bytes))
    case _:
      IO.pure(Unit, Unit{})

def run(msgs: List<&2, V.Vec>) -> IO(Unit):
  match msgs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +m <> rest:
      do IO<Unit>:
        one(m, V.Vec.text(V.Vec.field(m, "protocol")))
        run(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    run(N.Ngap.vectors())
    C.Check.report("a RAN-UE-NGAP-ID of 1 roundtrips", G.Ie.roundtrips(G.RAN_UE_NGAP_ID(), G.RAN_UE_NGAP_ID.read, v => G.RAN_UE_NGAP_ID.valid(v), v => G.RAN_UE_NGAP_ID.write(v, 0n, []), [0, 1]))
    C.Check.report("a RAN-UE-NGAP-ID with a leading zero octet does not", Bool.not(G.Ie.roundtrips(G.RAN_UE_NGAP_ID(), G.RAN_UE_NGAP_ID.read, v => G.RAN_UE_NGAP_ID.valid(v), v => G.RAN_UE_NGAP_ID.write(v, 0n, []), [64, 0, 1])))
    C.Check.report("a PLMN identity of four octets does not", Bool.not(G.Ie.roundtrips(G.PLMNIdentity(), G.PLMNIdentity.read, v => G.PLMNIdentity.valid(v), v => G.PLMNIdentity.write(v, 0n, []), [0, 241, 16, 0])))
    C.Check.report("an RRC establishment cause mo-Signalling roundtrips", G.Ie.roundtrips(G.RRCEstablishmentCause(), G.RRCEstablishmentCause.read, v => G.RRCEstablishmentCause.valid(v), v => G.RRCEstablishmentCause.write(v, 0n, []), [48]))
    C.Check.report("a PDU session type ipv4 roundtrips", G.Ie.roundtrips(G.PDUSessionType(), G.PDUSessionType.read, v => G.PDUSessionType.valid(v), v => G.PDUSessionType.write(v, 0n, []), [0]))
