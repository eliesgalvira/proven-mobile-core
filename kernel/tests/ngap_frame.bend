import Base
import ../bytes.bend as B
import ../aper.bend as A
import ../ngap/frame.bend as F
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./lib/ngap_vectors.bend as N

# Every captured NGAP PDU decodes to its kind, procedure code and
# criticality, and its protocol IE container lists the ids and criticalities
# the capture records, with only zero padding left. (ngap_gen.bend checks
# that each re-encodes to its bytes.)

def crit_code(s: String) -> U32:
  match s:
    case "reject":
      F.Criticality.reject()
    case "ignore":
      F.Criticality.ignore()
    case "notify":
      F.Criticality.notify()
    case _:
      255

def pdu_code(s: String) -> U32:
  match s:
    case "initiatingMessage":
      F.Pdu.initiating()
    case "successfulOutcome":
      F.Pdu.successful()
    case "unsuccessfulOutcome":
      F.Pdu.unsuccessful()
    case _:
      255

def ies_match(expected: List<&2, V.Vec>, ies: List<&2, F.Ie>) -> Bool:
  match expected ies:
    case Nil{} Nil{}:
      True{}
    case Nil{} ie <> more:
      False{}
    case v <> vs Nil{}:
      False{}
    case +v <> vs +ie <> more:
      Bool.and(U32.is_eq(F.Ie.id(ie), U32.from_nat(V.Vec.nat(V.Vec.field(v, "id")))), Bool.and(U32.is_eq(F.Ie.crit(ie), crit_code(V.Vec.text(V.Vec.field(v, "criticality")))), ies_match(vs, more)))

def container(expected: List<&2, V.Vec>, r: A.Rd(List<&2, F.Ie>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(+ies, c)}:
      match c:
        case A.Cur{rem, bits}:
          Bool.and(ies_match(expected, ies), Bool.and(A.Tail.zero(bits), F.Ies.valid(ies)))

def check(+name: String, +m: V.Vec, r: Result<&2, &2, B.Err, F.Pdu>) -> IO(Unit):
  match r:
    case Fail{e}:
      C.Check.report(name ++ " decodes", False{})
    case Done{+p}:
      do IO<Unit>:
        C.Check.report(name ++ " is an " ++ V.Vec.text(V.Vec.field(m, "pdu")), U32.is_eq(F.Pdu.kind(p), pdu_code(V.Vec.text(V.Vec.field(m, "pdu")))))
        C.Check.report(name ++ " has its procedure code", U32.is_eq(F.Pdu.code(p), U32.from_nat(V.Vec.nat(V.Vec.field(m, "procedure_code")))))
        C.Check.report(name ++ " has its criticality", U32.is_eq(F.Pdu.crit(p), crit_code(V.Vec.text(V.Vec.field(m, "criticality")))))
        C.Check.report(name ++ " is valid", F.Pdu.valid(p))
        C.Check.report(name ++ " lists its IEs", container(V.Vec.items(V.Vec.field(m, "ies")), F.Ies.read(A.Cur{7n, List.drop(&2, Bool, A.unpack(F.Pdu.value(p)), 1n)})))

def one(+m: V.Vec, protocol: String) -> IO(Unit):
  match protocol:
    case "NGAP":
      check(V.Vec.text(V.Vec.field(m, "message")), m, F.Pdu.read(V.Vec.bytes(V.Vec.field(m, "hex"))))
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

def fails(bs: List<&2, U32>) -> Bool:
  Result.is_fail(&2, &2, B.Err, F.Pdu, F.Pdu.read(bs))

def main() -> IO(Unit):
  do IO<Unit>:
    run(N.Ngap.captured())
    C.Check.report("a PDU with the extension bit set is Unsupported", fails([128, 21, 0, 1, 0]))
    C.Check.report("a PDU short of its message is Short", fails([0, 21, 0, 62, 0, 0]))
    C.Check.report("a PDU with a non-zero byte after its message is rejected", fails([0, 21, 0, 1, 0, 1]))
    C.Check.report("an empty message is a PDU", Bool.not(fails([0, 21, 0, 1, 0])))
    C.Check.report("a built PDU reads back", Bool.not(fails(F.Pdu.write(F.Pdu{1, 21, 0, [0, 0, 0, 0]}))))
