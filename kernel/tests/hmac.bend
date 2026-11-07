import Base
import ../crypto/hmac.bend as H
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/spec-rfc4231.bend as Rfc4231

# RFC 4231 cases 1 to 7; case 5 compares the first `mac_length` bytes.

def run(cases: List<&2, V.Vec>) -> IO(Unit):
  match cases:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +c <> rest:
      do IO<Unit>:
        mac : List<&2, U32> = List.take(&2, U32, H.hmac(V.Vec.bytes(V.Vec.field(c, "key")), V.Vec.bytes(V.Vec.field(c, "data"))), V.Vec.nat(V.Vec.field(c, "mac_length")))
        C.Check.report("RFC 4231 test case " ++ Nat.show(V.Vec.nat(V.Vec.field(c, "test_case"))), C.Check.bytes_eq(mac, V.Vec.bytes(V.Vec.field(c, "hmac_sha256"))))
        run(rest)

def main() -> IO(Unit):
  run(V.Vec.items(V.Vec.field(Rfc4231.data(), "cases")))
