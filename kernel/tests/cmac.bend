import Base
import ../crypto/cmac.bend as M
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/spec-rfc4493.bend as Rfc4493

# RFC 4493 §4 examples 1 to 4.

def run(cases: List<&2, V.Vec>) -> IO(Unit):
  match cases:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +c <> rest:
      do IO<Unit>:
        C.Check.report("RFC 4493 example " ++ Nat.show(V.Vec.nat(V.Vec.field(c, "example"))), C.Check.bytes_eq(M.cmac(V.Vec.bytes(V.Vec.field(c, "key")), V.Vec.bytes(V.Vec.field(c, "message"))), V.Vec.bytes(V.Vec.field(c, "mac"))))
        run(rest)

def main() -> IO(Unit):
  run(V.Vec.items(V.Vec.field(Rfc4493.data(), "cases")))
