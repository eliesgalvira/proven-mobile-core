import Base
import ../crypto/aes.bend as A
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/spec-fips197.bend as Fips197

# FIPS 197 Appendix B and C.1: AES-128 block encryption.

def run(cases: List<&2, V.Vec>) -> IO(Unit):
  match cases:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +c <> rest:
      do IO<Unit>:
        C.Check.report("FIPS 197 " ++ V.Vec.text(V.Vec.field(c, "section")), C.Check.bytes_eq(A.aes128(V.Vec.bytes(V.Vec.field(c, "key")), V.Vec.bytes(V.Vec.field(c, "plaintext"))), V.Vec.bytes(V.Vec.field(c, "ciphertext"))))
        run(rest)

def main() -> IO(Unit):
  run(V.Vec.items(V.Vec.field(Fips197.data(), "cases")))
