import Base
import ../crypto/ctr.bend as Ctr
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/spec-sp800-38a.bend as Sp800

# SP 800-38A F.5.1 CTR-AES128.Encrypt, plus decryption and a partial block.

def run(cases: List<&2, V.Vec>) -> IO(Unit):
  match cases:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +c <> rest:
      do IO<Unit>:
        +key : List<&2, U32> = V.Vec.bytes(V.Vec.field(c, "key"))
        +iv : List<&2, U32> = V.Vec.bytes(V.Vec.field(c, "initial_counter"))
        +plain : List<&2, U32> = V.Vec.bytes(V.Vec.field(c, "plaintext"))
        +cipher : List<&2, U32> = V.Vec.bytes(V.Vec.field(c, "ciphertext"))
        C.Check.report("SP 800-38A " ++ V.Vec.text(V.Vec.field(c, "section")) ++ " encrypt", C.Check.bytes_eq(Ctr.ctr(key, iv, plain), cipher))
        C.Check.report("SP 800-38A " ++ V.Vec.text(V.Vec.field(c, "section")) ++ " decrypt", C.Check.bytes_eq(Ctr.ctr(key, iv, cipher), plain))
        C.Check.report("SP 800-38A " ++ V.Vec.text(V.Vec.field(c, "section")) ++ " first 37 bytes", C.Check.bytes_eq(Ctr.ctr(key, iv, List.take(&2, U32, plain, 37n)), List.take(&2, U32, cipher, 37n)))
        run(rest)

def main() -> IO(Unit):
  run(V.Vec.items(V.Vec.field(Sp800.data(), "cases")))
