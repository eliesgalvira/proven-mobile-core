import Base
import ../crypto/sha256.bend as S
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/spec-fips180-4.bend as Fips180

# Every FIPS 180-4 example: `message` as hex, or `message_repeat` {byte, count}.

def message(c: V.Vec, repeat: Maybe<&2, V.Vec>) -> List<&2, U32>:
  match repeat:
    case Some{+rep}:
      List.replicate(U32, V.Vec.nat(V.Vec.field(rep, "count")), Maybe.default(&2, U32, List.head(&2, U32, V.Vec.bytes(V.Vec.field(rep, "byte"))), 0))
    case None{}:
      V.Vec.bytes(V.Vec.field(c, "message"))

def run(cases: List<&2, V.Vec>) -> IO(Unit):
  match cases:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +c <> rest:
      do IO<Unit>:
        C.Check.report(V.Vec.text(V.Vec.field(c, "section")), C.Check.bytes_eq(S.sha256(message(c, V.Vec.get(c, "message_repeat"))), V.Vec.bytes(V.Vec.field(c, "digest"))))
        run(rest)

def main() -> IO(Unit):
  run(V.Vec.items(V.Vec.field(Fips180.data(), "cases")))
