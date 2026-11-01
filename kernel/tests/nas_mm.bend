import Base
import ../bytes.bend as B
import ../nas/ie.bend as I
import ../nas/mm.bend as M
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture

# Every plain 5GMM message of the capture decodes, re-encodes to the same
# bytes and carries the message type its name says.

def code_of_name(name: String) -> U32:
  match name:
    case "Registration request":
      65
    case "Registration accept":
      66
    case "Registration complete":
      67
    case "Authentication request":
      86
    case "Authentication response":
      87
    case "Security mode command":
      93
    case "Security mode complete":
      94
    case "Configuration update command":
      84
    case "UL NAS transport":
      103
    case "DL NAS transport":
      104
    case _:
      0

def check(+name: String, +plain: List<&2, U32>, r: Result<&2, &2, B.Err, M.Mm>) -> IO(Unit):
  match r:
    case Fail{e}:
      C.Check.report(name ++ " decodes", False{})
    case Done{+m}:
      do IO<Unit>:
        C.Check.report(name ++ " re-encodes to the captured bytes", B.bytes_eq(M.Mm.write(m), plain))
        C.Check.report(name ++ " has message type " ++ U32.show(code_of_name(name)), U32.is_eq(M.Mm.Type.code(M.Mm.mt(m)), code_of_name(name)))
        C.Check.report(name ++ " is valid", M.Mm.valid(m))

def one(+m: V.Vec, protocol: String) -> IO(Unit):
  match protocol:
    case "NAS-5GMM":
      +plain : List<&2, U32> = V.Vec.bytes(V.Vec.field(m, "plaintext_hex"))
      check(V.Vec.text(V.Vec.field(m, "message")), plain, M.Mm.read(plain))
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
    run(V.Vec.items(V.Vec.field(Capture.data(), "messages")))
    C.Check.report("a truncated Registration accept is rejected", Result.is_fail(&2, &2, B.Err, M.Mm, M.Mm.read([126, 0, 66, 1, 1, 119, 0, 11, 242, 0])))
    C.Check.report("a protected header is not a plain message", Result.is_fail(&2, &2, B.Err, M.Mm, M.Mm.read([126, 2, 0, 0, 0, 0, 1, 126, 0, 67])))
    C.Check.report("an unknown message type is Unsupported", Result.is_fail(&2, &2, B.Err, M.Mm, M.Mm.read([126, 0, 1])))
