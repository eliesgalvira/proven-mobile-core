import Base
import ../bytes.bend as B
import ../nas/ie.bend as I
import ../nas/sm.bend as S
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture

# Every 5GSM message of the capture decodes, re-encodes to the same bytes and
# carries the message type, PDU session identity and PTI its entry says.

def check(+name: String, +m: V.Vec, +bytes: List<&2, U32>, r: Result<&2, &2, B.Err, S.Sm>) -> IO(Unit):
  match r:
    case Fail{e}:
      C.Check.report(name ++ " decodes", False{})
    case Done{+sm}:
      do IO<Unit>:
        C.Check.report(name ++ " re-encodes to the captured bytes", B.bytes_eq(S.Sm.write(sm), bytes))
        C.Check.report(name ++ " has its message type", U32.is_eq(S.Sm.Type.code(S.Sm.mt(sm)), U32.from_nat(V.Vec.nat(V.Vec.field(m, "message_type")))))
        C.Check.report(name ++ " has its PDU session identity", U32.is_eq(S.Sm.psi(sm), U32.from_nat(V.Vec.nat(V.Vec.field(m, "pdu_session_id")))))
        C.Check.report(name ++ " has its PTI", U32.is_eq(S.Sm.pti(sm), U32.from_nat(V.Vec.nat(V.Vec.field(m, "pti")))))
        C.Check.report(name ++ " is valid", S.Sm.valid(sm))

def one(+m: V.Vec, protocol: String) -> IO(Unit):
  match protocol:
    case "NAS-5GSM":
      +bytes : List<&2, U32> = V.Vec.bytes(V.Vec.field(m, "hex"))
      check(V.Vec.text(V.Vec.field(m, "message")), m, bytes, S.Sm.read(bytes))
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
  Result.is_fail(&2, &2, B.Err, S.Sm, S.Sm.read(bs))

def main() -> IO(Unit):
  do IO<Unit>:
    run(V.Vec.items(V.Vec.field(Capture.data(), "messages")))
    C.Check.report("a 5GSM status decodes", Bool.not(fails([46, 1, 1, 214, 36])))
    C.Check.report("a release request with a cause decodes", Bool.not(fails([46, 1, 2, 209, 89, 36])))
    C.Check.report("an establishment accept short of its Session-AMBR is Short", fails([46, 1, 1, 194, 17, 0, 1, 1, 6, 3]))
    C.Check.report("a 5GMM header is not a 5GSM message", fails([46, 0, 67]))
    C.Check.report("an unknown 5GSM type is Unsupported", fails([46, 1, 1, 200]))
    C.Check.report("a wrong protocol discriminator is rejected", fails([126, 1, 1, 214, 36]))
