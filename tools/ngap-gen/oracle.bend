import Base
import ../../kernel/bytes.bend as B
import ../../kernel/ngap/frame.bend as F
import ../../kernel/ngap/gen/show.bend as S
import ../../kernel/tests/lib/vec.bend as V
import ../../kernel/tests/lib/ngap_vectors.bend as N

# Prints one line per NGAP message of the vectors, in order: the message
# name, then the normal form of our decoding (PDU kind/code/criticality and
# the message value), for tools/ngap-gen/oracle.py to compare with pycrate.

def message(r: Maybe<&2, String>) -> String:
  match r:
    case None{}:
      "?"
    case Some{s}:
      s

def pdu(r: Result<&2, &2, B.Err, F.Pdu>) -> String:
  match r:
    case Fail{e}:
      "!"
    case Done{p}:
      match p:
        case F.Pdu{+kind, +code, crit, value}:
          S.Dec(kind) ++ "/" ++ S.Dec(code) ++ "/" ++ S.Dec(crit) ++ "/" ++ message(S.Message.show(U32.to_nat(kind), U32.to_nat(code), value))

def one(+m: V.Vec, protocol: String) -> IO(Unit):
  match protocol:
    case "NGAP":
      IO.print(V.Vec.text(V.Vec.field(m, "message")) ++ ": " ++ pdu(F.Pdu.read(V.Vec.bytes(V.Vec.field(m, "hex")))))
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
  run(N.Ngap.vectors())
