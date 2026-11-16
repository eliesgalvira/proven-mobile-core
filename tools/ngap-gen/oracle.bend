import Base
import ../../kernel/bytes.bend as B
import ../../kernel/ngap/frame.bend as F
import ../../kernel/ngap/gen/show.bend as S
import ../../kernel/tests/lib/vec.bend as V
import ../../kernel/tests/lib/ngap_vectors.bend as N
import ../../kernel/ngap/gen/types.bend as G
import ../../kernel/amf/ngap.bend as Ng
import ../../kernel/tests/lib/amf.bend as A

# Prints one line per NGAP message of the vectors, in order: the message
# name, then the normal form of our decoding (PDU kind/code/criticality and
# the message value), for tools/ngap-gen/oracle.py to compare with pycrate.
# Then the same for messages no vector holds, built by the kernel and the
# tests, each name followed by the message in hex.

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

def built(name: String, +bytes: B.Bytes()) -> IO(Unit):
  IO.print(name ++ " " ++ S.Hex.bytes(bytes) ++ ": " ++ pdu(F.Pdu.read(bytes)))

def main() -> IO(Unit):
  do IO<Unit>:
    run(N.Ngap.vectors())
    built("PDUSessionResourceReleaseCommand", Ng.Ngap.pdu_release(1, [1], 1, [126, 0, 104, 1, 0, 5, 46, 1, 0, 211, 26, 18, 1], Ng.Ngap.misc(G.CauseMisc.unspecified())))
    built("PDUSessionResourceReleaseResponse", A.pdu_release_response([1], [1], 1))
