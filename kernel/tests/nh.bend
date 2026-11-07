import Base
import ../state.bend as S
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-handover.bend as Capture

# The handover capture: every NH and NCC Open5GS sent, recomputed along the
# chain from the captured KAMF and KgNB (TS 33.501 §6.9.2.1.1, Annex A.10).

def sent(c: S.Nh, +v: V.Vec) -> Bool:
  match c:
    case S.Nh{k_amf, nh, ncc}:
      Bool.and(C.Check.bytes_eq(nh, V.Vec.bytes_at(v, "nh")), U32.is_eq(ncc, U32.from_nat(V.Vec.nat(V.Vec.field(v, "ncc")))))

def main() -> IO(Unit):
  do IO<Unit>:
    +s : V.Vec = V.Vec.field(Capture.data(), "secrets")
    +cs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(V.Vec.field(s, "handovers"), "security_contexts"))
    +nh1 : S.Nh = S.Nh.initial(V.Vec.secret(s, "k_amf"), V.Vec.secret(s, "k_gnb"))
    +nh2 : S.Nh = S.Nh.next(nh1)
    +nh3 : S.Nh = S.Nh.next(nh2)
    C.Check.report("Path Switch Request Acknowledge: NH 2, NCC 2, the pair after the one kept at initial setup", sent(nh2, V.Vec.message(cs, 54n)))
    C.Check.report("Handover Request, cancelled: NH 3, NCC 3", sent(nh3, V.Vec.message(cs, 60n)))
    C.Check.report("Handover Request: NH 4, NCC 4", sent(S.Nh.next(nh3), V.Vec.message(cs, 74n)))
