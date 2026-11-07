import Base
import ../crypto/milenage.bend as M
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/spec-ts35208.bend as Ts35208
import ./vectors/capture-vectors.bend as Capture

# TS 35.208 test sets 1 to 6, then the captured registration (K, OPc, RAND).

def set(+c: V.Vec) -> IO(Unit):
  do IO<Unit>:
    +name : String = "TS 35.208 set " ++ Nat.show(V.Vec.nat(V.Vec.field(c, "test_set")))
    +k : List<&2, U32> = V.Vec.bytes_at(c, "k")
    +opc : List<&2, U32> = V.Vec.bytes_at(c, "opc")
    +rand : List<&2, U32> = V.Vec.bytes_at(c, "rand")
    C.Check.report(name ++ " OPc", C.Check.bytes_eq(M.milenage.opc(k, V.Vec.bytes_at(c, "op")), opc))
    C.Check.report(name ++ " f1", C.Check.bytes_eq(M.milenage.f1(k, opc, rand, V.Vec.bytes_at(c, "sqn"), V.Vec.bytes_at(c, "amf")), V.Vec.bytes_at(c, "f1")))
    C.Check.report(name ++ " f1*", C.Check.bytes_eq(M.milenage.f1_star(k, opc, rand, V.Vec.bytes_at(c, "sqn"), V.Vec.bytes_at(c, "amf")), V.Vec.bytes_at(c, "f1_star")))
    C.Check.report(name ++ " f2", C.Check.bytes_eq(M.milenage.f2(k, opc, rand), V.Vec.bytes_at(c, "f2")))
    C.Check.report(name ++ " f3", C.Check.bytes_eq(M.milenage.f3(k, opc, rand), V.Vec.bytes_at(c, "f3")))
    C.Check.report(name ++ " f4", C.Check.bytes_eq(M.milenage.f4(k, opc, rand), V.Vec.bytes_at(c, "f4")))
    C.Check.report(name ++ " f5", C.Check.bytes_eq(M.milenage.f5(k, opc, rand), V.Vec.bytes_at(c, "f5")))
    C.Check.report(name ++ " f5*", C.Check.bytes_eq(M.milenage.f5_star(k, opc, rand), V.Vec.bytes_at(c, "f5_star")))

def run(cases: List<&2, V.Vec>) -> IO(Unit):
  match cases:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case c <> rest:
      do IO<Unit>:
        set(c)
        run(rest)

def capture() -> IO(Unit):
  do IO<Unit>:
    +s : V.Vec = V.Vec.field(Capture.data(), "secrets")
    +k : List<&2, U32> = V.Vec.secret(s, "k")
    +opc : List<&2, U32> = V.Vec.secret(s, "opc")
    +rand : List<&2, U32> = V.Vec.secret(s, "rand")
    +m : V.Vec = V.Vec.field(s, "milenage")
    C.Check.report("capture MAC-A", C.Check.bytes_eq(M.milenage.f1(k, opc, rand, V.Vec.secret(s, "sqn"), V.Vec.secret(s, "amf_field")), V.Vec.bytes_at(m, "mac_a")))
    C.Check.report("capture RES", C.Check.bytes_eq(M.milenage.f2(k, opc, rand), V.Vec.bytes_at(m, "res")))
    C.Check.report("capture CK", C.Check.bytes_eq(M.milenage.f3(k, opc, rand), V.Vec.bytes_at(m, "ck")))
    C.Check.report("capture IK", C.Check.bytes_eq(M.milenage.f4(k, opc, rand), V.Vec.bytes_at(m, "ik")))
    C.Check.report("capture AK", C.Check.bytes_eq(M.milenage.f5(k, opc, rand), V.Vec.bytes_at(m, "ak")))
    C.Check.report("capture AK*", C.Check.bytes_eq(M.milenage.f5_star(k, opc, rand), V.Vec.bytes_at(m, "ak_star")))

def main() -> IO(Unit):
  do IO<Unit>:
    run(V.Vec.items(V.Vec.field(Ts35208.data(), "cases")))
    capture()
