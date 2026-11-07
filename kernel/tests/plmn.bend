import Base
import ../bytes.bend as B
import ../plmn.bend as P
import ./lib/check.bend as C

# The captured PLMN 00 f1 10 (MCC 001, MNC 01) and a three-digit MNC.

def plmn_is(r: B.Read(P.Plmn), p: P.Plmn, rest: B.Bytes()) -> Bool:
  match r p:
    case Done{(P.Plmn{a, b, c, d, e, f}, rs)} P.Plmn{a2, b2, c2, d2, e2, f2}:
      Bool.and(C.Check.bytes_eq([a, b, c, d, e, f], [a2, b2, c2, d2, e2, f2]), C.Check.bytes_eq(rs, rest))
    case _ _:
      False{}

def main() -> IO(Unit):
  do IO<Unit>:
    C.Check.report("read 00 f1 10", plmn_is(P.Plmn.read([0, 241, 16, 9]), P.Plmn{0, 0, 1, 0, 1, 15}, [9]))
    C.Check.report("mcc and mnc digits", Bool.and(C.Check.bytes_eq(P.Plmn.mcc(P.Plmn{0, 0, 1, 0, 1, 15}), [0, 0, 1]), C.Check.bytes_eq(P.Plmn.mnc(P.Plmn{0, 0, 1, 0, 1, 15}), [0, 1])))
    C.Check.report("write 00 f1 10", C.Check.bytes_eq(P.Plmn.write(P.Plmn{0, 0, 1, 0, 1, 15}, [9]), [0, 241, 16, 9]))
    C.Check.report("three-digit MNC 274 012", Bool.and(C.Check.bytes_eq(P.Plmn.write(P.Plmn{2, 7, 4, 0, 1, 2}, []), [114, 36, 16]), plmn_is(P.Plmn.read([114, 36, 16]), P.Plmn{2, 7, 4, 0, 1, 2}, [])))
    C.Check.report("three-digit mnc digits", C.Check.bytes_eq(P.Plmn.mnc(P.Plmn{2, 7, 4, 0, 1, 2}), [0, 1, 2]))
    C.Check.report("a non-digit is Invalid", Result.is_fail(&2, &2, B.Err, B.ReadValue(P.Plmn), P.Plmn.read([170, 241, 16])))
    C.Check.report("two bytes are Short", Result.is_fail(&2, &2, B.Err, B.ReadValue(P.Plmn), P.Plmn.read([0, 241])))
