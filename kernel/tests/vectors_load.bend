import Base
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/spec-fips180-4.bend as Fips180
import ./vectors/spec-fips197.bend as Fips197
import ./vectors/spec-rfc4231.bend as Rfc4231
import ./vectors/spec-rfc4493.bend as Rfc4493
import ./vectors/spec-rfc7748.bend as Rfc7748
import ./vectors/spec-sp800-38a.bend as Sp800
import ./vectors/spec-ts33401-annex-c.bend as Ts33401
import ./vectors/spec-ts33501-annex-c4.bend as Ts33501
import ./vectors/spec-ts35208.bend as Ts35208
import ./vectors/capture-vectors.bend as Capture

# Every generated vector module loads, and each has at least one case.

def count(doc: V.Vec, +key: String) -> Nat:
  List.length(&2, V.Vec, V.Vec.items(V.Vec.field(doc, key)))

def report(name: String, +n: Nat) -> IO(Bool):
  do IO<Bool>:
    IO.print(name ++ ": " ++ Nat.show(n) ++ " cases")
    return Nat.is_gt(n, 0n)

def main() -> IO(Unit):
  do IO<Unit>:
    a : Bool <- report("fips180-4", count(Fips180.data(), "cases"))
    b : Bool <- report("fips197", count(Fips197.data(), "cases"))
    c : Bool <- report("rfc4231", count(Rfc4231.data(), "cases"))
    d : Bool <- report("rfc4493", count(Rfc4493.data(), "cases"))
    e : Bool <- report("rfc7748", count(Rfc7748.data(), "cases"))
    f : Bool <- report("sp800-38a", count(Sp800.data(), "cases"))
    g : Bool <- report("ts33401-annex-c", count(Ts33401.data(), "cases"))
    h : Bool <- report("ts33501-annex-c4", count(Ts33501.data(), "cases"))
    i : Bool <- report("ts35208", count(Ts35208.data(), "cases"))
    j : Bool <- report("capture/vectors messages", count(Capture.data(), "messages"))
    C.Check.report("every vector module has cases", List.all(~&2, ~Bool, ~(x => x), [a, b, c, d, e, f, g, h, i, j]))
