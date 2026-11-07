import Base
import ../bytes.bend as B
import ../plmn.bend as P
import ../suci.bend as Su
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/spec-ts33501-annex-c4.bend as Ts33501
import ./vectors/capture-vectors.bend as Capture

# TS 33.501 C.4.2.1 (null scheme), C.4.3.1 (Profile A) and the captured SUCI.

def digits_is(r: Result<&2, &2, B.Err, B.Digits()>, expected: B.Digits()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{ds}:
      B.bytes_eq(ds, expected)

def supi_is(r: Result<&2, &2, B.Err, Su.Supi>, mcc: B.Digits(), mnc: B.Digits(), msin: B.Digits()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{Su.Imsi{+plmn, ds}}:
      Bool.and(Bool.and(B.bytes_eq(P.Plmn.mcc(plmn), mcc), B.bytes_eq(P.Plmn.mnc(plmn), mnc)), B.bytes_eq(ds, msin))

def suci_is(r: Result<&2, &2, B.Err, Su.Suci>, routing: B.Digits(), scheme: U32, key_id: U32, output: B.Bytes()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{Su.Suci{plmn, ri, sc, kid, out}}:
      Bool.and(Bool.and(B.bytes_eq(ri, routing), Bool.and(U32.is_eq(sc, scheme), U32.is_eq(kid, key_id))), B.bytes_eq(out, output))

def fails(r: Result<&2, &2, B.Err, B.Digits()>) -> Bool:
  Result.is_fail(&2, &2, B.Err, B.Digits(), r)

def spec_case(+c: V.Vec, section: String) -> IO(Unit):
  match section:
    case "C.4.2.1":
      C.Check.report("C.4.2.1 null scheme MSIN", digits_is(Su.Suci.null_msin(V.Vec.bytes_at(c, "scheme_output")), [0, 0, 1, 0, 0, 2, 0, 8, 6]))
    case "C.4.3.1":
      do IO<Unit>:
        +key : List<&2, U32> = V.Vec.bytes_at(c, "home_network_private_key")
        +output : List<&2, U32> = V.Vec.bytes_at(c, "scheme_output")
        C.Check.report("C.4.3.1 Profile A MSIN", digits_is(Su.Suci.deconceal_a(key, output), [0, 0, 1, 0, 0, 2, 0, 8, 6]))
        C.Check.report("C.4.3.1 Profile A keys", C.Check.bytes_eq(Su.Suci.keys(key, output), List.append(&2, U32, V.Vec.bytes_at(c, "eph_enc_key"), List.append(&2, U32, V.Vec.bytes_at(c, "icb"), V.Vec.bytes_at(c, "eph_mac_key")))))
        C.Check.report("C.4.3.1 Profile A MAC tag", C.Check.bytes_eq(Su.Suci.tag(key, output), V.Vec.bytes_at(c, "mac_tag")))
        C.Check.report("C.4.3.1 a flipped MAC bit is rejected", fails(Su.Suci.deconceal_a(key, List.append(&2, U32, List.take(&2, U32, output, 44n), U32.xor(1, Maybe.default(&2, U32, List.get(&2, U32, output, 44n), 0)) <> List.drop(&2, U32, output, 45n)))))
        C.Check.report("C.4.3.1 a short output is rejected", fails(Su.Suci.deconceal_a(key, List.take(&2, U32, output, 40n))))
    case _:
      IO.pure(Unit, Unit{})

def run(cases: List<&2, V.Vec>) -> IO(Unit):
  match cases:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +c <> rest:
      do IO<Unit>:
        spec_case(c, V.Vec.text(V.Vec.field(c, "section")))
        run(rest)

def capture() -> IO(Unit):
  do IO<Unit>:
    +s : V.Vec = V.Vec.field(Capture.data(), "secrets")
    +key : List<&2, U32> = V.Vec.bytes(V.Vec.field(V.Vec.field(s, "home_network_key"), "private"))
    +identity : List<&2, U32> = V.Vec.bytes(V.Vec.field(V.Vec.field(s, "suci"), "mobile_identity_hex"))
    +output : List<&2, U32> = List.drop(&2, U32, identity, 8n)
    C.Check.report("capture SUCI decodes", suci_is(Su.Suci.read(identity), [0, 0, 0, 0], 1, 1, output))
    C.Check.report("capture SUCI re-encodes", Result.default(&2, &2, B.Err, Bool, Result.map(&2, &2, B.Err, Su.Suci, Bool, x => B.bytes_eq(Su.Suci.write(x), identity), Su.Suci.read(identity)), False{}))
    C.Check.report("capture Profile A MSIN", digits_is(Su.Suci.deconceal_a(key, output), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]))
    C.Check.report("capture SUPI", Result.default(&2, &2, B.Err, Bool, Result.map(&2, &2, B.Err, Su.Suci, Bool, x => supi_is(Su.Suci.deconceal(key, x), [0, 0, 1], [0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), Su.Suci.read(identity)), False{}))
    C.Check.report("null scheme SUCI roundtrips", suci_is(Su.Suci.read(Su.Suci.write(Su.Suci.null(P.Plmn{0, 0, 1, 0, 1, 15}, [7], [0, 0, 1]))), [7], 0, 0, [0, 241]))

def main() -> IO(Unit):
  do IO<Unit>:
    run(V.Vec.items(V.Vec.field(Ts33501.data(), "cases")))
    capture()
