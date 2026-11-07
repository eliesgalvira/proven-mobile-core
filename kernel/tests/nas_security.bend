import Base
import ../bytes.bend as B
import ../nas/security.bend as N
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/spec-ts33401-annex-c.bend as Ts33401
import ./vectors/capture-vectors.bend as Capture

# TS 33.401 Annex C (128-EEA2 C.1, 128-EIA2 C.2), then every protected NAS
# message of the capture: its MAC, and protect/unprotect reproducing the bytes.

def nat(c: V.Vec, +key: String) -> Nat:
  V.Vec.nat(V.Vec.field(c, key))

def read_u32(r: B.Read(U32)) -> U32:
  match r:
    case Fail{e}:
      0
    case Done{(v, rest)}:
      v

def count32(c: V.Vec) -> U32:
  read_u32(B.u32(V.Vec.bytes_at(c, "count")))

# The first `bits` bits of two byte strings agree (whole bytes, then a masked byte).
def prefix_eq(+xs: List<&2, U32>, +ys: List<&2, U32>, +bits: Nat) -> Bool:
  +n : Nat = Nat.div(bits, 8n)
  +mask : U32 = U32.and(255, U32.shln(255, Nat.sub(8n, Nat.mod(bits, 8n))))
  Bool.and(B.bytes_eq(List.take(&2, U32, xs, n), List.take(&2, U32, ys, n)), U32.is_eq(U32.and(mask, Maybe.default(&2, U32, List.get(&2, U32, xs, n), 0)), U32.and(mask, Maybe.default(&2, U32, List.get(&2, U32, ys, n), 0))))

def spec_case(+c: V.Vec, algorithm: String) -> IO(Unit):
  match algorithm:
    case "128-EEA2":
      C.Check.report("TS 33.401 " ++ V.Vec.text(V.Vec.field(c, "section")) ++ " 128-EEA2", prefix_eq(N.nea2(V.Vec.bytes_at(c, "key"), count32(c), U32.from_nat(nat(c, "bearer")), U32.from_nat(nat(c, "direction")), V.Vec.bytes_at(c, "plaintext")), V.Vec.bytes_at(c, "ciphertext"), nat(c, "length_bits")))
    case "128-EIA2":
      C.Check.report("TS 33.401 " ++ V.Vec.text(V.Vec.field(c, "section")) ++ " 128-EIA2", C.Check.bytes_eq(N.nia2_bits(V.Vec.bytes_at(c, "key"), count32(c), U32.from_nat(nat(c, "bearer")), U32.from_nat(nat(c, "direction")), V.Vec.bytes_at(c, "message"), nat(c, "length_bits")), V.Vec.bytes_at(c, "mac")))
    case _:
      C.Check.report("unknown algorithm", False{})

def run(cases: List<&2, V.Vec>) -> IO(Unit):
  match cases:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +c <> rest:
      do IO<Unit>:
        spec_case(c, V.Vec.text(V.Vec.field(c, "algorithm")))
        run(rest)

def count_pick(more: Unit -> U32, found: U32, hit: Bool) -> U32:
  match hit:
    case True{}:
      found
    case False{}:
      more(Unit{})

# The captured NAS COUNT of message `index`.
def count_of(counts: List<&2, V.Vec>, +index: Nat) -> U32:
  match counts:
    case Nil{}:
      0
    case +c <> rest:
      count_pick(u => count_of(rest, index), U32.from_nat(V.Vec.nat(V.Vec.field(c, "count"))), Nat.is_eq(V.Vec.nat(V.Vec.field(c, "index")), index))

def direction(d: String) -> U32:
  match d:
    case "DL":
      N.Nas.downlink()
    case _:
      N.Nas.uplink()

def mac_check(+k_int: List<&2, U32>, counts: List<&2, V.Vec>, +m: V.Vec, protected: Maybe<&2, V.Vec>) -> IO(Unit):
  match protected:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{outer}:
      +bytes : List<&2, U32> = V.Vec.bytes(outer)
      C.Check.report("capture MAC of " ++ V.Vec.text(V.Vec.field(m, "message")), C.Check.bytes_eq(N.nia2(k_int, count_of(counts, V.Vec.nat(V.Vec.field(m, "index"))), 1, direction(V.Vec.text(V.Vec.field(m, "direction"))), List.drop(&2, U32, bytes, 6n)), V.Vec.bytes_at(m, "mac")))

def macs(+k_int: List<&2, U32>, +counts: List<&2, V.Vec>, messages: List<&2, V.Vec>) -> IO(Unit):
  match messages:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +m <> rest:
      do IO<Unit>:
        mac_check(k_int, counts, m, V.Vec.get(m, "outer_hex"))
        macs(k_int, counts, rest)

# The captured message with this index.
def unprotected_is(r: Result<&2, &2, B.Err, N.Nas.Unprotected>, plain: List<&2, U32>, prot: U32, count: U32) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{N.Unprotected{p, pl, c, ctx}}:
      Bool.and(Bool.and(B.bytes_eq(pl, plain), U32.is_eq(N.Nas.Protection.code(p), prot)), U32.is_eq(N.Nas.Count.value(c), count))

def next_ctx(r: Result<&2, &2, B.Err, N.Nas.Unprotected>, fallback: N.Nas.Ctx) -> N.Nas.Ctx:
  match r:
    case Fail{e}:
      fallback
    case Done{N.Unprotected{p, pl, c, ctx}}:
      ctx

def capture() -> IO(Unit):
  do IO<Unit>:
    +s : V.Vec = V.Vec.field(Capture.data(), "secrets")
    +k_int : List<&2, U32> = V.Vec.bytes(V.Vec.field(V.Vec.field(s, "k_nas_int"), "value"))
    +k_enc : List<&2, U32> = V.Vec.bytes(V.Vec.field(V.Vec.field(s, "k_nas_enc"), "value"))
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    macs(k_int, V.Vec.items(V.Vec.field(s, "nas_counts")), msgs)
    +keys : N.Nas.Keys = N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, 1}
    +ctx0 : N.Nas.Ctx = N.Ctx{keys, N.Nas.Count.zero(), None{}}
    +smc : V.Vec = V.Vec.message(msgs, 21n)
    +p1 : N.Nas.Protected = N.Nas.protect(ctx0, N.IntegrityNew{}, V.Vec.bytes_at(smc, "plaintext_hex"))
    C.Check.report("protect reproduces the Security mode command", C.Check.bytes_eq(N.Nas.Protected.msg(p1), V.Vec.bytes_at(smc, "outer_hex")))
    +accept : V.Vec = V.Vec.message(msgs, 26n)
    C.Check.report("protect reproduces the Registration accept", C.Check.bytes_eq(N.Nas.Protected.msg(N.Nas.protect(N.Nas.Protected.ctx(p1), N.Ciphered{}, V.Vec.bytes_at(accept, "plaintext_hex"))), V.Vec.bytes_at(accept, "outer_hex")))
    +smcomplete : V.Vec = V.Vec.message(msgs, 23n)
    +u1 : Result<&2, &2, B.Err, N.Nas.Unprotected> = N.Nas.unprotect(ctx0, V.Vec.bytes_at(smcomplete, "outer_hex"))
    C.Check.report("unprotect accepts the Security mode complete", unprotected_is(u1, V.Vec.bytes_at(smcomplete, "plaintext_hex"), 4, 0))
    +ctx1 : N.Nas.Ctx = next_ctx(u1, ctx0)
    +complete : V.Vec = V.Vec.message(msgs, 29n)
    +u2 : Result<&2, &2, B.Err, N.Nas.Unprotected> = N.Nas.unprotect(ctx1, V.Vec.bytes_at(complete, "outer_hex"))
    C.Check.report("unprotect accepts the Registration complete", unprotected_is(u2, V.Vec.bytes_at(complete, "plaintext_hex"), 2, 1))
    C.Check.report("a replayed Registration complete is rejected", Result.is_fail(&2, &2, B.Err, N.Nas.Unprotected, N.Nas.unprotect(next_ctx(u2, ctx1), V.Vec.bytes_at(complete, "outer_hex"))))
    C.Check.report("a corrupted MAC is rejected", Result.is_fail(&2, &2, B.Err, N.Nas.Unprotected, N.Nas.unprotect(ctx1, List.append(&2, U32, [126, 2, 0, 0, 0, 0], List.drop(&2, U32, V.Vec.bytes_at(complete, "outer_hex"), 6n)))))
    C.Check.report("a six-byte message is Short", Result.is_fail(&2, &2, B.Err, N.Nas.Unprotected, N.Nas.unprotect(ctx1, [126, 2, 0, 0, 0, 0])))

def main() -> IO(Unit):
  do IO<Unit>:
    run(V.Vec.items(V.Vec.field(Ts33401.data(), "cases")))
    capture()
