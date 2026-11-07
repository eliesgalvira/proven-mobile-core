import Base
import ../crypto/x25519.bend as X
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/spec-rfc7748.bend as Rfc7748

# RFC 7748 §5.2 vectors, the iterated test, and the §6.1 Diffie-Hellman example.

# k, u := X25519(k, u), k
def iterate(n: Nat, +k: List<&2, U32>, u: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      k
    case 1n+p:
      iterate(p, X.x25519(k, u), k)

def case_(+c: V.Vec, kind: String) -> IO(Unit):
  match kind:
    case "x25519":
      C.Check.report("RFC 7748 5.2 " ++ V.Vec.text(V.Vec.field(c, "u")), C.Check.bytes_eq(X.x25519(V.Vec.bytes_at(c, "scalar"), V.Vec.bytes_at(c, "u")), V.Vec.bytes_at(c, "output")))
    case "x25519_iterated":
      C.Check.report("RFC 7748 5.2 iterated " ++ Nat.show(V.Vec.nat(V.Vec.field(c, "iterations"))), C.Check.bytes_eq(iterate(V.Vec.nat(V.Vec.field(c, "iterations")), V.Vec.bytes_at(c, "initial_k"), V.Vec.bytes_at(c, "initial_u")), V.Vec.bytes_at(c, "output")))
    case "diffie_hellman":
      do IO<Unit>:
        C.Check.report("RFC 7748 6.1 Alice public", C.Check.bytes_eq(X.x25519(V.Vec.bytes_at(c, "alice_private"), X.x25519.base()), V.Vec.bytes_at(c, "alice_public")))
        C.Check.report("RFC 7748 6.1 Bob public", C.Check.bytes_eq(X.x25519(V.Vec.bytes_at(c, "bob_private"), X.x25519.base()), V.Vec.bytes_at(c, "bob_public")))
        C.Check.report("RFC 7748 6.1 shared (Alice)", C.Check.bytes_eq(X.x25519(V.Vec.bytes_at(c, "alice_private"), V.Vec.bytes_at(c, "bob_public")), V.Vec.bytes_at(c, "shared_secret")))
        C.Check.report("RFC 7748 6.1 shared (Bob)", C.Check.bytes_eq(X.x25519(V.Vec.bytes_at(c, "bob_private"), V.Vec.bytes_at(c, "alice_public")), V.Vec.bytes_at(c, "shared_secret")))
    case _:
      C.Check.report("unknown case kind", False{})

def run(cases: List<&2, V.Vec>) -> IO(Unit):
  match cases:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +c <> rest:
      do IO<Unit>:
        case_(c, V.Vec.text(V.Vec.field(c, "kind")))
        run(rest)

def main() -> IO(Unit):
  run(V.Vec.items(V.Vec.field(Rfc7748.data(), "cases")))
