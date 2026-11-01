import Base
import ./bytes.bend as B
import ./plmn.bend as P
import ./crypto/x25519.bend as X
import ./crypto/sha256.bend as S
import ./crypto/hmac.bend as H
import ./crypto/ctr.bend as C

# SUCI (TS 24.501 §9.11.3.4, SUPI format IMSI): one header byte, the PLMN,
# the routing indicator (two bytes of digits padded with 1111), the protection
# scheme, the home network public key identifier, then the scheme output.
# Profile A de-concealment follows TS 33.501 Annex C.3.2 and C.3.4.1.

type Suci is Data:
  Suci{plmn: P.Plmn, routing: B.Digits(), scheme: U32, key_id: U32, output: B.Bytes()}

type Supi is Data:
  Imsi{plmn: P.Plmn, msin: B.Digits()}

def Suci.header() -> U32:
  1

def Suci.scheme_null() -> U32:
  0

def Suci.scheme_a() -> U32:
  1

# Routing indicator
# -----------------

def Routing.cons(d: U32, r: Result<&2, &2, B.Err, B.Digits()>) -> Result<&2, &2, B.Err, B.Digits()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ds}:
      Done{d <> ds}

def Routing.filler(n: U32, more: Unit -> Result<&2, &2, B.Err, B.Digits()>, ok: Bool) -> Result<&2, &2, B.Err, B.Digits()>:
  match ok:
    case True{}:
      more(Unit{})
    case False{}:
      Fail{B.Invalid{n}}

def Routing.fillers(ns: List<&2, U32>) -> Result<&2, &2, B.Err, B.Digits()>:
  match ns:
    case Nil{}:
      Done{[]}
    case +n <> rest:
      Routing.filler(n, u => Routing.fillers(rest), U32.is_eq(n, 15))

def Routing.step(n: U32, rest: List<&2, U32>, more: Unit -> Result<&2, &2, B.Err, B.Digits()>, digit: Bool, filler: Bool) -> Result<&2, &2, B.Err, B.Digits()>:
  match digit:
    case True{}:
      Routing.cons(n, more(Unit{}))
    case False{}:
      match filler:
        case True{}:
          Routing.fillers(rest)
        case False{}:
          Fail{B.Invalid{n}}

# Digits, then fillers only.
def Routing.digits(ns: List<&2, U32>) -> Result<&2, &2, B.Err, B.Digits()>:
  match ns:
    case Nil{}:
      Done{[]}
    case +n <> +rest:
      Routing.step(n, rest, u => Routing.digits(rest), B.Tbcd.is_digit(n), U32.is_eq(n, 15))

def Routing.nonempty(r: Result<&2, &2, B.Err, B.Digits()>) -> Result<&2, &2, B.Err, B.Digits()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Nil{}}:
      Fail{B.Invalid{15}}
    case Done{d <> ds}:
      Done{d <> ds}

# Two bytes: digit 1 | digit 2, digit 3 | digit 4.
def Routing.read(+b0: U32, +b1: U32) -> Result<&2, &2, B.Err, B.Digits()>:
  Routing.nonempty(Routing.digits([U32.and(15, b0), U32.and(15, U32.shrn(b0, 4n)), U32.and(15, b1), U32.and(15, U32.shrn(b1, 4n))]))

def Routing.pad4(ds: B.Digits()) -> List<&2, U32>:
  match ds:
    case Nil{}:
      [15, 15, 15, 15]
    case a <> Nil{}:
      [a, 15, 15, 15]
    case a <> b <> Nil{}:
      [a, b, 15, 15]
    case a <> b <> c <> Nil{}:
      [a, b, c, 15]
    case a <> b <> c <> d <> more:
      [a, b, c, d]

def Routing.write4(ns: List<&2, U32>, rest: B.Bytes()) -> B.Bytes():
  match ns:
    case a <> b <> c <> d <> more:
      B.write_nibbles(b, a, B.write_nibbles(d, c, rest))
    case _:
      rest

def Routing.write(ds: B.Digits(), rest: B.Bytes()) -> B.Bytes():
  Routing.write4(Routing.pad4(ds), rest)

# Decoding the identity
# ---------------------

def Suci.r_key(plmn: P.Plmn, routing: B.Digits(), scheme: U32, r: B.Read(U32)) -> Result<&2, &2, B.Err, Suci>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(key_id, output)}:
      Done{Suci{plmn, routing, scheme, key_id, output}}

def Suci.r_scheme(plmn: P.Plmn, routing: B.Digits(), r: B.Read(U32)) -> Result<&2, &2, B.Err, Suci>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(scheme, rest)}:
      Suci.r_key(plmn, routing, scheme, B.u8(rest))

def Suci.r_routing(plmn: P.Plmn, r: Result<&2, &2, B.Err, B.Digits()>, rest: B.Bytes()) -> Result<&2, &2, B.Err, Suci>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{routing}:
      Suci.r_scheme(plmn, routing, B.u8(rest))

def Suci.r_plmn(r: B.Read(P.Plmn)) -> Result<&2, &2, B.Err, Suci>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(plmn, b0 <> b1 <> rest)}:
      Suci.r_routing(plmn, Routing.read(b0, b1), rest)
    case Done{(plmn, short)}:
      Fail{B.Short{}}

def Suci.r_type(h: U32, rest: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, Suci>:
  match ok:
    case True{}:
      Suci.r_plmn(P.Plmn.read(rest))
    case False{}:
      Fail{B.Unsupported{h}}

def Suci.r_header(r: B.Read(U32)) -> Result<&2, &2, B.Err, Suci>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+h, rest)}:
      Suci.r_type(h, rest, U32.is_eq(h, Suci.header()))

def Suci.read(bs: B.Bytes()) -> Result<&2, &2, B.Err, Suci>:
  Suci.r_header(B.u8(bs))

def Suci.write(s: Suci) -> B.Bytes():
  match s:
    case Suci{plmn, routing, scheme, key_id, output}:
      Suci.header() <> P.Plmn.write(plmn, Routing.write(routing, B.write_u8(scheme, B.write_u8(key_id, output))))

def Suci.null(plmn: P.Plmn, routing: B.Digits(), msin: B.Digits()) -> Suci:
  Suci{plmn, routing, Suci.scheme_null(), 0, B.write_tbcd(msin, [])}

# Scheme output
# -------------

def Suci.null_msin(output: B.Bytes()) -> Result<&2, &2, B.Err, B.Digits()>:
  B.Tbcd.decode(output)

def Suci.eph(output: B.Bytes()) -> B.Bytes():
  List.take(&2, U32, output, 32n)

def Suci.cipher(+output: B.Bytes()) -> B.Bytes():
  List.take(&2, U32, List.drop(&2, U32, output, 32n), Nat.sub(List.length(&2, U32, output), 40n))

def Suci.mac(+output: B.Bytes()) -> B.Bytes():
  List.drop(&2, U32, output, Nat.sub(List.length(&2, U32, output), 8n))

# ANSI X9.63 KDF with SHA-256, 64 bytes: Ek (16) || ICB (16) || MK (32).
def Suci.x963(+z: B.Bytes(), +info: B.Bytes()) -> B.Bytes():
  List.append(&2, U32, S.sha256(List.append(&2, U32, z, List.append(&2, U32, [0, 0, 0, 1], info))), S.sha256(List.append(&2, U32, z, List.append(&2, U32, [0, 0, 0, 2], info))))

def Suci.keys(hn_private: B.Bytes(), +output: B.Bytes()) -> B.Bytes():
  Suci.x963(X.x25519(hn_private, Suci.eph(output)), Suci.eph(output))

def Suci.tag_of(+keys: B.Bytes(), output: B.Bytes()) -> B.Bytes():
  List.take(&2, U32, H.hmac(List.drop(&2, U32, keys, 32n), Suci.cipher(output)), 8n)

# The MAC tag this output should carry.
def Suci.tag(hn_private: B.Bytes(), +output: B.Bytes()) -> B.Bytes():
  Suci.tag_of(Suci.keys(hn_private, output), output)

def Suci.a_mac(+output: B.Bytes(), +keys: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, B.Digits()>:
  match ok:
    case True{}:
      B.Tbcd.decode(C.ctr(List.take(&2, U32, keys, 16n), List.take(&2, U32, List.drop(&2, U32, keys, 16n), 16n), Suci.cipher(output)))
    case False{}:
      Fail{B.Invalid{2}}

def Suci.a_keys(+output: B.Bytes(), +keys: B.Bytes()) -> Result<&2, &2, B.Err, B.Digits()>:
  Suci.a_mac(output, keys, B.bytes_eq(Suci.tag_of(keys, output), Suci.mac(output)))

def Suci.a_len(hn_private: B.Bytes(), +output: B.Bytes(), long_enough: Bool) -> Result<&2, &2, B.Err, B.Digits()>:
  match long_enough:
    case True{}:
      Suci.a_keys(output, Suci.keys(hn_private, output))
    case False{}:
      Fail{B.Short{}}

# Profile A: ephemeral key (32) || ciphertext (at least 1) || MAC tag (8).
def Suci.deconceal_a(hn_private: B.Bytes(), +output: B.Bytes()) -> Result<&2, &2, B.Err, B.Digits()>:
  Suci.a_len(hn_private, output, Nat.is_ge(List.length(&2, U32, output), 41n))

def Suci.supi(plmn: P.Plmn, r: Result<&2, &2, B.Err, B.Digits()>) -> Result<&2, &2, B.Err, Supi>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{msin}:
      Done{Imsi{plmn, msin}}

def Suci.by_scheme(hn_private: B.Bytes(), s: Suci, null: Bool, profile_a: Bool) -> Result<&2, &2, B.Err, Supi>:
  match s:
    case Suci{plmn, routing, scheme, key_id, output}:
      match null:
        case True{}:
          Suci.supi(plmn, Suci.null_msin(output))
        case False{}:
          match profile_a:
            case True{}:
              Suci.supi(plmn, Suci.deconceal_a(hn_private, output))
            case False{}:
              Fail{B.Unsupported{scheme}}

# The SUPI behind a SUCI, with the home network's Profile A private key.
def Suci.deconceal(hn_private: B.Bytes(), s: Suci) -> Result<&2, &2, B.Err, Supi>:
  match s:
    case Suci{plmn, routing, +scheme, key_id, output}:
      Suci.by_scheme(hn_private, Suci{plmn, routing, scheme, key_id, output}, U32.is_eq(scheme, Suci.scheme_null()), U32.is_eq(scheme, Suci.scheme_a()))
