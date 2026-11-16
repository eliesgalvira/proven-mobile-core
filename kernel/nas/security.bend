import Base
import ../bytes.bend as B
import ../crypto/cmac.bend as M
import ../crypto/ctr.bend as C

# NAS security: 128-NIA2 and 128-NEA2 (TS 33.401 Annex B, as used by TS 33.501
# §6.4.3), NEA0, the security-protected NAS message of TS 24.501 §4.4 and §9.1.1,
# and the NAS COUNT with the uplink estimate of TS 24.501 §4.4.3.1.

# The algorithms the kernel can select; nothing else is representable.
type Nas.Ea is Data:
  Nea0{}
  Nea2{}

type Nas.Ia is Data:
  Nia2{}

# Algorithm identifiers (TS 24.501 §9.11.3.34), and the identifiers the kernel implements.
def Nas.Ea.id(ea: Nas.Ea) -> U32:
  match ea:
    case Nea0{}:
      0
    case Nea2{}:
      2

def Nas.Ia.id(ia: Nas.Ia) -> U32:
  match ia:
    case Nia2{}:
      2

def Nas.Ea.of_nat(n: Nat) -> Maybe<&2, Nas.Ea>:
  match n:
    case 0n:
      Some{Nea0{}}
    case 2n:
      Some{Nea2{}}
    case other:
      None{}

def Nas.Ia.of_nat(n: Nat) -> Maybe<&2, Nas.Ia>:
  match n:
    case 2n:
      Some{Nia2{}}
    case other:
      None{}

def Nas.Ea.of(id: U32) -> Maybe<&2, Nas.Ea>:
  Nas.Ea.of_nat(U32.to_nat(id))

def Nas.Ia.of(id: U32) -> Maybe<&2, Nas.Ia>:
  Nas.Ia.of_nat(U32.to_nat(id))

# NAS COUNT: a 16-bit overflow counter and an 8-bit sequence number.
type Nas.Count is Data:
  Count{overflow: U32, sqn: U32}

def Nas.Count.zero() -> Nas.Count:
  Count{0, 0}

def Nas.Count.sqn(c: Nas.Count) -> U32:
  match c:
    case Count{overflow, sqn}:
      sqn

# The 32-bit COUNT: 0x00 || overflow || sqn.
def Nas.Count.value(c: Nas.Count) -> U32:
  match c:
    case Count{overflow, sqn}:
      U32.or(U32.shln(overflow, 8n), sqn)

def Nas.Count.carry(overflow: U32, wrapped: Bool) -> U32:
  match wrapped:
    case True{}:
      U32.inc(overflow)
    case False{}:
      overflow

def Nas.Count.same(a: Nas.Count, b: Nas.Count) -> Bool:
  match a b:
    case Count{o1, s1} Count{o2, s2}:
      Bool.and(U32.is_eq(o1, o2), U32.is_eq(s1, s2))

def Nas.Count.next(c: Nas.Count) -> Nas.Count:
  match c:
    case Count{overflow, +sqn}:
      Count{Nas.Count.carry(overflow, U32.is_eq(sqn, 255)), U32.and(255, U32.inc(sqn))}

# c moved forward from last: same overflow and a larger sequence number, or the
# next overflow (which did not wrap, as last's overflow was below 65535).
def Nas.Count.advanced(last: Nas.Count, c: Nas.Count) -> Bool:
  match last c:
    case Count{+o1, s1} Count{+o2, s2}:
      Bool.or(Bool.and(U32.is_eq(o2, o1), U32.is_lt(s1, s2)), Bool.and(U32.is_eq(o2, U32.inc(o1)), U32.is_lt(o1, 65535)))

# Security header types 1 to 4 (TS 24.501 §9.3).
type Nas.Protection is Data:
  Integrity{}
  Ciphered{}
  IntegrityNew{}
  CipheredNew{}

def Nas.Protection.code(p: Nas.Protection) -> U32:
  match p:
    case Integrity{}:
      1
    case Ciphered{}:
      2
    case IntegrityNew{}:
      3
    case CipheredNew{}:
      4

def Nas.Protection.ciphers(p: Nas.Protection) -> Bool:
  match p:
    case Integrity{}:
      False{}
    case Ciphered{}:
      True{}
    case IntegrityNew{}:
      False{}
    case CipheredNew{}:
      True{}

def Nas.Protection.of_nat(n: Nat) -> Maybe<&2, Nas.Protection>:
  match n:
    case 1n:
      Some{Integrity{}}
    case 2n:
      Some{Ciphered{}}
    case 3n:
      Some{IntegrityNew{}}
    case 4n:
      Some{CipheredNew{}}
    case other:
      None{}

def Nas.Protection.of(code: U32) -> Maybe<&2, Nas.Protection>:
  Nas.Protection.of_nat(U32.to_nat(code))

def Nas.epd() -> U32:
  126

# Keys and algorithms of one NAS security context; BEARER is the NAS connection
# identifier (TS 33.501 §6.4.3.1), 1 for 3GPP access.
type Nas.Keys is Data:
  Keys{k_int: B.Bytes(), k_enc: B.Bytes(), ea: Nas.Ea, ia: Nas.Ia, bearer: U32}

def Nas.Keys.k_int(k: Nas.Keys) -> B.Bytes():
  match k:
    case Keys{k_int, k_enc, ea, ia, bearer}:
      k_int

def Nas.Keys.ia(k: Nas.Keys) -> Nas.Ia:
  match k:
    case Keys{k_int, k_enc, ea, ia, bearer}:
      ia

def Nas.Keys.bearer(k: Nas.Keys) -> U32:
  match k:
    case Keys{k_int, k_enc, ea, ia, bearer}:
      bearer

# The same keys: one NAS security context.
def Nas.Keys.same(a: Nas.Keys, b: Nas.Keys) -> Bool:
  match a b:
    case Keys{i1, e1, ea1, ia1, b1} Keys{i2, e2, ea2, ia2, b2}:
      Bool.and(B.bytes_eq(i1, i2), Bool.and(B.bytes_eq(e1, e2), Bool.and(U32.is_eq(Nas.Ea.id(ea1), Nas.Ea.id(ea2)), Bool.and(U32.is_eq(Nas.Ia.id(ia1), Nas.Ia.id(ia2)), U32.is_eq(b1, b2)))))

def Nas.downlink() -> U32:
  1

def Nas.uplink() -> U32:
  0

# COUNT || BEARER || DIRECTION || 0^26: the first 8 bytes of both algorithm inputs.
def Nas.header8(count32: U32, bearer: U32, dir: U32, rest: B.Bytes()) -> B.Bytes():
  B.write_u32(count32, U32.or(U32.shln(U32.and(31, bearer), 3n), U32.shln(U32.and(1, dir), 2n)) <> 0 <> 0 <> 0 <> rest)

# 128-NIA2: the first 32 bits of the CMAC (TS 33.401 B.2.3).
def nia2(k_int: B.Bytes(), count32: U32, bearer: U32, dir: U32, msg: B.Bytes()) -> B.Bytes():
  List.take(&2, U32, M.cmac(k_int, Nas.header8(count32, bearer, dir, msg)), 4n)

# 128-NIA2 over a message of `bits` bits (the TS 33.401 test sets).
def nia2_bits(k_int: B.Bytes(), count32: U32, bearer: U32, dir: U32, msg: B.Bytes(), bits: Nat) -> B.Bytes():
  List.take(&2, U32, M.cmac_bits(k_int, Nas.header8(count32, bearer, dir, msg), Nat.add(64n, bits)), 4n)

# 128-NEA2: AES-CTR with the counter block COUNT || BEARER || DIRECTION || 0^90 (TS 33.401 B.1.3).
def nea2(k_enc: B.Bytes(), count32: U32, bearer: U32, dir: U32, msg: B.Bytes()) -> B.Bytes():
  C.ctr(k_enc, Nas.header8(count32, bearer, dir, [0, 0, 0, 0, 0, 0, 0, 0]), msg)

def Nas.cipher(ea: Nas.Ea, k_enc: B.Bytes(), count32: U32, bearer: U32, dir: U32, msg: B.Bytes()) -> B.Bytes():
  match ea:
    case Nea0{}:
      msg
    case Nea2{}:
      nea2(k_enc, count32, bearer, dir, msg)

def Nas.cipher_if(ea: Nas.Ea, k_enc: B.Bytes(), count32: U32, bearer: U32, dir: U32, msg: B.Bytes(), on: Bool) -> B.Bytes():
  match on:
    case True{}:
      Nas.cipher(ea, k_enc, count32, bearer, dir, msg)
    case False{}:
      msg

def Nas.mac(ia: Nas.Ia, k_int: B.Bytes(), count32: U32, bearer: U32, dir: U32, msg: B.Bytes()) -> B.Bytes():
  match ia:
    case Nia2{}:
      nia2(k_int, count32, bearer, dir, msg)

# A security protected NAS message (TS 24.501 §9.1.1): EPD, security header
# type, MAC (4), sequence number, then the plain NAS message, ciphered or not.
def Nas.seal(keys: Nas.Keys, +prot: Nas.Protection, +dir: U32, +count: Nas.Count, plain: B.Bytes()) -> B.Bytes():
  match keys:
    case Keys{k_int, k_enc, ea, ia, +bearer}:
      +body = Nas.cipher_if(ea, k_enc, Nas.Count.value(count), bearer, dir, plain, Nas.Protection.ciphers(prot))
      Nas.epd() <> Nas.Protection.code(prot) <> List.append(&2, U32, Nas.mac(ia, k_int, Nas.Count.value(count), bearer, dir, Nas.Count.sqn(count) <> body), Nas.Count.sqn(count) <> body)

type Nas.Opened is Data:
  Opened{prot: Nas.Protection, plain: B.Bytes()}

def Nas.o_body(ea: Nas.Ea, k_enc: B.Bytes(), count32: U32, bearer: U32, dir: U32, +prot: Nas.Protection, body: B.Bytes(), mac_ok: Bool) -> Result<&2, &2, B.Err, Nas.Opened>:
  match mac_ok:
    case True{}:
      Done{Opened{prot, Nas.cipher_if(ea, k_enc, count32, bearer, dir, body, Nas.Protection.ciphers(prot))}}
    case False{}:
      Fail{B.Invalid{Nas.Protection.code(prot)}}

def Nas.o_prot(keys: Nas.Keys, +dir: U32, +count32: U32, received: B.Bytes(), sqn: U32, +body: B.Bytes(), prot: Maybe<&2, Nas.Protection>) -> Result<&2, &2, B.Err, Nas.Opened>:
  match keys:
    case Keys{k_int, k_enc, ea, ia, +bearer}:
      match prot:
        case None{}:
          Fail{B.Unsupported{0}}
        case Some{+p}:
          Nas.o_body(ea, k_enc, count32, bearer, dir, p, body, B.bytes_eq(received, Nas.mac(ia, k_int, count32, bearer, dir, sqn <> body)))

def Nas.o_epd(keys: Nas.Keys, dir: U32, count32: U32, code: U32, received: B.Bytes(), sqn: U32, body: B.Bytes(), epd_ok: Bool) -> Result<&2, &2, B.Err, Nas.Opened>:
  match epd_ok:
    case True{}:
      Nas.o_prot(keys, dir, count32, received, sqn, body, Nas.Protection.of(code))
    case False{}:
      Fail{B.Invalid{code}}

# Verify and decipher a protected message with the COUNT the caller estimated.
def Nas.open(keys: Nas.Keys, dir: U32, count: Nas.Count, msg: B.Bytes()) -> Result<&2, &2, B.Err, Nas.Opened>:
  match msg:
    case epd <> code <> m0 <> m1 <> m2 <> m3 <> sqn <> body:
      Nas.o_epd(keys, dir, Nas.Count.value(count), code, [m0, m1, m2, m3], sqn, body, U32.is_eq(epd, Nas.epd()))
    case _:
      Fail{B.Short{}}

# A security protected NAS message: security header type 1 to 4.
def Nas.protected_by(p: Maybe<&2, Nas.Protection>) -> Bool:
  match p:
    case Some{x}:
      True{}
    case None{}:
      False{}

def Nas.is_protected(msg: B.Bytes()) -> Bool:
  match msg:
    case epd <> code <> rest:
      Nas.protected_by(Nas.Protection.of(code))
    case _:
      False{}

def Nas.resealed(keys: Nas.Keys, +count: Nas.Count, +msg: B.Bytes(), r: Result<&2, &2, B.Err, Nas.Opened>) -> Bool:
  match r:
    case Done{Opened{prot, plain}}:
      B.bytes_eq(Nas.seal(keys, prot, Nas.downlink(), count, plain), msg)
    case Fail{e}:
      False{}

# msg is a downlink message sealed under keys at count: what it opens to
# there, sealed there again, is msg.
def Nas.sealed(+keys: Nas.Keys, +count: Nas.Count, +msg: B.Bytes()) -> Bool:
  Nas.resealed(keys, count, msg, Nas.open(keys, Nas.downlink(), count, msg))

# The MAC a protected message carries.
def Nas.received_mac(msg: B.Bytes()) -> B.Bytes():
  List.take(&2, U32, List.drop(&2, U32, msg, 2n), 4n)

# A context with its downlink COUNT and the last accepted uplink COUNT.
type Nas.Ctx is Data:
  Ctx{keys: Nas.Keys, dl: Nas.Count, ul: Maybe<&2, Nas.Count>}

def Nas.Ctx.ul(ctx: Nas.Ctx) -> Maybe<&2, Nas.Count>:
  match ctx:
    case Ctx{keys, dl, ul}:
      ul

type Nas.Protected is Data:
  Protected{msg: B.Bytes(), ctx: Nas.Ctx}

def Nas.Protected.msg(p: Nas.Protected) -> B.Bytes():
  match p:
    case Protected{msg, ctx}:
      msg

def Nas.Protected.ctx(p: Nas.Protected) -> Nas.Ctx:
  match p:
    case Protected{msg, ctx}:
      ctx

def Nas.protect(ctx: Nas.Ctx, prot: Nas.Protection, plain: B.Bytes()) -> Nas.Protected:
  match ctx:
    case Ctx{+keys, +dl, ul}:
      Protected{Nas.seal(keys, prot, Nas.downlink(), dl, plain), Ctx{keys, Nas.Count.next(dl), ul}}

def Nas.estimate.step(+overflow: U32, +sqn: U32, greater: Bool, same: Bool, room: Bool) -> Result<&2, &2, B.Err, Nas.Count>:
  match greater:
    case True{}:
      Done{Count{overflow, sqn}}
    case False{}:
      match same:
        case True{}:
          Fail{B.Invalid{sqn}}
        case False{}:
          match room:
            case True{}:
              Done{Count{U32.inc(overflow), sqn}}
            case False{}:
              Fail{B.Unsupported{sqn}}

# TS 24.501 §4.4.3.1: the uplink COUNT of a received sequence number. A
# repeated sequence number is a replay; a smaller one wraps into the next
# overflow, unless the overflow counter is exhausted.
def Nas.estimate(ul: Maybe<&2, Nas.Count>, +sqn: U32) -> Result<&2, &2, B.Err, Nas.Count>:
  match ul:
    case None{}:
      Done{Count{0, sqn}}
    case Some{Count{+overflow, +last}}:
      Nas.estimate.step(overflow, sqn, U32.is_lt(last, sqn), U32.is_eq(last, sqn), U32.is_lt(overflow, 65535))

type Nas.Unprotected is Data:
  Unprotected{prot: Nas.Protection, plain: B.Bytes(), count: Nas.Count, ctx: Nas.Ctx}

def Nas.Unprotected.count(u: Nas.Unprotected) -> Nas.Count:
  match u:
    case Unprotected{prot, plain, count, ctx}:
      count

def Nas.u_open(keys: Nas.Keys, dl: Nas.Count, +count: Nas.Count, r: Result<&2, &2, B.Err, Nas.Opened>) -> Result<&2, &2, B.Err, Nas.Unprotected>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Opened{prot, plain}}:
      Done{Unprotected{prot, plain, count, Ctx{keys, dl, Some{count}}}}

def Nas.u_count(+keys: Nas.Keys, dl: Nas.Count, msg: B.Bytes(), r: Result<&2, &2, B.Err, Nas.Count>) -> Result<&2, &2, B.Err, Nas.Unprotected>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+count}:
      Nas.u_open(keys, dl, count, Nas.open(keys, Nas.uplink(), count, msg))

def Nas.u_sqn(ctx: Nas.Ctx, +msg: B.Bytes(), r: B.Read(U32)) -> Result<&2, &2, B.Err, Nas.Unprotected>:
  match ctx:
    case Ctx{keys, dl, ul}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{(sqn, rest)}:
          Nas.u_count(keys, dl, msg, Nas.estimate(ul, sqn))

# Verify an uplink message, estimating its COUNT, and record that COUNT.
def Nas.unprotect(ctx: Nas.Ctx, +msg: B.Bytes()) -> Result<&2, &2, B.Err, Nas.Unprotected>:
  Nas.u_sqn(ctx, msg, B.u8(List.drop(&2, U32, msg, 6n)))
