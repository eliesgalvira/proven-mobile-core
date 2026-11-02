import Base
import ./bytes.bend as B

# ITU-T X.691 aligned PER building blocks (the ones NGAP uses). The stream is
# a list of bits in wire order. A cursor carries `rem`, the bits left before
# the next octet boundary (0 when aligned). Readers answer the value and the
# cursor after it; writers prepend to `rest` and take the `rem` at which they
# start, since alignment padding depends on it; `after` gives the `rem` after
# a value, so writers compose: `A.write(a, rem, B.write(b, A.after(a, rem), rest))`.

def Bits() -> Data:
  List<&2, Bool>

type Cur is Data:
  Cur{rem: Nat, bits: Bits()}

def Rd(-A: Data) -> Data:
  Result<&2, &2, B.Err, Sigma<&2, &2, A, _ => Cur>>

def Rem.next(r: Nat) -> Nat:
  match r:
    case 0n:
      7n
    case 1n+p:
      p

def Rem.add(n: Nat, r: Nat) -> Nat:
  match n:
    case 0n:
      r
    case 1n+p:
      Rem.add(p, Rem.next(r))

# Bits
# ----

def Bit.read(c: Cur) -> Rd(Bool):
  match c:
    case Cur{rem, bits}:
      match bits:
        case Nil{}:
          Fail{B.Short{}}
        case b <> rest:
          Done{(b, Cur{Rem.next(rem), rest})}

def Bit.write(b: Bool, rem: Nat, rest: Bits()) -> Bits():
  b <> rest

def Bit.after(rem: Nat) -> Nat:
  Rem.next(rem)

def Bits.cons(b: Bool, r: Rd(Bits())) -> Rd(Bits()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bs, c)}:
      Done{(b <> bs, c)}

def Bits.go(n: Nat, after: Nat, bits: Bits()) -> Rd(Bits()):
  match n bits:
    case 0n rest:
      Done{([], Cur{after, rest})}
    case 1n+p Nil{}:
      Fail{B.Short{}}
    case 1n+p b <> rest:
      Bits.cons(b, Bits.go(p, after, rest))

# Exactly n bits.
def Bits.read(+n: Nat, c: Cur) -> Rd(Bits()):
  match c:
    case Cur{+rem, bits}:
      Bits.go(n, Rem.add(n, rem), bits)

def Bits.write(bs: Bits(), rem: Nat, rest: Bits()) -> Bits():
  List.append(&2, Bool, bs, rest)

def Bits.after(n: Nat, rem: Nat) -> Nat:
  Rem.add(n, rem)

# Octet alignment (§11.1.4): the padding bits are zero.
def Align.go(rem: Nat, bits: Bits()) -> Rd(Unit):
  match rem bits:
    case 0n rest:
      Done{(Unit{}, Cur{0n, rest})}
    case 1n+p Nil{}:
      Fail{B.Short{}}
    case 1n+p b <> rest:
      match b:
        case False{}:
          Align.go(p, rest)
        case True{}:
          Fail{B.Invalid{0}}

def Align.read(c: Cur) -> Rd(Unit):
  match c:
    case Cur{rem, bits}:
      Align.go(rem, bits)

def Align.write(rem: Nat, rest: Bits()) -> Bits():
  match rem:
    case 0n:
      rest
    case 1n+p:
      False{} <> Align.write(p, rest)

# Numbers
# -------

# The low n bits of a word, least significant first, zero beyond the word.
def Word.prefix(n: Nat, m: Nat, w: Word(m)) -> Bits():
  match n m:
    case 0n _:
      []
    case 1n+p 0n:
      False{} <> Word.prefix(p, 0n, w)
    case 1n+p 1n+q:
      match w:
        case WCon{b, t}:
          b <> Word.prefix(p, q, t)

# A word from bits, least significant first; missing bits are zero, extra bits are dropped.
def Word.of_lsb(m: Nat, bs: Bits()) -> Word(m):
  match m:
    case 0n:
      WNil{}
    case 1n+q:
      match bs:
        case Nil{}:
          WCon{False{}, Word.of_lsb(q, [])}
        case b <> rest:
          WCon{b, Word.of_lsb(q, rest)}

# Every bit from position n up is zero.
def Word.high_zero(m: Nat, w: Word(m), n: Nat) -> Bool:
  match m:
    case 0n:
      True{}
    case 1n+q:
      match w:
        case WCon{b, t}:
          match n:
            case 0n:
              Bool.and(Bool.not(b), Word.high_zero(q, t, 0n))
            case 1n+p:
              Word.high_zero(q, t, p)

# n bits in wire order (most significant first).
def U32.to_bits(n: Nat, v: U32) -> Bits():
  match v:
    case U32{w}:
      List.reverse(&2, Bool, Word.prefix(n, 32n, w))

def U32.of_bits(bs: Bits()) -> U32:
  U32{Word.of_lsb(32n, List.reverse(&2, Bool, bs))}

def U32.fits(n: Nat, v: U32) -> Bool:
  match v:
    case U32{w}:
      Word.high_zero(32n, w, n)

def Nat.is_odd(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n:
      True{}
    case 2n+k:
      Nat.is_odd(k)

def Nat.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      0n
    case 2n+k:
      1n+Nat.half(k)

def Nat.pow2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(Nat.pow2(p))

def Nat.of_lsb(bs: Bits()) -> Nat:
  match bs:
    case Nil{}:
      0n
    case b <> rest:
      match b:
        case False{}:
          Nat.double(Nat.of_lsb(rest))
        case True{}:
          1n+Nat.double(Nat.of_lsb(rest))

def Nat.to_lsb(n: Nat, +k: Nat) -> Bits():
  match n:
    case 0n:
      []
    case 1n+p:
      Nat.is_odd(k) <> Nat.to_lsb(p, Nat.half(k))

def Nat.to_bits(n: Nat, k: Nat) -> Bits():
  List.reverse(&2, Bool, Nat.to_lsb(n, k))

def Nat.of_bits(bs: Bits()) -> Nat:
  Nat.of_lsb(List.reverse(&2, Bool, bs))

# Constrained whole number in a bit-field (§11.5.7.1, range up to 255). The
# value is the offset from the lower bound, as on the wire; `diff` is the
# range less one.
def Int.valid(n: Nat, diff: U32, +x: U32) -> Bool:
  Bool.and(U32.fits(n, x), U32.is_le(x, diff))

def Int.of(x: U32, c: Cur, ok: Bool) -> Rd(U32):
  match ok:
    case True{}:
      Done{(x, c)}
    case False{}:
      Fail{B.Invalid{x}}

def Int.check(diff: U32, +x: U32, c: Cur) -> Rd(U32):
  Int.of(x, c, U32.is_le(x, diff))

def Int.bits(diff: U32, r: Rd(Bits())) -> Rd(U32):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bs, c)}:
      Int.check(diff, U32.of_bits(bs), c)

def Int.read(n: Nat, diff: U32, c: Cur) -> Rd(U32):
  Int.bits(diff, Bits.read(n, c))

def Int.write(n: Nat, x: U32, rem: Nat, rest: Bits()) -> Bits():
  List.append(&2, Bool, U32.to_bits(n, x), rest)

def Int.after(n: Nat, rem: Nat) -> Nat:
  Rem.add(n, rem)

# Constrained whole number in one or two aligned octets (§11.5.7.2–3): n is 8 or 16.
def AInt.aligned(n: Nat, diff: U32, r: Rd(Unit)) -> Rd(U32):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(u, c)}:
      Int.read(n, diff, c)

def AInt.read(n: Nat, diff: U32, c: Cur) -> Rd(U32):
  AInt.aligned(n, diff, Align.read(c))

def AInt.write(n: Nat, x: U32, rem: Nat, rest: Bits()) -> Bits():
  Align.write(rem, Int.write(n, x, 0n, rest))

def AInt.after(n: Nat, rem: Nat) -> Nat:
  Rem.add(n, 0n)

# Normally small non-negative whole number (§11.6), values below 64 only.
def Small.valid(v: U32) -> Bool:
  Int.valid(6n, 63, v)

def Small.form(r: Rd(Bool)) -> Rd(U32):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(b, c)}:
      match b:
        case False{}:
          Int.read(6n, 63, c)
        case True{}:
          Fail{B.Unsupported{64}}

def Small.read(c: Cur) -> Rd(U32):
  Small.form(Bit.read(c))

def Small.write(v: U32, rem: Nat, rest: Bits()) -> Bits():
  False{} <> Int.write(6n, v, Rem.next(rem), rest)

def Small.after(rem: Nat) -> Nat:
  Rem.add(7n, rem)

# Length determinant (§11.9.3.6–8), unconstrained: one octet below 128, two
# below 16384; fragmented lengths are not supported.
def Len.valid(n: Nat) -> Bool:
  Nat.is_lt(n, 16384n)

def Len.of(n: Nat, c: Cur, ok: Bool) -> Rd(Nat):
  match ok:
    case True{}:
      Done{(n, c)}
    case False{}:
      Fail{B.Invalid{128}}

def Len.canonical(+n: Nat, c: Cur) -> Rd(Nat):
  Len.of(n, c, Nat.is_le(128n, n))

def Len.long(r: Rd(Bits())) -> Rd(Nat):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bs, c)}:
      Len.canonical(Nat.of_bits(bs), c)

def Len.short(r: Rd(Bits())) -> Rd(Nat):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bs, c)}:
      Done{(Nat.of_bits(bs), c)}

def Len.second(r: Rd(Bool)) -> Rd(Nat):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(b, c)}:
      match b:
        case False{}:
          Len.long(Bits.read(14n, c))
        case True{}:
          Fail{B.Unsupported{192}}

def Len.first(r: Rd(Bool)) -> Rd(Nat):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(b, c)}:
      match b:
        case False{}:
          Len.short(Bits.read(7n, c))
        case True{}:
          Len.second(Bit.read(c))

def Len.aligned(r: Rd(Unit)) -> Rd(Nat):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(u, c)}:
      Len.first(Bit.read(c))

def Len.read(c: Cur) -> Rd(Nat):
  Len.aligned(Align.read(c))

def Len.body(n: Nat, short: Bool, rest: Bits()) -> Bits():
  match short:
    case True{}:
      False{} <> List.append(&2, Bool, Nat.to_bits(7n, n), rest)
    case False{}:
      True{} <> False{} <> List.append(&2, Bool, Nat.to_bits(14n, n), rest)

def Len.write(+n: Nat, rem: Nat, rest: Bits()) -> Bits():
  Align.write(rem, Len.body(n, Nat.is_lt(n, 128n), rest))

def Len.after(rem: Nat) -> Nat:
  0n

# Constrained length (§11.9.3.3, upper bound below 64K) as a count: lo plus
# an n-bit offset of at most diff.
def Size.valid(+lo: Nat, diff: Nat, +k: Nat) -> Bool:
  Bool.and(Nat.is_le(lo, k), Nat.is_le(k, Nat.add(lo, diff)))

def Size.of(lo: Nat, x: Nat, c: Cur, ok: Bool) -> Rd(Nat):
  match ok:
    case True{}:
      Done{(Nat.add(lo, x), c)}
    case False{}:
      Fail{B.Invalid{U32.from_nat(x)}}

def Size.check(lo: Nat, diff: Nat, +x: Nat, c: Cur) -> Rd(Nat):
  Size.of(lo, x, c, Nat.is_le(x, diff))

def Size.bits(lo: Nat, diff: Nat, r: Rd(Bits())) -> Rd(Nat):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bs, c)}:
      Size.check(lo, diff, Nat.of_bits(bs), c)

def Size.aligned(n: Nat, lo: Nat, diff: Nat, r: Rd(Unit)) -> Rd(Nat):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(u, c)}:
      Size.bits(lo, diff, Bits.read(n, c))

# `al` is True for ranges above 255, whose length takes one or two aligned octets.
def Size.read(al: Bool, n: Nat, lo: Nat, diff: Nat, c: Cur) -> Rd(Nat):
  match al:
    case False{}:
      Size.bits(lo, diff, Bits.read(n, c))
    case True{}:
      Size.aligned(n, lo, diff, Align.read(c))

def Size.write(al: Bool, n: Nat, lo: Nat, k: Nat, rem: Nat, rest: Bits()) -> Bits():
  match al:
    case False{}:
      List.append(&2, Bool, Nat.to_bits(n, Nat.sub(k, lo)), rest)
    case True{}:
      Align.write(rem, List.append(&2, Bool, Nat.to_bits(n, Nat.sub(k, lo)), rest))

def Size.after(al: Bool, n: Nat, rem: Nat) -> Nat:
  match al:
    case False{}:
      Rem.add(n, rem)
    case True{}:
      Rem.add(n, 0n)

# Octets
# ------

def Octets.cons(b: U32, r: Rd(B.Bytes())) -> Rd(B.Bytes()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bs, c)}:
      Done{(b <> bs, c)}

def Octets.go(n: Nat, rem: Nat, bits: Bits()) -> Rd(B.Bytes()):
  match n bits:
    case 0n rest:
      Done{([], Cur{rem, rest})}
    case 1n+p b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> rest:
      Octets.cons(U32.of_bits([b7, b6, b5, b4, b3, b2, b1, b0]), Octets.go(p, rem, rest))
    case 1n+p _:
      Fail{B.Short{}}

# Exactly n octets at the current position (no alignment).
def Octets.read(n: Nat, c: Cur) -> Rd(B.Bytes()):
  match c:
    case Cur{rem, bits}:
      Octets.go(n, rem, bits)

def Octets.write(bs: B.Bytes(), rem: Nat, rest: Bits()) -> Bits():
  match bs:
    case Nil{}:
      rest
    case b <> more:
      List.append(&2, Bool, U32.to_bits(8n, b), Octets.write(more, rem, rest))

def Octets.after(rem: Nat) -> Nat:
  rem

# Bytes in and out of the bit stream.
def unpack(bs: B.Bytes()) -> Bits():
  Octets.write(bs, 0n, [])

def pack(bits: Bits()) -> B.Bytes():
  match bits:
    case b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> rest:
      U32.of_bits([b7, b6, b5, b4, b3, b2, b1, b0]) <> pack(rest)
    case _:
      []

# Fixed-size strings that are octet-aligned (§16.10, §17.6).
def AOctets.aligned(n: Nat, r: Rd(Unit)) -> Rd(B.Bytes()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(u, c)}:
      Octets.read(n, c)

def AOctets.read(n: Nat, c: Cur) -> Rd(B.Bytes()):
  AOctets.aligned(n, Align.read(c))

def AOctets.write(bs: B.Bytes(), rem: Nat, rest: Bits()) -> Bits():
  Align.write(rem, Octets.write(bs, 0n, rest))

def AOctets.after(rem: Nat) -> Nat:
  0n

def ABits.aligned(n: Nat, r: Rd(Unit)) -> Rd(Bits()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(u, c)}:
      Bits.read(n, c)

def ABits.read(n: Nat, c: Cur) -> Rd(Bits()):
  ABits.aligned(n, Align.read(c))

def ABits.write(bs: Bits(), rem: Nat, rest: Bits()) -> Bits():
  Align.write(rem, List.append(&2, Bool, bs, rest))

def ABits.after(n: Nat, rem: Nat) -> Nat:
  Rem.add(n, 0n)

# Constrained whole number of indefinite length (§11.5.7.4, range above 64K):
# a count of octets (1 to 1+diff, as a constrained length of n bits) and the
# value in that many aligned octets. The value is kept as its canonical octets.
def Big.canonical(bs: B.Bytes()) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case b <> more:
      match more:
        case Nil{}:
          True{}
        case b2 <> rest:
          Bool.not(U32.is_eq(b, 0))

def Big.valid(diff: Nat, +bs: B.Bytes()) -> Bool:
  Bool.and(Big.canonical(bs), Bool.and(Nat.is_le(List.length(&2, U32, bs), 1n+diff), B.all_bytes(bs)))

def Big.of(bs: B.Bytes(), c: Cur, ok: Bool) -> Rd(B.Bytes()):
  match ok:
    case True{}:
      Done{(bs, c)}
    case False{}:
      Fail{B.Invalid{0}}

def Big.check(+bs: B.Bytes(), c: Cur) -> Rd(B.Bytes()):
  Big.of(bs, c, Big.canonical(bs))

def Big.octets(r: Rd(B.Bytes())) -> Rd(B.Bytes()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bs, c)}:
      Big.check(bs, c)

def Big.count(r: Rd(Nat)) -> Rd(B.Bytes()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(l, c)}:
      Big.octets(AOctets.read(l, c))

def Big.read(n: Nat, diff: Nat, c: Cur) -> Rd(B.Bytes()):
  Big.count(Size.read(False{}, n, 1n, diff, c))

def Big.write(+n: Nat, +bs: B.Bytes(), +rem: Nat, rest: Bits()) -> Bits():
  Size.write(False{}, n, 1n, List.length(&2, U32, bs), rem, AOctets.write(bs, Size.after(False{}, n, rem), rest))

def Big.after(rem: Nat) -> Nat:
  0n

# Variable-size strings with an upper bound below 64K (§16.11, §17.7): a
# constrained length, then the contents, octet-aligned.
def OctStr.valid(lo: Nat, diff: Nat, +bs: B.Bytes()) -> Bool:
  Bool.and(Size.valid(lo, diff, List.length(&2, U32, bs)), B.all_bytes(bs))

def OctStr.count(r: Rd(Nat)) -> Rd(B.Bytes()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(l, c)}:
      AOctets.read(l, c)

def OctStr.read(al: Bool, n: Nat, lo: Nat, diff: Nat, c: Cur) -> Rd(B.Bytes()):
  OctStr.count(Size.read(al, n, lo, diff, c))

def OctStr.write(+al: Bool, +n: Nat, lo: Nat, +bs: B.Bytes(), +rem: Nat, rest: Bits()) -> Bits():
  Size.write(al, n, lo, List.length(&2, U32, bs), rem, AOctets.write(bs, Size.after(al, n, rem), rest))

def OctStr.after(rem: Nat) -> Nat:
  0n

def BitStr.valid(lo: Nat, diff: Nat, bs: Bits()) -> Bool:
  Size.valid(lo, diff, List.length(&2, Bool, bs))

def BitStr.count(r: Rd(Nat)) -> Rd(Bits()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(l, c)}:
      ABits.read(l, c)

def BitStr.read(al: Bool, n: Nat, lo: Nat, diff: Nat, c: Cur) -> Rd(Bits()):
  BitStr.count(Size.read(al, n, lo, diff, c))

def BitStr.write(+al: Bool, +n: Nat, lo: Nat, +bs: Bits(), +rem: Nat, rest: Bits()) -> Bits():
  Size.write(al, n, lo, List.length(&2, Bool, bs), rem, ABits.write(bs, Size.after(al, n, rem), rest))

def BitStr.after(bs: Bits(), rem: Nat) -> Nat:
  Rem.add(List.length(&2, Bool, bs), 0n)

# Unconstrained strings (§16.6, §17.5) and open types (§11.2): a length
# determinant, then the contents.
def Open.valid(+bs: B.Bytes()) -> Bool:
  Bool.and(Len.valid(List.length(&2, U32, bs)), B.all_bytes(bs))

def Open.count(r: Rd(Nat)) -> Rd(B.Bytes()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(l, c)}:
      Octets.read(l, c)

def Open.read(c: Cur) -> Rd(B.Bytes()):
  Open.count(Len.read(c))

def Open.write(+bs: B.Bytes(), rem: Nat, rest: Bits()) -> Bits():
  Len.write(List.length(&2, U32, bs), rem, Octets.write(bs, 0n, rest))

def Open.after(rem: Nat) -> Nat:
  0n

def UBitStr.valid(bs: Bits()) -> Bool:
  Len.valid(List.length(&2, Bool, bs))

def UBitStr.count(r: Rd(Nat)) -> Rd(Bits()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(l, c)}:
      Bits.read(l, c)

def UBitStr.read(c: Cur) -> Rd(Bits()):
  UBitStr.count(Len.read(c))

def UBitStr.write(+bs: Bits(), rem: Nat, rest: Bits()) -> Bits():
  Len.write(List.length(&2, Bool, bs), rem, List.append(&2, Bool, bs, rest))

def UBitStr.after(bs: Bits(), rem: Nat) -> Nat:
  Rem.add(List.length(&2, Bool, bs), 0n)

# PrintableString (§30, 8 bits per character in the aligned variant).
def Str.printable(+c: U32) -> Bool:
  Bool.or(U32.is_eq(c, 32), Bool.or(Bool.and(U32.is_le(39, c), U32.is_le(c, 41)), Bool.or(Bool.and(U32.is_le(43, c), U32.is_le(c, 58)), Bool.or(U32.is_eq(c, 61), Bool.or(U32.is_eq(c, 63), Bool.or(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), Bool.and(U32.is_le(97, c), U32.is_le(c, 122))))))))

def Str.all(s: B.Bytes()) -> Bool:
  match s:
    case Nil{}:
      True{}
    case c <> rest:
      Bool.and(Str.printable(c), Str.all(rest))

def Str.valid(lo: Nat, diff: Nat, +s: B.Bytes()) -> Bool:
  Bool.and(Size.valid(lo, diff, List.length(&2, U32, s)), Str.all(s))

def Str.of(s: B.Bytes(), c: Cur, ok: Bool) -> Rd(B.Bytes()):
  match ok:
    case True{}:
      Done{(s, c)}
    case False{}:
      Fail{B.Invalid{1}}

def Str.check(r: Rd(B.Bytes())) -> Rd(B.Bytes()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+s, c)}:
      Str.of(s, c, Str.all(s))

def Str.read(al: Bool, n: Nat, lo: Nat, diff: Nat, c: Cur) -> Rd(B.Bytes()):
  Str.check(OctStr.read(al, n, lo, diff, c))

def Str.write(al: Bool, n: Nat, lo: Nat, s: B.Bytes(), rem: Nat, rest: Bits()) -> Bits():
  OctStr.write(al, n, lo, s, rem, rest)

def Str.after(rem: Nat) -> Nat:
  0n

def UStr.valid(+s: B.Bytes()) -> Bool:
  Bool.and(Len.valid(List.length(&2, U32, s)), Str.all(s))

def UStr.read(c: Cur) -> Rd(B.Bytes()):
  Str.check(Open.read(c))

def UStr.write(s: B.Bytes(), rem: Nat, rest: Bits()) -> Bits():
  Open.write(s, rem, rest)

def UStr.after(rem: Nat) -> Nat:
  0n

# ENUMERATED (§14): a root index, or (when extensible) an extension index.
type Enum is Data:
  Root{index: U32}
  Ext{index: U32}

def Enum.valid(n: Nat, diff: U32, ext: Bool, e: Enum) -> Bool:
  match e:
    case Root{i}:
      Int.valid(n, diff, i)
    case Ext{i}:
      Bool.and(ext, Small.valid(i))

def Enum.root(r: Rd(U32)) -> Rd(Enum):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(i, c)}:
      Done{(Root{i}, c)}

def Enum.ext(r: Rd(U32)) -> Rd(Enum):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(i, c)}:
      Done{(Ext{i}, c)}

def Enum.bit(n: Nat, diff: U32, r: Rd(Bool)) -> Rd(Enum):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(b, c)}:
      match b:
        case False{}:
          Enum.root(Int.read(n, diff, c))
        case True{}:
          Enum.ext(Small.read(c))

def Enum.read(n: Nat, diff: U32, ext: Bool, c: Cur) -> Rd(Enum):
  match ext:
    case False{}:
      Enum.root(Int.read(n, diff, c))
    case True{}:
      Enum.bit(n, diff, Bit.read(c))

def Enum.write(n: Nat, ext: Bool, e: Enum, rem: Nat, rest: Bits()) -> Bits():
  match ext e:
    case False{} Root{i}:
      Int.write(n, i, rem, rest)
    case False{} Ext{i}:
      Int.write(n, i, rem, rest)
    case True{} Root{i}:
      False{} <> Int.write(n, i, Rem.next(rem), rest)
    case True{} Ext{i}:
      True{} <> Small.write(i, Rem.next(rem), rest)

def Enum.after(n: Nat, ext: Bool, e: Enum, rem: Nat) -> Nat:
  match ext e:
    case False{} Root{i}:
      Rem.add(n, rem)
    case False{} Ext{i}:
      Rem.add(n, rem)
    case True{} Root{i}:
      Rem.add(n, Rem.next(rem))
    case True{} Ext{i}:
      Rem.add(7n, Rem.next(rem))
