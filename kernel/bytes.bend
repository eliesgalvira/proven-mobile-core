import Base

# The only module that turns byte lists into numbers and back. Readers answer
# the value and the unread rest; writers prepend to `rest`, so encoders compose
# without `++` chains. Multi-byte values are assembled by bit layout (`cat4`),
# which keeps every roundtrip proof a plain computation.

type Err is Data:
  Short{}
  Invalid{tag: U32}
  Unsupported{tag: U32}

def Bytes() -> Data:
  List<&2, U32>

def Digits() -> Data:
  List<&2, U32>

def Nibbles() -> Data:
  Sigma<&2, &2, U32, _ => U32>

def ReadValue(-A: Data) -> Data:
  Sigma<&2, &2, A, _ => Bytes()>

def Read(-A: Data) -> Data:
  Result<&2, &2, Err, ReadValue(A)>

def is_byte(x: U32) -> Bool:
  U32.is_lt(x, 256)

def all_bytes(bs: Bytes()) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case b <> rest:
      Bool.and(is_byte(b), all_bytes(rest))

def bytes_eq(xs: Bytes(), ys: Bytes()) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yt:
      False{}
    case x <> xt Nil{}:
      False{}
    case x <> xt y <> yt:
      Bool.and(U32.is_eq(x, y), bytes_eq(xt, yt))

# lo's low 4 bits, then hi's low 28 bits: (hi << 4) | (lo & 15).
def cat4(lo: U32, hi: U32) -> U32:
  match lo hi:
    case U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, _}}}}} U32{WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WCon{h24, WCon{h25, WCon{h26, WCon{h27, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WCon{h24, WCon{h25, WCon{h26, WCon{h27, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

# (hi << 8) | (lo & 255)
def cat8(+lo: U32, hi: U32) -> U32:
  cat4(lo, cat4(U32.shrn(lo, 4n), hi))

def u8(bs: Bytes()) -> Read(U32):
  match bs:
    case Nil{}:
      Fail{Short{}}
    case b <> rest:
      Done{(b, rest)}

def u16(bs: Bytes()) -> Read(U32):
  match bs:
    case b1 <> b0 <> rest:
      Done{(cat8(b0, b1), rest)}
    case _:
      Fail{Short{}}

def u24(bs: Bytes()) -> Read(U32):
  match bs:
    case b2 <> b1 <> b0 <> rest:
      Done{(cat8(b0, cat8(b1, b2)), rest)}
    case _:
      Fail{Short{}}

def u32(bs: Bytes()) -> Read(U32):
  match bs:
    case b3 <> b2 <> b1 <> b0 <> rest:
      Done{(cat8(b0, cat8(b1, cat8(b2, b3))), rest)}
    case _:
      Fail{Short{}}

def write_u8(v: U32, rest: Bytes()) -> Bytes():
  U32.and(255, v) <> rest

def write_u16(+v: U32, rest: Bytes()) -> Bytes():
  write_u8(U32.shrn(v, 8n), write_u8(v, rest))

def write_u24(+v: U32, rest: Bytes()) -> Bytes():
  write_u8(U32.shrn(v, 16n), write_u16(v, rest))

def write_u32(+v: U32, rest: Bytes()) -> Bytes():
  write_u8(U32.shrn(v, 24n), write_u24(v, rest))

def nibbles(bs: Bytes()) -> Read(Nibbles()):
  match bs:
    case Nil{}:
      Fail{Short{}}
    case +b <> rest:
      Done{((U32.and(15, U32.shrn(b, 4n)), U32.and(15, b)), rest)}

def write_nibbles(hi: U32, lo: U32, rest: Bytes()) -> Bytes():
  cat4(lo, U32.and(15, hi)) <> rest

def Take.cons(b: U32, r: Read(Bytes())) -> Read(Bytes()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(taken, rest)}:
      Done{(b <> taken, rest)}

# Exactly n bytes, or Short.
def take(n: Nat, bs: Bytes()) -> Read(Bytes()):
  match n bs:
    case 0n rest:
      Done{([], rest)}
    case 1n+p Nil{}:
      Fail{Short{}}
    case 1n+p b <> rest:
      Take.cons(b, take(p, rest))

# TBCD (TS 24.008 §10.5.1.4): each byte holds two digits, the first in its low
# nibble; an odd digit count ends with the filler 0xF in the last high nibble.

def Tbcd.is_digit(d: U32) -> Bool:
  U32.is_lt(d, 10)

def Tbcd.all_digits(ds: Digits()) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case d <> rest:
      Bool.and(Tbcd.is_digit(d), Tbcd.all_digits(rest))

# ceil(n / 2)
def Tbcd.byte_count(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      1n
    case 2n+p:
      1n+Tbcd.byte_count(p)

def Tbcd.cons2(lo: U32, hi: U32, r: Result<&2, &2, Err, Digits()>) -> Result<&2, &2, Err, Digits()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ds}:
      Done{lo <> hi <> ds}

# A filler is only allowed in the last byte.
def Tbcd.filler(lo: U32, rest: Bytes()) -> Result<&2, &2, Err, Digits()>:
  match rest:
    case Nil{}:
      Done{[lo]}
    case b <> more:
      Fail{Invalid{15}}

def Tbcd.high(lo: U32, hi: U32, rest: Bytes(), more: Unit -> Result<&2, &2, Err, Digits()>, hi_digit: Bool, hi_filler: Bool) -> Result<&2, &2, Err, Digits()>:
  match hi_digit:
    case True{}:
      Tbcd.cons2(lo, hi, more(Unit{}))
    case False{}:
      match hi_filler:
        case True{}:
          Tbcd.filler(lo, rest)
        case False{}:
          Fail{Invalid{hi}}

def Tbcd.low(lo: U32, +hi: U32, rest: Bytes(), more: Unit -> Result<&2, &2, Err, Digits()>, lo_digit: Bool) -> Result<&2, &2, Err, Digits()>:
  match lo_digit:
    case True{}:
      Tbcd.high(lo, hi, rest, more, Tbcd.is_digit(hi), U32.is_eq(hi, 15))
    case False{}:
      Fail{Invalid{lo}}

def Tbcd.decode(bs: Bytes()) -> Result<&2, &2, Err, Digits()>:
  match bs:
    case Nil{}:
      Done{[]}
    case +b <> +rest:
      Tbcd.low(U32.and(15, b), U32.and(15, U32.shrn(b, 4n)), rest, u => Tbcd.decode(rest), Tbcd.is_digit(U32.and(15, b)))

def Tbcd.with_rest(r: Result<&2, &2, Err, Digits()>, rest: Bytes()) -> Read(Digits()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ds}:
      Done{(ds, rest)}

def Tbcd.after_take(r: Read(Bytes())) -> Read(Digits()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bytes, rest)}:
      Tbcd.with_rest(Tbcd.decode(bytes), rest)

# The digits held in the next `count` bytes.
def tbcd_digits(bs: Bytes(), count: Nat) -> Read(Digits()):
  Tbcd.after_take(take(count, bs))

def write_tbcd(ds: Digits(), rest: Bytes()) -> Bytes():
  match ds:
    case Nil{}:
      rest
    case d <> Nil{}:
      cat4(d, 15) <> rest
    case d1 <> d2 <> more:
      cat4(d1, U32.and(15, d2)) <> write_tbcd(more, rest)
