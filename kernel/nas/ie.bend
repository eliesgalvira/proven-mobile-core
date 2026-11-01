import Base
import ../bytes.bend as B

# NAS information element formats (TS 24.007 §11.2). A decoded IE keeps its
# wire format, its length byte(s) as read and its content, so that encoding
# reproduces the input byte for byte. Typed views of the content are
# separate functions (kernel/nas/mm.bend).

def fits8(+x: U32) -> Bool:
  U32.is_eq(U32.and(255, x), x)

def fits16(+x: U32) -> Bool:
  U32.is_eq(U32.and(65535, x), x)

# A length prefix and the bytes it covers.
type LenBody is Data:
  LenBody{len: U32, body: B.Bytes()}

def LenBody.valid8(lb: LenBody) -> Bool:
  match lb:
    case LenBody{+len, body}:
      Bool.and(fits8(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)))

def LenBody.valid16(lb: LenBody) -> Bool:
  match lb:
    case LenBody{+len, body}:
      Bool.and(fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)))

def Len.join(len: U32, r: B.Read(B.Bytes())) -> B.Read(LenBody):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(body, rest)}:
      Done{(LenBody{len, body}, rest)}

def Len.take(+len: U32, rest: B.Bytes(), ok: Bool) -> B.Read(LenBody):
  match ok:
    case True{}:
      Len.join(len, B.take(U32.to_nat(len), rest))
    case False{}:
      Fail{B.Invalid{len}}

def Lv.body(r: B.Read(U32)) -> B.Read(LenBody):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+len, rest)}:
      Len.take(len, rest, fits8(len))

def Lve.body(r: B.Read(U32)) -> B.Read(LenBody):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+len, rest)}:
      Len.take(len, rest, fits16(len))

# LV: one length byte, then that many bytes.
def lv(bs: B.Bytes()) -> B.Read(LenBody):
  Lv.body(B.u8(bs))

# LV-E: a two-byte length, then that many bytes.
def lve(bs: B.Bytes()) -> B.Read(LenBody):
  Lve.body(B.u16(bs))

def write_lv(lb: LenBody, rest: B.Bytes()) -> B.Bytes():
  match lb:
    case LenBody{len, body}:
      B.write_u8(len, List.append(&2, U32, body, rest))

def write_lve(lb: LenBody, rest: B.Bytes()) -> B.Bytes():
  match lb:
    case LenBody{len, body}:
      B.write_u16(len, List.append(&2, U32, body, rest))

# Mandatory fields
# ----------------

type Lay is Data:
  V1{}
  Lv{}
  LvE{}

type Field is Data:
  FByte{v: U32}
  FLv{lb: LenBody}
  FLvE{lb: LenBody}

def Field.valid(lay: Lay, f: Field) -> Bool:
  match lay f:
    case V1{} FByte{+v}:
      fits8(v)
    case Lv{} FLv{lb}:
      LenBody.valid8(lb)
    case LvE{} FLvE{lb}:
      LenBody.valid16(lb)
    case _ _:
      False{}

def Fields.valid(lays: List<&2, Lay>, fs: List<&2, Field>) -> Bool:
  match lays fs:
    case Nil{} Nil{}:
      True{}
    case l <> ls f <> rest:
      Bool.and(Field.valid(l, f), Fields.valid(ls, rest))
    case _ _:
      False{}

def Field.write(f: Field, rest: B.Bytes()) -> B.Bytes():
  match f:
    case FByte{v}:
      B.write_u8(v, rest)
    case FLv{lb}:
      write_lv(lb, rest)
    case FLvE{lb}:
      write_lve(lb, rest)

def Fields.write(fs: List<&2, Field>, rest: B.Bytes()) -> B.Bytes():
  match fs:
    case Nil{}:
      rest
    case f <> more:
      Field.write(f, Fields.write(more, rest))

def Field.byte_ok(v: U32, rest: B.Bytes(), ok: Bool) -> B.Read(Field):
  match ok:
    case True{}:
      Done{(FByte{v}, rest)}
    case False{}:
      Fail{B.Invalid{v}}

def Field.byte(r: B.Read(U32)) -> B.Read(Field):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+v, rest)}:
      Field.byte_ok(v, rest, fits8(v))

def Field.of_lv(r: B.Read(LenBody)) -> B.Read(Field):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(lb, rest)}:
      Done{(FLv{lb}, rest)}

def Field.of_lve(r: B.Read(LenBody)) -> B.Read(Field):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(lb, rest)}:
      Done{(FLvE{lb}, rest)}

def Field.read(lay: Lay, bs: B.Bytes()) -> B.Read(Field):
  match lay:
    case V1{}:
      Field.byte(B.u8(bs))
    case Lv{}:
      Field.of_lv(lv(bs))
    case LvE{}:
      Field.of_lve(lve(bs))

def Fields.cons(f: Field, r: B.Read(List<&2, Field>)) -> B.Read(List<&2, Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(fs, rest)}:
      Done{(f <> fs, rest)}

def Fields.next(r: B.Read(Field), more: B.Bytes() -> B.Read(List<&2, Field>)) -> B.Read(List<&2, Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(f, rest)}:
      Fields.cons(f, more(rest))

def Fields.read(lays: List<&2, Lay>, bs: B.Bytes()) -> B.Read(List<&2, Field>):
  match lays:
    case Nil{}:
      Done{([], bs)}
    case l <> ls:
      Fields.next(Field.read(l, bs), rest => Fields.read(ls, rest))

# Optional IEs
# ------------

# One octet (IEI with its value in the low nibble, or a bare type), a fixed
# number of value bytes, a one-byte length, or a two-byte length.
type Fmt is Data:
  T1{}
  Tv{n: Nat}
  Tlv{}
  TlvE{}

# The formats an IEI below 0x80 can have.
type Low is Data:
  LowTv{n: Nat}
  LowTlv{}
  LowTlvE{}

def Fmt.of_low(l: Low) -> Fmt:
  match l:
    case LowTv{n}:
      Tv{n}
    case LowTlv{}:
      Tlv{}
    case LowTlvE{}:
      TlvE{}

def Fmt.eq(a: Fmt, b: Fmt) -> Bool:
  match a b:
    case T1{} T1{}:
      True{}
    case Tv{m} Tv{n}:
      Nat.is_eq(m, n)
    case Tlv{} Tlv{}:
      True{}
    case TlvE{} TlvE{}:
      True{}
    case _ _:
      False{}

type Ie is Data:
  Ie{iei: U32, fmt: Fmt, len: U32, body: B.Bytes()}

def Ie.iei(ie: Ie) -> U32:
  match ie:
    case Ie{iei, fmt, len, body}:
      iei

def Ie.body(ie: Ie) -> B.Bytes():
  match ie:
    case Ie{iei, fmt, len, body}:
      body

def Ie.valid_body(fmt: Fmt, iei: U32, len: U32, body: B.Bytes()) -> Bool:
  match fmt:
    case T1{}:
      Bool.and(U32.is_ge(iei, 128), Bool.and(List.is_empty(&2, U32, body), U32.is_eq(len, 0)))
    case Tv{n}:
      Bool.and(U32.is_lt(iei, 128), Bool.and(Nat.is_eq(List.length(&2, U32, body), n), U32.is_eq(len, 0)))
    case Tlv{}:
      Bool.and(U32.is_lt(iei, 128), LenBody.valid8(LenBody{len, body}))
    case TlvE{}:
      Bool.and(U32.is_lt(iei, 128), LenBody.valid16(LenBody{len, body}))

# Valid against the format the message type assigns to the IEI.
def Ie.valid(expected: Fmt, ie: Ie) -> Bool:
  match ie:
    case Ie{+iei, +fmt, +len, +body}:
      Bool.and(Fmt.eq(fmt, expected), Bool.and(fits8(iei), Ie.valid_body(fmt, iei, len, body)))

def Ie.write(ie: Ie, rest: B.Bytes()) -> B.Bytes():
  match ie:
    case Ie{iei, fmt, len, body}:
      match fmt:
        case T1{}:
          B.write_u8(iei, rest)
        case Tv{n}:
          B.write_u8(iei, List.append(&2, U32, body, rest))
        case Tlv{}:
          B.write_u8(iei, B.write_u8(len, List.append(&2, U32, body, rest)))
        case TlvE{}:
          B.write_u8(iei, B.write_u16(len, List.append(&2, U32, body, rest)))

def Ies.write(ies: List<&2, Ie>, rest: B.Bytes()) -> B.Bytes():
  match ies:
    case Nil{}:
      rest
    case ie <> more:
      Ie.write(ie, Ies.write(more, rest))

def Ie.of_tv(iei: U32, n: Nat, r: B.Read(B.Bytes())) -> B.Read(Ie):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(body, rest)}:
      Done{(Ie{iei, Tv{n}, 0, body}, rest)}

def Ie.of_len(iei: U32, fmt: Fmt, r: B.Read(LenBody)) -> B.Read(Ie):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(LenBody{len, body}, rest)}:
      Done{(Ie{iei, fmt, len, body}, rest)}

# The rest of an IE after its IEI byte, in the format the message assigns it.
def Ie.read_body(iei: U32, fmt: Fmt, bs: B.Bytes()) -> B.Read(Ie):
  match fmt:
    case T1{}:
      Done{(Ie{iei, T1{}, 0, []}, bs)}
    case Tv{+n}:
      Ie.of_tv(iei, n, B.take(n, bs))
    case Tlv{}:
      Ie.of_len(iei, Tlv{}, lv(bs))
    case TlvE{}:
      Ie.of_len(iei, TlvE{}, lve(bs))

# Which format an IEI below 0x80 has in a given message, by exception from TLV.
type Rule is Data:
  Rule{iei: U32, low: Low}

def Table.pick(l: Low, more: Unit -> Low, hit: Bool) -> Low:
  match hit:
    case True{}:
      l
    case False{}:
      more(Unit{})

def Table.low(rules: List<&2, Rule>, +iei: U32) -> Low:
  match rules:
    case Nil{}:
      LowTlv{}
    case Rule{k, l} <> more:
      Table.pick(l, u => Table.low(more, iei), U32.is_eq(iei, k))

def Fmt.pick(l: Low, one_octet: Bool) -> Fmt:
  match one_octet:
    case True{}:
      T1{}
    case False{}:
      Fmt.of_low(l)

# The format of an optional IE (TS 24.007 §11.2.4): IEIs from 0x80 are one
# octet; the others are TLV unless the message's table says TV or TLV-E.
def Opts.format(table: List<&2, Rule>, +iei: U32) -> Fmt:
  Fmt.pick(Table.low(table, iei), U32.is_ge(iei, 128))

def Opts.valid(+table: List<&2, Rule>, ies: List<&2, Ie>) -> Bool:
  match ies:
    case Nil{}:
      True{}
    case +ie <> more:
      Bool.and(Ie.valid(Opts.format(table, Ie.iei(ie)), ie), Opts.valid(table, more))

# Optional IEs to the end of the message. The fuel is the byte count: every
# IE takes at least one byte.
def Opts.cons(ie: Ie, r: Result<&2, &2, B.Err, List<&2, Ie>>) -> Result<&2, &2, B.Err, List<&2, Ie>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ies}:
      Done{ie <> ies}

def Opts.next(r: B.Read(Ie), more: B.Bytes() -> Result<&2, &2, B.Err, List<&2, Ie>>) -> Result<&2, &2, B.Err, List<&2, Ie>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(ie, rest)}:
      Opts.cons(ie, more(rest))

def Opts.iei(table: List<&2, Rule>, +iei: U32, rest: B.Bytes(), more: B.Bytes() -> Result<&2, &2, B.Err, List<&2, Ie>>, ok: Bool) -> Result<&2, &2, B.Err, List<&2, Ie>>:
  match ok:
    case True{}:
      Opts.next(Ie.read_body(iei, Opts.format(table, iei), rest), more)
    case False{}:
      Fail{B.Invalid{iei}}

def Opts.read(fuel: Nat, +table: List<&2, Rule>, bs: B.Bytes()) -> Result<&2, &2, B.Err, List<&2, Ie>>:
  match fuel bs:
    case _ Nil{}:
      Done{[]}
    case 0n b <> rest:
      Fail{B.Invalid{b}}
    case 1n+f +iei <> rest:
      Opts.iei(table, iei, rest, left => Opts.read(f, table, left), fits8(iei))
