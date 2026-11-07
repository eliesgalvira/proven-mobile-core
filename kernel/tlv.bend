import Base
import ./bytes.bend as B

# TLVs: a 16-bit kind, a 16-bit length and the body it counts, bytes in and
# bytes out. PFCP information elements (TS 29.244 §8.1.1) and the Config TLVs
# of the frame protocol share it. A TLV keeps its kind, its length word and
# its body as read; `make` fills the length word.

type Tlv is Data:
  Tlv{kind: U32, len: U32, body: B.Bytes()}

def Tlv.kind(t: Tlv) -> U32:
  match t:
    case Tlv{kind, len, body}:
      kind

def Tlv.len(t: Tlv) -> U32:
  match t:
    case Tlv{kind, len, body}:
      len

def Tlv.body(t: Tlv) -> B.Bytes():
  match t:
    case Tlv{kind, len, body}:
      body

def Tlv.valid(t: Tlv) -> Bool:
  match t:
    case Tlv{+kind, +len, body}:
      Bool.and(B.fits16(kind), Bool.and(B.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body))))

type Hdr is Data:
  Hdr{kind: U32, len: U32}

def Tlv.hdr_len(kind: U32, r: B.Read(U32)) -> B.Read(Hdr):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(len, rest)}:
      Done{(Hdr{kind, len}, rest)}

def Tlv.hdr_type(r: B.Read(U32)) -> B.Read(Hdr):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(kind, rest)}:
      Tlv.hdr_len(kind, B.u16(rest))

# The four header octets: type, then length.
def Tlv.header(bs: B.Bytes()) -> B.Read(Hdr):
  Tlv.hdr_type(B.u16(bs))

def Tlv.of_body(kind: U32, len: U32, r: B.Read(B.Bytes())) -> B.Read(Tlv):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(body, rest)}:
      Done{(Tlv{kind, len, body}, rest)}

def Tlv.checked(kind: U32, +len: U32, rest: B.Bytes(), ok: Bool) -> B.Read(Tlv):
  match ok:
    case True{}:
      Tlv.of_body(kind, len, B.take(U32.to_nat(len), rest))
    case False{}:
      Fail{B.Invalid{len}}

def Tlv.of_hdr(h: Hdr, rest: B.Bytes()) -> B.Read(Tlv):
  match h:
    case Hdr{+kind, +len}:
      Tlv.checked(kind, len, rest, Bool.and(B.fits16(kind), B.fits16(len)))

def Tlv.of_header(r: B.Read(Hdr)) -> B.Read(Tlv):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(h, rest)}:
      Tlv.of_hdr(h, rest)

def Tlv.read(bs: B.Bytes()) -> B.Read(Tlv):
  Tlv.of_header(Tlv.header(bs))

def Tlv.write(t: Tlv, rest: B.Bytes()) -> B.Bytes():
  match t:
    case Tlv{kind, len, body}:
      B.write_u16(kind, B.write_u16(len, List.append(&2, U32, body, rest)))

# An TLV over a body, with the length word it needs.
def Tlv.make(kind: U32, +body: B.Bytes()) -> Tlv:
  Tlv{kind, U32.from_nat(List.length(&2, U32, body)), body}

def Tlvs.valid(tl: List<&2, Tlv>) -> Bool:
  match tl:
    case Nil{}:
      True{}
    case t <> more:
      Bool.and(Tlv.valid(t), Tlvs.valid(more))

def Tlvs.next(r: B.Read(Tlv), more: B.Bytes() -> Result<&2, &2, B.Err, List<&2, Tlv>>) -> Result<&2, &2, B.Err, List<&2, Tlv>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(t, rest)}:
      B.Res.cons(Tlv, t, more(rest))

# Every TLV up to the end of the bytes; each takes at least four, so the byte count is fuel enough.
def Tlvs.read(fuel: Nat, bs: B.Bytes()) -> Result<&2, &2, B.Err, List<&2, Tlv>>:
  match fuel bs:
    case _ Nil{}:
      Done{[]}
    case 0n b <> rest:
      Fail{B.Invalid{b}}
    case 1n+f b <> rest:
      Tlvs.next(Tlv.read(b <> rest), left => Tlvs.read(f, left))

def Tlvs.decode(+bs: B.Bytes()) -> Result<&2, &2, B.Err, List<&2, Tlv>>:
  Tlvs.read(List.length(&2, U32, bs), bs)

def Tlvs.write(tl: List<&2, Tlv>, rest: B.Bytes()) -> B.Bytes():
  match tl:
    case Nil{}:
      rest
    case t <> more:
      Tlv.write(t, Tlvs.write(more, rest))

def Tlvs.size(tl: List<&2, Tlv>) -> Nat:
  match tl:
    case Nil{}:
      0n
    case t <> more:
      Nat.add(4n, Nat.add(List.length(&2, U32, Tlv.body(t)), Tlvs.size(more)))

def Tlvs.pick(t: Tlv, more: Maybe<&2, Tlv>, hit: Bool) -> Maybe<&2, Tlv>:
  match hit:
    case True{}:
      Some{t}
    case False{}:
      more

# The first TLV of a type.
def Tlvs.find(+kind: U32, tl: List<&2, Tlv>) -> Maybe<&2, Tlv>:
  match tl:
    case Nil{}:
      None{}
    case +t <> more:
      Tlvs.pick(t, Tlvs.find(kind, more), U32.is_eq(Tlv.kind(t), kind))
