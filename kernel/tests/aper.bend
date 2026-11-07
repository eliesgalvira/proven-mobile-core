import Base
import ../bytes.bend as B
import ../aper.bend as A
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture

# X.691 primitives on hand-made vectors, then the protocol IE walk over every
# captured NGAP PDU: PDU header, IE ids and criticalities in order, every open
# type cut at its declared length, nothing left over, every padding bit zero.

def bits(bs: List<&2, U32>) -> A.Cur:
  A.Cur{0n, A.unpack(bs)}

def at(rem: Nat, bs: List<&2, Bool>) -> A.Cur:
  A.Cur{rem, bs}

def bits_eq(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yt:
      False{}
    case x <> xt Nil{}:
      False{}
    case x <> xt y <> yt:
      Bool.and(Bool.not(Bool.xor(x, y)), bits_eq(xt, yt))

def ends(+rem: Nat, +rest: List<&2, Bool>, c: A.Cur) -> Bool:
  match c:
    case A.Cur{r, bs}:
      Bool.and(Nat.is_eq(r, rem), bits_eq(bs, rest))

def u32_is(+v: U32, +rem: Nat, +rest: List<&2, Bool>, r: A.Rd(U32)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(x, c)}:
      Bool.and(U32.is_eq(x, v), ends(rem, rest, c))

def nat_is(+v: Nat, +rem: Nat, +rest: List<&2, Bool>, r: A.Rd(Nat)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(x, c)}:
      Bool.and(Nat.is_eq(x, v), ends(rem, rest, c))

def bytes_is(+v: List<&2, U32>, +rem: Nat, +rest: List<&2, Bool>, r: A.Rd(List<&2, U32>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(x, c)}:
      Bool.and(B.bytes_eq(x, v), ends(rem, rest, c))

def bits_is(+v: List<&2, Bool>, +rem: Nat, +rest: List<&2, Bool>, r: A.Rd(List<&2, Bool>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(x, c)}:
      Bool.and(bits_eq(x, v), ends(rem, rest, c))

def fails_u32(r: A.Rd(U32)) -> Bool:
  Result.is_fail(&2, &2, B.Err, Sigma<&2, &2, U32, _ => A.Cur>, r)

def fails_nat(r: A.Rd(Nat)) -> Bool:
  Result.is_fail(&2, &2, B.Err, Sigma<&2, &2, Nat, _ => A.Cur>, r)

def fails_bytes(r: A.Rd(List<&2, U32>)) -> Bool:
  Result.is_fail(&2, &2, B.Err, Sigma<&2, &2, List<&2, U32>, _ => A.Cur>, r)

def fails_unit(r: A.Rd(Unit)) -> Bool:
  Result.is_fail(&2, &2, B.Err, Sigma<&2, &2, Unit, _ => A.Cur>, r)

def fails_enum(r: A.Rd(A.Enum)) -> Bool:
  Result.is_fail(&2, &2, B.Err, Sigma<&2, &2, A.Enum, _ => A.Cur>, r)

def enum_eq(e: A.Enum, x: A.Enum) -> Bool:
  match e x:
    case A.Root{i} A.Root{j}:
      U32.is_eq(i, j)
    case A.Ext{i} A.Ext{j}:
      U32.is_eq(i, j)
    case _ _:
      False{}

def enum_is(+e: A.Enum, +rem: Nat, +rest: List<&2, Bool>, r: A.Rd(A.Enum)) -> Bool:
  match r:
    case Fail{err}:
      False{}
    case Done{(x, c)}:
      Bool.and(enum_eq(e, x), ends(rem, rest, c))

# A ten-bit tail that follows a value in several tests.
def tail() -> List<&2, Bool>:
  [True{}, False{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}, True{}]

def primitives() -> IO(Unit):
  do IO<Unit>:
    C.Check.report("3-bit constrained number 5 of 0..6", u32_is(5, 5n, tail(), A.Int.read(3n, 6, at(0n, A.Int.write(3n, 5, 0n, tail())))))
    C.Check.report("a bit-field value above its range is Invalid", fails_u32(A.Int.read(3n, 4, at(0n, A.Int.write(3n, 5, 0n, tail())))))
    C.Check.report("aligned octet 21 after three bits", u32_is(21, 0n, tail(), A.AInt.read(8n, 255, at(5n, A.AInt.write(8n, 21, 5n, tail())))))
    C.Check.report("aligned octet writes five zero bits then 0x15", bits_eq(A.AInt.write(8n, 21, 5n, []), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, True{}]))
    C.Check.report("two aligned octets 0x1234", u32_is(4660, 0n, [], A.AInt.read(16n, 65535, bits([18, 52]))))
    C.Check.report("non-zero padding is Invalid", fails_unit(A.Align.read(at(3n, [False{}, True{}, False{}, True{}]))))
    C.Check.report("zero padding aligns", ends(0n, [True{}], A.Cur{0n, [True{}]}))
    C.Check.report("length 5 is one octet", nat_is(5n, 0n, [], A.Len.read(bits([5]))))
    C.Check.report("length 258 is 0x81 0x02", nat_is(258n, 0n, [], A.Len.read(bits([129, 2]))))
    C.Check.report("length 5 written back", B.bytes_eq(A.pack(A.Len.write(5n, 0n, [])), [5]))
    C.Check.report("length 258 written back", B.bytes_eq(A.pack(A.Len.write(258n, 0n, [])), [129, 2]))
    C.Check.report("length 16383 is the largest", nat_is(16383n, 0n, [], A.Len.read(bits([191, 255]))))
    C.Check.report("a fragmented length is Unsupported", fails_nat(A.Len.read(bits([193, 0, 0]))))
    C.Check.report("a two-octet length below 128 is Invalid", fails_nat(A.Len.read(bits([128, 5]))))
    C.Check.report("the length aligns first", nat_is(5n, 0n, [], A.Len.read(at(3n, A.Len.write(5n, 3n, [])))))
    C.Check.report("small number 5", u32_is(5, 1n, tail(), A.Small.read(at(0n, A.Small.write(5, 0n, tail())))))
    C.Check.report("a small number of 64 or more is Unsupported", fails_u32(A.Small.read(at(0n, [True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}]))))
    C.Check.report("AMF-UE-NGAP-ID 1 is one octet after a 3-bit count", bytes_is([1], 0n, [], A.Big.read(3n, 4n, bits([0, 1]))))
    C.Check.report("AMF-UE-NGAP-ID 1 written back", B.bytes_eq(A.pack(A.Big.write(3n, [1], 0n, [])), [0, 1]))
    C.Check.report("a 40-bit value takes five octets", bytes_is([255, 1, 2, 3, 4], 0n, [], A.Big.read(3n, 4n, bits([128, 255, 1, 2, 3, 4]))))
    C.Check.report("a leading zero octet is not canonical", fails_bytes(A.Big.read(3n, 4n, bits([32, 0, 1]))))
    C.Check.report("six octets exceed AMF-UE-NGAP-ID", fails_bytes(A.Big.read(3n, 4n, bits([160, 1, 2, 3, 4, 5, 6]))))
    C.Check.report("a 16-bit size of 4 is aligned", nat_is(4n, 0n, [], A.Size.read(True{}, 16n, 0n, 65535n, at(7n, A.Size.write(True{}, 16n, 0n, 4n, 7n, [])))))
    C.Check.report("a size above its bound is Invalid", fails_nat(A.Size.read(False{}, 4n, 22n, 10n, at(0n, [True{}, True{}, False{}, False{}]))))
    C.Check.report("a size writes its offset", bits_eq(A.Size.write(False{}, 4n, 22n, 32n, 0n, []), [True{}, False{}, True{}, False{}]))
    C.Check.report("bytes pack and unpack", B.bytes_eq(A.pack(A.unpack([0, 1, 127, 128, 255])), [0, 1, 127, 128, 255]))
    C.Check.report("two unaligned octets", bytes_is([171, 205], 3n, tail(), A.Octets.read(2n, at(3n, A.Octets.write([171, 205], 3n, tail())))))
    C.Check.report("too few bits for an octet is Short", fails_bytes(A.Octets.read(2n, at(0n, A.unpack([171])))))
    C.Check.report("an open type cuts its octets", bytes_is([1, 2, 3], 0n, A.unpack([9]), A.Open.read(bits([3, 1, 2, 3, 9]))))
    C.Check.report("an open type short of its length is Short", fails_bytes(A.Open.read(bits([4, 1, 2, 3]))))
    C.Check.report("an open type written back", B.bytes_eq(A.pack(A.Open.write([1, 2, 3], 0n, [])), [3, 1, 2, 3]))
    C.Check.report("a variable bit string aligns its bits", bits_is(A.unpack([10, 33, 0, 30]), 0n, [], A.BitStr.read(False{}, 8n, 1n, 159n, at(5n, A.BitStr.write(False{}, 8n, 1n, A.unpack([10, 33, 0, 30]), 5n, [])))))
    C.Check.report("an unconstrained bit string", bits_is([True{}, False{}, True{}], 5n, [], A.UBitStr.read(at(2n, A.UBitStr.write([True{}, False{}, True{}], 2n, [])))))
    C.Check.report("a printable string", bytes_is([65, 66, 45, 49], 0n, [], A.Str.read(False{}, 8n, 1n, 149n, at(1n, A.Str.write(False{}, 8n, 1n, [65, 66, 45, 49], 1n, [])))))
    C.Check.report("a control character is not printable", fails_bytes(A.Str.read(False{}, 8n, 1n, 149n, at(1n, A.Str.write(False{}, 8n, 1n, [65, 7], 1n, [])))))
    C.Check.report("criticality ignore is 01", enum_is(A.Root{1}, 6n, tail(), A.Enum.read(2n, 2, False{}, at(0n, A.Enum.write(2n, False{}, A.Root{1}, 0n, tail())))))
    C.Check.report("an extensible enum root value", enum_is(A.Root{4}, 4n, tail(), A.Enum.read(3n, 4, True{}, at(0n, A.Enum.write(3n, True{}, A.Root{4}, 0n, tail())))))
    C.Check.report("an extensible enum extension value", enum_is(A.Ext{2}, 0n, tail(), A.Enum.read(2n, 4, True{}, at(0n, A.Enum.write(2n, True{}, A.Ext{2}, 0n, tail())))))
    C.Check.report("an enum index above the root is Invalid", fails_enum(A.Enum.read(2n, 2, False{}, at(0n, [True{}, True{}]))))

# GlobalRANNodeID of the captured NGSetupRequest: choice globalGNB-ID, PLMN
# 001/01, gNB-ID as a 32-bit string holding 1.
def gnb_id.bits(r: A.Rd(List<&2, Bool>)) -> Bool:
  bits_is(A.unpack([0, 0, 0, 1]), 0n, [], r)

def gnb_id.choice(r: A.Rd(Bool)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(ext, c)}:
      Bool.and(Bool.not(ext), gnb_id.bits(A.BitStr.read(False{}, 4n, 22n, 10n, c)))

def gnb_id.plmn(r: A.Rd(List<&2, U32>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(plmn, c)}:
      Bool.and(B.bytes_eq(plmn, [0, 241, 16]), gnb_id.choice(A.Bit.read(c)))

def gnb_id.flags(r: A.Rd(List<&2, Bool>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(flags, c)}:
      Bool.and(bits_eq(flags, [False{}, False{}]), gnb_id.plmn(A.AOctets.read(3n, c)))

def gnb_id.index(r: A.Rd(U32)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(i, c)}:
      Bool.and(U32.is_eq(i, 0), gnb_id.flags(A.Bits.read(2n, c)))

def gnb_id(r: A.Rd(Bool)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(ext, c)}:
      Bool.and(Bool.not(ext), gnb_id.index(A.Int.read(2n, 2, c)))

# The gNB's GTP tunnel in the captured PDU session resource setup response
# transfer: a 32-bit transport layer address then a four-octet TEID.
def tunnel.teid(r: A.Rd(List<&2, U32>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(teid, c)}:
      B.bytes_eq(teid, [0, 0, 0, 1])

def tunnel.address(r: A.Rd(List<&2, Bool>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(addr, c)}:
      Bool.and(B.bytes_eq(A.pack(addr), [10, 33, 0, 30]), tunnel.teid(A.AOctets.read(4n, c)))

def tunnel.flags(r: A.Rd(List<&2, Bool>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(flags, c)}:
      tunnel.address(A.BitStr.read(False{}, 8n, 1n, 159n, c))

def tunnel() -> Bool:
  tunnel.flags(A.Bits.read(11n, bits([0, 3, 224, 10, 33, 0, 30, 0, 0, 0, 1, 0, 1])))

# The protocol IE walk.
def crit_code(s: String) -> U32:
  match s:
    case "reject":
      0
    case "ignore":
      1
    case "notify":
      2
    case _:
      255

def pdu_code(s: String) -> U32:
  match s:
    case "initiatingMessage":
      0
    case "successfulOutcome":
      1
    case "unsuccessfulOutcome":
      2
    case _:
      255

def when(ok: Bool, next: Maybe<&2, A.Cur>) -> Maybe<&2, A.Cur>:
  match ok:
    case True{}:
      next
    case False{}:
      None{}

def ie.value(r: A.Rd(List<&2, U32>)) -> Maybe<&2, A.Cur>:
  match r:
    case Fail{e}:
      None{}
    case Done{(value, c)}:
      Some{c}

def ie.crit(+ie: V.Vec, r: A.Rd(U32)) -> Maybe<&2, A.Cur>:
  match r:
    case Fail{e}:
      None{}
    case Done{(crit, c)}:
      when(U32.is_eq(crit, crit_code(V.Vec.text(V.Vec.field(ie, "criticality")))), ie.value(A.Open.read(c)))

def ie.id(+ie: V.Vec, r: A.Rd(U32)) -> Maybe<&2, A.Cur>:
  match r:
    case Fail{e}:
      None{}
    case Done{(id, c)}:
      when(U32.is_eq(id, U32.from_nat(V.Vec.nat(V.Vec.field(ie, "id")))), ie.crit(ie, A.Int.read(2n, 2, c)))

def ies(expected: List<&2, V.Vec>, m: Maybe<&2, A.Cur>) -> Bool:
  match expected m:
    case Nil{} None{}:
      False{}
    case Nil{} Some{c}:
      ends(0n, [], c)
    case ie <> more None{}:
      False{}
    case ie <> more Some{c}:
      ies(more, ie.id(ie, A.AInt.read(16n, 65535, c)))

def body.count(+expected: List<&2, V.Vec>, r: A.Rd(Nat)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(n, c)}:
      Bool.and(Nat.is_eq(n, List.length(&2, V.Vec, expected)), ies(expected, Some{c}))

def body.ext(expected: List<&2, V.Vec>, r: A.Rd(Bool)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(ext, c)}:
      Bool.and(Bool.not(ext), body.count(expected, A.Size.read(True{}, 16n, 0n, 65535n, c)))

def body(expected: List<&2, V.Vec>, bs: List<&2, U32>) -> Bool:
  body.ext(expected, A.Bit.read(bits(bs)))

def pdu.body(expected: List<&2, V.Vec>, r: A.Rd(List<&2, U32>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(value, c)}:
      Bool.and(ends(0n, [], c), body(expected, value))

def pdu.crit(+m: V.Vec, r: A.Rd(U32)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(crit, c)}:
      Bool.and(U32.is_eq(crit, crit_code(V.Vec.text(V.Vec.field(m, "criticality")))), pdu.body(V.Vec.items(V.Vec.field(m, "ies")), A.Open.read(c)))

def pdu.code(+m: V.Vec, r: A.Rd(U32)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(code, c)}:
      Bool.and(U32.is_eq(code, U32.from_nat(V.Vec.nat(V.Vec.field(m, "procedure_code")))), pdu.crit(m, A.Int.read(2n, 2, c)))

def pdu.kind(+m: V.Vec, r: A.Rd(U32)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(kind, c)}:
      Bool.and(U32.is_eq(kind, pdu_code(V.Vec.text(V.Vec.field(m, "pdu")))), pdu.code(m, A.AInt.read(8n, 255, c)))

def pdu(+m: V.Vec, r: A.Rd(Bool)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(ext, c)}:
      Bool.and(Bool.not(ext), pdu.kind(m, A.Int.read(2n, 2, c)))

def one(+m: V.Vec, protocol: String) -> IO(Unit):
  match protocol:
    case "NGAP":
      C.Check.report(V.Vec.text(V.Vec.field(m, "message")) ++ ": header, IE ids and criticalities walk to the end", pdu(m, A.Bit.read(bits(V.Vec.bytes(V.Vec.field(m, "hex"))))))
    case _:
      IO.pure(Unit, Unit{})

def run(msgs: List<&2, V.Vec>) -> IO(Unit):
  match msgs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +m <> rest:
      do IO<Unit>:
        one(m, V.Vec.text(V.Vec.field(m, "protocol")))
        run(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    primitives()
    C.Check.report("the captured GlobalRANNodeID is gNB 1 of PLMN 001/01", gnb_id(A.Bit.read(bits([0, 0, 241, 16, 80, 0, 0, 0, 1]))))
    C.Check.report("the captured gNB tunnel is 10.33.0.30 TEID 1", tunnel())
    run(V.Vec.items(V.Vec.field(Capture.data(), "messages")))
