import Base
import ../bytes.bend as B
import ./lib/check.bend as C

# PFCP Heartbeat Request from test-vectors/capture (message 2):
# 20 01 000c 000002 00 | 0060 0004 ee92035e
def heartbeat() -> B.Bytes():
  [32, 1, 0, 12, 0, 0, 2, 0, 0, 96, 0, 4, 238, 146, 3, 94]

def recovery() -> B.Bytes():
  [238, 146, 3, 94]

def from(n: Nat) -> B.Bytes():
  List.drop(&2, U32, heartbeat(), n)

def u32_is(r: B.Read(U32), v: U32, rest: B.Bytes()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(x, rs)}:
      Bool.and(U32.is_eq(x, v), C.Check.bytes_eq(rs, rest))

def bytes_is(r: B.Read(B.Bytes()), v: B.Bytes(), rest: B.Bytes()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(x, rs)}:
      Bool.and(C.Check.bytes_eq(x, v), C.Check.bytes_eq(rs, rest))

def nibbles_is(r: B.Read(B.Nibbles()), hi: U32, lo: U32, rest: B.Bytes()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{((h, l), rs)}:
      Bool.and(Bool.and(U32.is_eq(h, hi), U32.is_eq(l, lo)), C.Check.bytes_eq(rs, rest))

def short_u32(r: B.Read(U32)) -> Bool:
  match r:
    case Fail{B.Short{}}:
      True{}
    case _:
      False{}

def digits_is(r: Result<&2, &2, B.Err, B.Digits()>, v: B.Digits()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      C.Check.bytes_eq(x, v)

def fails_digits(r: Result<&2, &2, B.Err, B.Digits()>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{v}:
      False{}

def main() -> IO(Unit):
  do IO<Unit>:
    C.Check.report("u8 reads the flags byte", u32_is(B.u8(heartbeat()), 32, from(1n)))
    C.Check.report("u16 reads the length", u32_is(B.u16(from(2n)), 12, from(4n)))
    C.Check.report("u24 reads the sequence", u32_is(B.u24(from(4n)), 2, from(7n)))
    C.Check.report("u32 reads the recovery time stamp", u32_is(B.u32(recovery()), 4002546526, []))
    C.Check.report("u16 on one byte is Short", short_u32(B.u16([1])))
    C.Check.report("u32 on three bytes is Short", short_u32(B.u32([1, 2, 3])))
    C.Check.report("write_u16 big-endian", C.Check.bytes_eq(B.write_u16(12, [7]), [0, 12, 7]))
    C.Check.report("write_u24 big-endian", C.Check.bytes_eq(B.write_u24(2, []), [0, 0, 2]))
    C.Check.report("write_u32 big-endian", C.Check.bytes_eq(B.write_u32(4002546526, []), recovery()))
    C.Check.report("write_u8 masks to one byte", C.Check.bytes_eq(B.write_u8(300, []), [44]))
    C.Check.report("take exactly n", bytes_is(B.take(4n, from(12n)), recovery(), []))
    C.Check.report("take too many is Short", Bool.not(bytes_is(B.take(5n, recovery()), recovery(), [])))
    C.Check.report("nibbles of PLMN 00 f1 10", Bool.and(Bool.and(nibbles_is(B.nibbles([0, 241, 16]), 0, 0, [241, 16]), nibbles_is(B.nibbles([241, 16]), 15, 1, [16])), nibbles_is(B.nibbles([16]), 1, 0, [])))
    C.Check.report("write_nibbles packs hi then lo", C.Check.bytes_eq(B.write_nibbles(15, 1, []), [241]))
    C.Check.report("tbcd decodes the MSIN 0000000001", digits_is(B.Tbcd.decode([0, 0, 0, 0, 16]), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]))
    C.Check.report("tbcd encodes the MSIN", C.Check.bytes_eq(B.write_tbcd([0, 0, 0, 0, 0, 0, 0, 0, 0, 1], []), [0, 0, 0, 0, 16]))
    C.Check.report("tbcd odd count gets a filler", C.Check.bytes_eq(B.write_tbcd([0, 0, 1], [9]), [0, 241, 9]))
    C.Check.report("tbcd decodes an odd count", digits_is(B.Tbcd.decode([0, 241]), [0, 0, 1]))
    C.Check.report("tbcd rejects a non-digit", fails_digits(B.Tbcd.decode([250])))
    C.Check.report("tbcd rejects a filler before the end", fails_digits(B.Tbcd.decode([240, 18])))
