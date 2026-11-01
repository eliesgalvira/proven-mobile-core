import Base
import ./bytes.bend as B

# Range conditions are stated as mask equations: `U32.and(255, v) == v` is "v fits in 8 bits".

# bytes (ticket 02)
# -----------------

law bytes.u8.roundtrip:
  for v: U32
  for rest: B.Bytes()
  for e: {U32.and(255, v) == v : U32}
  {B.u8(B.write_u8(v, rest)) == Done{(v, rest)} : B.Read(U32)}

law bytes.u16.roundtrip:
  for v: U32
  for rest: B.Bytes()
  for e: {U32.and(65535, v) == v : U32}
  {B.u16(B.write_u16(v, rest)) == Done{(v, rest)} : B.Read(U32)}

law bytes.u24.roundtrip:
  for v: U32
  for rest: B.Bytes()
  for e: {U32.and(16777215, v) == v : U32}
  {B.u24(B.write_u24(v, rest)) == Done{(v, rest)} : B.Read(U32)}

law bytes.u32.roundtrip:
  for v: U32
  for rest: B.Bytes()
  {B.u32(B.write_u32(v, rest)) == Done{(v, rest)} : B.Read(U32)}

law bytes.nibbles.roundtrip:
  for hi: U32
  for lo: U32
  for rest: B.Bytes()
  for eh: {U32.and(15, hi) == hi : U32}
  for el: {U32.and(15, lo) == lo : U32}
  {B.nibbles(B.write_nibbles(hi, lo, rest)) == Done{((hi, lo), rest)} : B.Read(B.Nibbles())}

law bytes.take.length:
  for +n: Nat
  for +bs: B.Bytes()
  for taken: B.Bytes()
  for rest: B.Bytes()
  for +e: {B.take(n, bs) == Done{(taken, rest)} : B.Read(B.Bytes())}
  {List.length(&2, U32, taken) == n : Nat} & {List.append(&2, U32, taken, rest) == bs : B.Bytes()}

# Every reader on an input shorter than its width answers Fail{B.Short{}}.
law bytes.short_input_fails:
  for +bs: B.Bytes()
  ({Nat.is_lt(List.length(&2, U32, bs), 1n) == True{} : Bool} -> {B.u8(bs) == Fail{B.Short{}} : B.Read(U32)})
  & ({Nat.is_lt(List.length(&2, U32, bs), 2n) == True{} : Bool} -> {B.u16(bs) == Fail{B.Short{}} : B.Read(U32)})
  & ({Nat.is_lt(List.length(&2, U32, bs), 3n) == True{} : Bool} -> {B.u24(bs) == Fail{B.Short{}} : B.Read(U32)})
  & ({Nat.is_lt(List.length(&2, U32, bs), 4n) == True{} : Bool} -> {B.u32(bs) == Fail{B.Short{}} : B.Read(U32)})
  & ({Nat.is_lt(List.length(&2, U32, bs), 1n) == True{} : Bool} -> {B.nibbles(bs) == Fail{B.Short{}} : B.Read(B.Nibbles())})
  & (@n: Nat -> {Nat.is_lt(List.length(&2, U32, bs), n) == True{} : Bool} -> {B.take(n, bs) == Fail{B.Short{}} : B.Read(B.Bytes())})
  & (@n: Nat -> {Nat.is_lt(List.length(&2, U32, bs), n) == True{} : Bool} -> {B.tbcd_digits(bs, n) == Fail{B.Short{}} : B.Read(B.Digits())})

# Advisory GHSA-vp44-3q85-5cm4: decoding k bytes yields at most 2k digits, each 0..9;
# encoding d digits yields ceil(d/2) bytes.
law bytes.tbcd.length:
  for +bs: B.Bytes()
  for +k: Nat
  for +digits: B.Digits()
  for rest: B.Bytes()
  for e: {B.tbcd_digits(bs, k) == Done{(digits, rest)} : B.Read(B.Digits())}
  {Nat.is_le(List.length(&2, U32, digits), Nat.double(k)) == True{} : Bool}
  & {B.Tbcd.all_digits(digits) == True{} : Bool}
  & (@ds: B.Digits() -> @out: B.Bytes() -> {List.length(&2, U32, B.write_tbcd(ds, out))
      == Nat.add(B.Tbcd.byte_count(List.length(&2, U32, ds)), List.length(&2, U32, out)) : Nat})
