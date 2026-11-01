import Base
import ./bytes.bend as B
import ./crypto/sha256.bend as S
import ./crypto/hmac.bend as H
import ./crypto/aes.bend as A
import ./crypto/ctr.bend as Ctr
import ./crypto/cmac.bend as M
import ./crypto/milenage.bend as Mil
import ./crypto/kdf.bend as K

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

# crypto: SHA-256 and HMAC (ticket 04)
# ------------------------------------
# Correctness against FIPS 180-4 and RFC 4231 is established by the test vectors.

law sha256.length:
  for msg: B.Bytes()
  {List.length(&2, U32, S.sha256(msg)) == 32n : Nat}

law hmac.length:
  for key: B.Bytes()
  for msg: B.Bytes()
  {List.length(&2, U32, H.hmac(key, msg)) == 32n : Nat}

# crypto: AES-128, CTR and CMAC (ticket 05)
# -----------------------------------------
# Correctness against FIPS 197, SP 800-38A and RFC 4493 is established by the test vectors.

law aes.block_length:
  for key: B.Bytes()
  for block: B.Bytes()
  {List.length(&2, U32, A.aes128(key, block)) == 16n : Nat}

law ctr.length:
  for +key: B.Bytes()
  for +iv: B.Bytes()
  for +m: B.Bytes()
  {List.length(&2, U32, Ctr.ctr(key, iv, m)) == List.length(&2, U32, m) : Nat}

law ctr.involution:
  for +key: B.Bytes()
  for +iv: B.Bytes()
  for +m: B.Bytes()
  {Ctr.ctr(key, iv, Ctr.ctr(key, iv, m)) == m : B.Bytes()}

law cmac.length:
  for +key: B.Bytes()
  for msg: B.Bytes()
  {List.length(&2, U32, M.cmac(key, msg)) == 16n : Nat}

# crypto: MILENAGE (ticket 06)
# ---------------------------
# Correctness against TS 35.208 is established by the test vectors.

law milenage.lengths:
  for +key: B.Bytes()
  for +opc: B.Bytes()
  for +rand: B.Bytes()
  for +sqn: B.Bytes()
  for +amf: B.Bytes()
  {List.length(&2, U32, Mil.milenage.f1(key, opc, rand, sqn, amf)) == 8n : Nat}
  & ({List.length(&2, U32, Mil.milenage.f1_star(key, opc, rand, sqn, amf)) == 8n : Nat}
  & ({List.length(&2, U32, Mil.milenage.f2(key, opc, rand)) == 8n : Nat}
  & ({List.length(&2, U32, Mil.milenage.f3(key, opc, rand)) == 16n : Nat}
  & ({List.length(&2, U32, Mil.milenage.f4(key, opc, rand)) == 16n : Nat}
  & ({List.length(&2, U32, Mil.milenage.f5(key, opc, rand)) == 6n : Nat}
  & {List.length(&2, U32, Mil.milenage.f5_star(key, opc, rand)) == 6n : Nat})))))

# crypto: 5G key derivation (ticket 07)
# -------------------------------------

law kdf.length:
  for +key: B.Bytes()
  for +fc: U32
  for +ps: List<&2, B.Bytes()>
  for +ck: B.Bytes()
  for +ik: B.Bytes()
  for +snn: B.Bytes()
  for +sqn_xor_ak: B.Bytes()
  for +rand: B.Bytes()
  for +res: B.Bytes()
  for +res_star: B.Bytes()
  for +k_ausf: B.Bytes()
  for +k_seaf: B.Bytes()
  for +supi: B.Bytes()
  for +abba: B.Bytes()
  for +k_amf: B.Bytes()
  for +alg: U32
  for +count: U32
  {List.length(&2, U32, K.kdf(key, fc, ps)) == 32n : Nat}
  & ({List.length(&2, U32, K.kdf.k_ausf(ck, ik, snn, sqn_xor_ak)) == 32n : Nat}
  & ({List.length(&2, U32, K.kdf.res_star(ck, ik, snn, rand, res)) == 16n : Nat}
  & ({List.length(&2, U32, K.kdf.hres_star(rand, res_star)) == 16n : Nat}
  & ({List.length(&2, U32, K.kdf.k_seaf(k_ausf, snn)) == 32n : Nat}
  & ({List.length(&2, U32, K.kdf.k_amf(k_seaf, supi, abba)) == 32n : Nat}
  & ({List.length(&2, U32, K.kdf.k_nas_enc(k_amf, alg)) == 16n : Nat}
  & ({List.length(&2, U32, K.kdf.k_nas_int(k_amf, alg)) == 16n : Nat}
  & {List.length(&2, U32, K.kdf.k_gnb(k_amf, count)) == 32n : Nat})))))))

# Advisory GHSA-f9c2-535p-3mwc: the serving network name is never empty.
law kdf.snn.nonempty:
  for mcc: B.Digits()
  for mnc: B.Digits()
  {List.is_empty(&2, U32, K.kdf.serving_network_name(mcc, mnc)) == False{} : Bool}
