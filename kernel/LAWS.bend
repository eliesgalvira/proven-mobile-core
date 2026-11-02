import Base
import ./bytes.bend as B
import ./crypto/sha256.bend as S
import ./crypto/hmac.bend as H
import ./crypto/aes.bend as A
import ./crypto/ctr.bend as Ctr
import ./crypto/cmac.bend as M
import ./crypto/milenage.bend as Mil
import ./crypto/kdf.bend as K
import ./plmn.bend as P
import ./crypto/x25519.bend as X
import ./suci.bend as Su
import ./nas/security.bend as N
import ./nas/ie.bend as I
import ./nas/mm.bend as Mm
import ./nas/mobile_id.bend as Mi
import ./nas/sm.bend as Sm
import ./nas/sm_ies.bend as Q
import ./aper.bend as Ap

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

# PLMN identity (ticket 08)
# -------------------------

law plmn.roundtrip:
  for +p: P.Plmn
  for rest: B.Bytes()
  for +v: {P.Plmn.valid(p) == True{} : Bool}
  {P.Plmn.read(P.Plmn.write(p, rest)) == Done{(p, rest)} : B.Read(P.Plmn)}

law plmn.decode_valid:
  for +bs: B.Bytes()
  for +p: P.Plmn
  for +rest: B.Bytes()
  for e: {P.Plmn.read(bs) == Done{(p, rest)} : B.Read(P.Plmn)}
  {P.Plmn.valid(p) == True{} : Bool}

law plmn.suffix:
  for +bs: B.Bytes()
  for +p: P.Plmn
  for +rest: B.Bytes()
  for e: {P.Plmn.read(bs) == Done{(p, rest)} : B.Read(P.Plmn)}
  {List.drop(&2, U32, bs, 3n) == rest : B.Bytes()}

# X25519 and SUCI (ticket 08)
# ---------------------------

law x25519.length:
  for k: B.Bytes()
  for +u: B.Bytes()
  {List.length(&2, U32, X.x25519(k, u)) == 32n : Nat}

# Advisory GHSA-vp5f-rg8g-8p7j: a Profile A scheme output is accepted only when
# it holds the ephemeral key, at least one ciphertext byte and the 8-byte MAC;
# the received MAC is compared with the expected one over all 8 bytes; and a
# mismatch answers Fail, never a SUPI.
law suci.deconceal.length_checked:
  for +key: B.Bytes()
  for +output: B.Bytes()
  for msin: B.Digits()
  (({Nat.is_lt(List.length(&2, U32, output), 41n) == True{} : Bool} -> {Su.Suci.deconceal_a(key, output) == Fail{B.Short{}} : Result<&2, &2, B.Err, B.Digits()>})
  & (({Su.Suci.deconceal_a(key, output) == Done{msin} : Result<&2, &2, B.Err, B.Digits()>} ->
      {Su.Suci.tag(key, output) == Su.Suci.mac(output) : B.Bytes()} & {List.length(&2, U32, Su.Suci.tag(key, output)) == 8n : Nat})
  & ({B.bytes_eq(Su.Suci.tag(key, output), Su.Suci.mac(output)) == False{} : Bool} -> {Result.is_fail(&2, &2, B.Err, B.Digits(), Su.Suci.deconceal_a(key, output)) == True{} : Bool})))

law suci.null_scheme.roundtrip:
  for +plmn: P.Plmn
  for +routing: B.Digits()
  for +msin: B.Digits()
  for +v: {P.Plmn.valid(plmn) == True{} : Bool}
  for +r: {Su.Routing.valid(routing) == True{} : Bool}
  for +m: {B.Tbcd.all_digits(msin) == True{} : Bool}
  {Su.Suci.read(Su.Suci.write(Su.Suci.null(plmn, routing, msin))) == Done{Su.Suci.null(plmn, routing, msin)} : Result<&2, &2, B.Err, Su.Suci>}
  & {Su.Suci.null_msin(B.write_tbcd(msin, [])) == Done{msin} : Result<&2, &2, B.Err, B.Digits()>}

# NAS security (ticket 09)
# ------------------------

# Integrity verification compares all 4 MAC bytes, and a message shorter than
# its header plus MAC answers Fail.
law nas_sec.mac_full_length:
  for +keys: N.Nas.Keys
  for +dir: U32
  for +count: N.Nas.Count
  for +msg: B.Bytes()
  for +o: N.Nas.Opened
  ({Nat.is_lt(List.length(&2, U32, msg), 7n) == True{} : Bool} -> {N.Nas.open(keys, dir, count, msg) == Fail{B.Short{}} : Result<&2, &2, B.Err, N.Nas.Opened>})
  & ({N.Nas.open(keys, dir, count, msg) == Done{o} : Result<&2, &2, B.Err, N.Nas.Opened>} ->
     {N.Nas.received_mac(msg) == N.Nas.mac(N.Nas.Keys.ia(keys), N.Nas.Keys.k_int(keys), N.Nas.Count.value(count), N.Nas.Keys.bearer(keys), dir, List.drop(&2, U32, msg, 6n)) : B.Bytes()}
     & {List.length(&2, U32, N.Nas.received_mac(msg)) == 4n : Nat})

# unprotect(protect(m)) = m, for NEA0 and NEA2 with NIA2 and every header type.
law nas_sec.roundtrip:
  for +keys: N.Nas.Keys
  for +prot: N.Nas.Protection
  for +dir: U32
  for +count: N.Nas.Count
  for +plain: B.Bytes()
  {N.Nas.open(keys, dir, count, N.Nas.seal(keys, prot, dir, count, plain)) == Done{N.Opened{prot, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}

# Accepting an uplink message moves the stored uplink COUNT forward, and a
# message repeating the last accepted sequence number is never accepted.
law nas_sec.count_monotonic:
  for +ctx: N.Nas.Ctx
  for +msg: B.Bytes()
  for +u: N.Nas.Unprotected
  for +last: N.Nas.Count
  for +e: {N.Nas.unprotect(ctx, msg) == Done{u} : Result<&2, &2, B.Err, N.Nas.Unprotected>}
  for +s: {N.Nas.Ctx.ul(ctx) == Some{last} : Maybe<&2, N.Nas.Count>}
  {N.Nas.Count.advanced(last, N.Nas.Unprotected.count(u)) == True{} : Bool}
  & {U32.is_eq(N.Nas.Count.sqn(last), N.Nas.Count.sqn(N.Nas.Unprotected.count(u))) == False{} : Bool}

# NAS 5GMM codec (ticket 10)
# --------------------------

law nas.mm.roundtrip:
  for +m: Mm.Mm
  for +v: {Mm.Mm.valid(m) == True{} : Bool}
  {Mm.Mm.read(Mm.Mm.write(m)) == Done{m} : Result<&2, &2, B.Err, Mm.Mm>}

law nas.mm.decode_valid:
  for +bs: B.Bytes()
  for +m: Mm.Mm
  for +e: {Mm.Mm.read(bs) == Done{m} : Result<&2, &2, B.Err, Mm.Mm>}
  {Mm.Mm.valid(m) == True{} : Bool}

# The bytes a decoded message came from are exactly its encoding.
law nas.mm.suffix:
  for +bs: B.Bytes()
  for +m: Mm.Mm
  for +e: {Mm.Mm.read(bs) == Done{m} : Result<&2, &2, B.Err, Mm.Mm>}
  for +ab: {B.all_bytes(bs) == True{} : Bool}
  {Mm.Mm.write(m) == bs : B.Bytes()}

# GHSA-f4mx-3x6p-cfwp: a 5GS mobile identity is read only inside its content,
# a decoded identity is exactly the content's encoding, and it has the digits,
# PLMN and field widths its type requires.
law nas.mobile_identity.suffix:
  for +bs: B.Bytes()
  for +id: Mi.MobileId
  for +e: {Mi.MobileId.read(bs) == Done{id} : Result<&2, &2, B.Err, Mi.MobileId>}
  for +ab: {B.all_bytes(bs) == True{} : Bool}
  {Mi.MobileId.write(id) == bs : B.Bytes()}

law nas.mobile_identity.decode_valid:
  for +bs: B.Bytes()
  for +id: Mi.MobileId
  for +e: {Mi.MobileId.read(bs) == Done{id} : Result<&2, &2, B.Err, Mi.MobileId>}
  {Mi.MobileId.valid(id) == True{} : Bool}

# A 5G-GUTI is eleven bytes of content.
law nas.mobile_identity.guti_length:
  for +bs: B.Bytes()
  for +plmn: P.Plmn
  for +region: U32
  for +amf: U32
  for +tmsi: U32
  for +e: {Mi.MobileId.read(bs) == Done{Mi.Guti{plmn, region, amf, tmsi}} : Result<&2, &2, B.Err, Mi.MobileId>}
  for +ab: {B.all_bytes(bs) == True{} : Bool}
  {List.length(&2, U32, bs) == 11n : Nat}

# GHSA-hcjf-j847-3gx8: an IMEISV has exactly sixteen decimal digits (the
# decoder ties the odd/even flag to the count, so the count is fixed).
law nas.imeisv.decode_valid:
  for +bs: B.Bytes()
  for +ds: B.Digits()
  for +e: {Mi.MobileId.read(bs) == Done{Mi.Imeisv{ds}} : Result<&2, &2, B.Err, Mi.MobileId>}
  {List.length(&2, U32, ds) == 16n : Nat} & {B.Tbcd.all_digits(ds) == True{} : Bool}

# GHSA-9643-6pmq-j7g2: the payload container is the LV-E field of the
# transport messages. Fewer bytes than its two-byte length declares is Short,
# and a decoded container is exactly the declared slice.
law nas.payload_container.short:
  for +b1: U32
  for +b0: U32
  for +tail: B.Bytes()
  for +e1: {U32.is_lt(b1, 256) == True{} : Bool}
  for +e0: {U32.is_lt(b0, 256) == True{} : Bool}
  for +short: {Nat.is_lt(List.length(&2, U32, tail), U32.to_nat(B.cat8(b0, b1))) == True{} : Bool}
  {I.lve(b1 <> b0 <> tail) == Fail{B.Short{}} : B.Read(I.LenBody)}

law nas.payload_container.suffix:
  for +bs: B.Bytes()
  for +len: U32
  for +body: B.Bytes()
  for +rest: B.Bytes()
  for +e: {I.lve(bs) == Done{(I.LenBody{len, body}, rest)} : B.Read(I.LenBody)}
  {List.length(&2, U32, body) == U32.to_nat(len) : Nat} & {List.drop(&2, U32, bs, 2n) == List.append(&2, U32, body, rest) : B.Bytes()}

law nas.sm.roundtrip:
  for +m: Sm.Sm
  for +v: {Sm.Sm.valid(m) == True{} : Bool}
  {Sm.Sm.read(Sm.Sm.write(m)) == Done{m} : Result<&2, &2, B.Err, Sm.Sm>}

law nas.sm.decode_valid:
  for +bs: B.Bytes()
  for +m: Sm.Sm
  for +e: {Sm.Sm.read(bs) == Done{m} : Result<&2, &2, B.Err, Sm.Sm>}
  {Sm.Sm.valid(m) == True{} : Bool}

law nas.sm.suffix:
  for +bs: B.Bytes()
  for +m: Sm.Sm
  for +e: {Sm.Sm.read(bs) == Done{m} : Result<&2, &2, B.Err, Sm.Sm>}
  for +ab: {B.all_bytes(bs) == True{} : Bool}
  {Sm.Sm.write(m) == bs : B.Bytes()}

# GHSA-6w6j-vjx3-pwqr: QoS rules and their packet filters are read only inside
# their declared lengths, which their contents must fill exactly; the bytes a
# decoded list came from are its encoding.
law nas.qos_rules.suffix:
  for +bs: B.Bytes()
  for +rs: List<&2, Q.Rule>
  for +e: {Q.Rules.read(bs) == Done{rs} : Result<&2, &2, B.Err, List<&2, Q.Rule>>}
  for +ab: {B.all_bytes(bs) == True{} : Bool}
  {Q.Rules.write(rs) == bs : B.Bytes()}

# GHSA-g4xp-3ccr-264w: an IPv4 address component decodes only with a mask
# that is a contiguous run of ones from the top bit.
law nas.packet_filter.mask_contiguous:
  for +bs: B.Bytes()
  for +kind: U32
  for +addr: U32
  for +mask: U32
  for +rest: B.Bytes()
  for +e: {Q.Comp.read(bs) == Done{(Q.Comp{kind, Q.PIpv4{addr, mask}}, rest)} : B.Read(Q.Comp)}
  {Q.Mask.contiguous(mask) == True{} : Bool}

# GHSA-m795-gjf7-c8ch: Session-AMBR content is exactly six bytes and both
# units are defined values.
law nas.session_ambr.decode_valid:
  for +bs: B.Bytes()
  for +a: Q.Ambr
  for +e: {Q.Ambr.read(bs) == Done{a} : Result<&2, &2, B.Err, Q.Ambr>}
  {List.length(&2, U32, bs) == 6n : Nat} & {Q.Ambr.valid(a) == True{} : Bool}

# GHSA-fvg8-6r68-v3x7: a decoded ePCO holds at most 255 containers, each with
# the length its byte declares, and its size is what the bytes held.
law nas.epco.decode_bounded:
  for +bs: B.Bytes()
  for +e: Q.Epco
  for +d: {Q.Epco.read(bs) == Done{e} : Result<&2, &2, B.Err, Q.Epco>}
  {Nat.is_le(List.length(&2, Q.Container, Q.Epco.containers(e)), 255n) == True{} : Bool} & ({Q.Epco.valid(e) == True{} : Bool} & {Q.Epco.size(e) == List.length(&2, U32, bs) : Nat})

# GHSA-796x-8w26-2xfp: a valid ePCO encodes to at most 65535 bytes and reads
# back as itself, so no container is ever cut.
law nas.epco.encode_bounded:
  for +e: Q.Epco
  for +v: {Q.Epco.valid(e) == True{} : Bool}
  {Nat.is_le(List.length(&2, U32, Q.Epco.write(e)), 65535n) == True{} : Bool} & {Q.Epco.read(Q.Epco.write(e)) == Done{e} : Result<&2, &2, B.Err, Q.Epco>}

# aper (ticket 12)
# ----------------
# A value written at `rem` reads back with the `rem` its `after` gives, and
# what a reader accepts satisfies the value's validity predicate.

law aper.bit.roundtrip:
  for b: Bool
  for +rem: Nat
  for +rest: Ap.Bits()
  {Ap.Bit.read(Ap.Cur{rem, Ap.Bit.write(b, rem, rest)}) == Done{(b, Ap.Cur{Ap.Bit.after(rem), rest})} : Ap.Rd(Bool)}

law aper.bits.roundtrip:
  for +bs: Ap.Bits()
  for +rem: Nat
  for +rest: Ap.Bits()
  {Ap.Bits.read(List.length(&2, Bool, bs), Ap.Cur{rem, Ap.Bits.write(bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.Bits.after(List.length(&2, Bool, bs), rem), rest})} : Ap.Rd(Ap.Bits())}

law aper.align.roundtrip:
  for +rem: Nat
  for +rest: Ap.Bits()
  {Ap.Align.read(Ap.Cur{rem, Ap.Align.write(rem, rest)}) == Done{(Unit{}, Ap.Cur{0n, rest})} : Ap.Rd(Unit)}

# §11.1.4: alignment accepts nothing but the zero padding the writer makes.
law aper.padding_zero:
  for +rem: Nat
  for +bits: Ap.Bits()
  for +r2: Nat
  for +rest: Ap.Bits()
  for +e: {Ap.Align.read(Ap.Cur{rem, bits}) == Done{(Unit{}, Ap.Cur{r2, rest})} : Ap.Rd(Unit)}
  {bits == Ap.Align.write(rem, rest) : Ap.Bits()}

law aper.int.roundtrip:
  for +n: Nat
  for +diff: U32
  for +x: U32
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.Int.valid(n, diff, x) == True{} : Bool}
  {Ap.Int.read(n, diff, Ap.Cur{rem, Ap.Int.write(n, x, rem, rest)}) == Done{(x, Ap.Cur{Ap.Int.after(n, rem), rest})} : Ap.Rd(U32)}

law aper.int.decode_valid:
  for +n: Nat
  for +diff: U32
  for +c: Ap.Cur
  for +x: U32
  for +c2: Ap.Cur
  for +e: {Ap.Int.read(n, diff, c) == Done{(x, c2)} : Ap.Rd(U32)}
  {Ap.Int.valid(n, diff, x) == True{} : Bool}

law aper.aint.roundtrip:
  for +n: Nat
  for +diff: U32
  for +x: U32
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.Int.valid(n, diff, x) == True{} : Bool}
  {Ap.AInt.read(n, diff, Ap.Cur{rem, Ap.AInt.write(n, x, rem, rest)}) == Done{(x, Ap.Cur{Ap.AInt.after(n, rem), rest})} : Ap.Rd(U32)}

law aper.aint.decode_valid:
  for +n: Nat
  for +diff: U32
  for +c: Ap.Cur
  for +x: U32
  for +c2: Ap.Cur
  for +e: {Ap.AInt.read(n, diff, c) == Done{(x, c2)} : Ap.Rd(U32)}
  {Ap.Int.valid(n, diff, x) == True{} : Bool}

# The octet count is an n-bit constrained length whose range (diff) fits n bits.
law aper.big.roundtrip:
  for +n: Nat
  for +diff: Nat
  for +bs: B.Bytes()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.Big.valid(diff, bs) == True{} : Bool}
  for +w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}
  {Ap.Big.read(n, diff, Ap.Cur{rem, Ap.Big.write(n, bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.Big.after(rem), rest})} : Ap.Rd(B.Bytes())}

law aper.big.decode_valid:
  for +n: Nat
  for +diff: Nat
  for +c: Ap.Cur
  for +bs: B.Bytes()
  for +c2: Ap.Cur
  for +e: {Ap.Big.read(n, diff, c) == Done{(bs, c2)} : Ap.Rd(B.Bytes())}
  {Ap.Big.valid(diff, bs) == True{} : Bool}

law aper.small.roundtrip:
  for +v: U32
  for +rem: Nat
  for +rest: Ap.Bits()
  for +ok: {Ap.Small.valid(v) == True{} : Bool}
  {Ap.Small.read(Ap.Cur{rem, Ap.Small.write(v, rem, rest)}) == Done{(v, Ap.Cur{Ap.Small.after(rem), rest})} : Ap.Rd(U32)}

law aper.small.decode_valid:
  for +c: Ap.Cur
  for +v: U32
  for +c2: Ap.Cur
  for +e: {Ap.Small.read(c) == Done{(v, c2)} : Ap.Rd(U32)}
  {Ap.Small.valid(v) == True{} : Bool}

law aper.len.roundtrip:
  for +n: Nat
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.Len.valid(n) == True{} : Bool}
  {Ap.Len.read(Ap.Cur{rem, Ap.Len.write(n, rem, rest)}) == Done{(n, Ap.Cur{Ap.Len.after(rem), rest})} : Ap.Rd(Nat)}

# No decoder builds a large Nat: the length determinant, the one count whose
# bound is not a parameter, stays below 16384 (fragments are refused), and
# every constrained count stays within its bound (aper.size.decode_valid).
law aper.no_big_nat:
  for +c: Ap.Cur
  for +n: Nat
  for +c2: Ap.Cur
  for +e: {Ap.Len.read(c) == Done{(n, c2)} : Ap.Rd(Nat)}
  {Nat.is_lt(n, 16384n) == True{} : Bool}

law aper.size.roundtrip:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +k: Nat
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.Size.valid(lo, diff, k) == True{} : Bool}
  for +w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}
  {Ap.Size.read(al, n, lo, diff, Ap.Cur{rem, Ap.Size.write(al, n, lo, k, rem, rest)}) == Done{(k, Ap.Cur{Ap.Size.after(al, n, rem), rest})} : Ap.Rd(Nat)}

law aper.size.decode_valid:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +c: Ap.Cur
  for +k: Nat
  for +c2: Ap.Cur
  for +e: {Ap.Size.read(al, n, lo, diff, c) == Done{(k, c2)} : Ap.Rd(Nat)}
  {Ap.Size.valid(lo, diff, k) == True{} : Bool}

law aper.octets.roundtrip:
  for +bs: B.Bytes()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +ab: {B.all_bytes(bs) == True{} : Bool}
  {Ap.Octets.read(List.length(&2, U32, bs), Ap.Cur{rem, Ap.Octets.write(bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.Octets.after(rem), rest})} : Ap.Rd(B.Bytes())}

law aper.octets.decode_valid:
  for +n: Nat
  for +c: Ap.Cur
  for +bs: B.Bytes()
  for +c2: Ap.Cur
  for +e: {Ap.Octets.read(n, c) == Done{(bs, c2)} : Ap.Rd(B.Bytes())}
  {B.all_bytes(bs) == True{} : Bool}

law aper.pack.roundtrip:
  for +bs: B.Bytes()
  for +ab: {B.all_bytes(bs) == True{} : Bool}
  {Ap.pack(Ap.unpack(bs)) == bs : B.Bytes()}

law aper.aoctets.roundtrip:
  for +bs: B.Bytes()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +ab: {B.all_bytes(bs) == True{} : Bool}
  {Ap.AOctets.read(List.length(&2, U32, bs), Ap.Cur{rem, Ap.AOctets.write(bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.AOctets.after(rem), rest})} : Ap.Rd(B.Bytes())}

law aper.abits.roundtrip:
  for +bs: Ap.Bits()
  for +rem: Nat
  for +rest: Ap.Bits()
  {Ap.ABits.read(List.length(&2, Bool, bs), Ap.Cur{rem, Ap.ABits.write(bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.ABits.after(List.length(&2, Bool, bs), rem), rest})} : Ap.Rd(Ap.Bits())}

law aper.octstr.roundtrip:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +bs: B.Bytes()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.OctStr.valid(lo, diff, bs) == True{} : Bool}
  for +w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}
  {Ap.OctStr.read(al, n, lo, diff, Ap.Cur{rem, Ap.OctStr.write(al, n, lo, bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.OctStr.after(rem), rest})} : Ap.Rd(B.Bytes())}

law aper.octstr.decode_valid:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +c: Ap.Cur
  for +bs: B.Bytes()
  for +c2: Ap.Cur
  for +e: {Ap.OctStr.read(al, n, lo, diff, c) == Done{(bs, c2)} : Ap.Rd(B.Bytes())}
  {Ap.OctStr.valid(lo, diff, bs) == True{} : Bool}

law aper.bitstr.roundtrip:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +bs: Ap.Bits()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.BitStr.valid(lo, diff, bs) == True{} : Bool}
  for +w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}
  {Ap.BitStr.read(al, n, lo, diff, Ap.Cur{rem, Ap.BitStr.write(al, n, lo, bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.BitStr.after(bs, rem), rest})} : Ap.Rd(Ap.Bits())}

law aper.bitstr.decode_valid:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +c: Ap.Cur
  for +bs: Ap.Bits()
  for +c2: Ap.Cur
  for +e: {Ap.BitStr.read(al, n, lo, diff, c) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}
  {Ap.BitStr.valid(lo, diff, bs) == True{} : Bool}

law aper.ubitstr.roundtrip:
  for +bs: Ap.Bits()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.UBitStr.valid(bs) == True{} : Bool}
  {Ap.UBitStr.read(Ap.Cur{rem, Ap.UBitStr.write(bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.UBitStr.after(bs, rem), rest})} : Ap.Rd(Ap.Bits())}

law aper.ubitstr.decode_valid:
  for +c: Ap.Cur
  for +bs: Ap.Bits()
  for +c2: Ap.Cur
  for +e: {Ap.UBitStr.read(c) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}
  {Ap.UBitStr.valid(bs) == True{} : Bool}

law aper.open.roundtrip:
  for +bs: B.Bytes()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.Open.valid(bs) == True{} : Bool}
  {Ap.Open.read(Ap.Cur{rem, Ap.Open.write(bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.Open.after(rem), rest})} : Ap.Rd(B.Bytes())}

law aper.open.decode_valid:
  for +c: Ap.Cur
  for +bs: B.Bytes()
  for +c2: Ap.Cur
  for +e: {Ap.Open.read(c) == Done{(bs, c2)} : Ap.Rd(B.Bytes())}
  {Ap.Open.valid(bs) == True{} : Bool}

# §11.2: the octets an open type yields are exactly the ones its length
# determinant declared, and the stream continues right after them.
law aper.open_type.exact:
  for +c: Ap.Cur
  for +body: B.Bytes()
  for +r2: Nat
  for +rest: Ap.Bits()
  for +e: {Ap.Open.read(c) == Done{(body, Ap.Cur{r2, rest})} : Ap.Rd(B.Bytes())}
  {Ap.Len.read(c) == Done{(List.length(&2, U32, body), Ap.Cur{0n, Ap.Octets.write(body, 0n, rest)})} : Ap.Rd(Nat)}

law aper.str.roundtrip:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +s: B.Bytes()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.Str.valid(lo, diff, s) == True{} : Bool}
  for +w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}
  {Ap.Str.read(al, n, lo, diff, Ap.Cur{rem, Ap.Str.write(al, n, lo, s, rem, rest)}) == Done{(s, Ap.Cur{Ap.Str.after(rem), rest})} : Ap.Rd(B.Bytes())}

law aper.str.decode_valid:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +c: Ap.Cur
  for +s: B.Bytes()
  for +c2: Ap.Cur
  for +e: {Ap.Str.read(al, n, lo, diff, c) == Done{(s, c2)} : Ap.Rd(B.Bytes())}
  {Ap.Str.valid(lo, diff, s) == True{} : Bool}

law aper.ustr.roundtrip:
  for +s: B.Bytes()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.UStr.valid(s) == True{} : Bool}
  {Ap.UStr.read(Ap.Cur{rem, Ap.UStr.write(s, rem, rest)}) == Done{(s, Ap.Cur{Ap.UStr.after(rem), rest})} : Ap.Rd(B.Bytes())}

law aper.ustr.decode_valid:
  for +c: Ap.Cur
  for +s: B.Bytes()
  for +c2: Ap.Cur
  for +e: {Ap.UStr.read(c) == Done{(s, c2)} : Ap.Rd(B.Bytes())}
  {Ap.UStr.valid(s) == True{} : Bool}

law aper.enum.roundtrip:
  for +n: Nat
  for +diff: U32
  for +ext: Bool
  for +e: Ap.Enum
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.Enum.valid(n, diff, ext, e) == True{} : Bool}
  {Ap.Enum.read(n, diff, ext, Ap.Cur{rem, Ap.Enum.write(n, ext, e, rem, rest)}) == Done{(e, Ap.Cur{Ap.Enum.after(n, ext, e, rem), rest})} : Ap.Rd(Ap.Enum)}

law aper.enum.decode_valid:
  for +n: Nat
  for +diff: U32
  for +ext: Bool
  for +c: Ap.Cur
  for +e: Ap.Enum
  for +c2: Ap.Cur
  for +d: {Ap.Enum.read(n, diff, ext, c) == Done{(e, c2)} : Ap.Rd(Ap.Enum)}
  {Ap.Enum.valid(n, diff, ext, e) == True{} : Bool}

# Extensible values: the extension bit picks the root or the unconstrained
# form, and a value that fits the root is only accepted in the root form.

law aper.xint.roundtrip:
  for +n: Nat
  for +diff: U32
  for +x: Ap.XInt
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.XInt.valid(n, diff, x) == True{} : Bool}
  {Ap.XInt.read(n, diff, Ap.Cur{rem, Ap.XInt.write(n, x, rem, rest)}) == Done{(x, Ap.Cur{Ap.XInt.after(n, x, rem), rest})} : Ap.Rd(Ap.XInt)}

law aper.xint.decode_valid:
  for +n: Nat
  for +diff: U32
  for +c: Ap.Cur
  for +x: Ap.XInt
  for +c2: Ap.Cur
  for +e: {Ap.XInt.read(n, diff, c) == Done{(x, c2)} : Ap.Rd(Ap.XInt)}
  {Ap.XInt.valid(n, diff, x) == True{} : Bool}

law aper.xbig.roundtrip:
  for +n: Nat
  for +diff: Nat
  for +x: Ap.XBig
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.XBig.valid(diff, x) == True{} : Bool}
  for +w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}
  {Ap.XBig.read(n, diff, Ap.Cur{rem, Ap.XBig.write(n, x, rem, rest)}) == Done{(x, Ap.Cur{Ap.XBig.after(x, rem), rest})} : Ap.Rd(Ap.XBig)}

law aper.xbig.decode_valid:
  for +n: Nat
  for +diff: Nat
  for +c: Ap.Cur
  for +x: Ap.XBig
  for +c2: Ap.Cur
  for +e: {Ap.XBig.read(n, diff, c) == Done{(x, c2)} : Ap.Rd(Ap.XBig)}
  {Ap.XBig.valid(diff, x) == True{} : Bool}

law aper.xbits.roundtrip:
  for +n: Nat
  for +bs: Ap.Bits()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.XBits.valid(n, bs) == True{} : Bool}
  {Ap.XBits.read(n, Ap.Cur{rem, Ap.XBits.write(n, bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.XBits.after(n, bs, rem), rest})} : Ap.Rd(Ap.Bits())}

law aper.xbits.decode_valid:
  for +n: Nat
  for +c: Ap.Cur
  for +bs: Ap.Bits()
  for +c2: Ap.Cur
  for +e: {Ap.XBits.read(n, c) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}
  {Ap.XBits.valid(n, bs) == True{} : Bool}

law aper.xbitstr.roundtrip:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +bs: Ap.Bits()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.XBitStr.valid(lo, diff, bs) == True{} : Bool}
  for +w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}
  {Ap.XBitStr.read(al, n, lo, diff, Ap.Cur{rem, Ap.XBitStr.write(al, n, lo, diff, bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.XBitStr.after(bs, rem), rest})} : Ap.Rd(Ap.Bits())}

law aper.xbitstr.decode_valid:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +c: Ap.Cur
  for +bs: Ap.Bits()
  for +c2: Ap.Cur
  for +e: {Ap.XBitStr.read(al, n, lo, diff, c) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}
  {Ap.XBitStr.valid(lo, diff, bs) == True{} : Bool}

law aper.xstr.roundtrip:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +s: B.Bytes()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.XStr.valid(lo, diff, s) == True{} : Bool}
  for +w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}
  {Ap.XStr.read(al, n, lo, diff, Ap.Cur{rem, Ap.XStr.write(al, n, lo, diff, s, rem, rest)}) == Done{(s, Ap.Cur{Ap.XStr.after(rem), rest})} : Ap.Rd(B.Bytes())}

law aper.xstr.decode_valid:
  for +al: Bool
  for +n: Nat
  for +lo: Nat
  for +diff: Nat
  for +c: Ap.Cur
  for +s: B.Bytes()
  for +c2: Ap.Cur
  for +e: {Ap.XStr.read(al, n, lo, diff, c) == Done{(s, c2)} : Ap.Rd(B.Bytes())}
  {Ap.XStr.valid(lo, diff, s) == True{} : Bool}
