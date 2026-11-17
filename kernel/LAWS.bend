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
import ./ngap/frame.bend as Fr
import ./ngap/gen/types.bend as G
import ./ngap/gen/views.bend as GV
import ./pfcp.bend as Pf
import ./tlv.bend as T
import ./frame.bend as F
import ./table.bend as Tb
import ./state.bend as St
import ./step.bend as Ke
import ./amf/ngap.bend as Ng
import ./amf/gmm.bend as Gm
import ./smf/gsm.bend as Gs
import ./ausf.bend as Au
import ./smf/n4.bend as Up
import ./smf/switch.bend as Sw
import ./amf/path_switch.bend as Ps
import ./amf/handover.bend as Ho

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

# Advisory GHSA-vp44-3q85-5cm4: the TBCD decoder of MSIN, IMEI and IMEISV
# yields at most 2k digits from k bytes, each 0..9; encoding d digits yields
# ceil(d/2) bytes.
law bytes.tbcd.length:
  for +bs: B.Bytes()
  for +digits: B.Digits()
  for e: {B.Tbcd.decode(bs) == Done{digits} : Result<&2, &2, B.Err, B.Digits()>}
  {Nat.is_le(List.length(&2, U32, digits), Nat.double(List.length(&2, U32, bs))) == True{} : Bool}
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

# NH and NCC (ticket 26)
# ----------------------

law kdf.nh.length:
  for +k_amf: B.Bytes()
  for +sync: B.Bytes()
  {List.length(&2, U32, K.kdf.nh(k_amf, sync)) == 32n : Nat}

# TS 33.501 §6.9.2.1.1: a new {NH, NCC} pair chains NH from the stored NH
# under the same KAMF, and NCC is the stored NCC plus 1 modulo 8. The stored
# pair at initial setup is the first step from KgNB, a virtual NH with NCC 0.
# A UE keeps only its latest pair and `St.Nh.next` takes no NH of its own, so
# a derivation from an older NH can't be represented.
law amf.ncc.chain:
  for +k_amf: B.Bytes()
  for +nh: B.Bytes()
  for +ncc: U32
  for +k_gnb: B.Bytes()
  {St.Nh.next(St.Nh{k_amf, nh, ncc}) == St.Nh{k_amf, K.kdf.nh(k_amf, nh), U32.mod(U32.add(ncc, 1), 8)} : St.Nh}
  & {St.Nh.initial(k_amf, k_gnb) == St.Nh{k_amf, K.kdf.nh(k_amf, k_gnb), 1} : St.Nh}

# TS 33.501 §6.9.2.1.1: a UE's {NH, NCC} pair moves only along its chain.
# After any step, a context that held a pair holds it or the next one
# (Handover Required, Path Switch), and one that held none was in Security
# Mode and holds Nh.initial of the K_AMF it derived there and of a KgNB the
# same step sends it in Initial Context Setup (Security Mode Complete;
# amf.ncc.chain gives its NCC, 1). So the stored pair never goes back, skips
# one or starts again. It holds where the contexts are unique
# (amf.indexes.unique).
law amf.ncc.step:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +k: U32
  for +m: St.Nh
  for +k_amf: B.Bytes()
  for +nh: B.Bytes()
  for +ncc: U32
  for +eu: {St.Ues.unique(St.State.ues(st)) == True{} : Bool}
  for +en: {St.Ue.nh(Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy))))) == Some{St.Nh{k_amf, nh, ncc}} : Maybe<&2, St.Nh>}
  ({St.Ue.nh(Tb.Table.get(St.Ue, k, St.State.ues(st))) == Some{m} : Maybe<&2, St.Nh>} -> {St.Nh{k_amf, nh, ncc} == m : St.Nh} | {St.Nh{k_amf, nh, ncc} == St.Nh.next(m) : St.Nh})
  & ({St.Ue.nh(Tb.Table.get(St.Ue, k, St.State.ues(st))) == None{} : Maybe<&2, St.Nh>} -> {St.Ue.mode_k_amf(Tb.Table.get(St.Ue, k, St.State.ues(st))) == Some{k_amf} : Maybe<&2, B.Bytes()>} & {Ng.Acts.seeds(k_amf, k, St.Nh{k_amf, nh, ncc}, Ke.Kernel.actions(Ke.Kernel.step(st, ev, entropy))) == True{} : Bool})

# Advisory GHSA-f9c2-535p-3mwc: the serving network name the AUSF derives keys
# with, built from the configured PLMN, is never empty: every configuration the
# kernel holds is valid (kernel.config.valid).
law kdf.snn.nonempty:
  for +cfg: St.Cfg
  for +e: {St.Cfg.valid(cfg) == True{} : Bool}
  {List.is_empty(&2, U32, Au.Ausf.snn(St.Cfg.plmn(cfg))) == False{} : Bool}

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

# TS 24.501 §4.4.3.1, TS 33.501 §6.4.3: a 5G NAS security context keeps one
# downlink NAS COUNT, which the AMF increases by one after each new or
# retransmitted security protected message, so no two downlink messages under
# the same keys share a COUNT. NEA1, NEA2 and NEA3 draw the keystream from the
# keys and the COUNT: two messages under one COUNT give away the XOR of their
# plaintexts, and the UE drops the second as a replay. Over any step, the
# security protected NAS messages the actions carry to the UE keyed k (in DL
# NAS Transport, Initial Context Setup, PDU Session Resource Setup or Release)
# are each sealed under the COUNT after the one before (Ng.Fresh.run). Where
# k's phase held a NAS context before the step (St.Phase.nas, in force or
# kept through an N2 handover), they go under its keys, the first at its
# downlink COUNT, and a context k holds after has those very keys; only where
# k held none do they start at 0, under a context taken into use by Security
# Mode (TS 24.501 §5.4.2), so keys that seal alike cannot start a held
# context's COUNT again. If k holds a context after the step, its downlink
# COUNT is the one after the last of them: unchanged when there is none, so
# the next step starts where this one ends, and no COUNT is used twice under
# k's keys. If it holds none, they are still sealed in turn from where k's
# context left off, under its keys; where k held none either, under one
# context's keys from 0. It holds where no two contexts share a key
# (amf.indexes.unique).
law nas_sec.downlink_fresh:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +k: U32
  for +eu: {St.Ues.unique(St.State.ues(st)) == True{} : Bool}
  Ng.Fresh.Law(St.Ue.nas(Tb.Table.get(St.Ue, k, St.State.ues(st))), St.Ue.nas(Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy))))), Ng.Acts.nas(k, Ke.Kernel.actions(Ke.Kernel.step(st, ev, entropy))))

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

law aper.wbitstr.roundtrip:
  for +lo: Nat
  for +diff: Nat
  for +bs: Ap.Bits()
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.WBitStr.valid(lo, diff, bs) == True{} : Bool}
  {Ap.WBitStr.read(lo, diff, Ap.Cur{rem, Ap.UBitStr.write(bs, rem, rest)}) == Done{(bs, Ap.Cur{Ap.UBitStr.after(bs, rem), rest})} : Ap.Rd(Ap.Bits())}

law aper.wbitstr.decode_valid:
  for +lo: Nat
  for +diff: Nat
  for +c: Ap.Cur
  for +bs: Ap.Bits()
  for +c2: Ap.Cur
  for +e: {Ap.WBitStr.read(lo, diff, c) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}
  {Ap.WBitStr.valid(lo, diff, bs) == True{} : Bool}

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
  for +al: Bool
  for +n: Nat
  for +diff: U32
  for +x: Ap.XInt
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Ap.XInt.valid(n, diff, x) == True{} : Bool}
  {Ap.XInt.read(al, n, diff, Ap.Cur{rem, Ap.XInt.write(al, n, x, rem, rest)}) == Done{(x, Ap.Cur{Ap.XInt.after(al, n, x, rem), rest})} : Ap.Rd(Ap.XInt)}

law aper.xint.decode_valid:
  for +al: Bool
  for +n: Nat
  for +diff: U32
  for +c: Ap.Cur
  for +x: Ap.XInt
  for +c2: Ap.Cur
  for +e: {Ap.XInt.read(al, n, diff, c) == Done{(x, c2)} : Ap.Rd(Ap.XInt)}
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

# A complete encoding is padded to an octet with zero bits (§11.1.3), and
# only such a tail may follow one.
law aper.pack.padding:
  for +bits: Ap.Bits()
  {Ap.unpack(Ap.pack(bits)) == List.append(&2, Bool, bits, Ap.padding(bits)) : Ap.Bits()}

law aper.pack.padding_zero:
  for +bits: Ap.Bits()
  {Ap.Tail.zero(Ap.padding(bits)) == True{} : Bool}

# ngap framing (ticket 13)
# ------------------------
# The roundtrip, decode_valid and suffix laws of every generated type, and the
# mandatory law of every view, are stated with the code they are about, in
# kernel/ngap/gen/laws.bend, and proven in kernel/ngap/gen/proofs.bend;
# PROOF.bend imports them. The mandatory laws below restate four of them
# under the names the tickets give.

law ngap.ie.roundtrip:
  for +ie: Fr.Ie
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Fr.Ie.valid(ie) == True{} : Bool}
  {Fr.Ie.read(Ap.Cur{rem, Fr.Ie.write(ie, rem, rest)}) == Done{(ie, Ap.Cur{Fr.Ie.after(rem), rest})} : Ap.Rd(Fr.Ie)}

law ngap.ie.decode_valid:
  for +c: Ap.Cur
  for +ie: Fr.Ie
  for +c2: Ap.Cur
  for +e: {Fr.Ie.read(c) == Done{(ie, c2)} : Ap.Rd(Fr.Ie)}
  {Fr.Ie.valid(ie) == True{} : Bool}

law ngap.ies.roundtrip:
  for +ies: List<&2, Fr.Ie>
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Fr.Ies.valid(ies) == True{} : Bool}
  {Fr.Ies.read(Ap.Cur{rem, Fr.Ies.write(ies, rem, rest)}) == Done{(ies, Ap.Cur{Fr.Ies.after(rem), rest})} : Ap.Rd(List<&2, Fr.Ie>)}

law ngap.ies.decode_valid:
  for +c: Ap.Cur
  for +ies: List<&2, Fr.Ie>
  for +c2: Ap.Cur
  for +e: {Fr.Ies.read(c) == Done{(ies, c2)} : Ap.Rd(List<&2, Fr.Ie>)}
  {Fr.Ies.valid(ies) == True{} : Bool}

law ngap.exts.roundtrip:
  for +ies: List<&2, Fr.Ie>
  for +rem: Nat
  for +rest: Ap.Bits()
  for +v: {Fr.Exts.valid(ies) == True{} : Bool}
  {Fr.Exts.read(Ap.Cur{rem, Fr.Exts.write(ies, rem, rest)}) == Done{(ies, Ap.Cur{Fr.Exts.after(rem), rest})} : Ap.Rd(List<&2, Fr.Ie>)}

law ngap.exts.decode_valid:
  for +c: Ap.Cur
  for +ies: List<&2, Fr.Ie>
  for +c2: Ap.Cur
  for +e: {Fr.Exts.read(c) == Done{(ies, c2)} : Ap.Rd(List<&2, Fr.Ie>)}
  {Fr.Exts.valid(ies) == True{} : Bool}

# The PDU codec works on bytes: a valid PDU reads back from its own bytes,
# and whatever reads is valid.
law ngap.pdu.roundtrip:
  for +p: Fr.Pdu
  for +v: {Fr.Pdu.valid(p) == True{} : Bool}
  {Fr.Pdu.read(Fr.Pdu.write(p)) == Done{p} : Result<&2, &2, B.Err, Fr.Pdu>}

law ngap.pdu.decode_valid:
  for +bs: B.Bytes()
  for +p: Fr.Pdu
  for +e: {Fr.Pdu.read(bs) == Done{p} : Result<&2, &2, B.Err, Fr.Pdu>}
  {Fr.Pdu.valid(p) == True{} : Bool}

# AMF-UE-NGAP-ID (40 bits) and BitRate (up to 4·10¹², extensible) decode to
# byte lists, never to a Nat: at most five canonical octets for the id, and
# octets for the bit rate in either form.
law ngap.no_big_nat:
  for +c: Ap.Cur
  for +c2: Ap.Cur
  (@v: B.Bytes() -> {G.AMF_UE_NGAP_ID.read(c) == Done{(v, c2)} : Ap.Rd(G.AMF_UE_NGAP_ID())} -> {Nat.is_le(List.length(&2, U32, v), 5n) == True{} : Bool} & {B.all_bytes(v) == True{} : Bool})
  & (@v: Ap.XBig -> {G.BitRate.read(c) == Done{(v, c2)} : Ap.Rd(G.BitRate())} -> {B.all_bytes(Ap.XBig.octets(v)) == True{} : Bool})

# Message views (TS 38.413 §10.3). Every generated view passes Fr.View.prelude
# first, so an IE id that appears twice fails the view (§10.3.6).
law ngap.view.duplicate_rejected:
  for +known: List<&2, U32>
  for +ies: List<&2, Fr.Ie>
  for +ies2: List<&2, Fr.Ie>
  for +e: {Fr.View.prelude(known, ies) == Done{ies2} : Result<&2, &2, B.Err, List<&2, Fr.Ie>>}
  {Fr.Ies.no_dups(ies) == True{} : Bool}

# GHSA-cfp8-93x2-6h9x: the InitialUEMessage view succeeds only when
# RAN-UE-NGAP-ID (85), NAS-PDU (38), UserLocationInformation (121) and
# RRCEstablishmentCause (90) are each present exactly once.
law ngap.initial_ue_message.mandatory:
  for +ies: List<&2, Fr.Ie>
  for +v: GV.InitialUEMessage.View
  for +e: {GV.InitialUEMessage.view(ies) == Done{v} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}
  {Fr.Ies.occurrences(85, ies) == 1n : Nat} & ({Fr.Ies.occurrences(38, ies) == 1n : Nat} & ({Fr.Ies.occurrences(121, ies) == 1n : Nat} & {Fr.Ies.occurrences(90, ies) == 1n : Nat}))

# The Path Switch Request view succeeds only when RAN-UE-NGAP-ID (85),
# Source AMF-UE-NGAP-ID (100), UserLocationInformation (121),
# UESecurityCapabilities (119) and the PDU session list (76) are each present
# exactly once.
law ngap.path_switch_request.mandatory:
  for +ies: List<&2, Fr.Ie>
  for +v: GV.PathSwitchRequest.View
  for +e: {GV.PathSwitchRequest.view(ies) == Done{v} : Result<&2, &2, B.Err, GV.PathSwitchRequest.View>}
  {Fr.Ies.occurrences(85, ies) == 1n : Nat} & ({Fr.Ies.occurrences(100, ies) == 1n : Nat} & ({Fr.Ies.occurrences(121, ies) == 1n : Nat} & ({Fr.Ies.occurrences(119, ies) == 1n : Nat} & {Fr.Ies.occurrences(76, ies) == 1n : Nat})))

# The Handover Request Acknowledge view: AMF-UE-NGAP-ID (10), RAN-UE-NGAP-ID
# (85), the admitted PDU sessions (53) and the Target to Source container (106).
law ngap.handover_request_acknowledge.mandatory:
  for +ies: List<&2, Fr.Ie>
  for +v: GV.HandoverRequestAcknowledge.View
  for +e: {GV.HandoverRequestAcknowledge.view(ies) == Done{v} : Result<&2, &2, B.Err, GV.HandoverRequestAcknowledge.View>}
  {Fr.Ies.occurrences(10, ies) == 1n : Nat} & ({Fr.Ies.occurrences(85, ies) == 1n : Nat} & ({Fr.Ies.occurrences(53, ies) == 1n : Nat} & {Fr.Ies.occurrences(106, ies) == 1n : Nat}))

# The Handover Required view: AMF-UE-NGAP-ID (10), RAN-UE-NGAP-ID (85),
# HandoverType (29), Cause (15), TargetID (105), the PDU sessions (61) and the
# Source to Target container (101).
law ngap.handover_required.mandatory:
  for +ies: List<&2, Fr.Ie>
  for +v: GV.HandoverRequired.View
  for +e: {GV.HandoverRequired.view(ies) == Done{v} : Result<&2, &2, B.Err, GV.HandoverRequired.View>}
  {Fr.Ies.occurrences(10, ies) == 1n : Nat} & ({Fr.Ies.occurrences(85, ies) == 1n : Nat} & ({Fr.Ies.occurrences(29, ies) == 1n : Nat} & ({Fr.Ies.occurrences(15, ies) == 1n : Nat} & ({Fr.Ies.occurrences(105, ies) == 1n : Nat} & ({Fr.Ies.occurrences(61, ies) == 1n : Nat} & {Fr.Ies.occurrences(101, ies) == 1n : Nat})))))

# pfcp (ticket 14)
# ----------------
# TS 29.244 over bytes: a valid message reads back from its encoding, what
# reads is valid, and the bytes a message was read from are its encoding.
law pfcp.roundtrip:
  for +m: Pf.Msg
  for +rest: B.Bytes()
  for +v: {Pf.Msg.valid(m) == True{} : Bool}
  {Pf.Msg.read(Pf.Msg.write(m, rest)) == Done{(m, rest)} : B.Read(Pf.Msg)}

law pfcp.decode_valid:
  for +bs: B.Bytes()
  for +m: Pf.Msg
  for +rest: B.Bytes()
  for +e: {Pf.Msg.read(bs) == Done{(m, rest)} : B.Read(Pf.Msg)}
  {Pf.Msg.valid(m) == True{} : Bool}

law pfcp.suffix:
  for +bs: B.Bytes()
  for +m: Pf.Msg
  for +rest: B.Bytes()
  for +e: {Pf.Msg.read(bs) == Done{(m, rest)} : B.Read(Pf.Msg)}
  for +ab: {B.all_bytes(bs) == True{} : Bool}
  {Pf.Msg.write(m, rest) == bs : B.Bytes()}

# GHSA-4x7x-2p8x-jwrq: an IE header is four octets; fewer fail as Short.
law pfcp.ie_header.short_input_fails:
  for +bs: B.Bytes()
  for +e: {Nat.is_lt(List.length(&2, U32, bs), 4n) == True{} : Bool}
  {T.Tlv.read(bs) == Fail{B.Short{}} : B.Read(T.Tlv)}

# GHSA-37c3-hv4f-688p: every IE, known or not, consumes exactly its four
# header octets plus the length it declares, and fails as Short when fewer
# octets remain.
law pfcp.ie.suffix:
  for +bs: B.Bytes()
  (@ie: T.Tlv -> @rest: B.Bytes() -> {T.Tlv.read(bs) == Done{(ie, rest)} : B.Read(T.Tlv)} -> {List.drop(&2, U32, bs, Nat.add(4n, U32.to_nat(T.Tlv.len(ie)))) == rest : B.Bytes()} & {List.length(&2, U32, T.Tlv.body(ie)) == U32.to_nat(T.Tlv.len(ie)) : Nat})
  & (@kind: U32 -> @len: U32 -> @tail: B.Bytes() -> {T.Tlv.header(bs) == Done{(T.Hdr{kind, len}, tail)} : B.Read(T.Hdr)} -> {B.all_bytes(bs) == True{} : Bool} -> {Nat.is_lt(List.length(&2, U32, tail), U32.to_nat(len)) == True{} : Bool} -> {T.Tlv.read(bs) == Fail{B.Short{}} : B.Read(T.Tlv)})

# GHSA-3mxx-vq7h-x8ff: an F-TEID or an F-SEID (the one the kernel reads from
# the UPF) decodes only when its body is exactly what its flags call for: what
# decodes is valid (each address of its length, an F-TEID naming at least one,
# its CH form with no TEID and no address by construction, an F-SEID's SEID of
# eight octets) and re-encodes to the body it was read from.
law pfcp.fteid.decode_valid:
  for +body: B.Bytes()
  for +f: Pf.Fteid
  for +e: {Pf.Fteid.read(body) == Done{f} : Result<&2, &2, B.Err, Pf.Fteid>}
  {Pf.Fteid.valid(f) == True{} : Bool} & ({B.all_bytes(body) == True{} : Bool} -> {Pf.Fteid.write(f) == body : B.Bytes()})

law pfcp.fseid.decode_valid:
  for +body: B.Bytes()
  for +f: Pf.Fseid
  for +e: {Pf.Fseid.read(body) == Done{f} : Result<&2, &2, B.Err, Pf.Fseid>}
  {Pf.Fseid.valid(f) == True{} : Bool} & {Pf.Fseid.write(f) == body : B.Bytes()}

# The length field counts exactly the octets that follow it.
law pfcp.header.length_consistent:
  for +bs: B.Bytes()
  for +m: Pf.Msg
  for +rest: B.Bytes()
  for +e: {Pf.Msg.read(bs) == Done{(m, rest)} : B.Read(Pf.Msg)}
  {List.length(&2, U32, bs) == Nat.add(4n, Nat.add(U32.to_nat(Pf.Msg.len(m)), List.length(&2, U32, rest))) : Nat}

# frame (ticket 15)
# -----------------
# The edge ⇄ kernel frame protocol (milestone-1.md § The frame protocol): a
# length-prefixed body holding one event or one list of actions.

# A body longer than 262144 octets is refused on its length word alone.
law frame.max_length:
  for +b3: U32
  for +b2: U32
  for +b1: U32
  for +b0: U32
  for +rest: B.Bytes()
  for +e: {Nat.is_lt(262144n, U32.to_nat(B.cat8(b0, B.cat8(b1, B.cat8(b2, b3))))) == True{} : Bool}
  {F.Frame.read(b3 <> b2 <> b1 <> b0 <> rest) == Fail{B.Invalid{B.cat8(b0, B.cat8(b1, B.cat8(b2, b3)))}} : B.Read(B.Bytes())}

law frame.event.roundtrip:
  for +i: F.Input
  for +rest: B.Bytes()
  for +v: {F.Input.valid(i) == True{} : Bool}
  {F.Input.read(F.Input.write(i, rest)) == Done{(i, rest)} : B.Read(F.Input)}

law frame.event.decode_valid:
  for +bs: B.Bytes()
  for +i: F.Input
  for +rest: B.Bytes()
  for +e: {F.Input.read(bs) == Done{(i, rest)} : B.Read(F.Input)}
  {F.Input.valid(i) == True{} : Bool}

law frame.event.suffix:
  for +bs: B.Bytes()
  for +i: F.Input
  for +rest: B.Bytes()
  for +e: {F.Input.read(bs) == Done{(i, rest)} : B.Read(F.Input)}
  for +ab: {B.all_bytes(bs) == True{} : Bool}
  {F.Input.write(i, rest) == bs : B.Bytes()}

law frame.actions.roundtrip:
  for +as: F.Actions
  for +rest: B.Bytes()
  for +v: {F.Actions.valid(as) == True{} : Bool}
  {F.Actions.read(F.Actions.write(as, rest)) == Done{(as, rest)} : B.Read(F.Actions)}

# A repeated Config tag yields the later value.
law frame.config.repeat_replaces:
  for +tl: List<&2, T.Tlv>
  for +tag: U32
  for +len: U32
  for +v: B.Bytes()
  {F.Config.get(tag, List.append(&2, T.Tlv, tl, [T.Tlv{tag, len, v}])) == Some{v} : Maybe<&2, B.Bytes()>}

# kernel (ticket 16)
# ------------------
# The step function over the AMF's first procedures.

# NG Setup Response goes out only for a request whose supported TA list names
# the configured PLMN and TAC.
law amf.ng_setup.requires_supported_plmn:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +e: {Ng.Ngap.any_ng_setup_response(Ke.Kernel.actions(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == True{} : Bool}
  {Ng.NgSetup.supported_request(St.State.config(st), bytes) == True{} : Bool}

# The kernel holds no configuration but a valid one (St.Cfg.valid), in the
# initial state and after every step: Config takes effect only when complete,
# and nothing else changes the configuration.
law kernel.config.valid:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +cfg: St.Cfg
  for e: @c: St.Cfg -> {St.State.config(st) == Some{c} : Maybe<&2, St.Cfg>} -> {St.Cfg.valid(c) == True{} : Bool}
  for +ec: {St.State.config(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy))) == Some{cfg} : Maybe<&2, St.Cfg>}
  {St.State.config(St.State.initial()) == None{} : Maybe<&2, St.Cfg>} & {St.Cfg.valid(cfg) == True{} : Bool}

# After an association goes down, no UE context is owned by it.
law amf.assoc_down.releases_all:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  {St.Ues.none_assoc(assoc, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapAssocDown{assoc}, entropy)))) == True{} : Bool}

# An undecodable NGAP PDU changes no state and yields Error Indication and a
# log line, nothing else.
law kernel.bad_pdu.only_error_indication:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +err: B.Err
  for +e: {Fr.Pdu.read(bytes) == Fail{err} : Result<&2, &2, B.Err, Fr.Pdu>}
  {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.bad_pdu(assoc)) : Ng.Step()}

# TS 38.413 §8.7.1.1: NG Setup is the first NGAP procedure on an
# association. Every other message from an association that has not
# completed it, InitialUEMessage and every UE-associated message included,
# changes no state; the only actions are Error Indication and a log line.
# The laws below that say what a UE-associated message does take its
# association as set up; this law says what happens otherwise.
law amf.ng_setup.first:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +kind: U32
  for +code: U32
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +en: {Ng.Ngap.is_ng_setup(U32.to_nat(kind), U32.to_nat(code)) == False{} : Bool}
  for +ea: {St.Assocs.has(assoc, St.State.assocs(st)) == False{} : Bool}
  {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.unhandled(assoc)) : Ng.Step()}

# amf (ticket 17)
# ---------------
# Identification and 5G-AKA.

# GHSA-cfp8-93x2-6h9x: an InitialUEMessage whose view fails leaves the state as
# it was; the only actions are Error Indication and a log line.
law amf.initial_ue.reject_leaves_state:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +err: B.Err
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 15, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ev: {GV.InitialUEMessage.view(ies) == Fail{err} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}
  for +eup: {St.Assocs.has(assoc, St.State.assocs(st)) == True{} : Bool}
  {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.bad_view(assoc)) : Ng.Step()}

# GHSA-r9rw-hx33-745g (5G analogue): authentication succeeds only when RES* is
# sixteen octets, HRES* equals HXRES* over all of them and RES* equals XRES*
# over all of them.
law ausf.res_star.full_length:
  for +av: Au.Av
  for +res: B.Bytes()
  for +e: {Au.Ausf.verify(av, res) == True{} : Bool}
  {Nat.is_eq(List.length(&2, U32, res), 16n) == True{} : Bool} & ({B.bytes_eq(K.kdf.hres_star(Au.Av.rand(av), res), Au.Av.hxres_star(av)) == True{} : Bool} & {B.bytes_eq(res, Au.Av.xres_star(av)) == True{} : Bool})

# amf (ticket 18)
# ---------------
# Security mode, acceptance and release.

# GHSA-mg8r-2cvv-xq9j: a UE Context Release Request or Complete, an Initial
# Context Setup Response, a PDU Session Resource Setup Response or an Uplink NAS
# Transport naming a UE that another association owns changes no state.
law amf.ue_context_release.owner_only:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +ran: B.Bytes()
  for +pdus: Maybe<&2, G.PDUSessionResourceListCxtRelReq()>
  for +cause: G.Cause
  for +uli: Maybe<&2, G.UserLocationInformation>
  for +rel: Maybe<&2, G.PDUSessionResourceListCxtRelCpl()>
  for +diag: Maybe<&2, G.CriticalityDiagnostics>
  for +oks: Maybe<&2, G.PDUSessionResourceSetupListSURes()>
  for +fails: Maybe<&2, G.PDUSessionResourceFailedToSetupListSURes()>
  for +nas: B.Bytes()
  for +loc: G.UserLocationInformation
  for +ue: St.Ue
  for +eu: {Tb.Table.get(St.Ue, Ng.Ngap.of_big(amf), St.State.ues(st)) == Some{ue} : Maybe<&2, St.Ue>}
  for +ea: {U32.is_eq(St.Ue.assoc(ue), assoc) == False{} : Bool}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 42, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.UEContextReleaseRequest.view(ies) == Done{GV.UEContextReleaseRequest.View{amf, ran, pdus, cause}} : Result<&2, &2, B.Err, GV.UEContextReleaseRequest.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 41, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.UEContextReleaseComplete.view(ies) == Done{GV.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}} : Result<&2, &2, B.Err, GV.UEContextReleaseComplete.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 14, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.InitialContextSetupResponse.view(ies) == Done{GV.InitialContextSetupResponse.View{amf, ran, diag}} : Result<&2, &2, B.Err, GV.InitialContextSetupResponse.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 29, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.PDUSessionResourceSetupResponse.view(ies) == Done{GV.PDUSessionResourceSetupResponse.View{amf, ran, oks, fails, diag, uli}} : Result<&2, &2, B.Err, GV.PDUSessionResourceSetupResponse.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.UplinkNASTransport.view(ies) == Done{GV.UplinkNASTransport.View{amf, ran, nas, loc}} : Result<&2, &2, B.Err, GV.UplinkNASTransport.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State})

# After the owner's UE Context Release Complete, no UE context carries the
# UE's AMF-UE-NGAP-ID and no session belongs to it: those the UPF knows are
# being deleted there, which belong to no UE (St.Session.tag).
law amf.release.complete_forgets:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +k: U32
  for +ran: B.Bytes()
  for +uli: Maybe<&2, G.UserLocationInformation>
  for +rel: Maybe<&2, G.PDUSessionResourceListCxtRelCpl()>
  for +diag: Maybe<&2, G.CriticalityDiagnostics>
  for +ue: St.Ue
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 41, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ev: {GV.UEContextReleaseComplete.view(ies) == Done{GV.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}} : Result<&2, &2, B.Err, GV.UEContextReleaseComplete.View>}
  for +eid: {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}
  for +eo: {Gm.Gmm.owner(st, assoc, k, ran) == Some{ue} : Maybe<&2, St.Ue>}
  for +eup: {St.Assocs.has(assoc, St.State.assocs(st)) == True{} : Bool}
  {Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == None{} : Maybe<&2, St.Ue>}
  & {St.Sessions.of_ue(k, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == [] : Tb.Table(St.Session)}

# GHSA-7g3v-g4gp-p624: the indexes are the contexts themselves, so every entry
# is a context and every context is indexed; what remains is that no two
# contexts share a key, a SUPI, a 5G-TMSI or a RAN-UE-NGAP-ID on an association,
# in the initial state and after every step.
law amf.indexes.unique:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +e: {St.Ues.unique(St.State.ues(st)) == True{} : Bool}
  {St.Ues.unique(St.State.ues(St.State.initial())) == True{} : Bool}
  & {St.Ues.unique(St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == True{} : Bool}

# With a NAS security context in force, an uplink message that fails to verify
# under it changes no state.
law amf.nas.plaintext_after_security:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +ran: B.Bytes()
  for +nas: B.Bytes()
  for +uli: G.UserLocationInformation
  for +ue: St.Ue
  for +ctx: N.Nas.Ctx
  for +err: B.Err
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ev: {GV.UplinkNASTransport.view(ies) == Done{GV.UplinkNASTransport.View{amf, ran, nas, uli}} : Result<&2, &2, B.Err, GV.UplinkNASTransport.View>}
  for +eo: {Gm.Gmm.owner(st, assoc, Ng.Ngap.of_big(amf), ran) == Some{ue} : Maybe<&2, St.Ue>}
  for +ec: {St.Phase.ctx(St.Ue.phase(ue)) == Some{ctx} : Maybe<&2, N.Nas.Ctx>}
  for +ef: {N.Nas.unprotect(ctx, nas) == Fail{err} : Result<&2, &2, B.Err, N.Nas.Unprotected>}
  {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State}

# amf (ticket 32)
# ---------------
# Identity takeover after authentication.

# GHSA-mg8r-2cvv-xq9j: an NGAP message from one association removes no UE
# context that another association owns, neither forgetting it nor writing
# another over its key, unless, in the resulting state, a context with its
# SUPI holds a NAS security context, which exists only once 5G-AKA has
# verified that SUPI. It holds in every state whose indexes are unique, which
# is every state step reaches (amf.indexes.unique).
law amf.takeover.authenticated:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +k: U32
  for +u: St.Ue
  for +e: {St.Ues.unique(St.State.ues(st)) == True{} : Bool}
  for +eu: {Tb.Table.get(St.Ue, k, St.State.ues(st)) == Some{u} : Maybe<&2, St.Ue>}
  for +ea: {U32.is_eq(St.Ue.assoc(u), assoc) == False{} : Bool}
  for eg: {Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == Some{u} : Maybe<&2, St.Ue>} -> Empty
  {St.Ues.secured(St.Ue.supi(u), St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == True{} : Bool}

# amf (ticket 33)
# ---------------
# Liveness: a guard that fires ends the wait it bounds, and a UE that is gone
# is never acted for again.

# GHSA-cfp8-93x2-6h9x: a context whose guard fires at the retry limit moves to
# Releasing with a new guard; a Releasing context whose guard fires is gone, and
# no session belongs to it: each the UPF knows is being deleted there, under
# its guard started again, and the others are gone, their guards stopped. A
# context's guard timer is its key.
law amf.guard.expires:
  for +st: St.State
  for +entropy: B.Bytes()
  for +k: U32
  for +u: St.Ue
  for +g: St.Guard
  for +et: {Tb.Table.get(St.Ue, k, St.State.ues(st)) == Some{u} : Maybe<&2, St.Ue>}
  for +eg: {St.Ue.guard(u) == Some{g} : Maybe<&2, St.Guard>}
  (({St.Ue.phase(u) == St.Releasing{g} : St.Phase} -> Empty) -> {U32.is_lt(St.Guard.retries(g), Gm.Gmm.max_retries()) == False{} : Bool} -> {Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{k}, entropy)))) == Some{St.Ue.with_phase(u, St.Releasing{St.Guard{0}})} : Maybe<&2, St.Ue>})
  & ({St.Ue.phase(u) == St.Releasing{g} : St.Phase} -> {Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{k}, entropy)))) == None{} : Maybe<&2, St.Ue>} & ({St.Sessions.of_ue(k, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{k}, entropy)))) == [] : Tb.Table(St.Session)} & {Ke.Kernel.actions(Ke.Kernel.step(st, F.TimerFired{k}, entropy)) == List.append(&2, Ng.Act, List.append(&2, Ng.Act, Ng.Out.acts(Up.N4.deletions(St.Sessions.of_ue(k, St.State.sessions(st)), St.State.pfcp_seq(st))), [Ng.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]), Ng.Gone.cancels(St.State.sessions(st), St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{k}, entropy))))) : List<&2, Ng.Act>}))

# Every session belongs to a UE context, in the initial state and after every
# step, but a session being deleted at the UPF, whose context may be gone:
# whatever forgets a context first deletes its sessions, and a session being
# deleted belongs to no UE and stays so until its row goes
# (smf.deletion.retransmitted, smf.deletion.answered).
law amf.sessions.owned:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +e: {St.Sessions.owned(St.State.sessions(st), St.State.ues(st)) == True{} : Bool}
  {St.Sessions.owned(St.State.sessions(St.State.initial()), St.State.ues(St.State.initial())) == True{} : Bool}
  & {St.Sessions.owned(St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy))), St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == True{} : Bool}

# GHSA-88pq-hpwv-2vjw: a UE context that is gone, by whatever path, is never
# acted for again. No UE-associated NGAP message, PFCP message or timer a step
# starts is built from a key that names no context, unless it is the key the
# step gives a new context; Error Indication names no UE. It holds in every
# state whose sessions belong to contexts (amf.sessions.owned).
law amf.release.forgets_ue:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +k: U32
  for +eo: {St.Sessions.owned(St.State.sessions(st), St.State.ues(st)) == True{} : Bool}
  for +eg: {Tb.Table.get(St.Ue, k, St.State.ues(st)) == None{} : Maybe<&2, St.Ue>}
  for +en: {St.Maybe.same_u32(St.State.fresh(st), Some{k}) == False{} : Bool}
  {Ng.Acts.spare(k, Ke.Kernel.actions(Ke.Kernel.step(st, ev, entropy))) == True{} : Bool}

# amf (ticket 38)
# ---------------

# GHSA-cfp8-93x2-6h9x: every context is registered or waits under its guard
# timer, so none is ever stored Created, in the initial state and after every
# step; amf.guard.expires shows what the guard does when it fires.
law amf.contexts.guarded:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +e: {St.Ues.guarded(St.State.ues(st)) == True{} : Bool}
  {St.Ues.guarded(St.State.ues(St.State.initial())) == True{} : Bool}
  & {St.Ues.guarded(St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == True{} : Bool}

# TS 38.413 §8.7.1.1: every context is owned by an association that has
# completed NG Setup, in the initial state and after every step: contexts are
# made and moved only by messages from such an association, and NG Setup and
# the association going down release its contexts first. A UE-associated
# message from an association without NG Setup therefore names no context
# (amf.ng_setup.first says what it gets).
law amf.contexts.set_up:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +e: {St.Ues.set_up(St.State.ues(st), St.State.assocs(st)) == True{} : Bool}
  {St.Ues.set_up(St.State.ues(St.State.initial()), St.State.assocs(St.State.initial())) == True{} : Bool}
  & {St.Ues.set_up(St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy))), St.State.assocs(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == True{} : Bool}

# state (ticket 35)
# -----------------

# The key an InitialUEMessage gives its new context (St.State.fresh) holds no
# context, and no context appears under any other key. In the initial state
# and after every step every context's key is odd and every session's key
# even and not zero (St.Ids.free); a row's guard timer is its key and timer 0
# the N4 association's, so no two rows share a guard timer: no key holds both
# a context and a session, and neither table holds timer 0. It holds in every
# state that keeps the keys so, which is every state step reaches, and whose
# sessions belong to contexts (amf.sessions.owned).
law state.ids.free:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +k: U32
  for +e: {St.Ids.free(St.State.ues(st), St.State.sessions(st)) == True{} : Bool}
  for +eo: {St.Sessions.owned(St.State.sessions(st), St.State.ues(st)) == True{} : Bool}
  ({St.State.fresh(st) == Some{k} : Maybe<&2, U32>} -> {Tb.Table.get(St.Ue, k, St.State.ues(st)) == None{} : Maybe<&2, St.Ue>})
  & (({Tb.Table.get(St.Ue, k, St.State.ues(st)) == None{} : Maybe<&2, St.Ue>} -> {Tb.Table.has(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == True{} : Bool} -> {St.State.fresh(st) == Some{k} : Maybe<&2, U32>})
  & ({St.Ids.free(St.State.ues(St.State.initial()), St.State.sessions(St.State.initial())) == True{} : Bool}
  & ({St.Ids.free(St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy))), St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == True{} : Bool}
  & (({Tb.Table.has(St.Ue, k, St.State.ues(st)) == True{} : Bool} -> {Tb.Table.has(St.Session, k, St.State.sessions(st)) == False{} : Bool})
  & ({Tb.Table.has(St.Ue, St.N4.timer(), St.State.ues(st)) == False{} : Bool} & {Tb.Table.has(St.Session, St.N4.timer(), St.State.sessions(st)) == False{} : Bool})))))

# A step that removes a session row stops that row's guard timer, its key, so
# no stale timer can end a later session drawn under the same SEID, whatever
# path forgets the session.
law smf.guard.stopped:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +k: U32
  for +s: St.Session
  for +g: St.Guard
  for +es: {Tb.Table.get(St.Session, k, St.State.sessions(st)) == Some{s} : Maybe<&2, St.Session>}
  for +eg: {St.SPhase.guard(St.Session.phase(s)) == Some{g} : Maybe<&2, St.Guard>}
  for +eh: {Tb.Table.get(St.Session, k, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == None{} : Maybe<&2, St.Session>}
  {Ng.Acts.stops(k, Ke.Kernel.actions(Ke.Kernel.step(st, ev, entropy))) == True{} : Bool}

# An AMF-UE-NGAP-ID of 2^32 or more, which Ng.Ngap.ue_key gives no key for,
# names no UE context, never the one its low 32 bits would fold onto: a UE
# Context Release Request or Complete, an Initial Context Setup Response, a
# PDU Session Resource Setup Response, an Uplink NAS Transport or a PDU
# Session Resource Release Response carrying one changes no state, and the
# only actions are Error Indication and a log line.
law amf.ue_key.unknown:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +ran: B.Bytes()
  for +pdus: Maybe<&2, G.PDUSessionResourceListCxtRelReq()>
  for +cause: G.Cause
  for +uli: Maybe<&2, G.UserLocationInformation>
  for +rel: Maybe<&2, G.PDUSessionResourceListCxtRelCpl()>
  for +diag: Maybe<&2, G.CriticalityDiagnostics>
  for +oks: Maybe<&2, G.PDUSessionResourceSetupListSURes()>
  for +fails: Maybe<&2, G.PDUSessionResourceFailedToSetupListSURes()>
  for +nas: B.Bytes()
  for +loc: G.UserLocationInformation
  for +items: G.PDUSessionResourceReleasedListRelRes()
  for +eid: {Ng.Ngap.ue_key(amf) == None{} : Maybe<&2, U32>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +eup: {St.Assocs.has(assoc, St.State.assocs(st)) == True{} : Bool}
  ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 42, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.UEContextReleaseRequest.view(ies) == Done{GV.UEContextReleaseRequest.View{amf, ran, pdus, cause}} : Result<&2, &2, B.Err, GV.UEContextReleaseRequest.View>} -> {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.unknown_ue(assoc)) : Ng.Step()})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 41, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.UEContextReleaseComplete.view(ies) == Done{GV.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}} : Result<&2, &2, B.Err, GV.UEContextReleaseComplete.View>} -> {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.unknown_ue(assoc)) : Ng.Step()})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 14, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.InitialContextSetupResponse.view(ies) == Done{GV.InitialContextSetupResponse.View{amf, ran, diag}} : Result<&2, &2, B.Err, GV.InitialContextSetupResponse.View>} -> {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.unknown_ue(assoc)) : Ng.Step()})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 29, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.PDUSessionResourceSetupResponse.view(ies) == Done{GV.PDUSessionResourceSetupResponse.View{amf, ran, oks, fails, diag, uli}} : Result<&2, &2, B.Err, GV.PDUSessionResourceSetupResponse.View>} -> {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.unknown_ue(assoc)) : Ng.Step()})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.UplinkNASTransport.view(ies) == Done{GV.UplinkNASTransport.View{amf, ran, nas, loc}} : Result<&2, &2, B.Err, GV.UplinkNASTransport.View>} -> {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.unknown_ue(assoc)) : Ng.Step()})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 28, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.PDUSessionResourceReleaseResponse.view(ies) == Done{GV.PDUSessionResourceReleaseResponse.View{amf, ran, items, uli, diag}} : Result<&2, &2, B.Err, GV.PDUSessionResourceReleaseResponse.View>} -> {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.unknown_ue(assoc)) : Ng.Step()})

# smf (ticket 19)
# ---------------
# PDU session establishment.

# GHSA-ch5j-wv55-jmr6: a PDU Session Establishment Request that fails
# validation (the session identity, request type, DNN, slice, no association,
# type, or no free address in the pool, TEID or SEID, #26) leaves the sessions and the PFCP
# sequence as they were; the UE is told why and nothing else happens.
law smf.establish.reject_leaves_state:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +k: U32
  for +ran: B.Bytes()
  for +nas: B.Bytes()
  for +uli: G.UserLocationInformation
  for +ue: St.Ue
  for +ctx: N.Nas.Ctx
  for +prot: N.Nas.Protection
  for +plain: B.Bytes()
  for +count: N.Nas.Count
  for +ctx2: N.Nas.Ctx
  for +old: N.Nas.Ctx
  for +nh: St.Nh
  for +released: Maybe<&2, St.Side>
  for +fields: List<&2, I.Field>
  for +opts: List<&2, I.Ie>
  for +psi: U32
  for +pti: U32
  for +sfields: List<&2, I.Field>
  for +sopts: List<&2, I.Ie>
  for +cfg: St.Cfg
  for +cause: U32
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ev: {GV.UplinkNASTransport.view(ies) == Done{GV.UplinkNASTransport.View{amf, ran, nas, uli}} : Result<&2, &2, B.Err, GV.UplinkNASTransport.View>}
  for +eid: {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}
  for +eo: {Gm.Gmm.owner(st, assoc, k, ran) == Some{ue} : Maybe<&2, St.Ue>}
  for +ec: {St.Phase.ctx(St.Ue.phase(ue)) == Some{ctx} : Maybe<&2, N.Nas.Ctx>}
  for +eu: {N.Nas.unprotect(ctx, nas) == Done{N.Unprotected{prot, plain, count, ctx2}} : Result<&2, &2, B.Err, N.Nas.Unprotected>}
  for +em: {Mm.Mm.read(plain) == Done{Mm.Mm{Mm.UlNasTransport{}, fields, opts}} : Result<&2, &2, B.Err, Mm.Mm>}
  for +er: {St.Ue.phase(ue) == St.Registered{old, nh, released} : St.Phase}
  for +en: {U32.is_eq(I.Fields.byte1(fields), 1) == True{} : Bool}
  for +es: {Sm.Sm.read(I.Fields.lve2(fields)) == Done{Sm.Sm{psi, pti, Sm.EstablishmentRequest{}, sfields, sopts}} : Result<&2, &2, B.Err, Sm.Sm>}
  for +ef: {St.State.config(st) == Some{cfg} : Maybe<&2, St.Cfg>}
  for +ex: {Gs.Gsm.validate(cfg, psi, opts, sopts, Up.N4.up(st), St.State.sessions(st), entropy) == Gs.Refuse{cause} : Gs.Check}
  for +eup: {St.Assocs.has(assoc, St.State.assocs(st)) == True{} : Bool}
  {St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == St.State.sessions(st) : Tb.Table(St.Session)}
  & ({St.State.pfcp_seq(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == St.State.pfcp_seq(st) : U32}
  & {Ke.Kernel.actions(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == [Ng.DlNas{St.Ue.assoc(ue), St.Ue.stream(ue), k, St.Ue.ran_id(ue), N.Nas.Protected.msg(N.Nas.protect(ctx2, N.Ciphered{}, Gs.Gsm.dl_transport(psi, Gs.Gsm.reject(psi, pti, cause))))}] : List<&2, Ng.Act>})

# GHSA-855g-699w-9w28: whichever later step fails, the session belongs to no
# UE any more. While it is being created the UPF does not know it
# (smf.sessions.known) and no entry remains, so no address, TEID or SEID is
# held for it; past Creating a PFCP Session Deletion Request for it goes out,
# its guard started right after it, and its entry, if any, is being deleted
# under that guard, which has not fired yet: it holds its address, TEID and
# SEID only until the UPF answers or the retries run out
# (smf.deletion.retransmitted, smf.deletion.answered). The failures: the UPF refuses the Session
# Establishment; the guard, timer the session's key, expires while it is being
# set up, or while it is being created or modified once its PFCP request has
# gone N1 times again (smf.request.retransmitted); the UPF refuses the Session
# Modification; or the gNB lists the session among those that failed to set
# up, whatever else its response names. When the guard fires while the
# session is being set up, or its Session Modification is refused or goes
# unanswered, all after the Accept went out in the PDU Session Resource Setup
# Request, the first action also tells the UE's gNB to release the session,
# the PDU Session Release Command inside, when the UE holds a NAS context
# (TS 23.502 §4.3.4.2). A setup response that lists the session set up, in
# the last item naming it, with a tunnel that does not read (Gs.Gsm.modify)
# sends its Session Deletion Request too, its guard right after it, and,
# when the UE holds a NAS context, the PDU Session Resource Release Command
# to its gNB with the PDU Session Release Command inside, sealed under the
# context's keys (Gs.Gsm.told_gnb; at which COUNT, nas_sec.downlink_fresh
# says), whatever the items around it do. What its entry is then, items
# after it that modify another session under the same key would decide,
# which no reachable state has (smf.ip_pool.unique) but this law does not
# assume.
law smf.establish.failure_releases:
  for +st: St.State
  for +entropy: B.Bytes()
  for +len: U32
  for +bytes: B.Bytes()
  for +msg: Pf.Msg
  for +rest: B.Bytes()
  for +skey: U32
  for +s: St.Session
  for +guard: St.Guard
  for +pti: U32
  for +accept: Sm.Sm
  for +request: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +k: U32
  for +ran: B.Bytes()
  for +oks: Maybe<&2, G.PDUSessionResourceSetupListSURes()>
  for +pre: G.PDUSessionResourceFailedToSetupListSURes()
  for +psi: U32
  for +transfer: B.Bytes()
  for +x: Maybe<&2, List<&2, Fr.Ie>>
  for +post: G.PDUSessionResourceFailedToSetupListSURes()
  for +diag: Maybe<&2, G.CriticalityDiagnostics>
  for +uli: Maybe<&2, G.UserLocationInformation>
  for +ue: St.Ue
  for +ctx: N.Nas.Ctx
  for +opre: G.PDUSessionResourceSetupListSURes()
  for +opost: G.PDUSessionResourceSetupListSURes()
  for +fl: Maybe<&2, G.PDUSessionResourceFailedToSetupListSURes()>
  for +ek: {St.Sessions.known(St.State.sessions(st)) == True{} : Bool}
  ({Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)} -> {Pf.Msg.kind(msg) == 51 : U32} -> {St.Sessions.by_seq(Pf.Msg.seq(msg), St.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => St.Session>>} -> {St.Session.phase(s) == St.Creating{guard, pti, accept, request} : St.SPhase} -> {Up.N4.accepted(Up.N4.cause(msg)) == False{} : Bool}
    -> {Tb.Table.get(St.Session, skey, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.PfcpData{len, bytes}, entropy)))) == None{} : Maybe<&2, St.Session>})
  & (({Tb.Table.get(St.Ue, skey, St.State.ues(st)) == None{} : Maybe<&2, St.Ue>} -> {Tb.Table.get(St.Session, skey, St.State.sessions(st)) == Some{s} : Maybe<&2, St.Session>}
    -> ({St.Session.phase(s) == St.Setting{guard, pti} : St.SPhase} -> {St.Sessions.each(skey, St.SFresh{}, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)))) == True{} : Bool} & Up.N4.deleted(skey, s, Ke.Kernel.actions(Ke.Kernel.step(st, F.TimerFired{skey}, entropy))) & ({Tb.Table.get(St.Ue, St.Session.ue(s), St.State.ues(st)) == Some{ue} : Maybe<&2, St.Ue>} -> {St.Phase.ctx(St.Ue.phase(ue)) == Some{ctx} : Maybe<&2, N.Nas.Ctx>} -> Gs.Gsm.tells_gnb(ue, ctx, s, Ke.Kernel.actions(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)))))
    & (({St.Session.phase(s) == St.Creating{guard, pti, accept, request} : St.SPhase} -> {U32.is_lt(St.Guard.retries(guard), Up.N4.n1()) == False{} : Bool} -> {Tb.Table.get(St.Session, skey, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)))) == None{} : Maybe<&2, St.Session>})
    & ({St.Session.phase(s) == St.Modifying{guard, request} : St.SPhase} -> {U32.is_lt(St.Guard.retries(guard), Up.N4.n1()) == False{} : Bool} -> {St.Sessions.each(skey, St.SFresh{}, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)))) == True{} : Bool} & Up.N4.deleted(skey, s, Ke.Kernel.actions(Ke.Kernel.step(st, F.TimerFired{skey}, entropy))) & ({Tb.Table.get(St.Ue, St.Session.ue(s), St.State.ues(st)) == Some{ue} : Maybe<&2, St.Ue>} -> {St.Phase.ctx(St.Ue.phase(ue)) == Some{ctx} : Maybe<&2, N.Nas.Ctx>} -> Gs.Gsm.tells_gnb(ue, ctx, s, Ke.Kernel.actions(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)))))))
  & (({Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)} -> {Pf.Msg.kind(msg) == 53 : U32} -> {St.Sessions.by_seq(Pf.Msg.seq(msg), St.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => St.Session>>} -> {St.Session.phase(s) == St.Modifying{guard, request} : St.SPhase} -> {Up.N4.accepted(Up.N4.cause(msg)) == False{} : Bool}
    -> {St.Sessions.each(skey, St.SFresh{}, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.PfcpData{len, bytes}, entropy)))) == True{} : Bool} & Up.N4.deleted(skey, s, Ke.Kernel.actions(Ke.Kernel.step(st, F.PfcpData{len, bytes}, entropy))) & ({Tb.Table.get(St.Ue, St.Session.ue(s), St.State.ues(st)) == Some{ue} : Maybe<&2, St.Ue>} -> {St.Phase.ctx(St.Ue.phase(ue)) == Some{ctx} : Maybe<&2, N.Nas.Ctx>} -> Gs.Gsm.tells_gnb(ue, ctx, s, Ke.Kernel.actions(Ke.Kernel.step(st, F.PfcpData{len, bytes}, entropy)))))
  & ({St.Assocs.has(assoc, St.State.assocs(st)) == True{} : Bool} -> {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 29, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)} -> {GV.PDUSessionResourceSetupResponse.view(ies) == Done{GV.PDUSessionResourceSetupResponse.View{amf, ran, oks, Some{List.append(&2, G.PDUSessionResourceFailedToSetupItemSURes, pre, G.PDUSessionResourceFailedToSetupItemSURes{psi, transfer, x} <> post)}, diag, uli}} : Result<&2, &2, B.Err, GV.PDUSessionResourceSetupResponse.View>} -> {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>} -> {Ng.Owner.of(Tb.Table.get(St.Ue, k, St.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, St.Ue>} -> {St.Sessions.by_psi(k, psi, St.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => St.Session>>} -> {St.Session.phase(s) == St.Setting{guard, pti} : St.SPhase}
    -> {St.Sessions.each(skey, St.SFresh{}, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == True{} : Bool} & Up.N4.deleted(skey, s, Ke.Kernel.actions(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))
  & ({St.Assocs.has(assoc, St.State.assocs(st)) == True{} : Bool} -> {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 29, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)} -> {GV.PDUSessionResourceSetupResponse.view(ies) == Done{GV.PDUSessionResourceSetupResponse.View{amf, ran, Some{List.append(&2, G.PDUSessionResourceSetupItemSURes, opre, G.PDUSessionResourceSetupItemSURes{psi, transfer, x} <> opost)}, fl, diag, uli}} : Result<&2, &2, B.Err, GV.PDUSessionResourceSetupResponse.View>} -> {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>} -> {Ng.Owner.of(Tb.Table.get(St.Ue, k, St.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, St.Ue>} -> {Gs.Gsm.named(psi, opost) == False{} : Bool} -> {Gs.Gsm.tunnel_of(G.PDUSessionResourceSetupResponseTransfer.read(Ap.Cur{0n, Ap.unpack(transfer)})) == None{} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>} -> {St.Sessions.by_psi(k, psi, St.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => St.Session>>} -> {St.Session.phase(s) == St.Setting{guard, pti} : St.SPhase}
    -> Up.N4.deleted(skey, s, Ke.Kernel.actions(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) & ({St.Phase.ctx(St.Ue.phase(ue)) == Some{ctx} : Maybe<&2, N.Nas.Ctx>} -> Gs.Gsm.told_gnb(ue, k, N.Nas.Ctx.keys(ctx), s, Ke.Kernel.actions(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))))))

# What the release messages are, so that the laws naming them
# (smf.establish.failure_releases, amf.path_switch.stored_capabilities,
# amf.handover.notify_releases) keep their meaning: the PDU Session Resource
# Release Command to a UE's gNB (Gs.Gsm.n2_release), and the PDU Session
# Release Commands in DL NAS Transport for the sessions a handover releases
# (Gs.Gsm.releases). Each holds PDU Session Release Command #26 sealed under
# the downlink COUNT of the context given, and leaves the context with the
# next COUNT: none for no session, the first session's under the context's
# COUNT and the rest's from the next, the context they leave last.
law smf.releases.sent:
  for +key: U32
  for +assoc: U32
  for +stream: U32
  for +ran: B.Bytes()
  for +p: U32
  for +more: List<&2, U32>
  for +ctx: N.Nas.Ctx
  for +keys: N.Nas.Keys
  for +dl: N.Nas.Count
  for +ul: Maybe<&2, N.Nas.Count>
  for +ue: St.Ue
  {Gs.Gsm.releases(key, assoc, stream, ran, [], ctx) == (ctx, []) : Sigma<&2, &2, N.Nas.Ctx, _ => List<&2, Ng.Act>>}
  & {Gs.Gsm.releases(key, assoc, stream, ran, p <> more, N.Ctx{keys, dl, ul}) == (Gs.Gsm.Told.ctx(Gs.Gsm.releases(key, assoc, stream, ran, more, N.Ctx{keys, N.Nas.Count.next(dl), ul})), Ng.DlNas{assoc, stream, key, ran, N.Nas.seal(keys, N.Ciphered{}, N.Nas.downlink(), dl, Gs.Gsm.dl_transport(p, Gs.Gsm.release_command(p)))} <> Gs.Gsm.Told.acts(Gs.Gsm.releases(key, assoc, stream, ran, more, N.Ctx{keys, N.Nas.Count.next(dl), ul}))) : Sigma<&2, &2, N.Nas.Ctx, _ => List<&2, Ng.Act>>}
  & {Gs.Gsm.n2_release(key, ue, N.Ctx{keys, dl, ul}, p) == (St.Rephase{key, St.Phase.with_ctx(St.Ue.phase(ue), N.Ctx{keys, N.Nas.Count.next(dl), ul})}, [Ng.PduRelease{St.Ue.assoc(ue), St.Ue.stream(ue), key, St.Ue.ran_id(ue), p, N.Nas.seal(keys, N.Ciphered{}, N.Nas.downlink(), dl, Gs.Gsm.dl_transport(p, Gs.Gsm.release_command(p)))}]) : Ng.GOut()}
  & {Ng.Act.render(Ng.PduRelease{St.Ue.assoc(ue), St.Ue.stream(ue), key, St.Ue.ran_id(ue), p, N.Nas.seal(keys, N.Ciphered{}, N.Nas.downlink(), dl, Gs.Gsm.dl_transport(p, Gs.Gsm.release_command(p)))}) == Ng.Act.render(Ng.UeSend{St.Ue.assoc(ue), St.Ue.stream(ue), key, Ng.Ngap.pdu_release(key, St.Ue.ran_id(ue), p, N.Nas.seal(keys, N.Ciphered{}, N.Nas.downlink(), dl, Gs.Gsm.dl_transport(p, Gs.Gsm.release_command(p))), Ng.Ngap.misc(G.CauseMisc.unspecified()))}) : F.Action}

# TS 38.413 §8.2.2.2: the gNB's PDU Session Resource Release Response answers
# a Command whose sessions the step that sent it already deleted at the UPF.
# Whatever it names and whoever sends it, it changes no state.
law smf.release_response.keeps_state:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 28, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State}

# TS 29.244 §6.4: a Session Establishment or Modification Request still
# unanswered when the session's guard fires, before it has gone N1 times
# again, goes again unchanged, its sequence number included, under the guard
# started again; the session stays, its guard counting one more
# retransmission (smf.establish.failure_releases says what the next expiry does).
law smf.request.retransmitted:
  for +st: St.State
  for +entropy: B.Bytes()
  for +skey: U32
  for +s: St.Session
  for +guard: St.Guard
  for +pti: U32
  for +accept: Sm.Sm
  for +request: B.Bytes()
  for +et: {Tb.Table.get(St.Ue, skey, St.State.ues(st)) == None{} : Maybe<&2, St.Ue>}
  for +es: {Tb.Table.get(St.Session, skey, St.State.sessions(st)) == Some{s} : Maybe<&2, St.Session>}
  for +er: {U32.is_lt(St.Guard.retries(guard), Up.N4.n1()) == True{} : Bool}
  ({St.Session.phase(s) == St.Creating{guard, pti, accept, request} : St.SPhase} -> {Tb.Table.get(St.Session, skey, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)))) == Some{St.Session.with_var(s, St.SVar{St.Session.up_seid(s), St.Session.seq(s), St.Creating{St.Guard{U32.add(St.Guard.retries(guard), 1)}, pti, accept, request}})} : Maybe<&2, St.Session>} & {Ke.Kernel.actions(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)) == [Ng.Pfcp{Some{St.Session.ue(s)}, request}, Ng.TimerStart{Some{St.Session.ue(s)}, skey, Up.N4.t1_ms()}] : List<&2, Ng.Act>})
  & ({St.Session.phase(s) == St.Modifying{guard, request} : St.SPhase} -> {Tb.Table.get(St.Session, skey, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)))) == Some{St.Session.with_var(s, St.SVar{St.Session.up_seid(s), St.Session.seq(s), St.Modifying{St.Guard{U32.add(St.Guard.retries(guard), 1)}, request}})} : Maybe<&2, St.Session>} & {Ke.Kernel.actions(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)) == [Ng.Pfcp{Some{St.Session.ue(s)}, request}, Ng.TimerStart{Some{St.Session.ue(s)}, skey, Up.N4.t1_ms()}] : List<&2, Ng.Act>})

# TS 29.244 §6.4: a session being deleted whose guard fires before its
# Session Deletion Request has gone N1 times again sends the request again
# unchanged, its sequence number included, under its guard started again,
# tagged with no UE, as its UE may be gone; the row stays, its guard counting
# one more retransmission. At the next expiry the deletion is given up: the
# row goes, freeing its address, TEID and SEID, and its guard is stopped.
# Every Session Deletion Request leaves its session being deleted under it
# (Up.N4.deletions) until the UPF answers (smf.deletion.answered).
law smf.deletion.retransmitted:
  for +st: St.State
  for +entropy: B.Bytes()
  for +skey: U32
  for +s: St.Session
  for +guard: St.Guard
  for +request: B.Bytes()
  for +et: {Tb.Table.get(St.Ue, skey, St.State.ues(st)) == None{} : Maybe<&2, St.Ue>}
  for +es: {Tb.Table.get(St.Session, skey, St.State.sessions(st)) == Some{s} : Maybe<&2, St.Session>}
  for +ep: {St.Session.phase(s) == St.Deleting{guard, request} : St.SPhase}
  ({U32.is_lt(St.Guard.retries(guard), Up.N4.n1()) == True{} : Bool} -> {Tb.Table.get(St.Session, skey, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)))) == Some{St.Session.with_var(s, St.SVar{St.Session.up_seid(s), St.Session.seq(s), St.Deleting{St.Guard{U32.add(St.Guard.retries(guard), 1)}, request}})} : Maybe<&2, St.Session>} & {Ke.Kernel.actions(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)) == [Ng.Pfcp{None{}, request}, Ng.TimerStart{None{}, skey, Up.N4.t1_ms()}] : List<&2, Ng.Act>})
  & ({U32.is_lt(St.Guard.retries(guard), Up.N4.n1()) == False{} : Bool} -> {Tb.Table.get(St.Session, skey, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{skey}, entropy)))) == None{} : Maybe<&2, St.Session>} & {Ng.Acts.stops(skey, Ke.Kernel.actions(Ke.Kernel.step(st, F.TimerFired{skey}, entropy))) == True{} : Bool})

# A Session Deletion Response with the sequence number of a session being
# deleted ends the deletion: the row goes, freeing its address, TEID and SEID,
# and its guard is stopped.
law smf.deletion.answered:
  for +st: St.State
  for +entropy: B.Bytes()
  for +len: U32
  for +bytes: B.Bytes()
  for +msg: Pf.Msg
  for +rest: B.Bytes()
  for +skey: U32
  for +s: St.Session
  for +guard: St.Guard
  for +request: B.Bytes()
  for +em: {Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)}
  for +ek: {Pf.Msg.kind(msg) == 55 : U32}
  for +es: {St.Sessions.by_seq(Pf.Msg.seq(msg), St.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => St.Session>>}
  for +ep: {St.Session.phase(s) == St.Deleting{guard, request} : St.SPhase}
  {Tb.Table.get(St.Session, skey, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.PfcpData{len, bytes}, entropy)))) == None{} : Maybe<&2, St.Session>} & {Ng.Acts.stops(skey, Ke.Kernel.actions(Ke.Kernel.step(st, F.PfcpData{len, bytes}, entropy))) == True{} : Bool}

# A session being deleted stays as it is until its guard fires or the UPF
# answers its Session Deletion Request (smf.deletion.retransmitted,
# smf.deletion.answered): no other step changes or forgets its row, so no
# other session is given its address, TEID or SEID while the UPF may still
# hold them, nor starts or stops its guard, so one of the two comes within
# T1. It holds in every state where no two sessions share a key or an
# identity (smf.ip_pool.unique) and the session's key is neither a context's,
# nor the one a new context takes, nor the PFCP association's timer: those
# are odd (state.ids.free; a new context's by St.Ues.free_key) or 0, a
# session's even and not 0 (state.ids.free).
law smf.deletion.held:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +skey: U32
  for +s: St.Session
  for +guard: St.Guard
  for +request: B.Bytes()
  for +eu: {St.Sessions.unique(St.State.sessions(st)) == True{} : Bool}
  for +en: {Tb.Table.get(St.Ue, skey, St.State.ues(st)) == None{} : Maybe<&2, St.Ue>}
  for +ef: {St.Maybe.same_u32(St.State.fresh(st), Some{skey}) == False{} : Bool}
  for +ez: {U32.is_eq(skey, St.N4.timer()) == False{} : Bool}
  for +es: {Tb.Table.get(St.Session, skey, St.State.sessions(st)) == Some{s} : Maybe<&2, St.Session>}
  for +ep: {St.Session.phase(s) == St.Deleting{guard, request} : St.SPhase}
  for et: {ev == F.TimerFired{skey} : F.Evt} -> Empty
  for ea: @len:U32 -> @bytes:B.Bytes() -> @msg:Pf.Msg -> @rest:B.Bytes() -> {ev == F.PfcpData{len, bytes} : F.Evt} -> {Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)} -> {Pf.Msg.kind(msg) == 55 : U32} -> {St.Sessions.by_seq(Pf.Msg.seq(msg), St.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => St.Session>>} -> Empty
  {Tb.Table.get(St.Session, skey, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == Some{s} : Maybe<&2, St.Session>} & {Ng.Acts.touches(skey, Ke.Kernel.actions(Ke.Kernel.step(st, ev, entropy))) == False{} : Bool}

# Whatever starts deleting a session (its release, its UE's, an eviction, an
# association going down or its NG Setup, a failure: Up.N4.deletions) leaves it being deleted
# under a guard that has not fired, sends its Session Deletion Request and
# leaves its guard running for T1: with smf.deletion.held,
# smf.deletion.retransmitted and smf.deletion.answered, the row goes within
# (N1 + 1) x T1. It holds in every state where the session's key is neither a
# context's, nor the one a new context takes, nor the PFCP association's
# timer, as smf.deletion.held.
law smf.deletion.armed:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +skey: U32
  for +s: St.Session
  for +guard: St.Guard
  for +request: B.Bytes()
  for +en: {Tb.Table.get(St.Ue, skey, St.State.ues(st)) == None{} : Maybe<&2, St.Ue>}
  for +ef: {St.Maybe.same_u32(St.State.fresh(st), Some{skey}) == False{} : Bool}
  for +ez: {U32.is_eq(skey, St.N4.timer()) == False{} : Bool}
  for +eh: {St.Sessions.each(skey, St.SLive{}, St.State.sessions(st)) == True{} : Bool}
  for +es: {Tb.Table.get(St.Session, skey, St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == Some{s} : Maybe<&2, St.Session>}
  for +ep: {St.Session.phase(s) == St.Deleting{guard, request} : St.SPhase}
  {guard == St.Guard{0} : St.Guard} & ({Ng.Acts.sends(request, Ke.Kernel.actions(Ke.Kernel.step(st, ev, entropy))) == True{} : Bool} & {Ng.Acts.runs(skey, Up.N4.t1_ms(), Ke.Kernel.actions(Ke.Kernel.step(st, ev, entropy))) == True{} : Bool})

# The UPF knows every session past Creating, by the UP SEID it answered with,
# and none being created, in the initial state and after every step.
law smf.sessions.known:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +e: {St.Sessions.known(St.State.sessions(st)) == True{} : Bool}
  {St.Sessions.known(St.State.sessions(St.State.initial())) == True{} : Bool}
  & {St.Sessions.known(St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == True{} : Bool}

# GHSA-x8ww-5xvf-qxg6: a PDU Session Modification Request gets Modification
# Reject #31; the sessions are as they were. A later milestone that offers
# modification must replace this law with one stating that contradictory
# directives are rejected.
law smf.modification.rejected:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +k: U32
  for +ran: B.Bytes()
  for +nas: B.Bytes()
  for +uli: G.UserLocationInformation
  for +ue: St.Ue
  for +ctx: N.Nas.Ctx
  for +prot: N.Nas.Protection
  for +plain: B.Bytes()
  for +count: N.Nas.Count
  for +ctx2: N.Nas.Ctx
  for +old: N.Nas.Ctx
  for +nh: St.Nh
  for +released: Maybe<&2, St.Side>
  for +fields: List<&2, I.Field>
  for +opts: List<&2, I.Ie>
  for +psi: U32
  for +pti: U32
  for +sfields: List<&2, I.Field>
  for +sopts: List<&2, I.Ie>
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ev: {GV.UplinkNASTransport.view(ies) == Done{GV.UplinkNASTransport.View{amf, ran, nas, uli}} : Result<&2, &2, B.Err, GV.UplinkNASTransport.View>}
  for +eid: {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}
  for +eo: {Gm.Gmm.owner(st, assoc, k, ran) == Some{ue} : Maybe<&2, St.Ue>}
  for +ec: {St.Phase.ctx(St.Ue.phase(ue)) == Some{ctx} : Maybe<&2, N.Nas.Ctx>}
  for +eu: {N.Nas.unprotect(ctx, nas) == Done{N.Unprotected{prot, plain, count, ctx2}} : Result<&2, &2, B.Err, N.Nas.Unprotected>}
  for +em: {Mm.Mm.read(plain) == Done{Mm.Mm{Mm.UlNasTransport{}, fields, opts}} : Result<&2, &2, B.Err, Mm.Mm>}
  for +er: {St.Ue.phase(ue) == St.Registered{old, nh, released} : St.Phase}
  for +en: {U32.is_eq(I.Fields.byte1(fields), 1) == True{} : Bool}
  for +es: {Sm.Sm.read(I.Fields.lve2(fields)) == Done{Sm.Sm{psi, pti, Sm.ModificationRequest{}, sfields, sopts}} : Result<&2, &2, B.Err, Sm.Sm>}
  for +eup: {St.Assocs.has(assoc, St.State.assocs(st)) == True{} : Bool}
  {St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == St.State.sessions(st) : Tb.Table(St.Session)}
  & {Ke.Kernel.actions(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == [Ng.DlNas{St.Ue.assoc(ue), St.Ue.stream(ue), k, St.Ue.ran_id(ue), N.Nas.Protected.msg(N.Nas.protect(ctx2, N.Ciphered{}, Gs.Gsm.dl_transport(psi, Gs.Gsm.modification_reject(psi, pti))))}] : List<&2, Ng.Act>}

# GHSA-g97g-v8mh-wg24: the Accept every session holds while the UPF creates it,
# its QoS rules read as the UE reads them, carries at most sixteen packet
# filters, in the initial state and after every step; modification, the only
# way to add filters, is rejected (smf.modification.rejected).
law smf.packet_filters.capacity_reject:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +e: {Gs.Gsm.bounded(St.State.sessions(st)) == True{} : Bool}
  {Gs.Gsm.bounded(St.State.sessions(St.State.initial())) == True{} : Bool}
  & {Gs.Gsm.bounded(St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == True{} : Bool}

# GHSA-f77j-h86j-2vcf: the ePCO of an Accept holds each container identifier at
# most once, however many times the request repeats it.
law smf.epco.response_bounded:
  for +cfg: St.Cfg
  for +wanted: Bool
  {Gs.Gsm.ids_unique(Gs.Gsm.epco_containers(cfg, wanted)) == True{} : Bool}

# GHSA-796x-8w26-2xfp: the ePCO of an Accept is valid (each container's length
# byte is its content's length; at most 255 containers in at most 65534 octets)
# for every configuration the kernel holds (kernel.config.valid), so
# nas.epco.encode_bounded covers it.
law smf.epco.accept_valid:
  for +cfg: St.Cfg
  for +wanted: Bool
  for +e: {St.Cfg.valid(cfg) == True{} : Bool}
  {Q.Epco.valid(Q.Epco{Gs.Gsm.epco_containers(cfg, wanted)}) == True{} : Bool}

# No two sessions share a UE IPv4 address or an uplink TEID, a session being
# deleted included, nor a key, nor two sessions of one UE a PDU session
# identity (a session being deleted belongs to no UE), in the initial state
# and after every step.
law smf.ip_pool.unique:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +e: {St.Sessions.unique(St.State.sessions(st)) == True{} : Bool}
  {St.Sessions.unique(St.State.sessions(St.State.initial())) == True{} : Bool}
  & {St.Sessions.unique(St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))) == True{} : Bool}

# No two sessions of a table where Sessions.unique holds (every table a step
# reaches, smf.ip_pool.unique) share an uplink TEID.
law smf.teid.unique:
  for +ss: Tb.Table(St.Session)
  for +k1: U32
  for +s1: St.Session
  for +k2: U32
  for +s2: St.Session
  for +e: {St.Sessions.unique(ss) == True{} : Bool}
  for +e1: {Tb.Table.get(St.Session, k1, ss) == Some{s1} : Maybe<&2, St.Session>}
  for +e2: {Tb.Table.get(St.Session, k2, ss) == Some{s2} : Maybe<&2, St.Session>}
  for +ne: {U32.is_eq(k1, k2) == False{} : Bool}
  {U32.is_eq(St.Session.teid(s1), St.Session.teid(s2)) == False{} : Bool}

# amf (ticket 27)
# ---------------
# Xn handover: Path Switch (TS 23.502 §4.9.1.2.2, TS 38.413 §8.4.4). By
# design there is no owner check: any gNB with NG Setup done may claim a
# registered UE by its AMF-UE-NGAP-ID (loop/decisions.md).

# A Path Switch Request answered with Path Switch Request Failure changes no
# state: every failure comes before any PFCP request (the UE unknown or not
# registered, the RAN-UE-NGAP-ID taken on the gNB, no session the request
# names that can be switched). A gNB without NG Setup is refused before
# (amf.ng_setup.first).
law amf.path_switch.failure_leaves_state:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 25, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ef: {Ng.Ngap.any_switch_failure(Ke.Kernel.actions(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == True{} : Bool}
  {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State}

# After a Path Switch Request, the context it names is as it was, or owned by
# the requesting association under the RAN-UE-NGAP-ID the request gives. It
# is one row, so no other association owns the UE, and the switch completes
# for that row: the acknowledgement goes to its owner (Gs.Gsm.switch_end).
law amf.path_switch.moves_owner:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +ran: B.Bytes()
  for +amf: B.Bytes()
  for +uli: G.UserLocationInformation
  for +caps: G.UESecurityCapabilities
  for +items: G.PDUSessionResourceToBeSwitchedDLList()
  for +failed: Maybe<&2, G.PDUSessionResourceFailedToSetupListPSReq()>
  for +rrc: Maybe<&2, G.RRCEstablishmentCause()>
  for +k: U32
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 25, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ev: {GV.PathSwitchRequest.view(ies) == Done{GV.PathSwitchRequest.View{ran, amf, uli, caps, items, failed, rrc}} : Result<&2, &2, B.Err, GV.PathSwitchRequest.View>}
  for +eid: {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}
  {Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == Tb.Table.get(St.Ue, k, St.State.ues(st)) : Maybe<&2, St.Ue>}
  | ({Tb.Table.has(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == True{} : Bool}
  & {Ng.Owner.of(Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))), assoc, ran) == Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) : Maybe<&2, St.Ue>})

# TS 33.501 §6.7.3.1: the UE security capabilities a Path Switch Request
# carries are only compared with the stored ones. Two requests that differ in
# nothing else leave the same state, and the acknowledgement, built from the
# context the state holds, carries the capabilities of the Registration
# Request stored for it. After it, the UE is sent PDU Session Release Command
# for each session released (Gs.Gsm.releases), its NAS context moving on.
law amf.path_switch.stored_capabilities:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len1: U32
  for +bytes1: B.Bytes()
  for +crit1: U32
  for +value1: B.Bytes()
  for +ies1: List<&2, Fr.Ie>
  for +c1: Ap.Cur
  for +len2: U32
  for +bytes2: B.Bytes()
  for +crit2: U32
  for +value2: B.Bytes()
  for +ies2: List<&2, Fr.Ie>
  for +c2: Ap.Cur
  for +ran: B.Bytes()
  for +amf: B.Bytes()
  for +uli: G.UserLocationInformation
  for +caps1: G.UESecurityCapabilities
  for +caps2: G.UESecurityCapabilities
  for +items: G.PDUSessionResourceToBeSwitchedDLList()
  for +failed: Maybe<&2, G.PDUSessionResourceFailedToSetupListPSReq()>
  for +rrc: Maybe<&2, G.RRCEstablishmentCause()>
  for +key: U32
  for +ue: St.Ue
  for +ctx: N.Nas.Ctx
  for +nh: St.Nh
  for +released: List<&2, U32>
  for +p: U32
  for +more: List<&2, U32>
  for +cfg: St.Cfg
  for +ep1: {Fr.Pdu.read(bytes1) == Done{Fr.Pdu{0, 25, crit1, value1}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei1: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value1), 1n)}) == Done{(ies1, c1)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ev1: {GV.PathSwitchRequest.view(ies1) == Done{GV.PathSwitchRequest.View{ran, amf, uli, caps1, items, failed, rrc}} : Result<&2, &2, B.Err, GV.PathSwitchRequest.View>}
  for +ep2: {Fr.Pdu.read(bytes2) == Done{Fr.Pdu{0, 25, crit2, value2}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei2: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value2), 1n)}) == Done{(ies2, c2)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ev2: {GV.PathSwitchRequest.view(ies2) == Done{GV.PathSwitchRequest.View{ran, amf, uli, caps2, items, failed, rrc}} : Result<&2, &2, B.Err, GV.PathSwitchRequest.View>}
  {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len1, bytes1}, entropy)) == Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len2, bytes2}, entropy)) : St.State}
  & {Gs.Gsm.switch_end(key, ue, ctx, nh, released, p <> more, Some{cfg}) == (St.Rephase{key, St.Registered{Gs.Gsm.Told.ctx(Gs.Gsm.releases(key, St.Ue.assoc(ue), St.Ue.stream(ue), St.Ue.ran_id(ue), released, ctx)), nh, None{}}}, Ng.SwitchAck{St.Ue.assoc(ue), St.Ue.stream(ue), key, St.Ue.ran_id(ue), Ng.Ue.caps(ue), nh, p <> more, released, St.Cfg.sst(cfg)} <> List.append(&2, Ng.Act, Gs.Gsm.Told.acts(Gs.Gsm.releases(key, St.Ue.assoc(ue), St.Ue.stream(ue), St.Ue.ran_id(ue), released, ctx)), [Ng.TimerCancel{key}, Ng.Note{F.Info{}, "NGAP: Path Switch done"}])) : Ng.GOut()}

# amf (ticket 28)
# ---------------
# N2 handover (TS 23.502 §4.9.1.3, TS 38.413 §8.4.1 to §8.4.3, §8.4.5 to
# §8.4.7). The target knows the UE by its AMF-UE-NGAP-ID too; the UE stays
# with its owner, the source, until the target's Handover Notify.

# GHSA-wpwr-xj64-h6cp: Handover Required, Handover Cancel and Uplink RAN
# Status Transfer change state only when they come from the UE's owner, under
# its RAN-UE-NGAP-ID there; Handover Request Acknowledge, Handover Failure and
# Handover Notify only when they come from the target of the UE's pending
# handover.
law amf.handover.owner_only:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +ran: B.Bytes()
  for +k: U32
  for +kind: G.HandoverType()
  for +cause: G.Cause
  for +id: G.TargetID
  for +direct: Maybe<&2, G.DirectForwardingPathAvailability()>
  for +items: G.PDUSessionResourceListHORqd()
  for +container: B.Bytes()
  for +status: G.RANStatusTransfer_TransparentContainer
  for +admitted: G.PDUSessionResourceAdmittedList()
  for +failed: Maybe<&2, G.PDUSessionResourceFailedToSetupListHOAck()>
  for +back: B.Bytes()
  for +diag: Maybe<&2, G.CriticalityDiagnostics>
  for +npn: Maybe<&2, G.NPN_AccessInformation>
  for +uli: G.UserLocationInformation
  for +eid: {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  ({Ng.Owner.of(Tb.Table.get(St.Ue, k, St.State.ues(st)), assoc, ran) == None{} : Maybe<&2, St.Ue>} ->
    ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 12, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.HandoverRequired.view(ies) == Done{GV.HandoverRequired.View{amf, ran, kind, cause, id, direct, items, container}} : Result<&2, &2, B.Err, GV.HandoverRequired.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State})
    & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 10, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.HandoverCancel.view(ies) == Done{GV.HandoverCancel.View{amf, ran, cause}} : Result<&2, &2, B.Err, GV.HandoverCancel.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State})
    & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 49, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.UplinkRANStatusTransfer.view(ies) == Done{GV.UplinkRANStatusTransfer.View{amf, ran, status}} : Result<&2, &2, B.Err, GV.UplinkRANStatusTransfer.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State}))
  & ({St.Maybe.same_u32(St.Ue.pending(Tb.Table.get(St.Ue, k, St.State.ues(st))), Some{assoc}) == False{} : Bool} ->
    ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.HandoverRequestAcknowledge.view(ies) == Done{GV.HandoverRequestAcknowledge.View{amf, ran, admitted, failed, back, diag, npn}} : Result<&2, &2, B.Err, GV.HandoverRequestAcknowledge.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State})
    & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{2, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.HandoverFailure.view(ies) == Done{GV.HandoverFailure.View{amf, cause, diag}} : Result<&2, &2, B.Err, GV.HandoverFailure.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State})
    & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 11, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.HandoverNotify.view(ies) == Done{GV.HandoverNotify.View{amf, ran, uli}} : Result<&2, &2, B.Err, GV.HandoverNotify.View>} -> {Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : St.State}))

# GHSA-v6fv-hmw8-6ffv: a Handover Request Acknowledge, Handover Failure or
# Handover Notify for a UE with no handover pending, as after a cancel or the
# guard firing (amf.handover.guarded), changes no state: the only actions are
# Error Indication and a log line, so no PFCP message goes out. After a
# Handover Cancel from the UE's owner no handover is pending. A Handover
# Required from the owner to a target its last handover released before the
# target answered is refused with Handover Preparation Failure and changes no
# state, so an answer to that attempt crossing the cancel is never taken for
# a new one's.
law amf.handover.responses_correlated:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +ran: B.Bytes()
  for +k: U32
  for +u: St.Ue
  for +cause: G.Cause
  for +admitted: G.PDUSessionResourceAdmittedList()
  for +failed: Maybe<&2, G.PDUSessionResourceFailedToSetupListHOAck()>
  for +back: B.Bytes()
  for +diag: Maybe<&2, G.CriticalityDiagnostics>
  for +npn: Maybe<&2, G.NPN_AccessInformation>
  for +uli: G.UserLocationInformation
  for +kind: G.HandoverType()
  for +hcause: G.Cause
  for +id: G.TargetID
  for +direct: Maybe<&2, G.DirectForwardingPathAvailability()>
  for +items: G.PDUSessionResourceListHORqd()
  for +container: B.Bytes()
  for +ctx: N.Nas.Ctx
  for +nh: St.Nh
  for +t: U32
  for +eid: {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +eup: {St.Assocs.has(assoc, St.State.assocs(st)) == True{} : Bool}
  ({St.Ue.pending(Tb.Table.get(St.Ue, k, St.State.ues(st))) == None{} : Maybe<&2, U32>} ->
    ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.HandoverRequestAcknowledge.view(ies) == Done{GV.HandoverRequestAcknowledge.View{amf, ran, admitted, failed, back, diag, npn}} : Result<&2, &2, B.Err, GV.HandoverRequestAcknowledge.View>} -> {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.unknown_ue(assoc)) : Ng.Step()})
    & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{2, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.HandoverFailure.view(ies) == Done{GV.HandoverFailure.View{amf, cause, diag}} : Result<&2, &2, B.Err, GV.HandoverFailure.View>} -> {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.unknown_ue(assoc)) : Ng.Step()})
    & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 11, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.HandoverNotify.view(ies) == Done{GV.HandoverNotify.View{amf, ran, uli}} : Result<&2, &2, B.Err, GV.HandoverNotify.View>} -> {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, Ng.Ngap.unknown_ue(assoc)) : Ng.Step()}))
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 10, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.HandoverCancel.view(ies) == Done{GV.HandoverCancel.View{amf, ran, cause}} : Result<&2, &2, B.Err, GV.HandoverCancel.View>} -> {Ng.Owner.of(Tb.Table.get(St.Ue, k, St.State.ues(st)), assoc, ran) == Some{u} : Maybe<&2, St.Ue>} -> {St.Ue.pending(Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == None{} : Maybe<&2, U32>})
  & ({St.Ue.phase(u) == St.Registered{ctx, nh, Some{St.Side{t, None{}}}} : St.Phase} -> {Ho.Ho.target(st, Ho.Ho.intra_type(kind), Ho.Ho.node(id)) == Some{t} : Maybe<&2, U32>} -> {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 12, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {GV.HandoverRequired.view(ies) == Done{GV.HandoverRequired.View{amf, ran, kind, hcause, id, direct, items, container}} : Result<&2, &2, B.Err, GV.HandoverRequired.View>} -> {Ng.Owner.of(Tb.Table.get(St.Ue, k, St.State.ues(st)), assoc, ran) == Some{u} : Maybe<&2, St.Ue>} -> {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, [Ho.Ho.preparation_failure(k, u, Ho.Ho.radio(G.CauseRadioNetwork.ho_target_not_allowed())), Ng.Note{F.Warn{}, "NGAP: Handover Required refused"}]) : Ng.Step()})

# At every reachable state each UE is one context, owned by one association:
# no two contexts share a key or an identity. A pending handover names its
# target but never transfers ownership before Handover Notify: in every
# reachable state a context with a pending handover is owned by the source it
# started from, which is not its target, whatever event the step takes.
# Besides, Handover Required, Handover Request Acknowledge, Handover Failure,
# Handover Cancel and Uplink RAN Status Transfer, and the guard of a pending
# handover firing, leave every context owned by the association, and under
# the RAN-UE-NGAP-ID, it had; a Handover Notify moves the UE it names only to
# the target of its pending handover.
law amf.handover.single_owner:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +ran: B.Bytes()
  for +uli: G.UserLocationInformation
  for +j: U32
  for +k: U32
  for +t: U32
  {Bool.and(St.Ues.unique(St.State.ues(St.State.initial())), St.Ues.single(St.State.ues(St.State.initial()))) == True{} : Bool}
  & ({Bool.and(St.Ues.unique(St.State.ues(st)), St.Ues.single(St.State.ues(st))) == True{} : Bool} -> {Bool.and(St.Ues.unique(St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))), St.Ues.single(St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy))))) == True{} : Bool})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 12, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {St.Ue.same_owner(Tb.Table.get(St.Ue, j, St.State.ues(st)), Tb.Table.get(St.Ue, j, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {St.Ue.same_owner(Tb.Table.get(St.Ue, j, St.State.ues(st)), Tb.Table.get(St.Ue, j, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{2, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {St.Ue.same_owner(Tb.Table.get(St.Ue, j, St.State.ues(st)), Tb.Table.get(St.Ue, j, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 10, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {St.Ue.same_owner(Tb.Table.get(St.Ue, j, St.State.ues(st)), Tb.Table.get(St.Ue, j, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 49, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {St.Ue.same_owner(Tb.Table.get(St.Ue, j, St.State.ues(st)), Tb.Table.get(St.Ue, j, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool})
  & ({St.Ue.pending(Tb.Table.get(St.Ue, k, St.State.ues(st))) == Some{t} : Maybe<&2, U32>} -> {St.Ue.same_owner(Tb.Table.get(St.Ue, j, St.State.ues(st)), Tb.Table.get(St.Ue, j, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{k}, entropy))))) == True{} : Bool})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 11, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)} -> {GV.HandoverNotify.view(ies) == Done{GV.HandoverNotify.View{amf, ran, uli}} : Result<&2, &2, B.Err, GV.HandoverNotify.View>} -> {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>} -> {St.Ue.pending(Tb.Table.get(St.Ue, k, St.State.ues(st))) == Some{t} : Maybe<&2, U32>} -> {Bool.or(St.Ue.same_owner(Tb.Table.get(St.Ue, k, St.State.ues(st)), Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))), St.Ue.on(Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))), t)) == True{} : Bool})

# Every pending handover has exactly one running guard timer: in every
# reachable state a context with a pending handover waits under its guard,
# whose timer is the context's key, and no two rows share a guard timer
# (state.ids.free). Handover Required and Handover Request Acknowledge, which
# begin a handover or advance it, start that timer, the preparation guard or
# the completion guard; when it fires, no handover is pending any more. Every
# other way out ends the handover first: the target or source association
# going down or sending NG Setup, the UE released or taken over. So no step
# stops the guard and leaves the handover pending: a step that stops timer
# k, which no session holds (state.ids.free), leaves no handover pending
# under k.
law amf.handover.guarded:
  for +st: St.State
  for +ev: F.Evt
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +k: U32
  for +t: U32
  for +p: St.Phase
  {St.Ues.timed(St.State.ues(St.State.initial())) == True{} : Bool}
  & ({Bool.and(St.Ids.free(St.State.ues(st), St.State.sessions(st)), St.Sessions.owned(St.State.sessions(st), St.State.ues(st))) == True{} : Bool} -> {Bool.and(St.Ues.timed(St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy)))), St.Ids.free(St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy))), St.State.sessions(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy))))) == True{} : Bool})
  & ({St.Phase.pending(p) == Some{t} : Maybe<&2, U32>} -> {Tb.Table.present(St.Guard, St.Phase.guard(p)) == True{} : Bool})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 12, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> ({Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == Tb.Table.get(St.Ue, k, St.State.ues(st)) : Maybe<&2, St.Ue>} -> Empty) -> {Ng.Acts.starts(k, Ke.Kernel.actions(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == True{} : Bool})
  & ({Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>} -> ({Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == Tb.Table.get(St.Ue, k, St.State.ues(st)) : Maybe<&2, St.Ue>} -> Empty) -> {Ng.Acts.starts(k, Ke.Kernel.actions(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == True{} : Bool})
  & ({St.Ue.pending(Tb.Table.get(St.Ue, k, St.State.ues(st))) == Some{t} : Maybe<&2, U32>} -> {St.Ue.pending(Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.TimerFired{k}, entropy))))) == None{} : Maybe<&2, U32>})
  & ({Tb.Table.get(St.Session, k, St.State.sessions(st)) == None{} : Maybe<&2, St.Session>} -> {Ng.Acts.stops(k, Ke.Kernel.actions(Ke.Kernel.step(st, ev, entropy))) == True{} : Bool} -> {St.Ue.pending(Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, ev, entropy))))) == None{} : Maybe<&2, U32>})

# TS 23.502 §4.9.1.3.3: Handover Notify from the target of the handover
# pending, under the RAN-UE-NGAP-ID it acknowledged with and still free on it,
# moves the UE to the target, and the step is exactly this: the UE's PDU
# sessions handed to Sw.Sw.sessions, which repoints those the target admitted
# with an IPv4 tunnel and deletes the others at the UPF; the context put on
# the target; the source told to release the UE; PDU Session Release Command
# to the UE for each session not admitted, in DL NAS Transport through the
# target (§4.3.4.2, Gs.Gsm.releases), the context holding the NAS context
# they leave; the guard stopped; a log line; and the guards of the session
# rows gone stopped (N.Step.of).
law amf.handover.notify_releases:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +ran: B.Bytes()
  for +uli: G.UserLocationInformation
  for +k: U32
  for +ue: St.Ue
  for +ctx: N.Nas.Ctx
  for +nh: St.Nh
  for +source: U32
  for +s: U32
  for +ts: List<&2, St.Tunnel>
  for +sp: B.Digits()
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 11, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ev: {GV.HandoverNotify.view(ies) == Done{GV.HandoverNotify.View{amf, ran, uli}} : Result<&2, &2, B.Err, GV.HandoverNotify.View>}
  for +eid: {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}
  for +eg: {Tb.Table.get(St.Ue, k, St.State.ues(st)) == Some{ue} : Maybe<&2, St.Ue>}
  for +eph: {St.Ue.phase(ue) == St.Handover{ctx, nh, source, St.Acked{assoc, ran, s, ts}} : St.Phase}
  for +es: {St.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>}
  for +eo: {U32.is_eq(St.Ue.assoc(ue), assoc) == False{} : Bool}
  for +ef: {St.Ues.ran_free(k, assoc, ran, St.State.ues(st)) == True{} : Bool}
  for +eup: {St.Assocs.has(assoc, St.State.assocs(st)) == True{} : Bool}
  {Tb.Table.get(St.Ue, k, St.State.ues(Ke.Kernel.state(Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == Some{St.Ue.moved(ue, assoc, ran, s, St.Registered{Gs.Gsm.Told.ctx(Gs.Gsm.releases(k, assoc, s, ran, Sw.Sw.released(ts, St.Sessions.of_ue(k, St.State.sessions(st))), ctx)), nh, Some{St.Side{St.Ue.assoc(ue), Some{St.Ue.ran_id(ue)}}}})} : Maybe<&2, St.Ue>}
  & {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == Ng.Step.of(st, Ng.Out.also(Ng.Out.join(Sw.Sw.sessions(ts, St.Sessions.of_ue(k, St.State.sessions(st)), St.State.pfcp_seq(st)), (St.Put{k, St.Ue.moved(ue, assoc, ran, s, St.Registered{Gs.Gsm.Told.ctx(Gs.Gsm.releases(k, assoc, s, ran, Sw.Sw.released(ts, St.Sessions.of_ue(k, St.State.sessions(st))), ctx)), nh, Some{St.Side{St.Ue.assoc(ue), Some{St.Ue.ran_id(ue)}}}})}, [])), Ng.Release{St.Ue.assoc(ue), St.Ue.stream(ue), k, St.Ue.ran_id(ue), Ho.Ho.radio(G.CauseRadioNetwork.successful_handover())} <> List.append(&2, Ng.Act, Gs.Gsm.Told.acts(Gs.Gsm.releases(k, assoc, s, ran, Sw.Sw.released(ts, St.Sessions.of_ue(k, St.State.sessions(st))), ctx)), [Ng.TimerCancel{k}, Ng.Note{F.Info{}, "NGAP: Handover Notify; the UE moved to the target"}]))) : Ng.Step()}

# TS 38.413 §8.3.3: the side an N2 handover released, the source after
# Handover Notify or the target after a cancel or the guard firing, answers
# its UE Context Release Command with UE Context Release Complete. That
# Complete, from an association that no longer owns the UE, changes no state,
# so no UE changes owner, and its only action is a log line: no Error
# Indication.
law amf.handover.released_side_completes:
  for +st: St.State
  for +entropy: B.Bytes()
  for +assoc: U32
  for +stream: U32
  for +len: U32
  for +bytes: B.Bytes()
  for +crit: U32
  for +value: B.Bytes()
  for +ies: List<&2, Fr.Ie>
  for +c: Ap.Cur
  for +amf: B.Bytes()
  for +k: U32
  for +ran: B.Bytes()
  for +uli: Maybe<&2, G.UserLocationInformation>
  for +rel: Maybe<&2, G.PDUSessionResourceListCxtRelCpl()>
  for +diag: Maybe<&2, G.CriticalityDiagnostics>
  for +ue: St.Ue
  for +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 41, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  for +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}
  for +ev: {GV.UEContextReleaseComplete.view(ies) == Done{GV.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}} : Result<&2, &2, B.Err, GV.UEContextReleaseComplete.View>}
  for +eid: {Ng.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}
  for +eu: {Tb.Table.get(St.Ue, k, St.State.ues(st)) == Some{ue} : Maybe<&2, St.Ue>}
  for +ea: {U32.is_eq(St.Ue.assoc(ue), assoc) == False{} : Bool}
  for +er: {St.Phase.released(St.Ue.phase(ue), assoc, ran) == True{} : Bool}
  for +eup: {St.Assocs.has(assoc, St.State.assocs(st)) == True{} : Bool}
  {Ke.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, [Ng.Note{F.Info{}, "NGAP: UE Context Release Complete from the side a handover released"}]) : Ng.Step()}
