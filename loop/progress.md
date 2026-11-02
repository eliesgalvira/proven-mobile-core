# Loop progress

Status values: `todo`, `in-progress`, `done`, `blocked`, `needs-human`. Tickets are in `docs/spec/tickets/`.

| # | Ticket | Status | Depends on | Notes |
|---|---|---|---|---|
| 01 | bootstrap | done | — | 3327ac8: LAWS/PROOF pair, check.sh gate, test runner, acceptance.py, gen-vectors.py and generated vector modules |
| 02 | bytes | done | 01 | 2799d0f: readers u8..u32, take, nibbles, TBCD; 8 laws proven; no U32 lemma file needed |
| 03 | vectors | done | 01 | ad79428: all 9 spec sources present with source fields; generator emits Vec modules; vectors_load smoke test |
| 04 | sha256-hmac | done | 02, 03 | e5369b6: SHA-256 and HMAC; 12+7 vectors pass; 2 laws proven; upstream draft 01 |
| 05 | aes | done | 02, 03 | 5f32c0d: AES-128, CTR, CMAC; 9 vectors pass; 4 laws proven |
| 06 | milenage | done | 05 | b1b468e: f1, f1*, f2..f5*, OP->OPc; 54 checks pass; lengths law proven |
| 07 | kdf | done | 04, 06 | 3641e6d: KDF, SNN, KAUSF..KgNB; capture keys reproduced; 2 laws proven |
| 08 | x25519-suci | done | 04, 05, 07 | 0493397: X25519, PLMN codec, SUCI decode and Profile A; 7 laws proven; upstream draft 02 |
| 09 | nas-security | done | 05, 07 | d62b26a: NIA2, NEA2, NEA0, protect/unprotect, COUNT estimate; 28 checks; 3 laws proven |
| 10 | nas-5gmm | done | 02, 03 | a6e0c85: generic 5GMM codec (19 types), typed IE views incl. 5GS mobile identity; 110 checks on the capture; 10 laws proven (mm roundtrip/decode_valid/suffix, mobile identity ×3, IMEISV, payload container ×2) |
| 11 | nas-5gsm | done | 10 | e46170b: 5GSM codec (9 types) sharing the 5GMM optional-IE machinery; typed QoS rules, packet filters, flow descriptions, Session-AMBR, PDU address, ePCO; 43 checks; 8 laws proven (sm ×3, qos_rules.suffix, mask_contiguous, session_ambr, epco ×2) |
| 12 | aper | done | 02 | d10b54a: X.691 aligned PER primitives (bits, alignment, constrained/indefinite/small numbers, lengths, sizes, octets, bit/octet/printable strings, open types, enumerations) over a bit-list cursor; 55 checks incl. the IE walk over all 14 captured NGAP PDUs; 36 laws proven; padding_zero kept strict |
| 13 | ngap | done | 03, 12 | 1358d02: generator over TS 38.413 V17.15.0 (pycrate 0.8.1) emitting 140 types with read/write/after/valid, per-message views with criticality handling, and 420 laws (roundtrip, decode_valid, suffix) with their proofs; frame codec and 10 hand-written laws; pycrate differential oracle agrees on all 14 captured PDUs; golden test; upstream draft 04 |
| 14 | pfcp | in-progress | 02, 03 | |
| 15 | frames | todo | 02 | |
| 16 | state-ng-setup | todo | 13, 15 | |
| 17 | registration-auth | todo | 08, 09, 10, 16 | |
| 18 | registration-complete | todo | 17 | |
| 19 | pdu-session | todo | 11, 14, 18 | |
| 20 | kernel-main | todo | 15, 19 | |
| 21 | edge | todo | 15 | |
| 22 | e2e | todo | 20, 21 | |
| 23 | acceptance | todo | 01–22 | |
