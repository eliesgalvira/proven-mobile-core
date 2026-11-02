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
| 14 | pfcp | done | 02, 03 | d65bfef: TS 29.244 header and IE codec with typed views (Node ID, F-SEID, F-TEID, UE IP, OHC, MBR, Cause and other one-octet IEs); all 20 captured PFCP messages decode, validate and re-encode (90 checks); 7 laws proven incl. the three advisory laws |
| 15 | frames | done | 02 | f0cdd2c: edge/kernel frame codec (envelope, six event kinds with Config TLVs and subscribers, six action kinds with a typed log level); TLV codec and proofs shared with PFCP via kernel/tlv.bend; 31 checks; 6 laws proven (max_length, event roundtrip/decode_valid/suffix, actions roundtrip, config repeat_replaces) |
| 16 | state-ng-setup | done | 13, 15 | 64897b7: State record with U32-keyed tables, Kernel.step over Config (typed Cfg, PFCP Association Setup Request), NGAP associations up/down (releasing UEs and sessions), NG Setup Response matching the capture byte for byte or Failure, Error Indication for undecodable PDUs; 16 checks; 3 laws proven |
| 17 | registration-auth | done | 08, 09, 10, 16 | 9563e69: InitialUEMessage creates a guarded UE context, SUCI deconcealment and subscriber lookup, Identity Request for an unknown 5G-GUTI, AUSF/UDM vector with SQN+32 and AUTS re-synchronisation, Authentication Request/Response/Failure over DL/UL NAS Transport, T3560 retransmission and release; the Authentication Request and KAMF match the capture; 16 checks; 3 laws proven |
| 18 | registration-complete | done | 17 | b869175: NAS security mode (SMC byte for byte, algorithm choice, SM Complete with RINMR), Initial Context Setup with the captured KgNB, Registration Accept with 5G-GUTI from entropy, Complete, deregistration, UE context release, identity takeover; UE procedures as transactions, UE table as one sieve; 32 checks; 5 laws proven |
| 19 | pdu-session | done | 11, 14, 18 | 3df1030: N4 association (T1/N1, pause, heartbeats), PDU Session Establishment over UL NAS Transport with validation and allocation, PFCP Session Establishment/Modification/Deletion to eUPF, PDU Session Resource Setup with the captured transfer byte for byte, Accept with default rule and DNS, failure paths, modification rejected, sessions as identity plus variable part with one sieve; NGAP generator extended with the SMF's IEs; 22 checks; 7 laws proven |
| 20 | kernel-main | done | 15, 19 | 7481566: kernel/main.bend listens on 127.0.0.1, takes one edge and answers every event frame with one Actions frame, echoing Log actions to stderr; protocol errors exit 1; scripts/frame-client.py drives it with Config, NgapAssocUp and the captured NG Setup Request and checks the captured NG Setup Response |
| 21 | edge | in-progress | 15 | |
| 22 | e2e | todo | 20, 21 | |
| 23 | acceptance | todo | 01–22 | |
