# 26 NH and NCC

Depends on: 07, 24. Estimate: 1–2 h.

## Goal

`kernel/crypto/kdf.bend` gains the NH derivation of TS 33.501 Annex A.10, with FC 0x6F, KAMF and SYNC-input. The UE's security context in `kernel/state.bend` gains NH and NCC, per TS 33.501 §6.9.2.1:

- **Initial values:** KgNB counts as a virtual NH with NCC 0. At Initial Context Setup the AMF derives the first NH from it, with NCC 1, and stores it without sending it (TS 33.501 §6.9.2.1.1, NOTE 3). A handover then raises NCC first, so the first pair a target gNB receives has NCC 2.
- **Each new pair** {NH, NCC} chains NH from the previous NH and increments NCC modulo 8.

## Laws

- `kdf.nh.length`: NH is always 32 bytes.
- `amf.ncc.chain`: every new {NH, NCC} pair derives NH from the stored NH (initially KgNB), and NCC is the previous NCC plus 1 modulo 8. A derivation from an older NH can't be represented.

## Tests

The NH values in the ticket 24 capture, recomputed from its KAMF and KgNB.

## Verify

`scripts/check.sh`
