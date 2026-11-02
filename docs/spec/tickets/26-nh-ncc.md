# 26 NH and NCC

Depends on: 07, 24. Estimate: 1–2 h.

## Goal

`kernel/crypto/kdf.bend` gains the NH derivation of TS 33.501 Annex A.10, with FC 0x6F, KAMF and SYNC-input. The UE's security context in `kernel/state.bend` gains NH and NCC, per TS 33.501 §6.9.2.1:

- **Initial values:** after Initial Context Setup, KgNB is stored as the initial NH and NCC starts at 0. The first derived NH uses that KgNB as its SYNC-input.
- **Each new pair** {NH, NCC} chains NH from the previous NH and increments NCC modulo 8.

## Laws

- `kdf.nh.length`: NH is always 32 bytes.
- `amf.ncc.chain`: every new {NH, NCC} pair derives NH from the stored NH (initially KgNB), and NCC is the previous NCC plus 1 modulo 8. A derivation from an older NH can't be represented.

## Tests

The NH values in the ticket 24 capture, recomputed from its KAMF and KgNB.

## Verify

`scripts/check.sh`
