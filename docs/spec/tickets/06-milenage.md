# 06 Milenage

Depends on: 05.

## Goal

`kernel/crypto/milenage.bend`: f1, f1*, f2, f3, f4, f5, f5* per 3GPP TS 35.206, with OPc given (the subscriber record stores OPc, not OP). Also provide OP→OPc for test vectors.

## Laws

- `milenage.lengths`: MAC-A and MAC-S are 8 bytes, RES 8, CK 16, IK 16, AK 6, for any 16-byte K, OPc and RAND and 6-byte SQN.

## Tests

TS 35.208 test sets 1 to 6. Also check RAND→RES/CK/IK against the captured session in `test-vectors/capture` (K, OPc, RAND).

## Verify

`scripts/check.nu`
