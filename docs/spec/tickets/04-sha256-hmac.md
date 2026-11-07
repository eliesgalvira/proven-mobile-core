# 04 SHA-256 and HMAC-SHA-256

Depends on: 02, 03.

## Goal

`kernel/crypto/sha256.bend` (FIPS 180-4) and `kernel/crypto/hmac.bend` (RFC 2104 over SHA-256), on byte lists.

## Laws

- `sha256.length`: the output is always 32 bytes.
- `hmac.length`: the output is always 32 bytes, for any key and message length (including keys longer than 64 bytes).

Correctness against the standard is established by the vectors, not by proof.

## Tests

`kernel/tests/sha256.bend`, `kernel/tests/hmac.bend`: every case in `test-vectors/spec/fips180-4.json` and `rfc4231.json` (truncated-output case 5 compares the first 16 bytes).

## Verify

`scripts/check.nu`
