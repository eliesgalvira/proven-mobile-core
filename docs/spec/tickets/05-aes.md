# 05 AES-128, CTR and CMAC

Depends on: 02, 03.

## Goal

`kernel/crypto/aes.bend`: AES-128 block encryption only (5G needs no AES decryption). Use table-free or table-based S-box; correctness over speed. Also:
- `kernel/crypto/ctr.bend`: AES-128-CTR keystream XOR, any length.
- `kernel/crypto/cmac.bend`: AES-CMAC per RFC 4493, any length.

## Laws

- `aes.block_length`: 16-byte key and 16-byte block give 16 bytes.
- `ctr.length`: output length equals input length.
- `ctr.involution`: `ctr(k, iv, ctr(k, iv, m)) = m`.
- `cmac.length`: the output is always 16 bytes.

## Tests

FIPS 197 C.1, SP 800-38A F.5.1, RFC 4493 examples 1 to 4.

## Verify

`scripts/check.nu`
