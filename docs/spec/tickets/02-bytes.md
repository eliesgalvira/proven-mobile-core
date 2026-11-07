# 02 Byte reader and writer

Depends on: 01.

## Goal

`kernel/bytes.bend`: the only module that turns byte lists into numbers and back. Readers return `Result<Err, (value, rest)>`; writers prepend to a `rest` list so that encoders compose without `++` chains.

Functions:
- `u8`, `u16`, `u24`, `u32`: big-endian.
- `take(n)`: exactly `n` bytes, or `Fail`.
- `nibbles`: high and low nibble.
- `tbcd_digits(bytes, count)`: TS 24.008 §10.5.1.4 TBCD, with filler `0xF`.
- `is_byte(x)`: `x < 256`.

`Err` is a closed datatype shared by every codec (at least `Short`, `Invalid(tag)`, `Unsupported(tag)`), defined here.

## Seams

The public readers and writers.

## Laws

- `bytes.u8.roundtrip`, `bytes.u16.roundtrip`, `bytes.u24.roundtrip`, `bytes.u32.roundtrip`: `read(write(v, rest)) = Done{(v, rest)}` for `v` in range.
- `bytes.take.length`: on success, the taken list has exactly `n` elements and `taken ++ rest = input`.
- `bytes.short_input_fails`: every reader on a list shorter than its width returns `Fail{Short}`.
- `bytes.tbcd.length` (advisory GHSA-vp44-3q85-5cm4): decoding `k` bytes yields at most `2k` digits, and every digit is `0..9`. Encoding `d` digits yields `ceil(d/2)` bytes.

These laws need lemmas about `U32` bit operations (`and`, `shr`, `shl`, `or` on values under 256). Put them in `kernel/u32_lemmas.bend`. If a lemma proves out of reach, write an `upstream:bend` draft (see `AGENTS.md`) asking for it in Base, mark the dependent law blocked, and continue.

## Tests

Hand-picked byte strings from `test-vectors/capture` (PLMN 3 bytes, a SUCI MSIN).

## Done when

All laws above pass `--verdict`; `kernel/tests/bytes.bend` passes.

## Verify

`scripts/check.nu`
