# 12 APER primitives

Depends on: 02.

## Goal

`kernel/aper.bend`: the ITU-T X.691 aligned PER building blocks NGAP uses. Read [the NGAP codec research](../../research/ngap-codec-approach.md) first. The building blocks:

- a bit reader and writer over byte lists (position in bits, octet alignment);
- constrained whole numbers (§11.5.7), including the 1-byte, 2-byte and indefinite-length cases;
- normally small numbers;
- length determinants (§11.9), rejecting fragmented lengths of 16K or more;
- extension bits, choice indices, enumerated;
- BIT STRING, OCTET STRING and PrintableString with size constraints;
- open types (§11.2) as length-prefixed byte slices.

## Laws

- `aper.<primitive>.roundtrip` for each primitive, over values inside its constraint.
- `aper.<primitive>.decode_valid`: decoded values satisfy the constraint they were decoded under.
- `aper.open_type.exact`: an open type's inner decoder sees exactly the `n` declared octets.
- `aper.no_big_nat`: no decoder builds a `Nat` of 2⁴⁸ or more. Values above 32 bits are byte lists.
- `aper.padding_zero`: alignment padding must be zero bits. Check this against the captured UERANSIM traffic. If UERANSIM sends non-zero padding, relax it to "ignored" and record why in `loop/progress.md`.

## Tests

Hand-made vectors per primitive taken from X.691 examples, plus the captured NGAP PDUs cut at their open-type boundaries.

## Verify

`scripts/check.nu`
