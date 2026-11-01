# 15 Edge ⇄ kernel frame codec

Depends on: 02.

## Goal

`kernel/frame.bend`: decode events and encode actions exactly as specified in `docs/spec/milestone-1.md` § The frame protocol, including the Config TLVs.

## Laws

- `frame.event.roundtrip`, `frame.event.suffix`, `frame.actions.roundtrip`.
- `frame.max_length`: a body over 262144 bytes is rejected before any field is decoded.
- `frame.config.repeat_replaces`: decoding a Config where a tag appears twice yields the later value.

## Tests

Hand-made frames for each kind, including a truncated frame and an oversize one.

## Verify

`scripts/check.sh`
