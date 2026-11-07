# 14 PFCP codec

Depends on: 02, 03.

## Goal

`kernel/pfcp.bend`: PFCP per TS 29.244, the subset eUPF needs. Read [the eUPF research](../../research/eupf-pfcp.md) first. Messages, with their headers (S flag, SEID, sequence number):

- Heartbeat Request and Response;
- Association Setup Request and Response;
- Session Establishment Request and Response;
- Session Modification Request and Response;
- Session Deletion Request and Response.

The IEs are the set listed in the research's "Implications" section. Any other IE is skipped by its length and kept raw.

## Laws

- `pfcp.roundtrip`, `pfcp.decode_valid`, `pfcp.suffix`.
- `pfcp.ie_header.short_input_fails` (advisory GHSA-4x7x-2p8x-jwrq): an IE header needs 4 bytes, otherwise `Fail{Short}`.
- `pfcp.ie.suffix` (advisory GHSA-37c3-hv4f-688p): every IE, known or unknown (including Volume Measurement), consumes exactly 4 + its declared length, and fails if fewer bytes remain.
- `pfcp.fteid.decode_valid` (advisory GHSA-3mxx-vq7h-x8ff): an F-TEID's length matches its flags (V4, V6, CH, CHID), and CH with a TEID or address present is rejected.
- `pfcp.header.length_consistent`: the message length field equals the bytes that follow it.

## Tests

The PFCP messages in `test-vectors/capture`.

## Verify

`scripts/check.nu`
