# 11 NAS 5GSM codec

Depends on: 10.

## Goal

`kernel/nas/sm.bend`: the 5GSM messages of TS 24.501 §8.3:

- PDU Session Establishment Request, Accept and Reject;
- PDU Session Modification Request and PDU Session Modification Reject;
- PDU Session Release Request, Release Command and Release Complete;
- 5GSM Status.

The IEs include QoS rules (§9.11.4.13) with packet filters, QoS flow descriptions (§9.11.4.12), Session-AMBR (§9.11.4.14), PDU address (§9.11.4.10) and extended protocol configuration options (ePCO, TS 24.008 §10.5.6.3A).

## Laws

- `nas.sm.roundtrip`, `nas.sm.decode_valid`, `nas.sm.suffix`.
- `nas.qos_rules.suffix` (advisory GHSA-6w6j-vjx3-pwqr): each rule and each packet filter is read only inside its declared length; a rule whose length disagrees with its contents is `Fail`.
- `nas.packet_filter.mask_contiguous` (advisory GHSA-g4xp-3ccr-264w): an IPv4 remote-address component decodes only if its mask is a contiguous run of ones from the top bit.
- `nas.session_ambr.decode_valid` (advisory GHSA-m795-gjf7-c8ch): Session-AMBR content is exactly 6 bytes and both units are defined values.
- `nas.epco.decode_bounded` (advisory GHSA-fvg8-6r68-v3x7): decoded ePCO holds at most 255 containers, and each container lies within the IE.
- `nas.epco.encode_bounded` (advisory GHSA-796x-8w26-2xfp): an encoded ePCO is at most 65535 bytes, and the encoder cannot produce a container longer than 255 bytes. This is a property of the datatype: container contents are a length-indexed list.

## Tests

The 5GSM messages in `test-vectors/capture`, plus hand-made malformed cases: truncated rule, non-contiguous mask, Session-AMBR of 5 bytes, ePCO with 300 containers.

## Verify

`scripts/check.sh`
