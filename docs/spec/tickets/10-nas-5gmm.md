# 10 NAS 5GMM codec

Depends on: 02, 03.

## Goal

`kernel/nas/mm.bend` and `kernel/nas/ie.bend`: decode and encode the plain 5GMM messages of TS 24.501 §8.2, and the security-protected outer header of §9.1.1 and §9.3. Messages:

- Registration Request, Registration Accept, Registration Complete, Registration Reject;
- Deregistration Request (UE originating) and Deregistration Accept (UE originating);
- Authentication Request, Authentication Response, Authentication Reject, Authentication Failure;
- Identity Request and Identity Response;
- Security Mode Command, Security Mode Complete, Security Mode Reject;
- 5GMM Status;
- UL NAS Transport and DL NAS Transport.

Every IE these messages carry in `test-vectors/capture` gets a typed decoder. Any other optional IE is skipped by its format (TS 24.007 §11.2.4) and kept as raw bytes, so that encode(decode(x)) can reproduce it. A missing mandatory IE is `Fail{Invalid}`.

The 5GS mobile identity (§9.11.3.4) covers SUCI (null scheme and Profile A, schemes kept as bytes for ticket 08), 5G-GUTI, IMEI, IMEISV, 5G-S-TMSI and no-identity.

## Laws

- `nas.mm.roundtrip`, `nas.mm.decode_valid`, `nas.mm.suffix`: the standard shapes, over every message type above.
- `nas.mobile_identity.suffix` and `nas.mobile_identity.decode_valid` (advisory GHSA-f4mx-3x6p-cfwp): decoding reads only inside the IE's declared length; the identity type and its length agree (for example, 5G-GUTI is exactly 11 bytes of content).
- `nas.imeisv.decode_valid` (advisory GHSA-hcjf-j847-3gx8): the odd/even flag and the digit count agree, and IMEISV has exactly 16 digits.
- `nas.payload_container.suffix` (advisory GHSA-9643-6pmq-j7g2): a payload container shorter than its declared length is `Fail{Short}`, and the inner 5GSM bytes are exactly the declared slice.

## Tests

Every 5GMM message in `test-vectors/capture`, plaintext form. Each must decode, re-encode to identical bytes, and show the expected message type.

## Verify

`scripts/check.nu`
