# 13 NGAP: generator, generated codec and message views

Depends on: 03, 12.

Read first: `docs/research/ngap-codec-approach.md`, then `docs/research/ngap-asn1-tooling.md`.

## Pinned inputs

- **ASN.1:** 3GPP TS 38.413 V17.15.0 (Release 17), in `tools/ngap-gen/asn/`, extracted unedited by `tools/ngap-gen/extract.py`. The sources and sha256 sums are in `tools/ngap-gen/asn/README.md`.
- **Parser:** pycrate exactly `0.8.1`, from PyPI. It is a build tool only; never vendor its code.
- **Generator language:** Python 3, run with `python3 -I`. `tools/ngap-gen/ngap_model.py` is the only module that touches pycrate's private attributes; the emitter talks to it, never to pycrate directly.

## Goal

1. **Generator.** `tools/ngap-gen/gen.py` reads the pinned ASN.1 and emits plain Bend into `kernel/ngap/gen/`. The generator is untrusted: `--verdict` checks what it emits. It emits, for every type in the closure of the milestone message set (tiers M and R in the tooling research):
   - a datatype;
   - `decode`, `encode` and `valid`;
   - the proof terms for the standard laws, composed from the APER primitive lemmas of ticket 12.
2. **Message set.** These messages, plus `PDUSessionResourceSetupRequestTransfer`, `PDUSessionResourceSetupResponseTransfer` and `PDUSessionResourceSetupUnsuccessfulTransfer`:
   - NGSetupRequest, NGSetupResponse, NGSetupFailure;
   - InitialUEMessage, DownlinkNASTransport, UplinkNASTransport;
   - InitialContextSetupRequest, InitialContextSetupResponse, InitialContextSetupFailure;
   - UEContextReleaseRequest, UEContextReleaseCommand, UEContextReleaseComplete;
   - PDUSessionResourceSetupRequest, PDUSessionResourceSetupResponse;
   - ErrorIndication.
3. **Unknown IEs and extensions.** IEs outside the closure, and unknown extensions, stay raw open-type bytes, handled by criticality as TS 38.413 §10.3 requires:
   - `reject` → the procedure fails with Error Indication;
   - `ignore`/`notify` → skipped.
4. **Message views.** `kernel/ngap/view.bend` holds one view per message, built from the object sets (ID, CRITICALITY, PRESENCE).
   - A view returns `Done` only if every mandatory IE appears exactly once and every IE with criticality `reject` is understood.
   - Mandatory IEs are plain fields, not `Maybe`.
5. **Golden output.** `tools/ngap-gen/test_gen.py` re-runs the generator and fails on any diff with the committed `kernel/ngap/gen/`.
6. **Differential oracle.** `tools/ngap-gen/oracle.py` uses pycrate's APER runtime to decode the same bytes as our codec, for every NGAP message in `test-vectors/capture`, and compares the results.

## Laws

- `ngap.<Type>.roundtrip`, `ngap.<Type>.decode_valid` and `ngap.<Type>.suffix` for every generated type. The generator emits them; listing them in `LAWS.bend` may be generated too.
- `ngap.no_big_nat`: AMF-UE-NGAP-ID (0..2⁴⁰−1) and BitRate (0..4·10¹², extensible) decode to byte lists or pairs of `U32`, never to `Nat`.
- `ngap.initial_ue_message.mandatory` (advisory GHSA-cfp8-93x2-6h9x): the InitialUEMessage view succeeds only when RAN-UE-NGAP-ID, NAS-PDU, UserLocationInformation and RRCEstablishmentCause are each present exactly once.
- `ngap.view.duplicate_rejected`: in every view, an IE id that appears twice makes the view fail (TS 38.413 §10.3.6).

## Tests

- Every NGAP message in `test-vectors/capture` decodes, re-encodes to identical bytes, and agrees with the pycrate oracle.
- Hand-made cases:
  - InitialUEMessage without UserLocationInformation;
  - a duplicated RAN-UE-NGAP-ID;
  - an unknown IE with criticality `reject`;
  - an unknown IE with criticality `ignore`.

## Verify

`python3 -I tools/ngap-gen/test_gen.py && scripts/check.sh`
