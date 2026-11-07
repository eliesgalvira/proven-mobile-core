# 16 Kernel state and NG Setup

Depends on: 13, 15.

## Goal

`kernel/state.bend`, `kernel/step.bend`, `kernel/amf/ngap.bend`. This ticket defines `State`, `Event`, `Action` and `Kernel.step`, as specified in `docs/spec/milestone-1.md` § The step function, and implements:

- `Config` → store the configuration; trigger PFCP Association Setup (ticket 19 completes it; here only emit the request).
- `NgapAssocUp` / `NgapAssocDown`. Going down releases every UE whose RAN side was that association, including their PDU sessions (PFCP Session Deletion).
- NG Setup Request → NG Setup Response, with:
  - AMF name;
  - served GUAMI from config;
  - relative capacity 255;
  - PLMN support with the configured S-NSSAI.

  If no supported TA matches the configured PLMN and TAC, reply NG Setup Failure with cause `unknown-PLMN-or-SNPN`.
- Any NGAP PDU that fails to decode → Error Indication with cause `protocol: transfer-syntax-error`, and no other state change.
- Non-UE-associated signalling uses stream 0. UE-associated replies use the stream on which that UE's InitialUEMessage arrived.

## Laws

- `amf.ng_setup.requires_supported_plmn`: NG Setup Response is emitted only if the request's supported TA list contains the configured PLMN and TAC.
- `amf.assoc_down.releases_all`: after `NgapAssocDown(a)`, no UE context has RAN association `a`.
- `kernel.bad_pdu.only_error_indication`: an undecodable NGAP PDU changes no state and emits only Error Indication (and a Log).

## Tests

`kernel/tests/ng_setup.bend` drives `step` with `Config`, `NgapAssocUp`, then the captured NG Setup Request, and checks the response decodes as NG Setup Response with the configured GUAMI.

## Verify

`scripts/check.nu`
