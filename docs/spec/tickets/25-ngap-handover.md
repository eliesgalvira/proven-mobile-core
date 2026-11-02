# 25 NGAP handover messages

Depends on: 13, 24. Estimate: 2–3 h.

## Goal

Extend `tools/ngap-gen`'s message set with these messages and their transfers, and regenerate `kernel/ngap/gen/` with its laws:

- Path Switch: PathSwitchRequest, PathSwitchRequestAcknowledge, PathSwitchRequestFailure.
- N2 handover:
  - HandoverRequired, HandoverRequest, HandoverRequestAcknowledge;
  - HandoverFailure, HandoverCommand, HandoverPreparationFailure;
  - HandoverNotify, HandoverCancel, HandoverCancelAcknowledge.
- RAN status transfer: UplinkRANStatusTransfer, DownlinkRANStatusTransfer.
- Transfers:
  - PathSwitchRequestTransfer, PathSwitchRequestAcknowledgeTransfer, PathSwitchRequestUnsuccessfulTransfer, PathSwitchRequestSetupFailedTransfer;
  - HandoverRequiredTransfer, HandoverCommandTransfer;
  - HandoverRequestAcknowledgeTransfer, HandoverResourceAllocationUnsuccessfulTransfer.

Add a view in `kernel/ngap/view.bend` for each message the AMF receives.

## Laws

The generated `ngap.<Type>.roundtrip`, `decode_valid` and `suffix` laws for every new type, plus:

- `ngap.path_switch_request.mandatory`: the view succeeds only when RAN-UE-NGAP-ID, Source AMF-UE-NGAP-ID, UserLocationInformation, UESecurityCapabilities and the PDU session list are each present exactly once.
- `ngap.handover_request_acknowledge.mandatory` and `ngap.handover_required.mandatory`: the same, for their mandatory IEs.

## Tests

Every new message in the ticket 24 capture decodes, re-encodes to identical bytes, and agrees with the pycrate oracle.

## Verify

`python3 -I tools/ngap-gen/test_gen.py && scripts/check.sh`
