# 28 N2 handover with cancel

Depends on: 25, 26, 19. Estimate: 4–5 h.

## Goal

Intra-AMF, intra-UPF N2 handover (TS 23.502 §4.9.1.3, TS 38.413 §8.4.1–8.4.3 and §8.4.5–8.4.7):

1. **Preparation:**
   - HandoverRequired from the UE's owner, naming a target known by Global gNB ID with NG Setup done.
   - The AMF sends HandoverRequest to the target, with the next {NH, NCC} and the PDU sessions' UL tunnels.
   - It starts its preparation guard: a kernel timer, since TS 38.413's TNGRELOCprep runs in the source gNB, not the AMF.
2. **Acknowledgement:** HandoverRequestAcknowledge from that target, for that pending handover only. The AMF sends HandoverCommand to the source and starts its completion guard.
3. **Failure:**
   - HandoverFailure from the target, or the preparation guard expiring, sends HandoverPreparationFailure to the source.
   - The pending handover and anything allocated for the target are released.
4. **Status transfer:** UplinkRANStatusTransfer from the source is relayed as DownlinkRANStatusTransfer to the target.
5. **Completion:**
   - HandoverNotify from the target: the SMF repoints the downlink FARs to the target's tunnels, the UE moves to the target association, and the AMF sends UEContextReleaseCommand to the source.
   - On the source's Complete, the source side is forgotten.
6. **Cancel:**
   - HandoverCancel from the source answers HandoverCancelAcknowledge and releases the target side.
   - After that, any target response for that handover is ignored.

## Laws

- `amf.handover.owner_only` (advisory GHSA-wpwr-xj64-h6cp): HandoverRequired, HandoverCancel and UplinkRANStatusTransfer change state only when they come from the UE's owner. HandoverRequestAcknowledge, HandoverFailure and HandoverNotify change state only when they come from the target of the UE's pending handover.
- `amf.handover.responses_correlated` (advisory GHSA-v6fv-hmw8-6ffv): a target response with no pending handover for that UE, including after a cancel or a timeout, changes no state and emits no PFCP message.
- `amf.handover.single_owner`: at every reachable state, each UE is owned by exactly one association. A pending handover names a target but never transfers ownership before HandoverNotify.
- `amf.handover.guarded`: every pending handover has exactly one running guard timer, preparation or completion, and a guard expiring ends the pending handover.

## Tests

Replay of the N2 handover and cancel in the ticket 24 capture. Hand-made cases:
- an acknowledgement from a third gNB;
- an acknowledgement after a cancel;
- a HandoverNotify from the source;
- the preparation guard expiring.

## Verify

`scripts/check.sh`
