# 27 Xn handover: Path Switch

Depends on: 25, 26, 19. Estimate: 2–3 h.

## Goal

The AMF handles PathSwitchRequest from a target gNB (TS 23.502 §4.9.1.2.2, TS 38.413 §8.4.4):

1. Find the UE by Source AMF-UE-NGAP-ID. If the UE doesn't exist, or the target association is not an NG-set-up gNB, reply PathSwitchRequestFailure.
2. Compare the UE security capabilities in the request with the stored ones (TS 33.501 §6.7.3.1). If they differ, use the stored ones in the acknowledgement, and log it.
3. The SMF repoints each listed PDU session's downlink FAR to the target's DL NG-U tunnel with one PFCP Session Modification. Sessions that fail are released, and listed in the acknowledgement as failed.
4. Move the UE to the target association with its new RAN-UE-NGAP-ID. Derive the next {NH, NCC}. Reply PathSwitchRequestAcknowledge with the security context and the switched sessions.
5. If no PDU session can be switched, reply PathSwitchRequestFailure (TS 38.413 §8.4.4.2) and change nothing; the UE is not released. Path Switch has no owner check, so releasing here would let any gNB with NG Setup log off any registered UE with a request naming no session it can switch. The UE is released only when the UPF has refused every session repointed.
6. The source gNB's later UEContextReleaseRequest for this UE is answered by its owner check, since the source is no longer the owner. The source's resources are freed when its association reports them, as in milestone 1.

## Laws

- `amf.path_switch.moves_owner`: after a successful Path Switch, the UE is owned by the target association and by no other.
- `amf.path_switch.stored_capabilities`: the acknowledgement carries the stored UE security capabilities, never the ones in the request.
- `amf.path_switch.failure_leaves_state`: a PathSwitchRequestFailure sent before any PFCP request (unknown UE, gNB without NG Setup) changes no state.

Trade-off: Path Switch carries no owner check by design. Any gNB with NG Setup done may claim a UE by its AMF-UE-NGAP-ID, as in TS 23.502. The kernel narrows this only by requiring the UE to be registered.

## Tests

Replay of the Xn handover in the ticket 24 capture. Hand-made cases: an unknown UE, a request from a gNB without NG Setup, mismatched capabilities.

## Verify

`scripts/check.nu`
