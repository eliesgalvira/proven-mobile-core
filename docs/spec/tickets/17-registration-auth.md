# 17 Registration, part 1: identification and 5G-AKA

Depends on: 08, 09, 10, 16.

## Goal

`kernel/amf/gmm.bend`, `kernel/ausf.bend` (AUSF + UDM in one module). This ticket covers InitialUEMessage through authentication:

1. **InitialUEMessage** is decoded through the NGAP view (ticket 13), which needs RAN-UE-NGAP-ID, NAS-PDU, UserLocationInformation and RRCEstablishmentCause. Create a UE context keyed by a fresh AMF-UE-NGAP-ID, unique and below 2³², owned by the association. If the view fails, send Error Indication and create nothing.
2. **Identifying the UE:**
   - Registration Request with a SUCI → de-conceal it (ticket 08) → look up the subscriber.
   - With a 5G-GUTI the AMF doesn't know → Identity Request (SUCI).
   - Unknown subscriber → Registration Reject, cause `#7 5GS services not allowed`, then UE context release.
3. **UDM** generates an authentication vector:
   - RAND = the first 16 bytes of the event's entropy;
   - SQN = the subscriber's SQN + 32, stored back (TS 33.102 Annex C.3.2, IND of 5 bits);
   - AUTN = SQN⊕AK ‖ AMF ‖ MAC-A;
   - XRES*, KAUSF and HXRES*.
4. **AMF sends Authentication Request** (ngKSI, ABBA `0x0000`, RAND, AUTN) and starts T3560 (6 s). On expiry it retransmits, up to 4 times, then releases the UE context.
5. **On Authentication Response:**
   - The SEAF compares HRES* with HXRES*, then the AUSF compares RES* with XRES*.
   - Both comparisons are over the full 16 bytes.
   - On success, derive KSEAF and then KAMF.
   - On failure, send Authentication Reject and release.
6. **On Authentication Failure:**
   - Cause `#21 synch failure` with AUTS → re-synchronise SQN (f1*, f5*, TS 33.102 §6.3.5) and re-authenticate, once.
   - Cause `#20 MAC failure` → Authentication Reject.

## Laws

- `amf.initial_ue.reject_leaves_state` (advisory GHSA-cfp8-93x2-6h9x): if the InitialUEMessage view fails, the state after `step` equals the state before, and the only actions are Error Indication and Log.
- `ausf.res_star.full_length` (advisory GHSA-r9rw-hx33-745g, 5G analogue): authentication succeeds only if RES* is exactly 16 bytes and all 16 equal XRES*, and HRES* equals HXRES* over all 16 bytes.
- `amf.auth.guarded`: every UE context that isn't registered has exactly one running guard timer (T3560, T3550 or T3555) or is being released.

## Tests

Replay with fixed entropy whose first 16 bytes are the captured RAND and with the captured SQN in config, so the captured Authentication Response verifies. Check that the emitted Authentication Request equals the captured one byte for byte, except NGAP IDs.

## Verify

`scripts/check.nu`
