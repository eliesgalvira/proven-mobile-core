# 18 Registration, part 2: security mode, acceptance and release

Depends on: 17.

## Goal

1. **Security Mode Command:**
   - Select the integrity algorithm as the first configured NIA (never NIA0) that the UE supports, and the ciphering algorithm as the first configured NEA it supports.
   - Send it integrity-protected with the new context (security header type 3), with replayed UE security capabilities and an IMEISV request. Start T3560.
2. **Security Mode Complete** must verify with the new context. If it carries a NAS message container, the container's Registration Request replaces the initial one.
3. **InitialContextSetupRequest**, which carries:
   - GUAMI, Allowed NSSAI, UE security capabilities;
   - the security key KgNB (NAS uplink COUNT of the Security Mode Complete);
   - a NAS-PDU holding Registration Accept: a new 5G-GUTI (5G-TMSI from entropy), a TAI list with the configured TAI, Allowed NSSAI, and T3512 of 54 minutes.

   Start T3550.
4. **InitialContextSetupResponse**, then **Registration Complete** → registered; stop T3550.
5. **Deregistration Request** (UE originating):
   - release the UE's PDU sessions (ticket 19);
   - send Deregistration Accept, unless it is a switch-off;
   - send UEContextReleaseCommand, and on UEContextReleaseComplete forget the UE.
6. **UEContextReleaseRequest** from the gNB that owns the UE → UEContextReleaseCommand → Complete → forget the UE. This milestone has no CM-IDLE, so release means deregistration.
7. **Identity takeover:**
   - A Registration Request whose SUPI or 5G-GUTI belongs to another live context releases the old context completely, sessions included, before indexing the new one.
   - The same applies to a UE IPv4 or SEID collision in the SMF.
8. **Plaintext after security:** once a NAS security context is active for a UE, accept only messages that verify under it. The exceptions are those TS 24.501 §4.4.4.3 lists for an unverified message, and those trigger re-authentication rather than being acted on.

## Laws

- `amf.ue_context_release.owner_only` (advisory GHSA-mg8r-2cvv-xq9j): a UEContextReleaseRequest or Complete from an association other than the UE's owner changes no state.
- `amf.release.forgets_ue` (advisory GHSA-88pq-hpwv-2vjw): after a UE is forgotten, no map, index, timer or pending transaction refers to its AMF-UE-NGAP-ID, and no later action can mention it.
- `amf.indexes.unique` (advisory GHSA-7g3v-g4gp-p624): in every state reachable by `step` from the initial state, each index (SUPI, 5G-TMSI, RAN-UE-NGAP-ID per association, UE IPv4, SEID) maps each key to at most one context, every entry points to an existing context, and every context is in each index that applies to it. Prove it as an invariant that `step` preserves.
- `amf.nas.plaintext_after_security`: with an active security context, a message that fails integrity verification never advances the UE's registration state.
- `amf.registration.completes_or_releases`: every context is registered, or holds a running guard timer, or is being released. This states "never left hanging"; `amf.auth.guarded` is its special case.

## Tests

Replay the captured Security Mode Complete, InitialContextSetupResponse and Registration Complete, choosing the same algorithms as the capture. Hand-made cases: a release request from a second association; a second registration with the same SUPI.

## Verify

`scripts/check.sh`
