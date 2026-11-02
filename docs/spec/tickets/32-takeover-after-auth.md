# 32 Identity takeover only after authentication

Depends on: 18. Estimate: 2–3 h.

## Goal

Today `Gmm.challenge` → `Gmm.place` evicts any context holding the same SUPI as soon as a SUCI is de-concealed, before RES* is verified. Anyone who captured a SUCI can replay it in a new InitialUEMessage to release a registered UE and delete its sessions at the UPF. Move the takeover so it happens only after authentication:

- An authenticating context keeps its SUPI in its phase, out of the SUPI index.
- The old context is released only after HRES* and RES* verify. The registration test that expects eviction at de-concealment changes with it.
- `amf.ue_context_release.owner_only` also covers procedure codes 14 (Initial Context Setup), 29 (PDU Session Resource Setup) and 46 (Uplink NAS Transport).

## Laws

- `amf.takeover.authenticated` (advisory GHSA-mg8r-2cvv-xq9j): an `NgapData` event from association b removes no registered context owned by another association unless, in the resulting state, a context with that SUPI holds a verified security context.
- `amf.ue_context_release.owner_only`, widened as above.

## Verify

`scripts/check.sh`
