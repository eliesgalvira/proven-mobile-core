# 33 Liveness laws that can fail

Depends on: 18. Estimate: 3–4 h.

## Goal

`amf.auth.guarded` and `amf.registration.completes_or_releases` are the same law, and both are true by construction: every phase before Registered carries a guard field. Neither says a timer runs, and `Releasing` has no guard, so a gNB that never sends UEContextReleaseComplete keeps the context and its UPF sessions forever. `amf.release.forgets_ue` covers only the owner's Release Complete.

1. `Releasing` gets a guard timer. On expiry, the context and its sessions are forgotten and the sessions are deleted at the UPF.
2. Replace the two vacuous laws with the liveness laws below, and delete the duplicate.
3. `next_ue` and `next_timer` must skip ids that are still live, instead of wrapping onto them.

## Laws

- `amf.guard.expires`: a context whose guard fires at the retry limit moves to `Releasing`, and a `Releasing` context whose guard fires is gone (`Table.get(k) == None`). Advisory GHSA-cfp8-93x2-6h9x.
- `amf.sessions.owned`: in every state reachable by `step`, every session's UE key exists in the UE table.
- `amf.release.forgets_ue` (advisory GHSA-88pq-hpwv-2vjw): if `get(k, ues(st)) == None` and `k` is not `next_ue(st)`, no NgapSend, PfcpSend or TimerStart action of `step(st, ev)` is built from a context keyed `k`. An Error Indication that echoes an ID taken from the received PDU is allowed. This holds whatever path forgot the UE.

## Verify

`scripts/check.sh`
