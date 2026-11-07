# 38 Close the gaps the merge review found

Depends on: 32, 33, 34. Estimate: 2–3 h.

## Goal

The review of tickets 32–34 found three premises that are true in every state the kernel reaches but are stated nowhere, plus overstated report rows. Turn the premises into invariant laws, then drop them from the laws that assume them.

1. **No unguarded context:** every context in a reachable state is Registered or holds a guard. `Created` is never stored.
2. **Free next ids:** in every reachable state, `next_ue` is not a live context key and `next_timer` is not a live timer, and no two rows share a guard timer. Then `amf.takeover.authenticated` covers the wrap case, and `amf.guard.expires` can speak of the one row a timer belongs to.
3. **Sessions known to the UPF:** every session past Creating holds an 8-octet UP SEID. Then `smf.establish.failure_releases` states the PFCP Session Deletion without the `Up.N4.known` premise.
4. **The report:** in `loop/acceptance-report.md`, fix the stale line numbers and the closing sentence. In the GHSA-88pq row, say that the actions' `ue` tag is not tied to the SEID in the PFCP bytes.

## Laws

- `amf.contexts.guarded`: invariant, preserved by `step`.
- `state.ids.free`: invariant, preserved by `step`.
- `smf.sessions.known`: invariant, preserved by `step`.
- `smf.establish.failure_releases`, restated without the premise.

## Verify

`scripts/test-kernel.sh --strict && python3 -I scripts/acceptance.py --strict && scripts/check.sh`
