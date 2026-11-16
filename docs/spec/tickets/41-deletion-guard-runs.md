# 41 A session being deleted keeps its guard running

Depends on: 39. Estimate: 2–4 h. Blocks merging ticket 39 into `main`.

## Goal

The pre-merge review of ticket 39 (2026-11-15) found that no law makes a session being deleted end. `smf.deletion.held` says only its guard or its answer changes the row, and `smf.deletion.retransmitted` that the guard ends it within N1 retries, but nothing says the guard is running:

- `smf.deletion.held` says the row is unchanged, not that the step leaves timer `skey` alone;
- `Up.N4.deleted` puts `TimerStart{None, skey, T1}` after the request, but a later action of the same step may still be `TimerCancel{skey}`;
- on `main`, `amf.release.complete_forgets`, `amf.guard.expires`, `amf.sessions.owned` and `smf.ip_pool.unique` made every path that forgets a UE or evicts a session remove its row. On `loop/m1`, `Sessions.of_ue`, `Sessions.owned` and `Session.conflicts` skip a session being deleted (`Session.tag`), so those laws allow the row to stay as `Deleting`.

Weaker case: a UE with one Active session the UPF knows; its owner's UE Context Release Complete arrives; a step that turns the row into `Deleting{Guard{7}, []}` and emits no PFCP message and no timer satisfies every law on `loop/m1`, and the row then holds its address, TEID and SEID forever. `main` rules it out. As far as the review traced, the code does not do this (every path goes through `N4.delete_if`, and `Gone.cancels` stops only rows that are gone); the laws must say so.

1. **Held keeps the guard:** add to `smf.deletion.held`'s conclusion that the step does not stop timer `skey` (`Ng.Acts.stops(skey, acts) == False{}`).
2. **Entering Deleting starts the guard:** one law over every event: if the row under `skey` was absent or not being deleted before the step and is `Deleting{g, request}` after, then `g` is `Guard{0}`, the step sends `request`, and its last timer action naming `skey` is a `TimerStart`. Prefer the shape that makes this structural if it is simpler, e.g. `N.Step.of` deriving the TimerStart of every row that becomes `Deleting` from the table diff, as `N.Gone.cancels` derives the stops of rows that go.

With both, the `loop/law-changes.md` entry for `smf.establish.failure_releases` holds as written: a session being deleted is freed within N1 + 1 guard periods.

## Verify

`scripts/check.nu --strict`, `nix build .#checks.x86_64-linux.e2e`, and a review that finds no law weaker than on `main`.
