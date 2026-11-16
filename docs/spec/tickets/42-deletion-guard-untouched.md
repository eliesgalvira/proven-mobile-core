# 42 Nothing but its own expiry touches a deleting session's guard

Depends on: 41. Estimate: 3–5 h. Blocks merging `loop/m1` into `main`.

## Goal

The pre-merge review of ticket 41 (2026-11-16) found two gaps left by `smf.deletion.held` and `smf.deletion.armed`, so a row being deleted is still not bound to end:

1. **A step may restart its guard.** `held` concludes that the step does not stop timer `skey` (`Acts.stops`, which counts only `TimerCancel`), but a step that emits `TimerStart{_, skey, ms}` while leaving the row as it is passes it, and `armed` does not apply to a row already being deleted. Weaker case: a session's row enters `Deleting` with its guard started (`armed` holds); then every later step, say each gNB message faster than T1, also emits `TimerStart{None, skey, T1}`; the guard never fires and, if the UPF never answers, the row holds its IPv4, TEID and SEID forever. As far as the review traced, the code does not do this: every `TimerStart` on a session's key comes with a write to that row, which `held` excludes. State it: `held` also concludes that the step starts no timer `skey` (`Ng.Acts.starts`, or one predicate saying the step names no timer `skey`). The proof work is in `Lv.reach` (`kernel/proofs/liveness.bend`), which today accepts any `TimerStart` tagged `None`: it needs the treatment ticket 41 gave `TimerCancel` (the timer is a context's key, or its row is not kept), at about 20 start sites.
2. **The guard's duration is free.** `Acts.runs` ignores the timer's duration, so `armed` holds for a step entering `Deleting` with `TimerStart{None, skey, 0xFFFFFFFF}`, about 50 days before the first retry. `armed` must say the last timer action naming `skey` is `TimerStart{_, skey, Up.N4.t1_ms()}`, as `smf.deletion.retransmitted` does for each retry. Every site that enters `Deleting` (`N4.delete_if`) already uses T1.

With both, the `loop/law-changes.md` entry for `smf.establish.failure_releases` holds as written: a session being deleted is freed within (N1 + 1) × T1.

Also from that review, in passing: `Lv.okf_w` is dead; `Lv.or_mono`, `Rl.or_mono` (and their counterpart `Cf.or_mono`) are one `Bool.or_mono` for `kernel/proofs/lib.bend`; the comment above `Lv.reach` cites `Lv.okw` for what `Lv.settles`/`Lv.fine` do; `St.Sessions.held` and `SPhase.held` mean "not being deleted", the opposite of what law `smf.deletion.held` names, so rename them (e.g. `Sessions.live`); `Ar.rows`, `Sessions.held` and `Sessions.deleting` are three copies of "every row under the key satisfies P".

## Verify

`scripts/check.nu --strict`, `nix build .#checks.x86_64-linux.e2e`, and a review that finds no law weaker than on `main`.
