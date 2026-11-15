# Blockers

One entry per blocker: ticket, what was tried, smallest reproduction, what would unblock it.

## Ticket 41: no law yet keeps a session being deleted's guard running (2026-11-16)

- **Tried:** the structural route on branch `ticket/41-deletion-guard-wip` (c579cd8, proofs do not check): `N.Step.of` sends the Session Deletion Request and starts the guard of every row that becomes `Deleting`, derived from the table diff (`N.Step.rows`, `N.Arm.*`) instead of `N4.delete_if`. Kernel tests `pdu_session registration path_switch handover ng_setup pfcp` pass; `bend kernel/PROOF.bend` fails first at `Del.one` in `kernel/proofs/smf.bend`, inside `smf.establish.failure_releases`.
- **Why it stalls:** the derived actions find the row by key (`Tb.Table.get`), while the PFCP and NGAP clauses of `failure_releases` find it by `by_seq`/`by_psi`; with two rows under one key they can differ, so the law needs `Sessions.unique` as a premise, which is weaker on its own than on `main` though equal on reachable states (`smf.ip_pool.unique`). Part 1 (`smf.deletion.held` leaves timer `skey` running) is not structural on either route: `Lv.act` needs a condition on every `TimerCancel` (a context's key, or a row kept), about 9 cancelling sites and the `Hd.*` lemmas redone; `Guard{0}` on entering `Deleting` needs a condition on `Revar`/`PutSession` in `Lv.homed`/`Lv.free`.
- **Unblocks it:** a choice by the owner between (a) accepting `Sessions.unique` as an invariant premise of `failure_releases` and the new law, as `smf.deletion.held` already does, and finishing the WIP (estimate 3–4 h); or (b) keeping `loop/m1`'s code and proving both laws through the `Lv` walk (estimate 4–6 h, no behaviour change).
