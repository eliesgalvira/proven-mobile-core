# Law changes

Each law whose statement in `kernel/LAWS.bend` differs from `main`, with why the new statement is not weaker than the old. `scripts/acceptance.py --base origin/main` fails for a changed law missing here and for an entry whose law did not change. The review before merging into `main` reads every entry; the merge deletes them.

One line per law: `` - `law.name`: why ``.

- `amf.handover.guarded`: every clause of main stays word for word; one is added, that a step stopping timer k, which no session holds, leaves no handover pending under k. Its premise only sets aside a session's guard under the same key, which every reachable state rules out (`state.ids.free`: context keys odd, session keys even).
