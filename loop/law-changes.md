# Law changes

Each law whose statement in `kernel/LAWS.bend` differs from `main`, with why the new statement is not weaker than the old. `scripts/acceptance.py --base origin/main` fails for a changed law missing here and for an entry whose law did not change. The review before merging into `main` reads every entry; the merge deletes them.

One line per law: `` - `law.name`: why ``.

- `amf.handover.guarded`: every clause of main stays word for word; one is added, that a step stopping timer k, which no session holds, leaves no handover pending under k. Its premise only sets aside a session's guard under the same key, which every reachable state rules out (`state.ids.free`: context keys odd, session keys even).
- `smf.establish.failure_releases`: every conjunct of main stays word for word, with one more variable (`ctx`); the three failures past the Accept that drop a session (its guard while being set up, the Session Modification refused or unanswered) gain a conjunct: when the session's UE holds a NAS context, the step's first action is the PDU Session Resource Release Command to its gNB with the PDU Session Release Command inside (`Gs.Gsm.released`).
