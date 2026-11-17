# Law changes

Each law whose statement in `kernel/LAWS.bend` differs from `main`, with why the new statement is not weaker than the old. `scripts/acceptance.py --base origin/main` fails for a changed law missing here and for an entry whose law did not change. The review before merging into `main` reads every entry; the merge deletes them.

One line per law: `` - `law.name`: why ``.

- `smf.releases.sent`: an exact restatement: its first two conjuncts stay word for word; the third states `Gs.Gsm.n2_release`'s outcome exactly, now with the action `PduRelease` that carries the PDU Session Release Command visibly instead of `UeSend` with the PDU already built, and a fourth says that action renders the very frame the old `UeSend` did.
- `smf.establish.failure_releases`: every conjunct of main stays word for word, with three more variables (`opre`, `opost`, `fl`); a conjunct is added for a failure main left unstated: a setup response listing the session set up, in the last item naming it, with a tunnel that does not read sends its Session Deletion Request, its guard started right after it (`Up.N4.deleted`), and, when the UE holds a NAS context, the PDU Session Resource Release Command to its gNB with the PDU Session Release Command inside sealed under the context's keys (`Gs.Gsm.told_gnb`), whatever the items around it. The three `Gs.Gsm.tells_gnb` conjuncts of main keep their text; their meaning goes through `Gs.Gsm.n2_release`, which now builds a `PduRelease` action, and the rendering conjunct of `smf.releases.sent` says that action renders the frame main's `UeSend` did.
