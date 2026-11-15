# Law changes

Each law whose statement in `kernel/LAWS.bend` differs from `main`, with why the new statement is not weaker than the old. `scripts/acceptance.py --base origin/main` fails for a changed law missing here and for an entry whose law did not change. The review before merging into `main` reads every entry; the merge deletes them.

One line per law: `` - `law.name`: why ``.

- `smf.deletion.keyed`: gone with the pending-deletion table it was about. A Session Deletion Request is now a session row in phase `Deleting`, whose guard timer is the session's key, so `state.ids.free` already says that it is neither a context's key nor timer 0 and the table keeps it apart from every other session's.
- `smf.deletion.retransmitted`: restated over the `Deleting` row instead of the pending table, with the same premises (no context under the key, the request unanswered) and the same retransmission: the same bytes, sequence number kept in the row, guard started again tagged with no UE. At the last retry it now also says the guard is stopped, which main's did not.
