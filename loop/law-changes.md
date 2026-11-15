# Law changes

Each law whose statement in `kernel/LAWS.bend` differs from `main`, with why the new statement is not weaker than the old. `scripts/acceptance.py --base origin/main` fails for a changed law missing here and for an entry whose law did not change. The review before merging into `main` reads every entry; the merge deletes them.

One line per law: `` - `law.name`: why ``.
