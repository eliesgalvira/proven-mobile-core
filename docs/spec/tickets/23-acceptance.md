# 23 Acceptance audit

Depends on: every earlier ticket.

## Goal

1. `python3 -I scripts/acceptance.py --strict` passes: every law named in the advisory log exists in `kernel/LAWS.bend`, and `bend kernel/PROOF.bend --verdict` prints ALL PROOFS CHECK.
2. Write `loop/acceptance-report.md`. For each in-scope advisory, give:
   - the law and its `file:line`;
   - one sentence on why that law rules the bug out;
   - whether the law is at least as strong as the ticket's wording. List every place it is not; there should be none.
3. Diff `kernel/LAWS.bend` against each ticket's law text and list every deviation.

## Verify

`python3 -I scripts/acceptance.py --strict && scripts/check.sh`
