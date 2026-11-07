# 01 Bootstrap: layout, gate and test harness

Depends on: nothing.

## Goal

Create the project skeleton so every later ticket has a gate to pass:

- `kernel/` with `LAWS.bend`, `PROOF.bend`, `tests/`.
- `scripts/check.nu` exactly as described in `docs/spec/milestone-1.md` § Verification. Steps that have nothing to check yet pass trivially: there is no `edge/` yet, and the acceptance script tolerates laws for tickets that are not done (see below).
- `scripts/test-kernel.nu`: runs each `kernel/tests/*.bend`. It fails unless every one prints a line starting `PASS` or `SKIP`; with `--strict` (used by ticket 23), `SKIP` fails too. Run each file with a per-file timeout of 300 s.
- `scripts/acceptance.py`: parses the "Law" column of `docs/security/open5gs-advisories-2026.md`. With `--strict`, every named law must appear as `law <name>:` in `kernel/LAWS.bend`. Without it, only laws whose ticket is marked done in `loop/progress.md` are required.
- `scripts/gen-vectors.py`: converts `test-vectors/**/*.json` into Bend modules under `kernel/tests/vectors/`. It runs with `python3 -I`.

## Seams

`scripts/check.nu` exit status; the `PASS` lines of test files.

## Laws

`bytes.placeholder`: a trivial law (for example `List.length([]) == 0n`) so the PROOF/LAWS pair exists. Delete it in ticket 02.

## Done when

- `scripts/check.nu` exits 0 on a clean checkout after `.claude/hooks/session-start.sh` has run.
- A deliberately broken law makes it exit non-zero (try it, then revert).

## Verify

`scripts/check.nu`
