# 30 End to end handover

Depends on: 24, 27, 28. Estimate: 2–3 h.

## Goal

Extend `e2e/test.nix` with a second gNB node (10.33.0.31) and, using the simulator chosen in ticket 24:
- an Xn handover with a ping before and after;
- an N2 handover with a ping before and after.

Each prints `E2E PASS: <name>` or fails with `E2E FAIL: <step>`. If ticket 24 found no simulator for a kind of handover, leave that case out and note it in `loop/progress.md`.

## Verify

`nix build .#checks.x86_64-linux.e2e -L`
