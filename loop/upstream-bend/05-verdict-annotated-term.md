# `--verdict` asks for "an annotated term" where the checker accepts the proof

Status: draft, not filed. Found by the loop in ticket 37 (one walk over the step function).

## What was attempted and what happened

Two proofs that `bend kernel/PROOF.bend` accepts are refused by `bend kernel/PROOF.bend --verdict`
with

```
expected: an annotated term
observed: λx8 => λx9 => (({λx10 => λx11 => ((proofs_2f_liveness.Pv.all +x0) x10) : ...} x8) x9)
Sorry - this is a mismatch between the TypeScript implementation, and the formalized BendTT kernel.
```

1. A def whose result type is a def returning `Data` that applies an erased predicate,
   `def Walk.Tables(-inv: A -> B -> Bool, o: N.Step()) -> Data: {inv(.., ..) == True{} : Bool}`,
   bound by a law with `+pv = Inv.step(ues => ss => Pv.all(st, ues), ...)` and then passed where
   `{Pv.all(st, ..) == True{} : Bool}` is expected. Spelling the equality out in `Inv.step`'s
   result type, instead of `Walk.Tables(inv, ...)`, passes.
2. A template walk (`def Inv.tx(~inv, ~pre, ~put, ..., tx, st, e, h)`) given its `~put` as a
   zero-argument def that returns a lambda (`def Gd.tx_put() -> Inv.Put(Gd.inv, Inv.none): +st0
   => ep => ... => body`, passed as `~Gd.tx_put()`). The instance `Inv.tx.qvvvvvvvv_1` fails with
   the same message, the observed term being a rewrite (`%`) inside the inlined lambda. The same
   ops written as defs with parameters and passed as `~Gd.tx_put` pass.

## Reproduction

Smaller files with the same shapes (a `Data` def over an erased two-argument predicate, a
template over a closed lambda, a template recursing on a list) all pass `--verdict`; the
mismatch shows only at the size of the kernel's proofs. The full-size reproduction is the
repository at the ticket 37 commits:

- case 1: at `7e60d26`, change the result type of `Inv.step` in `kernel/proofs/liveness.bend`
  to `PW.Walk.Tables(inv, K.Kernel.step(st, ev, entropy))` and run
  `bend kernel/PROOF.bend --verdict`;
- case 2: at the same commit, rewrite `Gd.tx_put` .. `Gd.tx_del_session` as zero-argument
  defs returning lambdas typed `Inv.Put(Gd.inv, Inv.none)` .. and pass them as `~Gd.tx_put()`.

## Environment

- `bend 2.0.39`
- `Linux x86_64`
- `clang version 21.1.8`

## Workaround

Case 1: the result type spelled out as the equality. Case 2: ops as defs with explicit
parameters.
