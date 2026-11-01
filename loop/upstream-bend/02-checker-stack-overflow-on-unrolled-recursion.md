# The checker overflows the machine stack when a type normalises a long fixed-count recursion

Status: draft, not filed. Found by the loop in ticket 08 (the `x25519.length` law).

## What was attempted

A law stated that a function's output has 32 bytes. The function ends with a
field inversion written as a recursion on a concrete `Nat` counter (254
squarings). Checking the proof made the checker normalise the type, and the
normaliser unrolled all 254 steps on a symbolic argument, nesting one stuck
multiplication inside the next. `bend PROOF.bend` then died with

```
Error: the machine stack overflowed (a deep recursion, or a literal too large to expand)
```

The same file checked fine when the proof module was loaded on its own (the
definition order or parallel scheduling changes which error is reported first),
so the failure looked intermittent. `ulimit -s unlimited` did not reliably help.

## Reproduction

A small file with a 100000-step counter loop over a symbolic list does not
reproduce it, so the trigger is the shape of the unrolled term, not its
depth alone. The project reproduces it exactly:

1. check out commit `c2583e1` of this repository;
2. in `kernel/crypto/x25519.bend`, `Fe.inv` is `Fe.inv.go(253n, a, a)`, a
   recursion on a concrete `Nat`, and each step calls `Fe.mul`, which
   normalises a 32-column product through four carry passes;
3. add the proof `def L.x25519.length(k, u)` from `kernel/proofs/suci.bend`
   at commit `8aa8220`, but with the original `Fe.inv`;
4. `bend kernel/PROOF.bend` overflows; with the fuel-list `Fe.inv` of commit
   `8aa8220` the same file prints ALL PROOFS CHECK.

A smaller reproduction still has to be isolated.

## Versions

- bend 2.0.39
- Linux x86_64
- Ubuntu clang version 18.1.3 (1ubuntu1)

## Workaround used here

The loop counter is produced by a match on the symbolic input
(`Fe.inv.fuel` in `kernel/crypto/x25519.bend`): at run time it is the constant
list of 254 steps, in a proof it is stuck, so nothing unrolls. The Montgomery
ladder iterates over the scalar's bit list for the same reason.
