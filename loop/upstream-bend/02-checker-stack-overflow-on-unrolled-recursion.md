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

## Smallest reproduction

```python
import Base

def step(z: List<&2, U32>) -> List<&2, U32>:
  match z:
    case Nil{}:
      Nil{}
    case x <> rest:
      U32.add(x, 1) <> step(rest)

def loop(n: Nat, z: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      z
    case 1n+p:
      loop(p, step(z))

def many(z: List<&2, U32>) -> List<&2, U32>:
  loop(100000n, z)

law many.same:
  for z: List<&2, U32>
  {List.length(&2, U32, many(z)) == List.length(&2, U32, many(z)) : Nat}

def many.same(z):
  {==}
```

`bend repro.bend` overflows the machine stack while normalising `many(z)` for
the symbolic `z`; with `1000n` it checks in a moment. (The project's case hit
the limit at 254 iterations because each step wraps several function calls.)

## Versions

- bend 2.0.39
- Linux x86_64
- Ubuntu clang version 18.1.3 (1ubuntu1)

## Workaround used here

The loop counter is produced by a match on the symbolic input
(`Fe.inv.fuel` in `kernel/crypto/x25519.bend`): at run time it is the constant
list of 254 steps, in a proof it is stuck, so nothing unrolls. The Montgomery
ladder iterates over the scalar's bit list for the same reason.
