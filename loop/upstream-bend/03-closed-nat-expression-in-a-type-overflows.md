# A closed `Nat` expression of a few thousand in a type overflows the checker

Status: draft, not filed. Found by the loop in ticket 12 (the APER length determinant, bounded by 16384).

## What was attempted

A proof needed the fact `n < 2^14`. Written with a literal, `Nat.is_lt(n, 16384n)`, everything
checks. Written with an expression that evaluates to the same number, such as `Nat.pow2(14n)`
(`pow2` by `Nat.double`), `Nat.double(8192n)` or even `Nat.add(16383n, 1n)`, the checker dies as
soon as it has to normalise or print the type:

```
RangeError: Maximum call stack size exceeded
    at map (1:11)
    ...
      return Typ(term_higher(tm.g, env), tm.s);
```

or, in a larger program,

```
Error: the machine stack overflowed (a deep recursion, or a literal too large to expand)
```

A literal is kept compact, but the result of evaluating a closed expression is a unary numeral,
and the checker then walks it recursively. The same expression evaluated inside a `Bool` such as
`{Nat.is_lt(16383n, Nat.add(16383n, 1n)) == True{}}` checks fine, so only `Nat`-valued terms in
types are affected. The failure depends on the surrounding stack depth: a proof file that checks
on its own overflowed once it was imported into the project's `PROOF.bend`.

## Reproduction

```
import Base

def probe(n: Nat, v: {Nat.is_lt(n, Nat.add(16383n, 1n)) == True{} : Bool}) -> {Nat.is_lt(n, 16384n) == True{} : Bool}:
  Unit{}
```

`bend probe.bend --check-only` should report a type mismatch (`Unit{}` is not a proof); instead it
crashes with the `RangeError` above. Replacing `Nat.add(16383n, 1n)` by `16384n` gives the expected
mismatch error.

## Versions

- bend 2.0.39
- Linux x86_64
- Ubuntu clang version 18.1.3 (1ubuntu1)

## Workaround used here

Every large bound in `kernel/LAWS.bend`, `kernel/aper.bend` and `kernel/proofs/aper.bend` is a
literal token (`16384n`, `128n`). The generic lemmas are stated over a symbolic `Nat.pow2(w)`, and the
bridge between the two forms is always a `Bool` evaluation, `Nat.lt_le_trans(x, Nat.pow2(14n), 16384n,
proof, {==})`, never an equation between two `Nat` terms.
