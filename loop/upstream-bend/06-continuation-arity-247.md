# The C backend refuses a continuation over 247 live words, where a def's parameters are boxed

Status: draft, not filed. Found by the loop in ticket 39 (one N4 `Waiting` state); reproduced in ticket 40.

## What was attempted and what happened

The N4 link states `Asking{seq, resent}` and `Beating{seq, resent}` were merged into one
`Waiting{req, request, seq, resent}`. That widens `S.State` by two words, as `Link` is laid out
flat inside it. The checker, `--verdict` and the JS backend accept the result; `bend
kernel/tests/pdu_session.bend -o <bin>` fails with

```
Error: an arity over 247
```

with no location. That test's `main` holds five `S.State`s, a `N.Step`, a User Location
Information and some bytes across its IO binds: 233 words in its widest continuation before the
change, 247 after it, and 248 with one more `U32` field in `Waiting`.

What the 247 counts: the C backend lays a non-recursive record of at most 247 words out flat, as
words, in every parameter and live variable. A code segment (a def body, or the continuation of a
non-tail call) takes as parameters the words of every value live across it, plus one for the
result, and fails when that passes 247. A def whose parameters pass 247 boxes its multi-word ones
instead; a continuation has no such fallback. 247 is where the 8-bit arity tag stops: 248 to 255
encode the power-of-two block classes of wide constructors.

Thresholds measured: live words across one call 246 builds, 247 fails (247 + 1 > 247), whether
one record of 247 words or several smaller ones (200 + 47, 124 + 123).

## Reproduction

One 247-word record (19 × 13 `U32`) live across a non-tail call. With 18 `Q`s (234 words), or
with `g(3n)` replaced by an operator, it builds. `bend repro.bend` prints `6`, `--verdict` prints
`ALL PROOFS CHECK`, `-o repro.js` builds and prints `6`; `-o repro.c` and `-o repro` fail.

```bend
import Base

type Q is Data:
  Q{a0: U32, a1: U32, a2: U32, a3: U32, a4: U32, a5: U32, a6: U32, a7: U32, a8: U32, a9: U32, a10: U32, a11: U32, a12: U32}

type R is Data:
  R{q0: Q, q1: Q, q2: Q, q3: Q, q4: Q, q5: Q, q6: Q, q7: Q, q8: Q, q9: Q, q10: Q, q11: Q, q12: Q, q13: Q, q14: Q, q15: Q, q16: Q, q17: Q, q18: Q}

def R.first(r: R) -> Q:
  match r:
    case R{q, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      q

def Q.first(q: Q) -> U32:
  match q:
    case Q{a, _, _, _, _, _, _, _, _, _, _, _, _}:
      a

def g(n: Nat) -> U32:
  match n:
    case 0n:
      0
    case 1n+p:
      U32.add(1, g(p))

def f(+x: U32) -> U32:
  +q : Q = Q{x, x, x, x, x, x, x, x, x, x, x, x, x}
  r : R = R{q, q, q, q, q, q, q, q, q, q, q, q, q, q, q, q, q, q, q}
  U32.add(g(3n), Q.first(R.first(r)))

def main() -> IO(Unit):
  IO.print(U32.show(f(3)))
```

`bend repro.bend -o repro.c` prints `Error: an arity over 247`. By contrast, `def h(r: R, y:
U32) -> U32` (248 words of parameters) called as `h(r, x)` builds; called as `h(r, g(3n))`, with
`r` live across `g`, it fails.

Not in `WONTFIX.txt` (checked at `fa4ba63`). The guide's SHADERS.md states the limit ("A def or
continuation takes at most 247 words"). The ask: a continuation boxes its multi-word live values
past 247 words, as a def's parameters already are; failing that, the error names the def and the
live values.

## Environment

- `bend 2.0.39`
- `Linux x86_64`
- `clang version 21.1.8`

## Workaround

Keep fewer wide values live at once. In `kernel/tests/pdu_session.bend`, the association and
heartbeat checks become their own IO def, called right after `o_tick` is made rather than at the
end of `main`, so `o_tick` (33 words) is dead before the widest continuation: 214 words with
`Waiting`. No kernel definition comes near the limit (the widest, in `Kernel.step`, is 109).
