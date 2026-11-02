# `--verdict` overflows the machine stack on a string dispatch over large callees

Status: draft, not filed. Found by the loop in ticket 13 (the generated NGAP codec).

## What was attempted

`kernel/ngap/gen/types.bend` (about 10k lines, 1700 defs) ended with a dispatch by message
name:

```
def Ie.check(msg: String, id: Nat, +value: B.Bytes()) -> Maybe<&2, Bool>:
  match msg:
    case "DownlinkNASTransport":
      DownlinkNASTransport.ie_check(id, value)
    ... (16 cases)
    case _:
      None{}
```

where each `X.ie_check` is a `match id` over Nat literals whose arms call the generated
`T.roundtrips` of that IE's type. `bend types.bend --check-only` and `bend types.bend` accept the
module in about ten seconds. `bend types.bend --verdict` dies with

```
Error: the machine stack overflowed (a deep recursion, or a literal too large to expand)
```

Bisecting by prefix shows every other definition of the module passes `--verdict`, including the
sixteen `X.ie_check` functions; only the `Ie.check` block triggers the overflow. Replacing the
string scrutinee by a pair of `Nat`s with the same sixteen arms and the same callees
(`match kind code: case 0n 21n: ...`) passes `--verdict` in the same time as the plain check.

Smaller analogues do not reproduce it: a sixteen-arm string match returning literals, a
sixteen-arm string match over small `match id` callees (three arms each calling one recursive
function), and 40-character string literals all pass `--verdict`.

## Reproduction

The full-size reproduction is the repository at commit `3856a68`:

```
git checkout 3856a68
bend kernel/ngap/gen/types.bend --verdict
```

(`bend kernel/ngap/gen/types.bend --check-only` passes at that commit.) No smaller file found yet.

## Environment

- `bend version`: 2.0.39
- `uname -sm`: Linux x86_64
- `clang --version`: Ubuntu clang version 18.1.3 (1ubuntu1)

## Workaround

The dispatch now takes the (PDU kind, procedure code) pair that NGAP-ELEMENTARY-PROCEDURES binds
to each message instead of the message name (commit `3297e7d`), which is also what a PDU actually
carries.
