# `bend file.bend` overflows the machine stack where the compiled binary does not

Status: draft, not filed. Found by the loop in ticket 04 (SHA-256 of the 1,000,000-byte FIPS 180-4 example).

## What was attempted

Running a test file whose `main` returns `IO(Unit)` with `bend file.bend`. It builds a million-element list with `List.replicate` and appends to it. The run dies with `bend: memory fault (machine stack overflow?)`, also under `ulimit -s unlimited`. The same file compiled with `bend file.bend -o file` and run as `./file` prints the expected output under the default 8 MiB stack.

## Smallest reproduction

```python
import Base

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(List.length(&2, U32, List.replicate(U32, 1000000n, 0))))
```

`bend repro.bend` → `bend: memory fault (machine stack overflow?)`. `bend repro.bend -o repro && ./repro` → `1000000`.

## Versions

- bend 2.0.39
- Linux x86_64
- Ubuntu clang version 18.1.3 (1ubuntu1)

## Workaround used here

`scripts/test-kernel.sh` compiles every test to a binary before running it.
