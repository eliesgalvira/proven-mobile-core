import sys

# gen.py WIDTH COUNT OUT: a record of WIDTH U32 fields, COUNT of them live
# across one IO bind in main.
w, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
fields = ", ".join(f"f{i}: U32" for i in range(w))
lines = [
    "import Base",
    "",
    f"# A record of {w} U32 words: under the 247-word cap, so it is kept unboxed.",
    "type R is Data:",
    f"  R{{{fields}}}",
    "",
    "def R.make(x: U32) -> R:",
    "  R{" + ", ".join(["x"] + ["0"] * (w - 1)) + "}",
    "",
    "def R.first(r: R) -> U32:",
    "  match r:",
    "    case R{" + ", ".join(["x"] + ["_"] * (w - 1)) + "}:",
    "      x",
    "",
    "def main() -> IO(Unit):",
    "  do IO<Unit>:",
]
for j in range(n):
    lines.append(f"    +r{j} : R = R.make({j + 1})")
lines.append('    IO.print("start")')
for j in range(n):
    lines.append(f"    IO.print(U32.show(R.first(r{j})))")
open(out, "w").write("\n".join(lines) + "\n")
