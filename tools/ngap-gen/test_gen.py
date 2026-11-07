#!/usr/bin/env python3
"""Golden-output test: regenerating kernel/ngap/gen/ from the pinned ASN.1 must change nothing.

Run with python -I from the repository root. Exits 1 and prints a diff on any change."""
import difflib
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
GEN = ROOT / "tools/ngap-gen/gen.py"
ASN = ROOT / "tools/ngap-gen/asn"
COMMITTED = ROOT / "kernel/ngap/gen"


def main():
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run([sys.executable, "-I", str(GEN), str(ASN), tmp], check=True, stdout=subprocess.DEVNULL)
        fresh = {p.name: p.read_text() for p in pathlib.Path(tmp).iterdir()}
    committed = {p.name: p.read_text() for p in COMMITTED.iterdir() if p.suffix == ".bend"}
    status = 0
    for name in sorted(set(fresh) | set(committed)):
        if fresh.get(name) == committed.get(name):
            print(f"ok   {name}")
            continue
        status = 1
        print(f"DIFF {name}")
        sys.stdout.writelines(difflib.unified_diff(
            committed.get(name, "").splitlines(True), fresh.get(name, "").splitlines(True),
            f"kernel/ngap/gen/{name}", f"generated/{name}"))
    if status == 0:
        print("generated code is current")
    return status


if __name__ == "__main__":
    sys.exit(main())
