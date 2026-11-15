#!/usr/bin/env python3
"""Checks the acceptance list against kernel/LAWS.bend and kernel/PROOF.bend.

Every law named in the Law column of docs/security/open5gs-advisories-2026.md
must be stated as `law <name>:` in LAWS.bend and proven as `def L.<name>(` in
PROOF.bend or kernel/proofs/*.bend. Without --strict, only laws whose ticket is `done` in
loop/progress.md are required. A law is tied to the ticket in docs/spec/tickets/
that names it.

With --base REF, every law stated in REF's kernel/LAWS.bend must be stated
there now with the same text, or be listed in loop/law-changes.md with why its
new statement is not weaker. A listed law whose text did not change fails too,
so the list holds only what the next merge into main must review.
"""
import glob
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LAW_RE = re.compile(r"`([a-z0-9_]+(?:\.[a-z0-9_]+)+)`")


def advisory_laws():
    laws = []
    for line in (ROOT / "docs/security/open5gs-advisories-2026.md").read_text().splitlines():
        cells = [c.strip() for c in line.split("|")]
        if len(cells) < 10 or not cells[1].startswith("[GHSA-"):
            continue
        laws.extend(LAW_RE.findall(cells[8]))
    return laws


def law_tickets():
    tickets = {}
    for path in sorted(glob.glob(str(ROOT / "docs/spec/tickets/*.md"))):
        number = Path(path).name.split("-")[0]
        for law in LAW_RE.findall(Path(path).read_text()):
            tickets.setdefault(law, number)
    return tickets


def done_tickets():
    done = set()
    for line in (ROOT / "loop/progress.md").read_text().splitlines():
        m = re.match(r"\|\s*(\d+)\s*\|[^|]*\|\s*done\s*\|", line)
        if m:
            done.add(m.group(1))
    return done


def statements(text):
    laws = {}
    for m in re.finditer(r"^law\s+(\S+):\n((?:[ \t].*\n?)*)", text, re.M):
        laws[m.group(1)] = " ".join(m.group(2).split())
    return laws


def changed_laws(base, laws):
    old = statements(subprocess.run(["git", "show", f"{base}:kernel/LAWS.bend"], cwd=ROOT, check=True, capture_output=True, text=True).stdout)
    changed = {name for name, text in old.items() if laws.get(name) != text}
    listed = set(re.findall(r"^- `([^`]+)`", (ROOT / "loop/law-changes.md").read_text(), re.M))
    return [f"{name}: statement differs from {base}; keep the old one or list it in loop/law-changes.md" for name in sorted(changed - listed)] + [
        f"{name}: listed in loop/law-changes.md but its statement is as in {base}; delete the entry" for name in sorted(listed - changed)]


def main():
    args = sys.argv[1:]
    strict = "--strict" in args
    laws = statements((ROOT / "kernel/LAWS.bend").read_text())
    stated = set(laws)
    proof_files = [ROOT / "kernel/PROOF.bend", *glob.glob(str(ROOT / "kernel/proofs/*.bend"))]
    proven = set()
    for path in proof_files:
        proven.update(re.findall(r"^def\s+L\.(\S+)\(", Path(path).read_text(), re.M))
    tickets = law_tickets()
    done = done_tickets()
    failures = []
    required = 0
    for law in advisory_laws():
        ticket = tickets.get(law)
        if ticket is None:
            failures.append(f"{law}: no ticket in docs/spec/tickets/ names it")
            continue
        if not strict and ticket not in done:
            continue
        required += 1
        if law not in stated:
            failures.append(f"{law}: not stated in kernel/LAWS.bend (ticket {ticket})")
        elif law not in proven:
            failures.append(f"{law}: open, no proof in kernel/PROOF.bend (ticket {ticket})")
    if "--base" in args:
        failures.extend(changed_laws(args[args.index("--base") + 1], laws))
    for failure in failures:
        print("FAIL", failure)
    mode = "strict" if strict else "done tickets only"
    print(f"acceptance ({mode}): {required} laws required, {len(failures)} failures")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
