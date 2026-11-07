#!/usr/bin/env python3
# Keeps a cloud loop session working while eligible tickets remain (AGENTS.md § The implementation loop).
import json
import os
import re
import subprocess
from pathlib import Path

STATE = Path("/tmp/loop-stop-guard")


def git(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], capture_output=True, text=True)


def main() -> None:
    if os.environ.get("CLAUDE_CODE_REMOTE") != "true":
        return
    try:
        os.chdir(os.environ["CLAUDE_PROJECT_DIR"])
    except (KeyError, OSError):
        return
    progress = Path("loop/progress.md")
    if not progress.is_file():
        return

    git("fetch", "-q", "origin")
    if git("rev-parse", "-q", "--verify", "refs/remotes/origin/loop/stop").returncode == 0:
        return
    if not re.search(r"^\| [0-9]+ \|[^|]*\| (todo|in-progress) \|", progress.read_text(), re.MULTILINE):
        return

    head = git("rev-parse", "HEAD").stdout.strip()
    try:
        last, count = STATE.read_text().split()[:2]
        count = int(count)
    except (OSError, ValueError):
        last, count = "", 0
    count = count + 1 if head == last else 1
    STATE.write_text(f"{head} {count}\n")
    if count > 3:
        return

    print(json.dumps({"decision": "block", "reason": "Tickets remain in loop/progress.md. Follow AGENTS.md § The implementation loop: commit and push what you have, then take the next eligible ticket. If every remaining ticket is blocked by a blocked or needs-human ticket, mark them so in loop/progress.md, push, and stop."}, ensure_ascii=False))


main()
