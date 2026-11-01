#!/usr/bin/env bash
# Keeps a cloud loop session working while eligible tickets remain (AGENTS.md § The implementation loop).
set -uo pipefail
[ "${CLAUDE_CODE_REMOTE:-}" = "true" ] || exit 0
cd "$CLAUDE_PROJECT_DIR" || exit 0
[ -f loop/progress.md ] || exit 0

git fetch -q origin 2>/dev/null
git rev-parse -q --verify refs/remotes/origin/loop/stop >/dev/null && exit 0
grep -qE '^\| [0-9]+ \|[^|]*\| (todo|in-progress) \|' loop/progress.md || exit 0

state=/tmp/loop-stop-guard
head=$(git rev-parse HEAD 2>/dev/null)
read -r last count 2>/dev/null < "$state" || { last=""; count=0; }
if [ "$head" = "$last" ]; then count=$((count + 1)); else count=1; fi
echo "$head $count" > "$state"
[ "$count" -gt 3 ] && exit 0

printf '%s\n' '{"decision":"block","reason":"Tickets remain in loop/progress.md. Follow AGENTS.md § The implementation loop: commit and push what you have, then take the next eligible ticket. If every remaining ticket is blocked by a blocked or needs-human ticket, mark them so in loop/progress.md, push, and stop."}'
