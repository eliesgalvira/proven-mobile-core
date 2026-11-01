#!/usr/bin/env bash
# Runs every kernel/tests/*.bend. Each must exit 0, print no FAIL line and
# print a line starting PASS or SKIP. With --strict, SKIP fails too.
set -uo pipefail
cd "$(dirname "$0")/.."

strict=0
[ "${1:-}" = "--strict" ] && strict=1
shopt -s nullglob
status=0

for f in kernel/tests/*.bend; do
  out=$(timeout 300 bend "$f" 2>&1)
  code=$?
  printf '%s\n' "$out" | sed "s|^|$f: |"
  if [ "$code" -ne 0 ] || grep -q '^FAIL' <<<"$out" || ! grep -qE '^(PASS|SKIP)' <<<"$out"; then
    echo "$f: FAILED (exit $code)"
    status=1
  elif [ "$strict" -eq 1 ] && grep -q '^SKIP' <<<"$out"; then
    echo "$f: SKIPPED tests are not allowed with --strict"
    status=1
  fi
done

exit "$status"
