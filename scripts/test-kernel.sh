#!/usr/bin/env bash
# Runs every kernel/tests/*.bend. Each must exit 0, print no FAIL line and
# print a line starting PASS or SKIP. With --strict, SKIP fails too.
# Tests are compiled to a binary first: `bend file.bend` overflows the machine
# stack on million-element lists where the binary does not (loop/upstream-bend/01).
set -uo pipefail
cd "$(dirname "$0")/.."

strict=0
[ "${1:-}" = "--strict" ] && strict=1
shopt -s nullglob
status=0
bin=$(mktemp -d)
trap 'rm -rf "$bin"' EXIT

for f in kernel/tests/*.bend; do
  name=$(basename "$f" .bend)
  if out=$(timeout 300 bend "$f" -o "$bin/$name" 2>&1); then
    out=$(timeout 300 "$bin/$name" 2>&1)
    code=$?
  else
    code=1
  fi
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
