#!/usr/bin/env bash
# End to end (docs/spec/tickets/22-e2e.md): build the core image, start eUPF,
# the data network, the core, then UERANSIM's gNB and UE; wait for the UE's
# PDU session and ping the data network through it. Prints E2E PASS or
# E2E FAIL: <step>, saves the containers' logs under $OUT, tears down.
# Needs: bend, cargo, docker with compose v2, nix (flakes) for the UERANSIM
# image, and the host's sctp kernel module loaded. KEEP_UP=1 leaves the stack up.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
CAPTURE="$ROOT/test-vectors/capture/setup"
OUT="${OUT:-$(mktemp -d -t speck5g-e2e.XXXXXX)}"
mkdir -p "$OUT/logs"
dc() { docker compose -f "$HERE/docker-compose.yml" "$@"; }

STEP=prerequisites
fail() {
  echo "E2E FAIL: $STEP"
  exit 1
}
teardown() {
  for s in core eupf gnb ue; do
    dc logs --no-color "$s" 2>&1 | sed 's/\x1b\[[0-9;]*m//g' > "$OUT/logs/$s.log" || true
  done
  echo "logs: $OUT/logs"
  if [ "${KEEP_UP:-0}" != 1 ]; then dc down -v --remove-orphans >/dev/null 2>&1 || true; fi
}
trap teardown EXIT

for tool in bend cargo docker nix; do command -v "$tool" >/dev/null || { echo "missing: $tool"; fail; }; done
docker info >/dev/null 2>&1 || { echo "the docker daemon is not reachable"; fail; }
grep -qw SCTP /proc/net/protocols || { echo "no SCTP in the host kernel (modprobe sctp)"; fail; }

STEP="build kernel"
(cd "$ROOT" && timeout 900 bend kernel/main.bend -o build/kernel) || fail

STEP="build edge"
(cd "$ROOT/edge" && timeout 900 cargo build --release --quiet) || fail

STEP="core image"
STAGE="$(mktemp -d)"
cp "$ROOT/build/kernel" "$ROOT/edge/target/release/edge" "$HERE/Dockerfile" "$STAGE/" || fail
docker build -q -t speck5g-core:e2e "$STAGE" >/dev/null || fail
rm -rf "$STAGE"

STEP="ueransim image"
docker image inspect speck5g-ueransim:3.3.0 >/dev/null 2>&1 \
  || docker load < "$(nix build --no-link --print-out-paths "$CAPTURE#ueransim-image")" || fail

STEP="start core"
dc down -v --remove-orphans >/dev/null 2>&1 || true
dc up -d eupf dn core || fail
for _ in $(seq 1 20); do
  dc logs core 2>&1 | grep -q "association with eUPF up" && break
  sleep 1
done
dc logs core 2>&1 | grep -q "association with eUPF up" || fail

STEP="start gnb"
dc up -d gnb || fail
for _ in $(seq 1 20); do
  dc logs gnb 2>&1 | grep -q "NG Setup procedure is successful" && break
  sleep 1
done
dc logs gnb 2>&1 | grep -q "NG Setup procedure is successful" || fail

STEP="register and establish"
dc up -d ue || fail
for _ in $(seq 1 40); do
  dc exec -T ue ip -4 -br addr show uesimtun0 2>/dev/null | grep -q '10\.45\.' && break
  sleep 1
done
dc exec -T ue ip -4 -br addr show uesimtun0 2>/dev/null | grep -q '10\.45\.' || fail

STEP="ping through eUPF"
dc exec -T ue ping -c 4 -i 0.5 -W 2 -I uesimtun0 10.33.0.40 | tee "$OUT/logs/ping.log" || fail

echo "E2E PASS"
