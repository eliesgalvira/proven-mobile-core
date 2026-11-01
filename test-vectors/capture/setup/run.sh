#!/usr/bin/env bash
# Reproduce the golden 5G capture end to end:
#   1. build Open5GS 2.8.0 and UERANSIM 3.3.0 images from pinned nixpkgs (flake.nix)
#      and docker-load them;
#   2. bring up Open5GS + eUPF v0.7.2 + MongoDB + a data-network container;
#   3. register one UE (SUCI Profile A), open an IPv4 PDU session on DNN "internet",
#      ping the data network, recording NGAP/PFCP/GTP-U to $OUT/raw.pcap;
#   4. probe eUPF (retransmitted Session Establishment, missing Outer Header Removal,
#      issue #637) into $OUT/probe.pcap and $OUT/probe.json;
#   5. save logs and the subscriber record, then tear everything down
#      (KEEP_UP=1 leaves the stack running).
# Needs: nix (flakes), docker with compose v2, the host's sctp kernel module available.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT="${OUT:-$(mktemp -d -t speck5g-capture.XXXXXX)}"   # set OUT to choose the output directory
mkdir -p "$OUT/logs"
cd "$HERE"
dc() { docker compose -f "$HERE/docker-compose.yml" "$@"; }
FILTER='sctp or udp port 8805 or udp port 2152 or icmp'

start_capture() {  # $1 = output file
  dc exec -T capture tcpdump -i br-5gcap -U -s 0 -w - "$FILTER" > "$1" 2> "$OUT/logs/tcpdump.log" &
  CAP_PID=$!
  sleep 2
}
stop_capture() {
  dc exec -T capture pkill -INT tcpdump || true
  wait "$CAP_PID" || true
}

echo "== build + load Nix images =="
docker load < "$(nix build --no-link --print-out-paths "$HERE#open5gs-image")"
docker load < "$(nix build --no-link --print-out-paths "$HERE#ueransim-image")"

echo "== clean start =="
dc down -v --remove-orphans >/dev/null 2>&1 || true

echo "== core up =="
dc up -d mongo
for _ in $(seq 1 30); do dc exec -T mongo mongosh --quiet --eval 'db.runCommand({ping:1}).ok' >/dev/null 2>&1 && break; sleep 1; done
dc exec -T mongo mongosh --quiet open5gs /subscriber.js
dc up -d nrf
sleep 2
dc up -d ausf udm udr pcf nssf bsf eupf dn capture
sleep 3

echo "== capture: PFCP association, NG setup, registration, PDU session, ping =="
start_capture "$OUT/raw.pcap"
dc up -d smf amf
sleep 8   # NF registration with the NRF, PFCP association SMF -> eUPF
dc up -d gnb
sleep 3
dc up -d ue
for i in $(seq 1 40); do
  if dc exec -T ue ip -4 -br addr show uesimtun0 2>/dev/null | grep -q '10\.45\.'; then
    echo "   uesimtun0 up after ${i}s"; break; fi
  sleep 1
done
dc exec -T ue ip -4 -br addr show uesimtun0
dc exec -T ue ping -c 4 -i 0.5 -I uesimtun0 10.33.0.40 | tee "$OUT/logs/ping.log" || true
sleep 2
stop_capture

echo "== eUPF probes =="
start_capture "$OUT/probe.pcap"
docker run --rm --network container:speck5g-smf-1 \
  -v "$HERE/pfcp_probe.py:/probe.py:ro" -v "$OUT/raw.pcap:/raw.pcap:ro" \
  --entrypoint python3 \
  nicolaka/netshoot:v0.14@sha256:7f08c4aff13ff61a35d30e30c5c1ea8396eac6ab4ce19fd02d5a4b3b5d0d09a2 \
  /probe.py /raw.pcap > "$OUT/probe.json" || true
sleep 2
stop_capture
docker inspect -f 'eupf state={{.State.Status}} exit={{.State.ExitCode}}' speck5g-eupf-1 | tee "$OUT/logs/eupf-state.txt"
# Does the real UE's session still carry traffic after the duplicate session?
dc exec -T ue ping -c 3 -W 1 -I uesimtun0 10.33.0.40 > "$OUT/logs/ping-after-probes.log" 2>&1 || true
tail -2 "$OUT/logs/ping-after-probes.log"
dc exec -T dn curl -s http://10.33.0.20:8080/api/v1/pfcp_sessions > "$OUT/logs/eupf-sessions.json" || true

echo "== logs =="
for s in amf smf ausf udm eupf gnb ue; do
  dc logs --no-color "$s" 2>&1 | sed 's/\x1b\[[0-9;]*m//g' > "$OUT/logs/$s.log" || true
done
dc exec -T mongo mongosh --quiet open5gs --eval \
  'printjson(db.subscribers.findOne({imsi:"001010000000001"},{security:1,_id:0}))' > "$OUT/logs/subscriber-after.txt"

if [ "${KEEP_UP:-0}" != 1 ]; then dc down -v --remove-orphans; fi

echo "== filter + extract vectors =="
TOOLS="$(nix build --no-link --print-out-paths "$HERE#extract-tools")"
"$TOOLS/bin/tshark" -r "$OUT/raw.pcap" -Y 'sctp || pfcp || gtp' -F pcapng -w "$OUT/registration-pdu.pcapng"
"$TOOLS/bin/tshark" -r "$OUT/probe.pcap" -Y 'pfcp || gtp || icmp' -F pcapng -w "$OUT/eupf-probes.pcapng"
PATH="$TOOLS/bin:$PATH" python3 -I "$HERE/extract.py" "$OUT/registration-pdu.pcapng" "$HERE" "$OUT/vectors.json"
echo "== done: $OUT/registration-pdu.pcapng, $OUT/vectors.json, $OUT/eupf-probes.pcapng, $OUT/probe.json =="
