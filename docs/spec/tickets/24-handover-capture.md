# 24 Handover capture and simulator

Depends on: nothing in milestone 2. Estimate: 2–3 h.

## Goal

1. Find a RAN simulator that performs Xn-based and N2-based handover between two gNBs against Open5GS 2.8.0. Read UERANSIM 3.3.0's source first, and PacketRusher's as the alternative. Record what each supports in `docs/research/handover-simulator.md`.
2. With the chosen simulator, extend `test-vectors/capture/setup` to capture one Xn handover and one N2 handover (including one Handover Cancel) after registration and PDU session establishment. Add the bytes and secrets to `test-vectors/capture/` in the same format as milestone 1's capture: messages in wire order, and the NH and NCC values each handover produced.
3. If no simulator supports a kind of handover, say so in the research note, and mark the tickets that need its vectors so they use hand-built vectors from TS 38.413 instead.

## Verify

`python3 -I scripts/gen-vectors.py --check` and the research note exists.
