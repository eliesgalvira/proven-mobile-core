# 47 A session dropped during an N2 handover is told to the UE

Depends on: 45. Estimate: 1–3 h.

## Goal

From the review of ticket 45 (2026-11-17); the gap is on `main` too. While an N2 handover is pending the UE's context is in the `Handover` phase, whose NAS context `St.Phase.ctx` does not give (only `St.Phase.nas` does). So when a PDU Session Resource Setup Response, a guard or the UPF drops a session after the Accept during that time, the kernel deletes it at the UPF but sends no PDU Session Resource Release Command and no N1 PDU Session Release Command, and `smf.establish.failure_releases` (its `tells_gnb` and `told_gnb` conjuncts) asks for none: the UE keeps a session the core deleted. Ticket 40 item 3 left the same case at Handover Notify ("as before").

Decide what the best expert would (tell the UE through the source while the handover is pending, or once it ends, as TS 23.502's N2 handover allows), with its reason in `loop/decisions.md`; make the release reach the UE under a fresh downlink COUNT (`nas_sec.downlink_fresh`), and extend `failure_releases` to the handover phase without weakening it.

## Verify

`scripts/check.nu --strict`, `nix build .#checks.x86_64-linux.e2e`, and a review that finds no law weaker than on `main`.
