# 46 A NAS COUNT never wraps under one key

Depends on: 45. Estimate: 3–5 h. Security: NAS COUNT reuse after wrap-around.

## Goal

From the review of ticket 45 (2026-11-17); the gap predates it. A NAS COUNT is 24 bits, a 16-bit overflow counter and the 8-bit sequence number (TS 24.501 §4.4.3.1, TS 33.501), and it must not wrap under one K_AMF: before it does, the AMF takes a new key (a new 5G-AKA run and Security Mode Control), since a wrapped COUNT gives a COUNT already used with the same key. Here `Count.next` has no ceiling and the overflow field is a full U32: after 2^24 messages `Count.value` leaves the 24-bit space the spec defines, and after 2^32 it repeats exactly, which `nas_sec.downlink_fresh` allows, as it only steps forward from the stored COUNT.

1. Bound the COUNT to 24 bits in `Count` and decide what the kernel does as it nears the end of the space, for downlink and uplink: the choice the best expert would make (re-authenticate and run Security Mode Control again, or release the UE) with its reason in `loop/decisions.md`.
2. State it: under one K_AMF no downlink COUNT is ever used twice, across steps as well as within one, and no COUNT outside 24 bits is sealed. Show the law fails on the unbounded code before the fix, as ticket 45 did.

## Verify

`scripts/check.nu --strict`, `nix build .#checks.x86_64-linux.e2e`, and a review that finds no law weaker than on `main`.
