# 45 One downlink NAS COUNT per message in a Setup Response

Depends on: 40. Estimate: 2–4 h. Security: NAS COUNT reuse, as the review traced it; confirm it with the test first.

## Goal

From the review of ticket 40 item 3 (2026-11-16); the bug is already on `main`. `Gsm.set_ups` and `Gsm.faileds` (`kernel/smf/gsm.bend`) hand the same state to every item of a PDU Session Resource Setup Response, and `Gsm.give_up` reads the UE's NAS context from that state. When one response drops two sessions of one UE (two unreadable tunnels, or one unreadable tunnel and one failed item), both N1 PDU Session Release Commands are sealed under the same downlink COUNT, and the two `Rephase` writes move the COUNT on only once. With NEA1, NEA2 or NEA3 that reuses the keystream, which TS 33.501's NAS COUNT handling exists to prevent, and the UE drops the second message as a replay. No law states that each downlink NAS message gets a fresh COUNT, so the gate cannot see it.

1. Thread the NAS context through both lists, as `Gsm.releases` does for the sessions a Path Switch or Handover Notify drops (`smf.releases.sent`). Test it with two sessions of one UE dropped by one Setup Response: two Release Commands with consecutive SQNs, and the context left on the COUNT after them.
2. State a law that rules the bug out where the kernel seals downlink NAS: for instance that over any step every DL NAS message sent for a UE is sealed under a COUNT no earlier message of that step used, and the stored downlink COUNT ends past all of them. Choose the shape that covers every sender, not only this one.
3. Then extend `smf.establish.failure_releases` to the unreadable tunnel in a successful Setup Response (a failure after the Accept its comment says it leaves out), now that the Release Command it sends carries a fresh COUNT.

## Verify

`scripts/check.nu --strict`, `nix build .#checks.x86_64-linux.e2e`, and a review that finds no law weaker than on `main`.
