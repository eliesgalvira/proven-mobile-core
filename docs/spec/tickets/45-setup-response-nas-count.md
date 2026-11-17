# 45 One downlink NAS COUNT per message in a Setup Response

Depends on: 40. Estimate: 2–4 h. Security: NAS COUNT reuse, as the review traced it; confirm it with the test first.

## Goal

From the review of ticket 40 item 3 (2026-11-16); the bug is already on `main`. `Gsm.set_ups` and `Gsm.faileds` (`kernel/smf/gsm.bend`) hand the same state to every item of a PDU Session Resource Setup Response, and `Gsm.give_up` reads the UE's NAS context from that state. When one response drops two sessions of one UE (two unreadable tunnels, or one unreadable tunnel and one failed item), both N1 PDU Session Release Commands are sealed under the same downlink COUNT, and the two `Rephase` writes move the COUNT on only once. With NEA1, NEA2 or NEA3 that reuses the keystream, which TS 33.501's NAS COUNT handling exists to prevent, and the UE drops the second message as a replay. No law states that each downlink NAS message gets a fresh COUNT, so the gate cannot see it.

1. Thread the NAS context through both lists, as `Gsm.releases` does for the sessions a Path Switch or Handover Notify drops (`smf.releases.sent`). Test it with two sessions of one UE dropped by one Setup Response: two Release Commands with consecutive SQNs, and the context left on the COUNT after them.
2. State a law that rules the bug out where the kernel seals downlink NAS: for instance that over any step every DL NAS message sent for a UE is sealed under a COUNT no earlier message of that step used, and the stored downlink COUNT ends past all of them. Choose the shape that covers every sender, not only this one.
3. Then extend `smf.establish.failure_releases` to the unreadable tunnel in a successful Setup Response (a failure after the Accept its comment says it leaves out), now that the Release Command it sends carries a fresh COUNT.

## Verify

`scripts/check.nu --strict`, `nix build .#checks.x86_64-linux.e2e`, and a review that finds no law weaker than on `main`.

## Done

- The bug, confirmed first: on the old kernel the test with two sessions of one UE dropped by one Setup Response failed on consecutive SQNs and on `nas_sec.downlink_fresh` (commit 02c8f9c, `kernel/tests/pdu_session.bend`); the law's statement is false there, so no proof of it exists for that kernel.
- One abstraction for every sender: a procedure that sends NAS takes the UE's context, seals each message under it in turn and writes the context it leaves once (`N.Told`, `N.Out.written`, `N.Out.dl`). A Setup Response runs the context through its items (`Gsm.Item`, `Gsm.then`, `Gsm.after`) and writes it once after the last (`Gsm.under`); `Gsm.give_up` goes through the same path. The PDU Session Resource Release Command is its own action (`N.PduRelease`) so the NAS it carries is visible; its frame is the old one (`smf.releases.sent`). Retransmissions (T3560 Security Mode Command, T3550 Registration Accept) are sealed afresh under the next COUNT; before a context the stored message goes again only when plain (`Gmm.plain_again`).
- `nas_sec.downlink_fresh` (`kernel/LAWS.bend`), over any step: the protected messages to key k are sealed in turn from the COUNT k's context held (from 0 under new keys), and the context k holds after holds the COUNT after the last (`N.Fresh.Law`). Proven through the walk (`kernel/proofs/downlink.bend`): every outcome seals and writes so (`PF.Fs.ok`, carried by `PL.Lv.does`), and the rows under k hold it from the first write of k on (`PH.Rw.Fresh`).
- `smf.establish.failure_releases` gains the unreadable tunnel in a successful Setup Response: its Session Deletion Request goes out, its guard right after it, whatever the items around it (`loop/law-changes.md`).
- e2e: no case. The AMF puts one session in each PDU Session Resource Setup Request, and UERANSIM and PacketRusher answer each request with its own response, every session set up with a tunnel that reads; a response that drops two sessions needs a gNB that sends one, which only the kernel tests build (crafted bytes, `kernel/tests/pdu_session.bend`).
- After review: `N.Out.seal` is the only call of `Nas.protect`, and every sender goes through it (`N.Out.then` threads the releases, `Gsm.releases` is an `N.Told()`). `nas_sec.downlink_fresh` no longer lets a held context's COUNT start again: keys must be the same in every field, and a step that leaves no context still seals under the old context's keys from its COUNT (`kernel/tests/pdu_session.bend`, keys with a bearer of 33). The unreadable-tunnel conjunct of `smf.establish.failure_releases` also asks for the Release Command to the gNB under the UE's keys (`Gs.Gsm.told_gnb`).
