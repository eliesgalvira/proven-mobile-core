# 44 A reset association ends the wait for its released side

Depends on: 40. Estimate: 1–2 h.

## Goal

From the review of ticket 40 item 1 (2026-11-16). After an N2 handover to target `t` ends before `t` answered (a cancel, or the preparation guard firing while `t` was asked), the context keeps `released = Some{Side{t, None}}`, and `Side.unanswered` refuses a new Handover Required of that UE to `t` (`amf.handover.responses_correlated`, ticket 28 review), until the UE leaves `Registered`. When `t` goes down or sends NG Setup, its UE-related contexts are gone (TS 38.413 §8.7.1.1), so no late acknowledgement from `t` can cross a new attempt any more, but `Route.reset` and `Ho.down` leave the field as it is: the UE still cannot be handed to `t`.

Clear a released side naming `t` when `t`'s association goes down or sends NG Setup, in the same `Route.reset` step, keeping `amf.handover.responses_correlated` and every other law at least as strong. Test it in `kernel/tests/handover.bend`: an early cancel to `t`, then `t`'s NG Setup, then a Handover Required to `t` goes ahead.

## Verify

`scripts/check.nu --strict`, `nix build .#checks.x86_64-linux.e2e`, and a review that finds no law weaker than on `main`.
