# 40 Deferred from ticket 39

Depends on: 39. Estimate: 6–9 h. Not started; the next plan decides when.

## Goal

What ticket 39 left open on 2026-11-12:

1. **NG Setup ends handovers:** a NG Setup that releases an association's UEs first ends the handovers that association takes part in (`Ho.down`), so a pending handover to it doesn't wait for its guard, and the target of a handover it started gets UE Context Release Command. Today `Ho.down` rephases another association's UE without the SUPI check `amf.takeover.authenticated` requires, which is the obstacle.
2. **Handover law strength** (ticket 39 item 10):
   - `amf.ncc.step`: after any step, every UE's stored {NH, NCC} is unchanged, `Nh.next` of the old pair, or `Nh.initial`.
   - `amf.handover.guarded`: while a handover stays pending, no step emits `TimerCancel` for its key.

   Either through evidence at every leaf of the shared walk, or by `N.Step.of` deriving UE guard stops from the table diff, as `N.Gone.cancels` does for sessions.
3. **Releases** (ticket 39 items 1 and 9):
   - PDU Session Resource Release Command and Response, with their transfers, in the NGAP generator. Send the Command after a failure that follows the Accept (TS 23.502 §4.3.4.2).
   - PDU Session Release Command to the UE for sessions dropped in a Path Switch or at Handover Notify.
4. **N4 states** (ticket 39 item 3): `Asking` and `Beating` become one `Waiting` state. That shape was written and proven, but it hit Bend's C backend limit "an arity over 247", so it needs a reproduction and an upstream draft first. Probes are on branch `ticket/39-arity`.
5. **Proofs** (the rest of ticket 39 item 5): one lemma for the five `Owner.*` proofs and `Step.gnb_failed`; `Walk.pdu` made input-dependent, so `Req.*` in `kernel/proofs/ng_setup.bend` goes.
6. **Proof deduplication** (the Session Deletion review): one `Bool.or_mono` in `kernel/proofs/lib.bend` for `Rl.or_mono`, `Cf.or_mono` and `Hp.or_mono`; one keep lemma for the six `*_keep` copies; `Session.conflicts_sym`, as `Ue.conflicts_sym`; `Sessions.deleting` stated through `Tb.Table.get`; `Gsm.setup_gone` in place of `Lw.setup_gone`.

## Verify

`scripts/check.nu` and `nix flake check`.
