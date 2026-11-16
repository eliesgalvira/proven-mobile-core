# 40 Deferred from ticket 39

Depends on: 39. Estimate: 6–9 h. Not started; the next plan decides when.

## Goal

What ticket 39 left open on 2026-11-12:

1. **NG Setup ends handovers:** a NG Setup that releases an association's UEs first ends the handovers that association takes part in (`Ho.down`), so a pending handover to it doesn't wait for its guard, and the target of a handover it started gets UE Context Release Command. Today `Ho.down` rephases another association's UE without the SUPI check `amf.takeover.authenticated` requires, which is the obstacle.
2. **Handover law strength** (ticket 39 item 10), done:
   - `amf.ncc.step`: where no two contexts share a key, after any step a context's stored {NH, NCC} is the one it held or `Nh.next` of it, and a context that held none was in Security Mode and holds the first pair of a chain, NCC 1, from that K_AMF.
   - `amf.handover.guarded`'s new clause: a step that stops timer k, which no session holds, leaves no handover pending under k.

   Through evidence at every leaf of the shared walk (`Lv.stops`, `Lv.chain`); `N.Step.of` deriving the stops would have changed the frames.
3. **Releases** (ticket 39 items 1 and 9):
   - PDU Session Resource Release Command and Response, with their transfers, in the NGAP generator. Send the Command after a failure that follows the Accept (TS 23.502 §4.3.4.2).
   - PDU Session Release Command to the UE for sessions dropped in a Path Switch or at Handover Notify.
4. **N4 states** (ticket 39 item 3), done: `Asking` and `Beating` are one `Waiting{req, request, seq, resent}`, `req` being `Setup` or `Heartbeat`. Bend's C backend limit "an arity over 247" is upstream draft 06; its workaround, `kernel/tests/pdu_session.bend`'s association checks in their own def, is applied.
5. **Proofs:** done. `PW.Rt.view`, `PW.Rt.ue` and `PW.Rt.owned` walk a UE message to its procedure, in place of the `Owner.*`, `Unknown.*` and `Step.gnb_failed` copies and the handover proofs' own routing; `PW.Walk.Ready` is indexed by what the request supports (`N.NgSetup.supported_*`), so `Req.answer`, `reply`, `view`, `ready`, `d1`, `ies` and `pdu` went.
6. **Proof deduplication:** done. `P.Keep.by` replaces 35 lemmas about `Tb.Table.keep`; `Session.conflicts_sym` replaces `Cf.l` and `Tg.same_l`; `Lw.setup_gone` is stated on `Gsm.setup_gone`, the deletion `kernel/smf/gsm.bend` wrote twice.

## Verify

`scripts/check.nu` and `nix flake check`.
