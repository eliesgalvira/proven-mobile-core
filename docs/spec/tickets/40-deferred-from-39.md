# 40 Deferred from ticket 39

Depends on: 39. Estimate: 6–9 h.

## Goal

What ticket 39 left open on 2026-11-12:

1. **NG Setup ends handovers:** a NG Setup that releases an association's UEs first ends the handovers that association takes part in (`Ho.down`), so a pending handover to it doesn't wait for its guard, and the target of a handover it started gets UE Context Release Command. Today `Ho.down` rephases another association's UE without the SUPI check `amf.takeover.authenticated` requires, which is the obstacle.

   Done: NG Setup and the association going down share `Route.reset` (`Ho.down`, then `Route.drop`). `Ho.down` ends a handover on the target's side only when `Ho.aimed` holds, so `amf.takeover.authenticated` keeps its statement, proven over the fold of `Ho.downs`: a key names one row of a unique table, so that row is rephased once, into a phase holding a security context, and keeps its owner through the sieve.
2. **Handover law strength** (ticket 39 item 10):
   - `amf.ncc.step`: after any step, every UE's stored {NH, NCC} is unchanged, `Nh.next` of the old pair, or `Nh.initial`.
   - `amf.handover.guarded`: while a handover stays pending, no step emits `TimerCancel` for its key.

   Either through evidence at every leaf of the shared walk, or by `N.Step.of` deriving UE guard stops from the table diff, as `N.Gone.cancels` does for sessions.

   Done, through evidence at every leaf (`Lv.stops`, `Lv.chain`, `Lv.seeds`); deriving the stops in `N.Step.of` would have changed the frames. `amf.ncc.step` holds where no two contexts share a key; its `Nh.initial` is of the K_AMF of the context's Security Mode and of the KgNB the same step sends it in Initial Context Setup (`Ng.Acts.seeds`). `amf.handover.guarded` holds for a key no session holds, and says that a step stopping the timer leaves no handover pending under it.
3. **Releases** (ticket 39 items 1 and 9):
   - PDU Session Resource Release Command and Response, with their transfers, in the NGAP generator. Send the Command after a failure that follows the Accept (TS 23.502 §4.3.4.2).
   - PDU Session Release Command to the UE for sessions dropped in a Path Switch or at Handover Notify.

   Done. The generator has PDU Session Resource Release Command and Response with their transfers (263 types, 32 views); `oracle.py` also checks both as the kernel builds them. A session dropped after the Accept sends its gNB the Command, the N1 PDU Session Release Command in its NAS-PDU, as the step's first action (`smf.establish.failure_releases`, extended). The Response changes no state (`smf.release_response.keeps_state`, which held on main too, when it went unhandled); one naming a live session is a warning, one for a UE the association does not own gets Error Indication (`amf.ue_key.unknown`, extended). The sessions a Path Switch or Handover Notify releases get PDU Session Release Command in DL NAS Transport through the target, after the acknowledgement or the source's release (`amf.path_switch.stored_capabilities`, restated; `amf.handover.notify_releases`, the step exactly). `smf.releases.sent` says what both release messages are, COUNT by COUNT. Not covered by a law: a setup response whose tunnel does not read also drops the session and sends the Command (tested).
4. **N4 states** (ticket 39 item 3), done: `Asking` and `Beating` are one `Waiting{req, request, seq, resent}`, `req` being `Setup` or `Heartbeat`. Bend's C backend limit "an arity over 247" is upstream draft 06; its workaround, `kernel/tests/pdu_session.bend`'s association checks in their own def, is applied.
5. **Proofs:** done. `PW.Rt.view`, `PW.Rt.ue` and `PW.Rt.owned` walk a UE message to its procedure, in place of the `Owner.*`, `Unknown.*` and `Step.gnb_failed` copies and the handover proofs' own routing; `PW.Walk.Ready` is indexed by what the request supports (`N.NgSetup.supported_*`), so `Req.answer`, `reply`, `view`, `ready`, `d1`, `ies` and `pdu` went.
6. **Proof deduplication:** done. `P.Keep.by` replaces 35 lemmas about `Tb.Table.keep`; `Session.conflicts_sym` replaces `Cf.l` and `Tg.same_l`; `Lw.setup_gone` is stated on `Gsm.setup_gone`, the deletion `kernel/smf/gsm.bend` wrote twice.

## Verify

`scripts/check.nu` and `nix flake check`.
