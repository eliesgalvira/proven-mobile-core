# 39 Second simplification and N2 session release

Depends on: 35–38. Estimate: 3–4 h.

## Goal

What the 2026-11-07 merge review left after the pre-merge fixes:

1. **N2 release:** after a failure following the Accept, send PDU Session Resource Release Command over N2 as well as the N1 release (TS 23.502 §4.3.4.2), so the gNB frees its radio and tunnel resources. Add the message, its response and its transfers to the NGAP generator's set.
2. **Session Deletion retransmission** (TS 29.244 §6.4): resend up to N1 = 3 times with the same sequence number. This needs a pending-deletion table with its own guard timers, in a key space `state.ids.free` keeps apart from new sessions' ids. It is the acceptance report's one open gap.
3. **N4 state machines:** `Asking` and `Beating` become one "outstanding request" state with a kind field.
4. **Draws and walks:**
   - one draw instead of `Ip.teid_from` and `Ip.seid_from`;
   - one walk instead of `Sessions.has_ip` and `has_teid`;
   - `N4.deletions` returns the next sequence number, so `deletion_count` goes.
5. **Proofs:**
   - one lemma from `Fr.Pdu.read`/`Fr.Ies.read` to the route, replacing the five `Owner.*` copies and `Step.gnb_failed`;
   - make `Walk.pdu` input-dependent so `Req.*` in `proofs/ng_setup.bend` goes.
6. **Edge test:** the kernel-exit closure is built once.
7. **Script names:** `scripts/check.sh` and `scripts/test-kernel.sh` are nushell; rename them to `.nu` and update every citation.

8. **NG Setup before UE messages:** InitialUEMessage and every other UE-associated NGAP message is refused from an association that hasn't completed NG Setup. Today only Path Switch checks this. State it as a law.
9. **Sessions dropped in a Path Switch:** tell the UE with a PDU Session Release Command (TS 23.502 §4.9.1.2.2). Today only the target gNB is told.

## Verify

`scripts/check.sh` (or its new name) and `nix build .#checks.x86_64-linux.e2e`.
