# 35 Procedure robustness

Depends on: 32, 33. Estimate: 3–4 h.

## Goal

1. **PFCP retransmission:** T1 = 3 s and N1 = 3 means three retransmissions after the first send, each with the same sequence number (TS 29.244 §6.4). Today there are two, each with a new sequence number.
2. **Failures after the Accept:** a Setting timeout, or a refused or timed-out modification, sends a PDU Session Release Command and frees the session. It does not send an Establishment Reject, and it does not drop the session silently.
3. **Identifier collisions:** when a 5G-TMSI, TEID or SEID drawn from entropy collides with a live one, draw again. Never evict on a collision. Takeover applies only to SUPI and 5G-GUTI (ticket 32).
4. **AMF-UE-NGAP-ID:** an ID of 2³² or more is an unknown UE, never folded into 32 bits (`Ngap.of_big`).
5. **Returning UEs:** a UE that comes back with an integrity-protected initial message (security header type 1) is read without verification, as TS 24.501 §4.4.6 allows. A Registration Request then goes to identification and authentication; a Service Request gets Service Reject #9.
6. **N4 association:** if Heartbeat Responses stop, the link goes down and new sessions are refused until it is back up.
7. **Config:** check the AMF Set ID and AMF Pointer ranges (10 and 6 bits) in `Cfg.complete`.
8. **Ids that are free by construction** (ticket 38 item 2; option A of its blocker, chosen 2026-11-07):
   - A context's guard timer is its AMF-UE-NGAP-ID, and a session's is its local SEID, drawn from a key space disjoint from the contexts'. Delete `next_timer`, `BumpTimer` and `Timers.*`.
   - An InitialUEMessage searches for an AMF-UE-NGAP-ID no context holds, and is refused when there is none.

   Law `state.ids.free`: the key an InitialUEMessage gives its context holds no other context, and no two rows share a guard timer. With it, `amf.takeover.authenticated` covers the wrap case.

## Verify

`scripts/check.sh`
