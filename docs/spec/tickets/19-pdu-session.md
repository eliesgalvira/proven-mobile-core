# 19 PDU session establishment

Depends on: 11, 14, 18.

## Goal

`kernel/smf.bend`. Read [the eUPF research](../../research/eupf-pfcp.md) for exactly what eUPF accepts.

1. **PFCP association:**
   - After `Config`, send Association Setup Request to the UPF. Retransmit with T1 = 3 s, N1 = 3; on exhausting retries, restart after 10 s.
   - Send a Heartbeat every 30 s.
   - Sessions are only set up while the association is up.
2. **UL NAS Transport** carrying an N1 SM PDU Session Establishment Request (request type initial, IPv4):
   - Check the DNN and S-NSSAI against config.
   - Allocate a UE IPv4 from the pool, a local SEID, and the N3 uplink TEID. eUPF's `ftup` is off, so the SMF allocates.
   - Send PFCP Session Establishment Request with uplink and downlink PDRs, FARs and one QER (QFI 1).
3. **On the PFCP response:**
   - Send PDUSessionResourceSetupRequest. Its transfer carries the UL NG-U UP TNL information, PDU session type IPv4, QoS flow 1 (5QI 9, ARP 8, no pre-emption) and Session-AMBR from config.
   - Its NAS-PDU is PDU Session Establishment Accept, carrying:
     - the default QoS rule (match-all);
     - Session-AMBR;
     - the PDU address;
     - ePCO with the configured DNS server, if the request asked for it.
4. **On PDUSessionResourceSetupResponse,** send PFCP Session Modification to give the downlink FAR its outer header creation (the gNB's TEID and address).
5. **PDU Session Modification Request:** reply with PDU Session Modification Reject, 5GSM cause `#31 request rejected, unspecified`. State is unchanged.
6. **Releasing a session** (deregistration or UE release): send PFCP Session Deletion and free the IP, TEID and SEID.
7. **Any failure** (bad DNN, pool empty, PFCP reject, PFCP timeout, setup failure from the gNB): send PDU Session Establishment Reject with the matching 5GSM cause, delete any PFCP session already created, and free everything allocated.

## Laws

- `smf.establish.reject_leaves_state` (advisory GHSA-ch5j-wv55-jmr6): a request that fails validation (DNN, S-NSSAI, session ID, pool) changes no SMF state.
- `smf.establish.failure_releases` (advisory GHSA-855g-699w-9w28): after a failure at any later step, no IP, TEID, SEID or session entry for that PDU session remains.
- `smf.modification.rejected` (advisory GHSA-x8ww-5xvf-qxg6): any PDU Session Modification Request yields Modification Reject and no state change. A later milestone that supports modification must replace this law with one stating that contradictory directives are rejected.
- `smf.packet_filters.capacity_reject` (advisory GHSA-g97g-v8mh-wg24): a session never holds more than 16 packet filters. A request that would exceed that is rejected, never truncated or crashed.
- `smf.epco.response_bounded` (advisory GHSA-f77j-h86j-2vcf): the ePCO in an Accept contains each container identifier at most once, however many times the request repeats it.
- `smf.ip_pool.unique`, `smf.teid.unique`: no two live sessions share a UE IPv4 or an uplink TEID.

## Tests

Replay the captured PDU Session Establishment exchange. eUPF responses come from `test-vectors/capture` when the capture used eUPF; otherwise, from hand-made PFCP responses built from the research doc. Hand-made failure cases: PFCP reject, PFCP timeout, pool exhausted, modification request.

## Verify

`scripts/check.nu`
