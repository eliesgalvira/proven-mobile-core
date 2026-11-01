# Open5GS security advisories, 2026: the acceptance list

These are all 42 security advisories published on the Open5GS GitHub repository between 2026-06-05 and 2026-10-22, read on 2026-10-30 with `gh api repos/open5gs/open5gs/security-advisories`. Most were reported against v2.8.0. Each row records which part of the kernel would own the bug and the property whose proof would make it impossible.

The kernel is done for a row when the property in that row is proven for the kernel's code. Rows marked **out** sit in components this project has deliberately left out (see `AGENTS.md`); they stay here because the same property returns when the scope grows.

Kernel parts:

- **Codec**: reading and writing messages.
- **Crypto**: 5G cryptography.
- **Conversation**: the state machine of each procedure.
- **Packet rules**: choosing what to do with each packet.
- **Thin layer**: code outside the kernel.

## Summary

| Bug class | Advisories | In scope |
|---|---|---|
| Reading or writing outside a message or buffer | 17 | 12 |
| Crash on input an attacker chose (reachable `assert`) | 8 | 5 |
| Data used after it was freed, or never released | 10 | 5 |
| Logic or permission error | 7 | 1 |
| **Total** | **42** | **23** |

In the "In scope" column, a row tagged "in (5G analogue)" counts as out, because only its 5G counterpart is in scope.

The broader record is larger: the NVD (National Vulnerability Database) lists about 205 CVEs (Common Vulnerabilities and Exposures) for Open5GS and 107 for free5GC as of 2026-10-30. Many of these were assigned one function per CVE.

## The log

| Advisory | Published | Severity | What went wrong | Kernel part | Property that rules it out | Scope |
|---|---|---|---|---|---|---|
| [GHSA-f4mx-3x6p-cfwp](https://github.com/open5gs/open5gs/security/advisories/GHSA-f4mx-3x6p-cfwp) | 2026-06-05 | high | Before authentication, the phone's identity field is read past its end (three places) | Codec (phone ↔ core) | Decoding is total and never reads outside the input | in |
| [GHSA-88pq-hpwv-2vjw](https://github.com/open5gs/open5gs/security/advisories/GHSA-88pq-hpwv-2vjw) | 2026-06-09 | low | Use after free in the receptionist (AMF, Access and Mobility Management Function) | Conversation | No user context is used after it is released (affine types) | in |
| [GHSA-w23j-r5rp-qj77](https://github.com/open5gs/open5gs/security/advisories/GHSA-w23j-r5rp-qj77) | 2026-06-09 | medium | The service registry (NRF, Network Repository Function) changes stored state even after rejecting the request | Conversation | A rejected request leaves state unchanged | out (no inter-program registry in the kernel) |
| [GHSA-c5j3-r6gw-prxj](https://github.com/open5gs/open5gs/security/advisories/GHSA-c5j3-r6gw-prxj) | 2026-06-11 | high | The service registry aborts on a negative heartbeat timer | Conversation | Every handler is total over its input type | out (registry) |
| [GHSA-fvpc-gmgr-qrg3](https://github.com/open5gs/open5gs/security/advisories/GHSA-fvpc-gmgr-qrg3) | 2026-06-26 | critical | The authentication server (AUSF, Authentication Server Function) accepts unvalidated status notifications, which lets an attacker redirect 5G authentication | Conversation | Only authenticated peers can change routing state | out (traffic between programs) |
| [GHSA-cfp8-93x2-6h9x](https://github.com/open5gs/open5gs/security/advisories/GHSA-cfp8-93x2-6h9x) | 2026-06-26 | high | A first message from the antenna missing a mandatory field leaves a context behind; repeating it exhausts the pool | Codec + Conversation | Missing mandatory fields are rejected at decode; every started context ends registered or released | in |
| [GHSA-mg8r-2cvv-xq9j](https://github.com/open5gs/open5gs/security/advisories/GHSA-mg8r-2cvv-xq9j) | 2026-06-26 | medium | One antenna can release a user that belongs to another antenna | Conversation | Only the owning antenna can modify or release a user | in |
| [GHSA-wv34-23hh-g243](https://github.com/open5gs/open5gs/security/advisories/GHSA-wv34-23hh-g243) | 2026-08-07 | high | The 4G mobility manager (MME, Mobility Management Entity) asserts when a stale timer event fires | Conversation | Timers are ordinary events and every state handles every event | out (4G) |
| [GHSA-3mxx-vq7h-x8ff](https://github.com/open5gs/open5gs/security/advisories/GHSA-3mxx-vq7h-x8ff) | 2026-08-07 | high | The tunnel-endpoint field (F-TEID, Fully qualified Tunnel Endpoint Identifier) in forwarder control messages (PFCP, Packet Forwarding Control Protocol) trusts its own length: out-of-bounds write and read | Codec (PFCP) | Length fields are checked against the real input size | in |
| [GHSA-6w6j-vjx3-pwqr](https://github.com/open5gs/open5gs/security/advisories/GHSA-6w6j-vjx3-pwqr) | 2026-08-07 | medium | The session manager (SMF, Session Management Function) reads past the end of quality-of-service rules | Codec (phone ↔ core) | Decoding is total and never reads outside the input | in |
| [GHSA-37c3-hv4f-688p](https://github.com/open5gs/open5gs/security/advisories/GHSA-37c3-hv4f-688p) | 2026-08-11 | high | Out-of-bounds read in the PFCP volume measurement field | Codec (PFCP) | Decoding is total and never reads outside the input | in |
| [GHSA-jv67-c9q6-68vj](https://github.com/open5gs/open5gs/security/advisories/GHSA-jv67-c9q6-68vj) | 2026-08-12 | high | Out-of-bounds read in the 4G subscriber server (HSS, Home Subscriber Server) | Codec | Decoding is total | out (4G) |
| [GHSA-9crh-64c8-56q6](https://github.com/open5gs/open5gs/security/advisories/GHSA-9crh-64c8-56q6) | 2026-08-12 | high | The 4G MME crashes on a malformed address in a GTP (GPRS Tunnelling Protocol) version 1 message | Codec | Decoding is total | out (4G) |
| [GHSA-4x7x-2p8x-jwrq](https://github.com/open5gs/open5gs/security/advisories/GHSA-4x7x-2p8x-jwrq) | 2026-08-12 | low | The shared TLV (type-length-value) reader reads past the end of the header | Codec (shared) | Decoding is total and never reads outside the input | in |
| [GHSA-ch5j-wv55-jmr6](https://github.com/open5gs/open5gs/security/advisories/GHSA-ch5j-wv55-jmr6) | 2026-08-13 | medium | A session is not cleaned up when its network name or slice fails validation | Conversation | Every failure path releases what it created | in |
| [GHSA-r9rw-hx33-745g](https://github.com/open5gs/open5gs/security/advisories/GHSA-r9rw-hx33-745g) | 2026-08-14 | critical | The 4G MME compares the authentication answer using the length the attacker sent, so authentication can be bypassed with a 1-in-256 guess | Crypto | The challenge answer is always compared at full length | in (5G analogue); the 4G MME itself is out |
| [GHSA-855g-699w-9w28](https://github.com/open5gs/open5gs/security/advisories/GHSA-855g-699w-9w28) | 2026-08-14 | medium | A session is orphaned after a failure while creating it | Conversation | Every failure path releases what it created | in |
| [GHSA-9643-6pmq-j7g2](https://github.com/open5gs/open5gs/security/advisories/GHSA-9643-6pmq-j7g2) | 2026-08-18 | high | The session manager reads past a truncated session-management container | Codec (phone ↔ core) | Decoding is total and never reads outside the input | in |
| [GHSA-wpwr-xj64-h6cp](https://github.com/open5gs/open5gs/security/advisories/GHSA-wpwr-xj64-h6cp) | 2026-08-18 | medium | During handover, one antenna can change a user context before the sender's ownership is checked | Conversation | Only the owning antenna can modify a user | out (handover) |
| [GHSA-v6fv-hmw8-6ffv](https://github.com/open5gs/open5gs/security/advisories/GHSA-v6fv-hmw8-6ffv) | 2026-08-21 | low | After a cancelled handover, a response with no matching request is accepted and redirects a user's downlink traffic | Conversation | Every response must answer an outstanding request from the same peer | out (handover) |
| [GHSA-m795-gjf7-c8ch](https://github.com/open5gs/open5gs/security/advisories/GHSA-m795-gjf7-c8ch) | 2026-09-16 | low | Out-of-bounds read in the session bit-rate field (Session-AMBR, Aggregate Maximum Bit Rate) | Codec (phone ↔ core) | Decoding is total and never reads outside the input | in |
| [GHSA-xmqj-59c5-jfjc](https://github.com/open5gs/open5gs/security/advisories/GHSA-xmqj-59c5-jfjc) | 2026-09-17 | low | Out-of-bounds read in the 4G policy server (PCRF, Policy and Charging Rules Function) | Codec | Decoding is total | out (4G, policy) |
| [GHSA-cvp4-6qm5-6jv2](https://github.com/open5gs/open5gs/security/advisories/GHSA-cvp4-6qm5-6jv2) | 2026-09-19 | high | The session manager aborts on a 4G session request with radio type 0 | Conversation | Every handler is total over its input type | out (4G interface) |
| [GHSA-vp44-3q85-5cm4](https://github.com/open5gs/open5gs/security/advisories/GHSA-vp44-3q85-5cm4) | 2026-09-19 | medium | One-byte out-of-bounds write while decoding subscriber and phone numbers (IMSI, International Mobile Subscriber Identity; MSISDN, the phone number) | Codec (identities) | Encoding and decoding never write outside the buffer | in |
| [GHSA-796x-8w26-2xfp](https://github.com/open5gs/open5gs/security/advisories/GHSA-796x-8w26-2xfp) | 2026-09-21 | high | Assertion and stack overflow while building protocol configuration options (PCO, Protocol Configuration Options) | Codec (encoder) | Encoding is total and never writes outside the buffer | in |
| [GHSA-f77j-h86j-2vcf](https://github.com/open5gs/open5gs/security/advisories/GHSA-f77j-h86j-2vcf) | 2026-09-21 | high | Stack out-of-bounds write from repeated DNS requests in extended protocol configuration options | Codec (encoder) | Encoding is total and never writes outside the buffer | in |
| [GHSA-f9c2-535p-3mwc](https://github.com/open5gs/open5gs/security/advisories/GHSA-f9c2-535p-3mwc) | 2026-09-21 | high | The subscriber-data function (UDM, Unified Data Management) aborts on an empty serving network name in an authentication request | Crypto | Key derivation is total, including on empty names | in |
| [GHSA-vc4h-jr29-v3q6](https://github.com/open5gs/open5gs/security/advisories/GHSA-vc4h-jr29-v3q6) | 2026-09-21 | low | Off-by-one read in a GTP version 1 mobility context | Codec | Decoding is total | out (4G) |
| [GHSA-g97g-v8mh-wg24](https://github.com/open5gs/open5gs/security/advisories/GHSA-g97g-v8mh-wg24) | 2026-09-21 | medium | The session manager asserts when its packet-filter pool runs out | Conversation | Running out of resources yields a reject, never a crash | in |
| [GHSA-fvg8-6r68-v3x7](https://github.com/open5gs/open5gs/security/advisories/GHSA-fvg8-6r68-v3x7) | 2026-09-21 | medium | Assertion on an unbounded number of IP configuration containers (IPCP, Internet Protocol Control Protocol) | Codec | Element counts are bounded by type | in |
| [GHSA-x8ww-5xvf-qxg6](https://github.com/open5gs/open5gs/security/advisories/GHSA-x8ww-5xvf-qxg6) | 2026-09-21 | medium | A session-modification request that both deletes and modifies the same traffic flow aborts the session manager | Conversation | Contradictory requests are rejected; impossible flag combinations cannot be represented | in |
| [GHSA-g4xp-3ccr-264w](https://github.com/open5gs/open5gs/security/advisories/GHSA-g4xp-3ccr-264w) | 2026-09-21 | medium | Assertion on a non-contiguous IPv4 mask in a packet filter | Codec + Packet rules | Masks are validated at decode, and packet rules accept only valid masks | in |
| [GHSA-25v2-v588-jq8g](https://github.com/open5gs/open5gs/security/advisories/GHSA-25v2-v588-jq8g) | 2026-09-25 | high | Before authentication, out-of-bounds write in the multipart parser of the HTTP interface between programs (SBI, Service-Based Interface) | Thin layer | — | out (traffic between programs) |
| [GHSA-vp5f-rg8g-8p7j](https://github.com/open5gs/open5gs/security/advisories/GHSA-vp5f-rg8g-8p7j) | 2026-09-25 | low | Out-of-bounds read while decrypting the hidden identity (SUCI, Subscription Concealed Identifier) | Crypto | Decryption of the hidden identity is total and never reads outside the input | in |
| [GHSA-hcjf-j847-3gx8](https://github.com/open5gs/open5gs/security/advisories/GHSA-hcjf-j847-3gx8) | 2026-10-01 | medium | One bit of the phone's device identity (IMEISV, International Mobile Equipment Identity and Software Version) corrupts the context; oversized options overflow the stack; two reachable assertions | Codec (identities) | Decoding and encoding stay inside their buffers; handlers are total | in (receptionist part); the MME part is out |
| [GHSA-m82c-3wmm-w452](https://github.com/open5gs/open5gs/security/advisories/GHSA-m82c-3wmm-w452) | 2026-10-18 | medium | Use after free in the 4G subscriber server's voice interface | Conversation | No use after release | out (4G, voice) |
| [GHSA-89hr-658g-pgf8](https://github.com/open5gs/open5gs/security/advisories/GHSA-89hr-658g-pgf8) | 2026-10-19 | medium | Use after free of subscribed network names in the 4G MME | Conversation | No use after release | out (4G) |
| [GHSA-x345-qp36-m8j8](https://github.com/open5gs/open5gs/security/advisories/GHSA-x345-qp36-m8j8) | 2026-10-19 | medium | Use after free of transactions in the 4G MME | Conversation | No use after release | out (4G) |
| [GHSA-vqp6-5553-c4hx](https://github.com/open5gs/open5gs/security/advisories/GHSA-vqp6-5553-c4hx) | 2026-10-19 | medium | The service registry uses objects after removal because of queued timer events (use after free, double free) | Conversation | Timers are events against current state; no use after release | out (registry) |
| [GHSA-3w99-v8jg-8v5m](https://github.com/open5gs/open5gs/security/advisories/GHSA-3w99-v8jg-8v5m) | 2026-10-19 | medium | Use after free in the HTTP/2 server | Thin layer | — | out (traffic between programs) |
| [GHSA-vjjc-hwmg-v94v](https://github.com/open5gs/open5gs/security/advisories/GHSA-vjjc-hwmg-v94v) | 2026-10-21 | medium | The roaming security proxy (SEPP, Security Edge Protection Proxy) lets one peer redirect another peer's traffic | Conversation | A peer can only act on its own state | out (roaming) |
| [GHSA-7g3v-g4gp-p624](https://github.com/open5gs/open5gs/security/advisories/GHSA-7g3v-g4gp-p624) | 2026-10-22 | medium | When a second context takes over a permanent identity, hidden identity or phone address, the old index key is used after free | Conversation | Identity indexes stay unique, and no use after release | in |

When new advisories appear, add them here with the same columns.
