# Acceptance report (ticket 23)

Audited at commit 657e746 on `loop/m1`, 2026-11-02. Figures and commands:

| Check | Result |
|---|---|
| `scripts/test-kernel.sh --strict` | every `kernel/tests/*.bend` passes, 694 checks, nothing skipped |
| `python3 -I scripts/acceptance.py --strict` | 26 laws required (the 23 in-scope advisories), 0 failures |
| `bend kernel/PROOF.bend` and `--verdict` | ALL PROOFS CHECK; 133 laws in `kernel/LAWS.bend` plus 471 generated NGAP laws in `kernel/ngap/gen/laws.bend` |
| `scripts/check.sh` | passes (see `loop/progress.md`) |
| `nix build .#checks.x86_64-linux.e2e` | `E2E PASS` on 2026-11-02 (ticket 22): registration, PDU session and 4/4 pings through eUPF |

Lines refer to `kernel/LAWS.bend` at the commit above.

## The in-scope advisories

| Advisory | Law (line) | Why the law rules the bug out | At least as strong as the ticket? |
|---|---|---|---|
| GHSA-f4mx-3x6p-cfwp (identity read past its end) | `nas.mobile_identity.suffix` (313), `nas.mobile_identity.decode_valid` (320) | A decoded identity re-encodes to exactly the bytes it was read from and satisfies its type's validity, so the reader never consumes outside the IE and never accepts a type whose length disagrees with its content; `nas.mobile_identity.guti_length` (327) states the eleven bytes of a 5G-GUTI the ticket names. | Yes |
| GHSA-88pq-hpwv-2vjw (use after free in the AMF) | `amf.release.forgets_ue` (1160) | After the owner's UE Context Release Complete, no UE context and no session carries the AMF-UE-NGAP-ID; timers live inside the context and transactions are applied within the step, so nothing survives it. | Yes for the state. The ticket's "no later action can mention it" is an argument (a later message for the id finds no owner, so no procedure runs for it), not a law. See deviations. |
| GHSA-cfp8-93x2-6h9x (first message missing a field leaves a context) | `ngap.initial_ue_message.mandatory` (938), `amf.initial_ue.reject_leaves_state` (1091) | The view succeeds only with each mandatory IE present exactly once, and a failed view leaves the state equal to what it was with Error Indication and a log line as the only actions. | Yes |
| GHSA-mg8r-2cvv-xq9j (one gNB releases another's UE) | `amf.ue_context_release.owner_only` (1131) | A Release Request or Complete naming a UE that another association owns leaves the state equal to what it was. | Yes |
| GHSA-3mxx-vq7h-x8ff (F-TEID trusts its own length) | `pfcp.fteid.decode_valid` (985) | What decodes is valid: an address form carries addresses of exactly four or sixteen octets and at least one of them, and the CH form carries no TEID and no address by construction of the type; `pfcp.ie.suffix` bounds the read to the declared length. | Yes |
| GHSA-6w6j-vjx3-pwqr (QoS rules read past their end) | `nas.qos_rules.suffix` (386) | A decoded rule list re-encodes to exactly its input bytes, so every rule and filter is read inside its declared length and a length its contents do not fill cannot decode. | Yes |
| GHSA-37c3-hv4f-688p (volume measurement read out of bounds) | `pfcp.ie.suffix` (978) | Every IE, known or not, consumes exactly four header octets plus its declared length and fails as Short with fewer octets left. | Yes |
| GHSA-4x7x-2p8x-jwrq (TLV header read past its end) | `pfcp.ie_header.short_input_fails` (970) | Fewer than four octets fail as Short. | Yes |
| GHSA-ch5j-wv55-jmr6 (session not cleaned up after failed validation) | `smf.establish.reject_leaves_state` (1240) | A request refused by validation leaves the sessions and the PFCP sequence as they were, and the only action is the 5GSM reject to the UE. | Yes for the SMF. The UE's NAS uplink COUNT (AMF state) advances, which is replay protection, not a leak. |
| GHSA-r9rw-hx33-745g (RES compared at the attacker's length) | `ausf.res_star.full_length` (1111) | Authentication succeeds only when RES* is sixteen octets equal to XRES* over all of them and HRES* equals HXRES* over all of them. | Yes |
| GHSA-855g-699w-9w28 (session orphaned after a failure while creating it) | `smf.establish.failure_releases` (1291) | Whichever later step fails (eUPF refuses the establishment, the guard expires in any pending phase, eUPF refuses the modification, the gNB reports the session failed to set up), the session's entry is gone, so its address, TEID and SEID are held by nothing. | Yes. Strengthened in this ticket from two failure paths to four; the gNB path is stated for a response that names the one session our requests carry. |
| GHSA-9643-6pmq-j7g2 (truncated 5GSM container) | `nas.payload_container.suffix` (357), with `nas.payload_container.short` (348) | Fewer bytes than the two-byte length declares fail as Short, and a decoded container is exactly the declared slice. | Yes |
| GHSA-m795-gjf7-c8ch (Session-AMBR read out of bounds) | `nas.session_ambr.decode_valid` (406) | A decoded Session-AMBR came from exactly six bytes and both units are defined values. | Yes |
| GHSA-vp44-3q85-5cm4 (one-byte write decoding digits) | `bytes.tbcd.length` (92) | Decoding k bytes yields at most 2k digits, each 0..9, and encoding d digits yields ceil(d/2) bytes. | Yes |
| GHSA-796x-8w26-2xfp (PCO encoder overflow) | `nas.epco.encode_bounded` (422) | A valid ePCO encodes to at most 65535 bytes and reads back as itself, so no container is cut or overrun. | Yes under the validity predicate. The ticket suggests a length-indexed type; see deviations. |
| GHSA-f77j-h86j-2vcf (repeated DNS requests overflow) | `smf.epco.response_bounded` (1380) | The Accept's ePCO holds each container identifier at most once, however many times the request repeats it. | Yes |
| GHSA-f9c2-535p-3mwc (empty serving network name) | `kdf.snn.nonempty` (192) | The serving network name is never empty, and the AUSF receives it from this function alone. | Yes |
| GHSA-g97g-v8mh-wg24 (packet-filter pool exhausted) | `smf.packet_filters.capacity_reject` (1375) | The one rule a session ever holds has one filter, and the only way to add filters, a Modification Request, is rejected by `smf.modification.rejected`, so no session holds more than sixteen. | Yes; "a request that would exceed it is rejected" holds because every such request is rejected. |
| GHSA-fvg8-6r68-v3x7 (unbounded IPCP containers) | `nas.epco.decode_bounded` (414) | A decoded ePCO holds at most 255 containers, each with the length its byte declares, inside the IE. | Yes |
| GHSA-x8ww-5xvf-qxg6 (delete and modify the same flow) | `smf.modification.rejected` (1331) | Every Modification Request gets Modification Reject #31 and the sessions are as they were. | Yes |
| GHSA-g4xp-3ccr-264w (non-contiguous IPv4 mask) | `nas.packet_filter.mask_contiguous` (395) | An IPv4 address component decodes only with a mask that is a contiguous run of ones from the top bit; the kernel installs no packet rule from a UE mask (the default rule matches everything), so no rule ever sees an invalid one. | Yes |
| GHSA-vp5f-rg8g-8p7j (SUCI read out of bounds) | `suci.deconceal.length_checked` (232) | A Profile A output shorter than 41 bytes fails as Short, the MAC is compared over all eight bytes, and a mismatch is Fail, never a SUPI. | Yes |
| GHSA-hcjf-j847-3gx8 (IMEISV bit corrupts the context) | `nas.imeisv.decode_valid` (339) | A decoded IMEISV has exactly sixteen decimal digits; the decoder ties the odd/even flag to the count. | Yes |
| GHSA-7g3v-g4gp-p624 (index key used after takeover) | `amf.indexes.unique` (1188), with `smf.ip_pool.unique` (1387) | No two UE contexts share a key, SUPI, 5G-TMSI or RAN-UE-NGAP-ID on an association, and no two sessions share a key (SEID), UE IPv4, TEID or PDU session identity of one UE, in the initial state and after every step; the indexes are the contexts themselves, so every entry is a context and every context is indexed. | Yes. The UE IPv4 and SEID halves the ticket lists under `amf.indexes.unique` live in `smf.ip_pool.unique`. |

## `kernel/LAWS.bend` against the ticket texts

Every law a ticket names is stated and proven, with these differences:

- **Ticket 07, `kdf.length`.** The ticket says every derived key is 32 bytes; the law gives K_NASint and K_NASenc 16 bytes, which is what TS 33.501 Annex A.8 derives (the low 128 bits). The law is right; the ticket's wording is loose.
- **Tickets 10, 11, 13, 14, `*.suffix`.** The ticket shape says "`rest` is a suffix of `bs` and the consumed prefix is exactly the declared length". For readers of whole messages the law says the input bytes are exactly the encoding of what was read, which implies both. `pfcp.ie.suffix` and `nas.payload_container.suffix` keep the ticket's shape.
- **Ticket 11, `nas.epco.encode_bounded`.** Stated for valid ePCO (each container at most 255 bytes) rather than by a length-indexed container type. The Accept's ePCO is built by `Gsm.epco_containers` from at most one four-byte DNS container, valid by inspection, not by law.
- **Ticket 13, `ngap.no_big_nat`.** Was never stated before this ticket; it is now (line 920) and proven in `kernel/proofs/ngap_view.bend`: AMF-UE-NGAP-ID decodes to at most five canonical octets, BitRate to octets in either form. Both are byte lists by type.
- **Ticket 17, `amf.auth.guarded`.** The ticket says "exactly one running guard timer (T3560, T3550 or T3555)"; the law says every context that is not registered holds a guard or is being released. A context has one guard field, so one is the only count possible; the guards are T3570, T3560 and T3550 (`loop/decisions.md`, ticket 17).
- **Ticket 18, `amf.release.forgets_ue`.** "No later action can mention it" is not stated as a law. The argument: actions carrying an AMF-UE-NGAP-ID come from UE procedures, which run only for a context an owner lookup finds.
- **Ticket 18, `amf.indexes.unique`.** UE IPv4 and SEID are session indexes and are covered by `smf.ip_pool.unique`; "every entry points to an existing context" holds because the indexes are the context table itself.
- **Ticket 19, `smf.establish.reject_leaves_state`.** "Changes no SMF state" is stated as sessions and PFCP sequence unchanged; the UE's NAS uplink COUNT advances.
- **Ticket 19, `smf.establish.failure_releases`.** Covered two of the four later failures before this ticket; now covers all four. The gNB branch is stated for a response with no successful item and the one failed item, the shape a one-session request produces.
- **Ticket 19, `smf.packet_filters.capacity_reject`.** Holds through `smf.modification.rejected`: nothing can add filters, so the default rule's one filter is the maximum.
- **Naming.** `aper.padding.zero` was renamed `aper.pack.padding_zero` in this ticket so it no longer sits one character from `aper.padding_zero`.
- **Extra laws** beyond the tickets: `bytes.nibbles.roundtrip`, `plmn.*`, `nas.mobile_identity.guti_length`, `nas.payload_container.short`, `frame.event.decode_valid`, `aper.pack.padding`, `aper.pack.padding_zero`, and the generated `.suffix` law per NGAP type.

Two clauses remain arguments rather than laws: the "later action" clause of `amf.release.forgets_ue` and the validity by inspection of the Accept's ePCO. Everything else a ticket states is at least as strong in `kernel/LAWS.bend`.
