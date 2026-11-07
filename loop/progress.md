# Loop progress

## Summary (2026-11-03)

- **Milestone 1: tickets 01–23 done**, with the end-to-end test passing (`nix build .#checks.x86_64-linux.e2e`). The owner's review on 2026-11-03 (`loop/decisions.md` § Owner review) found laws that don't yet rule out four in-scope advisories, so `loop/m1` reaches `main` only after tickets 32–34.
- **Next, in order:** hardening tickets 32–37, then milestone 2, handover (`docs/spec/milestone-2.md`, tickets 24–31). Neither has started. Deliberately out of scope: 4G, voice, roaming, policy and billing, and the handover cases excluded in `docs/spec/milestone-2.md`.

Status values: `todo`, `in-progress`, `done`, `blocked`, `needs-human`. Tickets are in `docs/spec/tickets/`.

| # | Ticket | Status | Depends on | Notes |
|---|---|---|---|---|
| 01 | bootstrap | done | — | 3327ac8: LAWS/PROOF pair, check.sh gate, test runner, acceptance.py, gen-vectors.py and generated vector modules |
| 02 | bytes | done | 01 | 2799d0f: readers u8..u32, take, nibbles, TBCD; 8 laws proven; no U32 lemma file needed |
| 03 | vectors | done | 01 | ad79428: all 9 spec sources present with source fields; generator emits Vec modules; vectors_load smoke test |
| 04 | sha256-hmac | done | 02, 03 | e5369b6: SHA-256 and HMAC; 12+7 vectors pass; 2 laws proven; upstream draft 01 |
| 05 | aes | done | 02, 03 | 5f32c0d: AES-128, CTR, CMAC; 9 vectors pass; 4 laws proven |
| 06 | milenage | done | 05 | b1b468e: f1, f1*, f2..f5*, OP->OPc; 54 checks pass; lengths law proven |
| 07 | kdf | done | 04, 06 | 3641e6d: KDF, SNN, KAUSF..KgNB; capture keys reproduced; 2 laws proven |
| 08 | x25519-suci | done | 04, 05, 07 | 0493397: X25519, PLMN codec, SUCI decode and Profile A; 7 laws proven; upstream draft 02 |
| 09 | nas-security | done | 05, 07 | d62b26a: NIA2, NEA2, NEA0, protect/unprotect, COUNT estimate; 28 checks; 3 laws proven |
| 10 | nas-5gmm | done | 02, 03 | a6e0c85: generic 5GMM codec (19 types), typed IE views incl. 5GS mobile identity; 110 checks on the capture; 10 laws proven (mm roundtrip/decode_valid/suffix, mobile identity ×3, IMEISV, payload container ×2) |
| 11 | nas-5gsm | done | 10 | e46170b: 5GSM codec (9 types) sharing the 5GMM optional-IE machinery; typed QoS rules, packet filters, flow descriptions, Session-AMBR, PDU address, ePCO; 43 checks; 8 laws proven (sm ×3, qos_rules.suffix, mask_contiguous, session_ambr, epco ×2) |
| 12 | aper | done | 02 | d10b54a: X.691 aligned PER primitives (bits, alignment, constrained/indefinite/small numbers, lengths, sizes, octets, bit/octet/printable strings, open types, enumerations) over a bit-list cursor; 55 checks incl. the IE walk over all 14 captured NGAP PDUs; 36 laws proven; padding_zero kept strict |
| 13 | ngap | done | 03, 12 | 1358d02: generator over TS 38.413 V17.15.0 (pycrate 0.8.1) emitting 140 types with read/write/after/valid, per-message views with criticality handling, and 420 laws (roundtrip, decode_valid, suffix) with their proofs; frame codec and 10 hand-written laws; pycrate differential oracle agrees on all 14 captured PDUs; golden test; upstream draft 04 |
| 14 | pfcp | done | 02, 03 | d65bfef: TS 29.244 header and IE codec with typed views (Node ID, F-SEID, F-TEID, UE IP, OHC, MBR, Cause and other one-octet IEs); all 20 captured PFCP messages decode, validate and re-encode (90 checks); 7 laws proven incl. the three advisory laws |
| 15 | frames | done | 02 | f0cdd2c: edge/kernel frame codec (envelope, six event kinds with Config TLVs and subscribers, six action kinds with a typed log level); TLV codec and proofs shared with PFCP via kernel/tlv.bend; 31 checks; 6 laws proven (max_length, event roundtrip/decode_valid/suffix, actions roundtrip, config repeat_replaces) |
| 16 | state-ng-setup | done | 13, 15 | 64897b7: State record with U32-keyed tables, Kernel.step over Config (typed Cfg, PFCP Association Setup Request), NGAP associations up/down (releasing UEs and sessions), NG Setup Response matching the capture byte for byte or Failure, Error Indication for undecodable PDUs; 16 checks; 3 laws proven |
| 17 | registration-auth | done | 08, 09, 10, 16 | 9563e69: InitialUEMessage creates a guarded UE context, SUCI deconcealment and subscriber lookup, Identity Request for an unknown 5G-GUTI, AUSF/UDM vector with SQN+32 and AUTS re-synchronisation, Authentication Request/Response/Failure over DL/UL NAS Transport, T3560 retransmission and release; the Authentication Request and KAMF match the capture; 16 checks; 3 laws proven |
| 18 | registration-complete | done | 17 | b869175: NAS security mode (SMC byte for byte, algorithm choice, SM Complete with RINMR), Initial Context Setup with the captured KgNB, Registration Accept with 5G-GUTI from entropy, Complete, deregistration, UE context release, identity takeover; UE procedures as transactions, UE table as one sieve; 32 checks; 5 laws proven |
| 19 | pdu-session | done | 11, 14, 18 | 3df1030: N4 association (T1/N1, pause, heartbeats), PDU Session Establishment over UL NAS Transport with validation and allocation, PFCP Session Establishment/Modification/Deletion to eUPF, PDU Session Resource Setup with the captured transfer byte for byte, Accept with default rule and DNS, failure paths, modification rejected, sessions as identity plus variable part with one sieve; NGAP generator extended with the SMF's IEs; 22 checks; 7 laws proven |
| 20 | kernel-main | done | 15, 19 | 7481566: kernel/main.bend listens on 127.0.0.1, takes one edge and answers every event frame with one Actions frame, echoing Log actions to stderr; protocol errors exit 1; scripts/frame-client.py drives it with Config, NgapAssocUp and the captured NG Setup Request and checks the captured NG Setup Response |
| 21 | edge | done | 15 | bfde196: Rust crate edge/ (library + binary): spawns the kernel and sends Config from TOML, SCTP N2 through libc in one unsafe module with stream ids and PPID 60, UDP N4 to the UPF only, timer heap, 32 bytes of OS entropy per event, one event in flight, exits non-zero on a dead or invalid kernel; 14 cargo tests incl. a fake kernel; test-vectors/frames.json shared with kernel/tests/frame.bend |
| 22 | e2e | done | 20, 21 | 057ab6a, 9ac4f63: NixOS test `e2e/test.nix` as flake check `e2e`, replacing the Docker bench and `run.sh`; `E2E PASS` with 4/4 pings through eUPF; found and fixed swapped SCTP cmsg types in the edge (9ac4f63) |
| 23 | acceptance | done | 01–22 | 1d2ad79: `scripts/test-kernel.sh --strict` (694 checks, none skipped), `acceptance.py --strict` (26 laws, 0 failures) and `scripts/check.sh` pass; `loop/acceptance-report.md` written; the audit strengthened `smf.establish.failure_releases` to all four failure paths, added `ngap.no_big_nat` (ticket 13) and renamed `aper.padding.zero`; re-checked 2026-11-02 on the e2e commits: `kernel/`, `tools/` and `scripts/` are unchanged since 1d2ad79, `acceptance.py --strict` gives 26 laws and 0 failures, and the edge's cargo tests ran in its Nix build |
| 32 | takeover-after-auth | done | 18 | e5a8895, d944697: the SUPI stays in Authenticating until HRES* and RES* verify and enters the index in `Gmm.secure`, so takeover follows 5G-AKA; 5G-TMSI drawn free of live ones; `owner_only` widened to codes 14, 29, 46; `amf.takeover.authenticated` proven over every NGAP path; replay test with a second gNB |
| 33 | liveness-laws | done | 18 | 3219d95, 168b4b0, 6582b9c: Releasing has a guard whose expiry forgets the UE and deletes its sessions at eUPF; ids skip live ones; the step returns actions naming their UE context; `amf.guard.expires`, `amf.sessions.owned` and `amf.release.forgets_ue` over every event replace the two vacuous laws |
| 34 | laws-on-real-paths | done | 19 | aced957..3cbac54: laws restated over what the kernel runs: SNN and ePCO over the valid Config every state holds (`kernel.config.valid`), TBCD over `Tbcd.decode`, F-SEID/F-TEID re-encode to their body, empty pool and any gNB failed list in the SMF laws with the PFCP deletion, packet-filter bound and TEID uniqueness as invariants; six advisory rows back to Yes; gate CHECK OK, 703 checks |
| 38 | review-gaps | done | 32, 33, 34 | d00a846: items 1, 3, 4 done: `amf.contexts.guarded` and `smf.sessions.known` (known exactly when past Creating) proven through the liveness walk, `failure_releases` states the PFCP deletion past Creating with no `Up.N4.known` premise, five table invariants share one event chain, report fixed; item 2 (`state.ids.free`, false only at id exhaustion) moved to ticket 35 item 8 |
| 35 | procedure-robustness | done | 32, 33 | 93de91c..a6058da: PFCP association and heartbeat retransmitted with their sequence number, a silent eUPF takes the link down; Release Command after the Accept; TEID/SEID drawn again on collision; AMF-UE-NGAP-ID ≥ 2³² unknown; returning UEs read unverified (Service Reject #9); Set ID/Pointer ranges; guard timers keyed by their row, free AMF-UE-NGAP-IDs, law `state.ids.free`, takeover law covers overwrites; 722 checks, E2E PASS |
| 36 | edge-robustness | done | 21 | 47eb0ca: timers fire after every event, kernel exit detected by its stdout closing, association ids checked and never reused while held, N4 replies to the UPF datagram's source port, oversize config values and Config refused; 15 cargo tests, clippy clean, E2E PASS |
| 37 | simplify | todo | 32–36 | |
| 24 | handover-capture | todo | — | |
| 25 | ngap-handover | todo | 13, 24 | |
| 26 | nh-ncc | todo | 07, 24 | |
| 27 | path-switch | todo | 19, 25, 26 | |
| 28 | n2-handover | todo | 19, 25, 26 | |
| 29 | handover-acceptance | todo | 27, 28 | |
| 30 | e2e-handover | todo | 24, 27, 28 | |
| 31 | edge-sctp-coverage | todo | 21, 30 | |
