# What eUPF needs from an SMF over PFCP

Answers [issue #3](https://github.com/eliesgalvira/5G-spec-kernel/issues/3). Researched 2026-11-01 by reading source code only. Nothing here was run against a live eUPF.

## Sources

| Source | Version | Pin |
|---|---|---|
| eUPF | v0.7.2, latest stable release (2026-10-30) | [`758ad14`](https://github.com/edgecomllc/eupf/tree/758ad14f6d350dafc2ff24b8bdcef3114415dfe6) |
| eUPF | v1.0.0-rc.1, pre-release (2026-10-31), compared only | [`a74d03a`](https://github.com/edgecomllc/eupf/tree/a74d03a22eb401ab129d379b59fc962c87ea310a) |
| wmnsk/go-pfcp, eUPF's PFCP library | v0.0.23 (`go.mod:19` of eUPF) | [`1c6f9e4`](https://github.com/wmnsk/go-pfcp/tree/1c6f9e42f1f34f394aa6b6cde45c540cf991d53b) |
| 3GPP TS 29.244 | V16.4.0, the release eUPF claims (`docs/eupf_3gpp_compatibility.md:3`) | [ETSI TS 129 244 V16.4.0](https://www.etsi.org/deliver/etsi_ts/129200_129299/129244/16.04.00_60/ts_129244v160400p.pdf) |

Citation format: a bare `file.go:N-M` is eUPF v0.7.2 `cmd/core/`, other eUPF paths start at the repo root, `go-pfcp/...` is go-pfcp v0.0.23, `§` is TS 29.244 V16.4.0. To open one, append the path and `#LN-LM` to the pinned tree URL above, with `blob` in place of `tree`. Lines marked **Inferred** are my reading of the code and were not observed at runtime.

## Short answer

- eUPF handles eight message types: Heartbeat Request and Response, Association Setup Request and Response, Association Update Request, and Session Establishment, Modification and Deletion Request (`pfcp_connection.go:27-36`). It logs any other type and sends no reply (`pfcp_handlers.go:51-53`).
- It validates very little. Missing or malformed IEs can crash the process (five open crash reports), point at another session's rules, or leave rules installed after a rejection. Our SMF has to send correct messages because eUPF will not catch our mistakes.
- A PDR matches on one key only: the F-TEID's TEID for uplink, or the UE IPv4 address for downlink. eUPF ignores Precedence, Source Interface, Network Instance and the other PDI fields.
- With default config the SMF allocates TEIDs and UE addresses. CHOOSE only works when `feature_ftup` is on.
- Downlink traffic needs a FAR with FORW and Outer Header Creation GTP-U/UDP/IPv4, and a QER whose QFI eUPF writes into every downlink GTP-U header.

## Transport and header

- UDP on `pfcp_address`. The code's default is `127.0.0.1:8805` (`cmd/config/config.go:50`) and the docs say `:8805` (`docs/Configuration.md:16`).
- The receive buffer is 1500 bytes (`pfcp_connection.go:119`). **Inferred:** a larger datagram gets truncated, fails to parse and is dropped without a reply (`pfcp_handlers.go:22-26`).
- go-pfcp never reads the version field (`go-pfcp/message/header.go:159-161` always returns 1). It also accepts a Length field that disagrees with the datagram size (`header.go:128-131`). eUPF never sends Version Not Supported (`docs/eupf_3gpp_compatibility.md:38`), although §6.2.6.2.2 requires it.
- There is no duplicate detection. The handler runs on every datagram (`pfcp_handlers.go:20-55`). §6.4 says a request gets exactly one response, not counting retransmissions. **Inferred:** a retransmitted Session Establishment Request creates a second session with new FAR and QER entries, and the first one leaks.
- Nothing in `cmd/` calls `recover()`, so a nil dereference in any handler stops the process.
- eUPF keys associations by the peer's source IP and drops the port (`pfcp_handlers.go:30-32`). It sends its own heartbeats and association requests to that IP on port 8805, a fixed value (`pfcp_hearbeat.go:48`, `pfcp_connection.go:259`).
- It accepts an association from any IP. `HandlePfcpAssociationSetupRequest` has no allow-list (`pfcp_handlers.go:63-142`).

## Node procedures

| Message | What eUPF does |
|---|---|
| Heartbeat Request | Replies with its Recovery Time Stamp, even to peers it has no association with. If the request has no Recovery Time Stamp, eUPF calls a method on a nil IE and panics (`pfcp_hearbeat.go:14-27`, `go-pfcp/ie/recovery-time-stamp.go:18-19`, open issue [#629](https://github.com/edgecomllc/eupf/issues/629), still present in rc.1). |
| Heartbeat Response | Matches the sequence number against the association's outstanding heartbeat (`pfcp_hearbeat.go:29-43`). |
| Heartbeats eUPF sends | Every `heartbeat_interval` (5 s) to each associated peer. After `heartbeat_retries` (3) timeouts of `heartbeat_timeout` (5 s) each, it deletes the association and all its sessions (`node_association.go:53-81`, `pfcp_connection.go:185-193`, `cmd/config/config.go:62-64`). |
| Association Setup Request | Requires Node ID and Recovery Time Stamp. Rejects with cause 66 when either is missing and 69 when either fails to parse. Ignores CP Function Features. If an association from that IP already exists, eUPF keeps it along with its sessions and answers "accepted" (`pfcp_handlers.go:63-142`). §6.2.6.2.2 says to replace the association and delete its sessions unless the request asks to retain them. The response carries Cause 1, Node ID, Recovery Time Stamp and UP Function Features. |
| UP Function Features | eUPF sets FTUP (octet 5 bit 5) when `feature_ftup` is on, UEIP (octet 7 bit 3) when `feature_ueip` is on, and EMPU (octet 6 bit 1) always (`pfcp_connection.go:85-92`, §8.2.25). Its own docs say EMPU is not supported and End Marker is not implemented (`docs/eupf_3gpp_compatibility.md:64,79`), so the EMPU bit is false. |
| Association Setup Response, when eUPF starts the association because `pfcp_remote_node` is set | Requires Node ID, Cause 1 and CP Function Features. Without CP Function Features it never records the association and retries every `association_setup_timeout` (`pfcp_handlers.go:202-271`, `pfcp_connection.go:176-182`). §7.4.4.2 makes that IE conditional on the CP function supporting at least one feature, so a spec-compliant SMF with no CP features never associates. |
| Association Update Request | Requires Node ID and an existing association. Replies "accepted" and does nothing else (`pfcp_handlers.go:144-189`). |
| Not handled in v0.7.2 | Association Release, Node Report, Session Set Deletion, Session Report (eUPF never sends a Session Report Request, so no Downlink Data Notification and no usage-report triggers), PFD Management, Version Not Supported (`docs/eupf_3gpp_compatibility.md:9-50`). |

## Session Establishment Request

`pfcp_session_handlers.go:23-149` handles it in this order:

1. Node ID and CP F-SEID must be present and parse. Otherwise cause 66 with header SEID 0 (`:26-31`, `:509-525`). eUPF does not compare this Node ID with the association's.
2. An association must exist for the source IP. Otherwise cause 72 (`:33-38`).
3. The UP SEID comes from a per-association counter whose first value is 2 (`node_association.go:40-43`).
4. eUPF installs all Create FARs, then QERs, then URRs, then PDRs, whatever order the message uses (`:49-123`). Any error gives cause 73, with the CP SEID in the header (`:125-129`). Nothing is rolled back: the entries already installed stay in the eBPF maps (`TODO` at `:45`, open issue [#633](https://github.com/edgecomllc/eupf/issues/633)).
5. On success it sends Node ID, Cause 1, a UP F-SEID carrying the IP of `pfcp_address`, and one Created PDR for each PDR where eUPF allocated a TEID or UE IP (`:135-145`, `pdr.go:36-50`). **Inferred:** with the documented `:8805` listen address, that F-SEID IPv4 encodes as 0.0.0.0 (`go-pfcp/ie/f-seid.go:48-63,136-154`). The SMF should send to the association peer, not to the F-SEID address.

### Create PDR (`pdr_creation_context.go:69-166`)

| IE | eUPF behaviour |
|---|---|
| PDR ID | Required, otherwise cause 73 (`pfcp_session_handlers.go:102-105`). |
| Precedence | Ignored. |
| PDI | Required, otherwise cause 73 (`:90-93`). |
| PDI / Source Interface | The rules ignore it. The request logger reads it unconditionally, though, and panics with an index of -1 when it is missing (`display_utils.go:358-361`, called from `pfcp_session_handlers.go:44`, open issue [#631](https://github.com/edgecomllc/eupf/issues/631)). So in practice it is mandatory. |
| PDI / F-TEID | Makes the PDR uplink, keyed by TEID alone in `pdr_map_teid_ip4` (`pdr.go:16-34`, `cmd/ebpf/pdr.go:66-78`). eUPF never checks the F-TEID's address against `n3_address`. With CH set it allocates a TEID, and with CHID the PDRs that share a Choose ID share one TEID (`:106-137`). When an F-TEID is present, eUPF ignores every other PDI IE, the UE IP Address included. |
| PDI / UE IP Address | Used only when there is no F-TEID. Makes the PDR downlink, keyed by UE IPv4, or IPv6 when only that is given (`:139-162`). With CHV4 set and `feature_ueip` on, eUPF allocates the address from `ueip_pool`. eUPF does not read the S/D flag. |
| Neither of those two | eUPF logs "Both F-TEID IE and UE IP Address IE are missing" and still returns success (`:164-165` returns a nil error), installing an uplink PDR keyed by TEID 0. This is open issue [#643](https://github.com/edgecomllc/eupf/issues/643), seen with Open5GS and UERANSIM. |
| PDI / Network Instance, QFI, Application ID | Ignored. |
| PDI / SDF Filter | eUPF reads the first one only. The Flow Description must match `permit out (icmp\|ip\|tcp\|udp\|N) from … to …` (`sdf_filter_parser.go:17`), and the only number accepted for N is 58 (`:64-81`). Anything else gives cause 73. Each key holds one SDF PDR plus one default PDR (`cmd/ebpf/pdr.go:310-330`). eUPF never reads an SDF filter in Update PDR, because `go-pfcp/ie/sdf-filter.go:26-56` has no Update PDR case. |
| Outer Header Removal | Read. The datapath strips GTP-U only for value 0 (GTP-U/UDP/IPv4) or 6 (GTP-U/UDP/IP) (`cmd/ebpf/xdp/n3n6_entrypoint.c:309-319`). Value 6 has been supported since v0.7.2, after [#639](https://github.com/edgecomllc/eupf/issues/639), which affected Open5GS. **Inferred:** an absent IE reads as 0, so eUPF strips GTP-U anyway. |
| FAR ID | Only one per PDR. An ID not in the session maps to internal FAR 0, which may belong to another session (`:191-193`, `session.go:70-72`). |
| QER ID | eUPF uses only the first. An unknown ID maps to internal QER 0, the same flaw as FAR ID. |
| URR ID | eUPF uses only the first two (`:80-88`). |
| Activation and deactivation times, predefined rules, MAR | Ignored. |

### Create FAR (`composeFarInfo`, `pfcp_session_handlers.go:579-616`)

| IE | eUPF behaviour |
|---|---|
| FAR ID | eUPF discards the parse error, so a missing FAR ID becomes 0 (`:58`). |
| Apply Action | eUPF stores the first octet. The datapath forwards only when FORW is set and drops otherwise. BUFF, NOCP and DUPL do nothing (`n3n6_entrypoint.c:85-87,281-283`, `cmd/ebpf/xdp/pdr.h:78-87`). Nothing is buffered and no Downlink Data Report is sent. |
| Forwarding Parameters / Destination Interface, Network Instance | Ignored. The direction follows from Outer Header Creation. A FAR with OHC GTP-U/UDP/IPv4 encapsulates the packet. A FAR without it routes the decapsulated packet through the kernel's routing table (FIB) (`n3n6_entrypoint.c:309-347`). |
| Outer Header Creation | eUPF reads the first description octet, the TEID and the IPv4 address. IPv6 gives cause 73 (`:605-608`). It discards parse errors and then dereferences the nil result (`:598`), which crashes the process (open issues [#630](https://github.com/edgecomllc/eupf/issues/630) and [#637](https://github.com/edgecomllc/eupf/issues/637); #637 reports the crash on a valid modification with Open5GS-style IEs). A downlink FAR without GTP-U/UDP/IPv4 OHC drops every packet (`n3n6_entrypoint.c:89-91`). |
| Transport Level Marking | Read and used as the outer ToS byte (`:644-651`, `n3n6_entrypoint.c:108`). |
| BAR, Duplicating Parameters, Redirect Information | Ignored. |

### Create QER (`updateQer`, `pfcp_session_handlers.go:618-642`)

- QER ID is required, otherwise cause 73.
- Gate Status UL/DL is read. Any value other than OPEN drops the packet (`n3n6_entrypoint.c:100-101`).
- MBR UL/DL is stored as `uint32(kbps) * 1000` (`:628-635`). Zero means no limit (`cmd/ebpf/xdp/qer.h:57-59`). **Inferred:** values above 4 294 967 kbps wrap around and throttle the flow.
- QFI is read and written into the PDU Session Container of every downlink GTP-U packet (`cmd/ebpf/xdp/utils/gtp_utils.h:162-168,234`).
- GBR, Packet Rate and RQI are ignored.
- The datapath drops a packet when the QER lookup fails (`n3n6_entrypoint.c:93-97`). The QER map is an array, and internal IDs start at 0 (`cmd/ebpf/xdp/qer.h:28-34`, `cmd/ebpf/objects.go:311-319`). **Inferred:** a PDR without a QER ID silently uses whatever sits in QER slot 0. Every PDR should reference its own QER.

### Create URR

eUPF reads only the URR ID. It ignores Measurement Method, Reporting Triggers and thresholds (`updateUrr`, `pfcp_session_handlers.go:653-661`). The datapath counts UL and DL bytes. eUPF reports them only in a Usage Report inside the Session Deletion Response, or inside the Session Modification Response for each Remove URR (`:189-207,389-415`).

## Session Modification Request (`pfcp_session_handlers.go:226-495`)

- The association is found by source IP. If none exists the reply has cause 72, with eUPF's own SEID in the header. The session is found by header SEID. If unknown the reply has cause 65 and SEID 0 (`:231-244`).
- A CP F-SEID in the request replaces the stored CP SEID (`:248-256`).
- eUPF processes Create, Update and Remove for FARs, then QERs, then URRs, then Create, Update and Remove for PDRs (`:268-469`).
- Update FAR reads Apply Action and Update Forwarding Parameters / Outer Header Creation. Absent fields keep their old values (`:285-302`). This is how the gNB's TEID arrives after N2 setup.
- Update PDR goes through `extractPDR` again, so eUPF requires a PDI although §7.5.4.2 includes it only when the PDI changes. Without one the reply has cause 73 (`:440-456`). **Inferred:** changing a PDR's TEID or UE IP leaves the old map entry in place.
- Remove FAR or Remove QER with an ID the session does not own is not an error. eUPF deletes internal entry 0, which can belong to another session (`:304-312,345-356`). Open issue [#635](https://github.com/edgecomllc/eupf/issues/635) shows one PFCP peer using this to redirect another session's traffic.
- A failure gives cause 73 with no rollback. Success gives Cause 1 plus any Created PDRs and Usage Reports, without Node ID.
- Query URR, PFCPSMReq-Flags and the BAR IEs are never read.

## Session Deletion Request (`pfcp_session_handlers.go:151-224`)

- No association gives cause 72. An unknown SEID gives cause 65 with SEID 0.
- eUPF removes the session's PDRs, FARs, QERs and URRs, then releases the UE IP and TEIDs it allocated. It tracks those by CP SEID (`pfcp_connection.go:221-233`).
- The reply is Cause 1, plus one Usage Report per URR, with the CP SEID in the header. A datapath delete failure gives cause 73. Since v0.7.2, a missing map key counts as success (`cmd/ebpf/pdr.go:22-27`, fix #650).

## Cause values eUPF sends

1 (accepted), 65 (session not found), 66 (mandatory IE missing), 69 (mandatory IE incorrect, Association Setup and Update only), 72 (no association), 73 (rule creation or modification failure). `convertErrorToIeCause` can return 64, but nothing reaches it with an error other than the missing-IE one (`pfcp_session_handlers.go:497-525`). eUPF never includes Offending IE. `docs/PfcpCauseCodes.md` lists 69 as unused, which is wrong.

## TEID and UE IP allocation

- With the defaults (`feature_ftup` and `feature_ueip` both false), the SMF allocates both. `Validate` empties both pools (`cmd/config/config.go:126-132`), so a CHOOSE request gets "no free TEID" and cause 73.
- With FTUP on, eUPF hands out TEIDs from 1 to `teid_pool` and returns each one in a Created PDR, with `n3_address` as the IPv4 (`service/resource_manager.go:54-68,90-108`, `pdr.go:36-50`). With UEIP on, eUPF allocates from `ueip_pool`, one address per session.

## v1.0.0-rc.1

A pre-release published one day after v0.7.2. It adds handlers for Association Update Response, Association Release Request and Session Report Response (`cmd/core/pfcp_connection.go:31-41` at `a74d03a`). It also adds rollback on failed session requests, a Huawei Sxa/Sxb profile, and moves to go-pfcp v0.0.24. It keeps the 1500-byte buffer and the heartbeat crash. For the milestone, pin v0.7.2.

## Implications for the milestone's PFCP codec

The milestone needs one association, heartbeats, and one IPv4 PDU session with two PDRs, two FARs and one QER. Run eUPF with `feature_ftup` and `feature_ueip` off and `pfcp_remote_node` empty, so the SMF starts the association and allocates the TEIDs and UE addresses. That way we never depend on Created PDR, and never have to send CP Function Features to satisfy eUPF.

**Messages to encode:** Heartbeat Request (1), Heartbeat Response (2), Association Setup Request (5), Session Establishment Request (50), Session Modification Request (52), Session Deletion Request (54).

**Messages to decode:** Heartbeat Request (1), Heartbeat Response (2), Association Setup Response (6), Session Establishment Response (51), Session Modification Response (53), Session Deletion Response (55). Every other type must be decoded far enough to drop it safely.

**IEs to encode:** Node ID (60), Recovery Time Stamp (96), F-SEID (57), Create PDR (1) containing PDR ID (56), Precedence (29), PDI (2) with Source Interface (20) and either F-TEID (21) or UE IP Address (93), Outer Header Removal (95, uplink only), FAR ID (108) and QER ID (109). Create FAR (3) containing FAR ID, Apply Action (44), and Forwarding Parameters (4) with Destination Interface (42), plus Outer Header Creation (84) on the downlink. Update FAR (10) containing FAR ID, Apply Action and Update Forwarding Parameters (11) with Destination Interface and Outer Header Creation. Create QER (7) containing QER ID, Gate Status (25), MBR (26) and QFI (124).

**IEs to decode:** Cause (19), Node ID (60), Recovery Time Stamp (96), F-SEID (57), and UP Function Features (43), which eUPF sends as 4 octets (`go-pfcp/ie/up-function-features.go:12-15`). The decoder must skip unknown IEs, and Created PDR (8) and Usage Report (79) in particular, without misreading them.

**Leave out for now:** URRs, SDF filters, Network Instance and BAR. eUPF ignores or mishandles each of them, and the default PDU session does not need them. Network Instance is spec-optional, so leaving it out costs nothing with eUPF. It may matter when we switch UPF.

**Rules our SMF must follow.** eUPF does not enforce any of these, so a slip turns into a crash or a silent misroute:

- Make uplink TEIDs unique across every session, because eUPF keys uplink PDRs by TEID alone.
- Have every PDR reference a FAR and a QER created earlier in the same session. Never send an unknown or removed ID.
- Put Source Interface in every PDI, and put a PDI in every Update PDR.
- Create the downlink FAR with Apply Action DROP. After the gNB answers, change it with Update FAR to FORW plus OHC GTP-U/UDP/IPv4 carrying the gNB's TEID and address. Set the QER's QFI to the QoS flow announced to the UE and gNB.
- Keep every message under 1500 bytes. Send from the IP the association used, listen on UDP 8805 at that IP, and answer eUPF's heartbeats within 5 s. Otherwise eUPF drops every session after roughly 15 to 30 s.
- Never retransmit a Session Establishment Request faster than eUPF can reply, since a duplicate creates a second session. A T1 of a few seconds should do.
- Treat eUPF's replies as untrusted input. ADR 0002 keeps the codec exposed for exactly this reason. Isolate the N4 network as well: eUPF accepts associations from any IP and lets one peer overwrite another's rules (#635), and nothing we prove in the kernel covers that.

## Open questions

- The **Inferred** lines above came from reading code. The ones that matter most for the milestone are the F-SEID address, duplicate sessions, and decapsulation when OHR is absent. A first run with UERANSIM, eUPF v0.7.2 and a packet capture should confirm or refute them.
- [#637](https://github.com/edgecomllc/eupf/issues/637) reports a crash on valid Session Modification IEs against the `:latest` image. Its stack trace line numbers do not match v0.7.2, and I could not tell from the source which valid input fails to parse. Our Update FAR uses the same function, so test it early.
