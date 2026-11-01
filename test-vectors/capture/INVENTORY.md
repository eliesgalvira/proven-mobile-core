# Inventory of the capture

What actually appeared in `registration-pdu.pcapng` / `vectors.json`, and what eUPF v0.7.2 did when probed (`eupf-probes.pcapng` / `eupf-probes.json`). `#` is the `index` in `vectors.json` `messages`. Names are Wireshark 4.6's. Bytes, IE ids and counts come from `setup/extract.py`'s own parser.

Flow: PFCP association (SMF starts it) and heartbeats, NG Setup, initial registration with SUCI Profile A, 5G-AKA, NAS security mode (NEA0/NIA2), Initial Context Setup, Registration complete, PDU session establishment (IPv4, DNN `internet`, SST 1), PFCP Session Establishment and Modification, then 4 pings from the UE to the data network (8 G-PDUs). There is no deregistration, release or Service Request in this capture.

## NGAP

| # | Message | Dir | Procedure code | Top-level IEs (id name) |
|---|---|---|---|---|
| 8 | NGSetupRequest (initiatingMessage) | gNB->AMF | 21 | 27 id-GlobalRANNodeID, 82 id-RANNodeName, 102 id-SupportedTAList, 21 id-DefaultPagingDRX |
| 9 | NGSetupResponse (successfulOutcome) | AMF->gNB | 21 | 1 id-AMFName, 96 id-ServedGUAMIList, 86 id-RelativeAMFCapacity, 80 id-PLMNSupportList |
| 14 | InitialUEMessage (initiatingMessage) | gNB->AMF | 15 | 85 id-RAN-UE-NGAP-ID, 38 id-NAS-PDU, 121 id-UserLocationInformation, 90 id-RRCEstablishmentCause, 112 id-UEContextRequest |
| 16 | DownlinkNASTransport (initiatingMessage) | AMF->gNB | 4 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID, 38 id-NAS-PDU |
| 18 | UplinkNASTransport (initiatingMessage) | gNB->AMF | 46 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID, 38 id-NAS-PDU, 121 id-UserLocationInformation |
| 20 | DownlinkNASTransport (initiatingMessage) | AMF->gNB | 4 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID, 38 id-NAS-PDU |
| 22 | UplinkNASTransport (initiatingMessage) | gNB->AMF | 46 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID, 38 id-NAS-PDU, 121 id-UserLocationInformation |
| 25 | InitialContextSetupRequest (initiatingMessage) | AMF->gNB | 14 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID, 28 id-GUAMI, 0 id-AllowedNSSAI, 119 id-UESecurityCapabilities, 94 id-SecurityKey, 34 id-MaskedIMEISV, 38 id-NAS-PDU |
| 27 | InitialContextSetupResponse (successfulOutcome) | gNB->AMF | 14 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID |
| 28 | UplinkNASTransport (initiatingMessage) | gNB->AMF | 46 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID, 38 id-NAS-PDU, 121 id-UserLocationInformation |
| 30 | UplinkNASTransport (initiatingMessage) | gNB->AMF | 46 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID, 38 id-NAS-PDU, 121 id-UserLocationInformation |
| 33 | DownlinkNASTransport (initiatingMessage) | AMF->gNB | 4 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID, 38 id-NAS-PDU |
| 37 | PDUSessionResourceSetupRequest (initiatingMessage) | AMF->gNB | 29 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID, 74 id-PDUSessionResourceSetupListSUReq, 110 id-UEAggregateMaximumBitRate |
| 40 | PDUSessionResourceSetupResponse (successfulOutcome) | gNB->AMF | 29 | 10 id-AMF-UE-NGAP-ID, 85 id-RAN-UE-NGAP-ID, 75 id-PDUSessionResourceSetupListSURes, 121 id-UserLocationInformation |

## NAS

| # | Protocol | Message (type) | Dir | Security header | NAS COUNT | Top-level IEs |
|---|---|---|---|---|---|---|
| 15 | NAS-5GMM | Registration request (0x41) | UL | 0 | - | 5GS registration type, NAS key set identifier, 5GS mobile identity, UE security capability (0x2e) |
| 17 | NAS-5GMM | Authentication request (0x56) | DL | 0 | - | NAS key set identifier - ngKSI, ABBA, Authentication Parameter RAND - 5G authentication challenge (0x21), Authentication Parameter AUTN (UMTS and EPS authentication challenge) - 5G authentication challenge (0x20) |
| 19 | NAS-5GMM | Authentication response (0x57) | UL | 0 | - | Authentication response parameter (0x2d) |
| 21 | NAS-5GMM | Security mode command (0x5d) | DL | 3 | 0 | NAS security algorithms, NAS key set identifier - ngKSI, UE security capability - Replayed UE security capabilities, IMEISV request (0x0e), Additional 5G security information (0x36) |
| 23 | NAS-5GMM | Security mode complete (0x5e) | UL | 4 | 0 | 5GS mobile identity (0x77), NAS message container (0x71) |
| 24 | NAS-5GMM | Registration request (0x41) | UL | 0 | - | 5GS registration type, NAS key set identifier, 5GS mobile identity, 5GMM capability (0x10), UE security capability (0x2e), NSSAI - Requested NSSAI (0x2f), 5GS update type (0x53) |
| 26 | NAS-5GMM | Registration accept (0x42) | DL | 2 | 1 | 5GS registration result, 5GS mobile identity - 5G-GUTI (0x77), 5GS tracking area identity list (0x54), NSSAI - Allowed NSSAI (0x15), 5GS network feature support (0x21), GPRS Timer 3 - T3512 value (0x5e) |
| 29 | NAS-5GMM | Registration complete (0x43) | UL | 2 | 1 | (none) |
| 31 | NAS-5GMM | UL NAS transport (0x67) | UL | 2 | 2 | Payload container type, Payload container, PDU session identity 2 - PDU session ID (0x12), Request type (0x08), S-NSSAI (0x22), DNN (0x25) |
| 32 | NAS-5GSM | PDU session establishment request (0xc1) | UL | - | - | Integrity protection maximum data rate, PDU session type (0x09), SSC mode (0x0a), 5GSM capability (0x28), Extended protocol configuration options (0x7b) |
| 34 | NAS-5GMM | Configuration update command (0x54) | DL | 2 | 2 | Network Name - Full name for network (0x43), Network Name - Short Name (0x45), Time Zone - Local (0x46), Time Zone and Time - Universal Time and Local Time Zone (0x47), Daylight Saving Time (0x49) |
| 38 | NAS-5GMM | DL NAS transport (0x68) | DL | 2 | 3 | Payload container type, Payload container, PDU session identity 2 - PDU session ID (0x12) |
| 39 | NAS-5GSM | PDU session establishment accept (0xc2) | DL | - | - | PDU session type - Selected PDU session type, QoS rules - Authorized QoS rules, Session-AMBR, PDU address (0x29), S-NSSAI (0x22), QoS flow descriptions - Authorized (0x79), Extended protocol configuration options (0x7b), DNN (0x25) |

## PFCP

### #0 Association Setup Request (SMF->UPF, type 5, seq 1)

- 60 Node ID (5 octets)
- 96 Recovery Time Stamp (4 octets)
- 89 CP Function Features (1 octets)

### #1 Association Setup Response (UPF->SMF, type 6, seq 1)

- 60 Node ID (5 octets)
- 19 Cause (1 octets)
- 96 Recovery Time Stamp (4 octets)
- 43 UP Function Features (4 octets)

### #35 Session Establishment Request (SMF->UPF, type 50, seq 4, header SEID 0x0000000000000000)

- 60 Node ID (5 octets)
- 57 F-SEID (13 octets)
- 1 Create PDR (74 octets)
  - 56 PDR ID (2 octets)
  - 29 Precedence (4 octets)
  - 2 PDI (32 octets)
    - 20 Source Interface (1 octets)
    - 22 Network Instance (9 octets)
    - 93 UE IP Address (5 octets)
    - 160 3GPP Interface Type (1 octets)
  - 108 FAR ID (4 octets)
  - 81 URR ID (4 octets)
  - 109 QER ID (4 octets)
- 1 Create PDR (80 octets)
  - 56 PDR ID (2 octets)
  - 29 Precedence (4 octets)
  - 2 PDI (41 octets)
    - 20 Source Interface (1 octets)
    - 21 F-TEID (9 octets)
    - 22 Network Instance (9 octets)
    - 124 QFI (1 octets)
    - 160 3GPP Interface Type (1 octets)
  - 95 Outer Header Removal (1 octets)
  - 108 FAR ID (4 octets)
  - 109 QER ID (4 octets)
- 1 Create PDR (49 octets)
  - 56 PDR ID (2 octets)
  - 29 Precedence (4 octets)
  - 2 PDI (18 octets)
    - 20 Source Interface (1 octets)
    - 21 F-TEID (9 octets)
  - 95 Outer Header Removal (1 octets)
  - 108 FAR ID (4 octets)
- 1 Create PDR (117 octets)
  - 56 PDR ID (2 octets)
  - 29 Precedence (4 octets)
  - 2 PDI (86 octets)
    - 20 Source Interface (1 octets)
    - 21 F-TEID (9 octets)
    - 22 Network Instance (9 octets)
    - 23 SDF Filter (46 octets)
    - 160 3GPP Interface Type (1 octets)
  - 95 Outer Header Removal (1 octets)
  - 108 FAR ID (4 octets)
- 3 Create FAR (19 octets)
  - 108 FAR ID (4 octets)
  - 44 Apply Action (2 octets)
  - 88 BAR ID (1 octets)
- 3 Create FAR (41 octets)
  - 108 FAR ID (4 octets)
  - 44 Apply Action (2 octets)
  - 4 Forwarding Parameters (23 octets)
    - 42 Destination Interface (1 octets)
    - 22 Network Instance (9 octets)
    - 160 3GPP Interface Type (1 octets)
- 3 Create FAR (37 octets)
  - 108 FAR ID (4 octets)
  - 44 Apply Action (2 octets)
  - 4 Forwarding Parameters (19 octets)
    - 42 Destination Interface (1 octets)
    - 84 Outer Header Creation (10 octets)
- 6 Create URR (33 octets)
  - 81 URR ID (4 octets)
  - 62 Measurement Method (1 octets)
  - 37 Reporting Triggers (3 octets)
  - 31 Volume Threshold (9 octets)
- 7 Create QER (32 octets)
  - 109 QER ID (4 octets)
  - 25 Gate Status (1 octets)
  - 26 MBR (10 octets)
  - 124 QFI (1 octets)
- 85 Create BAR (5 octets)
  - 88 BAR ID (1 octets)
- 113 PDN Type (1 octets)
- 141 User ID (19 octets)
- 159 APN/DNN (9 octets)
- 257 S-NSSAI (4 octets)

### #36 Session Establishment Response (UPF->SMF, type 51, seq 4, header SEID 0x00000000000001d2)

- 60 Node ID (5 octets)
- 19 Cause (1 octets)
- 57 F-SEID (13 octets)

### #41 Session Modification Request (SMF->UPF, type 52, seq 5, header SEID 0x0000000000000002)

- 10 Update FAR (55 octets)
  - 108 FAR ID (4 octets)
  - 44 Apply Action (2 octets)
  - 11 Update Forwarding Parameters (37 octets)
    - 42 Destination Interface (1 octets)
    - 22 Network Instance (9 octets)
    - 84 Outer Header Creation (10 octets)
    - 160 3GPP Interface Type (1 octets)

### #42 Session Modification Response (UPF->SMF, type 53, seq 5, header SEID 0x00000000000001d2)

- 19 Cause (1 octets)

Heartbeat Request/Response (types 1/2, both directions, only IE 96 Recovery Time Stamp): #2, #3, #4, #5, #6, #7, #10, #11, #12, #13, #51, #52

## GTP-U

| # | Dir | TEID | Flags | Inner |
|---|---|---|---|---|
| 43 | gNB->UPF | 0x0000c7c4 | 0x34 ext 01100100 | ICMP 10.45.0.2 -> 10.33.0.40 |
| 44 | UPF->gNB | 0x00000001 | 0x34 ext 01000100 | ICMP 10.33.0.40 -> 10.45.0.2 |
| 45 | gNB->UPF | 0x0000c7c4 | 0x34 ext 01100100 | ICMP 10.45.0.2 -> 10.33.0.40 |
| 46 | UPF->gNB | 0x00000001 | 0x34 ext 01000100 | ICMP 10.33.0.40 -> 10.45.0.2 |
| 47 | gNB->UPF | 0x0000c7c4 | 0x34 ext 01100100 | ICMP 10.45.0.2 -> 10.33.0.40 |
| 48 | UPF->gNB | 0x00000001 | 0x34 ext 01000100 | ICMP 10.33.0.40 -> 10.45.0.2 |
| 49 | gNB->UPF | 0x0000c7c4 | 0x34 ext 01100100 | ICMP 10.45.0.2 -> 10.33.0.40 |
| 50 | UPF->gNB | 0x00000001 | 0x34 ext 01000100 | ICMP 10.33.0.40 -> 10.45.0.2 |

Downlink TEID 1 is the gNB's (it comes in PDUSessionResourceSetupResponse and goes to eUPF in the Update FAR's Outer Header Creation). Every G-PDU has flags 0x34 (E set) and one PDU Session Container extension header (type 0x85, length 1). Its content is `00 01` downlink (PDU type 0, QFI 1) and `10 01` uplink (PDU type 1, QFI 1), followed by next-extension 0. The N6 leg of each ping (plain ICMP between eUPF and 10.33.0.40) was filtered out of the pcapng.

## Details worth knowing before writing codecs

- NGAP: every message has a single DATA chunk on SCTP stream 0 (NG Setup) or 1 (UE-associated), PPID 60. Two NGAP messages share one SCTP packet in frame 29 (Registration complete + UL NAS transport).
- NAS security: only the Security mode command uses security header type 3, and only the Security mode complete uses 4. After that, everything is type 2 (integrity protected and ciphered, with NEA0 the identity cipher). The NAS COUNT overflow stays 0. DL counts are 0,1,2,3 and UL counts are 0,1,2.
- **NIA2 BEARER is 1.** All 7 MACs verify with BEARER = 1 and none with BEARER = 0 (COUNT = overflow‖SQN, DIRECTION 0 = UL). TS 33.501 §6.4.3.1 says to use the NAS connection identifier. Check its value against the spec before you treat 1 as normative: Open5GS 2.8.0 and UERANSIM 3.3.0 both use 1 here.
- K_gNB in InitialContextSetupRequest (IE 94) = KDF(K_AMF, 0x6E, UL NAS COUNT = 0, access type 0x01). That count is the Security mode complete's.
- The Registration request inside the Security mode complete's NAS message container (#24) is a full plain copy. It adds 5GMM capability, Requested NSSAI and 5GS update type, which the initial one (#15) left out.
- Open5GS's AMF sends a Configuration update command (network name, time zone) without asking for an acknowledgement, so no Configuration update complete follows.
- PFCP: Open5GS sends Apply Action as 2 octets (`0200` FORW, `0c00` BUFF|NOCP). eUPF sends UP Function Features as 4 octets `00010000` (only EMPU, octet 6 bit 1). Open5GS sends CP Function Features `00`. The Session Establishment Request header has SEID 0. Every reply carries the SMF's CP SEID in its header. The Modification Request carries eUPF's UP SEID.
- Open5GS's Session Establishment Request (#35) carries 4 PDRs, 3 FARs, 1 URR, 1 QER and 1 BAR, which is more than the milestone needs:
  - PDR 1: Source Interface Core, UE IP 10.45.0.2, FAR 1. This is the downlink path.
  - PDR 2: Source Interface Access, F-TEID, QFI, OHR 6, FAR 2. This is the uplink path.
  - PDR 3: Source Interface CP-function (3), F-TEID, OHR 6, FAR 1. Packets from the SMF go to the UE.
  - PDR 4: Source Interface Access, F-TEID, SDF filter `permit out 58 from ff02::2/128 to assigned` (IPv6 router solicitation), OHR 6, FAR 3.
  - FAR 1 (`0c00`, BUFF|NOCP, with a BAR) becomes FORW with OHC towards the gNB in the Session Modification (#41). FAR 2 is FORW to Core. FAR 3 is FORW to CP-function, with OHC `0100 00000001 0a21000c` (TEID 1, the SMF at 10.33.0.12).

## eUPF v0.7.2 observations

eUPF ran from `ghcr.io/edgecomllc/eupf:0.7.2@sha256:01ad4488…` with `pfcp_address: :8805`, `feature_ftup: false`, `feature_ueip: false`, `pfcp_remote_node: []` and XDP generic mode on eth0 (N3 and N6 share one interface). Open5GS SMF 2.8.0 was its only PFCP peer. The probes ran from a helper container in the SMF's network namespace, so their source IP was the associated node 10.33.0.12. They used an ephemeral source port, and eUPF replied to that port. Script: `setup/pfcp_probe.py`.

### F-SEID address when listening on `:8805`: confirmed 0.0.0.0

Every Session Establishment Response carries a UP F-SEID with V4 set and IPv4 **0.0.0.0**. In #36 the F-SEID IE value is `02 0000000000000002 00000000` (UP SEID 2), and the probes' responses show the same. An SMF must send later session messages to the association peer address, never to the F-SEID address.

### A retransmitted Session Establishment Request creates a second session: confirmed, and it breaks the live session

Probe `retransmit` resent #35 byte for byte, with the same sequence number 4 and the same CP F-SEID, about 7 s after the original, and after the Session Modification. eUPF answered with cause 1 and a new UP SEID 3. `GET /api/v1/pfcp_sessions` went from 1 session to 2, and both have the same RemoteSEID (`logs/eupf-sessions.json`). The duplicate rewrote the eBPF entries for the UE's IP and uplink TEID. Its downlink FAR is still BUFF|NOCP, because the Session Modification only ever reached the first session. After that, the real UE's ping failed 3 of 3 (`logs/ping-after-probes.log`), where it had passed 4 of 4 before. eUPF does no duplicate detection on sequence numbers.

### Outer Header Removal absent: confirmed, eUPF strips GTP-U anyway

Probe `no_ohr` established a hand-built session whose uplink PDR (F-TEID 0xabcd) has no Outer Header Removal IE. eUPF logged `Put PDR Uplink: teid=43981, pdrInfo={OuterHeaderRemoval:0 …}` (`logs/eupf.log`). The probe then sent three G-PDUs carrying ICMP 10.45.0.99 → 10.33.0.40. In `eupf-probes.pcapng`, frames 7/10/13 are the GTP-U packets in, frames 8/11/14 are the bare decapsulated ICMP on N6, and frames 9/12/15 are the data network's replies. So an absent OHR behaves like OHR 0 (GTP-U/UDP/IPv4). Open5GS itself always sends OHR 6 (GTP-U/UDP/IP), which v0.7.2 also strips.

### Issue #637 (crash on Session Modification adding a FAR with Outer Header Creation): not reproduced on v0.7.2

- Probe `issue_637` sent the Modification from the issue on the `no_ohr` session: Create PDR (Source Interface Core, UE IPv4 10.45.0.99 with S/D set, SDF filter `permit out ip from any to assigned`, FAR 3, QER 1) + Create FAR (FAR 3, FORW, Destination Interface Access, Network Instance, OHC `0100` TEID 0x777 IPv4 10.33.0.30). eUPF answered cause 1 and installed the FAR (`OuterHeaderCreation:1 Teid:1911`). It did not crash.
- Probe `ohc_zero_addr_establishment` sent the issue's second trigger: a Session Establishment with an extra Create FAR whose OHC IPv4 is 0.0.0.0. Cause 1, no crash.
- The issue's third trigger is "Update FAR + valid OHC on a session a real SMF created". That is exactly Open5GS's own #41, which eUPF accepted. Open5GS's #35 also has a Create FAR with OHC, also accepted.
- eUPF was still `running`, exit 0, after all probes (`logs/eupf.log` has no panic). The issue reports the crash against `:latest`, with stack lines that do not match v0.7.2. The input that crashes it was not found here. Keep validating OHC before use anyway: it is the nil-dereference path in #630.
