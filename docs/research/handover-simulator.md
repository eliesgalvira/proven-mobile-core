# A RAN simulator for handover against Open5GS 2.8.0

Answers ticket 24's first question: which simulator runs an Xn-based and an N2-based handover between two gNBs against Open5GS 2.8.0. Researched 2026-11-07 by reading the source code, then by running PacketRusher in the capture bench (`test-vectors/capture/setup/handover.py`).

## Sources

| Source | Version | Pin |
|---|---|---|
| UERANSIM | v3.3.0, the milestone 1 simulator | nixpkgs `d357a2b` `ueransim.src`, upstream tag `v3.3.0` |
| PacketRusher | v2.0.0 (2026-10-05) | [`6fef144`](https://github.com/HewlettPackard/PacketRusher/tree/6fef144296d4b1595e690a3d8e55c2a25407077b) |
| free5gc/ngap, PacketRusher's NGAP library | v1.2.0 | `go.mod` of PacketRusher |
| Open5GS | v2.8.0 | nixpkgs `d357a2b` `open5gs.src` |

Citation format: `file:N` is a line in the source of the section's simulator at the pin above.

## Short answer

- **UERANSIM 3.3.0 implements no handover**, neither Xn nor N2. It cannot be the simulator.
- **PacketRusher v2.0.0 implements both**: Xn handover (Path Switch) and N2 handover (Handover Required) between gNBs it simulates in one process, triggered from a control socket. It has **no Handover Cancel**. A patch of 63 added lines adds one (`test-vectors/capture/setup/packetrusher/handover-cancel.patch`).
- PacketRusher with the patch is the chosen simulator. The capture in `test-vectors/capture/handover.json` holds one Xn handover, one N2 handover cancelled after the Handover Command, and one N2 handover, all accepted by Open5GS 2.8.0, with the user plane working through eUPF after each.
- The messages no simulator produced against Open5GS need hand-built vectors from TS 38.413 (see the last section).

## UERANSIM 3.3.0: no handover

- The gNB's NGAP receive dispatch handles only Error Indication, Initial Context Setup Request, Reroute NAS Request, UE Context Release Command, UE Context Modification Request, PDU Session Resource Setup Request, Downlink NAS Transport, AMF Configuration Update, Overload Start/Stop, PDU Session Resource Release Command and Paging (`src/gnb/ngap/transport.cpp:294-328`). Its only successful outcome is NG Setup Response (`:340`) and its only unsuccessful outcome NG Setup Failure (`:353`). Anything else, a Handover Request, Handover Command or Path Switch Request Acknowledge included, is logged as unhandled (`:331`, `:344`, `:357`).
- The handover procedure codes appear only in the criticality table used when building Error Indications (`src/gnb/ngap/transport.cpp:57`, `:64-66`). Outside the generated ASN.1 code (`src/asn/`), no file builds a Path Switch Request, Handover Required, Handover Request Acknowledge, Handover Notify or Handover Cancel.
- The UE has no handover either. It does cell selection only outside RRC_CONNECTED (`src/ue/rrc/idle.cpp:22-23`). When the serving cell's signal is lost in RRC_CONNECTED it declares a radio link failure (`src/ue/rrc/cells.cpp:46-70`) and reconnects through RRC setup and a NAS procedure on the new cell, which is not a handover.
- Neither CLI offers a handover command (`src/lib/app/cli_cmd.cpp:148-169`).

## PacketRusher v2.0.0: Xn and N2, without cancel

What it implements, from source and confirmed on the wire:

- **Xn handover.** `TriggerXnHandover` hands the UE to the target gNB inside the process (`internal/control_test_engine/gnb/ngap/trigger/trigger.go:211-228`). The target gNB sends the Path Switch Request when the UE attaches to it (`internal/control_test_engine/gnb/nas/service/service.go:80`, built by `trigger.go:163`). Path Switch Request Acknowledge updates the uplink tunnel and completes the move (`internal/control_test_engine/gnb/ngap/handler.go:911-988`).
- **N2 handover.** `TriggerNgapHandover` sends Handover Required from the source (`trigger.go:230-252`). The target answers Handover Request with Handover Request Acknowledge (`handler.go:990-1143`). The source moves the UE on Handover Command (`handler.go:1145-1181`), and the target sends Handover Notify once the UE arrives (`service.go:61`). Open5GS then releases the source context with UE Context Release Command, which PacketRusher handles (`handler.go:641-691`).
- **Triggers.** Timed (`--timeBeforeXnHandover`, `--timeBeforeNgapHandover`) or through `multi-ue --control-socket` with the actions `xn-handover` and `ng-handover` to a target gNB ID (`internal/common/tools/tools.go:231-238`, `internal/control/control.go:51`). `--number-of-gnbs N` creates N gNBs on consecutive N2/N3 addresses and gNB IDs (`tools.go:31-65`).

What it lacks:

- **Handover Cancel.** No code sends Handover Cancel or handles Handover Cancel Acknowledge: the dispatcher has no case for it (`internal/control_test_engine/gnb/ngap/dispatcher.go:85-118`), and `HandoverCancelled` appears only as a cause name for logs (`handler.go:1306`).
- **Failures.** A target that cannot admit the UE logs and sends nothing (`handler.go:1086-1090`): no Handover Failure. Nothing in the scenarios makes Open5GS answer Path Switch Request Failure or Handover Preparation Failure.
- **RAN status transfer.** No Uplink or Downlink RAN Status Transfer.
- **Security Context.** The gNBs ignore the NH and NCC in Path Switch Request Acknowledge and Handover Request, since PacketRusher simulates no AS security. Only the AMF's bytes carry them, which is what the capture needs.
- **Container contents are placeholders.** The Source-to-Target container smuggles PacketRusher's own UE ID in IndexToRFSP (read back at `handler.go:1080-1084`), and the Target-to-Source container's RRC container is the 3 octets `000011` (`.../ue_mobility_management/handover-request-acknowledge.go`, `buildTargetToSourceTransparentTransfer`). Both are valid ASN.1 but not real RRC. A kernel must treat both containers as opaque, which TS 38.413 asks for anyway.
- **No data forwarding.** Handover Request Acknowledge has no DL forwarding tunnel, so Open5GS sets up no indirect forwarding, which milestone 2 leaves out of scope anyway.

### The cancel patch

`ng-handover-cancel` sends Handover Required as `ng-handover` does, then answers the Handover Command with Handover Cancel, cause radio network `handover-cancelled`, and logs the Handover Cancel Acknowledge. It adds one builder file (`handover-cancel.go`, 17 lines) and touches five files of PacketRusher. The flake applies it to the pinned source (`setup/flake.nix`, `packetrusher`). The patch modifies an Apache-2.0 test tool and never enters the kernel.

Cancelling after the Handover Command is the case TS 38.413 §8.4.6 describes for a prepared handover. A cancel during preparation, before the Handover Command, is not captured.

## What Open5GS 2.8.0 did with them

- It accepts all three procedures: Path Switch (`src/amf/ngap-handler.c:2872`), Handover Required (`:3327`), Handover Cancel (`:4122`), Handover Notify (`:4423`).
- On Handover Cancel it asks the SMF to cancel, sends UE Context Release Command to the target, and answers the source with Handover Cancel Acknowledge after the target's release complete (`src/amf/nsmf-handler.c:761-773`). No PFCP message is sent for the cancel.
- NH and NCC: after registration the AMF holds NH_1 with NCC 1 (`src/amf/gmm-handler.c:295-296`). Path Switch and Handover Required each increment NCC and chain a new NH before sending it (`ngap-handler.c:3323-3324`, `:3740-3741`). The cancelled handover does not roll back: in the capture the Path Switch carries NCC 2 (NH_2), the cancelled Handover Request NCC 3 (NH_3), and the completed Handover Request NCC 4 (NH_4). `setup/extract.py` recomputes each NH from K_AMF and K_gNB.
- eUPF's XDP path sends downlink G-PDUs only to a gNB address already in its ARP table. Without the ARP warm-up in `handover.py`, the downlink to the second gNB was silently dropped after the Xn handover although the FAR was updated correctly. This is a bench artefact, not something the kernel's SMF can fix.

## What needs hand-built vectors from TS 38.413

Both kinds of handover are covered by the capture, so tickets 27, 28 and 30 can use PacketRusher. These messages and transfers of ticket 25's set never appeared on the wire, so their vectors must be built by hand from TS 38.413 (and checked with the pycrate oracle):

| Not captured | Needed by |
|---|---|
| PathSwitchRequestFailure, PathSwitchRequestUnsuccessfulTransfer, PathSwitchRequestSetupFailedTransfer | 25, 27 |
| HandoverFailure, HandoverPreparationFailure, HandoverResourceAllocationUnsuccessfulTransfer | 25, 28 |
| UplinkRANStatusTransfer, DownlinkRANStatusTransfer | 25, 28 |
| HandoverCancel before the Handover Command (during preparation) | 28 |

Ticket 30's end-to-end test can drive PacketRusher's `xn-handover` and `ng-handover` actions, and does not need the cancel patch.
