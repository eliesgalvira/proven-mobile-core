# Capture notes

This directory holds one real UERANSIM UE registration and IPv4 PDU session against Open5GS (AMF, SMF and the other NFs) with eUPF as the UPF. Everything ran in Docker on a Linux laptop on 2026-11-01, and nothing touched a real radio or network. `INVENTORY.md` lists what appeared; this file covers how the capture was made and what went wrong along the way.

## Files

| File | What it is |
|---|---|
| `registration-pdu.pcapng` | Capture on the Docker bridge, filtered to SCTP/NGAP, PFCP and GTP-U (48 frames, 7.8 kB). sha256 `d99d79b1…688a675c` |
| `vectors.json` | Every NGAP, NAS (5GMM, 5GSM) and PFCP message in wire order, plus the 8 G-PDUs, with hex, direction, names and IEs, plus `secrets` and `checks`. Generated from the pcapng by `setup/extract.py`. sha256 `5a3a1ba5…f8a0f92d` |
| `eupf-probes.pcapng`, `eupf-probes.json` | The eUPF probes from `INVENTORY.md`, run after the main capture: PFCP, GTP-U, and the N6 ICMP that shows decapsulation. |
| `logs/` | eUPF log (debug, shows eBPF map writes), the eUPF session list after the probes, AMF/gNB/UE logs, ping results, and the subscriber record after authentication (SQN 64 → 96). |
| `setup/` | Everything needed to rerun the capture: `flake.nix`/`flake.lock` (images and host tools), `docker-compose.yml`, configs, `subscriber.js`, the home-network key, `run.sh`, `pfcp_probe.py`, `extract.py`. |

## Reproduce

```
OUT=/tmp/speck5g-out test-vectors/capture/setup/run.sh
```

You need Nix with flakes, Docker with Compose v2, a user in the `docker` group, and the host's `sctp` kernel module (it was already loaded here; `run.sh` does not load it). No sudo. `run.sh` builds and `docker load`s the two Nix images, starts the stack, captures, runs the probes, saves logs, tears everything down (`KEEP_UP=1` keeps it), then filters the pcap and runs `extract.py`. A rerun gives new bytes, because RAND, the SUCI ephemeral key, TEIDs, SEIDs, the 5G-TMSI and timestamps all change. The message sequence and IE sets stay the same. `extract.py` aborts if any crypto check fails.

`run.sh` takes the flake from its own directory. Inside this repo, Nix evaluates it as a Git flake, so the tracked repo is copied into the store (small).

## Versions and pins

| Component | Version | Source |
|---|---|---|
| nixpkgs | `d357a2b54f0b6dc4aeb4e993190a52cf151b6f24` (lib 26.11.20261101.d357a2b, narHash `sha256-Thn0OE71NF80ZfOMGCgJvKtbCcnnz0fToT/qsvb/Gtc=`) | `setup/flake.lock` |
| Open5GS | 2.8.0 (nixpkgs `open5gs`, from upstream tag `v2.8.0`) | image `speck5g-open5gs:2.8.0`, `dockerTools.buildLayeredImage`, id `sha256:3ebc95c7…15ece53` |
| UERANSIM | 3.3.0 (nixpkgs `ueransim`, from upstream tag `v3.3.0`) | image `speck5g-ueransim:3.3.0`, id `sha256:3e8132e8…c3d39ce` |
| eUPF | v0.7.2 | `ghcr.io/edgecomllc/eupf:0.7.2@sha256:01ad44889ce546ae0720cdc9e648889e9a653d40a20a1867d6751ae6cbb6cb08` |
| MongoDB | 6.0 | `mongo:6.0@sha256:8b6d8f5bbedb25cb73517b65cf99f13aeb75ad5b157a56c479287a840bbad3ac` |
| netshoot (capture, data network, probe helper) | v0.14 | `nicolaka/netshoot:v0.14@sha256:7f08c4aff13ff61a35d30e30c5c1ea8396eac6ab4ce19fd02d5a4b3b5d0d09a2` |
| tshark | 4.6.9 | nixpkgs `wireshark-cli`, same rev (`extract-tools` in the flake) |
| Python | 3.14.8 + `cryptography` | same rev |
| Host | Linux 7.2.6 (CachyOS), Docker 29.8.0, Compose 5.5.1, Nix 2.34.7 | |

## Test bench

- One Docker bridge, `10.33.0.0/24` (`br-5gcap`): mongo .2, NRF .10, AMF .11, SMF .12, AUSF .13, UDM .14, UDR .15, PCF .16, NSSF .17, BSF .18, eUPF .20 (N3, N4 and N6 on one interface), gNB .30, UE .31, data network .40. The data network routes `10.45.0.0/16` via eUPF. UE pool `10.45.0.0/16`, and the UE got 10.45.0.2.
- PLMN 001/01, TAC 1, AMF region 2 / set 1 / pointer 0, gNB id 1 (32 bits), S-NSSAI SST 1, DNN `internet`.
- Subscriber `imsi-001010000000001`: K `465b5ce8b199b49faa5f0a2ee238a6bc`, OPc `e8ed289deba952e4283b54e88e6183ca`, AMF field `8000`, SQN provisioned as 64. Open5GS stores 96 after authenticating.
- SUCI Profile A, home-network key id 1. The X25519 key pair was generated for this bench (`openssl genpkey -algorithm X25519`) and lives in `setup/hnet/curve25519-1.key`. The UE has the public key and the UDM has the private key. Both raw values are in `vectors.json` `secrets.home_network_key`. These are test keys only.
- AMF preference: ciphering NEA0, NEA1, NEA2; integrity NIA2, NIA1, NIA0. Selected: NEA0/NIA2.
- eUPF: `feature_ftup: false`, `feature_ueip: false`, `pfcp_remote_node: []`, `pfcp_address: :8805`, XDP generic mode. The SMF starts the association and allocates TEIDs and UE addresses.
- tcpdump ran in a netshoot container in the host network namespace on `br-5gcap`, with filter `sctp or udp port 8805 or udp port 2152 or icmp`. Its output was streamed to a file the user owns. No host networking or sysctl was changed. eUPF's container is privileged (XDP), and its sysctls apply only inside its own namespace.

## What `vectors.json` can and cannot vouch for

- Captured (on the wire): every message's bytes, RAND, AUTN, ABBA, RES*, the SUCI, the NAS MACs and K_gNB.
- Configured: SUPI, K, OPc, AMF field and the home-network key pair.
- Derived by `extract.py`, an independent Python implementation of TS 35.206 Milenage and TS 33.501 Annex A: SQN (AUTN ⊕ AK, equal to the provisioned 64), CK, IK, AK, RES, HRES*, K_AUSF, K_SEAF, K_AMF, K_NASint, K_NASenc and the SUCI ECIES intermediates. Each is confirmed against captured bytes: MAC-A matches AUTN, the computed RES* matches the UE's, K_NASint verifies all 7 NAS MACs, K_AMF reproduces the K_gNB the AMF sent, and the SUCI MAC tag verifies and decrypts to MSIN 0000000001. HRES* has no on-air counterpart, since it only travels on SBI.
- Not recoverable or not captured: the UE's ephemeral X25519 private key; SBI (HTTP/2) between the NFs (filtered out); RRC (UERANSIM simulates the radio link over UDP 4997 and it was not captured).

## What failed or needed fixing

- Earlier attempts ran the `gradiant/open5gs` and `gradiant/ueransim` images. They were replaced by the Nix images.
- The Nix UERANSIM image first crashed (exit 139, `ProcTable could not be created`) because the image had no `/tmp`. Next, `nr-ue` could not set up its TUN (`Could not open '/etc/iproute2/rt_tables'`), and the image had no `ping`. Fixed with `extraCommands` (a 1777 `/tmp` and a writable `rt_tables`) and `iputils`.
- The first working capture missed the PFCP Association Setup, because tcpdump started after the SMF. `run.sh` now starts the capture before the SMF and AMF.
- The Open5GS image is large: about 3 GB unpacked, 2.96 GB as reported by Docker. The nixpkgs `open5gs` closure (1.2 GiB) pulls in mongosh, nodejs and gcc. It was not trimmed.
- eUPF issue #637 did not reproduce on v0.7.2 with the inputs the issue describes (see `INVENTORY.md`).
- After the probes, the real UE's session no longer carries downlink traffic, because the duplicate session overwrote its eBPF entries. That is why the probes run after the main capture.
- NIA2 MACs verify only with BEARER = 1. Check TS 33.501 before you treat that value as normative (see `INVENTORY.md`).
