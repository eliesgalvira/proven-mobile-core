# 07 5G key derivation

Depends on: 04, 06.

## Goal

`kernel/crypto/kdf.bend`: the generic KDF of TS 33.220 Annex B.2 (HMAC-SHA-256 over FC ‖ P0 ‖ L0 ‖ …). On top of it, per TS 33.501 Annex A:
- KAUSF (A.2), with the serving network name;
- RES*/XRES* (A.4);
- HRES*/HXRES* (A.5);
- KSEAF (A.6);
- KAMF (A.7);
- NAS keys KNASint/KNASenc (A.8);
- KgNB (A.9).

The serving network name is `5G:mnc<MNC>.mcc<MCC>.3gppnetwork.org` (TS 24.501 §9.12.1), built by `kdf.serving_network_name(plmn)`.

## Laws

- `kdf.length`: every derived key is 32 bytes; RES*/XRES* are 16 bytes (the last 128 bits of the KDF output); HXRES* is 16 bytes.
- `kdf.snn.nonempty` (advisory GHSA-f9c2-535p-3mwc): `serving_network_name(plmn)` is never empty. In this design the AUSF only ever receives the serving network name from this function, never from a peer.

## Tests

Recompute RES*, HXRES*, KAUSF, KSEAF, KAMF and the NAS keys for the captured session from K, OPc, RAND, SQN and the SNN, and compare with the captured RES* and the observed NAS MACs.

## Verify

`scripts/check.sh`
