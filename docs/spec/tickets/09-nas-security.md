# 09 NAS security: NIA2, NEA2 and COUNT

Depends on: 05, 07.

## Goal

`kernel/nas/security.bend`:
- 128-NIA2 (CMAC over COUNT ‖ BEARER ‖ DIRECTION ‖ 0…, TS 33.401 Annex B.2.3, as used by TS 33.501 §6.4.3);
- 128-NEA2 (CTR, TS 33.401 Annex B.1.3);
- NEA0;
- protect and unprotect per TS 24.501 §4.4.

The NAS COUNT is (overflow: 16 bits, sequence: 8 bits), with the uplink overflow estimated per TS 24.501 §4.4.3.1. BEARER is the NAS connection identifier (TS 33.501 §6.4.3.1). The captured MACs verify only with BEARER = 1, which is what Open5GS and UERANSIM both use; check that value against the spec before relying on it.

## Laws

- `nas_sec.mac_full_length`: integrity verification compares all 4 MAC bytes, and a message shorter than its header plus MAC returns `Fail`.
- `nas_sec.roundtrip`: `unprotect(protect(m, ctx), ctx) = m` for both NEA0 and NEA2 with NIA2.
- `nas_sec.count_monotonic`: accepting an uplink message never moves the stored uplink COUNT backwards, and a replayed COUNT is rejected.

## Tests

TS 33.401 Annex C 128-EIA2 and 128-EEA2 test sets; the captured protected NAS messages verified with the keys from ticket 07.

## Verify

`scripts/check.nu`
