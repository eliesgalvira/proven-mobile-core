# 29 Handover rows into the acceptance list

Depends on: 27, 28. Estimate: 1 h.

## Goal

1. In `docs/security/open5gs-advisories-2026.md`, move GHSA-wpwr-xj64-h6cp and GHSA-v6fv-hmw8-6ffv from `out (handover)` to `in`, naming the laws of ticket 28 in their Law column. Update the summary counts.
2. Extend `loop/acceptance-report.md` with both rows.

## Verify

`scripts/test-kernel.nu --strict && python3 -I scripts/acceptance.py --strict && scripts/check.nu`
