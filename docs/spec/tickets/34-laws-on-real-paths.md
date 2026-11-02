# 34 Laws stated over the paths the kernel runs

Depends on: 19. Estimate: 3–4 h.

## Goal

Restate the laws that are about helpers the kernel never calls, or that leave cases out, and correct `loop/acceptance-report.md` with them:

1. **Serving network name** (advisory GHSA-f9c2-535p-3mwc): state `kdf.snn.nonempty` over `Ausf.snn(Cfg.plmn(cfg))`, which is what the AUSF uses. Make `Cfg.complete` check that the PLMN decodes, with a law.
2. **TBCD** (advisory GHSA-vp44-3q85-5cm4): state `bytes.tbcd.length` over `B.Tbcd.decode`, the decoder of MSIN, IMEI and IMEISV. The `Tbcd.decode_len` lemma exists. Delete `B.tbcd_digits`.
3. **PFCP tunnels** (advisory GHSA-3mxx-vq7h-x8ff): add a law for `Fseid.read`, the F-SEID the kernel parses from the UPF: `Fseid.write(f) == body`. Restate `pfcp.fteid.decode_valid` in the same shape, because `valid(f)` can't say that the length matches the flags.
4. **ePCO in the Accept** (advisory GHSA-796x-8w26-2xfp): compute each container's length from its bytes, and add a law that `Epco.valid` holds for `Gsm.epco_containers(cfg, w)` with a validated config.
5. **Establishment failures:**
   - `smf.establish.reject_leaves_state` gains the empty-pool case (#26).
   - `smf.establish.failure_releases` holds whenever the PSI is in the gNB's failed list, and states that a PFCP Session Deletion is emitted.
6. **Laws that are true by construction:** tie `smf.packet_filters.capacity_reject` to the Accept stored in each Creating session, and restate `smf.teid.unique` over a table where `Sessions.unique` holds.
7. **Advisory rows:** the 5GSM laws whose decoders only tests use (`nas.qos_rules.suffix`, `nas.packet_filter.mask_contiguous`, `nas.session_ambr.decode_valid`) should say in their advisory rows that the kernel keeps those IEs as bytes and never parses them.

## Verify

`scripts/test-kernel.sh --strict && python3 -I scripts/acceptance.py --strict && scripts/check.sh`
