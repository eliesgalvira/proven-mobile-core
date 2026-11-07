# 37 Simplification pass

Depends on: 32–36. Estimate: 3–4 h.

## Goal

The findings of the owner's simplify review on 2026-11-03, about 3,000 lines and 150 branches. Re-run `--verdict` after each step that touches proofs.

1. **Generated round-trip helpers:** delete them (`emit_roundtrips`, about 2,200 lines of `kernel/ngap/gen/types.bend`). The one test that uses them gets a generic helper.
2. **NGAP generators:**
   - register EXTS and IE as pseudo-types, compute the type order once, and share `data()`;
   - stop emitting the unused `.Sx` types;
   - drop the comments inside function bodies in `gen.py` and `gen_proofs.py`.
3. **Dead definitions:**
   - `pfcp.bend`: `NodeId/Fseid/UeIp/Ohc.valid`;
   - `frame.bend`: `Sub.valid`, `Input.entropy`, `Action.kind`;
   - `nas/ies.bend`: `Ksi.write`, `MmCap.*`, `SNssai.sst/sd`, `NetFeature.ims_vops_3gpp`;
   - `nas/security.bend`: `Count.overflow`;
   - `smf/gsm.bend`: `Gsm.to_ue`, `Gsm.fired`;
   - unused lemmas: `U32.byte_fits`, `U8.rd`, `Hdr.kind`.
4. **Shared codec shapes:**
   - one `B.Read.cons`, one `B.end`/`B.guard` and one `B.Res`;
   - `Seid.write` becomes `Addr.write`, and `fits24` moves to `bytes.bend`;
   - the duplicate lemmas (`lt10_mask4` from `lt256_mask8`, `Bool.not_true`, `or_false_*`) go.
5. **Hot paths:**
   - an indexed S-box in AES;
   - one key expansion and one TEMP per Milenage run;
   - linear frame buffering in `main.bend`;
   - one walk for `N4.deletions`.
6. **Names:**
   - name the dispatch steps `Route.d1..d7` and `Gsm.pfcp_k1..k6`, with named constants for procedure codes and IE ids;
   - drop the product name "eUPF" from kernel code and logs (the glossary term is UPF).
7. **Tests:** move the test helpers copied between files to `kernel/tests/lib/`.
8. **Tooling:** add a flake dev shell with bend, Lean 4.34, python3 with pycrate 0.8.1, cargo and clang, so `scripts/check.sh` runs from a pinned environment.

9. **From the reviews of 2026-11-07:**
   - one invariant walk over the dispatch tree, parametric in its predicate, replacing the copies in `proofs/takeover.bend`, `proofs/liveness.bend`, `proofs/smf.bend` (`Bd.*`) and `proofs/kernel.bend` (`Route.*_unique`, `Cfgv.*`);
   - general lemmas (`Some.inj`, `U32.eq_true`, `Bytes.*`, `Lv.or_l`, `Lv.or_r`, `Bool.or_true`) moved to `proofs/lib.bend`;
   - `amf.ng_setup.requires_supported_plmn` moved out of `liveness.bend`;
   - one F-SEID/F-TEID flags lemma;
   - the per-step session search of `N.Step.of` (ticket 35) and the eager `Ip.alloc` in `Gsm.validate`;
   - the `Created` phase, if `Gmm.proceed` can build the context when its first phase is known.
10. **No bash:** rewrite `scripts/check.sh` and `scripts/test-kernel.sh` in nushell (add nushell to the dev shell), and replace `test-vectors/capture/setup/run.sh` with the Python orchestration ticket 24 started. The capture bring-up then exists once.
11. **The e2e edge unit** waits until its address is configured (`After` and `Wants` on the network target), so its first start doesn't fail binding.

## Verify

`scripts/check.sh && nix build .#checks.x86_64-linux.e2e`
