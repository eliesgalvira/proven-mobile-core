# 43 The tools in Rust

Depends on: 40. Estimate: 3–5 days.

## Goal

The repo's tools are 16 Python files, about 4,600 lines. Port every one to Rust, in one crate under `tools/` (or the existing `edge/` workspace if that is simpler), built by the flake and available in its dev shell. In this order:

1. **`tools/ngap-gen`**, half the lines: `ngap_model.py`, `gen.py`, `gen_show.py`, `gen_proofs.py`, `extract.py`, `test_gen.py`, `oracle.py`. Today the model comes from pycrate's parse of TS 38.413's ASN.1. The Rust generator needs its own ASN.1 front end for the subset NGAP uses (a Rust ASN.1 parser crate, or a parser for exactly that subset). The oracle's value is that it is an independent APER implementation: replace pycrate there with another independent one (for example a Rust crate generated from the same ASN.1), never with the generator's own codec.
2. **`test-vectors/capture/setup/*.py`**: `capture.py`, `extract.py` (pcap reading, NAS and PFCP decoding, the key derivations with AES, HMAC and SHA-256), `pfcp_probe.py` (scapy).
3. **`scripts/privacy-check.py`**, which stays the `pre-push` hook, and `.githooks/commit-msg`. A hook must work in a fresh clone, so it runs a binary the flake builds, or nushell where the hook is a few lines.
4. **`scripts/acceptance.py`**, `scripts/gen-vectors.py`, `scripts/frame-client.py`, and `.claude/hooks/session-start.py` and `stop.py` (nushell is enough for the last two).

## Acceptance

- Each port gives output byte for byte identical to the Python it replaces: the generated `.bend` files (`kernel/ngap/gen/`), the extracted vectors from the same pcaps, the privacy check's verdicts and messages on the same pushes, the acceptance list's lines. Show it by running both on the same inputs before deleting the Python.
- `scripts/check.nu --strict` and `nix build .#checks.x86_64-linux.e2e` pass.
- When everything is ported, the repo has no `.py` file, the dev shell has no Python, and `AGENTS.md` says new tools are written in Rust, or in nushell when they are a few lines, never in Python.

## Verify

`scripts/check.nu --strict`, `nix build .#checks.x86_64-linux.e2e`, and `git ls-files '*.py'` empty.
