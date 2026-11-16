# Proven Mobile Core

> [!WARNING]
> SLOP WARNING: There has been no adult supervision of the code.

The rules of a 5G core (AMF and SMF: registration, PDU sessions, Xn and N2 handover) written as pure functions in [Bend 2](https://github.com/bendlang/bend), with machine-checked proofs that rule out the bug classes behind Open5GS's 2026 security advisories (`docs/security/open5gs-advisories-2026.md`). A thin Rust edge (`edge/`) does the networking, timers and entropy; the user plane is eUPF. Laws are stated in `kernel/LAWS.bend` and count as proven only when `bend kernel/PROOF.bend --verdict` accepts them.

To check it: `nix develop -c nu scripts/check.nu` runs the gate (the proofs, the kernel tests, the edge's tests and the acceptance list), and `nix flake check` runs the end-to-end test (UERANSIM and PacketRusher against the kernel and eUPF in NixOS VMs) and the edge's SCTP test.

0BSD, see LICENSE.
