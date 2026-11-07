# 36 Edge robustness

Depends on: 21. Estimate: 1–2 h.

## Goal

1. **Timers:** today they are checked only when the channel read times out, so steady N2 and N4 traffic can starve T3560 and T1. Fire every expired timer after each event as well.
2. **Kernel exit:** notice when the kernel process exits while the edge is idle, then close every association and exit non-zero.
3. **Association ids:** they are drawn with `checked_add`, and an id still live in the map is never reused.
4. **N4 replies:** answer a UPF request at its source address and port, because the UPF sends from a port it chooses (TS 29.244 §7.2), and keep dropping datagrams from any other address.
5. **Config lengths:** the encoder rejects config values longer than a TLV can carry, such as an `amf_name` over 65535 bytes.

## Verify

`cargo test --manifest-path edge/Cargo.toml && nix build .#checks.x86_64-linux.e2e`
