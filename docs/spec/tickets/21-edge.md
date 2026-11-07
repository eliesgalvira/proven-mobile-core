# 21 Edge (Rust)

Depends on: 15.

## Goal

`edge/`, a Rust crate with one binary, `edge --config <file>`. It is plain Rust with no `unsafe` beyond the SCTP socket calls, which live in one module. Responsibilities:

- Spawn `build/kernel <port>`, connect to it, and send `Config` from the TOML file (`edge/config.example.toml` documents every key).
- **N2:** an SCTP listener on the configured address, port 38412, via `libc` (`IPPROTO_SCTP`), with NGAP PPID 60. Map each association to a `u32` id, and carry the stream id both ways.
- **N4:** a UDP socket on the SMF N4 address, port 8805, exchanging datagrams with the UPF N4 address only. Datagrams from any other source are dropped and logged.
- **Timers:** a min-heap keyed by the kernel's timer ids, which drives `TimerFired`.
- **Entropy:** 32 bytes from the OS CSPRNG (`getrandom`) on every event.
- **One event at a time:** wait for the `Actions` frame before sending the next event.
- **Failure handling:** if the kernel dies or sends an invalid frame, the edge logs, closes every association and exits non-zero. It never guesses.

## Laws

None (Rust). The frame codec reuses the hand-made frames of ticket 15 as shared JSON vectors in `test-vectors/frames.json`, so both sides are tested against the same bytes.

## Tests

- `cargo test`: the frame codec against the shared vectors, the timer heap, and the config parser.
- An integration test with a fake kernel.
- An SCTP loopback test that prints `SKIP: no SCTP` and passes if the kernel refuses `IPPROTO_SCTP`. In that case, record it in `loop/blockers.md` for ticket 22.

## Verify

`cargo test --manifest-path edge/Cargo.toml && scripts/check.nu`
