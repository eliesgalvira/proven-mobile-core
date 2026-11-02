# Blockers

One entry per blocker: ticket, what was tried, smallest reproduction, what would unblock it.

## Ticket 22: the cloud VM has no SCTP

- Ticket: 22 (found while testing ticket 21's edge).
- Tried: opening `socket(AF_INET, SOCK_STREAM, IPPROTO_SCTP)` on the session VM (Linux 6.18.44-fc-v185), from Python and from the edge's loopback test.
- Reproduction: `python3 -c 'import socket; socket.socket(socket.AF_INET, socket.SOCK_STREAM, 132)'` fails with `OSError: [Errno 93] Protocol not supported`; `cargo test --manifest-path edge/Cargo.toml -- --nocapture` prints `SKIP: no SCTP`.
- Unblocks: a host with the `sctp` kernel module loaded (the capture host had it), where `e2e/run.sh` can run and the SCTP loopback test runs instead of skipping.
