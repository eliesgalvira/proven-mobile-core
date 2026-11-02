# Blockers

One entry per blocker: ticket, what was tried, smallest reproduction, what would unblock it.

## Ticket 22: the cloud VM has no SCTP

- Ticket: 22 (found while testing ticket 21's edge).
- Tried: `e2e/run.sh` on the session VM (Linux 6.18.44-fc-v185). Its first step checks the host: the Docker daemon was not running (a `dockerd --bridge=none --iptables=false` started by hand came up), and `/proc/net/protocols` lists no SCTP; there is no `modprobe` in the VM. The edge's loopback test also prints `SKIP: no SCTP`, since `socket(AF_INET, SOCK_STREAM, IPPROTO_SCTP)` fails with `EPROTONOSUPPORT`.
- Failing step: `E2E FAIL: prerequisites` ("No SCTP in the host kernel (modprobe sctp)").
- Unblocks: run `e2e/run.sh` on a host with Docker, Nix and the `sctp` module loaded (the capture host had all three). It prints `E2E PASS` or the failing step and leaves the logs under `$OUT/logs`.
