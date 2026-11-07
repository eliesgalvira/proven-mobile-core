# 31 Edge: SCTP covered where it runs

Depends on: 21, 30. Estimate: 0.5 h.

## Goal

The edge's SCTP loopback test passes as a skip on hosts without the `sctp` module, so the swapped SCTP constants went unseen until the end-to-end test. With the second gNB from ticket 30, stream ids matter, because UERANSIM sets `ignoreStreamIds`.

1. Add a check to the flake that runs the edge's tests inside a NixOS VM with `sctp` loaded, where a skip is a failure.
2. Make one e2e gNB run with `ignoreStreamIds: false`.

## Verify

`nix flake check`
