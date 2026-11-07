# 20 Kernel process

Depends on: 15, 19.

## Goal

`kernel/main.bend`, the only IO module:
1. `TCP.listen("127.0.0.1", port)`, with the port taken from the first argument. Accept one connection.
2. Loop: read one frame (accumulating `recv_bytes` until the length is satisfied), decode the event, call `Kernel.step`, encode and send the `Actions` frame.
3. Write each Log action to stderr as well.

The loop may be `@unsafe`; this is the one place allowed. `PROOF.bend` must not import this file.

Build with `bend kernel/main.bend -o build/kernel`.

## Tests

`scripts/frame-client.py`: start `build/kernel 7000`, connect, send `Config`, `NgapAssocUp` and the captured NG Setup Request, and check the reply contains one `NgapSend` holding NG Setup Response. Keep timeouts short and always kill the process.

## Done when

The test above passes; `scripts/check.nu` passes and its `@unsafe` scan still finds nothing outside `main.bend`.

## Verify

`bend kernel/main.bend -o build/kernel && python3 -I scripts/frame-client.py && scripts/check.nu`
