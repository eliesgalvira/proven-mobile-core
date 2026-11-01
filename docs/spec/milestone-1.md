# Milestone 1: a UE registers and opens a PDU session through the kernel

A UERANSIM gNB and UE connect to our core: the kernel (Bend 2) behind the edge (Rust). eUPF v0.7.2 is the UPF. The UE registers with 5G-AKA, completes security mode, opens one IPv4 PDU session on DNN `internet`, and pings through eUPF. Every in-scope row of `docs/security/open5gs-advisories-2026.md` is a law that passes `bend kernel/PROOF.bend --verdict`.

Out of scope: see `AGENTS.md`. In particular: no N2 handover, no SBI, no 4G, no URR/charging, no IPv6, no Service Request, no network-initiated deregistration, no paging.

## Architecture

```
UERANSIM gNB --SCTP/NGAP--> edge (Rust) --TCP 127.0.0.1, frames--> kernel (Bend 2, one process)
                                   |                                 AMF + AUSF + UDM + SMF
eUPF  <-------- UDP 8805 / PFCP ---+
```

- **Kernel**: `kernel/`. A pure step function plus a thin IO wrapper (`kernel/main.bend`) that reads frames from the edge, calls `step`, and writes the returned actions. Only `main.bend` and anything it alone imports may perform IO. `kernel/PROOF.bend` must never import `main.bend`.
- **Edge**: `edge/`, a Rust crate producing one binary. It owns every socket, the clock and the randomness. It holds no 5G logic: it moves bytes between SCTP/UDP and the kernel, and runs timers. It is the thin layer in `GLOSSARY.md`.
- **UPF**: eUPF v0.7.2, started with `feature_ftup`, `feature_ueip` and `pfcp_remote_node` off. Our SMF allocates TEIDs and UE addresses and starts the PFCP association. See [the eUPF research](https://github.com/eliesgalvira/5G-spec-kernel/blob/research/eupf-pfcp/docs/research/eupf-pfcp.md).

## The step function

```
Kernel.step(state: State, event: Event, entropy: Bytes32) -> State & List<Action>
```

- Total, pure, no `@unsafe`. Every law about procedures is a law about `step`.
- `entropy` is 32 bytes of fresh OS randomness that the edge attaches to every event. The kernel never asks for randomness any other way. It uses entropy for RAND, 5G-TMSI and TEID/SEID choice.
- State is one record. Each UE context is owned by exactly one map entry, keyed by AMF-UE-NGAP-ID. Secondary indexes (RAN-UE-NGAP-ID per association, SUPI, 5G-TMSI, UE IPv4, SEID) map to that key. They never hold a copy of the context.

## The frame protocol (edge ⇄ kernel)

TCP on `127.0.0.1`. The kernel listens on the port given as its first argument; the edge connects. Every frame is `length: u32be` followed by `length` bytes of body. A body longer than 262144 bytes is a protocol error and closes the connection.

The edge sends one event at a time. The kernel answers each event with exactly one `Actions` frame, possibly empty, before the edge sends the next. All integers are big-endian.

| Body | Kind byte | Fields |
|---|---|---|
| Event | `0x01..0x0F` | kind, `entropy[32]`, then the payload |
| `Config` | `0x01` | `length: u32`, then the config TLVs below |
| `NgapAssocUp` | `0x02` | `assoc: u32` |
| `NgapAssocDown` | `0x03` | `assoc: u32` |
| `NgapData` | `0x04` | `assoc: u32`, `stream: u16`, `len: u32`, bytes |
| `PfcpData` | `0x05` | `len: u32`, bytes |
| `TimerFired` | `0x06` | `timer: u32` |
| `Actions` | `0x80` | `count: u16`, then `count` actions |
| `NgapSend` | `0x81` | `assoc: u32`, `stream: u16`, `len: u32`, bytes |
| `NgapClose` | `0x82` | `assoc: u32` |
| `PfcpSend` | `0x83` | `len: u32`, bytes |
| `TimerStart` | `0x84` | `timer: u32`, `ms: u32` |
| `TimerCancel` | `0x85` | `timer: u32` |
| `Log` | `0x86` | `level: u8` (0 debug, 1 info, 2 warn, 3 error), `len: u32`, UTF-8 bytes |

Config TLVs are `tag: u16`, `len: u16`, value. Unknown tags are skipped; a repeated tag replaces the earlier one.

- **Network identity:** `0x0001` PLMN (3 bytes, TS 24.501 encoding). `0x0002` AMF Region ID (1). `0x0003` AMF Set ID (2, 10 bits). `0x0004` AMF Pointer (1, 6 bits). `0x0005` TAC (3). `0x0006` AMF name (UTF-8).
- **Slice and data network:** `0x0007` S-NSSAI SST (1). `0x0008` DNN (UTF-8). `0x0009` UE IPv4 pool base (4). `0x000A` pool prefix length (1). `0x000B` DNS IPv4 (4).
- **N4 (SMF ⇄ eUPF):** `0x000C` SMF N4 IPv4 (4). `0x000D` UPF N3 IPv4 (4). `0x000E` UPF N4 IPv4 (4).
- **SUCI:** `0x000F` home-network private key for SUCI Profile A (32). `0x0010` its key identifier (1).
- **Algorithms:** `0x0011` NAS ciphering preference (list of NEA ids, 1 byte each). `0x0012` NAS integrity preference (list of NIA ids).
- **Subscribers:** `0x0020` subscriber, repeatable. Its value is SUPI digits (`len: u8`, ASCII digits), K (16), OPc (16), AMF field (2), SQN (6).

The edge reads a TOML file (`edge/config.example.toml`) and sends `Config` as its first event. Config is trusted operator input, but the kernel still decodes it with a proven codec.

## Data representation in Bend

- **Bytes:** `List<&2, U32>`, each element in `0..255`. Codecs take bytes and return `Result` values. Nothing indexes past the end of a list, because nothing indexes.
- **Integers:** values up to 32 bits are `U32`. AMF-UE-NGAP-ID (up to 2⁴⁰−1), BitRate (up to 4·10¹²), SEID (64 bits), SQN (48 bits) and NAS COUNT overflow are held as fixed-width byte lists or as a pair of `U32`, never as one `Nat`. The kernel never builds a `Nat` of 2⁴⁸ or more from attacker input, because Bend's runtime stops on such values.
- **Validity:** each codec's datatype comes with a `valid` predicate (`-> Bool`) for constraints the type can't express. Every decoder returns only valid values, and every round-trip law assumes `valid`.

## Law conventions

- `kernel/LAWS.bend` states every law; `kernel/PROOF.bend` proves each with a def of the same name.
- **The spec is normative.** A law in `LAWS.bend` may be stronger than its ticket says, never weaker. If a law in a ticket looks false, don't weaken it: write a blocker (see `AGENTS.md`).
- **Names.** Law names are `<area>.<property>`. The advisory log (`docs/security/open5gs-advisories-2026.md`) names, for each in-scope row, the law that rules it out.
- **Standard shapes.** Every codec has at least these laws:
  - `X.roundtrip`: `valid(v) → decode(encode(v) ++ rest) = Done{(v, rest)}`.
  - `X.decode_valid`: `decode(bs) = Done{(v, rest)} → valid(v)`.
  - `X.suffix`: on success, `rest` is a suffix of `bs`, and the consumed prefix is exactly the length the wire format declares.
- **Totality is structural.** A def without `@unsafe` terminates and handles every case, so "never crashes on any input" holds for every pure def that `--verdict` accepts. `scripts/check.sh` fails if any file under `kernel/` other than `main.bend` contains `@unsafe` or a foreign import.

## Test vectors

`test-vectors/` holds:

- **`capture/`:** a real UERANSIM registration and PDU session against Open5GS with eUPF. It has the bytes of every NGAP, NAS and PFCP message, plus the K, OPc, SUCI keys, RAND, AUTN and RES* that produced them. The setup that reproduced it is next to it.
- **`spec/`:** official vectors (FIPS 180-4, FIPS 197, RFC 4231, RFC 4493, RFC 7748, TS 35.208, TS 33.501 Annex C, TS 33.401 Annex C), each file citing its source and section.

`scripts/gen-vectors.py` turns the JSON vectors into Bend data under `kernel/tests/vectors/`. Expected values in tests come only from these files, never from our own code.

Both directories may still be arriving on `main` while the loop runs. A test whose vectors are missing prints `SKIP <reason>` instead of `PASS`. The ticket may be marked `done` with a note saying which tests were skipped. Ticket 23 fails while any test is skipped.

## Verification

`scripts/check.sh` is the gate. It runs, in order:
1. the `@unsafe` and foreign-import scan;
2. `bend kernel/PROOF.bend`;
3. `bend kernel/PROOF.bend --verdict`;
4. every `kernel/tests/*.bend`, each of which must print a line starting `PASS`;
5. `cargo test` in `edge/`, once it exists;
6. `scripts/acceptance.py`, which checks that every law named in the advisory log exists in `LAWS.bend` and isn't open.

A ticket is done only when `scripts/check.sh` passes and the ticket's own verification command does.
