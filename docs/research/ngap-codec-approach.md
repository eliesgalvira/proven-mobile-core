# NGAP codec: generate from the 3GPP ASN.1, or hand-write each message?

Research for [#4](https://github.com/eliesgalvira/proven-mobile-core/issues/4), 2026-11-01. Sources are pinned to the versions read. Statements marked *(inferred)* are my conclusions, not something a source says.

## What NGAP asks of the codec

**Transfer syntax.** NGAP uses BASIC-PER, ALIGNED variant ([TS 38.413 v19.2.0][ts] §9.5). The X.691 rules that do the work ([X.691 (02/2021)][x691]):

- **Constrained whole numbers** (§11.5.7). A range of up to 255 values is a bit-field of 1 to 8 bits with no alignment. A range of 256 is one aligned octet, and a range from 257 to 64K is two aligned octets. Larger ranges become a length followed by the minimum number of aligned octets.
- **Length determinants** (§11.9.3). Lengths with an upper bound below 64K are constrained whole numbers. Otherwise a length up to 127 takes one octet, up to 16K takes two octets, and from 16K up the value is split into fragments.
- **Open types** (§11.2). The inner value is encoded as a complete encoding and placed in an octet string with an unconstrained length.
- **SEQUENCE** (§19.1–19.9). An extension bit, then a bitmap of the OPTIONAL fields present. When extensions are present, a normally-small count, a presence bitmap and each extension addition wrapped as an open type.
- **Extensible INTEGER** (§13.1). One bit, and a value outside the root is encoded as an unconstrained integer.
- **CHOICE** (§23). The root index is a constrained number. An extension alternative is a normally-small index plus an open type.
- **Padding** (§11.1.4). Alignment padding consists of zero bits.

**Error handling** ([TS 38.413][ts] §10.3). The rules cover IEs that are not comprehended, missing, out of order or repeated:

- An IE the receiver does not support "shall be considered not comprehended … and action based on criticality shall be applied" (§10.3.2). Reject, ignore-and-notify and ignore each have their own required action (§10.3.4–10.3.5).
- The receiver "shall read the remaining message" after such an error (§10.3.1).
- IEs that arrive in the wrong order or too many times reject the procedure (§10.3.1 case 4, §10.3.6).

So the spec lets an AMF understand only a subset of IEs, as long as it decodes the framing of every IE and applies criticality to the rest.

**Which ASN.1 NGAP actually uses.** Measured on the Release 19 module (`38413-j20.asn`, 14,738 lines, 2,013 type and object-set assignments) that [Open5GS feeds to asn1c][o5-asn]:

- **Message layer.** Every message is `SEQUENCE { protocolIEs ProtocolIE-Container {{XIEs}}, ... }`. A container is `SEQUENCE (SIZE(0..65535)) OF ProtocolIE-Field`, and each field is `{id, criticality, value}` with the value an **open type** selected by `id` from an information-object set. Each row of that set gives the IE's `ID`, `CRITICALITY`, `TYPE` and `PRESENCE`. The top-level `NGAP-PDU` is a CHOICE whose `value` is again an open type, selected by procedure code ([ASN.1 L295–306][asn-pdu]).
- **Growth mechanism.** I found no `[[ ]]` extension groups and no SEQUENCE or CHOICE component after a `...`. New fields arrive as protocol IEs, as `iE-Extensions` (`ProtocolExtensionContainer`, also open types) or as `choice-Extensions` (73 uses). The only types with values after the marker are 10 ENUMERATEDs such as the cause enums. There are 86 extensible INTEGER or SIZE constraints.
- **Nested encodings.** There are 60 `OCTET STRING (CONTAINING …)`, used for example for the PDU session transfers ([L11095–11160][asn-sures]); each holds a complete APER encoding of its own.
- **Absent constructs.** No REAL, SET or SET OF. `OBJECT IDENTIFIER` appears only in private IEs. `DEFAULT` appears only inside a class definition, never in a message.
- **Values that do not fit in U32.** `AMF-UE-NGAP-ID ::= INTEGER (0..1099511627775)`, which is 2⁴⁰−1 ([L5820][asn-amfid]). `BitRate ::= INTEGER (0..4000000000000, ...)` ([L6066][asn-bitrate]). `RAN-UE-NGAP-ID` fits in U32 ([L11854][asn-ranid]). Some bit strings are long: `NRCellIdentity` has 36 bits and `SecurityKey` 256.

**The messages the milestone needs.** The UERANSIM gNB dispatches these NGAP messages ([`transport.cpp` L290–356][ue-dispatch]); UERANSIM's own codec is asn1c-0.9.29 output. The AMF needs NGSetupRequest, NGSetupResponse and NGSetupFailure; InitialUEMessage; DownlinkNASTransport and UplinkNASTransport; InitialContextSetupRequest and InitialContextSetupResponse; PDUSessionResourceSetupRequest and PDUSessionResourceSetupResponse with their two transfers; and ErrorIndication.

I computed the type closure over the value types of the IEs those messages carry, without extension containers, using a throwaway script over the `.asn` file. It comes to **about 134 type assignments and 750 lines of ASN.1**: 42 SEQUENCE, 28 ENUMERATED, 18 INTEGER, 15 SEQUENCE OF, 11 OCTET STRING, 11 BIT STRING, 4 CHOICE and 2 PrintableString. Following every IE of those 13 messages with extension containers gives 834 assignments. That figure is what full coverage would cost, and the milestone does not need it.

## How the existing codecs are built

### asn1c (Open5GS; UERANSIM uses it too)

- **Generator and runtime.** Open5GS regenerates NGAP with [mouse07410/asn1c][ac] `vlm_master`. Before running it, Open5GS hand-edits the 3GPP text into a `.asn` file. The command is `asn1c -pdu=all -fprefix=NGAP_ -fcompound-names -findirect-choice -no-gen-{BER,XER,JER,CBOR,OER,UPER}`, and the allocator macros in the runtime are hand-patched ([README][o5-readme]).
- **Measured size** at [b60aad4][o5]. `lib/asn1c/ngap` has 2,614 files and 477,766 lines of generated C. The shared runtime in `lib/asn1c/common` has 16,121 lines. The AMF's hand-written NGAP handling (`src/amf/ngap-*.c`) has 10,411 lines.
- **How it is built.** It is table-driven. The generated code is mostly descriptor tables (`asn_TYPE_descriptor_t`, member tables, information-object rows that include `&presence`), and generic skeletons interpret them. The APER skeletons in asn1c come to 6,254 lines (`*_aper.c`, `aper_*.c`, `per_*.c`), and `OPEN_TYPE_aper.c` alone is 989 lines.
- **What the runtime leaves to the application.** The `&presence` column is generated, but I found no runtime use of it. Presence and criticality are therefore left to the application *(inferred from a grep of the skeletons)*. Open5GS's handlers walk `protocolIEs` and null-check by hand, for example in `ngap_handle_initial_ue_message`. That is the code behind acceptance-list row [GHSA-cfp8-93x2-6h9x][ghsa-cfp8], where a missing mandatory IE leaves a context behind.
- **Open types are still being fixed.** As recently as 2026-10-22, asn1c [issue #586][ac-586] reported that an open type with an unknown id decoded but was then dropped, so the message could not be re-encoded.

### free5GC `aper` + `ngap` (Ella Core v1.11.1)

- **No own PER library at v1.11.1.** Ella Core v1.11.1 does not have its own PER library or `pergen`. Its `go.mod` pins `free5gc/aper v1.1.1` and `free5gc/ngap v1.1.3` ([go.mod L8–10][el-gomod]).
- **Where `per/` and `pergen` appear.** Those paths appear in later tags; I checked file paths only at v1.20.0. From v1.12.0 on, the repository is under the Business Source License, so I did not read them.
- **free5GC `aper` v1.1.1.** It has 2,026 lines of Go. It interprets Go struct tags such as `aper:"valueExt,referenceFieldValue:85"` through reflection at run time ([`aper.go`][ap]).
- **free5GC `ngap` v1.1.3.** It has 13,946 non-test lines and 598 files in `ngapType`, with tags in the structs ([e.g. `InitialUEMessageIEsValue`][ng-ies]). I found no generator in the repository.
- **Code paths in `aper` v1.1.1 worth noting.**
  - A failed SEQUENCE OF count is logged as a warning, and decoding continues with the lower bound ([L603][ap-603]).
  - A CHOICE extension alternative is "unsupported" ([L639][ap-639]).
  - In the SEQUENCE branch, I found no code that reads extension additions when the extension bit is 1 ([L719–747][ap-ext], [L794–902][ap-seq]). A crafted extension bit would therefore desynchronise the cursor *(inferred)*.
- **Ella's validation layer.** On top of this, Ella hand-wrote [`internal/amf/ngap/decode`][el-decode]: 3,632 lines and 5,509 lines of tests. It converts `ngapType` structs into Go records with the mandatory IEs present, and builds a `Report` that maps onto CriticalityDiagnostics (§10.3). It documents a "last wins" policy for duplicate IEs, which goes against §10.3.6 ([decode.go L14–19][el-decode]).
- **Other Ella NGAP code.** Dispatch and handlers are 3,316 lines and `send` is 2,647.

### VUPER ([arXiv 2608.09094][vuper], CCS '26)

- **What it is.** Rocq combinators for **UPER** with proofs, plus a compiler from ASN.1 to Rocq types and formats. The verified parser is extracted to OCaml and used as a test oracle; I found no mention of APER.
- **Size.** About 12k lines of Rocq and a 1.8k-line OCaml compiler, estimated at 4–5 person-months. The bijection proof for INTEGER alone is about 800 lines, because Rocq numbers are not machine words (§4.2).
- **Proven properties.**
  - Surjection: what the encoder writes, the decoder reads back as the same value.
  - Strong injection: re-encoding a successful decode gives the same bits. VUPER adds encode and decode invariance, because without them strong injection does not imply non-malleability.
  - Local write.
  - Length consistency.
  - Weak injection: a value decoded with unknown extensions can still be re-encoded, without matching the input bits.
  - Termination comes from structural recursion. Memory safety is left to OCaml.
- **Supported subset.** SEQUENCE, CHOICE and SEQUENCE OF with extensions, and open types limited to 16K bytes. It omits SET OF, fragmentation and **information object CLASSes**, the last because its RRC and V2X targets do not use them (§6). NGAP's whole message layer is built from them.
- **Lesson.** In 5G and V2X parsers, its oracle found 20 kinds of disagreement: lax constraint checks, value corruption and departures from UPER. It also showed attacks built on them.

### Other generators and cores

- **ASN1SCC with a Scala/Stainless backend** ([arXiv 2412.07235][asn1scc-paper]). It proves absence of runtime errors and decode-after-encode for the base library and for records, discharging more than 300k verification conditions by SMT. Sums and arrays are only partly done. The bitstream is about 3,700 lines and the codec about 4,000. ASN1SCC supports uPER, ACN, XER and BER but **not APER** ([README][asn1scc]).
- **Functional-language generators without proofs.** Erlang/OTP's `asn1ct` compiles to `per` (aligned), `uper`, `ber` and `jer` ([docs][erlang-asn1]). I found no generator that emits APER for a proof language.
- **No hand-written per-message codecs.** None of the cores I read writes the APER layer by hand per message. Open5GS and UERANSIM use asn1c, and free5GC and Ella v1.11.1 use reflection over tagged structs. The hand-written part is always the IE-presence and criticality layer above the codec (Open5GS handlers, Ella `decode`).

## What each approach costs in Bend 2

The Bend 2 facts that matter, as of [faeb02e][bend]:

- **Bytes.** Bytes are `List<&2, U32>`, which is what `TCP.recv_bytes` returns ([base.bend L460][bend-tcp]).
- **U32.** In the theory, `U32` is `Word(32n)`, a list of 32 `Bool`s ([L51–68][bend-word]), so bit operations compute in proofs. Base has only five `U32` laws, so the shift, mask and conversion lemmas a codec needs must be written *(inferred)*.
- **Numbers.** There is no U64; it is planned ([WONTFIX "SOON" #1027][bend-wontfix]). A `Nat` above 2⁴⁸−1 **fail-stops at run time**, but the theory has no such bound ([WONTFIX #779][bend-wontfix]).
- **Affinity and templates.** Closures and arrays are affine. A `~` template inlines a closed argument at compile time and may call it many times ([guide L257–277][bend-guide]).
- **Proof support.** There are no tactics, recursion must terminate, and the checker can be exponential on some terms ([WONTFIX #993, #1075][bend-wontfix]).
- **Build model.** Each program is one C file. A native library target for pure defs is planned but not scheduled ([#813][bend-wontfix]).

| Approach | How it maps to Bend | Proof cost | Main risk |
|---|---|---|---|
| **A. Hand-written per message** (bit operations inline in each message's decoder) | Direct, first-order | Every message re-proves alignment, lengths, open-type framing and constraints, by hand and without tactics | The ad-hoc duplication that produced the advisories. Nothing is checked against the ASN.1 |
| **B. One generic interpreter over type descriptions** (the asn1c and free5GC model, done with dependent types: `decode(d) : Bits → Result<Val(d)>`) | Natural in a dependent language: prove round-trip once for every `d` | Smallest proof base | `Val(d)` for about 130 nested descriptions is evaluated by the checker, which risks the blow-ups in #993 and #1075. Procedure code gets computed types rather than named records. Reuse needs higher-order code, and closures are affine *(inferred)* |
| **C. Generator from the 3GPP ASN.1 emitting first-order Bend**: one datatype, `decode`, `encode`, `valid` and proof term per ASN.1 type, built on a hand-proven APER primitive library (VUPER's split, adapted) | Plain defs and named records; no closures needed | Primitives are proven once by hand. Per-type proofs are glue the generator emits by composing primitive lemmas, so the lack of tactics matters less | The generator is not trusted for safety but is trusted for spec conformance. The volume of generated code makes checker time a risk |

The free5GC and asn1c runtimes interpret their descriptors at run time; that part cannot be proven in their languages, and in B it would sit inside the proof *(inferred)*. VUPER's proofs cannot be reused directly: they are UPER and Rocq, and APER changes the cases of every primitive (§11.5.7, §11.9.3, §11.1.4) *(inferred)*.

## Recommendation

**Approach: C, a codec generated from the 3GPP NGAP ASN.1 for a declared subset, on a hand-proven APER primitive library.** "Hand-written per message" should be rejected. "Generated" should cover only the IEs the milestone uses, and every other IE is decoded to its open-type bytes and handled by criticality, as §10.3.2 allows.

**Shape:**

1. **APER primitives**, hand-written and hand-proven in Bend.
   - A bit cursor over the received `List<U32>`, with alignment.
   - Constrained, normally-small, semi-constrained and unconstrained whole numbers.
   - Length determinants.
   - Open types and `CONTAINING` octet strings.
   - Lengths of 16K or more, which need fragmentation, are rejected and the rejection is stated as a law. VUPER makes the same cut, and the subset does not need longer lengths.
2. **Generator.** It lives outside the kernel and its language is open. It reads `38413-*.asn` at a pinned release and a list of IEs to understand, and emits:
   - Bend datatypes. Integers too large for U32 become `Nat`.
   - First-order `decode`, `encode` and `valid` per type, plus proof terms.
   - A **message view** per message, generated from the object set's `ID`, `CRITICALITY` and `PRESENCE`. It returns a record in which mandatory IEs are not `Maybe`, or a §10.3 report.

   `bend --verdict` checks the output, so a generator bug can produce wrong NGAP but not an unproven kernel.
3. **Unknown content is kept as raw bytes.** This covers IE ids outside the subset, unknown extension additions, CHOICE extensions and ENUMERATED or INTEGER values outside their roots. Keeping the bytes avoids the bug in asn1c #586 and makes exact re-encoding possible *(inferred)*.

**Rough size** *(inferred)*:

| Part | Estimate |
|---|---|
| Primitives | About 1k lines of code and 4–8k lines of proof (VUPER needed about 12k with tactics) |
| Generated code for about 134 types | 7–10k lines |
| 15 message views | About 2k lines |
| Generator | 2–3k lines; it must handle parameterised types and object sets, which VUPER skipped |
| **Total** | About 15–20k lines of Bend, most of it generated |

For comparison, asn1c's full Rel-19 NGAP output is about 478k lines of C. Ella's hand-written validation layer alone is 3.6k lines of Go.

**How the proofs are stated.** Each is a law, written informally here; `bs` is input bytes, `v` a value.

- **Total decode.** `decode` terminates on every input (Bend's check, with no `@unsafe` and no `def f?`) and returns `Ok` or `Err`. With list input there is no index to go out of bounds. The bound becomes the law "on `Ok(v, rest)`, `rest` is a suffix of `bs`".
- **Open-type framing.** An inner decoder sees exactly the `n` octets its length gives. Leftover octets inside the frame other than zero padding are an error, and so is non-zero alignment padding (§11.1.4). The stricter padding rule costs interoperability with sloppy encoders; it should be checked against UERANSIM traffic.
- **Round-trip.** `valid(v) → decode(encode(v)) = Ok(v, [])`. `encode` is total on valid values.
- **Canonical decoding.** `decode(bs) = Ok(v, []) → encode(v) = bs`. This holds even with unknown content, because raw bytes are kept. It requires rejecting non-minimal lengths and integers. It replaces VUPER's injection plus invariance pair: list-valued encoders do not depend on buffer or position *(inferred)*.
- **Constraints.**
  - `decode(bs) = Ok(v, _) → valid(v)`. `valid` covers ranges, SIZE bounds (so element counts are bounded by type, as in the acceptance list) and the PrintableString alphabet.
  - Every decoded `Nat` is below 2⁴⁸. This closes the gap between the run-time cap and the proof.
  - An out-of-root extensible INTEGER such as `BitRate` stays as bytes and is never built into a `Nat`.
- **Extension markers.** An unknown extension yields an explicit `Unknown` or `Extended` constructor, never a misread of the following fields (the free5GC desync above).
- **Protocol IE containers.**
  - The view returns `Ok(record)` only if every mandatory IE appears exactly once and every IE with criticality `reject` is comprehended.
  - Otherwise the report lists each IE's id, criticality and error type (§10.3.1 cases 1–6).
  - Encoding a record emits every mandatory IE, in object-set order.

  This is the codec half of [GHSA-cfp8-93x2-6h9x][ghsa-cfp8].

Proofs show the codec agrees with itself, not with X.691. Agreement with the spec needs differential testing against asn1c (UERANSIM) and pycrate on recorded UERANSIM traffic plus fuzzing, which is how VUPER caught non-conformance.

**Bend gaps** (candidate `upstream:bend` tickets, each only once a spike gives a minimal `.bend` reproducer):

1. **Laws over template combinators.** If the generated code needs shared helpers (for example one element codec reused across a SEQUENCE OF), the open question is whether laws can be stated and proven about `~` templates, given that closures are affine. The design above avoids this by emitting first-order code, but the first spike should confirm that.
2. **Base laws for `U32` and `Word`.** These are shift, mask, `U32.to_nat` and `from_nat` round-trip, and `Nat` div/mod by 2ᵏ. Base has five `U32` laws. Without a ticket we write them ourselves.
3. **Checker time at scale.** About 10k generated lines plus proofs checked in one program. File a ticket only with a concrete slow term, because WONTFIX #993 and #1075 already rule out generic reports.

Not tickets, because Bend's WONTFIX already lists them: U64 (#1027), the 2⁴⁸ `Nat` cap (#779) and the native library target (#813). The codec works around the first two, and the Rust thin layer depends on the third.

**First step.** Spike the primitives for constrained whole numbers, length determinants and open types with their laws. Then take InitialUEMessage end to end and time `bend --verdict`. The spike decides the code shape for gap 1 and gives the checker-time evidence for gap 3.

[ts]: https://www.etsi.org/deliver/etsi_ts/138400_138499/138413/19.02.00_60/ts_138413v190200p.pdf
[x691]: https://www.itu.int/rec/T-REC-X.691-202102-I
[o5]: https://github.com/open5gs/open5gs/tree/b60aad44e71b3f62c93440992a8b18cb67953c87
[o5-asn]: https://github.com/open5gs/open5gs/blob/b60aad44e71b3f62c93440992a8b18cb67953c87/lib/asn1c/support/ngap-r19.2.0/38413-j20.asn
[o5-readme]: https://github.com/open5gs/open5gs/blob/b60aad44e71b3f62c93440992a8b18cb67953c87/lib/asn1c/support/README.md
[asn-pdu]: https://github.com/open5gs/open5gs/blob/b60aad44e71b3f62c93440992a8b18cb67953c87/lib/asn1c/support/ngap-r19.2.0/38413-j20.asn#L295-L306
[asn-sures]: https://github.com/open5gs/open5gs/blob/b60aad44e71b3f62c93440992a8b18cb67953c87/lib/asn1c/support/ngap-r19.2.0/38413-j20.asn#L11095-L11160
[asn-amfid]: https://github.com/open5gs/open5gs/blob/b60aad44e71b3f62c93440992a8b18cb67953c87/lib/asn1c/support/ngap-r19.2.0/38413-j20.asn#L5820
[asn-bitrate]: https://github.com/open5gs/open5gs/blob/b60aad44e71b3f62c93440992a8b18cb67953c87/lib/asn1c/support/ngap-r19.2.0/38413-j20.asn#L6066
[asn-ranid]: https://github.com/open5gs/open5gs/blob/b60aad44e71b3f62c93440992a8b18cb67953c87/lib/asn1c/support/ngap-r19.2.0/38413-j20.asn#L11854
[ue-dispatch]: https://github.com/aligungr/UERANSIM/blob/4f45e18f80b0684f7d6e29f1fea0f579e9243d68/src/gnb/ngap/transport.cpp#L290-L356
[ac]: https://github.com/mouse07410/asn1c/tree/1d15bc426a0561e80b2cbba5d7c1984fadd0698b/skeletons
[ac-586]: https://github.com/mouse07410/asn1c/issues/586
[ghsa-cfp8]: https://github.com/open5gs/open5gs/security/advisories/GHSA-cfp8-93x2-6h9x
[el-gomod]: https://github.com/ellanetworks/core/blob/v1.11.1/go.mod#L8-L10
[el-decode]: https://github.com/ellanetworks/core/blob/v1.11.1/internal/amf/ngap/decode/decode.go#L1-L20
[ap]: https://github.com/free5gc/aper/blob/v1.1.1/aper.go
[ap-603]: https://github.com/free5gc/aper/blob/v1.1.1/aper.go#L603
[ap-639]: https://github.com/free5gc/aper/blob/v1.1.1/aper.go#L639
[ap-ext]: https://github.com/free5gc/aper/blob/v1.1.1/aper.go#L719-L747
[ap-seq]: https://github.com/free5gc/aper/blob/v1.1.1/aper.go#L794-L902
[ng-ies]: https://github.com/free5gc/ngap/blob/v1.1.3/ngapType/ProtocolIEField.go#L1282-L1293
[vuper]: https://arxiv.org/abs/2608.09094
[asn1scc-paper]: https://arxiv.org/abs/2412.07235
[asn1scc]: https://github.com/esa/asn1scc
[erlang-asn1]: https://www.erlang.org/doc/apps/asn1/asn1ct.html
[bend]: https://github.com/bendlang/bend/tree/faeb02eaa164d532f4cf13f1a455cbebda56ac40
[bend-tcp]: https://github.com/bendlang/bend/blob/faeb02eaa164d532f4cf13f1a455cbebda56ac40/bend2/base.bend#L460
[bend-word]: https://github.com/bendlang/bend/blob/faeb02eaa164d532f4cf13f1a455cbebda56ac40/bend2/base.bend#L51-L68
[bend-guide]: https://github.com/bendlang/bend/blob/faeb02eaa164d532f4cf13f1a455cbebda56ac40/guide/GUIDE.md#L257-L277
[bend-wontfix]: https://github.com/bendlang/bend/blob/faeb02eaa164d532f4cf13f1a455cbebda56ac40/WONTFIX.txt
