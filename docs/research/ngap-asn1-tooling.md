# NGAP ASN.1 front end for the Bend 2 codec generator

Research for wayfinder ticket #8, done 2026-11-01; it follows `docs/research/ngap-codec-approach.md`. The ASN.1, `extract.py` and `ngap_model.py` it mentions are in `tools/ngap-gen/`; `closure.txt` and `ies.txt` are regenerated with `ngap_model.py tools/ngap-gen/asn closure` and `... ies <MESSAGE>`.

## Recommendation

1. **Parser: pycrate 0.8.1, through its `pycrate_asn1c.asnproc` compiler.** It was the only tool I tried that took the 3GPP text unedited and returned a resolved model. In that model each IE container is already tied to its object set, every row carries id, criticality, presence and the value type as an object, and constraints arrive as numbers. The same package has an APER runtime that decodes IE values through those object sets, so it can also serve as the differential oracle the codec research asks for.
2. **Generator language: Python 3.** The generator imports pycrate in the same process. Every access to pycrate's model goes through one small adapter module. `ngap_model.py` already does this in 271 lines, including its command-line code. Pin `pycrate==0.8.1` exactly, because the generator uses attributes that start with an underscore.
3. **Release: TS 38.413 V17.15.0 (`38413-hf0.zip`, 2026-03-20), the latest Release 17.** UERANSIM is built from V17.9.0. For all 15 messages and 2 transfers, V17.15.0 has exactly the same IE rows as V17.9.0. srsRAN Project also uses Release 17. Release 19 still gets changes that break wire compatibility. Moving to a later release costs little, because tier M, defined in question 3, is the same 120 types from 17.9.0 to 19.4.0.

**Trade-offs I'm taking:**

- **pycrate has no stable public API.** The model lives in attributes such as `_cont`, `_const`, `_typeref`, `_ext`, `_root` and `_flag`, so an upgrade can break the adapter. The exact pin and a golden-output test on the generated Bend contain that risk.
- **One maintainer.** pycrate has one maintainer and 184 open issues. The original P1sec repository is archived and work moved to `pycrate-org/pycrate`, whose last push was 2026-10-10.
- **No static types.** Python gives the generator no type checking. That matters less because the generator is untrusted: `bend --verdict` checks its output either way.
- **The typed alternative.** rasn-compiler in Rust has a typed IR and a backend trait made for custom generators. It was the runner-up, and it would be my choice if the generator were trusted. Here it costs more work: the backend has to resolve object sets, IE ids and type names itself, and nothing from that crate can act as the oracle.
- **Newer IEs from later gNBs.** With Release 17 pinned, a Release 18 or 19 gNB that sends a new optional IE with criticality `reject`, such as `MobileIABNodeIndication`, `AIoT-Support` or `GW-Context-Release-Indication`, gets the procedure rejected. TS 38.413 §10.3 requires exactly that from an AMF that lacks those features. Newer ENUMERATED values, such as later Cause values, decode as unknown extension values.
- **Licence.** pycrate is LGPL-2.1-or-later. That is fine for a build tool we install from PyPI and never vendor. The generator can stay 0BSD, and the generated Bend comes from the 3GPP ASN.1, not from pycrate.

## 1. Which parser can handle NGAP's ASN.1

### What NGAP needs from a parser

NGAP's message layer is made of the constructs that ASN.1 front ends handle worst:

- **Parameterised containers.** Every message is `ProtocolIE-Container {{XIEs}}`.
- **Information object classes and sets.** The containers use the classes `NGAP-PROTOCOL-IES` and `NGAP-PROTOCOL-EXTENSION`, the PDU uses `NGAP-ELEMENTARY-PROCEDURE`, and the object sets use the class's own syntax, as in `{ ID … CRITICALITY … TYPE … PRESENCE … }`.
- **Open types tied to those sets** by a table constraint, `{IEsSetParam}{@id}`.
- **Constrained types written inside objects**, as in `TYPE OCTET STRING (CONTAINING X)`.
- **Constants in constraints**, as in `SIZE(1..maxnoofSliceItems)`.
- **Extension markers** on SEQUENCE, ENUMERATED, INTEGER and SIZE.

### Results

| Tool | Version, licence | Ran on the real NGAP | Model a generator can use | APER with open types resolved | Verdict |
|---|---|---|---|---|---|
| **pycrate** (`pycrate_asn1c.asnproc`), Python | 0.8.1 (PyPI, 2026-05-11), LGPL-2.1+ | All 6 modules of 17.9.0, 17.15.0, 18.11.0 and 19.4.0 compile unedited in 0.4–0.6 s, with no warnings | Yes. It instantiates the parameterised containers, attaches the object set to the open type, resolves constants and keeps the extension markers | Yes. A round trip works, and Wireshark agrees with its bytes | **Use** |
| **rasn-compiler**, Rust | 0.16.0 (crates.io, 2025-12-31), MIT/Apache-2.0 | Parses and links all 6 modules of 17.15.0 and 19.4.0 in about 2 s with 0 warnings | Partly. The IR keeps object-set rows, CONTAINING and extensibility, but ids, sets and types stay as names to resolve | No. The stock backend gives every IE value the type `Any` | Runner-up |
| **asn1tools**, Python | 0.169.0 (PyPI, 2026-09-01), MIT | Fails to parse on the first `TYPE OCTET STRING (CONTAINING …)` inside an object | After hand edits it parses, but every object set is empty | No. `compile_files(…, 'per')` crashes | Reject |

I did not run the following, for these reasons:

- **asn1c** ([mouse07410](https://github.com/mouse07410/asn1c), BSD-2-Clause). Open5GS and UERANSIM generate their C codecs with it. It has no IR API, so a Bend backend would be C code inside its tree. It remains the obvious partner for differential tests, since UERANSIM *is* asn1c output.
- **Wireshark `asn2wrs.py`** (GPL-2.0+). It is built to generate dissectors and needs hand-written `.cnf` files for the object sets. Its dissector worked well here as an independent APER decoder, and I used it that way.
- **Erlang `asn1ct`.** It supports X.681–683 fully, but Erlang is not installed in the cloud image, and the parsed form is internal to the compiler.
- **ASN1SCC.** It has no support for information object classes, as the ticket #4 research found.
- **OSS ASN.1, Objective Systems ASN1C and ffasn1c.** They are commercial.
- **Go and Node.** I know of no maintained ASN.1 compiler for either that handles information object classes. free5GC's `ngap` has no generator. I did not search those ecosystems exhaustively.

### pycrate: what was run and what it shows

Setup and the commands, all run with `-I`:

```
uv venv --python 3.12 venv
uv pip install --python venv/bin/python pycrate==0.8.1 asn1tools==0.169.0     # pyparsing 3.3.3 pulled in
venv/bin/python -I out/ngap_model.py out/asn ies InitialUEMessage PDUSessionResourceSetupRequest PDUSessionResourceSetupRequestTransfer
venv/bin/python -I out/ngap_model.py out/asn closure
```

`out/ngap_model.py` is the whole adapter. It uses `compile_text()`, then reads `GLOBAL.MOD[module][name]`. The full output for V17.15.0 is in `out/ies.txt` and `out/closure.txt`. Here is an excerpt for InitialUEMessage. The rows are in object-set order, which is also the order on the wire, and the ids and criticalities are resolved from `NGAP-Constants`:

```
== InitialUEMessage
  IE  85 id-RAN-UE-NGAP-ID                             reject  mandatory   RAN-UE-NGAP-ID
  IE  38 id-NAS-PDU                                    reject  mandatory   NAS-PDU
  IE 121 id-UserLocationInformation                    reject  mandatory   UserLocationInformation
  IE  90 id-RRCEstablishmentCause                      ignore  mandatory   RRCEstablishmentCause
  IE  26 id-FiveG-S-TMSI                               reject  optional    FiveG-S-TMSI
  ... 12 more optional rows
  -- 41 named types reached
  UserLocationInformation ::= CHOICE { userLocationInformationEUTRA UserLocationInformationEUTRA, userLocationInformationNR UserLocationInformationNR, userLocationInformationN3IWF-with-PortNumber UserLocationInformationN3IWF-with-PortNumber, choice-Extensions <ProtocolIE-SingleContainer: 4 known rows> }
  UserLocationInformationNR ::= SEQUENCE { nR-CGI NR-CGI, tAI TAI, timeStamp TimeStamp OPTIONAL, iE-Extensions <ProtocolExtensionContainer (SIZE(1..65535)): 3 known rows> OPTIONAL, ... }
  NR-CGI ::= SEQUENCE { pLMNIdentity PLMNIdentity, nRCellIdentity NRCellIdentity, iE-Extensions <…> OPTIONAL, ... }
  PLMNIdentity ::= OCTET STRING (SIZE(3))
  NRCellIdentity ::= BIT STRING (SIZE(36))
  RAN-UE-NGAP-ID ::= INTEGER (0..4294967295)
  RRCEstablishmentCause ::= ENUMERATED { emergency, …, mcs-PriorityAccess, ..., notAvailable, mo-ExceptionData }
```

The same for PDUSessionResourceSetupRequest. Its transfer is reached through `CONTAINING`, and the transfer's IE container is resolved the same way:

```
== PDUSessionResourceSetupRequest
  IE  10 id-AMF-UE-NGAP-ID                             reject  mandatory   AMF-UE-NGAP-ID
  IE  85 id-RAN-UE-NGAP-ID                             reject  mandatory   RAN-UE-NGAP-ID
  IE  83 id-RANPagingPriority                          ignore  optional    RANPagingPriority
  IE  38 id-NAS-PDU                                    reject  optional    NAS-PDU
  IE  74 id-PDUSessionResourceSetupListSUReq           reject  mandatory   PDUSessionResourceSetupListSUReq
  IE 110 id-UEAggregateMaximumBitRate                  ignore  optional    UEAggregateMaximumBitRate
  IE 335 id-UESliceMaximumBitRateList                  ignore  optional    UESliceMaximumBitRateList
  -- 66 named types reached
  PDUSessionResourceSetupListSUReq ::= SEQUENCE (SIZE(1..256)) OF PDUSessionResourceSetupItemSUReq
  PDUSessionResourceSetupItemSUReq ::= SEQUENCE { pDUSessionID PDUSessionID, pDUSessionNAS-PDU NAS-PDU OPTIONAL, s-NSSAI S-NSSAI, pDUSessionResourceSetupRequestTransfer OCTET STRING (CONTAINING PDUSessionResourceSetupRequestTransfer), iE-Extensions <…: 1 known rows> OPTIONAL, ... }
  AMF-UE-NGAP-ID ::= INTEGER (0..1099511627775)
  BitRate ::= INTEGER (0..4000000000000, ...)
== PDUSessionResourceSetupRequestTransfer
  IE 139 id-UL-NGU-UP-TNLInformation                   reject  mandatory   UPTransportLayerInformation
  IE 134 id-PDUSessionType                             reject  mandatory   PDUSessionType
  IE 136 id-QosFlowSetupRequestList                    reject  mandatory   QosFlowSetupRequestList
  ... 12 optional rows
  UPTransportLayerInformation ::= CHOICE { gTPTunnel GTPTunnel, choice-Extensions <ProtocolIE-SingleContainer: 0 known rows> }
  GTPTunnel ::= SEQUENCE { transportLayerAddress TransportLayerAddress, gTP-TEID GTP-TEID, iE-Extensions <…> OPTIONAL, ... }
  TransportLayerAddress ::= BIT STRING (SIZE(1..160, ...))
  GTP-TEID ::= OCTET STRING (SIZE(4))
  PDUSessionType ::= ENUMERATED { ipv4, ipv6, ipv4v6, ethernet, unstructured, ... }
```

How pycrate's model looks to a generator. I checked each of these by inspecting the objects:

- **The IE table.** The `protocolIEs` component is a `SEQUENCE OF` whose item is `ProtocolIE-Field`. Its `value` is an `OPEN_TYPE`, and `_const[0]` is `{'type': 'TABLE', 'tab': <object set>, 'at': …}`. The set's `_val['root']` is a list of rows such as `{id: 85, criticality: 'reject', Value: <RAN-UE-NGAP-ID INTEGER>, presence: 'mandatory'}`. The id is already an integer and `Value` is a type object you can walk. Extension containers have the same shape, with `extensionValue` and `Extension`.
- **Constraints are resolved.** `_const` holds `{'type': 'VAL'|'SIZE', 'root': [ASN1RangeInt(lb..ub)], 'ext': None|[]}`. Here `ext: []` means an extension marker with no additions, and `None` means the type is not extensible. Constants are substituted, so `maxnoofSliceItems` arrives as 1024. CONTAINING arrives as `{'type': 'CONTAINING', 'obj': <type object>}`.
- **Extension markers.** SEQUENCE, CHOICE and ENUMERATED have `_root` (the root names, in order) and `_ext`, which is `None` when the type is not extensible and otherwise lists the extension additions. ENUMERATED `_cont` maps each name to its index. OPTIONAL is `'OPTIONAL' in component._flag`.
- **Two traps.** First, a component that refers to a *constructed* named type has `_cont = None`. You have to follow `_typeref.called`, a `(module, name)` pair, to the definition. `deref()` in `ngap_model.py` does that. Second, the object sets are named with a hyphen, as in `InitialUEMessage-IEs`.

**APER oracle.** `scripts/pycrate_oracle.py` generates pycrate's runtime module from V17.9.0, the release UERANSIM uses. It then builds a full `NGAP-PDU` holding an InitialUEMessage with 5 IEs and a NAS Registration Request, and round-trips it:

```
APER: 000f40440000050055000200010026001a197e004179000d0109f1070000000000000010022e04f0f0f0f00079000f4009f107000000010009f107000001005a4001180070400100
round-trip ok; decoded IE value types: ['RAN-UE-NGAP-ID', 'NAS-PDU', 'UserLocationInformation', 'RRCEstablishmentCause', 'UEContextRequest']
unknown IE id 65000 decodes as: ('_unk_004', b'\x01\x02')
```

To check those bytes independently, I wrapped them as SCTP with PPID 60 using `text2pcap -S 38412,38412,60` and decoded them with `tshark -O ngap`, TShark 4.6.9 from `nix shell nixpkgs#wireshark-cli`. Wireshark reports `id-InitialUEMessage (15)` with 5 items, `RAN-UE-NGAP-ID: 1`, a decoded 5GMM Registration Request with a SUCI, `nRCellIdentity: 0x000000010`, `tAC: 1`, `RRCEstablishmentCause: mo-Signalling (3)` and `UEContextRequest: requested (0)`. It flags nothing as malformed. An unknown IE id stays as raw bytes, which is the behaviour the kernel needs.

### rasn-compiler: what was run and what it shows

I built the probe with `nix shell nixpkgs#cargo nixpkgs#rustc nixpkgs#gcc` (cargo and rustc 1.99.0), with `CARGO_HOME` inside the scratch directory. Its source is in `scripts/rasn-probe/`. It implements `rasn_compiler::prelude::Backend` to dump the linked IR, then also runs the stock `RasnBackend`.

```
IR dump: ok in 1.64s, 0 warnings            (V17.15.0; 1.74s on V19.4.0)
rasn backend: ok in 2.17s, 0 warnings, 1,184,914 bytes of Rust
```

**Good.** The IR keeps each object set as a `ToplevelDefinition::Object`. `InitialUEMessage-IEs` arrives as `ObjectSet { values: [Inline(DefaultSyntax([FixedValueField{&id = LinkedElsewhereDefinedValue "id-RAN-UE-NGAP-ID"}, FixedValueField{&criticality = reject}, TypeField{&Value = "RAN-UE-NGAP-ID"}, FixedValueField{&presence = mandatory}])), …] }`. The class's own syntax has been mapped to fields. The IR also has `Containing(...)`, `extensible: Some(n)` on SEQUENCE and ENUMERATED, and indices on enumerations. It is typed Rust, and the `Backend` trait exists for custom generators.

**Less good:**

- Inside a message, the table constraint is `TableConstraint { object_set: Reference("InitialUEMessage-IEs"), linked_fields: [id] }`. The backend has to look up the set, look up each id's value by name, and look up each type by name.
- The stock rasn output types 191 IE value fields as `Any`, so it does not decode IE values.
- It mistranslates 32 `OCTET STRING (CONTAINING X)` fields as `value("0..")`.
- The crate is pre-1.0 and the trait changed between minor versions; `Backend::new` is now required. The last release was 2025-12-31.
- I did not try to compile the generated Rust.

### asn1tools: what was run

```
venv/bin/python -I scripts/asn1tools_probe.py dl/j40/asn
asn1tools.parser.ParseError: Invalid ASN.1 syntax at line 6632, column 112: '{ ID id-PDUSessionResourceReleaseResponseTransfer CRITICALITY ignore EXTENSION OCTET STRING >!<(CONTAINING PDUSessionResourceReleaseResponseTransfer) PRESENCE optional },': Expected '}'.
```

V17.9.0 fails in the same way. NGAP-PDU-Contents has 27 such rows and NGAP-IEs has 1. After I stripped those constraints with `sed`, `parse_files` worked in 4.2 s, but the result is unusable:

- Every object set has `"members": []`.
- `InitialUEMessage` has `"actual-parameters": ["{"]`.
- `compile_files(files, 'per')` dies with `TypeError: string indices must be integers, not 'str'` in `pre_process_parameterization_step_1_dummy_to_actual_type`.

## 2. Where the ASN.1 comes from, and which release to pin

### Source and extraction

The 3GPP archive at https://www.3gpp.org/ftp/Specs/archive/38_series/38.413/ has one zip per version. Each zip holds a single `.docx`. The file name encodes the version: the letter is the release (f=15, g=16, h=17, i=18, j=19), and the next two characters are the minor and patch numbers in base 36. So `hf0` is 17.15.0.

| Release | First | Latest | Latest date on the server |
|---|---|---|---|
| 15 | f00 (15.0.0) | fd0 (15.13.0) | 2021-10-18 |
| 16 | g00 | gi0 (16.18.0) | 2026-03-20 |
| 17 | h00 | **hf0 (17.15.0)** | 2026-03-20 |
| 18 | i00 | ib0 (18.11.0) | 2026-09-27 |
| 19 | j00 | j40 (19.4.0) | 2026-09-27 |

`out/extract.py` uses only the standard library. It opens the zip, then the docx inside it, then `word/document.xml`, with a 64 MiB limit on that XML. It concatenates the runs, tabs and breaks of each paragraph and maps Word typography, such as non-breaking spaces and smart quotes, back to ASCII. It then writes every block between `-- ASN1START` and `-- ASN1STOP` to `<ModuleName>.asn`, and stops with an error if any non-ASCII character is left or a marker is out of place. Each release yields six modules: PDU-Descriptions, PDU-Contents, IEs, CommonDataTypes, Constants and Containers.

To check the extractor, I ran it on `38413-j20.zip` and compared the result with Open5GS's hand-prepared `lib/asn1c/support/ngap-r19.2.0/38413-j20.asn` at b60aad4, ignoring whitespace. The only differences were 17 comment lines where Open5GS had removed the spec's double quotes.

The deliverable is `out/asn/`, built from 38413-hf0.zip. The zip's sha256 is `6aef2bff270c5e8d9283a3ca5da5c4cba21151cdbf382f52fb30e5d1c892d5e6`. `out/asn/README.md` gives the per-file hashes.

### What UERANSIM uses: V17.9.0

- **Source history.** UERANSIM master is at 4f45e18 (2026-10-14) and the latest release is v3.3.0 (2026-06-07). The repository ships no `.asn` file, only asn1c-0.9.29 output in `src/asn/ngap/`. That directory last changed in commit 11dd5e78b4 (2024-10-28), "Add rel17 compiled asn and ngap files", from [PR #739](https://github.com/aligungr/UERANSIM/pull/739), "Update ASN and NGAP files to 3GPP Release 17", merged 2024-12-10. The PR's build script sets `NGAP_ASN_FILE="ngap-17.9.asn"`, and the PR says the ASN.1 was taken from obj-sys.com.
- **Fingerprint.** I listed the 1,071 `ASN_NGAP_*.h` type headers in UERANSIM and compared them with the type assignments in each release I extracted, after removing the 5 CLASS names, which asn1c does not emit, and asn1c's `asn_constant` header. Against **17.9.0 the match is exact, 1071 = 1071**. 17.15.0 differs by 1 and 4 names, 18.11.0 by 1 and 148, and 19.4.0 by 1 and 238.
- **Other implementations.**
  - srsRAN Project `main` says "3GPP TS ASN1 NGAP v17.4.0 (2023-03)" in `include/srsran/asn1/ngap/ngap_ies.h`.
  - OpenAirInterface `develop` still ships `openair3/NGAP/MESSAGES/ASN1/ngap-15.8.0.asn1`.
  - Open5GS uses 19.2.0.

### What the release changes for this message set

I ran the same `ies` and `closure` commands on 17.9.0, 17.15.0, 18.11.0 and 19.4.0 and compared the results for the 15 messages and 2 transfers:

- **IE rows.** No row's id, criticality, presence or type changes between 17.9.0 and 19.4.0, and none is removed. Newer releases only add optional rows. 17.15.0 adds none, 18.11.0 adds 21 and 19.4.0 adds 30. Of the added rows in messages the AMF receives, these have criticality `reject`: `MobileIABNodeIndication` in InitialUEMessage (Rel-18), and `AIoT-Support` in NGSetupRequest and `GW-Context-Release-Indication` in UEContextReleaseRequest (Rel-19).
- **Type definitions.** Of the types in the closure that two releases share, the only definitions that change are ENUMERATED values added after `...` and renames that keep the same index. The changed ENUMERATEDs are `CauseNas`, `CauseRadioNetwork`, `EventType`, `TraceDepth` and the fields of `BeamMeasurementsReportQuantity`. The renames are `MBS-SupportIndicator`'s `true`, which became `multicast-supported`, and `UserLocationInformation`'s third alternative. That alternative was `UserLocationInformationN3IWF` in 17.9.0 and became `…N3IWF-with-PortNumber` in 17.15.0, which also added a choice-extension row for a without-port variant. No root changed anywhere in this set, so APER bytes for this message set are identical across the releases.
- **Release 19 is still changing.** Between 19.2.0 and 19.4.0 the 3GPP text changed `estimateofExpectedD2RMsgSize` from `OPTIONAL` to mandatory and `AIOTFIdentifier` from `OCTET STRING` to `OCTET STRING (SIZE(16..36, ...))`, and it renamed `MBSCommServiceType`. These are AIoT and MBS features outside this set, but they show that the Release 19 ASN.1 is still being corrected in ways that break the wire format.
- **A warning from UERANSIM's own history.** [UERANSIM issue #684](https://github.com/aligungr/UERANSIM/issues/684) is still open. Its Release 15 build could not decode an AMF's NGSetupResponse because one `ServedGUAMIItem` carried an `iE-Extensions` row it did not know, `GUAMIType`, and the result was "APER decoding failed … transfer-syntax-error". APER extensibility made that message legal. The asn1c-generated decoder still failed on it. Two rules follow for the kernel. Its decoder must keep unknown rows as bytes, as the ticket #4 design already says. Its encoder should emit only IEs and extension rows that exist in UERANSIM's 17.9.0. Pinning 17.15.0 gives that for free, because these messages have the same rows in both versions. If the pin ever moves, the generator should check that rule.

### Why 17.15.0 rather than the alternatives

- **17.9.0 matches UERANSIM exactly.** But 17.15.0 is the same release with six more correction rounds, and for this message set it has the same IE rows and wire-compatible types. Differential tests against UERANSIM work the same with either.
- **18.11.0 or 19.4.0.** These add only optional IEs and enum values that neither UERANSIM nor srsRAN sends. Release 19 is still changing. They also enlarge the full closure, from 321 types in 17.15.0 to 343 in 18.11.0 and 353 in 19.4.0. One cost of not choosing Release 19: Open5GS, at 19.2.0, would have names the kernel lacks. That does not affect the bytes for this set.
- **Re-pinning later** means rerunning `extract.py` and the generator. Tier M stays the same 120 types.

## 3. Type closure of the milestone message set

`out/closure.txt` comes from `ngap_model.py out/asn closure` on V17.15.0. It lists every named type with its tier and a one-line definition, with constraints resolved. It ends with a table of every IE row: id, criticality, presence and type, plus the number of types that row would add beyond the M+R floor.

**What is counted.** The roots are the 15 messages and the 2 transfers, and they count themselves. Every named NGAP type their encoding reaches counts too, following SEQUENCE, CHOICE and SEQUENCE OF components and `CONTAINING`. The five generic containers are not counted, because the APER library handles them once: `ProtocolIE-Container`, `-SingleContainer`, `-Field`, `ProtocolExtensionContainer` and `-Field`. The tiers are cumulative:

- **M**: what the mandatory IEs reach, plus every root component of any type reached. A SEQUENCE's OPTIONAL components are in its root, so they cannot be skipped.
- **R**: adds the optional IEs with criticality `reject` in messages the AMF receives. Under TS 38.413 §10.3.4–10.3.5, if the AMF does not comprehend such an IE it must reject the procedure. So the codec has to comprehend them, or the AMF rejects legal UERANSIM messages. FiveG-S-TMSI in InitialUEMessage is one of them.
- **O**: adds every other optional IE.
- **X**: adds everything reachable through `iE-Extensions` and `choice-Extensions` rows.

| Release | M | M+R | M+R+O | M+R+O+X |
|---|---|---|---|---|
| 17.9.0 | 120 | 131 | 321 | 486 |
| **17.15.0 (recommended)** | **120** | **131** | **321** | **487** |
| 18.11.0 | 120 | 132 | 343 | 565 |
| 19.4.0 | 120 | 134 | 353 | 607 |

In 17.15.0, the 131 types of M+R are 53 SEQUENCE (the 17 roots among them), 18 ENUMERATED, 14 SEQUENCE OF, 14 INTEGER, 12 BIT STRING, 10 CHOICE, 9 OCTET STRING and 1 PrintableString. That is the floor for the codec. The milestone needs M+R plus the few optional IEs the AMF actually sends or reads. The table at the end of `closure.txt` gives the cost of each, for example:

- `CriticalityDiagnostics` adds 8 types.
- `MobilityRestrictionList` adds 12.
- `UEAggregateMaximumBitRate` adds 1.
- `UEContextRequest` adds 1.

My estimate for a realistic subset is about 140–150 types, the same order as the ~134 in the ticket #4 research. Its exact definition was not recorded, but by coincidence M+R on 19.4.0 is also 134.

**Facts from the closure that affect the APER library and the Bend types:**

- Only these kinds appear in M+R: SEQUENCE, SEQUENCE OF, CHOICE, ENUMERATED, INTEGER, BIT STRING, OCTET STRING and PrintableString. There is no BOOLEAN, NULL, REAL or SET. UTF8String and VisibleString appear only in tier O, through `Extended-RANNodeName` and `Extended-AMFName`.
- Some types are larger than U32 can hold. `AMF-UE-NGAP-ID ::= INTEGER (0..1099511627775)`, which is 40 bits, and `BitRate ::= INTEGER (0..4000000000000, ...)` are in M. `SecurityKey ::= BIT STRING (SIZE(256))` and `NRCellIdentity ::= BIT STRING (SIZE(36))` are in M too.
- `PDUSessionResourceSetupUnsuccessfulTransfer` is a third transfer the ticket's list leaves out. It is in tier O, reached through `PDUSessionResourceFailedToSetupListSURes` and `…FailedToSetupListCxtRes/Fail` with CONTAINING, so the AMF needs it to read why a gNB failed a PDU session. `PDUSessionResourceSetupResponseTransfer` is a plain SEQUENCE without an IE container. The request transfer has one.

## Files

| Path | What it is |
|---|---|
| `out/asn/*.asn`, `out/asn/README.md` | The TS 38.413 V17.15.0 modules, with the source URL, zip sha256 and per-file sha256 |
| `out/extract.py` | Extracts the ASN.1 from the 3GPP zip or docx. Standard library only. `python3 -I extract.py 38413-hf0.zip asn/` |
| `out/closure.txt` | The type closure with tiers, definitions and the cost of each IE |
| `out/ies.txt` | The IE and type enumeration for InitialUEMessage, PDUSessionResourceSetupRequest and the request transfer |
| `out/ngap_model.py` | The pycrate adapter that produced both files above. It is a starting point for the generator's front end |
| `scripts/` | The probes: `asn1tools_probe.py`, `pycrate_oracle.py`, `rasn-probe/` (Cargo.toml and main.rs). The deleted downloads, venv and Cargo build can be rebuilt from the commands above |
