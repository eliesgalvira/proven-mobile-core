# NGAP ASN.1, 3GPP TS 38.413 V17.15.0 (Release 17)

These six modules are the ASN.1 of 3GPP TS 38.413 V17.15.0 (2026-03), "NG-RAN; NG Application Protocol (NGAP) (Release 17)", §9.4. They are unedited: `extract.py` copies each block between `-- ASN1START` and `-- ASN1STOP` into `<ModuleName>.asn`.

| | |
|---|---|
| Source | https://www.3gpp.org/ftp/Specs/archive/38_series/38.413/38413-hf0.zip |
| Listed on the server | 2026/03/20 14:03, 3017,7 KB |
| Zip sha256 | `6aef2bff270c5e8d9283a3ca5da5c4cba21151cdbf382f52fb30e5d1c892d5e6` |
| Contents | `38413-hf0.docx` (3,133,084 bytes, dated 2026-02-24 inside the zip) |
| Title page | "3GPP TS 38.413 V17.15.0 (2026-03) … (Release 17)" |
| Extracted | 2026-11-01, `python3 -I extract.py 38413-hf0.zip asn/` |

| File | Lines | sha256 |
|---|---|---|
| NGAP-PDU-Descriptions.asn | 886 | `6a108ab99ecfe43b2f1ef2d3ad0b96392d5fbee86873b322a7f5f4ea48a596fa` |
| NGAP-PDU-Contents.asn | 3317 | `ad1d0c39e52d6f2025dec02efb9b90a41323b3e6ad6ef07749063b54f9379a6a` |
| NGAP-IEs.asn | 7018 | `258a72c3ea9f9d4211f8be1184ff5778880c3daaad5aaa53ba607773336dcea3` |
| NGAP-CommonDataTypes.asn | 32 | `fe0c981f70ef52e7377a0b976c0e0e582e0208f0575fea2120c61f7ea7c73731` |
| NGAP-Constants.asn | 584 | `3f639636d93a2c88b59b47c180a408bd24f8cd7c6a1423b73af17a1865018234` |
| NGAP-Containers.asn | 198 | `6582bc5c38f1e4f6c6cf7e3de041e36b6a7b063be516b039654a6f15110d741e` |

Things to know about the text:

- Some lines carry Word's indentation, which can be up to 24 leading tabs (for example before `MBS-SessionID ::=`). ASN.1 ignores it, but a line-anchored regex will miss those assignments.
- Comments keep the spec's double quotes, for example `-- … set to the value "required" or "preferred"`. Open5GS strips these quotes by hand before running asn1c. pycrate 0.8.1 does not need that.
- The object sets are named with a hyphen, as in `InitialUEMessage-IEs`, not `InitialUEMessageIEs`.
- To check the extractor, I ran it on `38413-j20.zip`. The result matched Open5GS's hand-prepared `38413-j20.asn` (commit b60aad4) except for whitespace and those comment quotes.
