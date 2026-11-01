# Official test vectors

Each file is `{ "source": {...}, "cases": [...] }`, transcribed from the primary source named in `source` and retrieved on 2026-11-01. Every case was recomputed independently with Python's standard library and the `cryptography` package before commit.

- `fips180-4.json`: SHA-256 examples from the NIST CSRC example values for FIPS 180-4 (`SHA256.pdf`: "abc" and the 448-bit message; `SHA2_Additional.pdf` #1–#10). Checked with `hashlib.sha256`.
- `rfc4231.json`: RFC 4231 test cases 1–7, HMAC-SHA-256 only. Checked with `hmac`; case 5 is the 128-bit truncation (`mac_length` 16).
- `fips197.json`: FIPS 197 (2001) Appendix B and Appendix C.1, AES-128. Checked with AES-ECB.
- `sp800-38a.json`: SP 800-38A F.5.1 CTR-AES128.Encrypt. Checked with AES-CTR.
- `rfc4493.json`: RFC 4493 §4 AES-CMAC examples 1–4. Checked with `cryptography` CMAC.
- `rfc7748.json`: RFC 7748 §5.2 X25519 single-step vectors, the 1- and 1,000-iteration results, and the §6.1 Diffie-Hellman example. Checked with `cryptography` X25519.
- `ts35208.json`: TS 35.208 V19.0.0 test sets 1–6 (sets 1 and 2 are identical in the spec). Checked against a Milenage implementation written from TS 35.206 V19.0.0 §4, and set 1's hex against its binary form.
- `ts33401-annex-c.json`: TS 33.401 V19.2.0 Annex C.1 128-EEA2 sets 1–6 and C.2 128-EIA2 sets 1–8. Checked with bit-exact AES-CTR and AES-CMAC built per Annex B.1.3 and B.2.3.
- `ts33501-annex-c4.json`: TS 33.501 V20.3.0 Annex C.4: null scheme, Profile A and Profile B, each for an IMSI and an NAI SUPI. Checked by recomputing the public keys, ECDH, the X9.63 KDF, AES-128-CTR, the HMAC-SHA-256 tag and the scheme output.

Conventions:

- Byte strings are lowercase hex. `count` (TS 33.401) is 4 bytes of hex; `bearer`, `direction`, lengths and set numbers are integers.
- TS 33.401 `plaintext`, `ciphertext` and `message` are copied as printed: left-aligned and padded with zero bits to a whole 32-bit word. Only the first `length_bits` bits count.
- `message_repeat: { byte, count }` stands for `count` copies of `byte` (1,000,000 zero bytes).
- TS 33.501 C.4 prints the NAI scheme outputs as text (`ecckey….cip….mac…`). They are kept verbatim in `scheme_output_text`. MCC/MNC and MSIN are digit strings. C.4 gives no assembled SUCI, so the files carry none.
