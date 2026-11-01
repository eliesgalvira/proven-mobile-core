# Loop progress

Status values: `todo`, `in-progress`, `done`, `blocked`, `needs-human`. Tickets are in `docs/spec/tickets/`.

| # | Ticket | Status | Depends on | Notes |
|---|---|---|---|---|
| 01 | bootstrap | done | — | 3327ac8: LAWS/PROOF pair, check.sh gate, test runner, acceptance.py, gen-vectors.py and generated vector modules |
| 02 | bytes | done | 01 | 2799d0f: readers u8..u32, take, nibbles, TBCD; 8 laws proven; no U32 lemma file needed |
| 03 | vectors | done | 01 | ad79428: all 9 spec sources present with source fields; generator emits Vec modules; vectors_load smoke test |
| 04 | sha256-hmac | done | 02, 03 | e5369b6: SHA-256 and HMAC; 12+7 vectors pass; 2 laws proven; upstream draft 01 |
| 05 | aes | done | 02, 03 | 5f32c0d: AES-128, CTR, CMAC; 9 vectors pass; 4 laws proven |
| 06 | milenage | done | 05 | b1b468e: f1, f1*, f2..f5*, OP->OPc; 54 checks pass; lengths law proven |
| 07 | kdf | done | 04, 06 | 3641e6d: KDF, SNN, KAUSF..KgNB; capture keys reproduced; 2 laws proven |
| 08 | x25519-suci | done | 04, 05, 07 | 0493397: X25519, PLMN codec, SUCI decode and Profile A; 7 laws proven; upstream draft 02 |
| 09 | nas-security | done | 05, 07 | d62b26a: NIA2, NEA2, NEA0, protect/unprotect, COUNT estimate; 28 checks; 3 laws proven |
| 10 | nas-5gmm | todo | 02, 03 | |
| 11 | nas-5gsm | todo | 10 | |
| 12 | aper | todo | 02 | |
| 13 | ngap | todo | 03, 12 | |
| 14 | pfcp | todo | 02, 03 | |
| 15 | frames | todo | 02 | |
| 16 | state-ng-setup | todo | 13, 15 | |
| 17 | registration-auth | todo | 08, 09, 10, 16 | |
| 18 | registration-complete | todo | 17 | |
| 19 | pdu-session | todo | 11, 14, 18 | |
| 20 | kernel-main | todo | 15, 19 | |
| 21 | edge | todo | 15 | |
| 22 | e2e | todo | 20, 21 | |
| 23 | acceptance | todo | 01–22 | |
