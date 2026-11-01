# Loop progress

Status values: `todo`, `in-progress`, `done`, `blocked`, `needs-human`. Tickets are in `docs/spec/tickets/`.

| # | Ticket | Status | Depends on | Notes |
|---|---|---|---|---|
| 01 | bootstrap | done | — | 3327ac8: LAWS/PROOF pair, check.sh gate, test runner, acceptance.py, gen-vectors.py and generated vector modules |
| 02 | bytes | done | 01 | 2799d0f: readers u8..u32, take, nibbles, TBCD; 8 laws proven; no U32 lemma file needed |
| 03 | vectors | in-progress | 01 | |
| 04 | sha256-hmac | todo | 02, 03 | |
| 05 | aes | todo | 02, 03 | |
| 06 | milenage | todo | 05 | |
| 07 | kdf | todo | 04, 06 | |
| 08 | x25519-suci | todo | 04, 05, 07 | |
| 09 | nas-security | todo | 05, 07 | |
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
