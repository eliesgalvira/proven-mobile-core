# Bend 2 is the kernel's language, with no fallback

The kernel is written in Bend 2 even though, as of 2026-10-30, its compiler is unaudited, it has no 64-bit integers, no SCTP and no IPv6, and it still ships breaking changes. Mature provers (Lean 4, F*, Rocq) were considered and rejected: we bet on the Bend team closing these gaps rather than keeping a fallback language. Every limitation we hit becomes an upstream ticket in this repo (label `upstream:bend`), reviewed by a human before anything is filed with Bend, so the project works around gaps in the open instead of switching languages.
