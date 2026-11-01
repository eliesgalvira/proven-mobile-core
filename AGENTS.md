# 5G spec kernel

The rules of 5G written as pure functions in Bend 2, with machine-checked proofs: message codecs, 5G cryptography, the state machines of each conversation, and the per-packet rule decision. Everything that touches the network, the disk or the clock lives in a thin layer outside the kernel.

## Why this project exists: security

Open-source 5G cores keep shipping the same classes of bug: reading past the end of an attacker's message, crashing on input an attacker chose, using a user's data after it was freed, and letting one peer act on state that belongs to another. Every design decision here is judged first by whether it lets us prove those bugs away. `docs/security/open5gs-advisories-2026.md` logs the advisories this project must be able to prove impossible; treat it as the acceptance list.

## Deliberately out of scope (for now)

- 4G
- voice calls
- roaming between operators
- policy and billing
- handover between antennas (the first planned extension)

When the user asks what is missing, list these as deliberately left out, separately from the gaps that are actually open.

## Bend 2 problems go through upstream tickets

Bend 2 is fixed as the language (`docs/adr/0001-bend-2-is-fixed.md`). When work hits a Bend limitation or bug, never file anything with Bend directly. Open an issue in this repo labelled `upstream:bend` with:

- what was attempted and what happened;
- the smallest `.bend` file that reproduces it;
- the `bend --version`, `uname -sm` and the first line of `clang --version`;
- the workaround used here, if any.

The human reviews it and decides whether to file it upstream.

Bend's preferences, read on 2026-11-01:

- Use the bug or feature forms at https://github.com/bendlang/bend/issues. Blank issues are disabled, and questions go to Discord.
- Read `WONTFIX.txt` in their repo first. If the problem is already listed there, note that on the ticket instead of proposing a report.
- Pull requests are accepted (124 merged from about 20 outside contributors), but an issue is the expected first step.

## Agent skills

### Issue tracker

Issues and the wayfinder map live in this repo's GitHub Issues (private repo `eliesgalvira/5G-spec-kernel`), via the `gh` CLI. See `docs/agents/issue-tracker.md`.

### Triage labels

The five default triage labels, each equal to its role name (`needs-triage`, `needs-info`, `ready-for-agent`, `ready-for-human`, `wontfix`). See `docs/agents/triage-labels.md`.

### Domain docs

Single-context: one `GLOSSARY.md` and `docs/adr/` at the repo root, created lazily. See `docs/agents/domain.md`.
