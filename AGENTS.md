# 5G spec kernel

The rules of 5G written as pure functions in Bend 2, with machine-checked proofs. Everything that touches the network, the disk or the clock lives in the thin layer. Terms are defined in `GLOSSARY.md`.

## Why this project exists: security

Open-source 5G cores keep shipping the same classes of bug: reading past the end of an attacker's message, crashing on input an attacker chose, using data after it was freed, and letting one peer act on another's state. Judge every decision first by whether it lets us prove those bugs away. `docs/security/open5gs-advisories-2026.md` is the acceptance list.

A property counts as proven only when it passes `bend --verdict`. The everyday checker is for development only.

## Deliberately out of scope (for now)

- 4G
- voice calls
- roaming between operators
- policy and billing
- handover beyond milestone 2's scope (inter-AMF, inter-UPF, indirect forwarding, conditional handover, DAPS)

When the user asks what is missing, list these as deliberately left out, separately from the gaps that are actually open.

## Licence: read, don't copy

The project is 0BSD. Read other cores (Open5GS, free5GC, Ella Core) for ideas, but never copy their code: their licences would come with it. Code generated from the 3GPP spec definitions is fine.

## Bend 2 problems go through upstream tickets

Bend 2 is fixed as the language (`docs/adr/0001-bend-2-is-fixed.md`). Never file anything with Bend directly. When work hits a Bend limitation or bug, check Bend's `WONTFIX.txt`, then write a draft in `loop/upstream-bend/NN-slug.md` with:

- what was attempted and what happened;
- the smallest `.bend` file that reproduces it;
- `bend version`, `uname -sm` and the first line of `clang --version`;
- the workaround used here, if any.

The human reviews each draft, turns the ones worth keeping into issues here labelled `upstream:bend`, and decides whether to file them upstream through Bend's bug or feature form.

## The implementation loop

The milestone specs are `docs/spec/milestone-1.md` and `docs/spec/milestone-2.md`; their tickets are `docs/spec/tickets/NN-*.md`, taken in the order of `loop/progress.md`. `loop/progress.md` tracks their status (`todo`, `in-progress`, `done`, `blocked`, `needs-human`). The loop runs unattended in a cloud session, and any new session resumes it from the files alone.

1. **Branch.** Work on `loop/m1`. If it exists on origin, check it out and pull; otherwise create it from `origin/main`. Never push to `main`.
2. **Before each ticket.** `git fetch origin`.
   - If the branch `loop/stop` exists on origin, push, add a final note to `loop/progress.md`, push again, and stop.
   - Otherwise merge `origin/main` into `loop/m1`. Spec fixes and new test vectors land on `main` while the loop runs.
   - Re-check every `blocked` ticket whose blocker the merge may have cleared.
3. **Pick.** Take the first ticket that is `in-progress` (resume it) or `todo` with every dependency `done`. Mark it `in-progress`, commit, push.
4. **Build.** Read the ticket and the spec overview. Work test-first with the `tdd` skill. The seams a ticket lists count as agreed with the user. Order: laws into `kernel/LAWS.bend`, then tests, then code and proofs.
5. **Commit and push often.** Commit after each green step, and push at least every 30 minutes and at the end of each ticket. Elies can stop the session at any moment and must lose nothing.
6. **Done.** When the ticket's Verify command and `scripts/check.nu` both pass, mark it `done` in `loop/progress.md` with the commit hash and one line on what was built. Commit and push.
7. **Blocked.** Never wait for a human. When something blocks a ticket (a law you can't prove after real effort, a missing tool, a Bend bug, a contradiction in the spec):
   - add an entry to `loop/blockers.md`: the ticket, what you tried, the smallest reproduction, and what would unblock it;
   - mark the ticket `blocked`, or `needs-human` if only a human can act;
   - push, and take the next eligible ticket.
8. **Bend problems.** Write a draft as § Bend 2 problems says. Don't file anything anywhere and don't open GitHub issues.
9. **Silent spec.** Where the spec doesn't decide something, choose what the best expert would, add one line with the reason to `loop/decisions.md`, and continue.
10. **Never weaken the target.** Don't weaken or delete a law, delete a test vector, or edit `docs/spec/`, `docs/security/` or `test-vectors/` to make something pass. Never use `@unsafe` or foreign imports outside `kernel/main.bend`.
11. **Long commands.** Give every command a timeout. Run anything longer than 5 minutes in the background and poll it. Split heavy checks per file.
12. **Finish.** When no eligible ticket remains, run `scripts/check.nu`, write a summary at the top of `loop/progress.md` (what's done, blocked and needs-human, and what to do next), push, and stop.

## Erasure

This section exists to amend your most glaring defect. You are a model trained by a big lab, and these labs neglect one fundamental half of intelligence: ERASURE. Every reward you ever received was for ADDING something -- an answer, a file, a patch, a comment, a rule. Almost none was for REMOVING. So you add by reflex and never subtract, and no amount of raw capability compensates for a missing half.

Why half? Because learning IS compression. A good abstraction is precisely a blob of information that lets you throw other information away, because it expands back into what was discarded. An aha-moment happens when your brain is capable of expressing new information in terms of information you already possess. This is what allows that info to be stored. That is how you learn. Intelligence is not producing knowledge; it is deleting bad knowledge so the good remains. This defect manifests wherever anything under your care only ever grows -- code, comments, docs, notes, memory. Unpruned growth is the symptom.

So install this now: erasure claims HALF of your cognitive budget for this task. While working on my code -- even autonomously, even mid-task -- hunt for things to remove: duplicated concepts to unify, dead code to delete, tangled logic to simplify. Your own confusion is a precision instrument: if something surprised you or was hard to follow, that IS a bad abstraction, and you should TAKE ACTION and untangle it on the spot. When writing new code, spend real effort finding the simplest possible shape, and scan the codebase first to reuse what exists rather than introduce a redundant concept. A diff that removes lines is at least as valuable as one that adds them.

The swap rule: when a task replaces X with Y -- a refactor, a fix, a syntax change -- fully deleting X is PART of the task, always. Keeping the old thing "for compatibility" is NEVER desirable unless explicitly requested. A bug fix -- bad: a special-case `if` shields the symptom; good: the design is re-derived, the cause dies, the `if` never exists. A behavior change -- bad: tests for the old behavior linger or get dodged; good: obsolete tests deleted, the rest updated.

For coding, a more effective way is to take a big codebase and ask it to make it shorter, while still preserving the same behavior. IMPORTANT: avoid code-golfing / minification / uglification. Removing comments or making variable names shorter IS reward hacking. Counter that by counting the NUMBER OF BRANCHES. A branch is: an "if", a "match", a "case". That's THE complexity of your program.

Comments are where you fail hardest. You narrate code with comments in the middle of function bodies -- that is NOT allowed; if you catch yourself doing it, clean it up. You also accumulate comments and never remove them, clogging files. Be aggressive: keep only what is truly essential. A refactor makes a comment stale -- bad: it stays, now lying; good: deleted or rewritten in the same diff. A TODO gets done -- bad: the marker remains; good: it leaves with the fix.

Prose rots the same way: every AGENTS.md, MEMORY.txt and wiki article tends to only grow -- rules added when something breaks, never removed when they stop applying. A server is decommissioned -- bad: its article sits forever; good: article deleted, every link fixed. MEMORY.txt nears its cap -- bad: append anyway; good: GC by importance, promote what lasts to the wiki. A TODO.md item closes -- bad: the line lingers; good: deleted on sight. Before finishing ANY task, ask: what did this change make obsolete -- and did I delete it?

These rules bind, but they do not exhaust the defect. It is baked into your training, so no list can enumerate every place it surfaces -- watch for unpruned growth everywhere, including in places this file never mentions.
For every decision, ask what the best expert in that field would do and why they would reject your current choice; if you can name that reason, don't make the choice. Optimize for what that expert would judge correct, never for what satisfies the stated constraints most cheaply. Every trade-off you take must be stated to the user, never absorbed.

## Agent skills

### Issue tracker

Planning (the wayfinder map) lives in GitHub Issues, through the `gh` CLI; see `docs/agents/issue-tracker.md`. Implementation tickets live in `docs/spec/tickets/`, because cloud sessions cannot use `gh issue`.

### Triage labels

The five default labels, each named after its role. See `docs/agents/triage-labels.md`.

### Domain docs

Single-context: `GLOSSARY.md` and `docs/adr/` at the repo root. See `docs/agents/domain.md`.
