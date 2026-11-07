# Milestone 2: handover within one AMF and one UPF

A UE registered through milestone 1 moves from one gNB to another, and its PDU session follows it:

- **Xn-based handover:** the target gNB sends Path Switch Request (TS 23.502 §4.9.1.2).
- **N2-based handover:** the source gNB sends Handover Required and the AMF prepares the target (TS 23.502 §4.9.1.3).

In both, the kernel moves the UE context to the target association, has the SMF repoint the downlink FAR to the target gNB's tunnel, and advances the NAS security context with a new NH and NCC. The two handover advisories in the acceptance list become in scope, each with its law.

Out of scope for this milestone:
- inter-AMF and inter-UPF handover, and intermediate UPF insertion;
- indirect data forwarding tunnels;
- conditional handover and DAPS;
- handover to or from 4G.

The rest of `AGENTS.md` § Deliberately out of scope still applies.

## What changes

- **Codecs:** the NGAP generator's message set grows by the handover messages and their transfers (ticket 25). NAS and PFCP need no new messages.
- **Keys:** NH and NCC (TS 33.501 §6.9.2, Annex A.10) join the UE's security context (ticket 26).
- **Procedures:** Path Switch (ticket 27) and N2 handover with cancel (ticket 28), both in `kernel/amf/` and `kernel/smf/`. Ticket 28 states the ownership and request-correlation laws over `Kernel.step`, and ticket 29 moves the two handover advisories into the acceptance list.
- **Edge:** no change in behaviour. It already carries several associations and their streams; ticket 31 only tightens its SCTP test coverage.
- **Tests:** replay tests from a new golden capture (ticket 24), and an end-to-end NixOS test with two gNBs (ticket 30).

## Estimates

Each ticket gives the time an unattended agent session would need, judged against milestone 1: 21 tickets in about 11 hours of cloud loop. They are estimates, not measurements. The milestone totals about 15–21 hours.
