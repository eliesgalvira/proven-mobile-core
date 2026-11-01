# 5G spec kernel

The rules of the 5G core network expressed as pure, machine-checked functions. Terms follow the 3GPP (3rd Generation Partnership Project) standards, so they match the specs, the advisories and other cores.

## Project

**Kernel**:
The pure part of the system: codecs, 5G cryptography, procedure state machines and packet rules, with their proofs. It never touches the network, the disk or the clock.
_Avoid_: core (that word means the whole 5G core network), engine

**Thin layer**:
The code outside the kernel that turns network traffic and timers into events for the kernel and carries out the actions it returns.
_Avoid_: shell, runtime, driver

**Acceptance list**:
The set of known security advisories whose bug classes the kernel must be proven to rule out.
_Avoid_: CVE list, bug list

**Upstream ticket**:
An issue in this repo describing a Bend 2 limitation or bug, reviewed by a human before anything is filed with the Bend project.

## Network

**Core network**:
The set of network functions behind the antennas that admits phones, authenticates them and carries their traffic.

**UE (User Equipment)**:
The phone or device that connects to the network.
_Avoid_: phone, handset, client (in specs and code)

**gNB (next-generation Node B)**:
The 5G base station: the antenna site the UE talks to over radio.
_Avoid_: antenna, cell, base station (in specs and code)

**Network function**:
One role in the core network with a defined interface, such as AMF, SMF or UPF.
_Avoid_: NF instance, service, server

**AMF (Access and Mobility Management Function)**:
The network function that admits UEs, runs registration and tracks where each UE is.

**SMF (Session Management Function)**:
The network function that sets up PDU sessions: assigns addresses and tells the UPF how to forward traffic.

**UPF (User Plane Function)**:
The network function that forwards the UE's packets between the gNB and the data network.

**AUSF (Authentication Server Function)**:
The network function that runs 5G authentication on behalf of the home network.

**UDM (Unified Data Management)**:
The network function that holds subscriber credentials and generates authentication challenges.

## Protocols

**NAS (Non-Access Stratum)**:
The protocol between the UE and the core network (AMF and SMF), carried through the gNB.

**NGAP (Next Generation Application Protocol)**:
The protocol between the gNB and the AMF.

**PFCP (Packet Forwarding Control Protocol)**:
The protocol the SMF uses to install forwarding rules in the UPF.

**GTP-U (GPRS Tunnelling Protocol, User plane)**:
The tunnel header that wraps the UE's packets between the gNB and the UPF.

**Codec**:
A pair of functions that decode bytes into a message and encode a message into bytes, for one protocol.
_Avoid_: parser (only half of it), serializer

## Procedures and identities

**Procedure**:
A defined exchange of messages with its own state machine, such as registration or PDU session establishment.
_Avoid_: conversation, flow, call flow

**Registration**:
The procedure by which a UE joins the network: identification, authentication, security mode and acceptance.
_Avoid_: attach (4G term), login

**PDU session (Protocol Data Unit session)**:
A UE's connection to a data network, with an address and forwarding rules in the UPF.
_Avoid_: bearer (4G term), data connection

**SUPI (Subscription Permanent Identifier)**:
The subscriber's permanent identity, never sent in clear over the air in 5G.
_Avoid_: IMSI (one possible format of a SUPI)

**SUCI (Subscription Concealed Identifier)**:
The SUPI encrypted by the UE for the home network, so eavesdroppers cannot track it.
_Avoid_: hidden identity, encrypted IMSI

**5G-AKA (5G Authentication and Key Agreement)**:
The challenge-response procedure that proves the UE holds the subscriber's secret key and derives the session keys.
