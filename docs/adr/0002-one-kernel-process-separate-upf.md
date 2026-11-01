# AMF, SMF, AUSF and UDM share one process; the UPF stays separate

The standard runs each network function as its own service and connects them over HTTP. We run AMF, SMF, AUSF and UDM in one process instead, calling each other as plain functions. A gNB never sees those internal interfaces, and removing them removes a whole HTTP attack surface we would otherwise have to prove safe.

The UPF stays a separate program, reached over real PFCP. This keeps the PFCP codec exposed to untrusted bytes, so its proofs matter. The cost is that we cannot mix in other vendors' AMF, SMF, AUSF or UDM.
