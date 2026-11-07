import Base
import ./bytes.bend as B
import ./tlv.bend as T
import ./frame.bend as F
import ./table.bend as Tb
import ./plmn.bend as P
import ./ausf.bend as Au
import ./nas/security.bend as N
import ./nas/sm.bend as Sm

# The kernel state (docs/spec/milestone-1.md § The step function): one record.
# Each UE context is owned by one row keyed by AMF-UE-NGAP-ID; everything else
# that refers to a UE holds that key.

# Operator configuration, as the Config event gives it (§ The frame protocol).
type Cfg is Data:
  Cfg{plmn: B.Bytes(), region: B.Bytes(), set_id: B.Bytes(), pointer: B.Bytes(), tac: B.Bytes(), name: B.Bytes(), sst: B.Bytes(), dnn: B.Bytes(), pool: B.Bytes(), prefix: B.Bytes(), dns: B.Bytes(), smf_n4: B.Bytes(), upf_n3: B.Bytes(), upf_n4: B.Bytes(), suci_key: B.Bytes(), suci_key_id: B.Bytes(), nea: B.Bytes(), nia: B.Bytes(), subscribers: List<&2, B.Bytes()>}

def Cfg.need(m: Maybe<&2, B.Bytes()>) -> B.Bytes():
  match m:
    case None{}:
      []
    case Some{v}:
      v

def Cfg.given(+tag: U32, tl: List<&2, T.Tlv>) -> Bool:
  Tb.Table.present(B.Bytes(), F.Config.get(tag, tl))

def Cfg.tag(+tag: U32, tl: List<&2, T.Tlv>) -> B.Bytes():
  Cfg.need(F.Config.get(tag, tl))

def Cfg.of(+tl: List<&2, T.Tlv>) -> Cfg:
  Cfg{Cfg.tag(1, tl), Cfg.tag(2, tl), Cfg.tag(3, tl), Cfg.tag(4, tl), Cfg.tag(5, tl), Cfg.tag(6, tl), Cfg.tag(7, tl), Cfg.tag(8, tl), Cfg.tag(9, tl), Cfg.tag(10, tl), Cfg.tag(11, tl), Cfg.tag(12, tl), Cfg.tag(13, tl), Cfg.tag(14, tl), Cfg.tag(15, tl), Cfg.tag(16, tl), Cfg.tag(17, tl), Cfg.tag(18, tl), F.Config.subscribers(tl)}

def Cfg.plmn(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      plmn

def Cfg.region(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      region

def Cfg.set_id(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      set_id

def Cfg.pointer(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      pointer

def Cfg.tac(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      tac

def Cfg.name(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      name

def Cfg.sst(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      sst

def Cfg.dnn(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      dnn

def Cfg.pool(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      pool

def Cfg.prefix(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      prefix

def Cfg.dns(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      dns

def Cfg.upf_n3(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      upf_n3

def Cfg.suci_key(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      suci_key

def Cfg.subscribers(c: Cfg) -> List<&2, B.Bytes()>:
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      subscribers

def Cfg.nea(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      nea

def Cfg.nia(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      nia

def Cfg.smf_n4(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      smf_n4

# What the kernel relies on beyond the tags being given: a PLMN of three
# octets that decodes, which the serving network name is built from, and a DNS
# server of four octets, which the Accept's ePCO carries.
def Cfg.valid(+c: Cfg) -> Bool:
  Bool.and(F.Len.is(Cfg.plmn(c), 3n), Bool.and(F.Result.ok(B.ReadValue(P.Plmn), P.Plmn.read(Cfg.plmn(c))), F.Len.is(Cfg.dns(c), 4n)))

# Every tag the milestone needs is given (0x0001 to 0x0012); subscribers may be absent.
def Cfg.given_all(+tl: List<&2, T.Tlv>) -> Bool:
  Bool.and(Cfg.given(1, tl), Bool.and(Cfg.given(2, tl), Bool.and(Cfg.given(3, tl), Bool.and(Cfg.given(4, tl), Bool.and(Cfg.given(5, tl), Bool.and(Cfg.given(6, tl), Bool.and(Cfg.given(7, tl), Bool.and(Cfg.given(8, tl), Bool.and(Cfg.given(9, tl), Bool.and(Cfg.given(10, tl), Bool.and(Cfg.given(11, tl), Bool.and(Cfg.given(12, tl), Bool.and(Cfg.given(13, tl), Bool.and(Cfg.given(14, tl), Bool.and(Cfg.given(15, tl), Bool.and(Cfg.given(16, tl), Bool.and(Cfg.given(17, tl), Cfg.given(18, tl))))))))))))))))))

# A configuration the kernel takes: every tag given, and valid.
def Cfg.complete(+tl: List<&2, T.Tlv>) -> Bool:
  Bool.and(Cfg.given_all(tl), Cfg.valid(Cfg.of(tl)))

# A guard timer the edge runs for a UE: its id and how often it has fired.
type Guard is Data:
  Guard{timer: U32, retries: U32}

def Guard.timer(g: Guard) -> U32:
  match g:
    case Guard{timer, retries}:
      timer

def Guard.retries(g: Guard) -> U32:
  match g:
    case Guard{timer, retries}:
      retries

# Where a UE is in registration. Every phase but Registered carries the guard
# timer that bounds it (T3570 identifying, T3560 authenticating and in
# security mode, T3550 setting up the context, and the wait for the gNB's UE
# Context Release Complete), so no context waits forever. Created is a context
# the InitialUEMessage has just made, before its first procedure places it;
# no stored context is in it (amf.contexts.guarded). The SUPI a SUCI
# de-conceals to stays in Authenticating, out of the SUPI index, until 5G-AKA
# verifies it.
type Phase is Data:
  Created{}
  Identifying{guard: Guard}
  Authenticating{guard: Guard, av: Au.Av, resynced: Bool, supi: B.Digits()}
  SecurityMode{guard: Guard, ctx: N.Nas.Ctx, k_amf: B.Bytes()}
  ContextSetup{guard: Guard, ctx: N.Nas.Ctx, response: Bool, complete: Bool}
  Registered{ctx: N.Nas.Ctx}
  Releasing{guard: Guard}

def Phase.guard(p: Phase) -> Maybe<&2, Guard>:
  match p:
    case Created{}:
      None{}
    case Identifying{guard}:
      Some{guard}
    case Authenticating{guard, av, resynced, supi}:
      Some{guard}
    case SecurityMode{guard, ctx, k_amf}:
      Some{guard}
    case ContextSetup{guard, ctx, response, complete}:
      Some{guard}
    case Registered{ctx}:
      None{}
    case Releasing{guard}:
      Some{guard}

# Registered, or waiting under its guard; Created is neither.
def Phase.guarded(p: Phase) -> Bool:
  match p:
    case Created{}:
      False{}
    case Registered{ctx}:
      True{}
    case other:
      Tb.Table.present(Guard, Phase.guard(other))

def Phase.with_guard(p: Phase, g: Guard) -> Phase:
  match p:
    case Created{}:
      Created{}
    case Identifying{guard}:
      Identifying{g}
    case Authenticating{guard, av, resynced, supi}:
      Authenticating{g, av, resynced, supi}
    case SecurityMode{guard, ctx, k_amf}:
      SecurityMode{g, ctx, k_amf}
    case ContextSetup{guard, ctx, response, complete}:
      ContextSetup{g, ctx, response, complete}
    case Registered{ctx}:
      Registered{ctx}
    case Releasing{guard}:
      Releasing{g}

# The NAS security context in force, once there is one.
def Phase.ctx(p: Phase) -> Maybe<&2, N.Nas.Ctx>:
  match p:
    case SecurityMode{guard, ctx, k_amf}:
      Some{ctx}
    case ContextSetup{guard, ctx, response, complete}:
      Some{ctx}
    case Registered{ctx}:
      Some{ctx}
    case _:
      None{}

def Phase.with_ctx(p: Phase, c: N.Nas.Ctx) -> Phase:
  match p:
    case SecurityMode{guard, ctx, k_amf}:
      SecurityMode{guard, c, k_amf}
    case ContextSetup{guard, ctx, response, complete}:
      ContextSetup{guard, c, response, complete}
    case Registered{ctx}:
      Registered{c}
    case other:
      other

# A UE context: the NGAP association that owns it, its RAN-UE-NGAP-ID there,
# the stream its InitialUEMessage arrived on, its SUPI once authenticated and
# its 5G-TMSI once given,
# the plain Registration Request, the ngKSI in use, its phase and the last
# downlink NAS message (retransmitted when the guard fires).
type Ue is Data:
  Ue{assoc: U32, ran_id: B.Bytes(), stream: U32, supi: Maybe<&2, B.Digits()>, tmsi: Maybe<&2, U32>, reg: B.Bytes(), ngksi: U32, phase: Phase, last_dl: B.Bytes()}

def Ue.assoc(u: Ue) -> U32:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      assoc

def Ue.ran_id(u: Ue) -> B.Bytes():
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      ran_id

def Ue.stream(u: Ue) -> U32:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      stream

def Ue.supi(u: Ue) -> Maybe<&2, B.Digits()>:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      supi

def Ue.tmsi(u: Ue) -> Maybe<&2, U32>:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      tmsi

def Ue.reg(u: Ue) -> B.Bytes():
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      reg

def Ue.ngksi(u: Ue) -> U32:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      ngksi

def Ue.phase(u: Ue) -> Phase:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      phase

def Ue.last_dl(u: Ue) -> B.Bytes():
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      last_dl

def Ue.guard(u: Ue) -> Maybe<&2, Guard>:
  Phase.guard(Ue.phase(u))

def Ue.with_phase(u: Ue, p: Phase) -> Ue:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, p, last_dl}

def Ue.with_dl(u: Ue, p: Phase, dl: B.Bytes()) -> Ue:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, p, dl}

def Ue.with_supi(u: Ue, s: B.Digits()) -> Ue:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      Ue{assoc, ran_id, stream, Some{s}, tmsi, reg, ngksi, phase, last_dl}

def Ue.with_tmsi(u: Ue, t: U32) -> Ue:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      Ue{assoc, ran_id, stream, supi, Some{t}, reg, ngksi, phase, last_dl}

def Ue.with_reg(u: Ue, r: B.Bytes()) -> Ue:
  match u:
    case Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      Ue{assoc, ran_id, stream, supi, tmsi, r, ngksi, phase, last_dl}

# A PDU session, keyed by its local SEID. Its identity (the UE, the PDU
# session identity, the UE IPv4 address, the N3 uplink TEID) never changes;
# the rest does as the procedure advances.
type SId is Data:
  SId{ue: U32, psi: U32, ip: U32, teid: U32}

# Where a session is: PFCP Session Establishment pending (the PTI and the
# Accept to send on success), the gNB's resource setup pending, the
# PFCP Session Modification with the gNB's tunnel pending, or active.
type SPhase is Data:
  Creating{guard: Guard, pti: U32, accept: Sm.Sm}
  Setting{guard: Guard, pti: U32}
  Modifying{guard: Guard}
  Active{}

def SPhase.guard(p: SPhase) -> Maybe<&2, Guard>:
  match p:
    case Creating{guard, pti, accept}:
      Some{guard}
    case Setting{guard, pti}:
      Some{guard}
    case Modifying{guard}:
      Some{guard}
    case Active{}:
      None{}

# eUPF knows a session exactly when it is past Creating.
def SPhase.knows(p: SPhase, +known: Bool) -> Bool:
  match p:
    case Creating{guard, pti, accept}:
      Bool.not(known)
    case _:
      known

# The UP function's SEID, the sequence number of the PFCP request pending, the phase.
type SVar is Data:
  SVar{up_seid: B.Bytes(), seq: U32, phase: SPhase}

type Session is Data:
  Session{id: SId, var: SVar}

def Session.id(s: Session) -> SId:
  match s:
    case Session{id, var}:
      id

def Session.var(s: Session) -> SVar:
  match s:
    case Session{id, var}:
      var

def Session.with_var(s: Session, v: SVar) -> Session:
  match s:
    case Session{id, var}:
      Session{id, v}

def SId.ue(i: SId) -> U32:
  match i:
    case SId{ue, psi, ip, teid}:
      ue

def SId.psi(i: SId) -> U32:
  match i:
    case SId{ue, psi, ip, teid}:
      psi

def SId.ip(i: SId) -> U32:
  match i:
    case SId{ue, psi, ip, teid}:
      ip

def SId.teid(i: SId) -> U32:
  match i:
    case SId{ue, psi, ip, teid}:
      teid

def Session.ue(s: Session) -> U32:
  SId.ue(Session.id(s))

def Session.psi(s: Session) -> U32:
  SId.psi(Session.id(s))

def Session.ip(s: Session) -> U32:
  SId.ip(Session.id(s))

def Session.teid(s: Session) -> U32:
  SId.teid(Session.id(s))

def SVar.up_seid(v: SVar) -> B.Bytes():
  match v:
    case SVar{up_seid, seq, phase}:
      up_seid

def SVar.seq(v: SVar) -> U32:
  match v:
    case SVar{up_seid, seq, phase}:
      seq

def SVar.phase(v: SVar) -> SPhase:
  match v:
    case SVar{up_seid, seq, phase}:
      phase

def Session.up_seid(s: Session) -> B.Bytes():
  SVar.up_seid(Session.var(s))

def Session.seq(s: Session) -> U32:
  SVar.seq(Session.var(s))

def Session.phase(s: Session) -> SPhase:
  SVar.phase(Session.var(s))

# eUPF knows a session once it has answered with its UP SEID, eight octets.
def Session.known(s: Session) -> Bool:
  Nat.is_eq(List.length(&2, U32, Session.up_seid(s)), 8n)

# The PFCP association with eUPF, which the SMF starts: being asked for (T1
# running, so many tries), paused after too many tries, or up (heartbeats).
type Link is Data:
  Idle{}
  Asking{tries: U32}
  Paused{}
  Up{}

# N4: the PFCP recovery stamp chosen at Config, and the association.
type N4 is Data:
  N4{recovery: B.Bytes(), link: Link}

# Timer 0 is the N4 association's; UE and session guards take the others.
def N4.timer() -> U32:
  0

def N4.recovery(n: N4) -> B.Bytes():
  match n:
    case N4{recovery, link}:
      recovery

def N4.link(n: N4) -> Link:
  match n:
    case N4{recovery, link}:
      link

def N4.with_link(n: N4, l: Link) -> N4:
  match n:
    case N4{recovery, link}:
      N4{recovery, l}

type State is Data:
  State{config: Maybe<&2, Cfg>, subs: List<&2, Au.Subscriber>, assocs: List<&2, U32>, ues: Tb.Table(Ue), sessions: Tb.Table(Session), pfcp_seq: U32, next_ue: U32, next_timer: U32, n4: N4}

def State.initial() -> State:
  State{None{}, [], [], [], [], 1, 1, 1, N4{[], Idle{}}}

def State.config(st: State) -> Maybe<&2, Cfg>:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      config

def State.subs(st: State) -> List<&2, Au.Subscriber>:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      subs

def State.assocs(st: State) -> List<&2, U32>:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      assocs

def State.ues(st: State) -> Tb.Table(Ue):
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      ues

def State.sessions(st: State) -> Tb.Table(Session):
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      sessions

def State.pfcp_seq(st: State) -> U32:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      pfcp_seq

def State.next_ue(st: State) -> U32:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      next_ue

def State.next_timer(st: State) -> U32:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      next_timer

def State.n4(st: State) -> N4:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      n4

# Associations
# ------------

def Assocs.has(+a: U32, as: List<&2, U32>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case b <> more:
      Bool.or(U32.is_eq(b, a), Assocs.has(a, more))

def Assocs.add_if(a: U32, as: List<&2, U32>, known: Bool) -> List<&2, U32>:
  match known:
    case True{}:
      as
    case False{}:
      a <> as

def Assocs.add(+a: U32, +as: List<&2, U32>) -> List<&2, U32>:
  Assocs.add_if(a, as, Assocs.has(a, as))

def Assocs.drop_if(b: U32, rest: List<&2, U32>, hit: Bool) -> List<&2, U32>:
  match hit:
    case True{}:
      rest
    case False{}:
      b <> rest

def Assocs.drop(+a: U32, as: List<&2, U32>) -> List<&2, U32>:
  match as:
    case Nil{}:
      []
    case +b <> more:
      Assocs.drop_if(b, Assocs.drop(a, more), U32.is_eq(b, a))

# UE contexts of an association
# -----------------------------

# No context is owned by association a.
def Ues.none_assoc(+a: U32, ues: Tb.Table(Ue)) -> Bool:
  match ues:
    case Nil{}:
      True{}
    case (key, u) <> more:
      Bool.and(Bool.not(U32.is_eq(Ue.assoc(u), a)), Ues.none_assoc(a, more))

# The UE whose guard timer this is
# --------------------------------

def Ues.timer_is(g: Maybe<&2, Guard>, +timer: U32) -> Bool:
  match g:
    case None{}:
      False{}
    case Some{guard}:
      U32.is_eq(Guard.timer(guard), timer)

def Ues.pick_timer(key: U32, u: Ue, later: Maybe<&2, Sigma<&2, &2, U32, _ => Ue>>, hit: Bool) -> Maybe<&2, Sigma<&2, &2, U32, _ => Ue>>:
  match hit:
    case True{}:
      Some{(key, u)}
    case False{}:
      later

def Ues.by_timer(+timer: U32, ues: Tb.Table(Ue)) -> Maybe<&2, Sigma<&2, &2, U32, _ => Ue>>:
  match ues:
    case Nil{}:
      None{}
    case (key, +u) <> more:
      Ues.pick_timer(key, u, Ues.by_timer(timer, more), Ues.timer_is(Ue.guard(u), timer))

# Indexes
# -------
# The secondary indexes (SUPI, 5G-TMSI, RAN-UE-NGAP-ID per association) are
# the contexts themselves, searched; two rows conflict when they share a key
# or an identity. A sieve names the rows to keep.

def Maybe.same_bytes(a: Maybe<&2, B.Bytes()>, b: Maybe<&2, B.Bytes()>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      B.bytes_eq(x, y)
    case _ _:
      False{}

def Maybe.same_u32(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      U32.is_eq(x, y)
    case _ _:
      False{}

def Ue.conflicts(+u: Ue, +v: Ue) -> Bool:
  Bool.or(Maybe.same_bytes(Ue.supi(u), Ue.supi(v)), Bool.or(Maybe.same_u32(Ue.tmsi(u), Ue.tmsi(v)), Bool.and(U32.is_eq(Ue.assoc(u), Ue.assoc(v)), B.bytes_eq(Ue.ran_id(u), Ue.ran_id(v)))))

def Row.conflicts(key: U32, u: Ue, k: U32, v: Ue) -> Bool:
  Bool.or(U32.is_eq(k, key), Ue.conflicts(u, v))

def Ues.clear(+key: U32, +u: Ue, ues: Tb.Table(Ue)) -> Bool:
  match ues:
    case Nil{}:
      True{}
    case (k, v) <> more:
      Bool.and(Bool.not(Row.conflicts(key, u, k, v)), Ues.clear(key, u, more))

# Some context holds 5G-TMSI t.
def Ues.has_tmsi(+t: U32, ues: Tb.Table(Ue)) -> Bool:
  match ues:
    case Nil{}:
      False{}
    case (key, u) <> more:
      Bool.or(Maybe.same_u32(Some{t}, Ue.tmsi(u)), Ues.has_tmsi(t, more))

# Some context with this SUPI holds a NAS security context, which exists only
# once 5G-AKA has verified the SUPI.
def Ue.secures(+u: Ue, s: Maybe<&2, B.Digits()>) -> Bool:
  Bool.and(Maybe.same_bytes(Ue.supi(u), s), Tb.Table.present(N.Nas.Ctx, Phase.ctx(Ue.phase(u))))

def Ues.secured(+s: Maybe<&2, B.Digits()>, ues: Tb.Table(Ue)) -> Bool:
  match ues:
    case Nil{}:
      False{}
    case (key, u) <> more:
      Bool.or(Ue.secures(u, s), Ues.secured(s, more))

# No two rows share a key or an index.
def Ues.unique(ues: Tb.Table(Ue)) -> Bool:
  match ues:
    case Nil{}:
      True{}
    case (+key, +u) <> +more:
      Bool.and(Ues.clear(key, u, more), Ues.unique(more))

# Every context is registered or waits under its guard.
def Ues.guarded(ues: Tb.Table(Ue)) -> Bool:
  match ues:
    case Nil{}:
      True{}
    case (key, u) <> more:
      Bool.and(Phase.guarded(Ue.phase(u)), Ues.guarded(more))

type Sieve is Data:
  Others{assoc: U32}
  Clear{key: U32, u: Ue}
  Victims{key: U32, u: Ue}
  Except{key: U32}

def Sieve.keeps(s: Sieve, k: U32, v: Ue) -> Bool:
  match s:
    case Others{a}:
      Bool.not(U32.is_eq(Ue.assoc(v), a))
    case Clear{key, u}:
      Bool.not(Row.conflicts(key, u, k, v))
    case Victims{key, u}:
      Bool.and(Bool.not(U32.is_eq(k, key)), Ue.conflicts(u, v))
    case Except{key}:
      Bool.not(U32.is_eq(k, key))

def Ues.sift(+s: Sieve, ues: Tb.Table(Ue)) -> Tb.Table(Ue):
  match ues:
    case Nil{}:
      []
    case (+k, +v) <> more:
      Tb.Table.keep(Ue, k, v, Ues.sift(s, more), Sieve.keeps(s, k, v))

# The contexts not owned by association a.
def Ues.drop_assoc(a: U32, ues: Tb.Table(Ue)) -> Tb.Table(Ue):
  Ues.sift(Others{a}, ues)

# The context takes the place of its key and of every context it conflicts with.
def Ues.put(+key: U32, +u: Ue, ues: Tb.Table(Ue)) -> Tb.Table(Ue):
  (key, u) <> Ues.sift(Clear{key, u}, ues)

# The rows under other keys that a context would take the place of.
def Ues.evicted(key: U32, u: Ue, ues: Tb.Table(Ue)) -> Tb.Table(Ue):
  Ues.sift(Victims{key, u}, ues)

def Ues.del(key: U32, ues: Tb.Table(Ue)) -> Tb.Table(Ue):
  Ues.sift(Except{key}, ues)

# A phase change in place: the row under the key, its identity untouched.
def Ue.rephase_if(u: Ue, p: Phase, hit: Bool) -> Ue:
  match hit:
    case True{}:
      Ue.with_phase(u, p)
    case False{}:
      u

def Ues.rephase(+key: U32, +p: Phase, ues: Tb.Table(Ue)) -> Tb.Table(Ue):
  match ues:
    case Nil{}:
      []
    case (+k, u) <> more:
      (k, Ue.rephase_if(u, p, U32.is_eq(k, key))) <> Ues.rephase(key, p, more)

# Sessions
# --------
# The session indexes (UE IPv4, uplink TEID, the PDU session identity of a
# UE) are the sessions themselves, searched, like the UE indexes.

def Session.conflicts(+a: Session, +b: Session) -> Bool:
  Bool.or(U32.is_eq(Session.ip(a), Session.ip(b)), Bool.or(U32.is_eq(Session.teid(a), Session.teid(b)), Bool.and(U32.is_eq(Session.ue(a), Session.ue(b)), U32.is_eq(Session.psi(a), Session.psi(b)))))

def SRow.conflicts(key: U32, s: Session, k: U32, t: Session) -> Bool:
  Bool.or(U32.is_eq(k, key), Session.conflicts(s, t))

def Sessions.clear(+key: U32, +s: Session, sessions: Tb.Table(Session)) -> Bool:
  match sessions:
    case Nil{}:
      True{}
    case (k, t) <> more:
      Bool.and(Bool.not(SRow.conflicts(key, s, k, t)), Sessions.clear(key, s, more))

def Sessions.unique(sessions: Tb.Table(Session)) -> Bool:
  match sessions:
    case Nil{}:
      True{}
    case (+key, +s) <> +more:
      Bool.and(Sessions.clear(key, s, more), Sessions.unique(more))

# Every session belongs to a context of the table.
def Sessions.owned(sessions: Tb.Table(Session), +ues: Tb.Table(Ue)) -> Bool:
  match sessions:
    case Nil{}:
      True{}
    case (k, s) <> more:
      Bool.and(Tb.Table.has(Ue, Session.ue(s), ues), Sessions.owned(more, ues))

# eUPF knows every session past Creating and none being created.
def Sessions.known(sessions: Tb.Table(Session)) -> Bool:
  match sessions:
    case Nil{}:
      True{}
    case (k, +s) <> more:
      Bool.and(SPhase.knows(Session.phase(s), Session.known(s)), Sessions.known(more))

# Which sessions to keep: those of other UEs, those of one UE, those whose UE
# exists, the orphans, those clear of a session, the victims of one, all but a key.
type SSieve is Data:
  SOthers{ue: U32}
  SOf{ue: U32}
  SOwned{ues: Tb.Table(Ue)}
  SOrphan{ues: Tb.Table(Ue)}
  SClear{key: U32, s: Session}
  SVictims{key: U32, s: Session}
  SExcept{key: U32}

def SSieve.keeps(s: SSieve, k: U32, t: Session) -> Bool:
  match s:
    case SOthers{ue}:
      Bool.not(U32.is_eq(Session.ue(t), ue))
    case SOf{ue}:
      U32.is_eq(Session.ue(t), ue)
    case SOwned{ues}:
      Tb.Table.has(Ue, Session.ue(t), ues)
    case SOrphan{ues}:
      Bool.not(Tb.Table.has(Ue, Session.ue(t), ues))
    case SClear{key, u}:
      Bool.not(SRow.conflicts(key, u, k, t))
    case SVictims{key, u}:
      Bool.and(Bool.not(U32.is_eq(k, key)), Session.conflicts(u, t))
    case SExcept{key}:
      Bool.not(U32.is_eq(k, key))

def Sessions.sift(+s: SSieve, sessions: Tb.Table(Session)) -> Tb.Table(Session):
  match sessions:
    case Nil{}:
      []
    case (+k, +t) <> more:
      Tb.Table.keep(Session, k, t, Sessions.sift(s, more), SSieve.keeps(s, k, t))

def Sessions.drop_ue(ue: U32, sessions: Tb.Table(Session)) -> Tb.Table(Session):
  Sessions.sift(SOthers{ue}, sessions)

def Sessions.of_ue(ue: U32, sessions: Tb.Table(Session)) -> Tb.Table(Session):
  Sessions.sift(SOf{ue}, sessions)

def Sessions.put(+key: U32, +s: Session, sessions: Tb.Table(Session)) -> Tb.Table(Session):
  (key, s) <> Sessions.sift(SClear{key, s}, sessions)

def Sessions.evicted(key: U32, s: Session, sessions: Tb.Table(Session)) -> Tb.Table(Session):
  Sessions.sift(SVictims{key, s}, sessions)

def Sessions.del(key: U32, sessions: Tb.Table(Session)) -> Tb.Table(Session):
  Sessions.sift(SExcept{key}, sessions)

def Session.revar_if(s: Session, v: SVar, hit: Bool) -> Session:
  match hit:
    case True{}:
      Session.with_var(s, v)
    case False{}:
      s

def Sessions.revar(+key: U32, +v: SVar, sessions: Tb.Table(Session)) -> Tb.Table(Session):
  match sessions:
    case Nil{}:
      []
    case (+k, s) <> more:
      (k, Session.revar_if(s, v, U32.is_eq(k, key))) <> Sessions.revar(key, v, more)

# The session with a given UE IPv4 address, pending PFCP sequence number, guard timer, or UE and PDU session identity.
def Sessions.has_ip(+ip: U32, sessions: Tb.Table(Session)) -> Bool:
  match sessions:
    case Nil{}:
      False{}
    case (k, s) <> more:
      Bool.or(U32.is_eq(Session.ip(s), ip), Sessions.has_ip(ip, more))

def Sessions.pick(key: U32, s: Session, later: Maybe<&2, Sigma<&2, &2, U32, _ => Session>>, hit: Bool) -> Maybe<&2, Sigma<&2, &2, U32, _ => Session>>:
  match hit:
    case True{}:
      Some{(key, s)}
    case False{}:
      later

def Sessions.by_seq(+seq: U32, sessions: Tb.Table(Session)) -> Maybe<&2, Sigma<&2, &2, U32, _ => Session>>:
  match sessions:
    case Nil{}:
      None{}
    case (key, +s) <> more:
      Sessions.pick(key, s, Sessions.by_seq(seq, more), U32.is_eq(Session.seq(s), seq))

def Sessions.by_timer(+timer: U32, sessions: Tb.Table(Session)) -> Maybe<&2, Sigma<&2, &2, U32, _ => Session>>:
  match sessions:
    case Nil{}:
      None{}
    case (key, +s) <> more:
      Sessions.pick(key, s, Sessions.by_timer(timer, more), Ues.timer_is(SPhase.guard(Session.phase(s)), timer))

def Sessions.by_psi(+ue: U32, +psi: U32, sessions: Tb.Table(Session)) -> Maybe<&2, Sigma<&2, &2, U32, _ => Session>>:
  match sessions:
    case Nil{}:
      None{}
    case (key, +s) <> more:
      Sessions.pick(key, s, Sessions.by_psi(ue, psi, more), Bool.and(U32.is_eq(Session.ue(s), ue), U32.is_eq(Session.psi(s), psi)))

# Fresh ids
# ---------
# AMF-UE-NGAP-IDs and timer ids count up and wrap at 2^32, skipping every id
# still live. Fewer ids are live than the fuel given, so among that many
# candidates one is free and the search never runs out.

def Ids.next(id: U32, later: Unit -> U32, taken: Bool) -> U32:
  match taken:
    case True{}:
      later(Unit{})
    case False{}:
      id

def Ues.free_key(fuel: Nat, +id: U32, +ues: Tb.Table(Ue)) -> U32:
  match fuel:
    case 0n:
      id
    case 1n+n:
      Ids.next(id, u => Ues.free_key(n, U32.add(id, 1), ues), Tb.Table.has(Ue, id, ues))

# A timer id is the N4 association's, a context's guard or a session's guard.
def Timers.taken(+t: U32, ues: Tb.Table(Ue), sessions: Tb.Table(Session)) -> Bool:
  Bool.or(U32.is_eq(t, N4.timer()), Bool.or(Tb.Table.present(Sigma<&2, &2, U32, _ => Ue>, Ues.by_timer(t, ues)), Tb.Table.present(Sigma<&2, &2, U32, _ => Session>, Sessions.by_timer(t, sessions))))

def Timers.free(fuel: Nat, +id: U32, +ues: Tb.Table(Ue), +sessions: Tb.Table(Session)) -> U32:
  match fuel:
    case 0n:
      id
    case 1n+n:
      Ids.next(id, u => Timers.free(n, U32.add(id, 1), ues, sessions), Timers.taken(id, ues, sessions))

# Transactions
# ------------
# A procedure answers with what to change, applied by one interpreter: a
# context put (evicting the contexts it conflicts with, and their sessions) or
# rephased in place,
# a context and its sessions forgotten, a session put (evicting likewise),
# changed in place or forgotten, the subscribers replaced, the N4 link moved,
# fresh ids (the next free ones) and PFCP sequence numbers consumed.

type Tx is Data:
  Keep{}
  Put{key: U32, ue: Ue}
  Rephase{key: U32, phase: Phase}
  Del{key: U32}
  PutSession{key: U32, s: Session}
  Revar{key: U32, v: SVar}
  DelSession{key: U32}
  Subs{subs: List<&2, Au.Subscriber>}
  SetLink{link: Link}
  BumpUe{}
  BumpTimer{}
  BumpSeq{n: U32}
  Both{first: Tx, second: Tx}

def Tx.apply(tx: Tx, st: State) -> State:
  match tx:
    case Keep{}:
      st
    case Put{+key, +ue}:
      match st:
        case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          +left = Ues.put(key, ue, ues)
          State{config, subs, assocs, left, Sessions.sift(SOwned{left}, sessions), pfcp_seq, next_ue, next_timer, n4}
    case Rephase{key, phase}:
      match st:
        case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          State{config, subs, assocs, Ues.rephase(key, phase, ues), sessions, pfcp_seq, next_ue, next_timer, n4}
    case Del{+key}:
      match st:
        case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          State{config, subs, assocs, Ues.del(key, ues), Sessions.drop_ue(key, sessions), pfcp_seq, next_ue, next_timer, n4}
    case PutSession{key, s}:
      match st:
        case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          State{config, subs, assocs, ues, Sessions.put(key, s, sessions), pfcp_seq, next_ue, next_timer, n4}
    case Revar{key, v}:
      match st:
        case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          State{config, subs, assocs, ues, Sessions.revar(key, v, sessions), pfcp_seq, next_ue, next_timer, n4}
    case DelSession{key}:
      match st:
        case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          State{config, subs, assocs, ues, Sessions.del(key, sessions), pfcp_seq, next_ue, next_timer, n4}
    case Subs{new}:
      match st:
        case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          State{config, new, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}
    case SetLink{link}:
      match st:
        case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, N4.with_link(n4, link)}
    case BumpUe{}:
      match st:
        case State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          State{config, subs, assocs, ues, sessions, pfcp_seq, Ues.free_key(1n+List.length(&2, Sigma<&2, &2, U32, _ => Ue>, ues), U32.add(next_ue, 1), ues), next_timer, n4}
    case BumpTimer{}:
      match st:
        case State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, next_timer, n4}:
          State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, Timers.free(2n+Nat.add(List.length(&2, Sigma<&2, &2, U32, _ => Ue>, ues), List.length(&2, Sigma<&2, &2, U32, _ => Session>, sessions)), U32.add(next_timer, 1), ues, sessions), n4}
    case BumpSeq{n}:
      match st:
        case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          State{config, subs, assocs, ues, sessions, U32.add(pfcp_seq, n), next_ue, next_timer, n4}
    case Both{first, second}:
      Tx.apply(second, Tx.apply(first, st))
