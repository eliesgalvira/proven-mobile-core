import Base
import ./bytes.bend as B
import ./tlv.bend as T
import ./frame.bend as F
import ./table.bend as Tb
import ./ausf.bend as Au

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

# Every tag the milestone needs is given (0x0001 to 0x0012); subscribers may be absent.
def Cfg.complete(+tl: List<&2, T.Tlv>) -> Bool:
  Bool.and(Cfg.given(1, tl), Bool.and(Cfg.given(2, tl), Bool.and(Cfg.given(3, tl), Bool.and(Cfg.given(4, tl), Bool.and(Cfg.given(5, tl), Bool.and(Cfg.given(6, tl), Bool.and(Cfg.given(7, tl), Bool.and(Cfg.given(8, tl), Bool.and(Cfg.given(9, tl), Bool.and(Cfg.given(10, tl), Bool.and(Cfg.given(11, tl), Bool.and(Cfg.given(12, tl), Bool.and(Cfg.given(13, tl), Bool.and(Cfg.given(14, tl), Bool.and(Cfg.given(15, tl), Bool.and(Cfg.given(16, tl), Bool.and(Cfg.given(17, tl), Cfg.given(18, tl))))))))))))))))))

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

def Cfg.suci_key(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      suci_key

def Cfg.subscribers(c: Cfg) -> List<&2, B.Bytes()>:
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      subscribers

def Cfg.smf_n4(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      smf_n4

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

# Where a UE is in registration. Every phase before registration carries the
# guard timer that bounds it (T3570 identifying, T3560 authenticating), so a
# context is never left waiting without one; Releasing waits for the gNB.
type Phase is Data:
  Identifying{guard: Guard}
  Authenticating{guard: Guard, av: Au.Av, resynced: Bool}
  Authenticated{guard: Guard, k_amf: B.Bytes()}
  Releasing{}

def Phase.guard(p: Phase) -> Maybe<&2, Guard>:
  match p:
    case Identifying{guard}:
      Some{guard}
    case Authenticating{guard, av, resynced}:
      Some{guard}
    case Authenticated{guard, k_amf}:
      Some{guard}
    case Releasing{}:
      None{}

def Phase.with_guard(p: Phase, g: Guard) -> Phase:
  match p:
    case Identifying{guard}:
      Identifying{g}
    case Authenticating{guard, av, resynced}:
      Authenticating{g, av, resynced}
    case Authenticated{guard, k_amf}:
      Authenticated{g, k_amf}
    case Releasing{}:
      Releasing{}

def Phase.releasing(p: Phase) -> Bool:
  match p:
    case Releasing{}:
      True{}
    case _:
      False{}

# A UE context: the NGAP association that owns it, its RAN-UE-NGAP-ID there,
# the stream its InitialUEMessage arrived on, its SUPI once known, the plain
# Registration Request, the ngKSI in use, its phase and the last downlink NAS
# message (retransmitted when the guard fires).
type Ue is Data:
  Ue{assoc: U32, ran_id: B.Bytes(), stream: U32, supi: Maybe<&2, B.Digits()>, reg: B.Bytes(), ngksi: U32, phase: Phase, last_dl: B.Bytes()}

def Ue.assoc(u: Ue) -> U32:
  match u:
    case Ue{assoc, ran_id, stream, supi, reg, ngksi, phase, last_dl}:
      assoc

def Ue.ran_id(u: Ue) -> B.Bytes():
  match u:
    case Ue{assoc, ran_id, stream, supi, reg, ngksi, phase, last_dl}:
      ran_id

def Ue.stream(u: Ue) -> U32:
  match u:
    case Ue{assoc, ran_id, stream, supi, reg, ngksi, phase, last_dl}:
      stream

def Ue.supi(u: Ue) -> Maybe<&2, B.Digits()>:
  match u:
    case Ue{assoc, ran_id, stream, supi, reg, ngksi, phase, last_dl}:
      supi

def Ue.phase(u: Ue) -> Phase:
  match u:
    case Ue{assoc, ran_id, stream, supi, reg, ngksi, phase, last_dl}:
      phase

def Ue.last_dl(u: Ue) -> B.Bytes():
  match u:
    case Ue{assoc, ran_id, stream, supi, reg, ngksi, phase, last_dl}:
      last_dl

def Ue.guard(u: Ue) -> Maybe<&2, Guard>:
  Phase.guard(Ue.phase(u))

def Ue.with_phase(u: Ue, p: Phase) -> Ue:
  match u:
    case Ue{assoc, ran_id, stream, supi, reg, ngksi, phase, last_dl}:
      Ue{assoc, ran_id, stream, supi, reg, ngksi, p, last_dl}

def Ue.with_dl(u: Ue, p: Phase, dl: B.Bytes()) -> Ue:
  match u:
    case Ue{assoc, ran_id, stream, supi, reg, ngksi, phase, last_dl}:
      Ue{assoc, ran_id, stream, supi, reg, ngksi, p, dl}

def Ue.with_supi(u: Ue, s: B.Digits()) -> Ue:
  match u:
    case Ue{assoc, ran_id, stream, supi, reg, ngksi, phase, last_dl}:
      Ue{assoc, ran_id, stream, Some{s}, reg, ngksi, phase, last_dl}

# A PDU session, keyed by its local SEID: its UE and the UP function's SEID.
type Session is Data:
  Session{ue: U32, up_seid: B.Bytes()}

def Session.ue(s: Session) -> U32:
  match s:
    case Session{ue, up_seid}:
      ue

def Session.up_seid(s: Session) -> B.Bytes():
  match s:
    case Session{ue, up_seid}:
      up_seid

type State is Data:
  State{config: Maybe<&2, Cfg>, subs: List<&2, Au.Subscriber>, assocs: List<&2, U32>, ues: Tb.Table(Ue), sessions: Tb.Table(Session), pfcp_seq: U32, next_ue: U32, next_timer: U32, recovery: B.Bytes()}

def State.initial() -> State:
  State{None{}, [], [], [], [], 1, 1, 1, []}

def State.config(st: State) -> Maybe<&2, Cfg>:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      config

def State.subs(st: State) -> List<&2, Au.Subscriber>:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      subs

def State.assocs(st: State) -> List<&2, U32>:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      assocs

def State.ues(st: State) -> Tb.Table(Ue):
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      ues

def State.sessions(st: State) -> Tb.Table(Session):
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      sessions

def State.pfcp_seq(st: State) -> U32:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      pfcp_seq

def State.recovery(st: State) -> B.Bytes():
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      recovery

def State.put_ue(st: State, key: U32, u: Ue) -> State:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      State{config, subs, assocs, Tb.Table.set(Ue, key, u, ues), sessions, pfcp_seq, next_ue, next_timer, recovery}

def State.put_subs(st: State, new: List<&2, Au.Subscriber>) -> State:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      State{config, new, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}

# A fresh timer id, and a fresh AMF-UE-NGAP-ID.
def State.fresh_timer(st: State) -> Sigma<&2, &2, U32, _ => State>:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, +next_timer, recovery}:
      (next_timer, State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, U32.add(next_timer, 1), recovery})

def State.fresh_ue(st: State) -> Sigma<&2, &2, U32, _ => State>:
  match st:
    case State{config, subs, assocs, ues, sessions, pfcp_seq, +next_ue, next_timer, recovery}:
      (next_ue, State{config, subs, assocs, ues, sessions, pfcp_seq, U32.add(next_ue, 1), next_timer, recovery})

# What one step answers: the next state and the actions to perform.
def Out() -> Data:
  Sigma<&2, &2, State, _ => List<&2, F.Action>>

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

def Ues.keep_row(key: U32, u: Ue, rest: Tb.Table(Ue), other: Bool) -> Tb.Table(Ue):
  match other:
    case True{}:
      (key, u) <> rest
    case False{}:
      rest

# The contexts not owned by association a.
def Ues.drop_assoc(+a: U32, ues: Tb.Table(Ue)) -> Tb.Table(Ue):
  match ues:
    case Nil{}:
      []
    case (key, +u) <> more:
      Ues.keep_row(key, u, Ues.drop_assoc(a, more), Bool.not(U32.is_eq(Ue.assoc(u), a)))

# No context is owned by association a.
def Ues.none_assoc(+a: U32, ues: Tb.Table(Ue)) -> Bool:
  match ues:
    case Nil{}:
      True{}
    case (key, u) <> more:
      Bool.and(Bool.not(U32.is_eq(Ue.assoc(u), a)), Ues.none_assoc(a, more))

# Sessions whose UE is gone
# -------------------------

def Sessions.split(key: U32, s: Session, kept: Tb.Table(Session), gone: List<&2, Session>, owned: Bool) -> Sigma<&2, &2, Tb.Table(Session), _ => List<&2, Session>>:
  match owned:
    case True{}:
      ((key, s) <> kept, gone)
    case False{}:
      (kept, s <> gone)

def Sessions.split_go(key: U32, +s: Session, +ues: Tb.Table(Ue), r: Sigma<&2, &2, Tb.Table(Session), _ => List<&2, Session>>) -> Sigma<&2, &2, Tb.Table(Session), _ => List<&2, Session>>:
  match r:
    case (kept, gone):
      Sessions.split(key, s, kept, gone, Tb.Table.has(Ue, Session.ue(s), ues))

# The sessions whose UE still exists, and the orphans to release.
def Sessions.partition(+ues: Tb.Table(Ue), sessions: Tb.Table(Session)) -> Sigma<&2, &2, Tb.Table(Session), _ => List<&2, Session>>:
  match sessions:
    case Nil{}:
      ([], [])
    case (key, +s) <> more:
      Sessions.split_go(key, s, ues, Sessions.partition(ues, more))

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
