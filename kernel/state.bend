import Base
import ./bytes.bend as B
import ./tlv.bend as T
import ./frame.bend as F
import ./table.bend as Tb

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

def Cfg.smf_n4(c: Cfg) -> B.Bytes():
  match c:
    case Cfg{plmn, region, set_id, pointer, tac, name, sst, dnn, pool, prefix, dns, smf_n4, upf_n3, upf_n4, suci_key, suci_key_id, nea, nia, subscribers}:
      smf_n4

# A UE context: the NGAP association that owns it, its RAN-UE-NGAP-ID there
# and the stream its InitialUEMessage arrived on.
type Ue is Data:
  Ue{assoc: U32, ran_id: B.Bytes(), stream: U32}

def Ue.assoc(u: Ue) -> U32:
  match u:
    case Ue{assoc, ran_id, stream}:
      assoc

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
  State{config: Maybe<&2, Cfg>, assocs: List<&2, U32>, ues: Tb.Table(Ue), sessions: Tb.Table(Session), pfcp_seq: U32, next_ue: U32, next_timer: U32, recovery: B.Bytes()}

def State.initial() -> State:
  State{None{}, [], [], [], 1, 1, 1, []}

def State.config(st: State) -> Maybe<&2, Cfg>:
  match st:
    case State{config, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      config

def State.assocs(st: State) -> List<&2, U32>:
  match st:
    case State{config, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      assocs

def State.ues(st: State) -> Tb.Table(Ue):
  match st:
    case State{config, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      ues

def State.sessions(st: State) -> Tb.Table(Session):
  match st:
    case State{config, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      sessions

def State.pfcp_seq(st: State) -> U32:
  match st:
    case State{config, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      pfcp_seq

def State.recovery(st: State) -> B.Bytes():
  match st:
    case State{config, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      recovery

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
