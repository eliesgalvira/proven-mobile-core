import Base
import ../bytes.bend as B
import ../tlv.bend as T
import ../pfcp.bend as Pf
import ../table.bend as Tb
import ../frame.bend as F
import ../state.bend as S
import ../amf/ngap.bend as N

# N4: the SMF's PFCP messages to eUPF (TS 29.244, the subset of
# docs/research/eupf-pfcp.md) and the association with it, which the SMF
# starts: T1 = 3 s, three tries, a 10 s pause, then again; heartbeats every
# 30 s once up. Timer 0 is the association's; UE and session guards start at 1.

def N4.t1_ms() -> U32:
  3000

def N4.pause_ms() -> U32:
  10000

def N4.heartbeat_ms() -> U32:
  30000

def N4.n1() -> U32:
  3

def N4.timer() -> U32:
  0

# Messages
# --------

def N4.byte(kind: U32, v: U32) -> T.Tlv:
  T.Tlv.make(kind, Pf.Byte.write(v))

def N4.short(kind: U32, v: U32) -> T.Tlv:
  T.Tlv.make(kind, Pf.Short.write(v))

def N4.word(kind: U32, v: U32) -> T.Tlv:
  T.Tlv.make(kind, Pf.Word.write(v))

def N4.group(kind: U32, items: List<&2, T.Tlv>) -> T.Tlv:
  T.Tlv.make(kind, T.Tlvs.write(items, []))

def N4.node(cfg: S.Cfg) -> T.Tlv:
  T.Tlv.make(60, Pf.NodeId.write(Pf.NodeV4{S.Cfg.smf_n4(cfg)}))

def N4.msg(kind: U32, seid: Maybe<&2, B.Bytes()>, seq: U32, ies: List<&2, T.Tlv>) -> B.Bytes():
  Pf.Msg.write(Pf.Msg.make(kind, seid, seq, ies), [])

def N4.assoc_setup(cfg: S.Cfg, recovery: B.Bytes(), seq: U32) -> B.Bytes():
  N4.msg(5, None{}, seq, [N4.node(cfg), T.Tlv.make(96, recovery)])

# Heartbeat Request (1) or Response (2): the recovery stamp.
def N4.heartbeat(kind: U32, recovery: B.Bytes(), seq: U32) -> B.Bytes():
  N4.msg(kind, None{}, seq, [T.Tlv.make(96, recovery)])

# A local SEID as the eight octets of the F-SEID.
def N4.seid8(seid: U32) -> B.Bytes():
  B.write_u32(0, B.write_u32(seid, []))

# 1 Gbit/s in kbit/s, forty bits.
def N4.kbps() -> B.Bytes():
  [0, 0, 15, 66, 64]

# Uplink: packets to the N3 TEID, GTP-U removed, forwarded to the core.
def N4.uplink_pdr(cfg: S.Cfg, teid: U32) -> T.Tlv:
  N4.group(1, [N4.short(56, 1), N4.word(29, 255), N4.group(2, [N4.byte(20, 0), T.Tlv.make(21, Pf.Fteid.write(Pf.Teid{teid, Some{S.Cfg.upf_n3(cfg)}, None{}}))]), N4.byte(95, 0), N4.word(108, 1), N4.word(109, 1)])

# Downlink: packets to the UE's address; its FAR drops them until the gNB's tunnel is known.
def N4.downlink_pdr(ip: U32) -> T.Tlv:
  N4.group(1, [N4.short(56, 2), N4.word(29, 255), N4.group(2, [N4.byte(20, 1), T.Tlv.make(93, Pf.UeIp.write(Pf.UeIp{True{}, Some{B.write_u32(ip, [])}, None{}}))]), N4.word(108, 2), N4.word(109, 1)])

def N4.far(id: U32, action: U32, dest: U32) -> T.Tlv:
  N4.group(3, [N4.word(108, id), T.Tlv.make(44, [action, 0]), N4.group(4, [N4.byte(42, dest)])])

# QoS flow 1, gates open, 1 Gbit/s each way.
def N4.qer() -> T.Tlv:
  N4.group(7, [N4.word(109, 1), N4.byte(25, 0), T.Tlv.make(26, Pf.Mbr.write(Pf.Mbr{N4.kbps(), N4.kbps()})), N4.byte(124, 1)])

def N4.establish(+cfg: S.Cfg, seid: U32, ip: U32, teid: U32, seq: U32) -> B.Bytes():
  N4.msg(50, Some{N4.seid8(0)}, seq, [N4.node(cfg), T.Tlv.make(57, Pf.Fseid.write(Pf.Fseid{N4.seid8(seid), Some{S.Cfg.smf_n4(cfg)}, None{}})), N4.uplink_pdr(cfg, teid), N4.downlink_pdr(ip), N4.far(1, 2, 1), N4.far(2, 1, 0), N4.qer()])

# The downlink FAR forwards into the gNB's tunnel.
def N4.modify(up_seid: B.Bytes(), gnb_teid: U32, gnb_addr: B.Bytes(), seq: U32) -> B.Bytes():
  N4.msg(52, Some{up_seid}, seq, [N4.group(10, [N4.word(108, 2), T.Tlv.make(44, [2, 0]), N4.group(11, [N4.byte(42, 0), T.Tlv.make(84, Pf.Ohc.write(Pf.Ohc{256, Some{gnb_teid}, Some{gnb_addr}, None{}, None{}}))])])])

def N4.delete(up_seid: B.Bytes(), seq: U32) -> B.Bytes():
  N4.msg(54, Some{up_seid}, seq, [])

# A session eUPF knows has its UP SEID.
def N4.known(s: S.Session) -> Bool:
  Nat.is_eq(List.length(&2, U32, S.Session.up_seid(s)), 8n)

def N4.known_rows(rows: Tb.Table(S.Session)) -> Tb.Table(S.Session):
  match rows:
    case Nil{}:
      []
    case (key, +s) <> more:
      Tb.Table.keep(S.Session, key, s, N4.known_rows(more), N4.known(s))

def N4.number(rows: Tb.Table(S.Session), +seq: U32) -> List<&2, N.Act>:
  match rows:
    case Nil{}:
      []
    case (key, s) <> more:
      N.Pfcp{N4.delete(S.Session.up_seid(s), seq)} <> N4.number(more, U32.add(seq, 1))

# A Session Deletion for each session row eUPF knows, numbered from seq.
def N4.deletions(rows: Tb.Table(S.Session), seq: U32) -> List<&2, N.Act>:
  N4.number(N4.known_rows(rows), seq)

def N4.deletion_count(rows: Tb.Table(S.Session)) -> U32:
  U32.from_nat(List.length(&2, Sigma<&2, &2, U32, _ => S.Session>, N4.known_rows(rows)))

# Reading responses
# -----------------

def N4.value_of(r: Result<&2, &2, B.Err, U32>) -> Maybe<&2, U32>:
  match r:
    case Fail{e}:
      None{}
    case Done{v}:
      Some{v}

def N4.byte_of(m: Maybe<&2, T.Tlv>) -> Maybe<&2, U32>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      N4.value_of(Pf.Byte.read(T.Tlv.body(t)))

def N4.cause(msg: Pf.Msg) -> Maybe<&2, U32>:
  N4.byte_of(T.Tlvs.find(19, Pf.Msg.ies(msg)))

def N4.seid_of(r: Result<&2, &2, B.Err, Pf.Fseid>) -> Maybe<&2, B.Bytes()>:
  match r:
    case Fail{e}:
      None{}
    case Done{Pf.Fseid{seid, v4, v6}}:
      Some{seid}

def N4.fseid_of(m: Maybe<&2, T.Tlv>) -> Maybe<&2, B.Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      N4.seid_of(Pf.Fseid.read(T.Tlv.body(t)))

def N4.up_seid(msg: Pf.Msg) -> Maybe<&2, B.Bytes()>:
  N4.fseid_of(T.Tlvs.find(57, Pf.Msg.ies(msg)))

def N4.accepted(c: Maybe<&2, U32>) -> Bool:
  match c:
    case Some{1}:
      True{}
    case _:
      False{}

# The association
# ---------------

def N4.ask(cfg: S.Cfg, n4: S.N4, tries: U32, seq: U32) -> N.GOut():
  (S.Both{S.SetLink{S.Asking{tries}}, S.BumpSeq{1}}, [N.Pfcp{N4.assoc_setup(cfg, S.N4.recovery(n4), seq)}, N.TimerStart{N4.timer(), N4.t1_ms()}])

def N4.pause() -> N.GOut():
  (S.SetLink{S.Paused{}}, [N.TimerStart{N4.timer(), N4.pause_ms()}, N.Note{F.Warn{}, "PFCP: no association with eUPF; trying again later"}])

def N4.start_with_tries(+st: S.State, cfg: Maybe<&2, S.Cfg>, tries: U32) -> N.GOut():
  match cfg:
    case None{}:
      (S.Keep{}, [])
    case Some{c}:
      N4.ask(c, S.State.n4(st), tries, S.State.pfcp_seq(st))

# Config, or the pause over: ask for the association.
def N4.start(+st: S.State) -> N.GOut():
  N4.start_with_tries(st, S.State.config(st), 1)

def N4.retry(st: S.State, cfg: Maybe<&2, S.Cfg>, tries: U32, again: Bool) -> N.GOut():
  match again:
    case True{}:
      N4.start_with_tries(st, cfg, tries)
    case False{}:
      N4.pause()

def N4.heartbeat_out(+st: S.State) -> N.GOut():
  (S.BumpSeq{1}, [N.Pfcp{N4.heartbeat(1, S.N4.recovery(S.State.n4(st)), S.State.pfcp_seq(st))}, N.TimerStart{N4.timer(), N4.heartbeat_ms()}])

# Timer 0 fired.
def N4.expired(+st: S.State, link: S.Link) -> N.GOut():
  match link:
    case S.Idle{}:
      (S.Keep{}, [])
    case S.Asking{+tries}:
      N4.retry(st, S.State.config(st), U32.add(tries, 1), U32.is_lt(tries, N4.n1()))
    case S.Paused{}:
      N4.start(st)
    case S.Up{}:
      N4.heartbeat_out(st)

def N4.fired(+st: S.State) -> N.GOut():
  N4.expired(st, S.N4.link(S.State.n4(st)))

def N4.assoc_answer(ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      (S.SetLink{S.Up{}}, [N.TimerStart{N4.timer(), N4.heartbeat_ms()}, N.Note{F.Info{}, "PFCP: association with eUPF up"}])
    case False{}:
      N4.pause()

def N4.assoc_response(msg: Pf.Msg) -> N.GOut():
  N4.assoc_answer(N4.accepted(N4.cause(msg)))

def N4.heartbeat_answer(+st: S.State, msg: Pf.Msg) -> N.GOut():
  (S.Keep{}, [N.Pfcp{N4.heartbeat(2, S.N4.recovery(S.State.n4(st)), Pf.Msg.seq(msg))}])

def Link.up(l: S.Link) -> Bool:
  match l:
    case S.Up{}:
      True{}
    case _:
      False{}

def N4.up(st: S.State) -> Bool:
  Link.up(S.N4.link(S.State.n4(st)))
