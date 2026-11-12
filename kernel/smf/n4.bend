import Base
import ../bytes.bend as B
import ../tlv.bend as T
import ../pfcp.bend as Pf
import ../table.bend as Tb
import ../frame.bend as F
import ../state.bend as S
import ../amf/ngap.bend as N

# N4: the SMF's PFCP messages to the UPF (TS 29.244, the subset of
# docs/research/eupf-pfcp.md) and the association with it, which the SMF
# starts: T1 = 3 s, N1 = 3, a 10 s pause, then again; heartbeats every 30 s
# once up, on timer 0 (S.N4.timer).

def N4.t1_ms() -> U32:
  3000

def N4.pause_ms() -> U32:
  10000

def N4.heartbeat_ms() -> U32:
  30000

def N4.n1() -> U32:
  3

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
  T.Tlv.make(Pf.Ie.node_id(), Pf.NodeId.write(Pf.NodeV4{S.Cfg.smf_n4(cfg)}))

def N4.msg(kind: U32, seid: Maybe<&2, B.Bytes()>, seq: U32, ies: List<&2, T.Tlv>) -> B.Bytes():
  Pf.Msg.write(Pf.Msg.make(kind, seid, seq, ies), [])

def N4.assoc_setup(cfg: S.Cfg, recovery: B.Bytes(), seq: U32) -> B.Bytes():
  N4.msg(Pf.Type.association_setup_request(), None{}, seq, [N4.node(cfg), T.Tlv.make(Pf.Ie.recovery(), recovery)])

# Heartbeat Request (1) or Response (2): the recovery stamp.
def N4.heartbeat(kind: U32, recovery: B.Bytes(), seq: U32) -> B.Bytes():
  N4.msg(kind, None{}, seq, [T.Tlv.make(Pf.Ie.recovery(), recovery)])

# A local SEID as the eight octets of the F-SEID.
def N4.seid8(seid: U32) -> B.Bytes():
  B.write_u32(0, B.write_u32(seid, []))

# 1 Gbit/s in kbit/s, forty bits.
def N4.kbps() -> B.Bytes():
  [0, 0, 15, 66, 64]

# Uplink: packets to the N3 TEID, GTP-U removed, forwarded to the core.
def N4.uplink_pdr(cfg: S.Cfg, teid: U32) -> T.Tlv:
  N4.group(Pf.Ie.create_pdr(), [N4.short(Pf.Ie.pdr_id(), 1), N4.word(Pf.Ie.precedence(), 255), N4.group(Pf.Ie.pdi(), [N4.byte(Pf.Ie.source_interface(), 0), T.Tlv.make(Pf.Ie.fteid(), Pf.Fteid.write(Pf.Teid{teid, Some{S.Cfg.upf_n3(cfg)}, None{}}))]), N4.byte(Pf.Ie.outer_header_removal(), 0), N4.word(Pf.Ie.far_id(), 1), N4.word(Pf.Ie.qer_id(), 1)])

# Downlink: packets to the UE's address; its FAR drops them until the gNB's tunnel is known.
def N4.downlink_pdr(ip: U32) -> T.Tlv:
  N4.group(Pf.Ie.create_pdr(), [N4.short(Pf.Ie.pdr_id(), 2), N4.word(Pf.Ie.precedence(), 255), N4.group(Pf.Ie.pdi(), [N4.byte(Pf.Ie.source_interface(), 1), T.Tlv.make(Pf.Ie.ue_ip(), Pf.UeIp.write(Pf.UeIp{True{}, Some{B.write_u32(ip, [])}, None{}}))]), N4.word(Pf.Ie.far_id(), 2), N4.word(Pf.Ie.qer_id(), 1)])

def N4.far(id: U32, action: U32, dest: U32) -> T.Tlv:
  N4.group(Pf.Ie.create_far(), [N4.word(Pf.Ie.far_id(), id), T.Tlv.make(Pf.Ie.apply_action(), [action, 0]), N4.group(Pf.Ie.forwarding(), [N4.byte(Pf.Ie.destination_interface(), dest)])])

# QoS flow 1, gates open, 1 Gbit/s each way.
def N4.qer() -> T.Tlv:
  N4.group(Pf.Ie.create_qer(), [N4.word(Pf.Ie.qer_id(), 1), N4.byte(Pf.Ie.gate_status(), 0), T.Tlv.make(Pf.Ie.mbr(), Pf.Mbr.write(Pf.Mbr{N4.kbps(), N4.kbps()})), N4.byte(Pf.Ie.qfi(), 1)])

def N4.establish(+cfg: S.Cfg, seid: U32, ip: U32, teid: U32, seq: U32) -> B.Bytes():
  N4.msg(Pf.Type.session_establishment_request(), Some{N4.seid8(0)}, seq, [N4.node(cfg), T.Tlv.make(Pf.Ie.fseid(), Pf.Fseid.write(Pf.Fseid{N4.seid8(seid), Some{S.Cfg.smf_n4(cfg)}, None{}})), N4.uplink_pdr(cfg, teid), N4.downlink_pdr(ip), N4.far(1, 2, 1), N4.far(2, 1, 0), N4.qer()])

# The downlink FAR forwards into the gNB's tunnel.
def N4.modify(up_seid: B.Bytes(), gnb_teid: U32, gnb_addr: B.Bytes(), seq: U32) -> B.Bytes():
  N4.msg(Pf.Type.session_modification_request(), Some{up_seid}, seq, [N4.group(Pf.Ie.update_far(), [N4.word(Pf.Ie.far_id(), 2), T.Tlv.make(Pf.Ie.apply_action(), [2, 0]), N4.group(Pf.Ie.update_forwarding(), [N4.byte(Pf.Ie.destination_interface(), 0), T.Tlv.make(Pf.Ie.outer_header_creation(), Pf.Ohc.write(Pf.Ohc{256, Some{gnb_teid}, Some{gnb_addr}, None{}, None{}}))])])])

def N4.delete(up_seid: B.Bytes(), seq: U32) -> B.Bytes():
  N4.msg(Pf.Type.session_deletion_request(), Some{up_seid}, seq, [])

# A Session Deletion Request for the session is among the actions, at some sequence number.
def N4.deleted(+s: S.Session, +acts: List<&2, N.Act>) -> Type:
  Sigma<&2, &2, U32, seq => Sigma<&2, &2, List<&2, N.Act>, pre => Sigma<&2, &2, List<&2, N.Act>, post => {acts == List.append(&2, N.Act, pre, N.Pfcp{Some{S.Session.ue(s)}, N4.delete(S.Session.up_seid(s), seq)} <> post) : List<&2, N.Act>}>>>

# A Session Deletion Request for each session row the UPF knows, numbered
# from seq: the row waits, being deleted, under its guard, until the UPF
# answers or the retries run out (TS 29.244 §6.4); a row the UPF does not know
# goes at once.
def N4.delete_if(+key: U32, +s: S.Session, +seq: U32, later: U32 -> N.GOut(), known: Bool) -> N.GOut():
  match known:
    case True{}:
      +request = N4.delete(S.Session.up_seid(s), seq)
      N.Out.join((S.Both{S.Revar{key, S.SVar{S.Session.up_seid(s), seq, S.Deleting{S.Guard{0}, request}}}, S.BumpSeq{1}}, [N.Pfcp{S.Session.tag(s), request}, N.TimerStart{None{}, key, N4.t1_ms()}]), later(U32.add(seq, 1)))
    case False{}:
      N.Out.join((S.DelSession{key}, []), later(seq))

def N4.deletions(rows: Tb.Table(S.Session), seq: U32) -> N.GOut():
  match rows:
    case Nil{}:
      (S.Keep{}, [])
    case (+key, +s) <> more:
      N4.delete_if(key, s, seq, q => N4.deletions(more, q), S.Session.known(s))

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
  N4.byte_of(T.Tlvs.find(Pf.Ie.cause(), Pf.Msg.ies(msg)))

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
  N4.fseid_of(T.Tlvs.find(Pf.Ie.fseid(), Pf.Msg.ies(msg)))

def N4.accepted(c: Maybe<&2, U32>) -> Bool:
  match c:
    case Some{1}:
      True{}
    case _:
      False{}

# The association
# ---------------
# A request goes again with its own sequence number, T1 apart, up to N1 times
# (TS 29.244 §6.4). Without an answer to the Association Setup Request the SMF
# pauses; without one to a Heartbeat Request the association is lost, and
# asked for again.

def N4.asked(+st: S.State, cfg: Maybe<&2, S.Cfg>, +seq: U32, resent: U32, tx: S.Tx) -> N.GOut():
  match cfg:
    case None{}:
      (S.Keep{}, [])
    case Some{c}:
      (S.Both{tx, S.SetLink{S.Asking{seq, resent}}}, [N.Pfcp{None{}, N4.assoc_setup(c, S.N4.recovery(S.State.n4(st)), seq)}, N.TimerStart{None{}, S.N4.timer(), N4.t1_ms()}])

def N4.pause() -> N.GOut():
  (S.SetLink{S.Paused{}}, [N.TimerStart{None{}, S.N4.timer(), N4.pause_ms()}, N.Note{F.Warn{}, "PFCP: no association with the UPF; trying again later"}])

# Config, the pause over or the association lost: a new Association Setup Request.
def N4.start(+st: S.State) -> N.GOut():
  N4.asked(st, S.State.config(st), S.State.pfcp_seq(st), 0, S.BumpSeq{1})

def N4.ask_again(+st: S.State, +seq: U32, +resent: U32, more: Bool) -> N.GOut():
  match more:
    case True{}:
      N4.asked(st, S.State.config(st), seq, U32.add(resent, 1), S.Keep{})
    case False{}:
      N4.pause()

def N4.beat(+st: S.State, +seq: U32, resent: U32) -> N.GOut():
  (S.SetLink{S.Beating{seq, resent}}, [N.Pfcp{None{}, N4.heartbeat(Pf.Type.heartbeat_request(), S.N4.recovery(S.State.n4(st)), seq)}, N.TimerStart{None{}, S.N4.timer(), N4.t1_ms()}])

def N4.beat_again(+st: S.State, +seq: U32, +resent: U32, more: Bool) -> N.GOut():
  match more:
    case True{}:
      N4.beat(st, seq, U32.add(resent, 1))
    case False{}:
      N.Out.also(N4.start(st), [N.Note{F.Warn{}, "PFCP: no Heartbeat Response; association with the UPF lost"}])

# Timer 0 fired.
def N4.expired(+st: S.State, link: S.Link) -> N.GOut():
  match link:
    case S.Idle{}:
      (S.Keep{}, [])
    case S.Asking{seq, +resent}:
      N4.ask_again(st, seq, resent, U32.is_lt(resent, N4.n1()))
    case S.Paused{}:
      N4.start(st)
    case S.Up{}:
      N.Out.join((S.BumpSeq{1}, []), N4.beat(st, S.State.pfcp_seq(st), 0))
    case S.Beating{seq, +resent}:
      N4.beat_again(st, seq, resent, U32.is_lt(resent, N4.n1()))

def N4.fired(+st: S.State) -> N.GOut():
  N4.expired(st, S.N4.link(S.State.n4(st)))

def N4.assoc_answer(ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      (S.SetLink{S.Up{}}, [N.TimerStart{None{}, S.N4.timer(), N4.heartbeat_ms()}, N.Note{F.Info{}, "PFCP: association with the UPF up"}])
    case False{}:
      N4.pause()

def N4.assoc_seq(msg: Pf.Msg, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      N4.assoc_answer(N4.accepted(N4.cause(msg)))
    case False{}:
      N.Out.warn("PFCP: Association Setup Response for no pending request")

# An Association Setup Response answers the request outstanding, by its sequence number.
def N4.assoc_for(link: S.Link, +msg: Pf.Msg) -> N.GOut():
  match link:
    case S.Asking{seq, resent}:
      N4.assoc_seq(msg, U32.is_eq(seq, Pf.Msg.seq(msg)))
    case _:
      N.Out.warn("PFCP: Association Setup Response for no pending request")

def N4.assoc_response(+st: S.State, msg: Pf.Msg) -> N.GOut():
  N4.assoc_for(S.N4.link(S.State.n4(st)), msg)

def N4.alive_seq(ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      (S.SetLink{S.Up{}}, [N.TimerStart{None{}, S.N4.timer(), N4.heartbeat_ms()}])
    case False{}:
      (S.Keep{}, [])

# A Heartbeat Response answers the Heartbeat Request outstanding, by its sequence number.
def N4.alive_for(link: S.Link, +seq: U32) -> N.GOut():
  match link:
    case S.Beating{s, resent}:
      N4.alive_seq(U32.is_eq(s, seq))
    case _:
      (S.Keep{}, [])

def N4.alive(+st: S.State, msg: Pf.Msg) -> N.GOut():
  N4.alive_for(S.N4.link(S.State.n4(st)), Pf.Msg.seq(msg))

def N4.heartbeat_answer(+st: S.State, msg: Pf.Msg) -> N.GOut():
  (S.Keep{}, [N.Pfcp{None{}, N4.heartbeat(Pf.Type.heartbeat_response(), S.N4.recovery(S.State.n4(st)), Pf.Msg.seq(msg))}])

def Link.up(l: S.Link) -> Bool:
  match l:
    case S.Up{}:
      True{}
    case S.Beating{seq, resent}:
      True{}
    case _:
      False{}

def N4.up(st: S.State) -> Bool:
  Link.up(S.N4.link(S.State.n4(st)))
