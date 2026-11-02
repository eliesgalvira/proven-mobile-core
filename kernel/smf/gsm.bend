import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../nas/ie.bend as I
import ../nas/mm.bend as Mm
import ../nas/sm.bend as Sm
import ../nas/sm_ies.bend as Q
import ../nas/security.bend as Sec
import ../pfcp.bend as Pf
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../amf/ngap.bend as N
import ./n4.bend as Up

# PDU session establishment (TS 24.501 §6.4.1, TS 23.502 §4.3.2.2): one IPv4
# session per PDU session identity on the configured DNN and slice, set up at
# eUPF over N4 and at the gNB over N2, and released with its UE. Every outcome
# is a transaction and actions, like the UE procedures.

# 5GSM messages
# -------------

def Gsm.sm(psi: U32, pti: U32, mt: Sm.Sm.Type, fields: List<&2, I.Field>, opts: List<&2, I.Ie>) -> B.Bytes():
  Sm.Sm.write(Sm.Sm{psi, pti, mt, fields, opts})

def Gsm.reject(psi: U32, pti: U32, cause: U32) -> B.Bytes():
  Gsm.sm(psi, pti, Sm.EstablishmentReject{}, [I.FByte{cause}], [])

# Modification is not offered: #31, request rejected, unspecified.
def Gsm.modification_reject(psi: U32, pti: U32) -> B.Bytes():
  Gsm.sm(psi, pti, Sm.ModificationReject{}, [I.FByte{31}], [])

# The default QoS rule: QFI 1, precedence 255, one match-all packet filter in both directions.
def Gsm.default_rule() -> Q.Rule:
  Q.Rule{1, 6, 49, Q.Whole{[Q.Filter{49, 1, [Q.Comp{1, Q.PNone{}}]}]}, Q.Tail{255, 1}}

# Session-AMBR: 1 Gbit/s each way, in units of 1 Mbit/s.
def Gsm.ambr() -> B.Bytes():
  Q.Ambr.write(Q.Ambr{6, 1000, 6, 1000})

def Gsm.dns_opts(cfg: S.Cfg, wanted: Bool) -> List<&2, I.Ie>:
  match wanted:
    case True{}:
      [I.Ie{123, I.TlvE{}, 8, Q.Epco.write(Q.Epco{[Q.Container{13, I.LenBody{4, S.Cfg.dns(cfg)}}]})}]
    case False{}:
      []

# A UE that asked for IPv4v6 learns it got IPv4 only (#50).
def Gsm.type_opts(v4v6: Bool) -> List<&2, I.Ie>:
  match v4v6:
    case True{}:
      [I.Ie{89, I.Tv{1n}, 0, [50]}]
    case False{}:
      []

# PDU Session Establishment Accept: IPv4, SSC mode 1, the default rule, the
# AMBR, the UE's address, the DNS server if asked for.
def Gsm.accept(cfg: S.Cfg, psi: U32, pti: U32, ip: U32, dns: Bool, v4v6: Bool) -> B.Bytes():
  Gsm.sm(psi, pti, Sm.EstablishmentAccept{}, [I.FByte{17}, I.FLvE{I.LenBody{9, Q.Rules.write([Gsm.default_rule()])}}, I.FLv{I.LenBody{6, Gsm.ambr()}}], List.append(&2, I.Ie, Gsm.type_opts(v4v6), I.Ie{41, I.Tlv{}, 5, Q.PduAddr.write(Q.Ipv4{ip})} <> Gsm.dns_opts(cfg, dns)))

# DL NAS Transport carrying an N1 SM message for a PDU session.
def Gsm.dl_transport(psi: U32, +sm: B.Bytes()) -> B.Bytes():
  Mm.Mm.write(Mm.Mm{Mm.DlNasTransport{}, [I.FByte{1}, I.FLvE{I.LenBody{U32.from_nat(List.length(&2, U32, sm)), sm}}], [I.Ie{18, I.Tv{1n}, 0, [psi]}]})

def Gsm.dl(key: U32, ue: S.Ue, ctx: Sec.Nas.Ctx, psi: U32, sm: B.Bytes()) -> N.GOut():
  N.Out.dl(key, ue, ctx, Gsm.dl_transport(psi, sm))

# The N2 transfer: the session's AMBR, the N3 tunnel, IPv4, QoS flow 1 (5QI 9, ARP 8).
def Gsm.flow() -> G.QosFlowSetupRequestItem:
  G.QosFlowSetupRequestItem{Ap.IRoot{1}, G.QosFlowLevelQosParameters{G.QosCharacteristics_nonDynamic5QI{G.NonDynamic5QIDescriptor{Ap.IRoot{9}, None{}, None{}, None{}, None{}}}, G.AllocationAndRetentionPriority{8, Ap.Root{0}, Ap.Root{0}, None{}}, None{}, None{}, None{}, None{}}, None{}, None{}}

def Gsm.transfer(cfg: S.Cfg, teid: U32) -> B.Bytes():
  Ap.pack(G.PDUSessionResourceSetupRequestTransfer.write([N.Ngap.ie(130, Fr.Criticality.reject(), G.PDUSessionAggregateMaximumBitRate.write(G.PDUSessionAggregateMaximumBitRate{N.Ngap.gbps(), N.Ngap.gbps(), None{}}, 0n, [])), N.Ngap.ie(139, Fr.Criticality.reject(), G.UPTransportLayerInformation.write(G.UPTransportLayerInformation_gTPTunnel{G.GTPTunnel{Ap.unpack(S.Cfg.upf_n3(cfg)), B.write_u32(teid, []), None{}}}, 0n, [])), N.Ngap.ie(134, Fr.Criticality.reject(), G.PDUSessionType.write(Ap.Root{0}, 0n, [])), N.Ngap.ie(136, Fr.Criticality.reject(), G.QosFlowSetupRequestList.write([Gsm.flow()], 0n, []))], 0n, []))

# Allocation
# ----------
# UE addresses are the first free host of the pool after the gateway; the N3
# TEID and the local SEID come from entropy, never zero.

def Ip.nonzero(v: U32, zero: Bool) -> U32:
  match zero:
    case True{}:
      1
    case False{}:
      v

def Ip.word_at(entropy: B.Bytes(), n: Nat) -> U32:
  +v = N.Ngap.of_big(List.take(&2, U32, List.drop(&2, U32, entropy, n), 4n))
  Ip.nonzero(v, U32.is_eq(v, 0))

def Ip.teid(entropy: B.Bytes()) -> U32:
  Ip.word_at(entropy, 20n)

def Ip.seid(entropy: B.Bytes()) -> U32:
  Ip.word_at(entropy, 24n)

def Ip.next(candidate: U32, later: Unit -> Maybe<&2, U32>, used: Bool) -> Maybe<&2, U32>:
  match used:
    case True{}:
      later(Unit{})
    case False{}:
      Some{candidate}

def Ip.free_from(fuel: Nat, +candidate: U32, +sessions: Tb.Table(S.Session)) -> Maybe<&2, U32>:
  match fuel:
    case 0n:
      None{}
    case 1n+n:
      Ip.next(candidate, u => Ip.free_from(n, U32.add(candidate, 1), sessions), S.Sessions.has_ip(candidate, sessions))

def Ip.alloc_in(base: U32, +hosts: U32, sessions: Tb.Table(S.Session), ok: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Ip.free_from(U32.to_nat(U32.sub(hosts, 3)), U32.add(base, 2), sessions)
    case False{}:
      None{}

# The pool: base/prefix, with the network, gateway and broadcast addresses left out.
def Ip.alloc(+cfg: S.Cfg, sessions: Tb.Table(S.Session)) -> Maybe<&2, U32>:
  +prefix = N.Ngap.cap_byte(S.Cfg.prefix(cfg), 0n)
  Ip.alloc_in(N.Ngap.of_big(S.Cfg.pool(cfg)), U32.shln(1, U32.to_nat(U32.sub(32, U32.min(prefix, 30)))), sessions, U32.is_le(prefix, 30))

# Sessions in the state
# ---------------------

def Gsm.dels(victims: Tb.Table(S.Session)) -> S.Tx:
  match victims:
    case Nil{}:
      S.Keep{}
    case (k, t) <> more:
      S.Both{S.DelSession{k}, Gsm.dels(more)}

# Sessions forgotten, those eUPF knows deleted there, from sequence number seq.
def Gsm.forget(+victims: Tb.Table(S.Session), seq: U32) -> N.GOut():
  (S.Both{Gsm.dels(victims), S.BumpSeq{Up.N4.deletion_count(victims)}}, Up.N4.deletions(victims, seq))

# The one write of a session: it takes its place, and every live session it
# conflicts with (the same address, TEID, or PDU session of the UE) goes.
def Gsm.place(+st: S.State, +key: U32, +s: S.Session, seq: U32) -> N.GOut():
  N.Out.join((S.PutSession{key, s}, []), Gsm.forget(S.Sessions.evicted(key, s, S.State.sessions(st)), seq))

# The UE of a session, to answer it.
def Gsm.to_ue_ctx(key: U32, ue: S.Ue, psi: U32, sm: B.Bytes(), ctx: Maybe<&2, Sec.Nas.Ctx>) -> N.GOut():
  match ctx:
    case None{}:
      (S.Keep{}, [])
    case Some{c}:
      Gsm.dl(key, ue, c, psi, sm)

def Gsm.to_ue_m(key: U32, psi: U32, sm: B.Bytes(), m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, [])
    case Some{+ue}:
      Gsm.to_ue_ctx(key, ue, psi, sm, S.Phase.ctx(S.Ue.phase(ue)))

def Gsm.to_ue(st: S.State, +key: U32, psi: U32, sm: B.Bytes()) -> N.GOut():
  Gsm.to_ue_m(key, psi, sm, Tb.Table.get(S.Ue, key, S.State.ues(st)))

def Gsm.cancel(g: Maybe<&2, S.Guard>) -> List<&2, N.Act>:
  match g:
    case None{}:
      []
    case Some{guard}:
      [N.TimerCancel{S.Guard.timer(guard)}]

# A session given up: its UE told why, eUPF told, the row and guard gone.
def Gsm.abort(st: S.State, +skey: U32, +s: S.Session, pti: U32, cause: U32, seq: U32) -> N.GOut():
  N.Out.join(Gsm.to_ue(st, S.Session.ue(s), S.Session.psi(s), Gsm.reject(S.Session.psi(s), pti, cause)), N.Out.also(Gsm.forget([(skey, s)], seq), Gsm.cancel(S.SPhase.guard(S.Session.phase(s)))))

# Establishment
# -------------

# What a request checks out to: a 5GSM cause, or the session to create.
type Check is Data:
  Refuse{cause: U32}
  Go{v4v6: Bool, dns: Bool}

def Gsm.pick(ok: Bool, cause: U32, next: Check) -> Check:
  match ok:
    case True{}:
      next
    case False{}:
      Refuse{cause}

def Gsm.type_check(t: Maybe<&2, U32>, dns: Bool) -> Check:
  match t:
    case None{}:
      Go{False{}, dns}
    case Some{1}:
      Go{False{}, dns}
    case Some{3}:
      Go{True{}, dns}
    case Some{other}:
      Refuse{50}

def Gsm.dnn_ok(+cfg: S.Cfg, m: Maybe<&2, B.Bytes()>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{d}:
      B.bytes_eq(d, U32.from_nat(List.length(&2, U32, S.Cfg.dnn(cfg))) <> S.Cfg.dnn(cfg))

def Gsm.slice_ok(cfg: S.Cfg, m: Maybe<&2, B.Bytes()>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      U32.is_eq(N.Ngap.cap_byte(s, 0n), N.Ngap.cap_byte(S.Cfg.sst(cfg), 0n))

def Gsm.has_container(+id: U32, cs: List<&2, Q.Container>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Q.Container{i, lb} <> more:
      Bool.or(U32.is_eq(i, id), Gsm.has_container(id, more))

def Gsm.wants_dns(r: Q.Res(Q.Epco)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{Q.Epco{cs}}:
      Gsm.has_container(13, cs)

def Gsm.dns_asked(m: Maybe<&2, B.Bytes()>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{bs}:
      Gsm.wants_dns(Q.Epco.read(bs))

def Gsm.request_type_ok(m: Maybe<&2, U32>) -> Bool:
  match m:
    case Some{1}:
      True{}
    case _:
      False{}

# TS 24.501 §6.4.1.4.3: the identity must be one of a session (1 to 15), the
# request an initial one, the DNN and slice the configured ones, the type
# IPv4 (IPv4v6 is granted IPv4), and eUPF must be associated.
def Gsm.validate(+cfg: S.Cfg, +psi: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, up: Bool) -> Check:
  Gsm.pick(Bool.and(U32.is_lt(0, psi), U32.is_lt(psi, 16)), 95, Gsm.pick(Gsm.request_type_ok(I.Opts.t1(8, mm_opts)), 31, Gsm.pick(Gsm.dnn_ok(cfg, I.Opts.find(37, mm_opts)), 27, Gsm.pick(Gsm.slice_ok(cfg, I.Opts.find(34, mm_opts)), 70, Gsm.pick(up, 38, Gsm.type_check(I.Opts.t1(9, sm_opts), Gsm.dns_asked(I.Opts.find(123, sm_opts))))))))

# The PFCP Session Establishment Request goes out; the session waits for eUPF with its Accept ready.
def Gsm.create(+st: S.State, +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, +ip: U32, +entropy: B.Bytes(), v4v6: Bool, dns: Bool) -> N.GOut():
  +timer = S.State.next_timer(st)
  +seq = S.State.pfcp_seq(st)
  +teid = Ip.teid(entropy)
  +s : S.Session = S.Session{S.SId{key, psi, ip, teid}, S.SVar{[], seq, S.Creating{S.Guard{timer, 0}, pti, Gsm.accept(cfg, psi, pti, ip, dns, v4v6)}}}
  N.Out.join((S.Both{S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), ctx)}, S.Both{S.BumpTimer{}, S.BumpSeq{1}}}, [N.Pfcp{Up.N4.establish(cfg, Ip.seid(entropy), ip, teid, seq)}, N.TimerStart{timer, Up.N4.t1_ms()}]), Gsm.place(st, Ip.seid(entropy), s, U32.add(seq, 1)))

def Gsm.allocated(st: S.State, key: U32, ue: S.Ue, ctx: Sec.Nas.Ctx, cfg: S.Cfg, +psi: U32, +pti: U32, entropy: B.Bytes(), v4v6: Bool, dns: Bool, m: Maybe<&2, U32>) -> N.GOut():
  match m:
    case None{}:
      Gsm.dl(key, ue, ctx, psi, Gsm.reject(psi, pti, 26))
    case Some{ip}:
      Gsm.create(st, key, ue, ctx, cfg, psi, pti, ip, entropy, v4v6, dns)

def Gsm.checked(+st: S.State, key: U32, ue: S.Ue, ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, entropy: B.Bytes(), c: Check) -> N.GOut():
  match c:
    case Refuse{cause}:
      Gsm.dl(key, ue, ctx, psi, Gsm.reject(psi, pti, cause))
    case Go{v4v6, dns}:
      Gsm.allocated(st, key, ue, ctx, cfg, psi, pti, entropy, v4v6, dns, Ip.alloc(cfg, S.State.sessions(st)))

def Gsm.with_cfg(+st: S.State, key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, +psi: U32, pti: U32, mm_opts: List<&2, I.Ie>, sm_opts: List<&2, I.Ie>, entropy: B.Bytes(), cfg: Maybe<&2, S.Cfg>) -> N.GOut():
  match cfg:
    case None{}:
      N.Out.verified(key, ue, ctx, "5GSM: no configuration")
    case Some{+c}:
      Gsm.checked(st, key, ue, ctx, c, psi, pti, entropy, Gsm.validate(c, psi, mm_opts, sm_opts, Up.N4.up(st)))

def Gsm.establish(+st: S.State, key: U32, ue: S.Ue, ctx: Sec.Nas.Ctx, psi: U32, pti: U32, mm_opts: List<&2, I.Ie>, sm_opts: List<&2, I.Ie>, entropy: B.Bytes()) -> N.GOut():
  Gsm.with_cfg(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy, S.State.config(st))

# The N1 SM message of a UL NAS Transport, by type.
def Gsm.message(st: S.State, key: U32, ue: S.Ue, ctx: Sec.Nas.Ctx, mm_opts: List<&2, I.Ie>, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Sm.Sm>) -> N.GOut():
  match r:
    case Fail{e}:
      N.Out.verified(key, ue, ctx, "5GSM: message not understood")
    case Done{Sm.Sm{+psi, +pti, mt, fields, opts}}:
      match mt:
        case Sm.EstablishmentRequest{}:
          Gsm.establish(st, key, ue, ctx, psi, pti, mm_opts, opts, entropy)
        case Sm.ModificationRequest{}:
          Gsm.dl(key, ue, ctx, psi, Gsm.modification_reject(psi, pti))
        case _:
          N.Out.verified(key, ue, ctx, "5GSM: message not expected")

def Gsm.n1(st: S.State, key: U32, ue: S.Ue, ctx: Sec.Nas.Ctx, mm_opts: List<&2, I.Ie>, entropy: B.Bytes(), container: B.Bytes(), n1: Bool) -> N.GOut():
  match n1:
    case True{}:
      Gsm.message(st, key, ue, ctx, mm_opts, entropy, Sm.Sm.read(container))
    case False{}:
      N.Out.verified(key, ue, ctx, "5GMM: payload container not N1 SM information")

# UL NAS Transport from a registered UE, verified.
def Gsm.ul_transport(st: S.State, key: U32, ue: S.Ue, ctx: Sec.Nas.Ctx, +fields: List<&2, I.Field>, opts: List<&2, I.Ie>, entropy: B.Bytes()) -> N.GOut():
  Gsm.n1(st, key, ue, ctx, opts, entropy, I.Fields.lve2(fields), U32.is_eq(I.Fields.byte1(fields), 1))

# eUPF's answers
# --------------

# Session Establishment accepted: the UP SEID is kept and the gNB is asked to
# set the session up, the Accept inside; the same guard bounds the wait.
def Gsm.setup_ue(st: S.State, +skey: U32, +s: S.Session, +guard: S.Guard, pti: U32, accept: B.Bytes(), +up_seid: B.Bytes(), +ue: S.Ue, ctx: Maybe<&2, Sec.Nas.Ctx>, cfg: Maybe<&2, S.Cfg>) -> N.GOut():
  match ctx cfg:
    case Some{c} Some{+cf}:
      +p : Sec.Nas.Protected = Sec.Nas.protect(c, Sec.Ciphered{}, Gsm.dl_transport(S.Session.psi(s), accept))
      (S.Both{S.Rephase{S.Session.ue(s), S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))}, S.Revar{skey, S.SVar{up_seid, S.Session.seq(s), S.Setting{S.Guard{S.Guard.timer(guard), 0}, pti}}}}, [N.PduSetup{S.Ue.assoc(ue), S.Ue.stream(ue), S.Session.ue(s), S.Ue.ran_id(ue), S.Session.psi(s), S.Cfg.sst(cf), Sec.Nas.Protected.msg(p), Gsm.transfer(cf, S.Session.teid(s))}, N.TimerStart{S.Guard.timer(guard), Up.N4.t1_ms()}])
    case _ _:
      Gsm.forget([(skey, S.Session.with_var(s, S.SVar{up_seid, S.Session.seq(s), S.Active{}}))], S.State.pfcp_seq(st))

def Gsm.setup(+st: S.State, skey: U32, +s: S.Session, guard: S.Guard, pti: U32, accept: B.Bytes(), up_seid: B.Bytes(), m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      Gsm.forget([(skey, S.Session.with_var(s, S.SVar{up_seid, S.Session.seq(s), S.Active{}}))], S.State.pfcp_seq(st))
    case Some{+ue}:
      Gsm.setup_ue(st, skey, s, guard, pti, accept, up_seid, ue, S.Phase.ctx(S.Ue.phase(ue)), S.State.config(st))

# Refused, or no UP SEID: the UE is told (#38), nothing of the session remains.
def Gsm.established_as(+st: S.State, skey: U32, +s: S.Session, guard: S.Guard, pti: U32, accept: B.Bytes(), up: Maybe<&2, B.Bytes()>, ok: Bool) -> N.GOut():
  match up ok:
    case Some{up_seid} True{}:
      Gsm.setup(st, skey, s, guard, pti, accept, up_seid, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)))
    case _ _:
      Gsm.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st))

def Gsm.established_phase(st: S.State, skey: U32, s: S.Session, +msg: Pf.Msg, p: S.SPhase) -> N.GOut():
  match p:
    case S.Creating{guard, pti, accept}:
      Gsm.established_as(st, skey, s, guard, pti, accept, Up.N4.up_seid(msg), Up.N4.accepted(Up.N4.cause(msg)))
    case _:
      N.Out.warn("PFCP: Session Establishment Response for a session not being created")

def Gsm.established(st: S.State, msg: Pf.Msg, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> N.GOut():
  match m:
    case None{}:
      N.Out.warn("PFCP: Session Establishment Response for no pending request")
    case Some{(skey, +s)}:
      Gsm.established_phase(st, skey, s, msg, S.Session.phase(s))

# Session Modification accepted: active; refused: the session goes, silently.
def Gsm.modified_as(st: S.State, +skey: U32, +s: S.Session, guard: S.Guard, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      (S.Revar{skey, S.SVar{S.Session.up_seid(s), S.Session.seq(s), S.Active{}}}, [N.TimerCancel{S.Guard.timer(guard)}, N.Note{F.Info{}, "5GSM: PDU session active"}])
    case False{}:
      N.Out.also(Gsm.forget([(skey, s)], S.State.pfcp_seq(st)), [N.TimerCancel{S.Guard.timer(guard)}, N.Note{F.Warn{}, "PFCP: Session Modification refused; session released"}])

def Gsm.modified_phase(st: S.State, skey: U32, s: S.Session, msg: Pf.Msg, p: S.SPhase) -> N.GOut():
  match p:
    case S.Modifying{guard}:
      Gsm.modified_as(st, skey, s, guard, Up.N4.accepted(Up.N4.cause(msg)))
    case _:
      N.Out.warn("PFCP: Session Modification Response for a session not being modified")

def Gsm.modified(st: S.State, msg: Pf.Msg, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> N.GOut():
  match m:
    case None{}:
      N.Out.warn("PFCP: Session Modification Response for no pending request")
    case Some{(skey, +s)}:
      Gsm.modified_phase(st, skey, s, msg, S.Session.phase(s))

def Gsm.pfcp_k6(+st: S.State, +msg: Pf.Msg, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gsm.modified(st, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))
    case False{}:
      N.Out.warn("PFCP: message not handled")

def Gsm.pfcp_k5(+st: S.State, +msg: Pf.Msg, +kind: U32, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gsm.established(st, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))
    case False{}:
      Gsm.pfcp_k6(st, msg, U32.is_eq(kind, 53))

def Gsm.pfcp_k4(st: S.State, msg: Pf.Msg, +kind: U32, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      (S.Keep{}, [])
    case False{}:
      Gsm.pfcp_k5(st, msg, kind, U32.is_eq(kind, 51))

def Gsm.pfcp_k3(st: S.State, +msg: Pf.Msg, +kind: U32, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Up.N4.assoc_response(msg)
    case False{}:
      Gsm.pfcp_k4(st, msg, kind, U32.is_eq(kind, 55))

def Gsm.pfcp_k2(st: S.State, msg: Pf.Msg, +kind: U32, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      (S.Keep{}, [])
    case False{}:
      Gsm.pfcp_k3(st, msg, kind, U32.is_eq(kind, 6))

def Gsm.pfcp_k1(+st: S.State, +msg: Pf.Msg, +kind: U32, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Up.N4.heartbeat_answer(st, msg)
    case False{}:
      Gsm.pfcp_k2(st, msg, kind, U32.is_eq(kind, 2))

def Gsm.pfcp_msg(st: S.State, r: B.Read(Pf.Msg)) -> N.GOut():
  match r:
    case Fail{e}:
      N.Out.warn("PFCP: message not decodable")
    case Done{(+msg, rest)}:
      +kind = Pf.Msg.kind(msg)
      Gsm.pfcp_k1(st, msg, kind, U32.is_eq(kind, 1))

# A PFCP datagram from eUPF.
def Gsm.pfcp_data(st: S.State, bytes: B.Bytes()) -> N.GOut():
  Gsm.pfcp_msg(st, Pf.Msg.read(bytes))

# The gNB's answer
# ----------------

# The gNB's tunnel from the response transfer: a four-octet address and a TEID.
def Gsm.tunnel_if(teid: U32, addr: B.Bytes(), ok: Bool) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  match ok:
    case True{}:
      Some{(teid, addr)}
    case False{}:
      None{}

def Gsm.tunnel_v4(teid: U32, +addr: B.Bytes()) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  Gsm.tunnel_if(teid, addr, Nat.is_eq(List.length(&2, U32, addr), 4n))

def Gsm.tunnel_up(up: G.UPTransportLayerInformation) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  match up:
    case G.UPTransportLayerInformation_gTPTunnel{G.GTPTunnel{addr, teid, x}}:
      Gsm.tunnel_v4(N.Ngap.of_big(teid), Ap.pack(addr))
    case _:
      None{}

def Gsm.tunnel_dl(dl: G.QosFlowPerTNLInformation) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  match dl:
    case G.QosFlowPerTNLInformation{up, flows, x}:
      Gsm.tunnel_up(up)

def Gsm.tunnel(t: G.PDUSessionResourceSetupResponseTransfer) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  match t:
    case G.PDUSessionResourceSetupResponseTransfer{dl, add, sec, failed, x}:
      Gsm.tunnel_dl(dl)

def Gsm.tunnel_of(r: Ap.Rd(G.PDUSessionResourceSetupResponseTransfer)) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  match r:
    case Fail{e}:
      None{}
    case Done{(t, c)}:
      Gsm.tunnel(t)

# eUPF is told the gNB's tunnel; the same guard bounds the wait.
def Gsm.modify(st: S.State, +skey: U32, +s: S.Session, +guard: S.Guard, pti: U32, +seq: U32, tunnel: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>) -> N.GOut():
  match tunnel:
    case None{}:
      Gsm.abort(st, skey, s, pti, 26, seq)
    case Some{(gnb_teid, gnb_addr)}:
      (S.Both{S.Revar{skey, S.SVar{S.Session.up_seid(s), seq, S.Modifying{S.Guard{S.Guard.timer(guard), 0}}}}, S.BumpSeq{1}}, [N.Pfcp{Up.N4.modify(S.Session.up_seid(s), gnb_teid, gnb_addr, seq)}, N.TimerStart{S.Guard.timer(guard), Up.N4.t1_ms()}])

def Gsm.set_up_phase(st: S.State, skey: U32, s: S.Session, transfer: B.Bytes(), seq: U32, p: S.SPhase) -> N.GOut():
  match p:
    case S.Setting{guard, pti}:
      Gsm.modify(st, skey, s, guard, pti, seq, Gsm.tunnel_of(G.PDUSessionResourceSetupResponseTransfer.read(Ap.Cur{0n, Ap.unpack(transfer)})))
    case _:
      N.Out.warn("NGAP: PDU session set up at the gNB while not being set up")

def Gsm.set_up(st: S.State, transfer: B.Bytes(), seq: U32, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> N.GOut():
  match m:
    case None{}:
      N.Out.warn("NGAP: PDU session set up at the gNB for no session")
    case Some{(skey, +s)}:
      Gsm.set_up_phase(st, skey, s, transfer, seq, S.Session.phase(s))

def Gsm.set_ups(+st: S.State, +key: U32, items: G.PDUSessionResourceSetupListSURes(), +seq: U32) -> N.GOut():
  match items:
    case Nil{}:
      (S.Keep{}, [])
    case G.PDUSessionResourceSetupItemSURes{psi, transfer, x} <> more:
      N.Out.join(N.Out.also((S.BumpSeq{1}, []), []), N.Out.join(Gsm.set_up(st, transfer, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st))), Gsm.set_ups(st, key, more, U32.add(seq, 1))))

def Gsm.failed_phase(st: S.State, skey: U32, s: S.Session, seq: U32, p: S.SPhase) -> N.GOut():
  match p:
    case S.Setting{guard, pti}:
      Gsm.abort(st, skey, s, pti, 26, seq)
    case _:
      N.Out.warn("NGAP: PDU session failed at the gNB while not being set up")

def Gsm.failed(st: S.State, seq: U32, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> N.GOut():
  match m:
    case None{}:
      N.Out.warn("NGAP: PDU session failed at the gNB for no session")
    case Some{(skey, +s)}:
      Gsm.failed_phase(st, skey, s, seq, S.Session.phase(s))

def Gsm.faileds(+st: S.State, +key: U32, items: G.PDUSessionResourceFailedToSetupListSURes(), +seq: U32) -> N.GOut():
  match items:
    case Nil{}:
      (S.Keep{}, [])
    case G.PDUSessionResourceFailedToSetupItemSURes{psi, transfer, x} <> more:
      N.Out.join((S.BumpSeq{1}, []), N.Out.join(Gsm.failed(st, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st))), Gsm.faileds(st, key, more, U32.add(seq, 1))))

def Gsm.list_or(-A: Data, m: Maybe<&2, List<&2, A>>) -> List<&2, A>:
  match m:
    case None{}:
      []
    case Some{xs}:
      xs

# Each session the response names: set up at the gNB, or failed there; one
# PFCP sequence number is spent per session named.
def Gsm.results(+st: S.State, +key: U32, +oks: G.PDUSessionResourceSetupListSURes(), fails: G.PDUSessionResourceFailedToSetupListSURes()) -> N.GOut():
  N.Out.join(Gsm.set_ups(st, key, oks, S.State.pfcp_seq(st)), Gsm.faileds(st, key, fails, U32.add(S.State.pfcp_seq(st), U32.from_nat(List.length(&2, G.PDUSessionResourceSetupItemSURes, oks)))))

def Gsm.setup_response_ue(st: S.State, assoc: U32, key: U32, oks: G.PDUSessionResourceSetupListSURes(), fails: G.PDUSessionResourceFailedToSetupListSURes(), m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{ue}:
      Gsm.results(st, key, oks, fails)

def Gsm.owner_if(ue: S.Ue, ok: Bool) -> Maybe<&2, S.Ue>:
  match ok:
    case True{}:
      Some{ue}
    case False{}:
      None{}

def Gsm.owner_of(m: Maybe<&2, S.Ue>, assoc: U32, ran: B.Bytes()) -> Maybe<&2, S.Ue>:
  match m:
    case None{}:
      None{}
    case Some{+ue}:
      Gsm.owner_if(ue, Bool.and(U32.is_eq(S.Ue.assoc(ue), assoc), B.bytes_eq(S.Ue.ran_id(ue), ran)))

def Gsm.setup_response(+st: S.State, +assoc: U32, v: V.PDUSessionResourceSetupResponse.View) -> N.GOut():
  match v:
    case V.PDUSessionResourceSetupResponse.View{amf_ue_ngap_id, ran_ue_ngap_id, oks, fails, diagnostics, uli}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Gsm.setup_response_ue(st, assoc, key, Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), Gsm.list_or(G.PDUSessionResourceFailedToSetupItemSURes, fails), Gsm.owner_of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran_ue_ngap_id))

def Gsm.setup_response_of_view(st: S.State, assoc: U32, r: Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Gsm.setup_response(st, assoc, v)

# Guard timers
# ------------

# No answer in time: before the Accept went out the UE is told (#38); after
# it, the session is released silently.
def Gsm.expired(+st: S.State, +skey: U32, +s: S.Session, +p: S.SPhase) -> N.GOut():
  match p:
    case S.Creating{guard, pti, accept}:
      Gsm.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st))
    case S.Setting{guard, pti}:
      Gsm.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st))
    case S.Modifying{guard}:
      N.Out.also(Gsm.forget([(skey, s)], S.State.pfcp_seq(st)), [N.Note{F.Warn{}, "PFCP: no Session Modification Response; session released"}])
    case S.Active{}:
      (S.Keep{}, [])

def Gsm.fired(st: S.State, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, [])
    case Some{(skey, +s)}:
      Gsm.expired(st, skey, s, S.Session.phase(s))
