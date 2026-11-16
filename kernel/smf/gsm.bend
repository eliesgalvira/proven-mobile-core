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
# the UPF over N4 and at the gNB over N2, and released with its UE. Every outcome
# is a transaction and actions, like the UE procedures.

# 5GSM messages
# -------------

def Gsm.sm(psi: U32, pti: U32, mt: Sm.Sm.Type, fields: List<&2, I.Field>, opts: List<&2, I.Ie>) -> B.Bytes():
  Sm.Sm.write(Sm.Sm{psi, pti, mt, fields, opts})

def Gsm.reject(psi: U32, pti: U32, cause: U32) -> B.Bytes():
  Gsm.sm(psi, pti, Sm.EstablishmentReject{}, [I.FByte{cause}], [])

# A session released by the network: no transaction (TS 24.501 §6.3.3.2), #26.
def Gsm.release_command(psi: U32) -> B.Bytes():
  Gsm.sm(psi, 0, Sm.ReleaseCommand{}, [I.FByte{26}], [])

# Modification is not offered: #31, request rejected, unspecified.
def Gsm.modification_reject(psi: U32, pti: U32) -> B.Bytes():
  Gsm.sm(psi, pti, Sm.ModificationReject{}, [I.FByte{31}], [])

# The default QoS rule: QFI 1, precedence 255, one match-all packet filter in both directions.
def Gsm.default_rule() -> Q.Rule:
  Q.Rule{1, 6, 49, Q.Whole{[Q.Filter{49, 1, [Q.Comp{1, Q.PNone{}}]}]}, Q.Tail{255, 1}}

# Session-AMBR: 1 Gbit/s each way, in units of 1 Mbit/s.
def Gsm.ambr() -> B.Bytes():
  Q.Ambr.write(Q.Ambr{6, 1000, 6, 1000})

def Gsm.rule_filters(r: Q.Rule) -> Q.RuleFilters:
  match r:
    case Q.Rule{qri, len, op, filters, tail}:
      filters

def Gsm.filter_count(rs: List<&2, Q.Rule>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case r <> more:
      Nat.add(Q.RuleFilters.count(Gsm.rule_filters(r)), Gsm.filter_count(more))

def Gsm.rules_bounded(r: B.Res(List<&2, Q.Rule>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{rs}:
      Nat.is_le(Gsm.filter_count(rs), 16n)

# The QoS rules of an Accept, read as the UE reads them, hold at most sixteen
# packet filters (GHSA-g97g-v8mh-wg24).
def Gsm.accept_bounded(m: Sm.Sm) -> Bool:
  Gsm.rules_bounded(Q.Rules.read(I.Fields.lve2(Sm.Sm.fields(m))))

def Gsm.phase_bounded(p: S.SPhase) -> Bool:
  match p:
    case S.Creating{guard, pti, accept, request}:
      Gsm.accept_bounded(accept)
    case _:
      True{}

# Every session being created holds an Accept within the bound.
def Gsm.bounded(ss: Tb.Table(S.Session)) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case (k, t) <> more:
      Bool.and(Gsm.phase_bounded(S.Session.phase(t)), Gsm.bounded(more))

# The ePCO containers of an Accept: the DNS server, when asked for.
def Gsm.epco_containers(cfg: S.Cfg, wanted: Bool) -> List<&2, Q.Container>:
  match wanted:
    case True{}:
      +dns = S.Cfg.dns(cfg)
      [Q.Container{13, I.LenBody{U32.from_nat(List.length(&2, U32, dns)), dns}}]
    case False{}:
      []

def Gsm.has_container(+id: U32, cs: List<&2, Q.Container>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Q.Container{i, lb} <> more:
      Bool.or(U32.is_eq(i, id), Gsm.has_container(id, more))

def Gsm.ids_unique(cs: List<&2, Q.Container>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Q.Container{+id, lb} <> +more:
      Bool.and(Bool.not(Gsm.has_container(id, more)), Gsm.ids_unique(more))

def Gsm.epco_opts(cs: List<&2, Q.Container>) -> List<&2, I.Ie>:
  match cs:
    case Nil{}:
      []
    case +c <> +more:
      [I.Ie{123, I.TlvE{}, U32.from_nat(Q.Epco.size(Q.Epco{c <> more})), Q.Epco.write(Q.Epco{c <> more})}]

def Gsm.dns_opts(cfg: S.Cfg, wanted: Bool) -> List<&2, I.Ie>:
  Gsm.epco_opts(Gsm.epco_containers(cfg, wanted))

# A UE that asked for IPv4v6 learns it got IPv4 only (#50).
def Gsm.type_opts(v4v6: Bool) -> List<&2, I.Ie>:
  match v4v6:
    case True{}:
      [I.Ie{89, I.Tv{1n}, 0, [50]}]
    case False{}:
      []

# PDU Session Establishment Accept: IPv4, SSC mode 1, the default rule, the
# AMBR, the UE's address, the DNS server if asked for.
def Gsm.accept(cfg: S.Cfg, psi: U32, pti: U32, ip: U32, dns: Bool, v4v6: Bool) -> Sm.Sm:
  Sm.Sm{psi, pti, Sm.EstablishmentAccept{}, [I.FByte{17}, I.FLvE{I.LenBody{9, Q.Rules.write([Gsm.default_rule()])}}, I.FLv{I.LenBody{6, Gsm.ambr()}}], List.append(&2, I.Ie, Gsm.type_opts(v4v6), I.Ie{41, I.Tlv{}, 5, Q.PduAddr.write(Q.Ipv4{ip})} <> Gsm.dns_opts(cfg, dns))}

# DL NAS Transport carrying an N1 SM message for a PDU session.
def Gsm.dl_transport(psi: U32, +sm: B.Bytes()) -> B.Bytes():
  Mm.Mm.write(Mm.Mm{Mm.DlNasTransport{}, [I.FByte{1}, I.FLvE{I.LenBody{U32.from_nat(List.length(&2, U32, sm)), sm}}], [I.Ie{18, I.Tv{1n}, 0, [psi]}]})

def Gsm.dl(key: U32, ue: S.Ue, ctx: Sec.Nas.Ctx, psi: U32, sm: B.Bytes()) -> N.GOut():
  N.Out.dl(key, ue, ctx, Gsm.dl_transport(psi, sm))

# The N2 transfer: the session's AMBR, the N3 tunnel, the IEs given, IPv4,
# QoS flow 1 (5QI 9, ARP priority 8: a constrained INTEGER is held as its
# offset from the lower bound, 1 here, so 7).
def Gsm.flow() -> G.QosFlowSetupRequestItem:
  G.QosFlowSetupRequestItem{Ap.IRoot{1}, G.QosFlowLevelQosParameters{G.QosCharacteristics_nonDynamic5QI{G.NonDynamic5QIDescriptor{Ap.IRoot{9}, None{}, None{}, None{}, None{}}}, G.AllocationAndRetentionPriority{7, Ap.Root{0}, Ap.Root{0}, None{}}, None{}, None{}, None{}, None{}}, None{}, None{}}

def Gsm.transfer_with(cfg: S.Cfg, teid: U32, more: List<&2, Fr.Ie>) -> B.Bytes():
  Ap.pack(G.PDUSessionResourceSetupRequestTransfer.write(N.Ngap.ie(G.Id.PDUSessionAggregateMaximumBitRate(), Fr.Criticality.reject(), G.PDUSessionAggregateMaximumBitRate.write(G.PDUSessionAggregateMaximumBitRate{N.Ngap.gbps(), N.Ngap.gbps(), None{}}, 0n, [])) <> N.Ngap.ie(G.Id.UL_NGU_UP_TNLInformation(), Fr.Criticality.reject(), G.UPTransportLayerInformation.write(G.UPTransportLayerInformation_gTPTunnel{G.GTPTunnel{Ap.unpack(S.Cfg.upf_n3(cfg)), B.write_u32(teid, []), None{}}}, 0n, [])) <> List.append(&2, Fr.Ie, more, [N.Ngap.ie(G.Id.PDUSessionType(), Fr.Criticality.reject(), G.PDUSessionType.write(Ap.Root{0}, 0n, [])), N.Ngap.ie(G.Id.QosFlowSetupRequestList(), Fr.Criticality.reject(), G.QosFlowSetupRequestList.write([Gsm.flow()], 0n, []))]), 0n, []))

def Gsm.transfer(cfg: S.Cfg, teid: U32) -> B.Bytes():
  Gsm.transfer_with(cfg, teid, [])

# Allocation
# ----------
# UE addresses are the first free host of the pool after the gateway. The N3
# TEID and the local SEID are words of entropy, from bytes 20 and 24 on and
# around: the first that is not zero and that no session holds (Ip.draw). A
# collision draws again; none is ever evicted.

def Ip.around(+entropy: B.Bytes(), +n: Nat) -> B.Bytes():
  List.append(&2, U32, List.drop(&2, U32, entropy, n), List.take(&2, U32, entropy, n))

# What is drawn: an uplink TEID, or a local SEID made even (S.Ids).
type Draw is Data:
  Teid{}
  Seid{}

def Draw.word(d: Draw, +w: U32) -> U32:
  match d:
    case Teid{}:
      w
    case Seid{}:
      U32.and(4294967294, w)

def Draw.taken(d: Draw, +v: U32, sessions: Tb.Table(S.Session)) -> Bool:
  match d:
    case Teid{}:
      S.Sessions.holds(S.Teid{}, v, sessions)
    case Seid{}:
      Tb.Table.has(S.Session, v, sessions)

def Ip.draw(+d: Draw, +sessions: Tb.Table(S.Session), words: B.Bytes()) -> Maybe<&2, U32>:
  match words:
    case a <> b <> c <> d0 <> more:
      +k = Draw.word(d, N.Ngap.of_big([a, b, c, d0]))
      Tb.Table.hit(U32, k, Ip.draw(d, sessions, more), Bool.not(Bool.or(U32.is_eq(k, 0), Draw.taken(d, k, sessions))))
    case _:
      None{}

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
      Ip.next(candidate, u => Ip.free_from(n, U32.add(candidate, 1), sessions), S.Sessions.holds(S.Ip{}, candidate, sessions))

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

# The one write of a session: a session it conflicts with is deleted first,
# then it takes its place. The address, TEID and SEID are drawn free, so that
# is only one of the UE's under the same PDU session identity.
def Gsm.place(+st: S.State, +key: U32, +s: S.Session, seq: U32) -> N.GOut():
  N.Out.join(Up.N4.deletions(S.Sessions.evicted(key, s, S.State.sessions(st)), seq), (S.PutSession{key, s}, []))

# What a UE is told of a session given up: before the Accept went out, the
# 5GSM message given, in DL NAS Transport; after it, the gNB is told to
# release the session's resources, PDU Session Release Command inside
# (TS 23.502 §4.3.4.2).
type Tell is Data:
  Reply{sm: B.Bytes()}
  Release{}

# PDU Session Release Command, #26, protected for the UE.
def Gsm.release_nas(ctx: Sec.Nas.Ctx, +psi: U32) -> Sec.Nas.Protected:
  Sec.Nas.protect(ctx, Sec.Ciphered{}, Gsm.dl_transport(psi, Gsm.release_command(psi)))

# What the UE is told under ctx: the 5GSM message given, in DL NAS
# Transport, or the PDU Session Resource Release Command to its gNB, the NAS
# message inside.
def Gsm.told(+key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, +psi: U32, t: Tell) -> N.Told():
  match t:
    case Reply{sm}:
      N.Out.told_dl(key, ue, ctx, Gsm.dl_transport(psi, sm))
    case Release{}:
      +p : Sec.Nas.Protected = Gsm.release_nas(ctx, psi)
      (Sec.Nas.Protected.ctx(p), [N.PduRelease{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), psi, Sec.Nas.Protected.msg(p)}])

def Gsm.n2_release(+key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, +psi: U32) -> N.GOut():
  N.Out.written(key, ue, Gsm.told(key, ue, ctx, psi, Release{}))

# The first action tells the UE's gNB to release the session, the PDU Session
# Release Command inside, protected under ctx.
def Gsm.tells_gnb(+ue: S.Ue, +ctx: Sec.Nas.Ctx, +s: S.Session, +acts: List<&2, N.Act>) -> Type:
  Sigma<&2, &2, List<&2, N.Act>, post => {acts == List.append(&2, N.Act, N.Out.acts(Gsm.n2_release(S.Session.ue(s), ue, ctx, S.Session.psi(s))), post) : List<&2, N.Act>}>

# What a procedure does while the UE's NAS context runs through it: the
# context it leaves, and its outcome with that context not yet written.
def Gsm.Item() -> Data:
  Sigma<&2, &2, Maybe<&2, Sec.Nas.Ctx>, _ => N.GOut()>

# One part, then the rest under the context it leaves.
def Gsm.after(+o: N.GOut(), r: Gsm.Item()) -> Gsm.Item():
  match r:
    case (c, o2):
      (c, N.Out.join(o, o2))

def Gsm.then(r: Gsm.Item(), rest: Maybe<&2, Sec.Nas.Ctx> -> Gsm.Item()) -> Gsm.Item():
  match r:
    case (c, +o):
      Gsm.after(o, rest(c))

# The context left, written to the UE's phase.
def Gsm.ctx_written(+key: U32, +ue: S.Ue, c: Maybe<&2, Sec.Nas.Ctx>) -> N.GOut():
  match c:
    case None{}:
      (S.Keep{}, [])
    case Some{x}:
      (S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), x)}, [])

def Gsm.Item.out(r: Gsm.Item()) -> N.GOut():
  match r:
    case (c, o):
      o

def Gsm.settled(+key: U32, +ue: S.Ue, r: Gsm.Item()) -> N.GOut():
  match r:
    case (c, o):
      N.Out.join(Gsm.ctx_written(key, ue, c), o)

# What f does under the NAS context the UE's phase holds, the context it
# leaves written to the phase once; with none, nothing is written.
def Gsm.under_ctx(+key: U32, +ue: S.Ue, f: Maybe<&2, Sec.Nas.Ctx> -> Gsm.Item(), c: Maybe<&2, Sec.Nas.Ctx>) -> N.GOut():
  match c:
    case None{}:
      Gsm.Item.out(f(None{}))
    case Some{x}:
      Gsm.settled(key, ue, f(Some{x}))

def Gsm.under(+key: U32, +ue: S.Ue, f: Maybe<&2, Sec.Nas.Ctx> -> Gsm.Item()) -> N.GOut():
  Gsm.under_ctx(key, ue, f, S.Phase.ctx(S.Ue.phase(ue)))

def Gsm.told_then(r: N.Told(), +o: N.GOut()) -> Gsm.Item():
  match r:
    case (c, acts):
      (Some{c}, N.Out.join((S.Keep{}, acts), o))

# A session given up: its UE told under the context c, when it holds one,
# the session deleted at the UPF.
def Gsm.give_up_in(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, t: Tell, +seq: U32, c: Maybe<&2, Sec.Nas.Ctx>) -> Gsm.Item():
  match c:
    case None{}:
      (None{}, Up.N4.deletions([(skey, s)], seq))
    case Some{x}:
      Gsm.told_then(Gsm.told(key, ue, x, S.Session.psi(s), t), Up.N4.deletions([(skey, s)], seq))

def Gsm.give_up_ue(+skey: U32, +s: S.Session, t: Tell, +seq: U32, m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      Up.N4.deletions([(skey, s)], seq)
    case Some{+ue}:
      Gsm.under(S.Session.ue(s), ue, c => Gsm.give_up_in(S.Session.ue(s), ue, skey, s, t, seq, c))

def Gsm.give_up(st: S.State, +skey: U32, +s: S.Session, t: Tell, +seq: U32) -> N.GOut():
  Gsm.give_up_ue(skey, s, t, seq, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)))

# Before the Accept went out, the UE is refused the session.
def Gsm.abort(st: S.State, skey: U32, +s: S.Session, pti: U32, cause: U32, seq: U32) -> N.GOut():
  Gsm.give_up(st, skey, s, Reply{Gsm.reject(S.Session.psi(s), pti, cause)}, seq)

# After it, the session is released (TS 24.501 §6.3.3).
def Gsm.drop(st: S.State, skey: U32, +s: S.Session, seq: U32) -> N.GOut():
  Gsm.give_up(st, skey, s, Release{}, seq)

# Establishment
# -------------

# What a request checks out to: a 5GSM cause, or the session to create.
type Check is Data:
  Refuse{cause: U32}
  Go{v4v6: Bool, dns: Bool, ip: U32, teid: U32, seid: U32}

# The first check a request fails, as its 5GSM cause.
def Gsm.pick(ok: Bool, cause: U32, next: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      next
    case False{}:
      Some{cause}

# A free address of the pool, a free TEID and a free SEID, or #26.
def Gsm.grant(v4v6: Bool, dns: Bool, ip: Maybe<&2, U32>, teid: Maybe<&2, U32>, seid: Maybe<&2, U32>) -> Check:
  match ip teid seid:
    case Some{a} Some{t} Some{k}:
      Go{v4v6, dns, a, t, k}
    case _ _ _:
      Refuse{26}

# The address, TEID and SEID are drawn only for a request that passed.
def Gsm.allocate(refused: Maybe<&2, U32>, v4v6: Bool, dns: Bool, +cfg: S.Cfg, +sessions: Tb.Table(S.Session), +entropy: B.Bytes()) -> Check:
  match refused:
    case Some{cause}:
      Refuse{cause}
    case None{}:
      Gsm.grant(v4v6, dns, Ip.alloc(cfg, sessions), Ip.draw(Teid{}, sessions, Ip.around(entropy, 20n)), Ip.draw(Seid{}, sessions, Ip.around(entropy, 24n)))

# IPv4 (1) or IPv4v6 (3), granted IPv4; another type is refused (#50).
def Gsm.type_ok(t: Maybe<&2, U32>) -> Bool:
  match t:
    case None{}:
      True{}
    case Some{+v}:
      Bool.or(U32.is_eq(v, 1), U32.is_eq(v, 3))

def Gsm.v4v6(t: Maybe<&2, U32>) -> Bool:
  match t:
    case None{}:
      False{}
    case Some{v}:
      U32.is_eq(v, 3)

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

def Gsm.wants_dns(r: B.Res(Q.Epco)) -> Bool:
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
# request an initial one, the DNN and slice the configured ones, the UPF
# associated, the type IPv4 (IPv4v6 is granted IPv4), and the pool must hold
# a free address, and entropy a free TEID and SEID.
def Gsm.validate(+cfg: S.Cfg, +psi: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, up: Bool, +sessions: Tb.Table(S.Session), +entropy: B.Bytes()) -> Check:
  +t = I.Opts.t1(I.Iei.pdu_session_type(), sm_opts)
  Gsm.allocate(Gsm.pick(Bool.and(U32.is_lt(0, psi), U32.is_lt(psi, 16)), 95, Gsm.pick(Gsm.request_type_ok(I.Opts.t1(I.Iei.request_type(), mm_opts)), 31, Gsm.pick(Gsm.dnn_ok(cfg, I.Opts.find(I.Iei.dnn(), mm_opts)), 27, Gsm.pick(Gsm.slice_ok(cfg, I.Opts.find(I.Iei.s_nssai(), mm_opts)), 70, Gsm.pick(up, 38, Gsm.pick(Gsm.type_ok(t), 50, None{})))))), Gsm.v4v6(t), Gsm.dns_asked(I.Opts.find(I.Iei.extended_pco(), sm_opts)), cfg, sessions, entropy)

# The PFCP Session Establishment Request goes out; the session waits for the UPF
# with its Accept ready, under its guard, its local SEID.
def Gsm.create(+st: S.State, +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, +ip: U32, +teid: U32, +seid: U32, v4v6: Bool, dns: Bool) -> N.GOut():
  +seq = S.State.pfcp_seq(st)
  +request = Up.N4.establish(cfg, seid, ip, teid, seq)
  +s : S.Session = S.Session{S.SId{key, psi, ip, teid}, S.SVar{[], seq, S.Creating{S.Guard{0}, pti, Gsm.accept(cfg, psi, pti, ip, dns, v4v6), request}}}
  N.Out.join((S.Both{S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), ctx)}, S.BumpSeq{1}}, [N.Pfcp{Some{key}, request}, N.TimerStart{Some{key}, seid, Up.N4.t1_ms()}]), Gsm.place(st, seid, s, U32.add(seq, 1)))

def Gsm.checked(+st: S.State, key: U32, ue: S.Ue, ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, c: Check) -> N.GOut():
  match c:
    case Refuse{cause}:
      Gsm.dl(key, ue, ctx, psi, Gsm.reject(psi, pti, cause))
    case Go{v4v6, dns, ip, teid, seid}:
      Gsm.create(st, key, ue, ctx, cfg, psi, pti, ip, teid, seid, v4v6, dns)

def Gsm.with_cfg(+st: S.State, key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, +psi: U32, pti: U32, mm_opts: List<&2, I.Ie>, sm_opts: List<&2, I.Ie>, entropy: B.Bytes(), cfg: Maybe<&2, S.Cfg>) -> N.GOut():
  match cfg:
    case None{}:
      N.Out.verified(key, ue, ctx, "5GSM: no configuration")
    case Some{+c}:
      Gsm.checked(st, key, ue, ctx, c, psi, pti, Gsm.validate(c, psi, mm_opts, sm_opts, Up.N4.up(st), S.State.sessions(st), entropy))

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

# The UPF's answers
# --------------

# Session Establishment accepted with no UE context, security context or
# configuration to set it up with: the session the UPF made is deleted.
def Gsm.setup_gone(+st: S.State, skey: U32, +s: S.Session, up_seid: B.Bytes()) -> N.GOut():
  Up.N4.deletions([(skey, S.Session.with_var(s, S.SVar{up_seid, S.Session.seq(s), S.Session.phase(s)}))], S.State.pfcp_seq(st))

# Session Establishment accepted: the UP SEID is kept and the gNB is asked to
# set the session up, the Accept inside; the session's guard bounds the wait.
def Gsm.setup_ue(st: S.State, +skey: U32, +s: S.Session, pti: U32, accept: Sm.Sm, +up_seid: B.Bytes(), +ue: S.Ue, ctx: Maybe<&2, Sec.Nas.Ctx>, cfg: Maybe<&2, S.Cfg>) -> N.GOut():
  match ctx cfg:
    case Some{c} Some{+cf}:
      +p : Sec.Nas.Protected = Sec.Nas.protect(c, Sec.Ciphered{}, Gsm.dl_transport(S.Session.psi(s), Sm.Sm.write(accept)))
      (S.Both{S.Rephase{S.Session.ue(s), S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))}, S.Revar{skey, S.SVar{up_seid, S.Session.seq(s), S.Setting{S.Guard{0}, pti}}}}, [N.PduSetup{S.Ue.assoc(ue), S.Ue.stream(ue), S.Session.ue(s), S.Ue.ran_id(ue), S.Session.psi(s), S.Cfg.sst(cf), Sec.Nas.Protected.msg(p), Gsm.transfer(cf, S.Session.teid(s))}, N.TimerStart{Some{S.Session.ue(s)}, skey, Up.N4.t1_ms()}])
    case _ _:
      Gsm.setup_gone(st, skey, s, up_seid)

def Gsm.setup(+st: S.State, skey: U32, +s: S.Session, pti: U32, accept: Sm.Sm, up_seid: B.Bytes(), m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      Gsm.setup_gone(st, skey, s, up_seid)
    case Some{+ue}:
      Gsm.setup_ue(st, skey, s, pti, accept, up_seid, ue, S.Phase.ctx(S.Ue.phase(ue)), S.State.config(st))

# Refused, or no UP SEID: the UE is told (#38), nothing of the session remains.
def Gsm.established_as(+st: S.State, skey: U32, +s: S.Session, pti: U32, accept: Sm.Sm, ok: Bool, up: Maybe<&2, B.Bytes()>) -> N.GOut():
  match ok up:
    case True{} Some{up_seid}:
      Gsm.setup(st, skey, s, pti, accept, up_seid, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)))
    case _ _:
      Gsm.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st))

def Gsm.established_phase(st: S.State, skey: U32, s: S.Session, +msg: Pf.Msg, p: S.SPhase) -> N.GOut():
  match p:
    case S.Creating{guard, pti, accept, request}:
      Gsm.established_as(st, skey, s, pti, accept, Up.N4.accepted(Up.N4.cause(msg)), Up.N4.up_seid(msg))
    case _:
      N.Out.warn("PFCP: Session Establishment Response for a session not being created")

def Gsm.established(st: S.State, msg: Pf.Msg, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> N.GOut():
  match m:
    case None{}:
      N.Out.warn("PFCP: Session Establishment Response for no pending request")
    case Some{(skey, +s)}:
      Gsm.established_phase(st, skey, s, msg, S.Session.phase(s))

# Sessions a handover released: PDU Session Release Command (#26) to the UE
# for each, in DL NAS Transport through its new gNB, which never set them up
# (TS 23.502 §4.3.4.2), protected in turn; with the NAS context they leave.
def Gsm.releases_then(+a: N.Act, r: Sigma<&2, &2, Sec.Nas.Ctx, _ => List<&2, N.Act>>) -> Sigma<&2, &2, Sec.Nas.Ctx, _ => List<&2, N.Act>>:
  match r:
    case (c, acts):
      (c, a <> acts)

def Gsm.releases(+key: U32, +assoc: U32, +stream: U32, +ran: B.Bytes(), psis: List<&2, U32>, ctx: Sec.Nas.Ctx) -> Sigma<&2, &2, Sec.Nas.Ctx, _ => List<&2, N.Act>>:
  match psis:
    case Nil{}:
      (ctx, [])
    case +p <> more:
      +q : Sec.Nas.Protected = Gsm.release_nas(ctx, p)
      Gsm.releases_then(N.DlNas{assoc, stream, key, ran, Sec.Nas.Protected.msg(q)}, Gsm.releases(key, assoc, stream, ran, more, Sec.Nas.Protected.ctx(q)))

def Gsm.Told.ctx(r: Sigma<&2, &2, Sec.Nas.Ctx, _ => List<&2, N.Act>>) -> Sec.Nas.Ctx:
  match r:
    case (c, acts):
      c

def Gsm.Told.acts(r: Sigma<&2, &2, Sec.Nas.Ctx, _ => List<&2, N.Act>>) -> List<&2, N.Act>:
  match r:
    case (c, acts):
      acts

# Path Switch (TS 23.502 §4.9.1.2.2)
# -----------------------------------
# A session repointed to the target gNB is switched once the UPF accepts it,
# and released otherwise: deleted at the UPF and named to the target as
# released. Once no session of the UE waits, the AMF answers the target: Path
# Switch Request Acknowledge with the next {NH, NCC} when some session was
# switched, then PDU Session Release Command to the UE for each session
# released; Path Switch Request Failure and the UE's release otherwise (TS
# 38.413 §8.4.4.2).

def Gsm.repoint_done(+st: S.State, +skey: U32, +s: S.Session, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      (S.Revar{skey, S.SVar{S.Session.up_seid(s), S.Session.seq(s), S.Active{}}}, [N.TimerCancel{skey}])
    case False{}:
      Up.N4.deletions([(skey, s)], S.State.pfcp_seq(st))

def Gsm.repointing(p: S.SPhase) -> Bool:
  match p:
    case S.Repointing{guard, request}:
      True{}
    case _:
      False{}

def Gsm.active(p: S.SPhase) -> Bool:
  match p:
    case S.Active{}:
      True{}
    case _:
      False{}

# Another session of the UE still waits for the UPF.
def Gsm.waits(+key: U32, +skey: U32, ss: Tb.Table(S.Session)) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case (+k, +t) <> more:
      Bool.or(Bool.and(Bool.and(S.Maybe.same_u32(S.Session.tag(t), Some{key}), Bool.not(U32.is_eq(k, skey))), Gsm.repointing(S.Session.phase(t))), Gsm.waits(key, skey, more))

def Gsm.psi_if(psi: U32, more: List<&2, U32>, hit: Bool) -> List<&2, U32>:
  match hit:
    case True{}:
      psi <> more
    case False{}:
      more

# The PDU session identities of the UE's active sessions.
def Gsm.active_psis(+key: U32, ss: Tb.Table(S.Session)) -> List<&2, U32>:
  match ss:
    case Nil{}:
      []
    case (k, +t) <> more:
      Gsm.psi_if(S.Session.psi(t), Gsm.active_psis(key, more), Bool.and(S.Maybe.same_u32(S.Session.tag(t), Some{key}), Gsm.active(S.Session.phase(t))))

# No session switched: Failure naming every session released, then the UE released.
def Gsm.switch_failed(+key: U32, +ue: S.Ue, psis: List<&2, U32>) -> N.GOut():
  +cause = N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified())
  (S.Rephase{key, S.Releasing{S.Guard{0}}}, [N.SwitchFail{S.Ue.assoc(ue), S.Ue.stream(ue), Some{key}, N.Ngap.big(key), S.Ue.ran_id(ue), psis, cause}, N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}, N.TimerStart{Some{key}, key, N.Ue.guard_ms()}, N.Note{F.Warn{}, "NGAP: Path Switch failed, no PDU session switched; UE released"}])

def Gsm.switch_end(+key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, +nh: S.Nh, +released: List<&2, U32>, +switched: List<&2, U32>, cfg: Maybe<&2, S.Cfg>) -> N.GOut():
  match switched cfg:
    case (p <> more) Some{c}:
      +r = Gsm.releases(key, S.Ue.assoc(ue), S.Ue.stream(ue), S.Ue.ran_id(ue), released, ctx)
      (S.Rephase{key, S.Registered{Gsm.Told.ctx(r), nh, None{}}}, N.SwitchAck{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), N.Ue.caps(ue), nh, p <> more, released, S.Cfg.sst(c)} <> List.append(&2, N.Act, Gsm.Told.acts(r), [N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Path Switch done"}]))
    case _ _:
      Gsm.switch_failed(key, ue, List.append(&2, U32, released, switched))

def Gsm.switch_next(+st: S.State, +key: U32, +ue: S.Ue, guard: S.Guard, ctx: Sec.Nas.Ctx, nh: S.Nh, released: List<&2, U32>, switched: List<&2, U32>, waits: Bool) -> N.GOut():
  match waits:
    case True{}:
      (S.Rephase{key, S.Switching{guard, ctx, nh, released}}, [])
    case False{}:
      Gsm.switch_end(key, ue, ctx, nh, released, switched, S.State.config(st))

def Gsm.switch_ue(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, +ue: S.Ue, p: S.Phase) -> N.GOut():
  match p:
    case S.Switching{guard, ctx, nh, released}:
      +key = S.Session.ue(s)
      +psi = S.Session.psi(s)
      Gsm.switch_next(st, key, ue, guard, ctx, nh, Gsm.psi_if(psi, released, Bool.not(ok)), Gsm.psi_if(psi, Gsm.active_psis(key, S.State.sessions(st)), ok), Gsm.waits(key, skey, S.State.sessions(st)))
    case _:
      (S.Keep{}, [])

def Gsm.switch_of(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, [])
    case Some{+ue}:
      Gsm.switch_ue(st, skey, s, ok, ue, S.Ue.phase(ue))

# The UPF answered a repointed session, or its last retransmission went unanswered.
def Gsm.repointed(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool) -> N.GOut():
  N.Out.join(Gsm.repoint_done(st, skey, s, ok), Gsm.switch_of(st, skey, s, ok, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st))))

# Session Modification accepted: active; refused: the session is released.
def Gsm.modified_as(+st: S.State, +skey: U32, +s: S.Session, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      (S.Revar{skey, S.SVar{S.Session.up_seid(s), S.Session.seq(s), S.Active{}}}, [N.TimerCancel{skey}, N.Note{F.Info{}, "5GSM: PDU session active"}])
    case False{}:
      Gsm.drop(st, skey, s, S.State.pfcp_seq(st))

def Gsm.modified_phase(st: S.State, skey: U32, s: S.Session, msg: Pf.Msg, p: S.SPhase) -> N.GOut():
  match p:
    case S.Modifying{guard, request}:
      Gsm.modified_as(st, skey, s, Up.N4.accepted(Up.N4.cause(msg)))
    case S.Repointing{guard, request}:
      Gsm.repointed(st, skey, s, Up.N4.accepted(Up.N4.cause(msg)))
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
      Gsm.pfcp_k6(st, msg, U32.is_eq(kind, Pf.Type.session_modification_response()))

# A Session Deletion Response ends the deletion it answers, by its sequence
# number, whatever its cause: the row goes, and with it its guard; a cause
# other than Request accepted is logged.
def Gsm.deleted_notes(ok: Bool) -> List<&2, N.Act>:
  match ok:
    case True{}:
      []
    case False{}:
      [N.Note{F.Warn{}, "PFCP: Session Deletion Response refused the deletion; session forgotten"}]

def Gsm.deleted_phase(+skey: U32, +msg: Pf.Msg, p: S.SPhase) -> N.GOut():
  match p:
    case S.Deleting{guard, request}:
      (S.DelSession{skey}, Gsm.deleted_notes(Up.N4.accepted(Up.N4.cause(msg))))
    case _:
      N.Out.warn("PFCP: Session Deletion Response for a session not being deleted")

def Gsm.deleted(+msg: Pf.Msg, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> N.GOut():
  match m:
    case None{}:
      N.Out.warn("PFCP: Session Deletion Response for no pending request")
    case Some{(+skey, s)}:
      Gsm.deleted_phase(skey, msg, S.Session.phase(s))

def Gsm.pfcp_k4(st: S.State, +msg: Pf.Msg, +kind: U32, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gsm.deleted(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))
    case False{}:
      Gsm.pfcp_k5(st, msg, kind, U32.is_eq(kind, Pf.Type.session_establishment_response()))

def Gsm.pfcp_k3(+st: S.State, +msg: Pf.Msg, +kind: U32, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Up.N4.assoc_response(st, msg)
    case False{}:
      Gsm.pfcp_k4(st, msg, kind, U32.is_eq(kind, Pf.Type.session_deletion_response()))

def Gsm.pfcp_k2(+st: S.State, +msg: Pf.Msg, +kind: U32, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Up.N4.alive(st, msg)
    case False{}:
      Gsm.pfcp_k3(st, msg, kind, U32.is_eq(kind, Pf.Type.association_setup_response()))

def Gsm.pfcp_k1(+st: S.State, +msg: Pf.Msg, +kind: U32, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Up.N4.heartbeat_answer(st, msg)
    case False{}:
      Gsm.pfcp_k2(st, msg, kind, U32.is_eq(kind, Pf.Type.heartbeat_response()))

def Gsm.pfcp_msg(st: S.State, r: B.Read(Pf.Msg)) -> N.GOut():
  match r:
    case Fail{e}:
      N.Out.warn("PFCP: message not decodable")
    case Done{(+msg, rest)}:
      +kind = Pf.Msg.kind(msg)
      Gsm.pfcp_k1(st, msg, kind, U32.is_eq(kind, Pf.Type.heartbeat_request()))

# A PFCP datagram from the UPF.
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

# The UPF is told the gNB's tunnel; the session's guard bounds the wait.
def Gsm.modify(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, +seq: U32, tunnel: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, c: Maybe<&2, Sec.Nas.Ctx>) -> Gsm.Item():
  match tunnel:
    case None{}:
      Gsm.give_up_in(key, ue, skey, s, Release{}, seq, c)
    case Some{(gnb_teid, gnb_addr)}:
      +request = Up.N4.modify(S.Session.up_seid(s), gnb_teid, gnb_addr, seq)
      (c, (S.Both{S.Revar{skey, S.SVar{S.Session.up_seid(s), seq, S.Modifying{S.Guard{0}, request}}}, S.BumpSeq{1}}, [N.Pfcp{S.Session.tag(s), request}, N.TimerStart{S.Session.tag(s), skey, Up.N4.t1_ms()}]))

def Gsm.set_up_phase(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, transfer: B.Bytes(), +seq: U32, p: S.SPhase, c: Maybe<&2, Sec.Nas.Ctx>) -> Gsm.Item():
  match p:
    case S.Setting{guard, pti}:
      Gsm.modify(key, ue, skey, s, seq, Gsm.tunnel_of(G.PDUSessionResourceSetupResponseTransfer.read(Ap.Cur{0n, Ap.unpack(transfer)})), c)
    case _:
      (c, N.Out.warn("NGAP: PDU session set up at the gNB while not being set up"))

def Gsm.set_up(+key: U32, +ue: S.Ue, transfer: B.Bytes(), +seq: U32, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, c: Maybe<&2, Sec.Nas.Ctx>) -> Gsm.Item():
  match m:
    case None{}:
      (c, N.Out.warn("NGAP: PDU session set up at the gNB for no session"))
    case Some{(skey, +s)}:
      Gsm.set_up_phase(key, ue, skey, s, transfer, seq, S.Session.phase(s), c)

# The setup list names the PDU session again later.
def Gsm.named(+psi: U32, items: G.PDUSessionResourceSetupListSURes()) -> Bool:
  match items:
    case Nil{}:
      False{}
    case G.PDUSessionResourceSetupItemSURes{p, transfer, x} <> more:
      Bool.or(U32.is_eq(p, psi), Gsm.named(psi, more))

# Only a session's last naming in the list counts, so no item undoes what an
# earlier one did to the same session.
def Gsm.set_up_last(+key: U32, +ue: S.Ue, transfer: B.Bytes(), +seq: U32, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, again: Bool, c: Maybe<&2, Sec.Nas.Ctx>) -> Gsm.Item():
  match again:
    case True{}:
      (c, N.Out.warn("NGAP: PDU session named again later in the setup list; this naming ignored"))
    case False{}:
      Gsm.set_up(key, ue, transfer, seq, m, c)

def Gsm.set_ups(+st: S.State, +key: U32, +ue: S.Ue, items: G.PDUSessionResourceSetupListSURes(), +seq: U32, c: Maybe<&2, Sec.Nas.Ctx>) -> Gsm.Item():
  match items:
    case Nil{}:
      (c, (S.Keep{}, []))
    case G.PDUSessionResourceSetupItemSURes{+psi, transfer, x} <> +more:
      Gsm.then(Gsm.after((S.BumpSeq{1}, []), Gsm.set_up_last(key, ue, transfer, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), Gsm.named(psi, more), c)), c2 => Gsm.set_ups(st, key, ue, more, U32.add(seq, 1), c2))

def Gsm.failed_phase(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, +seq: U32, p: S.SPhase, c: Maybe<&2, Sec.Nas.Ctx>) -> Gsm.Item():
  match p:
    case S.Setting{guard, pti}:
      Gsm.give_up_in(key, ue, skey, s, Reply{Gsm.reject(S.Session.psi(s), pti, 26)}, seq, c)
    case _:
      (c, N.Out.warn("NGAP: PDU session failed at the gNB while not being set up"))

def Gsm.failed(+key: U32, +ue: S.Ue, +seq: U32, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, c: Maybe<&2, Sec.Nas.Ctx>) -> Gsm.Item():
  match m:
    case None{}:
      (c, N.Out.warn("NGAP: PDU session failed at the gNB for no session"))
    case Some{(skey, +s)}:
      Gsm.failed_phase(key, ue, skey, s, seq, S.Session.phase(s), c)

def Gsm.faileds(+st: S.State, +key: U32, +ue: S.Ue, items: G.PDUSessionResourceFailedToSetupListSURes(), +seq: U32, c: Maybe<&2, Sec.Nas.Ctx>) -> Gsm.Item():
  match items:
    case Nil{}:
      (c, (S.Keep{}, []))
    case G.PDUSessionResourceFailedToSetupItemSURes{psi, transfer, x} <> more:
      Gsm.then(Gsm.after((S.BumpSeq{1}, []), Gsm.failed(key, ue, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), c)), c2 => Gsm.faileds(st, key, ue, more, U32.add(seq, 1), c2))

def Gsm.list_or(-A: Data, m: Maybe<&2, List<&2, A>>) -> List<&2, A>:
  match m:
    case None{}:
      []
    case Some{xs}:
      xs

# Each session the response names: set up at the gNB, or failed there; one
# PFCP sequence number is spent per session named. The UE's NAS context runs
# through the items in turn and is written once, after the last.
def Gsm.results(+st: S.State, +key: U32, +ue: S.Ue, +oks: G.PDUSessionResourceSetupListSURes(), fails: G.PDUSessionResourceFailedToSetupListSURes()) -> N.GOut():
  Gsm.under(key, ue, c => Gsm.then(Gsm.set_ups(st, key, ue, oks, S.State.pfcp_seq(st), c), c2 => Gsm.faileds(st, key, ue, fails, U32.add(S.State.pfcp_seq(st), U32.from_nat(List.length(&2, G.PDUSessionResourceSetupItemSURes, oks))), c2)))

def Gsm.setup_response_ue(st: S.State, assoc: U32, key: U32, oks: G.PDUSessionResourceSetupListSURes(), fails: G.PDUSessionResourceFailedToSetupListSURes(), m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{+ue}:
      Gsm.results(st, key, ue, oks, fails)

def Gsm.setup_response_key(+st: S.State, +assoc: U32, ran: B.Bytes(), oks: G.PDUSessionResourceSetupListSURes(), fails: G.PDUSessionResourceFailedToSetupListSURes(), m: Maybe<&2, U32>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{+key}:
      Gsm.setup_response_ue(st, assoc, key, oks, fails, N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran))

def Gsm.setup_response(+st: S.State, +assoc: U32, v: V.PDUSessionResourceSetupResponse.View) -> N.GOut():
  match v:
    case V.PDUSessionResourceSetupResponse.View{amf_ue_ngap_id, ran_ue_ngap_id, oks, fails, diagnostics, uli}:
      Gsm.setup_response_key(st, assoc, ran_ue_ngap_id, Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), Gsm.list_or(G.PDUSessionResourceFailedToSetupItemSURes, fails), N.Ngap.ue_key(amf_ue_ngap_id))

def Gsm.setup_response_of_view(st: S.State, assoc: U32, r: Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Gsm.setup_response(st, assoc, v)

# The gNB's release
# -----------------
# PDU Session Resource Release Response (TS 38.413 §8.2.2.2): the sessions a
# Release Command named were deleted at the UPF when it went, so the answer
# changes nothing. One naming a live session of the UE answers no Command of
# ours: a logical error in a response, handled locally (§10.4), by a warning.

def Gsm.unasked(+key: U32, items: G.PDUSessionResourceReleasedListRelRes(), +ss: Tb.Table(S.Session)) -> Bool:
  match items:
    case Nil{}:
      False{}
    case G.PDUSessionResourceReleasedItemRelRes{+psi, transfer, x} <> more:
      Bool.or(Tb.Table.present(Sigma<&2, &2, U32, _ => S.Session>, S.Sessions.by_psi(key, psi, ss)), Gsm.unasked(key, more, ss))

def Gsm.release_noted(unasked: Bool) -> List<&2, N.Act>:
  match unasked:
    case True{}:
      [N.Note{F.Warn{}, "NGAP: PDU Session Resource Release Response naming a PDU session not being released"}]
    case False{}:
      [N.Note{F.Info{}, "NGAP: PDU Session Resource Release Response"}]

def Gsm.release_answer_ue(+st: S.State, +assoc: U32, +key: U32, items: G.PDUSessionResourceReleasedListRelRes(), m: Maybe<&2, S.Ue>) -> List<&2, N.Act>:
  match m:
    case None{}:
      N.Ngap.unknown_ue(assoc)
    case Some{ue}:
      Gsm.release_noted(Gsm.unasked(key, items, S.State.sessions(st)))

def Gsm.release_answer_key(+st: S.State, +assoc: U32, ran: B.Bytes(), items: G.PDUSessionResourceReleasedListRelRes(), m: Maybe<&2, U32>) -> List<&2, N.Act>:
  match m:
    case None{}:
      N.Ngap.unknown_ue(assoc)
    case Some{+key}:
      Gsm.release_answer_ue(st, assoc, key, items, N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran))

def Gsm.release_answer(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.PDUSessionResourceReleaseResponse.View>) -> List<&2, N.Act>:
  match r:
    case Fail{e}:
      N.Ngap.bad_view(assoc)
    case Done{V.PDUSessionResourceReleaseResponse.View{amf, ran, items, uli, diagnostics}}:
      Gsm.release_answer_key(st, assoc, ran, items, N.Ngap.ue_key(amf))

def Gsm.release_response_of_view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.PDUSessionResourceReleaseResponse.View>) -> N.GOut():
  (S.Keep{}, Gsm.release_answer(st, assoc, r))

# Guard timers
# ------------

# A PFCP request unanswered for T1 goes again, unchanged, its sequence number
# included, up to N1 times (TS 29.244 §6.4); after that the session fails.
def Gsm.resend_if(+skey: U32, +s: S.Session, p: S.SPhase, +request: B.Bytes(), fail: N.GOut(), more: Bool) -> N.GOut():
  match more:
    case True{}:
      (S.Revar{skey, S.SVar{S.Session.up_seid(s), S.Session.seq(s), p}}, [N.Pfcp{S.Session.tag(s), request}, N.TimerStart{S.Session.tag(s), skey, Up.N4.t1_ms()}])
    case False{}:
      fail

# No answer in time: before the Accept went out the UE is refused (#38);
# after it, the session is released; a deletion is given up.
def Gsm.expired(+st: S.State, +skey: U32, +s: S.Session, +p: S.SPhase) -> N.GOut():
  match p:
    case S.Creating{+guard, +pti, accept, +request}:
      Gsm.resend_if(skey, s, S.Creating{S.Guard{U32.add(S.Guard.retries(guard), 1)}, pti, accept, request}, request, Gsm.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st)), U32.is_lt(S.Guard.retries(guard), Up.N4.n1()))
    case S.Setting{guard, pti}:
      Gsm.drop(st, skey, s, S.State.pfcp_seq(st))
    case S.Modifying{+guard, +request}:
      Gsm.resend_if(skey, s, S.Modifying{S.Guard{U32.add(S.Guard.retries(guard), 1)}, request}, request, Gsm.drop(st, skey, s, S.State.pfcp_seq(st)), U32.is_lt(S.Guard.retries(guard), Up.N4.n1()))
    case S.Repointing{+guard, +request}:
      Gsm.resend_if(skey, s, S.Repointing{S.Guard{U32.add(S.Guard.retries(guard), 1)}, request}, request, Gsm.repointed(st, skey, s, False{}), U32.is_lt(S.Guard.retries(guard), Up.N4.n1()))
    case S.Deleting{+guard, +request}:
      Gsm.resend_if(skey, s, S.Deleting{S.Guard{U32.add(S.Guard.retries(guard), 1)}, request}, request, (S.DelSession{skey}, [N.Note{F.Warn{}, "PFCP: no Session Deletion Response; deletion given up"}]), U32.is_lt(S.Guard.retries(guard), Up.N4.n1()))
    case S.Active{}:
      (S.Keep{}, [])
