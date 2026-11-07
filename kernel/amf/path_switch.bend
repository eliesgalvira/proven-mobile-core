import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../nas/security.bend as Sec
import ../smf/n4.bend as Up
import ../smf/gsm.bend as Gsm
import ./ngap.bend as N

# Path Switch Request (TS 23.502 §4.9.1.2.2, TS 38.413 §8.4.4): the target gNB
# of an Xn handover claims a registered UE by its AMF-UE-NGAP-ID. There is no
# owner check, as TS 23.502 has none: any gNB with NG Setup done may claim any
# registered UE. The UE moves to the target at once, under the RAN-UE-NGAP-ID
# the request gives, with the next {NH, NCC}; each active PDU session the
# request names has its downlink repointed to the target's tunnel, and every
# other session of the UE is released. A request that can switch nothing
# changes nothing and gets Path Switch Request Failure.

# The UPF answers a repointed session within T1 × (N1 + 1); the switch's guard
# allows one T1 more.
def Ps.guard_ms() -> U32:
  15000

def Ps.psis(+items: G.PDUSessionResourceToBeSwitchedDLList()) -> List<&2, U32>:
  match items:
    case Nil{}:
      []
    case G.PDUSessionResourceToBeSwitchedDLItem{psi, transfer, x} <> more:
      psi <> Ps.psis(more)

# Failure before any PFCP request: the request's IDs echoed, every session it names released.
def Ps.fail(assoc: U32, stream: U32, +amf: B.Bytes(), ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), cause: G.Cause) -> N.GOut():
  (S.Keep{}, [N.SwitchFail{assoc, stream, None{}, amf, ran, Ps.psis(items), cause}, N.Note{F.Warn{}, "NGAP: Path Switch Request refused"}])

# The target's downlink tunnel for a session: the session active and named
# with a transfer that reads.
def Ps.transfer(+psi: U32, +items: G.PDUSessionResourceToBeSwitchedDLList()) -> Maybe<&2, B.Bytes()>:
  match items:
    case Nil{}:
      None{}
    case G.PDUSessionResourceToBeSwitchedDLItem{+p, transfer, x} <> more:
      Tb.Table.hit(B.Bytes(), transfer, Ps.transfer(psi, more), U32.is_eq(p, psi))

def Ps.tunnel_of(r: Ap.Rd(G.PathSwitchRequestTransfer)) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  match r:
    case Fail{e}:
      None{}
    case Done{(G.PathSwitchRequestTransfer{dl, reused, security, flows, x}, c)}:
      Gsm.Gsm.tunnel_up(dl)

def Ps.tunnel(p: S.SPhase, m: Maybe<&2, B.Bytes()>) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  match p m:
    case S.Active{} Some{t}:
      Ps.tunnel_of(G.PathSwitchRequestTransfer.read(Ap.Cur{0n, Ap.unpack(t)}))
    case _ _:
      None{}

def Ps.tunnel_for(+items: G.PDUSessionResourceToBeSwitchedDLList(), +s: S.Session) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  Ps.tunnel(S.Session.phase(s), Ps.transfer(S.Session.psi(s), items))

def Ps.any(+items: G.PDUSessionResourceToBeSwitchedDLList(), rows: Tb.Table(S.Session)) -> Bool:
  match rows:
    case Nil{}:
      False{}
    case (skey, +s) <> more:
      Bool.or(Tb.Table.present(Sigma<&2, &2, U32, _ => B.Bytes()>, Ps.tunnel_for(items, s)), Ps.any(items, more))

def Ps.released(+items: G.PDUSessionResourceToBeSwitchedDLList(), rows: Tb.Table(S.Session)) -> List<&2, U32>:
  match rows:
    case Nil{}:
      []
    case (skey, +s) <> more:
      Gsm.Gsm.psi_if(S.Session.psi(s), Ps.released(items, more), Bool.not(Tb.Table.present(Sigma<&2, &2, U32, _ => B.Bytes()>, Ps.tunnel_for(items, s))))

# One PFCP Session Modification repoints a session's downlink FAR, under the
# session's guard; a session with no tunnel is released.
def Ps.session(+skey: U32, +s: S.Session, +seq: U32, t: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>) -> N.GOut():
  match t:
    case None{}:
      Gsm.Gsm.forget([(skey, s)], seq)
    case Some{(teid, addr)}:
      +request = Up.N4.modify(S.Session.up_seid(s), teid, addr, seq)
      (S.Revar{skey, S.SVar{S.Session.up_seid(s), seq, S.Repointing{S.Guard{0}, request}}}, [N.Pfcp{Some{S.Session.ue(s)}, request}, N.TimerStart{Some{S.Session.ue(s)}, skey, Up.N4.t1_ms()}])

def Ps.sessions(+items: G.PDUSessionResourceToBeSwitchedDLList(), rows: Tb.Table(S.Session), +seq: U32) -> N.GOut():
  match rows:
    case Nil{}:
      (S.Keep{}, [])
    case (+skey, +s) <> more:
      N.Out.join(N.Out.join((S.BumpSeq{1}, []), Ps.session(skey, s, seq, Ps.tunnel_for(items, s))), Ps.sessions(items, more, U32.add(seq, 1)))

def Ps.go(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, +rows: Tb.Table(S.Session), ok: Bool) -> N.GOut():
  match ok:
    case False{}:
      Ps.fail(assoc, stream, amf, ran, items, N.Ngap.radio_cause(G.CauseRadioNetwork.unknown_PDU_session_ID()))
    case True{}:
      +moved = S.Ue.moved(ue, assoc, ran, stream, S.Switching{S.Guard{0}, ctx, S.Nh.next(nh), Ps.released(items, rows)})
      N.Out.also(N.Out.join(Ps.sessions(items, rows, S.State.pfcp_seq(st)), (S.Put{key, moved}, [])), [N.TimerStart{Some{key}, key, Ps.guard_ms()}, N.Note{F.Info{}, "NGAP: Path Switch Request; the UE moved, its PDU sessions being switched"}])

def Ps.unknown() -> G.Cause:
  N.Ngap.radio_cause(G.CauseRadioNetwork.unknown_local_UE_NGAP_ID())

# The RAN-UE-NGAP-ID the request gives names no other context on the target.
def Ps.ran_free(+key: U32, +assoc: U32, +ran: B.Bytes(), ues: Tb.Table(S.Ue)) -> Bool:
  match ues:
    case Nil{}:
      True{}
    case (+k, +v) <> more:
      Bool.and(Bool.not(Bool.and(Bool.not(U32.is_eq(k, key)), Bool.and(U32.is_eq(S.Ue.assoc(v), assoc), B.bytes_eq(S.Ue.ran_id(v), ran)))), Ps.ran_free(key, assoc, ran, more))

def Ps.free(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, ok: Bool) -> N.GOut():
  match ok:
    case False{}:
      Ps.fail(assoc, stream, amf, ran, items, N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified()))
    case True{}:
      +rows = S.Sessions.of_ue(key, S.State.sessions(st))
      Ps.go(st, assoc, stream, amf, ran, items, key, ue, ctx, nh, rows, Ps.any(items, rows))

# Only a registered UE, whose SUPI 5G-AKA has verified, is switched.
def Ps.identified(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, supi: Maybe<&2, B.Digits()>) -> N.GOut():
  match supi:
    case None{}:
      Ps.fail(assoc, stream, amf, ran, items, Ps.unknown())
    case Some{s}:
      Ps.free(st, assoc, stream, amf, ran, items, key, ue, ctx, nh, Ps.ran_free(key, assoc, ran, S.State.ues(st)))

def Ps.phase(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +key: U32, +ue: S.Ue, p: S.Phase) -> N.GOut():
  match p:
    case S.Registered{ctx, nh}:
      Ps.identified(st, assoc, stream, amf, ran, items, key, ue, ctx, nh, S.Ue.supi(ue))
    case _:
      Ps.fail(assoc, stream, amf, ran, items, Ps.unknown())

def Ps.found(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +key: U32, m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      Ps.fail(assoc, stream, amf, ran, items, Ps.unknown())
    case Some{+ue}:
      Ps.phase(st, assoc, stream, amf, ran, items, key, ue, S.Ue.phase(ue))

def Ps.keyed(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), m: Maybe<&2, U32>) -> N.GOut():
  match m:
    case None{}:
      Ps.fail(assoc, stream, amf, ran, items, Ps.unknown())
    case Some{+key}:
      Ps.found(st, assoc, stream, amf, ran, items, key, Tb.Table.get(S.Ue, key, S.State.ues(st)))

# Only a gNB that has completed NG Setup may switch a path.
def Ps.ready(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), ok: Bool) -> N.GOut():
  match ok:
    case False{}:
      Ps.fail(assoc, stream, amf, ran, items, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()))
    case True{}:
      Ps.keyed(st, assoc, stream, amf, ran, items, N.Ngap.ue_key(amf))

# The request's UE security capabilities are only compared with the stored
# ones, which the acknowledgement carries (TS 33.501 §6.7.3.1): a mismatch is logged.
def Ps.caps_same(ok: Bool) -> List<&2, N.Act>:
  match ok:
    case True{}:
      []
    case False{}:
      [N.Note{F.Warn{}, "NGAP: Path Switch Request UE security capabilities differ from the stored ones"}]

def Ps.caps_ue(caps: G.UESecurityCapabilities, m: Maybe<&2, S.Ue>) -> List<&2, N.Act>:
  match m:
    case None{}:
      []
    case Some{ue}:
      Ps.caps_same(B.bytes_eq(Ap.pack(G.UESecurityCapabilities.write(N.Ngap.ue_caps(N.Ue.caps(ue)), 0n, [])), Ap.pack(G.UESecurityCapabilities.write(caps, 0n, []))))

def Ps.caps_note(+st: S.State, caps: G.UESecurityCapabilities, m: Maybe<&2, U32>) -> List<&2, N.Act>:
  match m:
    case None{}:
      []
    case Some{+key}:
      Ps.caps_ue(caps, Tb.Table.get(S.Ue, key, S.State.ues(st)))

def Ps.request(+st: S.State, +assoc: U32, +stream: U32, v: V.PathSwitchRequest.View) -> N.GOut():
  match v:
    case V.PathSwitchRequest.View{+ran, +amf, uli, caps, items, failed, rrc}:
      N.Out.also(Ps.ready(st, assoc, stream, amf, ran, items, S.Assocs.has(assoc, S.State.assocs(st))), Ps.caps_note(st, caps, N.Ngap.ue_key(amf)))

def Ps.of_view(+st: S.State, +assoc: U32, +stream: U32, r: Result<&2, &2, B.Err, V.PathSwitchRequest.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Ps.request(st, assoc, stream, v)
