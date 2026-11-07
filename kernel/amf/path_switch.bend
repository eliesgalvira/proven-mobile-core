import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../nas/security.bend as Sec
import ../smf/switch.bend as Sw
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

def Ps.go(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, +rows: Tb.Table(S.Session), ok: Bool) -> N.GOut():
  match ok:
    case False{}:
      Ps.fail(assoc, stream, amf, ran, items, N.Ngap.radio_cause(G.CauseRadioNetwork.unknown_PDU_session_ID()))
    case True{}:
      +moved = S.Ue.moved(ue, assoc, ran, stream, S.Switching{S.Guard{0}, ctx, S.Nh.next(nh), Sw.Sw.released(ts, rows)})
      N.Out.also(N.Out.join(Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st)), (S.Put{key, moved}, [])), [N.TimerStart{Some{key}, key, Ps.guard_ms()}, N.Note{F.Info{}, "NGAP: Path Switch Request; the UE moved, its PDU sessions being switched"}])

def Ps.unknown() -> G.Cause:
  N.Ngap.radio_cause(G.CauseRadioNetwork.unknown_local_UE_NGAP_ID())

def Ps.free(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, ok: Bool) -> N.GOut():
  match ok:
    case False{}:
      Ps.fail(assoc, stream, amf, ran, items, N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified()))
    case True{}:
      +rows = S.Sessions.of_ue(key, S.State.sessions(st))
      Ps.go(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, rows, Sw.Sw.any(ts, rows))

# Only a registered UE, whose SUPI 5G-AKA has verified, is switched.
def Ps.identified(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, nh: S.Nh, supi: Maybe<&2, B.Digits()>) -> N.GOut():
  match supi:
    case None{}:
      Ps.fail(assoc, stream, amf, ran, items, Ps.unknown())
    case Some{s}:
      Ps.free(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, S.Ues.ran_free(key, assoc, ran, S.State.ues(st)))

def Ps.phase(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, p: S.Phase) -> N.GOut():
  match p:
    case S.Registered{ctx, nh, released}:
      Ps.identified(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, S.Ue.supi(ue))
    case _:
      Ps.fail(assoc, stream, amf, ran, items, Ps.unknown())

# The UE the request's AMF-UE-NGAP-ID names, claimed.
def Ps.claim(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, m: Maybe<&2, N.Keyed()>) -> N.GOut():
  N.Ue.found(m, Ps.fail(assoc, stream, amf, ran, items, Ps.unknown()), +key => +ue => Ps.phase(st, assoc, stream, amf, ran, items, ts, key, ue, S.Ue.phase(ue)))

# The request's UE security capabilities are only compared with the stored
# ones, which the acknowledgement carries (TS 33.501 §6.7.3.1): a mismatch is logged.
def Ps.caps_same(ok: Bool) -> List<&2, N.Act>:
  match ok:
    case True{}:
      []
    case False{}:
      [N.Note{F.Warn{}, "NGAP: Path Switch Request UE security capabilities differ from the stored ones"}]

def Ps.caps_note(caps: G.UESecurityCapabilities, m: Maybe<&2, N.Keyed()>) -> List<&2, N.Act>:
  match m:
    case None{}:
      []
    case Some{(key, ue)}:
      Ps.caps_same(B.bytes_eq(Ap.pack(G.UESecurityCapabilities.write(N.Ngap.ue_caps(N.Ue.caps(ue)), 0n, [])), Ap.pack(G.UESecurityCapabilities.write(caps, 0n, []))))

# The UE the request names, whatever association owns it.
def Ps.named(+st: S.State, +amf: B.Bytes()) -> Maybe<&2, N.Keyed()>:
  N.Ue.keyed(N.Ngap.ue_key(amf), k => Tb.Table.get(S.Ue, k, S.State.ues(st)))

def Ps.request(+st: S.State, +assoc: U32, +stream: U32, v: V.PathSwitchRequest.View) -> N.GOut():
  match v:
    case V.PathSwitchRequest.View{+ran, +amf, uli, caps, +items, failed, rrc}:
      +m = Ps.named(st, amf)
      N.Out.also(Ps.claim(st, assoc, stream, amf, ran, items, Sw.Sw.path_tunnels(items), m), Ps.caps_note(caps, m))

def Ps.of_view(+st: S.State, +assoc: U32, +stream: U32, r: Result<&2, &2, B.Err, V.PathSwitchRequest.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Ps.request(st, assoc, stream, v)
