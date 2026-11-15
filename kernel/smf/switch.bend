import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/gen/types.bend as G
import ../table.bend as Tb
import ../state.bend as S
import ../amf/ngap.bend as N
import ./n4.bend as Up
import ./gsm.bend as Gsm

# The SMF's part in both handovers, Xn (Path Switch) and N2: the target's
# downlink tunnels read from the N2 transfers, and each of the UE's sessions
# repointed to its tunnel or released.

# The target's downlink tunnels: one for each session a transfer that reads
# gives an IPv4 GTP tunnel.
def Sw.tunnel_in(psi: U32, m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, more: List<&2, S.Tunnel>) -> List<&2, S.Tunnel>:
  match m:
    case None{}:
      more
    case Some{(teid, addr)}:
      S.Tunnel{psi, teid, addr} <> more

def Sw.path_tunnel(psi: U32, r: Ap.Rd(G.PathSwitchRequestTransfer), more: List<&2, S.Tunnel>) -> List<&2, S.Tunnel>:
  match r:
    case Fail{e}:
      more
    case Done{(G.PathSwitchRequestTransfer{dl, reused, security, flows, x}, c)}:
      Sw.tunnel_in(psi, Gsm.Gsm.tunnel_up(dl), more)

def Sw.path_tunnels(items: G.PDUSessionResourceToBeSwitchedDLList()) -> List<&2, S.Tunnel>:
  match items:
    case Nil{}:
      []
    case G.PDUSessionResourceToBeSwitchedDLItem{psi, transfer, x} <> more:
      Sw.path_tunnel(psi, G.PathSwitchRequestTransfer.read(Ap.Cur{0n, Ap.unpack(transfer)}), Sw.path_tunnels(more))

def Sw.ack_tunnel(psi: U32, r: Ap.Rd(G.HandoverRequestAcknowledgeTransfer), more: List<&2, S.Tunnel>) -> List<&2, S.Tunnel>:
  match r:
    case Fail{e}:
      more
    case Done{(G.HandoverRequestAcknowledgeTransfer{dl, forwarding, security, flows, failed, drbs, x}, c)}:
      Sw.tunnel_in(psi, Gsm.Gsm.tunnel_up(dl), more)

def Sw.admitted(items: G.PDUSessionResourceAdmittedList()) -> List<&2, S.Tunnel>:
  match items:
    case Nil{}:
      []
    case G.PDUSessionResourceAdmittedItem{psi, transfer, x} <> more:
      Sw.ack_tunnel(psi, G.HandoverRequestAcknowledgeTransfer.read(Ap.Cur{0n, Ap.unpack(transfer)}), Sw.admitted(more))

def Sw.find(+psi: U32, ts: List<&2, S.Tunnel>) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  match ts:
    case Nil{}:
      None{}
    case S.Tunnel{+p, teid, addr} <> more:
      Tb.Table.hit(Sigma<&2, &2, U32, _ => B.Bytes()>, (teid, addr), Sw.find(psi, more), U32.is_eq(p, psi))

# A session's new downlink tunnel: the session active, and a tunnel given for it.
def Sw.tunnel(p: S.SPhase, m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  match p m:
    case S.Active{} Some{t}:
      Some{t}
    case _ _:
      None{}

def Sw.tunnel_for(+ts: List<&2, S.Tunnel>, +s: S.Session) -> Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>:
  Sw.tunnel(S.Session.phase(s), Sw.find(S.Session.psi(s), ts))

def Sw.any(+ts: List<&2, S.Tunnel>, rows: Tb.Table(S.Session)) -> Bool:
  match rows:
    case Nil{}:
      False{}
    case (skey, +s) <> more:
      Bool.or(Tb.Table.present(Sigma<&2, &2, U32, _ => B.Bytes()>, Sw.tunnel_for(ts, s)), Sw.any(ts, more))

def Sw.released(+ts: List<&2, S.Tunnel>, rows: Tb.Table(S.Session)) -> List<&2, U32>:
  match rows:
    case Nil{}:
      []
    case (skey, +s) <> more:
      Gsm.Gsm.psi_if(S.Session.psi(s), Sw.released(ts, more), Bool.not(Tb.Table.present(Sigma<&2, &2, U32, _ => B.Bytes()>, Sw.tunnel_for(ts, s))))

# One PFCP Session Modification repoints a session's downlink FAR, under the
# session's guard; a session with no tunnel is released.
def Sw.session(+skey: U32, +s: S.Session, +seq: U32, t: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>) -> N.GOut():
  match t:
    case None{}:
      Up.N4.deletions([(skey, s)], seq)
    case Some{(teid, addr)}:
      +request = Up.N4.modify(S.Session.up_seid(s), teid, addr, seq)
      (S.Revar{skey, S.SVar{S.Session.up_seid(s), seq, S.Repointing{S.Guard{0}, request}}}, [N.Pfcp{S.Session.tag(s), request}, N.TimerStart{S.Session.tag(s), skey, S.N4.t1_ms()}])

def Sw.sessions(+ts: List<&2, S.Tunnel>, rows: Tb.Table(S.Session), +seq: U32) -> N.GOut():
  match rows:
    case Nil{}:
      (S.Keep{}, [])
    case (+skey, +s) <> more:
      N.Out.join(N.Out.join((S.BumpSeq{1}, []), Sw.session(skey, s, seq, Sw.tunnel_for(ts, s))), Sw.sessions(ts, more, U32.add(seq, 1)))
