import Base
import ./bytes.bend as B
import ./tlv.bend as T
import ./table.bend as Tb
import ./frame.bend as F
import ./state.bend as S
import ./smf/n4.bend as Up
import ./smf/gsm.bend as Gsm
import ./ausf.bend as Au
import ./amf/ngap.bend as N
import ./amf/gmm.bend as Gmm
import ./amf/route.bend as R

# The step function (docs/spec/milestone-1.md § The step function): total and
# pure; every law about a procedure is a law about it.

def Kernel.state(o: N.Step()) -> S.State:
  match o:
    case (st, actions):
      st

def Kernel.actions(o: N.Step()) -> List<&2, N.Act>:
  match o:
    case (st, actions):
      actions

# The actions as the edge receives them.
def Kernel.frames(o: N.Step()) -> List<&2, F.Action>:
  N.Acts.render(Kernel.actions(o))

# Config: keep it, choose the PFCP recovery stamp, ask eUPF for an association.
def Kernel.config(complete: Bool, st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes()) -> N.Step():
  match complete:
    case False{}:
      (st, [N.Note{F.Error{}, "Config: a required tag is missing or invalid; configuration unchanged"}])
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          +cfg = S.Cfg.of(tlvs)
          +st2 : S.State = S.State{Some{cfg}, Au.Subscribers.of(S.Cfg.subscribers(cfg)), assocs, ues, sessions, pfcp_seq, next_ue, next_timer, S.N4{List.take(&2, U32, entropy, 4n), S.Idle{}}}
          N.Step.of(st2, N.Out.also(Up.N4.start(st2), [N.Note{F.Info{}, "Config: loaded; PFCP association requested"}]))

def Kernel.assoc_up(st: S.State, assoc: U32) -> N.Step():
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      (S.State{config, subs, S.Assocs.add(assoc, assocs), ues, sessions, pfcp_seq, next_ue, next_timer, n4}, [])

# An association going down releases every UE it owned, their sessions at eUPF included.
def Kernel.assoc_down(st: S.State, +assoc: U32) -> N.Step():
  match st:
    case S.State{config, subs, assocs, ues, +sessions, +pfcp_seq, next_ue, next_timer, n4}:
      +left = S.Ues.drop_assoc(assoc, ues)
      +gone = S.Sessions.sift(S.SOrphan{left}, sessions)
      (S.State{config, subs, S.Assocs.drop(assoc, assocs), left, S.Sessions.sift(S.SOwned{left}, sessions), U32.add(pfcp_seq, Up.N4.deletion_count(gone)), next_ue, next_timer, n4}, List.append(&2, N.Act, Up.N4.deletions(gone, pfcp_seq), [N.Note{F.Info{}, "NGAP: association down; its UE contexts and sessions released"}]))

# A guard timer fired: a UE's, a session's, or the N4 association's (timer 0).
def Kernel.node_timer(+st: S.State, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Up.N4.fired(st)
    case False{}:
      (S.Keep{}, [])

def Kernel.fired_session(+st: S.State, +timer: U32, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> N.GOut():
  match m:
    case None{}:
      Kernel.node_timer(st, U32.is_eq(timer, S.N4.timer()))
    case Some{(skey, +s)}:
      Gsm.Gsm.expired(st, skey, s, S.Session.phase(s))

def Kernel.fired_ue(+st: S.State, +timer: U32, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>) -> N.GOut():
  match m:
    case None{}:
      Kernel.fired_session(st, timer, S.Sessions.by_timer(timer, S.State.sessions(st)))
    case Some{(key, +ue)}:
      Gmm.Gmm.expired(st, key, ue, S.Ue.phase(ue))

def Kernel.fired(+st: S.State, +timer: U32) -> N.GOut():
  Kernel.fired_ue(st, timer, S.Ues.by_timer(timer, S.State.ues(st)))

def Kernel.step(+st: S.State, ev: F.Evt, +entropy: B.Bytes()) -> N.Step():
  match ev:
    case F.Config{len, +tlvs}:
      Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)
    case F.NgapAssocUp{assoc}:
      Kernel.assoc_up(st, assoc)
    case F.NgapAssocDown{assoc}:
      Kernel.assoc_down(st, assoc)
    case F.NgapData{assoc, stream, len, bytes}:
      R.Route.data(st, assoc, stream, bytes, entropy)
    case F.PfcpData{len, bytes}:
      N.Step.of(st, Gsm.Gsm.pfcp_data(st, bytes))
    case F.TimerFired{timer}:
      N.Step.of(st, Kernel.fired(st, timer))
