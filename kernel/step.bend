import Base
import ./bytes.bend as B
import ./tlv.bend as T
import ./table.bend as Tb
import ./frame.bend as F
import ./state.bend as S
import ./smf.bend as Smf
import ./amf/ngap.bend as N

# The step function (docs/spec/milestone-1.md § The step function): total and
# pure; every law about a procedure is a law about it.

def Kernel.state(o: S.Out()) -> S.State:
  match o:
    case (st, actions):
      st

def Kernel.actions(o: S.Out()) -> List<&2, F.Action>:
  match o:
    case (st, actions):
      actions

# Config: keep it, choose the PFCP recovery stamp, ask eUPF for an association.
def Kernel.config(complete: Bool, st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes()) -> S.Out():
  match complete:
    case False{}:
      (st, [F.Action.log_make(F.Error{}, "Config: a required tag is missing; configuration unchanged")])
    case True{}:
      match st:
        case S.State{config, assocs, ues, sessions, +pfcp_seq, next_ue, next_timer, recovery}:
          +cfg = S.Cfg.of(tlvs)
          +stamp = List.take(&2, U32, entropy, 4n)
          (S.State{Some{cfg}, assocs, ues, sessions, U32.add(pfcp_seq, 1), next_ue, next_timer, stamp}, [F.Action.pfcp_make(Smf.Assoc.setup_request(cfg, stamp, pfcp_seq)), F.Action.log_make(F.Info{}, "Config: loaded; PFCP association requested")])

def Kernel.assoc_up(st: S.State, assoc: U32) -> S.Out():
  match st:
    case S.State{config, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      (S.State{config, S.Assocs.add(assoc, assocs), ues, sessions, pfcp_seq, next_ue, next_timer, recovery}, [])

def Kernel.deletions_cons(a: F.Action, r: Sigma<&2, &2, List<&2, F.Action>, _ => U32>) -> Sigma<&2, &2, List<&2, F.Action>, _ => U32>:
  match r:
    case (actions, seq):
      (a <> actions, seq)

def Kernel.deletions(gone: List<&2, S.Session>, +seq: U32) -> Sigma<&2, &2, List<&2, F.Action>, _ => U32>:
  match gone:
    case Nil{}:
      ([], seq)
    case s <> more:
      Kernel.deletions_cons(F.Action.pfcp_make(Smf.Session.deletion_request(S.Session.up_seid(s), seq)), Kernel.deletions(more, U32.add(seq, 1)))

def Kernel.released_out(config: Maybe<&2, S.Cfg>, assocs: List<&2, U32>, ues: Tb.Table(S.Ue), kept: Tb.Table(S.Session), next_ue: U32, next_timer: U32, recovery: B.Bytes(), r: Sigma<&2, &2, List<&2, F.Action>, _ => U32>) -> S.Out():
  match r:
    case (actions, seq):
      (S.State{config, assocs, ues, kept, seq, next_ue, next_timer, recovery}, List.append(&2, F.Action, actions, [F.Action.log_make(F.Info{}, "NGAP: association down; its UE contexts and sessions released")]))

# An association going down releases every UE it owned, sessions included.
def Kernel.released(config: Maybe<&2, S.Cfg>, assocs: List<&2, U32>, ues: Tb.Table(S.Ue), next_ue: U32, next_timer: U32, recovery: B.Bytes(), split: Sigma<&2, &2, Tb.Table(S.Session), _ => List<&2, S.Session>>, seq: U32) -> S.Out():
  match split:
    case (kept, gone):
      Kernel.released_out(config, assocs, ues, kept, next_ue, next_timer, recovery, Kernel.deletions(gone, seq))

def Kernel.assoc_down(st: S.State, +assoc: U32) -> S.Out():
  match st:
    case S.State{config, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      +left = S.Ues.drop_assoc(assoc, ues)
      Kernel.released(config, S.Assocs.drop(assoc, assocs), left, next_ue, next_timer, recovery, S.Sessions.partition(left, sessions), pfcp_seq)

def Kernel.step(st: S.State, ev: F.Evt, entropy: B.Bytes()) -> S.Out():
  match ev:
    case F.Config{len, +tlvs}:
      Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)
    case F.NgapAssocUp{assoc}:
      Kernel.assoc_up(st, assoc)
    case F.NgapAssocDown{assoc}:
      Kernel.assoc_down(st, assoc)
    case F.NgapData{assoc, stream, len, bytes}:
      N.Ngap.data(st, assoc, stream, bytes)
    case F.PfcpData{len, bytes}:
      (st, [])
    case F.TimerFired{timer}:
      (st, [])
