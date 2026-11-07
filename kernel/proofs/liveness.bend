import Base
import ../bytes.bend as B
import ../table.bend as Tb
import ../state.bend as S
import ../ngap/gen/types.bend as G
import ../frame.bend as F
import ../tlv.bend as T
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/gmm.bend as Gmm
import ../smf/n4.bend as Up
import ../smf/gsm.bend as Gsm
import ../pfcp.bend as Pf
import ../nas/security.bend as Sec
import ../nas/mm.bend as Mm
import ../nas/sm.bend as Sm
import ../nas/ie.bend as I
import ../nas/mobile_id.bend as Mi
import ../suci.bend as Su
import ../ausf.bend as Au
import ../plmn.bend as Pl
import ../crypto/kdf.bend as Kd
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../amf/route.bend as R
import ../amf/path_switch.bend as Ps
import ../amf/handover.bend as Ho
import ../LAWS.bend as L
import ./lib.bend as P
import ./kernel.bend as PK
import ./takeover.bend as PT
import ./walk.bend as PW

# Proofs of the liveness laws (ticket 33) and of the invariants every step keeps.

# A guard that fires
# ------------------

def Lv.tx_prepend(+a: N.Act, +o: N.GOut()) -> {PT.Tk.tx(N.Out.prepend(a, o)) == PT.Tk.tx(o) : S.Tx}:
  match o:
    case (tx, acts):
      {==}

def Lv.tx_also(+o: N.GOut(), +more: List<&2, N.Act>) -> {PT.Tk.tx(N.Out.also(o, more)) == PT.Tk.tx(o) : S.Tx}:
  match o:
    case (tx, acts):
      {==}

# Release Command: the context stays under its key, releasing, with a new guard.
def Lv.release_get(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause) -> {Tb.Table.get(S.Ue, key, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release(st, key, ue, cause))))) == Some{S.Ue.with_phase(ue, S.Releasing{S.Guard{0}})} : Maybe<&2, S.Ue>}:
  +ur = S.Ue.with_phase(ue, S.Releasing{S.Guard{0}})
  +p = Gmm.Gmm.place(st, key, ur)
  +ts : List<&2, N.Act> = N.TimerStart{Some{key}, key, N.Ue.guard_ms()} <> Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause)
  +e = Gmm.Gmm.evict(S.Ues.evicted(key, ur, S.State.ues(st)), S.State.sessions(st), S.State.pfcp_seq(st))
  er = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release(st, key, ue, cause)))), PT.Tk.ues(PT.Tk.tx(Gmm.Gmm.release(st, key, ue, cause)), S.State.ues(st)), PT.Tk.render(st, Gmm.Gmm.release(st, key, ue, cause)))
  %er : {Tb.Table.get(S.Ue, key, _) == Some{ur} : Maybe<&2, S.Ue>}
  ep = Equal.sym(S.Tx, PT.Tk.tx(N.Out.prepend(N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}, N.Out.also(p, ts))), PT.Tk.tx(N.Out.also(p, ts)), Lv.tx_prepend(N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}, N.Out.also(p, ts)))
  %ep : {Tb.Table.get(S.Ue, key, PT.Tk.ues(_, S.State.ues(st))) == Some{ur} : Maybe<&2, S.Ue>}
  ea = Equal.sym(S.Tx, PT.Tk.tx(N.Out.also(p, ts)), PT.Tk.tx(p), Lv.tx_also(p, ts))
  %ea : {Tb.Table.get(S.Ue, key, PT.Tk.ues(_, S.State.ues(st))) == Some{ur} : Maybe<&2, S.Ue>}
  ei = Equal.sym(S.Tx, PT.Tk.tx(p), S.Both{S.Put{key, ur}, PT.Tk.tx(e)}, PT.Tk.tx_join((S.Put{key, ur}, []), e))
  %ei : {Tb.Table.get(S.Ue, key, PT.Tk.ues(_, S.State.ues(st))) == Some{ur} : Maybe<&2, S.Ue>}
  ee = Equal.sym(Tb.Table(S.Ue), PT.Tk.ues(PT.Tk.tx(e), S.Ues.put(key, ur, S.State.ues(st))), S.Ues.put(key, ur, S.State.ues(st)), PT.Tk.evict(S.Ues.evicted(key, ur, S.State.ues(st)), S.State.sessions(st), S.State.pfcp_seq(st), S.Ues.put(key, ur, S.State.ues(st))))
  %ee : {Tb.Table.get(S.Ue, key, _) == Some{ur} : Maybe<&2, S.Ue>}
  ek = Equal.sym(Bool, U32.is_eq(key, key), True{}, P.U32.is_eq_refl(key))
  %ek : {Tb.Table.hit(S.Ue, ur, Tb.Table.get(S.Ue, key, S.Ues.sift(S.Clear{key, ur}, S.State.ues(st))), _) == Some{ur} : Maybe<&2, S.Ue>}
  {==}

def Lv.retried(+st: S.State, +k: U32, +u: S.Ue, +g: S.Guard, +et: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eg: {S.Ue.guard(u) == Some{g} : Maybe<&2, S.Guard>}, np: {S.Ue.phase(u) == S.Releasing{g} : S.Phase} -> Empty, +er: {U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()) == False{} : Bool}) -> {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, S.Ue.phase(u)))))) == Some{S.Ue.with_phase(u, S.Releasing{S.Guard{0}})} : Maybe<&2, S.Ue>}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      match phase:
        case S.Created{}:
          Empty.absurd({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Created{}, last_dl}, S.Created{}))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}, P.Refute.none_some(S.Guard, g, eg))
        case S.Identifying{+guard}:
          eq = Equal.sym(S.Guard, guard, g, P.Some.inj(S.Guard, guard, g, eg))
          ser = Equal.sym(Bool, U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()), False{}, er)
          %eq : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Identifying{_}, last_dl}, _, S.Identifying{_}, U32.is_lt(S.Guard.retries(_), Gmm.Gmm.max_retries())))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          %ser : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Identifying{g}, last_dl}, g, S.Identifying{g}, _))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          Lv.release_get(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Identifying{g}, last_dl}, N.Ngap.nas_cause(G.CauseNas.unspecified()))
        case S.Authenticating{+guard, av, resynced, asupi}:
          eq = Equal.sym(S.Guard, guard, g, P.Some.inj(S.Guard, guard, g, eg))
          ser = Equal.sym(Bool, U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()), False{}, er)
          %eq : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Authenticating{_, av, resynced, asupi}, last_dl}, _, S.Authenticating{_, av, resynced, asupi}, U32.is_lt(S.Guard.retries(_), Gmm.Gmm.max_retries())))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          %ser : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Authenticating{g, av, resynced, asupi}, last_dl}, g, S.Authenticating{g, av, resynced, asupi}, _))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          Lv.release_get(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Authenticating{g, av, resynced, asupi}, last_dl}, N.Ngap.nas_cause(G.CauseNas.unspecified()))
        case S.SecurityMode{+guard, ctx, k_amf}:
          eq = Equal.sym(S.Guard, guard, g, P.Some.inj(S.Guard, guard, g, eg))
          ser = Equal.sym(Bool, U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()), False{}, er)
          %eq : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.SecurityMode{_, ctx, k_amf}, last_dl}, _, S.SecurityMode{_, ctx, k_amf}, U32.is_lt(S.Guard.retries(_), Gmm.Gmm.max_retries())))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          %ser : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.SecurityMode{g, ctx, k_amf}, last_dl}, g, S.SecurityMode{g, ctx, k_amf}, _))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          Lv.release_get(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.SecurityMode{g, ctx, k_amf}, last_dl}, N.Ngap.nas_cause(G.CauseNas.unspecified()))
        case S.ContextSetup{+guard, ctx, nh, response, complete}:
          eq = Equal.sym(S.Guard, guard, g, P.Some.inj(S.Guard, guard, g, eg))
          ser = Equal.sym(Bool, U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()), False{}, er)
          %eq : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.ContextSetup{_, ctx, nh, response, complete}, last_dl}, _, S.ContextSetup{_, ctx, nh, response, complete}, U32.is_lt(S.Guard.retries(_), Gmm.Gmm.max_retries())))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          %ser : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.ContextSetup{g, ctx, nh, response, complete}, last_dl}, g, S.ContextSetup{g, ctx, nh, response, complete}, _))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          Lv.release_get(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.ContextSetup{g, ctx, nh, response, complete}, last_dl}, N.Ngap.nas_cause(G.CauseNas.unspecified()))
        case S.Registered{ctx, nh}:
          Empty.absurd({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Registered{ctx, nh}, last_dl}, S.Registered{ctx, nh}))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}, P.Refute.none_some(S.Guard, g, eg))
        case S.Switching{guard, ctx, nh, released}:
          Lv.release_get(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Switching{guard, ctx, nh, released}, last_dl}, N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified()))
        case S.Handover{+guard, ctx, nh, source, leg}:
          eq = Equal.sym(S.Guard, guard, g, P.Some.inj(S.Guard, guard, g, eg))
          ser = Equal.sym(Bool, U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()), False{}, er)
          %eq : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Ho.Ho.expired(k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Handover{guard, ctx, nh, source, leg}, last_dl}, ctx, nh, leg, U32.is_lt(S.Guard.retries(_), Gmm.Gmm.max_retries())))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          %ser : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Ho.Ho.expired(k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Handover{guard, ctx, nh, source, leg}, last_dl}, ctx, nh, leg, _))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          sa = Equal.sym(Tb.Table(S.Ue), S.State.ues(S.Tx.apply(S.Rephase{k, S.Releasing{S.Guard{0}}}, st)), PT.Tk.ues(S.Rephase{k, S.Releasing{S.Guard{0}}}, S.State.ues(st)), PT.Tk.ues_apply(S.Rephase{k, S.Releasing{S.Guard{0}}}, st))
          %sa : {Tb.Table.get(S.Ue, k, _) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}
          PT.Rephase.self(k, S.Releasing{S.Guard{0}}, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Handover{guard, ctx, nh, source, leg}, last_dl}, S.State.ues(st), et)
        case S.Releasing{+guard}:
          eq = Equal.sym(S.Guard, guard, g, P.Some.inj(S.Guard, guard, g, eg))
          Empty.absurd({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{guard}, last_dl}, S.Releasing{guard}))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}, np((%eq : {S.Releasing{_} == S.Releasing{g} : S.Phase}; {==})))

def Lv.exp1(+st: S.State, +entropy: B.Bytes(), +k: U32, +u: S.Ue, +g: S.Guard, +et: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eg: {S.Ue.guard(u) == Some{g} : Maybe<&2, S.Guard>}, np: {S.Ue.phase(u) == S.Releasing{g} : S.Phase} -> Empty, +er: {U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()) == False{} : Bool}) -> {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.TimerFired{k}, entropy)))) == Some{S.Ue.with_phase(u, S.Releasing{S.Guard{0}})} : Maybe<&2, S.Ue>}:
  set = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{u}, et)
  %set : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, k, _))))) == Some{S.Ue.with_phase(u, S.Releasing{S.Guard{0}})} : Maybe<&2, S.Ue>}
  Lv.retried(st, k, u, g, et, eg, np, er)

def Lv.exp2(+st: S.State, +entropy: B.Bytes(), +k: U32, +u: S.Ue, +g: S.Guard, +et: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(u) == S.Releasing{g} : S.Phase}) -> {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.TimerFired{k}, entropy)))) == None{} : Maybe<&2, S.Ue>} & ({S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{k}, entropy)))) == [] : Tb.Table(S.Session)} & {K.Kernel.actions(K.Kernel.step(st, F.TimerFired{k}, entropy)) == List.append(&2, N.Act, List.append(&2, N.Act, Up.N4.deletions(S.Sessions.of_ue(k, S.State.sessions(st)), S.State.pfcp_seq(st)), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]), N.Gone.cancels(S.State.sessions(st), S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{k}, entropy))))) : List<&2, N.Act>}):
  +n = Up.N4.deletion_count(S.Sessions.of_ue(k, S.State.sessions(st)))
  set = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{u}, et)
  %set : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, k, _))))) == None{} : Maybe<&2, S.Ue>} & ({S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, k, _))))) == [] : Tb.Table(S.Session)} & {K.Kernel.actions(N.Step.of(st, K.Kernel.fired_ue(st, k, _))) == List.append(&2, N.Act, List.append(&2, N.Act, Up.N4.deletions(S.Sessions.of_ue(k, S.State.sessions(st)), S.State.pfcp_seq(st)), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]), N.Gone.cancels(S.State.sessions(st), S.State.sessions(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, k, _)))))) : List<&2, N.Act>})
  sep = Equal.sym(S.Phase, S.Ue.phase(u), S.Releasing{g}, ep)
  %sep : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _))))) == None{} : Maybe<&2, S.Ue>} & ({S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _))))) == [] : Tb.Table(S.Session)} & {K.Kernel.actions(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _))) == List.append(&2, N.Act, List.append(&2, N.Act, Up.N4.deletions(S.Sessions.of_ue(k, S.State.sessions(st)), S.State.pfcp_seq(st)), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]), N.Gone.cancels(S.State.sessions(st), S.State.sessions(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _)))))) : List<&2, N.Act>})
  (PK.Tx.forget_ue(k, n, st), (PK.Tx.forget_sessions(k, n, st), {==}))

def L.amf.guard.expires(st, entropy, k, u, g, et, eg):
  (np => er => Lv.exp1(st, entropy, k, u, g, et, eg, np, er), ep => Lv.exp2(st, entropy, k, u, g, et, ep))

# What a step may do
# ------------------
# A key is live in a state when a context holds it, it is the one a new context
# takes, or a session belongs to it. A UE procedure builds its actions only
# from live keys and never answers NG Setup; every context it puts or rephases
# is registered or guarded; every session it puts belongs to a context, with an
# Accept within the packet-filter bound if it is being created, and every
# session it puts or changes is known to the UPF exactly when past Creating, the
# changes relying on the sessions of the state before the step being so. A UE
# that is gone holds none of these, so nothing is built from it
# (amf.release.forgets_ue), no session outlives its context
# (amf.sessions.owned), no context is left Created (amf.contexts.guarded), no
# session holds an Accept beyond the bound (smf.packet_filters.capacity_reject)
# and the UPF knows the sessions past Creating (smf.sessions.known).

def Lv.owner(+x: U32, ss: Tb.Table(S.Session)) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case (k, t) <> more:
      Bool.or(U32.is_eq(S.Session.ue(t), x), Lv.owner(x, more))

# A key held: a context's, or the one the step gives a new context.
def Lv.held(+st: S.State, +x: U32) -> Bool:
  Bool.or(Tb.Table.has(S.Ue, x, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{x}))

def Lv.live(+st: S.State, +x: U32) -> Bool:
  Bool.or(Lv.held(st, x), Lv.owner(x, S.State.sessions(st)))

# A context is put only under a key held, when sessions belong to contexts.
def Lv.keyed(+st: S.State, +x: U32) -> Bool:
  Bool.or(Lv.held(st, x), Bool.not(S.Sessions.owned(S.State.sessions(st), S.State.ues(st))))

def Lv.tag(+st: S.State, m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Lv.live(st, x)

def Lv.act(+st: S.State, +a: N.Act) -> Bool:
  Bool.and(Bool.not(N.Ngap.is_ng_setup_response(a)), Lv.tag(st, N.Act.ue(a)))

def Lv.acts(+st: S.State, as: List<&2, N.Act>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case +a <> more:
      Bool.and(Lv.act(st, a), Lv.acts(st, more))

# A session's variable part agrees with the UPF.
def Lv.var_ok(+v: S.SVar) -> Bool:
  S.SPhase.knows(S.SVar.phase(v), Nat.is_eq(List.length(&2, U32, S.SVar.up_seid(v)), 8n))

# A change of a session keeps the Accept's bound and agrees with the UPF,
# given the sessions of st do.
def Lv.revar_ok(+st: S.State, +v: S.SVar) -> Bool:
  Bool.and(Bool.or(Gsm.Gsm.phase_bounded(S.SVar.phase(v)), Bool.not(Gsm.Gsm.bounded(S.State.sessions(st)))), Bool.or(Lv.var_ok(v), Bool.not(S.Sessions.known(S.State.sessions(st)))))

def Lv.free(+st: S.State, tx: S.Tx) -> Bool:
  match tx:
    case S.Put{+key, +ue}:
      Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), S.Ue.single(ue)))
    case S.Rephase{key, +phase}:
      Bool.and(S.Phase.guarded(phase), S.Phase.idle(phase))
    case S.PutSession{key, s}:
      False{}
    case S.Revar{key, +v}:
      Lv.revar_ok(st, v)
    case S.Both{a, b}:
      Bool.and(Lv.free(st, a), Lv.free(st, b))
    case _:
      True{}

def Lv.homed(+st: S.State, +tx: S.Tx, +ues: Tb.Table(S.Ue)) -> Bool:
  match tx:
    case S.Put{+key, +ue}:
      Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), S.Ue.single(ue)))
    case S.Rephase{+key, +phase}:
      Bool.and(S.Phase.guarded(phase), S.Ue.fits(phase, Tb.Table.get(S.Ue, key, ues)))
    case S.PutSession{+key, +s}:
      Bool.and(S.Ids.seid(key), Bool.and(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s)))))
    case S.Revar{key, +v}:
      Lv.revar_ok(st, v)
    case S.Both{+a, b}:
      Bool.and(Lv.homed(st, a, ues), Lv.homed(st, b, PT.Tk.ues(a, ues)))
    case _:
      True{}

def Lv.as(o: N.GOut()) -> List<&2, N.Act>:
  match o:
    case (tx, acts):
      acts

# A phase with no handover pending belongs to any context.
def Lv.idle_owned(+p: S.Phase, +a: U32, +e: {S.Phase.idle(p) == True{} : Bool}) -> {S.Phase.owned_by(p, a) == True{} : Bool}:
  match p:
    case S.Handover{guard, ctx, nh, source, leg}:
      Empty.absurd({S.Phase.owned_by(S.Handover{guard, ctx, nh, source, leg}, a) == True{} : Bool}, P.Refute.bool(e))
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lv.idle_fits(+p: S.Phase, +m: Maybe<&2, S.Ue>, +e: {S.Phase.idle(p) == True{} : Bool}) -> {S.Ue.fits(p, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      Lv.idle_owned(p, S.Ue.assoc(w), e)

# An outcome puts no session (okf), or only sessions of contexts (ok).
def Lv.okf(+st: S.State, +o: N.GOut()) -> Bool:
  Bool.and(Lv.acts(st, Lv.as(o)), Lv.free(st, PT.Tk.tx(o)))

def Lv.ok(+st: S.State, +o: N.GOut()) -> Bool:
  Bool.and(Lv.acts(st, Lv.as(o)), Lv.homed(st, PT.Tk.tx(o), S.State.ues(st)))

# Composing outcomes
# ------------------

def Lv.free_homed(+st: S.State, +tx: S.Tx, +ues: Tb.Table(S.Ue), +e: {Lv.free(st, tx) == True{} : Bool}) -> {Lv.homed(st, tx, ues) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      {==}
    case S.Put{key, ue}:
      e
    case S.Rephase{+key, +phase}:
      P.Bool.and_intro(S.Phase.guarded(phase), S.Ue.fits(phase, Tb.Table.get(S.Ue, key, ues)), P.Bool.and_true_l(S.Phase.guarded(phase), S.Phase.idle(phase), e), Lv.idle_fits(phase, Tb.Table.get(S.Ue, key, ues), P.Bool.and_true_r(S.Phase.guarded(phase), S.Phase.idle(phase), e)))
    case S.Del{key}:
      {==}
    case S.PutSession{key, +s}:
      Empty.absurd({Lv.homed(st, S.PutSession{key, s}, ues) == True{} : Bool}, P.Refute.bool(e))
    case S.Revar{key, v}:
      e
    case S.DelSession{key}:
      {==}
    case S.Subs{subs}:
      {==}
    case S.SetLink{link}:
      {==}
    case S.BumpUe{bk}:
      {==}
    case S.BumpSeq{n}:
      {==}
    case S.Both{+a, +b}:
      P.Bool.and_intro(Lv.homed(st, a, ues), Lv.homed(st, b, PT.Tk.ues(a, ues)), Lv.free_homed(st, a, ues, P.Bool.and_true_l(Lv.free(st, a), Lv.free(st, b), e)), Lv.free_homed(st, b, PT.Tk.ues(a, ues), P.Bool.and_true_r(Lv.free(st, a), Lv.free(st, b), e)))

def Lv.ok_of(+st: S.State, +o: N.GOut(), +h: {Lv.okf(st, o) == True{} : Bool}) -> {Lv.ok(st, o) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      P.Bool.and_intro(Lv.acts(st, acts), Lv.homed(st, tx, S.State.ues(st)), P.Bool.and_true_l(Lv.acts(st, acts), Lv.free(st, tx), h), Lv.free_homed(st, tx, S.State.ues(st), P.Bool.and_true_r(Lv.acts(st, acts), Lv.free(st, tx), h)))

def Lv.cons(+st: S.State, +a: N.Act, +more: List<&2, N.Act>, +ha: {Lv.act(st, a) == True{} : Bool}, +hm: {Lv.acts(st, more) == True{} : Bool}) -> {Lv.acts(st, a <> more) == True{} : Bool}:
  P.Bool.and_intro(Lv.act(st, a), Lv.acts(st, more), ha, hm)

def Lv.append(+st: S.State, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {Lv.acts(st, xs) == True{} : Bool}, +hy: {Lv.acts(st, ys) == True{} : Bool}) -> {Lv.acts(st, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      Lv.cons(st, a, List.append(&2, N.Act, more, ys), P.Bool.and_true_l(Lv.act(st, a), Lv.acts(st, more), hx), Lv.append(st, more, ys, P.Bool.and_true_r(Lv.act(st, a), Lv.acts(st, more), hx), hy))

def Lv.leaf(+st: S.State, +tx: S.Tx, +as: List<&2, N.Act>, +ha: {Lv.acts(st, as) == True{} : Bool}, +hf: {Lv.free(st, tx) == True{} : Bool}) -> {Lv.okf(st, (tx, as)) == True{} : Bool}:
  P.Bool.and_intro(Lv.acts(st, as), Lv.free(st, tx), ha, hf)

def Lv.prepend(+st: S.State, +a: N.Act, +o: N.GOut(), +ha: {Lv.act(st, a) == True{} : Bool}, +h: {Lv.okf(st, o) == True{} : Bool}) -> {Lv.okf(st, N.Out.prepend(a, o)) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      Lv.leaf(st, tx, a <> acts, Lv.cons(st, a, acts, ha, P.Bool.and_true_l(Lv.acts(st, acts), Lv.free(st, tx), h)), P.Bool.and_true_r(Lv.acts(st, acts), Lv.free(st, tx), h))

def Lv.also(+st: S.State, +o: N.GOut(), +more: List<&2, N.Act>, +h: {Lv.okf(st, o) == True{} : Bool}, +hm: {Lv.acts(st, more) == True{} : Bool}) -> {Lv.okf(st, N.Out.also(o, more)) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      Lv.leaf(st, tx, List.append(&2, N.Act, acts, more), Lv.append(st, acts, more, P.Bool.and_true_l(Lv.acts(st, acts), Lv.free(st, tx), h), hm), P.Bool.and_true_r(Lv.acts(st, acts), Lv.free(st, tx), h))

def Lv.join(+st: S.State, +a: N.GOut(), +b: N.GOut(), +ha: {Lv.okf(st, a) == True{} : Bool}, +hb: {Lv.okf(st, b) == True{} : Bool}) -> {Lv.okf(st, N.Out.join(a, b)) == True{} : Bool}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          Lv.leaf(st, S.Both{ta, tb}, List.append(&2, N.Act, aa, ab), Lv.append(st, aa, ab, P.Bool.and_true_l(Lv.acts(st, aa), Lv.free(st, ta), ha), P.Bool.and_true_l(Lv.acts(st, ab), Lv.free(st, tb), hb)), P.Bool.and_intro(Lv.free(st, ta), Lv.free(st, tb), P.Bool.and_true_r(Lv.acts(st, aa), Lv.free(st, ta), ha), P.Bool.and_true_r(Lv.acts(st, ab), Lv.free(st, tb), hb)))

def Lv.cancel(+st: S.State, +key: U32, +g: Maybe<&2, S.Guard>) -> {Lv.acts(st, N.Guard.cancel(key, g)) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{guard}:
      {==}

# Guards
# ------
# A context put takes a phase of its own, and a NAS context replaced keeps the
# phase, which holds one only from Security Mode on.

def Lv.g_phase(+u: S.Ue, +p: S.Phase) -> {S.Phase.guarded(S.Ue.phase(S.Ue.with_phase(u, p))) == S.Phase.guarded(p) : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.g_moved(+u: S.Ue, +a: U32, +r: B.Bytes(), +s: U32, +p: S.Phase) -> {S.Phase.guarded(S.Ue.phase(S.Ue.moved(u, a, r, s, p))) == S.Phase.guarded(p) : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.g_dl(+u: S.Ue, +p: S.Phase, +dl: B.Bytes()) -> {S.Phase.guarded(S.Ue.phase(S.Ue.with_dl(u, p, dl))) == S.Phase.guarded(p) : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.g_ics(+u: S.Ue, +p: S.Phase, +dl: B.Bytes(), +r: B.Bytes(), +t: U32) -> {S.Phase.guarded(S.Ue.phase(S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(u, p, dl), r), t))) == S.Phase.guarded(p) : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.s_phase(+u: S.Ue, +p: S.Phase) -> {S.Ue.single(S.Ue.with_phase(u, p)) == S.Phase.owned_by(p, S.Ue.assoc(u)) : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.s_moved(+u: S.Ue, +a: U32, +r: B.Bytes(), +s: U32, +p: S.Phase) -> {S.Ue.single(S.Ue.moved(u, a, r, s, p)) == S.Phase.owned_by(p, a) : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.s_dl(+u: S.Ue, +p: S.Phase, +dl: B.Bytes()) -> {S.Ue.single(S.Ue.with_dl(u, p, dl)) == S.Phase.owned_by(p, S.Ue.assoc(u)) : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.s_ics(+u: S.Ue, +p: S.Phase, +dl: B.Bytes(), +r: B.Bytes(), +t: U32) -> {S.Ue.single(S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(u, p, dl), r), t)) == S.Phase.owned_by(p, S.Ue.assoc(u)) : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.g_ctx(+q: S.Phase, +c: Sec.Nas.Ctx, +e: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(q)) == True{} : Bool}) -> {Bool.and(S.Phase.guarded(S.Phase.with_ctx(q, c)), S.Phase.idle(S.Phase.with_ctx(q, c))) == True{} : Bool}:
  match q:
    case S.Created{}:
      Empty.absurd({Bool.and(S.Phase.guarded(S.Phase.with_ctx(S.Created{}, c)), S.Phase.idle(S.Phase.with_ctx(S.Created{}, c))) == True{} : Bool}, P.Refute.bool(e))
    case S.Identifying{guard}:
      Empty.absurd({Bool.and(S.Phase.guarded(S.Phase.with_ctx(S.Identifying{guard}, c)), S.Phase.idle(S.Phase.with_ctx(S.Identifying{guard}, c))) == True{} : Bool}, P.Refute.bool(e))
    case S.Authenticating{guard, av, resynced, supi}:
      Empty.absurd({Bool.and(S.Phase.guarded(S.Phase.with_ctx(S.Authenticating{guard, av, resynced, supi}, c)), S.Phase.idle(S.Phase.with_ctx(S.Authenticating{guard, av, resynced, supi}, c))) == True{} : Bool}, P.Refute.bool(e))
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Handover{guard, ctx, nh, source, leg}:
      Empty.absurd({Bool.and(S.Phase.guarded(S.Phase.with_ctx(S.Handover{guard, ctx, nh, source, leg}, c)), S.Phase.idle(S.Phase.with_ctx(S.Handover{guard, ctx, nh, source, leg}, c))) == True{} : Bool}, P.Refute.bool(e))
    case S.Releasing{guard}:
      Empty.absurd({Bool.and(S.Phase.guarded(S.Phase.with_ctx(S.Releasing{guard}, c)), S.Phase.idle(S.Phase.with_ctx(S.Releasing{guard}, c))) == True{} : Bool}, P.Refute.bool(e))

def Lv.has_ctx(+p: S.Phase, +c: Sec.Nas.Ctx, +e: {S.Phase.ctx(p) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}) -> {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(p)) == True{} : Bool}:
  se = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.ctx(p), Some{c}, e)
  %se : {Tb.Table.present(Sec.Nas.Ctx, _) == True{} : Bool}
  {==}

# Live keys
# ---------

def Lv.has_live(+st: S.State, +x: U32, +e: {Tb.Table.has(S.Ue, x, S.State.ues(st)) == True{} : Bool}) -> {Lv.live(st, x) == True{} : Bool}:
  P.Bool.or_l(Lv.held(st, x), Lv.owner(x, S.State.sessions(st)), P.Bool.or_l(Tb.Table.has(S.Ue, x, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{x}), e))

def Lv.owner_live(+st: S.State, +x: U32, +e: {Lv.owner(x, S.State.sessions(st)) == True{} : Bool}) -> {Lv.live(st, x) == True{} : Bool}:
  P.Bool.or_r(Lv.held(st, x), Lv.owner(x, S.State.sessions(st)), e)

def Lv.fresh_live(+st: S.State, +key: U32, +em: {S.State.fresh(st) == Some{key} : Maybe<&2, U32>}) -> {Lv.live(st, key) == True{} : Bool}:
  sem = Equal.sym(Maybe<&2, U32>, S.State.fresh(st), Some{key}, em)
  ef : {S.Maybe.same_u32(S.State.fresh(st), Some{key}) == True{} : Bool} = (%sem : {S.Maybe.same_u32(_, Some{key}) == True{} : Bool}; P.U32.is_eq_refl(key))
  P.Bool.or_l(Lv.held(st, key), Lv.owner(key, S.State.sessions(st)), P.Bool.or_r(Tb.Table.has(S.Ue, key, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{key}), ef))

def Lv.owner_row(+x: U32, +t: S.Session, +more: Tb.Table(S.Session), +ues: Tb.Table(S.Ue), +b: Bool, +eb: {U32.is_eq(S.Session.ue(t), x) == b : Bool}, +eo: {Bool.and(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(more, ues)) == True{} : Bool}, +ew: {Bool.or(b, Lv.owner(x, more)) == True{} : Bool}, ih: {S.Sessions.owned(more, ues) == True{} : Bool} -> {Lv.owner(x, more) == True{} : Bool} -> {Tb.Table.has(S.Ue, x, ues) == True{} : Bool}) -> {Tb.Table.has(S.Ue, x, ues) == True{} : Bool}:
  match b:
    case True{}:
      ex = P.U32.eq_of_is_eq(S.Session.ue(t), x, eb)
      %ex : {Tb.Table.has(S.Ue, _, ues) == True{} : Bool}
      P.Bool.and_true_l(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(more, ues), eo)
    case False{}:
      ih(P.Bool.and_true_r(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(more, ues), eo), ew)

# With every session owned, a UE that owns a session holds a context.
def Lv.owner_has(+x: U32, +ss: Tb.Table(S.Session), +ues: Tb.Table(S.Ue), +eo: {S.Sessions.owned(ss, ues) == True{} : Bool}, +ew: {Lv.owner(x, ss) == True{} : Bool}) -> {Tb.Table.has(S.Ue, x, ues) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({Tb.Table.has(S.Ue, x, ues) == True{} : Bool}, P.Refute.bool(ew))
    case (k, +t) <> +more:
      Lv.owner_row(x, t, more, ues, U32.is_eq(S.Session.ue(t), x), {==}, eo, ew, a => b => Lv.owner_has(x, more, ues, a, b))

# A live key is held, when sessions belong to contexts.
def Lv.kd(+st: S.State, +x: U32, +h: Bool, +eh: {Lv.held(st, x) == h : Bool}, +o: Bool, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == o : Bool}, +ek: {Lv.live(st, x) == True{} : Bool}) -> {Lv.keyed(st, x) == True{} : Bool}:
  match h:
    case True{}:
      P.Bool.or_l(Lv.held(st, x), Bool.not(S.Sessions.owned(S.State.sessions(st), S.State.ues(st))), eh)
    case False{}:
      match o:
        case False{}:
          seo = Equal.sym(Bool, S.Sessions.owned(S.State.sessions(st), S.State.ues(st)), False{}, eo)
          P.Bool.or_r(Lv.held(st, x), Bool.not(S.Sessions.owned(S.State.sessions(st), S.State.ues(st))), (%seo : {Bool.not(_) == True{} : Bool}; {==}))
        case True{}:
          ew : {Lv.owner(x, S.State.sessions(st)) == True{} : Bool} = (%eh : {Bool.or(_, Lv.owner(x, S.State.sessions(st))) == True{} : Bool}; ek)
          hh = P.Bool.or_l(Tb.Table.has(S.Ue, x, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{x}), Lv.owner_has(x, S.State.sessions(st), S.State.ues(st), eo, ew))
          Empty.absurd({Lv.keyed(st, x) == True{} : Bool}, P.Refute.true_false(Equal.trans(Bool, True{}, Lv.held(st, x), False{}, Equal.sym(Bool, Lv.held(st, x), True{}, hh), eh)))

def Lv.keyed_of(+st: S.State, +x: U32, +ek: {Lv.live(st, x) == True{} : Bool}) -> {Lv.keyed(st, x) == True{} : Bool}:
  Lv.kd(st, x, Lv.held(st, x), {==}, S.Sessions.owned(S.State.sessions(st), S.State.ues(st)), {==}, ek)

def Lv.get_has(+ues: Tb.Table(S.Ue), +key: U32, +ue: S.Ue, +e: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>}) -> {Tb.Table.has(S.Ue, key, ues) == True{} : Bool}:
  se = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, ues), Some{ue}, e)
  %se : {Tb.Table.present(S.Ue, _) == True{} : Bool}
  {==}

# The context an owner check finds holds its key.
def Lv.pair_has(+ues: Tb.Table(S.Ue), +key: U32, +ue: S.Ue, +assoc: U32, pr: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>} & {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}) -> {Tb.Table.has(S.Ue, key, ues) == True{} : Bool}:
  match pr:
    case (+eg, eb):
      Lv.get_has(ues, key, ue, eg)

def Lv.owned_has(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +ue: S.Ue, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}:
  Lv.pair_has(S.State.ues(st), key, ue, assoc, PT.Own.get(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran, ue, eo))

# Rows of the tables
# ------------------
# A row of a sifting is a row of the table: a context's key is held, a
# session's UE owns a session.

def Lv.hit_present(+v: S.Ue, +m: Maybe<&2, S.Ue>, +b: Bool, +e: {Tb.Table.present(S.Ue, m) == True{} : Bool}) -> {Tb.Table.present(S.Ue, Tb.Table.hit(S.Ue, v, m, b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def Lv.has_cons(+x: U32, +k: U32, +v: S.Ue, +more: Tb.Table(S.Ue), +e: {Tb.Table.has(S.Ue, x, more) == True{} : Bool}) -> {Tb.Table.has(S.Ue, x, (k, v) <> more) == True{} : Bool}:
  Lv.hit_present(v, Tb.Table.get(S.Ue, x, more), U32.is_eq(k, x), e)

def Lv.has_head(+k: U32, +v: S.Ue, +more: Tb.Table(S.Ue)) -> {Tb.Table.has(S.Ue, k, (k, v) <> more) == True{} : Bool}:
  ek = Equal.sym(Bool, U32.is_eq(k, k), True{}, P.U32.is_eq_refl(k))
  %ek : {Tb.Table.present(S.Ue, Tb.Table.hit(S.Ue, v, Tb.Table.get(S.Ue, k, more), _)) == True{} : Bool}
  {==}

def Lv.keys_in(vs: Tb.Table(S.Ue), +ues: Tb.Table(S.Ue)) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case (k, v) <> more:
      Bool.and(Tb.Table.has(S.Ue, k, ues), Lv.keys_in(more, ues))

def Lv.keys_cons(+vs: Tb.Table(S.Ue), +k: U32, +v: S.Ue, +more: Tb.Table(S.Ue), +e: {Lv.keys_in(vs, more) == True{} : Bool}) -> {Lv.keys_in(vs, (k, v) <> more) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case (+k1, +v1) <> +rest:
      P.Bool.and_intro(Tb.Table.has(S.Ue, k1, (k, v) <> more), Lv.keys_in(rest, (k, v) <> more), Lv.has_cons(k1, k, v, more, P.Bool.and_true_l(Tb.Table.has(S.Ue, k1, more), Lv.keys_in(rest, more), e)), Lv.keys_cons(rest, k, v, more, P.Bool.and_true_r(Tb.Table.has(S.Ue, k1, more), Lv.keys_in(rest, more), e)))


def Pv.refl(+ues: Tb.Table(S.Ue)) -> {Lv.keys_in(ues, ues) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      P.Bool.and_intro(Tb.Table.has(S.Ue, k, (k, v) <> more), Lv.keys_in(more, (k, v) <> more), Lv.has_head(k, v, more), Lv.keys_cons(more, k, v, more, Pv.refl(more)))

def Lv.keys_keep(+k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), +b: Bool, +ues: Tb.Table(S.Ue), +hk: {Tb.Table.has(S.Ue, k, ues) == True{} : Bool}, +hr: {Lv.keys_in(rest, ues) == True{} : Bool}) -> {Lv.keys_in(Tb.Table.keep(S.Ue, k, v, rest, b), ues) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Tb.Table.has(S.Ue, k, ues), Lv.keys_in(rest, ues), hk, hr)
    case False{}:
      hr

def Lv.keys_sift(+s: S.Sieve, +ues: Tb.Table(S.Ue)) -> {Lv.keys_in(S.Ues.sift(s, ues), ues) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      Lv.keys_keep(k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), (k, v) <> more, Lv.has_head(k, v, more), Lv.keys_cons(S.Ues.sift(s, more), k, v, more, Lv.keys_sift(s, more)))

def Lv.owner_cons(+x: U32, +k: U32, +t: S.Session, +more: Tb.Table(S.Session), +e: {Lv.owner(x, more) == True{} : Bool}) -> {Lv.owner(x, (k, t) <> more) == True{} : Bool}:
  P.Bool.or_r(U32.is_eq(S.Session.ue(t), x), Lv.owner(x, more), e)

def Lv.owner_head(+k: U32, +t: S.Session, +more: Tb.Table(S.Session)) -> {Lv.owner(S.Session.ue(t), (k, t) <> more) == True{} : Bool}:
  P.Bool.or_l(U32.is_eq(S.Session.ue(t), S.Session.ue(t)), Lv.owner(S.Session.ue(t), more), P.U32.is_eq_refl(S.Session.ue(t)))

def Lv.srows(rows: Tb.Table(S.Session), +ss: Tb.Table(S.Session)) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case (k, t) <> more:
      Bool.and(Lv.owner(S.Session.ue(t), ss), Lv.srows(more, ss))

def Lv.srows_cons(+rows: Tb.Table(S.Session), +k: U32, +t: S.Session, +more: Tb.Table(S.Session), +e: {Lv.srows(rows, more) == True{} : Bool}) -> {Lv.srows(rows, (k, t) <> more) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k1, +t1) <> +rest:
      P.Bool.and_intro(Lv.owner(S.Session.ue(t1), (k, t) <> more), Lv.srows(rest, (k, t) <> more), Lv.owner_cons(S.Session.ue(t1), k, t, more, P.Bool.and_true_l(Lv.owner(S.Session.ue(t1), more), Lv.srows(rest, more), e)), Lv.srows_cons(rest, k, t, more, P.Bool.and_true_r(Lv.owner(S.Session.ue(t1), more), Lv.srows(rest, more), e)))

def Lv.srows_keep(+k: U32, +t: S.Session, +rest: Tb.Table(S.Session), +b: Bool, +ss: Tb.Table(S.Session), +ht: {Lv.owner(S.Session.ue(t), ss) == True{} : Bool}, +hr: {Lv.srows(rest, ss) == True{} : Bool}) -> {Lv.srows(Tb.Table.keep(S.Session, k, t, rest, b), ss) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Lv.owner(S.Session.ue(t), ss), Lv.srows(rest, ss), ht, hr)
    case False{}:
      hr

def Lv.srows_sift(+s: S.SSieve, +ss: Tb.Table(S.Session)) -> {Lv.srows(S.Sessions.sift(s, ss), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      Lv.srows_keep(k, t, S.Sessions.sift(s, more), S.SSieve.keeps(s, k, t), (k, t) <> more, Lv.owner_head(k, t, more), Lv.srows_cons(S.Sessions.sift(s, more), k, t, more, Lv.srows_sift(s, more)))

def Lv.del_if(+st: S.State, +t: S.Session, +seq: U32, +more: Tb.Table(S.Session), +b: Bool, +ht: {Lv.owner(S.Session.ue(t), S.State.sessions(st)) == True{} : Bool}, later: @q:U32 -> {Lv.acts(st, Up.N4.deletions(more, q)) == True{} : Bool}) -> {Lv.acts(st, Up.N4.delete_if(t, seq, q => Up.N4.deletions(more, q), b)) == True{} : Bool}:
  match b:
    case True{}:
      Lv.cons(st, N.Pfcp{Some{S.Session.ue(t)}, Up.N4.delete(S.Session.up_seid(t), seq)}, Up.N4.deletions(more, U32.add(seq, 1)), Lv.owner_live(st, S.Session.ue(t), ht), later(U32.add(seq, 1)))
    case False{}:
      later(seq)

# Session Deletions at the UPF are built from sessions of the state.
def Lv.dels(+st: S.State, +rows: Tb.Table(S.Session), +seq: U32, +e: {Lv.srows(rows, S.State.sessions(st)) == True{} : Bool}) -> {Lv.acts(st, Up.N4.deletions(rows, seq)) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      +hm = P.Bool.and_true_r(Lv.owner(S.Session.ue(t), S.State.sessions(st)), Lv.srows(more, S.State.sessions(st)), e)
      Lv.del_if(st, t, seq, more, S.Session.known(t), P.Bool.and_true_l(Lv.owner(S.Session.ue(t), S.State.sessions(st)), Lv.srows(more, S.State.sessions(st)), e), +q => Lv.dels(st, more, q, hm))

def Lv.dels_free(+st: S.State, +vs: Tb.Table(S.Session)) -> {Lv.free(st, Gsm.Gsm.dels(vs)) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case (k, t) <> +more:
      Lv.dels_free(st, more)

# Sessions forgotten
def Lw.gsm_forget(+st: S.State, +vs: Tb.Table(S.Session), +seq: U32, +e: {Lv.srows(vs, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.forget(vs, seq)) == True{} : Bool}:
  Lv.leaf(st, S.Both{Gsm.Gsm.dels(vs), S.BumpSeq{Up.N4.deletion_count(vs)}}, Up.N4.deletions(vs, seq), Lv.dels(st, vs, seq, e), P.Bool.and_intro(Lv.free(st, Gsm.Gsm.dels(vs)), True{}, Lv.dels_free(st, vs), {==}))

# A row a session search finds is a session of the table: its UE owns a
# session, and it agrees with the UPF when every session does.
def Lv.found(m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +ss: Tb.Table(S.Session)) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{(k, +t)}:
      Bool.and(Lv.owner(S.Session.ue(t), ss), Bool.or(S.SPhase.knows(S.Session.phase(t), S.Session.known(t)), Bool.not(S.Sessions.known(ss))))

def Lv.kn_head(+a: Bool, +y: Bool) -> {Bool.or(a, Bool.not(Bool.and(a, y))) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Lv.kn_cons(+a: Bool, +x: Bool, +y: Bool, +e: {Bool.or(a, Bool.not(y)) == True{} : Bool}) -> {Bool.or(a, Bool.not(Bool.and(x, y))) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match x:
        case True{}:
          e
        case False{}:
          {==}

def Lv.found_cons(+m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +k: U32, +t: S.Session, +more: Tb.Table(S.Session), +e: {Lv.found(m, more) == True{} : Bool}) -> {Lv.found(m, (k, t) <> more) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+k1, +t1)}:
      +a = S.SPhase.knows(S.Session.phase(t1), S.Session.known(t1))
      +y = S.Sessions.known(more)
      P.Bool.and_intro(Lv.owner(S.Session.ue(t1), (k, t) <> more), Bool.or(a, Bool.not(Bool.and(S.SPhase.knows(S.Session.phase(t), S.Session.known(t)), y))), Lv.owner_cons(S.Session.ue(t1), k, t, more, P.Bool.and_true_l(Lv.owner(S.Session.ue(t1), more), Bool.or(a, Bool.not(y)), e)), Lv.kn_cons(a, S.SPhase.knows(S.Session.phase(t), S.Session.known(t)), y, P.Bool.and_true_r(Lv.owner(S.Session.ue(t1), more), Bool.or(a, Bool.not(y)), e)))

def Lv.pick(+key: U32, +t: S.Session, +later: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +hit: Bool, +more: Tb.Table(S.Session), +e: {Lv.found(later, more) == True{} : Bool}) -> {Lv.found(S.Sessions.pick(key, t, later, hit), (key, t) <> more) == True{} : Bool}:
  match hit:
    case True{}:
      +a = S.SPhase.knows(S.Session.phase(t), S.Session.known(t))
      P.Bool.and_intro(Lv.owner(S.Session.ue(t), (key, t) <> more), Bool.or(a, Bool.not(Bool.and(a, S.Sessions.known(more)))), Lv.owner_head(key, t, more), Lv.kn_head(a, S.Sessions.known(more)))
    case False{}:
      Lv.found_cons(later, key, t, more, e)

# The found row agrees with the UPF when every session does.
def Lv.found_known(+m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +ss: Tb.Table(S.Session), +skey: U32, +s: S.Session, +em: {m == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, +h: {Lv.found(m, ss) == True{} : Bool}, +ek: {S.Sessions.known(ss) == True{} : Bool}) -> {S.SPhase.knows(S.Session.phase(s), S.Session.known(s)) == True{} : Bool}:
  sem = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, m, Some{(skey, s)}, em)
  hf : {Lv.found(Some{(skey, s)}, ss) == True{} : Bool} = (%em : {Lv.found(_, ss) == True{} : Bool}; h)
  +a = S.SPhase.knows(S.Session.phase(s), S.Session.known(s))
  sk = Equal.sym(Bool, S.Sessions.known(ss), True{}, ek)
  P.Bool.or_true_l(a, Bool.not(S.Sessions.known(ss)), (%sk : {Bool.not(_) == False{} : Bool}; {==}), P.Bool.and_true_r(Lv.owner(S.Session.ue(s), ss), Bool.or(a, Bool.not(S.Sessions.known(ss))), hf))

# Every row of a table a session search might find: of a sifting, each row.
def Lv.frows(rows: Tb.Table(S.Session), +ss: Tb.Table(S.Session)) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case (+k, +t) <> more:
      Bool.and(Lv.found(Some{(k, t)}, ss), Lv.frows(more, ss))

def Lv.frows_cons(+rows: Tb.Table(S.Session), +k: U32, +t: S.Session, +more: Tb.Table(S.Session), +e: {Lv.frows(rows, more) == True{} : Bool}) -> {Lv.frows(rows, (k, t) <> more) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k1, +t1) <> +rest:
      P.Bool.and_intro(Lv.found(Some{(k1, t1)}, (k, t) <> more), Lv.frows(rest, (k, t) <> more), Lv.found_cons(Some{(k1, t1)}, k, t, more, P.Bool.and_true_l(Lv.found(Some{(k1, t1)}, more), Lv.frows(rest, more), e)), Lv.frows_cons(rest, k, t, more, P.Bool.and_true_r(Lv.found(Some{(k1, t1)}, more), Lv.frows(rest, more), e)))

def Lv.frows_keep(+k: U32, +t: S.Session, +rest: Tb.Table(S.Session), +b: Bool, +ss: Tb.Table(S.Session), +ht: {Lv.found(Some{(k, t)}, ss) == True{} : Bool}, +hr: {Lv.frows(rest, ss) == True{} : Bool}) -> {Lv.frows(Tb.Table.keep(S.Session, k, t, rest, b), ss) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Lv.found(Some{(k, t)}, ss), Lv.frows(rest, ss), ht, hr)
    case False{}:
      hr

def Lv.frows_sift(+s: S.SSieve, +ss: Tb.Table(S.Session)) -> {Lv.frows(S.Sessions.sift(s, ss), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      Lv.frows_keep(k, t, S.Sessions.sift(s, more), S.SSieve.keeps(s, k, t), (k, t) <> more, Lv.pick(k, t, None{}, True{}, more, {==}), Lv.frows_cons(S.Sessions.sift(s, more), k, t, more, Lv.frows_sift(s, more)))

def Lv.by_seq(+seq: U32, +ss: Tb.Table(S.Session)) -> {Lv.found(S.Sessions.by_seq(seq, ss), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Lv.pick(key, t, S.Sessions.by_seq(seq, more), U32.is_eq(S.Session.seq(t), seq), more, Lv.by_seq(seq, more))

def Lv.sget_row(+k: U32, +s: S.Session, +k0: U32, +t: S.Session, +more: Tb.Table(S.Session), +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +e: {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), b) == Some{s} : Maybe<&2, S.Session>}, ih: {Tb.Table.get(S.Session, k, more) == Some{s} : Maybe<&2, S.Session>} -> {Lv.found(Some{(k, s)}, more) == True{} : Bool}) -> {Lv.found(Some{(k, s)}, (k0, t) <> more) == True{} : Bool}:
  match b:
    case True{}:
      et = P.Some.inj(S.Session, t, s, e)
      %et : {Lv.found(Some{(k, _)}, (k0, t) <> more) == True{} : Bool}
      +a = S.SPhase.knows(S.Session.phase(t), S.Session.known(t))
      P.Bool.and_intro(Lv.owner(S.Session.ue(t), (k0, t) <> more), Bool.or(a, Bool.not(Bool.and(a, S.Sessions.known(more)))), Lv.owner_head(k0, t, more), Lv.kn_head(a, S.Sessions.known(more)))
    case False{}:
      Lv.found_cons(Some{(k, s)}, k0, t, more, ih(e))

# The session under a key is a session of the table.
def Lv.sget(+ss: Tb.Table(S.Session), +k: U32, +s: S.Session, +e: {Tb.Table.get(S.Session, k, ss) == Some{s} : Maybe<&2, S.Session>}) -> {Lv.found(Some{(k, s)}, ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({Lv.found(Some{(k, s)}, []) == True{} : Bool}, P.Refute.none_some(S.Session, s, e))
    case (+k0, +t) <> +more:
      Lv.sget_row(k, s, k0, t, more, U32.is_eq(k0, k), {==}, e, ih => Lv.sget(more, k, s, ih))

# A session found under its key keeps the Accept's bound when its table does.
def Lv.sbound_row(+k: U32, +s: S.Session, +k0: U32, +t: S.Session, +more: Tb.Table(S.Session), +b: Bool, +e: {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), b) == Some{s} : Maybe<&2, S.Session>}, ih: {Tb.Table.get(S.Session, k, more) == Some{s} : Maybe<&2, S.Session>} -> {Bool.or(Gsm.Gsm.phase_bounded(S.Session.phase(s)), Bool.not(Gsm.Gsm.bounded(more))) == True{} : Bool}) -> {Bool.or(Gsm.Gsm.phase_bounded(S.Session.phase(s)), Bool.not(Gsm.Gsm.bounded((k0, t) <> more))) == True{} : Bool}:
  match b:
    case True{}:
      et = P.Some.inj(S.Session, t, s, e)
      %et : {Bool.or(Gsm.Gsm.phase_bounded(S.Session.phase(_)), Bool.not(Gsm.Gsm.bounded((k0, t) <> more))) == True{} : Bool}
      Lv.kn_head(Gsm.Gsm.phase_bounded(S.Session.phase(t)), Gsm.Gsm.bounded(more))
    case False{}:
      Lv.kn_cons(Gsm.Gsm.phase_bounded(S.Session.phase(s)), Gsm.Gsm.phase_bounded(S.Session.phase(t)), Gsm.Gsm.bounded(more), ih(e))

def Lv.sbound(+ss: Tb.Table(S.Session), +k: U32, +s: S.Session, +e: {Tb.Table.get(S.Session, k, ss) == Some{s} : Maybe<&2, S.Session>}) -> {Bool.or(Gsm.Gsm.phase_bounded(S.Session.phase(s)), Bool.not(Gsm.Gsm.bounded(ss))) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({Bool.or(Gsm.Gsm.phase_bounded(S.Session.phase(s)), Bool.not(Gsm.Gsm.bounded([]))) == True{} : Bool}, P.Refute.none_some(S.Session, s, e))
    case (+k0, +t) <> +more:
      Lv.sbound_row(k, s, k0, t, more, U32.is_eq(k0, k), e, ih => Lv.sbound(more, k, s, ih))

def Lv.by_psi(+ue: U32, +psi: U32, +ss: Tb.Table(S.Session)) -> {Lv.found(S.Sessions.by_psi(ue, psi, ss), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Lv.pick(key, t, S.Sessions.by_psi(ue, psi, more), Bool.and(U32.is_eq(S.Session.ue(t), ue), U32.is_eq(S.Session.psi(t), psi)), more, Lv.by_psi(ue, psi, more))

# Contexts put and released
# -------------------------

# The target released.
def Lw.ho_drop(+st: S.State, +key: U32, +leg: S.Leg, +cause: G.Cause, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.acts(st, Ho.Ho.drop(key, leg, cause)) == True{} : Bool}:
  match leg:
    case S.Asked{+t}:
      Lv.cons(st, N.UeSend{t, Ho.Ho.stream(), key, Ho.Ho.release_amf(key, cause)}, [], ek, {==})
    case S.Acked{+t, +r, +s, ts}:
      Lv.cons(st, N.Release{t, s, key, r, cause}, [], ek, {==})

def Lw.ho_leg_drop(+st: S.State, +key: U32, +p: S.Phase, +cause: G.Cause, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.acts(st, Ho.Ho.leg_drop(key, p, cause)) == True{} : Bool}:
  match p:
    case S.Handover{guard, ctx, nh, source, +leg}:
      Lw.ho_drop(st, key, leg, cause, ek)
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.evict(+st: S.State, +vs: Tb.Table(S.Ue), +q: U32, +e: {Lv.keys_in(vs, S.State.ues(st)) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.evict(vs, S.State.sessions(st), q)) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case (+key, +v) <> +more:
      +gone = S.Sessions.of_ue(key, S.State.sessions(st))
      +ek = Lv.has_live(st, key, P.Bool.and_true_l(Tb.Table.has(S.Ue, key, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e))
      +cause = N.Ngap.nas_cause(G.CauseNas.deregister())
      +rel : N.Act = N.Release{S.Ue.assoc(v), S.Ue.stream(v), key, S.Ue.ran_id(v), cause}
      +xs : List<&2, N.Act> = List.append(&2, N.Act, Up.N4.deletions(gone, q), Ho.Ho.leg_drop(key, S.Ue.phase(v), cause))
      Lv.join(st, N.Out.prepend(rel, (S.BumpSeq{Up.N4.deletion_count(gone)}, xs)), Gmm.Gmm.evict(more, S.State.sessions(st), U32.add(q, Up.N4.deletion_count(gone))), Lv.prepend(st, rel, (S.BumpSeq{Up.N4.deletion_count(gone)}, xs), ek, Lv.leaf(st, S.BumpSeq{Up.N4.deletion_count(gone)}, xs, Lv.append(st, Up.N4.deletions(gone, q), Ho.Ho.leg_drop(key, S.Ue.phase(v), cause), Lv.dels(st, gone, q, Lv.srows_sift(S.SOf{key}, S.State.sessions(st))), Lw.ho_leg_drop(st, key, S.Ue.phase(v), cause, ek)), {==})), Lw.evict(st, more, U32.add(q, Up.N4.deletion_count(gone)), P.Bool.and_true_r(Tb.Table.has(S.Ue, key, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e)))

def Lw.place(+st: S.State, +key: U32, +ue: S.Ue, +eg: {S.Phase.guarded(S.Ue.phase(ue)) == True{} : Bool}, +es: {S.Ue.single(ue) == True{} : Bool}, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.place(st, key, ue)) == True{} : Bool}:
  Lv.join(st, (S.Put{key, ue}, []), Gmm.Gmm.evict(S.Ues.evicted(key, ue, S.State.ues(st)), S.State.sessions(st), S.State.pfcp_seq(st)), P.Bool.and_intro(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), S.Ue.single(ue)), Lv.keyed_of(st, key, ek), P.Bool.and_intro(S.Phase.guarded(S.Ue.phase(ue)), S.Ue.single(ue), eg, es)), Lw.evict(st, S.Ues.evicted(key, ue, S.State.ues(st)), S.State.pfcp_seq(st), Lv.keys_sift(S.Victims{key, ue}, S.State.ues(st))))

def Lw.forget(+st: S.State, +key: U32) -> {Lv.okf(st, Gmm.Gmm.forget(st, key)) == True{} : Bool}:
  +gone = S.Sessions.of_ue(key, S.State.sessions(st))
  Lv.leaf(st, S.Both{S.Del{key}, S.BumpSeq{Up.N4.deletion_count(gone)}}, Up.N4.deletions(gone, S.State.pfcp_seq(st)), Lv.dels(st, gone, S.State.pfcp_seq(st), Lv.srows_sift(S.SOf{key}, S.State.sessions(st))), {==})

# 5GSM
# ----

def Lw.out_dl(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +plain: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.okf(st, N.Out.dl(key, ue, ctx, plain)) == True{} : Bool}:
  +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.Ciphered{}, plain)
  +x : N.Act = N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), Sec.Nas.Protected.msg(p)}
  Lv.leaf(st, S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))}, [x], Lv.cons(st, x, [], ek, {==}), Lv.g_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p), ec))

# A verified message not acted on: the context's phase keeps its NAS context.
def Lw.out_verified(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +why: String, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, N.Out.verified(key, ue, ctx, why)) == True{} : Bool}:
  Lv.free_homed(st, S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), ctx)}, S.State.ues(st), Lv.g_ctx(S.Ue.phase(ue), ctx, ec))

def Lw.to_ue_ctx(+st: S.State, +key: U32, +ue: S.Ue, +psi: U32, +sm: B.Bytes(), +ctx: Maybe<&2, Sec.Nas.Ctx>, +ek: {Lv.live(st, key) == True{} : Bool}, +ec: {S.Phase.ctx(S.Ue.phase(ue)) == ctx : Maybe<&2, Sec.Nas.Ctx>}) -> {Lv.okf(st, Gsm.Gsm.to_ue_ctx(key, ue, psi, sm, ctx)) == True{} : Bool}:
  match ctx:
    case None{}:
      {==}
    case Some{+c}:
      Lw.out_dl(st, key, ue, c, Gsm.Gsm.dl_transport(psi, sm), ek, Lv.has_ctx(S.Ue.phase(ue), c, ec))

def Lw.to_ue_m(+st: S.State, +key: U32, +psi: U32, +sm: B.Bytes(), +m: Maybe<&2, S.Ue>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.to_ue_m(key, psi, sm, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.to_ue_ctx(st, key, ue, psi, sm, S.Phase.ctx(S.Ue.phase(ue)), ek, {==})

def Lw.one(+st: S.State, +skey: U32, +s: S.Session, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.srows([(skey, s)], S.State.sessions(st)) == True{} : Bool}:
  P.Bool.and_intro(Lv.owner(S.Session.ue(s), S.State.sessions(st)), True{}, es, {==})

def Lw.give_up_m(+st: S.State, +skey: U32, +s: S.Session, +sm: B.Bytes(), +seq: U32, +m: Maybe<&2, S.Ue>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.give_up_m(skey, s, sm, seq, m)) == True{} : Bool}:
  Lv.join(st, Gsm.Gsm.to_ue_m(S.Session.ue(s), S.Session.psi(s), sm, m), Gsm.Gsm.forget([(skey, s)], seq), Lw.to_ue_m(st, S.Session.ue(s), S.Session.psi(s), sm, m, Lv.owner_live(st, S.Session.ue(s), es)), Lw.gsm_forget(st, [(skey, s)], seq, Lw.one(st, skey, s, es)))

def Lw.give_up(+st: S.State, +skey: U32, +s: S.Session, +sm: B.Bytes(), +seq: U32, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.give_up(st, skey, s, sm, seq)) == True{} : Bool}:
  Lw.give_up_m(st, skey, s, sm, seq, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), es)

def Lw.abort(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +cause: U32, +seq: U32, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.abort(st, skey, s, pti, cause, seq)) == True{} : Bool}:
  Lw.give_up(st, skey, s, Gsm.Gsm.reject(S.Session.psi(s), pti, cause), seq, es)

def Lw.drop(+st: S.State, +skey: U32, +s: S.Session, +seq: U32, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.drop(st, skey, s, seq)) == True{} : Bool}:
  Lw.give_up(st, skey, s, Gsm.Gsm.release_command(S.Session.psi(s)), seq, es)


def Lv.hit_same(+u1: S.Ue, +u2: S.Ue, +m1: Maybe<&2, S.Ue>, +m2: Maybe<&2, S.Ue>, +b: Bool, +e: {Tb.Table.present(S.Ue, m1) == Tb.Table.present(S.Ue, m2) : Bool}) -> {Tb.Table.present(S.Ue, Tb.Table.hit(S.Ue, u1, m1, b)) == Tb.Table.present(S.Ue, Tb.Table.hit(S.Ue, u2, m2, b)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def Lv.has_rephase(+x: U32, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue)) -> {Tb.Table.has(S.Ue, x, S.Ues.rephase(key, p, ues)) == Tb.Table.has(S.Ue, x, ues) : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      Lv.hit_same(S.Ue.rephase_if(u, p, U32.is_eq(k, key)), u, Tb.Table.get(S.Ue, x, S.Ues.rephase(key, p, more)), Tb.Table.get(S.Ue, x, more), U32.is_eq(k, x), Lv.has_rephase(x, key, p, more))

# The one path that puts a session: its UE is the context the message names.
def Lw.create(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, +ip: U32, +teid: U32, +seid: U32, +v4v6: Bool, +dns: Bool, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}, +es: {S.Ids.seid(seid) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.create(st, key, ue, ctx, cfg, psi, pti, ip, teid, seid, v4v6, dns)) == True{} : Bool}:
  +seq = S.State.pfcp_seq(st)
  +ph = S.Phase.with_ctx(S.Ue.phase(ue), ctx)
  +s : S.Session = S.Session{S.SId{key, psi, ip, teid}, S.SVar{[], seq, S.Creating{S.Guard{0}, pti, Gsm.Gsm.accept(cfg, psi, pti, ip, dns, v4v6), Up.N4.establish(cfg, seid, ip, teid, seq)}}}
  +x : N.Act = N.Pfcp{Some{key}, Up.N4.establish(cfg, seid, ip, teid, seq)}
  +y : N.Act = N.TimerStart{Some{key}, seid, Up.N4.t1_ms()}
  +vs = S.Sessions.evicted(seid, s, S.State.sessions(st))
  +rep = S.Ues.rephase(key, ph, S.State.ues(st))
  +ek = Lv.has_live(st, key, eh)
  hr = Equal.sym(Bool, Tb.Table.has(S.Ue, key, rep), Tb.Table.has(S.Ue, key, S.State.ues(st)), Lv.has_rephase(key, key, ph, S.State.ues(st)))
  +old = Bool.and(Tb.Table.has(S.Ue, key, rep), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s))))
  +put = Bool.and(S.Ids.seid(seid), old)
  +ha = Lv.append(st, [x, y], Up.N4.deletions(vs, U32.add(seq, 1)), Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), Lv.dels(st, vs, U32.add(seq, 1), Lv.srows_sift(S.SVictims{seid, s}, S.State.sessions(st))))
  +hg = P.Bool.and_intro(Bool.and(S.Phase.guarded(ph), S.Ue.fits(ph, Tb.Table.get(S.Ue, key, S.State.ues(st)))), True{}, Lv.free_homed(st, S.Rephase{key, ph}, S.State.ues(st), Lv.g_ctx(S.Ue.phase(ue), ctx, ec)), {==})
  +ho = P.Bool.and_intro(Tb.Table.has(S.Ue, key, rep), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s))), (%hr : {_ == True{} : Bool}; eh), {==})
  +hp = P.Bool.and_intro(S.Ids.seid(seid), old, es, ho)
  +hb = P.Bool.and_intro(put, Bool.and(Lv.homed(st, Gsm.Gsm.dels(vs), rep), True{}), hp, P.Bool.and_intro(Lv.homed(st, Gsm.Gsm.dels(vs), rep), True{}, Lv.free_homed(st, Gsm.Gsm.dels(vs), rep, Lv.dels_free(st, vs)), {==}))
  P.Bool.and_intro(Lv.acts(st, List.append(&2, N.Act, [x, y], Up.N4.deletions(vs, U32.add(seq, 1)))), Bool.and(Bool.and(Bool.and(S.Phase.guarded(ph), S.Ue.fits(ph, Tb.Table.get(S.Ue, key, S.State.ues(st)))), True{}), Bool.and(put, Bool.and(Lv.homed(st, Gsm.Gsm.dels(vs), rep), True{}))), ha, P.Bool.and_intro(Bool.and(Bool.and(S.Phase.guarded(ph), S.Ue.fits(ph, Tb.Table.get(S.Ue, key, S.State.ues(st)))), True{}), Bool.and(put, Bool.and(Lv.homed(st, Gsm.Gsm.dels(vs), rep), True{})), hg, hb))

# What a request checks out to keys its session with a local SEID.
def Ck.seid_ok(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+k}:
      S.Ids.seid(k)

def Ck.ok(c: Gsm.Check) -> Bool:
  match c:
    case Gsm.Refuse{cause}:
      True{}
    case Gsm.Go{v4v6, dns, ip, teid, +seid}:
      S.Ids.seid(seid)

def Ck.grant(+v4v6: Bool, +dns: Bool, +ip: Maybe<&2, U32>, +teid: Maybe<&2, U32>, +seid: Maybe<&2, U32>, +h: {Ck.seid_ok(seid) == True{} : Bool}) -> {Ck.ok(Gsm.Gsm.grant(v4v6, dns, ip, teid, seid)) == True{} : Bool}:
  match ip teid seid:
    case Some{a} Some{t} Some{k}:
      h
    case Some{a} Some{t} None{}:
      {==}
    case Some{a} None{} Some{k}:
      {==}
    case Some{a} None{} None{}:
      {==}
    case None{} Some{t} Some{k}:
      {==}
    case None{} Some{t} None{}:
      {==}
    case None{} None{} Some{k}:
      {==}
    case None{} None{} None{}:
      {==}

def Ck.even(+w: U32) -> {S.Ids.odd(U32.and(4294967294, w)) == False{} : Bool}:
  match w:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Ck.hit(+k: U32, +ss: Tb.Table(S.Session), +later: Maybe<&2, U32>, +ok: Bool, +eok: {Bool.not(Bool.or(U32.is_eq(k, 0), Tb.Table.has(S.Session, k, ss))) == ok : Bool}, +ev: {S.Ids.odd(k) == False{} : Bool}, +hl: {Ck.seid_ok(later) == True{} : Bool}) -> {Ck.seid_ok(Tb.Table.hit(U32, k, later, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      nz = P.Bool.or_false_l(U32.is_eq(k, 0), Tb.Table.has(S.Session, k, ss), P.Bool.not_true(Bool.or(U32.is_eq(k, 0), Tb.Table.has(S.Session, k, ss)), eok))
      sev = Equal.sym(Bool, S.Ids.odd(k), False{}, ev)
      snz = Equal.sym(Bool, U32.is_eq(k, 0), False{}, nz)
      (%sev : {Bool.and(Bool.not(_), Bool.not(U32.is_eq(k, 0))) == True{} : Bool}; (%snz : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}; {==}))
    case False{}:
      hl

def Ck.seid_from(+ss: Tb.Table(S.Session), +words: B.Bytes()) -> {Ck.seid_ok(Gsm.Ip.seid_from(ss, words)) == True{} : Bool}:
  match words:
    case a <> b <> c <> d <> more:
      +k = U32.and(4294967294, N.Ngap.of_big([a, b, c, d]))
      Ck.hit(k, ss, Gsm.Ip.seid_from(ss, more), Bool.not(Bool.or(U32.is_eq(k, 0), Tb.Table.has(S.Session, k, ss))), {==}, Ck.even(N.Ngap.of_big([a, b, c, d])), Ck.seid_from(ss, more))
    case a <> b <> c <> Nil{}:
      {==}
    case a <> b <> Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case Nil{}:
      {==}

def Ck.allocate(+r: Maybe<&2, U32>, +v4v6: Bool, +dns: Bool, +cfg: S.Cfg, +ss: Tb.Table(S.Session), +entropy: B.Bytes()) -> {Ck.ok(Gsm.Gsm.allocate(r, v4v6, dns, cfg, ss, entropy)) == True{} : Bool}:
  match r:
    case Some{cause}:
      {==}
    case None{}:
      Ck.grant(v4v6, dns, Gsm.Ip.alloc(cfg, ss), Gsm.Ip.teid_from(ss, Gsm.Ip.around(entropy, 20n)), Gsm.Ip.seid_from(ss, Gsm.Ip.around(entropy, 24n)), Ck.seid_from(ss, Gsm.Ip.around(entropy, 24n)))

def Ck.validate(+cfg: S.Cfg, +psi: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, +up: Bool, +ss: Tb.Table(S.Session), +entropy: B.Bytes()) -> {Ck.ok(Gsm.Gsm.validate(cfg, psi, mm_opts, sm_opts, up, ss, entropy)) == True{} : Bool}:
  +t = I.Opts.t1(I.Iei.pdu_session_type(), sm_opts)
  Ck.allocate(Gsm.Gsm.pick(Bool.and(U32.is_lt(0, psi), U32.is_lt(psi, 16)), 95, Gsm.Gsm.pick(Gsm.Gsm.request_type_ok(I.Opts.t1(I.Iei.request_type(), mm_opts)), 31, Gsm.Gsm.pick(Gsm.Gsm.dnn_ok(cfg, I.Opts.find(I.Iei.dnn(), mm_opts)), 27, Gsm.Gsm.pick(Gsm.Gsm.slice_ok(cfg, I.Opts.find(I.Iei.s_nssai(), mm_opts)), 70, Gsm.Gsm.pick(up, 38, Gsm.Gsm.pick(Gsm.Gsm.type_ok(t), 50, None{})))))), Gsm.Gsm.v4v6(t), Gsm.Gsm.dns_asked(I.Opts.find(I.Iei.extended_pco(), sm_opts)), cfg, ss, entropy)

def Lw.checked(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, +c: Gsm.Check, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}, +eck: {Ck.ok(c) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.checked(st, key, ue, ctx, cfg, psi, pti, c)) == True{} : Bool}:
  match c:
    case Gsm.Refuse{+cause}:
      Lv.ok_of(st, Gsm.Gsm.dl(key, ue, ctx, psi, Gsm.Gsm.reject(psi, pti, cause)), Lw.out_dl(st, key, ue, ctx, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause)), Lv.has_live(st, key, eh), ec))
    case Gsm.Go{+v4v6, +dns, +ip, +teid, +seid}:
      Lw.create(st, key, ue, ctx, cfg, psi, pti, ip, teid, seid, v4v6, dns, eh, ec, eck)

def Lw.gsm_with_cfg(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +psi: U32, +pti: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +cfg: Maybe<&2, S.Cfg>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.with_cfg(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy, cfg)) == True{} : Bool}:
  match cfg:
    case None{}:
      Lw.out_verified(st, key, ue, ctx, "5GSM: no configuration", ec)
    case Some{+c}:
      Lw.checked(st, key, ue, ctx, c, psi, pti, Gsm.Gsm.validate(c, psi, mm_opts, sm_opts, Up.N4.up(st), S.State.sessions(st), entropy), eh, ec, Ck.validate(c, psi, mm_opts, sm_opts, Up.N4.up(st), S.State.sessions(st), entropy))

def Lw.establish(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +psi: U32, +pti: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.establish(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy)) == True{} : Bool}:
  Lw.gsm_with_cfg(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy, S.State.config(st), eh, ec)

def Lw.message(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +mm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Sm.Sm>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.message(st, key, ue, ctx, mm_opts, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      Lw.out_verified(st, key, ue, ctx, "5GSM: message not understood", ec)
    case Done{Sm.Sm{+psi, +pti, mt, fields, +opts}}:
      match mt:
        case Sm.EstablishmentRequest{}:
          Lw.establish(st, key, ue, ctx, psi, pti, mm_opts, opts, entropy, eh, ec)
        case Sm.EstablishmentAccept{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec)
        case Sm.EstablishmentReject{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec)
        case Sm.ModificationRequest{}:
          Lv.ok_of(st, Gsm.Gsm.dl(key, ue, ctx, psi, Gsm.Gsm.modification_reject(psi, pti)), Lw.out_dl(st, key, ue, ctx, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.modification_reject(psi, pti)), Lv.has_live(st, key, eh), ec))
        case Sm.ModificationReject{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec)
        case Sm.ReleaseRequest{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec)
        case Sm.ReleaseCommand{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec)
        case Sm.ReleaseComplete{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec)
        case Sm.SmStatus{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec)

def Lw.n1(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +mm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +container: B.Bytes(), +n1: Bool, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.n1(st, key, ue, ctx, mm_opts, entropy, container, n1)) == True{} : Bool}:
  match n1:
    case True{}:
      Lw.message(st, key, ue, ctx, mm_opts, entropy, Sm.Sm.read(container), eh, ec)
    case False{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: payload container not N1 SM information", ec)

def Lw.ul_transport(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +entropy: B.Bytes(), +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.ul_transport(st, key, ue, ctx, fields, opts, entropy)) == True{} : Bool}:
  Lw.n1(st, key, ue, ctx, opts, entropy, I.Fields.lve2(fields), U32.is_eq(I.Fields.byte1(fields), 1), eh, ec)


# The UPF's answers
# --------------

# A UP SEID the UPF answers with has eight octets (pfcp.fseid.decode_valid).
def Lv.seid_ok(m: Maybe<&2, B.Bytes()>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Nat.is_eq(List.length(&2, U32, x), 8n)

def Lv.fseid_valid(+f: Pf.Fseid, +body: B.Bytes(), h: {Pf.Fseid.valid(f) == True{} : Bool} & {Pf.Fseid.write(f) == body : B.Bytes()}) -> {Pf.Fseid.valid(f) == True{} : Bool}:
  (v, w) = h
  v

def Lv.seid_read(+body: B.Bytes(), +r: Result<&2, &2, B.Err, Pf.Fseid>, +er: {Pf.Fseid.read(body) == r : Result<&2, &2, B.Err, Pf.Fseid>}) -> {Lv.seid_ok(Up.N4.seid_of(r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{Pf.Fseid{+seid, +v4, +v6}}:
      P.Bool.and_true_l(Nat.is_eq(List.length(&2, U32, seid), 8n), Bool.and(Pf.Addr.valid(v4, 4n), Pf.Addr.valid(v6, 16n)), Lv.fseid_valid(Pf.Fseid{seid, v4, v6}, body, L.pfcp.fseid.decode_valid(body, Pf.Fseid{seid, v4, v6}, er)))

def Lv.fseid_of(+m: Maybe<&2, T.Tlv>) -> {Lv.seid_ok(Up.N4.fseid_of(m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+t}:
      Lv.seid_read(T.Tlv.body(t), Pf.Fseid.read(T.Tlv.body(t)), {==})

def Lv.up_seid(+msg: Pf.Msg) -> {Lv.seid_ok(Up.N4.up_seid(msg)) == True{} : Bool}:
  Lv.fseid_of(T.Tlvs.find(Pf.Ie.fseid(), Pf.Msg.ies(msg)))

# What a session search finds, split.
def Lv.owns(+skey: U32, +s: S.Session, +ss: Tb.Table(S.Session), +e: {Lv.found(Some{(skey, s)}, ss) == True{} : Bool}) -> {Lv.owner(S.Session.ue(s), ss) == True{} : Bool}:
  P.Bool.and_true_l(Lv.owner(S.Session.ue(s), ss), Bool.or(S.SPhase.knows(S.Session.phase(s), S.Session.known(s)), Bool.not(S.Sessions.known(ss))), e)

def Lv.knows(+skey: U32, +s: S.Session, +ss: Tb.Table(S.Session), +e: {Lv.found(Some{(skey, s)}, ss) == True{} : Bool}) -> {Bool.or(S.SPhase.knows(S.Session.phase(s), S.Session.known(s)), Bool.not(S.Sessions.known(ss))) == True{} : Bool}:
  P.Bool.and_true_r(Lv.owner(S.Session.ue(s), ss), Bool.or(S.SPhase.knows(S.Session.phase(s), S.Session.known(s)), Bool.not(S.Sessions.known(ss))), e)

def Lv.owner_var(+s: S.Session, +v: S.SVar, +ss: Tb.Table(S.Session), +es: {Lv.owner(S.Session.ue(s), ss) == True{} : Bool}) -> {Lv.owner(S.Session.ue(S.Session.with_var(s, v)), ss) == True{} : Bool}:
  match s:
    case S.Session{id, var}:
      es

def Lw.setup_gone(+st: S.State, +skey: U32, +s: S.Session, +up_seid: B.Bytes(), +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.forget([(skey, S.Session.with_var(s, S.SVar{up_seid, S.Session.seq(s), S.Active{}}))], S.State.pfcp_seq(st))) == True{} : Bool}:
  +s2 = S.Session.with_var(s, S.SVar{up_seid, S.Session.seq(s), S.Active{}})
  Lw.gsm_forget(st, [(skey, s2)], S.State.pfcp_seq(st), Lw.one(st, skey, s2, Lv.owner_var(s, S.SVar{up_seid, S.Session.seq(s), S.Active{}}, S.State.sessions(st), es)))

def Lw.setup_ue(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +accept: Sm.Sm, +up_seid: B.Bytes(), +ue: S.Ue, +ctx: Maybe<&2, Sec.Nas.Ctx>, +cfg: Maybe<&2, S.Cfg>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +ec: {S.Phase.ctx(S.Ue.phase(ue)) == ctx : Maybe<&2, Sec.Nas.Ctx>}, +e8: {Nat.is_eq(List.length(&2, U32, up_seid), 8n) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.setup_ue(st, skey, s, pti, accept, up_seid, ue, ctx, cfg)) == True{} : Bool}:
  match ctx cfg:
    case Some{+c} Some{+cf}:
      +p : Sec.Nas.Protected = Sec.Nas.protect(c, Sec.Ciphered{}, Gsm.Gsm.dl_transport(S.Session.psi(s), Sm.Sm.write(accept)))
      +x : N.Act = N.PduSetup{S.Ue.assoc(ue), S.Ue.stream(ue), S.Session.ue(s), S.Ue.ran_id(ue), S.Session.psi(s), S.Cfg.sst(cf), Sec.Nas.Protected.msg(p), Gsm.Gsm.transfer(cf, S.Session.teid(s))}
      +y : N.Act = N.TimerStart{Some{S.Session.ue(s)}, skey, Up.N4.t1_ms()}
      +ek = Lv.owner_live(st, S.Session.ue(s), es)
      +v : S.SVar = S.SVar{up_seid, S.Session.seq(s), S.Setting{S.Guard{0}, pti}}
      +hv = P.Bool.or_l(Lv.var_ok(v), Bool.not(S.Sessions.known(S.State.sessions(st))), e8)
      Lv.leaf(st, S.Both{S.Rephase{S.Session.ue(s), S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))}, S.Revar{skey, v}}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), P.Bool.and_intro(Bool.and(S.Phase.guarded(S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))), S.Phase.idle(S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p)))), Lv.revar_ok(st, v), Lv.g_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p), Lv.has_ctx(S.Ue.phase(ue), c, ec)), hv))
    case Some{c} None{}:
      Lw.setup_gone(st, skey, s, up_seid, es)
    case None{} Some{cf}:
      Lw.setup_gone(st, skey, s, up_seid, es)
    case None{} None{}:
      Lw.setup_gone(st, skey, s, up_seid, es)

# 5GMM
# ----
# Each lemma follows one procedure; key is the context it acts for, live.

def Lw.release(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.release(st, key, ue, cause)) == True{} : Bool}:
  +ur = S.Ue.with_phase(ue, S.Releasing{S.Guard{0}})
  +rel : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}
  +ts : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  +more : List<&2, N.Act> = ts <> Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause)
  Lv.prepend(st, rel, N.Out.also(Gmm.Gmm.place(st, key, ur), more), ek, Lv.also(st, Gmm.Gmm.place(st, key, ur), more, Lw.place(st, key, ur, Lv.g_phase(ue, S.Releasing{S.Guard{0}}), Lv.s_phase(ue, S.Releasing{S.Guard{0}}), ek), Lv.cons(st, ts, Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause), ek, Lw.ho_leg_drop(st, key, S.Ue.phase(ue), cause, ek))))

def Lw.refuse(+st: S.State, +key: U32, +ue: S.Ue, +nas: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.refuse(st, key, ue, nas)) == True{} : Bool}:
  Lv.prepend(st, Gmm.Gmm.dl(key, ue, nas), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified())), ek, Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek))

def Lw.reject(+st: S.State, +key: U32, +ue: S.Ue, +cause: U32, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.reject(st, key, ue, cause)) == True{} : Bool}:
  Lw.refuse(st, key, ue, Gmm.Gmm.registration_reject(cause), ek)

def Lw.auth_reject(+st: S.State, +key: U32, +ue: S.Ue, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.auth_reject(st, key, ue)) == True{} : Bool}:
  Lv.prepend(st, Gmm.Gmm.dl(key, ue, Gmm.Gmm.authentication_reject()), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure())), ek, Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure()), ek))


def Lw.identity_ask(+st: S.State, +key: U32, +ue: S.Ue, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.identity_ask(st, key, ue)) == True{} : Bool}:
  +nas = Gmm.Gmm.identity_request()
  +ue2 = S.Ue.with_dl(ue, S.Identifying{S.Guard{0}}, nas)
  +x : N.Act = Gmm.Gmm.dl(key, ue2, nas)
  +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  Lv.also(st, Gmm.Gmm.place(st, key, ue2), [x, y], Lw.place(st, key, ue2, Lv.g_dl(ue, S.Identifying{S.Guard{0}}, nas), Lv.s_dl(ue, S.Identifying{S.Guard{0}}, nas), ek), Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})))

def Lw.challenge(+st: S.State, +key: U32, +ue: S.Ue, +sub: Au.Subscriber, +snn: B.Bytes(), +entropy: B.Bytes(), +resynced: Bool, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.challenge(st, key, ue, sub, snn, entropy, resynced)) == True{} : Bool}:
  +sub2 = Au.Subscriber.with_sqn(sub, Au.Sqn.next(Au.Subscriber.sqn(sub)))
  +av = Au.Av.make(sub2, snn, List.take(&2, U32, entropy, 16n))
  +nas = Gmm.Gmm.auth_request(0, av)
  +ue2 = S.Ue.with_dl(ue, S.Authenticating{S.Guard{0}, av, resynced, Au.Subscriber.supi(sub2)}, nas)
  +x : N.Act = Gmm.Gmm.dl(key, ue2, nas)
  +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  +tx : S.Tx = S.Subs{Au.Subscribers.update(sub2, S.State.subs(st))}
  Lv.join(st, Gmm.Gmm.place(st, key, ue2), (tx, [x, y]), Lw.place(st, key, ue2, Lv.g_dl(ue, S.Authenticating{S.Guard{0}, av, resynced, Au.Subscriber.supi(sub2)}, nas), Lv.s_dl(ue, S.Authenticating{S.Guard{0}, av, resynced, Au.Subscriber.supi(sub2)}, nas), ek), Lv.leaf(st, tx, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), {==}))

def Lw.by_sub(+st: S.State, +key: U32, +ue: S.Ue, +cfg: S.Cfg, +m: Maybe<&2, Au.Subscriber>, +entropy: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.by_sub(st, key, ue, cfg, m, entropy)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.reject(st, key, ue, 7, ek)
    case Some{+sub}:
      Lw.challenge(st, key, ue, sub, Au.Ausf.snn(S.Cfg.plmn(cfg)), entropy, False{}, ek)

def Lw.by_supi(+st: S.State, +key: U32, +ue: S.Ue, +cfg: S.Cfg, +r: Result<&2, &2, B.Err, Su.Supi>, +entropy: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.by_supi(st, key, ue, cfg, r, entropy)) == True{} : Bool}:
  match r:
    case Fail{e}:
      Lw.reject(st, key, ue, 7, ek)
    case Done{Su.Imsi{+plmn, +msin}}:
      Lw.by_sub(st, key, ue, cfg, Au.Subscribers.find(List.append(&2, U32, Pl.Plmn.mcc(plmn), List.append(&2, U32, Pl.Plmn.mnc(plmn), msin)), S.State.subs(st)), entropy, ek)

def Lw.with_cfg(+st: S.State, +key: U32, +ue: S.Ue, +suci: Su.Suci, +entropy: B.Bytes(), +cfg: Maybe<&2, S.Cfg>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.with_cfg(st, key, ue, suci, entropy, cfg)) == True{} : Bool}:
  match cfg:
    case None{}:
      Lw.reject(st, key, ue, 7, ek)
    case Some{+c}:
      Lw.by_supi(st, key, ue, c, Su.Suci.deconceal(S.Cfg.suci_key(c), suci), entropy, ek)

def Lw.identified(+st: S.State, +key: U32, +ue: S.Ue, +suci: Su.Suci, +entropy: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.identified(st, key, ue, suci, entropy)) == True{} : Bool}:
  Lw.with_cfg(st, key, ue, suci, entropy, S.State.config(st), ek)

def Lw.proceed(+st: S.State, +key: U32, +ue: S.Ue, +how: Gmm.Start, +entropy: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.proceed(st, key, ue, how, entropy)) == True{} : Bool}:
  match how:
    case Gmm.Identified{+suci}:
      Lw.identified(st, key, ue, suci, entropy, ek)
    case Gmm.Ask{}:
      Lw.identity_ask(st, key, ue, ek)
    case Gmm.Unknown{}:
      Lw.reject(st, key, ue, 7, ek)

def Lw.register(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +r: Mi.MobileId.Res(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.register(st, key, assoc, stream, entropy, ran, nas, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+id}:
      +fresh : S.Ue = Gmm.Gmm.fresh(assoc, ran, stream, nas)
      Lv.join(st, (S.BumpUe{key}, []), Gmm.Gmm.proceed(st, key, fresh, Gmm.Gmm.start_of(id), entropy), {==}, Lw.proceed(st, key, fresh, Gmm.Gmm.start_of(id), entropy, ek))

def Lw.serve(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +ran: B.Bytes(), +nas: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.serve(st, key, assoc, stream, ran, nas)) == True{} : Bool}:
  +fresh : S.Ue = Gmm.Gmm.fresh(assoc, ran, stream, nas)
  Lv.join(st, (S.BumpUe{key}, []), Gmm.Gmm.refuse(st, key, fresh, Gmm.Gmm.service_reject()), {==}, Lw.refuse(st, key, fresh, Gmm.Gmm.service_reject(), ek))

def Lw.initial_mm(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +m: Mm.Mm, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.initial_mm(st, key, assoc, stream, entropy, ran, nas, m)) == True{} : Bool}:
  match m:
    case Mm.Mm{mt, +fields, opts}:
      match mt:
        case Mm.RegistrationRequest{}:
          Lw.register(st, key, assoc, stream, entropy, ran, nas, Mi.MobileId.read(I.Fields.lve2(fields)), ek)
        case Mm.RegistrationAccept{}:
          {==}
        case Mm.RegistrationComplete{}:
          {==}
        case Mm.RegistrationReject{}:
          {==}
        case Mm.DeregistrationRequestUe{}:
          {==}
        case Mm.DeregistrationAcceptUe{}:
          {==}
        case Mm.ConfigurationUpdateCommand{}:
          {==}
        case Mm.AuthenticationRequest{}:
          {==}
        case Mm.AuthenticationResponse{}:
          {==}
        case Mm.AuthenticationReject{}:
          {==}
        case Mm.AuthenticationFailure{}:
          {==}
        case Mm.IdentityRequest{}:
          {==}
        case Mm.IdentityResponse{}:
          {==}
        case Mm.SecurityModeCommand{}:
          {==}
        case Mm.SecurityModeComplete{}:
          {==}
        case Mm.SecurityModeReject{}:
          {==}
        case Mm.Status{}:
          {==}
        case Mm.UlNasTransport{}:
          {==}
        case Mm.DlNasTransport{}:
          {==}
        case Mm.ServiceRequest{}:
          Lw.serve(st, key, assoc, stream, ran, nas, ek)
        case Mm.ServiceReject{}:
          {==}

def Lw.initial_nas(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +r: Result<&2, &2, B.Err, Mm.Mm>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.initial_nas(st, key, assoc, stream, entropy, ran, nas, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+m}:
      Lw.initial_mm(st, key, assoc, stream, entropy, ran, nas, m, ek)

def Lw.initial_key(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +m: Maybe<&2, U32>, +em: {S.State.fresh(st) == m : Maybe<&2, U32>}) -> {Lv.okf(st, Gmm.Gmm.initial_key(st, assoc, stream, entropy, ran, nas, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.initial_nas(st, key, assoc, stream, entropy, ran, nas, Mm.Mm.read(nas), Lv.fresh_live(st, key, em))

def Lw.initial(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +v: V.InitialUEMessage.View) -> {Lv.okf(st, Gmm.Gmm.initial(st, assoc, stream, entropy, v)) == True{} : Bool}:
  match v:
    case V.InitialUEMessage.View{+ran_ue_ngap_id, +nas_pdu, userlocationinformation, rrcestablishmentcause, fiveg_s_tmsi, amfsetid, allowednssai, selectedplmnidentity, iabnodeindication, cemodebsupport_indicator, npn_accessinformation}:
      Lw.initial_key(st, assoc, stream, entropy, ran_ue_ngap_id, Gmm.Gmm.unprotected(nas_pdu), S.State.fresh(st), {==})

def Lw.initial_of_view(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, V.InitialUEMessage.View>) -> {Lv.okf(st, Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.initial(st, assoc, stream, entropy, v)


def Lw.secure(+st: S.State, +key: U32, +ue: S.Ue, +supi: B.Digits(), +k_amf: B.Bytes(), +nea: Sec.Nas.Ea, +nia: Sec.Nas.Ia, +caps: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.secure(st, key, ue, supi, k_amf, nea, nia, caps)) == True{} : Bool}:
  +ctx : Sec.Nas.Ctx = Sec.Ctx{Sec.Keys{Kd.kdf.k_nas_int(k_amf, Sec.Nas.Ia.id(nia)), Kd.kdf.k_nas_enc(k_amf, Sec.Nas.Ea.id(nea)), nea, nia, 1}, Sec.Nas.Count.zero(), None{}}
  +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.IntegrityNew{}, Gmm.Gmm.security_mode_command(U32.or(U32.shln(Sec.Nas.Ea.id(nea), 4n), Sec.Nas.Ia.id(nia)), S.Ue.ngksi(ue), caps))
  +ue2 = S.Ue.with_dl(S.Ue.with_supi(ue, supi), S.SecurityMode{S.Guard{0}, Sec.Nas.Protected.ctx(p), k_amf}, Sec.Nas.Protected.msg(p))
  +x : N.Act = Gmm.Gmm.dl(key, ue2, Sec.Nas.Protected.msg(p))
  +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  Lv.also(st, Gmm.Gmm.place(st, key, ue2), [x, y], Lw.place(st, key, ue2, Lv.g_dl(S.Ue.with_supi(ue, supi), S.SecurityMode{S.Guard{0}, Sec.Nas.Protected.ctx(p), k_amf}, Sec.Nas.Protected.msg(p)), Lv.s_dl(S.Ue.with_supi(ue, supi), S.SecurityMode{S.Guard{0}, Sec.Nas.Protected.ctx(p), k_amf}, Sec.Nas.Protected.msg(p)), ek), Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})))

def Lw.algorithms(+st: S.State, +key: U32, +ue: S.Ue, +supi: B.Digits(), +k_amf: B.Bytes(), +caps: B.Bytes(), +mea: Maybe<&2, Sec.Nas.Ea>, +mia: Maybe<&2, Sec.Nas.Ia>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.algorithms(st, key, ue, supi, k_amf, caps, mea, mia)) == True{} : Bool}:
  match mea mia:
    case Some{+a} Some{+b}:
      Lw.secure(st, key, ue, supi, k_amf, a, b, caps, ek)
    case Some{a} None{}:
      Lw.reject(st, key, ue, 23, ek)
    case None{} Some{b}:
      Lw.reject(st, key, ue, 23, ek)
    case None{} None{}:
      Lw.reject(st, key, ue, 23, ek)

def Lw.keys(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +cfg: Maybe<&2, S.Cfg>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.keys(st, key, ue, av, supi, cfg)) == True{} : Bool}:
  match cfg:
    case Some{+c}:
      +caps = N.Ue.caps(ue)
      Lw.algorithms(st, key, ue, supi, Au.Ausf.k_amf(av, Au.Ausf.snn(S.Cfg.plmn(c)), supi), caps, Gmm.Alg.pick_ea(S.Cfg.nea(c), N.Ngap.cap_byte(caps, 0n)), Gmm.Alg.pick_ia(S.Cfg.nia(c), N.Ngap.cap_byte(caps, 1n)), ek)
    case None{}:
      Lw.auth_reject(st, key, ue, ek)

def Lw.verified(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +ok: Bool, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.verified(st, key, ue, av, supi, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.keys(st, key, ue, av, supi, S.State.config(st), ek)
    case False{}:
      Lw.auth_reject(st, key, ue, ek)

def Lw.response(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +res: Maybe<&2, B.Bytes()>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.response(st, key, ue, av, supi, res)) == True{} : Bool}:
  match res:
    case None{}:
      Lw.auth_reject(st, key, ue, ek)
    case Some{+r}:
      Lw.verified(st, key, ue, av, supi, Au.Ausf.verify(av, r), ek)

def Lw.resynced(+st: S.State, +key: U32, +ue: S.Ue, +sub: Au.Subscriber, +cfg: S.Cfg, +entropy: B.Bytes(), +m: Maybe<&2, B.Bytes()>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.resynced(st, key, ue, sub, cfg, entropy, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.auth_reject(st, key, ue, ek)
    case Some{+sqn_ms}:
      Lw.challenge(st, key, ue, Au.Subscriber.with_sqn(sub, sqn_ms), Au.Ausf.snn(S.Cfg.plmn(cfg)), entropy, True{}, ek)

def Lw.resync_sub(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +auts: B.Bytes(), +entropy: B.Bytes(), +cfg: S.Cfg, +m: Maybe<&2, Au.Subscriber>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.resync_sub(st, key, ue, av, auts, entropy, cfg, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.auth_reject(st, key, ue, ek)
    case Some{+sub}:
      Lw.resynced(st, key, ue, sub, cfg, entropy, Au.Ausf.resync(sub, Au.Av.rand(av), auts), ek)

def Lw.resync(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +auts: B.Bytes(), +entropy: B.Bytes(), +supi: B.Digits(), +cfg: Maybe<&2, S.Cfg>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.resync(st, key, ue, av, auts, entropy, supi, cfg)) == True{} : Bool}:
  match cfg:
    case Some{+c}:
      Lw.resync_sub(st, key, ue, av, auts, entropy, c, Au.Subscribers.find(supi, S.State.subs(st)), ek)
    case None{}:
      Lw.auth_reject(st, key, ue, ek)

def Lw.failure_kind(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +auts: Maybe<&2, B.Bytes()>, +entropy: B.Bytes(), +retry: Bool, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.failure_kind(st, key, ue, av, supi, auts, entropy, retry)) == True{} : Bool}:
  match auts retry:
    case Some{+a} True{}:
      Lw.resync(st, key, ue, av, a, entropy, supi, S.State.config(st), ek)
    case Some{a} False{}:
      Lw.auth_reject(st, key, ue, ek)
    case None{} True{}:
      Lw.auth_reject(st, key, ue, ek)
    case None{} False{}:
      Lw.auth_reject(st, key, ue, ek)

def Lw.failure(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +resynced: Bool, +supi: B.Digits(), +cause: U32, +auts: Maybe<&2, B.Bytes()>, +entropy: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.failure(st, key, ue, av, resynced, supi, cause, auts, entropy)) == True{} : Bool}:
  Lw.failure_kind(st, key, ue, av, supi, auts, entropy, Bool.and(U32.is_eq(cause, 21), Bool.not(resynced)), ek)

def Lw.identity_answer(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Mi.MobileId.Res(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.identity_answer(st, key, ue, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      Lw.reject(st, key, ue, 7, ek)
    case Done{Mi.NoId{}}:
      Lw.reject(st, key, ue, 7, ek)
    case Done{Mi.Suci{+suci}}:
      Lw.identified(st, key, ue, suci, entropy, ek)
    case Done{Mi.Guti{plmn, region, amf, tmsi}}:
      Lw.reject(st, key, ue, 7, ek)
    case Done{Mi.Imei{digits}}:
      Lw.reject(st, key, ue, 7, ek)
    case Done{Mi.Imeisv{digits}}:
      Lw.reject(st, key, ue, 7, ek)
    case Done{Mi.STmsi{amf, tmsi}}:
      Lw.reject(st, key, ue, 7, ek)


def Lw.phase(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +p: S.Phase, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.phase(st, key, ue, entropy, mt, fields, opts, p)) == True{} : Bool}:
  match mt:
    case Mm.RegistrationRequest{}:
      {==}
    case Mm.RegistrationAccept{}:
      {==}
    case Mm.RegistrationComplete{}:
      {==}
    case Mm.RegistrationReject{}:
      {==}
    case Mm.DeregistrationRequestUe{}:
      {==}
    case Mm.DeregistrationAcceptUe{}:
      {==}
    case Mm.ConfigurationUpdateCommand{}:
      {==}
    case Mm.AuthenticationRequest{}:
      {==}
    case Mm.AuthenticationResponse{}:
      match p:
        case S.Created{}:
          {==}
        case S.Identifying{guard}:
          {==}
        case S.Authenticating{guard, +av, +resynced, +supi}:
          Lw.response(st, key, ue, av, supi, I.Opts.find(I.Iei.authentication_response_parameter(), opts), ek)
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{guard, old, nh, response, complete}:
          {==}
        case S.Registered{old, nh}:
          {==}
        case S.Switching{guard, old, nh, released}:
          {==}
        case S.Handover{guard, old, nh, source, leg}:
          {==}
        case S.Releasing{guard}:
          {==}
    case Mm.AuthenticationReject{}:
      {==}
    case Mm.AuthenticationFailure{}:
      match p:
        case S.Created{}:
          {==}
        case S.Identifying{guard}:
          {==}
        case S.Authenticating{guard, +av, +resynced, +supi}:
          Lw.failure(st, key, ue, av, resynced, supi, I.Fields.byte1(fields), I.Opts.find(I.Iei.authentication_failure_parameter(), opts), entropy, ek)
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{guard, old, nh, response, complete}:
          {==}
        case S.Registered{old, nh}:
          {==}
        case S.Switching{guard, old, nh, released}:
          {==}
        case S.Handover{guard, old, nh, source, leg}:
          {==}
        case S.Releasing{guard}:
          {==}
    case Mm.IdentityRequest{}:
      {==}
    case Mm.IdentityResponse{}:
      match p:
        case S.Created{}:
          {==}
        case S.Identifying{guard}:
          Lw.identity_answer(st, key, ue, entropy, Mi.MobileId.read(I.Fields.lve1(fields)), ek)
        case S.Authenticating{guard, av, resynced, supi}:
          {==}
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{guard, old, nh, response, complete}:
          {==}
        case S.Registered{old, nh}:
          {==}
        case S.Switching{guard, old, nh, released}:
          {==}
        case S.Handover{guard, old, nh, source, leg}:
          {==}
        case S.Releasing{guard}:
          {==}
    case Mm.SecurityModeCommand{}:
      {==}
    case Mm.SecurityModeComplete{}:
      {==}
    case Mm.SecurityModeReject{}:
      {==}
    case Mm.Status{}:
      {==}
    case Mm.UlNasTransport{}:
      {==}
    case Mm.DlNasTransport{}:
      {==}
    case Mm.ServiceRequest{}:
      {==}
    case Mm.ServiceReject{}:
      {==}

def Lw.plain(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Mm.Mm>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.plain(st, key, ue, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{Mm.Mm{+mt, +fields, +opts}}:
      Lw.phase(st, key, ue, entropy, mt, fields, opts, S.Ue.phase(ue), ek)


def Lw.sm_complete(+st: S.State, +key: U32, +ue: S.Ue, +k_amf: B.Bytes(), +ctx: Sec.Nas.Ctx, +count: Sec.Nas.Count, +opts: List<&2, I.Ie>, +cfg: Maybe<&2, S.Cfg>, +m: Maybe<&2, U32>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.sm_complete(st, key, ue, k_amf, ctx, count, opts, cfg, m)) == True{} : Bool}:
  match cfg m:
    case Some{+c} Some{+tmsi}:
      +reg = I.Bytes.or(I.Opts.find(I.Iei.nas_message_container(), opts), S.Ue.reg(ue))
      +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.Ciphered{}, Gmm.Gmm.registration_accept(c, tmsi))
      +k_gnb = Kd.kdf.k_gnb(k_amf, Sec.Nas.Count.value(count))
      +ph : S.Phase = S.ContextSetup{S.Guard{0}, Sec.Nas.Protected.ctx(p), S.Nh.initial(k_amf, k_gnb), False{}, False{}}
      +ue2 = S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(ue, ph, Sec.Nas.Protected.msg(p)), reg), tmsi)
      +x : N.Act = N.Ics{S.Ue.assoc(ue2), S.Ue.stream(ue2), key, S.Ue.ran_id(ue2), c, N.Ue.caps(ue2), k_gnb, Sec.Nas.Protected.msg(p)}
      +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
      Lv.also(st, Gmm.Gmm.place(st, key, ue2), [x, y], Lw.place(st, key, ue2, Lv.g_ics(ue, ph, Sec.Nas.Protected.msg(p), reg, tmsi), Lv.s_ics(ue, ph, Sec.Nas.Protected.msg(p), reg, tmsi), ek), Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})))
    case Some{c} None{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek)
    case None{} Some{t}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek)
    case None{} None{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek)

def Lw.setup_done(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +response: Bool, +complete: Bool, +both: Bool) -> {Lv.okf(st, Gmm.Gmm.setup_done(st, key, ue, guard, ctx, nh, response, complete, both)) == True{} : Bool}:
  match both:
    case True{}:
      {==}
    case False{}:
      {==}

def Lw.setup_step(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +response: Bool, +complete: Bool) -> {Lv.okf(st, Gmm.Gmm.setup_step(st, key, ue, guard, ctx, nh, response, complete)) == True{} : Bool}:
  Lw.setup_done(st, key, ue, guard, ctx, nh, response, complete, Bool.and(response, complete))

def Lw.dereg_answer(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +switch_off: Bool, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.dereg_answer(st, key, ue, ctx, switch_off)) == True{} : Bool}:
  match switch_off:
    case True{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister()), ek)
    case False{}:
      Lv.prepend(st, Gmm.Gmm.dl(key, ue, Sec.Nas.Protected.msg(Sec.Nas.protect(ctx, Sec.Ciphered{}, Gmm.Gmm.deregistration_accept()))), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister())), ek, Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister()), ek))

def Lw.deregister(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +kind: U32, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.deregister(st, key, ue, ctx, kind)) == True{} : Bool}:
  Lw.dereg_answer(st, key, ue, ctx, Bool.not(U32.is_eq(U32.and(kind, 8), 0)), ek)


# A verified 5GMM message: the UL NAS Transport of a registered UE may put a session.
def Lw.sphase(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +count: Sec.Nas.Count, +ctx: Sec.Nas.Ctx, +mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +p: S.Phase, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.sphase(st, key, ue, entropy, count, ctx, mt, fields, opts, p)) == True{} : Bool}:
  match mt:
    case Mm.RegistrationRequest{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.RegistrationAccept{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.RegistrationComplete{}:
      match p:
        case S.Created{}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Identifying{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Authenticating{guard, av, resynced, supi}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.SecurityMode{guard, old, k_amf}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.ContextSetup{+guard, old, nh, +response, complete}:
          Lv.ok_of(st, Gmm.Gmm.setup_step(st, key, ue, guard, ctx, nh, response, True{}), Lw.setup_step(st, key, ue, guard, ctx, nh, response, True{}))
        case S.Registered{old, nh}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Switching{guard, old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Handover{guard, old, nh, source, leg}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Releasing{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.RegistrationReject{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.DeregistrationRequestUe{}:
      match p:
        case S.Created{}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Identifying{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Authenticating{guard, av, resynced, supi}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.SecurityMode{guard, old, k_amf}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.ContextSetup{guard, old, nh, response, complete}:
          Lv.ok_of(st, Gmm.Gmm.deregister(st, key, ue, ctx, I.Fields.byte1(fields)), Lw.deregister(st, key, ue, ctx, I.Fields.byte1(fields), Lv.has_live(st, key, eh)))
        case S.Registered{old, nh}:
          Lv.ok_of(st, Gmm.Gmm.deregister(st, key, ue, ctx, I.Fields.byte1(fields)), Lw.deregister(st, key, ue, ctx, I.Fields.byte1(fields), Lv.has_live(st, key, eh)))
        case S.Switching{guard, old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Handover{guard, old, nh, source, leg}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Releasing{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.DeregistrationAcceptUe{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.ConfigurationUpdateCommand{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.AuthenticationRequest{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.AuthenticationResponse{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.AuthenticationReject{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.AuthenticationFailure{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.IdentityRequest{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.IdentityResponse{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.SecurityModeCommand{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.SecurityModeComplete{}:
      match p:
        case S.Created{}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Identifying{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Authenticating{guard, av, resynced, supi}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.SecurityMode{guard, old, +k_amf}:
          Lv.ok_of(st, Gmm.Gmm.sm_complete(st, key, ue, k_amf, ctx, count, opts, S.State.config(st), Gmm.Gmm.tmsi(S.State.ues(st), List.drop(&2, U32, entropy, 16n))), Lw.sm_complete(st, key, ue, k_amf, ctx, count, opts, S.State.config(st), Gmm.Gmm.tmsi(S.State.ues(st), List.drop(&2, U32, entropy, 16n)), Lv.has_live(st, key, eh)))
        case S.ContextSetup{guard, old, nh, response, complete}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Registered{old, nh}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Switching{guard, old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Handover{guard, old, nh, source, leg}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Releasing{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.SecurityModeReject{}:
      match p:
        case S.Created{}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Identifying{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Authenticating{guard, av, resynced, supi}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.SecurityMode{guard, old, k_amf}:
          Lv.ok_of(st, Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified())), Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), Lv.has_live(st, key, eh)))
        case S.ContextSetup{guard, old, nh, response, complete}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Registered{old, nh}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Switching{guard, old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Handover{guard, old, nh, source, leg}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Releasing{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.Status{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.UlNasTransport{}:
      match p:
        case S.Created{}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Identifying{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Authenticating{guard, av, resynced, supi}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.SecurityMode{guard, old, k_amf}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.ContextSetup{guard, old, nh, response, complete}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Registered{old, nh}:
          Lw.ul_transport(st, key, ue, ctx, fields, opts, entropy, eh, ec)
        case S.Switching{guard, old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Handover{guard, old, nh, source, leg}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
        case S.Releasing{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.DlNasTransport{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.ServiceRequest{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)
    case Mm.ServiceReject{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec)

def Lw.protected(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +count: Sec.Nas.Count, +ctx: Sec.Nas.Ctx, +r: Result<&2, &2, B.Err, Mm.Mm>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.protected(st, key, ue, entropy, count, ctx, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not understood", ec)
    case Done{Mm.Mm{+mt, +fields, +opts}}:
      Lw.sphase(st, key, ue, entropy, count, ctx, mt, fields, opts, S.Ue.phase(ue), eh, ec)

def Lw.opened(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Sec.Nas.Unprotected>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.opened(st, key, ue, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{Sec.Unprotected{prot, +plain, +count, +ctx}}:
      Lw.protected(st, key, ue, entropy, count, ctx, Mm.Mm.read(plain), eh, ec)

def Lw.secured(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +nas: B.Bytes(), +m: Maybe<&2, Sec.Nas.Ctx>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +em: {S.Phase.ctx(S.Ue.phase(ue)) == m : Maybe<&2, Sec.Nas.Ctx>}) -> {Lv.ok(st, Gmm.Gmm.secured(st, key, ue, entropy, nas, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lv.ok_of(st, Gmm.Gmm.plain(st, key, ue, entropy, Mm.Mm.read(nas)), Lw.plain(st, key, ue, entropy, Mm.Mm.read(nas), Lv.has_live(st, key, eh)))
    case Some{+ctx}:
      Lw.opened(st, key, ue, entropy, Sec.Nas.unprotect(ctx, nas), eh, Lv.has_ctx(S.Ue.phase(ue), ctx, em))

def Lw.mm(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +nas: B.Bytes(), +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.mm(st, key, ue, entropy, nas)) == True{} : Bool}:
  Lw.secured(st, key, ue, entropy, nas, S.Phase.ctx(S.Ue.phase(ue)), eh, {==})

def Lw.uplink_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +nas: B.Bytes(), +entropy: B.Bytes(), +m: Maybe<&2, S.Ue>, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> {Lv.ok(st, Gmm.Gmm.uplink_ue(st, assoc, key, nas, entropy, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.mm(st, key, ue, entropy, nas, Lv.owned_has(st, assoc, key, ran, ue, eo))


def Lw.uplink_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +nas: B.Bytes(), +entropy: B.Bytes(), +m: Maybe<&2, U32>) -> {Lv.ok(st, Gmm.Gmm.uplink_key(st, assoc, ran, nas, entropy, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.uplink_ue(st, assoc, key, ran, nas, entropy, Gmm.Gmm.owner(st, assoc, key, ran), {==})

def Lw.uplink(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +v: V.UplinkNASTransport.View) -> {Lv.ok(st, Gmm.Gmm.uplink(st, assoc, stream, entropy, v)) == True{} : Bool}:
  match v:
    case V.UplinkNASTransport.View{+amf_ue_ngap_id, +ran_ue_ngap_id, +nas_pdu, userlocationinformation}:
      Lw.uplink_key(st, assoc, ran_ue_ngap_id, nas_pdu, entropy, N.Ngap.ue_key(amf_ue_ngap_id))

def Lw.uplink_of_view(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, V.UplinkNASTransport.View>) -> {Lv.ok(st, Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.uplink(st, assoc, stream, entropy, v)


def Lw.setup_phase(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase) -> {Lv.okf(st, Gmm.Gmm.setup_phase(st, key, ue, p)) == True{} : Bool}:
  match p:
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, old, k_amf}:
      {==}
    case S.ContextSetup{+guard, +ctx, nh, response, +complete}:
      Lw.setup_step(st, key, ue, guard, ctx, nh, True{}, complete)
    case S.Registered{old, nh}:
      {==}
    case S.Switching{guard, old, nh, released}:
      {==}
    case S.Handover{guard, old, nh, source, leg}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.ics_response_ue(+st: S.State, +assoc: U32, +key: U32, +m: Maybe<&2, S.Ue>) -> {Lv.okf(st, Gmm.Gmm.ics_response_ue(st, assoc, key, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.setup_phase(st, key, ue, S.Ue.phase(ue))


def Lw.ics_response_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +m: Maybe<&2, U32>) -> {Lv.okf(st, Gmm.Gmm.ics_response_key(st, assoc, ran, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.ics_response_ue(st, assoc, key, Gmm.Gmm.owner(st, assoc, key, ran))

def Lw.ics_response(+st: S.State, +assoc: U32, +v: V.InitialContextSetupResponse.View) -> {Lv.okf(st, Gmm.Gmm.ics_response(st, assoc, v)) == True{} : Bool}:
  match v:
    case V.InitialContextSetupResponse.View{+amf_ue_ngap_id, +ran_ue_ngap_id, diagnostics}:
      Lw.ics_response_key(st, assoc, ran_ue_ngap_id, N.Ngap.ue_key(amf_ue_ngap_id))

def Lw.ics_response_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.InitialContextSetupResponse.View>) -> {Lv.okf(st, Gmm.Gmm.ics_response_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.ics_response(st, assoc, v)

def Lw.release_request_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +cause: G.Cause, +m: Maybe<&2, S.Ue>, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Gmm.Gmm.release_request_ue(st, assoc, key, cause, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.release(st, key, ue, cause, Lv.has_live(st, key, Lv.owned_has(st, assoc, key, ran, ue, eo)))


def Lw.release_request_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +cause: G.Cause, +m: Maybe<&2, U32>) -> {Lv.okf(st, Gmm.Gmm.release_request_key(st, assoc, ran, cause, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.release_request_ue(st, assoc, key, ran, cause, Gmm.Gmm.owner(st, assoc, key, ran), {==})

def Lw.release_request(+st: S.State, +assoc: U32, +v: V.UEContextReleaseRequest.View) -> {Lv.okf(st, Gmm.Gmm.release_request(st, assoc, v)) == True{} : Bool}:
  match v:
    case V.UEContextReleaseRequest.View{+amf_ue_ngap_id, +ran_ue_ngap_id, pdusessionresourcelistcxtrelreq, +cause}:
      Lw.release_request_key(st, assoc, ran_ue_ngap_id, cause, N.Ngap.ue_key(amf_ue_ngap_id))

def Lw.release_request_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>) -> {Lv.okf(st, Gmm.Gmm.release_request_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.release_request(st, assoc, v)

def Lw.release_complete_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +m: Maybe<&2, S.Ue>, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Gmm.Gmm.release_complete_ue(st, assoc, key, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      +ek = Lv.has_live(st, key, Lv.owned_has(st, assoc, key, ran, ue, eo))
      +c = N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified())
      +tail : List<&2, N.Act> = List.append(&2, N.Act, Ho.Ho.leg_drop(key, S.Ue.phase(ue), c), [N.Note{F.Info{}, "NGAP: UE context released"}])
      +more = List.append(&2, N.Act, N.Guard.cancel(key, S.Ue.guard(ue)), tail)
      Lv.also(st, Gmm.Gmm.forget(st, key), more, Lw.forget(st, key), Lv.append(st, N.Guard.cancel(key, S.Ue.guard(ue)), tail, Lv.cancel(st, key, S.Ue.guard(ue)), Lv.append(st, Ho.Ho.leg_drop(key, S.Ue.phase(ue), c), [N.Note{F.Info{}, "NGAP: UE context released"}], Lw.ho_leg_drop(st, key, S.Ue.phase(ue), c, ek), {==})))


def Lw.release_complete_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +m: Maybe<&2, U32>) -> {Lv.okf(st, Gmm.Gmm.release_complete_key(st, assoc, ran, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.release_complete_ue(st, assoc, key, ran, Gmm.Gmm.owner(st, assoc, key, ran), {==})

def Lw.release_complete(+st: S.State, +assoc: U32, +v: V.UEContextReleaseComplete.View) -> {Lv.okf(st, Gmm.Gmm.release_complete(st, assoc, v)) == True{} : Bool}:
  match v:
    case V.UEContextReleaseComplete.View{+amf_ue_ngap_id, +ran_ue_ngap_id, userlocationinformation, pdusessionresourcelistcxtrelcpl, diagnostics}:
      Lw.release_complete_key(st, assoc, ran_ue_ngap_id, N.Ngap.ue_key(amf_ue_ngap_id))

def Lw.release_complete_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>) -> {Lv.okf(st, Gmm.Gmm.release_complete_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.release_complete(st, assoc, v)

# The guard fired.
def Lw.ho_expiry(+st: S.State, +key: U32, +ue: S.Ue, +leg: S.Leg, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.acts(st, Ho.Ho.expiry(key, ue, leg)) == True{} : Bool}:
  match leg:
    case S.Asked{+t}:
      +x : N.Act = N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.preparation_failure(key, S.Ue.ran_id(ue), Ho.Ho.radio(G.CauseRadioNetwork.tngrelocprep_expiry()))}
      +y : N.Act = N.UeSend{t, Ho.Ho.stream(), key, Ho.Ho.release_amf(key, Ho.Ho.radio(G.CauseRadioNetwork.tngrelocprep_expiry()))}
      Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==}))
    case S.Acked{+t, +r, +s, ts}:
      Lv.cons(st, N.Release{t, s, key, r, Ho.Ho.radio(G.CauseRadioNetwork.tngrelocoverall_expiry())}, [], ek, {==})

def Lw.ho_expired(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +ok: Bool, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Ho.Ho.expired(key, ue, ctx, nh, leg, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      +n : List<&2, N.Act> = [N.Note{F.Warn{}, "NGAP: N2 handover guard expired; the UE stays with its owner"}]
      Lv.leaf(st, S.Rephase{key, S.Registered{ctx, nh}}, List.append(&2, N.Act, Ho.Ho.expiry(key, ue, leg), n), Lv.append(st, Ho.Ho.expiry(key, ue, leg), n, Lw.ho_expiry(st, key, ue, leg, ek), {==}), {==})
    case False{}:
      +x : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), Ho.Ho.radio(G.CauseRadioNetwork.unspecified())}
      +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
      +c = Ho.Ho.radio(G.CauseRadioNetwork.unspecified())
      Lv.leaf(st, S.Rephase{key, S.Releasing{S.Guard{0}}}, x <> y <> Ho.Ho.drop(key, leg, c), Lv.cons(st, x, y <> Ho.Ho.drop(key, leg, c), ek, Lv.cons(st, y, Ho.Ho.drop(key, leg, c), ek, Lw.ho_drop(st, key, leg, c, ek))), {==})


def Lw.retry_if(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +p: S.Phase, +ok: Bool, +ek: {Lv.live(st, key) == True{} : Bool}, +eg: {Bool.and(S.Phase.guarded(S.Phase.with_guard(p, S.Guard{U32.add(S.Guard.retries(guard), 1)})), S.Phase.idle(S.Phase.with_guard(p, S.Guard{U32.add(S.Guard.retries(guard), 1)}))) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.retry_if(st, key, ue, guard, p, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      +x : N.Act = Gmm.Gmm.dl(key, ue, S.Ue.last_dl(ue))
      +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
      Lv.leaf(st, S.Rephase{key, S.Phase.with_guard(p, S.Guard{U32.add(S.Guard.retries(guard), 1)})}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), eg)
    case False{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek)

def Lw.expired(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.expired(st, key, ue, p)) == True{} : Bool}:
  match p:
    case S.Created{}:
      {==}
    case S.Identifying{+guard}:
      Lw.retry_if(st, key, ue, guard, S.Identifying{guard}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek, {==})
    case S.Authenticating{+guard, +av, +resynced, +supi}:
      Lw.retry_if(st, key, ue, guard, S.Authenticating{guard, av, resynced, supi}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek, {==})
    case S.SecurityMode{+guard, +ctx, +k_amf}:
      Lw.retry_if(st, key, ue, guard, S.SecurityMode{guard, ctx, k_amf}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek, {==})
    case S.ContextSetup{+guard, +ctx, nh, +response, +complete}:
      Lw.retry_if(st, key, ue, guard, S.ContextSetup{guard, ctx, nh, response, complete}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek, {==})
    case S.Registered{ctx, nh}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      Lw.release(st, key, ue, N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified()), ek)
    case S.Handover{+guard, +ctx, +nh, source, +leg}:
      Lw.ho_expired(st, key, ue, ctx, nh, leg, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek)
    case S.Releasing{guard}:
      Lv.also(st, Gmm.Gmm.forget(st, key), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}], Lw.forget(st, key), {==})


def Lw.setup(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +accept: Sm.Sm, +up_seid: B.Bytes(), +m: Maybe<&2, S.Ue>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +e8: {Nat.is_eq(List.length(&2, U32, up_seid), 8n) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.setup(st, skey, s, pti, accept, up_seid, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.setup_gone(st, skey, s, up_seid, es)
    case Some{+ue}:
      Lw.setup_ue(st, skey, s, pti, accept, up_seid, ue, S.Phase.ctx(S.Ue.phase(ue)), S.State.config(st), es, {==}, e8)

def Lw.established_as(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +accept: Sm.Sm, +ok: Bool, +up: Maybe<&2, B.Bytes()>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +eu: {Lv.seid_ok(up) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.established_as(st, skey, s, pti, accept, ok, up)) == True{} : Bool}:
  match ok up:
    case True{} Some{+up_seid}:
      Lw.setup(st, skey, s, pti, accept, up_seid, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), es, eu)
    case True{} None{}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es)
    case False{} Some{up_seid}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es)
    case False{} None{}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es)

def Lw.established_phase(+st: S.State, +skey: U32, +s: S.Session, +msg: Pf.Msg, +p: S.SPhase, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.established_phase(st, skey, s, msg, p)) == True{} : Bool}:
  match p:
    case S.Creating{+guard, +pti, +accept, request}:
      Lw.established_as(st, skey, s, pti, accept, Up.N4.accepted(Up.N4.cause(msg)), Up.N4.up_seid(msg), es, Lv.up_seid(msg))
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Lw.established(+st: S.State, +msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.established(st, msg, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.established_phase(st, skey, s, msg, S.Session.phase(s), Lv.owns(skey, s, S.State.sessions(st), em))

# Path Switch: a repointed session settled
# ----------------------------------------

def Lw.repoint_done(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.Session.known(s), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.repoint_done(st, skey, s, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      kf
    case False{}:
      Lw.gsm_forget(st, [(skey, s)], S.State.pfcp_seq(st), Lw.one(st, skey, s, es))

def Lw.switch_failed(+st: S.State, +key: U32, +ue: S.Ue, +psis: List<&2, U32>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.switch_failed(key, ue, psis)) == True{} : Bool}:
  +cause = N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified())
  +a : N.Act = N.SwitchFail{S.Ue.assoc(ue), S.Ue.stream(ue), Some{key}, N.Ngap.big(key), S.Ue.ran_id(ue), psis, cause}
  +b : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}
  +c : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  +d : N.Act = N.Note{F.Warn{}, "NGAP: Path Switch failed, no PDU session switched; UE released"}
  Lv.leaf(st, S.Rephase{key, S.Releasing{S.Guard{0}}}, [a, b, c, d], Lv.cons(st, a, [b, c, d], ek, Lv.cons(st, b, [c, d], ek, Lv.cons(st, c, [d], ek, {==}))), {==})

def Lw.switch_end(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +released: List<&2, U32>, +switched: List<&2, U32>, +cfg: Maybe<&2, S.Cfg>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.switch_end(key, ue, ctx, nh, released, switched, cfg)) == True{} : Bool}:
  match switched:
    case Nil{}:
      match cfg:
        case None{}:
          Lw.switch_failed(st, key, ue, List.append(&2, U32, released, []), ek)
        case Some{c}:
          Lw.switch_failed(st, key, ue, List.append(&2, U32, released, []), ek)
    case +p <> +more:
      match cfg:
        case None{}:
          Lw.switch_failed(st, key, ue, List.append(&2, U32, released, p <> more), ek)
        case Some{+c}:
          +a : N.Act = N.SwitchAck{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), N.Ue.caps(ue), nh, p <> more, released, S.Cfg.sst(c)}
          Lv.leaf(st, S.Rephase{key, S.Registered{ctx, nh}}, [a, N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Path Switch done"}], Lv.cons(st, a, [N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Path Switch done"}], ek, {==}), {==})

def Lw.switch_next(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +released: List<&2, U32>, +switched: List<&2, U32>, +waits: Bool, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.switch_next(st, key, ue, guard, ctx, nh, released, switched, waits)) == True{} : Bool}:
  match waits:
    case True{}:
      {==}
    case False{}:
      Lw.switch_end(st, key, ue, ctx, nh, released, switched, S.State.config(st), ek)

def Lw.switch_ue(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, +ue: S.Ue, +p: S.Phase, +ek: {Lv.live(st, S.Session.ue(s)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.switch_ue(st, skey, s, ok, ue, p)) == True{} : Bool}:
  match p:
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh}:
      {==}
    case S.Switching{+guard, +ctx, +nh, +released}:
      +key = S.Session.ue(s)
      +psi = S.Session.psi(s)
      Lw.switch_next(st, key, ue, guard, ctx, nh, Gsm.Gsm.psi_if(psi, released, Bool.not(ok)), Gsm.Gsm.psi_if(psi, Gsm.Gsm.active_psis(key, S.State.sessions(st)), ok), Gsm.Gsm.waits(key, skey, S.State.sessions(st)), ek)
    case S.Handover{guard, ctx, nh, source, leg}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.switch_of(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, +m: Maybe<&2, S.Ue>, +ek: {Lv.live(st, S.Session.ue(s)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.switch_of(st, skey, s, ok, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.switch_ue(st, skey, s, ok, ue, S.Ue.phase(ue), ek)

def Lw.repointed(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.Session.known(s), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.repointed(st, skey, s, ok)) == True{} : Bool}:
  Lv.join(st, Gsm.Gsm.repoint_done(st, skey, s, ok), Gsm.Gsm.switch_of(st, skey, s, ok, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st))), Lw.repoint_done(st, skey, s, ok, es, kf), Lw.switch_of(st, skey, s, ok, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), Lv.owner_live(st, S.Session.ue(s), es)))

def Lw.modified_as(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.Session.known(s), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.modified_as(st, skey, s, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      kf
    case False{}:
      Lw.drop(st, skey, s, S.State.pfcp_seq(st), es)

def Lw.modified_phase(+st: S.State, +skey: U32, +s: S.Session, +msg: Pf.Msg, +p: S.SPhase, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.SPhase.knows(p, S.Session.known(s)), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.modified_phase(st, skey, s, msg, p)) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{+guard, request}:
      Lw.modified_as(st, skey, s, Up.N4.accepted(Up.N4.cause(msg)), es, kf)
    case S.Repointing{+guard, +request}:
      Lw.repointed(st, skey, s, Up.N4.accepted(Up.N4.cause(msg)), es, kf)
    case S.Active{}:
      {==}

def Lw.modified(+st: S.State, +msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.modified(st, msg, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.modified_phase(st, skey, s, msg, S.Session.phase(s), Lv.owns(skey, s, S.State.sessions(st), em), Lv.knows(skey, s, S.State.sessions(st), em))

def Lw.assoc_answer(+st: S.State, +ok: Bool) -> {Lv.okf(st, Up.N4.assoc_answer(ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Lw.assoc_seq(+st: S.State, +msg: Pf.Msg, +ok: Bool) -> {Lv.okf(st, Up.N4.assoc_seq(msg, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.assoc_answer(st, Up.N4.accepted(Up.N4.cause(msg)))
    case False{}:
      {==}

def Lw.assoc_for(+st: S.State, +link: S.Link, +msg: Pf.Msg) -> {Lv.okf(st, Up.N4.assoc_for(link, msg)) == True{} : Bool}:
  match link:
    case S.Idle{}:
      {==}
    case S.Asking{+seq, resent}:
      Lw.assoc_seq(st, msg, U32.is_eq(seq, Pf.Msg.seq(msg)))
    case S.Paused{}:
      {==}
    case S.Up{}:
      {==}
    case S.Beating{seq, resent}:
      {==}

def Lw.alive_seq(+st: S.State, +ok: Bool) -> {Lv.okf(st, Up.N4.alive_seq(ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Lw.alive_for(+st: S.State, +link: S.Link, +seq: U32) -> {Lv.okf(st, Up.N4.alive_for(link, seq)) == True{} : Bool}:
  match link:
    case S.Idle{}:
      {==}
    case S.Asking{s, resent}:
      {==}
    case S.Paused{}:
      {==}
    case S.Up{}:
      {==}
    case S.Beating{+s, resent}:
      Lw.alive_seq(st, U32.is_eq(s, seq))

def Lw.pfcp_k6(+st: S.State, +msg: Pf.Msg, +ok: Bool) -> {Lv.okf(st, Gsm.Gsm.pfcp_k6(st, msg, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.modified(st, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Lv.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))
    case False{}:
      {==}

def Lw.pfcp_k5(+st: S.State, +msg: Pf.Msg, +kind: U32, +ok: Bool) -> {Lv.okf(st, Gsm.Gsm.pfcp_k5(st, msg, kind, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.established(st, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Lv.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))
    case False{}:
      Lw.pfcp_k6(st, msg, U32.is_eq(kind, Pf.Type.session_modification_response()))

def Lw.pfcp_k4(+st: S.State, +msg: Pf.Msg, +kind: U32, +ok: Bool) -> {Lv.okf(st, Gsm.Gsm.pfcp_k4(st, msg, kind, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Lw.pfcp_k5(st, msg, kind, U32.is_eq(kind, Pf.Type.session_establishment_response()))

def Lw.pfcp_k3(+st: S.State, +msg: Pf.Msg, +kind: U32, +ok: Bool) -> {Lv.okf(st, Gsm.Gsm.pfcp_k3(st, msg, kind, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.assoc_for(st, S.N4.link(S.State.n4(st)), msg)
    case False{}:
      Lw.pfcp_k4(st, msg, kind, U32.is_eq(kind, Pf.Type.session_deletion_response()))

def Lw.pfcp_k2(+st: S.State, +msg: Pf.Msg, +kind: U32, +ok: Bool) -> {Lv.okf(st, Gsm.Gsm.pfcp_k2(st, msg, kind, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.alive_for(st, S.N4.link(S.State.n4(st)), Pf.Msg.seq(msg))
    case False{}:
      Lw.pfcp_k3(st, msg, kind, U32.is_eq(kind, Pf.Type.association_setup_response()))

def Lw.pfcp_k1(+st: S.State, +msg: Pf.Msg, +kind: U32, +ok: Bool) -> {Lv.okf(st, Gsm.Gsm.pfcp_k1(st, msg, kind, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Lw.pfcp_k2(st, msg, kind, U32.is_eq(kind, Pf.Type.heartbeat_response()))

def Lw.pfcp_msg(+st: S.State, +r: B.Read(Pf.Msg)) -> {Lv.okf(st, Gsm.Gsm.pfcp_msg(st, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{(+msg, rest)}:
      Lw.pfcp_k1(st, msg, Pf.Msg.kind(msg), U32.is_eq(Pf.Msg.kind(msg), 1))

def Lw.pfcp_data(+st: S.State, +bytes: B.Bytes()) -> {Lv.okf(st, Gsm.Gsm.pfcp_data(st, bytes)) == True{} : Bool}:
  Lw.pfcp_msg(st, Pf.Msg.read(bytes))


# The gNB's answer to PDU Session Resource Setup
# ----------------------------------------------

def Lw.modify(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +seq: U32, +tunnel: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.Session.known(s), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.modify(st, skey, s, pti, seq, tunnel)) == True{} : Bool}:
  match tunnel:
    case None{}:
      Lw.drop(st, skey, s, seq, es)
    case Some{(+gnb_teid, +gnb_addr)}:
      +x : N.Act = N.Pfcp{Some{S.Session.ue(s)}, Up.N4.modify(S.Session.up_seid(s), gnb_teid, gnb_addr, seq)}
      +y : N.Act = N.TimerStart{Some{S.Session.ue(s)}, skey, Up.N4.t1_ms()}
      +ek = Lv.owner_live(st, S.Session.ue(s), es)
      +v : S.SVar = S.SVar{S.Session.up_seid(s), seq, S.Modifying{S.Guard{0}, Up.N4.modify(S.Session.up_seid(s), gnb_teid, gnb_addr, seq)}}
      Lv.leaf(st, S.Both{S.Revar{skey, v}, S.BumpSeq{1}}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), P.Bool.and_intro(Lv.revar_ok(st, v), True{}, kf, {==}))

def Lw.set_up_phase(+st: S.State, +skey: U32, +s: S.Session, +transfer: B.Bytes(), +seq: U32, +p: S.SPhase, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.SPhase.knows(p, S.Session.known(s)), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.set_up_phase(st, skey, s, transfer, seq, p)) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{+guard, +pti}:
      Lw.modify(st, skey, s, pti, seq, Gsm.Gsm.tunnel_of(G.PDUSessionResourceSetupResponseTransfer.read(Ap.Cur{0n, Ap.unpack(transfer)})), es, kf)
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Lw.set_up(+st: S.State, +transfer: B.Bytes(), +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.set_up(st, transfer, seq, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.set_up_phase(st, skey, s, transfer, seq, S.Session.phase(s), Lv.owns(skey, s, S.State.sessions(st), em), Lv.knows(skey, s, S.State.sessions(st), em))

def Lw.set_ups(+st: S.State, +key: U32, +items: G.PDUSessionResourceSetupListSURes(), +seq: U32) -> {Lv.okf(st, Gsm.Gsm.set_ups(st, key, items, seq)) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case G.PDUSessionResourceSetupItemSURes{+psi, +transfer, x} <> +more:
      +a = Gsm.Gsm.set_up(st, transfer, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)))
      +b = Gsm.Gsm.set_ups(st, key, more, U32.add(seq, 1))
      Lv.join(st, N.Out.also((S.BumpSeq{1}, []), []), N.Out.join(a, b), {==}, Lv.join(st, a, b, Lw.set_up(st, transfer, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), Lv.by_psi(key, psi, S.State.sessions(st))), Lw.set_ups(st, key, more, U32.add(seq, 1))))

def Lw.failed_phase(+st: S.State, +skey: U32, +s: S.Session, +seq: U32, +p: S.SPhase, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.failed_phase(st, skey, s, seq, p)) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, +pti}:
      Lw.abort(st, skey, s, pti, 26, seq, es)
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Lw.failed(+st: S.State, +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.failed(st, seq, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.failed_phase(st, skey, s, seq, S.Session.phase(s), Lv.owns(skey, s, S.State.sessions(st), em))

def Lw.faileds(+st: S.State, +key: U32, +items: G.PDUSessionResourceFailedToSetupListSURes(), +seq: U32) -> {Lv.okf(st, Gsm.Gsm.faileds(st, key, items, seq)) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case G.PDUSessionResourceFailedToSetupItemSURes{+psi, transfer, x} <> +more:
      +a = Gsm.Gsm.failed(st, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)))
      +b = Gsm.Gsm.faileds(st, key, more, U32.add(seq, 1))
      Lv.join(st, (S.BumpSeq{1}, []), N.Out.join(a, b), {==}, Lv.join(st, a, b, Lw.failed(st, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), Lv.by_psi(key, psi, S.State.sessions(st))), Lw.faileds(st, key, more, U32.add(seq, 1))))

def Lw.results(+st: S.State, +key: U32, +oks: G.PDUSessionResourceSetupListSURes(), +fails: G.PDUSessionResourceFailedToSetupListSURes()) -> {Lv.okf(st, Gsm.Gsm.results(st, key, oks, fails)) == True{} : Bool}:
  +seq2 = U32.add(S.State.pfcp_seq(st), U32.from_nat(List.length(&2, G.PDUSessionResourceSetupItemSURes, oks)))
  Lv.join(st, Gsm.Gsm.set_ups(st, key, oks, S.State.pfcp_seq(st)), Gsm.Gsm.faileds(st, key, fails, seq2), Lw.set_ups(st, key, oks, S.State.pfcp_seq(st)), Lw.faileds(st, key, fails, seq2))

def Lw.setup_response_ue(+st: S.State, +assoc: U32, +key: U32, +oks: G.PDUSessionResourceSetupListSURes(), +fails: G.PDUSessionResourceFailedToSetupListSURes(), +m: Maybe<&2, S.Ue>) -> {Lv.okf(st, Gsm.Gsm.setup_response_ue(st, assoc, key, oks, fails, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{ue}:
      Lw.results(st, key, oks, fails)


def Lw.setup_response_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +oks: G.PDUSessionResourceSetupListSURes(), +fails: G.PDUSessionResourceFailedToSetupListSURes(), +m: Maybe<&2, U32>) -> {Lv.okf(st, Gsm.Gsm.setup_response_key(st, assoc, ran, oks, fails, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.setup_response_ue(st, assoc, key, oks, fails, N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran))

def Lw.setup_response(+st: S.State, +assoc: U32, +v: V.PDUSessionResourceSetupResponse.View) -> {Lv.okf(st, Gsm.Gsm.setup_response(st, assoc, v)) == True{} : Bool}:
  match v:
    case V.PDUSessionResourceSetupResponse.View{+amf_ue_ngap_id, +ran_ue_ngap_id, +oks, +fails, diagnostics, uli}:
      Lw.setup_response_key(st, assoc, ran_ue_ngap_id, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), Gsm.Gsm.list_or(G.PDUSessionResourceFailedToSetupItemSURes, fails), N.Ngap.ue_key(amf_ue_ngap_id))

def Lw.setup_response_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>) -> {Lv.okf(st, Gsm.Gsm.setup_response_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.setup_response(st, assoc, v)

def Lw.resend_if(+st: S.State, +skey: U32, +s: S.Session, +p: S.SPhase, +request: B.Bytes(), +fail: N.GOut(), +more: Bool, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +hv: {Lv.revar_ok(st, S.SVar{S.Session.up_seid(s), S.Session.seq(s), p}) == True{} : Bool}, +hf: {Lv.okf(st, fail) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.resend_if(skey, s, p, request, fail, more)) == True{} : Bool}:
  match more:
    case True{}:
      +ek = Lv.owner_live(st, S.Session.ue(s), es)
      +x : N.Act = N.Pfcp{Some{S.Session.ue(s)}, request}
      +y : N.Act = N.TimerStart{Some{S.Session.ue(s)}, skey, Up.N4.t1_ms()}
      Lv.leaf(st, S.Revar{skey, S.SVar{S.Session.up_seid(s), S.Session.seq(s), p}}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), hv)
    case False{}:
      hf

def Lw.gsm_expired(+st: S.State, +skey: U32, +s: S.Session, +p: S.SPhase, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.SPhase.knows(p, S.Session.known(s)), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}, +kb: {Bool.or(Gsm.Gsm.phase_bounded(p), Bool.not(Gsm.Gsm.bounded(S.State.sessions(st)))) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.expired(st, skey, s, p)) == True{} : Bool}:
  match p:
    case S.Creating{+guard, +pti, +accept, +request}:
      Lw.resend_if(st, skey, s, S.Creating{S.Guard{U32.add(S.Guard.retries(guard), 1)}, pti, accept, request}, request, Gsm.Gsm.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st)), U32.is_lt(S.Guard.retries(guard), Up.N4.n1()), es, P.Bool.and_intro(Bool.or(Gsm.Gsm.accept_bounded(accept), Bool.not(Gsm.Gsm.bounded(S.State.sessions(st)))), Bool.or(Bool.not(S.Session.known(s)), Bool.not(S.Sessions.known(S.State.sessions(st)))), kb, kf), Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es))
    case S.Setting{guard, pti}:
      Lw.drop(st, skey, s, S.State.pfcp_seq(st), es)
    case S.Modifying{+guard, +request}:
      Lw.resend_if(st, skey, s, S.Modifying{S.Guard{U32.add(S.Guard.retries(guard), 1)}, request}, request, Gsm.Gsm.drop(st, skey, s, S.State.pfcp_seq(st)), U32.is_lt(S.Guard.retries(guard), Up.N4.n1()), es, kf, Lw.drop(st, skey, s, S.State.pfcp_seq(st), es))
    case S.Repointing{+guard, +request}:
      Lw.resend_if(st, skey, s, S.Repointing{S.Guard{U32.add(S.Guard.retries(guard), 1)}, request}, request, Gsm.Gsm.repointed(st, skey, s, False{}), U32.is_lt(S.Guard.retries(guard), Up.N4.n1()), es, kf, Lw.repointed(st, skey, s, False{}, es, kf))
    case S.Active{}:
      {==}


# Timers
# ------

def Lw.asked(+st: S.State, +cfg: Maybe<&2, S.Cfg>, +seq: U32, +resent: U32, +tx: S.Tx, +ht: {Lv.free(st, tx) == True{} : Bool}) -> {Lv.okf(st, Up.N4.asked(st, cfg, seq, resent, tx)) == True{} : Bool}:
  match cfg:
    case None{}:
      {==}
    case Some{c}:
      P.Bool.and_intro(Lv.free(st, tx), True{}, ht, {==})

def Lw.n4_start(+st: S.State) -> {Lv.okf(st, Up.N4.start(st)) == True{} : Bool}:
  Lw.asked(st, S.State.config(st), S.State.pfcp_seq(st), 0, S.BumpSeq{1}, {==})

def Lw.ask_again(+st: S.State, +seq: U32, +resent: U32, +more: Bool) -> {Lv.okf(st, Up.N4.ask_again(st, seq, resent, more)) == True{} : Bool}:
  match more:
    case True{}:
      Lw.asked(st, S.State.config(st), seq, U32.add(resent, 1), S.Keep{}, {==})
    case False{}:
      {==}

def Lw.beat_again(+st: S.State, +seq: U32, +resent: U32, +more: Bool) -> {Lv.okf(st, Up.N4.beat_again(st, seq, resent, more)) == True{} : Bool}:
  match more:
    case True{}:
      {==}
    case False{}:
      Lv.also(st, Up.N4.start(st), [N.Note{F.Warn{}, "PFCP: no Heartbeat Response; association with the UPF lost"}], Lw.n4_start(st), {==})

def Lw.n4_expired(+st: S.State, +link: S.Link) -> {Lv.okf(st, Up.N4.expired(st, link)) == True{} : Bool}:
  match link:
    case S.Idle{}:
      {==}
    case S.Asking{+seq, +resent}:
      Lw.ask_again(st, seq, resent, U32.is_lt(resent, Up.N4.n1()))
    case S.Paused{}:
      Lw.n4_start(st)
    case S.Up{}:
      {==}
    case S.Beating{+seq, +resent}:
      Lw.beat_again(st, seq, resent, U32.is_lt(resent, Up.N4.n1()))

def Lw.node_timer(+st: S.State, +ok: Bool) -> {Lv.okf(st, K.Kernel.node_timer(st, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.n4_expired(st, S.N4.link(S.State.n4(st)))
    case False{}:
      {==}

def Lw.fired_session(+st: S.State, +timer: U32, +m: Maybe<&2, S.Session>, +em: {Tb.Table.get(S.Session, timer, S.State.sessions(st)) == m : Maybe<&2, S.Session>}) -> {Lv.okf(st, K.Kernel.fired_session(st, timer, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.node_timer(st, U32.is_eq(timer, S.N4.timer()))
    case Some{+s}:
      Lw.gsm_expired(st, timer, s, S.Session.phase(s), Lv.owns(timer, s, S.State.sessions(st), Lv.sget(S.State.sessions(st), timer, s, em)), Lv.knows(timer, s, S.State.sessions(st), Lv.sget(S.State.sessions(st), timer, s, em)), Lv.sbound(S.State.sessions(st), timer, s, em))

def Lw.fired_ue(+st: S.State, +timer: U32, +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, timer, S.State.ues(st)) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, K.Kernel.fired_ue(st, timer, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.fired_session(st, timer, Tb.Table.get(S.Session, timer, S.State.sessions(st)), {==})
    case Some{+ue}:
      Lw.expired(st, timer, ue, S.Ue.phase(ue), Lv.has_live(st, timer, Lv.get_has(S.State.ues(st), timer, ue, em)))

def Lw.fired(+st: S.State, +timer: U32) -> {Lv.okf(st, K.Kernel.fired(st, timer)) == True{} : Bool}:
  Lw.fired_ue(st, timer, Tb.Table.get(S.Ue, timer, S.State.ues(st)), {==})


# NGAP
# ----

# Path Switch Request
# -------------------
# The context moves under its own key, guarded; its sessions are repointed
# or forgotten, every action built from the context's key.

def Lw.ps_session(+st: S.State, +skey: U32, +s: S.Session, +seq: U32, +t: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +kk: {Bool.or(S.Session.known(s), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}) -> {Lv.okf(st, Ps.Ps.session(skey, s, seq, t)) == True{} : Bool}:
  match t:
    case None{}:
      Lw.gsm_forget(st, [(skey, s)], seq, Lw.one(st, skey, s, es))
    case Some{(+teid, +addr)}:
      +request = Up.N4.modify(S.Session.up_seid(s), teid, addr, seq)
      +ek = Lv.owner_live(st, S.Session.ue(s), es)
      +x : N.Act = N.Pfcp{Some{S.Session.ue(s)}, request}
      +y : N.Act = N.TimerStart{Some{S.Session.ue(s)}, skey, Up.N4.t1_ms()}
      Lv.leaf(st, S.Revar{skey, S.SVar{S.Session.up_seid(s), seq, S.Repointing{S.Guard{0}, request}}}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), kk)

def Lw.ps_tun(+st: S.State, +skey: U32, +s: S.Session, +seq: U32, +p: S.SPhase, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}, +kn: {Bool.or(S.SPhase.knows(p, S.Session.known(s)), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}) -> {Lv.okf(st, Ps.Ps.session(skey, s, seq, Ps.Ps.tunnel(p, m))) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      Lw.gsm_forget(st, [(skey, s)], seq, Lw.one(st, skey, s, es))
    case S.Setting{guard, pti}:
      Lw.gsm_forget(st, [(skey, s)], seq, Lw.one(st, skey, s, es))
    case S.Modifying{guard, request}:
      Lw.gsm_forget(st, [(skey, s)], seq, Lw.one(st, skey, s, es))
    case S.Repointing{guard, request}:
      Lw.gsm_forget(st, [(skey, s)], seq, Lw.one(st, skey, s, es))
    case S.Active{}:
      Lw.ps_session(st, skey, s, seq, Ps.Ps.tunnel(S.Active{}, m), es, kn)

def Lw.ps_sessions(+st: S.State, +ts: List<&2, S.Tunnel>, +rows: Tb.Table(S.Session), +seq: U32, +e: {Lv.frows(rows, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Ps.Ps.sessions(ts, rows, seq)) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+skey, +s) <> +more:
      +ss = S.State.sessions(st)
      +kn = Bool.or(S.SPhase.knows(S.Session.phase(s), S.Session.known(s)), Bool.not(S.Sessions.known(ss)))
      +hf = P.Bool.and_true_l(Lv.found(Some{(skey, s)}, ss), Lv.frows(more, ss), e)
      hm = P.Bool.and_true_r(Lv.found(Some{(skey, s)}, ss), Lv.frows(more, ss), e)
      es = P.Bool.and_true_l(Lv.owner(S.Session.ue(s), ss), kn, hf)
      ek = P.Bool.and_true_r(Lv.owner(S.Session.ue(s), ss), kn, hf)
      +o = Ps.Ps.session(skey, s, seq, Ps.Ps.tunnel_for(ts, s))
      Lv.join(st, N.Out.join((S.BumpSeq{1}, []), o), Ps.Ps.sessions(ts, more, U32.add(seq, 1)), Lv.join(st, (S.BumpSeq{1}, []), o, {==}, Lw.ps_tun(st, skey, s, seq, S.Session.phase(s), Ps.Ps.find(S.Session.psi(s), ts), es, ek)), Lw.ps_sessions(st, ts, more, U32.add(seq, 1), hm))

def Lw.ps_go(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +rows: Tb.Table(S.Session), +ok: Bool, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +er: {Lv.frows(rows, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Ps.Ps.go(st, assoc, stream, amf, ran, items, key, ue, ctx, nh, rows, ok)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      +p : S.Phase = S.Switching{S.Guard{0}, ctx, S.Nh.next(nh), Ps.Ps.released(Ps.Ps.tunnels(items), rows)}
      +v = S.Ue.moved(ue, assoc, ran, stream, p)
      +a = Ps.Ps.sessions(Ps.Ps.tunnels(items), rows, S.State.pfcp_seq(st))
      +b : N.GOut() = (S.Put{key, v}, [])
      +ek = Lv.has_live(st, key, eh)
      hb = Lv.leaf(st, S.Put{key, v}, [], {==}, P.Bool.and_intro(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(v)), S.Ue.single(v)), Lv.keyed_of(st, key, ek), P.Bool.and_intro(S.Phase.guarded(S.Ue.phase(v)), S.Ue.single(v), Lv.g_moved(ue, assoc, ran, stream, p), Lv.s_moved(ue, assoc, ran, stream, p))))
      +ts : N.Act = N.TimerStart{Some{key}, key, Ps.Ps.guard_ms()}
      +note : N.Act = N.Note{F.Info{}, "NGAP: Path Switch Request; the UE moved, its PDU sessions being switched"}
      Lv.also(st, N.Out.join(a, b), [ts, note], Lv.join(st, a, b, Lw.ps_sessions(st, Ps.Ps.tunnels(items), rows, S.State.pfcp_seq(st), er), hb), Lv.cons(st, ts, [note], ek, {==}))

def Lw.ps_free(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +ok: Bool, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.okf(st, Ps.Ps.free(st, assoc, stream, amf, ran, items, key, ue, ctx, nh, ok)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      +rows = S.Sessions.of_ue(key, S.State.sessions(st))
      Lw.ps_go(st, assoc, stream, amf, ran, items, key, ue, ctx, nh, rows, Ps.Ps.any(Ps.Ps.tunnels(items), rows), eh, Lv.frows_sift(S.SOf{key}, S.State.sessions(st)))

def Lw.ps_identified(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +supi: Maybe<&2, B.Digits()>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.okf(st, Ps.Ps.identified(st, assoc, stream, amf, ran, items, key, ue, ctx, nh, supi)) == True{} : Bool}:
  match supi:
    case None{}:
      {==}
    case Some{sp}:
      Lw.ps_free(st, assoc, stream, amf, ran, items, key, ue, ctx, nh, Ps.Ps.ran_free(key, assoc, ran, S.State.ues(st)), eh)

def Lw.ps_phase(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +key: U32, +ue: S.Ue, +p: S.Phase, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.okf(st, Ps.Ps.phase(st, assoc, stream, amf, ran, items, key, ue, p)) == True{} : Bool}:
  match p:
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{+ctx, +nh}:
      Lw.ps_identified(st, assoc, stream, amf, ran, items, key, ue, ctx, nh, S.Ue.supi(ue), eh)
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Handover{guard, ctx, nh, source, leg}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.ps_found(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +key: U32, +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Ps.Ps.found(st, assoc, stream, amf, ran, items, key, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.ps_phase(st, assoc, stream, amf, ran, items, key, ue, S.Ue.phase(ue), Lv.get_has(S.State.ues(st), key, ue, em))

def Lw.ps_keyed(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +m: Maybe<&2, U32>) -> {Lv.okf(st, Ps.Ps.keyed(st, assoc, stream, amf, ran, items, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.ps_found(st, assoc, stream, amf, ran, items, key, Tb.Table.get(S.Ue, key, S.State.ues(st)), {==})

def Lw.ps_ready(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ok: Bool) -> {Lv.okf(st, Ps.Ps.ready(st, assoc, stream, amf, ran, items, ok)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      Lw.ps_keyed(st, assoc, stream, amf, ran, items, N.Ngap.ue_key(amf))

def Lw.caps_same(+st: S.State, +ok: Bool) -> {Lv.acts(st, Ps.Ps.caps_same(ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Lw.caps_ue(+st: S.State, +caps: G.UESecurityCapabilities, +m: Maybe<&2, S.Ue>) -> {Lv.acts(st, Ps.Ps.caps_ue(caps, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.caps_same(st, B.bytes_eq(Ap.pack(G.UESecurityCapabilities.write(N.Ngap.ue_caps(N.Ue.caps(ue)), 0n, [])), Ap.pack(G.UESecurityCapabilities.write(caps, 0n, []))))

def Lw.caps_note(+st: S.State, +caps: G.UESecurityCapabilities, +m: Maybe<&2, U32>) -> {Lv.acts(st, Ps.Ps.caps_note(st, caps, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.caps_ue(st, caps, Tb.Table.get(S.Ue, key, S.State.ues(st)))

def Lw.ps_of_view(+st: S.State, +assoc: U32, +stream: U32, +r: Result<&2, &2, B.Err, V.PathSwitchRequest.View>) -> {Lv.okf(st, Ps.Ps.of_view(st, assoc, stream, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.PathSwitchRequest.View{+ran, +amf, uli, +caps, +items, failed, rrc}}:
      +ok = S.Assocs.has(assoc, S.State.assocs(st))
      Lv.also(st, Ps.Ps.ready(st, assoc, stream, amf, ran, items, ok), Ps.Ps.caps_note(st, caps, N.Ngap.ue_key(amf)), Lw.ps_ready(st, assoc, stream, amf, ran, items, ok), Lw.caps_note(st, caps, N.Ngap.ue_key(amf)))

# N2 handover
# -----------
# Every action is built from the context the message names, whose key a
# context holds; the context is rephased into a guarded phase, or moved
# under its own key by Handover Notify.

def Lw.ho_fail(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Ho.Ho.fail(key, ue, cause)) == True{} : Bool}:
  +x : N.Act = N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.preparation_failure(key, S.Ue.ran_id(ue), cause)}
  +n : N.Act = N.Note{F.Warn{}, "NGAP: Handover Required refused"}
  Lv.leaf(st, S.Keep{}, [x, n], Lv.cons(st, x, [n], ek, {==}), {==})

def Lw.not_true(+x: Bool, +e: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.Refute.bool(e))
    case False{}:
      {==}

def Lw.pair_get(+m: Maybe<&2, S.Ue>, +u: S.Ue, -Q: Type, pr: {m == Some{u} : Maybe<&2, S.Ue>} & Q) -> {m == Some{u} : Maybe<&2, S.Ue>}:
  match pr:
    case (+e, q):
      e

# A pending handover's phase, written over the context it belongs to, names
# that context's owner as its source and another association as its target.
def Lw.ho_homed(+st: S.State, +key: U32, +ue: S.Ue, +g: S.Guard, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(S.Leg.target(leg), S.Ue.assoc(ue)) == False{} : Bool}) -> {Lv.homed(st, S.Rephase{key, S.Handover{g, ctx, nh, S.Ue.assoc(ue), leg}}, S.State.ues(st)) == True{} : Bool}:
  sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, S.State.ues(st)), Some{ue}, eg)
  %sg : {Bool.and(True{}, S.Ue.fits(S.Handover{g, ctx, nh, S.Ue.assoc(ue), leg}, _)) == True{} : Bool}
  er = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), S.Ue.assoc(ue)), True{}, P.U32.is_eq_refl(S.Ue.assoc(ue)))
  %er : {Bool.and(_, Bool.not(U32.is_eq(S.Leg.target(leg), S.Ue.assoc(ue)))) == True{} : Bool}
  sn = Equal.sym(Bool, U32.is_eq(S.Leg.target(leg), S.Ue.assoc(ue)), False{}, ne)
  %sn : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
  {==}

def Lw.ho_leafok(+st: S.State, +key: U32, +ue: S.Ue, +g: S.Guard, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +acts: List<&2, N.Act>, +ha: {Lv.acts(st, acts) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(S.Leg.target(leg), S.Ue.assoc(ue)) == False{} : Bool}) -> {Lv.ok(st, (S.Rephase{key, S.Handover{g, ctx, nh, S.Ue.assoc(ue), leg}}, acts)) == True{} : Bool}:
  P.Bool.and_intro(Lv.acts(st, acts), Lv.homed(st, S.Rephase{key, S.Handover{g, ctx, nh, S.Ue.assoc(ue), leg}}, S.State.ues(st)), ha, Lw.ho_homed(st, key, ue, g, ctx, nh, leg, eg, ne))

def Lw.ho_prepare(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +t: U32, +cfg: S.Cfg, +cause: G.Cause, +container: B.Bytes(), +items: G.PDUSessionResourceSetupListHOReq(), +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(t, S.Ue.assoc(ue)) == False{} : Bool}) -> {Lv.ok(st, Ho.Ho.prepare(key, ue, ctx, nh, t, cfg, cause, container, items)) == True{} : Bool}:
  match items:
    case Nil{}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unknown_PDU_session_ID())), Lw.ho_fail(st, key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unknown_PDU_session_ID()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case +i <> +more:
      +ek = Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))
      +next = S.Nh.next(nh)
      +x : N.Act = N.UeSend{t, Ho.Ho.stream(), key, Ho.Ho.request(key, cfg, cause, N.Ue.caps(ue), next, i <> more, container)}
      +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
      +n : N.Act = N.Note{F.Info{}, "NGAP: Handover Required; Handover Request sent to the target"}
      Lw.ho_leafok(st, key, ue, S.Guard{0}, ctx, next, S.Asked{t}, [x, y, n], Lv.cons(st, x, [y, n], ek, Lv.cons(st, y, [n], ek, {==})), eg, ne)

def Lw.ho_required_cfg(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +t: U32, +cause: G.Cause, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +m: Maybe<&2, S.Cfg>, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(t, S.Ue.assoc(ue)) == False{} : Bool}) -> {Lv.ok(st, Ho.Ho.required_cfg(st, key, ue, ctx, nh, t, cause, items, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unspecified())), Lw.ho_fail(st, key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unspecified()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case Some{+cfg}:
      Lw.ho_prepare(st, key, ue, ctx, nh, t, cfg, cause, container, Ho.Ho.setup_items(cfg, items, S.Sessions.of_ue(key, S.State.sessions(st))), eg, ne)

def Lw.ho_required_other(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +t: U32, +cause: G.Cause, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +same: Bool, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +es: {U32.is_eq(t, S.Ue.assoc(ue)) == same : Bool}) -> {Lv.ok(st, Ho.Ho.required_other(st, key, ue, ctx, nh, t, cause, items, container, same)) == True{} : Bool}:
  match same:
    case True{}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unknown_targetID())), Lw.ho_fail(st, key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unknown_targetID()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case False{}:
      Lw.ho_required_cfg(st, key, ue, ctx, nh, t, cause, items, container, S.State.config(st), eg, es)

def Lw.ho_required_target(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +cause: G.Cause, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +m: Maybe<&2, U32>, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.ok(st, Ho.Ho.required_target(st, key, ue, ctx, nh, cause, items, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unknown_targetID())), Lw.ho_fail(st, key, ue, Ho.Ho.radio(G.CauseRadioNetwork.unknown_targetID()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case Some{+t}:
      Lw.ho_required_other(st, key, ue, ctx, nh, t, cause, items, container, U32.is_eq(t, S.Ue.assoc(ue)), eg, {==})

def Lw.ho_required_phase(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +kind: G.HandoverType(), +cause: G.Cause, +id: G.TargetID, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +p: S.Phase, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.ok(st, Ho.Ho.required_phase(st, assoc, key, ue, kind, cause, id, items, container, p)) == True{} : Bool}:
  match p:
    case S.Registered{+ctx, +nh}:
      Lw.ho_required_target(st, key, ue, ctx, nh, cause, items, container, Ho.Ho.target(st, Ho.Ho.intra_type(kind), Ho.Ho.node(id)), eg)
    case S.Created{}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())), Lw.ho_fail(st, key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case S.Identifying{guard}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())), Lw.ho_fail(st, key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case S.Authenticating{guard, av, resynced, supi}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())), Lw.ho_fail(st, key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case S.SecurityMode{guard, ctx, k_amf}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())), Lw.ho_fail(st, key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())), Lw.ho_fail(st, key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case S.Switching{guard, ctx, nh, released}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())), Lw.ho_fail(st, key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case S.Handover{guard, ctx, nh, source, leg}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())), Lw.ho_fail(st, key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))
    case S.Releasing{guard}:
      Lv.ok_of(st, Ho.Ho.fail(key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state())), Lw.ho_fail(st, key, ue, N.Ngap.protocol(G.CauseProtocol.message_not_compatible_with_receiver_state()), Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))))

def Lw.ho_required_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +kind: G.HandoverType(), +cause: G.Cause, +id: G.TargetID, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +m: Maybe<&2, S.Ue>, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> {Lv.ok(st, Ho.Ho.required_ue(st, assoc, key, kind, cause, id, items, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.ho_required_phase(st, assoc, key, ue, kind, cause, id, items, container, S.Ue.phase(ue), Lw.pair_get(Tb.Table.get(S.Ue, key, S.State.ues(st)), ue, {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}, PT.Own.get(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran, ue, eo)))

def Lw.ho_required_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +kind: G.HandoverType(), +cause: G.Cause, +id: G.TargetID, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +m: Maybe<&2, U32>) -> {Lv.ok(st, Ho.Ho.required_key(st, assoc, ran, kind, cause, id, items, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.ho_required_ue(st, assoc, key, ran, kind, cause, id, items, container, N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran), {==})

def Lw.ho_required(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverRequired.View>) -> {Lv.ok(st, Ho.Ho.required_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.HandoverRequired.View{+amf, +ran, +kind, +cause, +id, direct, +items, +container}}:
      Lw.ho_required_key(st, assoc, ran, kind, cause, id, items, container, N.Ngap.ue_key(amf))

def Lw.first_has(+ues: Tb.Table(S.Ue), +key: U32, +ue: S.Ue, -Q: Type, pr: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>} & Q) -> {Tb.Table.has(S.Ue, key, ues) == True{} : Bool}:
  match pr:
    case (+eg, q):
      Lv.get_has(ues, key, ue, eg)

# The context a target's answer is for holds its key.
def Lw.ho_target_has(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +e: {Ho.Ho.for_target(st, assoc, key) == Some{ue} : Maybe<&2, S.Ue>}) -> {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}:
  Lw.first_has(S.State.ues(st), key, ue, {Ho.Ho.aimed(ue, assoc) == True{} : Bool}, PW.Walk.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ue, e))

# The target of a pending handover is not the context's owner.
def Lw.ho_aimed_ne(+ue: S.Ue, +assoc: U32, +e: {Ho.Ho.aimed(ue, assoc) == True{} : Bool}) -> {U32.is_eq(assoc, S.Ue.assoc(ue)) == False{} : Bool}:
  +rest = Bool.and(Tb.Table.present(B.Digits(), S.Ue.supi(ue)), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc)))
  n = P.Bool.and_true_r(Tb.Table.present(B.Digits(), S.Ue.supi(ue)), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc)), P.Bool.and_true_r(S.Maybe.same_u32(S.Phase.pending(S.Ue.phase(ue)), Some{assoc}), rest, e))
  Equal.trans(Bool, U32.is_eq(assoc, S.Ue.assoc(ue)), U32.is_eq(S.Ue.assoc(ue), assoc), False{}, P.U32.sym(assoc, S.Ue.assoc(ue)), Lw.not_true(U32.is_eq(S.Ue.assoc(ue), assoc), n))

def Lw.ho_ack_phase(+st: S.State, +assoc: U32, +stream: U32, +key: U32, +ue: S.Ue, +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes(), +p: S.Phase, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(assoc, S.Ue.assoc(ue)) == False{} : Bool}) -> {Lv.ok(st, Ho.Ho.ack_phase(assoc, stream, key, ue, ran, admitted, container, p)) == True{} : Bool}:
  match p:
    case S.Handover{guard, +ctx, +nh, source, leg}:
      match leg:
        case S.Asked{t}:
          +ek = Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))
          +ts = Ho.Ho.admitted(admitted)
          +x : N.Act = N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.command(key, S.Ue.ran_id(ue), ts, container)}
          +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
          +n : N.Act = N.Note{F.Info{}, "NGAP: Handover Request Acknowledge; Handover Command sent to the source"}
          Lw.ho_leafok(st, key, ue, S.Guard{0}, ctx, nh, S.Acked{assoc, ran, stream, ts}, [x, y, n], Lv.cons(st, x, [y, n], ek, Lv.cons(st, y, [n], ek, {==})), eg, ne)
        case S.Acked{t, r, s, ts}:
          {==}
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.ho_ack_found(+st: S.State, +assoc: U32, +stream: U32, +key: U32, +ue: S.Ue, +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes(), pr: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>} & {Ho.Ho.aimed(ue, assoc) == True{} : Bool}) -> {Lv.ok(st, Ho.Ho.ack_phase(assoc, stream, key, ue, ran, admitted, container, S.Ue.phase(ue))) == True{} : Bool}:
  match pr:
    case (+eg, +ea):
      Lw.ho_ack_phase(st, assoc, stream, key, ue, ran, admitted, container, S.Ue.phase(ue), eg, Lw.ho_aimed_ne(ue, assoc, ea))

def Lw.ho_ack_ue(+st: S.State, +assoc: U32, +stream: U32, +key: U32, +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes(), +m: Maybe<&2, S.Ue>, +em: {Ho.Ho.for_target(st, assoc, key) == m : Maybe<&2, S.Ue>}) -> {Lv.ok(st, Ho.Ho.ack_ue(assoc, stream, key, ran, admitted, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.ho_ack_found(st, assoc, stream, key, ue, ran, admitted, container, PW.Walk.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ue, em))

def Lw.ho_ack_key(+st: S.State, +assoc: U32, +stream: U32, +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes(), +m: Maybe<&2, U32>) -> {Lv.ok(st, Ho.Ho.ack_key(st, assoc, stream, ran, admitted, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.ho_ack_ue(st, assoc, stream, key, ran, admitted, container, Ho.Ho.for_target(st, assoc, key), {==})

def Lw.ho_ack(+st: S.State, +assoc: U32, +stream: U32, +r: Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View>) -> {Lv.ok(st, Ho.Ho.ack_of_view(st, assoc, stream, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.HandoverRequestAcknowledge.View{+amf, +ran, +admitted, failed, +container, diag, npn}}:
      Lw.ho_ack_key(st, assoc, stream, ran, admitted, container, N.Ngap.ue_key(amf))

def Lw.ho_failure_phase(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +cause: G.Cause, +p: S.Phase, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Ho.Ho.failure_phase(assoc, key, ue, cause, p)) == True{} : Bool}:
  match p:
    case S.Handover{guard, +ctx, +nh, source, leg}:
      match leg:
        case S.Asked{t}:
          +x : N.Act = N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.preparation_failure(key, S.Ue.ran_id(ue), cause)}
          +n : N.Act = N.Note{F.Warn{}, "NGAP: Handover Failure; Handover Preparation Failure sent to the source"}
          Lv.leaf(st, S.Rephase{key, S.Registered{ctx, nh}}, [x, N.TimerCancel{key}, n], Lv.cons(st, x, [N.TimerCancel{key}, n], ek, {==}), {==})
        case S.Acked{t, r, s, ts}:
          {==}
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.ho_failure_ue(+st: S.State, +assoc: U32, +key: U32, +cause: G.Cause, +m: Maybe<&2, S.Ue>, +em: {Ho.Ho.for_target(st, assoc, key) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Ho.Ho.failure_ue(assoc, key, cause, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.ho_failure_phase(st, assoc, key, ue, cause, S.Ue.phase(ue), Lv.has_live(st, key, Lw.ho_target_has(st, assoc, key, ue, em)))

def Lw.ho_failure_key(+st: S.State, +assoc: U32, +cause: G.Cause, +m: Maybe<&2, U32>) -> {Lv.okf(st, Ho.Ho.failure_key(st, assoc, cause, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.ho_failure_ue(st, assoc, key, cause, Ho.Ho.for_target(st, assoc, key), {==})

def Lw.ho_failure(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverFailure.View>) -> {Lv.okf(st, Ho.Ho.failure_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.HandoverFailure.View{+amf, +cause, diag}}:
      Lw.ho_failure_key(st, assoc, cause, N.Ngap.ue_key(amf))

def Lw.ho_complete(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +ok: Bool, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, ok)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      +rows = S.Sessions.of_ue(key, S.State.sessions(st))
      +v = S.Ue.moved(ue, assoc, r, s, S.Registered{ctx, nh})
      +a = Ps.Ps.sessions(ts, rows, S.State.pfcp_seq(st))
      +b : N.GOut() = (S.Put{key, v}, [])
      hb = Lv.leaf(st, S.Put{key, v}, [], {==}, P.Bool.and_intro(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(v)), S.Ue.single(v)), Lv.keyed_of(st, key, ek), P.Bool.and_intro(S.Phase.guarded(S.Ue.phase(v)), S.Ue.single(v), Lv.g_moved(ue, assoc, r, s, S.Registered{ctx, nh}), Lv.s_moved(ue, assoc, r, s, S.Registered{ctx, nh}))))
      +x : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), Ho.Ho.radio(G.CauseRadioNetwork.successful_handover())}
      +n : N.Act = N.Note{F.Info{}, "NGAP: Handover Notify; the UE moved to the target"}
      Lv.also(st, N.Out.join(a, b), [x, N.TimerCancel{key}, n], Lv.join(st, a, b, Lw.ps_sessions(st, ts, rows, S.State.pfcp_seq(st), Lv.frows_sift(S.SOf{key}, S.State.sessions(st))), hb), Lv.cons(st, x, [N.TimerCancel{key}, n], ek, {==}))

def Lw.ho_notify_phase(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ran: B.Bytes(), +p: S.Phase, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Ho.Ho.notify_phase(st, assoc, key, ue, ran, p)) == True{} : Bool}:
  match p:
    case S.Handover{guard, +ctx, +nh, source, leg}:
      match leg:
        case S.Asked{t}:
          {==}
        case S.Acked{t, +r, +s, +ts}:
          Lw.ho_complete(st, assoc, key, ue, ctx, nh, r, s, ts, Bool.and(B.bytes_eq(r, ran), Ps.Ps.ran_free(key, assoc, r, S.State.ues(st))), ek)
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.ho_notify_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +m: Maybe<&2, S.Ue>, +em: {Ho.Ho.for_target(st, assoc, key) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Ho.Ho.notify_ue(st, assoc, key, ran, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.ho_notify_phase(st, assoc, key, ue, ran, S.Ue.phase(ue), Lv.has_live(st, key, Lw.ho_target_has(st, assoc, key, ue, em)))

def Lw.ho_notify_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +m: Maybe<&2, U32>) -> {Lv.okf(st, Ho.Ho.notify_key(st, assoc, ran, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.ho_notify_ue(st, assoc, key, ran, Ho.Ho.for_target(st, assoc, key), {==})

def Lw.ho_notify(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverNotify.View>) -> {Lv.okf(st, Ho.Ho.notify_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.HandoverNotify.View{+amf, +ran, uli}}:
      Lw.ho_notify_key(st, assoc, ran, N.Ngap.ue_key(amf))

def Lw.ho_cancel_none(+st: S.State, +key: U32, +ue: S.Ue, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, (S.Keep{}, [N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.cancel_ack(key, S.Ue.ran_id(ue))}, N.Note{F.Warn{}, "NGAP: Handover Cancel with no handover pending"}])) == True{} : Bool}:
  +x : N.Act = N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.cancel_ack(key, S.Ue.ran_id(ue))}
  +n : N.Act = N.Note{F.Warn{}, "NGAP: Handover Cancel with no handover pending"}
  Lv.leaf(st, S.Keep{}, [x, n], Lv.cons(st, x, [n], ek, {==}), {==})

def Lw.ho_cancel_phase(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Ho.Ho.cancel_phase(key, ue, p)) == True{} : Bool}:
  match p:
    case S.Handover{guard, +ctx, +nh, source, +leg}:
      +x : N.Act = N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.cancel_ack(key, S.Ue.ran_id(ue))}
      +c = Ho.Ho.radio(G.CauseRadioNetwork.handover_cancelled())
      +more : List<&2, N.Act> = [N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Handover Cancel; the target released"}]
      Lv.leaf(st, S.Rephase{key, S.Registered{ctx, nh}}, x <> List.append(&2, N.Act, Ho.Ho.drop(key, leg, c), more), Lv.cons(st, x, List.append(&2, N.Act, Ho.Ho.drop(key, leg, c), more), ek, Lv.append(st, Ho.Ho.drop(key, leg, c), more, Lw.ho_drop(st, key, leg, c, ek), {==})), {==})
    case S.Created{}:
      Lw.ho_cancel_none(st, key, ue, ek)
    case S.Identifying{guard}:
      Lw.ho_cancel_none(st, key, ue, ek)
    case S.Authenticating{guard, av, resynced, supi}:
      Lw.ho_cancel_none(st, key, ue, ek)
    case S.SecurityMode{guard, ctx, k_amf}:
      Lw.ho_cancel_none(st, key, ue, ek)
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      Lw.ho_cancel_none(st, key, ue, ek)
    case S.Registered{ctx, nh}:
      Lw.ho_cancel_none(st, key, ue, ek)
    case S.Switching{guard, ctx, nh, released}:
      Lw.ho_cancel_none(st, key, ue, ek)
    case S.Releasing{guard}:
      Lw.ho_cancel_none(st, key, ue, ek)

def Lw.ho_cancel_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +m: Maybe<&2, S.Ue>, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Ho.Ho.cancel_ue(assoc, key, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.ho_cancel_phase(st, key, ue, S.Ue.phase(ue), Lv.has_live(st, key, Lv.owned_has(st, assoc, key, ran, ue, eo)))

def Lw.ho_cancel_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +m: Maybe<&2, U32>) -> {Lv.okf(st, Ho.Ho.cancel_key(st, assoc, ran, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.ho_cancel_ue(st, assoc, key, ran, N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran), {==})

def Lw.ho_cancel(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverCancel.View>) -> {Lv.okf(st, Ho.Ho.cancel_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.HandoverCancel.View{+amf, +ran, cause}}:
      Lw.ho_cancel_key(st, assoc, ran, N.Ngap.ue_key(amf))

def Lw.ho_status_phase(+st: S.State, +key: U32, +container: G.RANStatusTransfer_TransparentContainer, +p: S.Phase, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Ho.Ho.status_phase(key, container, p)) == True{} : Bool}:
  match p:
    case S.Handover{guard, ctx, nh, source, leg}:
      match leg:
        case S.Asked{t}:
          {==}
        case S.Acked{+t, +r, +s, ts}:
          Lv.leaf(st, S.Keep{}, [N.UeSend{t, s, key, Ho.Ho.dl_status(key, r, container)}], Lv.cons(st, N.UeSend{t, s, key, Ho.Ho.dl_status(key, r, container)}, [], ek, {==}), {==})
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.ho_status_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +container: G.RANStatusTransfer_TransparentContainer, +m: Maybe<&2, S.Ue>, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Ho.Ho.status_ue(assoc, key, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.ho_status_phase(st, key, container, S.Ue.phase(ue), Lv.has_live(st, key, Lv.owned_has(st, assoc, key, ran, ue, eo)))

def Lw.ho_status_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +container: G.RANStatusTransfer_TransparentContainer, +m: Maybe<&2, U32>) -> {Lv.okf(st, Ho.Ho.status_key(st, assoc, ran, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.ho_status_ue(st, assoc, key, ran, container, N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran), {==})

def Lw.ho_status(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View>) -> {Lv.okf(st, Ho.Ho.status_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.UplinkRANStatusTransfer.View{+amf, +ran, +container}}:
      Lw.ho_status_key(st, assoc, ran, container, N.Ngap.ue_key(amf))


# An association going down
# -------------------------
# The handovers it takes part in end, every action built from a context of
# the state, each context only rephased (quiet).

def Lv.quiet(tx: S.Tx) -> Bool:
  match tx:
    case S.Keep{}:
      True{}
    case S.Rephase{key, p}:
      True{}
    case S.Both{a, b}:
      Bool.and(Lv.quiet(a), Lv.quiet(b))
    case _:
      False{}

def Lv.quiet_sessions(+tx: S.Tx, +st: S.State, +e: {Lv.quiet(tx) == True{} : Bool}) -> {S.State.sessions(S.Tx.apply(tx, st)) == S.State.sessions(st) : Tb.Table(S.Session)}:
  match tx:
    case S.Keep{}:
      {==}
    case S.Rephase{key, p}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Both{+a, +b}:
      Equal.trans(Tb.Table(S.Session), S.State.sessions(S.Tx.apply(b, S.Tx.apply(a, st))), S.State.sessions(S.Tx.apply(a, st)), S.State.sessions(st), Lv.quiet_sessions(b, S.Tx.apply(a, st), P.Bool.and_true_r(Lv.quiet(a), Lv.quiet(b), e)), Lv.quiet_sessions(a, st, P.Bool.and_true_l(Lv.quiet(a), Lv.quiet(b), e)))
    case S.Put{key, ue}:
      Empty.absurd({S.State.sessions(S.Tx.apply(S.Put{key, ue}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}, P.Refute.bool(e))
    case S.Del{key}:
      Empty.absurd({S.State.sessions(S.Tx.apply(S.Del{key}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}, P.Refute.bool(e))
    case S.PutSession{key, x}:
      Empty.absurd({S.State.sessions(S.Tx.apply(S.PutSession{key, x}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}, P.Refute.bool(e))
    case S.Revar{key, v}:
      Empty.absurd({S.State.sessions(S.Tx.apply(S.Revar{key, v}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}, P.Refute.bool(e))
    case S.DelSession{key}:
      Empty.absurd({S.State.sessions(S.Tx.apply(S.DelSession{key}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}, P.Refute.bool(e))
    case S.Subs{subs}:
      Empty.absurd({S.State.sessions(S.Tx.apply(S.Subs{subs}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}, P.Refute.bool(e))
    case S.SetLink{link}:
      Empty.absurd({S.State.sessions(S.Tx.apply(S.SetLink{link}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}, P.Refute.bool(e))
    case S.BumpUe{bk}:
      Empty.absurd({S.State.sessions(S.Tx.apply(S.BumpUe{bk}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}, P.Refute.bool(e))
    case S.BumpSeq{n}:
      Empty.absurd({S.State.sessions(S.Tx.apply(S.BumpSeq{n}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}, P.Refute.bool(e))

def Lw.ho_lost(+st: S.State, +k: U32, +u: S.Ue, +leg: S.Leg, +ek: {Lv.live(st, k) == True{} : Bool}) -> {Lv.acts(st, Ho.Ho.lost(k, u, leg)) == True{} : Bool}:
  match leg:
    case S.Asked{t}:
      Lv.cons(st, N.UeSend{S.Ue.assoc(u), S.Ue.stream(u), k, Ho.Ho.preparation_failure(k, S.Ue.ran_id(u), Ho.Ho.radio(G.CauseRadioNetwork.ho_failure_in_target_5GC_ngran_node_or_target_system()))}, [], ek, {==})
    case S.Acked{t, r, s, ts}:
      {==}

def Lw.dq(+st: S.State, +o: N.GOut(), +h: {Lv.okf(st, o) == True{} : Bool}, +hq: {Lv.quiet(PT.Tk.tx(o)) == True{} : Bool}) -> {Bool.and(Lv.okf(st, o), Lv.quiet(PT.Tk.tx(o))) == True{} : Bool}:
  P.Bool.and_intro(Lv.okf(st, o), Lv.quiet(PT.Tk.tx(o)), h, hq)

def Lw.ho_down_leg(+st: S.State, +k: U32, +u: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +target: Bool, +source: Bool, +ek: {Lv.live(st, k) == True{} : Bool}) -> {Bool.and(Lv.okf(st, Ho.Ho.down_leg(k, u, ctx, nh, leg, target, source)), Lv.quiet(PT.Tk.tx(Ho.Ho.down_leg(k, u, ctx, nh, leg, target, source)))) == True{} : Bool}:
  match target source:
    case True{} True{}:
      Lw.dq(st, (S.Rephase{k, S.Registered{ctx, nh}}, List.append(&2, N.Act, Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's association went down; N2 handover ended"}])), Lv.leaf(st, S.Rephase{k, S.Registered{ctx, nh}}, List.append(&2, N.Act, Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's association went down; N2 handover ended"}]), Lv.append(st, Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's association went down; N2 handover ended"}], Lw.ho_lost(st, k, u, leg, ek), {==}), {==}), {==})
    case True{} False{}:
      Lw.dq(st, (S.Rephase{k, S.Registered{ctx, nh}}, List.append(&2, N.Act, Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's association went down; N2 handover ended"}])), Lv.leaf(st, S.Rephase{k, S.Registered{ctx, nh}}, List.append(&2, N.Act, Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's association went down; N2 handover ended"}]), Lv.append(st, Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's association went down; N2 handover ended"}], Lw.ho_lost(st, k, u, leg, ek), {==}), {==}), {==})
    case False{} True{}:
      Lw.dq(st, (S.Keep{}, Ho.Ho.drop(k, leg, Ho.Ho.radio(G.CauseRadioNetwork.unspecified()))), Lv.leaf(st, S.Keep{}, Ho.Ho.drop(k, leg, Ho.Ho.radio(G.CauseRadioNetwork.unspecified())), Lw.ho_drop(st, k, leg, Ho.Ho.radio(G.CauseRadioNetwork.unspecified()), ek), {==}), {==})
    case False{} False{}:
      {==}

def Lw.ho_down_row(+st: S.State, +assoc: U32, +k: U32, +u: S.Ue, +p: S.Phase, +ek: {Lv.live(st, k) == True{} : Bool}) -> {Bool.and(Lv.okf(st, Ho.Ho.down_row(assoc, k, u, p)), Lv.quiet(PT.Tk.tx(Ho.Ho.down_row(assoc, k, u, p)))) == True{} : Bool}:
  match p:
    case S.Handover{guard, +ctx, +nh, source, +leg}:
      Lw.ho_down_leg(st, k, u, ctx, nh, leg, U32.is_eq(S.Leg.target(leg), assoc), U32.is_eq(S.Ue.assoc(u), assoc), ek)
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.ho_down_join(+st: S.State, +a: N.GOut(), +b: N.GOut(), +ha: {Bool.and(Lv.okf(st, a), Lv.quiet(PT.Tk.tx(a))) == True{} : Bool}, +hb: {Bool.and(Lv.okf(st, b), Lv.quiet(PT.Tk.tx(b))) == True{} : Bool}) -> {Bool.and(Lv.okf(st, N.Out.join(a, b)), Lv.quiet(PT.Tk.tx(N.Out.join(a, b)))) == True{} : Bool}:
  sj = Equal.sym(S.Tx, PT.Tk.tx(N.Out.join(a, b)), S.Both{PT.Tk.tx(a), PT.Tk.tx(b)}, PT.Tk.tx_join(a, b))
  hq : {Lv.quiet(PT.Tk.tx(N.Out.join(a, b))) == True{} : Bool} = (%sj : {Lv.quiet(_) == True{} : Bool}; P.Bool.and_intro(Lv.quiet(PT.Tk.tx(a)), Lv.quiet(PT.Tk.tx(b)), P.Bool.and_true_r(Lv.okf(st, a), Lv.quiet(PT.Tk.tx(a)), ha), P.Bool.and_true_r(Lv.okf(st, b), Lv.quiet(PT.Tk.tx(b)), hb)))
  P.Bool.and_intro(Lv.okf(st, N.Out.join(a, b)), Lv.quiet(PT.Tk.tx(N.Out.join(a, b))), Lv.join(st, a, b, P.Bool.and_true_l(Lv.okf(st, a), Lv.quiet(PT.Tk.tx(a)), ha), P.Bool.and_true_l(Lv.okf(st, b), Lv.quiet(PT.Tk.tx(b)), hb)), hq)

def Lw.ho_downs(+st: S.State, +assoc: U32, +rows: Tb.Table(S.Ue), +e: {Lv.keys_in(rows, S.State.ues(st)) == True{} : Bool}) -> {Bool.and(Lv.okf(st, Ho.Ho.downs(assoc, rows)), Lv.quiet(PT.Tk.tx(Ho.Ho.downs(assoc, rows)))) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      +ek = Lv.has_live(st, k, P.Bool.and_true_l(Tb.Table.has(S.Ue, k, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e))
      Lw.ho_down_join(st, Ho.Ho.down_row(assoc, k, u, S.Ue.phase(u)), Ho.Ho.downs(assoc, more), Lw.ho_down_row(st, assoc, k, u, S.Ue.phase(u), ek), Lw.ho_downs(st, assoc, more, P.Bool.and_true_r(Tb.Table.has(S.Ue, k, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e)))

def Lw.ho_down_q(+st: S.State, +assoc: U32) -> {Bool.and(Lv.okf(st, Ho.Ho.down(st, assoc)), Lv.quiet(PT.Tk.tx(Ho.Ho.down(st, assoc)))) == True{} : Bool}:
  Lw.ho_downs(st, assoc, S.State.ues(st), Pv.refl(S.State.ues(st)))

def Lw.ho_down(+st: S.State, +assoc: U32) -> {Lv.ok(st, Ho.Ho.down(st, assoc)) == True{} : Bool}:
  Lv.ok_of(st, Ho.Ho.down(st, assoc), P.Bool.and_true_l(Lv.okf(st, Ho.Ho.down(st, assoc)), Lv.quiet(PT.Tk.tx(Ho.Ho.down(st, assoc))), Lw.ho_down_q(st, assoc)))

def Lw.step_sessions(+st: S.State, +o: N.GOut(), +e: {Lv.quiet(PT.Tk.tx(o)) == True{} : Bool}) -> {S.State.sessions(K.Kernel.state(N.Step.of(st, o))) == S.State.sessions(st) : Tb.Table(S.Session)}:
  match o:
    case (+tx, acts):
      Lv.quiet_sessions(tx, st, e)

# The first part of an association going down leaves the sessions.
def Lw.down_sessions(+st: S.State, +assoc: U32) -> {S.State.sessions(K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, assoc)))) == S.State.sessions(st) : Tb.Table(S.Session)}:
  Lw.step_sessions(st, Ho.Ho.down(st, assoc), P.Bool.and_true_r(Lv.okf(st, Ho.Ho.down(st, assoc)), Lv.quiet(PT.Tk.tx(Ho.Ho.down(st, assoc))), Lw.ho_down_q(st, assoc)))

def Lw.ho_route(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>) -> {Lv.ok(st, Ho.Ho.route(st, assoc, stream, kind, code, ies)) == True{} : Bool}:
  PW.Walk.ho(o => {Lv.ok(st, o) == True{} : Bool}, st, assoc, stream, kind, code, ies, {==}, +r => Lw.ho_required(st, assoc, r), +r => Lw.ho_ack(st, assoc, stream, r), +r => Lv.ok_of(st, Ho.Ho.failure_of_view(st, assoc, r), Lw.ho_failure(st, assoc, r)), +r => Lv.ok_of(st, Ho.Ho.notify_of_view(st, assoc, r), Lw.ho_notify(st, assoc, r)), +r => Lv.ok_of(st, Ho.Ho.cancel_of_view(st, assoc, r), Lw.ho_cancel(st, assoc, r)), +r => Lv.ok_of(st, Ho.Ho.status_of_view(st, assoc, r), Lw.ho_status(st, assoc, r)))

def Lw.d2(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool) -> {Lv.ok(st, R.Route.d2(st, assoc, stream, kind, code, ies, entropy, b)) == True{} : Bool}:
  PW.Walk.d2(o => {Lv.ok(st, o) == True{} : Bool}, st, assoc, stream, kind, code, ies, entropy, b, Lw.ho_route(st, assoc, stream, kind, code, ies), +r => Lv.ok_of(st, Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, r), Lw.initial_of_view(st, assoc, stream, entropy, r)), +r => Lw.uplink_of_view(st, assoc, stream, entropy, r), +r => Lv.ok_of(st, Gmm.Gmm.ics_response_of_view(st, assoc, r), Lw.ics_response_of_view(st, assoc, r)), +r => Lv.ok_of(st, Gmm.Gmm.release_request_of_view(st, assoc, r), Lw.release_request_of_view(st, assoc, r)), +r => Lv.ok_of(st, Gmm.Gmm.release_complete_of_view(st, assoc, r), Lw.release_complete_of_view(st, assoc, r)), +r => Lv.ok_of(st, Gsm.Gsm.setup_response_of_view(st, assoc, r), Lw.setup_response_of_view(st, assoc, r)), +r => Lv.ok_of(st, Ps.Ps.of_view(st, assoc, stream, r), Lw.ps_of_view(st, assoc, stream, r)))

def Lv.routed(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32) -> PW.Walk.Routed(o => {Lv.ok(st, o) == True{} : Bool}, st, assoc, stream, entropy):
  +kind => +code => +ies => Lw.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code))

# Every procedure's outcome is ok (Lw).
def Lv.walk(-Q: N.Step() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: PW.Walk.Keep(Q, st), ready: PW.Walk.Ready(Q, st), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), up: @assoc:U32 -> Q(K.Kernel.assoc_up(st, assoc)), down: @assoc:U32 -> Q(K.Kernel.assoc_down(st, assoc)), out: PW.Walk.Out(Q, o => {Lv.ok(st, o) == True{} : Bool}, st)) -> Q(K.Kernel.step(st, ev, entropy)):
  PW.Walk.step(Q, o => {Lv.ok(st, o) == True{} : Bool}, st, ev, entropy, keep, ready, config, up, down, out, +a => +s => Lv.routed(st, entropy, a, s), +bytes => Lv.ok_of(st, Gsm.Gsm.pfcp_data(st, bytes), Lw.pfcp_data(st, bytes)), +timer => Lv.ok_of(st, K.Kernel.fired(st, timer), Lw.fired(st, timer)))


# Steps
# -----

# The guards a step stops name no UE.
def Lv.gone_row(+st: S.State, +k: U32, +t: S.Session, +kept: Bool) -> {Lv.acts(st, N.Gone.row(k, t, kept)) == True{} : Bool}:
  match kept:
    case True{}:
      {==}
    case False{}:
      Lv.cancel(st, k, S.SPhase.guard(S.Session.phase(t)))

def Lv.gone(+st: S.State, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> {Lv.acts(st, N.Gone.cancels(before, after)) == True{} : Bool}:
  match before:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      Lv.append(st, N.Gone.row(k, t, Tb.Table.has(S.Session, k, after)), N.Gone.cancels(more, after), Lv.gone_row(st, k, t, Tb.Table.has(S.Session, k, after)), Lv.gone(st, more, after))

def Lv.gone_when(+st: S.State, +keeps: Bool, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> {Lv.acts(st, N.Gone.when(keeps, before, after)) == True{} : Bool}:
  match keeps:
    case True{}:
      {==}
    case False{}:
      Lv.gone(st, before, after)

def Lv.step_acts(+st: S.State, +o: N.GOut(), +h: {Lv.ok(st, o) == True{} : Bool}) -> {Lv.acts(st, K.Kernel.actions(N.Step.of(st, o))) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      Lv.append(st, acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))), P.Bool.and_true_l(Lv.acts(st, acts), Lv.homed(st, tx, S.State.ues(st)), h), Lv.gone_when(st, S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))))

def Lv.no_response(+st: S.State, +as: List<&2, N.Act>, +h: {Lv.acts(st, as) == True{} : Bool}) -> {N.Ngap.any_ng_setup_response(as) == False{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case +a <> +more:
      +hn = P.Bool.not_true(N.Ngap.is_ng_setup_response(a), P.Bool.and_true_l(Bool.not(N.Ngap.is_ng_setup_response(a)), Lv.tag(st, N.Act.ue(a)), P.Bool.and_true_l(Lv.act(st, a), Lv.acts(st, more), h)))
      sn = Equal.sym(Bool, N.Ngap.is_ng_setup_response(a), False{}, hn)
      %sn : {Bool.or(_, N.Ngap.any_ng_setup_response(more)) == False{} : Bool}
      Lv.no_response(st, more, P.Bool.and_true_r(Lv.act(st, a), Lv.acts(st, more), h))

# Sessions stay owned
# -------------------

def Lv.owned_keep(+k: U32, +t: S.Session, +rest: Tb.Table(S.Session), +b: Bool, +ues: Tb.Table(S.Ue), +ht: {Tb.Table.has(S.Ue, S.Session.ue(t), ues) == True{} : Bool}, +hr: {S.Sessions.owned(rest, ues) == True{} : Bool}) -> {S.Sessions.owned(Tb.Table.keep(S.Session, k, t, rest, b), ues) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(rest, ues), ht, hr)
    case False{}:
      hr

def Lv.owned_sift(+s: S.SSieve, +ss: Tb.Table(S.Session), +ues: Tb.Table(S.Ue), +e: {S.Sessions.owned(ss, ues) == True{} : Bool}) -> {S.Sessions.owned(S.Sessions.sift(s, ss), ues) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      Lv.owned_keep(k, t, S.Sessions.sift(s, more), S.SSieve.keeps(s, k, t), ues, P.Bool.and_true_l(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(more, ues), e), Lv.owned_sift(s, more, ues, P.Bool.and_true_r(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(more, ues), e)))

def Lv.owned_own_keep(+k: U32, +t: S.Session, +rest: Tb.Table(S.Session), +b: Bool, +ues: Tb.Table(S.Ue), +eb: {Tb.Table.has(S.Ue, S.Session.ue(t), ues) == b : Bool}, +hr: {S.Sessions.owned(rest, ues) == True{} : Bool}) -> {S.Sessions.owned(Tb.Table.keep(S.Session, k, t, rest, b), ues) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(rest, ues), eb, hr)
    case False{}:
      hr

# The sessions a put keeps are those of the contexts left.
def Lv.owned_owned(+ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> {S.Sessions.owned(S.Sessions.sift(S.SOwned{ues}, ss), ues) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      Lv.owned_own_keep(k, t, S.Sessions.sift(S.SOwned{ues}, more), Tb.Table.has(S.Ue, S.Session.ue(t), ues), ues, {==}, Lv.owned_owned(ues, more))

def Lv.owned_rephase(+ss: Tb.Table(S.Session), +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +e: {S.Sessions.owned(ss, ues) == True{} : Bool}) -> {S.Sessions.owned(ss, S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (k, +t) <> +more:
      +x = S.Session.ue(t)
      P.Bool.and_intro(Tb.Table.has(S.Ue, x, S.Ues.rephase(key, p, ues)), S.Sessions.owned(more, S.Ues.rephase(key, p, ues)), Equal.trans(Bool, Tb.Table.has(S.Ue, x, S.Ues.rephase(key, p, ues)), Tb.Table.has(S.Ue, x, ues), True{}, Lv.has_rephase(x, key, p, ues), P.Bool.and_true_l(Tb.Table.has(S.Ue, x, ues), S.Sessions.owned(more, ues), e)), Lv.owned_rephase(more, key, p, ues, P.Bool.and_true_r(Tb.Table.has(S.Ue, x, ues), S.Sessions.owned(more, ues), e)))

def Lv.has_except(+x: U32, +key: U32, +ues: Tb.Table(S.Ue), +ne: {Bool.not(U32.is_eq(x, key)) == True{} : Bool}, +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, x, ues) == m : Maybe<&2, S.Ue>}, +eh: {Tb.Table.present(S.Ue, m) == True{} : Bool}) -> {Tb.Table.has(S.Ue, x, S.Ues.sift(S.Except{key}, ues)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Tb.Table.has(S.Ue, x, S.Ues.sift(S.Except{key}, ues)) == True{} : Bool}, P.Refute.bool(eh))
    case Some{+w}:
      Lv.get_has(S.Ues.sift(S.Except{key}, ues), x, w, PT.Sift.get(S.Except{key}, x, w, ues, em, ne))

def Lv.owned_del_keep(+k: U32, +t: S.Session, +rest: Tb.Table(S.Session), +b: Bool, +key: U32, +ues: Tb.Table(S.Ue), +eb: {Bool.not(U32.is_eq(S.Session.ue(t), key)) == b : Bool}, +ht: {Tb.Table.has(S.Ue, S.Session.ue(t), ues) == True{} : Bool}, +hr: {S.Sessions.owned(rest, S.Ues.sift(S.Except{key}, ues)) == True{} : Bool}) -> {S.Sessions.owned(Tb.Table.keep(S.Session, k, t, rest, b), S.Ues.sift(S.Except{key}, ues)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Tb.Table.has(S.Ue, S.Session.ue(t), S.Ues.sift(S.Except{key}, ues)), S.Sessions.owned(rest, S.Ues.sift(S.Except{key}, ues)), Lv.has_except(S.Session.ue(t), key, ues, eb, Tb.Table.get(S.Ue, S.Session.ue(t), ues), {==}, ht), hr)
    case False{}:
      hr

# Forgetting a context forgets its sessions, so the others keep theirs.
def Lv.owned_del(+ss: Tb.Table(S.Session), +key: U32, +ues: Tb.Table(S.Ue), +e: {S.Sessions.owned(ss, ues) == True{} : Bool}) -> {S.Sessions.owned(S.Sessions.sift(S.SOthers{key}, ss), S.Ues.sift(S.Except{key}, ues)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      Lv.owned_del_keep(k, t, S.Sessions.sift(S.SOthers{key}, more), Bool.not(U32.is_eq(S.Session.ue(t), key)), key, ues, {==}, P.Bool.and_true_l(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(more, ues), e), Lv.owned_del(more, key, ues, P.Bool.and_true_r(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(more, ues), e)))

def Lv.ue_revar(+hit: Bool, +t: S.Session, +v: S.SVar) -> {S.Session.ue(S.Session.revar_if(t, v, hit)) == S.Session.ue(t) : U32}:
  match hit:
    case False{}:
      {==}
    case True{}:
      match t:
        case S.Session{id, var}:
          {==}

def Lv.owned_revar(+ss: Tb.Table(S.Session), +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +e: {S.Sessions.owned(ss, ues) == True{} : Bool}) -> {S.Sessions.owned(S.Sessions.revar(key, v, ss), ues) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      er = Equal.sym(U32, S.Session.ue(S.Session.revar_if(t, v, U32.is_eq(k, key))), S.Session.ue(t), Lv.ue_revar(U32.is_eq(k, key), t, v))
      %er : {Bool.and(Tb.Table.has(S.Ue, _, ues), S.Sessions.owned(S.Sessions.revar(key, v, more), ues)) == True{} : Bool}
      P.Bool.and_intro(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(S.Sessions.revar(key, v, more), ues), P.Bool.and_true_l(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(more, ues), e), Lv.owned_revar(more, key, v, ues, P.Bool.and_true_r(Tb.Table.has(S.Ue, S.Session.ue(t), ues), S.Sessions.owned(more, ues), e)))

# A gone UE is not live
# ---------------------

def Inv.none(+st0: S.State) -> Bool:
  True{}

def Inv.owned(+st0: S.State) -> Bool:
  S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0))

def Ow.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  S.Sessions.owned(ss, ues)

def Ow.tx_put(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Ow.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Ow.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  Lv.owned_owned(S.Ues.put(key, ue, ues), ss)

def Ow.tx_rephase(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Ow.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Ow.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  Lv.owned_rephase(ss, key, p, ues, e)

def Ow.tx_del(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Ow.inv(st0, ues, ss) == True{} : Bool}) -> {Ow.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Lv.owned_del(ss, key, ues, e)

def Ow.tx_put_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Ow.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Ow.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  +hs = P.Bool.and_true_r(S.Ids.seid(key), Bool.and(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s)))), h)
  P.Bool.and_intro(Tb.Table.has(S.Ue, S.Session.ue(s), ues), S.Sessions.owned(S.Sessions.sift(S.SClear{key, s}, ss), ues), P.Bool.and_true_l(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s))), hs), Lv.owned_sift(S.SClear{key, s}, ss, ues, e))

def Ow.tx_revar(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Ow.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.revar_ok(st0, v) == True{} : Bool}) -> {Ow.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  Lv.owned_revar(ss, key, v, ues, e)

def Ow.tx_del_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Ow.inv(st0, ues, ss) == True{} : Bool}) -> {Ow.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  Lv.owned_sift(S.SExcept{key}, ss, ues, e)

def Lv.dead3(+h: Bool, +n: Bool, +o: Bool, +eh: {h == False{} : Bool}, +en: {n == False{} : Bool}, eo: {o == True{} : Bool} -> {h == True{} : Bool}) -> {Bool.or(Bool.or(h, n), o) == False{} : Bool}:
  match h:
    case True{}:
      Empty.absurd({Bool.or(Bool.or(True{}, n), o) == False{} : Bool}, P.Refute.true_false(eh))
    case False{}:
      match n:
        case True{}:
          Empty.absurd({Bool.or(Bool.or(False{}, True{}), o) == False{} : Bool}, P.Refute.true_false(en))
        case False{}:
          match o:
            case True{}:
              Empty.absurd({Bool.or(Bool.or(False{}, False{}), True{}) == False{} : Bool}, P.Refute.bool(eo({==})))
            case False{}:
              {==}

def Lv.dead(+st: S.State, +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}) -> {Lv.live(st, k) == False{} : Bool}:
  sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), None{}, eg)
  Lv.dead3(Tb.Table.has(S.Ue, k, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{k}), Lv.owner(k, S.State.sessions(st)), (%sg : {Tb.Table.present(S.Ue, _) == False{} : Bool}; {==}), en, w => Lv.owner_has(k, S.State.sessions(st), S.State.ues(st), eo, w))

def Lv.not_k(+st: S.State, +x: U32, +k: U32, +b: Bool, +eb: {U32.is_eq(x, k) == b : Bool}, +ht: {Lv.live(st, x) == True{} : Bool}, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      ex = P.U32.eq_of_is_eq(x, k, eb)
      hk : {Lv.live(st, k) == True{} : Bool} = (%ex : {Lv.live(st, _) == True{} : Bool}; ht)
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, P.Refute.true_false(Equal.trans(Bool, True{}, Lv.live(st, k), False{}, Equal.sym(Bool, Lv.live(st, k), True{}, hk), Lv.dead(st, k, eo, eg, en))))

def Lv.tag_spare(+st: S.State, +m: Maybe<&2, U32>, +k: U32, +ht: {Lv.tag(st, m) == True{} : Bool}, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}) -> {Bool.not(S.Maybe.same_u32(m, Some{k})) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      Lv.not_k(st, x, k, U32.is_eq(x, k), {==}, ht, eo, eg, en)

# No action a UE procedure takes is built from a key that is not live.
def Lv.spare_of(+st: S.State, +as: List<&2, N.Act>, +k: U32, +h: {Lv.acts(st, as) == True{} : Bool}, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}) -> {N.Acts.spare(k, as) == True{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case +a <> +more:
      +ha = P.Bool.and_true_l(Lv.act(st, a), Lv.acts(st, more), h)
      P.Bool.and_intro(Bool.not(S.Maybe.same_u32(N.Act.ue(a), Some{k})), N.Acts.spare(k, more), Lv.tag_spare(st, N.Act.ue(a), k, P.Bool.and_true_r(Bool.not(N.Ngap.is_ng_setup_response(a)), Lv.tag(st, N.Act.ue(a)), ha), eo, eg, en), Lv.spare_of(st, more, k, P.Bool.and_true_r(Lv.act(st, a), Lv.acts(st, more), h), eo, eg, en))

# Every event
# -----------

# The guards a step stops name no UE either.
def Lv.spare_app(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {N.Acts.spare(k, xs) == True{} : Bool}, +hy: {N.Acts.spare(k, ys) == True{} : Bool}) -> {N.Acts.spare(k, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      +x = Bool.not(S.Maybe.same_u32(N.Act.ue(a), Some{k}))
      P.Bool.and_intro(x, N.Acts.spare(k, List.append(&2, N.Act, more, ys)), P.Bool.and_true_l(x, N.Acts.spare(k, more), hx), Lv.spare_app(k, more, ys, P.Bool.and_true_r(x, N.Acts.spare(k, more), hx), hy))

def Lv.spare_cancel(+k: U32, +key: U32, +g: Maybe<&2, S.Guard>) -> {N.Acts.spare(k, N.Guard.cancel(key, g)) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{guard}:
      {==}

def Lv.spare_row(+k: U32, +key: U32, +t: S.Session, +kept: Bool) -> {N.Acts.spare(k, N.Gone.row(key, t, kept)) == True{} : Bool}:
  match kept:
    case True{}:
      {==}
    case False{}:
      Lv.spare_cancel(k, key, S.SPhase.guard(S.Session.phase(t)))

def Lv.spare_gone(+k: U32, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> {N.Acts.spare(k, N.Gone.cancels(before, after)) == True{} : Bool}:
  match before:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Lv.spare_app(k, N.Gone.row(key, t, Tb.Table.has(S.Session, key, after)), N.Gone.cancels(more, after), Lv.spare_row(k, key, t, Tb.Table.has(S.Session, key, after)), Lv.spare_gone(k, more, after))

def Lv.spare_when(+k: U32, +keeps: Bool, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> {N.Acts.spare(k, N.Gone.when(keeps, before, after)) == True{} : Bool}:
  match keeps:
    case True{}:
      {==}
    case False{}:
      Lv.spare_gone(k, before, after)

def Lv.spare_step(+k: U32, +st: S.State, +o: N.GOut(), +h: {N.Acts.spare(k, Lv.as(o)) == True{} : Bool}) -> {N.Acts.spare(k, K.Kernel.actions(N.Step.of(st, o))) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      Lv.spare_app(k, acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))), h, Lv.spare_when(k, S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))))

def Lv.config_spare(+complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), +k: U32) -> {N.Acts.spare(k, K.Kernel.actions(K.Kernel.config(complete, st, tlvs, entropy))) == True{} : Bool}:
  match complete:
    case False{}:
      {==}
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          +cfg = S.Cfg.of(tlvs)
          +st2 : S.State = S.State{Some{cfg}, Au.Subscribers.of(S.Cfg.subscribers(cfg)), assocs, ues, sessions, pfcp_seq, next_ue, S.N4{List.take(&2, U32, entropy, 4n), S.Idle{}}}
          Lv.spare_step(k, st2, N.Out.also(Up.N4.start(st2), [N.Note{F.Info{}, "Config: loaded; PFCP association requested"}]), {==})

def Lv.up_spare(+st: S.State, +assoc: U32, +k: U32) -> {N.Acts.spare(k, K.Kernel.actions(K.Kernel.assoc_up(st, assoc))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      {==}

def Lv.drop_spare(+st: S.State, +s1: S.State, +assoc: U32, +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}, +ess: {S.State.sessions(s1) == S.State.sessions(st) : Tb.Table(S.Session)}) -> {N.Acts.spare(k, K.Kernel.actions(K.Kernel.drop(s1, assoc))) == True{} : Bool}:
  match s1:
    case S.State{config, subs, assocs, +ues, +sessions, +pfcp_seq, next_ue, n4}:
      +gone = S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions)
      +note : N.Act = N.Note{F.Info{}, "NGAP: association down; its UE contexts and sessions released"}
      +xs = List.append(&2, N.Act, Up.N4.deletions(gone, pfcp_seq), [note])
      hr : {Lv.srows(gone, S.State.sessions(st)) == True{} : Bool} = (%ess : {Lv.srows(gone, _) == True{} : Bool}; Lv.srows_sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions))
      Lv.spare_app(k, xs, N.Gone.cancels(gone, []), Lv.spare_of(st, xs, k, Lv.append(st, Up.N4.deletions(gone, pfcp_seq), [note], Lv.dels(st, gone, pfcp_seq, hr), {==}), eo, eg, en), Lv.spare_gone(k, gone, []))

# An association going down: its handovers end, then its contexts go.
def Lv.down_spare(+st: S.State, +assoc: U32, +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}) -> {N.Acts.spare(k, K.Kernel.actions(K.Kernel.assoc_down(st, assoc))) == True{} : Bool}:
  +o = Ho.Ho.down(st, assoc)
  +hq = Lw.ho_down_q(st, assoc)
  +hf = P.Bool.and_true_l(Lv.okf(st, o), Lv.quiet(PT.Tk.tx(o)), hq)
  +hx = Lv.spare_step(k, st, o, Lv.spare_of(st, Lv.as(o), k, P.Bool.and_true_l(Lv.acts(st, Lv.as(o)), Lv.free(st, PT.Tk.tx(o)), hf), eo, eg, en))
  Lv.spare_app(k, K.Kernel.actions(N.Step.of(st, o)), K.Kernel.actions(K.Kernel.drop(K.Kernel.state(N.Step.of(st, o)), assoc)), hx, Lv.drop_spare(st, K.Kernel.state(N.Step.of(st, o)), assoc, k, eo, eg, en, Lw.down_sessions(st, assoc)))
def Lv.down_owned(+st: S.State, +assoc: U32) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(K.Kernel.drop(st, assoc))), S.State.ues(K.Kernel.state(K.Kernel.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
      Lv.owned_owned(S.Ues.drop_assoc(assoc, ues), sessions)

# Invariants of every step
# ------------------------
# A property of the context and session tables that every transaction a UE
# procedure may run keeps (Inv.tx), and that an association going down keeps,
# holds after every step (PW.Walk).

def Inv.Tx(-inv: Tb.Table(S.Ue) -> Tb.Table(S.Session) -> Bool, +st0: S.State) -> Type:
  @tx:S.Tx -> @st:S.State -> {inv(S.State.ues(st), S.State.sessions(st)) == True{} : Bool} -> {Lv.homed(st0, tx, S.State.ues(st)) == True{} : Bool} -> {inv(S.State.ues(S.Tx.apply(tx, st)), S.State.sessions(S.Tx.apply(tx, st))) == True{} : Bool}

# Each kind of transaction keeps inv, a property of the tables under a
# premise pre on the state before the step: a walk over the transaction
# holds it through every one.

def Inv.Put(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+ue:S.Ue -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> @+h:{Lv.homed(st0, S.Put{key, ue}, ues) == True{} : Bool} -> {inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}

def Inv.Rephase(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+p:S.Phase -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> @+h:{Lv.homed(st0, S.Rephase{key, p}, ues) == True{} : Bool} -> {inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}

def Inv.Del(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> {inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}

def Inv.PutSession(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+s:S.Session -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> @+h:{Lv.homed(st0, S.PutSession{key, s}, ues) == True{} : Bool} -> {inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}

def Inv.Revar(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+v:S.SVar -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> @+h:{Lv.revar_ok(st0, v) == True{} : Bool} -> {inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}

def Inv.DelSession(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> {inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}

# The second of two transactions is homed in the tables the first leaves.
def Inv.second(+st0: S.State, +a: S.Tx, +b: S.Tx, +st: S.State, +h: {Lv.homed(st0, S.Both{a, b}, S.State.ues(st)) == True{} : Bool}) -> {Lv.homed(st0, b, S.State.ues(S.Tx.apply(a, st))) == True{} : Bool}:
  eu = Equal.sym(Tb.Table(S.Ue), S.State.ues(S.Tx.apply(a, st)), PT.Tk.ues(a, S.State.ues(st)), PT.Tk.ues_apply(a, st))
  (%eu : {Lv.homed(st0, b, _) == True{} : Bool}; P.Bool.and_true_r(Lv.homed(st0, a, S.State.ues(st)), Lv.homed(st0, b, PT.Tk.ues(a, S.State.ues(st))), h))

def Inv.tx(~inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, ~pre: @+st0:S.State -> Bool, ~put: Inv.Put(inv, pre), ~rephase: Inv.Rephase(inv, pre), ~del: Inv.Del(inv, pre), ~put_session: Inv.PutSession(inv, pre), ~revar: Inv.Revar(inv, pre), ~del_session: Inv.DelSession(inv, pre), +st0: S.State, +ep: {pre(st0) == True{} : Bool}, +tx: S.Tx, +st: S.State, +e: {inv(st0, S.State.ues(st), S.State.sessions(st)) == True{} : Bool}, +h: {Lv.homed(st0, tx, S.State.ues(st)) == True{} : Bool}) -> {inv(st0, S.State.ues(S.Tx.apply(tx, st)), S.State.sessions(S.Tx.apply(tx, st))) == True{} : Bool}:
  match tx:
    case S.Put{+key, +ue}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
          put(st0, ep, key, ue, ues, sessions, e, h)
    case S.Rephase{+key, +phase}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
          rephase(st0, ep, key, phase, ues, sessions, e, h)
    case S.Del{+key}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
          del(st0, ep, key, ues, sessions, e)
    case S.PutSession{+key, +s}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
          put_session(st0, ep, key, s, ues, sessions, e, h)
    case S.Revar{+key, +v}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
          revar(st0, ep, key, v, ues, sessions, e, h)
    case S.DelSession{+key}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
          del_session(st0, ep, key, ues, sessions, e)
    case S.Both{+a, +b}:
      Inv.tx(~inv, ~pre, ~put, ~rephase, ~del, ~put_session, ~revar, ~del_session, st0, ep, b, S.Tx.apply(a, st), Inv.tx(~inv, ~pre, ~put, ~rephase, ~del, ~put_session, ~revar, ~del_session, st0, ep, a, st, e, P.Bool.and_true_l(Lv.homed(st0, a, S.State.ues(st)), Lv.homed(st0, b, PT.Tk.ues(a, S.State.ues(st))), h)), Inv.second(st0, a, b, st, h))
    case S.Keep{}:
      e
    case S.Subs{new}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          e
    case S.SetLink{link}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          e
    case S.BumpUe{bk}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          e
    case S.BumpSeq{n}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          e

def Inv.out(-inv: Tb.Table(S.Ue) -> Tb.Table(S.Session) -> Bool, +st: S.State, +o: N.GOut(), +e: {inv(S.State.ues(st), S.State.sessions(st)) == True{} : Bool}, t: Inv.Tx(inv, st), +h: {Lv.ok(st, o) == True{} : Bool}) -> PW.Walk.Tables(inv, N.Step.of(st, o)):
  match o:
    case (+tx, +acts):
      t(tx, st, e, P.Bool.and_true_r(Lv.acts(st, acts), Lv.homed(st, tx, S.State.ues(st)), h))

def Inv.step(-inv: Tb.Table(S.Ue) -> Tb.Table(S.Session) -> Bool, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), +e: {inv(S.State.ues(st), S.State.sessions(st)) == True{} : Bool}, t: Inv.Tx(inv, st), t2: Inv.Tx(inv, st), down: @a:U32 -> @s:S.State -> {inv(S.State.ues(s), S.State.sessions(s)) == True{} : Bool} -> PW.Walk.Tables(inv, K.Kernel.drop(s, a))) -> {inv(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))), S.State.sessions(K.Kernel.state(K.Kernel.step(st, ev, entropy)))) == True{} : Bool}:
  Lv.walk(o => PW.Walk.Tables(inv, o), st, ev, entropy, acts => h => e, +as => +acts => h => PW.Walk.assocs(inv, st, as, acts, e), +tlvs => PW.Walk.config(inv, S.Cfg.complete(tlvs), st, tlvs, entropy, e), a => PW.Walk.up(inv, st, a, e), +a => down(a, K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, a))), Inv.out(inv, st, Ho.Ho.down(st, a), e, t2, Lw.ho_down(st, a))), +o => h => Inv.out(inv, st, o, e, t, h))

def Un.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  S.Ues.unique(ues)

def Un.tx_put(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Un.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.clear(key, ue, S.Ues.sift(S.Clear{key, ue}, ues)), S.Ues.unique(S.Ues.sift(S.Clear{key, ue}, ues)), PK.Clear.own(key, ue, ues), PK.Unique.sift(S.Clear{key, ue}, ues, e))

def Un.tx_rephase(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Un.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  er = Equal.sym(Bool, S.Ues.unique(S.Ues.rephase(key, p, ues)), S.Ues.unique(ues), PK.Unique.rephase(key, p, ues))
  %er : {_ == True{} : Bool}
  e

def Un.tx_del(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}) -> {Un.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  PK.Unique.sift(S.Except{key}, ues, e)

def Un.tx_put_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Un.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  e

def Un.tx_revar(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.revar_ok(st0, v) == True{} : Bool}) -> {Un.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  e

def Un.tx_del_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}) -> {Un.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  e

def L.amf.indexes.unique(st, ev, entropy, e):
  ({==}, Inv.step(ues => ss => S.Ues.unique(ues), st, ev, entropy, e, tx => st2 => e2 => h => Inv.tx(~Un.inv, ~Inv.none, ~Un.tx_put, ~Un.tx_rephase, ~Un.tx_del, ~Un.tx_put_session, ~Un.tx_revar, ~Un.tx_del_session, st, {==}, tx, st2, e2, h), tx => st2 => e2 => h => Inv.tx(~Un.inv, ~Inv.none, ~Un.tx_put, ~Un.tx_rephase, ~Un.tx_del, ~Un.tx_put_session, ~Un.tx_revar, ~Un.tx_del_session, st, {==}, tx, st2, e2, h), a => s => e1 => PK.Down.unique(s, a, e1)))

def L.amf.sessions.owned(st, ev, entropy, e):
  ({==}, Inv.step(ues => ss => S.Sessions.owned(ss, ues), st, ev, entropy, e, tx => st2 => e2 => h => Inv.tx(~Ow.inv, ~Inv.none, ~Ow.tx_put, ~Ow.tx_rephase, ~Ow.tx_del, ~Ow.tx_put_session, ~Ow.tx_revar, ~Ow.tx_del_session, st, {==}, tx, st2, e2, h), tx => st2 => e2 => h => Inv.tx(~Ow.inv, ~Inv.none, ~Ow.tx_put, ~Ow.tx_rephase, ~Ow.tx_del, ~Ow.tx_put_session, ~Ow.tx_revar, ~Ow.tx_del_session, st, {==}, tx, st2, e2, h), a => s => e1 => Lv.down_owned(s, a)))

# Contexts stay guarded
# ---------------------

def Gd.keep(+k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), +b: Bool, +hv: {S.Phase.guarded(S.Ue.phase(v)) == True{} : Bool}, +hr: {S.Ues.guarded(rest) == True{} : Bool}) -> {S.Ues.guarded(Tb.Table.keep(S.Ue, k, v, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(S.Phase.guarded(S.Ue.phase(v)), S.Ues.guarded(rest), hv, hr)
    case False{}:
      hr

def Gd.sift(+s: S.Sieve, +ues: Tb.Table(S.Ue), +e: {S.Ues.guarded(ues) == True{} : Bool}) -> {S.Ues.guarded(S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      Gd.keep(k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), P.Bool.and_true_l(S.Phase.guarded(S.Ue.phase(v)), S.Ues.guarded(more), e), Gd.sift(s, more, P.Bool.and_true_r(S.Phase.guarded(S.Ue.phase(v)), S.Ues.guarded(more), e)))

def Gd.rephase_if(+b: Bool, +u: S.Ue, +p: S.Phase, +hu: {S.Phase.guarded(S.Ue.phase(u)) == True{} : Bool}, +hp: {S.Phase.guarded(p) == True{} : Bool}) -> {S.Phase.guarded(S.Ue.phase(S.Ue.rephase_if(u, p, b))) == True{} : Bool}:
  match b:
    case True{}:
      Equal.trans(Bool, S.Phase.guarded(S.Ue.phase(S.Ue.with_phase(u, p))), S.Phase.guarded(p), True{}, Lv.g_phase(u, p), hp)
    case False{}:
      hu

def Gd.rephase(+key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +e: {S.Ues.guarded(ues) == True{} : Bool}, +hp: {S.Phase.guarded(p) == True{} : Bool}) -> {S.Ues.guarded(S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      P.Bool.and_intro(S.Phase.guarded(S.Ue.phase(S.Ue.rephase_if(u, p, U32.is_eq(k, key)))), S.Ues.guarded(S.Ues.rephase(key, p, more)), Gd.rephase_if(U32.is_eq(k, key), u, p, P.Bool.and_true_l(S.Phase.guarded(S.Ue.phase(u)), S.Ues.guarded(more), e), hp), Gd.rephase(key, p, more, P.Bool.and_true_r(S.Phase.guarded(S.Ue.phase(u)), S.Ues.guarded(more), e), hp))

def Gd.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  S.Ues.guarded(ues)

def Gd.tx_put(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Gd.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Phase.guarded(S.Ue.phase(ue)), S.Ues.guarded(S.Ues.sift(S.Clear{key, ue}, ues)), P.Bool.and_true_l(S.Phase.guarded(S.Ue.phase(ue)), S.Ue.single(ue), P.Bool.and_true_r(Lv.keyed(st0, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), S.Ue.single(ue)), h)), Gd.sift(S.Clear{key, ue}, ues, e))

def Gd.tx_rephase(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Gd.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  Gd.rephase(key, p, ues, e, P.Bool.and_true_l(S.Phase.guarded(p), S.Ue.fits(p, Tb.Table.get(S.Ue, key, ues)), h))

def Gd.tx_del(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}) -> {Gd.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Gd.sift(S.Except{key}, ues, e)

def Gd.tx_put_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Gd.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  e

def Gd.tx_revar(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.revar_ok(st0, v) == True{} : Bool}) -> {Gd.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  e

def Gd.tx_del_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}) -> {Gd.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  e

def Gd.down(+st: S.State, +assoc: U32, +e: {S.Ues.guarded(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.guarded(S.State.ues(K.Kernel.state(K.Kernel.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, n4}:
      Gd.sift(S.Others{assoc}, ues, e)

def L.amf.contexts.guarded(st, ev, entropy, e):
  ({==}, Inv.step(ues => ss => S.Ues.guarded(ues), st, ev, entropy, e, tx => st2 => e2 => h => Inv.tx(~Gd.inv, ~Inv.none, ~Gd.tx_put, ~Gd.tx_rephase, ~Gd.tx_del, ~Gd.tx_put_session, ~Gd.tx_revar, ~Gd.tx_del_session, st, {==}, tx, st2, e2, h), tx => st2 => e2 => h => Inv.tx(~Gd.inv, ~Inv.none, ~Gd.tx_put, ~Gd.tx_rephase, ~Gd.tx_del, ~Gd.tx_put_session, ~Gd.tx_revar, ~Gd.tx_del_session, st, {==}, tx, st2, e2, h), a => s => e1 => Gd.down(s, a, e1)))

# Keys
# ----
# Every context key odd and every session key even and not zero, by the keys
# a step puts: a context under a key held, a session under a SEID drawn
# (S.Ids). A context appears only under a key held, that is a context's or
# the one the step gives.

def Id.keep(+k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), +b: Bool, +hk: {S.Ids.odd(k) == True{} : Bool}, +hr: {S.Ues.keyed(rest) == True{} : Bool}) -> {S.Ues.keyed(Tb.Table.keep(S.Ue, k, v, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(S.Ids.odd(k), S.Ues.keyed(rest), hk, hr)
    case False{}:
      hr

def Id.sift(+s: S.Sieve, +ues: Tb.Table(S.Ue), +e: {S.Ues.keyed(ues) == True{} : Bool}) -> {S.Ues.keyed(S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      Id.keep(k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), P.Bool.and_true_l(S.Ids.odd(k), S.Ues.keyed(more), e), Id.sift(s, more, P.Bool.and_true_r(S.Ids.odd(k), S.Ues.keyed(more), e)))

def Id.rephase(+key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +e: {S.Ues.keyed(ues) == True{} : Bool}) -> {S.Ues.keyed(S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      P.Bool.and_intro(S.Ids.odd(k), S.Ues.keyed(S.Ues.rephase(key, p, more)), P.Bool.and_true_l(S.Ids.odd(k), S.Ues.keyed(more), e), Id.rephase(key, p, more, P.Bool.and_true_r(S.Ids.odd(k), S.Ues.keyed(more), e)))

def Id.skeep(+k: U32, +t: S.Session, +rest: Tb.Table(S.Session), +b: Bool, +hk: {S.Ids.seid(k) == True{} : Bool}, +hr: {S.Sessions.keyed(rest) == True{} : Bool}) -> {S.Sessions.keyed(Tb.Table.keep(S.Session, k, t, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(S.Ids.seid(k), S.Sessions.keyed(rest), hk, hr)
    case False{}:
      hr

def Id.ssift(+s: S.SSieve, +ss: Tb.Table(S.Session), +e: {S.Sessions.keyed(ss) == True{} : Bool}) -> {S.Sessions.keyed(S.Sessions.sift(s, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      Id.skeep(k, t, S.Sessions.sift(s, more), S.SSieve.keeps(s, k, t), P.Bool.and_true_l(S.Ids.seid(k), S.Sessions.keyed(more), e), Id.ssift(s, more, P.Bool.and_true_r(S.Ids.seid(k), S.Sessions.keyed(more), e)))

def Id.srevar(+key: U32, +v: S.SVar, +ss: Tb.Table(S.Session), +e: {S.Sessions.keyed(ss) == True{} : Bool}) -> {S.Sessions.keyed(S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Bool.and_intro(S.Ids.seid(k), S.Sessions.keyed(S.Sessions.revar(key, v, more)), P.Bool.and_true_l(S.Ids.seid(k), S.Sessions.keyed(more), e), Id.srevar(key, v, more, P.Bool.and_true_r(S.Ids.seid(k), S.Sessions.keyed(more), e)))

# A key a table holds is odd.
def Id.has_row(+k: U32, +k0: U32, +v: S.Ue, +more: Tb.Table(S.Ue), +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +e: {Bool.and(S.Ids.odd(k0), S.Ues.keyed(more)) == True{} : Bool}, +h: {Tb.Table.present(S.Ue, Tb.Table.hit(S.Ue, v, Tb.Table.get(S.Ue, k, more), b)) == True{} : Bool}, ih: {S.Ues.keyed(more) == True{} : Bool} -> {Tb.Table.has(S.Ue, k, more) == True{} : Bool} -> {S.Ids.odd(k) == True{} : Bool}) -> {S.Ids.odd(k) == True{} : Bool}:
  match b:
    case True{}:
      ek = P.U32.eq_of_is_eq(k0, k, eb)
      (%ek : {S.Ids.odd(_) == True{} : Bool}; P.Bool.and_true_l(S.Ids.odd(k0), S.Ues.keyed(more), e))
    case False{}:
      ih(P.Bool.and_true_r(S.Ids.odd(k0), S.Ues.keyed(more), e), h)

def Id.has_odd(+ues: Tb.Table(S.Ue), +k: U32, +e: {S.Ues.keyed(ues) == True{} : Bool}, +h: {Tb.Table.has(S.Ue, k, ues) == True{} : Bool}) -> {S.Ids.odd(k) == True{} : Bool}:
  match ues:
    case Nil{}:
      Empty.absurd({S.Ids.odd(k) == True{} : Bool}, P.Refute.bool(h))
    case (+k0, +v) <> +more:
      Id.has_row(k, k0, v, more, U32.is_eq(k0, k), {==}, e, h, a => b => Id.has_odd(more, k, a, b))

# The key the step gives is odd.
def Id.fresh_odd(+st0: S.State, +key: U32, +m: Maybe<&2, U32>, +em: {S.State.fresh(st0) == m : Maybe<&2, U32>}, +h: {S.Maybe.same_u32(m, Some{key}) == True{} : Bool}) -> {S.Ids.odd(key) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({S.Ids.odd(key) == True{} : Bool}, P.Refute.bool(h))
    case Some{+x}:
      ex = P.U32.eq_of_is_eq(x, key, h)
      ho = P.Bool.and_true_r(Bool.not(Tb.Table.has(S.Ue, x, S.State.ues(st0))), S.Ids.odd(x), PT.Fresh.of(st0, x, em))
      (%ex : {S.Ids.odd(_) == True{} : Bool}; ho)

def Id.held_go(+st0: S.State, +key: U32, +a: Bool, +ea: {Tb.Table.has(S.Ue, key, S.State.ues(st0)) == a : Bool}, +eu: {S.Ues.keyed(S.State.ues(st0)) == True{} : Bool}, +h: {Bool.or(a, S.Maybe.same_u32(S.State.fresh(st0), Some{key})) == True{} : Bool}) -> {S.Ids.odd(key) == True{} : Bool}:
  match a:
    case True{}:
      Id.has_odd(S.State.ues(st0), key, eu, ea)
    case False{}:
      Id.fresh_odd(st0, key, S.State.fresh(st0), {==}, h)

# A key a context is put under is held, when sessions belong to contexts.
def Id.keyed_held(+st0: S.State, +key: U32, +eo: {S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0)) == True{} : Bool}, +hk: {Lv.keyed(st0, key) == True{} : Bool}) -> {Lv.held(st0, key) == True{} : Bool}:
  seo = Equal.sym(Bool, S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0)), True{}, eo)
  P.Bool.or_true_l(Lv.held(st0, key), Bool.not(S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0))), (%seo : {Bool.not(_) == False{} : Bool}; {==}), hk)

def Id.put_odd(+st0: S.State, +e0: {S.Ids.free(S.State.ues(st0), S.State.sessions(st0)) == True{} : Bool}, +eo: {S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0)) == True{} : Bool}, +key: U32, +hk: {Lv.keyed(st0, key) == True{} : Bool}) -> {S.Ids.odd(key) == True{} : Bool}:
  Id.held_go(st0, key, Tb.Table.has(S.Ue, key, S.State.ues(st0)), {==}, P.Bool.and_true_l(S.Ues.keyed(S.State.ues(st0)), S.Sessions.keyed(S.State.sessions(st0)), e0), Id.keyed_held(st0, key, eo, hk))

def Id.pre(+st0: S.State) -> Bool:
  Bool.and(S.Ids.free(S.State.ues(st0), S.State.sessions(st0)), S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0)))

def Id.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  S.Ids.free(ues, ss)

def Id.tx_put(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Id.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  +e0 = P.Bool.and_true_l(S.Ids.free(S.State.ues(st0), S.State.sessions(st0)), S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0)), ep)
  +eo = P.Bool.and_true_r(S.Ids.free(S.State.ues(st0), S.State.sessions(st0)), S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0)), ep)
  +ho = Id.put_odd(st0, e0, eo, key, P.Bool.and_true_l(Lv.keyed(st0, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), S.Ue.single(ue)), h))
  P.Bool.and_intro(S.Ues.keyed(S.Ues.put(key, ue, ues)), S.Sessions.keyed(S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)), P.Bool.and_intro(S.Ids.odd(key), S.Ues.keyed(S.Ues.sift(S.Clear{key, ue}, ues)), ho, Id.sift(S.Clear{key, ue}, ues, P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e))), Id.ssift(S.SOwned{S.Ues.put(key, ue, ues)}, ss, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)))

def Id.tx_rephase(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Id.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.keyed(S.Ues.rephase(key, p, ues)), S.Sessions.keyed(ss), Id.rephase(key, p, ues, P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)), P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e))

def Id.tx_del(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}) -> {Id.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.keyed(S.Ues.del(key, ues)), S.Sessions.keyed(S.Sessions.drop_ue(key, ss)), Id.sift(S.Except{key}, ues, P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)), Id.ssift(S.SOthers{key}, ss, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)))

def Id.tx_put_session(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Id.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  +old = Bool.and(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s))))
  P.Bool.and_intro(S.Ues.keyed(ues), S.Sessions.keyed(S.Sessions.put(key, s, ss)), P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e), P.Bool.and_intro(S.Ids.seid(key), S.Sessions.keyed(S.Sessions.sift(S.SClear{key, s}, ss)), P.Bool.and_true_l(S.Ids.seid(key), old, h), Id.ssift(S.SClear{key, s}, ss, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e))))

def Id.tx_revar(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.revar_ok(st0, v) == True{} : Bool}) -> {Id.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.keyed(ues), S.Sessions.keyed(S.Sessions.revar(key, v, ss)), P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e), Id.srevar(key, v, ss, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)))

def Id.tx_del_session(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}) -> {Id.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.keyed(ues), S.Sessions.keyed(S.Sessions.del(key, ss)), P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e), Id.ssift(S.SExcept{key}, ss, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)))

def Id.down(+st: S.State, +assoc: U32, +e: {S.Ids.free(S.State.ues(st), S.State.sessions(st)) == True{} : Bool}) -> {S.Ids.free(S.State.ues(K.Kernel.state(K.Kernel.drop(st, assoc))), S.State.sessions(K.Kernel.state(K.Kernel.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
      P.Bool.and_intro(S.Ues.keyed(S.Ues.drop_assoc(assoc, ues)), S.Sessions.keyed(S.Sessions.sift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, sessions)), Id.sift(S.Others{assoc}, ues, P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(sessions), e)), Id.ssift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, sessions, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(sessions), e)))

# No session holds a key that is not a local SEID, nor a context a key that is not odd.
def Id.miss_srow(+k: U32, +k0: U32, +t: S.Session, +more: Tb.Table(S.Session), +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +e: {Bool.and(S.Ids.seid(k0), S.Sessions.keyed(more)) == True{} : Bool}, +f: {S.Ids.seid(k) == False{} : Bool}, ih: {S.Sessions.keyed(more) == True{} : Bool} -> {Tb.Table.has(S.Session, k, more) == False{} : Bool}) -> {Tb.Table.present(S.Session, Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), b)) == False{} : Bool}:
  match b:
    case True{}:
      ek = P.U32.eq_of_is_eq(k0, k, eb)
      hk : {S.Ids.seid(k) == True{} : Bool} = (%ek : {S.Ids.seid(_) == True{} : Bool}; P.Bool.and_true_l(S.Ids.seid(k0), S.Sessions.keyed(more), e))
      Empty.absurd({True{} == False{} : Bool}, P.Refute.true_false(Equal.trans(Bool, True{}, S.Ids.seid(k), False{}, Equal.sym(Bool, S.Ids.seid(k), True{}, hk), f)))
    case False{}:
      ih(P.Bool.and_true_r(S.Ids.seid(k0), S.Sessions.keyed(more), e))

def Id.miss_s(+ss: Tb.Table(S.Session), +k: U32, +e: {S.Sessions.keyed(ss) == True{} : Bool}, +f: {S.Ids.seid(k) == False{} : Bool}) -> {Tb.Table.has(S.Session, k, ss) == False{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      Id.miss_srow(k, k0, t, more, U32.is_eq(k0, k), {==}, e, f, ih => Id.miss_s(more, k, ih, f))

def Id.miss_urow(+k: U32, +k0: U32, +v: S.Ue, +more: Tb.Table(S.Ue), +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +e: {Bool.and(S.Ids.odd(k0), S.Ues.keyed(more)) == True{} : Bool}, +f: {S.Ids.odd(k) == False{} : Bool}, ih: {S.Ues.keyed(more) == True{} : Bool} -> {Tb.Table.has(S.Ue, k, more) == False{} : Bool}) -> {Tb.Table.present(S.Ue, Tb.Table.hit(S.Ue, v, Tb.Table.get(S.Ue, k, more), b)) == False{} : Bool}:
  match b:
    case True{}:
      ek = P.U32.eq_of_is_eq(k0, k, eb)
      hk : {S.Ids.odd(k) == True{} : Bool} = (%ek : {S.Ids.odd(_) == True{} : Bool}; P.Bool.and_true_l(S.Ids.odd(k0), S.Ues.keyed(more), e))
      Empty.absurd({True{} == False{} : Bool}, P.Refute.true_false(Equal.trans(Bool, True{}, S.Ids.odd(k), False{}, Equal.sym(Bool, S.Ids.odd(k), True{}, hk), f)))
    case False{}:
      ih(P.Bool.and_true_r(S.Ids.odd(k0), S.Ues.keyed(more), e))

def Id.miss_u(+ues: Tb.Table(S.Ue), +k: U32, +e: {S.Ues.keyed(ues) == True{} : Bool}, +f: {S.Ids.odd(k) == False{} : Bool}) -> {Tb.Table.has(S.Ue, k, ues) == False{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k0, +v) <> +more:
      Id.miss_urow(k, k0, v, more, U32.is_eq(k0, k), {==}, e, f, ih => Id.miss_u(more, k, ih, f))

def Id.odd_seid(+k: U32, +ho: {S.Ids.odd(k) == True{} : Bool}) -> {S.Ids.seid(k) == False{} : Bool}:
  sho = Equal.sym(Bool, S.Ids.odd(k), True{}, ho)
  (%sho : {Bool.and(Bool.not(_), Bool.not(U32.is_eq(k, 0))) == False{} : Bool}; {==})

# Provenance: every context key of a table is held in st0.
def Pv.all(+st0: S.State, ues: Tb.Table(S.Ue)) -> Bool:
  match ues:
    case Nil{}:
      True{}
    case (+k, v) <> more:
      Bool.and(Lv.held(st0, k), Pv.all(st0, more))

def Pv.of_keys(+st: S.State, +vs: Tb.Table(S.Ue), +e: {Lv.keys_in(vs, S.State.ues(st)) == True{} : Bool}) -> {Pv.all(st, vs) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      +hk = P.Bool.and_true_l(Tb.Table.has(S.Ue, k, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e)
      P.Bool.and_intro(Lv.held(st, k), Pv.all(st, more), P.Bool.or_l(Tb.Table.has(S.Ue, k, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{k}), hk), Pv.of_keys(st, more, P.Bool.and_true_r(Tb.Table.has(S.Ue, k, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e)))

def Pv.keep(+st0: S.State, +k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), +b: Bool, +hk: {Lv.held(st0, k) == True{} : Bool}, +hr: {Pv.all(st0, rest) == True{} : Bool}) -> {Pv.all(st0, Tb.Table.keep(S.Ue, k, v, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Lv.held(st0, k), Pv.all(st0, rest), hk, hr)
    case False{}:
      hr

def Pv.sift(+st0: S.State, +s: S.Sieve, +ues: Tb.Table(S.Ue), +e: {Pv.all(st0, ues) == True{} : Bool}) -> {Pv.all(st0, S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      Pv.keep(st0, k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), P.Bool.and_true_l(Lv.held(st0, k), Pv.all(st0, more), e), Pv.sift(st0, s, more, P.Bool.and_true_r(Lv.held(st0, k), Pv.all(st0, more), e)))

def Pv.rephase(+st0: S.State, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +e: {Pv.all(st0, ues) == True{} : Bool}) -> {Pv.all(st0, S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      P.Bool.and_intro(Lv.held(st0, k), Pv.all(st0, S.Ues.rephase(key, p, more)), P.Bool.and_true_l(Lv.held(st0, k), Pv.all(st0, more), e), Pv.rephase(st0, key, p, more, P.Bool.and_true_r(Lv.held(st0, k), Pv.all(st0, more), e)))

def Pv.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  Pv.all(st0, ues)

def Pv.tx_put(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Pv.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  P.Bool.and_intro(Lv.held(st0, key), Pv.all(st0, S.Ues.sift(S.Clear{key, ue}, ues)), Id.keyed_held(st0, key, ep, P.Bool.and_true_l(Lv.keyed(st0, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), S.Ue.single(ue)), h)), Pv.sift(st0, S.Clear{key, ue}, ues, e))

def Pv.tx_rephase(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Pv.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  Pv.rephase(st0, key, p, ues, e)

def Pv.tx_del(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}) -> {Pv.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Pv.sift(st0, S.Except{key}, ues, e)

def Pv.tx_put_session(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homed(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Pv.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  e

def Pv.tx_revar(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.revar_ok(st0, v) == True{} : Bool}) -> {Pv.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  e

def Pv.tx_del_session(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}) -> {Pv.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  e

def Pv.down(+st0: S.State, +st: S.State, +assoc: U32, +e: {Pv.all(st0, S.State.ues(st)) == True{} : Bool}) -> {Pv.all(st0, S.State.ues(K.Kernel.state(K.Kernel.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, n4}:
      Pv.sift(st0, S.Others{assoc}, ues, e)

def Pv.held_row(+st0: S.State, +k: U32, +k0: U32, +v: S.Ue, +more: Tb.Table(S.Ue), +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +e: {Bool.and(Lv.held(st0, k0), Pv.all(st0, more)) == True{} : Bool}, +h: {Tb.Table.present(S.Ue, Tb.Table.hit(S.Ue, v, Tb.Table.get(S.Ue, k, more), b)) == True{} : Bool}, ih: {Pv.all(st0, more) == True{} : Bool} -> {Tb.Table.has(S.Ue, k, more) == True{} : Bool} -> {Lv.held(st0, k) == True{} : Bool}) -> {Lv.held(st0, k) == True{} : Bool}:
  match b:
    case True{}:
      ek = P.U32.eq_of_is_eq(k0, k, eb)
      (%ek : {Lv.held(st0, _) == True{} : Bool}; P.Bool.and_true_l(Lv.held(st0, k0), Pv.all(st0, more), e))
    case False{}:
      ih(P.Bool.and_true_r(Lv.held(st0, k0), Pv.all(st0, more), e), h)

def Pv.held_of(+st0: S.State, +vs: Tb.Table(S.Ue), +k: U32, +e: {Pv.all(st0, vs) == True{} : Bool}, +h: {Tb.Table.has(S.Ue, k, vs) == True{} : Bool}) -> {Lv.held(st0, k) == True{} : Bool}:
  match vs:
    case Nil{}:
      Empty.absurd({Lv.held(st0, k) == True{} : Bool}, P.Refute.bool(h))
    case (+k0, +v) <> +more:
      Pv.held_row(st0, k, k0, v, more, U32.is_eq(k0, k), {==}, e, h, a => b => Pv.held_of(st0, more, k, a, b))

def Pv.same(+m: Maybe<&2, U32>, +k: U32, +e: {S.Maybe.same_u32(m, Some{k}) == True{} : Bool}) -> {m == Some{k} : Maybe<&2, U32>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{k} : Maybe<&2, U32>}, P.Refute.bool(e))
    case Some{+x}:
      Equal.cong(U32, Maybe<&2, U32>, y => Some{y}, x, k, P.U32.eq_of_is_eq(x, k, e))

# A key that held no context and holds one after the step is the one the step gives.
def Pv.fresh(+st: S.State, +k: U32, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +hh: {Lv.held(st, k) == True{} : Bool}) -> {S.State.fresh(st) == Some{k} : Maybe<&2, U32>}:
  Pv.same(S.State.fresh(st), k, (%eg : {Bool.or(Tb.Table.present(S.Ue, _), S.Maybe.same_u32(S.State.fresh(st), Some{k})) == True{} : Bool}; hh))

def L.state.ids.free(st, ev, entropy, k, e, eo):
  +eu = P.Bool.and_true_l(S.Ues.keyed(S.State.ues(st)), S.Sessions.keyed(S.State.sessions(st)), e)
  +es = P.Bool.and_true_r(S.Ues.keyed(S.State.ues(st)), S.Sessions.keyed(S.State.sessions(st)), e)
  +pv = Inv.step(ues => ss => Pv.all(st, ues), st, ev, entropy, Pv.of_keys(st, S.State.ues(st), Pv.refl(S.State.ues(st))), tx => st2 => e2 => h => Inv.tx(~Pv.inv, ~Inv.owned, ~Pv.tx_put, ~Pv.tx_rephase, ~Pv.tx_del, ~Pv.tx_put_session, ~Pv.tx_revar, ~Pv.tx_del_session, st, eo, tx, st2, e2, h), tx => st2 => e2 => h => Inv.tx(~Pv.inv, ~Inv.owned, ~Pv.tx_put, ~Pv.tx_rephase, ~Pv.tx_del, ~Pv.tx_put_session, ~Pv.tx_revar, ~Pv.tx_del_session, st, eo, tx, st2, e2, h), a => s => e1 => Pv.down(st, s, a, e1))
  +iv = Inv.step(ues => ss => S.Ids.free(ues, ss), st, ev, entropy, e, tx => st2 => e2 => h => Inv.tx(~Id.inv, ~Id.pre, ~Id.tx_put, ~Id.tx_rephase, ~Id.tx_del, ~Id.tx_put_session, ~Id.tx_revar, ~Id.tx_del_session, st, P.Bool.and_intro(S.Ids.free(S.State.ues(st), S.State.sessions(st)), S.Sessions.owned(S.State.sessions(st), S.State.ues(st)), e, eo), tx, st2, e2, h), tx => st2 => e2 => h => Inv.tx(~Id.inv, ~Id.pre, ~Id.tx_put, ~Id.tx_rephase, ~Id.tx_del, ~Id.tx_put_session, ~Id.tx_revar, ~Id.tx_del_session, st, P.Bool.and_intro(S.Ids.free(S.State.ues(st), S.State.sessions(st)), S.Sessions.owned(S.State.sessions(st), S.State.ues(st)), e, eo), tx, st2, e2, h), a => s => e1 => Id.down(s, a, e1))
  (em => PT.Fresh.none(st, k, em), (eg => eh => Pv.fresh(st, k, eg, Pv.held_of(st, S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))), k, pv, eh)), ({==}, (iv, (eh => Id.miss_s(S.State.sessions(st), k, es, Id.odd_seid(k, Id.has_odd(S.State.ues(st), k, eu, eh))), (Id.miss_u(S.State.ues(st), S.N4.timer(), eu, {==}), Id.miss_s(S.State.sessions(st), S.N4.timer(), es, {==})))))))

# Guards stopped
# --------------
# A step that removes a session row stops its guard: every outcome's actions
# end with the stops N.Step.of adds for the rows gone, and an association
# going down adds the same; the other steps keep the session table.

def Gs.stops_app(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.stops(k, ys) == True{} : Bool}) -> {N.Acts.stops(k, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +a <> +more:
      P.Bool.or_r(N.Act.stops(k, a), N.Acts.stops(k, List.append(&2, N.Act, more, ys)), Gs.stops_app(k, more, ys, h))

def Gs.row(+k: U32, +k0: U32, +t: S.Session, +s: S.Session, +g: S.Guard, +more: Tb.Table(S.Session), +after: Tb.Table(S.Session), +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +es: {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), b) == Some{s} : Maybe<&2, S.Session>}, +eg: {S.SPhase.guard(S.Session.phase(s)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.get(S.Session, k, after) == None{} : Maybe<&2, S.Session>}, ih: {Tb.Table.get(S.Session, k, more) == Some{s} : Maybe<&2, S.Session>} -> {N.Acts.stops(k, N.Gone.cancels(more, after)) == True{} : Bool}) -> {N.Acts.stops(k, List.append(&2, N.Act, N.Gone.row(k0, t, Tb.Table.has(S.Session, k0, after)), N.Gone.cancels(more, after))) == True{} : Bool}:
  match b:
    case True{}:
      ek = Equal.sym(U32, k0, k, P.U32.eq_of_is_eq(k0, k, eb))
      %ek : {N.Acts.stops(k, List.append(&2, N.Act, N.Gone.row(_, t, Tb.Table.has(S.Session, _, after)), N.Gone.cancels(more, after))) == True{} : Bool}
      et = Equal.sym(S.Session, t, s, P.Some.inj(S.Session, t, s, es))
      %et : {N.Acts.stops(k, List.append(&2, N.Act, N.Gone.row(k, _, Tb.Table.has(S.Session, k, after)), N.Gone.cancels(more, after))) == True{} : Bool}
      seh = Equal.sym(Maybe<&2, S.Session>, Tb.Table.get(S.Session, k, after), None{}, eh)
      %seh : {N.Acts.stops(k, List.append(&2, N.Act, N.Gone.row(k, s, Tb.Table.present(S.Session, _)), N.Gone.cancels(more, after))) == True{} : Bool}
      seg = Equal.sym(Maybe<&2, S.Guard>, S.SPhase.guard(S.Session.phase(s)), Some{g}, eg)
      %seg : {N.Acts.stops(k, List.append(&2, N.Act, N.Guard.cancel(k, _), N.Gone.cancels(more, after))) == True{} : Bool}
      sk = Equal.sym(Bool, U32.is_eq(k, k), True{}, P.U32.is_eq_refl(k))
      %sk : {Bool.or(_, N.Acts.stops(k, N.Gone.cancels(more, after))) == True{} : Bool}
      {==}
    case False{}:
      Gs.stops_app(k, N.Gone.row(k0, t, Tb.Table.has(S.Session, k0, after)), N.Gone.cancels(more, after), ih(es))

def Gs.gone(+before: Tb.Table(S.Session), +after: Tb.Table(S.Session), +k: U32, +s: S.Session, +g: S.Guard, +es: {Tb.Table.get(S.Session, k, before) == Some{s} : Maybe<&2, S.Session>}, +eg: {S.SPhase.guard(S.Session.phase(s)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.get(S.Session, k, after) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, N.Gone.cancels(before, after)) == True{} : Bool}:
  match before:
    case Nil{}:
      Empty.absurd({N.Acts.stops(k, N.Gone.cancels([], after)) == True{} : Bool}, P.Refute.none_some(S.Session, s, es))
    case (+k0, +t) <> +more:
      Gs.row(k, k0, t, s, g, more, after, U32.is_eq(k0, k), {==}, es, eg, eh, e => Gs.gone(more, after, k, s, g, e, eg, eh))

# A step that keeps the session table removes no row.
def Gs.kept(+ss: Tb.Table(S.Session), +k: U32, +s: S.Session, +es: {Tb.Table.get(S.Session, k, ss) == Some{s} : Maybe<&2, S.Session>}, +eh: {Tb.Table.get(S.Session, k, ss) == None{} : Maybe<&2, S.Session>}) -> Empty:
  P.Refute.none_some(S.Session, s, Equal.trans(Maybe<&2, S.Session>, None{}, Tb.Table.get(S.Session, k, ss), Some{s}, Equal.sym(Maybe<&2, S.Session>, Tb.Table.get(S.Session, k, ss), None{}, eh), es))

def Gs.when(+st: S.State, +tx: S.Tx, +k: U32, +s: S.Session, +g: S.Guard, +keeps: Bool, +ek: {S.Tx.keeps_sessions(tx) == keeps : Bool}, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +eg: {S.SPhase.guard(S.Session.phase(s)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.get(S.Session, k, S.State.sessions(S.Tx.apply(tx, st))) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, N.Gone.when(keeps, S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)))) == True{} : Bool}:
  match keeps:
    case True{}:
      Empty.absurd({N.Acts.stops(k, []) == True{} : Bool}, Gs.kept(S.State.sessions(st), k, s, es, PK.Tx.kept(tx, st, ek, k, eh)))
    case False{}:
      Gs.gone(S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)), k, s, g, es, eg, eh)

def Gs.of(+st: S.State, +o: N.GOut(), +k: U32, +s: S.Session, +g: S.Guard, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +eg: {S.SPhase.guard(S.Session.phase(s)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.get(S.Session, k, S.State.sessions(K.Kernel.state(N.Step.of(st, o)))) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, K.Kernel.actions(N.Step.of(st, o))) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      Gs.stops_app(k, acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))), Gs.when(st, tx, k, s, g, S.Tx.keeps_sessions(tx), {==}, es, eg, eh))

def Gs.config(+complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), +k: U32, +s: S.Session, +g: S.Guard, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +eg: {S.SPhase.guard(S.Session.phase(s)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.get(S.Session, k, S.State.sessions(K.Kernel.state(K.Kernel.config(complete, st, tlvs, entropy)))) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, K.Kernel.actions(K.Kernel.config(complete, st, tlvs, entropy))) == True{} : Bool}:
  match complete:
    case False{}:
      Empty.absurd({N.Acts.stops(k, K.Kernel.actions(K.Kernel.config(False{}, st, tlvs, entropy))) == True{} : Bool}, Gs.kept(S.State.sessions(st), k, s, es, eh))
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          +cfg = S.Cfg.of(tlvs)
          +st2 : S.State = S.State{Some{cfg}, Au.Subscribers.of(S.Cfg.subscribers(cfg)), assocs, ues, sessions, pfcp_seq, next_ue, S.N4{List.take(&2, U32, entropy, 4n), S.Idle{}}}
          Gs.of(st2, N.Out.also(Up.N4.start(st2), [N.Note{F.Info{}, "Config: loaded; PFCP association requested"}]), k, s, g, es, eg, eh)

def Gs.assocs(+st: S.State, +as: Tb.Table(B.Bytes()), +acts: List<&2, N.Act>, +k: U32, +s: S.Session, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +eh: {Tb.Table.get(S.Session, k, S.State.sessions(S.State.with_assocs(st, as))) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, acts) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
      Empty.absurd({N.Acts.stops(k, acts) == True{} : Bool}, Gs.kept(sessions, k, s, es, eh))

def Gs.up(+st: S.State, +assoc: U32, +k: U32, +s: S.Session, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +eh: {Tb.Table.get(S.Session, k, S.State.sessions(K.Kernel.state(K.Kernel.assoc_up(st, assoc)))) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, K.Kernel.actions(K.Kernel.assoc_up(st, assoc))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
      Empty.absurd({N.Acts.stops(k, []) == True{} : Bool}, Gs.kept(sessions, k, s, es, eh))

# A row the sessions owned by left lack is one of the orphans.
def Gs.lost(+k: U32, +s: S.Session, +t: S.Session, +more: Tb.Table(S.Session), +owned: Tb.Table(S.Session), +orphan: Tb.Table(S.Session), +c: Bool, +es: {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), c) == Some{s} : Maybe<&2, S.Session>}, +eh: {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, owned), c) == None{} : Maybe<&2, S.Session>}, ih: {Tb.Table.get(S.Session, k, more) == Some{s} : Maybe<&2, S.Session>} -> {Tb.Table.get(S.Session, k, owned) == None{} : Maybe<&2, S.Session>} -> {Tb.Table.get(S.Session, k, orphan) == Some{s} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, k, orphan) == Some{s} : Maybe<&2, S.Session>}:
  match c:
    case True{}:
      Empty.absurd({Tb.Table.get(S.Session, k, orphan) == Some{s} : Maybe<&2, S.Session>}, P.Refute.none_some(S.Session, t, Equal.sym(Maybe<&2, S.Session>, Some{t}, None{}, eh)))
    case False{}:
      ih(es, eh)

def Gs.found(+k: U32, +s: S.Session, +t: S.Session, +more: Tb.Table(S.Session), +owned: Tb.Table(S.Session), +orphan: Tb.Table(S.Session), +c: Bool, +es: {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), c) == Some{s} : Maybe<&2, S.Session>}, +eh: {Tb.Table.get(S.Session, k, owned) == None{} : Maybe<&2, S.Session>}, ih: {Tb.Table.get(S.Session, k, more) == Some{s} : Maybe<&2, S.Session>} -> {Tb.Table.get(S.Session, k, owned) == None{} : Maybe<&2, S.Session>} -> {Tb.Table.get(S.Session, k, orphan) == Some{s} : Maybe<&2, S.Session>}) -> {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, orphan), c) == Some{s} : Maybe<&2, S.Session>}:
  match c:
    case True{}:
      es
    case False{}:
      ih(es, eh)

def Gs.orphan_row(+k: U32, +s: S.Session, +k0: U32, +t: S.Session, +more: Tb.Table(S.Session), +owned: Tb.Table(S.Session), +orphan: Tb.Table(S.Session), +b: Bool, +es: {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), U32.is_eq(k0, k)) == Some{s} : Maybe<&2, S.Session>}, +eh: {Tb.Table.get(S.Session, k, Tb.Table.keep(S.Session, k0, t, owned, b)) == None{} : Maybe<&2, S.Session>}, ih: {Tb.Table.get(S.Session, k, more) == Some{s} : Maybe<&2, S.Session>} -> {Tb.Table.get(S.Session, k, owned) == None{} : Maybe<&2, S.Session>} -> {Tb.Table.get(S.Session, k, orphan) == Some{s} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, k, Tb.Table.keep(S.Session, k0, t, orphan, Bool.not(b))) == Some{s} : Maybe<&2, S.Session>}:
  match b:
    case True{}:
      Gs.lost(k, s, t, more, owned, orphan, U32.is_eq(k0, k), es, eh, ih)
    case False{}:
      Gs.found(k, s, t, more, owned, orphan, U32.is_eq(k0, k), es, eh, ih)

def Gs.orphan(+left: Tb.Table(S.Ue), ss: Tb.Table(S.Session), +k: U32, +s: S.Session, +es: {Tb.Table.get(S.Session, k, ss) == Some{s} : Maybe<&2, S.Session>}, +eh: {Tb.Table.get(S.Session, k, S.Sessions.sift(S.SOwned{left}, ss)) == None{} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, k, S.Sessions.sift(S.SOrphan{left}, ss)) == Some{s} : Maybe<&2, S.Session>}:
  match ss:
    case Nil{}:
      Empty.absurd({Tb.Table.get(S.Session, k, []) == Some{s} : Maybe<&2, S.Session>}, P.Refute.none_some(S.Session, s, es))
    case (+k0, +t) <> +more:
      Gs.orphan_row(k, s, k0, t, more, S.Sessions.sift(S.SOwned{left}, more), S.Sessions.sift(S.SOrphan{left}, more), Tb.Table.has(S.Ue, S.Session.ue(t), left), es, eh, e1 => e2 => Gs.orphan(left, more, k, s, e1, e2))

def Gs.down(+st: S.State, +assoc: U32, +k: U32, +s: S.Session, +g: S.Guard, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +eg: {S.SPhase.guard(S.Session.phase(s)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.get(S.Session, k, S.State.sessions(K.Kernel.state(K.Kernel.drop(st, assoc)))) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, K.Kernel.actions(K.Kernel.drop(st, assoc))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, +sessions, +pfcp_seq, next_ue, n4}:
      +left = S.Ues.drop_assoc(assoc, ues)
      +gone = S.Sessions.sift(S.SOrphan{left}, sessions)
      +xs = List.append(&2, N.Act, Up.N4.deletions(gone, pfcp_seq), [N.Note{F.Info{}, "NGAP: association down; its UE contexts and sessions released"}])
      Gs.stops_app(k, xs, N.Gone.cancels(gone, []), Gs.gone(gone, [], k, s, g, Gs.orphan(left, sessions, k, s, es, eh), eg, {==}))

# An association going down leaves the sessions until its contexts go.
def Gs.adown(+st: S.State, +assoc: U32, +k: U32, +s: S.Session, +g: S.Guard, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +eg: {S.SPhase.guard(S.Session.phase(s)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.get(S.Session, k, S.State.sessions(K.Kernel.state(K.Kernel.assoc_down(st, assoc)))) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, K.Kernel.actions(K.Kernel.assoc_down(st, assoc))) == True{} : Bool}:
  +s1 = K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, assoc)))
  ss = Equal.sym(Tb.Table(S.Session), S.State.sessions(s1), S.State.sessions(st), Lw.down_sessions(st, assoc))
  es1 : {Tb.Table.get(S.Session, k, S.State.sessions(s1)) == Some{s} : Maybe<&2, S.Session>} = (%ss : {Tb.Table.get(S.Session, k, _) == Some{s} : Maybe<&2, S.Session>}; es)
  Gs.stops_app(k, K.Kernel.actions(N.Step.of(st, Ho.Ho.down(st, assoc))), K.Kernel.actions(K.Kernel.drop(s1, assoc)), Gs.down(s1, assoc, k, s, g, es1, eg, eh))

def L.smf.guard.stopped(st, ev, entropy, k, s, g, es, eg, eh):
  PW.Walk.any(o => {Tb.Table.get(S.Session, k, S.State.sessions(K.Kernel.state(o))) == None{} : Maybe<&2, S.Session>} -> {N.Acts.stops(k, K.Kernel.actions(o)) == True{} : Bool}, st, ev, entropy, acts => h => eh => Empty.absurd({N.Acts.stops(k, acts) == True{} : Bool}, Gs.kept(S.State.sessions(st), k, s, es, eh)), +as => +acts => h => eh => Gs.assocs(st, as, acts, k, s, es, eh), +tlvs => eh => Gs.config(S.Cfg.complete(tlvs), st, tlvs, entropy, k, s, g, es, eg, eh), +a => eh => Gs.up(st, a, k, s, es, eh), +a => eh => Gs.adown(st, a, k, s, g, es, eg, eh), +o => eh => Gs.of(st, o, k, s, g, es, eg, eh))(eh)

def L.amf.release.forgets_ue(st, ev, entropy, k, eo, eg, en):
  Lv.walk(o => {N.Acts.spare(k, K.Kernel.actions(o)) == True{} : Bool}, st, ev, entropy, acts => h => h(k), as => acts => h => h(k), +tlvs => Lv.config_spare(S.Cfg.complete(tlvs), st, tlvs, entropy, k), a => Lv.up_spare(st, a, k), a => Lv.down_spare(st, a, k, eo, eg, en), +o => h => Lv.spare_of(st, K.Kernel.actions(N.Step.of(st, o)), k, Lv.step_acts(st, o, h), eo, eg, en))


