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
import ../LAWS.bend as L
import ./lib.bend as P
import ./kernel.bend as PK
import ./takeover.bend as PT

# Proofs of the liveness laws (ticket 33) and of amf.ng_setup.requires_supported_plmn.

# A guard that fires
# ------------------

def Lv.tx_prepend(+a: N.Act, +o: N.GOut()) -> {PT.Tk.tx(N.Out.prepend(a, o)) == PT.Tk.tx(o) : S.Tx}:
  match o:
    case (tx, acts):
      {==}

# Release Command: the context stays under its key, releasing, with a new guard.
def Lv.release_get(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause) -> {Tb.Table.get(S.Ue, key, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release(st, key, ue, cause))))) == Some{S.Ue.with_phase(ue, S.Releasing{S.Guard{S.State.next_timer(st), 0}})} : Maybe<&2, S.Ue>}:
  +ur = S.Ue.with_phase(ue, S.Releasing{S.Guard{S.State.next_timer(st), 0}})
  +p = Gmm.Gmm.place(st, key, ur)
  +b : N.GOut() = (S.BumpTimer{}, List.append(&2, N.Act, N.Guard.cancel(S.Ue.guard(ue)), [N.TimerStart{Some{key}, S.State.next_timer(st), Gmm.Gmm.guard_ms()}]))
  +e = Gmm.Gmm.evict(S.Ues.evicted(key, ur, S.State.ues(st)), S.State.sessions(st), S.State.pfcp_seq(st))
  er = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release(st, key, ue, cause)))), PT.Tk.ues(PT.Tk.tx(Gmm.Gmm.release(st, key, ue, cause)), S.State.ues(st)), PT.Tk.render(st, Gmm.Gmm.release(st, key, ue, cause)))
  %er : {Tb.Table.get(S.Ue, key, _) == Some{ur} : Maybe<&2, S.Ue>}
  ep = Equal.sym(S.Tx, PT.Tk.tx(N.Out.prepend(N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}, N.Out.join(p, b))), PT.Tk.tx(N.Out.join(p, b)), Lv.tx_prepend(N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}, N.Out.join(p, b)))
  %ep : {Tb.Table.get(S.Ue, key, PT.Tk.ues(_, S.State.ues(st))) == Some{ur} : Maybe<&2, S.Ue>}
  ej = Equal.sym(S.Tx, PT.Tk.tx(N.Out.join(p, b)), S.Both{PT.Tk.tx(p), PT.Tk.tx(b)}, PT.Tk.tx_join(p, b))
  %ej : {Tb.Table.get(S.Ue, key, PT.Tk.ues(_, S.State.ues(st))) == Some{ur} : Maybe<&2, S.Ue>}
  ei = Equal.sym(S.Tx, PT.Tk.tx(p), S.Both{S.Put{key, ur}, PT.Tk.tx(e)}, PT.Tk.tx_join((S.Put{key, ur}, []), e))
  %ei : {Tb.Table.get(S.Ue, key, PT.Tk.ues(S.BumpTimer{}, PT.Tk.ues(_, S.State.ues(st)))) == Some{ur} : Maybe<&2, S.Ue>}
  ee = Equal.sym(Tb.Table(S.Ue), PT.Tk.ues(PT.Tk.tx(e), S.Ues.put(key, ur, S.State.ues(st))), S.Ues.put(key, ur, S.State.ues(st)), PT.Tk.evict(S.Ues.evicted(key, ur, S.State.ues(st)), S.State.sessions(st), S.State.pfcp_seq(st), S.Ues.put(key, ur, S.State.ues(st))))
  %ee : {Tb.Table.get(S.Ue, key, _) == Some{ur} : Maybe<&2, S.Ue>}
  ek = Equal.sym(Bool, U32.is_eq(key, key), True{}, P.U32.is_eq_refl(key))
  %ek : {Tb.Table.hit(S.Ue, ur, Tb.Table.get(S.Ue, key, S.Ues.sift(S.Clear{key, ur}, S.State.ues(st))), _) == Some{ur} : Maybe<&2, S.Ue>}
  {==}

# At the retry limit a guard that is not the release's gives up and releases.
def Lv.retried(+st: S.State, +k: U32, +u: S.Ue, +g: S.Guard, +eg: {S.Ue.guard(u) == Some{g} : Maybe<&2, S.Guard>}, np: {S.Ue.phase(u) == S.Releasing{g} : S.Phase} -> Empty, +er: {U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()) == False{} : Bool}) -> {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, S.Ue.phase(u)))))) == Some{S.Ue.with_phase(u, S.Releasing{S.Guard{S.State.next_timer(st), 0}})} : Maybe<&2, S.Ue>}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      match phase:
        case S.Created{}:
          Empty.absurd({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Created{}, last_dl}, S.Created{}))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}, P.Refute.none_some(S.Guard, g, eg))
        case S.Identifying{+guard}:
          eq = Equal.sym(S.Guard, guard, g, PT.Some.inj(S.Guard, guard, g, eg))
          ser = Equal.sym(Bool, U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()), False{}, er)
          %eq : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Identifying{_}, last_dl}, _, S.Identifying{_}, U32.is_lt(S.Guard.retries(_), Gmm.Gmm.max_retries())))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}
          %ser : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Identifying{g}, last_dl}, g, S.Identifying{g}, _))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}
          Lv.release_get(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Identifying{g}, last_dl}, N.Ngap.nas_cause(G.CauseNas.unspecified()))
        case S.Authenticating{+guard, av, resynced, asupi}:
          eq = Equal.sym(S.Guard, guard, g, PT.Some.inj(S.Guard, guard, g, eg))
          ser = Equal.sym(Bool, U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()), False{}, er)
          %eq : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Authenticating{_, av, resynced, asupi}, last_dl}, _, S.Authenticating{_, av, resynced, asupi}, U32.is_lt(S.Guard.retries(_), Gmm.Gmm.max_retries())))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}
          %ser : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Authenticating{g, av, resynced, asupi}, last_dl}, g, S.Authenticating{g, av, resynced, asupi}, _))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}
          Lv.release_get(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Authenticating{g, av, resynced, asupi}, last_dl}, N.Ngap.nas_cause(G.CauseNas.unspecified()))
        case S.SecurityMode{+guard, ctx, k_amf}:
          eq = Equal.sym(S.Guard, guard, g, PT.Some.inj(S.Guard, guard, g, eg))
          ser = Equal.sym(Bool, U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()), False{}, er)
          %eq : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.SecurityMode{_, ctx, k_amf}, last_dl}, _, S.SecurityMode{_, ctx, k_amf}, U32.is_lt(S.Guard.retries(_), Gmm.Gmm.max_retries())))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}
          %ser : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.SecurityMode{g, ctx, k_amf}, last_dl}, g, S.SecurityMode{g, ctx, k_amf}, _))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}
          Lv.release_get(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.SecurityMode{g, ctx, k_amf}, last_dl}, N.Ngap.nas_cause(G.CauseNas.unspecified()))
        case S.ContextSetup{+guard, ctx, response, complete}:
          eq = Equal.sym(S.Guard, guard, g, PT.Some.inj(S.Guard, guard, g, eg))
          ser = Equal.sym(Bool, U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()), False{}, er)
          %eq : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.ContextSetup{_, ctx, response, complete}, last_dl}, _, S.ContextSetup{_, ctx, response, complete}, U32.is_lt(S.Guard.retries(_), Gmm.Gmm.max_retries())))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}
          %ser : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.retry_if(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.ContextSetup{g, ctx, response, complete}, last_dl}, g, S.ContextSetup{g, ctx, response, complete}, _))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}
          Lv.release_get(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.ContextSetup{g, ctx, response, complete}, last_dl}, N.Ngap.nas_cause(G.CauseNas.unspecified()))
        case S.Registered{ctx}:
          Empty.absurd({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Registered{ctx}, last_dl}, S.Registered{ctx}))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}, P.Refute.none_some(S.Guard, g, eg))
        case S.Releasing{+guard}:
          eq = Equal.sym(S.Guard, guard, g, PT.Some.inj(S.Guard, guard, g, eg))
          Empty.absurd({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{guard}, last_dl}, S.Releasing{guard}))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{S.State.next_timer(st), 0}}, last_dl}} : Maybe<&2, S.Ue>}, np((%eq : {S.Releasing{_} == S.Releasing{g} : S.Phase}; {==})))

def Lv.exp1(+st: S.State, +entropy: B.Bytes(), +timer: U32, +k: U32, +u: S.Ue, +g: S.Guard, +et: {S.Ues.by_timer(timer, S.State.ues(st)) == Some{(k, u)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>}, +eg: {S.Ue.guard(u) == Some{g} : Maybe<&2, S.Guard>}, np: {S.Ue.phase(u) == S.Releasing{g} : S.Phase} -> Empty, +er: {U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()) == False{} : Bool}) -> {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.TimerFired{timer}, entropy)))) == Some{S.Ue.with_phase(u, S.Releasing{S.Guard{S.State.next_timer(st), 0}})} : Maybe<&2, S.Ue>}:
  set = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>, S.Ues.by_timer(timer, S.State.ues(st)), Some{(k, u)}, et)
  %set : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, timer, _))))) == Some{S.Ue.with_phase(u, S.Releasing{S.Guard{S.State.next_timer(st), 0}})} : Maybe<&2, S.Ue>}
  Lv.retried(st, k, u, g, eg, np, er)

# The release's guard fires: the context and its sessions are forgotten, the sessions deleted at eUPF.
def Lv.exp2(+st: S.State, +entropy: B.Bytes(), +timer: U32, +k: U32, +u: S.Ue, +g: S.Guard, +et: {S.Ues.by_timer(timer, S.State.ues(st)) == Some{(k, u)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>}, +ep: {S.Ue.phase(u) == S.Releasing{g} : S.Phase}) -> {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.TimerFired{timer}, entropy)))) == None{} : Maybe<&2, S.Ue>} & ({S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{timer}, entropy)))) == [] : Tb.Table(S.Session)} & {K.Kernel.actions(K.Kernel.step(st, F.TimerFired{timer}, entropy)) == List.append(&2, N.Act, Up.N4.deletions(S.Sessions.of_ue(k, S.State.sessions(st)), S.State.pfcp_seq(st)), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]) : List<&2, N.Act>}):
  +n = Up.N4.deletion_count(S.Sessions.of_ue(k, S.State.sessions(st)))
  set = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>, S.Ues.by_timer(timer, S.State.ues(st)), Some{(k, u)}, et)
  %set : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, timer, _))))) == None{} : Maybe<&2, S.Ue>} & ({S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, timer, _))))) == [] : Tb.Table(S.Session)} & {K.Kernel.actions(N.Step.of(st, K.Kernel.fired_ue(st, timer, _))) == List.append(&2, N.Act, Up.N4.deletions(S.Sessions.of_ue(k, S.State.sessions(st)), S.State.pfcp_seq(st)), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]) : List<&2, N.Act>})
  sep = Equal.sym(S.Phase, S.Ue.phase(u), S.Releasing{g}, ep)
  %sep : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _))))) == None{} : Maybe<&2, S.Ue>} & ({S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _))))) == [] : Tb.Table(S.Session)} & {K.Kernel.actions(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _))) == List.append(&2, N.Act, Up.N4.deletions(S.Sessions.of_ue(k, S.State.sessions(st)), S.State.pfcp_seq(st)), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]) : List<&2, N.Act>})
  (PK.Tx.forget_ue(k, n, st), (PK.Tx.forget_sessions(k, n, st), {==}))

def L.amf.guard.expires(st, entropy, timer, k, u, g, et, eg):
  (np => er => Lv.exp1(st, entropy, timer, k, u, g, et, eg, np, er), ep => Lv.exp2(st, entropy, timer, k, u, g, et, ep))

# What a step may do
# ------------------
# A key is live in a state when a context holds it, it is the one a new context
# takes, or a session belongs to it. A UE procedure builds its actions only
# from live keys and never answers NG Setup, and every session it puts belongs
# to a context, with an Accept within the packet-filter bound if it is being
# created. A UE that is gone holds none of these, so nothing is built from it
# (amf.release.forgets_ue), no session outlives its context
# (amf.sessions.owned), and no session holds an Accept beyond the bound
# (smf.packet_filters.capacity_reject).

def Lv.owner(+x: U32, ss: Tb.Table(S.Session)) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case (k, t) <> more:
      Bool.or(U32.is_eq(S.Session.ue(t), x), Lv.owner(x, more))

def Lv.live(+st: S.State, +x: U32) -> Bool:
  Bool.or(Tb.Table.has(S.Ue, x, S.State.ues(st)), Bool.or(U32.is_eq(x, S.State.next_ue(st)), Lv.owner(x, S.State.sessions(st))))

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

def Lv.free(tx: S.Tx) -> Bool:
  match tx:
    case S.PutSession{key, s}:
      False{}
    case S.Revar{key, v}:
      Gsm.Gsm.phase_bounded(S.SVar.phase(v))
    case S.Both{a, b}:
      Bool.and(Lv.free(a), Lv.free(b))
    case _:
      True{}

def Lv.homed(+tx: S.Tx, +ues: Tb.Table(S.Ue)) -> Bool:
  match tx:
    case S.PutSession{key, +s}:
      Bool.and(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Gsm.Gsm.phase_bounded(S.Session.phase(s)))
    case S.Revar{key, v}:
      Gsm.Gsm.phase_bounded(S.SVar.phase(v))
    case S.Both{+a, b}:
      Bool.and(Lv.homed(a, ues), Lv.homed(b, PT.Tk.ues(a, ues)))
    case _:
      True{}

def Lv.as(o: N.GOut()) -> List<&2, N.Act>:
  match o:
    case (tx, acts):
      acts

# An outcome puts no session (okf), or only sessions of contexts (ok); either
# way every session it creates or changes keeps the packet-filter bound.
def Lv.okf(+st: S.State, +o: N.GOut()) -> Bool:
  Bool.and(Lv.acts(st, Lv.as(o)), Lv.free(PT.Tk.tx(o)))

def Lv.ok(+st: S.State, +o: N.GOut()) -> Bool:
  Bool.and(Lv.acts(st, Lv.as(o)), Lv.homed(PT.Tk.tx(o), S.State.ues(st)))

# Composing outcomes
# ------------------

def Lv.free_homed(+tx: S.Tx, +ues: Tb.Table(S.Ue), +e: {Lv.free(tx) == True{} : Bool}) -> {Lv.homed(tx, ues) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      {==}
    case S.Put{key, ue}:
      {==}
    case S.Rephase{key, phase}:
      {==}
    case S.Del{key}:
      {==}
    case S.PutSession{key, +s}:
      Empty.absurd({Bool.and(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Gsm.Gsm.phase_bounded(S.Session.phase(s))) == True{} : Bool}, P.Refute.bool(e))
    case S.Revar{key, v}:
      e
    case S.DelSession{key}:
      {==}
    case S.Subs{subs}:
      {==}
    case S.SetLink{link}:
      {==}
    case S.BumpUe{}:
      {==}
    case S.BumpTimer{}:
      {==}
    case S.BumpSeq{n}:
      {==}
    case S.Both{+a, +b}:
      P.Bool.and_intro(Lv.homed(a, ues), Lv.homed(b, PT.Tk.ues(a, ues)), Lv.free_homed(a, ues, P.Bool.and_true_l(Lv.free(a), Lv.free(b), e)), Lv.free_homed(b, PT.Tk.ues(a, ues), P.Bool.and_true_r(Lv.free(a), Lv.free(b), e)))

def Lv.ok_of(+st: S.State, +o: N.GOut(), +h: {Lv.okf(st, o) == True{} : Bool}) -> {Lv.ok(st, o) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      P.Bool.and_intro(Lv.acts(st, acts), Lv.homed(tx, S.State.ues(st)), P.Bool.and_true_l(Lv.acts(st, acts), Lv.free(tx), h), Lv.free_homed(tx, S.State.ues(st), P.Bool.and_true_r(Lv.acts(st, acts), Lv.free(tx), h)))

def Lv.cons(+st: S.State, +a: N.Act, +more: List<&2, N.Act>, +ha: {Lv.act(st, a) == True{} : Bool}, +hm: {Lv.acts(st, more) == True{} : Bool}) -> {Lv.acts(st, a <> more) == True{} : Bool}:
  P.Bool.and_intro(Lv.act(st, a), Lv.acts(st, more), ha, hm)

def Lv.append(+st: S.State, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {Lv.acts(st, xs) == True{} : Bool}, +hy: {Lv.acts(st, ys) == True{} : Bool}) -> {Lv.acts(st, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      Lv.cons(st, a, List.append(&2, N.Act, more, ys), P.Bool.and_true_l(Lv.act(st, a), Lv.acts(st, more), hx), Lv.append(st, more, ys, P.Bool.and_true_r(Lv.act(st, a), Lv.acts(st, more), hx), hy))

def Lv.leaf(+st: S.State, +tx: S.Tx, +as: List<&2, N.Act>, +ha: {Lv.acts(st, as) == True{} : Bool}, +hf: {Lv.free(tx) == True{} : Bool}) -> {Lv.okf(st, (tx, as)) == True{} : Bool}:
  P.Bool.and_intro(Lv.acts(st, as), Lv.free(tx), ha, hf)

def Lv.prepend(+st: S.State, +a: N.Act, +o: N.GOut(), +ha: {Lv.act(st, a) == True{} : Bool}, +h: {Lv.okf(st, o) == True{} : Bool}) -> {Lv.okf(st, N.Out.prepend(a, o)) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      Lv.leaf(st, tx, a <> acts, Lv.cons(st, a, acts, ha, P.Bool.and_true_l(Lv.acts(st, acts), Lv.free(tx), h)), P.Bool.and_true_r(Lv.acts(st, acts), Lv.free(tx), h))

def Lv.also(+st: S.State, +o: N.GOut(), +more: List<&2, N.Act>, +h: {Lv.okf(st, o) == True{} : Bool}, +hm: {Lv.acts(st, more) == True{} : Bool}) -> {Lv.okf(st, N.Out.also(o, more)) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      Lv.leaf(st, tx, List.append(&2, N.Act, acts, more), Lv.append(st, acts, more, P.Bool.and_true_l(Lv.acts(st, acts), Lv.free(tx), h), hm), P.Bool.and_true_r(Lv.acts(st, acts), Lv.free(tx), h))

def Lv.join(+st: S.State, +a: N.GOut(), +b: N.GOut(), +ha: {Lv.okf(st, a) == True{} : Bool}, +hb: {Lv.okf(st, b) == True{} : Bool}) -> {Lv.okf(st, N.Out.join(a, b)) == True{} : Bool}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          Lv.leaf(st, S.Both{ta, tb}, List.append(&2, N.Act, aa, ab), Lv.append(st, aa, ab, P.Bool.and_true_l(Lv.acts(st, aa), Lv.free(ta), ha), P.Bool.and_true_l(Lv.acts(st, ab), Lv.free(tb), hb)), P.Bool.and_intro(Lv.free(ta), Lv.free(tb), P.Bool.and_true_r(Lv.acts(st, aa), Lv.free(ta), ha), P.Bool.and_true_r(Lv.acts(st, ab), Lv.free(tb), hb)))

def Lv.cancel(+st: S.State, +g: Maybe<&2, S.Guard>) -> {Lv.acts(st, N.Guard.cancel(g)) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{guard}:
      {==}

# Live keys
# ---------

def Lv.or_l(+a: Bool, +b: Bool, +e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, P.Refute.bool(e))

def Lv.or_r(+a: Bool, +b: Bool, +e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def Lv.has_live(+st: S.State, +x: U32, +e: {Tb.Table.has(S.Ue, x, S.State.ues(st)) == True{} : Bool}) -> {Lv.live(st, x) == True{} : Bool}:
  Lv.or_l(Tb.Table.has(S.Ue, x, S.State.ues(st)), Bool.or(U32.is_eq(x, S.State.next_ue(st)), Lv.owner(x, S.State.sessions(st))), e)

def Lv.owner_live(+st: S.State, +x: U32, +e: {Lv.owner(x, S.State.sessions(st)) == True{} : Bool}) -> {Lv.live(st, x) == True{} : Bool}:
  Lv.or_r(Tb.Table.has(S.Ue, x, S.State.ues(st)), Bool.or(U32.is_eq(x, S.State.next_ue(st)), Lv.owner(x, S.State.sessions(st))), Lv.or_r(U32.is_eq(x, S.State.next_ue(st)), Lv.owner(x, S.State.sessions(st)), e))

def Lv.next_live(+st: S.State) -> {Lv.live(st, S.State.next_ue(st)) == True{} : Bool}:
  Lv.or_r(Tb.Table.has(S.Ue, S.State.next_ue(st), S.State.ues(st)), Bool.or(U32.is_eq(S.State.next_ue(st), S.State.next_ue(st)), Lv.owner(S.State.next_ue(st), S.State.sessions(st))), Lv.or_l(U32.is_eq(S.State.next_ue(st), S.State.next_ue(st)), Lv.owner(S.State.next_ue(st), S.State.sessions(st)), P.U32.is_eq_refl(S.State.next_ue(st))))

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
  Lv.or_r(U32.is_eq(S.Session.ue(t), x), Lv.owner(x, more), e)

def Lv.owner_head(+k: U32, +t: S.Session, +more: Tb.Table(S.Session)) -> {Lv.owner(S.Session.ue(t), (k, t) <> more) == True{} : Bool}:
  Lv.or_l(U32.is_eq(S.Session.ue(t), S.Session.ue(t)), Lv.owner(S.Session.ue(t), more), P.U32.is_eq_refl(S.Session.ue(t)))

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

def Lv.known(+rows: Tb.Table(S.Session), +ss: Tb.Table(S.Session), +e: {Lv.srows(rows, ss) == True{} : Bool}) -> {Lv.srows(Up.N4.known_rows(rows), ss) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Lv.srows_keep(key, t, Up.N4.known_rows(more), Up.N4.known(t), ss, P.Bool.and_true_l(Lv.owner(S.Session.ue(t), ss), Lv.srows(more, ss), e), Lv.known(more, ss, P.Bool.and_true_r(Lv.owner(S.Session.ue(t), ss), Lv.srows(more, ss), e)))

def Lv.number(+st: S.State, +rows: Tb.Table(S.Session), +seq: U32, +e: {Lv.srows(rows, S.State.sessions(st)) == True{} : Bool}) -> {Lv.acts(st, Up.N4.number(rows, seq)) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Lv.cons(st, N.Pfcp{Some{S.Session.ue(t)}, Up.N4.delete(S.Session.up_seid(t), seq)}, Up.N4.number(more, U32.add(seq, 1)), Lv.owner_live(st, S.Session.ue(t), P.Bool.and_true_l(Lv.owner(S.Session.ue(t), S.State.sessions(st)), Lv.srows(more, S.State.sessions(st)), e)), Lv.number(st, more, U32.add(seq, 1), P.Bool.and_true_r(Lv.owner(S.Session.ue(t), S.State.sessions(st)), Lv.srows(more, S.State.sessions(st)), e)))

# Session Deletions at eUPF are built from sessions of the state.
def Lv.dels(+st: S.State, +rows: Tb.Table(S.Session), +seq: U32, +e: {Lv.srows(rows, S.State.sessions(st)) == True{} : Bool}) -> {Lv.acts(st, Up.N4.deletions(rows, seq)) == True{} : Bool}:
  Lv.number(st, Up.N4.known_rows(rows), seq, Lv.known(rows, S.State.sessions(st), e))

def Lv.dels_free(+vs: Tb.Table(S.Session)) -> {Lv.free(Gsm.Gsm.dels(vs)) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case (k, t) <> +more:
      Lv.dels_free(more)

# Sessions forgotten
def Lw.gsm_forget(+st: S.State, +vs: Tb.Table(S.Session), +seq: U32, +e: {Lv.srows(vs, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.forget(vs, seq)) == True{} : Bool}:
  Lv.leaf(st, S.Both{Gsm.Gsm.dels(vs), S.BumpSeq{Up.N4.deletion_count(vs)}}, Up.N4.deletions(vs, seq), Lv.dels(st, vs, seq, e), P.Bool.and_intro(Lv.free(Gsm.Gsm.dels(vs)), True{}, Lv.dels_free(vs), {==}))

# A row a session search finds is a session of the table.
def Lv.found(m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +ss: Tb.Table(S.Session)) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{(k, t)}:
      Lv.owner(S.Session.ue(t), ss)

def Lv.found_cons(+m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +k: U32, +t: S.Session, +more: Tb.Table(S.Session), +e: {Lv.found(m, more) == True{} : Bool}) -> {Lv.found(m, (k, t) <> more) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+k1, +t1)}:
      Lv.owner_cons(S.Session.ue(t1), k, t, more, e)

def Lv.pick(+key: U32, +t: S.Session, +later: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +hit: Bool, +more: Tb.Table(S.Session), +e: {Lv.found(later, more) == True{} : Bool}) -> {Lv.found(S.Sessions.pick(key, t, later, hit), (key, t) <> more) == True{} : Bool}:
  match hit:
    case True{}:
      Lv.owner_head(key, t, more)
    case False{}:
      Lv.found_cons(later, key, t, more, e)

def Lv.by_seq(+seq: U32, +ss: Tb.Table(S.Session)) -> {Lv.found(S.Sessions.by_seq(seq, ss), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Lv.pick(key, t, S.Sessions.by_seq(seq, more), U32.is_eq(S.Session.seq(t), seq), more, Lv.by_seq(seq, more))

def Lv.by_timer(+timer: U32, +ss: Tb.Table(S.Session)) -> {Lv.found(S.Sessions.by_timer(timer, ss), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Lv.pick(key, t, S.Sessions.by_timer(timer, more), S.Ues.timer_is(S.SPhase.guard(S.Session.phase(t)), timer), more, Lv.by_timer(timer, more))

def Lv.by_psi(+ue: U32, +psi: U32, +ss: Tb.Table(S.Session)) -> {Lv.found(S.Sessions.by_psi(ue, psi, ss), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Lv.pick(key, t, S.Sessions.by_psi(ue, psi, more), Bool.and(U32.is_eq(S.Session.ue(t), ue), U32.is_eq(S.Session.psi(t), psi)), more, Lv.by_psi(ue, psi, more))

# The context a guard search finds holds its key.
def Lv.ufound(m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>, +ues: Tb.Table(S.Ue)) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{(k, u)}:
      Tb.Table.has(S.Ue, k, ues)

def Lv.ufound_cons(+m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>, +k: U32, +u: S.Ue, +more: Tb.Table(S.Ue), +e: {Lv.ufound(m, more) == True{} : Bool}) -> {Lv.ufound(m, (k, u) <> more) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+k1, u1)}:
      Lv.has_cons(k1, k, u, more, e)

def Lv.ue_pick(+key: U32, +u: S.Ue, +later: Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>, +hit: Bool, +more: Tb.Table(S.Ue), +e: {Lv.ufound(later, more) == True{} : Bool}) -> {Lv.ufound(S.Ues.pick_timer(key, u, later, hit), (key, u) <> more) == True{} : Bool}:
  match hit:
    case True{}:
      Lv.has_head(key, u, more)
    case False{}:
      Lv.ufound_cons(later, key, u, more, e)

def Lv.ue_by_timer(+timer: U32, +ues: Tb.Table(S.Ue)) -> {Lv.ufound(S.Ues.by_timer(timer, ues), ues) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+key, +u) <> +more:
      Lv.ue_pick(key, u, S.Ues.by_timer(timer, more), S.Ues.timer_is(S.Ue.guard(u), timer), more, Lv.ue_by_timer(timer, more))

# Contexts put and released
# -------------------------

def Lw.evict(+st: S.State, +vs: Tb.Table(S.Ue), +q: U32, +e: {Lv.keys_in(vs, S.State.ues(st)) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.evict(vs, S.State.sessions(st), q)) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case (+key, +v) <> +more:
      +gone = S.Sessions.of_ue(key, S.State.sessions(st))
      +ek = Lv.has_live(st, key, P.Bool.and_true_l(Tb.Table.has(S.Ue, key, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e))
      +rel : N.Act = N.Release{S.Ue.assoc(v), S.Ue.stream(v), key, S.Ue.ran_id(v), N.Ngap.nas_cause(G.CauseNas.deregister())}
      Lv.join(st, N.Out.prepend(rel, (S.BumpSeq{Up.N4.deletion_count(gone)}, Up.N4.deletions(gone, q))), Gmm.Gmm.evict(more, S.State.sessions(st), U32.add(q, Up.N4.deletion_count(gone))), Lv.prepend(st, rel, (S.BumpSeq{Up.N4.deletion_count(gone)}, Up.N4.deletions(gone, q)), ek, Lv.leaf(st, S.BumpSeq{Up.N4.deletion_count(gone)}, Up.N4.deletions(gone, q), Lv.dels(st, gone, q, Lv.srows_sift(S.SOf{key}, S.State.sessions(st))), {==})), Lw.evict(st, more, U32.add(q, Up.N4.deletion_count(gone)), P.Bool.and_true_r(Tb.Table.has(S.Ue, key, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e)))

def Lw.place(+st: S.State, +key: U32, +ue: S.Ue) -> {Lv.okf(st, Gmm.Gmm.place(st, key, ue)) == True{} : Bool}:
  Lv.join(st, (S.Put{key, ue}, []), Gmm.Gmm.evict(S.Ues.evicted(key, ue, S.State.ues(st)), S.State.sessions(st), S.State.pfcp_seq(st)), {==}, Lw.evict(st, S.Ues.evicted(key, ue, S.State.ues(st)), S.State.pfcp_seq(st), Lv.keys_sift(S.Victims{key, ue}, S.State.ues(st))))

def Lw.forget(+st: S.State, +key: U32) -> {Lv.okf(st, Gmm.Gmm.forget(st, key)) == True{} : Bool}:
  +gone = S.Sessions.of_ue(key, S.State.sessions(st))
  Lv.leaf(st, S.Both{S.Del{key}, S.BumpSeq{Up.N4.deletion_count(gone)}}, Up.N4.deletions(gone, S.State.pfcp_seq(st)), Lv.dels(st, gone, S.State.pfcp_seq(st), Lv.srows_sift(S.SOf{key}, S.State.sessions(st))), {==})

# 5GSM
# ----

def Lw.out_dl(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +plain: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, N.Out.dl(key, ue, ctx, plain)) == True{} : Bool}:
  +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.Ciphered{}, plain)
  +x : N.Act = N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), Sec.Nas.Protected.msg(p)}
  Lv.leaf(st, S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))}, [x], Lv.cons(st, x, [], ek, {==}), {==})

def Lw.to_ue_ctx(+st: S.State, +key: U32, +ue: S.Ue, +psi: U32, +sm: B.Bytes(), +ctx: Maybe<&2, Sec.Nas.Ctx>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.to_ue_ctx(key, ue, psi, sm, ctx)) == True{} : Bool}:
  match ctx:
    case None{}:
      {==}
    case Some{+c}:
      Lw.out_dl(st, key, ue, c, Gsm.Gsm.dl_transport(psi, sm), ek)

def Lw.to_ue_m(+st: S.State, +key: U32, +psi: U32, +sm: B.Bytes(), +m: Maybe<&2, S.Ue>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.to_ue_m(key, psi, sm, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.to_ue_ctx(st, key, ue, psi, sm, S.Phase.ctx(S.Ue.phase(ue)), ek)

def Lw.one(+st: S.State, +skey: U32, +s: S.Session, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.srows([(skey, s)], S.State.sessions(st)) == True{} : Bool}:
  P.Bool.and_intro(Lv.owner(S.Session.ue(s), S.State.sessions(st)), True{}, es, {==})

def Lw.abort_m(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +cause: U32, +seq: U32, +m: Maybe<&2, S.Ue>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.abort_m(skey, s, pti, cause, seq, m)) == True{} : Bool}:
  +sm = Gsm.Gsm.reject(S.Session.psi(s), pti, cause)
  +more = N.Guard.cancel(S.SPhase.guard(S.Session.phase(s)))
  Lv.join(st, Gsm.Gsm.to_ue_m(S.Session.ue(s), S.Session.psi(s), sm, m), N.Out.also(Gsm.Gsm.forget([(skey, s)], seq), more), Lw.to_ue_m(st, S.Session.ue(s), S.Session.psi(s), sm, m, Lv.owner_live(st, S.Session.ue(s), es)), Lv.also(st, Gsm.Gsm.forget([(skey, s)], seq), more, Lw.gsm_forget(st, [(skey, s)], seq, Lw.one(st, skey, s, es)), Lv.cancel(st, S.SPhase.guard(S.Session.phase(s)))))

def Lw.abort(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +cause: U32, +seq: U32, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.abort(st, skey, s, pti, cause, seq)) == True{} : Bool}:
  Lw.abort_m(st, skey, s, pti, cause, seq, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), es)


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
def Lw.create(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, +ip: U32, +entropy: B.Bytes(), +v4v6: Bool, +dns: Bool, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.create(st, key, ue, ctx, cfg, psi, pti, ip, entropy, v4v6, dns)) == True{} : Bool}:
  +timer = S.State.next_timer(st)
  +seq = S.State.pfcp_seq(st)
  +teid = Gsm.Ip.teid(entropy)
  +ph = S.Phase.with_ctx(S.Ue.phase(ue), ctx)
  +s : S.Session = S.Session{S.SId{key, psi, ip, teid}, S.SVar{[], seq, S.Creating{S.Guard{timer, 0}, pti, Gsm.Gsm.accept(cfg, psi, pti, ip, dns, v4v6)}}}
  +x : N.Act = N.Pfcp{Some{key}, Up.N4.establish(cfg, Gsm.Ip.seid(entropy), ip, teid, seq)}
  +y : N.Act = N.TimerStart{Some{key}, timer, Up.N4.t1_ms()}
  +vs = S.Sessions.evicted(Gsm.Ip.seid(entropy), s, S.State.sessions(st))
  +rep = S.Ues.rephase(key, ph, S.State.ues(st))
  +ek = Lv.has_live(st, key, eh)
  hr = Equal.sym(Bool, Tb.Table.has(S.Ue, key, rep), Tb.Table.has(S.Ue, key, S.State.ues(st)), Lv.has_rephase(key, key, ph, S.State.ues(st)))
  +ha = Lv.append(st, [x, y], Up.N4.deletions(vs, U32.add(seq, 1)), Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), Lv.dels(st, vs, U32.add(seq, 1), Lv.srows_sift(S.SVictims{Gsm.Ip.seid(entropy), s}, S.State.sessions(st))))
  +hp = P.Bool.and_intro(Tb.Table.has(S.Ue, key, rep), Gsm.Gsm.phase_bounded(S.Session.phase(s)), (%hr : {_ == True{} : Bool}; eh), {==})
  +hb = P.Bool.and_intro(Bool.and(Tb.Table.has(S.Ue, key, rep), Gsm.Gsm.phase_bounded(S.Session.phase(s))), Bool.and(Lv.homed(Gsm.Gsm.dels(vs), rep), True{}), hp, P.Bool.and_intro(Lv.homed(Gsm.Gsm.dels(vs), rep), True{}, Lv.free_homed(Gsm.Gsm.dels(vs), rep, Lv.dels_free(vs)), {==}))
  P.Bool.and_intro(Lv.acts(st, List.append(&2, N.Act, [x, y], Up.N4.deletions(vs, U32.add(seq, 1)))), Bool.and(Bool.and(Tb.Table.has(S.Ue, key, rep), Gsm.Gsm.phase_bounded(S.Session.phase(s))), Bool.and(Lv.homed(Gsm.Gsm.dels(vs), rep), True{})), ha, hb)

def Lw.checked(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, +entropy: B.Bytes(), +c: Gsm.Check, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.checked(st, key, ue, ctx, cfg, psi, pti, entropy, c)) == True{} : Bool}:
  match c:
    case Gsm.Refuse{+cause}:
      Lv.ok_of(st, Gsm.Gsm.dl(key, ue, ctx, psi, Gsm.Gsm.reject(psi, pti, cause)), Lw.out_dl(st, key, ue, ctx, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause)), Lv.has_live(st, key, eh)))
    case Gsm.Go{+v4v6, +dns, +ip}:
      Lw.create(st, key, ue, ctx, cfg, psi, pti, ip, entropy, v4v6, dns, eh)

def Lw.gsm_with_cfg(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +psi: U32, +pti: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +cfg: Maybe<&2, S.Cfg>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.with_cfg(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy, cfg)) == True{} : Bool}:
  match cfg:
    case None{}:
      {==}
    case Some{+c}:
      Lw.checked(st, key, ue, ctx, c, psi, pti, entropy, Gsm.Gsm.validate(c, psi, mm_opts, sm_opts, Up.N4.up(st), S.State.sessions(st)), eh)

def Lw.establish(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +psi: U32, +pti: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.establish(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy)) == True{} : Bool}:
  Lw.gsm_with_cfg(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy, S.State.config(st), eh)

def Lw.message(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +mm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Sm.Sm>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.message(st, key, ue, ctx, mm_opts, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{Sm.Sm{+psi, +pti, mt, fields, +opts}}:
      match mt:
        case Sm.EstablishmentRequest{}:
          Lw.establish(st, key, ue, ctx, psi, pti, mm_opts, opts, entropy, eh)
        case Sm.EstablishmentAccept{}:
          {==}
        case Sm.EstablishmentReject{}:
          {==}
        case Sm.ModificationRequest{}:
          Lv.ok_of(st, Gsm.Gsm.dl(key, ue, ctx, psi, Gsm.Gsm.modification_reject(psi, pti)), Lw.out_dl(st, key, ue, ctx, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.modification_reject(psi, pti)), Lv.has_live(st, key, eh)))
        case Sm.ModificationReject{}:
          {==}
        case Sm.ReleaseRequest{}:
          {==}
        case Sm.ReleaseCommand{}:
          {==}
        case Sm.ReleaseComplete{}:
          {==}
        case Sm.SmStatus{}:
          {==}

def Lw.n1(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +mm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +container: B.Bytes(), +n1: Bool, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.n1(st, key, ue, ctx, mm_opts, entropy, container, n1)) == True{} : Bool}:
  match n1:
    case True{}:
      Lw.message(st, key, ue, ctx, mm_opts, entropy, Sm.Sm.read(container), eh)
    case False{}:
      {==}

def Lw.ul_transport(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +entropy: B.Bytes(), +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.ul_transport(st, key, ue, ctx, fields, opts, entropy)) == True{} : Bool}:
  Lw.n1(st, key, ue, ctx, opts, entropy, I.Fields.lve2(fields), U32.is_eq(I.Fields.byte1(fields), 1), eh)


# eUPF's answers
# --------------

def Lv.owner_var(+s: S.Session, +v: S.SVar, +ss: Tb.Table(S.Session), +es: {Lv.owner(S.Session.ue(s), ss) == True{} : Bool}) -> {Lv.owner(S.Session.ue(S.Session.with_var(s, v)), ss) == True{} : Bool}:
  match s:
    case S.Session{id, var}:
      es

def Lw.setup_gone(+st: S.State, +skey: U32, +s: S.Session, +up_seid: B.Bytes(), +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.forget([(skey, S.Session.with_var(s, S.SVar{up_seid, S.Session.seq(s), S.Active{}}))], S.State.pfcp_seq(st))) == True{} : Bool}:
  +s2 = S.Session.with_var(s, S.SVar{up_seid, S.Session.seq(s), S.Active{}})
  Lw.gsm_forget(st, [(skey, s2)], S.State.pfcp_seq(st), Lw.one(st, skey, s2, Lv.owner_var(s, S.SVar{up_seid, S.Session.seq(s), S.Active{}}, S.State.sessions(st), es)))

def Lw.setup_ue(+st: S.State, +skey: U32, +s: S.Session, +guard: S.Guard, +pti: U32, +accept: Sm.Sm, +up_seid: B.Bytes(), +ue: S.Ue, +ctx: Maybe<&2, Sec.Nas.Ctx>, +cfg: Maybe<&2, S.Cfg>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.setup_ue(st, skey, s, guard, pti, accept, up_seid, ue, ctx, cfg)) == True{} : Bool}:
  match ctx cfg:
    case Some{+c} Some{+cf}:
      +p : Sec.Nas.Protected = Sec.Nas.protect(c, Sec.Ciphered{}, Gsm.Gsm.dl_transport(S.Session.psi(s), Sm.Sm.write(accept)))
      +x : N.Act = N.PduSetup{S.Ue.assoc(ue), S.Ue.stream(ue), S.Session.ue(s), S.Ue.ran_id(ue), S.Session.psi(s), S.Cfg.sst(cf), Sec.Nas.Protected.msg(p), Gsm.Gsm.transfer(cf, S.Session.teid(s))}
      +y : N.Act = N.TimerStart{Some{S.Session.ue(s)}, S.Guard.timer(guard), Up.N4.t1_ms()}
      +ek = Lv.owner_live(st, S.Session.ue(s), es)
      Lv.leaf(st, S.Both{S.Rephase{S.Session.ue(s), S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))}, S.Revar{skey, S.SVar{up_seid, S.Session.seq(s), S.Setting{S.Guard{S.Guard.timer(guard), 0}, pti}}}}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), {==})
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
  +ur = S.Ue.with_phase(ue, S.Releasing{S.Guard{S.State.next_timer(st), 0}})
  +rel : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}
  +ts : N.Act = N.TimerStart{Some{key}, S.State.next_timer(st), Gmm.Gmm.guard_ms()}
  +as = List.append(&2, N.Act, N.Guard.cancel(S.Ue.guard(ue)), [ts])
  Lv.prepend(st, rel, N.Out.join(Gmm.Gmm.place(st, key, ur), (S.BumpTimer{}, as)), ek, Lv.join(st, Gmm.Gmm.place(st, key, ur), (S.BumpTimer{}, as), Lw.place(st, key, ur), Lv.leaf(st, S.BumpTimer{}, as, Lv.append(st, N.Guard.cancel(S.Ue.guard(ue)), [ts], Lv.cancel(st, S.Ue.guard(ue)), Lv.cons(st, ts, [], ek, {==})), {==})))


def Lw.reject(+st: S.State, +key: U32, +ue: S.Ue, +cause: U32, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.reject(st, key, ue, cause)) == True{} : Bool}:
  Lv.prepend(st, Gmm.Gmm.dl(key, ue, Gmm.Gmm.registration_reject(cause)), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified())), ek, Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek))

def Lw.auth_reject(+st: S.State, +key: U32, +ue: S.Ue, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.auth_reject(st, key, ue)) == True{} : Bool}:
  Lv.prepend(st, Gmm.Gmm.dl(key, ue, Gmm.Gmm.authentication_reject()), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure())), ek, Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure()), ek))


def Lw.identity_ask(+st: S.State, +key: U32, +ue: S.Ue, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.identity_ask(st, key, ue)) == True{} : Bool}:
  +timer = S.State.next_timer(st)
  +nas = Gmm.Gmm.identity_request()
  +ue2 = S.Ue.with_dl(ue, S.Identifying{S.Guard{timer, 0}}, nas)
  +x : N.Act = Gmm.Gmm.dl(key, ue2, nas)
  +y : N.Act = N.TimerStart{Some{key}, timer, Gmm.Gmm.guard_ms()}
  Lv.join(st, Gmm.Gmm.place(st, key, ue2), (S.BumpTimer{}, [x, y]), Lw.place(st, key, ue2), Lv.leaf(st, S.BumpTimer{}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), {==}))


def Lw.challenge(+st: S.State, +key: U32, +ue: S.Ue, +sub: Au.Subscriber, +snn: B.Bytes(), +entropy: B.Bytes(), +resynced: Bool, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.challenge(st, key, ue, sub, snn, entropy, resynced)) == True{} : Bool}:
  +timer = S.State.next_timer(st)
  +sub2 = Au.Subscriber.with_sqn(sub, Au.Sqn.next(Au.Subscriber.sqn(sub)))
  +av = Au.Av.make(sub2, snn, List.take(&2, U32, entropy, 16n))
  +nas = Gmm.Gmm.auth_request(0, av)
  +ue2 = S.Ue.with_dl(ue, S.Authenticating{S.Guard{timer, 0}, av, resynced, Au.Subscriber.supi(sub2)}, nas)
  +x : N.Act = Gmm.Gmm.dl(key, ue2, nas)
  +y : N.Act = N.TimerStart{Some{key}, timer, Gmm.Gmm.guard_ms()}
  +as = List.append(&2, N.Act, N.Guard.cancel(S.Ue.guard(ue)), [x, y])
  +tx : S.Tx = S.Both{S.Subs{Au.Subscribers.update(sub2, S.State.subs(st))}, S.BumpTimer{}}
  Lv.join(st, Gmm.Gmm.place(st, key, ue2), (tx, as), Lw.place(st, key, ue2), Lv.leaf(st, tx, as, Lv.append(st, N.Guard.cancel(S.Ue.guard(ue)), [x, y], Lv.cancel(st, S.Ue.guard(ue)), Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==}))), {==}))


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

def Lw.register(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +r: Mi.MobileId.Res()) -> {Lv.okf(st, Gmm.Gmm.register(st, assoc, stream, entropy, ran, nas, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+id}:
      +fresh : S.Ue = S.Ue{assoc, ran, stream, None{}, None{}, nas, 0, S.Created{}, []}
      Lv.join(st, (S.BumpUe{}, []), Gmm.Gmm.proceed(st, S.State.next_ue(st), fresh, Gmm.Gmm.start_of(id), entropy), {==}, Lw.proceed(st, S.State.next_ue(st), fresh, Gmm.Gmm.start_of(id), entropy, Lv.next_live(st)))


def Lw.initial_mm(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +m: Mm.Mm) -> {Lv.okf(st, Gmm.Gmm.initial_mm(st, assoc, stream, entropy, ran, nas, m)) == True{} : Bool}:
  match m:
    case Mm.Mm{mt, +fields, opts}:
      match mt:
        case Mm.RegistrationRequest{}:
          Lw.register(st, assoc, stream, entropy, ran, nas, Mi.MobileId.read(I.Fields.lve2(fields)))
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

def Lw.initial_nas(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +r: Result<&2, &2, B.Err, Mm.Mm>) -> {Lv.okf(st, Gmm.Gmm.initial_nas(st, assoc, stream, entropy, ran, nas, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+m}:
      Lw.initial_mm(st, assoc, stream, entropy, ran, nas, m)

def Lw.initial(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +v: V.InitialUEMessage.View) -> {Lv.okf(st, Gmm.Gmm.initial(st, assoc, stream, entropy, v)) == True{} : Bool}:
  match v:
    case V.InitialUEMessage.View{+ran_ue_ngap_id, +nas_pdu, userlocationinformation, rrcestablishmentcause, fiveg_s_tmsi, amfsetid, allowednssai, selectedplmnidentity, iabnodeindication, cemodebsupport_indicator, npn_accessinformation}:
      Lw.initial_nas(st, assoc, stream, entropy, ran_ue_ngap_id, nas_pdu, Mm.Mm.read(nas_pdu))

def Lw.initial_of_view(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, V.InitialUEMessage.View>) -> {Lv.okf(st, Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.initial(st, assoc, stream, entropy, v)


def Lw.secure(+st: S.State, +key: U32, +ue: S.Ue, +supi: B.Digits(), +k_amf: B.Bytes(), +nea: Sec.Nas.Ea, +nia: Sec.Nas.Ia, +caps: B.Bytes(), +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.secure(st, key, ue, supi, k_amf, nea, nia, caps)) == True{} : Bool}:
  +timer = S.State.next_timer(st)
  +ctx : Sec.Nas.Ctx = Sec.Ctx{Sec.Keys{Kd.kdf.k_nas_int(k_amf, Sec.Nas.Ia.id(nia)), Kd.kdf.k_nas_enc(k_amf, Sec.Nas.Ea.id(nea)), nea, nia, 1}, Sec.Nas.Count.zero(), None{}}
  +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.IntegrityNew{}, Gmm.Gmm.security_mode_command(U32.or(U32.shln(Sec.Nas.Ea.id(nea), 4n), Sec.Nas.Ia.id(nia)), S.Ue.ngksi(ue), caps))
  +ue2 = S.Ue.with_dl(S.Ue.with_supi(ue, supi), S.SecurityMode{S.Guard{timer, 0}, Sec.Nas.Protected.ctx(p), k_amf}, Sec.Nas.Protected.msg(p))
  +x : N.Act = Gmm.Gmm.dl(key, ue2, Sec.Nas.Protected.msg(p))
  +y : N.Act = N.TimerStart{Some{key}, timer, Gmm.Gmm.guard_ms()}
  +as = List.append(&2, N.Act, N.Guard.cancel(S.Ue.guard(ue)), [x, y])
  Lv.join(st, Gmm.Gmm.place(st, key, ue2), (S.BumpTimer{}, as), Lw.place(st, key, ue2), Lv.leaf(st, S.BumpTimer{}, as, Lv.append(st, N.Guard.cancel(S.Ue.guard(ue)), [x, y], Lv.cancel(st, S.Ue.guard(ue)), Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==}))), {==}))

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
      +caps = Gmm.Gmm.caps(ue)
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
          Lw.response(st, key, ue, av, supi, I.Opts.find(45, opts), ek)
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{guard, old, response, complete}:
          {==}
        case S.Registered{old}:
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
          Lw.failure(st, key, ue, av, resynced, supi, I.Fields.byte1(fields), I.Opts.find(48, opts), entropy, ek)
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{guard, old, response, complete}:
          {==}
        case S.Registered{old}:
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
        case S.ContextSetup{guard, old, response, complete}:
          {==}
        case S.Registered{old}:
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

def Lw.plain(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Mm.Mm>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.plain(st, key, ue, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{Mm.Mm{+mt, +fields, +opts}}:
      Lw.phase(st, key, ue, entropy, mt, fields, opts, S.Ue.phase(ue), ek)


def Lw.sm_complete(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +k_amf: B.Bytes(), +ctx: Sec.Nas.Ctx, +count: Sec.Nas.Count, +opts: List<&2, I.Ie>, +cfg: Maybe<&2, S.Cfg>, +m: Maybe<&2, U32>, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.sm_complete(st, key, ue, guard, k_amf, ctx, count, opts, cfg, m)) == True{} : Bool}:
  match cfg m:
    case Some{+c} Some{+tmsi}:
      +timer = S.State.next_timer(st)
      +reg = I.Bytes.or(I.Opts.find(113, opts), S.Ue.reg(ue))
      +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.Ciphered{}, Gmm.Gmm.registration_accept(c, tmsi))
      +ph : S.Phase = S.ContextSetup{S.Guard{timer, 0}, Sec.Nas.Protected.ctx(p), False{}, False{}}
      +ue2 = S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(ue, ph, Sec.Nas.Protected.msg(p)), reg), tmsi)
      +x : N.Act = N.Ics{S.Ue.assoc(ue2), S.Ue.stream(ue2), key, S.Ue.ran_id(ue2), c, Gmm.Gmm.caps(ue2), Kd.kdf.k_gnb(k_amf, Sec.Nas.Count.value(count)), Sec.Nas.Protected.msg(p)}
      +y : N.Act = N.TimerStart{Some{key}, timer, Gmm.Gmm.guard_ms()}
      +z : N.Act = N.TimerCancel{S.Guard.timer(guard)}
      Lv.join(st, Gmm.Gmm.place(st, key, ue2), (S.BumpTimer{}, [z, x, y]), Lw.place(st, key, ue2), Lv.leaf(st, S.BumpTimer{}, [z, x, y], Lv.cons(st, z, [x, y], {==}, Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==}))), {==}))
    case Some{c} None{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek)
    case None{} Some{t}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek)
    case None{} None{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek)

def Lw.setup_done(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +ctx: Sec.Nas.Ctx, +response: Bool, +complete: Bool, +both: Bool) -> {Lv.okf(st, Gmm.Gmm.setup_done(st, key, ue, guard, ctx, response, complete, both)) == True{} : Bool}:
  match both:
    case True{}:
      {==}
    case False{}:
      {==}

def Lw.setup_step(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +ctx: Sec.Nas.Ctx, +response: Bool, +complete: Bool) -> {Lv.okf(st, Gmm.Gmm.setup_step(st, key, ue, guard, ctx, response, complete)) == True{} : Bool}:
  Lw.setup_done(st, key, ue, guard, ctx, response, complete, Bool.and(response, complete))

def Lw.dereg_answer(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +switch_off: Bool, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.dereg_answer(st, key, ue, ctx, switch_off)) == True{} : Bool}:
  match switch_off:
    case True{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister()), ek)
    case False{}:
      Lv.prepend(st, Gmm.Gmm.dl(key, ue, Sec.Nas.Protected.msg(Sec.Nas.protect(ctx, Sec.Ciphered{}, Gmm.Gmm.deregistration_accept()))), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister())), ek, Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister()), ek))

def Lw.deregister(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +kind: U32, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.deregister(st, key, ue, ctx, kind)) == True{} : Bool}:
  Lw.dereg_answer(st, key, ue, ctx, Bool.not(U32.is_eq(U32.and(kind, 8), 0)), ek)


# A verified 5GMM message: the UL NAS Transport of a registered UE may put a session.
def Lw.sphase(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +count: Sec.Nas.Count, +ctx: Sec.Nas.Ctx, +mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +p: S.Phase, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.sphase(st, key, ue, entropy, count, ctx, mt, fields, opts, p)) == True{} : Bool}:
  match mt:
    case Mm.RegistrationRequest{}:
      {==}
    case Mm.RegistrationAccept{}:
      {==}
    case Mm.RegistrationComplete{}:
      match p:
        case S.Created{}:
          {==}
        case S.Identifying{guard}:
          {==}
        case S.Authenticating{guard, av, resynced, supi}:
          {==}
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{+guard, old, +response, complete}:
          Lv.ok_of(st, Gmm.Gmm.setup_step(st, key, ue, guard, ctx, response, True{}), Lw.setup_step(st, key, ue, guard, ctx, response, True{}))
        case S.Registered{old}:
          {==}
        case S.Releasing{guard}:
          {==}
    case Mm.RegistrationReject{}:
      {==}
    case Mm.DeregistrationRequestUe{}:
      match p:
        case S.Created{}:
          {==}
        case S.Identifying{guard}:
          {==}
        case S.Authenticating{guard, av, resynced, supi}:
          {==}
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{guard, old, response, complete}:
          Lv.ok_of(st, Gmm.Gmm.deregister(st, key, ue, ctx, I.Fields.byte1(fields)), Lw.deregister(st, key, ue, ctx, I.Fields.byte1(fields), Lv.has_live(st, key, eh)))
        case S.Registered{old}:
          Lv.ok_of(st, Gmm.Gmm.deregister(st, key, ue, ctx, I.Fields.byte1(fields)), Lw.deregister(st, key, ue, ctx, I.Fields.byte1(fields), Lv.has_live(st, key, eh)))
        case S.Releasing{guard}:
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
      match p:
        case S.Created{}:
          {==}
        case S.Identifying{guard}:
          {==}
        case S.Authenticating{guard, av, resynced, supi}:
          {==}
        case S.SecurityMode{+guard, old, +k_amf}:
          Lv.ok_of(st, Gmm.Gmm.sm_complete(st, key, ue, guard, k_amf, ctx, count, opts, S.State.config(st), Gmm.Gmm.tmsi(S.State.ues(st), List.drop(&2, U32, entropy, 16n))), Lw.sm_complete(st, key, ue, guard, k_amf, ctx, count, opts, S.State.config(st), Gmm.Gmm.tmsi(S.State.ues(st), List.drop(&2, U32, entropy, 16n)), Lv.has_live(st, key, eh)))
        case S.ContextSetup{guard, old, response, complete}:
          {==}
        case S.Registered{old}:
          {==}
        case S.Releasing{guard}:
          {==}
    case Mm.SecurityModeReject{}:
      match p:
        case S.Created{}:
          {==}
        case S.Identifying{guard}:
          {==}
        case S.Authenticating{guard, av, resynced, supi}:
          {==}
        case S.SecurityMode{guard, old, k_amf}:
          Lv.ok_of(st, Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified())), Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), Lv.has_live(st, key, eh)))
        case S.ContextSetup{guard, old, response, complete}:
          {==}
        case S.Registered{old}:
          {==}
        case S.Releasing{guard}:
          {==}
    case Mm.Status{}:
      {==}
    case Mm.UlNasTransport{}:
      match p:
        case S.Created{}:
          {==}
        case S.Identifying{guard}:
          {==}
        case S.Authenticating{guard, av, resynced, supi}:
          {==}
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{guard, old, response, complete}:
          {==}
        case S.Registered{old}:
          Lw.ul_transport(st, key, ue, ctx, fields, opts, entropy, eh)
        case S.Releasing{guard}:
          {==}
    case Mm.DlNasTransport{}:
      {==}

def Lw.protected(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +count: Sec.Nas.Count, +ctx: Sec.Nas.Ctx, +r: Result<&2, &2, B.Err, Mm.Mm>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.protected(st, key, ue, entropy, count, ctx, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{Mm.Mm{+mt, +fields, +opts}}:
      Lw.sphase(st, key, ue, entropy, count, ctx, mt, fields, opts, S.Ue.phase(ue), eh)

def Lw.opened(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Sec.Nas.Unprotected>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.opened(st, key, ue, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{Sec.Unprotected{prot, +plain, +count, +ctx}}:
      Lw.protected(st, key, ue, entropy, count, ctx, Mm.Mm.read(plain), eh)

def Lw.secured(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +nas: B.Bytes(), +m: Maybe<&2, Sec.Nas.Ctx>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.secured(st, key, ue, entropy, nas, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lv.ok_of(st, Gmm.Gmm.plain(st, key, ue, entropy, Mm.Mm.read(nas)), Lw.plain(st, key, ue, entropy, Mm.Mm.read(nas), Lv.has_live(st, key, eh)))
    case Some{+ctx}:
      Lw.opened(st, key, ue, entropy, Sec.Nas.unprotect(ctx, nas), eh)

def Lw.mm(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +nas: B.Bytes(), +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.mm(st, key, ue, entropy, nas)) == True{} : Bool}:
  Lw.secured(st, key, ue, entropy, nas, S.Phase.ctx(S.Ue.phase(ue)), eh)

def Lw.uplink_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +nas: B.Bytes(), +entropy: B.Bytes(), +m: Maybe<&2, S.Ue>, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> {Lv.ok(st, Gmm.Gmm.uplink_ue(st, assoc, key, nas, entropy, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.mm(st, key, ue, entropy, nas, Lv.owned_has(st, assoc, key, ran, ue, eo))

def Lw.uplink(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +v: V.UplinkNASTransport.View) -> {Lv.ok(st, Gmm.Gmm.uplink(st, assoc, stream, entropy, v)) == True{} : Bool}:
  match v:
    case V.UplinkNASTransport.View{+amf_ue_ngap_id, +ran_ue_ngap_id, +nas_pdu, userlocationinformation}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Lw.uplink_ue(st, assoc, key, ran_ue_ngap_id, nas_pdu, entropy, Gmm.Gmm.owner(st, assoc, key, ran_ue_ngap_id), {==})

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
    case S.ContextSetup{+guard, +ctx, response, +complete}:
      Lw.setup_step(st, key, ue, guard, ctx, True{}, complete)
    case S.Registered{old}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.ics_response_ue(+st: S.State, +assoc: U32, +key: U32, +m: Maybe<&2, S.Ue>) -> {Lv.okf(st, Gmm.Gmm.ics_response_ue(st, assoc, key, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.setup_phase(st, key, ue, S.Ue.phase(ue))

def Lw.ics_response(+st: S.State, +assoc: U32, +v: V.InitialContextSetupResponse.View) -> {Lv.okf(st, Gmm.Gmm.ics_response(st, assoc, v)) == True{} : Bool}:
  match v:
    case V.InitialContextSetupResponse.View{+amf_ue_ngap_id, +ran_ue_ngap_id, diagnostics}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Lw.ics_response_ue(st, assoc, key, Gmm.Gmm.owner(st, assoc, key, ran_ue_ngap_id))

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

def Lw.release_request(+st: S.State, +assoc: U32, +v: V.UEContextReleaseRequest.View) -> {Lv.okf(st, Gmm.Gmm.release_request(st, assoc, v)) == True{} : Bool}:
  match v:
    case V.UEContextReleaseRequest.View{+amf_ue_ngap_id, +ran_ue_ngap_id, pdusessionresourcelistcxtrelreq, +cause}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Lw.release_request_ue(st, assoc, key, ran_ue_ngap_id, cause, Gmm.Gmm.owner(st, assoc, key, ran_ue_ngap_id), {==})

def Lw.release_request_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>) -> {Lv.okf(st, Gmm.Gmm.release_request_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.release_request(st, assoc, v)

def Lw.release_complete_ue(+st: S.State, +assoc: U32, +key: U32, +m: Maybe<&2, S.Ue>) -> {Lv.okf(st, Gmm.Gmm.release_complete_ue(st, assoc, key, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      +more = List.append(&2, N.Act, N.Guard.cancel(S.Ue.guard(ue)), [N.Note{F.Info{}, "NGAP: UE context released"}])
      Lv.also(st, Gmm.Gmm.forget(st, key), more, Lw.forget(st, key), Lv.append(st, N.Guard.cancel(S.Ue.guard(ue)), [N.Note{F.Info{}, "NGAP: UE context released"}], Lv.cancel(st, S.Ue.guard(ue)), {==}))

def Lw.release_complete(+st: S.State, +assoc: U32, +v: V.UEContextReleaseComplete.View) -> {Lv.okf(st, Gmm.Gmm.release_complete(st, assoc, v)) == True{} : Bool}:
  match v:
    case V.UEContextReleaseComplete.View{+amf_ue_ngap_id, +ran_ue_ngap_id, userlocationinformation, pdusessionresourcelistcxtrelcpl, diagnostics}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Lw.release_complete_ue(st, assoc, key, Gmm.Gmm.owner(st, assoc, key, ran_ue_ngap_id))

def Lw.release_complete_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>) -> {Lv.okf(st, Gmm.Gmm.release_complete_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.release_complete(st, assoc, v)

def Lw.retry_if(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +p: S.Phase, +ok: Bool, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.retry_if(st, key, ue, guard, p, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      +x : N.Act = Gmm.Gmm.dl(key, ue, S.Ue.last_dl(ue))
      +y : N.Act = N.TimerStart{Some{key}, S.Guard.timer(guard), Gmm.Gmm.guard_ms()}
      Lv.leaf(st, S.Rephase{key, S.Phase.with_guard(p, S.Guard{S.Guard.timer(guard), U32.add(S.Guard.retries(guard), 1)})}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), {==})
    case False{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek)

def Lw.expired(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +ek: {Lv.live(st, key) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.expired(st, key, ue, p)) == True{} : Bool}:
  match p:
    case S.Created{}:
      {==}
    case S.Identifying{+guard}:
      Lw.retry_if(st, key, ue, guard, S.Identifying{guard}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek)
    case S.Authenticating{+guard, +av, +resynced, +supi}:
      Lw.retry_if(st, key, ue, guard, S.Authenticating{guard, av, resynced, supi}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek)
    case S.SecurityMode{+guard, +ctx, +k_amf}:
      Lw.retry_if(st, key, ue, guard, S.SecurityMode{guard, ctx, k_amf}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek)
    case S.ContextSetup{+guard, +ctx, +response, +complete}:
      Lw.retry_if(st, key, ue, guard, S.ContextSetup{guard, ctx, response, complete}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek)
    case S.Registered{ctx}:
      {==}
    case S.Releasing{guard}:
      Lv.also(st, Gmm.Gmm.forget(st, key), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}], Lw.forget(st, key), {==})


def Lw.setup(+st: S.State, +skey: U32, +s: S.Session, +guard: S.Guard, +pti: U32, +accept: Sm.Sm, +up_seid: B.Bytes(), +m: Maybe<&2, S.Ue>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.setup(st, skey, s, guard, pti, accept, up_seid, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.setup_gone(st, skey, s, up_seid, es)
    case Some{+ue}:
      Lw.setup_ue(st, skey, s, guard, pti, accept, up_seid, ue, S.Phase.ctx(S.Ue.phase(ue)), S.State.config(st), es)

def Lw.established_as(+st: S.State, +skey: U32, +s: S.Session, +guard: S.Guard, +pti: U32, +accept: Sm.Sm, +ok: Bool, +up: Maybe<&2, B.Bytes()>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.established_as(st, skey, s, guard, pti, accept, ok, up)) == True{} : Bool}:
  match ok up:
    case True{} Some{+up_seid}:
      Lw.setup(st, skey, s, guard, pti, accept, up_seid, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), es)
    case True{} None{}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es)
    case False{} Some{up_seid}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es)
    case False{} None{}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es)

def Lw.established_phase(+st: S.State, +skey: U32, +s: S.Session, +msg: Pf.Msg, +p: S.SPhase, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.established_phase(st, skey, s, msg, p)) == True{} : Bool}:
  match p:
    case S.Creating{+guard, +pti, +accept}:
      Lw.established_as(st, skey, s, guard, pti, accept, Up.N4.accepted(Up.N4.cause(msg)), Up.N4.up_seid(msg), es)
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{guard}:
      {==}
    case S.Active{}:
      {==}

def Lw.established(+st: S.State, +msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.established(st, msg, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.established_phase(st, skey, s, msg, S.Session.phase(s), em)

def Lw.modified_as(+st: S.State, +skey: U32, +s: S.Session, +guard: S.Guard, +ok: Bool, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.modified_as(st, skey, s, guard, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Lv.also(st, Gsm.Gsm.forget([(skey, s)], S.State.pfcp_seq(st)), [N.TimerCancel{S.Guard.timer(guard)}, N.Note{F.Warn{}, "PFCP: Session Modification refused; session released"}], Lw.gsm_forget(st, [(skey, s)], S.State.pfcp_seq(st), Lw.one(st, skey, s, es)), {==})

def Lw.modified_phase(+st: S.State, +skey: U32, +s: S.Session, +msg: Pf.Msg, +p: S.SPhase, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.modified_phase(st, skey, s, msg, p)) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept}:
      {==}
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{+guard}:
      Lw.modified_as(st, skey, s, guard, Up.N4.accepted(Up.N4.cause(msg)), es)
    case S.Active{}:
      {==}

def Lw.modified(+st: S.State, +msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.modified(st, msg, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.modified_phase(st, skey, s, msg, S.Session.phase(s), em)

def Lw.assoc_answer(+st: S.State, +ok: Bool) -> {Lv.okf(st, Up.N4.assoc_answer(ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

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
      Lw.pfcp_k6(st, msg, U32.is_eq(kind, 53))

def Lw.pfcp_k4(+st: S.State, +msg: Pf.Msg, +kind: U32, +ok: Bool) -> {Lv.okf(st, Gsm.Gsm.pfcp_k4(st, msg, kind, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Lw.pfcp_k5(st, msg, kind, U32.is_eq(kind, 51))

def Lw.pfcp_k3(+st: S.State, +msg: Pf.Msg, +kind: U32, +ok: Bool) -> {Lv.okf(st, Gsm.Gsm.pfcp_k3(st, msg, kind, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.assoc_answer(st, Up.N4.accepted(Up.N4.cause(msg)))
    case False{}:
      Lw.pfcp_k4(st, msg, kind, U32.is_eq(kind, 55))

def Lw.pfcp_k2(+st: S.State, +msg: Pf.Msg, +kind: U32, +ok: Bool) -> {Lv.okf(st, Gsm.Gsm.pfcp_k2(st, msg, kind, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Lw.pfcp_k3(st, msg, kind, U32.is_eq(kind, 6))

def Lw.pfcp_k1(+st: S.State, +msg: Pf.Msg, +kind: U32, +ok: Bool) -> {Lv.okf(st, Gsm.Gsm.pfcp_k1(st, msg, kind, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Lw.pfcp_k2(st, msg, kind, U32.is_eq(kind, 2))

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

def Lw.modify(+st: S.State, +skey: U32, +s: S.Session, +guard: S.Guard, +pti: U32, +seq: U32, +tunnel: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.modify(st, skey, s, guard, pti, seq, tunnel)) == True{} : Bool}:
  match tunnel:
    case None{}:
      Lw.abort(st, skey, s, pti, 26, seq, es)
    case Some{(+gnb_teid, +gnb_addr)}:
      +x : N.Act = N.Pfcp{Some{S.Session.ue(s)}, Up.N4.modify(S.Session.up_seid(s), gnb_teid, gnb_addr, seq)}
      +y : N.Act = N.TimerStart{Some{S.Session.ue(s)}, S.Guard.timer(guard), Up.N4.t1_ms()}
      +ek = Lv.owner_live(st, S.Session.ue(s), es)
      Lv.leaf(st, S.Both{S.Revar{skey, S.SVar{S.Session.up_seid(s), seq, S.Modifying{S.Guard{S.Guard.timer(guard), 0}}}}, S.BumpSeq{1}}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], ek, {==})), {==})

def Lw.set_up_phase(+st: S.State, +skey: U32, +s: S.Session, +transfer: B.Bytes(), +seq: U32, +p: S.SPhase, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.set_up_phase(st, skey, s, transfer, seq, p)) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept}:
      {==}
    case S.Setting{+guard, +pti}:
      Lw.modify(st, skey, s, guard, pti, seq, Gsm.Gsm.tunnel_of(G.PDUSessionResourceSetupResponseTransfer.read(Ap.Cur{0n, Ap.unpack(transfer)})), es)
    case S.Modifying{guard}:
      {==}
    case S.Active{}:
      {==}

def Lw.set_up(+st: S.State, +transfer: B.Bytes(), +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.set_up(st, transfer, seq, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.set_up_phase(st, skey, s, transfer, seq, S.Session.phase(s), em)

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
    case S.Creating{guard, pti, accept}:
      {==}
    case S.Setting{guard, +pti}:
      Lw.abort(st, skey, s, pti, 26, seq, es)
    case S.Modifying{guard}:
      {==}
    case S.Active{}:
      {==}

def Lw.failed(+st: S.State, +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.failed(st, seq, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.failed_phase(st, skey, s, seq, S.Session.phase(s), em)

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

def Lw.setup_response(+st: S.State, +assoc: U32, +v: V.PDUSessionResourceSetupResponse.View) -> {Lv.okf(st, Gsm.Gsm.setup_response(st, assoc, v)) == True{} : Bool}:
  match v:
    case V.PDUSessionResourceSetupResponse.View{+amf_ue_ngap_id, +ran_ue_ngap_id, +oks, +fails, diagnostics, uli}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Lw.setup_response_ue(st, assoc, key, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), Gsm.Gsm.list_or(G.PDUSessionResourceFailedToSetupItemSURes, fails), N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran_ue_ngap_id))

def Lw.setup_response_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>) -> {Lv.okf(st, Gsm.Gsm.setup_response_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.setup_response(st, assoc, v)

def Lw.gsm_expired(+st: S.State, +skey: U32, +s: S.Session, +p: S.SPhase, +es: {Lv.owner(S.Session.ue(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.expired(st, skey, s, p)) == True{} : Bool}:
  match p:
    case S.Creating{guard, +pti, accept}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es)
    case S.Setting{guard, +pti}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es)
    case S.Modifying{guard}:
      Lv.also(st, Gsm.Gsm.forget([(skey, s)], S.State.pfcp_seq(st)), [N.Note{F.Warn{}, "PFCP: no Session Modification Response; session released"}], Lw.gsm_forget(st, [(skey, s)], S.State.pfcp_seq(st), Lw.one(st, skey, s, es)), {==})
    case S.Active{}:
      {==}


# Timers
# ------

def Lw.start_with_tries(+st: S.State, +cfg: Maybe<&2, S.Cfg>, +tries: U32) -> {Lv.okf(st, Up.N4.start_with_tries(st, cfg, tries)) == True{} : Bool}:
  match cfg:
    case None{}:
      {==}
    case Some{c}:
      {==}

def Lw.retry(+st: S.State, +cfg: Maybe<&2, S.Cfg>, +tries: U32, +again: Bool) -> {Lv.okf(st, Up.N4.retry(st, cfg, tries, again)) == True{} : Bool}:
  match again:
    case True{}:
      Lw.start_with_tries(st, cfg, tries)
    case False{}:
      {==}

def Lw.n4_expired(+st: S.State, +link: S.Link) -> {Lv.okf(st, Up.N4.expired(st, link)) == True{} : Bool}:
  match link:
    case S.Idle{}:
      {==}
    case S.Asking{+tries}:
      Lw.retry(st, S.State.config(st), U32.add(tries, 1), U32.is_lt(tries, Up.N4.n1()))
    case S.Paused{}:
      Lw.start_with_tries(st, S.State.config(st), 1)
    case S.Up{}:
      {==}

def Lw.node_timer(+st: S.State, +ok: Bool) -> {Lv.okf(st, K.Kernel.node_timer(st, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.n4_expired(st, S.N4.link(S.State.n4(st)))
    case False{}:
      {==}

def Lw.fired_session(+st: S.State, +timer: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}) -> {Lv.okf(st, K.Kernel.fired_session(st, timer, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.node_timer(st, U32.is_eq(timer, S.N4.timer()))
    case Some{(+skey, +s)}:
      Lw.gsm_expired(st, skey, s, S.Session.phase(s), em)

def Lw.fired_ue(+st: S.State, +timer: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>, +em: {Lv.ufound(m, S.State.ues(st)) == True{} : Bool}) -> {Lv.okf(st, K.Kernel.fired_ue(st, timer, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.fired_session(st, timer, S.Sessions.by_timer(timer, S.State.sessions(st)), Lv.by_timer(timer, S.State.sessions(st)))
    case Some{(+key, +ue)}:
      Lw.expired(st, key, ue, S.Ue.phase(ue), Lv.has_live(st, key, em))

def Lw.fired(+st: S.State, +timer: U32) -> {Lv.okf(st, K.Kernel.fired(st, timer)) == True{} : Bool}:
  Lw.fired_ue(st, timer, S.Ues.by_timer(timer, S.State.ues(st)), Lv.ue_by_timer(timer, S.State.ues(st)))


# NGAP
# ----

def Lw.d7(+st: S.State, +assoc: U32, +ies: List<&2, Fr.Ie>, +ok: Bool) -> {Lv.ok(st, R.Route.d7(st, assoc, ies, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lv.ok_of(st, Gsm.Gsm.setup_response_of_view(st, assoc, V.PDUSessionResourceSetupResponse.view(ies)), Lw.setup_response_of_view(st, assoc, V.PDUSessionResourceSetupResponse.view(ies)))
    case False{}:
      {==}

def Lw.d6(+st: S.State, +assoc: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +ok: Bool) -> {Lv.ok(st, R.Route.d6(st, assoc, kind, code, ies, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lv.ok_of(st, Gmm.Gmm.release_complete_of_view(st, assoc, V.UEContextReleaseComplete.view(ies)), Lw.release_complete_of_view(st, assoc, V.UEContextReleaseComplete.view(ies)))
    case False{}:
      Lw.d7(st, assoc, ies, N.Ngap.is_procedure(kind, code, 1n, 29n))

def Lw.d5(+st: S.State, +assoc: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +ok: Bool) -> {Lv.ok(st, R.Route.d5(st, assoc, kind, code, ies, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lv.ok_of(st, Gmm.Gmm.release_request_of_view(st, assoc, V.UEContextReleaseRequest.view(ies)), Lw.release_request_of_view(st, assoc, V.UEContextReleaseRequest.view(ies)))
    case False{}:
      Lw.d6(st, assoc, kind, code, ies, N.Ngap.is_procedure(kind, code, 1n, 41n))

def Lw.d4(+st: S.State, +assoc: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +ok: Bool) -> {Lv.ok(st, R.Route.d4(st, assoc, kind, code, ies, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lv.ok_of(st, Gmm.Gmm.ics_response_of_view(st, assoc, V.InitialContextSetupResponse.view(ies)), Lw.ics_response_of_view(st, assoc, V.InitialContextSetupResponse.view(ies)))
    case False{}:
      Lw.d5(st, assoc, kind, code, ies, N.Ngap.is_procedure(kind, code, 0n, 42n))

def Lw.d3(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +ok: Bool) -> {Lv.ok(st, R.Route.d3(st, assoc, stream, kind, code, ies, entropy, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.uplink_of_view(st, assoc, stream, entropy, V.UplinkNASTransport.view(ies))
    case False{}:
      Lw.d4(st, assoc, kind, code, ies, N.Ngap.is_procedure(kind, code, 1n, 14n))

def Lw.d2(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +ok: Bool) -> {Lv.ok(st, R.Route.d2(st, assoc, stream, kind, code, ies, entropy, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lv.ok_of(st, Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, V.InitialUEMessage.view(ies)), Lw.initial_of_view(st, assoc, stream, entropy, V.InitialUEMessage.view(ies)))
    case False{}:
      Lw.d3(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 46n))


# Steps
# -----

def Lv.step_acts(+st: S.State, +o: N.GOut(), +h: {Lv.ok(st, o) == True{} : Bool}) -> {Lv.acts(st, K.Kernel.actions(N.Step.of(st, o))) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      P.Bool.and_true_l(Lv.acts(st, acts), Lv.homed(tx, S.State.ues(st)), h)

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

def Lv.owned_tx(+tx: S.Tx, +st: S.State, +e: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +h: {Lv.homed(tx, S.State.ues(st)) == True{} : Bool}) -> {S.Sessions.owned(S.State.sessions(S.Tx.apply(tx, st)), S.State.ues(S.Tx.apply(tx, st))) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      e
    case S.Put{+key, +ue}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, next_timer, n4}:
          Lv.owned_owned(S.Ues.put(key, ue, ues), sessions)
    case S.Rephase{+key, +phase}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, next_timer, n4}:
          Lv.owned_rephase(sessions, key, phase, ues, e)
    case S.Del{+key}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, next_timer, n4}:
          Lv.owned_del(sessions, key, ues, e)
    case S.PutSession{+key, +s}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, next_timer, n4}:
          P.Bool.and_intro(Tb.Table.has(S.Ue, S.Session.ue(s), ues), S.Sessions.owned(S.Sessions.sift(S.SClear{key, s}, sessions), ues), P.Bool.and_true_l(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Gsm.Gsm.phase_bounded(S.Session.phase(s)), h), Lv.owned_sift(S.SClear{key, s}, sessions, ues, e))
    case S.Revar{+key, +v}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, next_timer, n4}:
          Lv.owned_revar(sessions, key, v, ues, e)
    case S.DelSession{+key}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, next_timer, n4}:
          Lv.owned_sift(S.SExcept{key}, sessions, ues, e)
    case S.Subs{new}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.SetLink{link}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.BumpUe{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.BumpTimer{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.BumpSeq{n}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.Both{+a, +b}:
      +ha = P.Bool.and_true_l(Lv.homed(a, S.State.ues(st)), Lv.homed(b, PT.Tk.ues(a, S.State.ues(st))), h)
      +hb = P.Bool.and_true_r(Lv.homed(a, S.State.ues(st)), Lv.homed(b, PT.Tk.ues(a, S.State.ues(st))), h)
      eu = Equal.sym(Tb.Table(S.Ue), S.State.ues(S.Tx.apply(a, st)), PT.Tk.ues(a, S.State.ues(st)), PT.Tk.ues_apply(a, st))
      Lv.owned_tx(b, S.Tx.apply(a, st), Lv.owned_tx(a, st, e, ha), (%eu : {Lv.homed(b, _) == True{} : Bool}; hb))

def Lv.step_owned(+st: S.State, +o: N.GOut(), +e: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +h: {Lv.ok(st, o) == True{} : Bool}) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(N.Step.of(st, o))), S.State.ues(K.Kernel.state(N.Step.of(st, o)))) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      Lv.owned_tx(tx, st, e, P.Bool.and_true_r(Lv.acts(st, acts), Lv.homed(tx, S.State.ues(st)), h))

# A gone UE is not live
# ---------------------

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

def Lv.dead3(+h: Bool, +n: Bool, +o: Bool, +eh: {h == False{} : Bool}, +en: {n == False{} : Bool}, eo: {o == True{} : Bool} -> {h == True{} : Bool}) -> {Bool.or(h, Bool.or(n, o)) == False{} : Bool}:
  match h:
    case True{}:
      Empty.absurd({Bool.or(True{}, Bool.or(n, o)) == False{} : Bool}, P.Refute.true_false(eh))
    case False{}:
      match n:
        case True{}:
          Empty.absurd({Bool.or(False{}, Bool.or(True{}, o)) == False{} : Bool}, P.Refute.true_false(en))
        case False{}:
          match o:
            case True{}:
              Empty.absurd({Bool.or(False{}, Bool.or(False{}, True{})) == False{} : Bool}, P.Refute.bool(eo({==})))
            case False{}:
              {==}

def Lv.dead(+st: S.State, +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {U32.is_eq(k, S.State.next_ue(st)) == False{} : Bool}) -> {Lv.live(st, k) == False{} : Bool}:
  sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), None{}, eg)
  Lv.dead3(Tb.Table.has(S.Ue, k, S.State.ues(st)), U32.is_eq(k, S.State.next_ue(st)), Lv.owner(k, S.State.sessions(st)), (%sg : {Tb.Table.present(S.Ue, _) == False{} : Bool}; {==}), en, w => Lv.owner_has(k, S.State.sessions(st), S.State.ues(st), eo, w))

def Lv.not_k(+st: S.State, +x: U32, +k: U32, +b: Bool, +eb: {U32.is_eq(x, k) == b : Bool}, +ht: {Lv.live(st, x) == True{} : Bool}, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {U32.is_eq(k, S.State.next_ue(st)) == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      ex = P.U32.eq_of_is_eq(x, k, eb)
      hk : {Lv.live(st, k) == True{} : Bool} = (%ex : {Lv.live(st, _) == True{} : Bool}; ht)
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, P.Refute.true_false(Equal.trans(Bool, True{}, Lv.live(st, k), False{}, Equal.sym(Bool, Lv.live(st, k), True{}, hk), Lv.dead(st, k, eo, eg, en))))

def Lv.tag_spare(+st: S.State, +m: Maybe<&2, U32>, +k: U32, +ht: {Lv.tag(st, m) == True{} : Bool}, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {U32.is_eq(k, S.State.next_ue(st)) == False{} : Bool}) -> {Bool.not(S.Maybe.same_u32(m, Some{k})) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      Lv.not_k(st, x, k, U32.is_eq(x, k), {==}, ht, eo, eg, en)

# No action a UE procedure takes is built from a key that is not live.
def Lv.spare_of(+st: S.State, +as: List<&2, N.Act>, +k: U32, +h: {Lv.acts(st, as) == True{} : Bool}, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {U32.is_eq(k, S.State.next_ue(st)) == False{} : Bool}) -> {N.Acts.spare(k, as) == True{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case +a <> +more:
      +ha = P.Bool.and_true_l(Lv.act(st, a), Lv.acts(st, more), h)
      P.Bool.and_intro(Bool.not(S.Maybe.same_u32(N.Act.ue(a), Some{k})), N.Acts.spare(k, more), Lv.tag_spare(st, N.Act.ue(a), k, P.Bool.and_true_r(Bool.not(N.Ngap.is_ng_setup_response(a)), Lv.tag(st, N.Act.ue(a)), ha), eo, eg, en), Lv.spare_of(st, more, k, P.Bool.and_true_r(Lv.act(st, a), Lv.acts(st, more), h), eo, eg, en))

# Every event
# -----------

def Lv.setup_spare(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.NGSetupRequest.View>, +k: U32) -> {N.Acts.spare(k, K.Kernel.actions(N.NgSetup.of_view(st, assoc, r))) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{v}:
      {==}

def Lv.setup_owned(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.NGSetupRequest.View>, +e: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(N.NgSetup.of_view(st, assoc, r))), S.State.ues(K.Kernel.state(N.NgSetup.of_view(st, assoc, r)))) == True{} : Bool}:
  match r:
    case Fail{err}:
      e
    case Done{v}:
      e

def Lv.d1_spare(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +ok: Bool, +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {U32.is_eq(k, S.State.next_ue(st)) == False{} : Bool}) -> {N.Acts.spare(k, K.Kernel.actions(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, ok))) == True{} : Bool}:
  match ok:
    case True{}:
      Lv.setup_spare(st, assoc, V.NGSetupRequest.view(ies), k)
    case False{}:
      +o = R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n))
      Lv.spare_of(st, K.Kernel.actions(N.Step.of(st, o)), k, Lv.step_acts(st, o, Lw.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n))), eo, eg, en)

def Lv.d1_owned(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +ok: Bool, +e: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, ok))), S.State.ues(K.Kernel.state(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, ok)))) == True{} : Bool}:
  match ok:
    case True{}:
      Lv.setup_owned(st, assoc, V.NGSetupRequest.view(ies), e)
    case False{}:
      +o = R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n))
      Lv.step_owned(st, o, e, Lw.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n)))

def Lv.ies_spare(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +entropy: B.Bytes(), +r: Ap.Rd(List<&2, Fr.Ie>), +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {U32.is_eq(k, S.State.next_ue(st)) == False{} : Bool}) -> {N.Acts.spare(k, K.Kernel.actions(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r))) == True{} : Bool}:
  match r:
    case Fail{err}:
      {==}
    case Done{(+ies, c)}:
      Lv.d1_spare(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 21n), k, eo, eg, en)

def Lv.ies_owned(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +entropy: B.Bytes(), +r: Ap.Rd(List<&2, Fr.Ie>), +e: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r))), S.State.ues(K.Kernel.state(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r)))) == True{} : Bool}:
  match r:
    case Fail{err}:
      e
    case Done{(+ies, c)}:
      Lv.d1_owned(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 21n), e)

def Lv.pdu_spare(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Fr.Pdu>, +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {U32.is_eq(k, S.State.next_ue(st)) == False{} : Bool}) -> {N.Acts.spare(k, K.Kernel.actions(R.Route.of_pdu(st, assoc, stream, entropy, r))) == True{} : Bool}:
  match r:
    case Fail{err}:
      {==}
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Lv.ies_spare(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), k, eo, eg, en)

def Lv.pdu_owned(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Fr.Pdu>, +e: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(R.Route.of_pdu(st, assoc, stream, entropy, r))), S.State.ues(K.Kernel.state(R.Route.of_pdu(st, assoc, stream, entropy, r)))) == True{} : Bool}:
  match r:
    case Fail{err}:
      e
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Lv.ies_owned(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), e)

def Lv.config_spare(+complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), +k: U32) -> {N.Acts.spare(k, K.Kernel.actions(K.Kernel.config(complete, st, tlvs, entropy))) == True{} : Bool}:
  match complete:
    case False{}:
      {==}
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          {==}

def Lv.config_owned(+complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), +e: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(K.Kernel.config(complete, st, tlvs, entropy))), S.State.ues(K.Kernel.state(K.Kernel.config(complete, st, tlvs, entropy)))) == True{} : Bool}:
  match complete:
    case False{}:
      e
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e

def Lv.up_spare(+st: S.State, +assoc: U32, +k: U32) -> {N.Acts.spare(k, K.Kernel.actions(K.Kernel.assoc_up(st, assoc))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      {==}

def Lv.up_owned(+st: S.State, +assoc: U32, +e: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(K.Kernel.assoc_up(st, assoc))), S.State.ues(K.Kernel.state(K.Kernel.assoc_up(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      e

# An association going down deletes at eUPF the sessions of the contexts it owned.
def Lv.down_spare(+st: S.State, +assoc: U32, +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {U32.is_eq(k, S.State.next_ue(st)) == False{} : Bool}) -> {N.Acts.spare(k, K.Kernel.actions(K.Kernel.assoc_down(st, assoc))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, +sessions, +pfcp_seq, next_ue, next_timer, n4}:
      +st0 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}
      +gone = S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions)
      +note : N.Act = N.Note{F.Info{}, "NGAP: association down; its UE contexts and sessions released"}
      Lv.spare_of(st0, List.append(&2, N.Act, Up.N4.deletions(gone, pfcp_seq), [note]), k, Lv.append(st0, Up.N4.deletions(gone, pfcp_seq), [note], Lv.dels(st0, gone, pfcp_seq, Lv.srows_sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions)), {==}), eo, eg, en)

def Lv.down_owned(+st: S.State, +assoc: U32) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(K.Kernel.assoc_down(st, assoc))), S.State.ues(K.Kernel.state(K.Kernel.assoc_down(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, next_timer, n4}:
      Lv.owned_owned(S.Ues.drop_assoc(assoc, ues), sessions)

def Lv.step_spare(+st: S.State, +ev: F.Evt, +entropy: B.Bytes(), +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {U32.is_eq(k, S.State.next_ue(st)) == False{} : Bool}) -> {N.Acts.spare(k, K.Kernel.actions(K.Kernel.step(st, ev, entropy))) == True{} : Bool}:
  match ev:
    case F.Config{len, +tlvs}:
      Lv.config_spare(S.Cfg.complete(tlvs), st, tlvs, entropy, k)
    case F.NgapAssocUp{assoc}:
      Lv.up_spare(st, assoc, k)
    case F.NgapAssocDown{+assoc}:
      Lv.down_spare(st, assoc, k, eo, eg, en)
    case F.NgapData{+assoc, +stream, len, +bytes}:
      Lv.pdu_spare(st, assoc, stream, entropy, Fr.Pdu.read(bytes), k, eo, eg, en)
    case F.PfcpData{len, +bytes}:
      Lv.spare_of(st, K.Kernel.actions(N.Step.of(st, Gsm.Gsm.pfcp_data(st, bytes))), k, Lv.step_acts(st, Gsm.Gsm.pfcp_data(st, bytes), Lv.ok_of(st, Gsm.Gsm.pfcp_data(st, bytes), Lw.pfcp_data(st, bytes))), eo, eg, en)
    case F.TimerFired{+timer}:
      Lv.spare_of(st, K.Kernel.actions(N.Step.of(st, K.Kernel.fired(st, timer))), k, Lv.step_acts(st, K.Kernel.fired(st, timer), Lv.ok_of(st, K.Kernel.fired(st, timer), Lw.fired(st, timer))), eo, eg, en)

def Lv.step_owned_ev(+st: S.State, +ev: F.Evt, +entropy: B.Bytes(), +e: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(K.Kernel.step(st, ev, entropy))), S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy)))) == True{} : Bool}:
  match ev:
    case F.Config{len, +tlvs}:
      Lv.config_owned(S.Cfg.complete(tlvs), st, tlvs, entropy, e)
    case F.NgapAssocUp{assoc}:
      Lv.up_owned(st, assoc, e)
    case F.NgapAssocDown{+assoc}:
      Lv.down_owned(st, assoc)
    case F.NgapData{+assoc, +stream, len, +bytes}:
      Lv.pdu_owned(st, assoc, stream, entropy, Fr.Pdu.read(bytes), e)
    case F.PfcpData{len, +bytes}:
      Lv.step_owned(st, Gsm.Gsm.pfcp_data(st, bytes), e, Lv.ok_of(st, Gsm.Gsm.pfcp_data(st, bytes), Lw.pfcp_data(st, bytes)))
    case F.TimerFired{+timer}:
      Lv.step_owned(st, K.Kernel.fired(st, timer), e, Lv.ok_of(st, K.Kernel.fired(st, timer), Lw.fired(st, timer)))

def L.amf.sessions.owned(st, ev, entropy, e):
  ({==}, Lv.step_owned_ev(st, ev, entropy, e))

def L.amf.release.forgets_ue(st, ev, entropy, k, eo, eg, en):
  Lv.step_spare(st, ev, entropy, k, eo, eg, en)
# NG Setup answers only a supported request
# -----------------------------------------
# Every other path of the NgapData step is a UE procedure, and no action of
# a UE procedure is an NG Setup Response.

def Req.answer(cfg: S.Cfg, +assoc: U32, b: Bool, e: {N.Ngap.is_ng_setup_response(N.Setup{assoc, N.NgSetup.answer(cfg, b)}) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))

def Req.reply(config: Maybe<&2, S.Cfg>, +assoc: U32, v: V.NGSetupRequest.View, e: {N.Ngap.is_ng_setup_response(N.Setup{assoc, N.NgSetup.reply(config, v)}) == True{} : Bool}) -> {N.NgSetup.supported_view(config, v) == True{} : Bool}:
  match config:
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Some{+cfg}:
      match v:
        case V.NGSetupRequest.View{globalrannodeid, +supportedtalist, defaultpagingdrx}:
          Req.answer(cfg, assoc, N.Ta.supported(S.Cfg.plmn(cfg), S.Cfg.tac(cfg), supportedtalist), e)

def Req.view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.NGSetupRequest.View>, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(N.NgSetup.of_view(st, assoc, r))) == True{} : Bool}) -> {N.NgSetup.supported_of_view(S.State.config(st), r) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Done{+v}:
      Req.reply(S.State.config(st), assoc, v, PK.Bool.or_false(N.Ngap.is_ng_setup_response(N.Setup{assoc, N.NgSetup.reply(S.State.config(st), v)}), e))

def Req.d1(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), ok: Bool, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, ok))) == True{} : Bool}) -> {N.NgSetup.supported_d1(S.State.config(st), ies, ok) == True{} : Bool}:
  match ok:
    case True{}:
      Req.view(st, assoc, V.NGSetupRequest.view(ies), e)
    case False{}:
      +o = R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n))
      ar = Lv.no_response(st, K.Kernel.actions(N.Step.of(st, o)), Lv.step_acts(st, o, Lw.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n))))
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool((%ar : {_ == True{} : Bool}; e)))

def Req.ies(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, entropy: B.Bytes(), r: Ap.Rd(List<&2, Fr.Ie>), e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r))) == True{} : Bool}) -> {N.NgSetup.supported_ies(S.State.config(st), kind, code, r) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Done{(+ies, c)}:
      Req.d1(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 21n), e)

def Req.pdu(+st: S.State, +assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Fr.Pdu>, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.of_pdu(st, assoc, stream, entropy, r))) == True{} : Bool}) -> {N.NgSetup.supported_pdu(S.State.config(st), r) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Req.ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), e)

def L.amf.ng_setup.requires_supported_plmn(st, entropy, assoc, stream, len, bytes, e):
  Req.pdu(st, assoc, stream, entropy, Fr.Pdu.read(bytes), e)

