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
import ../smf/switch.bend as Sw
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

def Lv.tx_prepend(+a: N.Act, +o: N.GOut()) -> {N.Out.tx(N.Out.prepend(a, o)) == N.Out.tx(o) : S.Tx}:
  match o:
    case (tx, acts):
      {==}

def Lv.tx_also(+o: N.GOut(), +more: List<&2, N.Act>) -> {N.Out.tx(N.Out.also(o, more)) == N.Out.tx(o) : S.Tx}:
  match o:
    case (tx, acts):
      {==}

# Release Command: the context stays under its key, releasing, with a new guard.
def Lv.release_get(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause) -> {Tb.Table.get(S.Ue, key, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release(st, key, ue, cause))))) == Some{S.Ue.with_phase(ue, S.Releasing{S.Guard{0}})} : Maybe<&2, S.Ue>}:
  +ur = S.Ue.with_phase(ue, S.Releasing{S.Guard{0}})
  +p = Gmm.Gmm.place(st, key, ur)
  +ts : List<&2, N.Act> = N.TimerStart{Some{key}, key, N.Ue.guard_ms()} <> Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause)
  +gone = Gmm.Gmm.sessions(S.Ues.evicted(key, ur, S.State.ues(st)), S.State.sessions(st))
  +e = Up.N4.deletions(gone, S.State.pfcp_seq(st))
  er = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release(st, key, ue, cause)))), PT.Tk.ues(N.Out.tx(Gmm.Gmm.release(st, key, ue, cause)), S.State.ues(st)), PT.Tk.render(st, Gmm.Gmm.release(st, key, ue, cause)))
  %er : {Tb.Table.get(S.Ue, key, _) == Some{ur} : Maybe<&2, S.Ue>}
  ep = Equal.sym(S.Tx, N.Out.tx(N.Out.prepend(N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}, N.Out.also(p, ts))), N.Out.tx(N.Out.also(p, ts)), Lv.tx_prepend(N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}, N.Out.also(p, ts)))
  %ep : {Tb.Table.get(S.Ue, key, PT.Tk.ues(_, S.State.ues(st))) == Some{ur} : Maybe<&2, S.Ue>}
  ea = Equal.sym(S.Tx, N.Out.tx(N.Out.also(p, ts)), N.Out.tx(p), Lv.tx_also(p, ts))
  %ea : {Tb.Table.get(S.Ue, key, PT.Tk.ues(_, S.State.ues(st))) == Some{ur} : Maybe<&2, S.Ue>}
  ei = Equal.sym(S.Tx, N.Out.tx(p), S.Both{N.Out.tx(e), S.Put{key, ur}}, PW.Out.tx_join(e, (S.Put{key, ur}, Gmm.Gmm.evict(S.Ues.evicted(key, ur, S.State.ues(st))))))
  %ei : {Tb.Table.get(S.Ue, key, PT.Tk.ues(_, S.State.ues(st))) == Some{ur} : Maybe<&2, S.Ue>}
  ek = Equal.sym(Bool, U32.is_eq(key, key), True{}, P.U32.is_eq_refl(key))
  %ek : {Tb.Table.hit(S.Ue, ur, Tb.Table.get(S.Ue, key, S.Ues.sift(S.Clear{key, ur}, PT.Tk.ues(N.Out.tx(e), S.State.ues(st)))), _) == Some{ur} : Maybe<&2, S.Ue>}
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
        case S.Registered{ctx, nh, released}:
          Empty.absurd({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Registered{ctx, nh, released}, last_dl}, S.Registered{ctx, nh, released}))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}, P.Refute.none_some(S.Guard, g, eg))
        case S.Switching{guard, ctx, nh, released}:
          Lv.release_get(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Switching{guard, ctx, nh, released}, last_dl}, N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified()))
        case S.Handover{ctx, nh, source, leg}:
          eq = Equal.sym(S.Guard, S.Guard{0}, g, P.Some.inj(S.Guard, S.Guard{0}, g, eg))
          Empty.absurd({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Handover{ctx, nh, source, leg}, last_dl}, S.Handover{ctx, nh, source, leg}))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}, P.Refute.true_false((%eq : {U32.is_lt(S.Guard.retries(_), Gmm.Gmm.max_retries()) == False{} : Bool}; er)))
        case S.Releasing{+guard}:
          eq = Equal.sym(S.Guard, guard, g, P.Some.inj(S.Guard, guard, g, eg))
          Empty.absurd({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{guard}, last_dl}, S.Releasing{guard}))))) == Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, S.Releasing{S.Guard{0}}, last_dl}} : Maybe<&2, S.Ue>}, np((%eq : {S.Releasing{_} == S.Releasing{g} : S.Phase}; {==})))

def Lv.app_nil(+xs: List<&2, N.Act>) -> {List.append(&2, N.Act, xs, []) == xs : List<&2, N.Act>}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +more:
      e = Equal.sym(List<&2, N.Act>, List.append(&2, N.Act, more, []), more, Lv.app_nil(more))
      (%e : {a <> _ == a <> more : List<&2, N.Act>}; {==})

def Lv.and_false(+x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# A context forgotten after its sessions' deletions: their actions, then the
# guards of the sessions gone stopped.
def Lv.forget_acts(+st: S.State, +key: U32, +o: N.GOut(), +more: List<&2, N.Act>) -> {K.Kernel.actions(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more))) == List.append(&2, N.Act, List.append(&2, N.Act, N.Out.acts(o), more), N.Gone.cancels(S.State.sessions(st), S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more)))))) : List<&2, N.Act>}:
  match o:
    case (+tx, +acts):
      +after = S.State.sessions(S.Tx.apply(S.Del{key}, S.Tx.apply(tx, st)))
      e = Equal.sym(List<&2, N.Act>, List.append(&2, N.Act, acts, []), acts, Lv.app_nil(acts))
      ef = Equal.sym(Bool, Bool.and(S.Tx.keeps_sessions(tx), False{}), False{}, Lv.and_false(S.Tx.keeps_sessions(tx)))
      (%e : {List.append(&2, N.Act, List.append(&2, N.Act, _, more), N.Gone.when(Bool.and(S.Tx.keeps_sessions(tx), False{}), S.State.sessions(st), after)) == List.append(&2, N.Act, List.append(&2, N.Act, acts, more), N.Gone.cancels(S.State.sessions(st), after)) : List<&2, N.Act>}; (%ef : {List.append(&2, N.Act, List.append(&2, N.Act, acts, more), N.Gone.when(_, S.State.sessions(st), after)) == List.append(&2, N.Act, List.append(&2, N.Act, acts, more), N.Gone.cancels(S.State.sessions(st), after)) : List<&2, N.Act>}; {==}))

def Lv.forgot(+st: S.State, +key: U32, +o: N.GOut(), +more: List<&2, N.Act>, h: {Tb.Table.get(S.Ue, key, S.State.ues(K.Kernel.state(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more))))) == None{} : Maybe<&2, S.Ue>} & {S.Sessions.of_ue(key, S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more))))) == [] : Tb.Table(S.Session)}, +ea: {K.Kernel.actions(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more))) == List.append(&2, N.Act, List.append(&2, N.Act, N.Out.acts(o), more), N.Gone.cancels(S.State.sessions(st), S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more)))))) : List<&2, N.Act>}) -> {Tb.Table.get(S.Ue, key, S.State.ues(K.Kernel.state(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more))))) == None{} : Maybe<&2, S.Ue>} & ({S.Sessions.of_ue(key, S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more))))) == [] : Tb.Table(S.Session)} & {K.Kernel.actions(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more))) == List.append(&2, N.Act, List.append(&2, N.Act, N.Out.acts(o), more), N.Gone.cancels(S.State.sessions(st), S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more)))))) : List<&2, N.Act>}):
  match h:
    case (a, b):
      (a, (b, ea))

def Lv.exp1(+st: S.State, +entropy: B.Bytes(), +k: U32, +u: S.Ue, +g: S.Guard, +et: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eg: {S.Ue.guard(u) == Some{g} : Maybe<&2, S.Guard>}, np: {S.Ue.phase(u) == S.Releasing{g} : S.Phase} -> Empty, +er: {U32.is_lt(S.Guard.retries(g), Gmm.Gmm.max_retries()) == False{} : Bool}) -> {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.TimerFired{k}, entropy)))) == Some{S.Ue.with_phase(u, S.Releasing{S.Guard{0}})} : Maybe<&2, S.Ue>}:
  set = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{u}, et)
  %set : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, k, _))))) == Some{S.Ue.with_phase(u, S.Releasing{S.Guard{0}})} : Maybe<&2, S.Ue>}
  Lv.retried(st, k, u, g, et, eg, np, er)

def Lv.exp2(+st: S.State, +entropy: B.Bytes(), +k: U32, +u: S.Ue, +g: S.Guard, +et: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(u) == S.Releasing{g} : S.Phase}) -> {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.TimerFired{k}, entropy)))) == None{} : Maybe<&2, S.Ue>} & ({S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{k}, entropy)))) == [] : Tb.Table(S.Session)} & {K.Kernel.actions(K.Kernel.step(st, F.TimerFired{k}, entropy)) == List.append(&2, N.Act, List.append(&2, N.Act, N.Out.acts(Up.N4.deletions(S.Sessions.of_ue(k, S.State.sessions(st)), S.State.pfcp_seq(st))), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]), N.Gone.cancels(S.State.sessions(st), S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{k}, entropy))))) : List<&2, N.Act>}):
  set = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{u}, et)
  %set : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, k, _))))) == None{} : Maybe<&2, S.Ue>} & ({S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, k, _))))) == [] : Tb.Table(S.Session)} & {K.Kernel.actions(N.Step.of(st, K.Kernel.fired_ue(st, k, _))) == List.append(&2, N.Act, List.append(&2, N.Act, N.Out.acts(Up.N4.deletions(S.Sessions.of_ue(k, S.State.sessions(st)), S.State.pfcp_seq(st))), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]), N.Gone.cancels(S.State.sessions(st), S.State.sessions(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, k, _)))))) : List<&2, N.Act>})
  sep = Equal.sym(S.Phase, S.Ue.phase(u), S.Releasing{g}, ep)
  %sep : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _))))) == None{} : Maybe<&2, S.Ue>} & ({S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _))))) == [] : Tb.Table(S.Session)} & {K.Kernel.actions(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _))) == List.append(&2, N.Act, List.append(&2, N.Act, N.Out.acts(Up.N4.deletions(S.Sessions.of_ue(k, S.State.sessions(st)), S.State.pfcp_seq(st))), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]), N.Gone.cancels(S.State.sessions(st), S.State.sessions(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, _)))))) : List<&2, N.Act>})
  +d = Up.N4.deletions(S.Sessions.of_ue(k, S.State.sessions(st)), S.State.pfcp_seq(st))
  +more : List<&2, N.Act> = [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}]
  Lv.forgot(st, k, d, more, PK.Tx.forget(k, d, more, st), Lv.forget_acts(st, k, d, more))

def L.amf.guard.expires(st, entropy, k, u, g, et, eg):
  (np => er => Lv.exp1(st, entropy, k, u, g, et, eg, np, er), ep => Lv.exp2(st, entropy, k, u, g, et, ep))

# What a step may do
# ------------------
# A key is live in a state when a context holds it, it is the one a new context
# takes, or a session belongs to it (S.Session.tag: one being deleted belongs
# to none). A UE procedure builds its actions only
# from live keys and never answers NG Setup; every context it puts or rephases
# is registered or guarded; every session it puts belongs to a context, with an
# Accept within the packet-filter bound if it is being created, and every
# session it puts or changes is known to the UPF exactly when past Creating, the
# changes relying on the sessions of the state before the step being so. A UE
# that is gone holds none of these, so nothing is built from it
# (amf.release.forgets_ue), no session outlives its context but while it is
# being deleted at the UPF (amf.sessions.owned), no context is left Created (amf.contexts.guarded), no
# session holds an Accept beyond the bound (smf.packet_filters.capacity_reject)
# and the UPF knows the sessions past Creating (smf.sessions.known).

def Lv.owner(+x: U32, ss: Tb.Table(S.Session)) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case (k, +t) <> more:
      Bool.or(S.Maybe.same_u32(S.Session.tag(t), Some{x}), Lv.owner(x, more))

# The tag of a row: no UE, or a UE that owns a session.
def Lv.tagged(m: Maybe<&2, U32>, +ss: Tb.Table(S.Session)) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+x}:
      Lv.owner(x, ss)

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

# An action of any step: no answer to NG Setup, built from live keys only.
def Lv.actw(+st: S.State, +a: N.Act) -> Bool:
  Bool.and(Bool.not(N.Ngap.is_ng_setup_response(a)), Lv.tag(st, N.Act.ue(a)))

def Lv.actsw(+st: S.State, as: List<&2, N.Act>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case +a <> more:
      Bool.and(Lv.actw(st, a), Lv.actsw(st, more))

# A deletion a transaction starts has a guard that has not fired, its request
# among the actions, which start its guard for T1; a session it puts is not
# being deleted.
def Lv.arms_p(+k: U32, p: S.SPhase, +acts: List<&2, N.Act>) -> Bool:
  match p:
    case S.Deleting{guard, +request}:
      Bool.and(U32.is_eq(S.Guard.retries(guard), 0), Bool.and(N.Acts.sends(request, acts), N.Acts.starts_for(k, Up.N4.t1_ms(), acts)))
    case _:
      True{}

def Lv.arms(tx: S.Tx, +acts: List<&2, N.Act>) -> Bool:
  match tx:
    case S.Revar{+key, v}:
      Lv.arms_p(key, S.SVar.phase(v), acts)
    case S.PutSession{key, +s}:
      S.SPhase.live(S.Session.phase(s))
    case S.Both{a, b}:
      Bool.and(Lv.arms(a, acts), Lv.arms(b, acts))
    case _:
      True{}

# A session's variable part agrees with the UPF.
def Lv.var_ok(+v: S.SVar) -> Bool:
  S.SPhase.knows(S.SVar.phase(v), Nat.is_eq(List.length(&2, U32, S.SVar.up_seid(v)), 8n))

# A change of a session keeps the Accept's bound and agrees with the UPF,
# given the sessions of st do.
def Lv.revar_ok(+st: S.State, +v: S.SVar) -> Bool:
  Bool.and(Bool.or(Gsm.Gsm.phase_bounded(S.SVar.phase(v)), Bool.not(Gsm.Gsm.bounded(S.State.sessions(st)))), Bool.or(Lv.var_ok(v), Bool.not(S.Sessions.known(S.State.sessions(st)))))

# A session being deleted is changed or forgotten only when its guard fires
# or the UPF answers it (smf.deletion.held): every other change or deletion
# names a key whose row, in the state before the step, is live, when no two
# sessions share a key; a change that keeps the session live leaves one being
# deleted alone (S.SVar.follows); a session put conflicts with none.
def Lv.live_m(m: Maybe<&2, S.Session>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+t}:
      S.SPhase.live(S.Session.phase(t))

def Lv.kept(+st: S.State, +k: U32) -> Bool:
  Bool.or(Lv.live_m(Tb.Table.get(S.Session, k, S.State.sessions(st))), Bool.not(S.Sessions.unique(S.State.sessions(st))))

# An action of a UE procedure stops only a context's guard, and starts a
# context's or the next context's (Lv.held), the PFCP association's (timer
# 0), or for T1 that of a session whose row it may change (Lv.kept): a session
# being deleted has its guard stopped only when the UPF settles a session
# (Lv.fine) or its row goes (N.Gone.cancels), and started only when its guard
# fires (Lv.okw).
def Lv.timed(+st: S.State, +t: U32, +ms: U32) -> Bool:
  Bool.or(U32.is_eq(t, S.N4.timer()), Bool.or(Lv.held(st, t), Bool.and(Lv.kept(st, t), U32.is_eq(ms, Up.N4.t1_ms()))))

def Lv.reach(+st: S.State, +a: N.Act) -> Bool:
  match a:
    case N.TimerCancel{+t}:
      Tb.Table.has(S.Ue, t, S.State.ues(st))
    case N.TimerStart{+ue, +t, +ms}:
      Bool.and(Lv.tag(st, ue), Lv.timed(st, t, ms))
    case _:
      Lv.tag(st, N.Act.ue(a))

def Lv.act(+st: S.State, +a: N.Act) -> Bool:
  Bool.and(Bool.not(N.Ngap.is_ng_setup_response(a)), Lv.reach(st, a))

def Lv.acts(+st: S.State, as: List<&2, N.Act>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case +a <> more:
      Bool.and(Lv.act(st, a), Lv.acts(st, more))

def Lv.spare(+st: S.State, +k: U32, +v: S.SVar) -> Bool:
  Bool.or(S.SPhase.live(S.SVar.phase(v)), Lv.kept(st, k))

def Lv.clear(+k: U32, +s: S.Session, ss: Tb.Table(S.Session)) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case (+k0, +t) <> more:
      Bool.and(Bool.or(S.SPhase.live(S.Session.phase(t)), Bool.not(S.SRow.conflicts(k, s, k0, t))), Lv.clear(k, s, more))

# A context put is owned by an association that has completed NG Setup, when
# every context of st is.
def Lv.home(+st: S.State, +ue: S.Ue) -> Bool:
  Bool.or(S.Assocs.has(S.Ue.assoc(ue), S.State.assocs(st)), Bool.not(S.Ues.set_up(S.State.ues(st), S.State.assocs(st))))

def Lv.puts(+key: U32, +s: S.Session, +ues: Tb.Table(S.Ue)) -> Bool:
  Bool.and(S.Ids.seid(key), Bool.and(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s)))))

# A context's {NH, NCC} pair moves only along its chain (amf.ncc.step): a
# phase written under a key holds no pair, the one the context held or the
# next (Lv.chain); only a context put over one that held none takes a first
# pair, the first of the chain from the K_AMF of its Security Mode and from
# the KgNB the same outcome sends it in Initial Context Setup (Lv.seeds). The
# row written decides what the key's context holds only where no two
# contexts share a key.
def Lv.chained(b: Maybe<&2, S.Nh>, +y: S.Nh) -> Bool:
  match b:
    case Some{+x}:
      Bool.or(S.Nh.same(y, x), S.Nh.same(y, S.Nh.next(x)))
    case None{}:
      False{}

def Lv.chains(n: Maybe<&2, S.Nh>, +b: Maybe<&2, S.Nh>) -> Bool:
  match n:
    case None{}:
      True{}
    case Some{+y}:
      Lv.chained(b, y)

def Lv.chain(+st: S.State, +key: U32, +n: Maybe<&2, S.Nh>) -> Bool:
  Bool.or(Lv.chains(n, S.Ue.nh(Tb.Table.get(S.Ue, key, S.State.ues(st)))), Bool.not(S.Ues.unique(S.State.ues(st))))

def Lv.unpaired(+st: S.State, +key: U32) -> Bool:
  Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(Tb.Table.get(S.Ue, key, S.State.ues(st)))))

# A context put chains its pair, or takes a first one where it held none.
def Lv.chain_put(+st: S.State, +key: U32, +n: Maybe<&2, S.Nh>) -> Bool:
  Bool.or(Lv.chain(st, key, n), Lv.unpaired(st, key))

def Lv.from_mode(k: Maybe<&2, B.Bytes()>, +key: U32, +y: S.Nh, +acts: List<&2, N.Act>) -> Bool:
  match k:
    case None{}:
      False{}
    case Some{+ka}:
      N.Acts.seeds(ka, key, y, acts)

def Lv.firsts(n: Maybe<&2, S.Nh>, +k: Maybe<&2, B.Bytes()>, +key: U32, +acts: List<&2, N.Act>) -> Bool:
  match n:
    case None{}:
      True{}
    case Some{+y}:
      Lv.from_mode(k, key, y, acts)

def Lv.seed(+st: S.State, +key: U32, +n: Maybe<&2, S.Nh>, +acts: List<&2, N.Act>) -> Bool:
  Bool.or(Lv.firsts(n, S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st))), key, acts), Bool.not(Lv.unpaired(st, key)))

def Lv.seeds(+st: S.State, tx: S.Tx, +acts: List<&2, N.Act>) -> Bool:
  match tx:
    case S.Put{+key, +ue}:
      Lv.seed(st, key, S.Phase.nh(S.Ue.phase(ue)), acts)
    case S.Both{a, b}:
      Bool.and(Lv.seeds(st, a, acts), Lv.seeds(st, b, acts))
    case _:
      True{}

# What the actions say of a first pair stays said with more on either side.
def Lv.sd_l(+ka: B.Bytes(), +key: U32, +y: S.Nh, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.seeds(ka, key, y, xs) == True{} : Bool}) -> {N.Acts.seeds(ka, key, y, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({N.Acts.seeds(ka, key, y, ys) == True{} : Bool}, P.Refute.bool(h))
    case +a <> +more:
      P.Bool.or_mono(N.Act.seeds(ka, key, y, a), N.Acts.seeds(ka, key, y, more), N.Acts.seeds(ka, key, y, List.append(&2, N.Act, more, ys)), h, e => Lv.sd_l(ka, key, y, more, ys, e))

def Lv.sd_r(+ka: B.Bytes(), +key: U32, +y: S.Nh, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.seeds(ka, key, y, ys) == True{} : Bool}) -> {N.Acts.seeds(ka, key, y, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +a <> +more:
      P.Bool.or_r(N.Act.seeds(ka, key, y, a), N.Acts.seeds(ka, key, y, List.append(&2, N.Act, more, ys)), Lv.sd_r(ka, key, y, more, ys, h))

def Lv.mode_l(+k: Maybe<&2, B.Bytes()>, +key: U32, +y: S.Nh, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Lv.from_mode(k, key, y, xs) == True{} : Bool}) -> {Lv.from_mode(k, key, y, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match k:
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(h))
    case Some{+ka}:
      Lv.sd_l(ka, key, y, xs, ys, h)

def Lv.mode_r(+k: Maybe<&2, B.Bytes()>, +key: U32, +y: S.Nh, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Lv.from_mode(k, key, y, ys) == True{} : Bool}) -> {Lv.from_mode(k, key, y, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match k:
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(h))
    case Some{+ka}:
      Lv.sd_r(ka, key, y, xs, ys, h)

def Lv.firsts_l(+n: Maybe<&2, S.Nh>, +k: Maybe<&2, B.Bytes()>, +key: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Lv.firsts(n, k, key, xs) == True{} : Bool}) -> {Lv.firsts(n, k, key, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match n:
    case None{}:
      {==}
    case Some{+y}:
      Lv.mode_l(k, key, y, xs, ys, h)

def Lv.firsts_r(+n: Maybe<&2, S.Nh>, +k: Maybe<&2, B.Bytes()>, +key: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Lv.firsts(n, k, key, ys) == True{} : Bool}) -> {Lv.firsts(n, k, key, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match n:
    case None{}:
      {==}
    case Some{+y}:
      Lv.mode_r(k, key, y, xs, ys, h)

def Lv.seeds_l(+st: S.State, +tx: S.Tx, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Lv.seeds(st, tx, xs) == True{} : Bool}) -> {Lv.seeds(st, tx, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match tx:
    case S.Put{+key, +ue}:
      +k = S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st)))
      +n = S.Phase.nh(S.Ue.phase(ue))
      P.Bool.or_mono_l(Lv.firsts(n, k, key, xs), Lv.firsts(n, k, key, List.append(&2, N.Act, xs, ys)), Bool.not(Lv.unpaired(st, key)), h, e => Lv.firsts_l(n, k, key, xs, ys, e))
    case S.Both{+a, +b}:
      P.Bool.and_intro(Lv.seeds(st, a, List.append(&2, N.Act, xs, ys)), Lv.seeds(st, b, List.append(&2, N.Act, xs, ys)), Lv.seeds_l(st, a, xs, ys, P.Bool.and_true_l(Lv.seeds(st, a, xs), Lv.seeds(st, b, xs), h)), Lv.seeds_l(st, b, xs, ys, P.Bool.and_true_r(Lv.seeds(st, a, xs), Lv.seeds(st, b, xs), h)))
    case S.Keep{}:
      {==}
    case S.Rephase{key, phase}:
      {==}
    case S.Del{key}:
      {==}
    case S.PutSession{key, s}:
      {==}
    case S.Revar{key, v}:
      {==}
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

def Lv.seeds_r(+st: S.State, +tx: S.Tx, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Lv.seeds(st, tx, ys) == True{} : Bool}) -> {Lv.seeds(st, tx, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match tx:
    case S.Put{+key, +ue}:
      +k = S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st)))
      +n = S.Phase.nh(S.Ue.phase(ue))
      P.Bool.or_mono_l(Lv.firsts(n, k, key, ys), Lv.firsts(n, k, key, List.append(&2, N.Act, xs, ys)), Bool.not(Lv.unpaired(st, key)), h, e => Lv.firsts_r(n, k, key, xs, ys, e))
    case S.Both{+a, +b}:
      P.Bool.and_intro(Lv.seeds(st, a, List.append(&2, N.Act, xs, ys)), Lv.seeds(st, b, List.append(&2, N.Act, xs, ys)), Lv.seeds_r(st, a, xs, ys, P.Bool.and_true_l(Lv.seeds(st, a, ys), Lv.seeds(st, b, ys), h)), Lv.seeds_r(st, b, xs, ys, P.Bool.and_true_r(Lv.seeds(st, a, ys), Lv.seeds(st, b, ys), h)))
    case S.Keep{}:
      {==}
    case S.Rephase{key, phase}:
      {==}
    case S.Del{key}:
      {==}
    case S.PutSession{key, s}:
      {==}
    case S.Revar{key, v}:
      {==}
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

def Lv.nh_refl(+x: S.Nh) -> {S.Nh.same(x, x) == True{} : Bool}:
  match x:
    case S.Nh{+a, +h, +c}:
      ea = Equal.sym(Bool, B.bytes_eq(a, a), True{}, P.Bytes.eq_refl(a))
      eh = Equal.sym(Bool, B.bytes_eq(h, h), True{}, P.Bytes.eq_refl(h))
      ec = Equal.sym(Bool, U32.is_eq(c, c), True{}, P.U32.is_eq_refl(c))
      (%ea : {Bool.and(_, Bool.and(B.bytes_eq(h, h), U32.is_eq(c, c))) == True{} : Bool}; (%eh : {Bool.and(True{}, Bool.and(_, U32.is_eq(c, c))) == True{} : Bool}; (%ec : {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}; {==})))

# The pair kept, the next one.
def Lv.chains_same(+x: S.Nh) -> {Lv.chains(Some{x}, Some{x}) == True{} : Bool}:
  P.Bool.or_l(S.Nh.same(x, x), S.Nh.same(x, S.Nh.next(x)), Lv.nh_refl(x))

def Lv.chains_next(+x: S.Nh) -> {Lv.chains(Some{S.Nh.next(x)}, Some{x}) == True{} : Bool}:
  P.Bool.or_r(S.Nh.same(S.Nh.next(x), x), S.Nh.same(S.Nh.next(x), S.Nh.next(x)), Lv.nh_refl(S.Nh.next(x)))

# A pair written under the key of a context in phase p.
def Lv.chain_at(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == p : S.Phase}, +n: Maybe<&2, S.Nh>, +h: {Lv.chains(n, S.Phase.nh(p)) == True{} : Bool}) -> {Lv.chain(st, key, n) == True{} : Bool}:
  +m = Tb.Table.get(S.Ue, key, S.State.ues(st))
  sg = Equal.sym(Maybe<&2, S.Ue>, m, Some{ue}, eg)
  sp = Equal.sym(S.Phase, S.Ue.phase(ue), p, ep)
  P.Bool.or_l(Lv.chains(n, S.Ue.nh(m)), Bool.not(S.Ues.unique(S.State.ues(st))), (%sg : {Lv.chains(n, S.Ue.nh(_)) == True{} : Bool}; (%sp : {Lv.chains(n, S.Phase.nh(_)) == True{} : Bool}; h)))

def Lv.free(+st: S.State, tx: S.Tx) -> Bool:
  match tx:
    case S.Put{+key, +ue}:
      Bool.and(Lv.chain_put(st, key, S.Phase.nh(S.Ue.phase(ue))), Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue)))))
    case S.Rephase{+key, +phase}:
      Bool.and(Lv.chain(st, key, S.Phase.nh(phase)), Bool.and(S.Phase.guarded(phase), S.Phase.idle(phase)))
    case S.PutSession{key, s}:
      False{}
    case S.Revar{+key, +v}:
      Bool.and(Lv.spare(st, key, v), Lv.revar_ok(st, v))
    case S.DelSession{+key}:
      Lv.kept(st, key)
    case S.Both{a, b}:
      Bool.and(Lv.free(st, a), Lv.free(st, b))
    case _:
      True{}

def Lv.homed(+st: S.State, +tx: S.Tx, +ues: Tb.Table(S.Ue)) -> Bool:
  match tx:
    case S.Put{+key, +ue}:
      Bool.and(Lv.chain_put(st, key, S.Phase.nh(S.Ue.phase(ue))), Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st, ue)))))
    case S.Rephase{+key, +phase}:
      Bool.and(Lv.chain(st, key, S.Phase.nh(phase)), Bool.and(S.Phase.guarded(phase), S.Ue.fits(phase, Tb.Table.get(S.Ue, key, ues))))
    case S.PutSession{+key, +s}:
      Bool.and(Lv.clear(key, s, S.State.sessions(st)), Lv.puts(key, s, ues))
    case S.Revar{+key, +v}:
      Bool.and(Lv.spare(st, key, v), Lv.revar_ok(st, v))
    case S.DelSession{+key}:
      Lv.kept(st, key)
    case S.Both{+a, b}:
      Bool.and(Lv.homed(st, a, ues), Lv.homed(st, b, PT.Tk.ues(a, ues)))
    case _:
      True{}

# What the invariants of every step rely on (Inv.step): Lv.homed but what a
# session being deleted undergoes when its guard fires or the UPF answers it.
def Lv.homedw(+st: S.State, +tx: S.Tx, +ues: Tb.Table(S.Ue)) -> Bool:
  match tx:
    case S.Put{+key, +ue}:
      Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st, ue))))
    case S.Rephase{+key, +phase}:
      Bool.and(S.Phase.guarded(phase), S.Ue.fits(phase, Tb.Table.get(S.Ue, key, ues)))
    case S.PutSession{+key, +s}:
      Lv.puts(key, s, ues)
    case S.Revar{key, +v}:
      Lv.revar_ok(st, v)
    case S.Both{+a, b}:
      Bool.and(Lv.homedw(st, a, ues), Lv.homedw(st, b, PT.Tk.ues(a, ues)))
    case _:
      True{}

# A UE procedure stops a context's guard only with a transaction that leaves
# no handover pending under its key whatever the table holds (Lv.idles): it
# rephases, puts or forgets that context into a phase with none pending, and
# nothing after makes one pending there (Lv.keeps). So no step stops a
# pending handover's guard and leaves the handover pending
# (amf.handover.guarded). An outcome that writes no pending phase (Lv.calm)
# keeps every key.

def Lv.keeps(+t: U32, tx: S.Tx) -> Bool:
  match tx:
    case S.Rephase{+key, +phase}:
      Bool.or(S.Phase.idle(phase), Bool.not(U32.is_eq(key, t)))
    case S.Put{+key, +ue}:
      Bool.or(S.Phase.idle(S.Ue.phase(ue)), Bool.not(U32.is_eq(key, t)))
    case S.Both{a, b}:
      Bool.and(Lv.keeps(t, a), Lv.keeps(t, b))
    case _:
      True{}

def Lv.idles(+t: U32, tx: S.Tx) -> Bool:
  match tx:
    case S.Rephase{+key, +phase}:
      Bool.and(U32.is_eq(key, t), S.Phase.idle(phase))
    case S.Put{+key, +ue}:
      Bool.and(U32.is_eq(key, t), S.Phase.idle(S.Ue.phase(ue)))
    case S.Del{+key}:
      U32.is_eq(key, t)
    case S.Both{a, +b}:
      Bool.or(Lv.idles(t, b), Bool.and(Lv.idles(t, a), Lv.keeps(t, b)))
    case _:
      False{}

def Lv.calm(tx: S.Tx) -> Bool:
  match tx:
    case S.Rephase{key, +phase}:
      S.Phase.idle(phase)
    case S.Put{key, +ue}:
      S.Phase.idle(S.Ue.phase(ue))
    case S.Both{a, b}:
      Bool.and(Lv.calm(a), Lv.calm(b))
    case _:
      True{}

# The timer an action stops, if any.
def Lv.cancelled(a: N.Act) -> Maybe<&2, U32>:
  match a:
    case N.TimerCancel{t}:
      Some{t}
    case _:
      None{}

def Lv.stop(+tx: S.Tx, m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+t}:
      Lv.idles(t, tx)

def Lv.stops(+tx: S.Tx, acts: List<&2, N.Act>) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case a <> more:
      Bool.and(Lv.stop(tx, Lv.cancelled(a)), Lv.stops(tx, more))

def Lv.stops_cons(+tx: S.Tx, +a: N.Act, +more: List<&2, N.Act>, +ha: {Lv.stop(tx, Lv.cancelled(a)) == True{} : Bool}, +hm: {Lv.stops(tx, more) == True{} : Bool}) -> {Lv.stops(tx, a <> more) == True{} : Bool}:
  P.Bool.and_intro(Lv.stop(tx, Lv.cancelled(a)), Lv.stops(tx, more), ha, hm)

def Lv.stops_app(+tx: S.Tx, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {Lv.stops(tx, xs) == True{} : Bool}, +hy: {Lv.stops(tx, ys) == True{} : Bool}) -> {Lv.stops(tx, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      Lv.stops_cons(tx, a, List.append(&2, N.Act, more, ys), P.Bool.and_true_l(Lv.stop(tx, Lv.cancelled(a)), Lv.stops(tx, more), hx), Lv.stops_app(tx, more, ys, P.Bool.and_true_r(Lv.stop(tx, Lv.cancelled(a)), Lv.stops(tx, more), hx), hy))

# A context's own key: rephased, put or forgotten into no pending handover.
def Lv.idles_rephase(+key: U32, +p: S.Phase, +e: {S.Phase.idle(p) == True{} : Bool}) -> {Lv.idles(key, S.Rephase{key, p}) == True{} : Bool}:
  P.Bool.and_intro(U32.is_eq(key, key), S.Phase.idle(p), P.U32.is_eq_refl(key), e)

def Lv.idles_put(+key: U32, +ue: S.Ue, +e: {S.Phase.idle(S.Ue.phase(ue)) == True{} : Bool}) -> {Lv.idles(key, S.Put{key, ue}) == True{} : Bool}:
  P.Bool.and_intro(U32.is_eq(key, key), S.Phase.idle(S.Ue.phase(ue)), P.U32.is_eq_refl(key), e)

def Lv.idles_del(+key: U32) -> {Lv.idles(key, S.Del{key}) == True{} : Bool}:
  P.U32.is_eq_refl(key)

def Lv.keeps_calm(+t: U32, +tx: S.Tx, +e: {Lv.calm(tx) == True{} : Bool}) -> {Lv.keeps(t, tx) == True{} : Bool}:
  match tx:
    case S.Rephase{+key, +phase}:
      P.Bool.or_l(S.Phase.idle(phase), Bool.not(U32.is_eq(key, t)), e)
    case S.Put{+key, +ue}:
      P.Bool.or_l(S.Phase.idle(S.Ue.phase(ue)), Bool.not(U32.is_eq(key, t)), e)
    case S.Both{+a, +b}:
      P.Bool.and_intro(Lv.keeps(t, a), Lv.keeps(t, b), Lv.keeps_calm(t, a, P.Bool.and_true_l(Lv.calm(a), Lv.calm(b), e)), Lv.keeps_calm(t, b, P.Bool.and_true_r(Lv.calm(a), Lv.calm(b), e)))
    case S.Keep{}:
      {==}
    case S.Del{key}:
      {==}
    case S.PutSession{key, s}:
      {==}
    case S.Revar{key, v}:
      {==}
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

# A transaction of the session side only is calm.
def Lv.calm_sx(+tx: S.Tx, +e: {PW.Sx.only(tx) == True{} : Bool}) -> {Lv.calm(tx) == True{} : Bool}:
  match tx:
    case S.Both{+a, +b}:
      P.Bool.and_intro(Lv.calm(a), Lv.calm(b), Lv.calm_sx(a, P.Bool.and_true_l(PW.Sx.only(a), PW.Sx.only(b), e)), Lv.calm_sx(b, P.Bool.and_true_r(PW.Sx.only(a), PW.Sx.only(b), e)))
    case S.Rephase{key, phase}:
      Empty.absurd({Lv.calm(S.Rephase{key, phase}) == True{} : Bool}, P.Refute.bool(e))
    case S.Put{key, ue}:
      Empty.absurd({Lv.calm(S.Put{key, ue}) == True{} : Bool}, P.Refute.bool(e))
    case S.Keep{}:
      {==}
    case S.Del{key}:
      {==}
    case S.PutSession{key, s}:
      {==}
    case S.Revar{key, v}:
      {==}
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

def Lv.calm_join(+a: N.GOut(), +b: N.GOut(), +ea: {Lv.calm(N.Out.tx(a)) == True{} : Bool}, +eb: {Lv.calm(N.Out.tx(b)) == True{} : Bool}) -> {Lv.calm(N.Out.tx(N.Out.join(a, b))) == True{} : Bool}:
  e = Equal.sym(S.Tx, N.Out.tx(N.Out.join(a, b)), S.Both{N.Out.tx(a), N.Out.tx(b)}, PW.Out.tx_join(a, b))
  (%e : {Lv.calm(_) == True{} : Bool}; P.Bool.and_intro(Lv.calm(N.Out.tx(a)), Lv.calm(N.Out.tx(b)), ea, eb))

# A context forgotten: no handover pending under its key, and its guard,
# if it has one, stopped.
def Lv.forget_idles(+st: S.State, +key: U32) -> {Lv.idles(key, N.Out.tx(Gmm.Gmm.forget(st, key))) == True{} : Bool}:
  +d = Up.N4.deletions(S.Sessions.of_ue(key, S.State.sessions(st)), S.State.pfcp_seq(st))
  e = Equal.sym(S.Tx, N.Out.tx(N.Out.join(d, (S.Del{key}, []))), S.Both{N.Out.tx(d), S.Del{key}}, PW.Out.tx_join(d, (S.Del{key}, [])))
  (%e : {Lv.idles(key, _) == True{} : Bool}; P.Bool.or_l(Lv.idles(key, S.Del{key}), Bool.and(Lv.idles(key, N.Out.tx(d)), Lv.keeps(key, S.Del{key})), Lv.idles_del(key)))

def Lv.cancel_stops(+tx: S.Tx, +key: U32, +g: Maybe<&2, S.Guard>, +h: {Lv.idles(key, tx) == True{} : Bool}) -> {Lv.stops(tx, N.Guard.cancel(key, g)) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{guard}:
      Lv.stops_cons(tx, N.TimerCancel{key}, [], h, {==})

# A context put under its key after another outcome, into a phase with no
# handover pending.
def Lv.idles_join_put(+a: N.GOut(), +key: U32, +v: S.Ue, +p: S.Phase, +ep: {S.Ue.phase(v) == p : S.Phase}, +ei: {S.Phase.idle(p) == True{} : Bool}) -> {Lv.idles(key, N.Out.tx(N.Out.join(a, (S.Put{key, v}, [])))) == True{} : Bool}:
  e = Equal.sym(S.Tx, N.Out.tx(N.Out.join(a, (S.Put{key, v}, []))), S.Both{N.Out.tx(a), S.Put{key, v}}, PW.Out.tx_join(a, (S.Put{key, v}, [])))
  sp = Equal.sym(S.Phase, S.Ue.phase(v), p, ep)
  hi : {S.Phase.idle(S.Ue.phase(v)) == True{} : Bool} = (%sp : {S.Phase.idle(_) == True{} : Bool}; ei)
  (%e : {Lv.idles(key, _) == True{} : Bool}; P.Bool.or_l(Lv.idles(key, S.Put{key, v}), Bool.and(Lv.idles(key, N.Out.tx(a)), Lv.keeps(key, S.Put{key, v})), Lv.idles_put(key, v, hi)))

# What an outcome stops stays idled by it with another outcome on either
# side, the one after calm.
def Lv.stop_l(+ta: S.Tx, +tb: S.Tx, +m: Maybe<&2, U32>, +h: {Lv.stop(ta, m) == True{} : Bool}, +hc: {Lv.calm(tb) == True{} : Bool}) -> {Lv.stop(S.Both{ta, tb}, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+t}:
      P.Bool.or_r(Lv.idles(t, tb), Bool.and(Lv.idles(t, ta), Lv.keeps(t, tb)), P.Bool.and_intro(Lv.idles(t, ta), Lv.keeps(t, tb), h, Lv.keeps_calm(t, tb, hc)))

def Lv.stops_l(+ta: S.Tx, +tb: S.Tx, +acts: List<&2, N.Act>, +h: {Lv.stops(ta, acts) == True{} : Bool}, +hc: {Lv.calm(tb) == True{} : Bool}) -> {Lv.stops(S.Both{ta, tb}, acts) == True{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      Lv.stops_cons(S.Both{ta, tb}, a, more, Lv.stop_l(ta, tb, Lv.cancelled(a), P.Bool.and_true_l(Lv.stop(ta, Lv.cancelled(a)), Lv.stops(ta, more), h), hc), Lv.stops_l(ta, tb, more, P.Bool.and_true_r(Lv.stop(ta, Lv.cancelled(a)), Lv.stops(ta, more), h), hc))

def Lv.stop_r(+ta: S.Tx, +tb: S.Tx, +m: Maybe<&2, U32>, +h: {Lv.stop(tb, m) == True{} : Bool}) -> {Lv.stop(S.Both{ta, tb}, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+t}:
      P.Bool.or_l(Lv.idles(t, tb), Bool.and(Lv.idles(t, ta), Lv.keeps(t, tb)), h)

def Lv.stops_r(+ta: S.Tx, +tb: S.Tx, +acts: List<&2, N.Act>, +h: {Lv.stops(tb, acts) == True{} : Bool}) -> {Lv.stops(S.Both{ta, tb}, acts) == True{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      Lv.stops_cons(S.Both{ta, tb}, a, more, Lv.stop_r(ta, tb, Lv.cancelled(a), P.Bool.and_true_l(Lv.stop(tb, Lv.cancelled(a)), Lv.stops(tb, more), h)), Lv.stops_r(ta, tb, more, P.Bool.and_true_r(Lv.stop(tb, Lv.cancelled(a)), Lv.stops(tb, more), h)))

# The actions that release a handover's target stop no guard.
def Lv.drop_stops(+tx: S.Tx, +key: U32, +leg: S.Leg, +cause: G.Cause) -> {Lv.stops(tx, Ho.Ho.drop(key, leg, cause)) == True{} : Bool}:
  match leg:
    case S.Asked{t}:
      {==}
    case S.Acked{t, r, s, ts}:
      {==}

def Lv.leg_drop_stops(+tx: S.Tx, +key: U32, +p: S.Phase, +cause: G.Cause) -> {Lv.stops(tx, Ho.Ho.leg_drop(key, p, cause)) == True{} : Bool}:
  match p:
    case S.Handover{ctx, nh, source, +leg}:
      Lv.drop_stops(tx, key, leg, cause)
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
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lv.evict_stops(+tx: S.Tx, +vs: Tb.Table(S.Ue)) -> {Lv.stops(tx, Gmm.Gmm.evict(vs)) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case (+key, +v) <> +more:
      +cause = N.Ngap.nas_cause(G.CauseNas.deregister())
      Lv.stops_cons(tx, N.Release{S.Ue.assoc(v), S.Ue.stream(v), key, S.Ue.ran_id(v), cause}, List.append(&2, N.Act, Ho.Ho.leg_drop(key, S.Ue.phase(v), cause), Gmm.Gmm.evict(more)), {==}, Lv.stops_app(tx, Ho.Ho.leg_drop(key, S.Ue.phase(v), cause), Gmm.Gmm.evict(more), Lv.leg_drop_stops(tx, key, S.Ue.phase(v), cause), Lv.evict_stops(tx, more)))

def Lv.expiry_stops(+tx: S.Tx, +key: U32, +ue: S.Ue, +leg: S.Leg) -> {Lv.stops(tx, Ho.Ho.expiry(key, ue, leg)) == True{} : Bool}:
  match leg:
    case S.Asked{t}:
      {==}
    case S.Acked{t, r, s, ts}:
      {==}

def Lv.lost_stops(+tx: S.Tx, +k: U32, +u: S.Ue, +leg: S.Leg) -> {Lv.stops(tx, Ho.Ho.lost(k, u, leg)) == True{} : Bool}:
  match leg:
    case S.Asked{t}:
      {==}
    case S.Acked{t, r, s, ts}:
      {==}

def Lv.idle_owned(+p: S.Phase, +a: U32, +e: {S.Phase.idle(p) == True{} : Bool}) -> {S.Phase.owned_by(p, a) == True{} : Bool}:
  match p:
    case S.Handover{ctx, nh, source, leg}:
      Empty.absurd({S.Phase.owned_by(S.Handover{ctx, nh, source, leg}, a) == True{} : Bool}, P.Refute.bool(e))
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
    case S.Registered{ctx, nh, released}:
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

# An outcome puts no session (okf), or only sessions of contexts (ok); what it
# starts deleting it asks the UPF to delete under a guard it starts (Lv.arms).
# Every outcome, those that settle a session included, is okw.
# What an outcome's actions do, with f what its transaction writes.
def Lv.does(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, f: Bool) -> Bool:
  Bool.and(Lv.stops(tx, acts), Bool.and(Lv.seeds(st, tx, acts), Bool.and(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f))))

def Lv.okf(+st: S.State, +o: N.GOut()) -> Bool:
  Lv.does(st, N.Out.tx(o), N.Out.acts(o), Lv.free(st, N.Out.tx(o)))

def Lv.ok(+st: S.State, +o: N.GOut()) -> Bool:
  Lv.does(st, N.Out.tx(o), N.Out.acts(o), Lv.homed(st, N.Out.tx(o), S.State.ues(st)))

def Lv.okw(+st: S.State, +o: N.GOut()) -> Bool:
  Bool.and(Lv.actsw(st, N.Out.acts(o)), Lv.homedw(st, N.Out.tx(o), S.State.ues(st)))

# Composing outcomes
# ------------------

def Lv.does_intro(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +f: Bool, +hs: {Lv.stops(tx, acts) == True{} : Bool}, +hw: {Lv.seeds(st, tx, acts) == True{} : Bool}, +ha: {Lv.acts(st, acts) == True{} : Bool}, +hr: {Lv.arms(tx, acts) == True{} : Bool}, +hf: {f == True{} : Bool}) -> {Lv.does(st, tx, acts, f) == True{} : Bool}:
  +r = Bool.and(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f))
  P.Bool.and_intro(Lv.stops(tx, acts), Bool.and(Lv.seeds(st, tx, acts), r), hs, P.Bool.and_intro(Lv.seeds(st, tx, acts), r, hw, P.Bool.and_intro(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f), ha, P.Bool.and_intro(Lv.arms(tx, acts), f, hr, hf))))

def Lv.does_stops(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +f: Bool, +h: {Lv.does(st, tx, acts, f) == True{} : Bool}) -> {Lv.stops(tx, acts) == True{} : Bool}:
  P.Bool.and_true_l(Lv.stops(tx, acts), Bool.and(Lv.seeds(st, tx, acts), Bool.and(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f))), h)

def Lv.does_tail(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +f: Bool, +h: {Lv.does(st, tx, acts, f) == True{} : Bool}) -> {Bool.and(Lv.seeds(st, tx, acts), Bool.and(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f))) == True{} : Bool}:
  P.Bool.and_true_r(Lv.stops(tx, acts), Bool.and(Lv.seeds(st, tx, acts), Bool.and(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f))), h)

def Lv.does_seeds(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +f: Bool, +h: {Lv.does(st, tx, acts, f) == True{} : Bool}) -> {Lv.seeds(st, tx, acts) == True{} : Bool}:
  P.Bool.and_true_l(Lv.seeds(st, tx, acts), Bool.and(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f)), Lv.does_tail(st, tx, acts, f, h))

def Lv.does_mid(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +f: Bool, +h: {Lv.does(st, tx, acts, f) == True{} : Bool}) -> {Bool.and(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f)) == True{} : Bool}:
  P.Bool.and_true_r(Lv.seeds(st, tx, acts), Bool.and(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f)), Lv.does_tail(st, tx, acts, f, h))

def Lv.does_rest(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +f: Bool, +h: {Lv.does(st, tx, acts, f) == True{} : Bool}) -> {Bool.and(Lv.arms(tx, acts), f) == True{} : Bool}:
  P.Bool.and_true_r(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f), Lv.does_mid(st, tx, acts, f, h))

def Lv.does_acts(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +f: Bool, +h: {Lv.does(st, tx, acts, f) == True{} : Bool}) -> {Lv.acts(st, acts) == True{} : Bool}:
  P.Bool.and_true_l(Lv.acts(st, acts), Bool.and(Lv.arms(tx, acts), f), Lv.does_mid(st, tx, acts, f, h))

def Lv.does_arms(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +f: Bool, +h: {Lv.does(st, tx, acts, f) == True{} : Bool}) -> {Lv.arms(tx, acts) == True{} : Bool}:
  P.Bool.and_true_l(Lv.arms(tx, acts), f, Lv.does_rest(st, tx, acts, f, h))

def Lv.does_f(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +f: Bool, +h: {Lv.does(st, tx, acts, f) == True{} : Bool}) -> {f == True{} : Bool}:
  P.Bool.and_true_r(Lv.arms(tx, acts), f, Lv.does_rest(st, tx, acts, f, h))

def Lv.free_homed(+st: S.State, +tx: S.Tx, +ues: Tb.Table(S.Ue), +e: {Lv.free(st, tx) == True{} : Bool}) -> {Lv.homed(st, tx, ues) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      {==}
    case S.Put{+key, +ue}:
      +ef = P.Bool.and_true_r(Lv.chain_put(st, key, S.Phase.nh(S.Ue.phase(ue))), Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue)))), e)
      +r1 = P.Bool.and_true_r(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue))), ef)
      +r2 = P.Bool.and_true_r(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue)), r1)
      P.Bool.and_intro(Lv.chain_put(st, key, S.Phase.nh(S.Ue.phase(ue))), Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st, ue)))), P.Bool.and_true_l(Lv.chain_put(st, key, S.Phase.nh(S.Ue.phase(ue))), Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue)))), e), P.Bool.and_intro(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st, ue))), P.Bool.and_true_l(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue))), ef), P.Bool.and_intro(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st, ue)), P.Bool.and_true_l(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue)), r1), P.Bool.and_intro(S.Ue.single(ue), Lv.home(st, ue), Lv.idle_owned(S.Ue.phase(ue), S.Ue.assoc(ue), P.Bool.and_true_l(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue), r2)), P.Bool.and_true_r(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue), r2)))))
    case S.Rephase{+key, +phase}:
      +c = Lv.chain(st, key, S.Phase.nh(phase))
      +ef = P.Bool.and_true_r(c, Bool.and(S.Phase.guarded(phase), S.Phase.idle(phase)), e)
      P.Bool.and_intro(c, Bool.and(S.Phase.guarded(phase), S.Ue.fits(phase, Tb.Table.get(S.Ue, key, ues))), P.Bool.and_true_l(c, Bool.and(S.Phase.guarded(phase), S.Phase.idle(phase)), e), P.Bool.and_intro(S.Phase.guarded(phase), S.Ue.fits(phase, Tb.Table.get(S.Ue, key, ues)), P.Bool.and_true_l(S.Phase.guarded(phase), S.Phase.idle(phase), ef), Lv.idle_fits(phase, Tb.Table.get(S.Ue, key, ues), P.Bool.and_true_r(S.Phase.guarded(phase), S.Phase.idle(phase), ef))))
    case S.Del{key}:
      {==}
    case S.PutSession{key, +s}:
      Empty.absurd({Lv.homed(st, S.PutSession{key, s}, ues) == True{} : Bool}, P.Refute.bool(e))
    case S.Revar{key, v}:
      e
    case S.DelSession{key}:
      e
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

# A free transaction writes no pending phase.
def Lv.free_calm(+st: S.State, +tx: S.Tx, +e: {Lv.free(st, tx) == True{} : Bool}) -> {Lv.calm(tx) == True{} : Bool}:
  match tx:
    case S.Put{+key, +ue}:
      +ef = P.Bool.and_true_r(Lv.chain_put(st, key, S.Phase.nh(S.Ue.phase(ue))), Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue)))), e)
      P.Bool.and_true_l(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue), P.Bool.and_true_r(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue)), P.Bool.and_true_r(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Phase.idle(S.Ue.phase(ue)), Lv.home(st, ue))), ef)))
    case S.Rephase{+key, +phase}:
      P.Bool.and_true_r(S.Phase.guarded(phase), S.Phase.idle(phase), P.Bool.and_true_r(Lv.chain(st, key, S.Phase.nh(phase)), Bool.and(S.Phase.guarded(phase), S.Phase.idle(phase)), e))
    case S.Both{+a, +b}:
      P.Bool.and_intro(Lv.calm(a), Lv.calm(b), Lv.free_calm(st, a, P.Bool.and_true_l(Lv.free(st, a), Lv.free(st, b), e)), Lv.free_calm(st, b, P.Bool.and_true_r(Lv.free(st, a), Lv.free(st, b), e)))
    case S.PutSession{key, s}:
      Empty.absurd({Lv.calm(S.PutSession{key, s}) == True{} : Bool}, P.Refute.bool(e))
    case S.Keep{}:
      {==}
    case S.Del{key}:
      {==}
    case S.Revar{key, v}:
      {==}
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

def Lv.okf_acts(+st: S.State, +o: N.GOut(), +h: {Lv.okf(st, o) == True{} : Bool}) -> {Lv.acts(st, N.Out.acts(o)) == True{} : Bool}:
  Lv.does_acts(st, N.Out.tx(o), N.Out.acts(o), Lv.free(st, N.Out.tx(o)), h)

def Lv.okf_free(+st: S.State, +o: N.GOut(), +h: {Lv.okf(st, o) == True{} : Bool}) -> {Lv.free(st, N.Out.tx(o)) == True{} : Bool}:
  Lv.does_f(st, N.Out.tx(o), N.Out.acts(o), Lv.free(st, N.Out.tx(o)), h)

def Lv.okf_arms(+st: S.State, +o: N.GOut(), +h: {Lv.okf(st, o) == True{} : Bool}) -> {Lv.arms(N.Out.tx(o), N.Out.acts(o)) == True{} : Bool}:
  Lv.does_arms(st, N.Out.tx(o), N.Out.acts(o), Lv.free(st, N.Out.tx(o)), h)

def Lv.ok_acts(+st: S.State, +o: N.GOut(), +h: {Lv.ok(st, o) == True{} : Bool}) -> {Lv.acts(st, N.Out.acts(o)) == True{} : Bool}:
  Lv.does_acts(st, N.Out.tx(o), N.Out.acts(o), Lv.homed(st, N.Out.tx(o), S.State.ues(st)), h)

def Lv.ok_arms(+st: S.State, +o: N.GOut(), +h: {Lv.ok(st, o) == True{} : Bool}) -> {Lv.arms(N.Out.tx(o), N.Out.acts(o)) == True{} : Bool}:
  Lv.does_arms(st, N.Out.tx(o), N.Out.acts(o), Lv.homed(st, N.Out.tx(o), S.State.ues(st)), h)

def Lv.ok_homed(+st: S.State, +o: N.GOut(), +h: {Lv.ok(st, o) == True{} : Bool}) -> {Lv.homed(st, N.Out.tx(o), S.State.ues(st)) == True{} : Bool}:
  Lv.does_f(st, N.Out.tx(o), N.Out.acts(o), Lv.homed(st, N.Out.tx(o), S.State.ues(st)), h)

def Lv.ok_seeds(+st: S.State, +o: N.GOut(), +h: {Lv.ok(st, o) == True{} : Bool}) -> {Lv.seeds(st, N.Out.tx(o), N.Out.acts(o)) == True{} : Bool}:
  Lv.does_seeds(st, N.Out.tx(o), N.Out.acts(o), Lv.homed(st, N.Out.tx(o), S.State.ues(st)), h)

def Lv.ok_stops(+st: S.State, +o: N.GOut(), +h: {Lv.ok(st, o) == True{} : Bool}) -> {Lv.stops(N.Out.tx(o), N.Out.acts(o)) == True{} : Bool}:
  Lv.does_stops(st, N.Out.tx(o), N.Out.acts(o), Lv.homed(st, N.Out.tx(o), S.State.ues(st)), h)

# An outcome that puts no session is ok whatever contexts it runs on.
def Lv.ok_in(+st: S.State, +o: N.GOut(), +ues: Tb.Table(S.Ue), +h: {Lv.okf(st, o) == True{} : Bool}) -> {Lv.does(st, N.Out.tx(o), N.Out.acts(o), Lv.homed(st, N.Out.tx(o), ues)) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      +f = Lv.free(st, tx)
      Lv.does_intro(st, tx, acts, Lv.homed(st, tx, ues), Lv.does_stops(st, tx, acts, f, h), Lv.does_seeds(st, tx, acts, f, h), Lv.does_acts(st, tx, acts, f, h), Lv.does_arms(st, tx, acts, f, h), Lv.free_homed(st, tx, ues, Lv.does_f(st, tx, acts, f, h)))

def Lv.ok_of(+st: S.State, +o: N.GOut(), +h: {Lv.okf(st, o) == True{} : Bool}) -> {Lv.ok(st, o) == True{} : Bool}:
  Lv.ok_in(st, o, S.State.ues(st), h)

# What every outcome but a deletion's own guard or answer keeps holds of those too.
def Lv.weak(+st: S.State, +tx: S.Tx, +ues: Tb.Table(S.Ue), +h: {Lv.homed(st, tx, ues) == True{} : Bool}) -> {Lv.homedw(st, tx, ues) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      {==}
    case S.Put{+key, +ue}:
      P.Bool.and_true_r(Lv.chain_put(st, key, S.Phase.nh(S.Ue.phase(ue))), Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st, ue)))), h)
    case S.Rephase{+key, +phase}:
      P.Bool.and_true_r(Lv.chain(st, key, S.Phase.nh(phase)), Bool.and(S.Phase.guarded(phase), S.Ue.fits(phase, Tb.Table.get(S.Ue, key, ues))), h)
    case S.Del{key}:
      {==}
    case S.PutSession{+key, +s}:
      P.Bool.and_true_r(Lv.clear(key, s, S.State.sessions(st)), Lv.puts(key, s, ues), h)
    case S.Revar{+key, +v}:
      P.Bool.and_true_r(Lv.spare(st, key, v), Lv.revar_ok(st, v), h)
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
      P.Bool.and_intro(Lv.homedw(st, a, ues), Lv.homedw(st, b, PT.Tk.ues(a, ues)), Lv.weak(st, a, ues, P.Bool.and_true_l(Lv.homed(st, a, ues), Lv.homed(st, b, PT.Tk.ues(a, ues)), h)), Lv.weak(st, b, PT.Tk.ues(a, ues), P.Bool.and_true_r(Lv.homed(st, a, ues), Lv.homed(st, b, PT.Tk.ues(a, ues)), h)))

def Lv.cons(+st: S.State, +a: N.Act, +more: List<&2, N.Act>, +ha: {Lv.act(st, a) == True{} : Bool}, +hm: {Lv.acts(st, more) == True{} : Bool}) -> {Lv.acts(st, a <> more) == True{} : Bool}:
  P.Bool.and_intro(Lv.act(st, a), Lv.acts(st, more), ha, hm)

def Lv.append(+st: S.State, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {Lv.acts(st, xs) == True{} : Bool}, +hy: {Lv.acts(st, ys) == True{} : Bool}) -> {Lv.acts(st, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      Lv.cons(st, a, List.append(&2, N.Act, more, ys), P.Bool.and_true_l(Lv.act(st, a), Lv.acts(st, more), hx), Lv.append(st, more, ys, P.Bool.and_true_r(Lv.act(st, a), Lv.acts(st, more), hx), hy))

def Lv.appendw(+st: S.State, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {Lv.actsw(st, xs) == True{} : Bool}, +hy: {Lv.actsw(st, ys) == True{} : Bool}) -> {Lv.actsw(st, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      P.Bool.and_intro(Lv.actw(st, a), Lv.actsw(st, List.append(&2, N.Act, more, ys)), P.Bool.and_true_l(Lv.actw(st, a), Lv.actsw(st, more), hx), Lv.appendw(st, more, ys, P.Bool.and_true_r(Lv.actw(st, a), Lv.actsw(st, more), hx), hy))

# A guard a UE procedure starts: a context's, or for T1 a session's whose row
# it may change.
def Lv.ue_start(+st: S.State, +key: U32, +ms: U32, +eh: {Lv.held(st, key) == True{} : Bool}) -> {Lv.act(st, N.TimerStart{Some{key}, key, ms}) == True{} : Bool}:
  +s = Bool.and(Lv.kept(st, key), U32.is_eq(ms, Up.N4.t1_ms()))
  P.Bool.and_intro(Lv.live(st, key), Lv.timed(st, key, ms), P.Bool.or_l(Lv.held(st, key), Lv.owner(key, S.State.sessions(st)), eh), P.Bool.or_r(U32.is_eq(key, S.N4.timer()), Bool.or(Lv.held(st, key), s), P.Bool.or_l(Lv.held(st, key), s, eh)))

def Lv.s_start(+st: S.State, +m: Maybe<&2, U32>, +k: U32, +ht: {Lv.tag(st, m) == True{} : Bool}, +ek: {Lv.kept(st, k) == True{} : Bool}) -> {Lv.act(st, N.TimerStart{m, k, Up.N4.t1_ms()}) == True{} : Bool}:
  +s = Bool.and(Lv.kept(st, k), U32.is_eq(Up.N4.t1_ms(), Up.N4.t1_ms()))
  P.Bool.and_intro(Lv.tag(st, m), Lv.timed(st, k, Up.N4.t1_ms()), ht, P.Bool.or_r(U32.is_eq(k, S.N4.timer()), Bool.or(Lv.held(st, k), s), P.Bool.or_r(Lv.held(st, k), s, P.Bool.and_intro(Lv.kept(st, k), U32.is_eq(Up.N4.t1_ms(), Up.N4.t1_ms()), ek, {==}))))

def Lv.act_w(+st: S.State, +a: N.Act, +h: {Lv.act(st, a) == True{} : Bool}) -> {Lv.actw(st, a) == True{} : Bool}:
  match a:
    case N.TimerCancel{t}:
      {==}
    case N.DlNas{assoc, stream, key, ran_id, nas}:
      h
    case N.Ics{assoc, stream, key, ran_id, cfg, caps, k_gnb, nas}:
      h
    case N.PduSetup{assoc, stream, key, ran_id, psi, sst, nas, transfer}:
      h
    case N.Release{assoc, stream, key, ran_id, cause}:
      h
    case N.SwitchAck{assoc, stream, key, ran_id, caps, nh, switched, released, sst}:
      h
    case N.SwitchFail{assoc, stream, ue, amf, ran_id, psis, cause}:
      h
    case N.UeSend{assoc, stream, key, bytes}:
      h
    case N.ErrInd{assoc, cause}:
      h
    case N.Setup{assoc, answer}:
      h
    case N.Pfcp{ue, bytes}:
      h
    case N.Note{level, text}:
      h
    case N.TimerStart{+ue, +timer, +ms}:
      P.Bool.and_true_l(Lv.tag(st, ue), Lv.timed(st, timer, ms), h)

def Lv.acts_w(+st: S.State, +as: List<&2, N.Act>, +h: {Lv.acts(st, as) == True{} : Bool}) -> {Lv.actsw(st, as) == True{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case +a <> +more:
      P.Bool.and_intro(Lv.actw(st, a), Lv.actsw(st, more), Lv.act_w(st, a, P.Bool.and_true_l(Lv.act(st, a), Lv.acts(st, more), h)), Lv.acts_w(st, more, P.Bool.and_true_r(Lv.act(st, a), Lv.acts(st, more), h)))

def Lv.ok_w(+st: S.State, +o: N.GOut(), +h: {Lv.ok(st, o) == True{} : Bool}) -> {Lv.okw(st, o) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      P.Bool.and_intro(Lv.actsw(st, acts), Lv.homedw(st, tx, S.State.ues(st)), Lv.acts_w(st, acts, Lv.ok_acts(st, (tx, acts), h)), Lv.weak(st, tx, S.State.ues(st), Lv.ok_homed(st, (tx, acts), h)))

# An outcome of a PFCP answer is ok, or it settles a session: it stops the
# guard of a live row of the table first, then does only what a UE procedure
# may.
def Lv.lead(+st: S.State, +tx: S.Tx, +a: N.Act, +more: List<&2, N.Act>) -> Bool:
  match a:
    case N.TimerCancel{+k}:
      Bool.and(Lv.kept(st, k), Bool.and(Tb.Table.has(S.Session, k, S.State.sessions(st)), Lv.ok(st, (tx, more))))
    case _:
      False{}

def Lv.settles(+st: S.State, +tx: S.Tx, acts: List<&2, N.Act>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case +a <> +more:
      Lv.lead(st, tx, a, more)

def Lv.fine(+st: S.State, +o: N.GOut()) -> Bool:
  Bool.or(Lv.ok(st, o), Lv.settles(st, N.Out.tx(o), N.Out.acts(o)))

def Lv.ok_fine(+st: S.State, +o: N.GOut(), +h: {Lv.ok(st, o) == True{} : Bool}) -> {Lv.fine(st, o) == True{} : Bool}:
  P.Bool.or_l(Lv.ok(st, o), Lv.settles(st, N.Out.tx(o), N.Out.acts(o)), h)

def Lv.okf_fine(+st: S.State, +o: N.GOut(), +h: {Lv.okf(st, o) == True{} : Bool}) -> {Lv.fine(st, o) == True{} : Bool}:
  Lv.ok_fine(st, o, Lv.ok_of(st, o, h))

# The row a session the UPF answered was found under settles with its guard stopped.
def Lv.settled(+st: S.State, +k: U32, +u: B.Bytes(), +q: U32, +b: N.GOut(), +ek: {Lv.kept(st, k) == True{} : Bool}, +eh: {Tb.Table.has(S.Session, k, S.State.sessions(st)) == True{} : Bool}, +hv: {Lv.revar_ok(st, S.SVar{u, q, S.Active{}}) == True{} : Bool}, +hb: {Lv.ok(st, b) == True{} : Bool}) -> {Lv.fine(st, N.Out.join((S.Revar{k, S.SVar{u, q, S.Active{}}}, [N.TimerCancel{k}]), b)) == True{} : Bool}:
  match b:
    case (+tb, +ab):
      +ues = S.State.ues(st)
      +r : S.Tx = S.Revar{k, S.SVar{u, q, S.Active{}}}
      +fb = Lv.homed(st, tb, ues)
      +ho = Lv.does_intro(st, S.Both{r, tb}, ab, Lv.homed(st, S.Both{r, tb}, ues), Lv.stops_r(r, tb, ab, Lv.does_stops(st, tb, ab, fb, hb)), Lv.does_seeds(st, tb, ab, fb, hb), Lv.does_acts(st, tb, ab, fb, hb), Lv.does_arms(st, tb, ab, fb, hb), P.Bool.and_intro(Lv.revar_ok(st, S.SVar{u, q, S.Active{}}), fb, hv, Lv.does_f(st, tb, ab, fb, hb)))
      P.Bool.or_r(Lv.ok(st, (S.Both{r, tb}, N.TimerCancel{k} <> ab)), Lv.settles(st, S.Both{r, tb}, N.TimerCancel{k} <> ab), P.Bool.and_intro(Lv.kept(st, k), Bool.and(Tb.Table.has(S.Session, k, S.State.sessions(st)), Lv.ok(st, (S.Both{r, tb}, ab))), ek, P.Bool.and_intro(Tb.Table.has(S.Session, k, S.State.sessions(st)), Lv.ok(st, (S.Both{r, tb}, ab)), eh, ho)))

# What an outcome's actions say of the deletions it starts stays said with
# more actions on either side.
def Lv.starts_l(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.starts(k, xs) == True{} : Bool}) -> {N.Acts.starts(k, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, [], ys)) == True{} : Bool}, P.Refute.bool(h))
    case +a <> +more:
      P.Bool.or_mono(N.Act.starts(k, a), N.Acts.starts(k, more), N.Acts.starts(k, List.append(&2, N.Act, more, ys)), h, hm => Lv.starts_l(k, more, ys, hm))

def Lv.starts_for_l(+k: U32, +ms: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.starts_for(k, ms, xs) == True{} : Bool}) -> {N.Acts.starts_for(k, ms, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({N.Acts.starts_for(k, ms, List.append(&2, N.Act, [], ys)) == True{} : Bool}, P.Refute.bool(h))
    case +a <> +more:
      P.Bool.or_mono(N.Act.starts_for(k, ms, a), N.Acts.starts_for(k, ms, more), N.Acts.starts_for(k, ms, List.append(&2, N.Act, more, ys)), h, hm => Lv.starts_for_l(k, ms, more, ys, hm))

def Lv.starts_for_r(+k: U32, +ms: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.starts_for(k, ms, ys) == True{} : Bool}) -> {N.Acts.starts_for(k, ms, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +a <> +more:
      P.Bool.or_r(N.Act.starts_for(k, ms, a), N.Acts.starts_for(k, ms, List.append(&2, N.Act, more, ys)), Lv.starts_for_r(k, ms, more, ys, h))

def Lv.sends_l(+r: B.Bytes(), +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.sends(r, xs) == True{} : Bool}) -> {N.Acts.sends(r, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({N.Acts.sends(r, List.append(&2, N.Act, [], ys)) == True{} : Bool}, P.Refute.bool(h))
    case +a <> +more:
      P.Bool.or_mono(N.Act.sends(r, a), N.Acts.sends(r, more), N.Acts.sends(r, List.append(&2, N.Act, more, ys)), h, hm => Lv.sends_l(r, more, ys, hm))

def Lv.sends_r(+r: B.Bytes(), +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.sends(r, ys) == True{} : Bool}) -> {N.Acts.sends(r, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +a <> +more:
      P.Bool.or_r(N.Act.sends(r, a), N.Acts.sends(r, List.append(&2, N.Act, more, ys)), Lv.sends_r(r, more, ys, h))

def Lv.arms_pl(+k: U32, +p: S.SPhase, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Lv.arms_p(k, p, xs) == True{} : Bool}) -> {Lv.arms_p(k, p, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match p:
    case S.Deleting{+guard, +request}:
      +z = U32.is_eq(S.Guard.retries(guard), 0)
      +hr = P.Bool.and_true_r(z, Bool.and(N.Acts.sends(request, xs), N.Acts.starts_for(k, Up.N4.t1_ms(), xs)), h)
      P.Bool.and_intro(z, Bool.and(N.Acts.sends(request, List.append(&2, N.Act, xs, ys)), N.Acts.starts_for(k, Up.N4.t1_ms(), List.append(&2, N.Act, xs, ys))), P.Bool.and_true_l(z, Bool.and(N.Acts.sends(request, xs), N.Acts.starts_for(k, Up.N4.t1_ms(), xs)), h), P.Bool.and_intro(N.Acts.sends(request, List.append(&2, N.Act, xs, ys)), N.Acts.starts_for(k, Up.N4.t1_ms(), List.append(&2, N.Act, xs, ys)), Lv.sends_l(request, xs, ys, P.Bool.and_true_l(N.Acts.sends(request, xs), N.Acts.starts_for(k, Up.N4.t1_ms(), xs), hr)), Lv.starts_for_l(k, Up.N4.t1_ms(), xs, ys, P.Bool.and_true_r(N.Acts.sends(request, xs), N.Acts.starts_for(k, Up.N4.t1_ms(), xs), hr))))
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Lv.arms_pr(+k: U32, +p: S.SPhase, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Lv.arms_p(k, p, ys) == True{} : Bool}) -> {Lv.arms_p(k, p, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match p:
    case S.Deleting{+guard, +request}:
      +z = U32.is_eq(S.Guard.retries(guard), 0)
      +hr = P.Bool.and_true_r(z, Bool.and(N.Acts.sends(request, ys), N.Acts.starts_for(k, Up.N4.t1_ms(), ys)), h)
      P.Bool.and_intro(z, Bool.and(N.Acts.sends(request, List.append(&2, N.Act, xs, ys)), N.Acts.starts_for(k, Up.N4.t1_ms(), List.append(&2, N.Act, xs, ys))), P.Bool.and_true_l(z, Bool.and(N.Acts.sends(request, ys), N.Acts.starts_for(k, Up.N4.t1_ms(), ys)), h), P.Bool.and_intro(N.Acts.sends(request, List.append(&2, N.Act, xs, ys)), N.Acts.starts_for(k, Up.N4.t1_ms(), List.append(&2, N.Act, xs, ys)), Lv.sends_r(request, xs, ys, P.Bool.and_true_l(N.Acts.sends(request, ys), N.Acts.starts_for(k, Up.N4.t1_ms(), ys), hr)), Lv.starts_for_r(k, Up.N4.t1_ms(), xs, ys, P.Bool.and_true_r(N.Acts.sends(request, ys), N.Acts.starts_for(k, Up.N4.t1_ms(), ys), hr))))
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Lv.arms_l(+tx: S.Tx, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Lv.arms(tx, xs) == True{} : Bool}) -> {Lv.arms(tx, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match tx:
    case S.Revar{+key, +v}:
      Lv.arms_pl(key, S.SVar.phase(v), xs, ys, h)
    case S.PutSession{key, s}:
      h
    case S.Both{+a, +b}:
      P.Bool.and_intro(Lv.arms(a, List.append(&2, N.Act, xs, ys)), Lv.arms(b, List.append(&2, N.Act, xs, ys)), Lv.arms_l(a, xs, ys, P.Bool.and_true_l(Lv.arms(a, xs), Lv.arms(b, xs), h)), Lv.arms_l(b, xs, ys, P.Bool.and_true_r(Lv.arms(a, xs), Lv.arms(b, xs), h)))
    case S.Keep{}:
      {==}
    case S.Put{key, ue}:
      {==}
    case S.Rephase{key, phase}:
      {==}
    case S.Del{key}:
      {==}
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

def Lv.arms_r(+tx: S.Tx, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Lv.arms(tx, ys) == True{} : Bool}) -> {Lv.arms(tx, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match tx:
    case S.Revar{+key, +v}:
      Lv.arms_pr(key, S.SVar.phase(v), xs, ys, h)
    case S.PutSession{key, s}:
      h
    case S.Both{+a, +b}:
      P.Bool.and_intro(Lv.arms(a, List.append(&2, N.Act, xs, ys)), Lv.arms(b, List.append(&2, N.Act, xs, ys)), Lv.arms_r(a, xs, ys, P.Bool.and_true_l(Lv.arms(a, ys), Lv.arms(b, ys), h)), Lv.arms_r(b, xs, ys, P.Bool.and_true_r(Lv.arms(a, ys), Lv.arms(b, ys), h)))
    case S.Keep{}:
      {==}
    case S.Put{key, ue}:
      {==}
    case S.Rephase{key, phase}:
      {==}
    case S.Del{key}:
      {==}
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

def Lv.leaf(+st: S.State, +tx: S.Tx, +as: List<&2, N.Act>, +ha: {Lv.acts(st, as) == True{} : Bool}, +hf: {Bool.and(Lv.arms(tx, as), Lv.free(st, tx)) == True{} : Bool}, +hs: {Lv.stops(tx, as) == True{} : Bool}, +hw: {Lv.seeds(st, tx, as) == True{} : Bool}) -> {Lv.okf(st, (tx, as)) == True{} : Bool}:
  Lv.does_intro(st, tx, as, Lv.free(st, tx), hs, hw, ha, P.Bool.and_true_l(Lv.arms(tx, as), Lv.free(st, tx), hf), P.Bool.and_true_r(Lv.arms(tx, as), Lv.free(st, tx), hf))

def Lv.prepend(+st: S.State, +a: N.Act, +o: N.GOut(), +ha: {Lv.act(st, a) == True{} : Bool}, +h: {Lv.okf(st, o) == True{} : Bool}, +hs: {Lv.stop(N.Out.tx(o), Lv.cancelled(a)) == True{} : Bool}) -> {Lv.okf(st, N.Out.prepend(a, o)) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      +f = Lv.free(st, tx)
      +hr = Lv.does_rest(st, tx, acts, f, h)
      Lv.leaf(st, tx, a <> acts, Lv.cons(st, a, acts, ha, Lv.does_acts(st, tx, acts, f, h)), P.Bool.and_intro(Lv.arms(tx, a <> acts), f, Lv.arms_r(tx, [a], acts, P.Bool.and_true_l(Lv.arms(tx, acts), f, hr)), P.Bool.and_true_r(Lv.arms(tx, acts), f, hr)), Lv.stops_cons(tx, a, acts, hs, Lv.does_stops(st, tx, acts, f, h)), Lv.seeds_r(st, tx, [a], acts, Lv.does_seeds(st, tx, acts, f, h)))

def Lv.also(+st: S.State, +o: N.GOut(), +more: List<&2, N.Act>, +h: {Lv.okf(st, o) == True{} : Bool}, +hm: {Lv.acts(st, more) == True{} : Bool}, +hs: {Lv.stops(N.Out.tx(o), more) == True{} : Bool}) -> {Lv.okf(st, N.Out.also(o, more)) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      +f = Lv.free(st, tx)
      +hr = Lv.does_rest(st, tx, acts, f, h)
      Lv.leaf(st, tx, List.append(&2, N.Act, acts, more), Lv.append(st, acts, more, Lv.does_acts(st, tx, acts, f, h), hm), P.Bool.and_intro(Lv.arms(tx, List.append(&2, N.Act, acts, more)), f, Lv.arms_l(tx, acts, more, P.Bool.and_true_l(Lv.arms(tx, acts), f, hr)), P.Bool.and_true_r(Lv.arms(tx, acts), f, hr)), Lv.stops_app(tx, acts, more, Lv.does_stops(st, tx, acts, f, h), hs), Lv.seeds_l(st, tx, acts, more, Lv.does_seeds(st, tx, acts, f, h)))

# Two outcomes in order: what holds of each holds of both, the second calm.
def Lv.both(+st: S.State, +ta: S.Tx, +aa: List<&2, N.Act>, +tb: S.Tx, +ab: List<&2, N.Act>, +fa: Bool, +fb: Bool, +ha: {Lv.does(st, ta, aa, fa) == True{} : Bool}, +hb: {Lv.does(st, tb, ab, fb) == True{} : Bool}, +hc: {Lv.calm(tb) == True{} : Bool}) -> {Lv.does(st, S.Both{ta, tb}, List.append(&2, N.Act, aa, ab), Bool.and(fa, fb)) == True{} : Bool}:
  +ra = Lv.does_rest(st, ta, aa, fa, ha)
  +rb = Lv.does_rest(st, tb, ab, fb, hb)
  +xs = List.append(&2, N.Act, aa, ab)
  Lv.does_intro(st, S.Both{ta, tb}, xs, Bool.and(fa, fb), Lv.stops_app(S.Both{ta, tb}, aa, ab, Lv.stops_l(ta, tb, aa, Lv.does_stops(st, ta, aa, fa, ha), hc), Lv.stops_r(ta, tb, ab, Lv.does_stops(st, tb, ab, fb, hb))), P.Bool.and_intro(Lv.seeds(st, ta, xs), Lv.seeds(st, tb, xs), Lv.seeds_l(st, ta, aa, ab, Lv.does_seeds(st, ta, aa, fa, ha)), Lv.seeds_r(st, tb, aa, ab, Lv.does_seeds(st, tb, ab, fb, hb))), Lv.append(st, aa, ab, Lv.does_acts(st, ta, aa, fa, ha), Lv.does_acts(st, tb, ab, fb, hb)), P.Bool.and_intro(Lv.arms(ta, xs), Lv.arms(tb, xs), Lv.arms_l(ta, aa, ab, P.Bool.and_true_l(Lv.arms(ta, aa), fa, ra)), Lv.arms_r(tb, aa, ab, P.Bool.and_true_l(Lv.arms(tb, ab), fb, rb))), P.Bool.and_intro(fa, fb, P.Bool.and_true_r(Lv.arms(ta, aa), fa, ra), P.Bool.and_true_r(Lv.arms(tb, ab), fb, rb)))

def Lv.join(+st: S.State, +a: N.GOut(), +b: N.GOut(), +ha: {Lv.okf(st, a) == True{} : Bool}, +hb: {Lv.okf(st, b) == True{} : Bool}) -> {Lv.okf(st, N.Out.join(a, b)) == True{} : Bool}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          Lv.both(st, ta, aa, tb, ab, Lv.free(st, ta), Lv.free(st, tb), ha, hb, Lv.free_calm(st, tb, Lv.does_f(st, tb, ab, Lv.free(st, tb), hb)))

def Lv.ojoin(+st: S.State, +a: N.GOut(), +b: N.GOut(), +ues: Tb.Table(S.Ue), +ha: {Lv.does(st, N.Out.tx(a), N.Out.acts(a), Lv.homed(st, N.Out.tx(a), ues)) == True{} : Bool}, +hb: {Lv.does(st, N.Out.tx(b), N.Out.acts(b), Lv.homed(st, N.Out.tx(b), PT.Tk.ues(N.Out.tx(a), ues))) == True{} : Bool}, +hc: {Lv.calm(N.Out.tx(b)) == True{} : Bool}) -> {Lv.does(st, N.Out.tx(N.Out.join(a, b)), N.Out.acts(N.Out.join(a, b)), Lv.homed(st, N.Out.tx(N.Out.join(a, b)), ues)) == True{} : Bool}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          Lv.both(st, ta, aa, tb, ab, Lv.homed(st, ta, ues), Lv.homed(st, tb, PT.Tk.ues(ta, ues)), ha, hb, hc)

def Lv.cancel(+st: S.State, +key: U32, +g: Maybe<&2, S.Guard>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}) -> {Lv.acts(st, N.Guard.cancel(key, g)) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{guard}:
      P.Bool.and_intro(Lv.act(st, N.TimerCancel{key}), True{}, eh, {==})

# Guards
# ------
# A context put takes a phase of its own, and a NAS context replaced keeps the
# phase, which holds one only from Security Mode on.

def Lv.p_phase(+u: S.Ue, +p: S.Phase) -> {S.Ue.phase(S.Ue.with_phase(u, p)) == p : S.Phase}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.g_phase(+u: S.Ue, +p: S.Phase) -> {S.Phase.guarded(S.Ue.phase(S.Ue.with_phase(u, p))) == S.Phase.guarded(p) : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.s_phase(+u: S.Ue, +p: S.Phase) -> {S.Ue.single(S.Ue.with_phase(u, p)) == S.Phase.owned_by(p, S.Ue.assoc(u)) : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.p_moved(+u: S.Ue, +a: U32, +r: B.Bytes(), +s: U32, +p: S.Phase) -> {S.Ue.phase(S.Ue.moved(u, a, r, s, p)) == p : S.Phase}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.p_dl(+u: S.Ue, +p: S.Phase, +dl: B.Bytes()) -> {S.Ue.phase(S.Ue.with_dl(u, p, dl)) == p : S.Phase}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Lv.p_ics(+u: S.Ue, +p: S.Phase, +dl: B.Bytes(), +r: B.Bytes(), +t: U32) -> {S.Ue.phase(S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(u, p, dl), r), t)) == p : S.Phase}:
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
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Handover{ctx, nh, source, leg}:
      Empty.absurd({Bool.and(S.Phase.guarded(S.Phase.with_ctx(S.Handover{ctx, nh, source, leg}, c)), S.Phase.idle(S.Phase.with_ctx(S.Handover{ctx, nh, source, leg}, c))) == True{} : Bool}, P.Refute.bool(e))
    case S.Releasing{guard}:
      Empty.absurd({Bool.and(S.Phase.guarded(S.Phase.with_ctx(S.Releasing{guard}, c)), S.Phase.idle(S.Phase.with_ctx(S.Releasing{guard}, c))) == True{} : Bool}, P.Refute.bool(e))

def Lv.has_ctx(+p: S.Phase, +c: Sec.Nas.Ctx, +e: {S.Phase.ctx(p) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}) -> {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(p)) == True{} : Bool}:
  se = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.ctx(p), Some{c}, e)
  %se : {Tb.Table.present(Sec.Nas.Ctx, _) == True{} : Bool}
  {==}

# Live keys
# ---------

def Lv.held_live(+st: S.State, +x: U32, +e: {Lv.held(st, x) == True{} : Bool}) -> {Lv.live(st, x) == True{} : Bool}:
  P.Bool.or_l(Lv.held(st, x), Lv.owner(x, S.State.sessions(st)), e)

def Lv.has_held(+st: S.State, +x: U32, +e: {Tb.Table.has(S.Ue, x, S.State.ues(st)) == True{} : Bool}) -> {Lv.held(st, x) == True{} : Bool}:
  P.Bool.or_l(Tb.Table.has(S.Ue, x, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{x}), e)

def Lv.has_live(+st: S.State, +x: U32, +e: {Tb.Table.has(S.Ue, x, S.State.ues(st)) == True{} : Bool}) -> {Lv.live(st, x) == True{} : Bool}:
  P.Bool.or_l(Lv.held(st, x), Lv.owner(x, S.State.sessions(st)), P.Bool.or_l(Tb.Table.has(S.Ue, x, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{x}), e))

def Lv.owner_live(+st: S.State, +x: U32, +e: {Lv.owner(x, S.State.sessions(st)) == True{} : Bool}) -> {Lv.live(st, x) == True{} : Bool}:
  P.Bool.or_r(Lv.held(st, x), Lv.owner(x, S.State.sessions(st)), e)

def Lv.fresh_held(+st: S.State, +key: U32, +em: {S.State.fresh(st) == Some{key} : Maybe<&2, U32>}) -> {Lv.held(st, key) == True{} : Bool}:
  sem = Equal.sym(Maybe<&2, U32>, S.State.fresh(st), Some{key}, em)
  ef : {S.Maybe.same_u32(S.State.fresh(st), Some{key}) == True{} : Bool} = (%sem : {S.Maybe.same_u32(_, Some{key}) == True{} : Bool}; P.U32.is_eq_refl(key))
  P.Bool.or_r(Tb.Table.has(S.Ue, key, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{key}), ef)

def Lv.owner_row(+x: U32, +t: S.Session, +more: Tb.Table(S.Session), +ues: Tb.Table(S.Ue), +b: Bool, +eb: {S.Maybe.same_u32(S.Session.tag(t), Some{x}) == b : Bool}, +eo: {Bool.and(S.Session.owned(t, ues), S.Sessions.owned(more, ues)) == True{} : Bool}, +ew: {Bool.or(b, Lv.owner(x, more)) == True{} : Bool}, ih: {S.Sessions.owned(more, ues) == True{} : Bool} -> {Lv.owner(x, more) == True{} : Bool} -> {Tb.Table.has(S.Ue, x, ues) == True{} : Bool}) -> {Tb.Table.has(S.Ue, x, ues) == True{} : Bool}:
  match b:
    case True{}:
      PW.Tg.has(t, x, ues, eb, P.Bool.and_true_l(S.Session.owned(t, ues), S.Sessions.owned(more, ues), eo))
    case False{}:
      ih(P.Bool.and_true_r(S.Session.owned(t, ues), S.Sessions.owned(more, ues), eo), ew)

# With every session owned, a UE that owns a session holds a context.
def Lv.owner_has(+x: U32, +ss: Tb.Table(S.Session), +ues: Tb.Table(S.Ue), +eo: {S.Sessions.owned(ss, ues) == True{} : Bool}, +ew: {Lv.owner(x, ss) == True{} : Bool}) -> {Tb.Table.has(S.Ue, x, ues) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({Tb.Table.has(S.Ue, x, ues) == True{} : Bool}, P.Refute.bool(ew))
    case (k, +t) <> +more:
      Lv.owner_row(x, t, more, ues, S.Maybe.same_u32(S.Session.tag(t), Some{x}), {==}, eo, ew, a => b => Lv.owner_has(x, more, ues, a, b))

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
          P.Bool.contra({Lv.keyed(st, x) == True{} : Bool}, Lv.held(st, x), hh, eh)

def Lv.keyed_of(+st: S.State, +x: U32, +ek: {Lv.live(st, x) == True{} : Bool}) -> {Lv.keyed(st, x) == True{} : Bool}:
  Lv.kd(st, x, Lv.held(st, x), {==}, S.Sessions.owned(S.State.sessions(st), S.State.ues(st)), {==}, ek)

def Lv.get_has(+ues: Tb.Table(S.Ue), +key: U32, +ue: S.Ue, +e: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>}) -> {Tb.Table.has(S.Ue, key, ues) == True{} : Bool}:
  se = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, ues), Some{ue}, e)
  %se : {Tb.Table.present(S.Ue, _) == True{} : Bool}
  {==}

# The context an owner check finds holds its key.
def Lv.owned_get(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +ue: S.Ue, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}:
  PW.Walk.first({Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}, PT.Own.get(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran, ue, eo))

def Lv.owned_has(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +ue: S.Ue, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}:
  Lv.get_has(S.State.ues(st), key, ue, Lv.owned_get(st, assoc, key, ran, ue, eo))

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

def Lv.keys_sift(+s: S.Sieve, +ues: Tb.Table(S.Ue)) -> {Lv.keys_in(S.Ues.sift(s, ues), ues) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      P.Keep.by(S.Ue, tb => {Lv.keys_in(tb, (k, v) <> more) == True{} : Bool}, k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), e => h => P.Bool.and_intro(Tb.Table.has(S.Ue, k, (k, v) <> more), Lv.keys_in(S.Ues.sift(s, more), (k, v) <> more), Lv.has_head(k, v, more), h), Lv.keys_cons(S.Ues.sift(s, more), k, v, more, Lv.keys_sift(s, more)))

def Lv.owner_cons(+x: U32, +k: U32, +t: S.Session, +more: Tb.Table(S.Session), +e: {Lv.owner(x, more) == True{} : Bool}) -> {Lv.owner(x, (k, t) <> more) == True{} : Bool}:
  P.Bool.or_r(S.Maybe.same_u32(S.Session.tag(t), Some{x}), Lv.owner(x, more), e)

def Lv.tagged_cons(+m: Maybe<&2, U32>, +k: U32, +t: S.Session, +more: Tb.Table(S.Session), +e: {Lv.tagged(m, more) == True{} : Bool}) -> {Lv.tagged(m, (k, t) <> more) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      Lv.owner_cons(x, k, t, more, e)

def Lv.tagged_at(+m: Maybe<&2, U32>, +k: U32, +t: S.Session, +more: Tb.Table(S.Session), +em: {S.Session.tag(t) == m : Maybe<&2, U32>}) -> {Lv.tagged(m, (k, t) <> more) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      sem = Equal.sym(Maybe<&2, U32>, S.Session.tag(t), Some{x}, em)
      P.Bool.or_l(S.Maybe.same_u32(S.Session.tag(t), Some{x}), Lv.owner(x, more), (%sem : {S.Maybe.same_u32(_, Some{x}) == True{} : Bool}; P.U32.is_eq_refl(x)))

def Lv.tagged_head(+k: U32, +t: S.Session, +more: Tb.Table(S.Session)) -> {Lv.tagged(S.Session.tag(t), (k, t) <> more) == True{} : Bool}:
  Lv.tagged_at(S.Session.tag(t), k, t, more, {==})

# A row's tag is live in the state whose table it is a row of.
def Lv.tagged_live(+st: S.State, +m: Maybe<&2, U32>, +e: {Lv.tagged(m, S.State.sessions(st)) == True{} : Bool}) -> {Lv.tag(st, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      Lv.owner_live(st, x, e)

def Lv.srows(rows: Tb.Table(S.Session), +ss: Tb.Table(S.Session)) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case (k, +t) <> more:
      Bool.and(Lv.tagged(S.Session.tag(t), ss), Lv.srows(more, ss))

def Lv.srows_cons(+rows: Tb.Table(S.Session), +k: U32, +t: S.Session, +more: Tb.Table(S.Session), +e: {Lv.srows(rows, more) == True{} : Bool}) -> {Lv.srows(rows, (k, t) <> more) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k1, +t1) <> +rest:
      P.Bool.and_intro(Lv.tagged(S.Session.tag(t1), (k, t) <> more), Lv.srows(rest, (k, t) <> more), Lv.tagged_cons(S.Session.tag(t1), k, t, more, P.Bool.and_true_l(Lv.tagged(S.Session.tag(t1), more), Lv.srows(rest, more), e)), Lv.srows_cons(rest, k, t, more, P.Bool.and_true_r(Lv.tagged(S.Session.tag(t1), more), Lv.srows(rest, more), e)))

def Lv.srows_sift(+s: S.SSieve, +ss: Tb.Table(S.Session)) -> {Lv.srows(S.Sessions.sift(s, ss), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {Lv.srows(tb, (k, t) <> more) == True{} : Bool}, k, t, S.Sessions.sift(s, more), S.SSieve.keeps(s, k, t), e => h => P.Bool.and_intro(Lv.tagged(S.Session.tag(t), (k, t) <> more), Lv.srows(S.Sessions.sift(s, more), (k, t) <> more), Lv.tagged_head(k, t, more), h), Lv.srows_cons(S.Sessions.sift(s, more), k, t, more, Lv.srows_sift(s, more)))

def Lv.srows_app(+xs: Tb.Table(S.Session), +ys: Tb.Table(S.Session), +ss: Tb.Table(S.Session), +hx: {Lv.srows(xs, ss) == True{} : Bool}, +hy: {Lv.srows(ys, ss) == True{} : Bool}) -> {Lv.srows(List.append(&2, Sigma<&2, &2, U32, _ => S.Session>, xs, ys), ss) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case (+k, +t) <> +more:
      P.Bool.and_intro(Lv.tagged(S.Session.tag(t), ss), Lv.srows(List.append(&2, Sigma<&2, &2, U32, _ => S.Session>, more, ys), ss), P.Bool.and_true_l(Lv.tagged(S.Session.tag(t), ss), Lv.srows(more, ss), hx), Lv.srows_app(more, ys, ss, P.Bool.and_true_r(Lv.tagged(S.Session.tag(t), ss), Lv.srows(more, ss), hx), hy))

# The sessions of contexts are sessions of the table.
def Lv.srows_held(+ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> {Lv.srows(Gmm.Gmm.sessions(ues, ss), ss) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      Lv.srows_app(S.Sessions.of_ue(k, ss), Gmm.Gmm.sessions(more, ss), ss, Lv.srows_sift(S.SOf{k}, ss), Lv.srows_held(more, ss))

# The rows a step deletes at the UPF are live under their keys, when no two
# sessions share a key: a session belonging to a UE is live.
def Lv.krows(rows: Tb.Table(S.Session), +st: S.State) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case (+k, t) <> more:
      Bool.and(Lv.kept(st, k), Lv.krows(more, st))

def Lv.hrows(rows: Tb.Table(S.Session), +ss: Tb.Table(S.Session)) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case (+k, t) <> more:
      Bool.and(Lv.live_m(Tb.Table.get(S.Session, k, ss)), Lv.hrows(more, ss))

def Lv.krows_hr(+rows: Tb.Table(S.Session), +st: S.State, +h: {Lv.hrows(rows, S.State.sessions(st)) == True{} : Bool}) -> {Lv.krows(rows, st) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +hm = Lv.live_m(Tb.Table.get(S.Session, k, S.State.sessions(st)))
      P.Bool.and_intro(Lv.kept(st, k), Lv.krows(more, st), P.Bool.or_l(hm, Bool.not(S.Sessions.unique(S.State.sessions(st))), P.Bool.and_true_l(hm, Lv.hrows(more, S.State.sessions(st)), h)), Lv.krows_hr(more, st, P.Bool.and_true_r(hm, Lv.hrows(more, S.State.sessions(st)), h)))

def Lv.krows_none(+rows: Tb.Table(S.Session), +st: S.State, +eu: {S.Sessions.unique(S.State.sessions(st)) == False{} : Bool}) -> {Lv.krows(rows, st) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +hm = Lv.live_m(Tb.Table.get(S.Session, k, S.State.sessions(st)))
      seu = Equal.sym(Bool, S.Sessions.unique(S.State.sessions(st)), False{}, eu)
      P.Bool.and_intro(Lv.kept(st, k), Lv.krows(more, st), (%seu : {Bool.or(hm, Bool.not(_)) == True{} : Bool}; P.Bool.or_r(hm, True{}, {==})), Lv.krows_none(more, st, eu))

def Lv.krows_if(+rows: Tb.Table(S.Session), +st: S.State, +b: Bool, +eb: {S.Sessions.unique(S.State.sessions(st)) == b : Bool}, f: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool} -> {Lv.hrows(rows, S.State.sessions(st)) == True{} : Bool}) -> {Lv.krows(rows, st) == True{} : Bool}:
  match b:
    case True{}:
      Lv.krows_hr(rows, st, f(eb))
    case False{}:
      Lv.krows_none(rows, st, eb)

def Lv.krows_by(+rows: Tb.Table(S.Session), +st: S.State, f: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool} -> {Lv.hrows(rows, S.State.sessions(st)) == True{} : Bool}) -> {Lv.krows(rows, st) == True{} : Bool}:
  Lv.krows_if(rows, st, S.Sessions.unique(S.State.sessions(st)), {==}, f)

def Lv.krows_app(+xs: Tb.Table(S.Session), +ys: Tb.Table(S.Session), +st: S.State, +hx: {Lv.krows(xs, st) == True{} : Bool}, +hy: {Lv.krows(ys, st) == True{} : Bool}) -> {Lv.krows(List.append(&2, Sigma<&2, &2, U32, _ => S.Session>, xs, ys), st) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case (+k, +t) <> +more:
      P.Bool.and_intro(Lv.kept(st, k), Lv.krows(List.append(&2, Sigma<&2, &2, U32, _ => S.Session>, more, ys), st), P.Bool.and_true_l(Lv.kept(st, k), Lv.krows(more, st), hx), Lv.krows_app(more, ys, st, P.Bool.and_true_r(Lv.kept(st, k), Lv.krows(more, st), hx), hy))

def Lv.clear_sift(+key: U32, +s: S.Session, +v: S.SSieve, sessions: Tb.Table(S.Session), +e: {S.Sessions.clear(key, s, sessions) == True{} : Bool}) -> {S.Sessions.clear(key, s, S.Sessions.sift(v, sessions)) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {S.Sessions.clear(key, s, tb) == True{} : Bool}, k, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k, t), e2 => h => P.Bool.and_intro(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, S.Sessions.sift(v, more)), P.Bool.and_true_l(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, more), e), h), Lv.clear_sift(key, s, v, more, P.Bool.and_true_r(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, more), e)))

# A row clear of the rows keeps their lookups.
def Lv.hrows_cons(+rows: Tb.Table(S.Session), +k0: U32, +t0: S.Session, +more: Tb.Table(S.Session), +hc: {S.Sessions.clear(k0, t0, rows) == True{} : Bool}, +h: {Lv.hrows(rows, more) == True{} : Bool}) -> {Lv.hrows(rows, (k0, t0) <> more) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k1, +t1) <> +rest:
      +c = S.SRow.conflicts(k0, t0, k1, t1)
      +nc = P.Bool.not_true(c, P.Bool.and_true_l(Bool.not(c), S.Sessions.clear(k0, t0, rest), hc))
      +ne = P.Bool.or_false_l(U32.is_eq(k1, k0), S.Session.conflicts(t0, t1), nc)
      sf = P.U32.sym_false(k1, k0, U32.is_eq(k0, k1), {==}, ne)
      +hm = Lv.live_m(Tb.Table.get(S.Session, k1, more))
      (%sf : {Bool.and(Lv.live_m(Tb.Table.hit(S.Session, t0, Tb.Table.get(S.Session, k1, more), _)), Lv.hrows(rest, (k0, t0) <> more)) == True{} : Bool}; P.Bool.and_intro(hm, Lv.hrows(rest, (k0, t0) <> more), P.Bool.and_true_l(hm, Lv.hrows(rest, more), h), Lv.hrows_cons(rest, k0, t0, more, P.Bool.and_true_r(Bool.not(c), S.Sessions.clear(k0, t0, rest), hc), P.Bool.and_true_r(hm, Lv.hrows(rest, more), h))))

# Every row a sieve keeps is live.
def Lv.sieved(+v: S.SSieve, ss: Tb.Table(S.Session)) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case (+k, +t) <> more:
      Bool.and(Bool.or(Bool.not(S.SSieve.keeps(v, k, t)), S.SPhase.live(S.Session.phase(t))), Lv.sieved(v, more))

# The rows a sieve keeps, when it keeps only live ones, are live under their keys.
def Lv.hrows_sift(+v: S.SSieve, +ss: Tb.Table(S.Session), +eu: {S.Sessions.unique(ss) == True{} : Bool}, +es: {Lv.sieved(v, ss) == True{} : Bool}) -> {Lv.hrows(S.Sessions.sift(v, ss), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +ec = P.Bool.and_true_l(S.Sessions.clear(k, t, more), S.Sessions.unique(more), eu)
      +em = P.Bool.and_true_r(S.Sessions.clear(k, t, more), S.Sessions.unique(more), eu)
      +x = Bool.or(Bool.not(S.SSieve.keeps(v, k, t)), S.SPhase.live(S.Session.phase(t)))
      P.Keep.by(S.Session, tb => {Lv.hrows(tb, (k, t) <> more) == True{} : Bool}, k, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k, t), e => h => P.Bool.and_intro(Lv.live_m(Tb.Table.get(S.Session, k, (k, t) <> more)), Lv.hrows(S.Sessions.sift(v, more), (k, t) <> more), (%Equal.sym(Bool, U32.is_eq(k, k), True{}, P.U32.is_eq_refl(k)) : {Lv.live_m(Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), _)) == True{} : Bool}; P.Bool.or_true_r(Bool.not(S.SSieve.keeps(v, k, t)), S.SPhase.live(S.Session.phase(t)), (%Equal.sym(Bool, S.SSieve.keeps(v, k, t), True{}, e) : {Bool.not(_) == False{} : Bool}; {==}), P.Bool.and_true_l(x, Lv.sieved(v, more), es))), h), Lv.hrows_cons(S.Sessions.sift(v, more), k, t, more, Lv.clear_sift(k, t, v, more, ec), Lv.hrows_sift(v, more, em, P.Bool.and_true_r(x, Lv.sieved(v, more), es))))

def Lv.krows_sift(+st: S.State, +v: S.SSieve, +es: {Lv.sieved(v, S.State.sessions(st)) == True{} : Bool}) -> {Lv.krows(S.Sessions.sift(v, S.State.sessions(st)), st) == True{} : Bool}:
  Lv.krows_by(S.Sessions.sift(v, S.State.sessions(st)), st, eu => Lv.hrows_sift(v, S.State.sessions(st), eu, es))

def Lv.sv_if(+c: Bool, +h: Bool, f: {c == True{} : Bool} -> {h == True{} : Bool}) -> {Bool.or(Bool.not(c), h) == True{} : Bool}:
  match c:
    case True{}:
      f({==})
    case False{}:
      {==}

# A session that belongs to a UE is live.
def Lv.held_hit(+u: U32, +b: Bool, +e: {Tb.Table.present(U32, Tb.Table.hit(U32, u, None{}, b)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))

def Lv.held_tag(+t: S.Session, +e: {Tb.Table.present(U32, S.Session.tag(t)) == True{} : Bool}) -> {S.SPhase.live(S.Session.phase(t)) == True{} : Bool}:
  Lv.held_hit(S.Session.ue(t), S.SPhase.live(S.Session.phase(t)), e)

def Lv.same_present(+m: Maybe<&2, U32>, +x: U32, +e: {S.Maybe.same_u32(m, Some{x}) == True{} : Bool}) -> {Tb.Table.present(U32, m) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Tb.Table.present(U32, None{}) == True{} : Bool}, P.Refute.bool(e))
    case Some{y}:
      {==}

def Lv.unnot(+x: Bool, +e: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(Equal.sym(Bool, True{}, False{}, e)))


def Lv.orphan_present(+t: S.Session, +ues: Tb.Table(S.Ue), +e: {Bool.not(S.Session.owned(t, ues)) == True{} : Bool}) -> {Tb.Table.present(U32, S.Session.tag(t)) == True{} : Bool}:
  +p = Tb.Table.present(U32, S.Session.tag(t))
  +o = P.Bool.not_true(S.Session.owned(t, ues), e)
  +np = P.Bool.or_false_l(Bool.not(p), Tb.Table.has(S.Ue, S.Session.ue(t), ues), o)
  Lv.unnot(p, np)

def Lv.sieved_of(+ue: U32, +ss: Tb.Table(S.Session)) -> {Lv.sieved(S.SOf{ue}, ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Bool.and_intro(Bool.or(Bool.not(S.SSieve.keeps(S.SOf{ue}, k, t)), S.SPhase.live(S.Session.phase(t))), Lv.sieved(S.SOf{ue}, more), Lv.sv_if(S.SSieve.keeps(S.SOf{ue}, k, t), S.SPhase.live(S.Session.phase(t)), e => Lv.held_tag(t, Lv.same_present(S.Session.tag(t), ue, e))), Lv.sieved_of(ue, more))

def Lv.sieved_orphan(+ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> {Lv.sieved(S.SOrphan{ues}, ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Bool.and_intro(Bool.or(Bool.not(S.SSieve.keeps(S.SOrphan{ues}, k, t)), S.SPhase.live(S.Session.phase(t))), Lv.sieved(S.SOrphan{ues}, more), Lv.sv_if(S.SSieve.keeps(S.SOrphan{ues}, k, t), S.SPhase.live(S.Session.phase(t)), e => Lv.held_tag(t, Lv.orphan_present(t, ues, e))), Lv.sieved_orphan(ues, more))

def Lv.krows_of(+st: S.State, +ue: U32) -> {Lv.krows(S.Sessions.of_ue(ue, S.State.sessions(st)), st) == True{} : Bool}:
  Lv.krows_sift(st, S.SOf{ue}, Lv.sieved_of(ue, S.State.sessions(st)))

def Lv.krows_orphan(+st: S.State, +ues: Tb.Table(S.Ue)) -> {Lv.krows(S.Sessions.sift(S.SOrphan{ues}, S.State.sessions(st)), st) == True{} : Bool}:
  Lv.krows_sift(st, S.SOrphan{ues}, Lv.sieved_orphan(ues, S.State.sessions(st)))

def Lv.krows_held(+st: S.State, +ues: Tb.Table(S.Ue)) -> {Lv.krows(Gmm.Gmm.sessions(ues, S.State.sessions(st)), st) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      Lv.krows_app(S.Sessions.of_ue(k, S.State.sessions(st)), Gmm.Gmm.sessions(more, S.State.sessions(st)), st, Lv.krows_of(st, k), Lv.krows_held(st, more))

def Lv.del_if(+st: S.State, +key: U32, +t: S.Session, +seq: U32, +more: Tb.Table(S.Session), +b: Bool, +eb: {S.Session.known(t) == b : Bool}, +ht: {Lv.tagged(S.Session.tag(t), S.State.sessions(st)) == True{} : Bool}, +hk: {Lv.kept(st, key) == True{} : Bool}, later: @q:U32 -> {Lv.okf(st, Up.N4.deletions(more, q)) == True{} : Bool}) -> {Lv.okf(st, Up.N4.delete_if(key, t, seq, q => Up.N4.deletions(more, q), b)) == True{} : Bool}:
  match b:
    case True{}:
      +request = Up.N4.delete(S.Session.up_seid(t), seq)
      +v : S.SVar = S.SVar{S.Session.up_seid(t), seq, S.Deleting{S.Guard{0}, request}}
      +x : N.Act = N.Pfcp{S.Session.tag(t), request}
      +y : N.Act = N.TimerStart{None{}, key, Up.N4.t1_ms()}
      +ek = Lv.tagged_live(st, S.Session.tag(t), ht)
      +kv : {Lv.revar_ok(st, v) == True{} : Bool} = P.Bool.and_intro(True{}, Bool.or(Lv.var_ok(v), Bool.not(S.Sessions.known(S.State.sessions(st)))), {==}, P.Bool.or_l(Lv.var_ok(v), Bool.not(S.Sessions.known(S.State.sessions(st))), eb))
      +tx : S.Tx = S.Both{S.Revar{key, v}, S.BumpSeq{1}}
      +hs = P.Bool.or_l(N.Act.sends(request, x), N.Acts.sends(request, [y]), P.Bytes.eq_refl(request))
      +hg = P.Bool.or_r(N.Act.starts_for(key, Up.N4.t1_ms(), x), N.Acts.starts_for(key, Up.N4.t1_ms(), [y]), P.Bool.or_l(N.Act.starts_for(key, Up.N4.t1_ms(), y), False{}, P.Bool.and_intro(U32.is_eq(key, key), True{}, P.U32.is_eq_refl(key), {==})))
      +ha : {Lv.arms(tx, [x, y]) == True{} : Bool} = P.Bool.and_intro(Lv.arms(S.Revar{key, v}, [x, y]), True{}, P.Bool.and_intro(True{}, Bool.and(N.Acts.sends(request, [x, y]), N.Acts.starts_for(key, Up.N4.t1_ms(), [x, y])), {==}, P.Bool.and_intro(N.Acts.sends(request, [x, y]), N.Acts.starts_for(key, Up.N4.t1_ms(), [x, y]), hs, hg)), {==})
      +hf = P.Bool.and_intro(Bool.and(Lv.spare(st, key, v), Lv.revar_ok(st, v)), True{}, P.Bool.and_intro(Lv.spare(st, key, v), Lv.revar_ok(st, v), hk, kv), {==})
      Lv.join(st, (tx, [x, y]), Up.N4.deletions(more, U32.add(seq, 1)), Lv.leaf(st, tx, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], Lv.s_start(st, None{}, key, {==}, hk), {==})), P.Bool.and_intro(Lv.arms(tx, [x, y]), Lv.free(st, tx), ha, hf), {==}, {==}), later(U32.add(seq, 1)))
    case False{}:
      Lv.join(st, (S.DelSession{key}, []), Up.N4.deletions(more, seq), hk, later(seq))

# Session Deletions at the UPF are built from sessions of the state.
def Lv.dels(+st: S.State, +rows: Tb.Table(S.Session), +seq: U32, +e: {Lv.srows(rows, S.State.sessions(st)) == True{} : Bool}, +ek: {Lv.krows(rows, st) == True{} : Bool}) -> {Lv.okf(st, Up.N4.deletions(rows, seq)) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      +hm = P.Bool.and_true_r(Lv.tagged(S.Session.tag(t), S.State.sessions(st)), Lv.srows(more, S.State.sessions(st)), e)
      +km = P.Bool.and_true_r(Lv.kept(st, key), Lv.krows(more, st), ek)
      Lv.del_if(st, key, t, seq, more, S.Session.known(t), {==}, P.Bool.and_true_l(Lv.tagged(S.Session.tag(t), S.State.sessions(st)), Lv.srows(more, S.State.sessions(st)), e), P.Bool.and_true_l(Lv.kept(st, key), Lv.krows(more, st), ek), +q => Lv.dels(st, more, q, hm, km))

# One row deleted, its key kept.
def Lv.one_kept(+st: S.State, +skey: U32, +s: S.Session, +ek: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.krows([(skey, s)], st) == True{} : Bool}:
  P.Bool.and_intro(Lv.kept(st, skey), True{}, ek, {==})

def Lv.u32_ne(+a: U32, +b: U32, +e: {U32.is_eq(b, a) == False{} : Bool}) -> {U32.is_eq(a, b) == False{} : Bool}:
  Equal.sym(Bool, False{}, U32.is_eq(a, b), P.U32.sym_false(b, a, U32.is_eq(a, b), {==}, e))


# The row a search finds is the row under its key, when no two sessions
# share a key.
def Lv.Got(m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +ss: Tb.Table(S.Session)) -> Type:
  match m:
    case None{}:
      Unit
    case Some{(k, t)}:
      {S.Sessions.unique(ss) == True{} : Bool} -> {Tb.Table.get(S.Session, k, ss) == Some{t} : Maybe<&2, S.Session>}

def Lv.clear_get_row(+k0: U32, +t0: S.Session, +k1: U32, +t1: S.Session, +rest: Tb.Table(S.Session), +k: U32, +t: S.Session, +b: Bool, +eb: {U32.is_eq(k1, k) == b : Bool}, +ec: {S.Sessions.clear(k0, t0, (k1, t1) <> rest) == True{} : Bool}, +eg: {Tb.Table.hit(S.Session, t1, Tb.Table.get(S.Session, k, rest), b) == Some{t} : Maybe<&2, S.Session>}, ih: {S.Sessions.clear(k0, t0, rest) == True{} : Bool} -> {Tb.Table.get(S.Session, k, rest) == Some{t} : Maybe<&2, S.Session>} -> {U32.is_eq(k0, k) == False{} : Bool}) -> {U32.is_eq(k0, k) == False{} : Bool}:
  match b:
    case True{}:
      +c = S.SRow.conflicts(k0, t0, k1, t1)
      +nc = P.Bool.not_true(c, P.Bool.and_true_l(Bool.not(c), S.Sessions.clear(k0, t0, rest), ec))
      +ne = P.Bool.or_false_l(U32.is_eq(k1, k0), S.Session.conflicts(t0, t1), nc)
      e1 = P.U32.eq_of_is_eq(k1, k, eb)
      (%e1 : {U32.is_eq(k0, _) == False{} : Bool}; Lv.u32_ne(k0, k1, ne))
    case False{}:
      +c = S.SRow.conflicts(k0, t0, k1, t1)
      ih(P.Bool.and_true_r(Bool.not(c), S.Sessions.clear(k0, t0, rest), ec), eg)

# A row clear of a table has a key no row of it has.
def Lv.clear_get(+k0: U32, +t0: S.Session, ss: Tb.Table(S.Session), +k: U32, +t: S.Session, +ec: {S.Sessions.clear(k0, t0, ss) == True{} : Bool}, +eg: {Tb.Table.get(S.Session, k, ss) == Some{t} : Maybe<&2, S.Session>}) -> {U32.is_eq(k0, k) == False{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({U32.is_eq(k0, k) == False{} : Bool}, P.Refute.none_some(S.Session, t, eg))
    case (+k1, +t1) <> +rest:
      Lv.clear_get_row(k0, t0, k1, t1, rest, k, t, U32.is_eq(k1, k), {==}, ec, eg, e1 => e2 => Lv.clear_get(k0, t0, rest, k, t, e1, e2))

def Lv.got_head(+k0: U32, +t0: S.Session, +more: Tb.Table(S.Session)) -> {Tb.Table.get(S.Session, k0, (k0, t0) <> more) == Some{t0} : Maybe<&2, S.Session>}:
  ser = Equal.sym(Bool, U32.is_eq(k0, k0), True{}, P.U32.is_eq_refl(k0))
  (%ser : {Tb.Table.hit(S.Session, t0, Tb.Table.get(S.Session, k0, more), _) == Some{t0} : Maybe<&2, S.Session>}; {==})

def Lv.got_at(+k0: U32, +t0: S.Session, +more: Tb.Table(S.Session), +k: U32, +t: S.Session, ih: {S.Sessions.unique(more) == True{} : Bool} -> {Tb.Table.get(S.Session, k, more) == Some{t} : Maybe<&2, S.Session>}, +eu: {S.Sessions.unique((k0, t0) <> more) == True{} : Bool}) -> {Tb.Table.get(S.Session, k, (k0, t0) <> more) == Some{t} : Maybe<&2, S.Session>}:
  +ec = P.Bool.and_true_l(S.Sessions.clear(k0, t0, more), S.Sessions.unique(more), eu)
  +g = ih(P.Bool.and_true_r(S.Sessions.clear(k0, t0, more), S.Sessions.unique(more), eu))
  sne = Equal.sym(Bool, U32.is_eq(k0, k), False{}, Lv.clear_get(k0, t0, more, k, t, ec, g))
  (%sne : {Tb.Table.hit(S.Session, t0, Tb.Table.get(S.Session, k, more), _) == Some{t} : Maybe<&2, S.Session>}; g)

def Lv.got_cons(+k0: U32, +t0: S.Session, +more: Tb.Table(S.Session), +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, ih: Lv.Got(m, more)) -> Lv.Got(m, (k0, t0) <> more):
  match m:
    case None{}:
      Unit{}
    case Some{(+k, +t)}:
      eu => Lv.got_at(k0, t0, more, k, t, ih, eu)

def Lv.got_pick(+k0: U32, +t0: S.Session, +more: Tb.Table(S.Session), +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +hit: Bool, ih: Lv.Got(m, more)) -> Lv.Got(S.Sessions.pick(k0, t0, m, hit), (k0, t0) <> more):
  match hit:
    case True{}:
      eu => Lv.got_head(k0, t0, more)
    case False{}:
      Lv.got_cons(k0, t0, more, m, ih)

# The row a search finds is a row of the table.
def Lv.Has(m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +ss: Tb.Table(S.Session)) -> Type:
  match m:
    case None{}:
      Unit
    case Some{(+k, t)}:
      {Tb.Table.has(S.Session, k, ss) == True{} : Bool}

def Lv.shas_hit(+t0: S.Session, +m: Maybe<&2, S.Session>, +b: Bool, +e: {Tb.Table.present(S.Session, m) == True{} : Bool}) -> {Tb.Table.present(S.Session, Tb.Table.hit(S.Session, t0, m, b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def Lv.shas_head(+k0: U32, +t0: S.Session, +more: Tb.Table(S.Session)) -> {Tb.Table.has(S.Session, k0, (k0, t0) <> more) == True{} : Bool}:
  e = Equal.sym(Bool, U32.is_eq(k0, k0), True{}, P.U32.is_eq_refl(k0))
  (%e : {Tb.Table.present(S.Session, Tb.Table.hit(S.Session, t0, Tb.Table.get(S.Session, k0, more), _)) == True{} : Bool}; {==})

def Lv.shas_cons(+k0: U32, +t0: S.Session, +more: Tb.Table(S.Session), +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, ih: Lv.Has(m, more)) -> Lv.Has(m, (k0, t0) <> more):
  match m:
    case None{}:
      Unit{}
    case Some{(+k, t)}:
      Lv.shas_hit(t0, Tb.Table.get(S.Session, k, more), U32.is_eq(k0, k), ih)

def Lv.has_pick(+k0: U32, +t0: S.Session, +more: Tb.Table(S.Session), +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +hit: Bool, ih: Lv.Has(m, more)) -> Lv.Has(S.Sessions.pick(k0, t0, m, hit), (k0, t0) <> more):
  match hit:
    case True{}:
      Lv.shas_head(k0, t0, more)
    case False{}:
      Lv.shas_cons(k0, t0, more, m, ih)

def Lv.has_by_seq(+q: U32, ss: Tb.Table(S.Session)) -> Lv.Has(S.Sessions.by_seq(q, ss), ss):
  match ss:
    case Nil{}:
      Unit{}
    case (+k0, +t0) <> +more:
      Lv.has_pick(k0, t0, more, S.Sessions.by_seq(q, more), U32.is_eq(S.Session.seq(t0), q), Lv.has_by_seq(q, more))

def Lv.got_by_seq(+q: U32, ss: Tb.Table(S.Session)) -> Lv.Got(S.Sessions.by_seq(q, ss), ss):
  match ss:
    case Nil{}:
      Unit{}
    case (+k0, +t0) <> +more:
      Lv.got_pick(k0, t0, more, S.Sessions.by_seq(q, more), U32.is_eq(S.Session.seq(t0), q), Lv.got_by_seq(q, more))

def Lv.got_by_psi(+ue: U32, +psi: U32, ss: Tb.Table(S.Session)) -> Lv.Got(S.Sessions.by_psi(ue, psi, ss), ss):
  match ss:
    case Nil{}:
      Unit{}
    case (+k0, +t0) <> +more:
      Lv.got_pick(k0, t0, more, S.Sessions.by_psi(ue, psi, more), Bool.and(S.Maybe.same_u32(S.Session.tag(t0), Some{ue}), U32.is_eq(S.Session.psi(t0), psi)), Lv.got_by_psi(ue, psi, more))

# The key of a row the step found, kept unless being deleted.
def Lv.kept_if(+st: S.State, +k: U32, +p: S.SPhase) -> Bool:
  Bool.or(Lv.kept(st, k), Bool.not(S.SPhase.live(p)))

def Lv.kept_at(+st: S.State, +k: U32, +p: S.SPhase, +ek: {Lv.kept_if(st, k, p) == True{} : Bool}, +eh: {S.SPhase.live(p) == True{} : Bool}) -> {Lv.kept(st, k) == True{} : Bool}:
  seh = Equal.sym(Bool, S.SPhase.live(p), True{}, eh)
  P.Bool.or_true_l(Lv.kept(st, k), Bool.not(S.SPhase.live(p)), (%seh : {Bool.not(_) == False{} : Bool}; {==}), ek)

def Lv.kept_hit(+st: S.State, +k: U32, +t: S.Session, +b: Bool, +eb: {S.SPhase.live(S.Session.phase(t)) == b : Bool}, +eg: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>}) -> {Lv.kept_if(st, k, S.Session.phase(t)) == True{} : Bool}:
  match b:
    case True{}:
      seg = Equal.sym(Maybe<&2, S.Session>, Tb.Table.get(S.Session, k, S.State.sessions(st)), Some{t}, eg)
      P.Bool.or_l(Lv.kept(st, k), Bool.not(S.SPhase.live(S.Session.phase(t))), P.Bool.or_l(Lv.live_m(Tb.Table.get(S.Session, k, S.State.sessions(st))), Bool.not(S.Sessions.unique(S.State.sessions(st))), (%seg : {Lv.live_m(_) == True{} : Bool}; eb)))
    case False{}:
      seb = Equal.sym(Bool, S.SPhase.live(S.Session.phase(t)), False{}, eb)
      P.Bool.or_r(Lv.kept(st, k), Bool.not(S.SPhase.live(S.Session.phase(t))), (%seb : {Bool.not(_) == True{} : Bool}; {==}))

# The row under a key: its key is kept unless it is being deleted.
def Lv.kept_get(+st: S.State, +k: U32, +t: S.Session, +eg: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>}) -> {Lv.kept_if(st, k, S.Session.phase(t)) == True{} : Bool}:
  Lv.kept_hit(st, k, t, S.SPhase.live(S.Session.phase(t)), {==}, eg)

# A row a session search finds is a session of the table: its UE owns a
# session, and it agrees with the UPF when every session does.

def Lv.kept_got_if(+st: S.State, +k: U32, +t: S.Session, +b: Bool, +eb: {S.Sessions.unique(S.State.sessions(st)) == b : Bool}, g: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool} -> {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>}) -> {Lv.kept_if(st, k, S.Session.phase(t)) == True{} : Bool}:
  match b:
    case True{}:
      Lv.kept_get(st, k, t, g(eb))
    case False{}:
      +hm = Lv.live_m(Tb.Table.get(S.Session, k, S.State.sessions(st)))
      seb = Equal.sym(Bool, S.Sessions.unique(S.State.sessions(st)), False{}, eb)
      P.Bool.or_l(Lv.kept(st, k), Bool.not(S.SPhase.live(S.Session.phase(t))), (%seb : {Bool.or(hm, Bool.not(_)) == True{} : Bool}; P.Bool.or_r(hm, True{}, {==})))

# A row a search finds: its key is kept unless it is being deleted.
def Lv.kept_got(+st: S.State, +k: U32, +t: S.Session, g: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool} -> {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>}) -> {Lv.kept_if(st, k, S.Session.phase(t)) == True{} : Bool}:
  Lv.kept_got_if(st, k, t, S.Sessions.unique(S.State.sessions(st)), {==}, g)

def Lv.found(m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +ss: Tb.Table(S.Session)) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{(k, +t)}:
      Bool.and(Lv.tagged(S.Session.tag(t), ss), Bool.or(S.SPhase.knows(S.Session.phase(t), S.Session.known(t)), Bool.not(S.Sessions.known(ss))))

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
      P.Bool.and_intro(Lv.tagged(S.Session.tag(t1), (k, t) <> more), Bool.or(a, Bool.not(Bool.and(S.SPhase.knows(S.Session.phase(t), S.Session.known(t)), y))), Lv.tagged_cons(S.Session.tag(t1), k, t, more, P.Bool.and_true_l(Lv.tagged(S.Session.tag(t1), more), Bool.or(a, Bool.not(y)), e)), Lv.kn_cons(a, S.SPhase.knows(S.Session.phase(t), S.Session.known(t)), y, P.Bool.and_true_r(Lv.tagged(S.Session.tag(t1), more), Bool.or(a, Bool.not(y)), e)))

def Lv.pick(+key: U32, +t: S.Session, +later: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +hit: Bool, +more: Tb.Table(S.Session), +e: {Lv.found(later, more) == True{} : Bool}) -> {Lv.found(S.Sessions.pick(key, t, later, hit), (key, t) <> more) == True{} : Bool}:
  match hit:
    case True{}:
      +a = S.SPhase.knows(S.Session.phase(t), S.Session.known(t))
      P.Bool.and_intro(Lv.tagged(S.Session.tag(t), (key, t) <> more), Bool.or(a, Bool.not(Bool.and(a, S.Sessions.known(more)))), Lv.tagged_head(key, t, more), Lv.kn_head(a, S.Sessions.known(more)))
    case False{}:
      Lv.found_cons(later, key, t, more, e)

# The found row agrees with the UPF when every session does.
def Lv.found_known(+m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +ss: Tb.Table(S.Session), +skey: U32, +s: S.Session, +em: {m == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, +h: {Lv.found(m, ss) == True{} : Bool}, +ek: {S.Sessions.known(ss) == True{} : Bool}) -> {S.SPhase.knows(S.Session.phase(s), S.Session.known(s)) == True{} : Bool}:
  sem = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, m, Some{(skey, s)}, em)
  hf : {Lv.found(Some{(skey, s)}, ss) == True{} : Bool} = (%em : {Lv.found(_, ss) == True{} : Bool}; h)
  +a = S.SPhase.knows(S.Session.phase(s), S.Session.known(s))
  sk = Equal.sym(Bool, S.Sessions.known(ss), True{}, ek)
  P.Bool.or_true_l(a, Bool.not(S.Sessions.known(ss)), (%sk : {Bool.not(_) == False{} : Bool}; {==}), P.Bool.and_true_r(Lv.tagged(S.Session.tag(s), ss), Bool.or(a, Bool.not(S.Sessions.known(ss))), hf))

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

def Lv.frows_sift(+s: S.SSieve, +ss: Tb.Table(S.Session)) -> {Lv.frows(S.Sessions.sift(s, ss), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {Lv.frows(tb, (k, t) <> more) == True{} : Bool}, k, t, S.Sessions.sift(s, more), S.SSieve.keeps(s, k, t), e => h => P.Bool.and_intro(Lv.found(Some{(k, t)}, (k, t) <> more), Lv.frows(S.Sessions.sift(s, more), (k, t) <> more), Lv.pick(k, t, None{}, True{}, more, {==}), h), Lv.frows_cons(S.Sessions.sift(s, more), k, t, more, Lv.frows_sift(s, more)))

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
      P.Bool.and_intro(Lv.tagged(S.Session.tag(t), (k0, t) <> more), Bool.or(a, Bool.not(Bool.and(a, S.Sessions.known(more)))), Lv.tagged_head(k0, t, more), Lv.kn_head(a, S.Sessions.known(more)))
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
      Lv.pick(key, t, S.Sessions.by_psi(ue, psi, more), Bool.and(S.Maybe.same_u32(S.Session.tag(t), Some{ue}), U32.is_eq(S.Session.psi(t), psi)), more, Lv.by_psi(ue, psi, more))

# Contexts put and released
# -------------------------

# The target released.
def Lw.ho_drop(+st: S.State, +key: U32, +leg: S.Leg, +cause: G.Cause, +ek: {Lv.held(st, key) == True{} : Bool}) -> {Lv.acts(st, Ho.Ho.drop(key, leg, cause)) == True{} : Bool}:
  match leg:
    case S.Asked{+t}:
      Lv.cons(st, N.UeSend{t, Ho.Ho.stream(), key, N.Ngap.release_command(G.UE_NGAP_IDs_aMF_UE_NGAP_ID{N.Ngap.big(key)}, cause)}, [], Lv.held_live(st, key, ek), {==})
    case S.Acked{+t, +r, +s, ts}:
      Lv.cons(st, N.Release{t, s, key, r, cause}, [], Lv.held_live(st, key, ek), {==})

def Lw.ho_leg_drop(+st: S.State, +key: U32, +p: S.Phase, +cause: G.Cause, +ek: {Lv.held(st, key) == True{} : Bool}) -> {Lv.acts(st, Ho.Ho.leg_drop(key, p, cause)) == True{} : Bool}:
  match p:
    case S.Handover{ctx, nh, source, +leg}:
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
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.evict(+st: S.State, +vs: Tb.Table(S.Ue), +e: {Lv.keys_in(vs, S.State.ues(st)) == True{} : Bool}) -> {Lv.acts(st, Gmm.Gmm.evict(vs)) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case (+key, +v) <> +more:
      +eh = P.Bool.and_true_l(Tb.Table.has(S.Ue, key, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e)
      +ek = Lv.has_live(st, key, eh)
      +cause = N.Ngap.nas_cause(G.CauseNas.deregister())
      Lv.cons(st, N.Release{S.Ue.assoc(v), S.Ue.stream(v), key, S.Ue.ran_id(v), cause}, List.append(&2, N.Act, Ho.Ho.leg_drop(key, S.Ue.phase(v), cause), Gmm.Gmm.evict(more)), ek, Lv.append(st, Ho.Ho.leg_drop(key, S.Ue.phase(v), cause), Gmm.Gmm.evict(more), Lw.ho_leg_drop(st, key, S.Ue.phase(v), cause, Lv.has_held(st, key, eh)), Lw.evict(st, more, P.Bool.and_true_r(Tb.Table.has(S.Ue, key, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e))))

# Some context of a table that has every context set up is set up.
def Lv.set_up_row(+key: U32, +ue: S.Ue, +k0: U32, +w: S.Ue, +more: Tb.Table(S.Ue), +as: Tb.Table(B.Bytes()), +b: Bool, +eb: {U32.is_eq(k0, key) == b : Bool}, +e: {Bool.and(S.Assocs.has(S.Ue.assoc(w), as), S.Ues.set_up(more, as)) == True{} : Bool}, +eg: {Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, key, more), b) == Some{ue} : Maybe<&2, S.Ue>}, ih: {S.Ues.set_up(more, as) == True{} : Bool} -> {Tb.Table.get(S.Ue, key, more) == Some{ue} : Maybe<&2, S.Ue>} -> {S.Assocs.has(S.Ue.assoc(ue), as) == True{} : Bool}) -> {S.Assocs.has(S.Ue.assoc(ue), as) == True{} : Bool}:
  match b:
    case True{}:
      ew = P.Some.inj(S.Ue, w, ue, eg)
      (%ew : {S.Assocs.has(S.Ue.assoc(_), as) == True{} : Bool}; P.Bool.and_true_l(S.Assocs.has(S.Ue.assoc(w), as), S.Ues.set_up(more, as), e))
    case False{}:
      ih(P.Bool.and_true_r(S.Assocs.has(S.Ue.assoc(w), as), S.Ues.set_up(more, as), e), eg)

def Lv.set_up_get(+ues: Tb.Table(S.Ue), +as: Tb.Table(B.Bytes()), +key: U32, +ue: S.Ue, +e: {S.Ues.set_up(ues, as) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>}) -> {S.Assocs.has(S.Ue.assoc(ue), as) == True{} : Bool}:
  match ues:
    case Nil{}:
      Empty.absurd({S.Assocs.has(S.Ue.assoc(ue), as) == True{} : Bool}, P.Refute.none_some(S.Ue, ue, eg))
    case (+k0, +w) <> +more:
      Lv.set_up_row(key, ue, k0, w, more, as, U32.is_eq(k0, key), {==}, e, eg, e1 => e2 => Lv.set_up_get(more, as, key, ue, e1, e2))

def Lv.home_if(+st: S.State, +key: U32, +ue: S.Ue, +b: Bool, +eb: {S.Ues.set_up(S.State.ues(st), S.State.assocs(st)) == b : Bool}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}) -> {Bool.or(S.Assocs.has(S.Ue.assoc(ue), S.State.assocs(st)), Bool.not(b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.or_l(S.Assocs.has(S.Ue.assoc(ue), S.State.assocs(st)), False{}, Lv.set_up_get(S.State.ues(st), S.State.assocs(st), key, ue, eb, eg))
    case False{}:
      P.Bool.or_r(S.Assocs.has(S.Ue.assoc(ue), S.State.assocs(st)), True{}, {==})

# A context of st is at home.
def Lv.home_get(+st: S.State, +key: U32, +ue: S.Ue, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.home(st, ue) == True{} : Bool}:
  Lv.home_if(st, key, ue, S.Ues.set_up(S.State.ues(st), S.State.assocs(st)), {==}, eg)

def Lv.pair_home(+st: S.State, +key: U32, +ue: S.Ue, +assoc: U32, pr: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>} & {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}) -> {Lv.home(st, ue) == True{} : Bool}:
  match pr:
    case (+eg, eb):
      Lv.home_get(st, key, ue, eg)

# The context an association owns under the key is at home.
def Lv.owned_home(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +ue: S.Ue, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.home(st, ue) == True{} : Bool}:
  Lv.pair_home(st, key, ue, assoc, PT.Own.get(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran, ue, eo))

# A context on an association set up is at home.
def Lv.home_on(+st: S.State, +ue: S.Ue, +ea: {S.Assocs.has(S.Ue.assoc(ue), S.State.assocs(st)) == True{} : Bool}) -> {Lv.home(st, ue) == True{} : Bool}:
  P.Bool.or_l(S.Assocs.has(S.Ue.assoc(ue), S.State.assocs(st)), Bool.not(S.Ues.set_up(S.State.ues(st), S.State.assocs(st))), ea)

def Lv.home_moved(+st: S.State, +ue: S.Ue, +a: U32, +r: B.Bytes(), +s: U32, +p: S.Phase, +ea: {S.Assocs.has(a, S.State.assocs(st)) == True{} : Bool}) -> {Lv.home(st, S.Ue.moved(ue, a, r, s, p)) == True{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      Lv.home_on(st, S.Ue{a, r, s, supi, tmsi, reg, ngksi, p, last_dl}, ea)

def Lv.home_phase(+st: S.State, +ue: S.Ue, +p: S.Phase, +h: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.home(st, S.Ue.with_phase(ue, p)) == True{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      h

def Lv.home_dl(+st: S.State, +ue: S.Ue, +p: S.Phase, +d: B.Bytes(), +h: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.home(st, S.Ue.with_dl(ue, p, d)) == True{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      h

def Lv.home_supi(+st: S.State, +ue: S.Ue, +x: B.Digits(), +h: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.home(st, S.Ue.with_supi(ue, x)) == True{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      h

def Lv.home_reg(+st: S.State, +ue: S.Ue, +x: B.Bytes(), +h: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.home(st, S.Ue.with_reg(ue, x)) == True{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      h

def Lv.home_tmsi(+st: S.State, +ue: S.Ue, +x: U32, +h: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.home(st, S.Ue.with_tmsi(ue, x)) == True{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      h

# A phase that holds no pair chains and needs no first one.
def Lv.chain_none(+st: S.State, +key: U32, +p: S.Phase, +en: {S.Phase.nh(p) == None{} : Maybe<&2, S.Nh>}) -> {Lv.chain_put(st, key, S.Phase.nh(p)) == True{} : Bool}:
  sn = Equal.sym(Maybe<&2, S.Nh>, S.Phase.nh(p), None{}, en)
  (%sn : {Lv.chain_put(st, key, _) == True{} : Bool}; {==})

def Lv.seed_none(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +ep: {S.Ue.phase(ue) == p : S.Phase}, +en: {S.Phase.nh(p) == None{} : Maybe<&2, S.Nh>}, +acts: List<&2, N.Act>) -> {Lv.seeds(st, S.Put{key, ue}, acts) == True{} : Bool}:
  sp = Equal.sym(S.Phase, S.Ue.phase(ue), p, ep)
  sn = Equal.sym(Maybe<&2, S.Nh>, S.Phase.nh(p), None{}, en)
  (%sp : {Lv.seed(st, key, S.Phase.nh(_), acts) == True{} : Bool}; (%sn : {Lv.seed(st, key, _, acts) == True{} : Bool}; {==}))

# A context that held a pair needs no first one.
def Lv.paired_seed(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == p : S.Phase}, +h: {Tb.Table.present(S.Nh, S.Phase.nh(p)) == True{} : Bool}, +n: Maybe<&2, S.Nh>, +acts: List<&2, N.Act>) -> {Lv.seed(st, key, n, acts) == True{} : Bool}:
  sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, S.State.ues(st)), Some{ue}, eg)
  sp = Equal.sym(S.Phase, S.Ue.phase(ue), p, ep)
  sh = Equal.sym(Bool, Tb.Table.present(S.Nh, S.Phase.nh(p)), True{}, h)
  P.Bool.or_r(Lv.firsts(n, S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st))), key, acts), Bool.not(Lv.unpaired(st, key)), (%sg : {Bool.not(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(_)))) == True{} : Bool}; (%sp : {Bool.not(Bool.not(Tb.Table.present(S.Nh, S.Phase.nh(_)))) == True{} : Bool}; (%sh : {Bool.not(Bool.not(_)) == True{} : Bool}; {==}))))

def Lv.put_ok(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +ep: {S.Ue.phase(ue) == p : S.Phase}, +ek: {Lv.held(st, key) == True{} : Bool}, +eg: {S.Phase.guarded(p) == True{} : Bool}, +ei: {S.Phase.idle(p) == True{} : Bool}, +ec: {Lv.chain_put(st, key, S.Phase.nh(p)) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.free(st, S.Put{key, ue}) == True{} : Bool}:
  sep = Equal.sym(S.Phase, S.Ue.phase(ue), p, ep)
  %sep : {Bool.and(Lv.chain_put(st, key, S.Phase.nh(_)), Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(_), Bool.and(S.Phase.idle(_), Lv.home(st, ue))))) == True{} : Bool}
  P.Bool.and_intro(Lv.chain_put(st, key, S.Phase.nh(p)), Bool.and(Lv.keyed(st, key), Bool.and(S.Phase.guarded(p), Bool.and(S.Phase.idle(p), Lv.home(st, ue)))), ec, P.Bool.and_intro(Lv.keyed(st, key), Bool.and(S.Phase.guarded(p), Bool.and(S.Phase.idle(p), Lv.home(st, ue))), Lv.keyed_of(st, key, Lv.held_live(st, key, ek)), P.Bool.and_intro(S.Phase.guarded(p), Bool.and(S.Phase.idle(p), Lv.home(st, ue)), eg, P.Bool.and_intro(S.Phase.idle(p), Lv.home(st, ue), ei, ehome))))

def Lw.place(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +ep: {S.Ue.phase(ue) == p : S.Phase}, +eg: {S.Phase.guarded(p) == True{} : Bool}, +ei: {S.Phase.idle(p) == True{} : Bool}, +en: {S.Phase.nh(p) == None{} : Maybe<&2, S.Nh>}, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.place(st, key, ue)) == True{} : Bool}:
  +vs = S.Ues.evicted(key, ue, S.State.ues(st))
  +gone = Gmm.Gmm.sessions(S.Ues.evicted(key, ue, S.State.ues(st)), S.State.sessions(st))
  Lv.join(st, Up.N4.deletions(gone, S.State.pfcp_seq(st)), (S.Put{key, ue}, Gmm.Gmm.evict(vs)), Lv.dels(st, gone, S.State.pfcp_seq(st), Lv.srows_held(vs, S.State.sessions(st)), Lv.krows_held(st, vs)), Lv.leaf(st, S.Put{key, ue}, Gmm.Gmm.evict(vs), Lw.evict(st, vs, Lv.keys_sift(S.Victims{key, ue}, S.State.ues(st))), Lv.put_ok(st, key, ue, p, ep, ek, eg, ei, Lv.chain_none(st, key, p, en), ehome), Lv.evict_stops(S.Put{key, ue}, vs), Lv.seed_none(st, key, ue, p, ep, en, Gmm.Gmm.evict(vs))))

def Lw.forget(+st: S.State, +key: U32) -> {Lv.okf(st, Gmm.Gmm.forget(st, key)) == True{} : Bool}:
  +gone = S.Sessions.of_ue(key, S.State.sessions(st))
  Lv.join(st, Up.N4.deletions(gone, S.State.pfcp_seq(st)), (S.Del{key}, []), Lv.dels(st, gone, S.State.pfcp_seq(st), Lv.srows_sift(S.SOf{key}, S.State.sessions(st)), Lv.krows_of(st, key)), {==})

# 5GSM
# ----

# A NAS context replaced keeps the phase's pair.
def Lv.chains_ctx(+q: S.Phase, +c: Sec.Nas.Ctx) -> {Lv.chains(S.Phase.nh(S.Phase.with_ctx(q, c)), S.Phase.nh(q)) == True{} : Bool}:
  match q:
    case S.ContextSetup{guard, ctx, +nh, response, complete}:
      Lv.chains_same(nh)
    case S.Registered{ctx, +nh, released}:
      Lv.chains_same(nh)
    case S.Switching{guard, ctx, +nh, released}:
      Lv.chains_same(nh)
    case S.Handover{ctx, +nh, source, leg}:
      Lv.chains_same(nh)
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lv.free_ctx(+st: S.State, +key: U32, +ue: S.Ue, +c: Sec.Nas.Ctx, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.free(st, S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), c)}) == True{} : Bool}:
  +q = S.Phase.with_ctx(S.Ue.phase(ue), c)
  P.Bool.and_intro(Lv.chain(st, key, S.Phase.nh(q)), Bool.and(S.Phase.guarded(q), S.Phase.idle(q)), Lv.chain_at(st, key, ue, S.Ue.phase(ue), eg, {==}, S.Phase.nh(q), Lv.chains_ctx(S.Ue.phase(ue), c)), Lv.g_ctx(S.Ue.phase(ue), c, ec))

def Lw.out_dl(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +plain: B.Bytes(), +ek: {Lv.held(st, key) == True{} : Bool}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.okf(st, N.Out.dl(key, ue, ctx, plain)) == True{} : Bool}:
  +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.Ciphered{}, plain)
  +x : N.Act = N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), Sec.Nas.Protected.msg(p)}
  Lv.leaf(st, S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))}, [x], Lv.cons(st, x, [], Lv.held_live(st, key, ek), {==}), Lv.free_ctx(st, key, ue, Sec.Nas.Protected.ctx(p), eg, ec), {==}, {==})

# A verified message not acted on: the context's phase keeps its NAS context.
def Lw.out_verified(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +why: String, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.ok(st, N.Out.verified(key, ue, ctx, why)) == True{} : Bool}:
  Lv.free_homed(st, S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), ctx)}, S.State.ues(st), Lv.free_ctx(st, key, ue, ctx, eg, ec))

def Lw.to_ue_ctx(+st: S.State, +key: U32, +ue: S.Ue, +psi: U32, +sm: B.Bytes(), +ctx: Maybe<&2, Sec.Nas.Ctx>, +ek: {Lv.held(st, key) == True{} : Bool}, +ec: {S.Phase.ctx(S.Ue.phase(ue)) == ctx : Maybe<&2, Sec.Nas.Ctx>}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Gsm.Gsm.to_ue_ctx(key, ue, psi, sm, ctx)) == True{} : Bool}:
  match ctx:
    case None{}:
      {==}
    case Some{+c}:
      Lw.out_dl(st, key, ue, c, Gsm.Gsm.dl_transport(psi, sm), ek, Lv.has_ctx(S.Ue.phase(ue), c, ec), eg)

# The UE of a session is told only when it holds a context.
def Lw.to_ue_m(+st: S.State, +key: U32, +psi: U32, +sm: B.Bytes(), +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Gsm.Gsm.to_ue_m(key, psi, sm, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.to_ue_ctx(st, key, ue, psi, sm, S.Phase.ctx(S.Ue.phase(ue)), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, em)), {==}, em)

def Lw.one(+st: S.State, +skey: U32, +s: S.Session, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}) -> {Lv.srows([(skey, s)], S.State.sessions(st)) == True{} : Bool}:
  P.Bool.and_intro(Lv.tagged(S.Session.tag(s), S.State.sessions(st)), True{}, es, {==})

def Lw.give_up(+st: S.State, +skey: U32, +s: S.Session, +sm: B.Bytes(), +seq: U32, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.give_up(st, skey, s, sm, seq)) == True{} : Bool}:
  +m = Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st))
  Lv.join(st, Gsm.Gsm.to_ue_m(S.Session.ue(s), S.Session.psi(s), sm, m), Up.N4.deletions([(skey, s)], seq), Lw.to_ue_m(st, S.Session.ue(s), S.Session.psi(s), sm, m, {==}), Lv.dels(st, [(skey, s)], seq, Lw.one(st, skey, s, es), Lv.one_kept(st, skey, s, ekd)))

def Lw.abort(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +cause: U32, +seq: U32, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.abort(st, skey, s, pti, cause, seq)) == True{} : Bool}:
  Lw.give_up(st, skey, s, Gsm.Gsm.reject(S.Session.psi(s), pti, cause), seq, es, ekd)

def Lw.drop(+st: S.State, +skey: U32, +s: S.Session, +seq: U32, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.drop(st, skey, s, seq)) == True{} : Bool}:
  Lw.give_up(st, skey, s, Gsm.Gsm.release_command(S.Session.psi(s)), seq, es, ekd)


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

# A session drawn free: no row holds its address, TEID or key, so it evicts
# live rows only and conflicts with no session being deleted, whose tag is
# none.
def Lv.notf(+x: Bool, +e: {x == False{} : Bool}) -> {Bool.not(x) == True{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, P.Refute.true_false(e))
    case False{}:
      {==}

def Lv.miss_k(+t: S.Session, +m: Maybe<&2, S.Session>, +b: Bool, +e: {Bool.not(Tb.Table.present(S.Session, Tb.Table.hit(S.Session, t, m, b))) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.Refute.bool(e))
    case False{}:
      {==}

def Lv.miss_m(+t: S.Session, +m: Maybe<&2, S.Session>, +b: Bool, +e: {Bool.not(Tb.Table.present(S.Session, Tb.Table.hit(S.Session, t, m, b))) == True{} : Bool}) -> {Bool.not(Tb.Table.present(S.Session, m)) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.not(Tb.Table.present(S.Session, m)) == True{} : Bool}, P.Refute.bool(e))
    case False{}:
      e

def Lv.nc4(+a: Bool, +b: Bool, +c: Bool, +x: Bool, +y: Bool, +ea: {a == False{} : Bool}, +eb: {b == False{} : Bool}, +ec: {c == False{} : Bool}, +ex: {x == False{} : Bool}) -> {Bool.not(Bool.or(a, Bool.or(b, Bool.or(c, Bool.and(x, y))))) == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, P.Refute.true_false(ea))
    case False{}:
      match b:
        case True{}:
          Empty.absurd({Bool.not(True{}) == True{} : Bool}, P.Refute.true_false(eb))
        case False{}:
          match c:
            case True{}:
              Empty.absurd({Bool.not(True{}) == True{} : Bool}, P.Refute.true_false(ec))
            case False{}:
              match x:
                case True{}:
                  Empty.absurd({Bool.not(y) == True{} : Bool}, P.Refute.true_false(ex))
                case False{}:
                  {==}

def Lv.nc(+h: Bool, +a: Bool, +b: Bool, +c: Bool, +x: Bool, +y: Bool, +ea: {a == False{} : Bool}, +eb: {b == False{} : Bool}, +ec: {c == False{} : Bool}, ex: {h == False{} : Bool} -> {x == False{} : Bool}) -> {Bool.or(h, Bool.not(Bool.or(a, Bool.or(b, Bool.or(c, Bool.and(x, y)))))) == True{} : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      Lv.nc4(a, b, c, x, y, ea, eb, ec, ex({==}))

def Lv.vict(+b: Bool, +c: Bool, +n: Bool, +x: Bool, +y: Bool, +h: Bool, +eb: {b == False{} : Bool}, +ec: {c == False{} : Bool}, f: {x == True{} : Bool} -> {h == True{} : Bool}) -> {Bool.or(Bool.not(Bool.and(n, Bool.or(b, Bool.or(c, Bool.and(x, y))))), h) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.or(Bool.not(Bool.and(n, True{})), h) == True{} : Bool}, P.Refute.true_false(eb))
    case False{}:
      match c:
        case True{}:
          Empty.absurd({Bool.or(Bool.not(Bool.and(n, True{})), h) == True{} : Bool}, P.Refute.true_false(ec))
        case False{}:
          match n:
            case False{}:
              {==}
            case True{}:
              match x:
                case False{}:
                  {==}
                case True{}:
                  match y:
                    case False{}:
                      {==}
                    case True{}:
                      f({==})

def Lv.same_present_r(+x: U32, +m: Maybe<&2, U32>, +e: {S.Maybe.same_u32(Some{x}, m) == True{} : Bool}) -> {Tb.Table.present(U32, m) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Tb.Table.present(U32, None{}) == True{} : Bool}, P.Refute.bool(e))
    case Some{y}:
      {==}

def Lv.untag(+key: U32, +t: S.Session, +eh: {S.SPhase.live(S.Session.phase(t)) == False{} : Bool}) -> {S.Maybe.same_u32(Some{key}, S.Session.tag(t)) == False{} : Bool}:
  seh = Equal.sym(Bool, S.SPhase.live(S.Session.phase(t)), False{}, eh)
  (%seh : {S.Maybe.same_u32(Some{key}, Tb.Table.hit(U32, S.Session.ue(t), None{}, _)) == False{} : Bool}; {==})

def Lv.fresh(+s: S.Session, +key: U32, +et: {S.Session.tag(s) == Some{key} : Maybe<&2, U32>}, +seid: U32, ss: Tb.Table(S.Session), +fi: {Bool.not(S.Sessions.holds(S.Ip{}, S.Session.ip(s), ss)) == True{} : Bool}, +ft: {Bool.not(S.Sessions.holds(S.Teid{}, S.Session.teid(s), ss)) == True{} : Bool}, +fk: {Bool.not(Tb.Table.has(S.Session, seid, ss)) == True{} : Bool}) -> {Bool.and(Lv.sieved(S.SVictims{seid, s}, ss), Lv.clear(seid, s, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +hi = P.Bool.not_true(Bool.or(U32.is_eq(S.Session.ip(t), S.Session.ip(s)), S.Sessions.holds(S.Ip{}, S.Session.ip(s), more)), fi)
      +ht = P.Bool.not_true(Bool.or(U32.is_eq(S.Session.teid(t), S.Session.teid(s)), S.Sessions.holds(S.Teid{}, S.Session.teid(s), more)), ft)
      +ek = Lv.miss_k(t, Tb.Table.get(S.Session, seid, more), U32.is_eq(k, seid), fk)
      +fk2 = Lv.miss_m(t, Tb.Table.get(S.Session, seid, more), U32.is_eq(k, seid), fk)
      +ei = Lv.u32_ne(S.Session.ip(s), S.Session.ip(t), P.Bool.or_false_l(U32.is_eq(S.Session.ip(t), S.Session.ip(s)), S.Sessions.holds(S.Ip{}, S.Session.ip(s), more), hi))
      +eh = Lv.u32_ne(S.Session.teid(s), S.Session.teid(t), P.Bool.or_false_l(U32.is_eq(S.Session.teid(t), S.Session.teid(s)), S.Sessions.holds(S.Teid{}, S.Session.teid(s), more), ht))
      +fi2 = Lv.notf(S.Sessions.holds(S.Ip{}, S.Session.ip(s), more), P.Bool.or_false_r(U32.is_eq(S.Session.ip(t), S.Session.ip(s)), S.Sessions.holds(S.Ip{}, S.Session.ip(s), more), hi))
      +ft2 = Lv.notf(S.Sessions.holds(S.Teid{}, S.Session.teid(s), more), P.Bool.or_false_r(U32.is_eq(S.Session.teid(t), S.Session.teid(s)), S.Sessions.holds(S.Teid{}, S.Session.teid(s), more), ht))
      +x = S.Maybe.same_u32(S.Session.tag(s), S.Session.tag(t))
      +y = U32.is_eq(S.Session.psi(s), S.Session.psi(t))
      +h = S.SPhase.live(S.Session.phase(t))
      +rv = Lv.vict(U32.is_eq(S.Session.ip(s), S.Session.ip(t)), U32.is_eq(S.Session.teid(s), S.Session.teid(t)), Bool.not(U32.is_eq(k, seid)), x, y, h, ei, eh, e => Lv.held_tag(t, Lv.same_present_r(key, S.Session.tag(t), (%et : {S.Maybe.same_u32(_, S.Session.tag(t)) == True{} : Bool}; e))))
      set = Equal.sym(Maybe<&2, U32>, S.Session.tag(s), Some{key}, et)
      +rc = Lv.nc(h, U32.is_eq(k, seid), U32.is_eq(S.Session.ip(s), S.Session.ip(t)), U32.is_eq(S.Session.teid(s), S.Session.teid(t)), x, y, ek, ei, eh, e => (%set : {S.Maybe.same_u32(_, S.Session.tag(t)) == False{} : Bool}; Lv.untag(key, t, e)))
      +rest = Lv.fresh(s, key, et, seid, more, fi2, ft2, fk2)
      +sm = Lv.sieved(S.SVictims{seid, s}, more)
      +cm = Lv.clear(seid, s, more)
      P.Bool.and_intro(Bool.and(Bool.or(Bool.not(S.SSieve.keeps(S.SVictims{seid, s}, k, t)), h), sm), Bool.and(Bool.or(h, Bool.not(S.SRow.conflicts(seid, s, k, t))), cm), P.Bool.and_intro(Bool.or(Bool.not(S.SSieve.keeps(S.SVictims{seid, s}, k, t)), h), sm, rv, P.Bool.and_true_l(sm, cm, rest)), P.Bool.and_intro(Bool.or(h, Bool.not(S.SRow.conflicts(seid, s, k, t))), cm, rc, P.Bool.and_true_r(sm, cm, rest)))

# A key no session holds is kept.
def Lv.kept_miss(+st: S.State, +k: U32, +m: Maybe<&2, S.Session>, +em: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == m : Maybe<&2, S.Session>}, +fk: {Bool.not(Tb.Table.present(S.Session, m)) == True{} : Bool}) -> {Lv.kept(st, k) == True{} : Bool}:
  match m:
    case None{}:
      sem = Equal.sym(Maybe<&2, S.Session>, Tb.Table.get(S.Session, k, S.State.sessions(st)), None{}, em)
      P.Bool.or_l(Lv.live_m(Tb.Table.get(S.Session, k, S.State.sessions(st))), Bool.not(S.Sessions.unique(S.State.sessions(st))), (%sem : {Lv.live_m(_) == True{} : Bool}; {==}))
    case Some{t}:
      Empty.absurd({Lv.kept(st, k) == True{} : Bool}, P.Refute.bool(fk))

# The one path that puts a session: its UE is the context the message names.
def Lw.create(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, +ip: U32, +teid: U32, +seid: U32, +v4v6: Bool, +dns: Bool, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}, +es: {S.Ids.seid(seid) == True{} : Bool}, +fk: {Bool.not(Tb.Table.has(S.Session, seid, S.State.sessions(st))) == True{} : Bool}, +fi: {Bool.not(S.Sessions.holds(S.Ip{}, ip, S.State.sessions(st))) == True{} : Bool}, +ft: {Bool.not(S.Sessions.holds(S.Teid{}, teid, S.State.sessions(st))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.create(st, key, ue, ctx, cfg, psi, pti, ip, teid, seid, v4v6, dns)) == True{} : Bool}:
  +seq = S.State.pfcp_seq(st)
  +ph = S.Phase.with_ctx(S.Ue.phase(ue), ctx)
  +s : S.Session = S.Session{S.SId{key, psi, ip, teid}, S.SVar{[], seq, S.Creating{S.Guard{0}, pti, Gsm.Gsm.accept(cfg, psi, pti, ip, dns, v4v6), Up.N4.establish(cfg, seid, ip, teid, seq)}}}
  +x : N.Act = N.Pfcp{Some{key}, Up.N4.establish(cfg, seid, ip, teid, seq)}
  +y : N.Act = N.TimerStart{Some{key}, seid, Up.N4.t1_ms()}
  +vs = S.Sessions.evicted(seid, s, S.State.sessions(st))
  +rep = S.Ues.rephase(key, ph, S.State.ues(st))
  +ek = Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))
  hr = Equal.sym(Bool, Tb.Table.has(S.Ue, key, rep), Tb.Table.has(S.Ue, key, S.State.ues(st)), Lv.has_rephase(key, key, ph, S.State.ues(st)))
  +old = Bool.and(Tb.Table.has(S.Ue, key, rep), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s))))
  +put = Bool.and(S.Ids.seid(seid), old)
  +d = Up.N4.deletions(vs, U32.add(seq, 1))
  +fr = Lv.fresh(s, key, {==}, seid, S.State.sessions(st), fi, ft, fk)
  +sv = Lv.sieved(S.SVictims{seid, s}, S.State.sessions(st))
  +cl = Lv.clear(seid, s, S.State.sessions(st))
  +hd = Lv.dels(st, vs, U32.add(seq, 1), Lv.srows_sift(S.SVictims{seid, s}, S.State.sessions(st)), Lv.krows_sift(st, S.SVictims{seid, s}, P.Bool.and_true_l(sv, cl, fr)))
  +hg = P.Bool.and_intro(Lv.homed(st, S.Rephase{key, ph}, S.State.ues(st)), True{}, Lv.free_homed(st, S.Rephase{key, ph}, S.State.ues(st), Lv.free_ctx(st, key, ue, ctx, eg, ec)), {==})
  +ho = P.Bool.and_intro(Tb.Table.has(S.Ue, key, rep), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s))), (%hr : {_ == True{} : Bool}; Lv.get_has(S.State.ues(st), key, ue, eg)), {==})
  +hp = P.Bool.and_intro(cl, Bool.and(S.Ids.seid(seid), old), P.Bool.and_true_r(sv, cl, fr), P.Bool.and_intro(S.Ids.seid(seid), old, es, ho))
  +hdo = Lv.ok_in(st, d, rep, hd)
  eu = Equal.sym(Tb.Table(S.Ue), PT.Tk.ues(N.Out.tx(d), rep), rep, PT.Tk.ues_deletions(vs, U32.add(seq, 1), rep))
  +hpl = Lv.ojoin(st, d, (S.PutSession{seid, s}, []), rep, hdo, P.Bool.and_intro(True{}, Lv.homed(st, S.PutSession{seid, s}, PT.Tk.ues(N.Out.tx(d), rep)), {==}, (%eu : {Lv.homed(st, S.PutSession{seid, s}, _) == True{} : Bool}; hp)), {==})
  +ha = P.Bool.and_intro(Lv.acts(st, [x, y]), Lv.homed(st, S.Both{S.Rephase{key, ph}, S.BumpSeq{1}}, S.State.ues(st)), Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], Lv.s_start(st, Some{key}, seid, ek, Lv.kept_miss(st, seid, Tb.Table.get(S.Session, seid, S.State.sessions(st)), {==}, fk)), {==})), hg)
  Lv.ojoin(st, (S.Both{S.Rephase{key, ph}, S.BumpSeq{1}}, [x, y]), Gsm.Gsm.place(st, seid, s, U32.add(seq, 1)), S.State.ues(st), P.Bool.and_intro(True{}, Bool.and(Lv.acts(st, [x, y]), Lv.homed(st, S.Both{S.Rephase{key, ph}, S.BumpSeq{1}}, S.State.ues(st))), {==}, ha), hpl, Lv.calm_join(d, (S.PutSession{seid, s}, []), Lv.calm_sx(N.Out.tx(d), PW.Sx.deletions(vs, U32.add(seq, 1))), {==}))

# What a request checks out to keys its session with a local SEID, and draws
# an address, a TEID and a SEID no session holds.
def Ck.ip_ok(m: Maybe<&2, U32>, +ss: Tb.Table(S.Session)) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+a}:
      Bool.not(S.Sessions.holds(S.Ip{}, a, ss))

def Ck.teid_ok(m: Maybe<&2, U32>, +ss: Tb.Table(S.Session)) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+t}:
      Bool.not(S.Sessions.holds(S.Teid{}, t, ss))

def Ck.seid_ok(m: Maybe<&2, U32>, +ss: Tb.Table(S.Session)) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+k}:
      Bool.and(S.Ids.seid(k), Bool.not(Tb.Table.has(S.Session, k, ss)))

def Ck.ok(c: Gsm.Check, +ss: Tb.Table(S.Session)) -> Bool:
  match c:
    case Gsm.Refuse{cause}:
      True{}
    case Gsm.Go{v4v6, dns, +ip, +teid, +seid}:
      Bool.and(Ck.seid_ok(Some{seid}, ss), Bool.and(Ck.ip_ok(Some{ip}, ss), Ck.teid_ok(Some{teid}, ss)))

def Ck.grant(+v4v6: Bool, +dns: Bool, +ip: Maybe<&2, U32>, +teid: Maybe<&2, U32>, +seid: Maybe<&2, U32>, +ss: Tb.Table(S.Session), +hi: {Ck.ip_ok(ip, ss) == True{} : Bool}, +ht: {Ck.teid_ok(teid, ss) == True{} : Bool}, +hs: {Ck.seid_ok(seid, ss) == True{} : Bool}) -> {Ck.ok(Gsm.Gsm.grant(v4v6, dns, ip, teid, seid), ss) == True{} : Bool}:
  match ip teid seid:
    case Some{+a} Some{+t} Some{+k}:
      P.Bool.and_intro(Ck.seid_ok(Some{k}, ss), Bool.and(Ck.ip_ok(Some{a}, ss), Ck.teid_ok(Some{t}, ss)), hs, P.Bool.and_intro(Ck.ip_ok(Some{a}, ss), Ck.teid_ok(Some{t}, ss), hi, ht))
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

# A drawn SEID is even.
def Ck.even(+w: U32) -> {S.Ids.odd(U32.and(4294967294, w)) == False{} : Bool}:
  match w:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Ck.free_l(+z: Bool, +x: Bool, +e: {Bool.not(Bool.or(z, x)) == True{} : Bool}) -> {Bool.not(z) == True{} : Bool}:
  Lv.notf(z, P.Bool.or_false_l(z, x, P.Bool.not_true(Bool.or(z, x), e)))

def Ck.free_r(+z: Bool, +x: Bool, +e: {Bool.not(Bool.or(z, x)) == True{} : Bool}) -> {Bool.not(x) == True{} : Bool}:
  Lv.notf(x, P.Bool.or_false_r(z, x, P.Bool.not_true(Bool.or(z, x), e)))

def Ck.hit(+k: U32, +ss: Tb.Table(S.Session), +later: Maybe<&2, U32>, +ok: Bool, +eok: {Bool.not(Bool.or(U32.is_eq(k, 0), Tb.Table.has(S.Session, k, ss))) == ok : Bool}, +ev: {S.Ids.odd(k) == False{} : Bool}, +hl: {Ck.seid_ok(later, ss) == True{} : Bool}) -> {Ck.seid_ok(Tb.Table.hit(U32, k, later, ok), ss) == True{} : Bool}:
  match ok:
    case True{}:
      +nz = Ck.free_l(U32.is_eq(k, 0), Tb.Table.has(S.Session, k, ss), eok)
      +nh = Ck.free_r(U32.is_eq(k, 0), Tb.Table.has(S.Session, k, ss), eok)
      sev = Equal.sym(Bool, S.Ids.odd(k), False{}, ev)
      P.Bool.and_intro(S.Ids.seid(k), Bool.not(Tb.Table.has(S.Session, k, ss)), (%sev : {Bool.and(Bool.not(_), Bool.not(U32.is_eq(k, 0))) == True{} : Bool}; nz), nh)
    case False{}:
      hl

def Ck.draw(+ss: Tb.Table(S.Session), +words: B.Bytes()) -> {Ck.seid_ok(Gsm.Ip.draw(Gsm.Seid{}, ss, words), ss) == True{} : Bool}:
  match words:
    case a <> b <> c <> d <> more:
      +k = U32.and(4294967294, N.Ngap.of_big([a, b, c, d]))
      Ck.hit(k, ss, Gsm.Ip.draw(Gsm.Seid{}, ss, more), Bool.not(Bool.or(U32.is_eq(k, 0), Tb.Table.has(S.Session, k, ss))), {==}, Ck.even(N.Ngap.of_big([a, b, c, d])), Ck.draw(ss, more))
    case a <> b <> c <> Nil{}:
      {==}
    case a <> b <> Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case Nil{}:
      {==}

def Ck.hit_t(+k: U32, +ss: Tb.Table(S.Session), +later: Maybe<&2, U32>, +ok: Bool, +eok: {Bool.not(Bool.or(U32.is_eq(k, 0), S.Sessions.holds(S.Teid{}, k, ss))) == ok : Bool}, +hl: {Ck.teid_ok(later, ss) == True{} : Bool}) -> {Ck.teid_ok(Tb.Table.hit(U32, k, later, ok), ss) == True{} : Bool}:
  match ok:
    case True{}:
      Ck.free_r(U32.is_eq(k, 0), S.Sessions.holds(S.Teid{}, k, ss), eok)
    case False{}:
      hl

def Ck.draw_t(+ss: Tb.Table(S.Session), +words: B.Bytes()) -> {Ck.teid_ok(Gsm.Ip.draw(Gsm.Teid{}, ss, words), ss) == True{} : Bool}:
  match words:
    case a <> b <> c <> d <> more:
      +k = N.Ngap.of_big([a, b, c, d])
      Ck.hit_t(k, ss, Gsm.Ip.draw(Gsm.Teid{}, ss, more), Bool.not(Bool.or(U32.is_eq(k, 0), S.Sessions.holds(S.Teid{}, k, ss))), {==}, Ck.draw_t(ss, more))
    case a <> b <> c <> Nil{}:
      {==}
    case a <> b <> Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case Nil{}:
      {==}

def Ck.next(+c: U32, +ss: Tb.Table(S.Session), later: Unit -> Maybe<&2, U32>, +used: Bool, +eu: {S.Sessions.holds(S.Ip{}, c, ss) == used : Bool}, hl: {Ck.ip_ok(later(Unit{}), ss) == True{} : Bool}) -> {Ck.ip_ok(Gsm.Ip.next(c, later, used), ss) == True{} : Bool}:
  match used:
    case True{}:
      hl
    case False{}:
      seu = Equal.sym(Bool, S.Sessions.holds(S.Ip{}, c, ss), False{}, eu)
      (%seu : {Bool.not(_) == True{} : Bool}; {==})

def Ck.free_from(+fuel: Nat, +c: U32, +ss: Tb.Table(S.Session)) -> {Ck.ip_ok(Gsm.Ip.free_from(fuel, c, ss), ss) == True{} : Bool}:
  match fuel:
    case 0n:
      {==}
    case 1n+n:
      Ck.next(c, ss, u => Gsm.Ip.free_from(n, U32.add(c, 1), ss), S.Sessions.holds(S.Ip{}, c, ss), {==}, Ck.free_from(n, U32.add(c, 1), ss))

def Ck.alloc_in(+base: U32, +hosts: U32, +ss: Tb.Table(S.Session), +ok: Bool) -> {Ck.ip_ok(Gsm.Ip.alloc_in(base, hosts, ss, ok), ss) == True{} : Bool}:
  match ok:
    case True{}:
      Ck.free_from(U32.to_nat(U32.sub(hosts, 3)), U32.add(base, 2), ss)
    case False{}:
      {==}

def Ck.alloc(+cfg: S.Cfg, +ss: Tb.Table(S.Session)) -> {Ck.ip_ok(Gsm.Ip.alloc(cfg, ss), ss) == True{} : Bool}:
  +prefix = N.Ngap.cap_byte(S.Cfg.prefix(cfg), 0n)
  Ck.alloc_in(N.Ngap.of_big(S.Cfg.pool(cfg)), U32.shln(1, U32.to_nat(U32.sub(32, U32.min(prefix, 30)))), ss, U32.is_le(prefix, 30))

def Ck.allocate(+r: Maybe<&2, U32>, +v4v6: Bool, +dns: Bool, +cfg: S.Cfg, +ss: Tb.Table(S.Session), +entropy: B.Bytes()) -> {Ck.ok(Gsm.Gsm.allocate(r, v4v6, dns, cfg, ss, entropy), ss) == True{} : Bool}:
  match r:
    case Some{cause}:
      {==}
    case None{}:
      Ck.grant(v4v6, dns, Gsm.Ip.alloc(cfg, ss), Gsm.Ip.draw(Gsm.Teid{}, ss, Gsm.Ip.around(entropy, 20n)), Gsm.Ip.draw(Gsm.Seid{}, ss, Gsm.Ip.around(entropy, 24n)), ss, Ck.alloc(cfg, ss), Ck.draw_t(ss, Gsm.Ip.around(entropy, 20n)), Ck.draw(ss, Gsm.Ip.around(entropy, 24n)))

def Ck.validate(+cfg: S.Cfg, +psi: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, +up: Bool, +ss: Tb.Table(S.Session), +entropy: B.Bytes()) -> {Ck.ok(Gsm.Gsm.validate(cfg, psi, mm_opts, sm_opts, up, ss, entropy), ss) == True{} : Bool}:
  +t = I.Opts.t1(I.Iei.pdu_session_type(), sm_opts)
  Ck.allocate(Gsm.Gsm.pick(Bool.and(U32.is_lt(0, psi), U32.is_lt(psi, 16)), 95, Gsm.Gsm.pick(Gsm.Gsm.request_type_ok(I.Opts.t1(I.Iei.request_type(), mm_opts)), 31, Gsm.Gsm.pick(Gsm.Gsm.dnn_ok(cfg, I.Opts.find(I.Iei.dnn(), mm_opts)), 27, Gsm.Gsm.pick(Gsm.Gsm.slice_ok(cfg, I.Opts.find(I.Iei.s_nssai(), mm_opts)), 70, Gsm.Gsm.pick(up, 38, Gsm.Gsm.pick(Gsm.Gsm.type_ok(t), 50, None{})))))), Gsm.Gsm.v4v6(t), Gsm.Gsm.dns_asked(I.Opts.find(I.Iei.extended_pco(), sm_opts)), cfg, ss, entropy)

def Lw.checked(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, +c: Gsm.Check, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}, +eck: {Ck.ok(c, S.State.sessions(st)) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.checked(st, key, ue, ctx, cfg, psi, pti, c)) == True{} : Bool}:
  match c:
    case Gsm.Refuse{+cause}:
      Lv.ok_of(st, Gsm.Gsm.dl(key, ue, ctx, psi, Gsm.Gsm.reject(psi, pti, cause)), Lw.out_dl(st, key, ue, ctx, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause)), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg)), ec, eg))
    case Gsm.Go{+v4v6, +dns, +ip, +teid, +seid}:
      +ok_s = Ck.seid_ok(Some{seid}, S.State.sessions(st))
      +ok_r = Bool.and(Ck.ip_ok(Some{ip}, S.State.sessions(st)), Ck.teid_ok(Some{teid}, S.State.sessions(st)))
      +hs = P.Bool.and_true_l(ok_s, ok_r, eck)
      +hr = P.Bool.and_true_r(ok_s, ok_r, eck)
      +nk = Bool.not(Tb.Table.has(S.Session, seid, S.State.sessions(st)))
      Lw.create(st, key, ue, ctx, cfg, psi, pti, ip, teid, seid, v4v6, dns, eg, ec, P.Bool.and_true_l(S.Ids.seid(seid), nk, hs), P.Bool.and_true_r(S.Ids.seid(seid), nk, hs), P.Bool.and_true_l(Ck.ip_ok(Some{ip}, S.State.sessions(st)), Ck.teid_ok(Some{teid}, S.State.sessions(st)), hr), P.Bool.and_true_r(Ck.ip_ok(Some{ip}, S.State.sessions(st)), Ck.teid_ok(Some{teid}, S.State.sessions(st)), hr))

def Lw.gsm_with_cfg(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +psi: U32, +pti: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +cfg: Maybe<&2, S.Cfg>, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.with_cfg(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy, cfg)) == True{} : Bool}:
  match cfg:
    case None{}:
      Lw.out_verified(st, key, ue, ctx, "5GSM: no configuration", ec, eg)
    case Some{+c}:
      Lw.checked(st, key, ue, ctx, c, psi, pti, Gsm.Gsm.validate(c, psi, mm_opts, sm_opts, Up.N4.up(st), S.State.sessions(st), entropy), eg, ec, Ck.validate(c, psi, mm_opts, sm_opts, Up.N4.up(st), S.State.sessions(st), entropy))

def Lw.establish(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +psi: U32, +pti: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.establish(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy)) == True{} : Bool}:
  Lw.gsm_with_cfg(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy, S.State.config(st), eg, ec)

def Lw.message(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +mm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Sm.Sm>, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.message(st, key, ue, ctx, mm_opts, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      Lw.out_verified(st, key, ue, ctx, "5GSM: message not understood", ec, eg)
    case Done{Sm.Sm{+psi, +pti, mt, fields, +opts}}:
      match mt:
        case Sm.EstablishmentRequest{}:
          Lw.establish(st, key, ue, ctx, psi, pti, mm_opts, opts, entropy, eg, ec)
        case Sm.EstablishmentAccept{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec, eg)
        case Sm.EstablishmentReject{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec, eg)
        case Sm.ModificationRequest{}:
          Lv.ok_of(st, Gsm.Gsm.dl(key, ue, ctx, psi, Gsm.Gsm.modification_reject(psi, pti)), Lw.out_dl(st, key, ue, ctx, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.modification_reject(psi, pti)), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg)), ec, eg))
        case Sm.ModificationReject{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec, eg)
        case Sm.ReleaseRequest{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec, eg)
        case Sm.ReleaseCommand{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec, eg)
        case Sm.ReleaseComplete{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec, eg)
        case Sm.SmStatus{}:
          Lw.out_verified(st, key, ue, ctx, "5GSM: message not expected", ec, eg)

def Lw.n1(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +mm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +container: B.Bytes(), +n1: Bool, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.n1(st, key, ue, ctx, mm_opts, entropy, container, n1)) == True{} : Bool}:
  match n1:
    case True{}:
      Lw.message(st, key, ue, ctx, mm_opts, entropy, Sm.Sm.read(container), eg, ec)
    case False{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: payload container not N1 SM information", ec, eg)

def Lw.ul_transport(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +entropy: B.Bytes(), +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}) -> {Lv.ok(st, Gsm.Gsm.ul_transport(st, key, ue, ctx, fields, opts, entropy)) == True{} : Bool}:
  Lw.n1(st, key, ue, ctx, opts, entropy, I.Fields.lve2(fields), U32.is_eq(I.Fields.byte1(fields), 1), eg, ec)


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
def Lv.owns(+skey: U32, +s: S.Session, +ss: Tb.Table(S.Session), +e: {Lv.found(Some{(skey, s)}, ss) == True{} : Bool}) -> {Lv.tagged(S.Session.tag(s), ss) == True{} : Bool}:
  P.Bool.and_true_l(Lv.tagged(S.Session.tag(s), ss), Bool.or(S.SPhase.knows(S.Session.phase(s), S.Session.known(s)), Bool.not(S.Sessions.known(ss))), e)

def Lv.knows(+skey: U32, +s: S.Session, +ss: Tb.Table(S.Session), +e: {Lv.found(Some{(skey, s)}, ss) == True{} : Bool}) -> {Bool.or(S.SPhase.knows(S.Session.phase(s), S.Session.known(s)), Bool.not(S.Sessions.known(ss))) == True{} : Bool}:
  P.Bool.and_true_r(Lv.tagged(S.Session.tag(s), ss), Bool.or(S.SPhase.knows(S.Session.phase(s), S.Session.known(s)), Bool.not(S.Sessions.known(ss))), e)

# The session as the UPF answered it, under its UP SEID, keeps its tag.
def Lv.tag_var(+s: S.Session, +u: B.Bytes(), +q: U32, +ss: Tb.Table(S.Session), +es: {Lv.tagged(S.Session.tag(s), ss) == True{} : Bool}) -> {Lv.tagged(S.Session.tag(S.Session.with_var(s, S.SVar{u, q, S.Session.phase(s)})), ss) == True{} : Bool}:
  match s:
    case S.Session{id, var}:
      es

def Lw.setup_gone(+st: S.State, +skey: U32, +s: S.Session, +up_seid: B.Bytes(), +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.setup_gone(st, skey, s, up_seid)) == True{} : Bool}:
  +s2 = S.Session.with_var(s, S.SVar{up_seid, S.Session.seq(s), S.Session.phase(s)})
  Lv.dels(st, [(skey, s2)], S.State.pfcp_seq(st), Lw.one(st, skey, s2, Lv.tag_var(s, up_seid, S.Session.seq(s), S.State.sessions(st), es)), Lv.one_kept(st, skey, s2, ekd))

def Lw.setup_ue(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +accept: Sm.Sm, +up_seid: B.Bytes(), +ue: S.Ue, +ctx: Maybe<&2, Sec.Nas.Ctx>, +cfg: Maybe<&2, S.Cfg>, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +em: {Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {S.Phase.ctx(S.Ue.phase(ue)) == ctx : Maybe<&2, Sec.Nas.Ctx>}, +e8: {Nat.is_eq(List.length(&2, U32, up_seid), 8n) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.setup_ue(st, skey, s, pti, accept, up_seid, ue, ctx, cfg)) == True{} : Bool}:
  match ctx cfg:
    case Some{+c} Some{+cf}:
      +p : Sec.Nas.Protected = Sec.Nas.protect(c, Sec.Ciphered{}, Gsm.Gsm.dl_transport(S.Session.psi(s), Sm.Sm.write(accept)))
      +x : N.Act = N.PduSetup{S.Ue.assoc(ue), S.Ue.stream(ue), S.Session.ue(s), S.Ue.ran_id(ue), S.Session.psi(s), S.Cfg.sst(cf), Sec.Nas.Protected.msg(p), Gsm.Gsm.transfer(cf, S.Session.teid(s))}
      +y : N.Act = N.TimerStart{Some{S.Session.ue(s)}, skey, Up.N4.t1_ms()}
      +ek = Lv.has_live(st, S.Session.ue(s), Lv.get_has(S.State.ues(st), S.Session.ue(s), ue, em))
      +v : S.SVar = S.SVar{up_seid, S.Session.seq(s), S.Setting{S.Guard{0}, pti}}
      +hv = P.Bool.or_l(Lv.var_ok(v), Bool.not(S.Sessions.known(S.State.sessions(st))), e8)
      Lv.leaf(st, S.Both{S.Rephase{S.Session.ue(s), S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))}, S.Revar{skey, v}}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], Lv.s_start(st, Some{S.Session.ue(s)}, skey, ek, ekd), {==})), P.Bool.and_intro(Lv.free(st, S.Rephase{S.Session.ue(s), S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(p))}), Lv.revar_ok(st, v), Lv.free_ctx(st, S.Session.ue(s), ue, Sec.Nas.Protected.ctx(p), em, Lv.has_ctx(S.Ue.phase(ue), c, ec)), hv), {==}, {==})
    case Some{c} None{}:
      Lw.setup_gone(st, skey, s, up_seid, es, ekd)
    case None{} Some{cf}:
      Lw.setup_gone(st, skey, s, up_seid, es, ekd)
    case None{} None{}:
      Lw.setup_gone(st, skey, s, up_seid, es, ekd)

# 5GMM
# ----
# Each lemma follows one procedure; key is the context it acts for, live.

def Lw.release(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.release(st, key, ue, cause)) == True{} : Bool}:
  +ur = S.Ue.with_phase(ue, S.Releasing{S.Guard{0}})
  +rel : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}
  +ts : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  +more : List<&2, N.Act> = ts <> Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause)
  Lv.prepend(st, rel, N.Out.also(Gmm.Gmm.place(st, key, ur), more), Lv.held_live(st, key, ek), Lv.also(st, Gmm.Gmm.place(st, key, ur), more, Lw.place(st, key, ur, S.Releasing{S.Guard{0}}, Lv.p_phase(ue, S.Releasing{S.Guard{0}}), {==}, {==}, {==}, ek, Lv.home_phase(st, ue, S.Releasing{S.Guard{0}}, ehome)), Lv.cons(st, ts, Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause), Lv.ue_start(st, key, N.Ue.guard_ms(), ek), Lw.ho_leg_drop(st, key, S.Ue.phase(ue), cause, ek)), Lv.stops_cons(N.Out.tx(Gmm.Gmm.place(st, key, ur)), ts, Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause), {==}, Lv.leg_drop_stops(N.Out.tx(Gmm.Gmm.place(st, key, ur)), key, S.Ue.phase(ue), cause))), {==})

def Lw.refuse(+st: S.State, +key: U32, +ue: S.Ue, +nas: B.Bytes(), +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.refuse(st, key, ue, nas)) == True{} : Bool}:
  Lv.prepend(st, Gmm.Gmm.dl(key, ue, nas), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified())), Lv.held_live(st, key, ek), Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek, ehome), {==})

def Lw.reject(+st: S.State, +key: U32, +ue: S.Ue, +cause: U32, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.reject(st, key, ue, cause)) == True{} : Bool}:
  Lw.refuse(st, key, ue, Gmm.Gmm.registration_reject(cause), ek, ehome)

def Lw.auth_reject(+st: S.State, +key: U32, +ue: S.Ue, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.auth_reject(st, key, ue)) == True{} : Bool}:
  Lv.prepend(st, Gmm.Gmm.dl(key, ue, Gmm.Gmm.authentication_reject()), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure())), Lv.held_live(st, key, ek), Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure()), ek, ehome), {==})


def Lw.identity_ask(+st: S.State, +key: U32, +ue: S.Ue, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.identity_ask(st, key, ue)) == True{} : Bool}:
  +nas = Gmm.Gmm.identity_request()
  +ue2 = S.Ue.with_dl(ue, S.Identifying{S.Guard{0}}, nas)
  +x : N.Act = Gmm.Gmm.dl(key, ue2, nas)
  +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  Lv.also(st, Gmm.Gmm.place(st, key, ue2), [x, y], Lw.place(st, key, ue2, S.Identifying{S.Guard{0}}, Lv.p_dl(ue, S.Identifying{S.Guard{0}}, nas), {==}, {==}, {==}, ek, Lv.home_dl(st, ue, S.Identifying{S.Guard{0}}, nas, ehome)), Lv.cons(st, x, [y], Lv.held_live(st, key, ek), Lv.cons(st, y, [], Lv.ue_start(st, key, N.Ue.guard_ms(), ek), {==})), {==})

def Lw.challenge(+st: S.State, +key: U32, +ue: S.Ue, +sub: Au.Subscriber, +snn: B.Bytes(), +entropy: B.Bytes(), +resynced: Bool, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.challenge(st, key, ue, sub, snn, entropy, resynced)) == True{} : Bool}:
  +sub2 = Au.Subscriber.with_sqn(sub, Au.Sqn.next(Au.Subscriber.sqn(sub)))
  +av = Au.Av.make(sub2, snn, List.take(&2, U32, entropy, 16n))
  +nas = Gmm.Gmm.auth_request(0, av)
  +ue2 = S.Ue.with_dl(ue, S.Authenticating{S.Guard{0}, av, resynced, Au.Subscriber.supi(sub2)}, nas)
  +x : N.Act = Gmm.Gmm.dl(key, ue2, nas)
  +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  +tx : S.Tx = S.Subs{Au.Subscribers.update(sub2, S.State.subs(st))}
  Lv.join(st, Gmm.Gmm.place(st, key, ue2), (tx, [x, y]), Lw.place(st, key, ue2, S.Authenticating{S.Guard{0}, av, resynced, Au.Subscriber.supi(sub2)}, Lv.p_dl(ue, S.Authenticating{S.Guard{0}, av, resynced, Au.Subscriber.supi(sub2)}, nas), {==}, {==}, {==}, ek, Lv.home_dl(st, ue, S.Authenticating{S.Guard{0}, av, resynced, Au.Subscriber.supi(sub2)}, nas, ehome)), Lv.leaf(st, tx, [x, y], Lv.cons(st, x, [y], Lv.held_live(st, key, ek), Lv.cons(st, y, [], Lv.ue_start(st, key, N.Ue.guard_ms(), ek), {==})), {==}, {==}, {==}))

def Lw.by_sub(+st: S.State, +key: U32, +ue: S.Ue, +cfg: S.Cfg, +m: Maybe<&2, Au.Subscriber>, +entropy: B.Bytes(), +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.by_sub(st, key, ue, cfg, m, entropy)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.reject(st, key, ue, 7, ek, ehome)
    case Some{+sub}:
      Lw.challenge(st, key, ue, sub, Au.Ausf.snn(S.Cfg.plmn(cfg)), entropy, False{}, ek, ehome)

def Lw.by_supi(+st: S.State, +key: U32, +ue: S.Ue, +cfg: S.Cfg, +r: Result<&2, &2, B.Err, Su.Supi>, +entropy: B.Bytes(), +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.by_supi(st, key, ue, cfg, r, entropy)) == True{} : Bool}:
  match r:
    case Fail{e}:
      Lw.reject(st, key, ue, 7, ek, ehome)
    case Done{Su.Imsi{+plmn, +msin}}:
      Lw.by_sub(st, key, ue, cfg, Au.Subscribers.find(List.append(&2, U32, Pl.Plmn.mcc(plmn), List.append(&2, U32, Pl.Plmn.mnc(plmn), msin)), S.State.subs(st)), entropy, ek, ehome)

def Lw.with_cfg(+st: S.State, +key: U32, +ue: S.Ue, +suci: Su.Suci, +entropy: B.Bytes(), +cfg: Maybe<&2, S.Cfg>, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.with_cfg(st, key, ue, suci, entropy, cfg)) == True{} : Bool}:
  match cfg:
    case None{}:
      Lw.reject(st, key, ue, 7, ek, ehome)
    case Some{+c}:
      Lw.by_supi(st, key, ue, c, Su.Suci.deconceal(S.Cfg.suci_key(c), suci), entropy, ek, ehome)

def Lw.identified(+st: S.State, +key: U32, +ue: S.Ue, +suci: Su.Suci, +entropy: B.Bytes(), +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.identified(st, key, ue, suci, entropy)) == True{} : Bool}:
  Lw.with_cfg(st, key, ue, suci, entropy, S.State.config(st), ek, ehome)

def Lw.proceed(+st: S.State, +key: U32, +ue: S.Ue, +how: Gmm.Start, +entropy: B.Bytes(), +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.proceed(st, key, ue, how, entropy)) == True{} : Bool}:
  match how:
    case Gmm.Identified{+suci}:
      Lw.identified(st, key, ue, suci, entropy, ek, ehome)
    case Gmm.Ask{}:
      Lw.identity_ask(st, key, ue, ek, ehome)
    case Gmm.Unknown{}:
      Lw.reject(st, key, ue, 7, ek, ehome)

def Lw.register(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +r: Mi.MobileId.Res(), +ek: {Lv.held(st, key) == True{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.register(st, key, assoc, stream, entropy, ran, nas, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+id}:
      +fresh : S.Ue = Gmm.Gmm.fresh(assoc, ran, stream, nas)
      Lv.join(st, (S.BumpUe{key}, []), Gmm.Gmm.proceed(st, key, fresh, Gmm.Gmm.start_of(id), entropy), {==}, Lw.proceed(st, key, fresh, Gmm.Gmm.start_of(id), entropy, ek, Lv.home_on(st, fresh, ea)))

def Lw.serve(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +ran: B.Bytes(), +nas: B.Bytes(), +ek: {Lv.held(st, key) == True{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.serve(st, key, assoc, stream, ran, nas)) == True{} : Bool}:
  +fresh : S.Ue = Gmm.Gmm.fresh(assoc, ran, stream, nas)
  Lv.join(st, (S.BumpUe{key}, []), Gmm.Gmm.refuse(st, key, fresh, Gmm.Gmm.service_reject()), {==}, Lw.refuse(st, key, fresh, Gmm.Gmm.service_reject(), ek, Lv.home_on(st, fresh, ea)))

def Lw.initial_mm(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +m: Mm.Mm, +ek: {Lv.held(st, key) == True{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.initial_mm(st, key, assoc, stream, entropy, ran, nas, m)) == True{} : Bool}:
  match m:
    case Mm.Mm{mt, +fields, opts}:
      match mt:
        case Mm.RegistrationRequest{}:
          Lw.register(st, key, assoc, stream, entropy, ran, nas, Mi.MobileId.read(I.Fields.lve2(fields)), ek, ea)
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
          Lw.serve(st, key, assoc, stream, ran, nas, ek, ea)
        case Mm.ServiceReject{}:
          {==}

def Lw.initial_nas(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +r: Result<&2, &2, B.Err, Mm.Mm>, +ek: {Lv.held(st, key) == True{} : Bool}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.initial_nas(st, key, assoc, stream, entropy, ran, nas, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+m}:
      Lw.initial_mm(st, key, assoc, stream, entropy, ran, nas, m, ek, ea)

def Lw.initial_key(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +m: Maybe<&2, U32>, +em: {S.State.fresh(st) == m : Maybe<&2, U32>}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.initial_key(st, assoc, stream, entropy, ran, nas, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.initial_nas(st, key, assoc, stream, entropy, ran, nas, Mm.Mm.read(nas), Lv.fresh_held(st, key, em), ea)

def Lw.initial(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +v: V.InitialUEMessage.View, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.initial(st, assoc, stream, entropy, v)) == True{} : Bool}:
  match v:
    case V.InitialUEMessage.View{+ran_ue_ngap_id, +nas_pdu, userlocationinformation, rrcestablishmentcause, fiveg_s_tmsi, amfsetid, allowednssai, selectedplmnidentity, iabnodeindication, cemodebsupport_indicator, npn_accessinformation}:
      Lw.initial_key(st, assoc, stream, entropy, ran_ue_ngap_id, Gmm.Gmm.unprotected(nas_pdu), S.State.fresh(st), {==}, ea)

def Lw.initial_of_view(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, V.InitialUEMessage.View>, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      Lw.initial(st, assoc, stream, entropy, v, ea)


def Lw.secure(+st: S.State, +key: U32, +ue: S.Ue, +supi: B.Digits(), +k_amf: B.Bytes(), +nea: Sec.Nas.Ea, +nia: Sec.Nas.Ia, +caps: B.Bytes(), +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.secure(st, key, ue, supi, k_amf, nea, nia, caps)) == True{} : Bool}:
  +ctx : Sec.Nas.Ctx = Sec.Ctx{Sec.Keys{Kd.kdf.k_nas_int(k_amf, Sec.Nas.Ia.id(nia)), Kd.kdf.k_nas_enc(k_amf, Sec.Nas.Ea.id(nea)), nea, nia, 1}, Sec.Nas.Count.zero(), None{}}
  +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.IntegrityNew{}, Gmm.Gmm.security_mode_command(U32.or(U32.shln(Sec.Nas.Ea.id(nea), 4n), Sec.Nas.Ia.id(nia)), S.Ue.ngksi(ue), caps))
  +ue2 = S.Ue.with_dl(S.Ue.with_supi(ue, supi), S.SecurityMode{S.Guard{0}, Sec.Nas.Protected.ctx(p), k_amf}, Sec.Nas.Protected.msg(p))
  +x : N.Act = Gmm.Gmm.dl(key, ue2, Sec.Nas.Protected.msg(p))
  +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  Lv.also(st, Gmm.Gmm.place(st, key, ue2), [x, y], Lw.place(st, key, ue2, S.SecurityMode{S.Guard{0}, Sec.Nas.Protected.ctx(p), k_amf}, Lv.p_dl(S.Ue.with_supi(ue, supi), S.SecurityMode{S.Guard{0}, Sec.Nas.Protected.ctx(p), k_amf}, Sec.Nas.Protected.msg(p)), {==}, {==}, {==}, ek, Lv.home_dl(st, S.Ue.with_supi(ue, supi), S.SecurityMode{S.Guard{0}, Sec.Nas.Protected.ctx(p), k_amf}, Sec.Nas.Protected.msg(p), Lv.home_supi(st, ue, supi, ehome))), Lv.cons(st, x, [y], Lv.held_live(st, key, ek), Lv.cons(st, y, [], Lv.ue_start(st, key, N.Ue.guard_ms(), ek), {==})), {==})

def Lw.algorithms(+st: S.State, +key: U32, +ue: S.Ue, +supi: B.Digits(), +k_amf: B.Bytes(), +caps: B.Bytes(), +mea: Maybe<&2, Sec.Nas.Ea>, +mia: Maybe<&2, Sec.Nas.Ia>, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.algorithms(st, key, ue, supi, k_amf, caps, mea, mia)) == True{} : Bool}:
  match mea mia:
    case Some{+a} Some{+b}:
      Lw.secure(st, key, ue, supi, k_amf, a, b, caps, ek, ehome)
    case Some{a} None{}:
      Lw.reject(st, key, ue, 23, ek, ehome)
    case None{} Some{b}:
      Lw.reject(st, key, ue, 23, ek, ehome)
    case None{} None{}:
      Lw.reject(st, key, ue, 23, ek, ehome)

def Lw.keys(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +cfg: Maybe<&2, S.Cfg>, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.keys(st, key, ue, av, supi, cfg)) == True{} : Bool}:
  match cfg:
    case Some{+c}:
      +caps = N.Ue.caps(ue)
      Lw.algorithms(st, key, ue, supi, Au.Ausf.k_amf(av, Au.Ausf.snn(S.Cfg.plmn(c)), supi), caps, Gmm.Alg.pick_ea(S.Cfg.nea(c), N.Ngap.cap_byte(caps, 0n)), Gmm.Alg.pick_ia(S.Cfg.nia(c), N.Ngap.cap_byte(caps, 1n)), ek, ehome)
    case None{}:
      Lw.auth_reject(st, key, ue, ek, ehome)

def Lw.verified(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +ok: Bool, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.verified(st, key, ue, av, supi, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.keys(st, key, ue, av, supi, S.State.config(st), ek, ehome)
    case False{}:
      Lw.auth_reject(st, key, ue, ek, ehome)

def Lw.response(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +res: Maybe<&2, B.Bytes()>, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.response(st, key, ue, av, supi, res)) == True{} : Bool}:
  match res:
    case None{}:
      Lw.auth_reject(st, key, ue, ek, ehome)
    case Some{+r}:
      Lw.verified(st, key, ue, av, supi, Au.Ausf.verify(av, r), ek, ehome)

def Lw.resynced(+st: S.State, +key: U32, +ue: S.Ue, +sub: Au.Subscriber, +cfg: S.Cfg, +entropy: B.Bytes(), +m: Maybe<&2, B.Bytes()>, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.resynced(st, key, ue, sub, cfg, entropy, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.auth_reject(st, key, ue, ek, ehome)
    case Some{+sqn_ms}:
      Lw.challenge(st, key, ue, Au.Subscriber.with_sqn(sub, sqn_ms), Au.Ausf.snn(S.Cfg.plmn(cfg)), entropy, True{}, ek, ehome)

def Lw.resync_sub(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +auts: B.Bytes(), +entropy: B.Bytes(), +cfg: S.Cfg, +m: Maybe<&2, Au.Subscriber>, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.resync_sub(st, key, ue, av, auts, entropy, cfg, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.auth_reject(st, key, ue, ek, ehome)
    case Some{+sub}:
      Lw.resynced(st, key, ue, sub, cfg, entropy, Au.Ausf.resync(sub, Au.Av.rand(av), auts), ek, ehome)

def Lw.resync(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +auts: B.Bytes(), +entropy: B.Bytes(), +supi: B.Digits(), +cfg: Maybe<&2, S.Cfg>, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.resync(st, key, ue, av, auts, entropy, supi, cfg)) == True{} : Bool}:
  match cfg:
    case Some{+c}:
      Lw.resync_sub(st, key, ue, av, auts, entropy, c, Au.Subscribers.find(supi, S.State.subs(st)), ek, ehome)
    case None{}:
      Lw.auth_reject(st, key, ue, ek, ehome)

def Lw.failure_kind(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +auts: Maybe<&2, B.Bytes()>, +entropy: B.Bytes(), +retry: Bool, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.failure_kind(st, key, ue, av, supi, auts, entropy, retry)) == True{} : Bool}:
  match auts retry:
    case Some{+a} True{}:
      Lw.resync(st, key, ue, av, a, entropy, supi, S.State.config(st), ek, ehome)
    case Some{a} False{}:
      Lw.auth_reject(st, key, ue, ek, ehome)
    case None{} True{}:
      Lw.auth_reject(st, key, ue, ek, ehome)
    case None{} False{}:
      Lw.auth_reject(st, key, ue, ek, ehome)

def Lw.failure(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +resynced: Bool, +supi: B.Digits(), +cause: U32, +auts: Maybe<&2, B.Bytes()>, +entropy: B.Bytes(), +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.failure(st, key, ue, av, resynced, supi, cause, auts, entropy)) == True{} : Bool}:
  Lw.failure_kind(st, key, ue, av, supi, auts, entropy, Bool.and(U32.is_eq(cause, 21), Bool.not(resynced)), ek, ehome)

def Lw.identity_answer(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Mi.MobileId.Res(), +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.identity_answer(st, key, ue, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      Lw.reject(st, key, ue, 7, ek, ehome)
    case Done{Mi.NoId{}}:
      Lw.reject(st, key, ue, 7, ek, ehome)
    case Done{Mi.Suci{+suci}}:
      Lw.identified(st, key, ue, suci, entropy, ek, ehome)
    case Done{Mi.Guti{plmn, region, amf, tmsi}}:
      Lw.reject(st, key, ue, 7, ek, ehome)
    case Done{Mi.Imei{digits}}:
      Lw.reject(st, key, ue, 7, ek, ehome)
    case Done{Mi.Imeisv{digits}}:
      Lw.reject(st, key, ue, 7, ek, ehome)
    case Done{Mi.STmsi{amf, tmsi}}:
      Lw.reject(st, key, ue, 7, ek, ehome)


def Lw.phase(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +p: S.Phase, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.phase(st, key, ue, entropy, mt, fields, opts, p)) == True{} : Bool}:
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
          Lw.response(st, key, ue, av, supi, I.Opts.find(I.Iei.authentication_response_parameter(), opts), ek, ehome)
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{guard, old, nh, response, complete}:
          {==}
        case S.Registered{old, nh, released}:
          {==}
        case S.Switching{guard, old, nh, released}:
          {==}
        case S.Handover{old, nh, source, leg}:
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
          Lw.failure(st, key, ue, av, resynced, supi, I.Fields.byte1(fields), I.Opts.find(I.Iei.authentication_failure_parameter(), opts), entropy, ek, ehome)
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{guard, old, nh, response, complete}:
          {==}
        case S.Registered{old, nh, released}:
          {==}
        case S.Switching{guard, old, nh, released}:
          {==}
        case S.Handover{old, nh, source, leg}:
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
          Lw.identity_answer(st, key, ue, entropy, Mi.MobileId.read(I.Fields.lve1(fields)), ek, ehome)
        case S.Authenticating{guard, av, resynced, supi}:
          {==}
        case S.SecurityMode{guard, old, k_amf}:
          {==}
        case S.ContextSetup{guard, old, nh, response, complete}:
          {==}
        case S.Registered{old, nh, released}:
          {==}
        case S.Switching{guard, old, nh, released}:
          {==}
        case S.Handover{old, nh, source, leg}:
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

def Lw.plain(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Mm.Mm>, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.plain(st, key, ue, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{Mm.Mm{+mt, +fields, +opts}}:
      Lw.phase(st, key, ue, entropy, mt, fields, opts, S.Ue.phase(ue), ek, ehome)


def Lv.app_assoc(xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +zs: List<&2, N.Act>) -> {List.append(&2, N.Act, xs, List.append(&2, N.Act, ys, zs)) == List.append(&2, N.Act, List.append(&2, N.Act, xs, ys), zs) : List<&2, N.Act>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> more:
      Equal.cong(List<&2, N.Act>, List<&2, N.Act>, l => x <> l, List.append(&2, N.Act, more, List.append(&2, N.Act, ys, zs)), List.append(&2, N.Act, List.append(&2, N.Act, more, ys), zs), Lv.app_assoc(more, ys, zs))

def Lv.also_join(+a: N.GOut(), +b: N.GOut(), +more: List<&2, N.Act>) -> {N.Out.also(N.Out.join(a, b), more) == N.Out.join(a, N.Out.also(b, more)) : N.GOut()}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          e = Lv.app_assoc(aa, ab, more)
          (%e : {(S.Both{ta, tb}, _) == (S.Both{ta, tb}, List.append(&2, N.Act, aa, List.append(&2, N.Act, ab, more))) : N.GOut()}; {==})

# A context in a phase without a pair holds none.
def Lv.unpaired_at(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == p : S.Phase}) -> {Bool.not(Tb.Table.present(S.Nh, S.Phase.nh(p))) == True{} : Bool} -> {Lv.unpaired(st, key) == True{} : Bool}:
  sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, S.State.ues(st)), Some{ue}, eg)
  sp = Equal.sym(S.Phase, S.Ue.phase(ue), p, ep)
  h => (%sg : {Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(_))) == True{} : Bool}; (%sp : {Bool.not(Tb.Table.present(S.Nh, S.Phase.nh(_))) == True{} : Bool}; h))

# Security Mode Complete: the context put takes the first pair of the chain
# from its Security Mode's K_AMF and the KgNB Initial Context Setup sends it.
def Lv.seed_first(+st: S.State, +key: U32, +ue: S.Ue, +ue2: S.Ue, +ph: S.Phase, +g: S.Guard, +old: Sec.Nas.Ctx, +k_amf: B.Bytes(), +k_gnb: B.Bytes(), +ctx: Sec.Nas.Ctx, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == S.SecurityMode{g, old, k_amf} : S.Phase}, +ep2: {S.Ue.phase(ue2) == S.ContextSetup{S.Guard{0}, ctx, S.Nh.initial(k_amf, k_gnb), False{}, False{}} : S.Phase}, +assoc: U32, +stream: U32, +ran: B.Bytes(), +cfg: S.Cfg, +caps: B.Bytes(), +nas: B.Bytes(), +rest: List<&2, N.Act>) -> {Lv.seeds(st, S.Put{key, ue2}, N.Ics{assoc, stream, key, ran, cfg, caps, k_gnb, nas} <> rest) == True{} : Bool}:
  +acts : List<&2, N.Act> = N.Ics{assoc, stream, key, ran, cfg, caps, k_gnb, nas} <> rest
  +n = S.Nh.initial(k_amf, k_gnb)
  sp2 = Equal.sym(S.Phase, S.Ue.phase(ue2), S.ContextSetup{S.Guard{0}, ctx, n, False{}, False{}}, ep2)
  sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, S.State.ues(st)), Some{ue}, eg)
  sp = Equal.sym(S.Phase, S.Ue.phase(ue), S.SecurityMode{g, old, k_amf}, ep)
  hi = P.Bool.or_l(N.Act.seeds(k_amf, key, n, N.Ics{assoc, stream, key, ran, cfg, caps, k_gnb, nas}), N.Acts.seeds(k_amf, key, n, rest), P.Bool.and_intro(U32.is_eq(key, key), S.Nh.same(n, n), P.U32.is_eq_refl(key), Lv.nh_refl(n)))
  h1 : {Lv.firsts(S.Phase.nh(S.Ue.phase(ue2)), S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st))), key, acts) == True{} : Bool} = (%sp2 : {Lv.firsts(S.Phase.nh(_), S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st))), key, acts) == True{} : Bool}; (%sg : {Lv.firsts(Some{n}, S.Ue.mode_k_amf(_), key, acts) == True{} : Bool}; (%sp : {Lv.firsts(Some{n}, S.Phase.mode_k_amf(_), key, acts) == True{} : Bool}; hi)))
  P.Bool.or_l(Lv.firsts(S.Phase.nh(S.Ue.phase(ue2)), S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st))), key, acts), Bool.not(Lv.unpaired(st, key)), h1)

def Lw.sm_complete(+st: S.State, +key: U32, +ue: S.Ue, +k_amf: B.Bytes(), +ctx: Sec.Nas.Ctx, +count: Sec.Nas.Count, +opts: List<&2, I.Ie>, +cfg: Maybe<&2, S.Cfg>, +m: Maybe<&2, U32>, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}, +g: S.Guard, +old: Sec.Nas.Ctx, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == S.SecurityMode{g, old, k_amf} : S.Phase}) -> {Lv.okf(st, Gmm.Gmm.sm_complete(st, key, ue, k_amf, ctx, count, opts, cfg, m)) == True{} : Bool}:
  match cfg m:
    case Some{+c} Some{+tmsi}:
      +reg = I.Bytes.or(I.Opts.find(I.Iei.nas_message_container(), opts), S.Ue.reg(ue))
      +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.Ciphered{}, Gmm.Gmm.registration_accept(c, tmsi))
      +k_gnb = Kd.kdf.k_gnb(k_amf, Sec.Nas.Count.value(count))
      +ph : S.Phase = S.ContextSetup{S.Guard{0}, Sec.Nas.Protected.ctx(p), S.Nh.initial(k_amf, k_gnb), False{}, False{}}
      +ue2 = S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(ue, ph, Sec.Nas.Protected.msg(p)), reg), tmsi)
      +x : N.Act = N.Ics{S.Ue.assoc(ue2), S.Ue.stream(ue2), key, S.Ue.ran_id(ue2), c, N.Ue.caps(ue2), k_gnb, Sec.Nas.Protected.msg(p)}
      +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
      +vs = S.Ues.evicted(key, ue2, S.State.ues(st))
      +gone = Gmm.Gmm.sessions(vs, S.State.sessions(st))
      +d = Up.N4.deletions(gone, S.State.pfcp_seq(st))
      +ev = Gmm.Gmm.evict(vs)
      +tx : S.Tx = S.Put{key, ue2}
      +epc = Lv.p_ics(ue, ph, Sec.Nas.Protected.msg(p), reg, tmsi)
      +hu = Lv.unpaired_at(st, key, ue, S.SecurityMode{g, old, k_amf}, eg, ep)({==})
      +hp = Lv.put_ok(st, key, ue2, ph, epc, ek, {==}, {==}, P.Bool.or_r(Lv.chain(st, key, S.Phase.nh(ph)), Lv.unpaired(st, key), hu), Lv.home_tmsi(st, S.Ue.with_reg(S.Ue.with_dl(ue, ph, Sec.Nas.Protected.msg(p)), reg), tmsi, Lv.home_reg(st, S.Ue.with_dl(ue, ph, Sec.Nas.Protected.msg(p)), reg, Lv.home_dl(st, ue, ph, Sec.Nas.Protected.msg(p), ehome))))
      +hw = Lv.seed_first(st, key, ue, ue2, ph, g, old, k_amf, k_gnb, Sec.Nas.Protected.ctx(p), eg, ep, epc, S.Ue.assoc(ue2), S.Ue.stream(ue2), S.Ue.ran_id(ue2), c, N.Ue.caps(ue2), Sec.Nas.Protected.msg(p), [y])
      +hl = Lv.leaf(st, tx, List.append(&2, N.Act, ev, [x, y]), Lv.append(st, ev, [x, y], Lw.evict(st, vs, Lv.keys_sift(S.Victims{key, ue2}, S.State.ues(st))), Lv.cons(st, x, [y], Lv.held_live(st, key, ek), Lv.cons(st, y, [], Lv.ue_start(st, key, N.Ue.guard_ms(), ek), {==}))), hp, Lv.stops_app(tx, ev, [x, y], Lv.evict_stops(tx, vs), {==}), Lv.seeds_r(st, tx, ev, [x, y], hw))
      +hj = Lv.join(st, d, (tx, List.append(&2, N.Act, ev, [x, y])), Lv.dels(st, gone, S.State.pfcp_seq(st), Lv.srows_held(vs, S.State.sessions(st)), Lv.krows_held(st, vs)), hl)
      e = Equal.sym(N.GOut(), N.Out.also(N.Out.join(d, (tx, ev)), [x, y]), N.Out.join(d, N.Out.also((tx, ev), [x, y])), Lv.also_join(d, (tx, ev), [x, y]))
      (%e : {Lv.okf(st, _) == True{} : Bool}; hj)
    case Some{c} None{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek, ehome)
    case None{} Some{t}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek, ehome)
    case None{} None{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek, ehome)

def Lw.setup_done(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +response: Bool, +complete: Bool, +both: Bool, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Lv.chain(st, key, Some{nh}) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.setup_done(st, key, ue, guard, ctx, nh, response, complete, both)) == True{} : Bool}:
  match both:
    case True{}:
      +n : N.Act = N.Note{F.Info{}, "5GMM: UE registered"}
      +tx : S.Tx = S.Rephase{key, S.Registered{ctx, nh, None{}}}
      Lv.does_intro(st, tx, [N.TimerCancel{key}, n], Lv.free(st, tx), Lv.stops_cons(tx, N.TimerCancel{key}, [n], Lv.idles_rephase(key, S.Registered{ctx, nh, None{}}, {==}), {==}), {==}, Lv.cons(st, N.TimerCancel{key}, [n], eh, {==}), {==}, P.Bool.and_intro(Lv.chain(st, key, Some{nh}), True{}, ec, {==}))
    case False{}:
      P.Bool.and_intro(Lv.chain(st, key, Some{nh}), True{}, ec, {==})

def Lw.setup_step(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +response: Bool, +complete: Bool, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Lv.chain(st, key, Some{nh}) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.setup_step(st, key, ue, guard, ctx, nh, response, complete)) == True{} : Bool}:
  Lw.setup_done(st, key, ue, guard, ctx, nh, response, complete, Bool.and(response, complete), eh, ec)

def Lw.dereg_answer(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +switch_off: Bool, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.dereg_answer(st, key, ue, ctx, switch_off)) == True{} : Bool}:
  match switch_off:
    case True{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister()), ek, ehome)
    case False{}:
      Lv.prepend(st, Gmm.Gmm.dl(key, ue, Sec.Nas.Protected.msg(Sec.Nas.protect(ctx, Sec.Ciphered{}, Gmm.Gmm.deregistration_accept()))), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister())), Lv.held_live(st, key, ek), Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister()), ek, ehome), {==})

def Lw.deregister(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +kind: U32, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.deregister(st, key, ue, ctx, kind)) == True{} : Bool}:
  Lw.dereg_answer(st, key, ue, ctx, Bool.not(U32.is_eq(U32.and(kind, 8), 0)), ek, ehome)


# A verified 5GMM message: the UL NAS Transport of a registered UE may put a session.
def Lw.sphase(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +count: Sec.Nas.Count, +ctx: Sec.Nas.Ctx, +mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}, +ep: {S.Ue.phase(ue) == p : S.Phase}) -> {Lv.ok(st, Gmm.Gmm.sphase(st, key, ue, entropy, count, ctx, mt, fields, opts, p)) == True{} : Bool}:
  match mt:
    case Mm.RegistrationRequest{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.RegistrationAccept{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.RegistrationComplete{}:
      match p:
        case S.Created{}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Identifying{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Authenticating{guard, av, resynced, supi}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.SecurityMode{guard, old, k_amf}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.ContextSetup{+guard, +old, +nh, +response, +complete}:
          Lv.ok_of(st, Gmm.Gmm.setup_step(st, key, ue, guard, ctx, nh, response, True{}), Lw.setup_step(st, key, ue, guard, ctx, nh, response, True{}, Lv.get_has(S.State.ues(st), key, ue, eg), Lv.chain_at(st, key, ue, S.ContextSetup{guard, old, nh, response, complete}, eg, ep, Some{nh}, Lv.chains_same(nh))))
        case S.Registered{old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Switching{guard, old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Handover{old, nh, source, leg}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Releasing{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.RegistrationReject{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.DeregistrationRequestUe{}:
      match p:
        case S.Created{}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Identifying{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Authenticating{guard, av, resynced, supi}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.SecurityMode{guard, old, k_amf}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.ContextSetup{guard, old, nh, response, complete}:
          Lv.ok_of(st, Gmm.Gmm.deregister(st, key, ue, ctx, I.Fields.byte1(fields)), Lw.deregister(st, key, ue, ctx, I.Fields.byte1(fields), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg)), ehome))
        case S.Registered{old, nh, released}:
          Lv.ok_of(st, Gmm.Gmm.deregister(st, key, ue, ctx, I.Fields.byte1(fields)), Lw.deregister(st, key, ue, ctx, I.Fields.byte1(fields), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg)), ehome))
        case S.Switching{guard, old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Handover{old, nh, source, leg}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Releasing{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.DeregistrationAcceptUe{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.ConfigurationUpdateCommand{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.AuthenticationRequest{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.AuthenticationResponse{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.AuthenticationReject{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.AuthenticationFailure{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.IdentityRequest{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.IdentityResponse{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.SecurityModeCommand{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.SecurityModeComplete{}:
      match p:
        case S.Created{}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Identifying{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Authenticating{guard, av, resynced, supi}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.SecurityMode{+guard, +old, +k_amf}:
          Lv.ok_of(st, Gmm.Gmm.sm_complete(st, key, ue, k_amf, ctx, count, opts, S.State.config(st), Gmm.Gmm.tmsi(S.State.ues(st), List.drop(&2, U32, entropy, 16n))), Lw.sm_complete(st, key, ue, k_amf, ctx, count, opts, S.State.config(st), Gmm.Gmm.tmsi(S.State.ues(st), List.drop(&2, U32, entropy, 16n)), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg)), ehome, guard, old, eg, ep))
        case S.ContextSetup{guard, old, nh, response, complete}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Registered{old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Switching{guard, old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Handover{old, nh, source, leg}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Releasing{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.SecurityModeReject{}:
      match p:
        case S.Created{}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Identifying{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Authenticating{guard, av, resynced, supi}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.SecurityMode{guard, old, k_amf}:
          Lv.ok_of(st, Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified())), Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg)), ehome))
        case S.ContextSetup{guard, old, nh, response, complete}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Registered{old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Switching{guard, old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Handover{old, nh, source, leg}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Releasing{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.Status{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.UlNasTransport{}:
      match p:
        case S.Created{}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Identifying{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Authenticating{guard, av, resynced, supi}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.SecurityMode{guard, old, k_amf}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.ContextSetup{guard, old, nh, response, complete}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Registered{old, nh, released}:
          Lw.ul_transport(st, key, ue, ctx, fields, opts, entropy, eg, ec)
        case S.Switching{guard, old, nh, released}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Handover{old, nh, source, leg}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
        case S.Releasing{guard}:
          Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.DlNasTransport{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.ServiceRequest{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)
    case Mm.ServiceReject{}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not expected in this phase", ec, eg)

def Lw.protected(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +count: Sec.Nas.Count, +ctx: Sec.Nas.Ctx, +r: Result<&2, &2, B.Err, Mm.Mm>, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.protected(st, key, ue, entropy, count, ctx, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      Lw.out_verified(st, key, ue, ctx, "5GMM: message not understood", ec, eg)
    case Done{Mm.Mm{+mt, +fields, +opts}}:
      Lw.sphase(st, key, ue, entropy, count, ctx, mt, fields, opts, S.Ue.phase(ue), eg, ec, ehome, {==})

def Lw.opened(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Sec.Nas.Unprotected>, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.opened(st, key, ue, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{Sec.Unprotected{prot, +plain, +count, +ctx}}:
      Lw.protected(st, key, ue, entropy, count, ctx, Mm.Mm.read(plain), eg, ec, ehome)

def Lw.secured(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +nas: B.Bytes(), +m: Maybe<&2, Sec.Nas.Ctx>, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +em: {S.Phase.ctx(S.Ue.phase(ue)) == m : Maybe<&2, Sec.Nas.Ctx>}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.secured(st, key, ue, entropy, nas, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lv.ok_of(st, Gmm.Gmm.plain(st, key, ue, entropy, Mm.Mm.read(nas)), Lw.plain(st, key, ue, entropy, Mm.Mm.read(nas), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg)), ehome))
    case Some{+ctx}:
      Lw.opened(st, key, ue, entropy, Sec.Nas.unprotect(ctx, nas), eg, Lv.has_ctx(S.Ue.phase(ue), ctx, em), ehome)

def Lw.mm(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +nas: B.Bytes(), +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.ok(st, Gmm.Gmm.mm(st, key, ue, entropy, nas)) == True{} : Bool}:
  Lw.secured(st, key, ue, entropy, nas, S.Phase.ctx(S.Ue.phase(ue)), eg, {==}, ehome)

def Lw.uplink_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +nas: B.Bytes(), +entropy: B.Bytes(), +m: Maybe<&2, S.Ue>, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> {Lv.ok(st, Gmm.Gmm.uplink_ue(st, assoc, key, nas, entropy, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.mm(st, key, ue, entropy, nas, Lv.owned_get(st, assoc, key, ran, ue, eo), Lv.owned_home(st, assoc, key, ran, ue, eo))


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


def Lw.setup_phase(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == p : S.Phase}) -> {Lv.okf(st, Gmm.Gmm.setup_phase(st, key, ue, p)) == True{} : Bool}:
  match p:
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, old, k_amf}:
      {==}
    case S.ContextSetup{+guard, +ctx, +nh, +response, +complete}:
      Lw.setup_step(st, key, ue, guard, ctx, nh, True{}, complete, Lv.get_has(S.State.ues(st), key, ue, eg), Lv.chain_at(st, key, ue, S.ContextSetup{guard, ctx, nh, response, complete}, eg, ep, Some{nh}, Lv.chains_same(nh)))
    case S.Registered{old, nh, released}:
      {==}
    case S.Switching{guard, old, nh, released}:
      {==}
    case S.Handover{old, nh, source, leg}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.ics_response_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +m: Maybe<&2, S.Ue>, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Gmm.Gmm.ics_response_ue(st, assoc, key, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.setup_phase(st, key, ue, S.Ue.phase(ue), Lv.owned_get(st, assoc, key, ran, ue, eo), {==})


def Lw.ics_response_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +m: Maybe<&2, U32>) -> {Lv.okf(st, Gmm.Gmm.ics_response_key(st, assoc, ran, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Lw.ics_response_ue(st, assoc, key, ran, Gmm.Gmm.owner(st, assoc, key, ran), {==})

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
      Lw.release(st, key, ue, cause, Lv.has_held(st, key, Lv.owned_has(st, assoc, key, ran, ue, eo)), Lv.owned_home(st, assoc, key, ran, ue, eo))


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

# A Complete from another association names no UE.
def Lw.unowned(+st: S.State, +assoc: U32, +b: Bool) -> {Lv.okf(st, (S.Keep{}, Gmm.Gmm.unowned(assoc, b))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Lw.release_complete_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +m: Maybe<&2, S.Ue>, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Gmm.Gmm.release_complete_ue(st, assoc, key, m, S.Ue.released(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran))) == True{} : Bool}:
  match m:
    case None{}:
      Lw.unowned(st, assoc, S.Ue.released(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran))
    case Some{+ue}:
      +eh = Lv.owned_has(st, assoc, key, ran, ue, eo)
      +ek = Lv.has_live(st, key, eh)
      +c = N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified())
      +tail : List<&2, N.Act> = List.append(&2, N.Act, Ho.Ho.leg_drop(key, S.Ue.phase(ue), c), [N.Note{F.Info{}, "NGAP: UE context released"}])
      +more = List.append(&2, N.Act, N.Guard.cancel(key, S.Ue.guard(ue)), tail)
      +tx = N.Out.tx(Gmm.Gmm.forget(st, key))
      Lv.also(st, Gmm.Gmm.forget(st, key), more, Lw.forget(st, key), Lv.append(st, N.Guard.cancel(key, S.Ue.guard(ue)), tail, Lv.cancel(st, key, S.Ue.guard(ue), eh), Lv.append(st, Ho.Ho.leg_drop(key, S.Ue.phase(ue), c), [N.Note{F.Info{}, "NGAP: UE context released"}], Lw.ho_leg_drop(st, key, S.Ue.phase(ue), c, Lv.has_held(st, key, eh)), {==})), Lv.stops_app(tx, N.Guard.cancel(key, S.Ue.guard(ue)), tail, Lv.cancel_stops(tx, key, S.Ue.guard(ue), Lv.forget_idles(st, key)), Lv.stops_app(tx, Ho.Ho.leg_drop(key, S.Ue.phase(ue), c), [N.Note{F.Info{}, "NGAP: UE context released"}], Lv.leg_drop_stops(tx, key, S.Ue.phase(ue), c), {==})))


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
def Lw.ho_expiry(+st: S.State, +key: U32, +ue: S.Ue, +leg: S.Leg, +ek: {Lv.held(st, key) == True{} : Bool}) -> {Lv.acts(st, Ho.Ho.expiry(key, ue, leg)) == True{} : Bool}:
  match leg:
    case S.Asked{+t}:
      +c = Ho.Ho.radio(G.CauseRadioNetwork.tngrelocprep_expiry())
      Lv.cons(st, Ho.Ho.preparation_failure(key, ue, c), Ho.Ho.drop(key, S.Asked{t}, c), Lv.held_live(st, key, ek), Lw.ho_drop(st, key, S.Asked{t}, c, ek))
    case S.Acked{+t, +r, +s, +ts}:
      Lw.ho_drop(st, key, S.Acked{t, r, s, ts}, Ho.Ho.radio(G.CauseRadioNetwork.tngrelocoverall_expiry()), ek)

def Lw.ho_expired(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +source: U32, +leg: S.Leg, +ek: {Lv.held(st, key) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == S.Handover{ctx, nh, source, leg} : S.Phase}) -> {Lv.okf(st, Ho.Ho.expired(key, ue, ctx, nh, leg)) == True{} : Bool}:
  +n : List<&2, N.Act> = [N.Note{F.Warn{}, "NGAP: N2 handover guard expired; the UE stays with its owner"}]
  Lv.leaf(st, S.Rephase{key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}}, List.append(&2, N.Act, Ho.Ho.expiry(key, ue, leg), n), Lv.append(st, Ho.Ho.expiry(key, ue, leg), n, Lw.ho_expiry(st, key, ue, leg, ek), {==}), P.Bool.and_intro(Lv.chain(st, key, Some{nh}), True{}, Lv.chain_at(st, key, ue, S.Handover{ctx, nh, source, leg}, eg, ep, Some{nh}, Lv.chains_same(nh)), {==}), Lv.stops_app(S.Rephase{key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}}, Ho.Ho.expiry(key, ue, leg), n, Lv.expiry_stops(S.Rephase{key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}}, key, ue, leg), {==}), {==})

def Lw.retry_if(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +p: S.Phase, +ok: Bool, +ek: {Lv.held(st, key) == True{} : Bool}, +ef: {Lv.free(st, S.Rephase{key, S.Phase.with_guard(p, S.Guard{U32.add(S.Guard.retries(guard), 1)})}) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}) -> {Lv.okf(st, Gmm.Gmm.retry_if(st, key, ue, guard, p, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      +x : N.Act = Gmm.Gmm.dl(key, ue, S.Ue.last_dl(ue))
      +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
      Lv.leaf(st, S.Rephase{key, S.Phase.with_guard(p, S.Guard{U32.add(S.Guard.retries(guard), 1)})}, [x, y], Lv.cons(st, x, [y], Lv.held_live(st, key, ek), Lv.cons(st, y, [], Lv.ue_start(st, key, N.Ue.guard_ms(), ek), {==})), ef, {==}, {==})
    case False{}:
      Lw.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), ek, ehome)

def Lw.expired(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +ek: {Lv.held(st, key) == True{} : Bool}, +ehome: {Lv.home(st, ue) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == p : S.Phase}) -> {Lv.okf(st, Gmm.Gmm.expired(st, key, ue, p)) == True{} : Bool}:
  match p:
    case S.Created{}:
      {==}
    case S.Identifying{+guard}:
      Lw.retry_if(st, key, ue, guard, S.Identifying{guard}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek, {==}, ehome)
    case S.Authenticating{+guard, +av, +resynced, +supi}:
      Lw.retry_if(st, key, ue, guard, S.Authenticating{guard, av, resynced, supi}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek, {==}, ehome)
    case S.SecurityMode{+guard, +ctx, +k_amf}:
      Lw.retry_if(st, key, ue, guard, S.SecurityMode{guard, ctx, k_amf}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek, {==}, ehome)
    case S.ContextSetup{+guard, +ctx, +nh, +response, +complete}:
      Lw.retry_if(st, key, ue, guard, S.ContextSetup{guard, ctx, nh, response, complete}, U32.is_lt(S.Guard.retries(guard), Gmm.Gmm.max_retries()), ek, P.Bool.and_intro(Lv.chain(st, key, Some{nh}), True{}, Lv.chain_at(st, key, ue, S.ContextSetup{guard, ctx, nh, response, complete}, eg, ep, Some{nh}, Lv.chains_same(nh)), {==}), ehome)
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      Lw.release(st, key, ue, N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified()), ek, ehome)
    case S.Handover{+ctx, +nh, +source, +leg}:
      Lw.ho_expired(st, key, ue, ctx, nh, source, leg, ek, eg, ep)
    case S.Releasing{guard}:
      Lv.also(st, Gmm.Gmm.forget(st, key), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}], Lw.forget(st, key), {==}, {==})


def Lw.setup(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +accept: Sm.Sm, +up_seid: B.Bytes(), +m: Maybe<&2, S.Ue>, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +em: {Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)) == m : Maybe<&2, S.Ue>}, +e8: {Nat.is_eq(List.length(&2, U32, up_seid), 8n) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.setup(st, skey, s, pti, accept, up_seid, m)) == True{} : Bool}:
  match m:
    case None{}:
      Lw.setup_gone(st, skey, s, up_seid, es, ekd)
    case Some{+ue}:
      Lw.setup_ue(st, skey, s, pti, accept, up_seid, ue, S.Phase.ctx(S.Ue.phase(ue)), S.State.config(st), es, em, {==}, e8, ekd)

def Lw.established_as(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +accept: Sm.Sm, +ok: Bool, +up: Maybe<&2, B.Bytes()>, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +eu: {Lv.seid_ok(up) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.established_as(st, skey, s, pti, accept, ok, up)) == True{} : Bool}:
  match ok up:
    case True{} Some{+up_seid}:
      Lw.setup(st, skey, s, pti, accept, up_seid, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), es, {==}, eu, ekd)
    case True{} None{}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es, ekd)
    case False{} Some{up_seid}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es, ekd)
    case False{} None{}:
      Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es, ekd)

def Lw.established_phase(+st: S.State, +skey: U32, +s: S.Session, +msg: Pf.Msg, +p: S.SPhase, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +eki: {Lv.kept_if(st, skey, p) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.established_phase(st, skey, s, msg, p)) == True{} : Bool}:
  match p:
    case S.Creating{+guard, +pti, +accept, +request}:
      +ekd = Lv.kept_at(st, skey, S.Creating{guard, pti, accept, request}, eki, {==})
      Lw.established_as(st, skey, s, pti, accept, Up.N4.accepted(Up.N4.cause(msg)), Up.N4.up_seid(msg), es, Lv.up_seid(msg), ekd)
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Deleting{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Lw.established(+st: S.State, +msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}, eg: Lv.Got(m, S.State.sessions(st))) -> {Lv.okf(st, Gsm.Gsm.established(st, msg, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.established_phase(st, skey, s, msg, S.Session.phase(s), Lv.owns(skey, s, S.State.sessions(st), em), Lv.kept_got(st, skey, s, eg))

# Path Switch: a repointed session settled
# ----------------------------------------

def Lw.repoint_done(+st: S.State, +skey: U32, +s: S.Session, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.repoint_done(st, skey, s, False{})) == True{} : Bool}:
  Lv.dels(st, [(skey, s)], S.State.pfcp_seq(st), Lw.one(st, skey, s, es), Lv.one_kept(st, skey, s, ekd))

def Lw.switch_failed(+st: S.State, +key: U32, +ue: S.Ue, +psis: List<&2, U32>, +ek: {Lv.held(st, key) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.switch_failed(key, ue, psis)) == True{} : Bool}:
  +cause = N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified())
  +a : N.Act = N.SwitchFail{S.Ue.assoc(ue), S.Ue.stream(ue), Some{key}, N.Ngap.big(key), S.Ue.ran_id(ue), psis, cause}
  +b : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}
  +c : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  +d : N.Act = N.Note{F.Warn{}, "NGAP: Path Switch failed, no PDU session switched; UE released"}
  Lv.leaf(st, S.Rephase{key, S.Releasing{S.Guard{0}}}, [a, b, c, d], Lv.cons(st, a, [b, c, d], Lv.held_live(st, key, ek), Lv.cons(st, b, [c, d], Lv.held_live(st, key, ek), Lv.cons(st, c, [d], Lv.ue_start(st, key, N.Ue.guard_ms(), ek), {==}))), {==}, {==}, {==})

def Lw.switch_end(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +released: List<&2, U32>, +switched: List<&2, U32>, +cfg: Maybe<&2, S.Cfg>, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Lv.chain(st, key, Some{nh}) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.switch_end(key, ue, ctx, nh, released, switched, cfg)) == True{} : Bool}:
  match switched:
    case Nil{}:
      match cfg:
        case None{}:
          Lw.switch_failed(st, key, ue, List.append(&2, U32, released, []), Lv.has_held(st, key, eh))
        case Some{c}:
          Lw.switch_failed(st, key, ue, List.append(&2, U32, released, []), Lv.has_held(st, key, eh))
    case +p <> +more:
      match cfg:
        case None{}:
          Lw.switch_failed(st, key, ue, List.append(&2, U32, released, p <> more), Lv.has_held(st, key, eh))
        case Some{+c}:
          +a : N.Act = N.SwitchAck{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), N.Ue.caps(ue), nh, p <> more, released, S.Cfg.sst(c)}
          Lv.leaf(st, S.Rephase{key, S.Registered{ctx, nh, None{}}}, [a, N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Path Switch done"}], Lv.cons(st, a, [N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Path Switch done"}], Lv.has_live(st, key, eh), Lv.cons(st, N.TimerCancel{key}, [N.Note{F.Info{}, "NGAP: Path Switch done"}], eh, {==})), P.Bool.and_intro(Lv.chain(st, key, Some{nh}), True{}, ec, {==}), Lv.stops_cons(S.Rephase{key, S.Registered{ctx, nh, None{}}}, a, [N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Path Switch done"}], {==}, Lv.stops_cons(S.Rephase{key, S.Registered{ctx, nh, None{}}}, N.TimerCancel{key}, [N.Note{F.Info{}, "NGAP: Path Switch done"}], Lv.idles_rephase(key, S.Registered{ctx, nh, None{}}, {==}), {==})), {==})

def Lw.switch_next(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +released: List<&2, U32>, +switched: List<&2, U32>, +waits: Bool, +eh: {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}, +ec: {Lv.chain(st, key, Some{nh}) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.switch_next(st, key, ue, guard, ctx, nh, released, switched, waits)) == True{} : Bool}:
  match waits:
    case True{}:
      P.Bool.and_intro(Lv.chain(st, key, Some{nh}), True{}, ec, {==})
    case False{}:
      Lw.switch_end(st, key, ue, ctx, nh, released, switched, S.State.config(st), eh, ec)

def Lw.switch_ue(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, +ue: S.Ue, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == p : S.Phase}) -> {Lv.okf(st, Gsm.Gsm.switch_ue(st, skey, s, ok, ue, p)) == True{} : Bool}:
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
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{+guard, +ctx, +nh, +released}:
      +key = S.Session.ue(s)
      +psi = S.Session.psi(s)
      Lw.switch_next(st, key, ue, guard, ctx, nh, Gsm.Gsm.psi_if(psi, released, Bool.not(ok)), Gsm.Gsm.psi_if(psi, Gsm.Gsm.active_psis(key, S.State.sessions(st)), ok), Gsm.Gsm.waits(key, skey, S.State.sessions(st)), Lv.get_has(S.State.ues(st), key, ue, eg), Lv.chain_at(st, key, ue, S.Switching{guard, ctx, nh, released}, eg, ep, Some{nh}, Lv.chains_same(nh)))
    case S.Handover{ctx, nh, source, leg}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.switch_of(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)) == m : Maybe<&2, S.Ue>}) -> {Lv.okf(st, Gsm.Gsm.switch_of(st, skey, s, ok, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Lw.switch_ue(st, skey, s, ok, ue, S.Ue.phase(ue), em, {==})

def Lw.repointed(+st: S.State, +skey: U32, +s: S.Session, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.repointed(st, skey, s, False{})) == True{} : Bool}:
  Lv.join(st, Gsm.Gsm.repoint_done(st, skey, s, False{}), Gsm.Gsm.switch_of(st, skey, s, False{}, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st))), Lw.repoint_done(st, skey, s, es, ekd), Lw.switch_of(st, skey, s, False{}, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), {==}))

def Lw.repointed_f(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.Session.known(s), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}, +eh: {Tb.Table.has(S.Session, skey, S.State.sessions(st)) == True{} : Bool}) -> {Lv.fine(st, Gsm.Gsm.repointed(st, skey, s, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lv.settled(st, skey, S.Session.up_seid(s), S.Session.seq(s), Gsm.Gsm.switch_of(st, skey, s, True{}, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st))), ekd, eh, kf, Lv.ok_of(st, Gsm.Gsm.switch_of(st, skey, s, True{}, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st))), Lw.switch_of(st, skey, s, True{}, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), {==})))
    case False{}:
      Lv.ok_fine(st, Gsm.Gsm.repointed(st, skey, s, False{}), Lv.ok_of(st, Gsm.Gsm.repointed(st, skey, s, False{}), Lw.repointed(st, skey, s, es, ekd)))

def Lw.modified_as(+st: S.State, +skey: U32, +s: S.Session, +ok: Bool, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.Session.known(s), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}, +eh: {Tb.Table.has(S.Session, skey, S.State.sessions(st)) == True{} : Bool}) -> {Lv.fine(st, Gsm.Gsm.modified_as(st, skey, s, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      +v : S.SVar = S.SVar{S.Session.up_seid(s), S.Session.seq(s), S.Active{}}
      +n : N.Act = N.Note{F.Info{}, "5GSM: PDU session active"}
      P.Bool.or_r(Lv.ok(st, (S.Revar{skey, v}, [N.TimerCancel{skey}, n])), Lv.settles(st, S.Revar{skey, v}, [N.TimerCancel{skey}, n]), P.Bool.and_intro(Lv.kept(st, skey), Bool.and(Tb.Table.has(S.Session, skey, S.State.sessions(st)), Lv.ok(st, (S.Revar{skey, v}, [n]))), ekd, P.Bool.and_intro(Tb.Table.has(S.Session, skey, S.State.sessions(st)), Lv.ok(st, (S.Revar{skey, v}, [n])), eh, kf)))
    case False{}:
      Lv.ok_fine(st, Gsm.Gsm.drop(st, skey, s, S.State.pfcp_seq(st)), Lv.ok_of(st, Gsm.Gsm.drop(st, skey, s, S.State.pfcp_seq(st)), Lw.drop(st, skey, s, S.State.pfcp_seq(st), es, ekd)))

def Lw.modified_phase(+st: S.State, +skey: U32, +s: S.Session, +msg: Pf.Msg, +p: S.SPhase, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.SPhase.knows(p, S.Session.known(s)), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}, +eki: {Lv.kept_if(st, skey, p) == True{} : Bool}, +eh: {Tb.Table.has(S.Session, skey, S.State.sessions(st)) == True{} : Bool}) -> {Lv.fine(st, Gsm.Gsm.modified_phase(st, skey, s, msg, p)) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{+guard, +request}:
      +ekd = Lv.kept_at(st, skey, S.Modifying{guard, request}, eki, {==})
      Lw.modified_as(st, skey, s, Up.N4.accepted(Up.N4.cause(msg)), es, kf, ekd, eh)
    case S.Repointing{+guard, +request}:
      +ekd = Lv.kept_at(st, skey, S.Repointing{guard, request}, eki, {==})
      Lw.repointed_f(st, skey, s, Up.N4.accepted(Up.N4.cause(msg)), es, kf, ekd, eh)
    case S.Deleting{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Lw.modified(+st: S.State, +msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}, eg: Lv.Got(m, S.State.sessions(st)), eh: Lv.Has(m, S.State.sessions(st))) -> {Lv.fine(st, Gsm.Gsm.modified(st, msg, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.modified_phase(st, skey, s, msg, S.Session.phase(s), Lv.owns(skey, s, S.State.sessions(st), em), Lv.knows(skey, s, S.State.sessions(st), em), Lv.kept_got(st, skey, s, eg), eh)

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
    case S.Waiting{S.Setup{}, request, +seq, resent}:
      Lw.assoc_seq(st, msg, U32.is_eq(seq, Pf.Msg.seq(msg)))
    case S.Waiting{S.Heartbeat{}, request, seq, resent}:
      {==}
    case S.Paused{}:
      {==}
    case S.Up{}:
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
    case S.Waiting{S.Setup{}, request, s, resent}:
      {==}
    case S.Waiting{S.Heartbeat{}, request, +s, resent}:
      Lw.alive_seq(st, U32.is_eq(s, seq))
    case S.Paused{}:
      {==}
    case S.Up{}:
      {==}

def Lw.pfcp_k6(+st: S.State, +msg: Pf.Msg, +ok: Bool) -> {Lv.fine(st, Gsm.Gsm.pfcp_k6(st, msg, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.modified(st, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Lv.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Lv.got_by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Lv.has_by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))
    case False{}:
      {==}

def Lw.pfcp_k5(+st: S.State, +msg: Pf.Msg, +kind: U32, +ok: Bool) -> {Lv.fine(st, Gsm.Gsm.pfcp_k5(st, msg, kind, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lv.okf_fine(st, Gsm.Gsm.established(st, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st))), Lw.established(st, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Lv.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Lv.got_by_seq(Pf.Msg.seq(msg), S.State.sessions(st))))
    case False{}:
      Lw.pfcp_k6(st, msg, U32.is_eq(kind, Pf.Type.session_modification_response()))

def Lw.deleted_notes(+st: S.State, +ok: Bool) -> {Lv.actsw(st, Gsm.Gsm.deleted_notes(ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Lw.deleted_phase(+st: S.State, +skey: U32, +msg: Pf.Msg, +p: S.SPhase) -> {Lv.okw(st, Gsm.Gsm.deleted_phase(skey, msg, p)) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Deleting{guard, request}:
      P.Bool.and_intro(Lv.actsw(st, Gsm.Gsm.deleted_notes(Up.N4.accepted(Up.N4.cause(msg)))), True{}, Lw.deleted_notes(st, Up.N4.accepted(Up.N4.cause(msg))), {==})
    case S.Active{}:
      {==}

def Lw.deleted(+st: S.State, +msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> {Lv.okw(st, Gsm.Gsm.deleted(msg, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.deleted_phase(st, skey, msg, S.Session.phase(s))

# The gNB's answer to PDU Session Resource Setup
# ----------------------------------------------

def Lw.modify(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +seq: U32, +tunnel: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.Session.known(s), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.modify(st, skey, s, pti, seq, tunnel)) == True{} : Bool}:
  match tunnel:
    case None{}:
      Lw.drop(st, skey, s, seq, es, ekd)
    case Some{(+gnb_teid, +gnb_addr)}:
      +x : N.Act = N.Pfcp{S.Session.tag(s), Up.N4.modify(S.Session.up_seid(s), gnb_teid, gnb_addr, seq)}
      +y : N.Act = N.TimerStart{S.Session.tag(s), skey, Up.N4.t1_ms()}
      +ek = Lv.tagged_live(st, S.Session.tag(s), es)
      +v : S.SVar = S.SVar{S.Session.up_seid(s), seq, S.Modifying{S.Guard{0}, Up.N4.modify(S.Session.up_seid(s), gnb_teid, gnb_addr, seq)}}
      Lv.leaf(st, S.Both{S.Revar{skey, v}, S.BumpSeq{1}}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], Lv.s_start(st, S.Session.tag(s), skey, ek, ekd), {==})), P.Bool.and_intro(Lv.revar_ok(st, v), True{}, kf, {==}), {==}, {==})

def Lw.set_up_phase(+st: S.State, +skey: U32, +s: S.Session, +transfer: B.Bytes(), +seq: U32, +p: S.SPhase, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.SPhase.knows(p, S.Session.known(s)), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}, +eki: {Lv.kept_if(st, skey, p) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.set_up_phase(st, skey, s, transfer, seq, p)) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{+guard, +pti}:
      +ekd = Lv.kept_at(st, skey, S.Setting{guard, pti}, eki, {==})
      Lw.modify(st, skey, s, pti, seq, Gsm.Gsm.tunnel_of(G.PDUSessionResourceSetupResponseTransfer.read(Ap.Cur{0n, Ap.unpack(transfer)})), es, kf, ekd)
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Deleting{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Lw.set_up(+st: S.State, +transfer: B.Bytes(), +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}, eg: Lv.Got(m, S.State.sessions(st))) -> {Lv.okf(st, Gsm.Gsm.set_up(st, transfer, seq, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.set_up_phase(st, skey, s, transfer, seq, S.Session.phase(s), Lv.owns(skey, s, S.State.sessions(st), em), Lv.knows(skey, s, S.State.sessions(st), em), Lv.kept_got(st, skey, s, eg))

def Lw.set_up_last(+st: S.State, +transfer: B.Bytes(), +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}, +again: Bool, eg: Lv.Got(m, S.State.sessions(st))) -> {Lv.okf(st, Gsm.Gsm.set_up_last(st, transfer, seq, m, again)) == True{} : Bool}:
  match again:
    case True{}:
      {==}
    case False{}:
      Lw.set_up(st, transfer, seq, m, em, eg)

def Lw.set_ups(+st: S.State, +key: U32, +items: G.PDUSessionResourceSetupListSURes(), +seq: U32) -> {Lv.okf(st, Gsm.Gsm.set_ups(st, key, items, seq)) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case G.PDUSessionResourceSetupItemSURes{+psi, +transfer, x} <> +more:
      +a = Gsm.Gsm.set_up_last(st, transfer, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), Gsm.Gsm.named(psi, more))
      +b = Gsm.Gsm.set_ups(st, key, more, U32.add(seq, 1))
      Lv.join(st, N.Out.also((S.BumpSeq{1}, []), []), N.Out.join(a, b), {==}, Lv.join(st, a, b, Lw.set_up_last(st, transfer, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), Lv.by_psi(key, psi, S.State.sessions(st)), Gsm.Gsm.named(psi, more), Lv.got_by_psi(key, psi, S.State.sessions(st))), Lw.set_ups(st, key, more, U32.add(seq, 1))))

def Lw.failed_phase(+st: S.State, +skey: U32, +s: S.Session, +seq: U32, +p: S.SPhase, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +eki: {Lv.kept_if(st, skey, p) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.failed_phase(st, skey, s, seq, p)) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{+guard, +pti}:
      +ekd = Lv.kept_at(st, skey, S.Setting{guard, pti}, eki, {==})
      Lw.abort(st, skey, s, pti, 26, seq, es, ekd)
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Deleting{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Lw.failed(+st: S.State, +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +em: {Lv.found(m, S.State.sessions(st)) == True{} : Bool}, eg: Lv.Got(m, S.State.sessions(st))) -> {Lv.okf(st, Gsm.Gsm.failed(st, seq, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Lw.failed_phase(st, skey, s, seq, S.Session.phase(s), Lv.owns(skey, s, S.State.sessions(st), em), Lv.kept_got(st, skey, s, eg))

def Lw.faileds(+st: S.State, +key: U32, +items: G.PDUSessionResourceFailedToSetupListSURes(), +seq: U32) -> {Lv.okf(st, Gsm.Gsm.faileds(st, key, items, seq)) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case G.PDUSessionResourceFailedToSetupItemSURes{+psi, transfer, x} <> +more:
      +a = Gsm.Gsm.failed(st, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)))
      +b = Gsm.Gsm.faileds(st, key, more, U32.add(seq, 1))
      Lv.join(st, (S.BumpSeq{1}, []), N.Out.join(a, b), {==}, Lv.join(st, a, b, Lw.failed(st, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), Lv.by_psi(key, psi, S.State.sessions(st)), Lv.got_by_psi(key, psi, S.State.sessions(st))), Lw.faileds(st, key, more, U32.add(seq, 1))))

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

# A phase not being deleted starts no deletion.
def Lv.arms_live(+k: U32, +p: S.SPhase, +acts: List<&2, N.Act>, +hp: {S.SPhase.live(p) == True{} : Bool}) -> {Lv.arms_p(k, p, acts) == True{} : Bool}:
  match p:
    case S.Deleting{guard, request}:
      Empty.absurd({Lv.arms_p(k, S.Deleting{guard, request}, acts) == True{} : Bool}, P.Refute.bool(hp))
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Lw.resend_if(+st: S.State, +skey: U32, +s: S.Session, +p: S.SPhase, +request: B.Bytes(), +fail: N.GOut(), +more: Bool, +hp: {S.SPhase.live(p) == True{} : Bool}, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}, +hv: {Lv.revar_ok(st, S.SVar{S.Session.up_seid(s), S.Session.seq(s), p}) == True{} : Bool}, +hf: {Lv.okf(st, fail) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.resend_if(skey, s, p, request, fail, more)) == True{} : Bool}:
  match more:
    case True{}:
      +ek = Lv.tagged_live(st, S.Session.tag(s), es)
      +x : N.Act = N.Pfcp{S.Session.tag(s), request}
      +y : N.Act = N.TimerStart{S.Session.tag(s), skey, Up.N4.t1_ms()}
      +v : S.SVar = S.SVar{S.Session.up_seid(s), S.Session.seq(s), p}
      Lv.leaf(st, S.Revar{skey, v}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], Lv.s_start(st, S.Session.tag(s), skey, ek, ekd), {==})), P.Bool.and_intro(Lv.arms(S.Revar{skey, v}, [x, y]), Lv.free(st, S.Revar{skey, v}), Lv.arms_live(skey, p, [x, y], hp), P.Bool.and_intro(Lv.spare(st, skey, v), Lv.revar_ok(st, v), P.Bool.or_r(S.SPhase.live(p), Lv.kept(st, skey), ekd), hv)), {==}, {==})
    case False{}:
      hf

def Lw.resend_w(+st: S.State, +skey: U32, +s: S.Session, +p: S.SPhase, +request: B.Bytes(), +fail: N.GOut(), +more: Bool, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +hv: {Lv.revar_ok(st, S.SVar{S.Session.up_seid(s), S.Session.seq(s), p}) == True{} : Bool}, +hf: {Lv.okw(st, fail) == True{} : Bool}) -> {Lv.okw(st, Gsm.Gsm.resend_if(skey, s, p, request, fail, more)) == True{} : Bool}:
  match more:
    case True{}:
      +ek = Lv.tagged_live(st, S.Session.tag(s), es)
      +x : N.Act = N.Pfcp{S.Session.tag(s), request}
      +y : N.Act = N.TimerStart{S.Session.tag(s), skey, Up.N4.t1_ms()}
      P.Bool.and_intro(Lv.actsw(st, [x, y]), Lv.revar_ok(st, S.SVar{S.Session.up_seid(s), S.Session.seq(s), p}), P.Bool.and_intro(Lv.actw(st, x), Lv.actsw(st, [y]), ek, P.Bool.and_intro(Lv.actw(st, y), True{}, ek, {==})), hv)
    case False{}:
      hf

# A guard that fires on a session it holds.
def Lw.gsm_expired(+st: S.State, +skey: U32, +s: S.Session, +p: S.SPhase, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.SPhase.knows(p, S.Session.known(s)), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}, +kb: {Bool.or(Gsm.Gsm.phase_bounded(p), Bool.not(Gsm.Gsm.bounded(S.State.sessions(st)))) == True{} : Bool}, +eki: {Lv.kept_if(st, skey, p) == True{} : Bool}, +ehd: {S.SPhase.live(p) == True{} : Bool}) -> {Lv.okf(st, Gsm.Gsm.expired(st, skey, s, p)) == True{} : Bool}:
  match p:
    case S.Creating{+guard, +pti, +accept, +request}:
      +ekd = Lv.kept_at(st, skey, S.Creating{guard, pti, accept, request}, eki, {==})
      Lw.resend_if(st, skey, s, S.Creating{S.Guard{U32.add(S.Guard.retries(guard), 1)}, pti, accept, request}, request, Gsm.Gsm.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st)), U32.is_lt(S.Guard.retries(guard), Up.N4.n1()), {==}, es, ekd, P.Bool.and_intro(Bool.or(Gsm.Gsm.accept_bounded(accept), Bool.not(Gsm.Gsm.bounded(S.State.sessions(st)))), Bool.or(Bool.not(S.Session.known(s)), Bool.not(S.Sessions.known(S.State.sessions(st)))), kb, kf), Lw.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st), es, ekd))
    case S.Setting{+guard, +pti}:
      +ekd = Lv.kept_at(st, skey, S.Setting{guard, pti}, eki, {==})
      Lw.drop(st, skey, s, S.State.pfcp_seq(st), es, ekd)
    case S.Modifying{+guard, +request}:
      +ekd = Lv.kept_at(st, skey, S.Modifying{guard, request}, eki, {==})
      Lw.resend_if(st, skey, s, S.Modifying{S.Guard{U32.add(S.Guard.retries(guard), 1)}, request}, request, Gsm.Gsm.drop(st, skey, s, S.State.pfcp_seq(st)), U32.is_lt(S.Guard.retries(guard), Up.N4.n1()), {==}, es, ekd, kf, Lw.drop(st, skey, s, S.State.pfcp_seq(st), es, ekd))
    case S.Repointing{+guard, +request}:
      +ekd = Lv.kept_at(st, skey, S.Repointing{guard, request}, eki, {==})
      Lw.resend_if(st, skey, s, S.Repointing{S.Guard{U32.add(S.Guard.retries(guard), 1)}, request}, request, Gsm.Gsm.repointed(st, skey, s, False{}), U32.is_lt(S.Guard.retries(guard), Up.N4.n1()), {==}, es, ekd, kf, Lw.repointed(st, skey, s, es, ekd))
    case S.Deleting{guard, request}:
      Empty.absurd({Lv.okf(st, Gsm.Gsm.expired(st, skey, s, S.Deleting{guard, request})) == True{} : Bool}, P.Refute.bool(ehd))
    case S.Active{}:
      {==}

# Timers
# ------

def Lw.asked(+st: S.State, +cfg: Maybe<&2, S.Cfg>) -> {Lv.okf(st, Up.N4.asked(st, cfg)) == True{} : Bool}:
  match cfg:
    case None{}:
      {==}
    case Some{c}:
      {==}

def Lw.n4_start(+st: S.State) -> {Lv.okf(st, Up.N4.start(st)) == True{} : Bool}:
  Lw.asked(st, S.State.config(st))

def Lw.gave_up(+st: S.State, +req: S.Req) -> {Lv.okf(st, Up.N4.gave_up(st, req)) == True{} : Bool}:
  match req:
    case S.Setup{}:
      {==}
    case S.Heartbeat{}:
      Lv.also(st, Up.N4.start(st), [N.Note{F.Warn{}, "PFCP: no Heartbeat Response; association with the UPF lost"}], Lw.n4_start(st), {==}, {==})

def Lw.again(+st: S.State, +req: S.Req, +request: B.Bytes(), +seq: U32, +resent: U32, +more: Bool) -> {Lv.okf(st, Up.N4.again(st, req, request, seq, resent, more)) == True{} : Bool}:
  match more:
    case True{}:
      {==}
    case False{}:
      Lw.gave_up(st, req)

def Lw.n4_expired(+st: S.State, +link: S.Link) -> {Lv.okf(st, Up.N4.expired(st, link)) == True{} : Bool}:
  match link:
    case S.Idle{}:
      {==}
    case S.Waiting{+req, +request, +seq, +resent}:
      Lw.again(st, req, request, seq, resent, U32.is_lt(resent, Up.N4.n1()))
    case S.Paused{}:
      Lw.n4_start(st)
    case S.Up{}:
      {==}

def Lw.node_timer(+st: S.State, +ok: Bool) -> {Lv.okf(st, K.Kernel.node_timer(st, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Lw.n4_expired(st, S.N4.link(S.State.n4(st)))
    case False{}:
      {==}

# NGAP
# ----

# Path Switch Request
# -------------------
# The context moves under its own key, guarded; its sessions are repointed
# or forgotten, every action built from the context's key.

def Lw.ps_session(+st: S.State, +skey: U32, +s: S.Session, +seq: U32, +t: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +kk: {Bool.or(S.Session.known(s), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Sw.Sw.session(skey, s, seq, t)) == True{} : Bool}:
  match t:
    case None{}:
      Lv.dels(st, [(skey, s)], seq, Lw.one(st, skey, s, es), Lv.one_kept(st, skey, s, ekd))
    case Some{(+teid, +addr)}:
      +request = Up.N4.modify(S.Session.up_seid(s), teid, addr, seq)
      +ek = Lv.tagged_live(st, S.Session.tag(s), es)
      +x : N.Act = N.Pfcp{S.Session.tag(s), request}
      +y : N.Act = N.TimerStart{S.Session.tag(s), skey, Up.N4.t1_ms()}
      Lv.leaf(st, S.Revar{skey, S.SVar{S.Session.up_seid(s), seq, S.Repointing{S.Guard{0}, request}}}, [x, y], Lv.cons(st, x, [y], ek, Lv.cons(st, y, [], Lv.s_start(st, S.Session.tag(s), skey, ek, ekd), {==})), kk, {==}, {==})

def Lw.ps_tun(+st: S.State, +skey: U32, +s: S.Session, +seq: U32, +p: S.SPhase, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +es: {Lv.tagged(S.Session.tag(s), S.State.sessions(st)) == True{} : Bool}, +kn: {Bool.or(S.SPhase.knows(p, S.Session.known(s)), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}, +ekd: {Lv.kept(st, skey) == True{} : Bool}) -> {Lv.okf(st, Sw.Sw.session(skey, s, seq, Sw.Sw.tunnel(p, m))) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      Lv.dels(st, [(skey, s)], seq, Lw.one(st, skey, s, es), Lv.one_kept(st, skey, s, ekd))
    case S.Setting{guard, pti}:
      Lv.dels(st, [(skey, s)], seq, Lw.one(st, skey, s, es), Lv.one_kept(st, skey, s, ekd))
    case S.Modifying{guard, request}:
      Lv.dels(st, [(skey, s)], seq, Lw.one(st, skey, s, es), Lv.one_kept(st, skey, s, ekd))
    case S.Repointing{guard, request}:
      Lv.dels(st, [(skey, s)], seq, Lw.one(st, skey, s, es), Lv.one_kept(st, skey, s, ekd))
    case S.Deleting{guard, request}:
      Lv.dels(st, [(skey, s)], seq, Lw.one(st, skey, s, es), Lv.one_kept(st, skey, s, ekd))
    case S.Active{}:
      Lw.ps_session(st, skey, s, seq, Sw.Sw.tunnel(S.Active{}, m), es, kn, ekd)

def Lw.ps_sessions(+st: S.State, +ts: List<&2, S.Tunnel>, +rows: Tb.Table(S.Session), +seq: U32, +e: {Lv.frows(rows, S.State.sessions(st)) == True{} : Bool}, +ed: {Lv.krows(rows, st) == True{} : Bool}) -> {Lv.okf(st, Sw.Sw.sessions(ts, rows, seq)) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+skey, +s) <> +more:
      +ss = S.State.sessions(st)
      +kn = Bool.or(S.SPhase.knows(S.Session.phase(s), S.Session.known(s)), Bool.not(S.Sessions.known(ss)))
      +hf = P.Bool.and_true_l(Lv.found(Some{(skey, s)}, ss), Lv.frows(more, ss), e)
      hm = P.Bool.and_true_r(Lv.found(Some{(skey, s)}, ss), Lv.frows(more, ss), e)
      es = P.Bool.and_true_l(Lv.tagged(S.Session.tag(s), ss), kn, hf)
      ek = P.Bool.and_true_r(Lv.tagged(S.Session.tag(s), ss), kn, hf)
      +o = Sw.Sw.session(skey, s, seq, Sw.Sw.tunnel_for(ts, s))
      Lv.join(st, N.Out.join((S.BumpSeq{1}, []), o), Sw.Sw.sessions(ts, more, U32.add(seq, 1)), Lv.join(st, (S.BumpSeq{1}, []), o, {==}, Lw.ps_tun(st, skey, s, seq, S.Session.phase(s), Sw.Sw.find(S.Session.psi(s), ts), es, ek, P.Bool.and_true_l(Lv.kept(st, skey), Lv.krows(more, st), ed))), Lw.ps_sessions(st, ts, more, U32.add(seq, 1), hm, P.Bool.and_true_r(Lv.kept(st, skey), Lv.krows(more, st), ed)))

def Lw.ps_go(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}, +rel: Maybe<&2, S.Side>, +ep: {S.Ue.phase(ue) == S.Registered{ctx, nh, rel} : S.Phase}) -> {Lv.okf(st, Ps.Ps.go(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, S.Sessions.of_ue(key, S.State.sessions(st)), True{})) == True{} : Bool}:
  +rows = S.Sessions.of_ue(key, S.State.sessions(st))
  +p : S.Phase = S.Switching{S.Guard{0}, ctx, S.Nh.next(nh), Sw.Sw.released(ts, rows)}
  +v = S.Ue.moved(ue, assoc, ran, stream, p)
  +a = Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st))
  +b : N.GOut() = (S.Put{key, v}, [])
  +ek = Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))
  hb = Lv.leaf(st, S.Put{key, v}, [], {==}, Lv.put_ok(st, key, v, p, Lv.p_moved(ue, assoc, ran, stream, p), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg)), {==}, {==}, P.Bool.or_l(Lv.chain(st, key, Some{S.Nh.next(nh)}), Lv.unpaired(st, key), Lv.chain_at(st, key, ue, S.Registered{ctx, nh, rel}, eg, ep, Some{S.Nh.next(nh)}, Lv.chains_next(nh))), Lv.home_moved(st, ue, assoc, ran, stream, p, ea)), {==}, Lv.paired_seed(st, key, ue, S.Registered{ctx, nh, rel}, eg, ep, {==}, S.Phase.nh(S.Ue.phase(v)), []))
  +tm : N.Act = N.TimerStart{Some{key}, key, Ps.Ps.guard_ms()}
  +note : N.Act = N.Note{F.Info{}, "NGAP: Path Switch Request; the UE moved, its PDU sessions being switched"}
  Lv.also(st, N.Out.join(a, b), [tm, note], Lv.join(st, a, b, Lw.ps_sessions(st, ts, rows, S.State.pfcp_seq(st), Lv.frows_sift(S.SOf{key}, S.State.sessions(st)), Lv.krows_of(st, key)), hb), Lv.cons(st, tm, [note], Lv.ue_start(st, key, Ps.Ps.guard_ms(), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))), {==}), {==})

def Lw.caps_same(+st: S.State, +ok: Bool) -> {Lv.acts(st, Ps.Ps.caps_same(ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Lw.caps_note(+st: S.State, +caps: G.UESecurityCapabilities, +m: Maybe<&2, N.Keyed()>) -> {Lv.acts(st, Ps.Ps.caps_note(caps, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+key, +ue)}:
      Lw.caps_same(st, B.bytes_eq(Ap.pack(G.UESecurityCapabilities.write(N.Ngap.ue_caps(N.Ue.caps(ue)), 0n, [])), Ap.pack(G.UESecurityCapabilities.write(caps, 0n, []))))

def Lv.same_stops(+tx: S.Tx, +ok: Bool) -> {Lv.stops(tx, Ps.Ps.caps_same(ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Lv.caps_stops(+tx: S.Tx, +caps: G.UESecurityCapabilities, +m: Maybe<&2, N.Keyed()>) -> {Lv.stops(tx, Ps.Ps.caps_note(caps, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+key, +ue)}:
      Lv.same_stops(tx, B.bytes_eq(Ap.pack(G.UESecurityCapabilities.write(N.Ngap.ue_caps(N.Ue.caps(ue)), 0n, [])), Ap.pack(G.UESecurityCapabilities.write(caps, 0n, []))))

def Lw.ps_of_view(+st: S.State, +assoc: U32, +stream: U32, +r: Result<&2, &2, B.Err, V.PathSwitchRequest.View>, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.okf(st, Ps.Ps.of_view(st, assoc, stream, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.PathSwitchRequest.View{+ran, +amf, uli, +caps, +items, failed, rrc}}:
      +ts = Sw.Sw.path_tunnels(items)
      +m = Ps.Ps.named(st, amf)
      +h = PW.Pw.claim(o => {Lv.okf(st, o) == True{} : Bool}, st, assoc, stream, amf, ran, items, ts, cause => {==}, +key => +ue => +ctx => +nh => sp => ek => eg => es => +rel => ep => Lw.ps_go(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, eg, ea, rel, ep))
      Lv.also(st, Ps.Ps.claim(st, assoc, stream, amf, ran, items, ts, m), Ps.Ps.caps_note(caps, m), h, Lw.caps_note(st, caps, m), Lv.caps_stops(N.Out.tx(Ps.Ps.claim(st, assoc, stream, amf, ran, items, ts, m)), caps, m))

# N2 handover
# -----------
# Every action is built from the context the message names, whose key a
# context holds; the context is rephased into a guarded phase, or moved
# under its own key by Handover Notify.

def Lw.ho_fail(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause, +ek: {Lv.held(st, key) == True{} : Bool}) -> {Lv.okf(st, Ho.Ho.fail(key, ue, cause)) == True{} : Bool}:
  +x = Ho.Ho.preparation_failure(key, ue, cause)
  +n : N.Act = N.Note{F.Warn{}, "NGAP: Handover Required refused"}
  Lv.leaf(st, S.Keep{}, [x, n], Lv.cons(st, x, [n], Lv.held_live(st, key, ek), {==}), {==}, {==}, {==})

# A pending handover's phase, written over the context it belongs to, names
# that context's owner as its source and another association as its target.
def Lw.ho_fits(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(S.Leg.target(leg), S.Ue.assoc(ue)) == False{} : Bool}) -> {Bool.and(True{}, S.Ue.fits(S.Handover{ctx, nh, S.Ue.assoc(ue), leg}, Tb.Table.get(S.Ue, key, S.State.ues(st)))) == True{} : Bool}:
  sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, S.State.ues(st)), Some{ue}, eg)
  %sg : {Bool.and(True{}, S.Ue.fits(S.Handover{ctx, nh, S.Ue.assoc(ue), leg}, _)) == True{} : Bool}
  er = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), S.Ue.assoc(ue)), True{}, P.U32.is_eq_refl(S.Ue.assoc(ue)))
  %er : {Bool.and(_, Bool.not(U32.is_eq(S.Leg.target(leg), S.Ue.assoc(ue)))) == True{} : Bool}
  sn = Equal.sym(Bool, U32.is_eq(S.Leg.target(leg), S.Ue.assoc(ue)), False{}, ne)
  %sn : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
  {==}

def Lw.ho_leafok(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +acts: List<&2, N.Act>, +ha: {Lv.acts(st, acts) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(S.Leg.target(leg), S.Ue.assoc(ue)) == False{} : Bool}, +hs: {Lv.stops(S.Rephase{key, S.Handover{ctx, nh, S.Ue.assoc(ue), leg}}, acts) == True{} : Bool}, +ec: {Lv.chain(st, key, Some{nh}) == True{} : Bool}) -> {Lv.ok(st, (S.Rephase{key, S.Handover{ctx, nh, S.Ue.assoc(ue), leg}}, acts)) == True{} : Bool}:
  +tx : S.Tx = S.Rephase{key, S.Handover{ctx, nh, S.Ue.assoc(ue), leg}}
  Lv.does_intro(st, tx, acts, Lv.homed(st, tx, S.State.ues(st)), hs, {==}, ha, {==}, P.Bool.and_intro(Lv.chain(st, key, Some{nh}), Bool.and(True{}, S.Ue.fits(S.Handover{ctx, nh, S.Ue.assoc(ue), leg}, Tb.Table.get(S.Ue, key, S.State.ues(st)))), ec, Lw.ho_fits(st, key, ue, ctx, nh, leg, eg, ne)))

# The target of a pending handover is not the context's owner.
def Lw.ho_aimed_ne(+ue: S.Ue, +assoc: U32, +e: {Ho.Ho.aimed(ue, assoc) == True{} : Bool}) -> {U32.is_eq(assoc, S.Ue.assoc(ue)) == False{} : Bool}:
  +rest = Bool.and(Tb.Table.present(B.Digits(), S.Ue.supi(ue)), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc)))
  n = P.Bool.and_true_r(Tb.Table.present(B.Digits(), S.Ue.supi(ue)), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc)), P.Bool.and_true_r(S.Maybe.same_u32(S.Phase.pending(S.Ue.phase(ue)), Some{assoc}), rest, e))
  Equal.trans(Bool, U32.is_eq(assoc, S.Ue.assoc(ue)), U32.is_eq(S.Ue.assoc(ue), assoc), False{}, P.U32.sym(assoc, S.Ue.assoc(ue)), P.Bool.not_true(U32.is_eq(S.Ue.assoc(ue), assoc), n))

# The context a message from its owner names holds its key.
def Lw.owned_held(+st: S.State, +assoc: U32, +ran: B.Bytes(), +key: U32, +ue: S.Ue, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.held(st, key) == True{} : Bool}:
  Lv.has_held(st, key, Lv.owned_has(st, assoc, key, ran, ue, eo))

def Lw.owned_live(+st: S.State, +assoc: U32, +ran: B.Bytes(), +key: U32, +ue: S.Ue, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.live(st, key) == True{} : Bool}:
  Lv.has_live(st, key, Lv.owned_has(st, assoc, key, ran, ue, eo))

# The context a target's answer is for holds its key, and is not the target's.
def Lw.target_get(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}) -> {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}:
  PW.Walk.first({Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, {Ho.Ho.aimed(ue, assoc) == True{} : Bool}, PW.Walk.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ue, ep))

def Lw.target_has(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}) -> {Tb.Table.has(S.Ue, key, S.State.ues(st)) == True{} : Bool}:
  Lv.get_has(S.State.ues(st), key, ue, Lw.target_get(st, assoc, key, ue, ep))

def Lw.target_held(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.held(st, key) == True{} : Bool}:
  Lv.has_held(st, key, Lw.target_has(st, assoc, key, ue, ep))

def Lw.target_live(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}) -> {Lv.live(st, key) == True{} : Bool}:
  Lv.has_live(st, key, Lw.target_has(st, assoc, key, ue, ep))

def Lw.target_ne(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}) -> {U32.is_eq(assoc, S.Ue.assoc(ue)) == False{} : Bool}:
  Lw.ho_aimed_ne(ue, assoc, PW.Walk.second({Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, {Ho.Ho.aimed(ue, assoc) == True{} : Bool}, PW.Walk.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ue, ep)))

def Lw.ho_prepare(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +t: U32, +cfg: S.Cfg, +cause: G.Cause, +container: B.Bytes(), +i: G.PDUSessionResourceSetupItemHOReq, +more: G.PDUSessionResourceSetupListHOReq(), +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(t, S.Ue.assoc(ue)) == False{} : Bool}, +rel: Maybe<&2, S.Side>, +eph: {S.Ue.phase(ue) == S.Registered{ctx, nh, rel} : S.Phase}) -> {Lv.ok(st, Ho.Ho.prepare(key, ue, ctx, nh, t, cfg, cause, container, i <> more)) == True{} : Bool}:
  +ek = Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))
  +next = S.Nh.next(nh)
  +x : N.Act = N.UeSend{t, Ho.Ho.stream(), key, Ho.Ho.request(key, cfg, cause, N.Ue.caps(ue), next, i <> more, container)}
  +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  +n : N.Act = N.Note{F.Info{}, "NGAP: Handover Required; Handover Request sent to the target"}
  Lw.ho_leafok(st, key, ue, ctx, next, S.Asked{t}, [x, y, n], Lv.cons(st, x, [y, n], ek, Lv.cons(st, y, [n], Lv.ue_start(st, key, N.Ue.guard_ms(), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))), {==})), eg, ne, {==}, Lv.chain_at(st, key, ue, S.Registered{ctx, nh, rel}, eg, eph, Some{next}, Lv.chains_next(nh)))

def Lw.ho_required(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverRequired.View>) -> {Lv.ok(st, Ho.Ho.required_of_view(st, assoc, r)) == True{} : Bool}:
  PW.Hw.required(o => {Lv.ok(st, o) == True{} : Bool}, st, assoc, r, {==}, {==}, amf => +ran => +key => +ue => +c => ek => +eo => Lv.ok_of(st, Ho.Ho.fail(key, ue, c), Lw.ho_fail(st, key, ue, c, Lw.owned_held(st, assoc, ran, key, ue, eo))), amf => +ran => +key => +ue => +ctx => +nh => +t => +cfg => +cause => +container => +i => +more => ek => +eo => +ne => +rel => eph => Lw.ho_prepare(st, key, ue, ctx, nh, t, cfg, cause, container, i, more, Lv.owned_get(st, assoc, key, ran, ue, eo), ne, rel, eph))

def Lw.ho_acked(+st: S.State, +assoc: U32, +stream: U32, +key: U32, +ue: S.Ue, +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes(), +ctx: Sec.Nas.Ctx, +nh: S.Nh, +source: U32, +t: U32, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == S.Handover{ctx, nh, source, S.Asked{t}} : S.Phase}) -> {Lv.ok(st, Ho.Ho.ack_phase(assoc, stream, key, ue, ran, admitted, container, S.Handover{ctx, nh, source, S.Asked{t}})) == True{} : Bool}:
  +ek = Lw.target_live(st, assoc, key, ue, ep)
  +ts = Sw.Sw.admitted(admitted)
  +x : N.Act = N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.command(key, S.Ue.ran_id(ue), ts, container)}
  +y : N.Act = N.TimerStart{Some{key}, key, N.Ue.guard_ms()}
  +n : N.Act = N.Note{F.Info{}, "NGAP: Handover Request Acknowledge; Handover Command sent to the source"}
  Lw.ho_leafok(st, key, ue, ctx, nh, S.Acked{assoc, ran, stream, ts}, [x, y, n], Lv.cons(st, x, [y, n], ek, Lv.cons(st, y, [n], Lv.ue_start(st, key, N.Ue.guard_ms(), Lw.target_held(st, assoc, key, ue, ep)), {==})), Lw.target_get(st, assoc, key, ue, ep), Lw.target_ne(st, assoc, key, ue, ep), {==}, Lv.chain_at(st, key, ue, S.Handover{ctx, nh, source, S.Asked{t}}, Lw.target_get(st, assoc, key, ue, ep), eph, Some{nh}, Lv.chains_same(nh)))

def Lw.ho_ack(+st: S.State, +assoc: U32, +stream: U32, +r: Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View>) -> {Lv.ok(st, Ho.Ho.ack_of_view(st, assoc, stream, r)) == True{} : Bool}:
  PW.Hw.ack(o => {Lv.ok(st, o) == True{} : Bool}, st, assoc, stream, r, {==}, {==}, amf => +ran => +admitted => +container => +key => +ue => +ctx => +nh => +source => +t => ek => +ep => eph => Lw.ho_acked(st, assoc, stream, key, ue, ran, admitted, container, ctx, nh, source, t, ep, eph))

def Lw.ho_failed(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +cause: G.Cause, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +source: U32, +t: U32, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == S.Handover{ctx, nh, source, S.Asked{t}} : S.Phase}) -> {Lv.okf(st, Ho.Ho.failure_phase(assoc, key, ue, cause, S.Handover{ctx, nh, source, S.Asked{t}})) == True{} : Bool}:
  +x = Ho.Ho.preparation_failure(key, ue, cause)
  +n : N.Act = N.Note{F.Warn{}, "NGAP: Handover Failure; Handover Preparation Failure sent to the source"}
  Lv.leaf(st, S.Rephase{key, S.Registered{ctx, nh, None{}}}, [x, N.TimerCancel{key}, n], Lv.cons(st, x, [N.TimerCancel{key}, n], Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg)), Lv.cons(st, N.TimerCancel{key}, [n], Lv.get_has(S.State.ues(st), key, ue, eg), {==})), P.Bool.and_intro(Lv.chain(st, key, Some{nh}), True{}, Lv.chain_at(st, key, ue, S.Handover{ctx, nh, source, S.Asked{t}}, eg, eph, Some{nh}, Lv.chains_same(nh)), {==}), Lv.stops_cons(S.Rephase{key, S.Registered{ctx, nh, None{}}}, x, [N.TimerCancel{key}, n], {==}, Lv.stops_cons(S.Rephase{key, S.Registered{ctx, nh, None{}}}, N.TimerCancel{key}, [n], Lv.idles_rephase(key, S.Registered{ctx, nh, None{}}, {==}), {==})), {==})

def Lw.ho_failure(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverFailure.View>) -> {Lv.okf(st, Ho.Ho.failure_of_view(st, assoc, r)) == True{} : Bool}:
  PW.Hw.failure(o => {Lv.okf(st, o) == True{} : Bool}, st, assoc, r, {==}, {==}, amf => +cause => +key => +ue => +ctx => +nh => +source => +t => ek => +ep => eph => Lw.ho_failed(st, assoc, key, ue, cause, ctx, nh, source, t, Lw.target_get(st, assoc, key, ue, ep), eph))

def Lw.ho_complete(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +source: U32, +t: U32, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == S.Handover{ctx, nh, source, S.Acked{t, r, s, ts}} : S.Phase}, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.okf(st, Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, True{})) == True{} : Bool}:
  +ek = Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))
  +rows = S.Sessions.of_ue(key, S.State.sessions(st))
  +v = S.Ue.moved(ue, assoc, r, s, S.Registered{ctx, nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}})
  +a = Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st))
  +b : N.GOut() = (S.Put{key, v}, [])
  hb = Lv.leaf(st, S.Put{key, v}, [], {==}, Lv.put_ok(st, key, v, S.Registered{ctx, nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}}, Lv.p_moved(ue, assoc, r, s, S.Registered{ctx, nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}}), Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg)), {==}, {==}, P.Bool.or_l(Lv.chain(st, key, Some{nh}), Lv.unpaired(st, key), Lv.chain_at(st, key, ue, S.Handover{ctx, nh, source, S.Acked{t, r, s, ts}}, eg, eph, Some{nh}, Lv.chains_same(nh))), Lv.home_moved(st, ue, assoc, r, s, S.Registered{ctx, nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}}, ea)), {==}, Lv.paired_seed(st, key, ue, S.Handover{ctx, nh, source, S.Acked{t, r, s, ts}}, eg, eph, {==}, S.Phase.nh(S.Ue.phase(v)), []))
  +x : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), Ho.Ho.radio(G.CauseRadioNetwork.successful_handover())}
  +n : N.Act = N.Note{F.Info{}, "NGAP: Handover Notify; the UE moved to the target"}
  Lv.also(st, N.Out.join(a, b), [x, N.TimerCancel{key}, n], Lv.join(st, a, b, Lw.ps_sessions(st, ts, rows, S.State.pfcp_seq(st), Lv.frows_sift(S.SOf{key}, S.State.sessions(st)), Lv.krows_of(st, key)), hb), Lv.cons(st, x, [N.TimerCancel{key}, n], ek, Lv.cons(st, N.TimerCancel{key}, [n], Lv.get_has(S.State.ues(st), key, ue, eg), {==})), Lv.stops_cons(N.Out.tx(N.Out.join(a, b)), x, [N.TimerCancel{key}, n], {==}, Lv.stops_cons(N.Out.tx(N.Out.join(a, b)), N.TimerCancel{key}, [n], Lv.idles_join_put(a, key, v, S.Registered{ctx, nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}}, Lv.p_moved(ue, assoc, r, s, S.Registered{ctx, nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}}), {==}), {==})))

def Lw.ho_notify(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverNotify.View>, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.okf(st, Ho.Ho.notify_of_view(st, assoc, r)) == True{} : Bool}:
  PW.Hw.notify(o => {Lv.okf(st, o) == True{} : Bool}, st, assoc, r, {==}, {==}, amf => ran => +key => +ue => +ctx => +nh => +source => +t => +r2 => +s => +ts => sp => ek => +ep => eph => es => Lw.ho_complete(st, assoc, key, ue, ctx, nh, source, t, r2, s, ts, Lw.target_get(st, assoc, key, ue, ep), eph, ea))

def Lw.ho_cancel_none(+st: S.State, +key: U32, +ue: S.Ue, +ek: {Lv.held(st, key) == True{} : Bool}) -> {Lv.okf(st, (S.Keep{}, [N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.cancel_ack(key, S.Ue.ran_id(ue))}, N.Note{F.Warn{}, "NGAP: Handover Cancel with no handover pending"}])) == True{} : Bool}:
  +x : N.Act = N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.cancel_ack(key, S.Ue.ran_id(ue))}
  +n : N.Act = N.Note{F.Warn{}, "NGAP: Handover Cancel with no handover pending"}
  Lv.leaf(st, S.Keep{}, [x, n], Lv.cons(st, x, [n], Lv.held_live(st, key, ek), {==}), {==}, {==}, {==})

def Lw.ho_cancelled(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +source: U32, +leg: S.Leg, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == S.Handover{ctx, nh, source, leg} : S.Phase}) -> {Lv.okf(st, Ho.Ho.cancel_phase(key, ue, S.Handover{ctx, nh, source, leg})) == True{} : Bool}:
  +ek = Lv.has_live(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))
  +x : N.Act = N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), key, Ho.Ho.cancel_ack(key, S.Ue.ran_id(ue))}
  +c = Ho.Ho.radio(G.CauseRadioNetwork.handover_cancelled())
  +n : N.Act = N.Note{F.Info{}, "NGAP: Handover Cancel; the target released"}
  +more : List<&2, N.Act> = [N.TimerCancel{key}, n]
  Lv.leaf(st, S.Rephase{key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}}, x <> List.append(&2, N.Act, Ho.Ho.drop(key, leg, c), more), Lv.cons(st, x, List.append(&2, N.Act, Ho.Ho.drop(key, leg, c), more), ek, Lv.append(st, Ho.Ho.drop(key, leg, c), more, Lw.ho_drop(st, key, leg, c, Lv.has_held(st, key, Lv.get_has(S.State.ues(st), key, ue, eg))), Lv.cons(st, N.TimerCancel{key}, [n], Lv.get_has(S.State.ues(st), key, ue, eg), {==}))), P.Bool.and_intro(Lv.chain(st, key, Some{nh}), True{}, Lv.chain_at(st, key, ue, S.Handover{ctx, nh, source, leg}, eg, eph, Some{nh}, Lv.chains_same(nh)), {==}), Lv.stops_cons(S.Rephase{key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}}, x, List.append(&2, N.Act, Ho.Ho.drop(key, leg, c), more), {==}, Lv.stops_app(S.Rephase{key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}}, Ho.Ho.drop(key, leg, c), more, Lv.drop_stops(S.Rephase{key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}}, key, leg, c), Lv.stops_cons(S.Rephase{key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}}, N.TimerCancel{key}, [n], Lv.idles_rephase(key, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}, {==}), {==}))), {==})

def Lw.ho_cancel(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverCancel.View>) -> {Lv.okf(st, Ho.Ho.cancel_of_view(st, assoc, r)) == True{} : Bool}:
  PW.Hw.cancel(o => {Lv.okf(st, o) == True{} : Bool}, st, assoc, r, {==}, {==}, amf => +ran => +key => +ue => ek => +eo => en => Lw.ho_cancel_none(st, key, ue, Lw.owned_held(st, assoc, ran, key, ue, eo)), amf => +ran => +key => +ue => +ctx => +nh => +source => +leg => ek => +eo => eph => Lw.ho_cancelled(st, key, ue, ctx, nh, source, leg, Lv.owned_get(st, assoc, key, ran, ue, eo), eph))

def Lw.ho_status(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View>) -> {Lv.okf(st, Ho.Ho.status_of_view(st, assoc, r)) == True{} : Bool}:
  PW.Hw.status(o => {Lv.okf(st, o) == True{} : Bool}, st, assoc, r, {==}, {==}, {==}, amf => +ran => +container => +key => +ue => +t => +r2 => +s => ek => +eo => Lv.leaf(st, S.Keep{}, [N.UeSend{t, s, key, Ho.Ho.dl_status(key, r2, container)}], Lv.cons(st, N.UeSend{t, s, key, Ho.Ho.dl_status(key, r2, container)}, [], Lw.owned_live(st, assoc, ran, key, ue, eo), {==}), {==}, {==}, {==}))

# An association reset (going down, or its NG Setup)
# ---------------------------------------------------
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
      Lv.cons(st, Ho.Ho.preparation_failure(k, u, Ho.Ho.radio(G.CauseRadioNetwork.ho_failure_in_target_5GC_ngran_node_or_target_system())), [], ek, {==})
    case S.Acked{t, r, s, ts}:
      {==}

def Lw.dq(+st: S.State, +o: N.GOut(), +h: {Lv.okf(st, o) == True{} : Bool}, +hq: {Lv.quiet(N.Out.tx(o)) == True{} : Bool}) -> {Bool.and(Lv.okf(st, o), Lv.quiet(N.Out.tx(o))) == True{} : Bool}:
  P.Bool.and_intro(Lv.okf(st, o), Lv.quiet(N.Out.tx(o)), h, hq)

# Where no two contexts share a key, the row of the table under a key is the
# context the key names, so a phase rewritten from it keeps its pair.
def Lv.paired(+st: S.State, rows: Tb.Table(S.Ue)) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case (+k, +u) <> more:
      Bool.and(Lv.chain(st, k, S.Phase.nh(S.Ue.phase(u))), Lv.paired(st, more))

def Lv.paired_in(+t: Tb.Table(S.Ue), rows: Tb.Table(S.Ue)) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case (+k, +u) <> more:
      +m = Tb.Table.get(S.Ue, k, t)
      Bool.and(Lv.chains(S.Phase.nh(S.Ue.phase(u)), S.Ue.nh(m)), Lv.paired_in(t, more))

def Lv.chains_self(+n: Maybe<&2, S.Nh>) -> {Lv.chains(n, n) == True{} : Bool}:
  match n:
    case None{}:
      {==}
    case Some{+x}:
      Lv.chains_same(x)

def Lv.paired_row(+k0: U32, +u0: S.Ue, +more: Tb.Table(S.Ue), +k: U32, +u: S.Ue, +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +ne: {b == False{} : Bool}, +h: {Lv.chains(S.Phase.nh(S.Ue.phase(u)), S.Ue.nh(Tb.Table.get(S.Ue, k, more))) == True{} : Bool}) -> {Lv.chains(S.Phase.nh(S.Ue.phase(u)), S.Ue.nh(Tb.Table.hit(S.Ue, u0, Tb.Table.get(S.Ue, k, more), b))) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Lv.chains(S.Phase.nh(S.Ue.phase(u)), S.Ue.nh(Some{u0})) == True{} : Bool}, P.Refute.true_false(ne))
    case False{}:
      h

# Rows clear of a row under k0 are found past it.
def Lv.paired_cons(+k0: U32, +u0: S.Ue, +more: Tb.Table(S.Ue), +rows: Tb.Table(S.Ue), +hc: {S.Ues.clear(k0, u0, rows) == True{} : Bool}, +h: {Lv.paired_in(more, rows) == True{} : Bool}) -> {Lv.paired_in((k0, u0) <> more, rows) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k, +u) <> +rest:
      +m = Tb.Table.get(S.Ue, k, more)
      +x = Lv.chains(S.Phase.nh(S.Ue.phase(u)), S.Ue.nh(m))
      +nc = Bool.not(S.Row.conflicts(k0, u0, k, u))
      +nr = P.Bool.or_false_l(U32.is_eq(k, k0), S.Ue.conflicts(u0, u), P.Bool.not_true(S.Row.conflicts(k0, u0, k, u), P.Bool.and_true_l(nc, S.Ues.clear(k0, u0, rest), hc)))
      +ne = Equal.trans(Bool, U32.is_eq(k0, k), U32.is_eq(k, k0), False{}, P.U32.sym(k0, k), nr)
      P.Bool.and_intro(Lv.chains(S.Phase.nh(S.Ue.phase(u)), S.Ue.nh(Tb.Table.hit(S.Ue, u0, m, U32.is_eq(k0, k)))), Lv.paired_in((k0, u0) <> more, rest), Lv.paired_row(k0, u0, more, k, u, U32.is_eq(k0, k), {==}, ne, P.Bool.and_true_l(x, Lv.paired_in(more, rest), h)), Lv.paired_cons(k0, u0, more, rest, P.Bool.and_true_r(nc, S.Ues.clear(k0, u0, rest), hc), P.Bool.and_true_r(x, Lv.paired_in(more, rest), h)))

def Lv.paired_self(+t: Tb.Table(S.Ue), +eu: {S.Ues.unique(t) == True{} : Bool}) -> {Lv.paired_in(t, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case (+k0, +u0) <> +more:
      +hc = P.Bool.and_true_l(S.Ues.clear(k0, u0, more), S.Ues.unique(more), eu)
      +n = S.Phase.nh(S.Ue.phase(u0))
      e = Equal.sym(Bool, U32.is_eq(k0, k0), True{}, P.U32.is_eq_refl(k0))
      hd : {Lv.chains(n, S.Ue.nh(Tb.Table.hit(S.Ue, u0, Tb.Table.get(S.Ue, k0, more), U32.is_eq(k0, k0)))) == True{} : Bool} = (%e : {Lv.chains(n, S.Ue.nh(Tb.Table.hit(S.Ue, u0, Tb.Table.get(S.Ue, k0, more), _))) == True{} : Bool}; Lv.chains_self(n))
      P.Bool.and_intro(Lv.chains(n, S.Ue.nh(Tb.Table.hit(S.Ue, u0, Tb.Table.get(S.Ue, k0, more), U32.is_eq(k0, k0)))), Lv.paired_in((k0, u0) <> more, more), hd, Lv.paired_cons(k0, u0, more, more, hc, Lv.paired_self(more, P.Bool.and_true_r(S.Ues.clear(k0, u0, more), S.Ues.unique(more), eu))))

def Lv.paired_from(+st: S.State, +rows: Tb.Table(S.Ue), +h: {Lv.paired_in(S.State.ues(st), rows) == True{} : Bool}) -> {Lv.paired(st, rows) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      +m = Tb.Table.get(S.Ue, k, S.State.ues(st))
      +x = Lv.chains(S.Phase.nh(S.Ue.phase(u)), S.Ue.nh(m))
      P.Bool.and_intro(Lv.chain(st, k, S.Phase.nh(S.Ue.phase(u))), Lv.paired(st, more), P.Bool.or_l(x, Bool.not(S.Ues.unique(S.State.ues(st))), P.Bool.and_true_l(x, Lv.paired_in(S.State.ues(st), more), h)), Lv.paired_from(st, more, P.Bool.and_true_r(x, Lv.paired_in(S.State.ues(st), more), h)))

def Lv.paired_none(+st: S.State, +rows: Tb.Table(S.Ue), +en: {Bool.not(S.Ues.unique(S.State.ues(st))) == True{} : Bool}) -> {Lv.paired(st, rows) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      +m = Tb.Table.get(S.Ue, k, S.State.ues(st))
      P.Bool.and_intro(Lv.chain(st, k, S.Phase.nh(S.Ue.phase(u))), Lv.paired(st, more), P.Bool.or_r(Lv.chains(S.Phase.nh(S.Ue.phase(u)), S.Ue.nh(m)), Bool.not(S.Ues.unique(S.State.ues(st))), en), Lv.paired_none(st, more, en))

def Lv.paired_if(+st: S.State, +b: Bool, +eb: {S.Ues.unique(S.State.ues(st)) == b : Bool}) -> {Lv.paired(st, S.State.ues(st)) == True{} : Bool}:
  match b:
    case True{}:
      Lv.paired_from(st, S.State.ues(st), Lv.paired_self(S.State.ues(st), eb))
    case False{}:
      seb = Equal.sym(Bool, S.Ues.unique(S.State.ues(st)), False{}, eb)
      Lv.paired_none(st, S.State.ues(st), (%seb : {Bool.not(_) == True{} : Bool}; {==}))

def Lv.paired_all(+st: S.State) -> {Lv.paired(st, S.State.ues(st)) == True{} : Bool}:
  Lv.paired_if(st, S.Ues.unique(S.State.ues(st)), {==})

def Lw.ho_down_leg(+st: S.State, +k: U32, +u: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +target: Bool, +source: Bool, +eh: {Tb.Table.has(S.Ue, k, S.State.ues(st)) == True{} : Bool}, +ec: {Lv.chain(st, k, Some{nh}) == True{} : Bool}) -> {Bool.and(Lv.okf(st, Ho.Ho.down_leg(k, u, ctx, nh, leg, target, source)), Lv.quiet(N.Out.tx(Ho.Ho.down_leg(k, u, ctx, nh, leg, target, source)))) == True{} : Bool}:
  match target source:
    case True{} _:
      Lw.dq(st, (S.Rephase{k, S.Registered{ctx, nh, None{}}}, List.append(&2, N.Act, Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's UE contexts were re-initialised; N2 handover ended"}])), Lv.leaf(st, S.Rephase{k, S.Registered{ctx, nh, None{}}}, List.append(&2, N.Act, Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's UE contexts were re-initialised; N2 handover ended"}]), Lv.append(st, Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's UE contexts were re-initialised; N2 handover ended"}], Lw.ho_lost(st, k, u, leg, Lv.has_live(st, k, eh)), Lv.cons(st, N.TimerCancel{k}, [N.Note{F.Warn{}, "NGAP: the target's UE contexts were re-initialised; N2 handover ended"}], eh, {==})), P.Bool.and_intro(Lv.chain(st, k, Some{nh}), True{}, ec, {==}), Lv.stops_app(S.Rephase{k, S.Registered{ctx, nh, None{}}}, Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's UE contexts were re-initialised; N2 handover ended"}], Lv.lost_stops(S.Rephase{k, S.Registered{ctx, nh, None{}}}, k, u, leg), Lv.stops_cons(S.Rephase{k, S.Registered{ctx, nh, None{}}}, N.TimerCancel{k}, [N.Note{F.Warn{}, "NGAP: the target's UE contexts were re-initialised; N2 handover ended"}], Lv.idles_rephase(k, S.Registered{ctx, nh, None{}}, {==}), {==})), {==}), {==})
    case False{} True{}:
      Lw.dq(st, (S.Keep{}, Ho.Ho.drop(k, leg, Ho.Ho.radio(G.CauseRadioNetwork.unspecified()))), Lv.leaf(st, S.Keep{}, Ho.Ho.drop(k, leg, Ho.Ho.radio(G.CauseRadioNetwork.unspecified())), Lw.ho_drop(st, k, leg, Ho.Ho.radio(G.CauseRadioNetwork.unspecified()), Lv.has_held(st, k, eh)), {==}, Lv.drop_stops(S.Keep{}, k, leg, Ho.Ho.radio(G.CauseRadioNetwork.unspecified())), {==}), {==})
    case False{} False{}:
      {==}

def Lw.ho_down_row(+st: S.State, +assoc: U32, +k: U32, +u: S.Ue, +p: S.Phase, +eh: {Tb.Table.has(S.Ue, k, S.State.ues(st)) == True{} : Bool}, +ec: {Lv.chain(st, k, S.Phase.nh(p)) == True{} : Bool}) -> {Bool.and(Lv.okf(st, Ho.Ho.down_row(assoc, k, u, p)), Lv.quiet(N.Out.tx(Ho.Ho.down_row(assoc, k, u, p)))) == True{} : Bool}:
  match p:
    case S.Handover{+ctx, +nh, source, +leg}:
      Lw.ho_down_leg(st, k, u, ctx, nh, leg, Ho.Ho.aimed(u, assoc), U32.is_eq(S.Ue.assoc(u), assoc), eh, ec)
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
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Lw.ho_down_join(+st: S.State, +a: N.GOut(), +b: N.GOut(), +ha: {Bool.and(Lv.okf(st, a), Lv.quiet(N.Out.tx(a))) == True{} : Bool}, +hb: {Bool.and(Lv.okf(st, b), Lv.quiet(N.Out.tx(b))) == True{} : Bool}) -> {Bool.and(Lv.okf(st, N.Out.join(a, b)), Lv.quiet(N.Out.tx(N.Out.join(a, b)))) == True{} : Bool}:
  sj = Equal.sym(S.Tx, N.Out.tx(N.Out.join(a, b)), S.Both{N.Out.tx(a), N.Out.tx(b)}, PW.Out.tx_join(a, b))
  hq : {Lv.quiet(N.Out.tx(N.Out.join(a, b))) == True{} : Bool} = (%sj : {Lv.quiet(_) == True{} : Bool}; P.Bool.and_intro(Lv.quiet(N.Out.tx(a)), Lv.quiet(N.Out.tx(b)), P.Bool.and_true_r(Lv.okf(st, a), Lv.quiet(N.Out.tx(a)), ha), P.Bool.and_true_r(Lv.okf(st, b), Lv.quiet(N.Out.tx(b)), hb)))
  P.Bool.and_intro(Lv.okf(st, N.Out.join(a, b)), Lv.quiet(N.Out.tx(N.Out.join(a, b))), Lv.join(st, a, b, P.Bool.and_true_l(Lv.okf(st, a), Lv.quiet(N.Out.tx(a)), ha), P.Bool.and_true_l(Lv.okf(st, b), Lv.quiet(N.Out.tx(b)), hb)), hq)

def Lw.ho_downs(+st: S.State, +assoc: U32, +rows: Tb.Table(S.Ue), +e: {Lv.keys_in(rows, S.State.ues(st)) == True{} : Bool}, +ep: {Lv.paired(st, rows) == True{} : Bool}) -> {Bool.and(Lv.okf(st, Ho.Ho.downs(assoc, rows)), Lv.quiet(N.Out.tx(Ho.Ho.downs(assoc, rows)))) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      +eh = P.Bool.and_true_l(Tb.Table.has(S.Ue, k, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e)
      +c = Lv.chain(st, k, S.Phase.nh(S.Ue.phase(u)))
      Lw.ho_down_join(st, Ho.Ho.down_row(assoc, k, u, S.Ue.phase(u)), Ho.Ho.downs(assoc, more), Lw.ho_down_row(st, assoc, k, u, S.Ue.phase(u), eh, P.Bool.and_true_l(c, Lv.paired(st, more), ep)), Lw.ho_downs(st, assoc, more, P.Bool.and_true_r(Tb.Table.has(S.Ue, k, S.State.ues(st)), Lv.keys_in(more, S.State.ues(st)), e), P.Bool.and_true_r(c, Lv.paired(st, more), ep)))

def Lw.ho_down_q(+st: S.State, +assoc: U32) -> {Bool.and(Lv.okf(st, Ho.Ho.down(st, assoc)), Lv.quiet(N.Out.tx(Ho.Ho.down(st, assoc)))) == True{} : Bool}:
  Lw.ho_downs(st, assoc, S.State.ues(st), Pv.refl(S.State.ues(st)), Lv.paired_all(st))

def Lw.ho_down(+st: S.State, +assoc: U32) -> {Lv.ok(st, Ho.Ho.down(st, assoc)) == True{} : Bool}:
  Lv.ok_of(st, Ho.Ho.down(st, assoc), P.Bool.and_true_l(Lv.okf(st, Ho.Ho.down(st, assoc)), Lv.quiet(N.Out.tx(Ho.Ho.down(st, assoc))), Lw.ho_down_q(st, assoc)))

def Lw.step_sessions(+st: S.State, +o: N.GOut(), +e: {Lv.quiet(N.Out.tx(o)) == True{} : Bool}) -> {S.State.sessions(K.Kernel.state(N.Step.of(st, o))) == S.State.sessions(st) : Tb.Table(S.Session)}:
  match o:
    case (+tx, acts):
      Lv.quiet_sessions(tx, st, e)

# The first part of an association's reset (Ho.Ho.down) leaves the sessions.
def Lw.down_sessions(+st: S.State, +assoc: U32) -> {S.State.sessions(K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, assoc)))) == S.State.sessions(st) : Tb.Table(S.Session)}:
  Lw.step_sessions(st, Ho.Ho.down(st, assoc), P.Bool.and_true_r(Lv.okf(st, Ho.Ho.down(st, assoc)), Lv.quiet(N.Out.tx(Ho.Ho.down(st, assoc))), Lw.ho_down_q(st, assoc)))

def Lw.ho_route(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.ok(st, Ho.Ho.route(st, assoc, stream, kind, code, ies)) == True{} : Bool}:
  PW.Walk.ho(o => {Lv.ok(st, o) == True{} : Bool}, st, assoc, stream, kind, code, ies, {==}, +r => Lw.ho_required(st, assoc, r), +r => Lw.ho_ack(st, assoc, stream, r), +r => Lv.ok_of(st, Ho.Ho.failure_of_view(st, assoc, r), Lw.ho_failure(st, assoc, r)), +r => Lv.ok_of(st, Ho.Ho.notify_of_view(st, assoc, r), Lw.ho_notify(st, assoc, r, ea)), +r => Lv.ok_of(st, Ho.Ho.cancel_of_view(st, assoc, r), Lw.ho_cancel(st, assoc, r)), +r => Lv.ok_of(st, Ho.Ho.status_of_view(st, assoc, r), Lw.ho_status(st, assoc, r)))

def Lw.d2(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, +ea: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Lv.ok(st, R.Route.d2(st, assoc, stream, kind, code, ies, entropy, b)) == True{} : Bool}:
  PW.Walk.d2(o => {Lv.ok(st, o) == True{} : Bool}, st, assoc, stream, kind, code, ies, entropy, b, Lw.ho_route(st, assoc, stream, kind, code, ies, ea), +r => Lv.ok_of(st, Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, r), Lw.initial_of_view(st, assoc, stream, entropy, r, ea)), +r => Lw.uplink_of_view(st, assoc, stream, entropy, r), +r => Lv.ok_of(st, Gmm.Gmm.ics_response_of_view(st, assoc, r), Lw.ics_response_of_view(st, assoc, r)), +r => Lv.ok_of(st, Gmm.Gmm.release_request_of_view(st, assoc, r), Lw.release_request_of_view(st, assoc, r)), +r => Lv.ok_of(st, Gmm.Gmm.release_complete_of_view(st, assoc, r), Lw.release_complete_of_view(st, assoc, r)), +r => Lv.ok_of(st, Gsm.Gsm.setup_response_of_view(st, assoc, r), Lw.setup_response_of_view(st, assoc, r)), +r => Lv.ok_of(st, Ps.Ps.of_view(st, assoc, stream, r), Lw.ps_of_view(st, assoc, stream, r, ea)))

# The step, around sessions being deleted
# ---------------------------------------
# Every step ends as Walk.step says; of the procedures' outcomes, three may
# change a session being deleted or stop a session's guard: a session's guard
# firing while it is being deleted (resend), a Session Deletion Response
# (answered), and a Session Modification Response that settles a session
# (settled, Lv.fine). Every other outcome is ok (lift).

def Dw.Resend(-ok: N.GOut() -> Type, +st: S.State, -ev: F.Evt) -> Type:
  @k:U32 -> @t:S.Session -> @g:S.Guard -> @r:B.Bytes() -> {ev == F.TimerFired{k} : F.Evt} -> {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>} -> {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>} -> {S.Session.phase(t) == S.Deleting{g, r} : S.SPhase} -> ok(Gsm.Gsm.expired(st, k, t, S.Deleting{g, r}))

def Dw.Answered(-ok: N.GOut() -> Type, +st: S.State, -ev: F.Evt) -> Type:
  @len:U32 -> @bytes:B.Bytes() -> @msg:Pf.Msg -> @rest:B.Bytes() -> {ev == F.PfcpData{len, bytes} : F.Evt} -> {Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)} -> {Pf.Msg.kind(msg) == 55 : U32} -> ok(Gsm.Gsm.deleted(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st))))

def Dw.Settled(-ok: N.GOut() -> Type, +st: S.State) -> Type:
  @k:U32 -> @tx:S.Tx -> @more:List<&2, N.Act> -> {Lv.kept(st, k) == True{} : Bool} -> {Tb.Table.has(S.Session, k, S.State.sessions(st)) == True{} : Bool} -> {Lv.ok(st, (tx, more)) == True{} : Bool} -> ok((tx, N.TimerCancel{k} <> more))

def Dw.Lift(-ok: N.GOut() -> Type, +st: S.State) -> Type:
  @o:N.GOut() -> {Lv.ok(st, o) == True{} : Bool} -> ok(o)

def Dw.lead(-ok: N.GOut() -> Type, +st: S.State, +tx: S.Tx, +a: N.Act, +more: List<&2, N.Act>, +h: {Lv.lead(st, tx, a, more) == True{} : Bool}, settled: Dw.Settled(ok, st)) -> ok((tx, a <> more)):
  match a:
    case N.TimerCancel{+k}:
      +hr = P.Bool.and_true_r(Lv.kept(st, k), Bool.and(Tb.Table.has(S.Session, k, S.State.sessions(st)), Lv.ok(st, (tx, more))), h)
      settled(k, tx, more, P.Bool.and_true_l(Lv.kept(st, k), Bool.and(Tb.Table.has(S.Session, k, S.State.sessions(st)), Lv.ok(st, (tx, more))), h), P.Bool.and_true_l(Tb.Table.has(S.Session, k, S.State.sessions(st)), Lv.ok(st, (tx, more)), hr), P.Bool.and_true_r(Tb.Table.has(S.Session, k, S.State.sessions(st)), Lv.ok(st, (tx, more)), hr))
    case N.DlNas{assoc, stream, key, ran_id, nas}:
      Empty.absurd(ok((tx, N.DlNas{assoc, stream, key, ran_id, nas} <> more)), P.Refute.bool(h))
    case N.Ics{assoc, stream, key, ran_id, cfg, caps, k_gnb, nas}:
      Empty.absurd(ok((tx, N.Ics{assoc, stream, key, ran_id, cfg, caps, k_gnb, nas} <> more)), P.Refute.bool(h))
    case N.PduSetup{assoc, stream, key, ran_id, psi, sst, nas, transfer}:
      Empty.absurd(ok((tx, N.PduSetup{assoc, stream, key, ran_id, psi, sst, nas, transfer} <> more)), P.Refute.bool(h))
    case N.Release{assoc, stream, key, ran_id, cause}:
      Empty.absurd(ok((tx, N.Release{assoc, stream, key, ran_id, cause} <> more)), P.Refute.bool(h))
    case N.SwitchAck{assoc, stream, key, ran_id, caps, nh, switched, released, sst}:
      Empty.absurd(ok((tx, N.SwitchAck{assoc, stream, key, ran_id, caps, nh, switched, released, sst} <> more)), P.Refute.bool(h))
    case N.SwitchFail{assoc, stream, ue, amf, ran_id, psis, cause}:
      Empty.absurd(ok((tx, N.SwitchFail{assoc, stream, ue, amf, ran_id, psis, cause} <> more)), P.Refute.bool(h))
    case N.UeSend{assoc, stream, key, bytes}:
      Empty.absurd(ok((tx, N.UeSend{assoc, stream, key, bytes} <> more)), P.Refute.bool(h))
    case N.ErrInd{assoc, cause}:
      Empty.absurd(ok((tx, N.ErrInd{assoc, cause} <> more)), P.Refute.bool(h))
    case N.Setup{assoc, answer}:
      Empty.absurd(ok((tx, N.Setup{assoc, answer} <> more)), P.Refute.bool(h))
    case N.Pfcp{ue, bytes}:
      Empty.absurd(ok((tx, N.Pfcp{ue, bytes} <> more)), P.Refute.bool(h))
    case N.Note{level, text}:
      Empty.absurd(ok((tx, N.Note{level, text} <> more)), P.Refute.bool(h))
    case N.TimerStart{ue, timer, ms}:
      Empty.absurd(ok((tx, N.TimerStart{ue, timer, ms} <> more)), P.Refute.bool(h))

def Dw.settles(-ok: N.GOut() -> Type, +st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +h: {Lv.settles(st, tx, acts) == True{} : Bool}, settled: Dw.Settled(ok, st)) -> ok((tx, acts)):
  match acts:
    case Nil{}:
      Empty.absurd(ok((tx, [])), P.Refute.bool(h))
    case +a <> +more:
      Dw.lead(ok, st, tx, a, more, h, settled)

def Dw.fine_if(-ok: N.GOut() -> Type, +st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +b: Bool, +eb: {Lv.ok(st, (tx, acts)) == b : Bool}, +h: {Bool.or(b, Lv.settles(st, tx, acts)) == True{} : Bool}, lift: Dw.Lift(ok, st), settled: Dw.Settled(ok, st)) -> ok((tx, acts)):
  match b:
    case True{}:
      lift((tx, acts), eb)
    case False{}:
      Dw.settles(ok, st, tx, acts, h, settled)

def Dw.fine(-ok: N.GOut() -> Type, +st: S.State, +o: N.GOut(), +h: {Lv.fine(st, o) == True{} : Bool}, lift: Dw.Lift(ok, st), settled: Dw.Settled(ok, st)) -> ok(o):
  match o:
    case (+tx, +acts):
      Dw.fine_if(ok, st, tx, acts, Lv.ok(st, (tx, acts)), {==}, h, lift, settled)

def Dw.expired(-ok: N.GOut() -> Type, +st: S.State, +k: U32, +t: S.Session, +p: S.SPhase, +ep: {S.Session.phase(t) == p : S.SPhase}, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +em: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>}, +es: {Lv.tagged(S.Session.tag(t), S.State.sessions(st)) == True{} : Bool}, +kf: {Bool.or(S.SPhase.knows(p, S.Session.known(t)), Bool.not(S.Sessions.known(S.State.sessions(st)))) == True{} : Bool}, +kb: {Bool.or(Gsm.Gsm.phase_bounded(p), Bool.not(Gsm.Gsm.bounded(S.State.sessions(st)))) == True{} : Bool}, +eki: {Lv.kept_if(st, k, p) == True{} : Bool}, lift: Dw.Lift(ok, st), resend: @t:S.Session -> @g:S.Guard -> @r:B.Bytes() -> {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>} -> {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>} -> {S.Session.phase(t) == S.Deleting{g, r} : S.SPhase} -> ok(Gsm.Gsm.expired(st, k, t, S.Deleting{g, r}))) -> ok(Gsm.Gsm.expired(st, k, t, p)):
  match p:
    case S.Creating{+guard, +pti, +accept, +request}:
      +o = Gsm.Gsm.expired(st, k, t, S.Creating{guard, pti, accept, request})
      lift(o, Lv.ok_of(st, o, Lw.gsm_expired(st, k, t, S.Creating{guard, pti, accept, request}, es, kf, kb, eki, {==})))
    case S.Setting{+guard, +pti}:
      +o = Gsm.Gsm.expired(st, k, t, S.Setting{guard, pti})
      lift(o, Lv.ok_of(st, o, Lw.gsm_expired(st, k, t, S.Setting{guard, pti}, es, kf, kb, eki, {==})))
    case S.Modifying{+guard, +request}:
      +o = Gsm.Gsm.expired(st, k, t, S.Modifying{guard, request})
      lift(o, Lv.ok_of(st, o, Lw.gsm_expired(st, k, t, S.Modifying{guard, request}, es, kf, kb, eki, {==})))
    case S.Repointing{+guard, +request}:
      +o = Gsm.Gsm.expired(st, k, t, S.Repointing{guard, request})
      lift(o, Lv.ok_of(st, o, Lw.gsm_expired(st, k, t, S.Repointing{guard, request}, es, kf, kb, eki, {==})))
    case S.Deleting{+guard, +request}:
      resend(t, guard, request, eu, em, ep)
    case S.Active{}:
      lift(Gsm.Gsm.expired(st, k, t, S.Active{}), {==})

def Dw.fired_session(-ok: N.GOut() -> Type, +st: S.State, +timer: U32, +m: Maybe<&2, S.Session>, +em: {Tb.Table.get(S.Session, timer, S.State.sessions(st)) == m : Maybe<&2, S.Session>}, +eu: {Tb.Table.get(S.Ue, timer, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, lift: Dw.Lift(ok, st), resend: @t:S.Session -> @g:S.Guard -> @r:B.Bytes() -> {Tb.Table.get(S.Ue, timer, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>} -> {Tb.Table.get(S.Session, timer, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>} -> {S.Session.phase(t) == S.Deleting{g, r} : S.SPhase} -> ok(Gsm.Gsm.expired(st, timer, t, S.Deleting{g, r}))) -> ok(K.Kernel.fired_session(st, timer, m)):
  match m:
    case None{}:
      lift(K.Kernel.node_timer(st, U32.is_eq(timer, S.N4.timer())), Lv.ok_of(st, K.Kernel.node_timer(st, U32.is_eq(timer, S.N4.timer())), Lw.node_timer(st, U32.is_eq(timer, S.N4.timer()))))
    case Some{+t}:
      +ss = S.State.sessions(st)
      Dw.expired(ok, st, timer, t, S.Session.phase(t), {==}, eu, em, Lv.owns(timer, t, ss, Lv.sget(ss, timer, t, em)), Lv.knows(timer, t, ss, Lv.sget(ss, timer, t, em)), Lv.sbound(ss, timer, t, em), Lv.kept_get(st, timer, t, em), lift, resend)

def Dw.fired_ue(-ok: N.GOut() -> Type, +st: S.State, +timer: U32, +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, timer, S.State.ues(st)) == m : Maybe<&2, S.Ue>}, lift: Dw.Lift(ok, st), resend: @t:S.Session -> @g:S.Guard -> @r:B.Bytes() -> {Tb.Table.get(S.Ue, timer, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>} -> {Tb.Table.get(S.Session, timer, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>} -> {S.Session.phase(t) == S.Deleting{g, r} : S.SPhase} -> ok(Gsm.Gsm.expired(st, timer, t, S.Deleting{g, r}))) -> ok(K.Kernel.fired_ue(st, timer, m)):
  match m:
    case None{}:
      Dw.fired_session(ok, st, timer, Tb.Table.get(S.Session, timer, S.State.sessions(st)), {==}, em, lift, resend)
    case Some{+ue}:
      +o = Gmm.Gmm.expired(st, timer, ue, S.Ue.phase(ue))
      lift(o, Lv.ok_of(st, o, Lw.expired(st, timer, ue, S.Ue.phase(ue), Lv.has_held(st, timer, Lv.get_has(S.State.ues(st), timer, ue, em)), Lv.home_get(st, timer, ue, em), em, {==})))

def Dw.k4(-ok: N.GOut() -> Type, +st: S.State, +msg: Pf.Msg, +b: Bool, +eo: {U32.is_eq(Pf.Msg.kind(msg), Pf.Type.session_deletion_response()) == b : Bool}, lift: Dw.Lift(ok, st), answered: {Pf.Msg.kind(msg) == 55 : U32} -> ok(Gsm.Gsm.deleted(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))), settled: Dw.Settled(ok, st)) -> ok(Gsm.Gsm.pfcp_k4(st, msg, Pf.Msg.kind(msg), b)):
  match b:
    case True{}:
      answered(P.U32.eq_of_is_eq(Pf.Msg.kind(msg), Pf.Type.session_deletion_response(), eo))
    case False{}:
      +kind = Pf.Msg.kind(msg)
      Dw.fine(ok, st, Gsm.Gsm.pfcp_k5(st, msg, kind, U32.is_eq(kind, Pf.Type.session_establishment_response())), Lw.pfcp_k5(st, msg, kind, U32.is_eq(kind, Pf.Type.session_establishment_response())), lift, settled)

def Dw.k3(-ok: N.GOut() -> Type, +st: S.State, +msg: Pf.Msg, +b: Bool, lift: Dw.Lift(ok, st), answered: {Pf.Msg.kind(msg) == 55 : U32} -> ok(Gsm.Gsm.deleted(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))), settled: Dw.Settled(ok, st)) -> ok(Gsm.Gsm.pfcp_k3(st, msg, Pf.Msg.kind(msg), b)):
  match b:
    case True{}:
      +link = S.N4.link(S.State.n4(st))
      lift(Up.N4.assoc_for(link, msg), Lv.ok_of(st, Up.N4.assoc_for(link, msg), Lw.assoc_for(st, link, msg)))
    case False{}:
      Dw.k4(ok, st, msg, U32.is_eq(Pf.Msg.kind(msg), Pf.Type.session_deletion_response()), {==}, lift, answered, settled)

def Dw.k2(-ok: N.GOut() -> Type, +st: S.State, +msg: Pf.Msg, +b: Bool, lift: Dw.Lift(ok, st), answered: {Pf.Msg.kind(msg) == 55 : U32} -> ok(Gsm.Gsm.deleted(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))), settled: Dw.Settled(ok, st)) -> ok(Gsm.Gsm.pfcp_k2(st, msg, Pf.Msg.kind(msg), b)):
  match b:
    case True{}:
      +link = S.N4.link(S.State.n4(st))
      lift(Up.N4.alive_for(link, Pf.Msg.seq(msg)), Lv.ok_of(st, Up.N4.alive_for(link, Pf.Msg.seq(msg)), Lw.alive_for(st, link, Pf.Msg.seq(msg))))
    case False{}:
      Dw.k3(ok, st, msg, U32.is_eq(Pf.Msg.kind(msg), Pf.Type.association_setup_response()), lift, answered, settled)

def Dw.k1(-ok: N.GOut() -> Type, +st: S.State, +msg: Pf.Msg, +b: Bool, lift: Dw.Lift(ok, st), answered: {Pf.Msg.kind(msg) == 55 : U32} -> ok(Gsm.Gsm.deleted(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))), settled: Dw.Settled(ok, st)) -> ok(Gsm.Gsm.pfcp_k1(st, msg, Pf.Msg.kind(msg), b)):
  match b:
    case True{}:
      lift(Gsm.Gsm.pfcp_k1(st, msg, Pf.Msg.kind(msg), True{}), {==})
    case False{}:
      Dw.k2(ok, st, msg, U32.is_eq(Pf.Msg.kind(msg), Pf.Type.heartbeat_response()), lift, answered, settled)

def Dw.pfcp_msg(-ok: N.GOut() -> Type, +st: S.State, +bytes: B.Bytes(), +r: B.Read(Pf.Msg), +er: {Pf.Msg.read(bytes) == r : B.Read(Pf.Msg)}, lift: Dw.Lift(ok, st), answered: @msg:Pf.Msg -> @rest:B.Bytes() -> {Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)} -> {Pf.Msg.kind(msg) == 55 : U32} -> ok(Gsm.Gsm.deleted(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))), settled: Dw.Settled(ok, st)) -> ok(Gsm.Gsm.pfcp_msg(st, r)):
  match r:
    case Fail{e}:
      lift(Gsm.Gsm.pfcp_msg(st, Fail{e}), {==})
    case Done{(+msg, +rest)}:
      Dw.k1(ok, st, msg, U32.is_eq(Pf.Msg.kind(msg), 1), lift, ek => answered(msg, rest, er, ek), settled)

def Dw.walk(-Q: N.Step() -> Type, -ok: N.GOut() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: PW.Walk.Keep(Q, st), ready: @assoc:U32 -> @s:Bool -> PW.Walk.Ready(Q, st, assoc, s), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), down: @assoc:U32 -> Q(R.Route.down(st, assoc)), out: PW.Walk.Out(Q, ok, st), lift: Dw.Lift(ok, st), resend: Dw.Resend(ok, st, ev), answered: Dw.Answered(ok, st, ev), settled: Dw.Settled(ok, st)) -> Q(K.Kernel.step(st, ev, entropy)):
  match ev:
    case F.Config{len, +tlvs}:
      config(tlvs)
    case F.NgapAssocUp{assoc}:
      keep([], k => {==}, k => {==}, {==})
    case F.NgapAssocDown{+assoc}:
      down(assoc)
    case F.NgapData{+assoc, +stream, len, +bytes}:
      PW.Walk.pdu(Q, ok, st, assoc, stream, entropy, Fr.Pdu.read(bytes), keep, ready(assoc, N.NgSetup.supported_request(S.State.config(st), bytes)), out, +kind => +code => +ies => +ea => lift(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code)), Lw.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code), ea)))
    case F.PfcpData{+len, +bytes}:
      out(Gsm.Gsm.pfcp_data(st, bytes), Dw.pfcp_msg(ok, st, bytes, Pf.Msg.read(bytes), {==}, lift, +msg => +rest => er => ek => answered(len, bytes, msg, rest, {==}, er, ek), settled))
    case F.TimerFired{+timer}:
      out(K.Kernel.fired(st, timer), Dw.fired_ue(ok, st, timer, Tb.Table.get(S.Ue, timer, S.State.ues(st)), {==}, lift, +t => +g => +r => eu => em => ep => resend(timer, t, g, r, {==}, eu, em, ep)))

# The guard of a session being deleted fires: its request goes again, or the
# deletion is given up.
def Lv.resent_w(+st: S.State, +k: U32, +t: S.Session, +g: S.Guard, +r: B.Bytes(), +em: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>}, +ep: {S.Session.phase(t) == S.Deleting{g, r} : S.SPhase}) -> {Lv.okw(st, Gsm.Gsm.expired(st, k, t, S.Deleting{g, r})) == True{} : Bool}:
  +ss = S.State.sessions(st)
  +kf = Lv.knows(k, t, ss, Lv.sget(ss, k, t, em))
  Lw.resend_w(st, k, t, S.Deleting{S.Guard{U32.add(S.Guard.retries(g), 1)}, r}, r, (S.DelSession{k}, [N.Note{F.Warn{}, "PFCP: no Session Deletion Response; deletion given up"}]), U32.is_lt(S.Guard.retries(g), Up.N4.n1()), Lv.owns(k, t, ss, Lv.sget(ss, k, t, em)), (%ep : {Bool.or(S.SPhase.knows(_, S.Session.known(t)), Bool.not(S.Sessions.known(ss))) == True{} : Bool}; kf), {==})

def Lv.settled_w(+st: S.State, +k: U32, +tx: S.Tx, +more: List<&2, N.Act>, +h: {Lv.ok(st, (tx, more)) == True{} : Bool}) -> {Lv.okw(st, (tx, N.TimerCancel{k} <> more)) == True{} : Bool}:
  P.Bool.and_intro(Lv.actsw(st, more), Lv.homedw(st, tx, S.State.ues(st)), Lv.acts_w(st, more, Lv.ok_acts(st, (tx, more), h)), Lv.weak(st, tx, S.State.ues(st), Lv.ok_homed(st, (tx, more), h)))

# Every procedure's outcome is ok (Lw), or one of the three Dw tells apart.
def Lv.walk(-Q: N.Step() -> Type, +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), keep: PW.Walk.Keep(Q, st), ready: @assoc:U32 -> @s:Bool -> PW.Walk.Ready(Q, st, assoc, s), config: @tlvs:List<&2, T.Tlv> -> Q(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy)), down: @assoc:U32 -> Q(R.Route.down(st, assoc)), out: PW.Walk.Out(Q, o => {Lv.okw(st, o) == True{} : Bool}, st)) -> Q(K.Kernel.step(st, ev, entropy)):
  Dw.walk(Q, o => {Lv.okw(st, o) == True{} : Bool}, st, ev, entropy, keep, ready, config, down, out, +o => +h => Lv.ok_w(st, o, h), +k => +t => +g => +r => ek => eu => em => ep => Lv.resent_w(st, k, t, g, r, em, ep), +len => +bytes => +msg => +rest => ev2 => er => ek => Lw.deleted(st, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st))), +k => +tx => +more => ek => eh => h => Lv.settled_w(st, k, tx, more, h))


# Steps
# -----

def Lv.cancelw(+st: S.State, +key: U32, +g: Maybe<&2, S.Guard>) -> {Lv.actsw(st, N.Guard.cancel(key, g)) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{guard}:
      {==}

# The guards a step stops name no UE.
def Lv.gone_row(+st: S.State, +k: U32, +t: S.Session, +kept: Bool) -> {Lv.actsw(st, N.Gone.row(k, t, kept)) == True{} : Bool}:
  match kept:
    case True{}:
      {==}
    case False{}:
      Lv.cancelw(st, k, S.SPhase.guard(S.Session.phase(t)))

def Lv.gone(+st: S.State, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> {Lv.actsw(st, N.Gone.cancels(before, after)) == True{} : Bool}:
  match before:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      Lv.appendw(st, N.Gone.row(k, t, Tb.Table.has(S.Session, k, after)), N.Gone.cancels(more, after), Lv.gone_row(st, k, t, Tb.Table.has(S.Session, k, after)), Lv.gone(st, more, after))

def Lv.gone_when(+st: S.State, +keeps: Bool, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> {Lv.actsw(st, N.Gone.when(keeps, before, after)) == True{} : Bool}:
  match keeps:
    case True{}:
      {==}
    case False{}:
      Lv.gone(st, before, after)

def Lv.step_acts(+st: S.State, +o: N.GOut(), +h: {Lv.okw(st, o) == True{} : Bool}) -> {Lv.actsw(st, K.Kernel.actions(N.Step.of(st, o))) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      Lv.appendw(st, acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))), P.Bool.and_true_l(Lv.actsw(st, acts), Lv.homedw(st, tx, S.State.ues(st)), h), Lv.gone_when(st, S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))))

def Lv.no_response(+st: S.State, +as: List<&2, N.Act>, +h: {Lv.actsw(st, as) == True{} : Bool}) -> {N.Ngap.any_ng_setup_response(as) == False{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case +a <> +more:
      +hn = P.Bool.not_true(N.Ngap.is_ng_setup_response(a), P.Bool.and_true_l(Bool.not(N.Ngap.is_ng_setup_response(a)), Lv.tag(st, N.Act.ue(a)), P.Bool.and_true_l(Lv.actw(st, a), Lv.actsw(st, more), h)))
      sn = Equal.sym(Bool, N.Ngap.is_ng_setup_response(a), False{}, hn)
      %sn : {Bool.or(_, N.Ngap.any_ng_setup_response(more)) == False{} : Bool}
      Lv.no_response(st, more, P.Bool.and_true_r(Lv.actw(st, a), Lv.actsw(st, more), h))

# Sessions stay owned
# -------------------


# The deletions dropping an association's contexts sends are a transaction a
# UE procedure may run.
def Lv.drop_homed(+st: S.State, +assoc: U32) -> {Lv.homedw(st, N.Out.tx(Up.N4.deletions(S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, S.State.ues(st))}, S.State.sessions(st)), S.State.pfcp_seq(st))), S.State.ues(st)) == True{} : Bool}:
  +gone = S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, S.State.ues(st))}, S.State.sessions(st))
  +d = Up.N4.deletions(gone, S.State.pfcp_seq(st))
  Lv.weak(st, N.Out.tx(d), S.State.ues(st), Lv.free_homed(st, N.Out.tx(d), S.State.ues(st), Lv.okf_free(st, d, Lv.dels(st, gone, S.State.pfcp_seq(st), Lv.srows_sift(S.SOrphan{S.Ues.drop_assoc(assoc, S.State.ues(st))}, S.State.sessions(st)), Lv.krows_orphan(st, S.Ues.drop_assoc(assoc, S.State.ues(st)))))))

# What an association's contexts going leaves behind names live keys only.
def Lv.drop_acts(+st: S.State, +assoc: U32) -> {Lv.actsw(st, K.Kernel.actions(R.Route.drop(st, assoc))) == True{} : Bool}:
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s0 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      +gone = S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions)
      +d = Up.N4.deletions(gone, pfcp_seq)
      +kept = S.Sessions.sift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, S.State.sessions(S.Tx.apply(N.Out.tx(d), s0)))
      Lv.appendw(s0, N.Out.acts(d), N.Gone.cancels(sessions, kept), Lv.acts_w(s0, N.Out.acts(d), Lv.okf_acts(s0, d, Lv.dels(s0, gone, pfcp_seq, Lv.srows_sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions), Lv.krows_orphan(s0, S.Ues.drop_assoc(assoc, ues))))), Lv.gone(s0, sessions, kept))

def Lv.owned_sift(+s: S.SSieve, +ss: Tb.Table(S.Session), +ues: Tb.Table(S.Ue), +e: {S.Sessions.owned(ss, ues) == True{} : Bool}) -> {S.Sessions.owned(S.Sessions.sift(s, ss), ues) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {S.Sessions.owned(tb, ues) == True{} : Bool}, k, t, S.Sessions.sift(s, more), S.SSieve.keeps(s, k, t), e1 => h => P.Bool.and_intro(S.Session.owned(t, ues), S.Sessions.owned(S.Sessions.sift(s, more), ues), P.Bool.and_true_l(S.Session.owned(t, ues), S.Sessions.owned(more, ues), e), h), Lv.owned_sift(s, more, ues, P.Bool.and_true_r(S.Session.owned(t, ues), S.Sessions.owned(more, ues), e)))

# The sessions a put keeps are those owned by the contexts left.
def Lv.owned_owned(+ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> {S.Sessions.owned(S.Sessions.sift(S.SOwned{ues}, ss), ues) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {S.Sessions.owned(tb, ues) == True{} : Bool}, k, t, S.Sessions.sift(S.SOwned{ues}, more), S.Session.owned(t, ues), e => h => P.Bool.and_intro(S.Session.owned(t, ues), S.Sessions.owned(S.Sessions.sift(S.SOwned{ues}, more), ues), e, h), Lv.owned_owned(ues, more))

def Lv.owned_rephase(+ss: Tb.Table(S.Session), +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +e: {S.Sessions.owned(ss, ues) == True{} : Bool}) -> {S.Sessions.owned(ss, S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (k, +t) <> +more:
      +x = S.Session.ue(t)
      +nt = Bool.not(Tb.Table.present(U32, S.Session.tag(t)))
      eh = Equal.sym(Bool, Tb.Table.has(S.Ue, x, S.Ues.rephase(key, p, ues)), Tb.Table.has(S.Ue, x, ues), Lv.has_rephase(x, key, p, ues))
      P.Bool.and_intro(S.Session.owned(t, S.Ues.rephase(key, p, ues)), S.Sessions.owned(more, S.Ues.rephase(key, p, ues)), (%eh : {Bool.or(nt, _) == True{} : Bool}; P.Bool.and_true_l(S.Session.owned(t, ues), S.Sessions.owned(more, ues), e)), Lv.owned_rephase(more, key, p, ues, P.Bool.and_true_r(S.Session.owned(t, ues), S.Sessions.owned(more, ues), e)))

def Lv.has_except(+x: U32, +key: U32, +ues: Tb.Table(S.Ue), +ne: {Bool.not(U32.is_eq(x, key)) == True{} : Bool}, +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, x, ues) == m : Maybe<&2, S.Ue>}, +eh: {Tb.Table.present(S.Ue, m) == True{} : Bool}) -> {Tb.Table.has(S.Ue, x, S.Ues.sift(S.Except{key}, ues)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Tb.Table.has(S.Ue, x, S.Ues.sift(S.Except{key}, ues)) == True{} : Bool}, P.Refute.bool(eh))
    case Some{+w}:
      Lv.get_has(S.Ues.sift(S.Except{key}, ues), x, w, PT.Sift.get(S.Except{key}, x, w, ues, em, ne))

def Lv.owned_ex_go(+u: U32, +key: U32, +ues: Tb.Table(S.Ue), +h: Bool, +ne: {Bool.not(S.Maybe.same_u32(Tb.Table.hit(U32, u, None{}, h), Some{key})) == True{} : Bool}, +ht: {Bool.or(Bool.not(Tb.Table.present(U32, Tb.Table.hit(U32, u, None{}, h))), Tb.Table.has(S.Ue, u, ues)) == True{} : Bool}) -> {Bool.or(Bool.not(Tb.Table.present(U32, Tb.Table.hit(U32, u, None{}, h))), Tb.Table.has(S.Ue, u, S.Ues.sift(S.Except{key}, ues))) == True{} : Bool}:
  match h:
    case True{}:
      Lv.has_except(u, key, ues, ne, Tb.Table.get(S.Ue, u, ues), {==}, ht)
    case False{}:
      {==}

# A session of another UE, or of none, stays owned when a context is forgotten.
def Lv.owned_except(+t: S.Session, +key: U32, +ues: Tb.Table(S.Ue), +ne: {Bool.not(S.Maybe.same_u32(S.Session.tag(t), Some{key})) == True{} : Bool}, +ht: {S.Session.owned(t, ues) == True{} : Bool}) -> {S.Session.owned(t, S.Ues.sift(S.Except{key}, ues)) == True{} : Bool}:
  Lv.owned_ex_go(S.Session.ue(t), key, ues, S.SPhase.live(S.Session.phase(t)), ne, ht)

# Forgetting a context forgets its sessions, so the others keep theirs.
def Lv.owned_del(+ss: Tb.Table(S.Session), +key: U32, +ues: Tb.Table(S.Ue), +e: {S.Sessions.owned(ss, ues) == True{} : Bool}) -> {S.Sessions.owned(S.Sessions.sift(S.SOthers{key}, ss), S.Ues.sift(S.Except{key}, ues)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {S.Sessions.owned(tb, S.Ues.sift(S.Except{key}, ues)) == True{} : Bool}, k, t, S.Sessions.sift(S.SOthers{key}, more), Bool.not(S.Maybe.same_u32(S.Session.tag(t), Some{key})), e1 => h => P.Bool.and_intro(S.Session.owned(t, S.Ues.sift(S.Except{key}, ues)), S.Sessions.owned(S.Sessions.sift(S.SOthers{key}, more), S.Ues.sift(S.Except{key}, ues)), Lv.owned_except(t, key, ues, e1, P.Bool.and_true_l(S.Session.owned(t, ues), S.Sessions.owned(more, ues), e)), h), Lv.owned_del(more, key, ues, P.Bool.and_true_r(S.Session.owned(t, ues), S.Sessions.owned(more, ues), e)))

# A session changed in place stays owned: it keeps its UE, and keeps its tag or drops it.
def Lv.owned_moved(+t: S.Session, +t2: S.Session, +ues: Tb.Table(S.Ue), h: PW.Tg.Moved(t, t2), +ei: {S.Session.id(t2) == S.Session.id(t) : S.SId}, +e: {S.Session.owned(t, ues) == True{} : Bool}) -> {S.Session.owned(t2, ues) == True{} : Bool}:
  match h:
    case Inl{ee}:
      se = Equal.sym(Maybe<&2, U32>, S.Session.tag(t2), S.Session.tag(t), ee)
      sei = Equal.sym(S.SId, S.Session.id(t2), S.Session.id(t), ei)
      (%se : {Bool.or(Bool.not(Tb.Table.present(U32, _)), Tb.Table.has(S.Ue, S.SId.ue(S.Session.id(t2)), ues)) == True{} : Bool}; (%sei : {Bool.or(Bool.not(Tb.Table.present(U32, S.Session.tag(t))), Tb.Table.has(S.Ue, S.SId.ue(_), ues)) == True{} : Bool}; e))
    case Inr{en}:
      se = Equal.sym(Maybe<&2, U32>, S.Session.tag(t2), None{}, en)
      (%se : {Bool.or(Bool.not(Tb.Table.present(U32, _)), Tb.Table.has(S.Ue, S.Session.ue(t2), ues)) == True{} : Bool}; {==})

def Lv.owned_revar(+ss: Tb.Table(S.Session), +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +e: {S.Sessions.owned(ss, ues) == True{} : Bool}) -> {S.Sessions.owned(S.Sessions.revar(key, v, ss), ues) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +hit = Bool.and(U32.is_eq(k, key), S.SVar.follows(v, t))
      +t2 = S.Session.revar_if(t, v, hit)
      P.Bool.and_intro(S.Session.owned(t2, ues), S.Sessions.owned(S.Sessions.revar(key, v, more), ues), Lv.owned_moved(t, t2, ues, PW.Tg.revar(t, v, U32.is_eq(k, key)), PW.Tg.id(t, v, hit), P.Bool.and_true_l(S.Session.owned(t, ues), S.Sessions.owned(more, ues), e)), Lv.owned_revar(more, key, v, ues, P.Bool.and_true_r(S.Session.owned(t, ues), S.Sessions.owned(more, ues), e)))

# A gone UE is not live
# ---------------------

def Inv.none(+st0: S.State) -> Bool:
  True{}

def Inv.owned(+st0: S.State) -> Bool:
  S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0))

def Ow.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  S.Sessions.owned(ss, ues)

def Ow.tx_put(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Ow.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Ow.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  Lv.owned_owned(S.Ues.put(key, ue, ues), ss)

def Ow.tx_rephase(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Ow.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Ow.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  Lv.owned_rephase(ss, key, p, ues, e)

def Ow.tx_del(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Ow.inv(st0, ues, ss) == True{} : Bool}) -> {Ow.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Lv.owned_del(ss, key, ues, e)

def Ow.tx_put_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Ow.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Ow.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  +hs = P.Bool.and_true_r(S.Ids.seid(key), Bool.and(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s)))), h)
  P.Bool.and_intro(S.Session.owned(s, ues), S.Sessions.owned(S.Sessions.sift(S.SClear{key, s}, ss), ues), P.Bool.or_r(Bool.not(Tb.Table.present(U32, S.Session.tag(s))), Tb.Table.has(S.Ue, S.Session.ue(s), ues), P.Bool.and_true_l(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s))), hs)), Lv.owned_sift(S.SClear{key, s}, ss, ues, e))

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
      P.Bool.contra({Bool.not(True{}) == True{} : Bool}, Lv.live(st, k), hk, Lv.dead(st, k, eo, eg, en))

def Lv.tag_spare(+st: S.State, +m: Maybe<&2, U32>, +k: U32, +ht: {Lv.tag(st, m) == True{} : Bool}, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}) -> {Bool.not(S.Maybe.same_u32(m, Some{k})) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      Lv.not_k(st, x, k, U32.is_eq(x, k), {==}, ht, eo, eg, en)

# No action a UE procedure takes is built from a key that is not live.
def Lv.spare_of(+st: S.State, +as: List<&2, N.Act>, +k: U32, +h: {Lv.actsw(st, as) == True{} : Bool}, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}) -> {N.Acts.spare(k, as) == True{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case +a <> +more:
      +ha = P.Bool.and_true_l(Lv.actw(st, a), Lv.actsw(st, more), h)
      P.Bool.and_intro(Bool.not(S.Maybe.same_u32(N.Act.ue(a), Some{k})), N.Acts.spare(k, more), Lv.tag_spare(st, N.Act.ue(a), k, P.Bool.and_true_r(Bool.not(N.Ngap.is_ng_setup_response(a)), Lv.tag(st, N.Act.ue(a)), ha), eo, eg, en), Lv.spare_of(st, more, k, P.Bool.and_true_r(Lv.actw(st, a), Lv.actsw(st, more), h), eo, eg, en))

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

def Lv.spare_step(+k: U32, +st: S.State, +o: N.GOut(), +h: {N.Acts.spare(k, N.Out.acts(o)) == True{} : Bool}) -> {N.Acts.spare(k, K.Kernel.actions(N.Step.of(st, o))) == True{} : Bool}:
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

def Lv.drop_spare(+st: S.State, +s1: S.State, +assoc: U32, +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}, +ess: {S.State.sessions(s1) == S.State.sessions(st) : Tb.Table(S.Session)}) -> {N.Acts.spare(k, K.Kernel.actions(R.Route.drop(s1, assoc))) == True{} : Bool}:
  match s1:
    case S.State{config, subs, assocs, +ues, +sessions, +pfcp_seq, next_ue, n4}:
      +gone = S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions)
      +d = Up.N4.deletions(gone, pfcp_seq)
      hr : {Lv.srows(gone, S.State.sessions(st)) == True{} : Bool} = (%ess : {Lv.srows(gone, _) == True{} : Bool}; Lv.srows_sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions))
      sss = Equal.sym(Tb.Table(S.Session), sessions, S.State.sessions(st), ess)
      hk : {Lv.krows(gone, st) == True{} : Bool} = (%sss : {Lv.krows(S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, _), st) == True{} : Bool}; Lv.krows_orphan(st, S.Ues.drop_assoc(assoc, ues)))
      +hd = Lv.dels(st, gone, pfcp_seq, hr, hk)
      +kept = S.Sessions.sift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, S.State.sessions(S.Tx.apply(N.Out.tx(d), S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4})))
      Lv.spare_app(k, N.Out.acts(d), N.Gone.cancels(sessions, kept), Lv.spare_of(st, N.Out.acts(d), k, Lv.acts_w(st, N.Out.acts(d), Lv.okf_acts(st, d, hd)), eo, eg, en), Lv.spare_gone(k, sessions, kept))

# An association's contexts re-initialised: its handovers end, then its
# contexts go.
def Lv.reset_spare(+st: S.State, +assoc: U32, +k: U32, +eo: {S.Sessions.owned(S.State.sessions(st), S.State.ues(st)) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +en: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}) -> {N.Acts.spare(k, K.Kernel.actions(R.Route.reset(st, assoc))) == True{} : Bool}:
  +o = Ho.Ho.down(st, assoc)
  +hq = Lw.ho_down_q(st, assoc)
  +hf = P.Bool.and_true_l(Lv.okf(st, o), Lv.quiet(N.Out.tx(o)), hq)
  +hx = Lv.spare_step(k, st, o, Lv.spare_of(st, N.Out.acts(o), k, Lv.acts_w(st, N.Out.acts(o), Lv.okf_acts(st, o, hf)), eo, eg, en))
  Lv.spare_app(k, K.Kernel.actions(N.Step.of(st, o)), K.Kernel.actions(R.Route.drop(K.Kernel.state(N.Step.of(st, o)), assoc)), hx, Lv.drop_spare(st, K.Kernel.state(N.Step.of(st, o)), assoc, k, eo, eg, en, Lw.down_sessions(st, assoc)))

def Lv.down_owned(+st: S.State, +assoc: U32) -> {S.Sessions.owned(S.State.sessions(K.Kernel.state(R.Route.drop(st, assoc))), S.State.ues(K.Kernel.state(R.Route.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s0 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      +tx = N.Out.tx(Up.N4.deletions(S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions), pfcp_seq))
      Lv.owned_owned(S.Ues.drop_assoc(assoc, ues), S.State.sessions(S.Tx.apply(tx, s0)))

# Invariants of every step
# ------------------------
# A property of the context and session tables that every transaction a UE
# procedure may run keeps (Inv.tx), and that dropping an association's
# contexts keeps (R.Route.drop), holds after every step (PW.Walk).

def Inv.Tx(-inv: Tb.Table(S.Ue) -> Tb.Table(S.Session) -> Bool, +st0: S.State) -> Type:
  @tx:S.Tx -> @st:S.State -> {inv(S.State.ues(st), S.State.sessions(st)) == True{} : Bool} -> {Lv.homedw(st0, tx, S.State.ues(st)) == True{} : Bool} -> {inv(S.State.ues(S.Tx.apply(tx, st)), S.State.sessions(S.Tx.apply(tx, st))) == True{} : Bool}

# Each kind of transaction keeps inv, a property of the tables under a
# premise pre on the state before the step: a walk over the transaction
# holds it through every one.

def Inv.Put(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+ue:S.Ue -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> @+h:{Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool} -> {inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}

def Inv.Rephase(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+p:S.Phase -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> @+h:{Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool} -> {inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}

def Inv.Del(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> {inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}

def Inv.PutSession(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+s:S.Session -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> @+h:{Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool} -> {inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}

def Inv.Revar(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+v:S.SVar -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> @+h:{Lv.revar_ok(st0, v) == True{} : Bool} -> {inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}

def Inv.DelSession(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, -pre: @+st0:S.State -> Bool) -> Type:
  @+st0:S.State -> @+ep:{pre(st0) == True{} : Bool} -> @+key:U32 -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> @+e:{inv(st0, ues, ss) == True{} : Bool} -> {inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}

# The second of two transactions is homed in the tables the first leaves.
def Inv.second(+st0: S.State, +a: S.Tx, +b: S.Tx, +st: S.State, +h: {Lv.homedw(st0, S.Both{a, b}, S.State.ues(st)) == True{} : Bool}) -> {Lv.homedw(st0, b, S.State.ues(S.Tx.apply(a, st))) == True{} : Bool}:
  eu = Equal.sym(Tb.Table(S.Ue), S.State.ues(S.Tx.apply(a, st)), PT.Tk.ues(a, S.State.ues(st)), PT.Tk.ues_apply(a, st))
  (%eu : {Lv.homedw(st0, b, _) == True{} : Bool}; P.Bool.and_true_r(Lv.homedw(st0, a, S.State.ues(st)), Lv.homedw(st0, b, PT.Tk.ues(a, S.State.ues(st))), h))

def Inv.tx(~inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, ~pre: @+st0:S.State -> Bool, ~put: Inv.Put(inv, pre), ~rephase: Inv.Rephase(inv, pre), ~del: Inv.Del(inv, pre), ~put_session: Inv.PutSession(inv, pre), ~revar: Inv.Revar(inv, pre), ~del_session: Inv.DelSession(inv, pre), +st0: S.State, +ep: {pre(st0) == True{} : Bool}, +tx: S.Tx, +st: S.State, +e: {inv(st0, S.State.ues(st), S.State.sessions(st)) == True{} : Bool}, +h: {Lv.homedw(st0, tx, S.State.ues(st)) == True{} : Bool}) -> {inv(st0, S.State.ues(S.Tx.apply(tx, st)), S.State.sessions(S.Tx.apply(tx, st))) == True{} : Bool}:
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
      Inv.tx(~inv, ~pre, ~put, ~rephase, ~del, ~put_session, ~revar, ~del_session, st0, ep, b, S.Tx.apply(a, st), Inv.tx(~inv, ~pre, ~put, ~rephase, ~del, ~put_session, ~revar, ~del_session, st0, ep, a, st, e, P.Bool.and_true_l(Lv.homedw(st0, a, S.State.ues(st)), Lv.homedw(st0, b, PT.Tk.ues(a, S.State.ues(st))), h)), Inv.second(st0, a, b, st, h))
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

def Inv.out(-inv: Tb.Table(S.Ue) -> Tb.Table(S.Session) -> Bool, +st: S.State, +o: N.GOut(), +e: {inv(S.State.ues(st), S.State.sessions(st)) == True{} : Bool}, t: Inv.Tx(inv, st), +h: {Lv.okw(st, o) == True{} : Bool}) -> PW.Walk.Tables(inv, N.Step.of(st, o)):
  match o:
    case (+tx, +acts):
      t(tx, st, e, P.Bool.and_true_r(Lv.actsw(st, acts), Lv.homedw(st, tx, S.State.ues(st)), h))

# An association's contexts re-initialised: its handovers end, then its
# contexts go.
def Inv.reset(-inv: Tb.Table(S.Ue) -> Tb.Table(S.Session) -> Bool, +st: S.State, +e: {inv(S.State.ues(st), S.State.sessions(st)) == True{} : Bool}, t: Inv.Tx(inv, st), down: @a:U32 -> @s:S.State -> {inv(S.State.ues(s), S.State.sessions(s)) == True{} : Bool} -> PW.Walk.Tables(inv, R.Route.drop(s, a)), +a: U32) -> PW.Walk.Tables(inv, R.Route.reset(st, a)):
  down(a, K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, a))), Inv.out(inv, st, Ho.Ho.down(st, a), e, t, Lv.ok_w(st, Ho.Ho.down(st, a), Lw.ho_down(st, a))))

def Inv.Down(-inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool) -> Type:
  @+st0:S.State -> @a:U32 -> @s:S.State -> {inv(st0, S.State.ues(s), S.State.sessions(s)) == True{} : Bool} -> PW.Walk.Tables(ues => ss => inv(st0, ues, ss), R.Route.drop(s, a))

def Inv.at(~inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, ~pre: @+st0:S.State -> Bool, ~put: Inv.Put(inv, pre), ~rephase: Inv.Rephase(inv, pre), ~del: Inv.Del(inv, pre), ~put_session: Inv.PutSession(inv, pre), ~revar: Inv.Revar(inv, pre), ~del_session: Inv.DelSession(inv, pre), +st: S.State, +ep: {pre(st) == True{} : Bool}) -> Inv.Tx(ues => ss => inv(st, ues, ss), st):
  tx => st2 => e2 => h => Inv.tx(~inv, ~pre, ~put, ~rephase, ~del, ~put_session, ~revar, ~del_session, st, ep, tx, st2, e2, h)

# An invariant of the tables, preserved by every transaction (put, rephase,
# ...) under pre and by an association's contexts dropped (down), holds after
# every step.
def Inv.step(~inv: @+st0:S.State -> @+ues:Tb.Table(S.Ue) -> @+ss:Tb.Table(S.Session) -> Bool, ~pre: @+st0:S.State -> Bool, ~put: Inv.Put(inv, pre), ~rephase: Inv.Rephase(inv, pre), ~del: Inv.Del(inv, pre), ~put_session: Inv.PutSession(inv, pre), ~revar: Inv.Revar(inv, pre), ~del_session: Inv.DelSession(inv, pre), ~down: Inv.Down(inv), +st: S.State, +ev: F.Evt, +entropy: B.Bytes(), +ep: {pre(st) == True{} : Bool}, +e: {inv(st, S.State.ues(st), S.State.sessions(st)) == True{} : Bool}) -> {inv(st, S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))), S.State.sessions(K.Kernel.state(K.Kernel.step(st, ev, entropy)))) == True{} : Bool}:
  Lv.walk(o => PW.Walk.Tables(ues => ss => inv(st, ues, ss), o), st, ev, entropy, acts => h => cx => nr => e, +a => ns => +id => +ok => +acts => h => cx => er => PW.Walk.assocs(ues => ss => inv(st, ues, ss), K.Kernel.state(R.Route.reset(st, a)), S.Assocs.set(a, id, S.State.assocs(K.Kernel.state(R.Route.reset(st, a))), ok), List.append(&2, N.Act, K.Kernel.actions(R.Route.reset(st, a)), acts), Inv.reset(ues => ss => inv(st, ues, ss), st, e, Inv.at(~inv, ~pre, ~put, ~rephase, ~del, ~put_session, ~revar, ~del_session, st, ep), down(st), a)), +tlvs => PW.Walk.config(ues => ss => inv(st, ues, ss), S.Cfg.complete(tlvs), st, tlvs, entropy, e), +a => Inv.reset(ues => ss => inv(st, ues, ss), st, e, Inv.at(~inv, ~pre, ~put, ~rephase, ~del, ~put_session, ~revar, ~del_session, st, ep), down(st), a), +o => h => Inv.out(ues => ss => inv(st, ues, ss), st, o, e, Inv.at(~inv, ~pre, ~put, ~rephase, ~del, ~put_session, ~revar, ~del_session, st, ep), h))

def Un.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  S.Ues.unique(ues)

def Un.tx_put(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Un.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.clear(key, ue, S.Ues.sift(S.Clear{key, ue}, ues)), S.Ues.unique(S.Ues.sift(S.Clear{key, ue}, ues)), PK.Clear.own(key, ue, ues), PK.Unique.sift(S.Clear{key, ue}, ues, e))

def Un.tx_rephase(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Un.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  er = Equal.sym(Bool, S.Ues.unique(S.Ues.rephase(key, p, ues)), S.Ues.unique(ues), PK.Unique.rephase(key, p, ues))
  %er : {_ == True{} : Bool}
  e

def Un.tx_del(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}) -> {Un.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  PK.Unique.sift(S.Except{key}, ues, e)

def Un.tx_put_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Un.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  e

def Un.tx_revar(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.revar_ok(st0, v) == True{} : Bool}) -> {Un.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  e

def Un.tx_del_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Un.inv(st0, ues, ss) == True{} : Bool}) -> {Un.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  e

def L.amf.indexes.unique(st, ev, entropy, e):
  ({==}, Inv.step(~Un.inv, ~Inv.none, ~Un.tx_put, ~Un.tx_rephase, ~Un.tx_del, ~Un.tx_put_session, ~Un.tx_revar, ~Un.tx_del_session, ~(st0 => a => s => e1 => PK.Down.unique(s, a, e1)), st, ev, entropy, {==}, e))

def L.amf.sessions.owned(st, ev, entropy, e):
  ({==}, Inv.step(~Ow.inv, ~Inv.none, ~Ow.tx_put, ~Ow.tx_rephase, ~Ow.tx_del, ~Ow.tx_put_session, ~Ow.tx_revar, ~Ow.tx_del_session, ~(st0 => a => s => e1 => Lv.down_owned(s, a)), st, ev, entropy, {==}, e))

# Contexts on associations set up
# -------------------------------

def Hm.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  S.Ues.set_up(ues, S.State.assocs(st0))

def Hm.pre(+st0: S.State) -> Bool:
  S.Ues.set_up(S.State.ues(st0), S.State.assocs(st0))

def Hm.sift(+s: S.Sieve, +ues: Tb.Table(S.Ue), +as: Tb.Table(B.Bytes()), +e: {S.Ues.set_up(ues, as) == True{} : Bool}) -> {S.Ues.set_up(S.Ues.sift(s, ues), as) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      P.Keep.by(S.Ue, tb => {S.Ues.set_up(tb, as) == True{} : Bool}, k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), e1 => h => P.Bool.and_intro(S.Assocs.has(S.Ue.assoc(v), as), S.Ues.set_up(S.Ues.sift(s, more), as), P.Bool.and_true_l(S.Assocs.has(S.Ue.assoc(v), as), S.Ues.set_up(more, as), e), h), Hm.sift(s, more, as, P.Bool.and_true_r(S.Assocs.has(S.Ue.assoc(v), as), S.Ues.set_up(more, as), e)))

def Hm.rephase_if(+b: Bool, +u: S.Ue, +p: S.Phase, +as: Tb.Table(B.Bytes()), +hu: {S.Assocs.has(S.Ue.assoc(u), as) == True{} : Bool}) -> {S.Assocs.has(S.Ue.assoc(S.Ue.rephase_if(u, p, b)), as) == True{} : Bool}:
  match b:
    case True{}:
      match u:
        case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
          hu
    case False{}:
      hu

def Hm.rephase(+key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +as: Tb.Table(B.Bytes()), +e: {S.Ues.set_up(ues, as) == True{} : Bool}) -> {S.Ues.set_up(S.Ues.rephase(key, p, ues), as) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      P.Bool.and_intro(S.Assocs.has(S.Ue.assoc(S.Ue.rephase_if(u, p, U32.is_eq(k, key))), as), S.Ues.set_up(S.Ues.rephase(key, p, more), as), Hm.rephase_if(U32.is_eq(k, key), u, p, as, P.Bool.and_true_l(S.Assocs.has(S.Ue.assoc(u), as), S.Ues.set_up(more, as), e)), Hm.rephase(key, p, more, as, P.Bool.and_true_r(S.Assocs.has(S.Ue.assoc(u), as), S.Ues.set_up(more, as), e)))

# A context put is at home, and every context of st0 is: it is set up.
def Hm.home(+st0: S.State, +ue: S.Ue, +ep: {Hm.pre(st0) == True{} : Bool}, +h: {Lv.home(st0, ue) == True{} : Bool}) -> {S.Assocs.has(S.Ue.assoc(ue), S.State.assocs(st0)) == True{} : Bool}:
  P.Bool.or_true_l(S.Assocs.has(S.Ue.assoc(ue), S.State.assocs(st0)), False{}, {==}, (%ep : {Bool.or(S.Assocs.has(S.Ue.assoc(ue), S.State.assocs(st0)), Bool.not(_)) == True{} : Bool}; h))

def Hm.tx_put(+st0: S.State, +ep: {Hm.pre(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Hm.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Hm.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  +hh = P.Bool.and_true_r(S.Ue.single(ue), Lv.home(st0, ue), P.Bool.and_true_r(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st0, ue)), P.Bool.and_true_r(Lv.keyed(st0, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st0, ue))), h)))
  P.Bool.and_intro(S.Assocs.has(S.Ue.assoc(ue), S.State.assocs(st0)), S.Ues.set_up(S.Ues.sift(S.Clear{key, ue}, ues), S.State.assocs(st0)), Hm.home(st0, ue, ep, hh), Hm.sift(S.Clear{key, ue}, ues, S.State.assocs(st0), e))

def Hm.tx_rephase(+st0: S.State, +ep: {Hm.pre(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Hm.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Hm.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  Hm.rephase(key, p, ues, S.State.assocs(st0), e)

def Hm.tx_del(+st0: S.State, +ep: {Hm.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Hm.inv(st0, ues, ss) == True{} : Bool}) -> {Hm.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Hm.sift(S.Except{key}, ues, S.State.assocs(st0), e)

def Hm.tx_put_session(+st0: S.State, +ep: {Hm.pre(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Hm.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Hm.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  e

def Hm.tx_revar(+st0: S.State, +ep: {Hm.pre(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Hm.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.revar_ok(st0, v) == True{} : Bool}) -> {Hm.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  e

def Hm.tx_del_session(+st0: S.State, +ep: {Hm.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Hm.inv(st0, ues, ss) == True{} : Bool}) -> {Hm.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  e

# No transaction moves the associations set up.
def Hm.tx_assocs(tx: S.Tx, +st: S.State) -> {S.State.assocs(S.Tx.apply(tx, st)) == S.State.assocs(st) : Tb.Table(B.Bytes())}:
  match tx:
    case S.Keep{}:
      {==}
    case S.Put{key, ue}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Rephase{key, phase}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Del{key}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.PutSession{key, s}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Revar{key, v}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.DelSession{key}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Subs{new}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.SetLink{link}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.BumpUe{bk}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.BumpSeq{n}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Both{+first, second}:
      Equal.trans(Tb.Table(B.Bytes()), S.State.assocs(S.Tx.apply(second, S.Tx.apply(first, st))), S.State.assocs(S.Tx.apply(first, st)), S.State.assocs(st), Hm.tx_assocs(second, S.Tx.apply(first, st)), Hm.tx_assocs(first, st))

def Hm.render(+st: S.State, o: N.GOut()) -> {S.State.assocs(K.Kernel.state(N.Step.of(st, o))) == S.State.assocs(st) : Tb.Table(B.Bytes())}:
  match o:
    case (tx, acts):
      Hm.tx_assocs(tx, st)

def Hm.out(+st: S.State, +o: N.GOut(), +e: {S.Ues.set_up(S.State.ues(st), S.State.assocs(st)) == True{} : Bool}, +h: {Lv.okw(st, o) == True{} : Bool}) -> {S.Ues.set_up(S.State.ues(K.Kernel.state(N.Step.of(st, o))), S.State.assocs(K.Kernel.state(N.Step.of(st, o)))) == True{} : Bool}:
  w = Inv.out(ues => ss => S.Ues.set_up(ues, S.State.assocs(st)), st, o, e, tx => st2 => e2 => h2 => Inv.tx(~Hm.inv, ~Hm.pre, ~Hm.tx_put, ~Hm.tx_rephase, ~Hm.tx_del, ~Hm.tx_put_session, ~Hm.tx_revar, ~Hm.tx_del_session, st, e, tx, st2, e2, h2), h)
  sr = Equal.sym(Tb.Table(B.Bytes()), S.State.assocs(K.Kernel.state(N.Step.of(st, o))), S.State.assocs(st), Hm.render(st, o))
  (%sr : {S.Ues.set_up(S.State.ues(K.Kernel.state(N.Step.of(st, o))), _) == True{} : Bool}; w)

def Hm.hit_has(+v: B.Bytes(), +m: Maybe<&2, B.Bytes()>, +c: Bool, +e: {Tb.Table.present(B.Bytes(), m) == True{} : Bool}) -> {Tb.Table.present(B.Bytes(), Tb.Table.hit(B.Bytes(), v, m, c)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      e

# An association dropped: what was set up and is another association stays set up.
def Hm.drop_row(+b: U32, +a: U32, +k0: U32, +id: B.Bytes(), +more: Tb.Table(B.Bytes()), +c: Bool, +ec: {U32.is_eq(k0, b) == c : Bool}, +ne: {U32.is_eq(b, a) == False{} : Bool}, +e: {Tb.Table.present(B.Bytes(), Tb.Table.hit(B.Bytes(), id, Tb.Table.get(B.Bytes(), b, more), c)) == True{} : Bool}, ih: {Tb.Table.has(B.Bytes(), b, more) == True{} : Bool} -> {S.Assocs.has(b, S.Assocs.drop(a, more)) == True{} : Bool}) -> {S.Assocs.has(b, Tb.Table.keep(B.Bytes(), k0, id, S.Assocs.drop(a, more), Bool.not(U32.is_eq(k0, a)))) == True{} : Bool}:
  match c:
    case True{}:
      sk = Equal.sym(U32, k0, b, P.U32.eq_of_is_eq(k0, b, ec))
      %sk : {S.Assocs.has(b, Tb.Table.keep(B.Bytes(), _, id, S.Assocs.drop(a, more), Bool.not(U32.is_eq(_, a)))) == True{} : Bool}
      sn = Equal.sym(Bool, U32.is_eq(b, a), False{}, ne)
      %sn : {S.Assocs.has(b, Tb.Table.keep(B.Bytes(), b, id, S.Assocs.drop(a, more), Bool.not(_))) == True{} : Bool}
      r = Equal.sym(Bool, U32.is_eq(b, b), True{}, P.U32.is_eq_refl(b))
      (%r : {Tb.Table.present(B.Bytes(), Tb.Table.hit(B.Bytes(), id, Tb.Table.get(B.Bytes(), b, S.Assocs.drop(a, more)), _)) == True{} : Bool}; {==})
    case False{}:
      P.Keep.by(B.Bytes(), tb => {Tb.Table.has(B.Bytes(), b, tb) == True{} : Bool}, k0, id, S.Assocs.drop(a, more), Bool.not(U32.is_eq(k0, a)), e1 => h => Hm.hit_has(id, Tb.Table.get(B.Bytes(), b, S.Assocs.drop(a, more)), U32.is_eq(k0, b), h), ih(e))

def Hm.drop_has(+b: U32, +a: U32, +as: Tb.Table(B.Bytes()), +ne: {U32.is_eq(b, a) == False{} : Bool}, +e: {S.Assocs.has(b, as) == True{} : Bool}) -> {S.Assocs.has(b, S.Assocs.drop(a, as)) == True{} : Bool}:
  match as:
    case Nil{}:
      e
    case (+k0, +id) <> +more:
      Hm.drop_row(b, a, k0, id, more, U32.is_eq(k0, b), {==}, ne, e, e2 => Hm.drop_has(b, a, more, ne, e2))

def Hm.set_has(+b: U32, +a: U32, +id: B.Bytes(), +as: Tb.Table(B.Bytes()), +ok: Bool, +ne: {U32.is_eq(b, a) == False{} : Bool}, +e: {S.Assocs.has(b, as) == True{} : Bool}) -> {S.Assocs.has(b, S.Assocs.set(a, id, as, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      Hm.hit_has(id, Tb.Table.get(B.Bytes(), b, S.Assocs.drop(a, as)), U32.is_eq(a, b), Hm.drop_has(b, a, as, ne, e))
    case False{}:
      Hm.drop_has(b, a, as, ne, e)

# The contexts of the other associations stay set up, without the association
# (drop) or with it set up again or not (ready).
def Hm.others_drop(+a: U32, +ues: Tb.Table(S.Ue), +as: Tb.Table(B.Bytes()), +e: {S.Ues.set_up(ues, as) == True{} : Bool}) -> {S.Ues.set_up(S.Ues.sift(S.Others{a}, ues), S.Assocs.drop(a, as)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      P.Keep.by(S.Ue, tb => {S.Ues.set_up(tb, S.Assocs.drop(a, as)) == True{} : Bool}, k, v, S.Ues.sift(S.Others{a}, more), Bool.not(U32.is_eq(S.Ue.assoc(v), a)), e1 => h => P.Bool.and_intro(S.Assocs.has(S.Ue.assoc(v), S.Assocs.drop(a, as)), S.Ues.set_up(S.Ues.sift(S.Others{a}, more), S.Assocs.drop(a, as)), Hm.drop_has(S.Ue.assoc(v), a, as, P.Bool.not_true(U32.is_eq(S.Ue.assoc(v), a), e1), P.Bool.and_true_l(S.Assocs.has(S.Ue.assoc(v), as), S.Ues.set_up(more, as), e)), h), Hm.others_drop(a, more, as, P.Bool.and_true_r(S.Assocs.has(S.Ue.assoc(v), as), S.Ues.set_up(more, as), e)))

def Hm.others_ready(+a: U32, +id: B.Bytes(), +ok: Bool, +ues: Tb.Table(S.Ue), +as: Tb.Table(B.Bytes()), +e: {S.Ues.set_up(ues, as) == True{} : Bool}) -> {S.Ues.set_up(S.Ues.sift(S.Others{a}, ues), S.Assocs.set(a, id, S.Assocs.drop(a, as), ok)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      P.Keep.by(S.Ue, tb => {S.Ues.set_up(tb, S.Assocs.set(a, id, S.Assocs.drop(a, as), ok)) == True{} : Bool}, k, v, S.Ues.sift(S.Others{a}, more), Bool.not(U32.is_eq(S.Ue.assoc(v), a)), +e1 => h => P.Bool.and_intro(S.Assocs.has(S.Ue.assoc(v), S.Assocs.set(a, id, S.Assocs.drop(a, as), ok)), S.Ues.set_up(S.Ues.sift(S.Others{a}, more), S.Assocs.set(a, id, S.Assocs.drop(a, as), ok)), Hm.set_has(S.Ue.assoc(v), a, id, S.Assocs.drop(a, as), ok, P.Bool.not_true(U32.is_eq(S.Ue.assoc(v), a), e1), Hm.drop_has(S.Ue.assoc(v), a, as, P.Bool.not_true(U32.is_eq(S.Ue.assoc(v), a), e1), P.Bool.and_true_l(S.Assocs.has(S.Ue.assoc(v), as), S.Ues.set_up(more, as), e))), h), Hm.others_ready(a, id, ok, more, as, P.Bool.and_true_r(S.Assocs.has(S.Ue.assoc(v), as), S.Ues.set_up(more, as), e)))

def Hm.drop(+st: S.State, +assoc: U32, +e: {S.Ues.set_up(S.State.ues(st), S.State.assocs(st)) == True{} : Bool}) -> {S.Ues.set_up(S.State.ues(K.Kernel.state(R.Route.drop(st, assoc))), S.State.assocs(K.Kernel.state(R.Route.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, +assocs, +ues, sessions, pfcp_seq, next_ue, n4}:
      Hm.others_drop(assoc, ues, assocs, e)

def Hm.ready(+st: S.State, +assoc: U32, +id: B.Bytes(), +ok: Bool, +e: {S.Ues.set_up(S.State.ues(st), S.State.assocs(st)) == True{} : Bool}) -> {S.Ues.set_up(S.State.ues(S.State.ready(K.Kernel.state(R.Route.drop(st, assoc)), assoc, id, ok)), S.State.assocs(S.State.ready(K.Kernel.state(R.Route.drop(st, assoc)), assoc, id, ok))) == True{} : Bool}:
  match st:
    case S.State{config, subs, +assocs, +ues, sessions, pfcp_seq, next_ue, n4}:
      Hm.others_ready(assoc, id, ok, ues, assocs, e)

def Hm.ho_down(+st: S.State, +assoc: U32, +e: {S.Ues.set_up(S.State.ues(st), S.State.assocs(st)) == True{} : Bool}) -> {S.Ues.set_up(S.State.ues(K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, assoc)))), S.State.assocs(K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, assoc))))) == True{} : Bool}:
  Hm.out(st, Ho.Ho.down(st, assoc), e, Lv.ok_w(st, Ho.Ho.down(st, assoc), Lw.ho_down(st, assoc)))

def Hm.config(+complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), +e: {S.Ues.set_up(S.State.ues(st), S.State.assocs(st)) == True{} : Bool}) -> {S.Ues.set_up(S.State.ues(K.Kernel.state(K.Kernel.config(complete, st, tlvs, entropy))), S.State.assocs(K.Kernel.state(K.Kernel.config(complete, st, tlvs, entropy)))) == True{} : Bool}:
  match complete:
    case False{}:
      e
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          e

def L.amf.contexts.set_up(st, ev, entropy, e):
  ({==}, Lv.walk(o => {S.Ues.set_up(S.State.ues(K.Kernel.state(o)), S.State.assocs(K.Kernel.state(o))) == True{} : Bool}, st, ev, entropy, acts => h => cx => nr => e, +a => ns => +id => +ok => acts => h => cx => er => Hm.ready(K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, a))), a, id, ok, Hm.ho_down(st, a, e)), +tlvs => Hm.config(S.Cfg.complete(tlvs), st, tlvs, entropy, e), +a => Hm.drop(K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, a))), a, Hm.ho_down(st, a, e)), +o => h => Hm.out(st, o, e, h)))

# Contexts stay guarded
# ---------------------

def Gd.sift(+s: S.Sieve, +ues: Tb.Table(S.Ue), +e: {S.Ues.guarded(ues) == True{} : Bool}) -> {S.Ues.guarded(S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      P.Keep.by(S.Ue, tb => {S.Ues.guarded(tb) == True{} : Bool}, k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), e1 => h => P.Bool.and_intro(S.Phase.guarded(S.Ue.phase(v)), S.Ues.guarded(S.Ues.sift(s, more)), P.Bool.and_true_l(S.Phase.guarded(S.Ue.phase(v)), S.Ues.guarded(more), e), h), Gd.sift(s, more, P.Bool.and_true_r(S.Phase.guarded(S.Ue.phase(v)), S.Ues.guarded(more), e)))

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

def Gd.tx_put(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Gd.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Phase.guarded(S.Ue.phase(ue)), S.Ues.guarded(S.Ues.sift(S.Clear{key, ue}, ues)), P.Bool.and_true_l(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st0, ue)), P.Bool.and_true_r(Lv.keyed(st0, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st0, ue))), h)), Gd.sift(S.Clear{key, ue}, ues, e))

def Gd.tx_rephase(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Gd.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  Gd.rephase(key, p, ues, e, P.Bool.and_true_l(S.Phase.guarded(p), S.Ue.fits(p, Tb.Table.get(S.Ue, key, ues)), h))

def Gd.tx_del(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}) -> {Gd.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Gd.sift(S.Except{key}, ues, e)

def Gd.tx_put_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Gd.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  e

def Gd.tx_revar(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.revar_ok(st0, v) == True{} : Bool}) -> {Gd.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  e

def Gd.tx_del_session(+st0: S.State, +ep: {Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Gd.inv(st0, ues, ss) == True{} : Bool}) -> {Gd.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  e

def Gd.down(+st: S.State, +assoc: U32, +e: {S.Ues.guarded(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.guarded(S.State.ues(K.Kernel.state(R.Route.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, n4}:
      Gd.sift(S.Others{assoc}, ues, e)

def L.amf.contexts.guarded(st, ev, entropy, e):
  ({==}, Inv.step(~Gd.inv, ~Inv.none, ~Gd.tx_put, ~Gd.tx_rephase, ~Gd.tx_del, ~Gd.tx_put_session, ~Gd.tx_revar, ~Gd.tx_del_session, ~(st0 => a => s => e1 => Gd.down(s, a, e1)), st, ev, entropy, {==}, e))

# Keys
# ----
# Every context key odd and every session key even and not zero, by the keys
# a step puts: a context under a key held, a session under a SEID drawn
# (S.Ids). A context appears only under a key held, that is a context's or
# the one the step gives.

def Id.sift(+s: S.Sieve, +ues: Tb.Table(S.Ue), +e: {S.Ues.keyed(ues) == True{} : Bool}) -> {S.Ues.keyed(S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      P.Keep.by(S.Ue, tb => {S.Ues.keyed(tb) == True{} : Bool}, k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), e1 => h => P.Bool.and_intro(S.Ids.odd(k), S.Ues.keyed(S.Ues.sift(s, more)), P.Bool.and_true_l(S.Ids.odd(k), S.Ues.keyed(more), e), h), Id.sift(s, more, P.Bool.and_true_r(S.Ids.odd(k), S.Ues.keyed(more), e)))

def Id.rephase(+key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +e: {S.Ues.keyed(ues) == True{} : Bool}) -> {S.Ues.keyed(S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      P.Bool.and_intro(S.Ids.odd(k), S.Ues.keyed(S.Ues.rephase(key, p, more)), P.Bool.and_true_l(S.Ids.odd(k), S.Ues.keyed(more), e), Id.rephase(key, p, more, P.Bool.and_true_r(S.Ids.odd(k), S.Ues.keyed(more), e)))

def Id.ssift(+s: S.SSieve, +ss: Tb.Table(S.Session), +e: {S.Sessions.keyed(ss) == True{} : Bool}) -> {S.Sessions.keyed(S.Sessions.sift(s, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {S.Sessions.keyed(tb) == True{} : Bool}, k, t, S.Sessions.sift(s, more), S.SSieve.keeps(s, k, t), e1 => h => P.Bool.and_intro(S.Ids.seid(k), S.Sessions.keyed(S.Sessions.sift(s, more)), P.Bool.and_true_l(S.Ids.seid(k), S.Sessions.keyed(more), e), h), Id.ssift(s, more, P.Bool.and_true_r(S.Ids.seid(k), S.Sessions.keyed(more), e)))

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

def Id.tx_put(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Id.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  +e0 = P.Bool.and_true_l(S.Ids.free(S.State.ues(st0), S.State.sessions(st0)), S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0)), ep)
  +eo = P.Bool.and_true_r(S.Ids.free(S.State.ues(st0), S.State.sessions(st0)), S.Sessions.owned(S.State.sessions(st0), S.State.ues(st0)), ep)
  +ho = Id.put_odd(st0, e0, eo, key, P.Bool.and_true_l(Lv.keyed(st0, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st0, ue))), h))
  P.Bool.and_intro(S.Ues.keyed(S.Ues.put(key, ue, ues)), S.Sessions.keyed(S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)), P.Bool.and_intro(S.Ids.odd(key), S.Ues.keyed(S.Ues.sift(S.Clear{key, ue}, ues)), ho, Id.sift(S.Clear{key, ue}, ues, P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e))), Id.ssift(S.SOwned{S.Ues.put(key, ue, ues)}, ss, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)))

def Id.tx_rephase(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Id.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.keyed(S.Ues.rephase(key, p, ues)), S.Sessions.keyed(ss), Id.rephase(key, p, ues, P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)), P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e))

def Id.tx_del(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}) -> {Id.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.keyed(S.Ues.del(key, ues)), S.Sessions.keyed(S.Sessions.drop_ue(key, ss)), Id.sift(S.Except{key}, ues, P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)), Id.ssift(S.SOthers{key}, ss, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)))

def Id.tx_put_session(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Id.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  +old = Bool.and(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s))))
  P.Bool.and_intro(S.Ues.keyed(ues), S.Sessions.keyed(S.Sessions.put(key, s, ss)), P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e), P.Bool.and_intro(S.Ids.seid(key), S.Sessions.keyed(S.Sessions.sift(S.SClear{key, s}, ss)), P.Bool.and_true_l(S.Ids.seid(key), old, h), Id.ssift(S.SClear{key, s}, ss, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e))))

def Id.tx_revar(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.revar_ok(st0, v) == True{} : Bool}) -> {Id.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.keyed(ues), S.Sessions.keyed(S.Sessions.revar(key, v, ss)), P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e), Id.srevar(key, v, ss, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)))

def Id.tx_del_session(+st0: S.State, +ep: {Id.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Id.inv(st0, ues, ss) == True{} : Bool}) -> {Id.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.keyed(ues), S.Sessions.keyed(S.Sessions.del(key, ss)), P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(ss), e), Id.ssift(S.SExcept{key}, ss, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(ss), e)))

# Changing sessions in place and forgetting them keep every session key.
def Id.sx(+tx: S.Tx, +st: S.State, +e: {S.Sessions.keyed(S.State.sessions(st)) == True{} : Bool}, +ex: {PW.Sx.only(tx) == True{} : Bool}) -> {S.Sessions.keyed(S.State.sessions(S.Tx.apply(tx, st))) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      e
    case S.SetLink{link}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          e
    case S.Revar{+key, +v}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Id.srevar(key, v, sessions, e)
    case S.DelSession{+key}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Id.ssift(S.SExcept{key}, sessions, e)
    case S.BumpSeq{n}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          e
    case S.Both{+a, +b}:
      Id.sx(b, S.Tx.apply(a, st), Id.sx(a, st, e, P.Bool.and_true_l(PW.Sx.only(a), PW.Sx.only(b), ex)), P.Bool.and_true_r(PW.Sx.only(a), PW.Sx.only(b), ex))
    case S.Put{key, ue}:
      Empty.absurd({S.Sessions.keyed(S.State.sessions(S.Tx.apply(S.Put{key, ue}, st))) == True{} : Bool}, P.Refute.bool(ex))
    case S.Rephase{key, phase}:
      Empty.absurd({S.Sessions.keyed(S.State.sessions(S.Tx.apply(S.Rephase{key, phase}, st))) == True{} : Bool}, P.Refute.bool(ex))
    case S.Del{key}:
      Empty.absurd({S.Sessions.keyed(S.State.sessions(S.Tx.apply(S.Del{key}, st))) == True{} : Bool}, P.Refute.bool(ex))
    case S.PutSession{key, s}:
      Empty.absurd({S.Sessions.keyed(S.State.sessions(S.Tx.apply(S.PutSession{key, s}, st))) == True{} : Bool}, P.Refute.bool(ex))
    case S.Subs{new}:
      Empty.absurd({S.Sessions.keyed(S.State.sessions(S.Tx.apply(S.Subs{new}, st))) == True{} : Bool}, P.Refute.bool(ex))
    case S.BumpUe{bk}:
      Empty.absurd({S.Sessions.keyed(S.State.sessions(S.Tx.apply(S.BumpUe{bk}, st))) == True{} : Bool}, P.Refute.bool(ex))

def Id.down(+st: S.State, +assoc: U32, +e: {S.Ids.free(S.State.ues(st), S.State.sessions(st)) == True{} : Bool}) -> {S.Ids.free(S.State.ues(K.Kernel.state(R.Route.drop(st, assoc))), S.State.sessions(K.Kernel.state(R.Route.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s0 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      +gone = S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions)
      +tx = N.Out.tx(Up.N4.deletions(gone, pfcp_seq))
      +s1 = S.State.sessions(S.Tx.apply(tx, s0))
      P.Bool.and_intro(S.Ues.keyed(S.Ues.drop_assoc(assoc, ues)), S.Sessions.keyed(S.Sessions.sift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, s1)), Id.sift(S.Others{assoc}, ues, P.Bool.and_true_l(S.Ues.keyed(ues), S.Sessions.keyed(sessions), e)), Id.ssift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, s1, Id.sx(tx, s0, P.Bool.and_true_r(S.Ues.keyed(ues), S.Sessions.keyed(sessions), e), PW.Sx.deletions(gone, pfcp_seq))))

# No session holds a key that is not a local SEID, nor a context a key that is not odd.
def Id.miss_srow(+k: U32, +k0: U32, +t: S.Session, +more: Tb.Table(S.Session), +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +e: {Bool.and(S.Ids.seid(k0), S.Sessions.keyed(more)) == True{} : Bool}, +f: {S.Ids.seid(k) == False{} : Bool}, ih: {S.Sessions.keyed(more) == True{} : Bool} -> {Tb.Table.has(S.Session, k, more) == False{} : Bool}) -> {Tb.Table.present(S.Session, Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), b)) == False{} : Bool}:
  match b:
    case True{}:
      ek = P.U32.eq_of_is_eq(k0, k, eb)
      hk : {S.Ids.seid(k) == True{} : Bool} = (%ek : {S.Ids.seid(_) == True{} : Bool}; P.Bool.and_true_l(S.Ids.seid(k0), S.Sessions.keyed(more), e))
      P.Bool.contra({True{} == False{} : Bool}, S.Ids.seid(k), hk, f)
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
      P.Bool.contra({True{} == False{} : Bool}, S.Ids.odd(k), hk, f)
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

def Pv.sift(+st0: S.State, +s: S.Sieve, +ues: Tb.Table(S.Ue), +e: {Pv.all(st0, ues) == True{} : Bool}) -> {Pv.all(st0, S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      P.Keep.by(S.Ue, tb => {Pv.all(st0, tb) == True{} : Bool}, k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), e1 => h => P.Bool.and_intro(Lv.held(st0, k), Pv.all(st0, S.Ues.sift(s, more)), P.Bool.and_true_l(Lv.held(st0, k), Pv.all(st0, more), e), h), Pv.sift(st0, s, more, P.Bool.and_true_r(Lv.held(st0, k), Pv.all(st0, more), e)))

def Pv.rephase(+st0: S.State, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +e: {Pv.all(st0, ues) == True{} : Bool}) -> {Pv.all(st0, S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      P.Bool.and_intro(Lv.held(st0, k), Pv.all(st0, S.Ues.rephase(key, p, more)), P.Bool.and_true_l(Lv.held(st0, k), Pv.all(st0, more), e), Pv.rephase(st0, key, p, more, P.Bool.and_true_r(Lv.held(st0, k), Pv.all(st0, more), e)))

def Pv.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  Pv.all(st0, ues)

def Pv.tx_put(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Pv.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  P.Bool.and_intro(Lv.held(st0, key), Pv.all(st0, S.Ues.sift(S.Clear{key, ue}, ues)), Id.keyed_held(st0, key, ep, P.Bool.and_true_l(Lv.keyed(st0, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), Lv.home(st0, ue))), h)), Pv.sift(st0, S.Clear{key, ue}, ues, e))

def Pv.tx_rephase(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Pv.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  Pv.rephase(st0, key, p, ues, e)

def Pv.tx_del(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}) -> {Pv.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Pv.sift(st0, S.Except{key}, ues, e)

def Pv.tx_put_session(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Pv.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  e

def Pv.tx_revar(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}, +h: {Lv.revar_ok(st0, v) == True{} : Bool}) -> {Pv.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  e

def Pv.tx_del_session(+st0: S.State, +ep: {Inv.owned(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Pv.inv(st0, ues, ss) == True{} : Bool}) -> {Pv.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  e

def Pv.down(+st0: S.State, +st: S.State, +assoc: U32, +e: {Pv.all(st0, S.State.ues(st)) == True{} : Bool}) -> {Pv.all(st0, S.State.ues(K.Kernel.state(R.Route.drop(st, assoc)))) == True{} : Bool}:
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
  +pv = Inv.step(~Pv.inv, ~Inv.owned, ~Pv.tx_put, ~Pv.tx_rephase, ~Pv.tx_del, ~Pv.tx_put_session, ~Pv.tx_revar, ~Pv.tx_del_session, ~(st0 => a => s => e1 => Pv.down(st0, s, a, e1)), st, ev, entropy, eo, Pv.of_keys(st, S.State.ues(st), Pv.refl(S.State.ues(st))))
  +iv = Inv.step(~Id.inv, ~Id.pre, ~Id.tx_put, ~Id.tx_rephase, ~Id.tx_del, ~Id.tx_put_session, ~Id.tx_revar, ~Id.tx_del_session, ~(st0 => a => s => e1 => Id.down(s, a, e1)), st, ev, entropy, P.Bool.and_intro(S.Ids.free(S.State.ues(st), S.State.sessions(st)), S.Sessions.owned(S.State.sessions(st), S.State.ues(st)), e, eo), e)
  (em => PT.Fresh.none(st, k, em), (eg => eh => Pv.fresh(st, k, eg, Pv.held_of(st, S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))), k, pv, eh)), ({==}, (iv, (eh => Id.miss_s(S.State.sessions(st), k, es, Id.odd_seid(k, Id.has_odd(S.State.ues(st), k, eu, eh))), (Id.miss_u(S.State.ues(st), S.N4.timer(), eu, {==}), Id.miss_s(S.State.sessions(st), S.N4.timer(), es, {==})))))))

# Guards stopped
# --------------
# A step that removes a session row stops its guard: every outcome's actions
# end with the stops N.Step.of adds for the rows gone, and an association's
# reset adds the same; the other steps keep the session table.

def Gs.stops_app(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.stops(k, ys) == True{} : Bool}) -> {N.Acts.stops(k, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +a <> +more:
      P.Bool.or_r(N.Act.stops(k, a), N.Acts.stops(k, List.append(&2, N.Act, more, ys)), Gs.stops_app(k, more, ys, h))

def Gs.stops_pre_if(+k: U32, +a: N.Act, +more: List<&2, N.Act>, +ys: List<&2, N.Act>, +b: Bool, +eb: {N.Act.stops(k, a) == b : Bool}, +h: {Bool.or(b, N.Acts.stops(k, more)) == True{} : Bool}, ih: {N.Acts.stops(k, more) == True{} : Bool} -> {N.Acts.stops(k, List.append(&2, N.Act, more, ys)) == True{} : Bool}) -> {Bool.or(N.Act.stops(k, a), N.Acts.stops(k, List.append(&2, N.Act, more, ys))) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.or_l(N.Act.stops(k, a), N.Acts.stops(k, List.append(&2, N.Act, more, ys)), eb)
    case False{}:
      P.Bool.or_r(N.Act.stops(k, a), N.Acts.stops(k, List.append(&2, N.Act, more, ys)), ih(h))

def Gs.stops_pre(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.stops(k, xs) == True{} : Bool}) -> {N.Acts.stops(k, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({N.Acts.stops(k, ys) == True{} : Bool}, P.Refute.bool(h))
    case +a <> +more:
      Gs.stops_pre_if(k, a, more, ys, N.Act.stops(k, a), {==}, h, e => Gs.stops_pre(k, more, ys, e))

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

def Gs.down(+st: S.State, +assoc: U32, +k: U32, +s: S.Session, +g: S.Guard, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +eg: {S.SPhase.guard(S.Session.phase(s)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.get(S.Session, k, S.State.sessions(K.Kernel.state(R.Route.drop(st, assoc)))) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, K.Kernel.actions(R.Route.drop(st, assoc))) == True{} : Bool}:
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +left = S.Ues.drop_assoc(assoc, ues)
      +d = Up.N4.deletions(S.Sessions.sift(S.SOrphan{left}, sessions), pfcp_seq)
      +kept = S.Sessions.sift(S.SOwned{left}, S.State.sessions(S.Tx.apply(N.Out.tx(d), S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4})))
      Gs.stops_app(k, N.Out.acts(d), N.Gone.cancels(sessions, kept), Gs.gone(sessions, kept, k, s, g, es, eg, eh))

# An association's contexts re-initialised: its handovers end, leaving the
# sessions, then its contexts go.
def Gs.reset(+st: S.State, +assoc: U32, +k: U32, +s: S.Session, +g: S.Guard, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +eg: {S.SPhase.guard(S.Session.phase(s)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.get(S.Session, k, S.State.sessions(K.Kernel.state(R.Route.reset(st, assoc)))) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, K.Kernel.actions(R.Route.reset(st, assoc))) == True{} : Bool}:
  +s1 = K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, assoc)))
  ss = Equal.sym(Tb.Table(S.Session), S.State.sessions(s1), S.State.sessions(st), Lw.down_sessions(st, assoc))
  es1 : {Tb.Table.get(S.Session, k, S.State.sessions(s1)) == Some{s} : Maybe<&2, S.Session>} = (%ss : {Tb.Table.get(S.Session, k, _) == Some{s} : Maybe<&2, S.Session>}; es)
  Gs.stops_app(k, K.Kernel.actions(N.Step.of(st, Ho.Ho.down(st, assoc))), K.Kernel.actions(R.Route.drop(s1, assoc)), Gs.down(s1, assoc, k, s, g, es1, eg, eh))

def L.smf.guard.stopped(st, ev, entropy, k, s, g, es, eg, eh):
  PW.Walk.any(o => {Tb.Table.get(S.Session, k, S.State.sessions(K.Kernel.state(o))) == None{} : Maybe<&2, S.Session>} -> {N.Acts.stops(k, K.Kernel.actions(o)) == True{} : Bool}, st, ev, entropy, acts => h => cx => nr => eh => Empty.absurd({N.Acts.stops(k, acts) == True{} : Bool}, Gs.kept(S.State.sessions(st), k, s, es, eh)), +a => ns => +id => +ok => +acts => h => cx => er => eh => Gs.stops_pre(k, K.Kernel.actions(R.Route.reset(st, a)), acts, Gs.reset(st, a, k, s, g, es, eg, (%PW.Walk.assocs_sessions(K.Kernel.state(R.Route.reset(st, a)), S.Assocs.set(a, id, S.State.assocs(K.Kernel.state(R.Route.reset(st, a))), ok)) : {Tb.Table.get(S.Session, k, _) == None{} : Maybe<&2, S.Session>}; eh))), +tlvs => eh => Gs.config(S.Cfg.complete(tlvs), st, tlvs, entropy, k, s, g, es, eg, eh), +a => eh => Gs.reset(st, a, k, s, g, es, eg, eh), +o => eh => Gs.of(st, o, k, s, g, es, eg, eh))(eh)

def L.amf.release.forgets_ue(st, ev, entropy, k, eo, eg, en):
  Lv.walk(o => {N.Acts.spare(k, K.Kernel.actions(o)) == True{} : Bool}, st, ev, entropy, acts => h => cx => nr => h(k), +a => ns => +id => +ok => +acts => h => cx => er => Lv.spare_app(k, K.Kernel.actions(R.Route.reset(st, a)), acts, Lv.reset_spare(st, a, k, eo, eg, en), h(k)), +tlvs => Lv.config_spare(S.Cfg.complete(tlvs), st, tlvs, entropy, k), a => Lv.reset_spare(st, a, k, eo, eg, en), +o => h => Lv.spare_of(st, K.Kernel.actions(N.Step.of(st, o)), k, Lv.step_acts(st, o, h), eo, eg, en))


