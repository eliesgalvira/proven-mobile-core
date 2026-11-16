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
import ../tlv.bend as T
import ../pfcp.bend as Pf
import ../plmn.bend as Pl
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/gmm.bend as Gmm
import ../amf/route.bend as R
import ../smf/n4.bend as Up
import ../smf/gsm.bend as Gsm
import ../ausf.bend as Au
import ../amf/handover.bend as Ho
import ../LAWS.bend as L
import ./lib.bend as P
import ./walk.bend as PW
import ./takeover.bend as PT
import ./liveness.bend as PL

# Proofs of the SMF's laws (tickets 19 and 34).

def SUnique.sift(+v: S.SSieve, sessions: Tb.Table(S.Session), +e: {S.Sessions.unique(sessions) == True{} : Bool}) -> {S.Sessions.unique(S.Sessions.sift(v, sessions)) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+key, +s) <> +more:
      P.Keep.by(S.Session, tb => {S.Sessions.unique(tb) == True{} : Bool}, key, s, S.Sessions.sift(v, more), S.SSieve.keeps(v, key, s), e1 => h => P.Bool.and_intro(S.Sessions.clear(key, s, S.Sessions.sift(v, more)), S.Sessions.unique(S.Sessions.sift(v, more)), PL.Lv.clear_sift(key, s, v, more, P.Bool.and_true_l(S.Sessions.clear(key, s, more), S.Sessions.unique(more), e)), h), SUnique.sift(v, more, P.Bool.and_true_r(S.Sessions.clear(key, s, more), S.Sessions.unique(more), e)))

def SClear.own(+key: U32, +s: S.Session, sessions: Tb.Table(S.Session)) -> {S.Sessions.clear(key, s, S.Sessions.sift(S.SClear{key, s}, sessions)) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {S.Sessions.clear(key, s, tb) == True{} : Bool}, k, t, S.Sessions.sift(S.SClear{key, s}, more), S.SSieve.keeps(S.SClear{key, s}, k, t), e => h => P.Bool.and_intro(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, S.Sessions.sift(S.SClear{key, s}, more)), e, h), SClear.own(key, s, more))

def SDel.get(+key: U32, sessions: Tb.Table(S.Session)) -> {Tb.Table.get(S.Session, key, S.Sessions.del(key, sessions)) == None{} : Maybe<&2, S.Session>}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {Tb.Table.get(S.Session, key, tb) == None{} : Maybe<&2, S.Session>}, k, t, S.Sessions.sift(S.SExcept{key}, more), S.SSieve.keeps(S.SExcept{key}, k, t), e => h => (%Equal.sym(Bool, U32.is_eq(k, key), False{}, P.Bool.not_true(U32.is_eq(k, key), e)) : {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, key, S.Sessions.sift(S.SExcept{key}, more)), _) == None{} : Maybe<&2, S.Session>}; h), SDel.get(key, more))

# A change of a session in place keeps its identity and keeps or drops its
# tag (PW.Tg), so it adds no conflict.

def Cf.not_of(+x: Bool, +e: {x == False{} : Bool}) -> {Bool.not(x) == True{} : Bool}:
  se = Equal.sym(Bool, x, False{}, e)
  (%se : {Bool.not(_) == True{} : Bool}; {==})

def Cf.and_mono(+z: Bool, +z2: Bool, +w: Bool, +e: {Bool.and(z, w) == False{} : Bool}, f: {z == False{} : Bool} -> {z2 == False{} : Bool}) -> {Bool.and(z2, w) == False{} : Bool}:
  match z:
    case False{}:
      ez = Equal.sym(Bool, z2, False{}, f({==}))
      (%ez : {Bool.and(_, w) == False{} : Bool}; {==})
    case True{}:
      match z2:
        case True{}:
          e
        case False{}:
          {==}

# Moved at the second place: no conflict is added.
def Cf.r(+a: S.Session, +t: S.Session, +t2: S.Session, +h: PW.Tg.Moved(t, t2), +ei: {S.Session.id(t2) == S.Session.id(t) : S.SId}, +e: {S.Session.conflicts(a, t) == False{} : Bool}) -> {S.Session.conflicts(a, t2) == False{} : Bool}:
  +z = S.Maybe.same_u32(S.Session.tag(a), S.Session.tag(t))
  +z2 = S.Maybe.same_u32(S.Session.tag(a), S.Session.tag(t2))
  sei = Equal.sym(S.SId, S.Session.id(t2), S.Session.id(t), ei)
  (%sei : {Bool.or(U32.is_eq(S.Session.ip(a), S.SId.ip(_)), Bool.or(U32.is_eq(S.Session.teid(a), S.SId.teid(_)), Bool.and(z2, U32.is_eq(S.Session.psi(a), S.SId.psi(_))))) == False{} : Bool}; P.Bool.or_mono_false(U32.is_eq(S.Session.ip(a), S.Session.ip(t)), Bool.or(U32.is_eq(S.Session.teid(a), S.Session.teid(t)), Bool.and(z, U32.is_eq(S.Session.psi(a), S.Session.psi(t)))), Bool.or(U32.is_eq(S.Session.teid(a), S.Session.teid(t)), Bool.and(z2, U32.is_eq(S.Session.psi(a), S.Session.psi(t)))), e, e1 => P.Bool.or_mono_false(U32.is_eq(S.Session.teid(a), S.Session.teid(t)), Bool.and(z, U32.is_eq(S.Session.psi(a), S.Session.psi(t))), Bool.and(z2, U32.is_eq(S.Session.psi(a), S.Session.psi(t))), e1, e2 => Cf.and_mono(z, z2, U32.is_eq(S.Session.psi(a), S.Session.psi(t)), e2, ez => PW.Tg.same_r(S.Session.tag(a), t, t2, h, ez)))))

# Two sessions conflict whichever way round they are compared.
def Session.conflicts_sym(+a: S.Session, +b: S.Session) -> {S.Session.conflicts(a, b) == S.Session.conflicts(b, a) : Bool}:
  +l = S.Session.conflicts(a, b)
  %P.U32.sym(S.Session.ip(a), S.Session.ip(b)) : {l == Bool.or(_, Bool.or(U32.is_eq(S.Session.teid(b), S.Session.teid(a)), Bool.and(S.Maybe.same_u32(S.Session.tag(b), S.Session.tag(a)), U32.is_eq(S.Session.psi(b), S.Session.psi(a))))) : Bool}
  %P.U32.sym(S.Session.teid(a), S.Session.teid(b)) : {l == Bool.or(U32.is_eq(S.Session.ip(a), S.Session.ip(b)), Bool.or(_, Bool.and(S.Maybe.same_u32(S.Session.tag(b), S.Session.tag(a)), U32.is_eq(S.Session.psi(b), S.Session.psi(a))))) : Bool}
  %PT.Same.u32_sym(S.Session.tag(a), S.Session.tag(b)) : {l == Bool.or(U32.is_eq(S.Session.ip(a), S.Session.ip(b)), Bool.or(U32.is_eq(S.Session.teid(a), S.Session.teid(b)), Bool.and(_, U32.is_eq(S.Session.psi(b), S.Session.psi(a))))) : Bool}
  %P.U32.sym(S.Session.psi(a), S.Session.psi(b)) : {l == Bool.or(U32.is_eq(S.Session.ip(a), S.Session.ip(b)), Bool.or(U32.is_eq(S.Session.teid(a), S.Session.teid(b)), Bool.and(S.Maybe.same_u32(S.Session.tag(a), S.Session.tag(b)), _))) : Bool}
  {==}

def SClear.revar(+key2: U32, +s: S.Session, +key: U32, +v: S.SVar, sessions: Tb.Table(S.Session), +e: {S.Sessions.clear(key2, s, sessions) == True{} : Bool}) -> {S.Sessions.clear(key2, s, S.Sessions.revar(key, v, sessions)) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +hit = Bool.and(U32.is_eq(k, key), S.SVar.follows(v, t))
      +t2 = S.Session.revar_if(t, v, hit)
      +c = S.SRow.conflicts(key2, s, k, t)
      +nc = P.Bool.not_true(c, P.Bool.and_true_l(Bool.not(c), S.Sessions.clear(key2, s, more), e))
      P.Bool.and_intro(Bool.not(S.SRow.conflicts(key2, s, k, t2)), S.Sessions.clear(key2, s, S.Sessions.revar(key, v, more)), Cf.not_of(S.SRow.conflicts(key2, s, k, t2), P.Bool.or_mono_false(U32.is_eq(k, key2), S.Session.conflicts(s, t), S.Session.conflicts(s, t2), nc, ec => Cf.r(s, t, t2, PW.Tg.revar(t, v, U32.is_eq(k, key)), PW.Tg.id(t, v, hit), ec))), SClear.revar(key2, s, key, v, more, P.Bool.and_true_r(Bool.not(c), S.Sessions.clear(key2, s, more), e)))

def SClear.subject(+key: U32, +s: S.Session, +s2: S.Session, +h: PW.Tg.Moved(s, s2), +ei: {S.Session.id(s2) == S.Session.id(s) : S.SId}, sessions: Tb.Table(S.Session), +e: {S.Sessions.clear(key, s, sessions) == True{} : Bool}) -> {S.Sessions.clear(key, s2, sessions) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +c = S.SRow.conflicts(key, s, k, t)
      +nc = P.Bool.not_true(c, P.Bool.and_true_l(Bool.not(c), S.Sessions.clear(key, s, more), e))
      P.Bool.and_intro(Bool.not(S.SRow.conflicts(key, s2, k, t)), S.Sessions.clear(key, s2, more), Cf.not_of(S.SRow.conflicts(key, s2, k, t), P.Bool.or_mono_false(U32.is_eq(k, key), S.Session.conflicts(s, t), S.Session.conflicts(s2, t), nc, ec => (%Session.conflicts_sym(t, s2) : {_ == False{} : Bool}; Cf.r(t, s, s2, h, ei, (%Session.conflicts_sym(s, t) : {_ == False{} : Bool}; ec))))), SClear.subject(key, s, s2, h, ei, more, P.Bool.and_true_r(Bool.not(c), S.Sessions.clear(key, s, more), e)))

def SUnique.revar(+key: U32, +v: S.SVar, sessions: Tb.Table(S.Session), +e: {S.Sessions.unique(sessions) == True{} : Bool}) -> {S.Sessions.unique(S.Sessions.revar(key, v, sessions)) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +s) <> +more:
      +hit = Bool.and(U32.is_eq(k, key), S.SVar.follows(v, s))
      +s2 = S.Session.revar_if(s, v, hit)
      +ec = P.Bool.and_true_l(S.Sessions.clear(k, s, more), S.Sessions.unique(more), e)
      P.Bool.and_intro(S.Sessions.clear(k, s2, S.Sessions.revar(key, v, more)), S.Sessions.unique(S.Sessions.revar(key, v, more)), SClear.subject(k, s, s2, PW.Tg.revar(s, v, U32.is_eq(k, key)), PW.Tg.id(s, v, hit), S.Sessions.revar(key, v, more), SClear.revar(k, s, key, v, more, ec)), SUnique.revar(key, v, more, P.Bool.and_true_r(S.Sessions.clear(k, s, more), S.Sessions.unique(more), e)))

# Sessions stay unique
# --------------------

def Su.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  S.Sessions.unique(ss)

def Su.tx_put(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Su.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Su.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  SUnique.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss, e)

def Su.tx_rephase(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Su.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Su.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  e

def Su.tx_del(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Su.inv(st0, ues, ss) == True{} : Bool}) -> {Su.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  SUnique.sift(S.SOthers{key}, ss, e)

def Su.tx_put_session(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Su.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Su.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Sessions.clear(key, s, S.Sessions.sift(S.SClear{key, s}, ss)), S.Sessions.unique(S.Sessions.sift(S.SClear{key, s}, ss)), SClear.own(key, s, ss), SUnique.sift(S.SClear{key, s}, ss, e))

def Su.tx_revar(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Su.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.revar_ok(st0, v) == True{} : Bool}) -> {Su.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  SUnique.revar(key, v, ss, e)

def Su.tx_del_session(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Su.inv(st0, ues, ss) == True{} : Bool}) -> {Su.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  SUnique.sift(S.SExcept{key}, ss, e)

def Down.sunique(+st: S.State, +assoc: U32, +e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(K.Kernel.state(R.Route.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s0 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      +tx = N.Out.tx(Up.N4.deletions(S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions), pfcp_seq))
      SUnique.sift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, S.State.sessions(S.Tx.apply(tx, s0)), PL.Inv.tx(~Su.inv, ~PL.Inv.none, ~Su.tx_put, ~Su.tx_rephase, ~Su.tx_del, ~Su.tx_put_session, ~Su.tx_revar, ~Su.tx_del_session, s0, {==}, tx, s0, e, PL.Lv.drop_homed(s0, assoc)))

def L.smf.ip_pool.unique(st, ev, entropy, e):
  ({==}, PL.Inv.step(ues => ss => S.Sessions.unique(ss), st, ev, entropy, e, tx => st2 => e2 => h => PL.Inv.tx(~Su.inv, ~PL.Inv.none, ~Su.tx_put, ~Su.tx_rephase, ~Su.tx_del, ~Su.tx_put_session, ~Su.tx_revar, ~Su.tx_del_session, st, {==}, tx, st2, e2, h), tx => st2 => e2 => h => PL.Inv.tx(~Su.inv, ~PL.Inv.none, ~Su.tx_put, ~Su.tx_rephase, ~Su.tx_del, ~Su.tx_put_session, ~Su.tx_revar, ~Su.tx_del_session, st, {==}, tx, st2, e2, h), a => s => e1 => Down.sunique(s, a, e1), a => s => e1 => Down.sunique(s, a, e1)))

# Rows of a unique table
# ----------------------

def Teid.of_row(+key: U32, +s: S.Session, +k: U32, +t: S.Session, +nc: {S.SRow.conflicts(key, s, k, t) == False{} : Bool}) -> {U32.is_eq(S.Session.teid(s), S.Session.teid(t)) == False{} : Bool}:
  e2 = P.Bool.or_false_r(U32.is_eq(k, key), S.Session.conflicts(s, t), nc)
  e3 = P.Bool.or_false_r(U32.is_eq(S.Session.ip(s), S.Session.ip(t)), Bool.or(U32.is_eq(S.Session.teid(s), S.Session.teid(t)), Bool.and(S.Maybe.same_u32(S.Session.tag(s), S.Session.tag(t)), U32.is_eq(S.Session.psi(s), S.Session.psi(t)))), e2)
  P.Bool.or_false_l(U32.is_eq(S.Session.teid(s), S.Session.teid(t)), Bool.and(S.Maybe.same_u32(S.Session.tag(s), S.Session.tag(t)), U32.is_eq(S.Session.psi(s), S.Session.psi(t))), e3)

def SUniq.clear_row(+key0: U32, +w: S.Session, +k: U32, +u: S.Session, +k1: U32, +x: S.Session, +more: Tb.Table(S.Session), +hk: Bool, +ehk: {U32.is_eq(k1, k) == hk : Bool}, +ec: {Bool.and(Bool.not(S.SRow.conflicts(key0, w, k1, x)), S.Sessions.clear(key0, w, more)) == True{} : Bool}, +eu: {Tb.Table.hit(S.Session, x, Tb.Table.get(S.Session, k, more), hk) == Some{u} : Maybe<&2, S.Session>}, ih: {S.Sessions.clear(key0, w, more) == True{} : Bool} -> {Tb.Table.get(S.Session, k, more) == Some{u} : Maybe<&2, S.Session>} -> {S.SRow.conflicts(key0, w, k, u) == False{} : Bool}) -> {S.SRow.conflicts(key0, w, k, u) == False{} : Bool}:
  match hk:
    case True{}:
      r = P.Bool.not_true(S.SRow.conflicts(key0, w, k1, x), P.Bool.and_true_l(Bool.not(S.SRow.conflicts(key0, w, k1, x)), S.Sessions.clear(key0, w, more), ec))
      ek = P.U32.eq_of_is_eq(k1, k, ehk)
      %ek : {S.SRow.conflicts(key0, w, _, u) == False{} : Bool}
      ex = P.Some.inj(S.Session, x, u, eu)
      %ex : {S.SRow.conflicts(key0, w, k1, _) == False{} : Bool}
      r
    case False{}:
      ih(P.Bool.and_true_r(Bool.not(S.SRow.conflicts(key0, w, k1, x)), S.Sessions.clear(key0, w, more), ec), eu)

# A session clear of a table conflicts with none of its rows.
def SUniq.clear_get(+key0: U32, +w: S.Session, +t: Tb.Table(S.Session), +k: U32, +u: S.Session, +ec: {S.Sessions.clear(key0, w, t) == True{} : Bool}, +eu: {Tb.Table.get(S.Session, k, t) == Some{u} : Maybe<&2, S.Session>}) -> {S.SRow.conflicts(key0, w, k, u) == False{} : Bool}:
  match t:
    case Nil{}:
      Empty.absurd({S.SRow.conflicts(key0, w, k, u) == False{} : Bool}, P.Refute.none_some(S.Session, u, eu))
    case (+k1, +x) <> +more:
      SUniq.clear_row(key0, w, k, u, k1, x, more, U32.is_eq(k1, k), {==}, ec, eu, e1 => e2 => SUniq.clear_get(key0, w, more, k, u, e1, e2))

def SUniq.row(+key: U32, +k: U32, +v: S.Session, +u: S.Session, +k0: U32, +w: S.Session, +more: Tb.Table(S.Session), +a: Bool, +ea: {U32.is_eq(k0, key) == a : Bool}, +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +eun: {Bool.and(S.Sessions.clear(k0, w, more), S.Sessions.unique(more)) == True{} : Bool}, +ev: {Tb.Table.hit(S.Session, w, Tb.Table.get(S.Session, key, more), a) == Some{v} : Maybe<&2, S.Session>}, +eu: {Tb.Table.hit(S.Session, w, Tb.Table.get(S.Session, k, more), b) == Some{u} : Maybe<&2, S.Session>}, +ne: {U32.is_eq(k, key) == False{} : Bool}, ih: {S.Sessions.unique(more) == True{} : Bool} -> {Tb.Table.get(S.Session, key, more) == Some{v} : Maybe<&2, S.Session>} -> {Tb.Table.get(S.Session, k, more) == Some{u} : Maybe<&2, S.Session>} -> {U32.is_eq(S.Session.teid(v), S.Session.teid(u)) == False{} : Bool}) -> {U32.is_eq(S.Session.teid(v), S.Session.teid(u)) == False{} : Bool}:
  match a b:
    case True{} True{}:
      kk = Equal.trans(U32, k, k0, key, Equal.sym(U32, k0, k, P.U32.eq_of_is_eq(k0, k, eb)), P.U32.eq_of_is_eq(k0, key, ea))
      Empty.absurd({U32.is_eq(S.Session.teid(v), S.Session.teid(u)) == False{} : Bool}, P.Refute.bool(Equal.trans(Bool, False{}, U32.is_eq(k, key), True{}, Equal.sym(Bool, U32.is_eq(k, key), False{}, ne), P.U32.eq_true(k, key, kk))))
    case True{} False{}:
      ec = P.Bool.and_true_l(S.Sessions.clear(k0, w, more), S.Sessions.unique(more), eun)
      r = Teid.of_row(k0, w, k, u, SUniq.clear_get(k0, w, more, k, u, ec, eu))
      ew = P.Some.inj(S.Session, w, v, ev)
      %ew : {U32.is_eq(S.Session.teid(_), S.Session.teid(u)) == False{} : Bool}
      r
    case False{} True{}:
      ec = P.Bool.and_true_l(S.Sessions.clear(k0, w, more), S.Sessions.unique(more), eun)
      r = Teid.of_row(k0, w, key, v, SUniq.clear_get(k0, w, more, key, v, ec, ev))
      ew = P.Some.inj(S.Session, w, u, eu)
      %ew : {U32.is_eq(S.Session.teid(v), S.Session.teid(_)) == False{} : Bool}
      Equal.trans(Bool, U32.is_eq(S.Session.teid(v), S.Session.teid(w)), U32.is_eq(S.Session.teid(w), S.Session.teid(v)), False{}, P.U32.sym(S.Session.teid(v), S.Session.teid(w)), r)
    case False{} False{}:
      ih(P.Bool.and_true_r(S.Sessions.clear(k0, w, more), S.Sessions.unique(more), eun), ev, eu)

# Two sessions of a unique table under different keys never share a TEID.
def SUniq.apart(+ss: Tb.Table(S.Session), +key: U32, +k: U32, +v: S.Session, +u: S.Session, +eun: {S.Sessions.unique(ss) == True{} : Bool}, +ev: {Tb.Table.get(S.Session, key, ss) == Some{v} : Maybe<&2, S.Session>}, +eu: {Tb.Table.get(S.Session, k, ss) == Some{u} : Maybe<&2, S.Session>}, +ne: {U32.is_eq(k, key) == False{} : Bool}) -> {U32.is_eq(S.Session.teid(v), S.Session.teid(u)) == False{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({U32.is_eq(S.Session.teid(v), S.Session.teid(u)) == False{} : Bool}, P.Refute.none_some(S.Session, u, eu))
    case (+k0, +w) <> +more:
      SUniq.row(key, k, v, u, k0, w, more, U32.is_eq(k0, key), {==}, U32.is_eq(k0, k), {==}, eun, ev, eu, ne, e1 => e2 => e3 => SUniq.apart(more, key, k, v, u, e1, e2, e3, ne))

def L.smf.teid.unique(ss, k1, s1, k2, s2, e, e1, e2, ne):
  SUniq.apart(ss, k1, k2, s1, s2, e, e1, e2, Equal.trans(Bool, U32.is_eq(k2, k1), U32.is_eq(k1, k2), False{}, P.U32.sym(k2, k1), ne))

# Packet filters and the ePCO
# ---------------------------

# Every Accept a session holds while being created keeps the bound: the one
# session put (Lw.create) holds the default rule, and no change of a session
# makes it creating again.

def Bd.sift(+v: S.SSieve, ss: Tb.Table(S.Session), +e: {Gsm.Gsm.bounded(ss) == True{} : Bool}) -> {Gsm.Gsm.bounded(S.Sessions.sift(v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {Gsm.Gsm.bounded(tb) == True{} : Bool}, k, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k, t), e1 => h => P.Bool.and_intro(Gsm.Gsm.phase_bounded(S.Session.phase(t)), Gsm.Gsm.bounded(S.Sessions.sift(v, more)), P.Bool.and_true_l(Gsm.Gsm.phase_bounded(S.Session.phase(t)), Gsm.Gsm.bounded(more), e), h), Bd.sift(v, more, P.Bool.and_true_r(Gsm.Gsm.phase_bounded(S.Session.phase(t)), Gsm.Gsm.bounded(more), e)))

def Bd.revar_if(hit: Bool, +t: S.Session, +v: S.SVar, +ht: {Gsm.Gsm.phase_bounded(S.Session.phase(t)) == True{} : Bool}, +hv: {Gsm.Gsm.phase_bounded(S.SVar.phase(v)) == True{} : Bool}) -> {Gsm.Gsm.phase_bounded(S.Session.phase(S.Session.revar_if(t, v, hit))) == True{} : Bool}:
  match hit:
    case True{}:
      match t:
        case S.Session{id, var}:
          hv
    case False{}:
      ht

def Bd.revar(+key: U32, +v: S.SVar, ss: Tb.Table(S.Session), +e: {Gsm.Gsm.bounded(ss) == True{} : Bool}, +hv: {Gsm.Gsm.phase_bounded(S.SVar.phase(v)) == True{} : Bool}) -> {Gsm.Gsm.bounded(S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Bool.and_intro(Gsm.Gsm.phase_bounded(S.Session.phase(S.Session.revar_if(t, v, Bool.and(U32.is_eq(k, key), S.SVar.follows(v, t))))), Gsm.Gsm.bounded(S.Sessions.revar(key, v, more)), Bd.revar_if(Bool.and(U32.is_eq(k, key), S.SVar.follows(v, t)), t, v, P.Bool.and_true_l(Gsm.Gsm.phase_bounded(S.Session.phase(t)), Gsm.Gsm.bounded(more), e), hv), Bd.revar(key, v, more, P.Bool.and_true_r(Gsm.Gsm.phase_bounded(S.Session.phase(t)), Gsm.Gsm.bounded(more), e), hv))

def Bd.pre(+st0: S.State) -> Bool:
  Gsm.Gsm.bounded(S.State.sessions(st0))

def Bd.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  Gsm.Gsm.bounded(ss)

def Bd.tx_put(+st0: S.State, +ep: {Bd.pre(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Bd.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Bd.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  Bd.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss, e)

def Bd.tx_rephase(+st0: S.State, +ep: {Bd.pre(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Bd.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Bd.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  e

def Bd.tx_del(+st0: S.State, +ep: {Bd.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Bd.inv(st0, ues, ss) == True{} : Bool}) -> {Bd.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Bd.sift(S.SOthers{key}, ss, e)

def Bd.tx_put_session(+st0: S.State, +ep: {Bd.pre(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Bd.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Bd.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  P.Bool.and_intro(Gsm.Gsm.phase_bounded(S.Session.phase(s)), Gsm.Gsm.bounded(S.Sessions.sift(S.SClear{key, s}, ss)), P.Bool.and_true_l(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s)), P.Bool.and_true_r(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s))), P.Bool.and_true_r(S.Ids.seid(key), Bool.and(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), S.SPhase.knows(S.Session.phase(s), S.Session.known(s)))), h))), Bd.sift(S.SClear{key, s}, ss, e))

def Bd.tx_revar(+st0: S.State, +ep: {Bd.pre(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Bd.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.revar_ok(st0, v) == True{} : Bool}) -> {Bd.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  +y = Bool.not(Gsm.Gsm.bounded(S.State.sessions(st0)))
  sb = Equal.sym(Bool, Gsm.Gsm.bounded(S.State.sessions(st0)), True{}, ep)
  Bd.revar(key, v, ss, e, P.Bool.or_true_l(Gsm.Gsm.phase_bounded(S.SVar.phase(v)), y, (%sb : {Bool.not(_) == False{} : Bool}; {==}), P.Bool.and_true_l(Bool.or(Gsm.Gsm.phase_bounded(S.SVar.phase(v)), y), Bool.or(PL.Lv.var_ok(v), Bool.not(S.Sessions.known(S.State.sessions(st0)))), h)))

def Bd.tx_del_session(+st0: S.State, +ep: {Bd.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Bd.inv(st0, ues, ss) == True{} : Bool}) -> {Bd.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  Bd.sift(S.SExcept{key}, ss, e)

def Bd.down(+st: S.State, +assoc: U32, +e: {Gsm.Gsm.bounded(S.State.sessions(st)) == True{} : Bool}) -> {Gsm.Gsm.bounded(S.State.sessions(K.Kernel.state(R.Route.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s0 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      +tx = N.Out.tx(Up.N4.deletions(S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions), pfcp_seq))
      Bd.sift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, S.State.sessions(S.Tx.apply(tx, s0)), PL.Inv.tx(~Bd.inv, ~Bd.pre, ~Bd.tx_put, ~Bd.tx_rephase, ~Bd.tx_del, ~Bd.tx_put_session, ~Bd.tx_revar, ~Bd.tx_del_session, s0, e, tx, s0, e, PL.Lv.drop_homed(s0, assoc)))

def L.smf.packet_filters.capacity_reject(st, ev, entropy, e):
  ({==}, PL.Inv.step(ues => ss => Gsm.Gsm.bounded(ss), st, ev, entropy, e, tx => st2 => e2 => h => PL.Inv.tx(~Bd.inv, ~Bd.pre, ~Bd.tx_put, ~Bd.tx_rephase, ~Bd.tx_del, ~Bd.tx_put_session, ~Bd.tx_revar, ~Bd.tx_del_session, st, e, tx, st2, e2, h), tx => st2 => e2 => h => PL.Inv.tx(~Bd.inv, ~Bd.pre, ~Bd.tx_put, ~Bd.tx_rephase, ~Bd.tx_del, ~Bd.tx_put_session, ~Bd.tx_revar, ~Bd.tx_del_session, st, e, tx, st2, e2, h), a => s => e1 => Bd.down(s, a, e1), a => s => e1 => Bd.down(s, a, e1)))

def L.smf.epco.response_bounded(cfg, wanted):
  match wanted:
    case True{}:
      {==}
    case False{}:
      {==}

# A DNS server of four octets makes a valid container.
def Epco.dns(dns: B.Bytes(), e: {F.Len.is(dns, 4n) == True{} : Bool}) -> {Q.Epco.valid(Q.Epco{[Q.Container{13, I.LenBody{U32.from_nat(List.length(&2, U32, dns)), dns}}]}) == True{} : Bool}:
  match dns:
    case Nil{}:
      Empty.absurd({Q.Epco.valid(Q.Epco{[Q.Container{13, I.LenBody{0, []}}]}) == True{} : Bool}, P.Refute.bool(e))
    case a <> Nil{}:
      Empty.absurd({Q.Epco.valid(Q.Epco{[Q.Container{13, I.LenBody{1, [a]}}]}) == True{} : Bool}, P.Refute.bool(e))
    case a <> b <> Nil{}:
      Empty.absurd({Q.Epco.valid(Q.Epco{[Q.Container{13, I.LenBody{2, [a, b]}}]}) == True{} : Bool}, P.Refute.bool(e))
    case a <> b <> c <> Nil{}:
      Empty.absurd({Q.Epco.valid(Q.Epco{[Q.Container{13, I.LenBody{3, [a, b, c]}}]}) == True{} : Bool}, P.Refute.bool(e))
    case a <> b <> c <> d <> Nil{}:
      {==}
    case a <> b <> c <> d <> x <> t:
      Empty.absurd({Q.Epco.valid(Q.Epco{[Q.Container{13, I.LenBody{U32.from_nat(List.length(&2, U32, a <> b <> c <> d <> x <> t)), a <> b <> c <> d <> x <> t}}]}) == True{} : Bool}, P.Refute.bool(e))

def L.smf.epco.accept_valid(cfg, wanted, e):
  match wanted:
    case True{}:
      +ok = F.Result.ok(B.ReadValue(Pl.Plmn), Pl.Plmn.read(S.Cfg.plmn(cfg)))
      +rest = Bool.and(F.Len.is(S.Cfg.dns(cfg), 4n), S.Cfg.fits(cfg))
      Epco.dns(S.Cfg.dns(cfg), P.Bool.and_true_l(F.Len.is(S.Cfg.dns(cfg), 4n), S.Cfg.fits(cfg), P.Bool.and_true_r(ok, rest, P.Bool.and_true_r(F.Len.is(S.Cfg.plmn(cfg), 3n), Bool.and(ok, rest), e))))
    case False{}:
      {==}

# The UPF knows the sessions past Creating
# -------------------------------------

def Kw.sift(+v: S.SSieve, ss: Tb.Table(S.Session), +e: {S.Sessions.known(ss) == True{} : Bool}) -> {S.Sessions.known(S.Sessions.sift(v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +x = S.SPhase.knows(S.Session.phase(t), S.Session.known(t))
      P.Keep.by(S.Session, tb => {S.Sessions.known(tb) == True{} : Bool}, k, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k, t), e1 => h => P.Bool.and_intro(S.SPhase.knows(S.Session.phase(t), S.Session.known(t)), S.Sessions.known(S.Sessions.sift(v, more)), P.Bool.and_true_l(x, S.Sessions.known(more), e), h), Kw.sift(v, more, P.Bool.and_true_r(x, S.Sessions.known(more), e)))

def Kw.revar_if(hit: Bool, +t: S.Session, +v: S.SVar, +ht: {S.SPhase.knows(S.Session.phase(t), S.Session.known(t)) == True{} : Bool}, +hv: {PL.Lv.var_ok(v) == True{} : Bool}) -> {S.SPhase.knows(S.Session.phase(S.Session.revar_if(t, v, hit)), S.Session.known(S.Session.revar_if(t, v, hit))) == True{} : Bool}:
  match hit:
    case True{}:
      match t:
        case S.Session{id, var}:
          hv
    case False{}:
      ht

def Kw.revar(+key: U32, +v: S.SVar, ss: Tb.Table(S.Session), +e: {S.Sessions.known(ss) == True{} : Bool}, +hv: {PL.Lv.var_ok(v) == True{} : Bool}) -> {S.Sessions.known(S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +x = S.SPhase.knows(S.Session.phase(t), S.Session.known(t))
      +t2 = S.Session.revar_if(t, v, Bool.and(U32.is_eq(k, key), S.SVar.follows(v, t)))
      P.Bool.and_intro(S.SPhase.knows(S.Session.phase(t2), S.Session.known(t2)), S.Sessions.known(S.Sessions.revar(key, v, more)), Kw.revar_if(Bool.and(U32.is_eq(k, key), S.SVar.follows(v, t)), t, v, P.Bool.and_true_l(x, S.Sessions.known(more), e), hv), Kw.revar(key, v, more, P.Bool.and_true_r(x, S.Sessions.known(more), e), hv))

# The step starts from sessions the UPF knows, so every change agrees with it.
def Kw.pre(+st0: S.State) -> Bool:
  S.Sessions.known(S.State.sessions(st0))

def Kw.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  S.Sessions.known(ss)

def Kw.tx_put(+st0: S.State, +ep: {Kw.pre(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Kw.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Kw.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  Kw.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss, e)

def Kw.tx_rephase(+st0: S.State, +ep: {Kw.pre(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Kw.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Kw.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  e

def Kw.tx_del(+st0: S.State, +ep: {Kw.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Kw.inv(st0, ues, ss) == True{} : Bool}) -> {Kw.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Kw.sift(S.SOthers{key}, ss, e)

def Kw.tx_put_session(+st0: S.State, +ep: {Kw.pre(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Kw.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Kw.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  +x = S.SPhase.knows(S.Session.phase(s), S.Session.known(s))
  P.Bool.and_intro(x, S.Sessions.known(S.Sessions.sift(S.SClear{key, s}, ss)), P.Bool.and_true_r(Gsm.Gsm.phase_bounded(S.Session.phase(s)), x, P.Bool.and_true_r(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), x), P.Bool.and_true_r(S.Ids.seid(key), Bool.and(Tb.Table.has(S.Ue, S.Session.ue(s), ues), Bool.and(Gsm.Gsm.phase_bounded(S.Session.phase(s)), x)), h))), Kw.sift(S.SClear{key, s}, ss, e))

def Kw.tx_revar(+st0: S.State, +ep: {Kw.pre(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Kw.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.revar_ok(st0, v) == True{} : Bool}) -> {Kw.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  +y = Bool.not(S.Sessions.known(S.State.sessions(st0)))
  sk = Equal.sym(Bool, S.Sessions.known(S.State.sessions(st0)), True{}, ep)
  Kw.revar(key, v, ss, e, P.Bool.or_true_l(PL.Lv.var_ok(v), y, (%sk : {Bool.not(_) == False{} : Bool}; {==}), P.Bool.and_true_r(Bool.or(Gsm.Gsm.phase_bounded(S.SVar.phase(v)), Bool.not(Gsm.Gsm.bounded(S.State.sessions(st0)))), Bool.or(PL.Lv.var_ok(v), y), h)))

def Kw.tx_del_session(+st0: S.State, +ep: {Kw.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Kw.inv(st0, ues, ss) == True{} : Bool}) -> {Kw.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  Kw.sift(S.SExcept{key}, ss, e)

def Kw.down(+st: S.State, +assoc: U32, +e: {S.Sessions.known(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.known(S.State.sessions(K.Kernel.state(R.Route.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s0 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      +tx = N.Out.tx(Up.N4.deletions(S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions), pfcp_seq))
      Kw.sift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, S.State.sessions(S.Tx.apply(tx, s0)), PL.Inv.tx(~Kw.inv, ~Kw.pre, ~Kw.tx_put, ~Kw.tx_rephase, ~Kw.tx_del, ~Kw.tx_put_session, ~Kw.tx_revar, ~Kw.tx_del_session, s0, e, tx, s0, e, PL.Lv.drop_homed(s0, assoc)))

def L.smf.sessions.known(st, ev, entropy, e):
  ({==}, PL.Inv.step(ues => ss => S.Sessions.known(ss), st, ev, entropy, e, tx => st2 => e2 => h => PL.Inv.tx(~Kw.inv, ~Kw.pre, ~Kw.tx_put, ~Kw.tx_rephase, ~Kw.tx_del, ~Kw.tx_put_session, ~Kw.tx_revar, ~Kw.tx_del_session, st, e, tx, st2, e2, h), tx => st2 => e2 => h => PL.Inv.tx(~Kw.inv, ~Kw.pre, ~Kw.tx_put, ~Kw.tx_rephase, ~Kw.tx_del, ~Kw.tx_put_session, ~Kw.tx_revar, ~Kw.tx_del_session, st, e, tx, st2, e2, h), a => s => e1 => Kw.down(s, a, e1), a => s => e1 => Kw.down(s, a, e1)))

# A failed establishment releases the session
# --------------------------------------------
# An outcome releases a session when its transaction, applied to any state,
# leaves no row under the session's key that belongs to a UE
# (S.Sessions.each with S.SFresh: being deleted under a guard not fired yet), and none at all when the UPF does not know the
# session, and its actions delete the session at the UPF whenever the UPF
# knows it. A failure's outcome joins the release of the session with steps
# that put no session.

def Rel.Spec(+o: N.GOut(), +skey: U32, +s: S.Session) -> Type:
  (@st2: S.State -> {S.Sessions.each(skey, S.SFresh{}, S.State.sessions(S.Tx.apply(N.Out.tx(o), st2))) == True{} : Bool}) & (({S.Session.known(s) == False{} : Bool} -> @st2: S.State -> {Tb.Table.get(S.Session, skey, S.State.sessions(S.Tx.apply(N.Out.tx(o), st2))) == None{} : Maybe<&2, S.Session>}) & ({S.Session.known(s) == True{} : Bool} -> {S.SPhase.live(S.Session.phase(s)) == True{} : Bool} -> Up.N4.deleted(skey, s, N.Out.acts(o))))

def Rel.Law(+r: N.Step(), +skey: U32, +s: S.Session) -> Type:
  {S.Sessions.each(skey, S.SFresh{}, S.State.sessions(K.Kernel.state(r))) == True{} : Bool} & (({S.Session.known(s) == False{} : Bool} -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(r))) == None{} : Maybe<&2, S.Session>}) & ({S.Session.known(s) == True{} : Bool} -> {S.SPhase.live(S.Session.phase(s)) == True{} : Bool} -> Up.N4.deleted(skey, s, K.Kernel.actions(r))))

def Del.app_r.eq(+xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +pre: List<&2, N.Act>, +a: N.Act, +post: List<&2, N.Act>, e: {ys == List.append(&2, N.Act, pre, a <> post) : List<&2, N.Act>}) -> {List.append(&2, N.Act, xs, ys) == List.append(&2, N.Act, List.append(&2, N.Act, xs, pre), a <> post) : List<&2, N.Act>}:
  se = Equal.sym(List<&2, N.Act>, ys, List.append(&2, N.Act, pre, a <> post), e)
  %se : {List.append(&2, N.Act, xs, _) == List.append(&2, N.Act, List.append(&2, N.Act, xs, pre), a <> post) : List<&2, N.Act>}
  PL.Lv.app_assoc(xs, pre, a <> post)

def Del.app_l.eq(+xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +pre: List<&2, N.Act>, +a: N.Act, +post: List<&2, N.Act>, e: {xs == List.append(&2, N.Act, pre, a <> post) : List<&2, N.Act>}) -> {List.append(&2, N.Act, xs, ys) == List.append(&2, N.Act, pre, a <> List.append(&2, N.Act, post, ys)) : List<&2, N.Act>}:
  se = Equal.sym(List<&2, N.Act>, xs, List.append(&2, N.Act, pre, a <> post), e)
  %se : {List.append(&2, N.Act, _, ys) == List.append(&2, N.Act, pre, a <> List.append(&2, N.Act, post, ys)) : List<&2, N.Act>}
  Equal.sym(List<&2, N.Act>, List.append(&2, N.Act, pre, List.append(&2, N.Act, a <> post, ys)), List.append(&2, N.Act, List.append(&2, N.Act, pre, a <> post), ys), PL.Lv.app_assoc(pre, a <> post, ys))

def Del.app_r(+key: U32, +s: S.Session, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, d: Up.N4.deleted(key, s, ys)) -> Up.N4.deleted(key, s, List.append(&2, N.Act, xs, ys)):
  (+seq, (+pre, (+post, e))) = d
  (seq, (List.append(&2, N.Act, xs, pre), (post, Del.app_r.eq(xs, ys, pre, N.Pfcp{Some{S.Session.ue(s)}, Up.N4.delete(S.Session.up_seid(s), seq)}, N.TimerStart{None{}, key, Up.N4.t1_ms()} <> post, e))))

def Del.app_l(+key: U32, +s: S.Session, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, d: Up.N4.deleted(key, s, xs)) -> Up.N4.deleted(key, s, List.append(&2, N.Act, xs, ys)):
  (+seq, (+pre, (+post, e))) = d
  (seq, (pre, (List.append(&2, N.Act, post, ys), Del.app_l.eq(xs, ys, pre, N.Pfcp{Some{S.Session.ue(s)}, Up.N4.delete(S.Session.up_seid(s), seq)}, N.TimerStart{None{}, key, Up.N4.t1_ms()} <> post, e))))

def Rel.step(+st: S.State, +o: N.GOut(), +skey: U32, +s: S.Session, h: Rel.Spec(o, skey, s)) -> Rel.Law(N.Step.of(st, o), skey, s):
  match o:
    case (+tx, +acts):
      (g, (n, d)) = h
      (g(st), (kf => n(kf, st), k => eh => Del.app_l(skey, s, acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))), d(k, eh))))

def Rel.by(+r: N.Step(), +st: S.State, +o: N.GOut(), +skey: U32, +s: S.Session, eq: {r == N.Step.of(st, o) : N.Step()}, h: Rel.Spec(o, skey, s)) -> Rel.Law(r, skey, s):
  se = Equal.sym(N.Step(), r, N.Step.of(st, o), eq)
  %se : Rel.Law(_, skey, s)
  Rel.step(st, o, skey, s, h)

# The deletion among the actions
# ------------------------------

# The Session Deletion of a session the UPF knows, tagged with its UE.
def Del.one(+skey: U32, +s: S.Session, +seq: U32, k: {S.Session.known(s) == True{} : Bool}, eh: {S.SPhase.live(S.Session.phase(s)) == True{} : Bool}) -> Up.N4.deleted(skey, s, N.Out.acts(Up.N4.deletions([(skey, s)], seq))):
  sk = Equal.sym(Bool, S.Session.known(s), True{}, k)
  %sk : Up.N4.deleted(skey, s, N.Out.acts(Up.N4.delete_if(skey, s, seq, q => Up.N4.deletions([], q), _)))
  +request = Up.N4.delete(S.Session.up_seid(s), seq)
  +y : N.Act = N.TimerStart{None{}, skey, Up.N4.t1_ms()}
  seh = Equal.sym(Bool, S.SPhase.live(S.Session.phase(s)), True{}, eh)
  (seq, ([], ([], (%seh : {[N.Pfcp{Tb.Table.hit(U32, S.Session.ue(s), None{}, _), request}, y] == List.append(&2, N.Act, [], N.Pfcp{Some{S.Session.ue(s)}, request} <> y <> []) : List<&2, N.Act>}; {==}))))

# No session put
# --------------
# A transaction that puts no session leaves a key that holds no row without one.

def None.hit(+t: S.Session, +m: Maybe<&2, S.Session>, b: Bool, +hb: {b == False{} : Bool}, +hm: {m == None{} : Maybe<&2, S.Session>}) -> {Tb.Table.hit(S.Session, t, m, b) == None{} : Maybe<&2, S.Session>}:
  match b:
    case True{}:
      Empty.absurd({Some{t} == None{} : Maybe<&2, S.Session>}, P.Refute.true_false(hb))
    case False{}:
      hm

def None.row(+k: U32, +k0: U32, +t: S.Session, +more: Tb.Table(S.Session), b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +h: {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), b) == None{} : Maybe<&2, S.Session>}, -G: Type, kont: {U32.is_eq(k0, k) == False{} : Bool} -> {Tb.Table.get(S.Session, k, more) == None{} : Maybe<&2, S.Session>} -> G) -> G:
  match b:
    case True{}:
      Empty.absurd(G, P.Refute.none_some(S.Session, t, Equal.sym(Maybe<&2, S.Session>, Some{t}, None{}, h)))
    case False{}:
      kont(eb, h)

def None.sift(+v: S.SSieve, ss: Tb.Table(S.Session), +k: U32, +h: {Tb.Table.get(S.Session, k, ss) == None{} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, k, S.Sessions.sift(v, ss)) == None{} : Maybe<&2, S.Session>}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      None.row(k, k0, t, more, U32.is_eq(k0, k), {==}, h, {Tb.Table.get(S.Session, k, S.Sessions.sift(v, (k0, t) <> more)) == None{} : Maybe<&2, S.Session>}, h0 => hr => P.Keep.by(S.Session, tb => {Tb.Table.get(S.Session, k, tb) == None{} : Maybe<&2, S.Session>}, k0, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k0, t), e => h => None.hit(t, Tb.Table.get(S.Session, k, S.Sessions.sift(v, more)), U32.is_eq(k0, k), h0, h), None.sift(v, more, k, hr)))

def None.revar(+key: U32, +v: S.SVar, ss: Tb.Table(S.Session), +k: U32, +h: {Tb.Table.get(S.Session, k, ss) == None{} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, k, S.Sessions.revar(key, v, ss)) == None{} : Maybe<&2, S.Session>}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      None.row(k, k0, t, more, U32.is_eq(k0, k), {==}, h, {Tb.Table.get(S.Session, k, S.Sessions.revar(key, v, (k0, t) <> more)) == None{} : Maybe<&2, S.Session>}, h0 => hr => None.hit(S.Session.revar_if(t, v, Bool.and(U32.is_eq(k0, key), S.SVar.follows(v, t))), Tb.Table.get(S.Session, k, S.Sessions.revar(key, v, more)), U32.is_eq(k0, k), h0, None.revar(key, v, more, k, hr)))

def None.free(+st0: S.State, tx: S.Tx, +st2: S.State, +k: U32, +h: {Tb.Table.get(S.Session, k, S.State.sessions(st2)) == None{} : Maybe<&2, S.Session>}, +f: {PL.Lv.free(st0, tx) == True{} : Bool}) -> {Tb.Table.get(S.Session, k, S.State.sessions(S.Tx.apply(tx, st2))) == None{} : Maybe<&2, S.Session>}:
  match tx:
    case S.Keep{}:
      h
    case S.Put{+key, +ue}:
      match st2:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
          None.sift(S.SOwned{S.Ues.put(key, ue, ues)}, sessions, k, h)
    case S.Del{+key}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          None.sift(S.SOthers{key}, sessions, k, h)
    case S.PutSession{key, s}:
      Empty.absurd({Tb.Table.get(S.Session, k, S.State.sessions(S.Tx.apply(S.PutSession{key, s}, st2))) == None{} : Maybe<&2, S.Session>}, P.Refute.bool(f))
    case S.Revar{+key, +v}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          None.revar(key, v, sessions, k, h)
    case S.DelSession{+key}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          None.sift(S.SExcept{key}, sessions, k, h)
    case S.Rephase{key, phase}:
      match st2:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.Subs{new}:
      match st2:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.SetLink{link}:
      match st2:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.BumpUe{bk}:
      match st2:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.BumpSeq{n}:
      match st2:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.Both{+a, +b}:
      None.free(st0, b, S.Tx.apply(a, st2), k, None.free(st0, a, st2, k, h, P.Bool.and_true_l(PL.Lv.free(st0, a), PL.Lv.free(st0, b), f)), P.Bool.and_true_r(PL.Lv.free(st0, a), PL.Lv.free(st0, b), f))

# Keys being deleted
# ------------------
# Every row of a key being deleted under a guard not fired yet: whatever puts
# no session and changes a row only to that keeps it so, deleting a session at
# the UPF leaves its row so, and forgetting it leaves none.

def Dl.sift(+v: S.SSieve, ss: Tb.Table(S.Session), +key: U32, +e: {S.Sessions.each(key, S.SFresh{}, ss) == True{} : Bool}) -> {S.Sessions.each(key, S.SFresh{}, S.Sessions.sift(v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +x = Bool.or(Bool.not(U32.is_eq(k, key)), S.SPhase.fresh(S.Session.phase(t)))
      P.Keep.by(S.Session, tb => {S.Sessions.each(key, S.SFresh{}, tb) == True{} : Bool}, k, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k, t), e1 => h => P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k, key)), S.SPhase.fresh(S.Session.phase(t))), S.Sessions.each(key, S.SFresh{}, S.Sessions.sift(v, more)), P.Bool.and_true_l(x, S.Sessions.each(key, S.SFresh{}, more), e), h), Dl.sift(v, more, key, P.Bool.and_true_r(x, S.Sessions.each(key, S.SFresh{}, more), e)))

def Dl.fresh_if(+t: S.Session, +v: S.SVar, +b: Bool, +ht: {S.SPhase.fresh(S.Session.phase(t)) == True{} : Bool}, +hv: {S.SPhase.fresh(S.SVar.phase(v)) == True{} : Bool}) -> {S.SPhase.fresh(S.Session.phase(S.Session.revar_if(t, v, b))) == True{} : Bool}:
  match t:
    case S.Session{id, var}:
      match b:
        case True{}:
          hv
        case False{}:
          ht

def Dl.revar(+key2: U32, +v: S.SVar, ss: Tb.Table(S.Session), +key: U32, +e: {S.Sessions.each(key, S.SFresh{}, ss) == True{} : Bool}, +hv: {S.SPhase.fresh(S.SVar.phase(v)) == True{} : Bool}) -> {S.Sessions.each(key, S.SFresh{}, S.Sessions.revar(key2, v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +hit = Bool.and(U32.is_eq(k, key2), S.SVar.follows(v, t))
      +x = Bool.or(Bool.not(U32.is_eq(k, key)), S.SPhase.fresh(S.Session.phase(t)))
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k, key)), S.SPhase.fresh(S.Session.phase(S.Session.revar_if(t, v, hit)))), S.Sessions.each(key, S.SFresh{}, S.Sessions.revar(key2, v, more)), P.Bool.or_mono(Bool.not(U32.is_eq(k, key)), S.SPhase.fresh(S.Session.phase(t)), S.SPhase.fresh(S.Session.phase(S.Session.revar_if(t, v, hit))), P.Bool.and_true_l(x, S.Sessions.each(key, S.SFresh{}, more), e), ef => Dl.fresh_if(t, v, hit, ef, hv)), Dl.revar(key2, v, more, key, P.Bool.and_true_r(x, S.Sessions.each(key, S.SFresh{}, more), e), hv))

# A transaction that puts no session and changes a row only to being deleted
# under a guard not fired yet.
def Dl.quiet(tx: S.Tx) -> Bool:
  match tx:
    case S.PutSession{key, s}:
      False{}
    case S.Revar{key, v}:
      S.SPhase.fresh(S.SVar.phase(v))
    case S.Both{a, b}:
      Bool.and(Dl.quiet(a), Dl.quiet(b))
    case _:
      True{}

def Dl.free(tx: S.Tx, +st2: S.State, +k: U32, +h: {S.Sessions.each(k, S.SFresh{}, S.State.sessions(st2)) == True{} : Bool}, +f: {Dl.quiet(tx) == True{} : Bool}) -> {S.Sessions.each(k, S.SFresh{}, S.State.sessions(S.Tx.apply(tx, st2))) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      h
    case S.Put{+key, +ue}:
      match st2:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
          Dl.sift(S.SOwned{S.Ues.put(key, ue, ues)}, sessions, k, h)
    case S.Del{+key}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Dl.sift(S.SOthers{key}, sessions, k, h)
    case S.PutSession{key, s}:
      Empty.absurd({S.Sessions.each(k, S.SFresh{}, S.State.sessions(S.Tx.apply(S.PutSession{key, s}, st2))) == True{} : Bool}, P.Refute.bool(f))
    case S.Revar{+key, +v}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Dl.revar(key, v, sessions, k, h, f)
    case S.DelSession{+key}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Dl.sift(S.SExcept{key}, sessions, k, h)
    case S.Rephase{key, phase}:
      match st2:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.Subs{new}:
      match st2:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.SetLink{link}:
      match st2:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.BumpUe{bk}:
      match st2:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.BumpSeq{n}:
      match st2:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.Both{+a, +b}:
      Dl.free(b, S.Tx.apply(a, st2), k, Dl.free(a, st2, k, h, P.Bool.and_true_l(Dl.quiet(a), Dl.quiet(b), f)), P.Bool.and_true_r(Dl.quiet(a), Dl.quiet(b), f))

def Dl.del(+key: U32, ss: Tb.Table(S.Session)) -> {S.Sessions.each(key, S.SFresh{}, S.Sessions.del(key, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      P.Keep.by(S.Session, tb => {S.Sessions.each(key, S.SFresh{}, tb) == True{} : Bool}, k, t, S.Sessions.sift(S.SExcept{key}, more), S.SSieve.keeps(S.SExcept{key}, k, t), e => h => P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k, key)), S.SPhase.fresh(S.Session.phase(t))), S.Sessions.each(key, S.SFresh{}, S.Sessions.sift(S.SExcept{key}, more)), P.Bool.or_l(Bool.not(U32.is_eq(k, key)), S.SPhase.fresh(S.Session.phase(t)), e), h), Dl.del(key, more))

def Dl.fresh(+t: S.Session, +u: B.Bytes(), +q: U32, +r: B.Bytes()) -> {S.SPhase.fresh(S.Session.phase(S.Session.revar_if(t, S.SVar{u, q, S.Deleting{S.Guard{0}, r}}, True{}))) == True{} : Bool}:
  match t:
    case S.Session{id, var}:
      {==}

def Dl.deleting_row(+k: U32, +key: U32, +t: S.Session, +u: B.Bytes(), +q: U32, +r: B.Bytes(), +c: Bool, +ec: {U32.is_eq(k, key) == c : Bool}) -> {Bool.or(Bool.not(U32.is_eq(k, key)), S.SPhase.fresh(S.Session.phase(S.Session.revar_if(t, S.SVar{u, q, S.Deleting{S.Guard{0}, r}}, Bool.and(U32.is_eq(k, key), True{}))))) == True{} : Bool}:
  match c:
    case True{}:
      sec = Equal.sym(Bool, U32.is_eq(k, key), True{}, ec)
      (%sec : {Bool.or(Bool.not(_), S.SPhase.fresh(S.Session.phase(S.Session.revar_if(t, S.SVar{u, q, S.Deleting{S.Guard{0}, r}}, Bool.and(_, True{}))))) == True{} : Bool}; Dl.fresh(t, u, q, r))
    case False{}:
      sec = Equal.sym(Bool, U32.is_eq(k, key), False{}, ec)
      (%sec : {Bool.or(Bool.not(_), S.SPhase.fresh(S.Session.phase(S.Session.revar_if(t, S.SVar{u, q, S.Deleting{S.Guard{0}, r}}, Bool.and(U32.is_eq(k, key), True{}))))) == True{} : Bool}; {==})

# A session's row its Session Deletion Request has just left being deleted.
def Dl.deleting(+key: U32, +u: B.Bytes(), +q: U32, +r: B.Bytes(), ss: Tb.Table(S.Session)) -> {S.Sessions.each(key, S.SFresh{}, S.Sessions.revar(key, S.SVar{u, q, S.Deleting{S.Guard{0}, r}}, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +t2 = S.Session.revar_if(t, S.SVar{u, q, S.Deleting{S.Guard{0}, r}}, Bool.and(U32.is_eq(k, key), True{}))
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k, key)), S.SPhase.fresh(S.Session.phase(t2))), S.Sessions.each(key, S.SFresh{}, S.Sessions.revar(key, S.SVar{u, q, S.Deleting{S.Guard{0}, r}}, more)), Dl.deleting_row(k, key, t, u, q, r, U32.is_eq(k, key), {==}), Dl.deleting(key, u, q, r, more))

# Quiet outcomes
# --------------
# What follows the failed item: the UE told, the sessions deleted at the UPF.

def Ql.join(+a: N.GOut(), +b: N.GOut(), +ha: {Dl.quiet(N.Out.tx(a)) == True{} : Bool}, +hb: {Dl.quiet(N.Out.tx(b)) == True{} : Bool}) -> {Dl.quiet(N.Out.tx(N.Out.join(a, b))) == True{} : Bool}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          P.Bool.and_intro(Dl.quiet(ta), Dl.quiet(tb), ha, hb)

def Ql.del_if(+key: U32, +t: S.Session, +seq: U32, +more: Tb.Table(S.Session), +b: Bool, later: @q:U32 -> {Dl.quiet(N.Out.tx(Up.N4.deletions(more, q))) == True{} : Bool}) -> {Dl.quiet(N.Out.tx(Up.N4.delete_if(key, t, seq, q => Up.N4.deletions(more, q), b))) == True{} : Bool}:
  match b:
    case True{}:
      +request = Up.N4.delete(S.Session.up_seid(t), seq)
      Ql.join((S.Both{S.Revar{key, S.SVar{S.Session.up_seid(t), seq, S.Deleting{S.Guard{0}, request}}}, S.BumpSeq{1}}, [N.Pfcp{S.Session.tag(t), request}, N.TimerStart{None{}, key, Up.N4.t1_ms()}]), Up.N4.deletions(more, U32.add(seq, 1)), {==}, later(U32.add(seq, 1)))
    case False{}:
      Ql.join((S.DelSession{key}, []), Up.N4.deletions(more, seq), {==}, later(seq))

def Ql.deletions(rows: Tb.Table(S.Session), +seq: U32) -> {Dl.quiet(N.Out.tx(Up.N4.deletions(rows, seq))) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Ql.del_if(key, t, seq, more, S.Session.known(t), q => Ql.deletions(more, q))

def Ql.to_ue_ctx(+key: U32, +ue: S.Ue, +psi: U32, +sm: B.Bytes(), +ctx: Maybe<&2, Sec.Nas.Ctx>) -> {Dl.quiet(N.Out.tx(Gsm.Gsm.to_ue_ctx(key, ue, psi, sm, ctx))) == True{} : Bool}:
  match ctx:
    case None{}:
      {==}
    case Some{c}:
      {==}

def Ql.to_ue_m(+key: U32, +psi: U32, +sm: B.Bytes(), +m: Maybe<&2, S.Ue>) -> {Dl.quiet(N.Out.tx(Gsm.Gsm.to_ue_m(key, psi, sm, m))) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Ql.to_ue_ctx(key, ue, psi, sm, S.Phase.ctx(S.Ue.phase(ue)))

def Ql.give_up(+st: S.State, +skey: U32, +s: S.Session, +sm: B.Bytes(), +seq: U32) -> {Dl.quiet(N.Out.tx(Gsm.Gsm.give_up(st, skey, s, sm, seq))) == True{} : Bool}:
  Ql.join(Gsm.Gsm.to_ue_m(S.Session.ue(s), S.Session.psi(s), sm, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st))), Up.N4.deletions([(skey, s)], seq), Ql.to_ue_m(S.Session.ue(s), S.Session.psi(s), sm, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st))), Ql.deletions([(skey, s)], seq))

def Ql.failed_phase(+st: S.State, +skey: U32, +s: S.Session, +seq: U32, +p: S.SPhase) -> {Dl.quiet(N.Out.tx(Gsm.Gsm.failed_phase(st, skey, s, seq, p))) == True{} : Bool}:
  match p:
    case S.Setting{guard, +pti}:
      Ql.give_up(st, skey, s, Gsm.Gsm.reject(S.Session.psi(s), pti, 26), seq)
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Deleting{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Ql.failed(+st: S.State, +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> {Dl.quiet(N.Out.tx(Gsm.Gsm.failed(st, seq, m))) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Ql.failed_phase(st, skey, s, seq, S.Session.phase(s))

def Ql.faileds(+st: S.State, +key: U32, +items: G.PDUSessionResourceFailedToSetupListSURes(), +seq: U32) -> {Dl.quiet(N.Out.tx(Gsm.Gsm.faileds(st, key, items, seq))) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case G.PDUSessionResourceFailedToSetupItemSURes{+psi, transfer, x} <> +more:
      +a = Gsm.Gsm.failed(st, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)))
      +b = Gsm.Gsm.faileds(st, key, more, U32.add(seq, 1))
      Ql.join((S.BumpSeq{1}, []), N.Out.join(a, b), {==}, Ql.join(a, b, Ql.failed(st, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st))), Ql.faileds(st, key, more, U32.add(seq, 1))))

# Releases
# --------

def Rel.dg(+skey: U32, +s: S.Session, +seq: U32, +b: Bool, +st2: S.State) -> {S.Sessions.each(skey, S.SFresh{}, S.State.sessions(S.Tx.apply(N.Out.tx(Up.N4.delete_if(skey, s, seq, q => Up.N4.deletions([], q), b)), st2))) == True{} : Bool}:
  match b:
    case True{}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Dl.deleting(skey, S.Session.up_seid(s), seq, Up.N4.delete(S.Session.up_seid(s), seq), sessions)
    case False{}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Dl.del(skey, sessions)

def Rel.dn(+skey: U32, +s: S.Session, +seq: U32, +b: Bool, +eb: {S.Session.known(s) == b : Bool}, +kf: {S.Session.known(s) == False{} : Bool}, +st2: S.State) -> {Tb.Table.get(S.Session, skey, S.State.sessions(S.Tx.apply(N.Out.tx(Up.N4.delete_if(skey, s, seq, q => Up.N4.deletions([], q), b)), st2))) == None{} : Maybe<&2, S.Session>}:
  match b:
    case True{}:
      P.Bool.contra({Tb.Table.get(S.Session, skey, S.State.sessions(S.Tx.apply(N.Out.tx(Up.N4.delete_if(skey, s, seq, q => Up.N4.deletions([], q), True{})), st2))) == None{} : Maybe<&2, S.Session>}, S.Session.known(s), eb, kf)
    case False{}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          SDel.get(skey, sessions)

# Deleting one session releases it.
def Rel.deleted(+skey: U32, +s: S.Session, +seq: U32) -> Rel.Spec(Up.N4.deletions([(skey, s)], seq), skey, s):
  (+st2 => Rel.dg(skey, s, seq, S.Session.known(s), st2), (kf => +st2 => Rel.dn(skey, s, seq, S.Session.known(s), {==}, kf, st2), k => eh => Del.one(skey, s, seq, k, eh)))

def Rel.join_r(+a: N.GOut(), +b: N.GOut(), +skey: U32, +s: S.Session, h: Rel.Spec(b, skey, s)) -> Rel.Spec(N.Out.join(a, b), skey, s):
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          (g, (n, d)) = h
          (+st2 => g(S.Tx.apply(ta, st2)), (kf => +st2 => n(kf, S.Tx.apply(ta, st2)), k => eh => Del.app_r(skey, s, aa, ab, d(k, eh))))

# Nor does what comes after it, when that puts no session.
def Rel.join_l(+st0: S.State, +a: N.GOut(), +b: N.GOut(), +skey: U32, +s: S.Session, h: Rel.Spec(a, skey, s), +f: {PL.Lv.free(st0, N.Out.tx(b)) == True{} : Bool}, +q: {Dl.quiet(N.Out.tx(b)) == True{} : Bool}) -> Rel.Spec(N.Out.join(a, b), skey, s):
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          (g, (n, d)) = h
          (+st2 => Dl.free(tb, S.Tx.apply(ta, st2), skey, g(st2), q), (kf => +st2 => None.free(st0, tb, S.Tx.apply(ta, st2), skey, n(kf, st2), f), k => eh => Del.app_l(skey, s, aa, ab, d(k, eh))))

def Rel.give_up(+st: S.State, +skey: U32, +s: S.Session, +sm: B.Bytes(), +seq: U32) -> Rel.Spec(Gsm.Gsm.give_up(st, skey, s, sm, seq), skey, s):
  Rel.join_r(Gsm.Gsm.to_ue_m(S.Session.ue(s), S.Session.psi(s), sm, Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st))), Up.N4.deletions([(skey, s)], seq), skey, s, Rel.deleted(skey, s, seq))

def Rel.abort(+st: S.State, +skey: U32, +s: S.Session, +pti: U32, +cause: U32, +seq: U32) -> Rel.Spec(Gsm.Gsm.abort(st, skey, s, pti, cause, seq), skey, s):
  Rel.give_up(st, skey, s, Gsm.Gsm.reject(S.Session.psi(s), pti, cause), seq)

def Rel.drop(+st: S.State, +skey: U32, +s: S.Session, +seq: U32) -> Rel.Spec(Gsm.Gsm.drop(st, skey, s, seq), skey, s):
  Rel.give_up(st, skey, s, Gsm.Gsm.release_command(S.Session.psi(s)), seq)

# The gNB lists the session as failed: that item aborts it.
def Rel.failed(+st: S.State, +seq: U32, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +skey: U32, +s: S.Session, +guard: S.Guard, +pti: U32, em: {m == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, eh: {S.Session.phase(s) == S.Setting{guard, pti} : S.SPhase}) -> Rel.Spec(Gsm.Gsm.failed(st, seq, m), skey, s):
  sem = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, m, Some{(skey, s)}, em)
  %sem : Rel.Spec(Gsm.Gsm.failed(st, seq, _), skey, s)
  seh = Equal.sym(S.SPhase, S.Session.phase(s), S.Setting{guard, pti}, eh)
  %seh : Rel.Spec(Gsm.Gsm.failed_phase(st, skey, s, seq, _), skey, s)
  Rel.abort(st, skey, s, pti, 26, seq)

# Wherever the item stands in the failed list, the items after it put no session.
def Rel.faileds(+st: S.State, +key: U32, pre: G.PDUSessionResourceFailedToSetupListSURes(), +psi: U32, +transfer: B.Bytes(), +x: Maybe<&2, List<&2, Fr.Ie>>, +post: G.PDUSessionResourceFailedToSetupListSURes(), +seq: U32, +skey: U32, +s: S.Session, +guard: S.Guard, +pti: U32, +es: {S.Sessions.by_psi(key, psi, S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, +eh: {S.Session.phase(s) == S.Setting{guard, pti} : S.SPhase}) -> Rel.Spec(Gsm.Gsm.faileds(st, key, List.append(&2, G.PDUSessionResourceFailedToSetupItemSURes, pre, G.PDUSessionResourceFailedToSetupItemSURes{psi, transfer, x} <> post), seq), skey, s):
  match pre:
    case Nil{}:
      +a = Gsm.Gsm.failed(st, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)))
      +b = Gsm.Gsm.faileds(st, key, post, U32.add(seq, 1))
      Rel.join_r((S.BumpSeq{1}, []), N.Out.join(a, b), skey, s, Rel.join_l(st, a, b, skey, s, Rel.failed(st, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), skey, s, guard, pti, es, eh), PL.Lv.okf_free(st, b, PL.Lw.faileds(st, key, post, U32.add(seq, 1))), Ql.faileds(st, key, post, U32.add(seq, 1))))
    case G.PDUSessionResourceFailedToSetupItemSURes{+p2, t2, x2} <> +pre2:
      +a = Gsm.Gsm.failed(st, seq, S.Sessions.by_psi(key, p2, S.State.sessions(st)))
      +b = Gsm.Gsm.faileds(st, key, List.append(&2, G.PDUSessionResourceFailedToSetupItemSURes, pre2, G.PDUSessionResourceFailedToSetupItemSURes{psi, transfer, x} <> post), U32.add(seq, 1))
      Rel.join_r((S.BumpSeq{1}, []), N.Out.join(a, b), skey, s, Rel.join_r(a, b, skey, s, Rel.faileds(st, key, pre2, psi, transfer, x, post, U32.add(seq, 1), skey, s, guard, pti, es, eh)))

# The steps
# ---------

def Step.refused(+st: S.State, +entropy: B.Bytes(), +len: U32, +bytes: B.Bytes(), +msg: Pf.Msg, +rest: B.Bytes(), +skey: U32, +s: S.Session, +guard: S.Guard, +pti: U32, +accept: Sm.Sm, +request: B.Bytes(), em: {Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)}, ek: {Pf.Msg.kind(msg) == 51 : U32}, es: {S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, ep: {S.Session.phase(s) == S.Creating{guard, pti, accept, request} : S.SPhase}, ec: {Up.N4.accepted(Up.N4.cause(msg)) == False{} : Bool}) -> {K.Kernel.step(st, F.PfcpData{len, bytes}, entropy) == N.Step.of(st, Gsm.Gsm.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st))) : N.Step()}:
  +T : N.Step() = N.Step.of(st, Gsm.Gsm.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st)))
  sem = Equal.sym(B.Read(Pf.Msg), Pf.Msg.read(bytes), Done{(msg, rest)}, em)
  %sem : {N.Step.of(st, Gsm.Gsm.pfcp_msg(st, _)) == T : N.Step()}
  sek = Equal.sym(U32, Pf.Msg.kind(msg), 51, ek)
  %sek : {N.Step.of(st, Gsm.Gsm.pfcp_k1(st, msg, _, U32.is_eq(_, 1))) == T : N.Step()}
  ses = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Some{(skey, s)}, es)
  %ses : {N.Step.of(st, Gsm.Gsm.established(st, msg, _)) == T : N.Step()}
  sep = Equal.sym(S.SPhase, S.Session.phase(s), S.Creating{guard, pti, accept, request}, ep)
  %sep : {N.Step.of(st, Gsm.Gsm.established_phase(st, skey, s, msg, _)) == T : N.Step()}
  sec = Equal.sym(Bool, Up.N4.accepted(Up.N4.cause(msg)), False{}, ec)
  %sec : {N.Step.of(st, Gsm.Gsm.established_as(st, skey, s, pti, accept, _, Up.N4.up_seid(msg))) == T : N.Step()}
  {==}

def Step.expired(+st: S.State, +entropy: B.Bytes(), +skey: U32, +s: S.Session, et: {Tb.Table.get(S.Ue, skey, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, eg: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}) -> {K.Kernel.step(st, F.TimerFired{skey}, entropy) == N.Step.of(st, Gsm.Gsm.expired(st, skey, s, S.Session.phase(s))) : N.Step()}:
  +T : N.Step() = N.Step.of(st, Gsm.Gsm.expired(st, skey, s, S.Session.phase(s)))
  set = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, skey, S.State.ues(st)), None{}, et)
  %set : {N.Step.of(st, K.Kernel.fired_ue(st, skey, _)) == T : N.Step()}
  seg = Equal.sym(Maybe<&2, S.Session>, Tb.Table.get(S.Session, skey, S.State.sessions(st)), Some{s}, eg)
  %seg : {N.Step.of(st, K.Kernel.fired_session(st, skey, _)) == T : N.Step()}
  {==}

def Step.unmodified(+st: S.State, +entropy: B.Bytes(), +len: U32, +bytes: B.Bytes(), +msg: Pf.Msg, +rest: B.Bytes(), +skey: U32, +s: S.Session, +guard: S.Guard, +request: B.Bytes(), em: {Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)}, ek: {Pf.Msg.kind(msg) == 53 : U32}, es: {S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, ep: {S.Session.phase(s) == S.Modifying{guard, request} : S.SPhase}, ec: {Up.N4.accepted(Up.N4.cause(msg)) == False{} : Bool}) -> {K.Kernel.step(st, F.PfcpData{len, bytes}, entropy) == N.Step.of(st, Gsm.Gsm.drop(st, skey, s, S.State.pfcp_seq(st))) : N.Step()}:
  +T : N.Step() = N.Step.of(st, Gsm.Gsm.drop(st, skey, s, S.State.pfcp_seq(st)))
  sem = Equal.sym(B.Read(Pf.Msg), Pf.Msg.read(bytes), Done{(msg, rest)}, em)
  %sem : {N.Step.of(st, Gsm.Gsm.pfcp_msg(st, _)) == T : N.Step()}
  sek = Equal.sym(U32, Pf.Msg.kind(msg), 53, ek)
  %sek : {N.Step.of(st, Gsm.Gsm.pfcp_k1(st, msg, _, U32.is_eq(_, 1))) == T : N.Step()}
  ses = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Some{(skey, s)}, es)
  %ses : {N.Step.of(st, Gsm.Gsm.modified(st, msg, _)) == T : N.Step()}
  sep = Equal.sym(S.SPhase, S.Session.phase(s), S.Modifying{guard, request}, ep)
  %sep : {N.Step.of(st, Gsm.Gsm.modified_phase(st, skey, s, msg, _)) == T : N.Step()}
  sec = Equal.sym(Bool, Up.N4.accepted(Up.N4.cause(msg)), False{}, ec)
  %sec : {N.Step.of(st, Gsm.Gsm.modified_as(st, skey, s, _)) == T : N.Step()}
  {==}

# A session past Creating is known to the UPF.
def Kn.past(+s: S.Session, +p: S.SPhase, +ep: {S.Session.phase(s) == p : S.SPhase}, +k: {S.SPhase.knows(S.Session.phase(s), S.Session.known(s)) == True{} : Bool}) -> {S.SPhase.knows(p, S.Session.known(s)) == True{} : Bool}:
  %ep : {S.SPhase.knows(_, S.Session.known(s)) == True{} : Bool}
  k

# A session in a phase that belongs to a UE.
def Kn.held(+s: S.Session, +p: S.SPhase, +ep: {S.Session.phase(s) == p : S.SPhase}, +h: {S.SPhase.live(p) == True{} : Bool}) -> {S.SPhase.live(S.Session.phase(s)) == True{} : Bool}:
  sep = Equal.sym(S.SPhase, S.Session.phase(s), p, ep)
  (%sep : {S.SPhase.live(_) == True{} : Bool}; h)

# A session being created is not known to the UPF.
def Kn.creating(+s: S.Session, +guard: S.Guard, +pti: U32, +accept: Sm.Sm, +request: B.Bytes(), +ep: {S.Session.phase(s) == S.Creating{guard, pti, accept, request} : S.SPhase}, +k: {S.SPhase.knows(S.Session.phase(s), S.Session.known(s)) == True{} : Bool}) -> {S.Session.known(s) == False{} : Bool}:
  P.Bool.not_true(S.Session.known(s), Kn.past(s, S.Creating{guard, pti, accept, request}, ep, k))

# The release alone, of a session the UPF never knew.
def Fail.gone(+r: N.Step(), +skey: U32, +s: S.Session, h: Rel.Law(r, skey, s), +kf: {S.Session.known(s) == False{} : Bool}) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(r))) == None{} : Maybe<&2, S.Session>}:
  (g, (n, d)) = h
  n(kf)

def Fail.known(+r: N.Step(), +skey: U32, +s: S.Session, h: Rel.Law(r, skey, s), +k: {S.Session.known(s) == True{} : Bool}, +eh: {S.SPhase.live(S.Session.phase(s)) == True{} : Bool}) -> {S.Sessions.each(skey, S.SFresh{}, S.State.sessions(K.Kernel.state(r))) == True{} : Bool} & Up.N4.deleted(skey, s, K.Kernel.actions(r)):
  (g, (n, d)) = h
  (g, d(k, eh))

# The guard fires on a session in phase p: what the guard does in that phase.
def Fail.at(+st: S.State, +entropy: B.Bytes(), +skey: U32, +s: S.Session, +p: S.SPhase, +et: {Tb.Table.get(S.Ue, skey, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +eg: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +ep: {S.Session.phase(s) == p : S.SPhase}, h: Rel.Spec(Gsm.Gsm.expired(st, skey, s, p), skey, s)) -> Rel.Law(K.Kernel.step(st, F.TimerFired{skey}, entropy), skey, s):
  sep = Equal.sym(S.SPhase, S.Session.phase(s), p, ep)
  Rel.by(K.Kernel.step(st, F.TimerFired{skey}, entropy), st, Gsm.Gsm.expired(st, skey, s, S.Session.phase(s)), skey, s, Step.expired(st, entropy, skey, s, et, eg), (%sep : Rel.Spec(Gsm.Gsm.expired(st, skey, s, _), skey, s); h))

# At the retry limit a PFCP request gives up: the failure given.
def Rel.limit(+skey: U32, +s: S.Session, +p: S.SPhase, +request: B.Bytes(), +fail: N.GOut(), +guard: S.Guard, +el: {U32.is_lt(S.Guard.retries(guard), Up.N4.n1()) == False{} : Bool}, h: Rel.Spec(fail, skey, s)) -> Rel.Spec(Gsm.Gsm.resend_if(skey, s, p, request, fail, U32.is_lt(S.Guard.retries(guard), Up.N4.n1())), skey, s):
  sel = Equal.sym(Bool, U32.is_lt(S.Guard.retries(guard), Up.N4.n1()), False{}, el)
  %sel : Rel.Spec(Gsm.Gsm.resend_if(skey, s, p, request, fail, _), skey, s)
  h

def Fail.timer(+st: S.State, +entropy: B.Bytes(), +skey: U32, +s: S.Session, +guard: S.Guard, +pti: U32, +accept: Sm.Sm, +request: B.Bytes(), +ek: {S.Sessions.known(S.State.sessions(st)) == True{} : Bool}, +et: {Tb.Table.get(S.Ue, skey, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +eg: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}) -> ({S.Session.phase(s) == S.Setting{guard, pti} : S.SPhase} -> {S.Sessions.each(skey, S.SFresh{}, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{skey}, entropy)))) == True{} : Bool} & Up.N4.deleted(skey, s, K.Kernel.actions(K.Kernel.step(st, F.TimerFired{skey}, entropy)))) & (({S.Session.phase(s) == S.Creating{guard, pti, accept, request} : S.SPhase} -> {U32.is_lt(S.Guard.retries(guard), Up.N4.n1()) == False{} : Bool} -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{skey}, entropy)))) == None{} : Maybe<&2, S.Session>}) & ({S.Session.phase(s) == S.Modifying{guard, request} : S.SPhase} -> {U32.is_lt(S.Guard.retries(guard), Up.N4.n1()) == False{} : Bool} -> {S.Sessions.each(skey, S.SFresh{}, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{skey}, entropy)))) == True{} : Bool} & Up.N4.deleted(skey, s, K.Kernel.actions(K.Kernel.step(st, F.TimerFired{skey}, entropy))))):
  +r = K.Kernel.step(st, F.TimerFired{skey}, entropy)
  +kp = PL.Lv.found_known(Some{(skey, s)}, S.State.sessions(st), skey, s, {==}, PL.Lv.sget(S.State.sessions(st), skey, s, eg), ek)
  +seq = S.State.pfcp_seq(st)
  +up = U32.add(S.Guard.retries(guard), 1)
  (+ep => Fail.known(r, skey, s, Fail.at(st, entropy, skey, s, S.Setting{guard, pti}, et, eg, ep, Rel.drop(st, skey, s, seq)), Kn.past(s, S.Setting{guard, pti}, ep, kp), Kn.held(s, S.Setting{guard, pti}, ep, {==})), (+ep => el => Fail.gone(r, skey, s, Fail.at(st, entropy, skey, s, S.Creating{guard, pti, accept, request}, et, eg, ep, Rel.limit(skey, s, S.Creating{S.Guard{up}, pti, accept, request}, request, Gsm.Gsm.abort(st, skey, s, pti, 38, seq), guard, el, Rel.abort(st, skey, s, pti, 38, seq))), Kn.creating(s, guard, pti, accept, request, ep, kp)), +ep => el => Fail.known(r, skey, s, Fail.at(st, entropy, skey, s, S.Modifying{guard, request}, et, eg, ep, Rel.limit(skey, s, S.Modifying{S.Guard{up}, request}, request, Gsm.Gsm.drop(st, skey, s, seq), guard, el, Rel.drop(st, skey, s, seq))), Kn.past(s, S.Modifying{guard, request}, ep, kp), Kn.held(s, S.Modifying{guard, request}, ep, {==}))))

def L.smf.establish.failure_releases(st, entropy, len, bytes, msg, rest, skey, s, guard, pti, accept, request, assoc, stream, crit, value, ies, c, amf, k, ran, oks, pre, psi, transfer, x, post, diag, uli, ue, ek):
  +fails = List.append(&2, G.PDUSessionResourceFailedToSetupItemSURes, pre, G.PDUSessionResourceFailedToSetupItemSURes{psi, transfer, x} <> post)
  +seq2 = U32.add(S.State.pfcp_seq(st), U32.from_nat(List.length(&2, G.PDUSessionResourceSetupItemSURes, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks))))
  +ss = S.State.sessions(st)
  (em => ek1 => +es => +ep => ec => Fail.gone(K.Kernel.step(st, F.PfcpData{len, bytes}, entropy), skey, s, Rel.by(K.Kernel.step(st, F.PfcpData{len, bytes}, entropy), st, Gsm.Gsm.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st)), skey, s, Step.refused(st, entropy, len, bytes, msg, rest, skey, s, guard, pti, accept, request, em, ek1, es, ep, ec), Rel.abort(st, skey, s, pti, 38, S.State.pfcp_seq(st))), Kn.creating(s, guard, pti, accept, request, ep, PL.Lv.found_known(S.Sessions.by_seq(Pf.Msg.seq(msg), ss), ss, skey, s, es, PL.Lv.by_seq(Pf.Msg.seq(msg), ss), ek))),
   (et => eg => Fail.timer(st, entropy, skey, s, guard, pti, accept, request, ek, et, eg),
    (em => ek1 => +es => +ep => ec => Fail.known(K.Kernel.step(st, F.PfcpData{len, bytes}, entropy), skey, s, Rel.by(K.Kernel.step(st, F.PfcpData{len, bytes}, entropy), st, Gsm.Gsm.drop(st, skey, s, S.State.pfcp_seq(st)), skey, s, Step.unmodified(st, entropy, len, bytes, msg, rest, skey, s, guard, request, em, ek1, es, ep, ec), Rel.drop(st, skey, s, S.State.pfcp_seq(st))), Kn.past(s, S.Modifying{guard, request}, ep, PL.Lv.found_known(S.Sessions.by_seq(Pf.Msg.seq(msg), ss), ss, skey, s, es, PL.Lv.by_seq(Pf.Msg.seq(msg), ss), ek)), Kn.held(s, S.Modifying{guard, request}, ep, {==})),
     eup => ep => ei => ev => eid => eo => +es => +eh => Fail.known(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), skey, s, Rel.by(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), st, Gsm.Gsm.results(st, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), fails), skey, s, PW.Rt.owned(V.PDUSessionResourceSetupResponse.View, x => {x == N.Step.of(st, Gsm.Gsm.results(st, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), fails)) : N.Step()}, st, entropy, assoc, stream, len, bytes, 1, 29, crit, value, ies, c, i => V.PDUSessionResourceSetupResponse.view(i), r => Gsm.Gsm.setup_response_of_view(st, assoc, r), m => Gsm.Gsm.setup_response_key(st, assoc, ran, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), fails, m), o => Gsm.Gsm.setup_response_ue(st, assoc, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), fails, o), V.PDUSessionResourceSetupResponse.View{amf, ran, oks, Some{fails}, diag, uli}, amf, k, ran, Some{ue}, ep, ei, {==}, eup, {==}, ev, {==}, eid, {==}, eo, {==}), Rel.join_r(Gsm.Gsm.set_ups(st, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), S.State.pfcp_seq(st)), Gsm.Gsm.faileds(st, k, fails, seq2), skey, s, Rel.faileds(st, k, pre, psi, transfer, x, post, seq2, skey, s, guard, pti, es, eh))), Kn.past(s, S.Setting{guard, pti}, eh, PL.Lv.found_known(S.Sessions.by_psi(k, psi, ss), ss, skey, s, es, PL.Lv.by_psi(k, psi, ss), ek)), Kn.held(s, S.Setting{guard, pti}, eh, {==})))))

# A request sent again
# --------------------
# A PFCP request whose guard fires before the retry limit goes again, tagged
# with its session's UE, none once the session is being deleted; its
# session's row takes the guard's new count.

def Re.Sent(+r: N.Step(), +skey: U32, +s: S.Session, +v: S.SVar, +request: B.Bytes(), +m: Maybe<&2, U32>) -> Type:
  {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(r))) == Some{S.Session.with_var(s, v)} : Maybe<&2, S.Session>} & {K.Kernel.actions(r) == [N.Pfcp{m, request}, N.TimerStart{m, skey, Up.N4.t1_ms()}] : List<&2, N.Act>}

def Re.get_row(+key: U32, +v: S.SVar, +t: S.Session, +more: Tb.Table(S.Session), +s: S.Session, +b: Bool, +ef: {S.SVar.follows(v, s) == True{} : Bool}, +e: {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, key, more), b) == Some{s} : Maybe<&2, S.Session>}, ih: {Tb.Table.get(S.Session, key, more) == Some{s} : Maybe<&2, S.Session>} -> {Tb.Table.get(S.Session, key, S.Sessions.revar(key, v, more)) == Some{S.Session.with_var(s, v)} : Maybe<&2, S.Session>}) -> {Tb.Table.hit(S.Session, S.Session.revar_if(t, v, Bool.and(b, S.SVar.follows(v, t))), Tb.Table.get(S.Session, key, S.Sessions.revar(key, v, more)), b) == Some{S.Session.with_var(s, v)} : Maybe<&2, S.Session>}:
  match b:
    case True{}:
      +et = P.Some.inj(S.Session, t, s, e)
      set = Equal.sym(S.Session, t, s, et)
      eft : {S.SVar.follows(v, t) == True{} : Bool} = (%set : {S.SVar.follows(v, _) == True{} : Bool}; ef)
      sef = Equal.sym(Bool, S.SVar.follows(v, t), True{}, eft)
      (%et : {Some{S.Session.revar_if(t, v, S.SVar.follows(v, t))} == Some{S.Session.with_var(_, v)} : Maybe<&2, S.Session>}; (%sef : {Some{S.Session.revar_if(t, v, _)} == Some{S.Session.with_var(t, v)} : Maybe<&2, S.Session>}; {==}))
    case False{}:
      ih(e)

def Re.get(+key: U32, +v: S.SVar, ss: Tb.Table(S.Session), +s: S.Session, +ef: {S.SVar.follows(v, s) == True{} : Bool}, +e: {Tb.Table.get(S.Session, key, ss) == Some{s} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, key, S.Sessions.revar(key, v, ss)) == Some{S.Session.with_var(s, v)} : Maybe<&2, S.Session>}:
  match ss:
    case Nil{}:
      Empty.absurd({Tb.Table.get(S.Session, key, []) == Some{S.Session.with_var(s, v)} : Maybe<&2, S.Session>}, P.Refute.none_some(S.Session, s, e))
    case (+k0, +t) <> +more:
      Re.get_row(key, v, t, more, s, U32.is_eq(k0, key), ef, e, ih => Re.get(key, v, more, s, ef, ih))

def Re.out(+st: S.State, +skey: U32, +s: S.Session, +v: S.SVar, +request: B.Bytes(), +eg: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +ef: {S.SVar.follows(v, s) == True{} : Bool}) -> Re.Sent(N.Step.of(st, (S.Revar{skey, v}, [N.Pfcp{S.Session.tag(s), request}, N.TimerStart{S.Session.tag(s), skey, Up.N4.t1_ms()}])), skey, s, v, request, S.Session.tag(s)):
  match st:
    case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
      (Re.get(skey, v, sessions, s, ef, eg), {==})

# A session's tag, by its phase.
def Re.tag(+s: S.Session, +p: S.SPhase, +ep: {S.Session.phase(s) == p : S.SPhase}) -> {S.Session.tag(s) == Tb.Table.hit(U32, S.Session.ue(s), None{}, S.SPhase.live(p)) : Maybe<&2, U32>}:
  (%ep : {S.Session.tag(s) == Tb.Table.hit(U32, S.Session.ue(s), None{}, S.SPhase.live(_)) : Maybe<&2, U32>}; {==})

# The guard of a session in phase p fired before the retry limit.
def Re.fired(+st: S.State, +entropy: B.Bytes(), +skey: U32, +s: S.Session, +p: S.SPhase, +q: S.SPhase, +request: B.Bytes(), +fail: N.GOut(), +retries: U32, +m: Maybe<&2, U32>, +et: {Tb.Table.get(S.Ue, skey, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +eg: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +ep: {S.Session.phase(s) == p : S.SPhase}, +ex: {Gsm.Gsm.expired(st, skey, s, p) == Gsm.Gsm.resend_if(skey, s, q, request, fail, U32.is_lt(retries, Up.N4.n1())) : N.GOut()}, +er: {U32.is_lt(retries, Up.N4.n1()) == True{} : Bool}, +em: {S.Session.tag(s) == m : Maybe<&2, U32>}, +ef: {S.SVar.follows(S.SVar{S.Session.up_seid(s), S.Session.seq(s), q}, s) == True{} : Bool}) -> Re.Sent(K.Kernel.step(st, F.TimerFired{skey}, entropy), skey, s, S.SVar{S.Session.up_seid(s), S.Session.seq(s), q}, request, m):
  +v : S.SVar = S.SVar{S.Session.up_seid(s), S.Session.seq(s), q}
  se = Equal.sym(N.Step(), K.Kernel.step(st, F.TimerFired{skey}, entropy), N.Step.of(st, Gsm.Gsm.expired(st, skey, s, S.Session.phase(s))), Step.expired(st, entropy, skey, s, et, eg))
  %se : Re.Sent(_, skey, s, v, request, m)
  sep = Equal.sym(S.SPhase, S.Session.phase(s), p, ep)
  %sep : Re.Sent(N.Step.of(st, Gsm.Gsm.expired(st, skey, s, _)), skey, s, v, request, m)
  sex = Equal.sym(N.GOut(), Gsm.Gsm.expired(st, skey, s, p), Gsm.Gsm.resend_if(skey, s, q, request, fail, U32.is_lt(retries, Up.N4.n1())), ex)
  %sex : Re.Sent(N.Step.of(st, _), skey, s, v, request, m)
  ser = Equal.sym(Bool, U32.is_lt(retries, Up.N4.n1()), True{}, er)
  %ser : Re.Sent(N.Step.of(st, Gsm.Gsm.resend_if(skey, s, q, request, fail, _)), skey, s, v, request, m)
  %em : Re.Sent(N.Step.of(st, (S.Revar{skey, v}, [N.Pfcp{S.Session.tag(s), request}, N.TimerStart{S.Session.tag(s), skey, Up.N4.t1_ms()}])), skey, s, v, request, _)
  Re.out(st, skey, s, v, request, eg, ef)

def L.smf.request.retransmitted(st, entropy, skey, s, guard, pti, accept, request, et, eg, er):
  +up : S.Guard = S.Guard{U32.add(S.Guard.retries(guard), 1)}
  +seq = S.State.pfcp_seq(st)
  (+ep => Re.fired(st, entropy, skey, s, S.Creating{guard, pti, accept, request}, S.Creating{up, pti, accept, request}, request, Gsm.Gsm.abort(st, skey, s, pti, 38, seq), S.Guard.retries(guard), Some{S.Session.ue(s)}, et, eg, ep, {==}, er, Re.tag(s, S.Creating{guard, pti, accept, request}, ep), Kn.held(s, S.Creating{guard, pti, accept, request}, ep, {==})), +ep => Re.fired(st, entropy, skey, s, S.Modifying{guard, request}, S.Modifying{up, request}, request, Gsm.Gsm.drop(st, skey, s, seq), S.Guard.retries(guard), Some{S.Session.ue(s)}, et, eg, ep, {==}, er, Re.tag(s, S.Modifying{guard, request}, ep), Kn.held(s, S.Modifying{guard, request}, ep, {==})))

# A Session Deletion Request given up, or answered
# ------------------------------------------------
# Either way the row goes and N.Step.of stops its guard: the row the
# response's sequence number finds is among those it walks.

def De.gone(+st: S.State, +skey: U32, +acts: List<&2, N.Act>) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, (S.DelSession{skey}, acts))))) == None{} : Maybe<&2, S.Session>}:
  match st:
    case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
      SDel.get(skey, sessions)

def De.guard(+s: S.Session, +guard: S.Guard, +request: B.Bytes(), +ep: {S.Session.phase(s) == S.Deleting{guard, request} : S.SPhase}) -> {S.SPhase.guard(S.Session.phase(s)) == Some{guard} : Maybe<&2, S.Guard>}:
  sep = Equal.sym(S.SPhase, S.Session.phase(s), S.Deleting{guard, request}, ep)
  (%sep : {S.SPhase.guard(_) == Some{guard} : Maybe<&2, S.Guard>}; {==})

def De.note() -> N.Act:
  N.Note{F.Warn{}, "PFCP: no Session Deletion Response; deletion given up"}

def De.limit(+st: S.State, +entropy: B.Bytes(), +skey: U32, +s: S.Session, +guard: S.Guard, +request: B.Bytes(), +et: {Tb.Table.get(S.Ue, skey, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +eg: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}, +er: {U32.is_lt(S.Guard.retries(guard), Up.N4.n1()) == False{} : Bool}, +ep: {S.Session.phase(s) == S.Deleting{guard, request} : S.SPhase}) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{skey}, entropy)))) == None{} : Maybe<&2, S.Session>}:
  se = Equal.sym(N.Step(), K.Kernel.step(st, F.TimerFired{skey}, entropy), N.Step.of(st, Gsm.Gsm.expired(st, skey, s, S.Session.phase(s))), Step.expired(st, entropy, skey, s, et, eg))
  %se : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(_))) == None{} : Maybe<&2, S.Session>}
  sep = Equal.sym(S.SPhase, S.Session.phase(s), S.Deleting{guard, request}, ep)
  %sep : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.expired(st, skey, s, _))))) == None{} : Maybe<&2, S.Session>}
  ser = Equal.sym(Bool, U32.is_lt(S.Guard.retries(guard), Up.N4.n1()), False{}, er)
  %ser : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.resend_if(skey, s, S.Deleting{S.Guard{U32.add(S.Guard.retries(guard), 1)}, request}, request, (S.DelSession{skey}, [De.note()]), _))))) == None{} : Maybe<&2, S.Session>}
  De.gone(st, skey, [De.note()])

def L.smf.deletion.retransmitted(st, entropy, skey, s, guard, request, et, es, ep):
  +up : S.Guard = S.Guard{U32.add(S.Guard.retries(guard), 1)}
  (er => Re.fired(st, entropy, skey, s, S.Deleting{guard, request}, S.Deleting{up, request}, request, (S.DelSession{skey}, [De.note()]), S.Guard.retries(guard), None{}, et, es, ep, {==}, er, Re.tag(s, S.Deleting{guard, request}, ep), {==}), +er => (De.limit(st, entropy, skey, s, guard, request, et, es, er, ep), L.smf.guard.stopped(st, F.TimerFired{skey}, entropy, skey, s, guard, es, De.guard(s, guard, request, ep), De.limit(st, entropy, skey, s, guard, request, et, es, er, ep))))

def Ans.Stops(+m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +ss: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> Type:
  @k:U32 -> @t:S.Session -> @g:S.Guard -> {m == Some{(k, t)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>} -> {S.SPhase.guard(S.Session.phase(t)) == Some{g} : Maybe<&2, S.Guard>} -> {Tb.Table.has(S.Session, k, after) == False{} : Bool} -> {N.Acts.stops(k, N.Gone.cancels(ss, after)) == True{} : Bool}

def Ans.key(p: Sigma<&2, &2, U32, _ => S.Session>) -> U32:
  match p:
    case (k, t):
      k

def Ans.row(p: Sigma<&2, &2, U32, _ => S.Session>) -> S.Session:
  match p:
    case (k, t):
      t

def Ans.cancel(+k: U32, +t: S.Session, +g: S.Guard, +after: Tb.Table(S.Session), +eg: {S.SPhase.guard(S.Session.phase(t)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.has(S.Session, k, after) == False{} : Bool}) -> {N.Acts.stops(k, N.Gone.row(k, t, Tb.Table.has(S.Session, k, after))) == True{} : Bool}:
  seh = Equal.sym(Bool, Tb.Table.has(S.Session, k, after), False{}, eh)
  seg = Equal.sym(Maybe<&2, S.Guard>, S.SPhase.guard(S.Session.phase(t)), Some{g}, eg)
  (%seh : {N.Acts.stops(k, N.Gone.row(k, t, _)) == True{} : Bool}; (%seg : {N.Acts.stops(k, N.Guard.cancel(k, _)) == True{} : Bool}; P.Bool.or_l(U32.is_eq(k, k), False{}, P.U32.is_eq_refl(k))))

def Ans.head(+k0: U32, +t0: S.Session, +more: Tb.Table(S.Session), +after: Tb.Table(S.Session), +k: U32, +t: S.Session, +g: S.Guard, +em: {Some{(k0, t0)} == Some{(k, t)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, +eg: {S.SPhase.guard(S.Session.phase(t)) == Some{g} : Maybe<&2, S.Guard>}, +eh: {Tb.Table.has(S.Session, k, after) == False{} : Bool}) -> {N.Acts.stops(k, List.append(&2, N.Act, N.Gone.row(k0, t0, Tb.Table.has(S.Session, k0, after)), N.Gone.cancels(more, after))) == True{} : Bool}:
  +ep = P.Some.inj(Sigma<&2, &2, U32, _ => S.Session>, (k0, t0), (k, t), em)
  ek = Equal.sym(U32, k0, k, Equal.cong(Sigma<&2, &2, U32, _ => S.Session>, U32, Ans.key, (k0, t0), (k, t), ep))
  et = Equal.sym(S.Session, t0, t, Equal.cong(Sigma<&2, &2, U32, _ => S.Session>, S.Session, Ans.row, (k0, t0), (k, t), ep))
  (%ek : {N.Acts.stops(k, List.append(&2, N.Act, N.Gone.row(_, t0, Tb.Table.has(S.Session, _, after)), N.Gone.cancels(more, after))) == True{} : Bool}; (%et : {N.Acts.stops(k, List.append(&2, N.Act, N.Gone.row(k, _, Tb.Table.has(S.Session, k, after)), N.Gone.cancels(more, after))) == True{} : Bool}; PL.Gs.stops_pre(k, N.Gone.row(k, t, Tb.Table.has(S.Session, k, after)), N.Gone.cancels(more, after), Ans.cancel(k, t, g, after, eg, eh))))

def Ans.pick(+seq: U32, +k0: U32, +t0: S.Session, +more: Tb.Table(S.Session), +after: Tb.Table(S.Session), +hit: Bool, ih: Ans.Stops(S.Sessions.by_seq(seq, more), more, after)) -> Ans.Stops(S.Sessions.pick(k0, t0, S.Sessions.by_seq(seq, more), hit), (k0, t0) <> more, after):
  match hit:
    case True{}:
      +k => +t => +g => +em => +eg => +eh => Ans.head(k0, t0, more, after, k, t, g, em, eg, eh)
    case False{}:
      +k => +t => +g => +em => +eg => +eh => PL.Gs.stops_app(k, N.Gone.row(k0, t0, Tb.Table.has(S.Session, k0, after)), N.Gone.cancels(more, after), ih(k, t, g, em, eg, eh))

def Ans.by_seq(+seq: U32, +ss: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> Ans.Stops(S.Sessions.by_seq(seq, ss), ss, after):
  match ss:
    case Nil{}:
      +k => +t => g => em => eg => eh => Empty.absurd({N.Acts.stops(k, N.Gone.cancels([], after)) == True{} : Bool}, P.Refute.none_some(Sigma<&2, &2, U32, _ => S.Session>, (k, t), em))
    case (+k0, +t0) <> +more:
      Ans.pick(seq, k0, t0, more, after, U32.is_eq(S.Session.seq(t0), seq), Ans.by_seq(seq, more, after))

def Ans.has_del(+key: U32, +ss: Tb.Table(S.Session)) -> {Tb.Table.has(S.Session, key, S.Sessions.del(key, ss)) == False{} : Bool}:
  se = Equal.sym(Maybe<&2, S.Session>, Tb.Table.get(S.Session, key, S.Sessions.del(key, ss)), None{}, SDel.get(key, ss))
  (%se : {Tb.Table.present(S.Session, _) == False{} : Bool}; {==})

def Ans.stops(+st: S.State, +skey: U32, +s: S.Session, +guard: S.Guard, +request: B.Bytes(), +seq: U32, +acts: List<&2, N.Act>, +es: {S.Sessions.by_seq(seq, S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, +ep: {S.Session.phase(s) == S.Deleting{guard, request} : S.SPhase}) -> {N.Acts.stops(skey, K.Kernel.actions(N.Step.of(st, (S.DelSession{skey}, acts)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
      PL.Gs.stops_app(skey, acts, N.Gone.cancels(sessions, S.Sessions.del(skey, sessions)), Ans.by_seq(seq, sessions, S.Sessions.del(skey, sessions))(skey, s, guard, es, De.guard(s, guard, request, ep), Ans.has_del(skey, sessions)))

def Step.answered(+st: S.State, +entropy: B.Bytes(), +len: U32, +bytes: B.Bytes(), +msg: Pf.Msg, +rest: B.Bytes(), +skey: U32, +s: S.Session, +guard: S.Guard, +request: B.Bytes(), em: {Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)}, ek: {Pf.Msg.kind(msg) == 55 : U32}, es: {S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, ep: {S.Session.phase(s) == S.Deleting{guard, request} : S.SPhase}) -> {K.Kernel.step(st, F.PfcpData{len, bytes}, entropy) == N.Step.of(st, (S.DelSession{skey}, Gsm.Gsm.deleted_notes(Up.N4.accepted(Up.N4.cause(msg))))) : N.Step()}:
  +T : N.Step() = N.Step.of(st, (S.DelSession{skey}, Gsm.Gsm.deleted_notes(Up.N4.accepted(Up.N4.cause(msg)))))
  sem = Equal.sym(B.Read(Pf.Msg), Pf.Msg.read(bytes), Done{(msg, rest)}, em)
  %sem : {N.Step.of(st, Gsm.Gsm.pfcp_msg(st, _)) == T : N.Step()}
  sek = Equal.sym(U32, Pf.Msg.kind(msg), 55, ek)
  %sek : {N.Step.of(st, Gsm.Gsm.pfcp_k1(st, msg, _, U32.is_eq(_, 1))) == T : N.Step()}
  ses = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Some{(skey, s)}, es)
  %ses : {N.Step.of(st, Gsm.Gsm.deleted(msg, _)) == T : N.Step()}
  sep = Equal.sym(S.SPhase, S.Session.phase(s), S.Deleting{guard, request}, ep)
  %sep : {N.Step.of(st, Gsm.Gsm.deleted_phase(skey, msg, _)) == T : N.Step()}
  {==}

def L.smf.deletion.answered(st, entropy, len, bytes, msg, rest, skey, s, guard, request, em, ek, es, ep):
  +r = K.Kernel.step(st, F.PfcpData{len, bytes}, entropy)
  +notes = Gsm.Gsm.deleted_notes(Up.N4.accepted(Up.N4.cause(msg)))
  +T : N.Step() = N.Step.of(st, (S.DelSession{skey}, notes))
  sr1 = Equal.sym(N.Step(), r, T, Step.answered(st, entropy, len, bytes, msg, rest, skey, s, guard, request, em, ek, es, ep))
  sr2 = Equal.sym(N.Step(), r, T, Step.answered(st, entropy, len, bytes, msg, rest, skey, s, guard, request, em, ek, es, ep))
  ((%sr1 : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(_))) == None{} : Maybe<&2, S.Session>}; De.gone(st, skey, notes)), (%sr2 : {N.Acts.stops(skey, K.Kernel.actions(_)) == True{} : Bool}; Ans.stops(st, skey, s, guard, request, Pf.Msg.seq(msg), notes, es, ep)))

# What a UL NAS Transport comes to
# --------------------------------
# A verified UL NAS Transport from a registered UE is answered by the N1 SM
# message handler; the step is that answer rendered.

def Transport.out(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +k: U32, +ran: B.Bytes(), +nas: B.Bytes(), uli: G.UserLocationInformation, +ue: S.Ue, +ctx: Sec.Nas.Ctx, prot: Sec.Nas.Protection, +plain: B.Bytes(), count: Sec.Nas.Count, +ctx2: Sec.Nas.Ctx, old: Sec.Nas.Ctx, +nh: S.Nh, +released: Maybe<&2, S.Side>, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ev: {V.UplinkNASTransport.view(ies) == Done{V.UplinkNASTransport.View{amf, ran, nas, uli}} : Result<&2, &2, B.Err, V.UplinkNASTransport.View>}, eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, eo: {Gmm.Gmm.owner(st, assoc, k, ran) == Some{ue} : Maybe<&2, S.Ue>}, ec: {S.Phase.ctx(S.Ue.phase(ue)) == Some{ctx} : Maybe<&2, Sec.Nas.Ctx>}, eu: {Sec.Nas.unprotect(ctx, nas) == Done{Sec.Unprotected{prot, plain, count, ctx2}} : Result<&2, &2, B.Err, Sec.Nas.Unprotected>}, em: {Mm.Mm.read(plain) == Done{Mm.Mm{Mm.UlNasTransport{}, fields, opts}} : Result<&2, &2, B.Err, Mm.Mm>}, er: {S.Ue.phase(ue) == S.Registered{old, nh, released} : S.Phase}, en: {U32.is_eq(I.Fields.byte1(fields), 1) == True{} : Bool}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, Sm.Sm.read(I.Fields.lve2(fields)))) : N.Step()}:
  +R : N.Step() = N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, Sm.Sm.read(I.Fields.lve2(fields))))
  sec = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.ctx(S.Ue.phase(ue)), Some{ctx}, ec)
  seu = Equal.sym(Result<&2, &2, B.Err, Sec.Nas.Unprotected>, Sec.Nas.unprotect(ctx, nas), Done{Sec.Unprotected{prot, plain, count, ctx2}}, eu)
  sem = Equal.sym(Result<&2, &2, B.Err, Mm.Mm>, Mm.Mm.read(plain), Done{Mm.Mm{Mm.UlNasTransport{}, fields, opts}}, em)
  ser = Equal.sym(S.Phase, S.Ue.phase(ue), S.Registered{old, nh, released}, er)
  sen = Equal.sym(Bool, U32.is_eq(I.Fields.byte1(fields), 1), True{}, en)
  PW.Rt.owned(V.UplinkNASTransport.View, x => {x == R : N.Step()}, st, entropy, assoc, stream, len, bytes, 0, 46, crit, value, ies, c, i => V.UplinkNASTransport.view(i), r => Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, r), m => Gmm.Gmm.uplink_key(st, assoc, ran, nas, entropy, m), o => Gmm.Gmm.uplink_ue(st, assoc, k, nas, entropy, o), V.UplinkNASTransport.View{amf, ran, nas, uli}, amf, k, ran, Some{ue}, ep, ei, {==}, eup, {==}, ev, {==}, eid, {==}, eo, (%sec : {N.Step.of(st, Gmm.Gmm.secured(st, k, ue, entropy, nas, _)) == R : N.Step()}; (%seu : {N.Step.of(st, Gmm.Gmm.opened(st, k, ue, entropy, _)) == R : N.Step()}; (%sem : {N.Step.of(st, Gmm.Gmm.protected(st, k, ue, entropy, count, ctx2, _)) == R : N.Step()}; (%ser : {N.Step.of(st, Gmm.Gmm.sphase(st, k, ue, entropy, count, ctx2, Mm.UlNasTransport{}, fields, opts, _)) == R : N.Step()}; (%sen : {N.Step.of(st, Gsm.Gsm.n1(st, k, ue, ctx2, opts, entropy, I.Fields.lve2(fields), _)) == R : N.Step()}; {==}))))))

def Tx.rephase_sessions(key: U32, p: S.Phase, st: S.State) -> {S.State.sessions(S.Tx.apply(S.Rephase{key, p}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      {==}

def Tx.rephase_seq(key: U32, p: S.Phase, st: S.State) -> {S.State.pfcp_seq(S.Tx.apply(S.Rephase{key, p}, st)) == S.State.pfcp_seq(st) : U32}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      {==}

def L.smf.establish.reject_leaves_state(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, ran, nas, uli, ue, ctx, prot, plain, count, ctx2, old, nh, released, fields, opts, psi, pti, sfields, sopts, cfg, cause, ep, ei, ev, eid, eo, ec, eu, em, er, en, es, ef, ex, eup):
  eq = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, Sm.Sm.read(I.Fields.lve2(fields)))), Transport.out(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, ran, nas, uli, ue, ctx, prot, plain, count, ctx2, old, nh, released, fields, opts, ep, ei, ev, eid, eo, ec, eu, em, er, en, eup))
  %eq : {S.State.sessions(K.Kernel.state(_)) == S.State.sessions(st) : Tb.Table(S.Session)} & ({S.State.pfcp_seq(K.Kernel.state(_)) == S.State.pfcp_seq(st) : U32} & {K.Kernel.actions(_) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), k, S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))}] : List<&2, N.Act>})
  ses = Equal.sym(Result<&2, &2, B.Err, Sm.Sm>, Sm.Sm.read(I.Fields.lve2(fields)), Done{Sm.Sm{psi, pti, Sm.EstablishmentRequest{}, sfields, sopts}}, es)
  %ses : {S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, _)))) == S.State.sessions(st) : Tb.Table(S.Session)} & ({S.State.pfcp_seq(K.Kernel.state(N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, _)))) == S.State.pfcp_seq(st) : U32} & {K.Kernel.actions(N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, _))) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), k, S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))}] : List<&2, N.Act>})
  sef = Equal.sym(Maybe<&2, S.Cfg>, S.State.config(st), Some{cfg}, ef)
  %sef : {S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.with_cfg(st, k, ue, ctx2, psi, pti, opts, sopts, entropy, _)))) == S.State.sessions(st) : Tb.Table(S.Session)} & ({S.State.pfcp_seq(K.Kernel.state(N.Step.of(st, Gsm.Gsm.with_cfg(st, k, ue, ctx2, psi, pti, opts, sopts, entropy, _)))) == S.State.pfcp_seq(st) : U32} & {K.Kernel.actions(N.Step.of(st, Gsm.Gsm.with_cfg(st, k, ue, ctx2, psi, pti, opts, sopts, entropy, _))) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), k, S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))}] : List<&2, N.Act>})
  sex = Equal.sym(Gsm.Check, Gsm.Gsm.validate(cfg, psi, opts, sopts, Up.N4.up(st), S.State.sessions(st), entropy), Gsm.Refuse{cause}, ex)
  %sex : {S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.checked(st, k, ue, ctx2, cfg, psi, pti, _)))) == S.State.sessions(st) : Tb.Table(S.Session)} & ({S.State.pfcp_seq(K.Kernel.state(N.Step.of(st, Gsm.Gsm.checked(st, k, ue, ctx2, cfg, psi, pti, _)))) == S.State.pfcp_seq(st) : U32} & {K.Kernel.actions(N.Step.of(st, Gsm.Gsm.checked(st, k, ue, ctx2, cfg, psi, pti, _))) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), k, S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))}] : List<&2, N.Act>})
  (Tx.rephase_sessions(k, S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))), st), (Tx.rephase_seq(k, S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))), st), {==}))

def L.smf.modification.rejected(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, ran, nas, uli, ue, ctx, prot, plain, count, ctx2, old, nh, released, fields, opts, psi, pti, sfields, sopts, ep, ei, ev, eid, eo, ec, eu, em, er, en, es, eup):
  eq = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, Sm.Sm.read(I.Fields.lve2(fields)))), Transport.out(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, ran, nas, uli, ue, ctx, prot, plain, count, ctx2, old, nh, released, fields, opts, ep, ei, ev, eid, eo, ec, eu, em, er, en, eup))
  %eq : {S.State.sessions(K.Kernel.state(_)) == S.State.sessions(st) : Tb.Table(S.Session)} & {K.Kernel.actions(_) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), k, S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.modification_reject(psi, pti))))}] : List<&2, N.Act>}
  ses = Equal.sym(Result<&2, &2, B.Err, Sm.Sm>, Sm.Sm.read(I.Fields.lve2(fields)), Done{Sm.Sm{psi, pti, Sm.ModificationRequest{}, sfields, sopts}}, es)
  %ses : {S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, _)))) == S.State.sessions(st) : Tb.Table(S.Session)} & {K.Kernel.actions(N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, _))) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), k, S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.modification_reject(psi, pti))))}] : List<&2, N.Act>}
  (Tx.rephase_sessions(k, S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.modification_reject(psi, pti))))), st), {==})

# Guards left alone
# -----------------
# The guard of a key k that is neither a context's, nor the next context's,
# nor the PFCP association's timer: a UE procedure never stops it, and starts
# it only for T1 when its row is kept (Run.ok1); a step stops no guard of a
# row it keeps (N.Gone.cancels).

def Run.free(+st: S.State, +k: U32) -> Bool:
  Bool.not(Bool.or(U32.is_eq(k, S.N4.timer()), PL.Lv.held(st, k)))

def Run.free_of(+st: S.State, +k: U32, +en: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +ef: {S.Maybe.same_u32(S.State.fresh(st), Some{k}) == False{} : Bool}, +ez: {U32.is_eq(k, S.N4.timer()) == False{} : Bool}) -> {Run.free(st, k) == True{} : Bool}:
  sen = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), None{}, en)
  hn : {Tb.Table.has(S.Ue, k, S.State.ues(st)) == False{} : Bool} = (%sen : {Tb.Table.present(S.Ue, _) == False{} : Bool}; {==})
  sx = Equal.sym(Bool, Bool.or(U32.is_eq(k, S.N4.timer()), PL.Lv.held(st, k)), False{}, P.Bool.or_false(U32.is_eq(k, S.N4.timer()), PL.Lv.held(st, k), ez, P.Bool.or_false(Tb.Table.has(S.Ue, k, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{k}), hn, ef)))
  (%sx : {Bool.not(_) == True{} : Bool}; {==})

def Run.unfree(+st: S.State, +k: U32, +h: {Run.free(st, k) == True{} : Bool}) -> {Bool.or(U32.is_eq(k, S.N4.timer()), PL.Lv.held(st, k)) == False{} : Bool}:
  P.Bool.not_true(Bool.or(U32.is_eq(k, S.N4.timer()), PL.Lv.held(st, k)), h)

def Run.sure1(+k: U32, +a: N.Act) -> Bool:
  Bool.and(Bool.not(N.Act.stops(k, a)), Bool.or(Bool.not(N.Act.starts(k, a)), N.Act.starts_for(k, Up.N4.t1_ms(), a)))

def Run.ok1(+st: S.State, +k: U32, +a: N.Act) -> Bool:
  Bool.and(Bool.not(N.Act.stops(k, a)), Bool.or(Bool.not(N.Act.starts(k, a)), Bool.and(PL.Lv.kept(st, k), N.Act.starts_for(k, Up.N4.t1_ms(), a))))

def Run.oks(+st: S.State, +k: U32, as: List<&2, N.Act>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case +a <> more:
      Bool.and(Run.ok1(st, k, a), Run.oks(st, k, more))

def Run.sure(+k: U32, as: List<&2, N.Act>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case +a <> more:
      Bool.and(Run.sure1(k, a), Run.sure(k, more))

def Run.app(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {N.Acts.touches(k, xs) == False{} : Bool}, +hy: {N.Acts.touches(k, ys) == False{} : Bool}) -> {N.Acts.touches(k, List.append(&2, N.Act, xs, ys)) == False{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      +x = Bool.or(N.Act.starts(k, a), N.Act.stops(k, a))
      P.Bool.or_false(x, N.Acts.touches(k, List.append(&2, N.Act, more, ys)), P.Bool.or_false_l(x, N.Acts.touches(k, more), hx), Run.app(k, more, ys, P.Bool.or_false_r(x, N.Acts.touches(k, more), hx), hy))

def Run.ne(+ues: Tb.Table(S.Ue), +t: U32, +k: U32, +c: Bool, +ec: {U32.is_eq(t, k) == c : Bool}, +eh: {Tb.Table.has(S.Ue, t, ues) == True{} : Bool}, +hn: {Tb.Table.has(S.Ue, k, ues) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      e1 = P.U32.eq_of_is_eq(t, k, ec)
      ek : {Tb.Table.has(S.Ue, k, ues) == True{} : Bool} = (%e1 : {Tb.Table.has(S.Ue, _, ues) == True{} : Bool}; eh)
      P.Bool.contra({True{} == False{} : Bool}, Tb.Table.has(S.Ue, k, ues), ek, hn)
    case False{}:
      {==}

def Run.start_if(+st: S.State, +k: U32, +t: U32, +d: U32, +c: Bool, +ec: {U32.is_eq(t, k) == c : Bool}, +ef: {Run.free(st, k) == True{} : Bool}, +h: {PL.Lv.timed(st, t, d) == True{} : Bool}) -> {Bool.or(Bool.not(c), Bool.and(PL.Lv.kept(st, k), Bool.and(c, U32.is_eq(d, Up.N4.t1_ms())))) == True{} : Bool}:
  match c:
    case True{}:
      e1 = P.U32.eq_of_is_eq(t, k, ec)
      hk : {PL.Lv.timed(st, k, d) == True{} : Bool} = (%e1 : {PL.Lv.timed(st, _, d) == True{} : Bool}; h)
      +s = Bool.and(PL.Lv.kept(st, k), U32.is_eq(d, Up.N4.t1_ms()))
      +x = Run.unfree(st, k, ef)
      +h1 = P.Bool.or_true_r(U32.is_eq(k, S.N4.timer()), Bool.or(PL.Lv.held(st, k), s), P.Bool.or_false_l(U32.is_eq(k, S.N4.timer()), PL.Lv.held(st, k), x), hk)
      P.Bool.or_true_r(PL.Lv.held(st, k), s, P.Bool.or_false_r(U32.is_eq(k, S.N4.timer()), PL.Lv.held(st, k), x), h1)
    case False{}:
      {==}

def Run.act(+st: S.State, +k: U32, +a: N.Act, +ef: {Run.free(st, k) == True{} : Bool}, +h: {PL.Lv.act(st, a) == True{} : Bool}) -> {Run.ok1(st, k, a) == True{} : Bool}:
  match a:
    case N.TimerCancel{+t}:
      sne = Equal.sym(Bool, U32.is_eq(t, k), False{}, Run.ne(S.State.ues(st), t, k, U32.is_eq(t, k), {==}, h, P.Bool.or_false_l(Tb.Table.has(S.Ue, k, S.State.ues(st)), S.Maybe.same_u32(S.State.fresh(st), Some{k}), P.Bool.or_false_r(U32.is_eq(k, S.N4.timer()), PL.Lv.held(st, k), Run.unfree(st, k, ef)))))
      (%sne : {Bool.and(Bool.not(_), True{}) == True{} : Bool}; {==})
    case N.TimerStart{+ue, +t, +d}:
      Run.start_if(st, k, t, d, U32.is_eq(t, k), {==}, ef, P.Bool.and_true_r(PL.Lv.tag(st, ue), PL.Lv.timed(st, t, d), h))
    case N.DlNas{assoc, stream, key, ran_id, nas}:
      {==}
    case N.Ics{assoc, stream, key, ran_id, cfg, caps, k_gnb, nas}:
      {==}
    case N.PduSetup{assoc, stream, key, ran_id, psi, sst, nas, transfer}:
      {==}
    case N.Release{assoc, stream, key, ran_id, cause}:
      {==}
    case N.SwitchAck{assoc, stream, key, ran_id, caps, nh, switched, released, sst}:
      {==}
    case N.SwitchFail{assoc, stream, ue, amf, ran_id, psis, cause}:
      {==}
    case N.UeSend{assoc, stream, key, bytes}:
      {==}
    case N.ErrInd{assoc, cause}:
      {==}
    case N.Setup{assoc, answer}:
      {==}
    case N.Pfcp{ue, bytes}:
      {==}
    case N.Note{level, text}:
      {==}

def Run.acts(+st: S.State, +k: U32, +as: List<&2, N.Act>, +ef: {Run.free(st, k) == True{} : Bool}, +h: {PL.Lv.acts(st, as) == True{} : Bool}) -> {Run.oks(st, k, as) == True{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case +a <> +more:
      P.Bool.and_intro(Run.ok1(st, k, a), Run.oks(st, k, more), Run.act(st, k, a, ef, P.Bool.and_true_l(PL.Lv.act(st, a), PL.Lv.acts(st, more), h)), Run.acts(st, k, more, ef, P.Bool.and_true_r(PL.Lv.act(st, a), PL.Lv.acts(st, more), h)))

# Of a key whose row is not kept, a UE procedure starts no guard either.
def Run.quiet1(+st: S.State, +k: U32, +a: N.Act, +h: {Run.ok1(st, k, a) == True{} : Bool}, +nk: {PL.Lv.kept(st, k) == False{} : Bool}) -> {Bool.or(N.Act.starts(k, a), N.Act.stops(k, a)) == False{} : Bool}:
  +sf = N.Act.starts_for(k, Up.N4.t1_ms(), a)
  +so = P.Bool.not_true(N.Act.stops(k, a), P.Bool.and_true_l(Bool.not(N.Act.stops(k, a)), Bool.or(Bool.not(N.Act.starts(k, a)), Bool.and(PL.Lv.kept(st, k), sf)), h))
  r = P.Bool.and_true_r(Bool.not(N.Act.stops(k, a)), Bool.or(Bool.not(N.Act.starts(k, a)), Bool.and(PL.Lv.kept(st, k), sf)), h)
  r2 : {Bool.or(Bool.not(N.Act.starts(k, a)), False{}) == True{} : Bool} = (%nk : {Bool.or(Bool.not(N.Act.starts(k, a)), Bool.and(_, sf)) == True{} : Bool}; r)
  +sa = P.Bool.not_true(N.Act.starts(k, a), P.Bool.or_true_l(Bool.not(N.Act.starts(k, a)), False{}, {==}, r2))
  P.Bool.or_false(N.Act.starts(k, a), N.Act.stops(k, a), sa, so)

def Run.quiet(+st: S.State, +k: U32, +as: List<&2, N.Act>, +h: {Run.oks(st, k, as) == True{} : Bool}, +nk: {PL.Lv.kept(st, k) == False{} : Bool}) -> {N.Acts.touches(k, as) == False{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case +a <> +more:
      P.Bool.or_false(Bool.or(N.Act.starts(k, a), N.Act.stops(k, a)), N.Acts.touches(k, more), Run.quiet1(st, k, a, P.Bool.and_true_l(Run.ok1(st, k, a), Run.oks(st, k, more), h), nk), Run.quiet(st, k, more, P.Bool.and_true_r(Run.ok1(st, k, a), Run.oks(st, k, more), h), nk))

def Run.sure_of1(+st: S.State, +k: U32, +a: N.Act, +h: {Run.ok1(st, k, a) == True{} : Bool}) -> {Run.sure1(k, a) == True{} : Bool}:
  +sf = N.Act.starts_for(k, Up.N4.t1_ms(), a)
  +ns = Bool.not(N.Act.starts(k, a))
  P.Bool.and_intro(Bool.not(N.Act.stops(k, a)), Bool.or(ns, sf), P.Bool.and_true_l(Bool.not(N.Act.stops(k, a)), Bool.or(ns, Bool.and(PL.Lv.kept(st, k), sf)), h), P.Bool.or_mono(ns, Bool.and(PL.Lv.kept(st, k), sf), sf, P.Bool.and_true_r(Bool.not(N.Act.stops(k, a)), Bool.or(ns, Bool.and(PL.Lv.kept(st, k), sf)), h), e => P.Bool.and_true_r(PL.Lv.kept(st, k), sf, e)))

def Run.sure_of(+st: S.State, +k: U32, +as: List<&2, N.Act>, +h: {Run.oks(st, k, as) == True{} : Bool}) -> {Run.sure(k, as) == True{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case +a <> +more:
      P.Bool.and_intro(Run.sure1(k, a), Run.sure(k, more), Run.sure_of1(st, k, a, P.Bool.and_true_l(Run.ok1(st, k, a), Run.oks(st, k, more), h)), Run.sure_of(st, k, more, P.Bool.and_true_r(Run.ok1(st, k, a), Run.oks(st, k, more), h)))

def Run.cancel(+k0: U32, +g: Maybe<&2, S.Guard>, +k: U32, +ne: {U32.is_eq(k0, k) == False{} : Bool}) -> {N.Acts.touches(k, N.Guard.cancel(k0, g)) == False{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{guard}:
      sne = Equal.sym(Bool, U32.is_eq(k0, k), False{}, ne)
      (%sne : {Bool.or(Bool.or(False{}, _), False{}) == False{} : Bool}; {==})

def Run.row(+k0: U32, +t: S.Session, +kept: Bool, +k: U32, +ne: {U32.is_eq(k0, k) == False{} : Bool}) -> {N.Acts.touches(k, N.Gone.row(k0, t, kept)) == False{} : Bool}:
  match kept:
    case True{}:
      {==}
    case False{}:
      Run.cancel(k0, S.SPhase.guard(S.Session.phase(t)), k, ne)

def Run.row_if(+k0: U32, +t: S.Session, +after: Tb.Table(S.Session), +k: U32, +c: Bool, +ec: {U32.is_eq(k0, k) == c : Bool}, +eh: {Tb.Table.has(S.Session, k, after) == True{} : Bool}) -> {N.Acts.touches(k, N.Gone.row(k0, t, Tb.Table.has(S.Session, k0, after))) == False{} : Bool}:
  match c:
    case True{}:
      e1 = Equal.sym(U32, k0, k, P.U32.eq_of_is_eq(k0, k, ec))
      seh = Equal.sym(Bool, Tb.Table.has(S.Session, k, after), True{}, eh)
      (%e1 : {N.Acts.touches(k, N.Gone.row(_, t, Tb.Table.has(S.Session, _, after))) == False{} : Bool}; (%seh : {N.Acts.touches(k, N.Gone.row(k, t, _)) == False{} : Bool}; {==}))
    case False{}:
      Run.row(k0, t, Tb.Table.has(S.Session, k0, after), k, ec)

def Run.gone(+before: Tb.Table(S.Session), +after: Tb.Table(S.Session), +k: U32, +eh: {Tb.Table.has(S.Session, k, after) == True{} : Bool}) -> {N.Acts.touches(k, N.Gone.cancels(before, after)) == False{} : Bool}:
  match before:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      Run.app(k, N.Gone.row(k0, t, Tb.Table.has(S.Session, k0, after)), N.Gone.cancels(more, after), Run.row_if(k0, t, after, k, U32.is_eq(k0, k), {==}, eh), Run.gone(more, after, k, eh))

def Run.when(+keeps: Bool, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session), +k: U32, +eh: {Tb.Table.has(S.Session, k, after) == True{} : Bool}) -> {N.Acts.touches(k, N.Gone.when(keeps, before, after)) == False{} : Bool}:
  match keeps:
    case True{}:
      {==}
    case False{}:
      Run.gone(before, after, k, eh)

def Run.has(+ss: Tb.Table(S.Session), +k: U32, +s: S.Session, +eg: {Tb.Table.get(S.Session, k, ss) == Some{s} : Maybe<&2, S.Session>}) -> {Tb.Table.has(S.Session, k, ss) == True{} : Bool}:
  seg = Equal.sym(Maybe<&2, S.Session>, Tb.Table.get(S.Session, k, ss), Some{s}, eg)
  (%seg : {Tb.Table.present(S.Session, _) == True{} : Bool}; {==})

def Run.step(+st: S.State, +o: N.GOut(), +k: U32, +hs: {N.Acts.touches(k, N.Out.acts(o)) == False{} : Bool}, +eh: {Tb.Table.has(S.Session, k, S.State.sessions(K.Kernel.state(N.Step.of(st, o)))) == True{} : Bool}) -> {N.Acts.touches(k, K.Kernel.actions(N.Step.of(st, o))) == False{} : Bool}:
  match o:
    case (+tx, +acts):
      Run.app(k, acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))), hs, Run.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)), k, eh))

def Run.join(+k: U32, +a: N.GOut(), +b: N.GOut(), +ha: {N.Acts.touches(k, N.Out.acts(a)) == False{} : Bool}, +hb: {N.Acts.touches(k, N.Out.acts(b)) == False{} : Bool}) -> {N.Acts.touches(k, N.Out.acts(N.Out.join(a, b))) == False{} : Bool}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          Run.app(k, aa, ab, ha, hb)

def Run.key_ne(+st: S.State, +key: U32, +k: U32, +c: Bool, +ec: {U32.is_eq(key, k) == c : Bool}, +hk: {PL.Lv.kept(st, key) == True{} : Bool}, +nk: {PL.Lv.kept(st, k) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      e1 = P.U32.eq_of_is_eq(key, k, ec)
      hk2 : {PL.Lv.kept(st, k) == True{} : Bool} = (%e1 : {PL.Lv.kept(st, _) == True{} : Bool}; hk)
      P.Bool.contra({True{} == False{} : Bool}, PL.Lv.kept(st, k), hk2, nk)
    case False{}:
      {==}

# A guard a Session Deletion starts, of another key.
def Run.start1(+u: Maybe<&2, U32>, +key: U32, +d: U32, +k: U32, +ne: {U32.is_eq(key, k) == False{} : Bool}) -> {N.Acts.touches(k, [N.TimerStart{u, key, d}]) == False{} : Bool}:
  sne = Equal.sym(Bool, U32.is_eq(key, k), False{}, ne)
  (%sne : {Bool.or(Bool.or(_, False{}), False{}) == False{} : Bool}; {==})

def Run.del_if(+st: S.State, +key: U32, +t: S.Session, +seq: U32, +more: Tb.Table(S.Session), +b: Bool, +k: U32, +hk: {PL.Lv.kept(st, key) == True{} : Bool}, +nk: {PL.Lv.kept(st, k) == False{} : Bool}, later: @q:U32 -> {N.Acts.touches(k, N.Out.acts(Up.N4.deletions(more, q))) == False{} : Bool}) -> {N.Acts.touches(k, N.Out.acts(Up.N4.delete_if(key, t, seq, q => Up.N4.deletions(more, q), b))) == False{} : Bool}:
  match b:
    case True{}:
      +request = Up.N4.delete(S.Session.up_seid(t), seq)
      Run.join(k, (S.Both{S.Revar{key, S.SVar{S.Session.up_seid(t), seq, S.Deleting{S.Guard{0}, request}}}, S.BumpSeq{1}}, [N.Pfcp{S.Session.tag(t), request}, N.TimerStart{None{}, key, Up.N4.t1_ms()}]), Up.N4.deletions(more, U32.add(seq, 1)), Run.start1(None{}, key, Up.N4.t1_ms(), k, Run.key_ne(st, key, k, U32.is_eq(key, k), {==}, hk, nk)), later(U32.add(seq, 1)))
    case False{}:
      Run.join(k, (S.DelSession{key}, []), Up.N4.deletions(more, seq), {==}, later(seq))

# Session Deletions of kept rows leave the guard of a key that is not kept alone.
def Run.dels(+st: S.State, +rows: Tb.Table(S.Session), +seq: U32, +k: U32, +hk: {PL.Lv.krows(rows, st) == True{} : Bool}, +nk: {PL.Lv.kept(st, k) == False{} : Bool}) -> {N.Acts.touches(k, N.Out.acts(Up.N4.deletions(rows, seq))) == False{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Run.del_if(st, key, t, seq, more, S.Session.known(t), k, P.Bool.and_true_l(PL.Lv.kept(st, key), PL.Lv.krows(more, st), hk), nk, +q => Run.dels(st, more, q, k, P.Bool.and_true_r(PL.Lv.kept(st, key), PL.Lv.krows(more, st), hk), nk))

def Run.sure_app(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {Run.sure(k, xs) == True{} : Bool}, +hy: {Run.sure(k, ys) == True{} : Bool}) -> {Run.sure(k, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      P.Bool.and_intro(Run.sure1(k, a), Run.sure(k, List.append(&2, N.Act, more, ys)), P.Bool.and_true_l(Run.sure1(k, a), Run.sure(k, more), hx), Run.sure_app(k, more, ys, P.Bool.and_true_r(Run.sure1(k, a), Run.sure(k, more), hx), hy))

def Run.sure_t1(+u: Maybe<&2, U32>, +key: U32, +k: U32, +c: Bool, +ec: {U32.is_eq(key, k) == c : Bool}) -> {Run.sure1(k, N.TimerStart{u, key, Up.N4.t1_ms()}) == True{} : Bool}:
  match c:
    case True{}:
      sec = Equal.sym(Bool, U32.is_eq(key, k), True{}, ec)
      (%sec : {Bool.and(True{}, Bool.or(Bool.not(_), Bool.and(_, U32.is_eq(Up.N4.t1_ms(), Up.N4.t1_ms())))) == True{} : Bool}; {==})
    case False{}:
      sec = Equal.sym(Bool, U32.is_eq(key, k), False{}, ec)
      (%sec : {Bool.and(True{}, Bool.or(Bool.not(_), Bool.and(_, U32.is_eq(Up.N4.t1_ms(), Up.N4.t1_ms())))) == True{} : Bool}; {==})

def Run.sure_join(+k: U32, +a: N.GOut(), +b: N.GOut(), +ha: {Run.sure(k, N.Out.acts(a)) == True{} : Bool}, +hb: {Run.sure(k, N.Out.acts(b)) == True{} : Bool}) -> {Run.sure(k, N.Out.acts(N.Out.join(a, b))) == True{} : Bool}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          Run.sure_app(k, aa, ab, ha, hb)

def Run.sure_del_if(+key: U32, +t: S.Session, +seq: U32, +more: Tb.Table(S.Session), +b: Bool, +k: U32, later: @q:U32 -> {Run.sure(k, N.Out.acts(Up.N4.deletions(more, q))) == True{} : Bool}) -> {Run.sure(k, N.Out.acts(Up.N4.delete_if(key, t, seq, q => Up.N4.deletions(more, q), b))) == True{} : Bool}:
  match b:
    case True{}:
      +request = Up.N4.delete(S.Session.up_seid(t), seq)
      +y : N.Act = N.TimerStart{None{}, key, Up.N4.t1_ms()}
      Run.sure_join(k, (S.Both{S.Revar{key, S.SVar{S.Session.up_seid(t), seq, S.Deleting{S.Guard{0}, request}}}, S.BumpSeq{1}}, [N.Pfcp{S.Session.tag(t), request}, y]), Up.N4.deletions(more, U32.add(seq, 1)), P.Bool.and_intro(Run.sure1(k, y), True{}, Run.sure_t1(None{}, key, k, U32.is_eq(key, k), {==}), {==}), later(U32.add(seq, 1)))
    case False{}:
      Run.sure_join(k, (S.DelSession{key}, []), Up.N4.deletions(more, seq), {==}, later(seq))

# Session Deletions start guards for T1 only.
def Run.dels_sure(+rows: Tb.Table(S.Session), +seq: U32, +k: U32) -> {Run.sure(k, N.Out.acts(Up.N4.deletions(rows, seq))) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Run.sure_del_if(key, t, seq, more, S.Session.known(t), k, +q => Run.dels_sure(more, q, k))

def Run.notes(+k: U32, +ok: Bool) -> {N.Acts.touches(k, Gsm.Gsm.deleted_notes(ok)) == False{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# A session being deleted, held
# -----------------------------
# Every outcome but its guard's and the UPF's answer to it changes or forgets
# only rows live in the state before the step and puts only sessions clear
# of it (PL.Lv.homed); with no two sessions sharing a key, its row stays. A
# UE procedure stops only a context's guard and starts only a context's, timer
# 0 or a kept row's (PL.Lv.reach), and the guards a step stops are of rows
# gone, so its guard is left alone.

def Hd.Q(+skey: U32, +s0: S.Session, o: N.Step()) -> Type:
  {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(o))) == Some{s0} : Maybe<&2, S.Session>} & {N.Acts.touches(skey, K.Kernel.actions(o)) == False{} : Bool}

def Hd.keep_head(+v: S.SSieve, +k: U32, +t: S.Session, +rest: Tb.Table(S.Session), +ek: {S.SSieve.keeps(v, k, t) == True{} : Bool}) -> {Tb.Table.get(S.Session, k, Tb.Table.keep(S.Session, k, t, S.Sessions.sift(v, rest), S.SSieve.keeps(v, k, t))) == Some{t} : Maybe<&2, S.Session>}:
  sek = Equal.sym(Bool, S.SSieve.keeps(v, k, t), True{}, ek)
  ser = Equal.sym(Bool, U32.is_eq(k, k), True{}, P.U32.is_eq_refl(k))
  (%sek : {Tb.Table.get(S.Session, k, Tb.Table.keep(S.Session, k, t, S.Sessions.sift(v, rest), _)) == Some{t} : Maybe<&2, S.Session>}; (%ser : {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, S.Sessions.sift(v, rest)), _) == Some{t} : Maybe<&2, S.Session>}; {==}))

def Hd.sift_row(+v: S.SSieve, +k: U32, +t: S.Session, +k1: U32, +t1: S.Session, +rest: Tb.Table(S.Session), +b: Bool, +eb: {U32.is_eq(k1, k) == b : Bool}, +eg: {Tb.Table.hit(S.Session, t1, Tb.Table.get(S.Session, k, rest), b) == Some{t} : Maybe<&2, S.Session>}, +ek: {S.SSieve.keeps(v, k, t) == True{} : Bool}, ih: {Tb.Table.get(S.Session, k, rest) == Some{t} : Maybe<&2, S.Session>} -> {Tb.Table.get(S.Session, k, S.Sessions.sift(v, rest)) == Some{t} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, k, Tb.Table.keep(S.Session, k1, t1, S.Sessions.sift(v, rest), S.SSieve.keeps(v, k1, t1))) == Some{t} : Maybe<&2, S.Session>}:
  match b:
    case True{}:
      se1 = Equal.sym(U32, k1, k, P.U32.eq_of_is_eq(k1, k, eb))
      set = Equal.sym(S.Session, t1, t, P.Some.inj(S.Session, t1, t, eg))
      (%se1 : {Tb.Table.get(S.Session, k, Tb.Table.keep(S.Session, _, t1, S.Sessions.sift(v, rest), S.SSieve.keeps(v, _, t1))) == Some{t} : Maybe<&2, S.Session>}; (%set : {Tb.Table.get(S.Session, k, Tb.Table.keep(S.Session, k, _, S.Sessions.sift(v, rest), S.SSieve.keeps(v, k, _))) == Some{t} : Maybe<&2, S.Session>}; Hd.keep_head(v, k, t, rest, ek)))
    case False{}:
      P.Keep.by(S.Session, tb => {Tb.Table.get(S.Session, k, tb) == Some{t} : Maybe<&2, S.Session>}, k1, t1, S.Sessions.sift(v, rest), S.SSieve.keeps(v, k1, t1), e => h => (%Equal.sym(Bool, U32.is_eq(k1, k), False{}, eb) : {Tb.Table.hit(S.Session, t1, Tb.Table.get(S.Session, k, S.Sessions.sift(v, rest)), _) == Some{t} : Maybe<&2, S.Session>}; h), ih(eg))

# A row a sieve keeps stays the row under its key.
def Hd.get_sift(+v: S.SSieve, ss: Tb.Table(S.Session), +k: U32, +t: S.Session, +eg: {Tb.Table.get(S.Session, k, ss) == Some{t} : Maybe<&2, S.Session>}, +ek: {S.SSieve.keeps(v, k, t) == True{} : Bool}) -> {Tb.Table.get(S.Session, k, S.Sessions.sift(v, ss)) == Some{t} : Maybe<&2, S.Session>}:
  match ss:
    case Nil{}:
      Empty.absurd({Tb.Table.get(S.Session, k, []) == Some{t} : Maybe<&2, S.Session>}, P.Refute.none_some(S.Session, t, eg))
    case (+k1, +t1) <> +rest:
      Hd.sift_row(v, k, t, k1, t1, rest, U32.is_eq(k1, k), {==}, eg, ek, e => Hd.get_sift(v, rest, k, t, e, ek))

def Hd.revar_row(+key: U32, +v: S.SVar, +k: U32, +t: S.Session, +k1: U32, +t1: S.Session, +rest: Tb.Table(S.Session), +b: Bool, +eb: {U32.is_eq(k1, k) == b : Bool}, +eg: {Tb.Table.hit(S.Session, t1, Tb.Table.get(S.Session, k, rest), b) == Some{t} : Maybe<&2, S.Session>}, +en: {Bool.and(U32.is_eq(k, key), S.SVar.follows(v, t)) == False{} : Bool}, ih: {Tb.Table.get(S.Session, k, rest) == Some{t} : Maybe<&2, S.Session>} -> {Tb.Table.get(S.Session, k, S.Sessions.revar(key, v, rest)) == Some{t} : Maybe<&2, S.Session>}) -> {Tb.Table.hit(S.Session, S.Session.revar_if(t1, v, Bool.and(U32.is_eq(k1, key), S.SVar.follows(v, t1))), Tb.Table.get(S.Session, k, S.Sessions.revar(key, v, rest)), U32.is_eq(k1, k)) == Some{t} : Maybe<&2, S.Session>}:
  match b:
    case True{}:
      seb = Equal.sym(Bool, U32.is_eq(k1, k), True{}, eb)
      se1 = Equal.sym(U32, k1, k, P.U32.eq_of_is_eq(k1, k, eb))
      set = Equal.sym(S.Session, t1, t, P.Some.inj(S.Session, t1, t, eg))
      sen = Equal.sym(Bool, Bool.and(U32.is_eq(k, key), S.SVar.follows(v, t)), False{}, en)
      (%seb : {Tb.Table.hit(S.Session, S.Session.revar_if(t1, v, Bool.and(U32.is_eq(k1, key), S.SVar.follows(v, t1))), Tb.Table.get(S.Session, k, S.Sessions.revar(key, v, rest)), _) == Some{t} : Maybe<&2, S.Session>}; (%se1 : {Some{S.Session.revar_if(t1, v, Bool.and(U32.is_eq(_, key), S.SVar.follows(v, t1)))} == Some{t} : Maybe<&2, S.Session>}; (%set : {Some{S.Session.revar_if(_, v, Bool.and(U32.is_eq(k, key), S.SVar.follows(v, _)))} == Some{t} : Maybe<&2, S.Session>}; (%sen : {Some{S.Session.revar_if(t, v, _)} == Some{t} : Maybe<&2, S.Session>}; {==}))))
    case False{}:
      seb = Equal.sym(Bool, U32.is_eq(k1, k), False{}, eb)
      (%seb : {Tb.Table.hit(S.Session, S.Session.revar_if(t1, v, Bool.and(U32.is_eq(k1, key), S.SVar.follows(v, t1))), Tb.Table.get(S.Session, k, S.Sessions.revar(key, v, rest)), _) == Some{t} : Maybe<&2, S.Session>}; ih(eg))

# A change in place that misses a row leaves it the row under its key.
def Hd.get_revar(+key: U32, +v: S.SVar, ss: Tb.Table(S.Session), +k: U32, +t: S.Session, +eg: {Tb.Table.get(S.Session, k, ss) == Some{t} : Maybe<&2, S.Session>}, +en: {Bool.and(U32.is_eq(k, key), S.SVar.follows(v, t)) == False{} : Bool}) -> {Tb.Table.get(S.Session, k, S.Sessions.revar(key, v, ss)) == Some{t} : Maybe<&2, S.Session>}:
  match ss:
    case Nil{}:
      Empty.absurd({Tb.Table.get(S.Session, k, []) == Some{t} : Maybe<&2, S.Session>}, P.Refute.none_some(S.Session, t, eg))
    case (+k1, +t1) <> +rest:
      Hd.revar_row(key, v, k, t, k1, t1, rest, U32.is_eq(k1, k), {==}, eg, en, e => Hd.get_revar(key, v, rest, k, t, e, en))

# The key of a row being deleted is no key kept.
def Hd.key_ne_if(+st0: S.State, +k: U32, +skey: U32, +s0: S.Session, +c: Bool, +ec: {U32.is_eq(skey, k) == c : Bool}, +ek: {PL.Lv.kept(st0, k) == True{} : Bool}, +eu: {S.Sessions.unique(S.State.sessions(st0)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st0)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +ss0 = S.State.sessions(st0)
      seu = Equal.sym(Bool, S.Sessions.unique(ss0), True{}, eu)
      +hk = P.Bool.or_true_l(PL.Lv.live_m(Tb.Table.get(S.Session, k, ss0)), Bool.not(S.Sessions.unique(ss0)), (%seu : {Bool.not(_) == False{} : Bool}; {==}), ek)
      se1 = Equal.sym(U32, skey, k, P.U32.eq_of_is_eq(skey, k, ec))
      hk2 : {PL.Lv.live_m(Tb.Table.get(S.Session, skey, ss0)) == True{} : Bool} = (%se1 : {PL.Lv.live_m(Tb.Table.get(S.Session, _, ss0)) == True{} : Bool}; hk)
      h3 : {PL.Lv.live_m(Some{s0}) == True{} : Bool} = (%e0 : {PL.Lv.live_m(_) == True{} : Bool}; hk2)
      P.Bool.contra({True{} == False{} : Bool}, S.SPhase.live(S.Session.phase(s0)), h3, eh)
    case False{}:
      {==}

def Hd.key_ne(+st0: S.State, +k: U32, +skey: U32, +s0: S.Session, +ek: {PL.Lv.kept(st0, k) == True{} : Bool}, +eu: {S.Sessions.unique(S.State.sessions(st0)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st0)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> {U32.is_eq(skey, k) == False{} : Bool}:
  Hd.key_ne_if(st0, k, skey, s0, U32.is_eq(skey, k), {==}, ek, eu, e0, eh)

def Hd.clear_at(+k: U32, +t: S.Session, +k1: U32, +t1: S.Session, +rest: Tb.Table(S.Session), +skey: U32, +s0: S.Session, +b: Bool, +eb: {U32.is_eq(k1, skey) == b : Bool}, +ec: {PL.Lv.clear(k, t, (k1, t1) <> rest) == True{} : Bool}, +eg: {Tb.Table.hit(S.Session, t1, Tb.Table.get(S.Session, skey, rest), b) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}, ih: {PL.Lv.clear(k, t, rest) == True{} : Bool} -> {Tb.Table.get(S.Session, skey, rest) == Some{s0} : Maybe<&2, S.Session>} -> {Bool.not(S.SRow.conflicts(k, t, skey, s0)) == True{} : Bool}) -> {Bool.not(S.SRow.conflicts(k, t, skey, s0)) == True{} : Bool}:
  match b:
    case True{}:
      +x = Bool.or(S.SPhase.live(S.Session.phase(t1)), Bool.not(S.SRow.conflicts(k, t, k1, t1)))
      e1 = P.U32.eq_of_is_eq(k1, skey, eb)
      et = P.Some.inj(S.Session, t1, s0, eg)
      hc : {Bool.or(S.SPhase.live(S.Session.phase(s0)), Bool.not(S.SRow.conflicts(k, t, skey, s0))) == True{} : Bool} = (%e1 : {Bool.or(S.SPhase.live(S.Session.phase(s0)), Bool.not(S.SRow.conflicts(k, t, _, s0))) == True{} : Bool}; (%et : {Bool.or(S.SPhase.live(S.Session.phase(_)), Bool.not(S.SRow.conflicts(k, t, k1, _))) == True{} : Bool}; P.Bool.and_true_l(x, PL.Lv.clear(k, t, rest), ec)))
      P.Bool.or_true_r(S.SPhase.live(S.Session.phase(s0)), Bool.not(S.SRow.conflicts(k, t, skey, s0)), eh, hc)
    case False{}:
      +x = Bool.or(S.SPhase.live(S.Session.phase(t1)), Bool.not(S.SRow.conflicts(k, t, k1, t1)))
      ih(P.Bool.and_true_r(x, PL.Lv.clear(k, t, rest), ec), eg)

# A session put clear of the sessions being deleted conflicts with none.
def Hd.clear_row(+k: U32, +t: S.Session, ss: Tb.Table(S.Session), +skey: U32, +s0: S.Session, +ec: {PL.Lv.clear(k, t, ss) == True{} : Bool}, +eg: {Tb.Table.get(S.Session, skey, ss) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> {Bool.not(S.SRow.conflicts(k, t, skey, s0)) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({Bool.not(S.SRow.conflicts(k, t, skey, s0)) == True{} : Bool}, P.Refute.none_some(S.Session, s0, eg))
    case (+k1, +t1) <> +rest:
      Hd.clear_at(k, t, k1, t1, rest, skey, s0, U32.is_eq(k1, skey), {==}, ec, eg, eh, e1 => e2 => Hd.clear_row(k, t, rest, skey, s0, e1, e2, eh))

# A session being deleted belongs to no UE.
def Hd.owned(+s0: S.Session, +ues: Tb.Table(S.Ue), +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> {S.Session.owned(s0, ues) == True{} : Bool}:
  seh = Equal.sym(Bool, S.SPhase.live(S.Session.phase(s0)), False{}, eh)
  (%seh : {Bool.or(Bool.not(Tb.Table.present(U32, Tb.Table.hit(U32, S.Session.ue(s0), None{}, _))), Tb.Table.has(S.Ue, S.Session.ue(s0), ues)) == True{} : Bool}; {==})

def Hd.others(+s0: S.Session, +key: U32, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> {Bool.not(S.Maybe.same_u32(S.Session.tag(s0), Some{key})) == True{} : Bool}:
  seh = Equal.sym(Bool, S.SPhase.live(S.Session.phase(s0)), False{}, eh)
  (%seh : {Bool.not(S.Maybe.same_u32(Tb.Table.hit(U32, S.Session.ue(s0), None{}, _), Some{key})) == True{} : Bool}; {==})

def Hd.miss_if(+st0: S.State, +key: U32, +v: S.SVar, +skey: U32, +s0: S.Session, +b: Bool, +ebv: {S.SPhase.live(S.SVar.phase(v)) == b : Bool}, +hs: {PL.Lv.spare(st0, key, v) == True{} : Bool}, +eu: {S.Sessions.unique(S.State.sessions(st0)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st0)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> {Bool.and(U32.is_eq(skey, key), S.SVar.follows(v, s0)) == False{} : Bool}:
  match b:
    case True{}:
      sev = Equal.sym(Bool, S.SPhase.live(S.SVar.phase(v)), True{}, ebv)
      seh = Equal.sym(Bool, S.SPhase.live(S.Session.phase(s0)), False{}, eh)
      (%sev : {Bool.and(U32.is_eq(skey, key), Bool.or(Bool.not(_), S.SPhase.live(S.Session.phase(s0)))) == False{} : Bool}; (%seh : {Bool.and(U32.is_eq(skey, key), _) == False{} : Bool}; PL.Lv.and_false(U32.is_eq(skey, key))))
    case False{}:
      sne = Equal.sym(Bool, U32.is_eq(skey, key), False{}, Hd.key_ne(st0, key, skey, s0, P.Bool.or_true_r(S.SPhase.live(S.SVar.phase(v)), PL.Lv.kept(st0, key), ebv, hs), eu, e0, eh))
      (%sne : {Bool.and(_, S.SVar.follows(v, s0)) == False{} : Bool}; {==})

def Hd.except(+skey: U32, +key: U32, +ne: {U32.is_eq(skey, key) == False{} : Bool}) -> {Bool.not(U32.is_eq(skey, key)) == True{} : Bool}:
  sne = Equal.sym(Bool, U32.is_eq(skey, key), False{}, ne)
  (%sne : {Bool.not(_) == True{} : Bool}; {==})

def Hd.put_ne(+key: U32, +t: S.Session, +skey: U32, +s0: S.Session, +nc: {Bool.not(S.SRow.conflicts(key, t, skey, s0)) == True{} : Bool}) -> {U32.is_eq(key, skey) == False{} : Bool}:
  PL.Lv.u32_ne(key, skey, P.Bool.or_false_l(U32.is_eq(skey, key), S.Session.conflicts(t, s0), P.Bool.not_true(S.SRow.conflicts(key, t, skey, s0), nc)))

def Hd.put_get(+key: U32, +t: S.Session, +ss: Tb.Table(S.Session), +skey: U32, +s0: S.Session, +nc: {Bool.not(S.SRow.conflicts(key, t, skey, s0)) == True{} : Bool}, +eg: {Tb.Table.get(S.Session, skey, ss) == Some{s0} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, skey, S.Sessions.put(key, t, ss)) == Some{s0} : Maybe<&2, S.Session>}:
  sne = Equal.sym(Bool, U32.is_eq(key, skey), False{}, Hd.put_ne(key, t, skey, s0, nc))
  (%sne : {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, skey, S.Sessions.sift(S.SClear{key, t}, ss)), _) == Some{s0} : Maybe<&2, S.Session>}; Hd.get_sift(S.SClear{key, t}, ss, skey, s0, eg, nc))

# A transaction homed in st0 leaves a session being deleted in st0 as it was.
def Hd.apply(+st0: S.State, tx: S.Tx, +ues: Tb.Table(S.Ue), +st: S.State, +skey: U32, +s0: S.Session, +h: {PL.Lv.homed(st0, tx, ues) == True{} : Bool}, +eu: {S.Sessions.unique(S.State.sessions(st0)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st0)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}, +eg: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, skey, S.State.sessions(S.Tx.apply(tx, st))) == Some{s0} : Maybe<&2, S.Session>}:
  match tx:
    case S.Keep{}:
      eg
    case S.Put{+key, +ue}:
      match st:
        case S.State{config, subs, assocs, +us, +sessions, pfcp_seq, next_ue, n4}:
          Hd.get_sift(S.SOwned{S.Ues.put(key, ue, us)}, sessions, skey, s0, eg, Hd.owned(s0, S.Ues.put(key, ue, us), eh))
    case S.Rephase{key, phase}:
      match st:
        case S.State{config, subs, assocs, us, sessions, pfcp_seq, next_ue, n4}:
          eg
    case S.Del{+key}:
      match st:
        case S.State{config, subs, assocs, us, +sessions, pfcp_seq, next_ue, n4}:
          Hd.get_sift(S.SOthers{key}, sessions, skey, s0, eg, Hd.others(s0, key, eh))
    case S.PutSession{+key, +t}:
      match st:
        case S.State{config, subs, assocs, us, +sessions, pfcp_seq, next_ue, n4}:
          Hd.put_get(key, t, sessions, skey, s0, Hd.clear_row(key, t, S.State.sessions(st0), skey, s0, P.Bool.and_true_l(PL.Lv.clear(key, t, S.State.sessions(st0)), PL.Lv.puts(key, t, ues), h), e0, eh), eg)
    case S.Revar{+key, +v}:
      match st:
        case S.State{config, subs, assocs, us, +sessions, pfcp_seq, next_ue, n4}:
          Hd.get_revar(key, v, sessions, skey, s0, eg, Hd.miss_if(st0, key, v, skey, s0, S.SPhase.live(S.SVar.phase(v)), {==}, P.Bool.and_true_l(PL.Lv.spare(st0, key, v), PL.Lv.revar_ok(st0, v), h), eu, e0, eh))
    case S.DelSession{+key}:
      match st:
        case S.State{config, subs, assocs, us, +sessions, pfcp_seq, next_ue, n4}:
          Hd.get_sift(S.SExcept{key}, sessions, skey, s0, eg, Hd.except(skey, key, Hd.key_ne(st0, key, skey, s0, h, eu, e0, eh)))
    case S.Subs{new}:
      match st:
        case S.State{config, subs, assocs, us, sessions, pfcp_seq, next_ue, n4}:
          eg
    case S.SetLink{link}:
      match st:
        case S.State{config, subs, assocs, us, sessions, pfcp_seq, next_ue, n4}:
          eg
    case S.BumpUe{bk}:
      match st:
        case S.State{config, subs, assocs, us, sessions, pfcp_seq, next_ue, n4}:
          eg
    case S.BumpSeq{n}:
      match st:
        case S.State{config, subs, assocs, us, sessions, pfcp_seq, next_ue, n4}:
          eg
    case S.Both{+a, +b}:
      Hd.apply(st0, b, PT.Tk.ues(a, ues), S.Tx.apply(a, st), skey, s0, P.Bool.and_true_r(PL.Lv.homed(st0, a, ues), PL.Lv.homed(st0, b, PT.Tk.ues(a, ues)), h), eu, e0, eh, Hd.apply(st0, a, ues, st, skey, s0, P.Bool.and_true_l(PL.Lv.homed(st0, a, ues), PL.Lv.homed(st0, b, PT.Tk.ues(a, ues)), h), eu, e0, eh, eg))

def Hd.row(+skey: U32, +s0: S.Session, -o: N.Step(), q: Hd.Q(skey, s0, o)) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(o))) == Some{s0} : Maybe<&2, S.Session>}:
  match q:
    case (a, b):
      a

def Hd.running(+skey: U32, +s0: S.Session, -o: N.Step(), q: Hd.Q(skey, s0, o)) -> {N.Acts.touches(skey, K.Kernel.actions(o)) == False{} : Bool}:
  match q:
    case (a, b):
      b

# What a UE procedure's outcome does keeps a session being deleted, its row
# and its guard.
# The row under skey being deleted is not kept.
def Hd.unkept(+st: S.State, +skey: U32, +s0: S.Session, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> {PL.Lv.kept(st, skey) == False{} : Bool}:
  +ss = S.State.sessions(st)
  se0 = Equal.sym(Maybe<&2, S.Session>, Tb.Table.get(S.Session, skey, ss), Some{s0}, e0)
  seu = Equal.sym(Bool, S.Sessions.unique(ss), True{}, eu)
  (%se0 : {Bool.or(PL.Lv.live_m(_), Bool.not(S.Sessions.unique(ss))) == False{} : Bool}; (%seu : {Bool.or(S.SPhase.live(S.Session.phase(s0)), Bool.not(_)) == False{} : Bool}; P.Bool.or_false(S.SPhase.live(S.Session.phase(s0)), False{}, eh, {==})))

def Hd.of(+st: S.State, +o: N.GOut(), +skey: U32, +s0: S.Session, +hh: {PL.Lv.homed(st, N.Out.tx(o), S.State.ues(st)) == True{} : Bool}, +hs: {N.Acts.touches(skey, N.Out.acts(o)) == False{} : Bool}, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> Hd.Q(skey, s0, N.Step.of(st, o)):
  match o:
    case (+tx, +acts):
      +e1 = Hd.apply(st, tx, S.State.ues(st), st, skey, s0, hh, eu, e0, eh, e0)
      (e1, Run.step(st, (tx, acts), skey, hs, Run.has(S.State.sessions(S.Tx.apply(tx, st)), skey, s0, e1)))

def Hd.step_of(+st: S.State, +o: N.GOut(), +skey: U32, +s0: S.Session, +h: {PL.Lv.ok(st, o) == True{} : Bool}, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +ef: {Run.free(st, skey) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> Hd.Q(skey, s0, N.Step.of(st, o)):
  Hd.of(st, o, skey, s0, PL.Lv.ok_homed(st, o, h), Run.quiet(st, skey, N.Out.acts(o), Run.acts(st, skey, N.Out.acts(o), ef, PL.Lv.ok_acts(st, o, h)), Hd.unkept(st, skey, s0, eu, e0, eh)), eu, e0, eh)

# An association's contexts going: their sessions are live, and one being
# deleted belongs to no UE, so it stays; the deletions start guards only.
def Hd.drop(+st: S.State, +assoc: U32, +skey: U32, +s0: S.Session, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> Hd.Q(skey, s0, R.Route.drop(st, assoc)):
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s1 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      +left = S.Ues.drop_assoc(assoc, ues)
      +gone = S.Sessions.sift(S.SOrphan{left}, sessions)
      +d = Up.N4.deletions(gone, pfcp_seq)
      +hd = PL.Lv.dels(s1, gone, pfcp_seq, PL.Lv.srows_sift(S.SOrphan{left}, sessions), PL.Lv.krows_orphan(s1, left))
      +hh = PL.Lv.free_homed(s1, N.Out.tx(d), ues, PL.Lv.okf_free(s1, d, hd))
      +e1 = Hd.apply(s1, N.Out.tx(d), ues, s1, skey, s0, hh, eu, e0, eh, e0)
      +kept = S.Sessions.sift(S.SOwned{left}, S.State.sessions(S.Tx.apply(N.Out.tx(d), s1)))
      +e2 = Hd.get_sift(S.SOwned{left}, S.State.sessions(S.Tx.apply(N.Out.tx(d), s1)), skey, s0, e1, Hd.owned(s0, left, eh))
      (e2, Run.app(skey, N.Out.acts(d), N.Gone.cancels(sessions, kept), Run.dels(s1, gone, pfcp_seq, skey, PL.Lv.krows_orphan(s1, left), Hd.unkept(s1, skey, s0, eu, e0, eh)), Run.gone(sessions, kept, skey, Run.has(kept, skey, s0, e2))))

def Hd.ready(+st: S.State, +assoc: U32, +id: B.Bytes(), +ok: Bool, +acts: List<&2, N.Act>, +skey: U32, +s0: S.Session, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}, +hc: {N.Acts.touches(skey, acts) == False{} : Bool}) -> Hd.Q(skey, s0, (S.State.ready(N.Step.state(R.Route.drop(st, assoc)), assoc, id, ok), List.append(&2, N.Act, N.Step.acts(R.Route.drop(st, assoc)), acts))):
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s1 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      (Hd.row(skey, s0, R.Route.drop(s1, assoc), Hd.drop(s1, assoc, skey, s0, eu, e0, eh)), Run.app(skey, N.Step.acts(R.Route.drop(s1, assoc)), acts, Hd.running(skey, s0, R.Route.drop(s1, assoc), Hd.drop(s1, assoc, skey, s0, eu, e0, eh)), hc))

def Hd.down(+st: S.State, +assoc: U32, +skey: U32, +s0: S.Session, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +ef: {Run.free(st, skey) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> Hd.Q(skey, s0, R.Route.down(st, assoc)):
  +o1 = N.Step.of(st, Ho.Ho.down(st, assoc))
  +s1 = K.Kernel.state(o1)
  +ess = Equal.sym(Tb.Table(S.Session), S.State.sessions(s1), S.State.sessions(st), PL.Lw.down_sessions(st, assoc))
  h1 = Hd.running(skey, s0, o1, Hd.step_of(st, Ho.Ho.down(st, assoc), skey, s0, PL.Lw.ho_down(st, assoc), eu, ef, e0, eh))
  +eu1 : {S.Sessions.unique(S.State.sessions(s1)) == True{} : Bool} = (%ess : {S.Sessions.unique(_) == True{} : Bool}; eu)
  +e1 : {Tb.Table.get(S.Session, skey, S.State.sessions(s1)) == Some{s0} : Maybe<&2, S.Session>} = (%ess : {Tb.Table.get(S.Session, skey, _) == Some{s0} : Maybe<&2, S.Session>}; e0)
  (Hd.row(skey, s0, R.Route.drop(s1, assoc), Hd.drop(s1, assoc, skey, s0, eu1, e1, eh)), Run.app(skey, K.Kernel.actions(o1), N.Note{F.Info{}, "NGAP: association down; its UE contexts and sessions released"} <> K.Kernel.actions(R.Route.drop(s1, assoc)), h1, Hd.running(skey, s0, R.Route.drop(s1, assoc), Hd.drop(s1, assoc, skey, s0, eu1, e1, eh))))

def Hd.config(+complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), +skey: U32, +s0: S.Session, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}, +ez: {U32.is_eq(skey, S.N4.timer()) == False{} : Bool}) -> Hd.Q(skey, s0, K.Kernel.config(complete, st, tlvs, entropy)):
  match complete:
    case False{}:
      (e0, {==})
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          +cfg = S.Cfg.of(tlvs)
          +st2 : S.State = S.State{Some{cfg}, Au.Subscribers.of(S.Cfg.subscribers(cfg)), assocs, ues, sessions, pfcp_seq, next_ue, S.N4{List.take(&2, U32, entropy, 4n), S.Idle{}}}
          +o = N.Out.also(Up.N4.start(st2), [N.Note{F.Info{}, "Config: loaded; PFCP association requested"}])
          +ne = Equal.trans(Bool, U32.is_eq(S.N4.timer(), skey), U32.is_eq(skey, S.N4.timer()), False{}, P.U32.sym(S.N4.timer(), skey), ez)
          Hd.of(st2, o, skey, s0, {==}, Run.start1(None{}, S.N4.timer(), Up.N4.t1_ms(), skey, ne), eu, e0, eh)

# A change or deletion of another key leaves the row under skey.
def Hd.revar_ne(+st: S.State, +k: U32, +v: S.SVar, +acts: List<&2, N.Act>, +skey: U32, +s0: S.Session, +ne: {U32.is_eq(skey, k) == False{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +hs: {N.Acts.touches(skey, acts) == False{} : Bool}) -> Hd.Q(skey, s0, N.Step.of(st, (S.Revar{k, v}, acts))):
  match st:
    case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
      sne = Equal.sym(Bool, U32.is_eq(skey, k), False{}, ne)
      (Hd.get_revar(k, v, sessions, skey, s0, e0, (%sne : {Bool.and(_, S.SVar.follows(v, s0)) == False{} : Bool}; {==})), Run.app(skey, acts, [], hs, {==}))

def Hd.del_ne(+st: S.State, +k: U32, +acts: List<&2, N.Act>, +skey: U32, +s0: S.Session, +ne: {U32.is_eq(skey, k) == False{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +hs: {N.Acts.touches(skey, acts) == False{} : Bool}) -> Hd.Q(skey, s0, N.Step.of(st, (S.DelSession{k}, acts))):
  match st:
    case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
      +e1 = Hd.get_sift(S.SExcept{k}, sessions, skey, s0, e0, Hd.except(skey, k, ne))
      (e1, Run.app(skey, acts, N.Gone.cancels(sessions, S.Sessions.sift(S.SExcept{k}, sessions)), hs, Run.gone(sessions, S.Sessions.sift(S.SExcept{k}, sessions), skey, Run.has(S.Sessions.sift(S.SExcept{k}, sessions), skey, s0, e1))))

# Another session's guard
# -----------------------

def Hd.resent(+st: S.State, +k: U32, +t: S.Session, +p: S.SPhase, +request: B.Bytes(), +more: Bool, +skey: U32, +s0: S.Session, +ne: {U32.is_eq(skey, k) == False{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}) -> Hd.Q(skey, s0, N.Step.of(st, Gsm.Gsm.resend_if(k, t, p, request, (S.DelSession{k}, [N.Note{F.Warn{}, "PFCP: no Session Deletion Response; deletion given up"}]), more))):
  match more:
    case True{}:
      Hd.revar_ne(st, k, S.SVar{S.Session.up_seid(t), S.Session.seq(t), p}, [N.Pfcp{S.Session.tag(t), request}, N.TimerStart{S.Session.tag(t), k, Up.N4.t1_ms()}], skey, s0, ne, e0, Run.start1(S.Session.tag(t), k, Up.N4.t1_ms(), skey, PL.Lv.u32_ne(k, skey, ne)))
    case False{}:
      Hd.del_ne(st, k, [N.Note{F.Warn{}, "PFCP: no Session Deletion Response; deletion given up"}], skey, s0, ne, e0, {==})

def Hd.timer_ne(-ev: F.Evt, +k: U32, +skey: U32, +c: Bool, +ec: {U32.is_eq(skey, k) == c : Bool}, +ek: {ev == F.TimerFired{k} : F.Evt}, et: {ev == F.TimerFired{skey} : F.Evt} -> Empty) -> {c == False{} : Bool}:
  match c:
    case True{}:
      e1 = P.U32.eq_of_is_eq(skey, k, ec)
      se1 = Equal.sym(U32, skey, k, e1)
      Empty.absurd({True{} == False{} : Bool}, et((%se1 : {ev == F.TimerFired{_} : F.Evt}; ek)))
    case False{}:
      {==}

# A Session Deletion Response for another session
# -----------------------------------------------
def Hd.seq_ne_if(+st: S.State, +k: U32, +t: S.Session, +skey: U32, +s0: S.Session, +c: Bool, +ec: {U32.is_eq(skey, k) == c : Bool}, g: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool} -> {Tb.Table.get(S.Session, k, S.State.sessions(st)) == Some{t} : Maybe<&2, S.Session>}, nb: {Some{(k, t)} == Some{(skey, s0)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>} -> Empty, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +ss = S.State.sessions(st)
      +e1 = P.U32.eq_of_is_eq(skey, k, ec)
      e0k : {Tb.Table.get(S.Session, k, ss) == Some{s0} : Maybe<&2, S.Session>} = (%e1 : {Tb.Table.get(S.Session, _, ss) == Some{s0} : Maybe<&2, S.Session>}; e0)
      +gk = g(eu)
      ets = P.Some.inj(S.Session, t, s0, Equal.trans(Maybe<&2, S.Session>, Some{t}, Tb.Table.get(S.Session, k, ss), Some{s0}, Equal.sym(Maybe<&2, S.Session>, Tb.Table.get(S.Session, k, ss), Some{t}, gk), e0k))
      se1 = Equal.sym(U32, skey, k, e1)
      Empty.absurd({True{} == False{} : Bool}, nb((%se1 : {Some{(k, t)} == Some{(_, s0)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}; (%ets : {Some{(k, t)} == Some{(k, _)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}; {==}))))
    case False{}:
      {==}

def Hd.deleted_phase(+st: S.State, +k: U32, +msg: Pf.Msg, +p: S.SPhase, +skey: U32, +s0: S.Session, +ne: {U32.is_eq(skey, k) == False{} : Bool}, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> Hd.Q(skey, s0, N.Step.of(st, Gsm.Gsm.deleted_phase(k, msg, p))):
  match p:
    case S.Creating{guard, pti, accept, request}:
      (e0, {==})
    case S.Setting{guard, pti}:
      (e0, {==})
    case S.Modifying{guard, request}:
      (e0, {==})
    case S.Repointing{guard, request}:
      (e0, {==})
    case S.Deleting{guard, request}:
      Hd.del_ne(st, k, Gsm.Gsm.deleted_notes(Up.N4.accepted(Up.N4.cause(msg))), skey, s0, ne, e0, Run.notes(skey, Up.N4.accepted(Up.N4.cause(msg))))
    case S.Active{}:
      (e0, {==})

def Hd.deleted(+st: S.State, +skey: U32, +s0: S.Session, +msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, g: PL.Lv.Got(m, S.State.sessions(st)), nb: {m == Some{(skey, s0)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>} -> Empty, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> Hd.Q(skey, s0, N.Step.of(st, Gsm.Gsm.deleted(msg, m))):
  match m:
    case None{}:
      (e0, {==})
    case Some{(+k, +t)}:
      Hd.deleted_phase(st, k, msg, S.Session.phase(t), skey, s0, Hd.seq_ne_if(st, k, t, skey, s0, U32.is_eq(skey, k), {==}, g, nb, eu, e0), eu, e0, eh)

def Hd.unlive(+s: S.Session, +guard: S.Guard, +request: B.Bytes(), +ep: {S.Session.phase(s) == S.Deleting{guard, request} : S.SPhase}) -> {S.SPhase.live(S.Session.phase(s)) == False{} : Bool}:
  sep = Equal.sym(S.SPhase, S.Session.phase(s), S.Deleting{guard, request}, ep)
  (%sep : {S.SPhase.live(_) == False{} : Bool}; {==})

# A session the UPF settles is another: its row is live.
def Hd.settled(+st: S.State, +k: U32, +tx: S.Tx, +more: List<&2, N.Act>, +ek: {PL.Lv.kept(st, k) == True{} : Bool}, +h: {PL.Lv.ok(st, (tx, more)) == True{} : Bool}, +skey: U32, +s0: S.Session, +eu: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}, +ef: {Run.free(st, skey) == True{} : Bool}, +e0: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s0} : Maybe<&2, S.Session>}, +eh: {S.SPhase.live(S.Session.phase(s0)) == False{} : Bool}) -> Hd.Q(skey, s0, N.Step.of(st, (tx, N.TimerCancel{k} <> more))):
  +ne = PL.Lv.u32_ne(k, skey, Hd.key_ne(st, k, skey, s0, ek, eu, e0, eh))
  Hd.of(st, (tx, N.TimerCancel{k} <> more), skey, s0, PL.Lv.ok_homed(st, (tx, more), h), P.Bool.or_false(U32.is_eq(k, skey), N.Acts.touches(skey, more), ne, Run.quiet(st, skey, more, Run.acts(st, skey, more, ef, PL.Lv.ok_acts(st, (tx, more), h)), Hd.unkept(st, skey, s0, eu, e0, eh))), eu, e0, eh)

def L.smf.deletion.held(st, ev, entropy, skey, s, guard, request, eu, en, ef, ez, es, ep, et, ea):
  +eh = Hd.unlive(s, guard, request, ep)
  PL.Dw.walk(o => Hd.Q(skey, s, o), o => Hd.Q(skey, s, N.Step.of(st, o)), st, ev, entropy, acts => h => c => nr => (es, c(skey)), +assoc => ns => +id => +ok => +acts => h => c => ers => Hd.ready(st, assoc, id, ok, acts, skey, s, eu, es, eh, c(skey)), +tlvs => Hd.config(S.Cfg.complete(tlvs), st, tlvs, entropy, skey, s, eu, es, eh, ez), +assoc => Hd.down(st, assoc, skey, s, eu, Run.free_of(st, skey, en, ef, ez), es, eh), o => h => h, +o => +h => Hd.step_of(st, o, skey, s, h, eu, Run.free_of(st, skey, en, ef, ez), es, eh), +k => +t => +g => +r => ek => eu2 => em => ep2 => Hd.resent(st, k, t, S.Deleting{S.Guard{U32.add(S.Guard.retries(g), 1)}, r}, r, U32.is_lt(S.Guard.retries(g), Up.N4.n1()), skey, s, Hd.timer_ne(ev, k, skey, U32.is_eq(skey, k), {==}, ek, et), es), +len => +bytes => +msg => +rest => ev2 => er => ek => Hd.deleted(st, skey, s, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), PL.Lv.got_by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), e => ea(len, bytes, msg, rest, ev2, er, ek, e), eu, es, eh), +k => +tx => +more => ek => ehs => h => Hd.settled(st, k, tx, more, ek, h, skey, s, eu, Run.free_of(st, skey, en, ef, ez), es, eh))

# A session that starts being deleted, armed
# ------------------------------------------
# Every row under skey is live, or being deleted under a guard that has not
# fired, its request sent and timer skey running for T1 once the actions are
# done (Ar.rows). Where no row under skey is being deleted before the step and
# skey is free (Run.free), every outcome keeps it so: a UE procedure starts
# every deletion it makes with its request and its guard for T1 (PL.Lv.arms),
# stops no session's guard and starts one only for T1 (Run.sure), and the
# guards a step stops are of rows gone (N.Gone.cancels). Ar.rows is a fold of
# its own rather than S.Sessions.each: what it asks of a row depends on the
# step's actions, which state.bend cannot name.

def Ar.row(+k: U32, +acts: List<&2, N.Act>, p: S.SPhase) -> Bool:
  match p:
    case S.Deleting{guard, +request}:
      Bool.and(U32.is_eq(S.Guard.retries(guard), 0), Bool.and(N.Acts.sends(request, acts), N.Acts.runs(k, Up.N4.t1_ms(), acts)))
    case _:
      True{}

def Ar.rows(+k: U32, +acts: List<&2, N.Act>, ss: Tb.Table(S.Session)) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case (+k0, +t) <> more:
      Bool.and(Bool.or(Bool.not(U32.is_eq(k0, k)), Ar.row(k, acts, S.Session.phase(t))), Ar.rows(k, acts, more))

def Ar.Q(+k: U32, o: N.Step()) -> Type:
  {Tb.Table.has(S.Session, k, S.State.sessions(K.Kernel.state(o))) == True{} : Bool} -> {Ar.rows(k, K.Kernel.actions(o), S.State.sessions(K.Kernel.state(o))) == True{} : Bool}

# Timer k runs for T1
# -------------------

def Ar.quiet1(+k: U32, +a: N.Act, +hs: {Run.sure1(k, a) == True{} : Bool}, +hf: {N.Act.starts_for(k, Up.N4.t1_ms(), a) == False{} : Bool}) -> {Bool.or(N.Act.starts(k, a), N.Act.stops(k, a)) == False{} : Bool}:
  +sf = N.Act.starts_for(k, Up.N4.t1_ms(), a)
  +so = P.Bool.not_true(N.Act.stops(k, a), P.Bool.and_true_l(Bool.not(N.Act.stops(k, a)), Bool.or(Bool.not(N.Act.starts(k, a)), sf), hs))
  +sa = P.Bool.not_true(N.Act.starts(k, a), P.Bool.or_true_l(Bool.not(N.Act.starts(k, a)), sf, hf, P.Bool.and_true_r(Bool.not(N.Act.stops(k, a)), Bool.or(Bool.not(N.Act.starts(k, a)), sf), hs)))
  P.Bool.or_false(N.Act.starts(k, a), N.Act.stops(k, a), sa, so)

# Actions that never start timer k for T1, and start it for nothing else nor stop it, leave it alone.
def Ar.quiet(+k: U32, +xs: List<&2, N.Act>, +hs: {Run.sure(k, xs) == True{} : Bool}, +hf: {N.Acts.starts_for(k, Up.N4.t1_ms(), xs) == False{} : Bool}) -> {N.Acts.touches(k, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +more:
      +sf = N.Act.starts_for(k, Up.N4.t1_ms(), a)
      P.Bool.or_false(Bool.or(N.Act.starts(k, a), N.Act.stops(k, a)), N.Acts.touches(k, more), Ar.quiet1(k, a, P.Bool.and_true_l(Run.sure1(k, a), Run.sure(k, more), hs), P.Bool.or_false_l(sf, N.Acts.starts_for(k, Up.N4.t1_ms(), more), hf)), Ar.quiet(k, more, P.Bool.and_true_r(Run.sure1(k, a), Run.sure(k, more), hs), P.Bool.or_false_r(sf, N.Acts.starts_for(k, Up.N4.t1_ms(), more), hf)))

def Ar.runs_if(+k: U32, +a: N.Act, +more: List<&2, N.Act>, +c: Bool, +ec: {N.Acts.starts_for(k, Up.N4.t1_ms(), more) == c : Bool}, +hs: {Bool.or(N.Act.starts_for(k, Up.N4.t1_ms(), a), c) == True{} : Bool}, +hn: {Run.sure(k, more) == True{} : Bool}, ih: {N.Acts.starts_for(k, Up.N4.t1_ms(), more) == True{} : Bool} -> {N.Acts.runs(k, Up.N4.t1_ms(), more) == True{} : Bool}) -> {N.Acts.runs(k, Up.N4.t1_ms(), a <> more) == True{} : Bool}:
  match c:
    case True{}:
      P.Bool.or_l(N.Acts.runs(k, Up.N4.t1_ms(), more), Bool.and(N.Act.starts_for(k, Up.N4.t1_ms(), a), Bool.not(N.Acts.touches(k, more))), ih(ec))
    case False{}:
      stm = Equal.sym(Bool, N.Acts.touches(k, more), False{}, Ar.quiet(k, more, hn, ec))
      P.Bool.or_r(N.Acts.runs(k, Up.N4.t1_ms(), more), Bool.and(N.Act.starts_for(k, Up.N4.t1_ms(), a), Bool.not(N.Acts.touches(k, more))), P.Bool.and_intro(N.Act.starts_for(k, Up.N4.t1_ms(), a), Bool.not(N.Acts.touches(k, more)), P.Bool.or_true_l(N.Act.starts_for(k, Up.N4.t1_ms(), a), False{}, {==}, hs), (%stm : {Bool.not(_) == True{} : Bool}; {==})))

# Actions that start timer k for T1, and start it for nothing else nor stop
# it, leave it running for T1.
def Ar.runs_of(+k: U32, +xs: List<&2, N.Act>, +hs: {N.Acts.starts_for(k, Up.N4.t1_ms(), xs) == True{} : Bool}, +hn: {Run.sure(k, xs) == True{} : Bool}) -> {N.Acts.runs(k, Up.N4.t1_ms(), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({N.Acts.runs(k, Up.N4.t1_ms(), []) == True{} : Bool}, P.Refute.bool(hs))
    case +a <> +more:
      +hm = P.Bool.and_true_r(Run.sure1(k, a), Run.sure(k, more), hn)
      Ar.runs_if(k, a, more, N.Acts.starts_for(k, Up.N4.t1_ms(), more), {==}, hs, hm, e => Ar.runs_of(k, more, e, hm))

def Ar.runs_r(+k: U32, +ms: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.runs(k, ms, ys) == True{} : Bool}) -> {N.Acts.runs(k, ms, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +a <> +more:
      P.Bool.or_l(N.Acts.runs(k, ms, List.append(&2, N.Act, more, ys)), Bool.and(N.Act.starts_for(k, ms, a), Bool.not(N.Acts.touches(k, List.append(&2, N.Act, more, ys)))), Ar.runs_r(k, ms, more, ys, h))

def Ar.runs_lif(+k: U32, +ms: U32, +a: N.Act, +more: List<&2, N.Act>, +ys: List<&2, N.Act>, +c: Bool, +ec: {N.Acts.runs(k, ms, more) == c : Bool}, +h: {Bool.or(c, Bool.and(N.Act.starts_for(k, ms, a), Bool.not(N.Acts.touches(k, more)))) == True{} : Bool}, +hn: {N.Acts.touches(k, ys) == False{} : Bool}, ih: {N.Acts.runs(k, ms, more) == True{} : Bool} -> {N.Acts.runs(k, ms, List.append(&2, N.Act, more, ys)) == True{} : Bool}) -> {N.Acts.runs(k, ms, a <> List.append(&2, N.Act, more, ys)) == True{} : Bool}:
  match c:
    case True{}:
      P.Bool.or_l(N.Acts.runs(k, ms, List.append(&2, N.Act, more, ys)), Bool.and(N.Act.starts_for(k, ms, a), Bool.not(N.Acts.touches(k, List.append(&2, N.Act, more, ys)))), ih(ec))
    case False{}:
      +sa = P.Bool.and_true_l(N.Act.starts_for(k, ms, a), Bool.not(N.Acts.touches(k, more)), h)
      +sm = P.Bool.not_true(N.Acts.touches(k, more), P.Bool.and_true_r(N.Act.starts_for(k, ms, a), Bool.not(N.Acts.touches(k, more)), h))
      szs = Equal.sym(Bool, N.Acts.touches(k, List.append(&2, N.Act, more, ys)), False{}, Run.app(k, more, ys, sm, hn))
      P.Bool.or_r(N.Acts.runs(k, ms, List.append(&2, N.Act, more, ys)), Bool.and(N.Act.starts_for(k, ms, a), Bool.not(N.Acts.touches(k, List.append(&2, N.Act, more, ys)))), P.Bool.and_intro(N.Act.starts_for(k, ms, a), Bool.not(N.Acts.touches(k, List.append(&2, N.Act, more, ys))), sa, (%szs : {Bool.not(_) == True{} : Bool}; {==})))

def Ar.runs_l(+k: U32, +ms: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.runs(k, ms, xs) == True{} : Bool}, +hn: {N.Acts.touches(k, ys) == False{} : Bool}) -> {N.Acts.runs(k, ms, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({N.Acts.runs(k, ms, ys) == True{} : Bool}, P.Refute.bool(h))
    case +a <> +more:
      Ar.runs_lif(k, ms, a, more, ys, N.Acts.runs(k, ms, more), {==}, h, hn, e => Ar.runs_l(k, ms, more, ys, e, hn))

# More actions
# ------------

def Ar.row_r(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +p: S.SPhase, +h: {Ar.row(k, ys, p) == True{} : Bool}) -> {Ar.row(k, List.append(&2, N.Act, xs, ys), p) == True{} : Bool}:
  match p:
    case S.Deleting{+guard, +request}:
      +z = U32.is_eq(S.Guard.retries(guard), 0)
      +r = P.Bool.and_true_r(z, Bool.and(N.Acts.sends(request, ys), N.Acts.runs(k, Up.N4.t1_ms(), ys)), h)
      P.Bool.and_intro(z, Bool.and(N.Acts.sends(request, List.append(&2, N.Act, xs, ys)), N.Acts.runs(k, Up.N4.t1_ms(), List.append(&2, N.Act, xs, ys))), P.Bool.and_true_l(z, Bool.and(N.Acts.sends(request, ys), N.Acts.runs(k, Up.N4.t1_ms(), ys)), h), P.Bool.and_intro(N.Acts.sends(request, List.append(&2, N.Act, xs, ys)), N.Acts.runs(k, Up.N4.t1_ms(), List.append(&2, N.Act, xs, ys)), PL.Lv.sends_r(request, xs, ys, P.Bool.and_true_l(N.Acts.sends(request, ys), N.Acts.runs(k, Up.N4.t1_ms(), ys), r)), Ar.runs_r(k, Up.N4.t1_ms(), xs, ys, P.Bool.and_true_r(N.Acts.sends(request, ys), N.Acts.runs(k, Up.N4.t1_ms(), ys), r))))
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

def Ar.row_l(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +p: S.SPhase, +h: {Ar.row(k, xs, p) == True{} : Bool}, +hn: {N.Acts.touches(k, ys) == False{} : Bool}) -> {Ar.row(k, List.append(&2, N.Act, xs, ys), p) == True{} : Bool}:
  match p:
    case S.Deleting{+guard, +request}:
      +z = U32.is_eq(S.Guard.retries(guard), 0)
      +r = P.Bool.and_true_r(z, Bool.and(N.Acts.sends(request, xs), N.Acts.runs(k, Up.N4.t1_ms(), xs)), h)
      P.Bool.and_intro(z, Bool.and(N.Acts.sends(request, List.append(&2, N.Act, xs, ys)), N.Acts.runs(k, Up.N4.t1_ms(), List.append(&2, N.Act, xs, ys))), P.Bool.and_true_l(z, Bool.and(N.Acts.sends(request, xs), N.Acts.runs(k, Up.N4.t1_ms(), xs)), h), P.Bool.and_intro(N.Acts.sends(request, List.append(&2, N.Act, xs, ys)), N.Acts.runs(k, Up.N4.t1_ms(), List.append(&2, N.Act, xs, ys)), PL.Lv.sends_l(request, xs, ys, P.Bool.and_true_l(N.Acts.sends(request, xs), N.Acts.runs(k, Up.N4.t1_ms(), xs), r)), Ar.runs_l(k, Up.N4.t1_ms(), xs, ys, P.Bool.and_true_r(N.Acts.sends(request, xs), N.Acts.runs(k, Up.N4.t1_ms(), xs), r), hn)))
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

def Ar.rows_r(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, ss: Tb.Table(S.Session), +h: {Ar.rows(k, ys, ss) == True{} : Bool}) -> {Ar.rows(k, List.append(&2, N.Act, xs, ys), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      +b = Bool.not(U32.is_eq(k0, k))
      +x = Bool.or(b, Ar.row(k, ys, S.Session.phase(t)))
      P.Bool.and_intro(Bool.or(b, Ar.row(k, List.append(&2, N.Act, xs, ys), S.Session.phase(t))), Ar.rows(k, List.append(&2, N.Act, xs, ys), more), P.Bool.or_mono(b, Ar.row(k, ys, S.Session.phase(t)), Ar.row(k, List.append(&2, N.Act, xs, ys), S.Session.phase(t)), P.Bool.and_true_l(x, Ar.rows(k, ys, more), h), e => Ar.row_r(k, xs, ys, S.Session.phase(t), e)), Ar.rows_r(k, xs, ys, more, P.Bool.and_true_r(x, Ar.rows(k, ys, more), h)))

def Ar.rows_l(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, ss: Tb.Table(S.Session), +h: {Ar.rows(k, xs, ss) == True{} : Bool}, +hn: {N.Acts.touches(k, ys) == False{} : Bool}) -> {Ar.rows(k, List.append(&2, N.Act, xs, ys), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      +b = Bool.not(U32.is_eq(k0, k))
      +x = Bool.or(b, Ar.row(k, xs, S.Session.phase(t)))
      P.Bool.and_intro(Bool.or(b, Ar.row(k, List.append(&2, N.Act, xs, ys), S.Session.phase(t))), Ar.rows(k, List.append(&2, N.Act, xs, ys), more), P.Bool.or_mono(b, Ar.row(k, xs, S.Session.phase(t)), Ar.row(k, List.append(&2, N.Act, xs, ys), S.Session.phase(t)), P.Bool.and_true_l(x, Ar.rows(k, xs, more), h), e => Ar.row_l(k, xs, ys, S.Session.phase(t), e, hn)), Ar.rows_l(k, xs, ys, more, P.Bool.and_true_r(x, Ar.rows(k, xs, more), h), hn))

# Rows that change
# ----------------

def Ar.row_live(+k: U32, +acts: List<&2, N.Act>, +p: S.SPhase, +h: {S.SPhase.live(p) == True{} : Bool}) -> {Ar.row(k, acts, p) == True{} : Bool}:
  match p:
    case S.Deleting{guard, request}:
      Empty.absurd({Ar.row(k, acts, S.Deleting{guard, request}) == True{} : Bool}, P.Refute.bool(h))
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

# No row under k being deleted: every row of k is so.
def Ar.of_live(+k: U32, +acts: List<&2, N.Act>, ss: Tb.Table(S.Session), +h: {S.Sessions.each(k, S.SLive{}, ss) == True{} : Bool}) -> {Ar.rows(k, acts, ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      +b = Bool.not(U32.is_eq(k0, k))
      +x = Bool.or(b, S.SPhase.live(S.Session.phase(t)))
      P.Bool.and_intro(Bool.or(b, Ar.row(k, acts, S.Session.phase(t))), Ar.rows(k, acts, more), P.Bool.or_mono(b, S.SPhase.live(S.Session.phase(t)), Ar.row(k, acts, S.Session.phase(t)), P.Bool.and_true_l(x, S.Sessions.each(k, S.SLive{}, more), h), e => Ar.row_live(k, acts, S.Session.phase(t), e)), Ar.of_live(k, acts, more, P.Bool.and_true_r(x, S.Sessions.each(k, S.SLive{}, more), h)))

def Ar.sift(+v: S.SSieve, ss: Tb.Table(S.Session), +k: U32, +acts: List<&2, N.Act>, +h: {Ar.rows(k, acts, ss) == True{} : Bool}) -> {Ar.rows(k, acts, S.Sessions.sift(v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      +x = Bool.or(Bool.not(U32.is_eq(k0, k)), Ar.row(k, acts, S.Session.phase(t)))
      P.Keep.by(S.Session, tb => {Ar.rows(k, acts, tb) == True{} : Bool}, k0, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k0, t), e => h1 => P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k0, k)), Ar.row(k, acts, S.Session.phase(t))), Ar.rows(k, acts, S.Sessions.sift(v, more)), P.Bool.and_true_l(x, Ar.rows(k, acts, more), h), h1), Ar.sift(v, more, k, acts, P.Bool.and_true_r(x, Ar.rows(k, acts, more), h)))

def Ar.hit(+k: U32, +acts: List<&2, N.Act>, +t: S.Session, +v: S.SVar, +b: Bool, +ht: {Ar.row(k, acts, S.Session.phase(t)) == True{} : Bool}, hv: {b == True{} : Bool} -> {Ar.row(k, acts, S.SVar.phase(v)) == True{} : Bool}) -> {Ar.row(k, acts, S.Session.phase(S.Session.revar_if(t, v, b))) == True{} : Bool}:
  match t:
    case S.Session{id, var}:
      match b:
        case True{}:
          hv({==})
        case False{}:
          ht

def Ar.use(+key: U32, +k: U32, +v: S.SVar, +acts: List<&2, N.Act>, +ek: {U32.is_eq(key, k) == True{} : Bool}, +hv: {Bool.or(Bool.not(U32.is_eq(key, k)), Ar.row(k, acts, S.SVar.phase(v))) == True{} : Bool}) -> {Ar.row(k, acts, S.SVar.phase(v)) == True{} : Bool}:
  sek = Equal.sym(Bool, U32.is_eq(key, k), True{}, ek)
  P.Bool.or_true_r(Bool.not(U32.is_eq(key, k)), Ar.row(k, acts, S.SVar.phase(v)), (%sek : {Bool.not(_) == False{} : Bool}; {==}), hv)

def Ar.revar_row(+key: U32, +v: S.SVar, +k: U32, +acts: List<&2, N.Act>, +k0: U32, +t: S.Session, +b0: Bool, +eb0: {U32.is_eq(k0, k) == b0 : Bool}, +ht: {Bool.or(Bool.not(b0), Ar.row(k, acts, S.Session.phase(t))) == True{} : Bool}, +hv: {Bool.or(Bool.not(U32.is_eq(key, k)), Ar.row(k, acts, S.SVar.phase(v))) == True{} : Bool}) -> {Bool.or(Bool.not(U32.is_eq(k0, k)), Ar.row(k, acts, S.Session.phase(S.Session.revar_if(t, v, Bool.and(U32.is_eq(k0, key), S.SVar.follows(v, t)))))) == True{} : Bool}:
  match b0:
    case True{}:
      seb = Equal.sym(Bool, U32.is_eq(k0, k), True{}, eb0)
      +ek = P.U32.eq_of_is_eq(k0, k, eb0)
      +hit = Bool.and(U32.is_eq(k0, key), S.SVar.follows(v, t))
      (%seb : {Bool.or(Bool.not(_), Ar.row(k, acts, S.Session.phase(S.Session.revar_if(t, v, hit)))) == True{} : Bool}; Ar.hit(k, acts, t, v, hit, ht, eh => Ar.use(key, k, v, acts, Equal.trans(Bool, U32.is_eq(key, k), U32.is_eq(k, key), True{}, P.U32.sym(key, k), (%ek : {U32.is_eq(_, key) == True{} : Bool}; P.Bool.and_true_l(U32.is_eq(k0, key), S.SVar.follows(v, t), eh))), hv)))
    case False{}:
      seb = Equal.sym(Bool, U32.is_eq(k0, k), False{}, eb0)
      (%seb : {Bool.or(Bool.not(_), Ar.row(k, acts, S.Session.phase(S.Session.revar_if(t, v, Bool.and(U32.is_eq(k0, key), S.SVar.follows(v, t)))))) == True{} : Bool}; {==})

def Ar.revar(+key: U32, +v: S.SVar, ss: Tb.Table(S.Session), +k: U32, +acts: List<&2, N.Act>, +h: {Ar.rows(k, acts, ss) == True{} : Bool}, +hv: {Bool.or(Bool.not(U32.is_eq(key, k)), Ar.row(k, acts, S.SVar.phase(v))) == True{} : Bool}) -> {Ar.rows(k, acts, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      +x = Bool.or(Bool.not(U32.is_eq(k0, k)), Ar.row(k, acts, S.Session.phase(t)))
      +t2 = S.Session.revar_if(t, v, Bool.and(U32.is_eq(k0, key), S.SVar.follows(v, t)))
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k0, k)), Ar.row(k, acts, S.Session.phase(t2))), Ar.rows(k, acts, S.Sessions.revar(key, v, more)), Ar.revar_row(key, v, k, acts, k0, t, U32.is_eq(k0, k), {==}, P.Bool.and_true_l(x, Ar.rows(k, acts, more), h), hv), Ar.revar(key, v, more, k, acts, P.Bool.and_true_r(x, Ar.rows(k, acts, more), h), hv))

# A change to being deleted under the key: its request among the actions,
# which start timer k and stop it nowhere.
def Ar.armed(+key: U32, +k: U32, +p: S.SPhase, +acts: List<&2, N.Act>, +ha: {PL.Lv.arms_p(key, p, acts) == True{} : Bool}, +hs: {Run.sure(k, acts) == True{} : Bool}, +ek: {U32.is_eq(key, k) == True{} : Bool}) -> {Ar.row(k, acts, p) == True{} : Bool}:
  match p:
    case S.Deleting{+guard, +request}:
      +z = U32.is_eq(S.Guard.retries(guard), 0)
      +r = P.Bool.and_true_r(z, Bool.and(N.Acts.sends(request, acts), N.Acts.starts_for(key, Up.N4.t1_ms(), acts)), ha)
      +e1 = P.U32.eq_of_is_eq(key, k, ek)
      hk : {N.Acts.starts_for(k, Up.N4.t1_ms(), acts) == True{} : Bool} = (%e1 : {N.Acts.starts_for(_, Up.N4.t1_ms(), acts) == True{} : Bool}; P.Bool.and_true_r(N.Acts.sends(request, acts), N.Acts.starts_for(key, Up.N4.t1_ms(), acts), r))
      P.Bool.and_intro(z, Bool.and(N.Acts.sends(request, acts), N.Acts.runs(k, Up.N4.t1_ms(), acts)), P.Bool.and_true_l(z, Bool.and(N.Acts.sends(request, acts), N.Acts.starts_for(key, Up.N4.t1_ms(), acts)), ha), P.Bool.and_intro(N.Acts.sends(request, acts), N.Acts.runs(k, Up.N4.t1_ms(), acts), P.Bool.and_true_l(N.Acts.sends(request, acts), N.Acts.starts_for(key, Up.N4.t1_ms(), acts), r), Ar.runs_of(k, acts, hk, hs)))
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

def Ar.armed_or(+key: U32, +k: U32, +p: S.SPhase, +acts: List<&2, N.Act>, +c: Bool, +ec: {U32.is_eq(key, k) == c : Bool}, +ha: {PL.Lv.arms_p(key, p, acts) == True{} : Bool}, +hs: {Run.sure(k, acts) == True{} : Bool}) -> {Bool.or(Bool.not(U32.is_eq(key, k)), Ar.row(k, acts, p)) == True{} : Bool}:
  match c:
    case True{}:
      P.Bool.or_r(Bool.not(U32.is_eq(key, k)), Ar.row(k, acts, p), Ar.armed(key, k, p, acts, ha, hs, ec))
    case False{}:
      sec = Equal.sym(Bool, U32.is_eq(key, k), False{}, ec)
      (%sec : {Bool.or(Bool.not(_), Ar.row(k, acts, p)) == True{} : Bool}; {==})

def Ar.put(+key: U32, +t: S.Session, +ss: Tb.Table(S.Session), +k: U32, +acts: List<&2, N.Act>, +h: {Ar.rows(k, acts, ss) == True{} : Bool}, +ht: {S.SPhase.live(S.Session.phase(t)) == True{} : Bool}) -> {Ar.rows(k, acts, S.Sessions.put(key, t, ss)) == True{} : Bool}:
  +b = Bool.not(U32.is_eq(key, k))
  P.Bool.and_intro(Bool.or(b, Ar.row(k, acts, S.Session.phase(t))), Ar.rows(k, acts, S.Sessions.sift(S.SClear{key, t}, ss)), P.Bool.or_r(b, Ar.row(k, acts, S.Session.phase(t)), Ar.row_live(k, acts, S.Session.phase(t), ht)), Ar.sift(S.SClear{key, t}, ss, k, acts, h))

# What a transaction does to the rows under k, given the deletions it starts
# are armed by the actions and these never stop k.
def Ar.apply(tx: S.Tx, +st: S.State, +k: U32, +acts: List<&2, N.Act>, +ha: {PL.Lv.arms(tx, acts) == True{} : Bool}, +hs: {Run.sure(k, acts) == True{} : Bool}, +h: {Ar.rows(k, acts, S.State.sessions(st)) == True{} : Bool}) -> {Ar.rows(k, acts, S.State.sessions(S.Tx.apply(tx, st))) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      h
    case S.Put{+key, +ue}:
      match st:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
          Ar.sift(S.SOwned{S.Ues.put(key, ue, ues)}, sessions, k, acts, h)
    case S.Del{+key}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Ar.sift(S.SOthers{key}, sessions, k, acts, h)
    case S.PutSession{+key, +t}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Ar.put(key, t, sessions, k, acts, h, ha)
    case S.Revar{+key, +v}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Ar.revar(key, v, sessions, k, acts, h, Ar.armed_or(key, k, S.SVar.phase(v), acts, U32.is_eq(key, k), {==}, ha, hs))
    case S.DelSession{+key}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Ar.sift(S.SExcept{key}, sessions, k, acts, h)
    case S.Rephase{key, phase}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.Subs{new}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.SetLink{link}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.BumpUe{bk}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.BumpSeq{n}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          h
    case S.Both{+a, +b}:
      Ar.apply(b, S.Tx.apply(a, st), k, acts, P.Bool.and_true_r(PL.Lv.arms(a, acts), PL.Lv.arms(b, acts), ha), hs, Ar.apply(a, st, k, acts, P.Bool.and_true_l(PL.Lv.arms(a, acts), PL.Lv.arms(b, acts), ha), hs, h))

# The step
# --------

# An outcome whose transaction starts its deletions armed by actions that
# stop no k, after any actions: no row under k being deleted before, every
# one being deleted after is armed.
def Ar.of(+st: S.State, +pre: List<&2, N.Act>, +tx: S.Tx, +acts: List<&2, N.Act>, +k: U32, +ha: {PL.Lv.arms(tx, acts) == True{} : Bool}, +hs: {Run.sure(k, acts) == True{} : Bool}, +eh: {S.Sessions.each(k, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(k, N.Step.of(st, (tx, List.append(&2, N.Act, pre, acts)))):
  +ss = S.State.sessions(st)
  +ss2 = S.State.sessions(S.Tx.apply(tx, st))
  +r1 = Ar.apply(tx, st, k, acts, ha, hs, Ar.of_live(k, acts, ss, eh))
  hx => Ar.rows_l(k, List.append(&2, N.Act, pre, acts), N.Gone.when(S.Tx.keeps_sessions(tx), ss, ss2), ss2, Ar.rows_r(k, pre, acts, ss2, r1), Run.when(S.Tx.keeps_sessions(tx), ss, ss2, k, hx))

def Ar.step_of(+st: S.State, +o: N.GOut(), +k: U32, +h: {PL.Lv.ok(st, o) == True{} : Bool}, +ef: {Run.free(st, k) == True{} : Bool}, +eh: {S.Sessions.each(k, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(k, N.Step.of(st, o)):
  match o:
    case (+tx, +acts):
      Ar.of(st, [], tx, acts, k, PL.Lv.ok_arms(st, (tx, acts), h), Run.sure_of(st, k, acts, Run.acts(st, k, acts, ef, PL.Lv.ok_acts(st, (tx, acts), h))), eh)

# A session the UPF settles stops its own guard first.
def Ar.settled(+st: S.State, +k0: U32, +tx: S.Tx, +more: List<&2, N.Act>, +h: {PL.Lv.ok(st, (tx, more)) == True{} : Bool}, +k: U32, +ef: {Run.free(st, k) == True{} : Bool}, +eh: {S.Sessions.each(k, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(k, N.Step.of(st, (tx, N.TimerCancel{k0} <> more))):
  Ar.of(st, [N.TimerCancel{k0}], tx, more, k, PL.Lv.ok_arms(st, (tx, more), h), Run.sure_of(st, k, more, Run.acts(st, k, more, ef, PL.Lv.ok_acts(st, (tx, more), h))), eh)

# A step that leaves no row under k being deleted.
def Ar.calm(+k: U32, +o: N.Step(), +h: {S.Sessions.each(k, S.SLive{}, S.State.sessions(K.Kernel.state(o))) == True{} : Bool}) -> Ar.Q(k, o):
  hx => Ar.of_live(k, K.Kernel.actions(o), S.State.sessions(K.Kernel.state(o)), h)

def Ar.live_sift(+v: S.SSieve, ss: Tb.Table(S.Session), +k: U32, +h: {S.Sessions.each(k, S.SLive{}, ss) == True{} : Bool}) -> {S.Sessions.each(k, S.SLive{}, S.Sessions.sift(v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      +x = Bool.or(Bool.not(U32.is_eq(k0, k)), S.SPhase.live(S.Session.phase(t)))
      P.Keep.by(S.Session, tb => {S.Sessions.each(k, S.SLive{}, tb) == True{} : Bool}, k0, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k0, t), e => h1 => P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k0, k)), S.SPhase.live(S.Session.phase(t))), S.Sessions.each(k, S.SLive{}, S.Sessions.sift(v, more)), P.Bool.and_true_l(x, S.Sessions.each(k, S.SLive{}, more), h), h1), Ar.live_sift(v, more, k, P.Bool.and_true_r(x, S.Sessions.each(k, S.SLive{}, more), h)))

def Ar.del(+st: S.State, +key: U32, +acts: List<&2, N.Act>, +k: U32, +eh: {S.Sessions.each(k, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(k, N.Step.of(st, (S.DelSession{key}, acts))):
  match st:
    case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
      Ar.calm(k, N.Step.of(S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}, (S.DelSession{key}, acts)), Ar.live_sift(S.SExcept{key}, sessions, k, eh))

# The row under a key is live when no row under it is being deleted.
def Ar.live_at(+k: U32, +k0: U32, +t0: S.Session, +more: Tb.Table(S.Session), +t: S.Session, +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +eg: {Tb.Table.hit(S.Session, t0, Tb.Table.get(S.Session, k, more), b) == Some{t} : Maybe<&2, S.Session>}, +h: {Bool.and(Bool.or(Bool.not(b), S.SPhase.live(S.Session.phase(t0))), S.Sessions.each(k, S.SLive{}, more)) == True{} : Bool}, ih: {Tb.Table.get(S.Session, k, more) == Some{t} : Maybe<&2, S.Session>} -> {S.Sessions.each(k, S.SLive{}, more) == True{} : Bool} -> {S.SPhase.live(S.Session.phase(t)) == True{} : Bool}) -> {S.SPhase.live(S.Session.phase(t)) == True{} : Bool}:
  match b:
    case True{}:
      et = P.Some.inj(S.Session, t0, t, eg)
      (%et : {S.SPhase.live(S.Session.phase(_)) == True{} : Bool}; P.Bool.and_true_l(S.SPhase.live(S.Session.phase(t0)), S.Sessions.each(k, S.SLive{}, more), h))
    case False{}:
      ih(eg, h)

def Ar.live_get(+k: U32, ss: Tb.Table(S.Session), +t: S.Session, +eg: {Tb.Table.get(S.Session, k, ss) == Some{t} : Maybe<&2, S.Session>}, +h: {S.Sessions.each(k, S.SLive{}, ss) == True{} : Bool}) -> {S.SPhase.live(S.Session.phase(t)) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({S.SPhase.live(S.Session.phase(t)) == True{} : Bool}, P.Refute.none_some(S.Session, t, eg))
    case (+k0, +t0) <> +more:
      Ar.live_at(k, k0, t0, more, t, U32.is_eq(k0, k), {==}, eg, h, e => hm => Ar.live_get(k, more, t, e, hm))

# The guard of a row being deleted fires: the row is another key's.
def Ar.key_ne(ss: Tb.Table(S.Session), +k: U32, +t: S.Session, +skey: U32, +g: S.Guard, +r: B.Bytes(), +c: Bool, +ec: {U32.is_eq(k, skey) == c : Bool}, +em: {Tb.Table.get(S.Session, k, ss) == Some{t} : Maybe<&2, S.Session>}, +ep: {S.Session.phase(t) == S.Deleting{g, r} : S.SPhase}, +eh: {S.Sessions.each(skey, S.SLive{}, ss) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      e1 = P.U32.eq_of_is_eq(k, skey, ec)
      eg : {Tb.Table.get(S.Session, skey, ss) == Some{t} : Maybe<&2, S.Session>} = (%e1 : {Tb.Table.get(S.Session, _, ss) == Some{t} : Maybe<&2, S.Session>}; em)
      Empty.absurd({True{} == False{} : Bool}, P.Refute.bool((%ep : {S.SPhase.live(_) == True{} : Bool}; Ar.live_get(skey, ss, t, eg, eh))))
    case False{}:
      {==}

def Ar.revar_ne(+st: S.State, +k: U32, +v: S.SVar, +acts: List<&2, N.Act>, +skey: U32, +ne: {U32.is_eq(k, skey) == False{} : Bool}, +eh: {S.Sessions.each(skey, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(skey, N.Step.of(st, (S.Revar{k, v}, acts))):
  match st:
    case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
      +xs = K.Kernel.actions(N.Step.of(S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}, (S.Revar{k, v}, acts)))
      sne = Equal.sym(Bool, U32.is_eq(k, skey), False{}, ne)
      hx => Ar.revar(k, v, sessions, skey, xs, Ar.of_live(skey, xs, sessions, eh), (%sne : {Bool.or(Bool.not(_), Ar.row(skey, xs, S.SVar.phase(v))) == True{} : Bool}; {==}))

def Ar.resend(+st: S.State, +k: U32, +t: S.Session, +p: S.SPhase, +request: B.Bytes(), +more: Bool, +skey: U32, +ne: {U32.is_eq(k, skey) == False{} : Bool}, +eh: {S.Sessions.each(skey, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(skey, N.Step.of(st, Gsm.Gsm.resend_if(k, t, p, request, (S.DelSession{k}, [N.Note{F.Warn{}, "PFCP: no Session Deletion Response; deletion given up"}]), more))):
  match more:
    case True{}:
      Ar.revar_ne(st, k, S.SVar{S.Session.up_seid(t), S.Session.seq(t), p}, [N.Pfcp{S.Session.tag(t), request}, N.TimerStart{S.Session.tag(t), k, Up.N4.t1_ms()}], skey, ne, eh)
    case False{}:
      Ar.del(st, k, [N.Note{F.Warn{}, "PFCP: no Session Deletion Response; deletion given up"}], skey, eh)

def Ar.deleted_phase(+st: S.State, +k: U32, +msg: Pf.Msg, +p: S.SPhase, +skey: U32, +eh: {S.Sessions.each(skey, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(skey, N.Step.of(st, Gsm.Gsm.deleted_phase(k, msg, p))):
  match p:
    case S.Creating{guard, pti, accept, request}:
      Ar.calm(skey, N.Step.of(st, Gsm.Gsm.deleted_phase(k, msg, S.Creating{guard, pti, accept, request})), eh)
    case S.Setting{guard, pti}:
      Ar.calm(skey, N.Step.of(st, Gsm.Gsm.deleted_phase(k, msg, S.Setting{guard, pti})), eh)
    case S.Modifying{guard, request}:
      Ar.calm(skey, N.Step.of(st, Gsm.Gsm.deleted_phase(k, msg, S.Modifying{guard, request})), eh)
    case S.Repointing{guard, request}:
      Ar.calm(skey, N.Step.of(st, Gsm.Gsm.deleted_phase(k, msg, S.Repointing{guard, request})), eh)
    case S.Deleting{guard, request}:
      Ar.del(st, k, Gsm.Gsm.deleted_notes(Up.N4.accepted(Up.N4.cause(msg))), skey, eh)
    case S.Active{}:
      Ar.calm(skey, N.Step.of(st, Gsm.Gsm.deleted_phase(k, msg, S.Active{})), eh)

def Ar.deleted(+st: S.State, +msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +skey: U32, +eh: {S.Sessions.each(skey, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(skey, N.Step.of(st, Gsm.Gsm.deleted(msg, m))):
  match m:
    case None{}:
      Ar.calm(skey, N.Step.of(st, Gsm.Gsm.deleted(msg, None{})), eh)
    case Some{(+k, +t)}:
      Ar.deleted_phase(st, k, msg, S.Session.phase(t), skey, eh)

# An association's contexts going: the deletions it starts are armed.
def Ar.drop(+st: S.State, +assoc: U32, +skey: U32, +eh: {S.Sessions.each(skey, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(skey, R.Route.drop(st, assoc)):
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s1 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      +left = S.Ues.drop_assoc(assoc, ues)
      +gone = S.Sessions.sift(S.SOrphan{left}, sessions)
      +d = Up.N4.deletions(gone, pfcp_seq)
      +hd = PL.Lv.dels(s1, gone, pfcp_seq, PL.Lv.srows_sift(S.SOrphan{left}, sessions), PL.Lv.krows_orphan(s1, left))
      +r1 = Ar.apply(N.Out.tx(d), s1, skey, N.Out.acts(d), PL.Lv.okf_arms(s1, d, hd), Run.dels_sure(gone, pfcp_seq, skey), Ar.of_live(skey, N.Out.acts(d), sessions, eh))
      +kept = S.Sessions.sift(S.SOwned{left}, S.State.sessions(S.Tx.apply(N.Out.tx(d), s1)))
      +r2 = Ar.sift(S.SOwned{left}, S.State.sessions(S.Tx.apply(N.Out.tx(d), s1)), skey, N.Out.acts(d), r1)
      hx => Ar.rows_l(skey, N.Out.acts(d), N.Gone.cancels(sessions, kept), kept, r2, Run.gone(sessions, kept, skey, hx))

def Ar.ready(+st: S.State, +assoc: U32, +id: B.Bytes(), +ok: Bool, +acts: List<&2, N.Act>, +skey: U32, +eh: {S.Sessions.each(skey, S.SLive{}, S.State.sessions(st)) == True{} : Bool}, +hc: {N.Acts.touches(skey, acts) == False{} : Bool}) -> Ar.Q(skey, (S.State.ready(N.Step.state(R.Route.drop(st, assoc)), assoc, id, ok), List.append(&2, N.Act, N.Step.acts(R.Route.drop(st, assoc)), acts))):
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s1 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      hx => Ar.rows_l(skey, N.Step.acts(R.Route.drop(s1, assoc)), acts, S.State.sessions(N.Step.state(R.Route.drop(s1, assoc))), Ar.drop(s1, assoc, skey, eh, hx), hc)

def Ar.down(+st: S.State, +assoc: U32, +skey: U32, +eh: {S.Sessions.each(skey, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(skey, R.Route.down(st, assoc)):
  +o1 = N.Step.of(st, Ho.Ho.down(st, assoc))
  +s1 = K.Kernel.state(o1)
  +ess = Equal.sym(Tb.Table(S.Session), S.State.sessions(s1), S.State.sessions(st), PL.Lw.down_sessions(st, assoc))
  +eh1 : {S.Sessions.each(skey, S.SLive{}, S.State.sessions(s1)) == True{} : Bool} = (%ess : {S.Sessions.each(skey, S.SLive{}, _) == True{} : Bool}; eh)
  +n : N.Act = N.Note{F.Info{}, "NGAP: association down; its UE contexts and sessions released"}
  +ss = S.State.sessions(K.Kernel.state(R.Route.drop(s1, assoc)))
  hx => Ar.rows_r(skey, K.Kernel.actions(o1), n <> K.Kernel.actions(R.Route.drop(s1, assoc)), ss, Ar.rows_r(skey, [n], K.Kernel.actions(R.Route.drop(s1, assoc)), ss, Ar.drop(s1, assoc, skey, eh1, hx)))

def Ar.config(+complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), +skey: U32, +eh: {S.Sessions.each(skey, S.SLive{}, S.State.sessions(st)) == True{} : Bool}) -> Ar.Q(skey, K.Kernel.config(complete, st, tlvs, entropy)):
  match complete:
    case False{}:
      Ar.calm(skey, K.Kernel.config(False{}, st, tlvs, entropy), eh)
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          Ar.calm(skey, K.Kernel.config(True{}, S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}, tlvs, entropy), eh)

# The row the step leaves under skey
# ----------------------------------

def Ar.fresh(+g: S.Guard, +h: {U32.is_eq(S.Guard.retries(g), 0) == True{} : Bool}) -> {g == S.Guard{0} : S.Guard}:
  match g:
    case S.Guard{+n}:
      e = Equal.sym(U32, n, 0, P.U32.eq_of_is_eq(n, 0, h))
      (%e : {S.Guard{_} == S.Guard{0} : S.Guard}; {==})

def Ar.Armed(+acts: List<&2, N.Act>, +skey: U32, +g: S.Guard, +r: B.Bytes()) -> Type:
  {g == S.Guard{0} : S.Guard} & ({N.Acts.sends(r, acts) == True{} : Bool} & {N.Acts.runs(skey, Up.N4.t1_ms(), acts) == True{} : Bool})

def Ar.armed_row(+skey: U32, +acts: List<&2, N.Act>, +s: S.Session, +g: S.Guard, +r: B.Bytes(), +h: {Ar.row(skey, acts, S.Session.phase(s)) == True{} : Bool}, +ep: {S.Session.phase(s) == S.Deleting{g, r} : S.SPhase}) -> Ar.Armed(acts, skey, g, r):
  +hd : {Ar.row(skey, acts, S.Deleting{g, r}) == True{} : Bool} = (%ep : {Ar.row(skey, acts, _) == True{} : Bool}; h)
  +z = U32.is_eq(S.Guard.retries(g), 0)
  +rest = P.Bool.and_true_r(z, Bool.and(N.Acts.sends(r, acts), N.Acts.runs(skey, Up.N4.t1_ms(), acts)), hd)
  (Ar.fresh(g, P.Bool.and_true_l(z, Bool.and(N.Acts.sends(r, acts), N.Acts.runs(skey, Up.N4.t1_ms(), acts)), hd)), (P.Bool.and_true_l(N.Acts.sends(r, acts), N.Acts.runs(skey, Up.N4.t1_ms(), acts), rest), P.Bool.and_true_r(N.Acts.sends(r, acts), N.Acts.runs(skey, Up.N4.t1_ms(), acts), rest)))

def Ar.first_at(+skey: U32, +acts: List<&2, N.Act>, +k0: U32, +t0: S.Session, +more: Tb.Table(S.Session), +s: S.Session, +g: S.Guard, +r: B.Bytes(), +b: Bool, +eb: {U32.is_eq(k0, skey) == b : Bool}, +eg: {Tb.Table.hit(S.Session, t0, Tb.Table.get(S.Session, skey, more), b) == Some{s} : Maybe<&2, S.Session>}, +h: {Bool.and(Bool.or(Bool.not(b), Ar.row(skey, acts, S.Session.phase(t0))), Ar.rows(skey, acts, more)) == True{} : Bool}, +ep: {S.Session.phase(s) == S.Deleting{g, r} : S.SPhase}, ih: {Tb.Table.get(S.Session, skey, more) == Some{s} : Maybe<&2, S.Session>} -> {Ar.rows(skey, acts, more) == True{} : Bool} -> Ar.Armed(acts, skey, g, r)) -> Ar.Armed(acts, skey, g, r):
  match b:
    case True{}:
      et = P.Some.inj(S.Session, t0, s, eg)
      Ar.armed_row(skey, acts, s, g, r, (%et : {Ar.row(skey, acts, S.Session.phase(_)) == True{} : Bool}; P.Bool.and_true_l(Ar.row(skey, acts, S.Session.phase(t0)), Ar.rows(skey, acts, more), h)), ep)
    case False{}:
      ih(eg, h)

def Ar.first(+skey: U32, +acts: List<&2, N.Act>, ss: Tb.Table(S.Session), +s: S.Session, +g: S.Guard, +r: B.Bytes(), +h: {Ar.rows(skey, acts, ss) == True{} : Bool}, +es: {Tb.Table.get(S.Session, skey, ss) == Some{s} : Maybe<&2, S.Session>}, +ep: {S.Session.phase(s) == S.Deleting{g, r} : S.SPhase}) -> Ar.Armed(acts, skey, g, r):
  match ss:
    case Nil{}:
      Empty.absurd(Ar.Armed(acts, skey, g, r), P.Refute.none_some(S.Session, s, es))
    case (+k0, +t0) <> +more:
      Ar.first_at(skey, acts, k0, t0, more, s, g, r, U32.is_eq(k0, skey), {==}, es, h, ep, e => hm => Ar.first(skey, acts, more, s, g, r, hm, e, ep))

def L.smf.deletion.armed(st, ev, entropy, skey, s, guard, request, en, ef, ez, eh, es, ep):
  +o = K.Kernel.step(st, ev, entropy)
  +ss = S.State.sessions(K.Kernel.state(o))
  q = PL.Dw.walk(o => Ar.Q(skey, o), o => Ar.Q(skey, N.Step.of(st, o)), st, ev, entropy, acts => h => c => nr => Ar.calm(skey, (st, acts), eh), +assoc => ns => +id => +ok => +acts => h => c => ers => Ar.ready(st, assoc, id, ok, acts, skey, eh, c(skey)), +tlvs => Ar.config(S.Cfg.complete(tlvs), st, tlvs, entropy, skey, eh), +assoc => Ar.down(st, assoc, skey, eh), o => h => h, +o => +h => Ar.step_of(st, o, skey, h, Run.free_of(st, skey, en, ef, ez), eh), +k => +t => +g => +r => ek => eu => em => ep2 => Ar.resend(st, k, t, S.Deleting{S.Guard{U32.add(S.Guard.retries(g), 1)}, r}, r, U32.is_lt(S.Guard.retries(g), Up.N4.n1()), skey, Ar.key_ne(S.State.sessions(st), k, t, skey, g, r, U32.is_eq(k, skey), {==}, em, ep2, eh), eh), +len => +bytes => +msg => +rest => ev2 => er => ek => Ar.deleted(st, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), skey, eh), +k => +tx => +more => ek => ehs => h => Ar.settled(st, k, tx, more, h, skey, Run.free_of(st, skey, en, ef, ez), eh))
  Ar.first(skey, K.Kernel.actions(o), ss, s, guard, request, q(Run.has(ss, skey, s, es)), es, ep)
