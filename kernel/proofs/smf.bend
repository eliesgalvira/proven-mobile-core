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
import ./kernel.bend as PK
import ./takeover.bend as PT
import ./liveness.bend as PL

# Proofs of the SMF's laws (tickets 19 and 34).

def SClear.keep(+key: U32, +s: S.Session, +k: U32, +t: S.Session, +rest: Tb.Table(S.Session), b: Bool, e1: {Bool.not(S.SRow.conflicts(key, s, k, t)) == True{} : Bool}, ih: {S.Sessions.clear(key, s, rest) == True{} : Bool}) -> {S.Sessions.clear(key, s, Tb.Table.keep(S.Session, k, t, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, rest), e1, ih)
    case False{}:
      ih

def SClear.sift(+key: U32, +s: S.Session, +v: S.SSieve, sessions: Tb.Table(S.Session), +e: {S.Sessions.clear(key, s, sessions) == True{} : Bool}) -> {S.Sessions.clear(key, s, S.Sessions.sift(v, sessions)) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      SClear.keep(key, s, k, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k, t), P.Bool.and_true_l(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, more), e), SClear.sift(key, s, v, more, P.Bool.and_true_r(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, more), e)))

def SUnique.keep(+key: U32, +s: S.Session, +rest: Tb.Table(S.Session), b: Bool, ec: {S.Sessions.clear(key, s, rest) == True{} : Bool}, eu: {S.Sessions.unique(rest) == True{} : Bool}) -> {S.Sessions.unique(Tb.Table.keep(S.Session, key, s, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(S.Sessions.clear(key, s, rest), S.Sessions.unique(rest), ec, eu)
    case False{}:
      eu

def SUnique.sift(+v: S.SSieve, sessions: Tb.Table(S.Session), +e: {S.Sessions.unique(sessions) == True{} : Bool}) -> {S.Sessions.unique(S.Sessions.sift(v, sessions)) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+key, +s) <> +more:
      SUnique.keep(key, s, S.Sessions.sift(v, more), S.SSieve.keeps(v, key, s), SClear.sift(key, s, v, more, P.Bool.and_true_l(S.Sessions.clear(key, s, more), S.Sessions.unique(more), e)), SUnique.sift(v, more, P.Bool.and_true_r(S.Sessions.clear(key, s, more), S.Sessions.unique(more), e)))

def SClear.own_keep(+key: U32, +s: S.Session, +k: U32, +t: S.Session, +rest: Tb.Table(S.Session), b: Bool, eb: {Bool.not(S.SRow.conflicts(key, s, k, t)) == b : Bool}, ih: {S.Sessions.clear(key, s, rest) == True{} : Bool}) -> {S.Sessions.clear(key, s, Tb.Table.keep(S.Session, k, t, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, rest), eb, ih)
    case False{}:
      ih

def SClear.own(+key: U32, +s: S.Session, sessions: Tb.Table(S.Session)) -> {S.Sessions.clear(key, s, S.Sessions.sift(S.SClear{key, s}, sessions)) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      SClear.own_keep(key, s, k, t, S.Sessions.sift(S.SClear{key, s}, more), S.SSieve.keeps(S.SClear{key, s}, k, t), {==}, SClear.own(key, s, more))

def SDel.keep(+key: U32, +k: U32, +t: S.Session, +rest: Tb.Table(S.Session), b: Bool, eb: {Bool.not(U32.is_eq(k, key)) == b : Bool}, ih: {Tb.Table.get(S.Session, key, rest) == None{} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, key, Tb.Table.keep(S.Session, k, t, rest, b)) == None{} : Maybe<&2, S.Session>}:
  match b:
    case True{}:
      ne = Equal.sym(Bool, U32.is_eq(k, key), False{}, P.Bool.not_true(U32.is_eq(k, key), eb))
      %ne : {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, key, rest), _) == None{} : Maybe<&2, S.Session>}
      ih
    case False{}:
      ih

def SDel.get(+key: U32, sessions: Tb.Table(S.Session)) -> {Tb.Table.get(S.Session, key, S.Sessions.del(key, sessions)) == None{} : Maybe<&2, S.Session>}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      SDel.keep(key, k, t, S.Sessions.sift(S.SExcept{key}, more), S.SSieve.keeps(S.SExcept{key}, k, t), {==}, SDel.get(key, more))

# A change of a session in place keeps its identity and keeps or drops its
# tag (PW.Tg), so it adds no conflict.

def Cf.not_of(+x: Bool, +e: {x == False{} : Bool}) -> {Bool.not(x) == True{} : Bool}:
  se = Equal.sym(Bool, x, False{}, e)
  (%se : {Bool.not(_) == True{} : Bool}; {==})

def Cf.or_mono(+x: Bool, +c: Bool, +c2: Bool, +e: {Bool.or(x, c) == False{} : Bool}, f: {c == False{} : Bool} -> {c2 == False{} : Bool}) -> {Bool.or(x, c2) == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({Bool.or(True{}, c2) == False{} : Bool}, P.Refute.true_false(e))
    case False{}:
      f(e)

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
  (%sei : {Bool.or(U32.is_eq(S.Session.ip(a), S.SId.ip(_)), Bool.or(U32.is_eq(S.Session.teid(a), S.SId.teid(_)), Bool.and(z2, U32.is_eq(S.Session.psi(a), S.SId.psi(_))))) == False{} : Bool}; Cf.or_mono(U32.is_eq(S.Session.ip(a), S.Session.ip(t)), Bool.or(U32.is_eq(S.Session.teid(a), S.Session.teid(t)), Bool.and(z, U32.is_eq(S.Session.psi(a), S.Session.psi(t)))), Bool.or(U32.is_eq(S.Session.teid(a), S.Session.teid(t)), Bool.and(z2, U32.is_eq(S.Session.psi(a), S.Session.psi(t)))), e, e1 => Cf.or_mono(U32.is_eq(S.Session.teid(a), S.Session.teid(t)), Bool.and(z, U32.is_eq(S.Session.psi(a), S.Session.psi(t))), Bool.and(z2, U32.is_eq(S.Session.psi(a), S.Session.psi(t))), e1, e2 => Cf.and_mono(z, z2, U32.is_eq(S.Session.psi(a), S.Session.psi(t)), e2, ez => PW.Tg.same_r(S.Session.tag(a), t, t2, h, ez)))))

# Moved at the first place: no conflict is added.
def Cf.l(+t: S.Session, +t2: S.Session, +b: S.Session, +h: PW.Tg.Moved(t, t2), +ei: {S.Session.id(t2) == S.Session.id(t) : S.SId}, +e: {S.Session.conflicts(t, b) == False{} : Bool}) -> {S.Session.conflicts(t2, b) == False{} : Bool}:
  +z = S.Maybe.same_u32(S.Session.tag(t), S.Session.tag(b))
  +z2 = S.Maybe.same_u32(S.Session.tag(t2), S.Session.tag(b))
  sei = Equal.sym(S.SId, S.Session.id(t2), S.Session.id(t), ei)
  (%sei : {Bool.or(U32.is_eq(S.SId.ip(_), S.Session.ip(b)), Bool.or(U32.is_eq(S.SId.teid(_), S.Session.teid(b)), Bool.and(z2, U32.is_eq(S.SId.psi(_), S.Session.psi(b))))) == False{} : Bool}; Cf.or_mono(U32.is_eq(S.Session.ip(t), S.Session.ip(b)), Bool.or(U32.is_eq(S.Session.teid(t), S.Session.teid(b)), Bool.and(z, U32.is_eq(S.Session.psi(t), S.Session.psi(b)))), Bool.or(U32.is_eq(S.Session.teid(t), S.Session.teid(b)), Bool.and(z2, U32.is_eq(S.Session.psi(t), S.Session.psi(b)))), e, e1 => Cf.or_mono(U32.is_eq(S.Session.teid(t), S.Session.teid(b)), Bool.and(z, U32.is_eq(S.Session.psi(t), S.Session.psi(b))), Bool.and(z2, U32.is_eq(S.Session.psi(t), S.Session.psi(b))), e1, e2 => Cf.and_mono(z, z2, U32.is_eq(S.Session.psi(t), S.Session.psi(b)), e2, ez => PW.Tg.same_l(S.Session.tag(b), t, t2, h, ez)))))

def SClear.revar(+key2: U32, +s: S.Session, +key: U32, +v: S.SVar, sessions: Tb.Table(S.Session), +e: {S.Sessions.clear(key2, s, sessions) == True{} : Bool}) -> {S.Sessions.clear(key2, s, S.Sessions.revar(key, v, sessions)) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +hit = Bool.and(U32.is_eq(k, key), S.SVar.follows(v, t))
      +t2 = S.Session.revar_if(t, v, hit)
      +c = S.SRow.conflicts(key2, s, k, t)
      +nc = P.Bool.not_true(c, P.Bool.and_true_l(Bool.not(c), S.Sessions.clear(key2, s, more), e))
      P.Bool.and_intro(Bool.not(S.SRow.conflicts(key2, s, k, t2)), S.Sessions.clear(key2, s, S.Sessions.revar(key, v, more)), Cf.not_of(S.SRow.conflicts(key2, s, k, t2), Cf.or_mono(U32.is_eq(k, key2), S.Session.conflicts(s, t), S.Session.conflicts(s, t2), nc, ec => Cf.r(s, t, t2, PW.Tg.revar(t, v, U32.is_eq(k, key)), PW.Tg.id(t, v, hit), ec))), SClear.revar(key2, s, key, v, more, P.Bool.and_true_r(Bool.not(c), S.Sessions.clear(key2, s, more), e)))

def SClear.subject(+key: U32, +s: S.Session, +s2: S.Session, +h: PW.Tg.Moved(s, s2), +ei: {S.Session.id(s2) == S.Session.id(s) : S.SId}, sessions: Tb.Table(S.Session), +e: {S.Sessions.clear(key, s, sessions) == True{} : Bool}) -> {S.Sessions.clear(key, s2, sessions) == True{} : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +c = S.SRow.conflicts(key, s, k, t)
      +nc = P.Bool.not_true(c, P.Bool.and_true_l(Bool.not(c), S.Sessions.clear(key, s, more), e))
      P.Bool.and_intro(Bool.not(S.SRow.conflicts(key, s2, k, t)), S.Sessions.clear(key, s2, more), Cf.not_of(S.SRow.conflicts(key, s2, k, t), Cf.or_mono(U32.is_eq(k, key), S.Session.conflicts(s, t), S.Session.conflicts(s2, t), nc, ec => Cf.l(s, s2, t, h, ei, ec))), SClear.subject(key, s, s2, h, ei, more, P.Bool.and_true_r(Bool.not(c), S.Sessions.clear(key, s, more), e)))

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

def Su.tx_put(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Su.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Su.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  SUnique.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss, e)

def Su.tx_rephase(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Su.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Su.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  e

def Su.tx_del(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Su.inv(st0, ues, ss) == True{} : Bool}) -> {Su.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  SUnique.sift(S.SOthers{key}, ss, e)

def Su.tx_put_session(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Su.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Su.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
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

def Bd.keep(+k: U32, +t: S.Session, +rest: Tb.Table(S.Session), b: Bool, +ht: {Gsm.Gsm.phase_bounded(S.Session.phase(t)) == True{} : Bool}, +hr: {Gsm.Gsm.bounded(rest) == True{} : Bool}) -> {Gsm.Gsm.bounded(Tb.Table.keep(S.Session, k, t, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Gsm.Gsm.phase_bounded(S.Session.phase(t)), Gsm.Gsm.bounded(rest), ht, hr)
    case False{}:
      hr

def Bd.sift(+v: S.SSieve, ss: Tb.Table(S.Session), +e: {Gsm.Gsm.bounded(ss) == True{} : Bool}) -> {Gsm.Gsm.bounded(S.Sessions.sift(v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      Bd.keep(k, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k, t), P.Bool.and_true_l(Gsm.Gsm.phase_bounded(S.Session.phase(t)), Gsm.Gsm.bounded(more), e), Bd.sift(v, more, P.Bool.and_true_r(Gsm.Gsm.phase_bounded(S.Session.phase(t)), Gsm.Gsm.bounded(more), e)))

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

def Bd.tx_put(+st0: S.State, +ep: {Bd.pre(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Bd.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Bd.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  Bd.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss, e)

def Bd.tx_rephase(+st0: S.State, +ep: {Bd.pre(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Bd.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Bd.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  e

def Bd.tx_del(+st0: S.State, +ep: {Bd.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Bd.inv(st0, ues, ss) == True{} : Bool}) -> {Bd.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Bd.sift(S.SOthers{key}, ss, e)

def Bd.tx_put_session(+st0: S.State, +ep: {Bd.pre(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Bd.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Bd.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
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

def Kw.keep(+k: U32, +t: S.Session, +rest: Tb.Table(S.Session), b: Bool, +ht: {S.SPhase.knows(S.Session.phase(t), S.Session.known(t)) == True{} : Bool}, +hr: {S.Sessions.known(rest) == True{} : Bool}) -> {S.Sessions.known(Tb.Table.keep(S.Session, k, t, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(S.SPhase.knows(S.Session.phase(t), S.Session.known(t)), S.Sessions.known(rest), ht, hr)
    case False{}:
      hr

def Kw.sift(+v: S.SSieve, ss: Tb.Table(S.Session), +e: {S.Sessions.known(ss) == True{} : Bool}) -> {S.Sessions.known(S.Sessions.sift(v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +x = S.SPhase.knows(S.Session.phase(t), S.Session.known(t))
      Kw.keep(k, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k, t), P.Bool.and_true_l(x, S.Sessions.known(more), e), Kw.sift(v, more, P.Bool.and_true_r(x, S.Sessions.known(more), e)))

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

def Kw.tx_put(+st0: S.State, +ep: {Kw.pre(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Kw.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {Kw.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  Kw.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss, e)

def Kw.tx_rephase(+st0: S.State, +ep: {Kw.pre(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Kw.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {Kw.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  e

def Kw.tx_del(+st0: S.State, +ep: {Kw.pre(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Kw.inv(st0, ues, ss) == True{} : Bool}) -> {Kw.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  Kw.sift(S.SOthers{key}, ss, e)

def Kw.tx_put_session(+st0: S.State, +ep: {Kw.pre(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {Kw.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {Kw.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
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
# (S.Sessions.released), and none at all when the UPF does not know the
# session, and its actions delete the session at the UPF whenever the UPF
# knows it. A failure's outcome joins the release of the session with steps
# that put no session.

def Rel.Spec(+o: N.GOut(), +skey: U32, +s: S.Session) -> Type:
  (@st2: S.State -> {S.Sessions.released(skey, S.State.sessions(S.Tx.apply(N.Out.tx(o), st2))) == True{} : Bool}) & (({S.Session.known(s) == False{} : Bool} -> @st2: S.State -> {Tb.Table.get(S.Session, skey, S.State.sessions(S.Tx.apply(N.Out.tx(o), st2))) == None{} : Maybe<&2, S.Session>}) & ({S.Session.known(s) == True{} : Bool} -> {S.SPhase.held(S.Session.phase(s)) == True{} : Bool} -> Up.N4.deleted(s, N.Out.acts(o))))

def Rel.Law(+r: N.Step(), +skey: U32, +s: S.Session) -> Type:
  {S.Sessions.released(skey, S.State.sessions(K.Kernel.state(r))) == True{} : Bool} & (({S.Session.known(s) == False{} : Bool} -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(r))) == None{} : Maybe<&2, S.Session>}) & ({S.Session.known(s) == True{} : Bool} -> {S.SPhase.held(S.Session.phase(s)) == True{} : Bool} -> Up.N4.deleted(s, K.Kernel.actions(r))))

def App.assoc(xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +zs: List<&2, N.Act>) -> {List.append(&2, N.Act, xs, List.append(&2, N.Act, ys, zs)) == List.append(&2, N.Act, List.append(&2, N.Act, xs, ys), zs) : List<&2, N.Act>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> more:
      Equal.cong(List<&2, N.Act>, List<&2, N.Act>, l => x <> l, List.append(&2, N.Act, more, List.append(&2, N.Act, ys, zs)), List.append(&2, N.Act, List.append(&2, N.Act, more, ys), zs), App.assoc(more, ys, zs))

def Del.app_r.eq(+xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +pre: List<&2, N.Act>, +a: N.Act, +post: List<&2, N.Act>, e: {ys == List.append(&2, N.Act, pre, a <> post) : List<&2, N.Act>}) -> {List.append(&2, N.Act, xs, ys) == List.append(&2, N.Act, List.append(&2, N.Act, xs, pre), a <> post) : List<&2, N.Act>}:
  se = Equal.sym(List<&2, N.Act>, ys, List.append(&2, N.Act, pre, a <> post), e)
  %se : {List.append(&2, N.Act, xs, _) == List.append(&2, N.Act, List.append(&2, N.Act, xs, pre), a <> post) : List<&2, N.Act>}
  App.assoc(xs, pre, a <> post)

def Del.app_l.eq(+xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +pre: List<&2, N.Act>, +a: N.Act, +post: List<&2, N.Act>, e: {xs == List.append(&2, N.Act, pre, a <> post) : List<&2, N.Act>}) -> {List.append(&2, N.Act, xs, ys) == List.append(&2, N.Act, pre, a <> List.append(&2, N.Act, post, ys)) : List<&2, N.Act>}:
  se = Equal.sym(List<&2, N.Act>, xs, List.append(&2, N.Act, pre, a <> post), e)
  %se : {List.append(&2, N.Act, _, ys) == List.append(&2, N.Act, pre, a <> List.append(&2, N.Act, post, ys)) : List<&2, N.Act>}
  Equal.sym(List<&2, N.Act>, List.append(&2, N.Act, pre, List.append(&2, N.Act, a <> post, ys)), List.append(&2, N.Act, List.append(&2, N.Act, pre, a <> post), ys), App.assoc(pre, a <> post, ys))

def Del.app_r(+s: S.Session, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, d: Up.N4.deleted(s, ys)) -> Up.N4.deleted(s, List.append(&2, N.Act, xs, ys)):
  (+seq, (+pre, (+post, e))) = d
  (seq, (List.append(&2, N.Act, xs, pre), (post, Del.app_r.eq(xs, ys, pre, N.Pfcp{Some{S.Session.ue(s)}, Up.N4.delete(S.Session.up_seid(s), seq)}, post, e))))

def Del.app_l(+s: S.Session, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, d: Up.N4.deleted(s, xs)) -> Up.N4.deleted(s, List.append(&2, N.Act, xs, ys)):
  (+seq, (+pre, (+post, e))) = d
  (seq, (pre, (List.append(&2, N.Act, post, ys), Del.app_l.eq(xs, ys, pre, N.Pfcp{Some{S.Session.ue(s)}, Up.N4.delete(S.Session.up_seid(s), seq)}, post, e))))

def Rel.step(+st: S.State, +o: N.GOut(), +skey: U32, +s: S.Session, h: Rel.Spec(o, skey, s)) -> Rel.Law(N.Step.of(st, o), skey, s):
  match o:
    case (+tx, +acts):
      (g, (n, d)) = h
      (g(st), (kf => n(kf, st), k => eh => Del.app_l(s, acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))), d(k, eh))))

def Rel.by(+r: N.Step(), +st: S.State, +o: N.GOut(), +skey: U32, +s: S.Session, eq: {r == N.Step.of(st, o) : N.Step()}, h: Rel.Spec(o, skey, s)) -> Rel.Law(r, skey, s):
  se = Equal.sym(N.Step(), r, N.Step.of(st, o), eq)
  %se : Rel.Law(_, skey, s)
  Rel.step(st, o, skey, s, h)

# The deletion among the actions
# ------------------------------

# The Session Deletion of a session the UPF knows, tagged with its UE.
def Del.one(+skey: U32, +s: S.Session, +seq: U32, k: {S.Session.known(s) == True{} : Bool}, eh: {S.SPhase.held(S.Session.phase(s)) == True{} : Bool}) -> Up.N4.deleted(s, N.Out.acts(Up.N4.deletions([(skey, s)], seq))):
  sk = Equal.sym(Bool, S.Session.known(s), True{}, k)
  %sk : Up.N4.deleted(s, N.Out.acts(Up.N4.delete_if(skey, s, seq, q => Up.N4.deletions([], q), _)))
  +request = Up.N4.delete(S.Session.up_seid(s), seq)
  +y : N.Act = N.TimerStart{S.Session.tag(s), skey, Up.N4.t1_ms()}
  seh = Equal.sym(Bool, S.SPhase.held(S.Session.phase(s)), True{}, eh)
  (seq, ([], ([y], (%seh : {[N.Pfcp{Tb.Table.hit(U32, S.Session.ue(s), None{}, _), request}, y] == List.append(&2, N.Act, [], N.Pfcp{Some{S.Session.ue(s)}, request} <> [y]) : List<&2, N.Act>}; {==}))))

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

def None.keep(+k: U32, +k0: U32, +t: S.Session, +rest: Tb.Table(S.Session), b: Bool, +h0: {U32.is_eq(k0, k) == False{} : Bool}, +hr: {Tb.Table.get(S.Session, k, rest) == None{} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, k, Tb.Table.keep(S.Session, k0, t, rest, b)) == None{} : Maybe<&2, S.Session>}:
  match b:
    case True{}:
      None.hit(t, Tb.Table.get(S.Session, k, rest), U32.is_eq(k0, k), h0, hr)
    case False{}:
      hr

def None.sift(+v: S.SSieve, ss: Tb.Table(S.Session), +k: U32, +h: {Tb.Table.get(S.Session, k, ss) == None{} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, k, S.Sessions.sift(v, ss)) == None{} : Maybe<&2, S.Session>}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      None.row(k, k0, t, more, U32.is_eq(k0, k), {==}, h, {Tb.Table.get(S.Session, k, S.Sessions.sift(v, (k0, t) <> more)) == None{} : Maybe<&2, S.Session>}, h0 => hr => None.keep(k, k0, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k0, t), h0, None.sift(v, more, k, hr)))

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

# Released keys
# -------------
# A row of a key released belongs to no UE: whatever puts no session keeps it
# so, deleting a session at the UPF leaves its row so, and forgetting it
# leaves none.

def Rl.keep(+key: U32, +k: U32, +t: S.Session, +rest: Tb.Table(S.Session), +b: Bool, +ht: {Bool.or(Bool.not(U32.is_eq(k, key)), Bool.not(Tb.Table.present(U32, S.Session.tag(t)))) == True{} : Bool}, +hr: {S.Sessions.released(key, rest) == True{} : Bool}) -> {S.Sessions.released(key, Tb.Table.keep(S.Session, k, t, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k, key)), Bool.not(Tb.Table.present(U32, S.Session.tag(t)))), S.Sessions.released(key, rest), ht, hr)
    case False{}:
      hr

def Rl.sift(+v: S.SSieve, ss: Tb.Table(S.Session), +key: U32, +e: {S.Sessions.released(key, ss) == True{} : Bool}) -> {S.Sessions.released(key, S.Sessions.sift(v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +x = Bool.or(Bool.not(U32.is_eq(k, key)), Bool.not(Tb.Table.present(U32, S.Session.tag(t))))
      Rl.keep(key, k, t, S.Sessions.sift(v, more), S.SSieve.keeps(v, k, t), P.Bool.and_true_l(x, S.Sessions.released(key, more), e), Rl.sift(v, more, key, P.Bool.and_true_r(x, S.Sessions.released(key, more), e)))

def Rl.or_mono(+x: Bool, +a: Bool, +a2: Bool, +e: {Bool.or(x, a) == True{} : Bool}, f: {a == True{} : Bool} -> {a2 == True{} : Bool}) -> {Bool.or(x, a2) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      f(e)

def Rl.revar(+key2: U32, +v: S.SVar, ss: Tb.Table(S.Session), +key: U32, +e: {S.Sessions.released(key, ss) == True{} : Bool}) -> {S.Sessions.released(key, S.Sessions.revar(key2, v, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +hit = Bool.and(U32.is_eq(k, key2), S.SVar.follows(v, t))
      +t2 = S.Session.revar_if(t, v, hit)
      +x = Bool.or(Bool.not(U32.is_eq(k, key)), Bool.not(Tb.Table.present(U32, S.Session.tag(t))))
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k, key)), Bool.not(Tb.Table.present(U32, S.Session.tag(t2)))), S.Sessions.released(key, S.Sessions.revar(key2, v, more)), Rl.or_mono(Bool.not(U32.is_eq(k, key)), Bool.not(Tb.Table.present(U32, S.Session.tag(t))), Bool.not(Tb.Table.present(U32, S.Session.tag(t2))), P.Bool.and_true_l(x, S.Sessions.released(key, more), e), en => Cf.not_of(Tb.Table.present(U32, S.Session.tag(t2)), PW.Tg.untagged(t, t2, PW.Tg.revar(t, v, U32.is_eq(k, key2)), P.Bool.not_true(Tb.Table.present(U32, S.Session.tag(t)), en)))), Rl.revar(key2, v, more, key, P.Bool.and_true_r(x, S.Sessions.released(key, more), e)))

def Rl.free(+st0: S.State, tx: S.Tx, +st2: S.State, +k: U32, +h: {S.Sessions.released(k, S.State.sessions(st2)) == True{} : Bool}, +f: {PL.Lv.free(st0, tx) == True{} : Bool}) -> {S.Sessions.released(k, S.State.sessions(S.Tx.apply(tx, st2))) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      h
    case S.Put{+key, +ue}:
      match st2:
        case S.State{config, subs, assocs, +ues, +sessions, pfcp_seq, next_ue, n4}:
          Rl.sift(S.SOwned{S.Ues.put(key, ue, ues)}, sessions, k, h)
    case S.Del{+key}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Rl.sift(S.SOthers{key}, sessions, k, h)
    case S.PutSession{key, s}:
      Empty.absurd({S.Sessions.released(k, S.State.sessions(S.Tx.apply(S.PutSession{key, s}, st2))) == True{} : Bool}, P.Refute.bool(f))
    case S.Revar{+key, +v}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Rl.revar(key, v, sessions, k, h)
    case S.DelSession{+key}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Rl.sift(S.SExcept{key}, sessions, k, h)
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
      Rl.free(st0, b, S.Tx.apply(a, st2), k, Rl.free(st0, a, st2, k, h, P.Bool.and_true_l(PL.Lv.free(st0, a), PL.Lv.free(st0, b), f)), P.Bool.and_true_r(PL.Lv.free(st0, a), PL.Lv.free(st0, b), f))

def Rl.del_keep(+key: U32, +k: U32, +t: S.Session, +rest: Tb.Table(S.Session), +b: Bool, +eb: {Bool.not(U32.is_eq(k, key)) == b : Bool}, +hr: {S.Sessions.released(key, rest) == True{} : Bool}) -> {S.Sessions.released(key, Tb.Table.keep(S.Session, k, t, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k, key)), Bool.not(Tb.Table.present(U32, S.Session.tag(t)))), S.Sessions.released(key, rest), P.Bool.or_l(Bool.not(U32.is_eq(k, key)), Bool.not(Tb.Table.present(U32, S.Session.tag(t))), eb), hr)
    case False{}:
      hr

def Rl.del(+key: U32, ss: Tb.Table(S.Session)) -> {S.Sessions.released(key, S.Sessions.del(key, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      Rl.del_keep(key, k, t, S.Sessions.sift(S.SExcept{key}, more), S.SSieve.keeps(S.SExcept{key}, k, t), {==}, Rl.del(key, more))

def Rl.untag(+t: S.Session, +u: B.Bytes(), +q: U32, +g: S.Guard, +r: B.Bytes()) -> {Bool.not(Tb.Table.present(U32, S.Session.tag(S.Session.revar_if(t, S.SVar{u, q, S.Deleting{g, r}}, True{})))) == True{} : Bool}:
  match t:
    case S.Session{id, var}:
      {==}

def Rl.deleting_row(+k: U32, +key: U32, +t: S.Session, +u: B.Bytes(), +q: U32, +g: S.Guard, +r: B.Bytes(), +c: Bool, +ec: {U32.is_eq(k, key) == c : Bool}) -> {Bool.or(Bool.not(U32.is_eq(k, key)), Bool.not(Tb.Table.present(U32, S.Session.tag(S.Session.revar_if(t, S.SVar{u, q, S.Deleting{g, r}}, Bool.and(U32.is_eq(k, key), True{})))))) == True{} : Bool}:
  match c:
    case True{}:
      sec = Equal.sym(Bool, U32.is_eq(k, key), True{}, ec)
      (%sec : {Bool.or(Bool.not(_), Bool.not(Tb.Table.present(U32, S.Session.tag(S.Session.revar_if(t, S.SVar{u, q, S.Deleting{g, r}}, Bool.and(_, True{})))))) == True{} : Bool}; Rl.untag(t, u, q, g, r))
    case False{}:
      sec = Equal.sym(Bool, U32.is_eq(k, key), False{}, ec)
      (%sec : {Bool.or(Bool.not(_), Bool.not(Tb.Table.present(U32, S.Session.tag(S.Session.revar_if(t, S.SVar{u, q, S.Deleting{g, r}}, Bool.and(U32.is_eq(k, key), True{})))))) == True{} : Bool}; {==})

# A session's row being deleted belongs to no UE.
def Rl.deleting(+key: U32, +u: B.Bytes(), +q: U32, +g: S.Guard, +r: B.Bytes(), ss: Tb.Table(S.Session)) -> {S.Sessions.released(key, S.Sessions.revar(key, S.SVar{u, q, S.Deleting{g, r}}, ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      +t2 = S.Session.revar_if(t, S.SVar{u, q, S.Deleting{g, r}}, Bool.and(U32.is_eq(k, key), True{}))
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k, key)), Bool.not(Tb.Table.present(U32, S.Session.tag(t2)))), S.Sessions.released(key, S.Sessions.revar(key, S.SVar{u, q, S.Deleting{g, r}}, more)), Rl.deleting_row(k, key, t, u, q, g, r, U32.is_eq(k, key), {==}), Rl.deleting(key, u, q, g, r, more))

# Releases
# --------

def Rel.dg(+skey: U32, +s: S.Session, +seq: U32, +b: Bool, +st2: S.State) -> {S.Sessions.released(skey, S.State.sessions(S.Tx.apply(N.Out.tx(Up.N4.delete_if(skey, s, seq, q => Up.N4.deletions([], q), b)), st2))) == True{} : Bool}:
  match b:
    case True{}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Rl.deleting(skey, S.Session.up_seid(s), seq, S.Guard{0}, Up.N4.delete(S.Session.up_seid(s), seq), sessions)
    case False{}:
      match st2:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Rl.del(skey, sessions)

def Rel.dn(+skey: U32, +s: S.Session, +seq: U32, +b: Bool, +eb: {S.Session.known(s) == b : Bool}, +kf: {S.Session.known(s) == False{} : Bool}, +st2: S.State) -> {Tb.Table.get(S.Session, skey, S.State.sessions(S.Tx.apply(N.Out.tx(Up.N4.delete_if(skey, s, seq, q => Up.N4.deletions([], q), b)), st2))) == None{} : Maybe<&2, S.Session>}:
  match b:
    case True{}:
      Empty.absurd({Tb.Table.get(S.Session, skey, S.State.sessions(S.Tx.apply(N.Out.tx(Up.N4.delete_if(skey, s, seq, q => Up.N4.deletions([], q), True{})), st2))) == None{} : Maybe<&2, S.Session>}, P.Refute.true_false(Equal.trans(Bool, True{}, S.Session.known(s), False{}, Equal.sym(Bool, S.Session.known(s), True{}, eb), kf)))
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
          (+st2 => g(S.Tx.apply(ta, st2)), (kf => +st2 => n(kf, S.Tx.apply(ta, st2)), k => eh => Del.app_r(s, aa, ab, d(k, eh))))

# Nor does what comes after it, when that puts no session.
def Rel.join_l(+st0: S.State, +a: N.GOut(), +b: N.GOut(), +skey: U32, +s: S.Session, h: Rel.Spec(a, skey, s), +f: {PL.Lv.free(st0, N.Out.tx(b)) == True{} : Bool}) -> Rel.Spec(N.Out.join(a, b), skey, s):
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          (g, (n, d)) = h
          (+st2 => Rl.free(st0, tb, S.Tx.apply(ta, st2), skey, g(st2), f), (kf => +st2 => None.free(st0, tb, S.Tx.apply(ta, st2), skey, n(kf, st2), f), k => eh => Del.app_l(s, aa, ab, d(k, eh))))

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
      Rel.join_r((S.BumpSeq{1}, []), N.Out.join(a, b), skey, s, Rel.join_l(st, a, b, skey, s, Rel.failed(st, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), skey, s, guard, pti, es, eh), P.Bool.and_true_r(PL.Lv.acts(st, N.Out.acts(b)), PL.Lv.free(st, N.Out.tx(b)), PL.Lw.faileds(st, key, post, U32.add(seq, 1)))))
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

def Step.gnb_failed(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +k: U32, +ran: B.Bytes(), +oks: Maybe<&2, G.PDUSessionResourceSetupListSURes()>, +fails: G.PDUSessionResourceFailedToSetupListSURes(), +diag: Maybe<&2, G.CriticalityDiagnostics>, +uli: Maybe<&2, G.UserLocationInformation>, +ue: S.Ue, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 29, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ev: {V.PDUSessionResourceSetupResponse.view(ies) == Done{V.PDUSessionResourceSetupResponse.View{amf, ran, oks, Some{fails}, diag, uli}} : Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>}, eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == N.Step.of(st, Gsm.Gsm.results(st, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), fails)) : N.Step()}:
  +T : N.Step() = N.Step.of(st, Gsm.Gsm.results(st, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), fails))
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(1), U32.to_nat(29), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(1), U32.to_nat(29)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 1, 29, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {_ == T : N.Step()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>, V.PDUSessionResourceSetupResponse.view(ies), Done{V.PDUSessionResourceSetupResponse.View{amf, ran, oks, Some{fails}, diag, uli}}, ev)
  %sev : {N.Step.of(st, Gsm.Gsm.setup_response_of_view(st, assoc, _)) == T : N.Step()}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sek : {N.Step.of(st, Gsm.Gsm.setup_response_key(st, assoc, ran, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), fails, _)) == T : N.Step()}
  seo = Equal.sym(Maybe<&2, S.Ue>, N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran), Some{ue}, eo)
  %seo : {N.Step.of(st, Gsm.Gsm.setup_response_ue(st, assoc, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), fails, _)) == T : N.Step()}
  {==}

# A session past Creating is known to the UPF.
def Kn.past(+s: S.Session, +p: S.SPhase, +ep: {S.Session.phase(s) == p : S.SPhase}, +k: {S.SPhase.knows(S.Session.phase(s), S.Session.known(s)) == True{} : Bool}) -> {S.SPhase.knows(p, S.Session.known(s)) == True{} : Bool}:
  %ep : {S.SPhase.knows(_, S.Session.known(s)) == True{} : Bool}
  k

# A session in a phase that belongs to a UE.
def Kn.held(+s: S.Session, +p: S.SPhase, +ep: {S.Session.phase(s) == p : S.SPhase}, +h: {S.SPhase.held(p) == True{} : Bool}) -> {S.SPhase.held(S.Session.phase(s)) == True{} : Bool}:
  sep = Equal.sym(S.SPhase, S.Session.phase(s), p, ep)
  (%sep : {S.SPhase.held(_) == True{} : Bool}; h)

# A session being created is not known to the UPF.
def Kn.creating(+s: S.Session, +guard: S.Guard, +pti: U32, +accept: Sm.Sm, +request: B.Bytes(), +ep: {S.Session.phase(s) == S.Creating{guard, pti, accept, request} : S.SPhase}, +k: {S.SPhase.knows(S.Session.phase(s), S.Session.known(s)) == True{} : Bool}) -> {S.Session.known(s) == False{} : Bool}:
  P.Bool.not_true(S.Session.known(s), Kn.past(s, S.Creating{guard, pti, accept, request}, ep, k))

# The release alone, of a session the UPF never knew.
def Fail.gone(+r: N.Step(), +skey: U32, +s: S.Session, h: Rel.Law(r, skey, s), +kf: {S.Session.known(s) == False{} : Bool}) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(r))) == None{} : Maybe<&2, S.Session>}:
  (g, (n, d)) = h
  n(kf)

def Fail.known(+r: N.Step(), +skey: U32, +s: S.Session, h: Rel.Law(r, skey, s), +k: {S.Session.known(s) == True{} : Bool}, +eh: {S.SPhase.held(S.Session.phase(s)) == True{} : Bool}) -> {S.Sessions.released(skey, S.State.sessions(K.Kernel.state(r))) == True{} : Bool} & Up.N4.deleted(s, K.Kernel.actions(r)):
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

def Fail.timer(+st: S.State, +entropy: B.Bytes(), +skey: U32, +s: S.Session, +guard: S.Guard, +pti: U32, +accept: Sm.Sm, +request: B.Bytes(), +ek: {S.Sessions.known(S.State.sessions(st)) == True{} : Bool}, +et: {Tb.Table.get(S.Ue, skey, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}, +eg: {Tb.Table.get(S.Session, skey, S.State.sessions(st)) == Some{s} : Maybe<&2, S.Session>}) -> ({S.Session.phase(s) == S.Setting{guard, pti} : S.SPhase} -> {S.Sessions.released(skey, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{skey}, entropy)))) == True{} : Bool} & Up.N4.deleted(s, K.Kernel.actions(K.Kernel.step(st, F.TimerFired{skey}, entropy)))) & (({S.Session.phase(s) == S.Creating{guard, pti, accept, request} : S.SPhase} -> {U32.is_lt(S.Guard.retries(guard), Up.N4.n1()) == False{} : Bool} -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{skey}, entropy)))) == None{} : Maybe<&2, S.Session>}) & ({S.Session.phase(s) == S.Modifying{guard, request} : S.SPhase} -> {U32.is_lt(S.Guard.retries(guard), Up.N4.n1()) == False{} : Bool} -> {S.Sessions.released(skey, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{skey}, entropy)))) == True{} : Bool} & Up.N4.deleted(s, K.Kernel.actions(K.Kernel.step(st, F.TimerFired{skey}, entropy))))):
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
     eup => ep => ei => ev => eid => eo => +es => +eh => Fail.known(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), skey, s, Rel.by(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), st, Gsm.Gsm.results(st, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), fails), skey, s, Step.gnb_failed(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, ran, oks, fails, diag, uli, ue, ep, ei, ev, eid, eo, eup), Rel.join_r(Gsm.Gsm.set_ups(st, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), S.State.pfcp_seq(st)), Gsm.Gsm.faileds(st, k, fails, seq2), skey, s, Rel.faileds(st, k, pre, psi, transfer, x, post, seq2, skey, s, guard, pti, es, eh))), Kn.past(s, S.Setting{guard, pti}, eh, PL.Lv.found_known(S.Sessions.by_psi(k, psi, ss), ss, skey, s, es, PL.Lv.by_psi(k, psi, ss), ek)), Kn.held(s, S.Setting{guard, pti}, eh, {==})))))

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
def Re.tag(+s: S.Session, +p: S.SPhase, +ep: {S.Session.phase(s) == p : S.SPhase}) -> {S.Session.tag(s) == Tb.Table.hit(U32, S.Session.ue(s), None{}, S.SPhase.held(p)) : Maybe<&2, U32>}:
  (%ep : {S.Session.tag(s) == Tb.Table.hit(U32, S.Session.ue(s), None{}, S.SPhase.held(_)) : Maybe<&2, U32>}; {==})

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

def Ans.stops(+st: S.State, +skey: U32, +s: S.Session, +guard: S.Guard, +request: B.Bytes(), +seq: U32, +es: {S.Sessions.by_seq(seq, S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, +ep: {S.Session.phase(s) == S.Deleting{guard, request} : S.SPhase}) -> {N.Acts.stops(skey, K.Kernel.actions(N.Step.of(st, (S.DelSession{skey}, [])))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
      Ans.by_seq(seq, sessions, S.Sessions.del(skey, sessions))(skey, s, guard, es, De.guard(s, guard, request, ep), Ans.has_del(skey, sessions))

def Step.answered(+st: S.State, +entropy: B.Bytes(), +len: U32, +bytes: B.Bytes(), +msg: Pf.Msg, +rest: B.Bytes(), +skey: U32, +s: S.Session, +guard: S.Guard, +request: B.Bytes(), em: {Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)}, ek: {Pf.Msg.kind(msg) == 55 : U32}, es: {S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, ep: {S.Session.phase(s) == S.Deleting{guard, request} : S.SPhase}) -> {K.Kernel.step(st, F.PfcpData{len, bytes}, entropy) == N.Step.of(st, (S.DelSession{skey}, [])) : N.Step()}:
  +T : N.Step() = N.Step.of(st, (S.DelSession{skey}, []))
  sem = Equal.sym(B.Read(Pf.Msg), Pf.Msg.read(bytes), Done{(msg, rest)}, em)
  %sem : {N.Step.of(st, Gsm.Gsm.pfcp_msg(st, _)) == T : N.Step()}
  sek = Equal.sym(U32, Pf.Msg.kind(msg), 55, ek)
  %sek : {N.Step.of(st, Gsm.Gsm.pfcp_k1(st, msg, _, U32.is_eq(_, 1))) == T : N.Step()}
  ses = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Some{(skey, s)}, es)
  %ses : {N.Step.of(st, Gsm.Gsm.deleted(_)) == T : N.Step()}
  sep = Equal.sym(S.SPhase, S.Session.phase(s), S.Deleting{guard, request}, ep)
  %sep : {N.Step.of(st, Gsm.Gsm.deleted_phase(skey, _)) == T : N.Step()}
  {==}

def L.smf.deletion.answered(st, entropy, len, bytes, msg, rest, skey, s, guard, request, em, ek, es, ep):
  +r = K.Kernel.step(st, F.PfcpData{len, bytes}, entropy)
  +T : N.Step() = N.Step.of(st, (S.DelSession{skey}, []))
  sr1 = Equal.sym(N.Step(), r, T, Step.answered(st, entropy, len, bytes, msg, rest, skey, s, guard, request, em, ek, es, ep))
  sr2 = Equal.sym(N.Step(), r, T, Step.answered(st, entropy, len, bytes, msg, rest, skey, s, guard, request, em, ek, es, ep))
  ((%sr1 : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(_))) == None{} : Maybe<&2, S.Session>}; De.gone(st, skey, [])), (%sr2 : {N.Acts.stops(skey, K.Kernel.actions(_)) == True{} : Bool}; Ans.stops(st, skey, s, guard, request, Pf.Msg.seq(msg), es, ep)))

# What a UL NAS Transport comes to
# --------------------------------
# A verified UL NAS Transport from a registered UE is answered by the N1 SM
# message handler; the step is that answer rendered.

def Transport.out(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +k: U32, +ran: B.Bytes(), +nas: B.Bytes(), uli: G.UserLocationInformation, +ue: S.Ue, +ctx: Sec.Nas.Ctx, prot: Sec.Nas.Protection, +plain: B.Bytes(), count: Sec.Nas.Count, +ctx2: Sec.Nas.Ctx, old: Sec.Nas.Ctx, +nh: S.Nh, +released: Maybe<&2, S.Side>, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ev: {V.UplinkNASTransport.view(ies) == Done{V.UplinkNASTransport.View{amf, ran, nas, uli}} : Result<&2, &2, B.Err, V.UplinkNASTransport.View>}, eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, eo: {Gmm.Gmm.owner(st, assoc, k, ran) == Some{ue} : Maybe<&2, S.Ue>}, ec: {S.Phase.ctx(S.Ue.phase(ue)) == Some{ctx} : Maybe<&2, Sec.Nas.Ctx>}, eu: {Sec.Nas.unprotect(ctx, nas) == Done{Sec.Unprotected{prot, plain, count, ctx2}} : Result<&2, &2, B.Err, Sec.Nas.Unprotected>}, em: {Mm.Mm.read(plain) == Done{Mm.Mm{Mm.UlNasTransport{}, fields, opts}} : Result<&2, &2, B.Err, Mm.Mm>}, er: {S.Ue.phase(ue) == S.Registered{old, nh, released} : S.Phase}, en: {U32.is_eq(I.Fields.byte1(fields), 1) == True{} : Bool}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, Sm.Sm.read(I.Fields.lve2(fields)))) : N.Step()}:
  +R : N.Step() = N.Step.of(st, Gsm.Gsm.message(st, k, ue, ctx2, opts, entropy, Sm.Sm.read(I.Fields.lve2(fields))))
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(0), U32.to_nat(46), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(0), U32.to_nat(46)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 0, 46, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {_ == R : N.Step()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UplinkNASTransport.View>, V.UplinkNASTransport.view(ies), Done{V.UplinkNASTransport.View{amf, ran, nas, uli}}, ev)
  %sev : {N.Step.of(st, Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, _)) == R : N.Step()}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sek : {N.Step.of(st, Gmm.Gmm.uplink_key(st, assoc, ran, nas, entropy, _)) == R : N.Step()}
  seo = Equal.sym(Maybe<&2, S.Ue>, Gmm.Gmm.owner(st, assoc, k, ran), Some{ue}, eo)
  %seo : {N.Step.of(st, Gmm.Gmm.uplink_ue(st, assoc, k, nas, entropy, _)) == R : N.Step()}
  sec = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.ctx(S.Ue.phase(ue)), Some{ctx}, ec)
  %sec : {N.Step.of(st, Gmm.Gmm.secured(st, k, ue, entropy, nas, _)) == R : N.Step()}
  seu = Equal.sym(Result<&2, &2, B.Err, Sec.Nas.Unprotected>, Sec.Nas.unprotect(ctx, nas), Done{Sec.Unprotected{prot, plain, count, ctx2}}, eu)
  %seu : {N.Step.of(st, Gmm.Gmm.opened(st, k, ue, entropy, _)) == R : N.Step()}
  sem = Equal.sym(Result<&2, &2, B.Err, Mm.Mm>, Mm.Mm.read(plain), Done{Mm.Mm{Mm.UlNasTransport{}, fields, opts}}, em)
  %sem : {N.Step.of(st, Gmm.Gmm.protected(st, k, ue, entropy, count, ctx2, _)) == R : N.Step()}
  ser = Equal.sym(S.Phase, S.Ue.phase(ue), S.Registered{old, nh, released}, er)
  %ser : {N.Step.of(st, Gmm.Gmm.sphase(st, k, ue, entropy, count, ctx2, Mm.UlNasTransport{}, fields, opts, _)) == R : N.Step()}
  sen = Equal.sym(Bool, U32.is_eq(I.Fields.byte1(fields), 1), True{}, en)
  %sen : {N.Step.of(st, Gsm.Gsm.n1(st, k, ue, ctx2, opts, entropy, I.Fields.lve2(fields), _)) == R : N.Step()}
  {==}

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
