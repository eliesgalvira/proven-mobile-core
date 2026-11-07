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
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/gmm.bend as Gmm
import ../amf/route.bend as R
import ../smf/n4.bend as Up
import ../smf/gsm.bend as Gsm
import ../LAWS.bend as L
import ./lib.bend as P
import ./kernel.bend as PK

# Proofs of the SMF's laws (ticket 19).

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

# A change of a session's variable part leaves every conflict as it was.
def Session.conflicts_revar(hit: Bool, a: S.Session, b: S.Session, v: S.SVar) -> {S.Session.conflicts(a, S.Session.revar_if(b, v, hit)) == S.Session.conflicts(a, b) : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      match b:
        case S.Session{id, var}:
          {==}

def Session.conflicts_revar_l(hit: Bool, a: S.Session, b: S.Session, v: S.SVar) -> {S.Session.conflicts(S.Session.revar_if(a, v, hit), b) == S.Session.conflicts(a, b) : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      match a:
        case S.Session{id, var}:
          {==}

def SRow.conflicts_revar(key: U32, s: S.Session, k: U32, t: S.Session, v: S.SVar, hit: Bool) -> {S.SRow.conflicts(key, s, k, S.Session.revar_if(t, v, hit)) == S.SRow.conflicts(key, s, k, t) : Bool}:
  e = Equal.sym(Bool, S.Session.conflicts(s, S.Session.revar_if(t, v, hit)), S.Session.conflicts(s, t), Session.conflicts_revar(hit, s, t, v))
  %e : {Bool.or(U32.is_eq(k, key), _) == Bool.or(U32.is_eq(k, key), S.Session.conflicts(s, t)) : Bool}
  {==}

def SRow.conflicts_revar_l(key: U32, s: S.Session, k: U32, t: S.Session, v: S.SVar, hit: Bool) -> {S.SRow.conflicts(key, S.Session.revar_if(s, v, hit), k, t) == S.SRow.conflicts(key, s, k, t) : Bool}:
  e = Equal.sym(Bool, S.Session.conflicts(S.Session.revar_if(s, v, hit), t), S.Session.conflicts(s, t), Session.conflicts_revar_l(hit, s, t, v))
  %e : {Bool.or(U32.is_eq(k, key), _) == Bool.or(U32.is_eq(k, key), S.Session.conflicts(s, t)) : Bool}
  {==}

def SClear.revar(+key2: U32, +s: S.Session, +key: U32, +v: S.SVar, sessions: Tb.Table(S.Session)) -> {S.Sessions.clear(key2, s, S.Sessions.revar(key, v, sessions)) == S.Sessions.clear(key2, s, sessions) : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      e1 = Equal.sym(Bool, S.SRow.conflicts(key2, s, k, S.Session.revar_if(t, v, U32.is_eq(k, key))), S.SRow.conflicts(key2, s, k, t), SRow.conflicts_revar(key2, s, k, t, v, U32.is_eq(k, key)))
      %e1 : {Bool.and(Bool.not(_), S.Sessions.clear(key2, s, S.Sessions.revar(key, v, more))) == Bool.and(Bool.not(S.SRow.conflicts(key2, s, k, t)), S.Sessions.clear(key2, s, more)) : Bool}
      e2 = Equal.sym(Bool, S.Sessions.clear(key2, s, S.Sessions.revar(key, v, more)), S.Sessions.clear(key2, s, more), SClear.revar(key2, s, key, v, more))
      %e2 : {Bool.and(Bool.not(S.SRow.conflicts(key2, s, k, t)), _) == Bool.and(Bool.not(S.SRow.conflicts(key2, s, k, t)), S.Sessions.clear(key2, s, more)) : Bool}
      {==}

def SClear.subject_revar(+key: U32, +s: S.Session, +v: S.SVar, +hit: Bool, sessions: Tb.Table(S.Session)) -> {S.Sessions.clear(key, S.Session.revar_if(s, v, hit), sessions) == S.Sessions.clear(key, s, sessions) : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +t) <> +more:
      e1 = Equal.sym(Bool, S.SRow.conflicts(key, S.Session.revar_if(s, v, hit), k, t), S.SRow.conflicts(key, s, k, t), SRow.conflicts_revar_l(key, s, k, t, v, hit))
      %e1 : {Bool.and(Bool.not(_), S.Sessions.clear(key, S.Session.revar_if(s, v, hit), more)) == Bool.and(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, more)) : Bool}
      e2 = Equal.sym(Bool, S.Sessions.clear(key, S.Session.revar_if(s, v, hit), more), S.Sessions.clear(key, s, more), SClear.subject_revar(key, s, v, hit, more))
      %e2 : {Bool.and(Bool.not(S.SRow.conflicts(key, s, k, t)), _) == Bool.and(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, more)) : Bool}
      {==}

def SUnique.revar(+key: U32, +v: S.SVar, sessions: Tb.Table(S.Session)) -> {S.Sessions.unique(S.Sessions.revar(key, v, sessions)) == S.Sessions.unique(sessions) : Bool}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +s) <> +more:
      e1 = Equal.sym(Bool, S.Sessions.clear(k, S.Session.revar_if(s, v, U32.is_eq(k, key)), S.Sessions.revar(key, v, more)), S.Sessions.clear(k, s, S.Sessions.revar(key, v, more)), SClear.subject_revar(k, s, v, U32.is_eq(k, key), S.Sessions.revar(key, v, more)))
      %e1 : {Bool.and(_, S.Sessions.unique(S.Sessions.revar(key, v, more))) == Bool.and(S.Sessions.clear(k, s, more), S.Sessions.unique(more)) : Bool}
      e2 = Equal.sym(Bool, S.Sessions.clear(k, s, S.Sessions.revar(key, v, more)), S.Sessions.clear(k, s, more), SClear.revar(k, s, key, v, more))
      %e2 : {Bool.and(_, S.Sessions.unique(S.Sessions.revar(key, v, more))) == Bool.and(S.Sessions.clear(k, s, more), S.Sessions.unique(more)) : Bool}
      e3 = Equal.sym(Bool, S.Sessions.unique(S.Sessions.revar(key, v, more)), S.Sessions.unique(more), SUnique.revar(key, v, more))
      %e3 : {Bool.and(S.Sessions.clear(k, s, more), _) == Bool.and(S.Sessions.clear(k, s, more), S.Sessions.unique(more)) : Bool}
      {==}

# Sessions stay unique
# --------------------

def Tx.sunique(tx: S.Tx, +st: S.State, e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(S.Tx.apply(tx, st))) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      e
    case S.Put{+key, +ue}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          SUnique.sift(S.SOwned{S.Ues.put(key, ue, ues)}, sessions, e)
    case S.Rephase{key, phase}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.Del{+key}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          SUnique.sift(S.SOthers{key}, sessions, e)
    case S.PutSession{+key, +s}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, next_timer, n4}:
          P.Bool.and_intro(S.Sessions.clear(key, s, S.Sessions.sift(S.SClear{key, s}, sessions)), S.Sessions.unique(S.Sessions.sift(S.SClear{key, s}, sessions)), SClear.own(key, s, sessions), SUnique.sift(S.SClear{key, s}, sessions, e))
    case S.Revar{+key, +v}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, next_timer, n4}:
          er = Equal.sym(Bool, S.Sessions.unique(S.Sessions.revar(key, v, sessions)), S.Sessions.unique(sessions), SUnique.revar(key, v, sessions))
          %er : {_ == True{} : Bool}
          e
    case S.DelSession{+key}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          SUnique.sift(S.SExcept{key}, sessions, e)
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
    case S.Both{+first, second}:
      Tx.sunique(second, S.Tx.apply(first, st), Tx.sunique(first, st, e))

def Render.sunique(st: S.State, o: N.GOut(), e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(K.Kernel.state(N.Step.of(st, o)))) == True{} : Bool}:
  match o:
    case (tx, acts):
      Tx.sunique(tx, st, e)

def Setup.sunique(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.NGSetupRequest.View>, e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(K.Kernel.state(N.NgSetup.of_view(st, assoc, r)))) == True{} : Bool}:
  match r:
    case Fail{err}:
      e
    case Done{v}:
      e

def Route.d1_sunique(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool, e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(K.Kernel.state(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, ok)))) == True{} : Bool}:
  match ok:
    case True{}:
      Setup.sunique(st, assoc, V.NGSetupRequest.view(ies), e)
    case False{}:
      Render.sunique(st, R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n)), e)

def Route.ies_sunique(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, entropy: B.Bytes(), r: Ap.Rd(List<&2, Fr.Ie>), e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(K.Kernel.state(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r)))) == True{} : Bool}:
  match r:
    case Fail{err}:
      e
    case Done{(+ies, c)}:
      Route.d1_sunique(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 21n), e)

def Route.pdu_sunique(+st: S.State, +assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Fr.Pdu>, e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(K.Kernel.state(R.Route.of_pdu(st, assoc, stream, entropy, r)))) == True{} : Bool}:
  match r:
    case Fail{err}:
      e
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Route.ies_sunique(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), e)

def Config.sunique(complete: Bool, st: S.State, tlvs: List<&2, T.Tlv>, entropy: B.Bytes(), e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(K.Kernel.state(K.Kernel.config(complete, st, tlvs, entropy)))) == True{} : Bool}:
  match complete:
    case False{}:
      e
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e

def AssocUp.sunique(st: S.State, assoc: U32, e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(K.Kernel.state(K.Kernel.assoc_up(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      e

def Down.sunique(st: S.State, +assoc: U32, e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(K.Kernel.state(K.Kernel.assoc_down(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      SUnique.sift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, sessions, e)

def Step.sunique(+st: S.State, ev: F.Evt, +entropy: B.Bytes(), e: {S.Sessions.unique(S.State.sessions(st)) == True{} : Bool}) -> {S.Sessions.unique(S.State.sessions(K.Kernel.state(K.Kernel.step(st, ev, entropy)))) == True{} : Bool}:
  match ev:
    case F.Config{len, +tlvs}:
      Config.sunique(S.Cfg.complete(tlvs), st, tlvs, entropy, e)
    case F.NgapAssocUp{assoc}:
      AssocUp.sunique(st, assoc, e)
    case F.NgapAssocDown{assoc}:
      Down.sunique(st, assoc, e)
    case F.NgapData{assoc, stream, len, bytes}:
      Route.pdu_sunique(st, assoc, stream, entropy, Fr.Pdu.read(bytes), e)
    case F.PfcpData{len, bytes}:
      Render.sunique(st, Gsm.Gsm.pfcp_data(st, bytes), e)
    case F.TimerFired{timer}:
      Render.sunique(st, K.Kernel.fired(st, timer), e)

def L.smf.ip_pool.unique(st, ev, entropy, e):
  ({==}, Step.sunique(st, ev, entropy, e))

def L.smf.teid.unique(key, s, k, t, more, e):
  e1 = P.Bool.not_true(S.SRow.conflicts(key, s, k, t), P.Bool.and_true_l(Bool.not(S.SRow.conflicts(key, s, k, t)), S.Sessions.clear(key, s, more), e))
  e2 = P.Bool.or_false_r(U32.is_eq(k, key), S.Session.conflicts(s, t), e1)
  e3 = P.Bool.or_false_r(U32.is_eq(S.Session.ip(s), S.Session.ip(t)), Bool.or(U32.is_eq(S.Session.teid(s), S.Session.teid(t)), Bool.and(U32.is_eq(S.Session.ue(s), S.Session.ue(t)), U32.is_eq(S.Session.psi(s), S.Session.psi(t)))), e2)
  P.Bool.or_false_l(U32.is_eq(S.Session.teid(s), S.Session.teid(t)), Bool.and(U32.is_eq(S.Session.ue(s), S.Session.ue(t)), U32.is_eq(S.Session.psi(s), S.Session.psi(t))), e3)

# Packet filters and the ePCO
# ---------------------------

def L.smf.packet_filters.capacity_reject():
  {==}

def L.smf.epco.response_bounded(cfg, wanted):
  match wanted:
    case True{}:
      {==}
    case False{}:
      {==}

# A failed establishment leaves nothing
# -------------------------------------
# Aborting a session deletes its row whatever the UE lookup finds, since the
# UE's own transaction touches only the UE table.

def Abort.ctx(+skey: U32, +s: S.Session, pti: U32, cause: U32, seq: U32, key: U32, ue: S.Ue, mctx: Maybe<&2, Sec.Nas.Ctx>, st: S.State) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.join(Gsm.Gsm.to_ue_ctx(key, ue, S.Session.psi(s), Gsm.Gsm.reject(S.Session.psi(s), pti, cause), mctx), N.Out.also(Gsm.Gsm.forget([(skey, s)], seq), N.Guard.cancel(S.SPhase.guard(S.Session.phase(s))))))))) == None{} : Maybe<&2, S.Session>}:
  match mctx:
    case None{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          SDel.get(skey, sessions)
    case Some{c}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          SDel.get(skey, sessions)

def Abort.ue(+skey: U32, +s: S.Session, pti: U32, cause: U32, seq: U32, m: Maybe<&2, S.Ue>, st: S.State) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.abort_m(skey, s, pti, cause, seq, m))))) == None{} : Maybe<&2, S.Session>}:
  match m:
    case None{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          SDel.get(skey, sessions)
    case Some{+ue}:
      Abort.ctx(skey, s, pti, cause, seq, S.Session.ue(s), ue, S.Phase.ctx(S.Ue.phase(ue)), st)

def Failure.pfcp(+st: S.State, +entropy: B.Bytes(), len: U32, +bytes: B.Bytes(), +msg: Pf.Msg, rest: B.Bytes(), +skey: U32, +s: S.Session, guard: S.Guard, +pti: U32, accept: B.Bytes(), em: {Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)}, ek: {Pf.Msg.kind(msg) == 51 : U32}, es: {S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, ep: {S.Session.phase(s) == S.Creating{guard, pti, accept} : S.SPhase}, ec: {Up.N4.accepted(Up.N4.cause(msg)) == False{} : Bool}) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.PfcpData{len, bytes}, entropy)))) == None{} : Maybe<&2, S.Session>}:
  sem = Equal.sym(B.Read(Pf.Msg), Pf.Msg.read(bytes), Done{(msg, rest)}, em)
  %sem : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.pfcp_msg(st, _))))) == None{} : Maybe<&2, S.Session>}
  sek = Equal.sym(U32, Pf.Msg.kind(msg), 51, ek)
  %sek : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.pfcp_k1(st, msg, _, U32.is_eq(_, 1)))))) == None{} : Maybe<&2, S.Session>}
  ses = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Some{(skey, s)}, es)
  %ses : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.established(st, msg, _))))) == None{} : Maybe<&2, S.Session>}
  sep = Equal.sym(S.SPhase, S.Session.phase(s), S.Creating{guard, pti, accept}, ep)
  %sep : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.established_phase(st, skey, s, msg, _))))) == None{} : Maybe<&2, S.Session>}
  sec = Equal.sym(Bool, Up.N4.accepted(Up.N4.cause(msg)), False{}, ec)
  %sec : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.established_as(st, skey, s, guard, pti, accept, _, Up.N4.up_seid(msg)))))) == None{} : Maybe<&2, S.Session>}
  Abort.ue(skey, s, pti, 38, S.State.pfcp_seq(st), Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), st)

# A forgotten session is gone, whatever else the answer carries.
def Forget.gone(+skey: U32, +s: S.Session, seq: U32, acts: List<&2, N.Act>, st: S.State) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.also(Gsm.Gsm.forget([(skey, s)], seq), acts))))) == None{} : Maybe<&2, S.Session>}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      SDel.get(skey, sessions)

# The guard expires while the session is pending: it goes, whatever the phase.
def Expired.gone(+skey: U32, +s: S.Session, p: S.SPhase, pend: {S.SPhase.pending(p) == True{} : Bool}, +st: S.State) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.expired(st, skey, s, p))))) == None{} : Maybe<&2, S.Session>}:
  match p:
    case S.Creating{guard, pti, accept}:
      Abort.ue(skey, s, pti, 38, S.State.pfcp_seq(st), Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), st)
    case S.Setting{guard, pti}:
      Abort.ue(skey, s, pti, 38, S.State.pfcp_seq(st), Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), st)
    case S.Modifying{guard}:
      Forget.gone(skey, s, S.State.pfcp_seq(st), [N.Note{F.Warn{}, "PFCP: no Session Modification Response; session released"}], st)
    case S.Active{}:
      Empty.absurd({Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.expired(st, skey, s, S.Active{}))))) == None{} : Maybe<&2, S.Session>}, P.Refute.bool(pend))

def Failure.timer(+st: S.State, +entropy: B.Bytes(), +timer: U32, +skey: U32, +s: S.Session, pend: {S.SPhase.pending(S.Session.phase(s)) == True{} : Bool}, et: {S.Ues.by_timer(timer, S.State.ues(st)) == None{} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>}, eg: {S.Sessions.by_timer(timer, S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.TimerFired{timer}, entropy)))) == None{} : Maybe<&2, S.Session>}:
  set = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>, S.Ues.by_timer(timer, S.State.ues(st)), None{}, et)
  %set : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, timer, _))))) == None{} : Maybe<&2, S.Session>}
  seg = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, S.Sessions.by_timer(timer, S.State.sessions(st)), Some{(skey, s)}, eg)
  %seg : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, K.Kernel.fired_session(st, timer, _))))) == None{} : Maybe<&2, S.Session>}
  Expired.gone(skey, s, S.Session.phase(s), pend, st)

# eUPF refuses the Session Modification: the session goes.
def Failure.modify(+st: S.State, +entropy: B.Bytes(), len: U32, +bytes: B.Bytes(), +msg: Pf.Msg, rest: B.Bytes(), +skey: U32, +s: S.Session, guard: S.Guard, em: {Pf.Msg.read(bytes) == Done{(msg, rest)} : B.Read(Pf.Msg)}, ek: {Pf.Msg.kind(msg) == 53 : U32}, es: {S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, ep: {S.Session.phase(s) == S.Modifying{guard} : S.SPhase}, ec: {Up.N4.accepted(Up.N4.cause(msg)) == False{} : Bool}) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.PfcpData{len, bytes}, entropy)))) == None{} : Maybe<&2, S.Session>}:
  sem = Equal.sym(B.Read(Pf.Msg), Pf.Msg.read(bytes), Done{(msg, rest)}, em)
  %sem : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.pfcp_msg(st, _))))) == None{} : Maybe<&2, S.Session>}
  sek = Equal.sym(U32, Pf.Msg.kind(msg), 53, ek)
  %sek : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.pfcp_k1(st, msg, _, U32.is_eq(_, 1)))))) == None{} : Maybe<&2, S.Session>}
  ses = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)), Some{(skey, s)}, es)
  %ses : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.modified(st, msg, _))))) == None{} : Maybe<&2, S.Session>}
  sep = Equal.sym(S.SPhase, S.Session.phase(s), S.Modifying{guard}, ep)
  %sep : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.modified_phase(st, skey, s, msg, _))))) == None{} : Maybe<&2, S.Session>}
  sec = Equal.sym(Bool, Up.N4.accepted(Up.N4.cause(msg)), False{}, ec)
  %sec : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.modified_as(st, skey, s, guard, _))))) == None{} : Maybe<&2, S.Session>}
  Forget.gone(skey, s, S.State.pfcp_seq(st), [N.TimerCancel{S.Guard.timer(guard)}, N.Note{F.Warn{}, "PFCP: Session Modification refused; session released"}], st)

# The gNB reports the session failed to set up: the one item of the failed
# list aborts it, between the sequence number spent and nothing else.
def GnbFail.ctx(+skey: U32, +s: S.Session, pti: U32, seq: U32, key: U32, ue: S.Ue, mctx: Maybe<&2, Sec.Nas.Ctx>, st: S.State) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.join((S.Keep{}, []), N.Out.join((S.BumpSeq{1}, []), N.Out.join(N.Out.join(Gsm.Gsm.to_ue_ctx(key, ue, S.Session.psi(s), Gsm.Gsm.reject(S.Session.psi(s), pti, 26), mctx), N.Out.also(Gsm.Gsm.forget([(skey, s)], seq), N.Guard.cancel(S.SPhase.guard(S.Session.phase(s))))), (S.Keep{}, [])))))))) == None{} : Maybe<&2, S.Session>}:
  match mctx:
    case None{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          SDel.get(skey, sessions)
    case Some{c}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          SDel.get(skey, sessions)

def GnbFail.ue(+skey: U32, +s: S.Session, pti: U32, seq: U32, m: Maybe<&2, S.Ue>, st: S.State) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.join((S.Keep{}, []), N.Out.join((S.BumpSeq{1}, []), N.Out.join(Gsm.Gsm.abort_m(skey, s, pti, 26, seq, m), (S.Keep{}, [])))))))) == None{} : Maybe<&2, S.Session>}:
  match m:
    case None{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          SDel.get(skey, sessions)
    case Some{+ue}:
      GnbFail.ctx(skey, s, pti, seq, S.Session.ue(s), ue, S.Phase.ctx(S.Ue.phase(ue)), st)

def Failure.gnb(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +psi: U32, transfer: B.Bytes(), x: Maybe<&2, List<&2, Fr.Ie>>, diag: Maybe<&2, G.CriticalityDiagnostics>, uli: Maybe<&2, G.UserLocationInformation>, +ue: S.Ue, +skey: U32, +s: S.Session, guard: S.Guard, +pti: U32, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 29, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ev: {V.PDUSessionResourceSetupResponse.view(ies) == Done{V.PDUSessionResourceSetupResponse.View{amf, ran, None{}, Some{[G.PDUSessionResourceFailedToSetupItemSURes{psi, transfer, x}]}, diag, uli}} : Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>}, eo: {N.Owner.of(Tb.Table.get(S.Ue, N.Ngap.of_big(amf), S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}, es: {S.Sessions.by_psi(N.Ngap.of_big(amf), psi, S.State.sessions(st)) == Some{(skey, s)} : Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>}, eh: {S.Session.phase(s) == S.Setting{guard, pti} : S.SPhase}) -> {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == None{} : Maybe<&2, S.Session>}:
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{1, 29, crit, value}}, ep)
  %sep : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(R.Route.of_pdu(st, assoc, stream, entropy, _)))) == None{} : Maybe<&2, S.Session>}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(R.Route.of_ies(st, assoc, stream, U32.to_nat(1), U32.to_nat(29), entropy, _)))) == None{} : Maybe<&2, S.Session>}
  sev = Equal.sym(Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>, V.PDUSessionResourceSetupResponse.view(ies), Done{V.PDUSessionResourceSetupResponse.View{amf, ran, None{}, Some{[G.PDUSessionResourceFailedToSetupItemSURes{psi, transfer, x}]}, diag, uli}}, ev)
  %sev : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.setup_response_of_view(st, assoc, _))))) == None{} : Maybe<&2, S.Session>}
  seo = Equal.sym(Maybe<&2, S.Ue>, N.Owner.of(Tb.Table.get(S.Ue, N.Ngap.of_big(amf), S.State.ues(st)), assoc, ran), Some{ue}, eo)
  %seo : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.setup_response_ue(st, assoc, N.Ngap.of_big(amf), [], [G.PDUSessionResourceFailedToSetupItemSURes{psi, transfer, x}], _))))) == None{} : Maybe<&2, S.Session>}
  ses = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, S.Sessions.by_psi(N.Ngap.of_big(amf), psi, S.State.sessions(st)), Some{(skey, s)}, es)
  %ses : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.join(Gsm.Gsm.set_ups(st, N.Ngap.of_big(amf), [], S.State.pfcp_seq(st)), N.Out.join((S.BumpSeq{1}, []), N.Out.join(Gsm.Gsm.failed(st, U32.add(S.State.pfcp_seq(st), U32.from_nat(List.length(&2, G.PDUSessionResourceSetupItemSURes, []))), _), Gsm.Gsm.faileds(st, N.Ngap.of_big(amf), [], U32.add(U32.add(S.State.pfcp_seq(st), U32.from_nat(List.length(&2, G.PDUSessionResourceSetupItemSURes, []))), 1))))))))) == None{} : Maybe<&2, S.Session>}
  seh = Equal.sym(S.SPhase, S.Session.phase(s), S.Setting{guard, pti}, eh)
  %seh : {Tb.Table.get(S.Session, skey, S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.join(Gsm.Gsm.set_ups(st, N.Ngap.of_big(amf), [], S.State.pfcp_seq(st)), N.Out.join((S.BumpSeq{1}, []), N.Out.join(Gsm.Gsm.failed_phase(st, skey, s, U32.add(S.State.pfcp_seq(st), U32.from_nat(List.length(&2, G.PDUSessionResourceSetupItemSURes, []))), _), Gsm.Gsm.faileds(st, N.Ngap.of_big(amf), [], U32.add(U32.add(S.State.pfcp_seq(st), U32.from_nat(List.length(&2, G.PDUSessionResourceSetupItemSURes, []))), 1))))))))) == None{} : Maybe<&2, S.Session>}
  GnbFail.ue(skey, s, pti, U32.add(S.State.pfcp_seq(st), U32.from_nat(List.length(&2, G.PDUSessionResourceSetupItemSURes, []))), Tb.Table.get(S.Ue, S.Session.ue(s), S.State.ues(st)), st)

def L.smf.establish.failure_releases(st, entropy, len, bytes, msg, rest, skey, s, guard, pti, accept, timer, assoc, stream, crit, value, ies, c, amf, ran, psi, transfer, x, diag, uli, ue):
  (em => ek => es => ep => ec => Failure.pfcp(st, entropy, len, bytes, msg, rest, skey, s, guard, pti, accept, em, ek, es, ep, ec),
   (pend => et => eg => Failure.timer(st, entropy, timer, skey, s, pend, et, eg),
    (em => ek => es => ep => ec => Failure.modify(st, entropy, len, bytes, msg, rest, skey, s, guard, em, ek, es, ep, ec),
     ep => ei => ev => eo => es => eh => Failure.gnb(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, psi, transfer, x, diag, uli, ue, skey, s, guard, pti, ep, ei, ev, eo, es, eh))))

# What a UL NAS Transport comes to
# --------------------------------
# A verified UL NAS Transport from a registered UE is answered by the N1 SM
# message handler; the step is that answer rendered.

def Transport.out(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), uli: G.UserLocationInformation, +ue: S.Ue, +ctx: Sec.Nas.Ctx, prot: Sec.Nas.Protection, +plain: B.Bytes(), count: Sec.Nas.Count, +ctx2: Sec.Nas.Ctx, old: Sec.Nas.Ctx, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ev: {V.UplinkNASTransport.view(ies) == Done{V.UplinkNASTransport.View{amf, ran, nas, uli}} : Result<&2, &2, B.Err, V.UplinkNASTransport.View>}, eo: {Gmm.Gmm.owner(st, assoc, N.Ngap.of_big(amf), ran) == Some{ue} : Maybe<&2, S.Ue>}, ec: {S.Phase.ctx(S.Ue.phase(ue)) == Some{ctx} : Maybe<&2, Sec.Nas.Ctx>}, eu: {Sec.Nas.unprotect(ctx, nas) == Done{Sec.Unprotected{prot, plain, count, ctx2}} : Result<&2, &2, B.Err, Sec.Nas.Unprotected>}, em: {Mm.Mm.read(plain) == Done{Mm.Mm{Mm.UlNasTransport{}, fields, opts}} : Result<&2, &2, B.Err, Mm.Mm>}, er: {S.Ue.phase(ue) == S.Registered{old} : S.Phase}, en: {U32.is_eq(I.Fields.byte1(fields), 1) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == N.Step.of(st, Gsm.Gsm.message(st, N.Ngap.of_big(amf), ue, ctx2, opts, entropy, Sm.Sm.read(I.Fields.lve2(fields)))) : N.Step()}:
  +R : N.Step() = N.Step.of(st, Gsm.Gsm.message(st, N.Ngap.of_big(amf), ue, ctx2, opts, entropy, Sm.Sm.read(I.Fields.lve2(fields))))
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{0, 46, crit, value}}, ep)
  %sep : {R.Route.of_pdu(st, assoc, stream, entropy, _) == R : N.Step()}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {R.Route.of_ies(st, assoc, stream, U32.to_nat(0), U32.to_nat(46), entropy, _) == R : N.Step()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UplinkNASTransport.View>, V.UplinkNASTransport.view(ies), Done{V.UplinkNASTransport.View{amf, ran, nas, uli}}, ev)
  %sev : {N.Step.of(st, Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, _)) == R : N.Step()}
  seo = Equal.sym(Maybe<&2, S.Ue>, Gmm.Gmm.owner(st, assoc, N.Ngap.of_big(amf), ran), Some{ue}, eo)
  %seo : {N.Step.of(st, Gmm.Gmm.uplink_ue(st, assoc, N.Ngap.of_big(amf), nas, entropy, _)) == R : N.Step()}
  sec = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.ctx(S.Ue.phase(ue)), Some{ctx}, ec)
  %sec : {N.Step.of(st, Gmm.Gmm.secured(st, N.Ngap.of_big(amf), ue, entropy, nas, _)) == R : N.Step()}
  seu = Equal.sym(Result<&2, &2, B.Err, Sec.Nas.Unprotected>, Sec.Nas.unprotect(ctx, nas), Done{Sec.Unprotected{prot, plain, count, ctx2}}, eu)
  %seu : {N.Step.of(st, Gmm.Gmm.opened(st, N.Ngap.of_big(amf), ue, entropy, _)) == R : N.Step()}
  sem = Equal.sym(Result<&2, &2, B.Err, Mm.Mm>, Mm.Mm.read(plain), Done{Mm.Mm{Mm.UlNasTransport{}, fields, opts}}, em)
  %sem : {N.Step.of(st, Gmm.Gmm.protected(st, N.Ngap.of_big(amf), ue, entropy, count, ctx2, _)) == R : N.Step()}
  ser = Equal.sym(S.Phase, S.Ue.phase(ue), S.Registered{old}, er)
  %ser : {N.Step.of(st, Gmm.Gmm.sphase(st, N.Ngap.of_big(amf), ue, entropy, count, ctx2, Mm.UlNasTransport{}, fields, opts, _)) == R : N.Step()}
  sen = Equal.sym(Bool, U32.is_eq(I.Fields.byte1(fields), 1), True{}, en)
  %sen : {N.Step.of(st, Gsm.Gsm.n1(st, N.Ngap.of_big(amf), ue, ctx2, opts, entropy, I.Fields.lve2(fields), _)) == R : N.Step()}
  {==}

def Tx.rephase_sessions(key: U32, p: S.Phase, st: S.State) -> {S.State.sessions(S.Tx.apply(S.Rephase{key, p}, st)) == S.State.sessions(st) : Tb.Table(S.Session)}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      {==}

def Tx.rephase_seq(key: U32, p: S.Phase, st: S.State) -> {S.State.pfcp_seq(S.Tx.apply(S.Rephase{key, p}, st)) == S.State.pfcp_seq(st) : U32}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      {==}

def L.smf.establish.reject_leaves_state(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, nas, uli, ue, ctx, prot, plain, count, ctx2, old, fields, opts, psi, pti, sfields, sopts, cfg, cause, ep, ei, ev, eo, ec, eu, em, er, en, es, ef, ex):
  eq = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, Gsm.Gsm.message(st, N.Ngap.of_big(amf), ue, ctx2, opts, entropy, Sm.Sm.read(I.Fields.lve2(fields)))), Transport.out(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, nas, uli, ue, ctx, prot, plain, count, ctx2, old, fields, opts, ep, ei, ev, eo, ec, eu, em, er, en))
  %eq : {S.State.sessions(K.Kernel.state(_)) == S.State.sessions(st) : Tb.Table(S.Session)} & ({S.State.pfcp_seq(K.Kernel.state(_)) == S.State.pfcp_seq(st) : U32} & {K.Kernel.actions(_) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), N.Ngap.of_big(amf), S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))}] : List<&2, N.Act>})
  ses = Equal.sym(Result<&2, &2, B.Err, Sm.Sm>, Sm.Sm.read(I.Fields.lve2(fields)), Done{Sm.Sm{psi, pti, Sm.EstablishmentRequest{}, sfields, sopts}}, es)
  %ses : {S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.message(st, N.Ngap.of_big(amf), ue, ctx2, opts, entropy, _)))) == S.State.sessions(st) : Tb.Table(S.Session)} & ({S.State.pfcp_seq(K.Kernel.state(N.Step.of(st, Gsm.Gsm.message(st, N.Ngap.of_big(amf), ue, ctx2, opts, entropy, _)))) == S.State.pfcp_seq(st) : U32} & {K.Kernel.actions(N.Step.of(st, Gsm.Gsm.message(st, N.Ngap.of_big(amf), ue, ctx2, opts, entropy, _))) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), N.Ngap.of_big(amf), S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))}] : List<&2, N.Act>})
  sef = Equal.sym(Maybe<&2, S.Cfg>, S.State.config(st), Some{cfg}, ef)
  %sef : {S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.with_cfg(st, N.Ngap.of_big(amf), ue, ctx2, psi, pti, opts, sopts, entropy, _)))) == S.State.sessions(st) : Tb.Table(S.Session)} & ({S.State.pfcp_seq(K.Kernel.state(N.Step.of(st, Gsm.Gsm.with_cfg(st, N.Ngap.of_big(amf), ue, ctx2, psi, pti, opts, sopts, entropy, _)))) == S.State.pfcp_seq(st) : U32} & {K.Kernel.actions(N.Step.of(st, Gsm.Gsm.with_cfg(st, N.Ngap.of_big(amf), ue, ctx2, psi, pti, opts, sopts, entropy, _))) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), N.Ngap.of_big(amf), S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))}] : List<&2, N.Act>})
  sex = Equal.sym(Gsm.Check, Gsm.Gsm.validate(cfg, psi, opts, sopts, Up.N4.up(st)), Gsm.Refuse{cause}, ex)
  %sex : {S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.checked(st, N.Ngap.of_big(amf), ue, ctx2, cfg, psi, pti, entropy, _)))) == S.State.sessions(st) : Tb.Table(S.Session)} & ({S.State.pfcp_seq(K.Kernel.state(N.Step.of(st, Gsm.Gsm.checked(st, N.Ngap.of_big(amf), ue, ctx2, cfg, psi, pti, entropy, _)))) == S.State.pfcp_seq(st) : U32} & {K.Kernel.actions(N.Step.of(st, Gsm.Gsm.checked(st, N.Ngap.of_big(amf), ue, ctx2, cfg, psi, pti, entropy, _))) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), N.Ngap.of_big(amf), S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))}] : List<&2, N.Act>})
  (Tx.rephase_sessions(N.Ngap.of_big(amf), S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))), st), (Tx.rephase_seq(N.Ngap.of_big(amf), S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause))))), st), {==}))

def L.smf.modification.rejected(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, nas, uli, ue, ctx, prot, plain, count, ctx2, old, fields, opts, psi, pti, sfields, sopts, ep, ei, ev, eo, ec, eu, em, er, en, es):
  eq = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, Gsm.Gsm.message(st, N.Ngap.of_big(amf), ue, ctx2, opts, entropy, Sm.Sm.read(I.Fields.lve2(fields)))), Transport.out(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, nas, uli, ue, ctx, prot, plain, count, ctx2, old, fields, opts, ep, ei, ev, eo, ec, eu, em, er, en))
  %eq : {S.State.sessions(K.Kernel.state(_)) == S.State.sessions(st) : Tb.Table(S.Session)} & {K.Kernel.actions(_) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), N.Ngap.of_big(amf), S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.modification_reject(psi, pti))))}] : List<&2, N.Act>}
  ses = Equal.sym(Result<&2, &2, B.Err, Sm.Sm>, Sm.Sm.read(I.Fields.lve2(fields)), Done{Sm.Sm{psi, pti, Sm.ModificationRequest{}, sfields, sopts}}, es)
  %ses : {S.State.sessions(K.Kernel.state(N.Step.of(st, Gsm.Gsm.message(st, N.Ngap.of_big(amf), ue, ctx2, opts, entropy, _)))) == S.State.sessions(st) : Tb.Table(S.Session)} & {K.Kernel.actions(N.Step.of(st, Gsm.Gsm.message(st, N.Ngap.of_big(amf), ue, ctx2, opts, entropy, _))) == [N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), N.Ngap.of_big(amf), S.Ue.ran_id(ue), Sec.Nas.Protected.msg(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.modification_reject(psi, pti))))}] : List<&2, N.Act>}
  (Tx.rephase_sessions(N.Ngap.of_big(amf), S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(Sec.Nas.protect(ctx2, Sec.Ciphered{}, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.modification_reject(psi, pti))))), st), {==})
