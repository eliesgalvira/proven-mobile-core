import Base
import ../bytes.bend as B
import ../table.bend as Tb
import ../state.bend as S
import ../frame.bend as F
import ../step.bend as K
import ../amf/ngap.bend as N
import ../nas/security.bend as Sec
import ../amf/route.bend as R
import ../amf/handover.bend as Ho
import ../smf/gsm.bend as Gsm
import ../smf/n4.bend as Up
import ../pfcp.bend as Pf
import ../tlv.bend as T
import ../ausf.bend as Au
import ../LAWS.bend as L
import ./lib.bend as P
import ./walk.bend as PW
import ./takeover.bend as PT
import ./liveness.bend as PL
import ./fresh.bend as PF
import ./handover.bend as PH

# nas_sec.downlink_fresh
# ----------------------
# Where no two contexts share a key, the row under k before a step is the
# context k names (PH.Nc.base). A transaction then runs in order; until it
# writes k (Fq.mode) every row under k holds what k held with no message
# after it, and from the first write on every row under k holds a context
# the step's messages to k leave, sealed in turn from what k held: each
# write is one PF.Fs.sealed judges, and rows other writes leave or drop keep
# it (PH.Hs.rows). A step that never writes k sends k no message
# (PF.Fs.sends). Every write also gives the keys the law's last case asks
# for (Fq.Wit), whatever row is left.

def Fq.msgs_if(m: Bool, +msgs: List<&2, B.Bytes()>) -> List<&2, B.Bytes()>:
  match m:
    case True{}:
      msgs
    case False{}:
      []

# Whether k has been written, after tx, w saying whether it was before.
def Fq.mode(+k: U32, tx: S.Tx, w: Bool) -> Bool:
  match tx:
    case S.Put{key, ue}:
      Bool.or(U32.is_eq(key, k), w)
    case S.Rephase{key, p}:
      Bool.or(U32.is_eq(key, k), w)
    case S.Del{key}:
      Bool.or(U32.is_eq(key, k), w)
    case S.Both{a, b}:
      Fq.mode(k, b, Fq.mode(k, a, w))
    case _:
      w

def Fq.WitIf(m: Bool, +b: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>) -> Data:
  match m:
    case True{}:
      N.Fresh.Left(b, msgs)
    case False{}:
      Unit

def Fq.Now(+k: U32, +b: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>, +m: Bool, +ues: Tb.Table(S.Ue)) -> Data:
  Sigma<&2, &2, {PH.Hs.rows(k, PH.Fresh{b, Fq.msgs_if(m, msgs)}, ues) == True{} : Bool}, _ => Fq.WitIf(m, b, msgs)>

def Fq.Fin(+k: U32, +b: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>, +ues: Tb.Table(S.Ue)) -> Data:
  Sigma<&2, &2, {PH.Hs.rows(k, PH.Fresh{b, msgs}, ues) == True{} : Bool}, _ => N.Fresh.Left(b, msgs)>

def Fq.now_rows(+k: U32, +b: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>, +m: Bool, +ues: Tb.Table(S.Ue), +r: Fq.Now(k, b, msgs, m, ues)) -> {PH.Hs.rows(k, PH.Fresh{b, Fq.msgs_if(m, msgs)}, ues) == True{} : Bool}:
  match r:
    case (+e, w):
      e

def Fq.now_wit(+k: U32, +b: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>, +m: Bool, +ues: Tb.Table(S.Ue), +r: Fq.Now(k, b, msgs, m, ues)) -> Fq.WitIf(m, b, msgs):
  match r:
    case (e, +w):
      w

# The keys the law's last case asks for
# -------------------------------------

def Fq.keys0() -> Sec.Nas.Keys:
  Sec.Keys{[], [], Sec.Nea0{}, Sec.Nia2{}, 0}

def Fq.nil_wit(+b: Maybe<&2, Sec.Nas.Ctx>) -> N.Fresh.Left(b, []):
  match b:
    case None{}:
      (Fq.keys0(), {==})
    case Some{Sec.Ctx{kb, db, ub}}:
      {==}

def Fq.at_present(m: Maybe<&2, Sec.Nas.Count>, +d: Sec.Nas.Count, +h: {N.Fresh.at(m, d) == True{} : Bool}) -> {Tb.Table.present(Sec.Nas.Count, m) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Tb.Table.present(Sec.Nas.Count, None{}) == True{} : Bool}, P.Refute.bool(h))
    case Some{c}:
      {==}

def Fq.from_wit(+b: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>, +h: {N.Fresh.from(b, msgs) == True{} : Bool}) -> N.Fresh.Left(b, msgs):
  match b:
    case None{}:
      Empty.absurd(N.Fresh.Left(None{}, msgs), P.Refute.bool(h))
    case Some{Sec.Ctx{kb, db, ub}}:
      h

def Fq.gone_wit(+b: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>, +h: {N.Fresh.gone(b, msgs) == True{} : Bool}) -> N.Fresh.Left(b, msgs):
  match msgs:
    case Nil{}:
      Fq.nil_wit(b)
    case +m <> +more:
      Fq.from_wit(b, m <> more, h)

def Fq.into_wit(+b: Maybe<&2, Sec.Nas.Ctx>, +ka: Sec.Nas.Keys, +da: Sec.Nas.Count, +msgs: List<&2, B.Bytes()>, +h: {N.Fresh.into(b, ka, da, msgs) == True{} : Bool}) -> N.Fresh.Left(b, msgs):
  match b:
    case None{}:
      (ka, Fq.at_present(N.Fresh.run(msgs, ka, Sec.Nas.Count.zero()), da, h))
    case Some{Sec.Ctx{+kb, +db, ub}}:
      Fq.at_present(N.Fresh.run(msgs, kb, db), da, P.Bool.and_true_r(Sec.Nas.Keys.same(kb, ka), N.Fresh.at(N.Fresh.run(msgs, kb, db), da), h))

def Fq.wit_of(+b: Maybe<&2, Sec.Nas.Ctx>, +c: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>, +h: {N.Fresh.holds(b, c, msgs) == True{} : Bool}) -> N.Fresh.Left(b, msgs):
  match c:
    case Some{Sec.Ctx{+ka, +da, ua}}:
      Fq.into_wit(b, ka, da, msgs, h)
    case None{}:
      Fq.gone_wit(b, msgs, h)

# What the law asks of a context a row holds.
def Fq.law_holds(+b: Maybe<&2, Sec.Nas.Ctx>, +a: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>, +h: {N.Fresh.holds(b, a, msgs) == True{} : Bool}) -> N.Fresh.Law(b, a, msgs):
  match a:
    case Some{Sec.Ctx{+ka, +da, ua}}:
      h
    case None{}:
      Fq.gone_wit(b, msgs, h)

# The transaction in order
# ------------------------

def Fq.rephase(+st: S.State, +k: U32, +acts: List<&2, N.Act>, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +w: Bool, +x: Bool, +ex: {U32.is_eq(key, k) == x : Bool}, +hs: {PF.Fs.write(st, key, S.Phase.nas(p), acts) == True{} : Bool}, +e: {PH.Hs.rows(k, PH.Fresh{PF.Fs.ctx(st, k), Fq.msgs_if(w, N.Acts.nas(k, acts))}, ues) == True{} : Bool}, +wi: Fq.WitIf(w, PF.Fs.ctx(st, k), N.Acts.nas(k, acts))) -> Fq.Now(k, PF.Fs.ctx(st, k), N.Acts.nas(k, acts), Bool.or(x, w), S.Ues.rephase(key, p, ues)):
  match x:
    case True{}:
      +ek = P.U32.eq_of_is_eq(key, k, ex)
      +hk : {PF.Fs.write(st, k, S.Phase.nas(p), acts) == True{} : Bool} = (%ek : {PF.Fs.write(st, _, S.Phase.nas(p), acts) == True{} : Bool}; hs)
      +r : PH.Rw = PH.Fresh{PF.Fs.ctx(st, k), N.Acts.nas(k, acts)}
      ((%Equal.sym(U32, key, k, ek) : {PH.Hs.rows(k, r, S.Ues.rephase(_, p, ues)) == True{} : Bool}; PH.Hs.rephase_on(k, r, p, ues, hk)), Fq.wit_of(PF.Fs.ctx(st, k), S.Phase.nas(p), N.Acts.nas(k, acts), hk))
    case False{}:
      (PH.Hs.rephase_other(k, PH.Fresh{PF.Fs.ctx(st, k), Fq.msgs_if(w, N.Acts.nas(k, acts))}, key, p, ues, ex, e), wi)

def Fq.put(+st: S.State, +k: U32, +acts: List<&2, N.Act>, +key: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +w: Bool, +x: Bool, +ex: {U32.is_eq(key, k) == x : Bool}, +hs: {PF.Fs.write(st, key, S.Phase.nas(S.Ue.phase(u)), acts) == True{} : Bool}, +e: {PH.Hs.rows(k, PH.Fresh{PF.Fs.ctx(st, k), Fq.msgs_if(w, N.Acts.nas(k, acts))}, ues) == True{} : Bool}, +wi: Fq.WitIf(w, PF.Fs.ctx(st, k), N.Acts.nas(k, acts))) -> Fq.Now(k, PF.Fs.ctx(st, k), N.Acts.nas(k, acts), Bool.or(x, w), S.Ues.put(key, u, ues)):
  match x:
    case True{}:
      +ek = P.U32.eq_of_is_eq(key, k, ex)
      +hk : {PF.Fs.write(st, k, S.Phase.nas(S.Ue.phase(u)), acts) == True{} : Bool} = (%ek : {PF.Fs.write(st, _, S.Phase.nas(S.Ue.phase(u)), acts) == True{} : Bool}; hs)
      +r : PH.Rw = PH.Fresh{PF.Fs.ctx(st, k), N.Acts.nas(k, acts)}
      +hc : {PH.Hs.rows(k, r, S.Ues.sift(S.Clear{key, u}, ues)) == True{} : Bool} = (%Equal.sym(U32, key, k, ek) : {PH.Hs.rows(k, r, S.Ues.sift(S.Clear{_, u}, ues)) == True{} : Bool}; PH.Hs.clear(k, r, u, ues))
      +hh = P.Bool.or_r(Bool.not(U32.is_eq(key, k)), PH.Hs.holds(r, S.Ue.phase(u)), hk)
      (P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(key, k)), PH.Hs.holds(r, S.Ue.phase(u))), PH.Hs.rows(k, r, S.Ues.sift(S.Clear{key, u}, ues)), hh, hc), Fq.wit_of(PF.Fs.ctx(st, k), S.Phase.nas(S.Ue.phase(u)), N.Acts.nas(k, acts), hk))
    case False{}:
      +r : PH.Rw = PH.Fresh{PF.Fs.ctx(st, k), Fq.msgs_if(w, N.Acts.nas(k, acts))}
      +hh = P.Bool.or_l(Bool.not(U32.is_eq(key, k)), PH.Hs.holds(r, S.Ue.phase(u)), (%Equal.sym(Bool, U32.is_eq(key, k), False{}, ex) : {Bool.not(_) == True{} : Bool}; {==}))
      (P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(key, k)), PH.Hs.holds(r, S.Ue.phase(u))), PH.Hs.rows(k, r, S.Ues.sift(S.Clear{key, u}, ues)), hh, PH.Hs.sift(k, r, S.Clear{key, u}, ues, e)), wi)

def Fq.del(+st: S.State, +k: U32, +acts: List<&2, N.Act>, +key: U32, +ues: Tb.Table(S.Ue), +w: Bool, +x: Bool, +ex: {U32.is_eq(key, k) == x : Bool}, +hs: {PF.Fs.write(st, key, None{}, acts) == True{} : Bool}, +e: {PH.Hs.rows(k, PH.Fresh{PF.Fs.ctx(st, k), Fq.msgs_if(w, N.Acts.nas(k, acts))}, ues) == True{} : Bool}, +wi: Fq.WitIf(w, PF.Fs.ctx(st, k), N.Acts.nas(k, acts))) -> Fq.Now(k, PF.Fs.ctx(st, k), N.Acts.nas(k, acts), Bool.or(x, w), S.Ues.del(key, ues)):
  match x:
    case True{}:
      +ek = P.U32.eq_of_is_eq(key, k, ex)
      +hk : {PF.Fs.write(st, k, None{}, acts) == True{} : Bool} = (%ek : {PF.Fs.write(st, _, None{}, acts) == True{} : Bool}; hs)
      +r : PH.Rw = PH.Fresh{PF.Fs.ctx(st, k), N.Acts.nas(k, acts)}
      ((%Equal.sym(U32, key, k, ek) : {PH.Hs.rows(k, r, S.Ues.sift(S.Except{_}, ues)) == True{} : Bool}; PH.Hs.except(k, r, ues)), Fq.wit_of(PF.Fs.ctx(st, k), None{}, N.Acts.nas(k, acts), hk))
    case False{}:
      (PH.Hs.sift(k, PH.Fresh{PF.Fs.ctx(st, k), Fq.msgs_if(w, N.Acts.nas(k, acts))}, S.Except{key}, ues, e), wi)

def Fq.tx(+st: S.State, +k: U32, +acts: List<&2, N.Act>, +tx: S.Tx, +ues: Tb.Table(S.Ue), +w: Bool, +hs: {PF.Fs.sealed(st, tx, acts) == True{} : Bool}, +e: {PH.Hs.rows(k, PH.Fresh{PF.Fs.ctx(st, k), Fq.msgs_if(w, N.Acts.nas(k, acts))}, ues) == True{} : Bool}, +wi: Fq.WitIf(w, PF.Fs.ctx(st, k), N.Acts.nas(k, acts))) -> Fq.Now(k, PF.Fs.ctx(st, k), N.Acts.nas(k, acts), Fq.mode(k, tx, w), PT.Tk.ues(tx, ues)):
  match tx:
    case S.Rephase{+key, +p}:
      Fq.rephase(st, k, acts, key, p, ues, w, U32.is_eq(key, k), {==}, hs, e, wi)
    case S.Put{+key, +u}:
      Fq.put(st, k, acts, key, u, ues, w, U32.is_eq(key, k), {==}, hs, e, wi)
    case S.Del{+key}:
      Fq.del(st, k, acts, key, ues, w, U32.is_eq(key, k), {==}, hs, e, wi)
    case S.Both{+a, +c}:
      +b = PF.Fs.ctx(st, k)
      +ms = N.Acts.nas(k, acts)
      +m1 = Fq.mode(k, a, w)
      +u1 = PT.Tk.ues(a, ues)
      +r1 = Fq.tx(st, k, acts, a, ues, w, P.Bool.and_true_l(PF.Fs.sealed(st, a, acts), PF.Fs.sealed(st, c, acts), hs), e, wi)
      Fq.tx(st, k, acts, c, u1, m1, P.Bool.and_true_r(PF.Fs.sealed(st, a, acts), PF.Fs.sealed(st, c, acts), hs), Fq.now_rows(k, b, ms, m1, u1, r1), Fq.now_wit(k, b, ms, m1, u1, r1))
    case S.Keep{}:
      (e, wi)
    case S.PutSession{key, s}:
      (e, wi)
    case S.Revar{key, v}:
      (e, wi)
    case S.DelSession{key}:
      (e, wi)
    case S.Subs{subs}:
      (e, wi)
    case S.SetLink{link}:
      (e, wi)
    case S.BumpUe{bk}:
      (e, wi)
    case S.BumpSeq{n}:
      (e, wi)

# A transaction that never writes k sends k nothing
# ------------------------------------------------

def Fq.Off(+k: U32, +tx: S.Tx, +w: Bool) -> Data:
  Sigma<&2, &2, {PF.Fs.writes(k, tx) == False{} : Bool}, _ => {w == False{} : Bool}>

def Fq.off_writes(+k: U32, +tx: S.Tx, +w: Bool, +r: Fq.Off(k, tx, w)) -> {PF.Fs.writes(k, tx) == False{} : Bool}:
  match r:
    case (+x, y):
      x

def Fq.off_before(+k: U32, +tx: S.Tx, +w: Bool, +r: Fq.Off(k, tx, w)) -> {w == False{} : Bool}:
  match r:
    case (x, +y):
      y

def Fq.mode_off(+k: U32, +tx: S.Tx, +w: Bool, +e: {Fq.mode(k, tx, w) == False{} : Bool}) -> Fq.Off(k, tx, w):
  match tx:
    case S.Put{+key, u}:
      (P.Bool.or_false_l(U32.is_eq(key, k), w, e), P.Bool.or_false_r(U32.is_eq(key, k), w, e))
    case S.Rephase{+key, p}:
      (P.Bool.or_false_l(U32.is_eq(key, k), w, e), P.Bool.or_false_r(U32.is_eq(key, k), w, e))
    case S.Del{+key}:
      (P.Bool.or_false_l(U32.is_eq(key, k), w, e), P.Bool.or_false_r(U32.is_eq(key, k), w, e))
    case S.Both{+a, +c}:
      +m1 = Fq.mode(k, a, w)
      +rc = Fq.mode_off(k, c, m1, e)
      +ra = Fq.mode_off(k, a, w, Fq.off_before(k, c, m1, rc))
      (P.Bool.or_false(PF.Fs.writes(k, a), PF.Fs.writes(k, c), Fq.off_writes(k, a, w, ra), Fq.off_writes(k, c, m1, rc)), Fq.off_before(k, a, w, ra))
    case S.Keep{}:
      ({==}, e)
    case S.PutSession{key, s}:
      ({==}, e)
    case S.Revar{key, v}:
      ({==}, e)
    case S.DelSession{key}:
      ({==}, e)
    case S.Subs{subs}:
      ({==}, e)
    case S.SetLink{link}:
      ({==}, e)
    case S.BumpUe{bk}:
      ({==}, e)
    case S.BumpSeq{n}:
      ({==}, e)

def Fq.ne(+j: U32, +k: U32, +tx: S.Tx, +b: Bool, +eb: {U32.is_eq(j, k) == b : Bool}, +hj: {PF.Fs.writes(j, tx) == True{} : Bool}, +hk: {PF.Fs.writes(k, tx) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      +ej = P.U32.eq_of_is_eq(j, k, eb)
      +hw : {PF.Fs.writes(k, tx) == True{} : Bool} = (%ej : {PF.Fs.writes(_, tx) == True{} : Bool}; hj)
      Empty.absurd({True{} == False{} : Bool}, P.Refute.true_false(Equal.trans(Bool, True{}, PF.Fs.writes(k, tx), False{}, Equal.sym(Bool, PF.Fs.writes(k, tx), True{}, hw), hk)))
    case False{}:
      {==}

def Fq.unsent_one(+k: U32, +tx: S.Tx, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +xs: List<&2, B.Bytes()>, +hk: {PF.Fs.writes(k, tx) == False{} : Bool}, +hj: {PF.Fs.sent(tx, m) == True{} : Bool}) -> {N.Acts.nas_to(k, m, xs) == xs : List<&2, B.Bytes()>}:
  match m:
    case None{}:
      {==}
    case Some{(+j, +x)}:
      +ne = Fq.ne(j, k, tx, U32.is_eq(j, k), {==}, hj, hk)
      (%Equal.sym(Bool, U32.is_eq(j, k), False{}, ne) : {N.Acts.nas_keep(x, xs, _) == xs : List<&2, B.Bytes()>}; {==})

def Fq.unsent(+k: U32, +tx: S.Tx, +acts: List<&2, N.Act>, +hk: {PF.Fs.writes(k, tx) == False{} : Bool}, +hs: {PF.Fs.sends(tx, acts) == True{} : Bool}) -> {N.Acts.nas(k, acts) == [] : List<&2, B.Bytes()>}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      +h1 = P.Bool.and_true_l(PF.Fs.sent(tx, N.Act.nas(a)), PF.Fs.sends(tx, more), hs)
      +ih = Fq.unsent(k, tx, more, hk, P.Bool.and_true_r(PF.Fs.sent(tx, N.Act.nas(a)), PF.Fs.sends(tx, more), hs))
      Equal.trans(List<&2, B.Bytes()>, N.Acts.nas_to(k, N.Act.nas(a), N.Acts.nas(k, more)), N.Acts.nas(k, more), [], Fq.unsent_one(k, tx, N.Act.nas(a), N.Acts.nas(k, more), hk, h1), ih)

# Mute parts of a step
# --------------------

def Fq.row_mute(+k: U32, +s: S.Session, kept: Bool) -> {PF.Fs.amute(N.Gone.row(k, s, kept)) == True{} : Bool}:
  match kept:
    case True{}:
      {==}
    case False{}:
      PF.Fs.cancel_mute(k, S.SPhase.guard(S.Session.phase(s)))

def Fq.cancels_mute(+before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> {PF.Fs.amute(N.Gone.cancels(before, after)) == True{} : Bool}:
  match before:
    case Nil{}:
      {==}
    case (+k, +s) <> +more:
      PF.Fs.amute_app(N.Gone.row(k, s, Tb.Table.has(S.Session, k, after)), N.Gone.cancels(more, after), Fq.row_mute(k, s, Tb.Table.has(S.Session, k, after)), Fq.cancels_mute(more, after))

def Fq.gone_mute(+keeps: Bool, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> {PF.Fs.amute(N.Gone.when(keeps, before, after)) == True{} : Bool}:
  match keeps:
    case True{}:
      {==}
    case False{}:
      Fq.cancels_mute(before, after)

def Fq.drop_mute(+s: S.State, +assoc: U32) -> {PF.Fs.amute(K.Kernel.actions(R.Route.drop(s, assoc))) == True{} : Bool}:
  match s:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +left = S.Ues.drop_assoc(assoc, ues)
      +rows = S.Sessions.sift(S.SOrphan{left}, sessions)
      +o = Up.N4.deletions(rows, pfcp_seq)
      +st1 = S.Tx.apply(N.Out.tx(o), S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4})
      +kept = S.Sessions.sift(S.SOwned{left}, S.State.sessions(st1))
      PF.Fs.amute_app(N.Out.acts(o), N.Gone.cancels(sessions, kept), P.Bool.and_true_r(PF.Fs.tmute(N.Out.tx(o)), PF.Fs.amute(N.Out.acts(o)), PF.Fs.deletions_mute(rows, pfcp_seq)), Fq.cancels_mute(sessions, kept))

def Fq.notes_mute(+ok: Bool) -> {PF.Fs.amute(Gsm.Gsm.deleted_notes(ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Fq.resend_mute(+k1: U32, +t: S.Session, +p: S.SPhase, +request: B.Bytes(), +more: Bool) -> {PF.Fs.amute(N.Out.acts(Gsm.Gsm.resend_if(k1, t, p, request, (S.DelSession{k1}, [N.Note{F.Warn{}, "PFCP: no Session Deletion Response; deletion given up"}]), more))) == True{} : Bool}:
  match more:
    case True{}:
      {==}
    case False{}:
      {==}

def Fq.dphase_mute(+skey: U32, +msg: Pf.Msg, +p: S.SPhase) -> {PF.Fs.amute(N.Out.acts(Gsm.Gsm.deleted_phase(skey, msg, p))) == True{} : Bool}:
  match p:
    case S.Deleting{guard, request}:
      Fq.notes_mute(Up.N4.accepted(Up.N4.cause(msg)))
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

def Fq.deleted_mute(+msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> {PF.Fs.amute(N.Out.acts(Gsm.Gsm.deleted(msg, m))) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Fq.dphase_mute(skey, msg, S.Session.phase(s))

# Actions no NAS message to key goes in: none under key at all.
def Fq.keep_if(+k: U32, +key: U32, +nas: B.Bytes(), +p: Bool, +xs: List<&2, B.Bytes()>, +ne: {U32.is_eq(key, k) == False{} : Bool}) -> {N.Acts.nas_to(k, N.Act.nas_if(key, nas, p), xs) == xs : List<&2, B.Bytes()>}:
  match p:
    case True{}:
      (%Equal.sym(Bool, U32.is_eq(key, k), False{}, ne) : {N.Acts.nas_keep(nas, xs, _) == xs : List<&2, B.Bytes()>}; {==})
    case False{}:
      {==}

def Fq.spare_one(+k: U32, +a: N.Act, +xs: List<&2, B.Bytes()>, +h: {Bool.not(S.Maybe.same_u32(N.Act.ue(a), Some{k})) == True{} : Bool}) -> {N.Acts.nas_to(k, N.Act.nas(a), xs) == xs : List<&2, B.Bytes()>}:
  match a:
    case N.DlNas{assoc, stream, +key, ran_id, +nas}:
      Fq.keep_if(k, key, nas, Sec.Nas.is_protected(nas), xs, P.Bool.not_true(U32.is_eq(key, k), h))
    case N.Ics{assoc, stream, +key, ran_id, cfg, caps, k_gnb, +nas}:
      Fq.keep_if(k, key, nas, Sec.Nas.is_protected(nas), xs, P.Bool.not_true(U32.is_eq(key, k), h))
    case N.PduSetup{assoc, stream, +key, ran_id, psi, sst, +nas, transfer}:
      Fq.keep_if(k, key, nas, Sec.Nas.is_protected(nas), xs, P.Bool.not_true(U32.is_eq(key, k), h))
    case N.PduRelease{assoc, stream, +key, ran_id, psi, +nas}:
      Fq.keep_if(k, key, nas, Sec.Nas.is_protected(nas), xs, P.Bool.not_true(U32.is_eq(key, k), h))
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
    case N.TimerStart{ue, timer, ms}:
      {==}
    case N.TimerCancel{timer}:
      {==}

def Fq.spare_nas(+k: U32, +acts: List<&2, N.Act>, +h: {N.Acts.spare(k, acts) == True{} : Bool}) -> {N.Acts.nas(k, acts) == [] : List<&2, B.Bytes()>}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      +x = Bool.not(S.Maybe.same_u32(N.Act.ue(a), Some{k}))
      Equal.trans(List<&2, B.Bytes()>, N.Acts.nas_to(k, N.Act.nas(a), N.Acts.nas(k, more)), N.Acts.nas(k, more), [], Fq.spare_one(k, a, N.Acts.nas(k, more), P.Bool.and_true_l(x, N.Acts.spare(k, more), h)), Fq.spare_nas(k, more, P.Bool.and_true_r(x, N.Acts.spare(k, more), h)))

# From an outcome to the law
# --------------------------

def Fq.Law(+st: S.State, +k: U32, +o: N.Step()) -> Type:
  N.Fresh.Law(PF.Fs.ctx(st, k), S.Ue.nas(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(o)))), N.Acts.nas(k, K.Kernel.actions(o)))

def Fq.fin_nil(+k: U32, +b: Maybe<&2, Sec.Nas.Ctx>, +ms: List<&2, B.Bytes()>, +ues: Tb.Table(S.Ue), +e: {PH.Hs.rows(k, PH.Fresh{b, []}, ues) == True{} : Bool}, +en: {ms == [] : List<&2, B.Bytes()>}) -> Fq.Fin(k, b, ms, ues):
  +sn = Equal.sym(List<&2, B.Bytes()>, ms, [], en)
  ((%sn : {PH.Hs.rows(k, PH.Fresh{b, _}, ues) == True{} : Bool}; e), (%sn : N.Fresh.Left(b, _); Fq.nil_wit(b)))

def Fq.fin_mode(+k: U32, +tx: S.Tx, +acts: List<&2, N.Act>, +b: Maybe<&2, Sec.Nas.Ctx>, +m: Bool, +em: {Fq.mode(k, tx, False{}) == m : Bool}, +hs: {PF.Fs.sends(tx, acts) == True{} : Bool}, +ues: Tb.Table(S.Ue), +r: Fq.Now(k, b, N.Acts.nas(k, acts), m, ues)) -> Fq.Fin(k, b, N.Acts.nas(k, acts), ues):
  match m:
    case True{}:
      r
    case False{}:
      +off = Fq.mode_off(k, tx, False{}, em)
      Fq.fin_nil(k, b, N.Acts.nas(k, acts), ues, Fq.now_rows(k, b, N.Acts.nas(k, acts), False{}, ues, r), Fq.unsent(k, tx, acts, Fq.off_writes(k, tx, False{}, off), hs))

def Fq.fin_tx(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +tx: S.Tx, +acts: List<&2, N.Act>, +hn: {PF.Fs.nas(st, tx, acts) == True{} : Bool}) -> Fq.Fin(k, PF.Fs.ctx(st, k), N.Acts.nas(k, acts), PT.Tk.ues(tx, S.State.ues(st))):
  +e0 = PH.Nc.base(k, S.State.ues(st), PH.Kept{}, eu)
  +r = Fq.tx(st, k, acts, tx, S.State.ues(st), False{}, PF.Fs.sealed_of(st, tx, acts, hn), e0, Unit{})
  Fq.fin_mode(k, tx, acts, PF.Fs.ctx(st, k), Fq.mode(k, tx, False{}), {==}, PF.Fs.sends_of(st, tx, acts, hn), PT.Tk.ues(tx, S.State.ues(st)), r)

def Fq.fin_of(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +tx: S.Tx, +acts: List<&2, N.Act>, +hn: {PF.Fs.nas(st, tx, acts) == True{} : Bool}) -> Fq.Fin(k, PF.Fs.ctx(st, k), N.Acts.nas(k, K.Kernel.actions(N.Step.of(st, (tx, acts)))), S.State.ues(K.Kernel.state(N.Step.of(st, (tx, acts))))):
  +b = PF.Fs.ctx(st, k)
  +g = N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)))
  +t1 = PT.Tk.ues(tx, S.State.ues(st))
  +sr = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, (tx, acts)))), t1, PT.Tk.render(st, (tx, acts)))
  +eg = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, List.append(&2, N.Act, acts, g)), N.Acts.nas(k, acts), PF.Fs.nas_mute_r(k, acts, g, Fq.gone_mute(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)))))
  (%sr : Fq.Fin(k, b, N.Acts.nas(k, List.append(&2, N.Act, acts, g)), _); (%eg : Fq.Fin(k, b, _, t1); Fq.fin_tx(st, k, eu, tx, acts, hn)))

def Fq.unique_nas(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +h: {PF.Fs.ok(st, tx, acts) == True{} : Bool}) -> {PF.Fs.nas(st, tx, acts) == True{} : Bool}:
  PH.Nc.unique_or(st, PF.Fs.nas(st, tx, acts), eu, h)

def Fq.fin_out(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +o: N.GOut(), +h: {PL.Lv.ok(st, o) == True{} : Bool}) -> Fq.Fin(k, PF.Fs.ctx(st, k), N.Acts.nas(k, K.Kernel.actions(N.Step.of(st, o))), S.State.ues(K.Kernel.state(N.Step.of(st, o)))):
  match o:
    case (+tx, +acts):
      Fq.fin_of(st, k, eu, tx, acts, Fq.unique_nas(st, tx, acts, eu, PL.Lv.does_fs(st, tx, acts, PL.Lv.homed(st, tx, S.State.ues(st)), h)))

def Fq.law_rows(+k: U32, +b: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>, +ues: Tb.Table(S.Ue), +e: {PH.Hs.rows(k, PH.Fresh{b, msgs}, ues) == True{} : Bool}, +wt: N.Fresh.Left(b, msgs), +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, k, ues) == m : Maybe<&2, S.Ue>}) -> N.Fresh.Law(b, S.Ue.nas(m), msgs):
  match m:
    case None{}:
      wt
    case Some{+v}:
      Fq.law_holds(b, S.Phase.nas(S.Ue.phase(v)), msgs, PH.Nc.found(k, PH.Fresh{b, msgs}, ues, e, v, em))

def Fq.law_fin(+k: U32, +b: Maybe<&2, Sec.Nas.Ctx>, +msgs: List<&2, B.Bytes()>, +ues: Tb.Table(S.Ue), +f: Fq.Fin(k, b, msgs, ues)) -> N.Fresh.Law(b, S.Ue.nas(Tb.Table.get(S.Ue, k, ues)), msgs):
  match f:
    case (+e, +wt):
      Fq.law_rows(k, b, msgs, ues, e, wt, Tb.Table.get(S.Ue, k, ues), {==})

def Fq.out(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +o: N.GOut(), +h: {PL.Lv.ok(st, o) == True{} : Bool}) -> Fq.Law(st, k, N.Step.of(st, o)):
  Fq.law_fin(k, PF.Fs.ctx(st, k), N.Acts.nas(k, K.Kernel.actions(N.Step.of(st, o))), S.State.ues(K.Kernel.state(N.Step.of(st, o))), Fq.fin_out(st, k, eu, o, h))

# A session the UPF settles: its guard's stop in front.
def Fq.settled(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +k1: U32, +tx: S.Tx, +more: List<&2, N.Act>, +h: {PL.Lv.ok(st, (tx, more)) == True{} : Bool}) -> Fq.Law(st, k, N.Step.of(st, (tx, N.TimerCancel{k1} <> more))):
  +acts : List<&2, N.Act> = N.TimerCancel{k1} <> more
  +hn = PF.Fs.cons(st, tx, N.TimerCancel{k1}, more, Fq.unique_nas(st, tx, more, eu, PL.Lv.does_fs(st, tx, more, PL.Lv.homed(st, tx, S.State.ues(st)), h)), {==})
  Fq.law_fin(k, PF.Fs.ctx(st, k), N.Acts.nas(k, K.Kernel.actions(N.Step.of(st, (tx, acts)))), S.State.ues(K.Kernel.state(N.Step.of(st, (tx, acts)))), Fq.fin_of(st, k, eu, tx, acts, hn))

# The session side writes no context and sends no NAS message.
def Fq.sx(+st: S.State, +k: U32, +o: N.GOut(), +hx: {PW.Sx.only(N.Out.tx(o)) == True{} : Bool}, +hm: {PF.Fs.amute(N.Out.acts(o)) == True{} : Bool}) -> Fq.Law(st, k, N.Step.of(st, o)):
  match o:
    case (+tx, +acts):
      +b = PF.Fs.ctx(st, k)
      +g = N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)))
      +xs = List.append(&2, N.Act, acts, g)
      +en = PF.Fs.amute_nas(k, xs, PF.Fs.amute_app(acts, g, hm, Fq.gone_mute(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)))))
      +after = S.State.ues(K.Kernel.state(N.Step.of(st, (tx, acts))))
      +er = Equal.trans(Tb.Table(S.Ue), after, PT.Tk.ues(tx, S.State.ues(st)), S.State.ues(st), PT.Tk.render(st, (tx, acts)), PT.Tk.ues_sx(tx, S.State.ues(st), hx))
      (%Equal.sym(Tb.Table(S.Ue), after, S.State.ues(st), er) : N.Fresh.Law(b, S.Ue.nas(Tb.Table.get(S.Ue, k, _)), N.Acts.nas(k, xs)); (%Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, xs), [], en) : N.Fresh.Law(b, b, _); Fq.law_holds(b, b, [], PF.Fs.holds_self(b))))

# Nothing written, nothing sent to k.
def Fq.keep(+st: S.State, +k: U32, +acts: List<&2, N.Act>, +h: {N.Acts.spare(k, acts) == True{} : Bool}) -> Fq.Law(st, k, (st, acts)):
  +b = PF.Fs.ctx(st, k)
  (%Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, acts), [], Fq.spare_nas(k, acts, h)) : N.Fresh.Law(b, b, _); Fq.law_holds(b, b, [], PF.Fs.holds_self(b)))

# An association's contexts re-initialised: the handovers it takes part in
# end (an outcome), then its contexts go, with no NAS message.
def Fq.drop_fin(+s: S.State, +assoc: U32, +k: U32, +b: Maybe<&2, Sec.Nas.Ctx>, +ms0: List<&2, N.Act>, +f: Fq.Fin(k, b, N.Acts.nas(k, ms0), S.State.ues(s))) -> Fq.Fin(k, b, N.Acts.nas(k, List.append(&2, N.Act, ms0, K.Kernel.actions(R.Route.drop(s, assoc)))), S.State.ues(K.Kernel.state(R.Route.drop(s, assoc)))):
  match f:
    case (+e, +wt):
      +d = K.Kernel.actions(R.Route.drop(s, assoc))
      +sn = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, List.append(&2, N.Act, ms0, d)), N.Acts.nas(k, ms0), PF.Fs.nas_mute_r(k, ms0, d, Fq.drop_mute(s, assoc)))
      ((%sn : {PH.Hs.rows(k, PH.Fresh{b, _}, S.State.ues(K.Kernel.state(R.Route.drop(s, assoc)))) == True{} : Bool}; PH.Hs.drop_rows(s, assoc, k, PH.Fresh{b, N.Acts.nas(k, ms0)}, e)), (%sn : N.Fresh.Left(b, _); wt))

def Fq.reset(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +assoc: U32) -> Fq.Fin(k, PF.Fs.ctx(st, k), N.Acts.nas(k, N.Step.acts(R.Route.reset(st, assoc))), S.State.ues(N.Step.state(R.Route.reset(st, assoc)))):
  +o = Ho.Ho.down(st, assoc)
  +s1 = N.Step.of(st, o)
  Fq.drop_fin(N.Step.state(s1), assoc, k, PF.Fs.ctx(st, k), N.Step.acts(s1), Fq.fin_out(st, k, eu, o, PL.Lw.ho_down(st, assoc)))

def Fq.down(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +assoc: U32) -> Fq.Law(st, k, R.Route.down(st, assoc)):
  +rs = R.Route.reset(st, assoc)
  Fq.law_fin(k, PF.Fs.ctx(st, k), N.Acts.nas(k, N.Step.acts(rs)), S.State.ues(N.Step.state(rs)), Fq.reset(st, k, eu, assoc))

def Fq.assocs_fin(+k: U32, +b: Maybe<&2, Sec.Nas.Ctx>, +ms: List<&2, B.Bytes()>, +x: S.State, +as: Tb.Table(B.Bytes()), +f: Fq.Fin(k, b, ms, S.State.ues(x))) -> Fq.Fin(k, b, ms, S.State.ues(S.State.with_assocs(x, as))):
  match x:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      f

# NG Setup: the association's contexts re-initialised, then it is set up,
# its answer carrying no message to a UE.
def Fq.ready(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +assoc: U32, +id: B.Bytes(), +ok: Bool, +acts: List<&2, N.Act>, +sp: {N.Acts.spare(k, acts) == True{} : Bool}) -> Fq.Law(st, k, (S.State.ready(N.Step.state(R.Route.reset(st, assoc)), assoc, id, ok), List.append(&2, N.Act, N.Step.acts(R.Route.reset(st, assoc)), acts))):
  +b = PF.Fs.ctx(st, k)
  +rs = R.Route.reset(st, assoc)
  +x = N.Step.state(rs)
  +ms = N.Acts.nas(k, N.Step.acts(rs))
  +x2 = S.State.ready(x, assoc, id, ok)
  +e2 : {List.append(&2, B.Bytes(), ms, N.Acts.nas(k, acts)) == ms : List<&2, B.Bytes()>} = (%Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, acts), [], Fq.spare_nas(k, acts, sp)) : {List.append(&2, B.Bytes(), ms, _) == ms : List<&2, B.Bytes()>}; PF.Fs.app_nil(ms))
  +en = Equal.trans(List<&2, B.Bytes()>, N.Acts.nas(k, List.append(&2, N.Act, N.Step.acts(rs), acts)), List.append(&2, B.Bytes(), ms, N.Acts.nas(k, acts)), ms, PF.Fs.nas_app(k, N.Step.acts(rs), acts), e2)
  h = Fq.law_fin(k, b, ms, S.State.ues(x2), Fq.assocs_fin(k, b, ms, x, S.Assocs.set(assoc, id, S.State.assocs(x), ok), Fq.reset(st, k, eu, assoc)))
  (%Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, List.append(&2, N.Act, N.Step.acts(rs), acts)), ms, en) : N.Fresh.Law(b, S.Ue.nas(Tb.Table.get(S.Ue, k, S.State.ues(x2))), _); h)

# Configuration writes no context; what it asks the UPF is mute.
def Fq.step_nas(+s: S.State, +o: N.GOut(), +k: U32, +hm: {PF.Fs.amute(N.Out.acts(o)) == True{} : Bool}) -> {N.Acts.nas(k, K.Kernel.actions(N.Step.of(s, o))) == [] : List<&2, B.Bytes()>}:
  match o:
    case (+tx, +acts):
      PF.Fs.amute_nas(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(s), S.State.sessions(S.Tx.apply(tx, s)))), PF.Fs.amute_app(acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(s), S.State.sessions(S.Tx.apply(tx, s))), hm, Fq.gone_mute(S.Tx.keeps_sessions(tx), S.State.sessions(s), S.State.sessions(S.Tx.apply(tx, s)))))

def Fq.config_fin(+complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), +k: U32, +b: Maybe<&2, Sec.Nas.Ctx>, +e: {PH.Hs.rows(k, PH.Fresh{b, []}, S.State.ues(st)) == True{} : Bool}) -> Fq.Fin(k, b, N.Acts.nas(k, K.Kernel.actions(K.Kernel.config(complete, st, tlvs, entropy))), S.State.ues(K.Kernel.state(K.Kernel.config(complete, st, tlvs, entropy)))):
  match complete:
    case False{}:
      Fq.fin_nil(k, b, [], S.State.ues(st), e, {==})
    case True{}:
      match st:
        case S.State{config, subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, n4}:
          +cfg = S.Cfg.of(tlvs)
          +st2 : S.State = S.State{Some{cfg}, Au.Subscribers.of(S.Cfg.subscribers(cfg)), assocs, ues, sessions, pfcp_seq, next_ue, S.N4{List.take(&2, U32, entropy, 4n), S.Idle{}}}
          +o = N.Out.also(Up.N4.start(st2), [N.Note{F.Info{}, "Config: loaded; PFCP association requested"}])
          Fq.fin_nil(k, b, N.Acts.nas(k, K.Kernel.actions(N.Step.of(st2, o))), ues, e, Fq.step_nas(st2, o, k, {==}))

def Fq.config(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +complete: Bool, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes()) -> Fq.Law(st, k, K.Kernel.config(complete, st, tlvs, entropy)):
  +b = PF.Fs.ctx(st, k)
  +x = K.Kernel.config(complete, st, tlvs, entropy)
  Fq.law_fin(k, b, N.Acts.nas(k, K.Kernel.actions(x)), S.State.ues(K.Kernel.state(x)), Fq.config_fin(complete, st, tlvs, entropy, k, b, PH.Nc.base(k, S.State.ues(st), PH.Kept{}, eu)))

def Fq.step(+st: S.State, +ev: F.Evt, +entropy: B.Bytes(), +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> Fq.Law(st, k, K.Kernel.step(st, ev, entropy)):
  PL.Dw.walk(o => Fq.Law(st, k, o), o => Fq.Law(st, k, N.Step.of(st, o)), st, ev, entropy, +acts => sp => tc => nr => Fq.keep(st, k, acts, sp(k)), +assoc => ns => +id => +ok => +acts => sp => tc => nr => Fq.ready(st, k, eu, assoc, id, ok, acts, sp(k)), +tlvs => Fq.config(st, k, eu, S.Cfg.complete(tlvs), tlvs, entropy), +assoc => Fq.down(st, k, eu, assoc), o => h => h, +o => +h => Fq.out(st, k, eu, o, h), +k1 => +t => +g => +r => ek => eu2 => em => ep => Fq.sx(st, k, Gsm.Gsm.expired(st, k1, t, S.Deleting{g, r}), PH.Nc.resend_sx(k1, t, S.Deleting{S.Guard{U32.add(S.Guard.retries(g), 1)}, r}, r, U32.is_lt(S.Guard.retries(g), Up.N4.n1())), Fq.resend_mute(k1, t, S.Deleting{S.Guard{U32.add(S.Guard.retries(g), 1)}, r}, r, U32.is_lt(S.Guard.retries(g), Up.N4.n1()))), +len => +bytes => +msg => +rest => ev2 => er => ek => Fq.sx(st, k, Gsm.Gsm.deleted(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st))), PH.Nc.deleted_sx(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st))), Fq.deleted_mute(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))), +k1 => +tx => +more => ekd => eh => h => Fq.settled(st, k, eu, k1, tx, more, h))

def L.nas_sec.downlink_fresh(st, ev, entropy, k, eu):
  Fq.step(st, ev, entropy, k, eu)
