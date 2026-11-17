import Base
import ../bytes.bend as B
import ../table.bend as Tb
import ../state.bend as S
import ../ngap/gen/types.bend as G
import ../frame.bend as F
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/gmm.bend as Gmm
import ../smf/n4.bend as Up
import ../smf/gsm.bend as Gsm
import ../smf/switch.bend as Sw
import ../nas/security.bend as Sec
import ../nas/mm.bend as Mm
import ../nas/sm.bend as Sm
import ../nas/ie.bend as I
import ../nas/mobile_id.bend as Mi
import ../suci.bend as Su
import ../plmn.bend as Pl
import ../ausf.bend as Au
import ../crypto/kdf.bend as Kd
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../amf/route.bend as R
import ../amf/path_switch.bend as Ps
import ../amf/handover.bend as Ho
import ../LAWS.bend as L
import ./lib.bend as P
import ./walk.bend as PW

# Proof of amf.takeover.authenticated (ticket 32). A transaction keeps the row
# of another association's context unless it puts a context that conflicts
# with it; the walk below shows, path by path, that every such put carries a
# security context for that context's SUPI.

# Equalities
# ----------

def Same.bytes_sym(+a: Maybe<&2, B.Bytes()>, +b: Maybe<&2, B.Bytes()>) -> {S.Maybe.same_bytes(a, b) == S.Maybe.same_bytes(b, a) : Bool}:
  match a b:
    case Some{x} Some{y}:
      P.Bytes.sym(x, y)
    case Some{x} None{}:
      {==}
    case None{} Some{y}:
      {==}
    case None{} None{}:
      {==}

def Same.u32_sym(+a: Maybe<&2, U32>, +b: Maybe<&2, U32>) -> {S.Maybe.same_u32(a, b) == S.Maybe.same_u32(b, a) : Bool}:
  match a b:
    case Some{x} Some{y}:
      P.U32.sym(x, y)
    case Some{x} None{}:
      {==}
    case None{} Some{y}:
      {==}
    case None{} None{}:
      {==}

# Two contexts conflict whichever way round they are compared.
def Ue.conflicts_sym(+a: S.Ue, +b: S.Ue) -> {S.Ue.conflicts(a, b) == S.Ue.conflicts(b, a) : Bool}:
  match a b:
    case S.Ue{aa, ra, sa, pa, ta, ga, ka, ha, la} S.Ue{ab, rb, sb, pb, tb, gb, kb, hb, lb}:
      e1 = Same.bytes_sym(pa, pb)
      %e1 : {Bool.or(S.Maybe.same_bytes(pa, pb), Bool.or(S.Maybe.same_u32(ta, tb), Bool.and(U32.is_eq(aa, ab), B.bytes_eq(ra, rb)))) == Bool.or(_, Bool.or(S.Maybe.same_u32(tb, ta), Bool.and(U32.is_eq(ab, aa), B.bytes_eq(rb, ra)))) : Bool}
      e2 = Same.u32_sym(ta, tb)
      %e2 : {Bool.or(S.Maybe.same_bytes(pa, pb), Bool.or(S.Maybe.same_u32(ta, tb), Bool.and(U32.is_eq(aa, ab), B.bytes_eq(ra, rb)))) == Bool.or(S.Maybe.same_bytes(pa, pb), Bool.or(_, Bool.and(U32.is_eq(ab, aa), B.bytes_eq(rb, ra)))) : Bool}
      e3 = P.U32.sym(aa, ab)
      %e3 : {Bool.or(S.Maybe.same_bytes(pa, pb), Bool.or(S.Maybe.same_u32(ta, tb), Bool.and(U32.is_eq(aa, ab), B.bytes_eq(ra, rb)))) == Bool.or(S.Maybe.same_bytes(pa, pb), Bool.or(S.Maybe.same_u32(ta, tb), Bool.and(_, B.bytes_eq(rb, ra)))) : Bool}
      e4 = P.Bytes.sym(ra, rb)
      %e4 : {Bool.or(S.Maybe.same_bytes(pa, pb), Bool.or(S.Maybe.same_u32(ta, tb), Bool.and(U32.is_eq(aa, ab), B.bytes_eq(ra, rb)))) == Bool.or(S.Maybe.same_bytes(pa, pb), Bool.or(S.Maybe.same_u32(ta, tb), Bool.and(U32.is_eq(aa, ab), _))) : Bool}
      {==}

# A sieve keeps a row
# -------------------

def Sift.row(+s: S.Sieve, +k: U32, +u: S.Ue, +k0: U32, +w: S.Ue, +more: Tb.Table(S.Ue), +hk: Bool, +ehk: {U32.is_eq(k0, k) == hk : Bool}, +eu: {Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, k, more), hk) == Some{u} : Maybe<&2, S.Ue>}, +ek: {S.Sieve.keeps(s, k, u) == True{} : Bool}, ih: {Tb.Table.get(S.Ue, k, more) == Some{u} : Maybe<&2, S.Ue>} -> {Tb.Table.get(S.Ue, k, S.Ues.sift(s, more)) == Some{u} : Maybe<&2, S.Ue>}) -> {Tb.Table.get(S.Ue, k, Tb.Table.keep(S.Ue, k0, w, S.Ues.sift(s, more), S.Sieve.keeps(s, k0, w))) == Some{u} : Maybe<&2, S.Ue>}:
  match hk:
    case True{}:
      sk = Equal.sym(U32, k0, k, P.U32.eq_of_is_eq(k0, k, ehk))
      %sk : {Tb.Table.get(S.Ue, k, Tb.Table.keep(S.Ue, _, w, S.Ues.sift(s, more), S.Sieve.keeps(s, _, w))) == Some{u} : Maybe<&2, S.Ue>}
      sw = Equal.sym(S.Ue, w, u, P.Some.inj(S.Ue, w, u, eu))
      %sw : {Tb.Table.get(S.Ue, k, Tb.Table.keep(S.Ue, k, _, S.Ues.sift(s, more), S.Sieve.keeps(s, k, _))) == Some{u} : Maybe<&2, S.Ue>}
      sek = Equal.sym(Bool, S.Sieve.keeps(s, k, u), True{}, ek)
      %sek : {Tb.Table.get(S.Ue, k, Tb.Table.keep(S.Ue, k, u, S.Ues.sift(s, more), _)) == Some{u} : Maybe<&2, S.Ue>}
      r = Equal.sym(Bool, U32.is_eq(k, k), True{}, P.U32.is_eq_refl(k))
      %r : {Tb.Table.hit(S.Ue, u, Tb.Table.get(S.Ue, k, S.Ues.sift(s, more)), _) == Some{u} : Maybe<&2, S.Ue>}
      {==}
    case False{}:
      P.Keep.by(S.Ue, tb => {Tb.Table.get(S.Ue, k, tb) == Some{u} : Maybe<&2, S.Ue>}, k0, w, S.Ues.sift(s, more), S.Sieve.keeps(s, k0, w), e => h => (%Equal.sym(Bool, U32.is_eq(k0, k), False{}, ehk) : {Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, k, S.Ues.sift(s, more)), _) == Some{u} : Maybe<&2, S.Ue>}; h), ih(eu))

# The row under k survives a sieve that keeps it.
def Sift.get(+s: S.Sieve, +k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +ek: {S.Sieve.keeps(s, k, u) == True{} : Bool}) -> {Tb.Table.get(S.Ue, k, S.Ues.sift(s, ues)) == Some{u} : Maybe<&2, S.Ue>}:
  match ues:
    case Nil{}:
      Empty.absurd({Tb.Table.get(S.Ue, k, []) == Some{u} : Maybe<&2, S.Ue>}, P.Refute.none_some(S.Ue, u, eu))
    case (+k0, +w) <> +more:
      Sift.row(s, k, u, k0, w, more, U32.is_eq(k0, k), {==}, eu, ek, e => Sift.get(s, k, u, more, e, ek))

# A phase change elsewhere leaves the row under k as it was.
def Rephase.row(+key: U32, +p: S.Phase, +k: U32, +u: S.Ue, +k0: U32, +w: S.Ue, +more: Tb.Table(S.Ue), +hk: Bool, +ehk: {U32.is_eq(k0, k) == hk : Bool}, +eu: {Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, k, more), hk) == Some{u} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(k, key) == False{} : Bool}, ih: {Tb.Table.get(S.Ue, k, more) == Some{u} : Maybe<&2, S.Ue>} -> {Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, more)) == Some{u} : Maybe<&2, S.Ue>}) -> {Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, U32.is_eq(k0, key)), Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, more)), U32.is_eq(k0, k)) == Some{u} : Maybe<&2, S.Ue>}:
  match hk:
    case True{}:
      sk = Equal.sym(U32, k0, k, P.U32.eq_of_is_eq(k0, k, ehk))
      %sk : {Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, U32.is_eq(_, key)), Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, more)), U32.is_eq(_, k)) == Some{u} : Maybe<&2, S.Ue>}
      sn = Equal.sym(Bool, U32.is_eq(k, key), False{}, ne)
      %sn : {Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, _), Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, more)), U32.is_eq(k, k)) == Some{u} : Maybe<&2, S.Ue>}
      r = Equal.sym(Bool, U32.is_eq(k, k), True{}, P.U32.is_eq_refl(k))
      %r : {Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, more)), _) == Some{u} : Maybe<&2, S.Ue>}
      eu
    case False{}:
      se = Equal.sym(Bool, U32.is_eq(k0, k), False{}, ehk)
      %se : {Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, U32.is_eq(k0, key)), Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, more)), _) == Some{u} : Maybe<&2, S.Ue>}
      ih(eu)

def Rephase.get(+key: U32, +p: S.Phase, +k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(k, key) == False{} : Bool}) -> {Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, ues)) == Some{u} : Maybe<&2, S.Ue>}:
  match ues:
    case Nil{}:
      Empty.absurd({Tb.Table.get(S.Ue, k, []) == Some{u} : Maybe<&2, S.Ue>}, P.Refute.none_some(S.Ue, u, eu))
    case (+k0, +w) <> +more:
      Rephase.row(key, p, k, u, k0, w, more, U32.is_eq(k0, k), {==}, eu, ne, e => Rephase.get(key, p, k, u, more, e, ne))

# The row under the key rephased takes the phase.
def Rephase.self_row(+k: U32, +p: S.Phase, +u: S.Ue, +k0: U32, +w: S.Ue, +more: Tb.Table(S.Ue), +hk: Bool, +ehk: {U32.is_eq(k0, k) == hk : Bool}, +eu: {Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, k, more), hk) == Some{u} : Maybe<&2, S.Ue>}, ih: {Tb.Table.get(S.Ue, k, more) == Some{u} : Maybe<&2, S.Ue>} -> {Tb.Table.get(S.Ue, k, S.Ues.rephase(k, p, more)) == Some{S.Ue.with_phase(u, p)} : Maybe<&2, S.Ue>}) -> {Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, U32.is_eq(k0, k)), Tb.Table.get(S.Ue, k, S.Ues.rephase(k, p, more)), U32.is_eq(k0, k)) == Some{S.Ue.with_phase(u, p)} : Maybe<&2, S.Ue>}:
  match hk:
    case True{}:
      se = Equal.sym(Bool, U32.is_eq(k0, k), True{}, ehk)
      %se : {Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, _), Tb.Table.get(S.Ue, k, S.Ues.rephase(k, p, more)), _) == Some{S.Ue.with_phase(u, p)} : Maybe<&2, S.Ue>}
      ew = P.Some.inj(S.Ue, w, u, eu)
      %ew : {Some{S.Ue.with_phase(w, p)} == Some{S.Ue.with_phase(_, p)} : Maybe<&2, S.Ue>}
      {==}
    case False{}:
      se = Equal.sym(Bool, U32.is_eq(k0, k), False{}, ehk)
      %se : {Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, _), Tb.Table.get(S.Ue, k, S.Ues.rephase(k, p, more)), _) == Some{S.Ue.with_phase(u, p)} : Maybe<&2, S.Ue>}
      ih(eu)

def Rephase.self(+k: U32, +p: S.Phase, +u: S.Ue, +ues: Tb.Table(S.Ue), +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}) -> {Tb.Table.get(S.Ue, k, S.Ues.rephase(k, p, ues)) == Some{S.Ue.with_phase(u, p)} : Maybe<&2, S.Ue>}:
  match ues:
    case Nil{}:
      Empty.absurd({Tb.Table.get(S.Ue, k, S.Ues.rephase(k, p, [])) == Some{S.Ue.with_phase(u, p)} : Maybe<&2, S.Ue>}, P.Refute.none_some(S.Ue, u, eu))
    case (+k0, +w) <> +more:
      Rephase.self_row(k, p, u, k0, w, more, U32.is_eq(k0, k), {==}, eu, e => Rephase.self(k, p, u, more, e))

# Transactions on the UE table
# ----------------------------

# What a transaction does to the UE table, which depends on nothing else.
def Tk.ues(+tx: S.Tx, +ues: Tb.Table(S.Ue)) -> Tb.Table(S.Ue):
  match tx:
    case S.Put{key, ue}:
      S.Ues.put(key, ue, ues)
    case S.Rephase{key, phase}:
      S.Ues.rephase(key, phase, ues)
    case S.Del{key}:
      S.Ues.del(key, ues)
    case S.Both{a, b}:
      Tk.ues(b, Tk.ues(a, ues))
    case S.Keep{}:
      ues
    case S.PutSession{key, s}:
      ues
    case S.Revar{key, v}:
      ues
    case S.DelSession{key}:
      ues
    case S.Subs{subs}:
      ues
    case S.SetLink{link}:
      ues
    case S.BumpUe{bk}:
      ues
    case S.BumpSeq{n}:
      ues

def Tk.ues_apply(+tx: S.Tx, +st: S.State) -> {S.State.ues(S.Tx.apply(tx, st)) == Tk.ues(tx, S.State.ues(st)) : Tb.Table(S.Ue)}:
  match tx:
    case S.Both{+a, b}:
      ia = Tk.ues_apply(a, st)
      %ia : {S.State.ues(S.Tx.apply(b, S.Tx.apply(a, st))) == Tk.ues(b, _) : Tb.Table(S.Ue)}
      Tk.ues_apply(b, S.Tx.apply(a, st))
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
    case S.Keep{}:
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

# A transaction spares the row under k, holding u, when it puts no context
# that conflicts with u and changes or forgets no other context under k.
def Tk.spares(+k: U32, +u: S.Ue, +tx: S.Tx) -> Bool:
  match tx:
    case S.Put{key, v}:
      Bool.not(S.Row.conflicts(key, v, k, u))
    case S.Rephase{key, phase}:
      Bool.not(U32.is_eq(k, key))
    case S.Del{key}:
      Bool.not(U32.is_eq(k, key))
    case S.Both{a, b}:
      Bool.and(Tk.spares(k, u, a), Tk.spares(k, u, b))
    case S.Keep{}:
      True{}
    case S.PutSession{key, s}:
      True{}
    case S.Revar{key, v}:
      True{}
    case S.DelSession{key}:
      True{}
    case S.Subs{subs}:
      True{}
    case S.SetLink{link}:
      True{}
    case S.BumpUe{bk}:
      True{}
    case S.BumpSeq{n}:
      True{}

def Tk.spared(+k: U32, +u: S.Ue, +tx: S.Tx, +ues: Tb.Table(S.Ue), +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +es: {Tk.spares(k, u, tx) == True{} : Bool}) -> {Tb.Table.get(S.Ue, k, Tk.ues(tx, ues)) == Some{u} : Maybe<&2, S.Ue>}:
  match tx:
    case S.Put{+key, +v}:
      nc = P.Bool.not_true(S.Row.conflicts(key, v, k, u), es)
      nk = P.Bool.or_false_l(U32.is_eq(k, key), S.Ue.conflicts(v, u), nc)
      sk = Equal.trans(Bool, U32.is_eq(key, k), U32.is_eq(k, key), False{}, P.U32.sym(key, k), nk)
      ssk = Equal.sym(Bool, U32.is_eq(key, k), False{}, sk)
      %ssk : {Tb.Table.hit(S.Ue, v, Tb.Table.get(S.Ue, k, S.Ues.sift(S.Clear{key, v}, ues)), _) == Some{u} : Maybe<&2, S.Ue>}
      Sift.get(S.Clear{key, v}, k, u, ues, eu, es)
    case S.Rephase{+key, +phase}:
      Rephase.get(key, phase, k, u, ues, eu, P.Bool.not_true(U32.is_eq(k, key), es))
    case S.Del{+key}:
      Sift.get(S.Except{key}, k, u, ues, eu, es)
    case S.Both{+a, +b}:
      ga = Tk.spared(k, u, a, ues, eu, P.Bool.and_true_l(Tk.spares(k, u, a), Tk.spares(k, u, b), es))
      Tk.spared(k, u, b, Tk.ues(a, ues), ga, P.Bool.and_true_r(Tk.spares(k, u, a), Tk.spares(k, u, b), es))
    case S.Keep{}:
      eu
    case S.PutSession{key, s}:
      eu
    case S.Revar{key, v}:
      eu
    case S.DelSession{key}:
      eu
    case S.Subs{subs}:
      eu
    case S.SetLink{link}:
      eu
    case S.BumpUe{bk}:
      eu
    case S.BumpSeq{n}:
      eu

# Outcomes
# --------
# A step keeps u the row under k, or a context with u's SUPI holds a security context.

def Tk.Kept(+k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue)) -> Data:
  Either<&2, &2, {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, {S.Ues.secured(S.Ue.supi(u), ues) == True{} : Bool}>

def Tk.Ok(+k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +o: N.GOut()) -> Data:
  Tk.Kept(k, u, Tk.ues(N.Out.tx(o), ues))

def Tk.sp(+k: U32, +u: S.Ue, +o: N.GOut()) -> Bool:
  Tk.spares(k, u, N.Out.tx(o))

def Tk.render(+st: S.State, +o: N.GOut()) -> {S.State.ues(K.Kernel.state(N.Step.of(st, o))) == Tk.ues(N.Out.tx(o), S.State.ues(st)) : Tb.Table(S.Ue)}:
  match o:
    case (tx, acts):
      Tk.ues_apply(tx, st)

def Tk.kept_get(+k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}) -> Tk.Kept(k, u, ues):
  Inl{eu}

def Tk.ok_sp(+k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +o: N.GOut(), +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +es: {Tk.sp(k, u, o) == True{} : Bool}) -> Tk.Ok(k, u, ues, o):
  match o:
    case (+tx, acts):
      Inl{Tk.spared(k, u, tx, ues, eu, es)}

def Tk.ok_prepend(+k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +a: N.Act, +o: N.GOut(), +h: Tk.Ok(k, u, ues, o)) -> Tk.Ok(k, u, ues, N.Out.prepend(a, o)):
  match o:
    case (tx, acts):
      h

def Tk.ok_also(+k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +o: N.GOut(), +more: List<&2, N.Act>, +h: Tk.Ok(k, u, ues, o)) -> Tk.Ok(k, u, ues, N.Out.also(o, more)):
  match o:
    case (tx, acts):
      h

def Tk.ok_join(+k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +a: N.GOut(), +b: N.GOut(), +h: Tk.Kept(k, u, Tk.ues(N.Out.tx(b), Tk.ues(N.Out.tx(a), ues)))) -> Tk.Ok(k, u, ues, N.Out.join(a, b)):
  match a:
    case (ta, aa):
      match b:
        case (tb, ab):
          h

def Tk.sp_join(+k: U32, +u: S.Ue, +a: N.GOut(), +b: N.GOut(), +ha: {Tk.sp(k, u, a) == True{} : Bool}, +hb: {Tk.sp(k, u, b) == True{} : Bool}) -> {Tk.sp(k, u, N.Out.join(a, b)) == True{} : Bool}:
  match a:
    case (ta, aa):
      match b:
        case (tb, ab):
          P.Bool.and_intro(Tk.spares(k, u, ta), Tk.spares(k, u, tb), ha, hb)

# Session deletions, and every other transaction that changes no context,
# spare every context.
def Tk.ues_sx(+tx: S.Tx, +x: Tb.Table(S.Ue), +e: {PW.Sx.only(tx) == True{} : Bool}) -> {Tk.ues(tx, x) == x : Tb.Table(S.Ue)}:
  match tx:
    case S.Keep{}:
      {==}
    case S.SetLink{link}:
      {==}
    case S.Revar{key, v}:
      {==}
    case S.DelSession{key}:
      {==}
    case S.BumpSeq{n}:
      {==}
    case S.Both{+a, +b}:
      ea = Equal.sym(Tb.Table(S.Ue), Tk.ues(a, x), x, Tk.ues_sx(a, x, P.Bool.and_true_l(PW.Sx.only(a), PW.Sx.only(b), e)))
      (%ea : {Tk.ues(b, _) == x : Tb.Table(S.Ue)}; Tk.ues_sx(b, x, P.Bool.and_true_r(PW.Sx.only(a), PW.Sx.only(b), e)))
    case S.Put{key, ue}:
      Empty.absurd({Tk.ues(S.Put{key, ue}, x) == x : Tb.Table(S.Ue)}, P.Refute.bool(e))
    case S.Rephase{key, phase}:
      Empty.absurd({Tk.ues(S.Rephase{key, phase}, x) == x : Tb.Table(S.Ue)}, P.Refute.bool(e))
    case S.Del{key}:
      Empty.absurd({Tk.ues(S.Del{key}, x) == x : Tb.Table(S.Ue)}, P.Refute.bool(e))
    case S.PutSession{key, s}:
      Empty.absurd({Tk.ues(S.PutSession{key, s}, x) == x : Tb.Table(S.Ue)}, P.Refute.bool(e))
    case S.Subs{new}:
      Empty.absurd({Tk.ues(S.Subs{new}, x) == x : Tb.Table(S.Ue)}, P.Refute.bool(e))
    case S.BumpUe{bk}:
      Empty.absurd({Tk.ues(S.BumpUe{bk}, x) == x : Tb.Table(S.Ue)}, P.Refute.bool(e))

def Tk.sp_sx(+k: U32, +u: S.Ue, +tx: S.Tx, +e: {PW.Sx.only(tx) == True{} : Bool}) -> {Tk.spares(k, u, tx) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      {==}
    case S.SetLink{link}:
      {==}
    case S.Revar{key, v}:
      {==}
    case S.DelSession{key}:
      {==}
    case S.BumpSeq{n}:
      {==}
    case S.Both{+a, +b}:
      P.Bool.and_intro(Tk.spares(k, u, a), Tk.spares(k, u, b), Tk.sp_sx(k, u, a, P.Bool.and_true_l(PW.Sx.only(a), PW.Sx.only(b), e)), Tk.sp_sx(k, u, b, P.Bool.and_true_r(PW.Sx.only(a), PW.Sx.only(b), e)))
    case S.Put{key, v}:
      Empty.absurd({Tk.spares(k, u, S.Put{key, v}) == True{} : Bool}, P.Refute.bool(e))
    case S.Rephase{key, phase}:
      Empty.absurd({Tk.spares(k, u, S.Rephase{key, phase}) == True{} : Bool}, P.Refute.bool(e))
    case S.Del{key}:
      Empty.absurd({Tk.spares(k, u, S.Del{key}) == True{} : Bool}, P.Refute.bool(e))
    case S.PutSession{key, s}:
      Empty.absurd({Tk.spares(k, u, S.PutSession{key, s}) == True{} : Bool}, P.Refute.bool(e))
    case S.Subs{new}:
      Empty.absurd({Tk.spares(k, u, S.Subs{new}) == True{} : Bool}, P.Refute.bool(e))
    case S.BumpUe{bk}:
      Empty.absurd({Tk.spares(k, u, S.BumpUe{bk}) == True{} : Bool}, P.Refute.bool(e))

# Deleting sessions touches no context.
def Tk.ues_deletions(+vs: Tb.Table(S.Session), +seq: U32, +x: Tb.Table(S.Ue)) -> {Tk.ues(N.Out.tx(Up.N4.deletions(vs, seq)), x) == x : Tb.Table(S.Ue)}:
  Tk.ues_sx(N.Out.tx(Up.N4.deletions(vs, seq)), x, PW.Sx.deletions(vs, seq))

def Tk.sp_deletions(+k: U32, +u: S.Ue, +vs: Tb.Table(S.Session), +seq: U32) -> {Tk.sp(k, u, Up.N4.deletions(vs, seq)) == True{} : Bool}:
  Tk.sp_sx(k, u, N.Out.tx(Up.N4.deletions(vs, seq)), PW.Sx.deletions(vs, seq))

def Tk.keeps_clear(+k: U32, +u: S.Ue, +key: U32, +v: S.Ue, +nk: {U32.is_eq(k, key) == False{} : Bool}, +nc: {S.Ue.conflicts(v, u) == False{} : Bool}) -> {S.Sieve.keeps(S.Clear{key, v}, k, u) == True{} : Bool}:
  snk = Equal.sym(Bool, U32.is_eq(k, key), False{}, nk)
  %snk : {Bool.not(Bool.or(_, S.Ue.conflicts(v, u))) == True{} : Bool}
  snc = Equal.sym(Bool, S.Ue.conflicts(v, u), False{}, nc)
  %snc : {Bool.not(Bool.or(False{}, _)) == True{} : Bool}
  {==}

def Tk.apart(+u: S.Ue, +v: S.Ue, +c: Bool, +ec: {c == False{} : Bool}, +h: {Bool.or(Bool.not(S.Ue.conflicts(v, u)), c) == True{} : Bool}) -> {S.Ue.conflicts(v, u) == False{} : Bool}:
  match c:
    case False{}:
      P.Bool.not_true(S.Ue.conflicts(v, u), P.Bool.or_true_l(Bool.not(S.Ue.conflicts(v, u)), False{}, {==}, h))
    case True{}:
      Empty.absurd({S.Ue.conflicts(v, u) == False{} : Bool}, P.Refute.true_false(ec))

# A put keeps the row under k unless it conflicts with u, and then the put
# context holds a security context for u's SUPI.
# A put keeps the row under k, u, unless it puts a context under another key
# that conflicts with u, and then the put context holds a security context
# for u's SUPI.
def Tk.put_case(+k: U32, +u: S.Ue, +key: U32, +v: S.Ue, +ues: Tb.Table(S.Ue), +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}, +h: {Bool.or(Bool.not(S.Ue.conflicts(v, u)), S.Ue.secures(v, S.Ue.supi(u))) == True{} : Bool}, +c: Bool, +ec: {S.Ue.secures(v, S.Ue.supi(u)) == c : Bool}) -> Tk.Kept(k, u, S.Ues.put(key, v, ues)):
  match c:
    case True{}:
      sec = Equal.sym(Bool, S.Ue.secures(v, S.Ue.supi(u)), True{}, ec)
      Inr{(%sec : {Bool.or(_, S.Ues.secured(S.Ue.supi(u), S.Ues.sift(S.Clear{key, v}, ues))) == True{} : Bool}; {==})}
    case False{}:
      nc = Tk.apart(u, v, S.Ue.secures(v, S.Ue.supi(u)), ec, h)
      sk = Equal.sym(Bool, U32.is_eq(key, k), False{}, Equal.trans(Bool, U32.is_eq(key, k), U32.is_eq(k, key), False{}, P.U32.sym(key, k), h1))
      g = Sift.get(S.Clear{key, v}, k, u, ues, eu, Tk.keeps_clear(k, u, key, v, h1, nc))
      Inl{(%sk : {Tb.Table.hit(S.Ue, v, Tb.Table.get(S.Ue, k, S.Ues.sift(S.Clear{key, v}, ues)), _) == Some{u} : Maybe<&2, S.Ue>}; g)}

def Tk.put(+k: U32, +u: S.Ue, +key: U32, +v: S.Ue, +ues: Tb.Table(S.Ue), +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}, +h: {Bool.or(Bool.not(S.Ue.conflicts(v, u)), S.Ue.secures(v, S.Ue.supi(u))) == True{} : Bool}) -> Tk.Kept(k, u, S.Ues.put(key, v, ues)):
  Tk.put_case(k, u, key, v, ues, eu, h1, h, S.Ue.secures(v, S.Ue.supi(u)), {==})

def Tk.place(+k: U32, +u: S.Ue, +st: S.State, +key: U32, +v: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}, +h: {Bool.or(Bool.not(S.Ue.conflicts(v, u)), S.Ue.secures(v, S.Ue.supi(u))) == True{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.place(st, key, v)):
  +vs = Gmm.Gmm.sessions(S.Ues.evicted(key, v, S.State.ues(st)), S.State.sessions(st))
  ee = Equal.sym(Tb.Table(S.Ue), Tk.ues(N.Out.tx(Up.N4.deletions(vs, S.State.pfcp_seq(st))), S.State.ues(st)), S.State.ues(st), Tk.ues_deletions(vs, S.State.pfcp_seq(st), S.State.ues(st)))
  Tk.ok_join(k, u, S.State.ues(st), Up.N4.deletions(vs, S.State.pfcp_seq(st)), (S.Put{key, v}, Gmm.Gmm.evict(S.Ues.evicted(key, v, S.State.ues(st)))), (%ee : Tk.Kept(k, u, S.Ues.put(key, v, _)); Tk.put(k, u, key, v, S.State.ues(st), eu, h1, h)))

# The context a step acts for, keyed key, conflicts with u's row neither by
# key nor by identity.
def Tk.row(+k: U32, +key: U32, +ue: S.Ue, +u: S.Ue, +h1: {U32.is_eq(k, key) == False{} : Bool}, +h2: {S.Ue.conflicts(ue, u) == False{} : Bool}) -> {S.Row.conflicts(key, ue, k, u) == False{} : Bool}:
  sh = Equal.sym(Bool, U32.is_eq(k, key), False{}, h1)
  (%sh : {Bool.or(_, S.Ue.conflicts(ue, u)) == False{} : Bool}; h2)

def Tk.k1(+k: U32, +key: U32, +ue: S.Ue, +u: S.Ue, +h: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> {U32.is_eq(k, key) == False{} : Bool}:
  P.Bool.or_false_l(U32.is_eq(k, key), S.Ue.conflicts(ue, u), h)

def Tk.k2(+k: U32, +key: U32, +ue: S.Ue, +u: S.Ue, +h: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> {S.Ue.conflicts(ue, u) == False{} : Bool}:
  P.Bool.or_false_r(U32.is_eq(k, key), S.Ue.conflicts(ue, u), h)

# Rows of a unique table
# ----------------------

def Uniq.clear_row(+key0: U32, +w: S.Ue, +k: U32, +u: S.Ue, +k1: U32, +x: S.Ue, +more: Tb.Table(S.Ue), +hk: Bool, +ehk: {U32.is_eq(k1, k) == hk : Bool}, +ec: {Bool.and(Bool.not(S.Row.conflicts(key0, w, k1, x)), S.Ues.clear(key0, w, more)) == True{} : Bool}, +eu: {Tb.Table.hit(S.Ue, x, Tb.Table.get(S.Ue, k, more), hk) == Some{u} : Maybe<&2, S.Ue>}, ih: {S.Ues.clear(key0, w, more) == True{} : Bool} -> {Tb.Table.get(S.Ue, k, more) == Some{u} : Maybe<&2, S.Ue>} -> {S.Row.conflicts(key0, w, k, u) == False{} : Bool}) -> {S.Row.conflicts(key0, w, k, u) == False{} : Bool}:
  match hk:
    case True{}:
      r = P.Bool.not_true(S.Row.conflicts(key0, w, k1, x), P.Bool.and_true_l(Bool.not(S.Row.conflicts(key0, w, k1, x)), S.Ues.clear(key0, w, more), ec))
      ek = P.U32.eq_of_is_eq(k1, k, ehk)
      %ek : {S.Row.conflicts(key0, w, _, u) == False{} : Bool}
      ex = P.Some.inj(S.Ue, x, u, eu)
      %ex : {S.Row.conflicts(key0, w, k1, _) == False{} : Bool}
      r
    case False{}:
      ih(P.Bool.and_true_r(Bool.not(S.Row.conflicts(key0, w, k1, x)), S.Ues.clear(key0, w, more), ec), eu)

# A row clear of a table conflicts with none of its rows.
def Uniq.clear_get(+key0: U32, +w: S.Ue, +t: Tb.Table(S.Ue), +k: U32, +u: S.Ue, +ec: {S.Ues.clear(key0, w, t) == True{} : Bool}, +eu: {Tb.Table.get(S.Ue, k, t) == Some{u} : Maybe<&2, S.Ue>}) -> {S.Row.conflicts(key0, w, k, u) == False{} : Bool}:
  match t:
    case Nil{}:
      Empty.absurd({S.Row.conflicts(key0, w, k, u) == False{} : Bool}, P.Refute.none_some(S.Ue, u, eu))
    case (+k1, +x) <> +more:
      Uniq.clear_row(key0, w, k, u, k1, x, more, U32.is_eq(k1, k), {==}, ec, eu, e1 => e2 => Uniq.clear_get(key0, w, more, k, u, e1, e2))

def Uniq.row(+key: U32, +k: U32, +v: S.Ue, +u: S.Ue, +k0: U32, +w: S.Ue, +more: Tb.Table(S.Ue), +a: Bool, +ea: {U32.is_eq(k0, key) == a : Bool}, +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +eun: {Bool.and(S.Ues.clear(k0, w, more), S.Ues.unique(more)) == True{} : Bool}, +ev: {Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, key, more), a) == Some{v} : Maybe<&2, S.Ue>}, +eu: {Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, k, more), b) == Some{u} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(k, key) == False{} : Bool}, ih: {S.Ues.unique(more) == True{} : Bool} -> {Tb.Table.get(S.Ue, key, more) == Some{v} : Maybe<&2, S.Ue>} -> {Tb.Table.get(S.Ue, k, more) == Some{u} : Maybe<&2, S.Ue>} -> {S.Ue.conflicts(v, u) == False{} : Bool}) -> {S.Ue.conflicts(v, u) == False{} : Bool}:
  match a b:
    case True{} True{}:
      kk = Equal.trans(U32, k, k0, key, Equal.sym(U32, k0, k, P.U32.eq_of_is_eq(k0, k, eb)), P.U32.eq_of_is_eq(k0, key, ea))
      Empty.absurd({S.Ue.conflicts(v, u) == False{} : Bool}, P.Refute.bool(Equal.trans(Bool, False{}, U32.is_eq(k, key), True{}, Equal.sym(Bool, U32.is_eq(k, key), False{}, ne), P.U32.eq_true(k, key, kk))))
    case True{} False{}:
      ec = P.Bool.and_true_l(S.Ues.clear(k0, w, more), S.Ues.unique(more), eun)
      r = P.Bool.or_false_r(U32.is_eq(k, k0), S.Ue.conflicts(w, u), Uniq.clear_get(k0, w, more, k, u, ec, eu))
      ew = P.Some.inj(S.Ue, w, v, ev)
      %ew : {S.Ue.conflicts(_, u) == False{} : Bool}
      r
    case False{} True{}:
      ec = P.Bool.and_true_l(S.Ues.clear(k0, w, more), S.Ues.unique(more), eun)
      r = P.Bool.or_false_r(U32.is_eq(key, k0), S.Ue.conflicts(w, v), Uniq.clear_get(k0, w, more, key, v, ec, ev))
      ew = P.Some.inj(S.Ue, w, u, eu)
      %ew : {S.Ue.conflicts(v, _) == False{} : Bool}
      Equal.trans(Bool, S.Ue.conflicts(v, w), S.Ue.conflicts(w, v), False{}, Ue.conflicts_sym(v, w), r)
    case False{} False{}:
      ih(P.Bool.and_true_r(S.Ues.clear(k0, w, more), S.Ues.unique(more), eun), ev, eu)

# Two contexts of a unique table under different keys never conflict.
def Uniq.apart(+ues: Tb.Table(S.Ue), +key: U32, +k: U32, +v: S.Ue, +u: S.Ue, +eun: {S.Ues.unique(ues) == True{} : Bool}, +ev: {Tb.Table.get(S.Ue, key, ues) == Some{v} : Maybe<&2, S.Ue>}, +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +ne: {U32.is_eq(k, key) == False{} : Bool}) -> {S.Ue.conflicts(v, u) == False{} : Bool}:
  match ues:
    case Nil{}:
      Empty.absurd({S.Ue.conflicts(v, u) == False{} : Bool}, P.Refute.none_some(S.Ue, u, eu))
    case (+k0, +w) <> +more:
      Uniq.row(key, k, v, u, k0, w, more, U32.is_eq(k0, key), {==}, U32.is_eq(k0, k), {==}, eun, ev, eu, ne, e1 => e2 => e3 => Uniq.apart(more, key, k, v, u, e1, e2, e3, ne))

# The owner check
# ---------------

def Own.assoc(+w: S.Ue, +ue: S.Ue, +assoc: U32, +ew: {w == ue : S.Ue}, +ea: {U32.is_eq(S.Ue.assoc(w), assoc) == True{} : Bool}) -> {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}:
  %ew : {U32.is_eq(S.Ue.assoc(_), assoc) == True{} : Bool}
  ea

def Own.check(+w: S.Ue, +assoc: U32, +ran: B.Bytes(), +ue: S.Ue, +ok: Bool, +eok: {Bool.and(U32.is_eq(S.Ue.assoc(w), assoc), B.bytes_eq(S.Ue.ran_id(w), ran)) == ok : Bool}, +e: {N.Owner.check(w, ok) == Some{ue} : Maybe<&2, S.Ue>}) -> {Some{w} == Some{ue} : Maybe<&2, S.Ue>} & {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}:
  match ok:
    case True{}:
      ew = P.Some.inj(S.Ue, w, ue, e)
      ea = P.Bool.and_true_l(U32.is_eq(S.Ue.assoc(w), assoc), B.bytes_eq(S.Ue.ran_id(w), ran), eok)
      (e, Own.assoc(w, ue, assoc, ew, ea))
    case False{}:
      Empty.absurd({Some{w} == Some{ue} : Maybe<&2, S.Ue>} & {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}, P.Refute.none_some(S.Ue, ue, e))

def Own.get(+m: Maybe<&2, S.Ue>, +assoc: U32, +ran: B.Bytes(), +ue: S.Ue, +e: {N.Owner.of(m, assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> {m == Some{ue} : Maybe<&2, S.Ue>} & {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{ue} : Maybe<&2, S.Ue>} & {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}, P.Refute.none_some(S.Ue, ue, e))
    case Some{+w}:
      Own.check(w, assoc, ran, ue, Bool.and(U32.is_eq(S.Ue.assoc(w), assoc), B.bytes_eq(S.Ue.ran_id(w), ran)), {==}, e)

def Own.at(+ues: Tb.Table(S.Ue), +k: U32, +key: U32, +ue: S.Ue, +ek: {key == k : U32}, +eg: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>}) -> {Tb.Table.get(S.Ue, k, ues) == Some{ue} : Maybe<&2, S.Ue>}:
  %ek : {Tb.Table.get(S.Ue, _, ues) == Some{ue} : Maybe<&2, S.Ue>}
  eg

def Own.ne(+ues: Tb.Table(S.Ue), +key: U32, +k: U32, +ue: S.Ue, +u: S.Ue, +assoc: U32, +x: Bool, +ex: {U32.is_eq(k, key) == x : Bool}, +eg: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>}, +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +eb: {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      g = Own.at(ues, k, key, ue, Equal.sym(U32, k, key, P.U32.eq_of_is_eq(k, key, ex)), eg)
      eue = P.Some.inj(S.Ue, ue, u, Equal.trans(Maybe<&2, S.Ue>, Some{ue}, Tb.Table.get(S.Ue, k, ues), Some{u}, Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, ues), Some{ue}, g), eu))
      t = Own.assoc(ue, u, assoc, eue, eb)
      Empty.absurd({True{} == False{} : Bool}, P.Refute.bool(Equal.trans(Bool, False{}, U32.is_eq(S.Ue.assoc(u), assoc), True{}, Equal.sym(Bool, U32.is_eq(S.Ue.assoc(u), assoc), False{}, ea), t)))

def Own.split(+ues: Tb.Table(S.Ue), +assoc: U32, +key: U32, +ue: S.Ue, +k: U32, +u: S.Ue, +eun: {S.Ues.unique(ues) == True{} : Bool}, +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, pr: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>} & {U32.is_eq(S.Ue.assoc(ue), assoc) == True{} : Bool}) -> {U32.is_eq(k, key) == False{} : Bool} & {S.Ue.conflicts(ue, u) == False{} : Bool}:
  match pr:
    case (+eg, +eb):
      +h1 = Own.ne(ues, key, k, ue, u, assoc, U32.is_eq(k, key), {==}, eg, eu, eb, ea)
      (h1, Uniq.apart(ues, key, k, ue, u, eun, eg, eu, h1))

# The context an owner check finds is under another key than u's and, the
# table being unique, does not conflict with u.
def Own.apart(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +ue: S.Ue, +k: U32, +u: S.Ue, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> {U32.is_eq(k, key) == False{} : Bool} & {S.Ue.conflicts(ue, u) == False{} : Bool}:
  Own.split(S.State.ues(st), assoc, key, ue, k, u, eun, eu, ea, Own.get(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran, ue, eo))

# The 5G-TMSI drawn
# -----------------

def Tk.free(+ues: Tb.Table(S.Ue), +m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{t}:
      Bool.not(S.Ues.has_tmsi(t, ues))

def Tmsi.hit(+ues: Tb.Table(S.Ue), +t: U32, +later: Maybe<&2, U32>, +x: Bool, +ex: {Bool.not(S.Ues.has_tmsi(t, ues)) == x : Bool}, +el: {Tk.free(ues, later) == True{} : Bool}) -> {Tk.free(ues, Tb.Table.hit(U32, t, later, x)) == True{} : Bool}:
  match x:
    case True{}:
      ex
    case False{}:
      el

def Tmsi.free(+ues: Tb.Table(S.Ue), +words: B.Bytes()) -> {Tk.free(ues, Gmm.Gmm.tmsi(ues, words)) == True{} : Bool}:
  match words:
    case a <> b <> c <> d <> more:
      +t = N.Ngap.of_big([a, b, c, d])
      Tmsi.hit(ues, t, Gmm.Gmm.tmsi(ues, more), Bool.not(S.Ues.has_tmsi(t, ues)), {==}, Tmsi.free(ues, more))
    case a <> b <> c <> Nil{}:
      {==}
    case a <> b <> Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case Nil{}:
      {==}

def Tmsi.row(+t: U32, +k: U32, +u: S.Ue, +k0: U32, +w: S.Ue, +more: Tb.Table(S.Ue), +hk: Bool, +ehk: {U32.is_eq(k0, k) == hk : Bool}, +ef: {Bool.or(S.Maybe.same_u32(Some{t}, S.Ue.tmsi(w)), S.Ues.has_tmsi(t, more)) == False{} : Bool}, +eu: {Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, k, more), hk) == Some{u} : Maybe<&2, S.Ue>}, ih: {S.Ues.has_tmsi(t, more) == False{} : Bool} -> {Tb.Table.get(S.Ue, k, more) == Some{u} : Maybe<&2, S.Ue>} -> {S.Maybe.same_u32(Some{t}, S.Ue.tmsi(u)) == False{} : Bool}) -> {S.Maybe.same_u32(Some{t}, S.Ue.tmsi(u)) == False{} : Bool}:
  match hk:
    case True{}:
      ew = P.Some.inj(S.Ue, w, u, eu)
      %ew : {S.Maybe.same_u32(Some{t}, S.Ue.tmsi(_)) == False{} : Bool}
      P.Bool.or_false_l(S.Maybe.same_u32(Some{t}, S.Ue.tmsi(w)), S.Ues.has_tmsi(t, more), ef)
    case False{}:
      ih(P.Bool.or_false_r(S.Maybe.same_u32(Some{t}, S.Ue.tmsi(w)), S.Ues.has_tmsi(t, more), ef), eu)

# A 5G-TMSI no context holds is not u's.
def Tmsi.apart(+t: U32, +ues: Tb.Table(S.Ue), +k: U32, +u: S.Ue, +ef: {S.Ues.has_tmsi(t, ues) == False{} : Bool}, +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}) -> {S.Maybe.same_u32(Some{t}, S.Ue.tmsi(u)) == False{} : Bool}:
  match ues:
    case Nil{}:
      Empty.absurd({S.Maybe.same_u32(Some{t}, S.Ue.tmsi(u)) == False{} : Bool}, P.Refute.none_some(S.Ue, u, eu))
    case (+k0, +w) <> +more:
      Tmsi.row(t, k, u, k0, w, more, U32.is_eq(k0, k), {==}, ef, eu, e1 => e2 => Tmsi.apart(t, more, k, u, e1, e2))

# The AMF-UE-NGAP-ID given
# ------------------------
# The search for a fresh key gives an odd id that no context holds.

def Fresh.ok(+ues: Tb.Table(S.Ue), m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+k}:
      Bool.and(Bool.not(Tb.Table.has(S.Ue, k, ues)), S.Ids.odd(k))

def Fresh.odd(+id: U32) -> {S.Ids.odd(U32.or(1, id)) == True{} : Bool}:
  match id:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Fresh.next(+ues: Tb.Table(S.Ue), +c: U32, +n: Nat, +taken: Bool, +et: {Tb.Table.has(S.Ue, c, ues) == taken : Bool}, +eo: {S.Ids.odd(c) == True{} : Bool}, +ih: {Fresh.ok(ues, S.Ues.free_key(n, U32.add(c, 2), ues)) == True{} : Bool}) -> {Fresh.ok(ues, S.Ids.next(c, u => S.Ues.free_key(n, U32.add(c, 2), ues), taken)) == True{} : Bool}:
  match taken:
    case True{}:
      ih
    case False{}:
      set = Equal.sym(Bool, Tb.Table.has(S.Ue, c, ues), False{}, et)
      P.Bool.and_intro(Bool.not(Tb.Table.has(S.Ue, c, ues)), S.Ids.odd(c), (%set : {Bool.not(_) == True{} : Bool}; {==}), eo)

def Fresh.key(+fuel: Nat, +id: U32, +ues: Tb.Table(S.Ue)) -> {Fresh.ok(ues, S.Ues.free_key(fuel, id, ues)) == True{} : Bool}:
  match fuel:
    case 0n:
      {==}
    case 1n+n:
      +c = U32.or(1, id)
      Fresh.next(ues, c, n, Tb.Table.has(S.Ue, c, ues), {==}, Fresh.odd(id), Fresh.key(n, U32.add(c, 2), ues))

def Fresh.of(+st: S.State, +key: U32, +em: {S.State.fresh(st) == Some{key} : Maybe<&2, U32>}) -> {Bool.and(Bool.not(Tb.Table.has(S.Ue, key, S.State.ues(st))), S.Ids.odd(key)) == True{} : Bool}:
  +ues = S.State.ues(st)
  h = Fresh.key(1n+List.length(&2, Sigma<&2, &2, U32, _ => S.Ue>, ues), S.State.next_ue(st), ues)
  (%em : {Fresh.ok(ues, _) == True{} : Bool}; h)

def Fresh.absent(+m: Maybe<&2, S.Ue>, +e: {Tb.Table.present(S.Ue, m) == False{} : Bool}) -> {m == None{} : Maybe<&2, S.Ue>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      Empty.absurd({Some{v} == None{} : Maybe<&2, S.Ue>}, P.Refute.true_false(e))

# The key an InitialUEMessage gives holds no context.
def Fresh.none(+st: S.State, +key: U32, +em: {S.State.fresh(st) == Some{key} : Maybe<&2, U32>}) -> {Tb.Table.get(S.Ue, key, S.State.ues(st)) == None{} : Maybe<&2, S.Ue>}:
  +ues = S.State.ues(st)
  Fresh.absent(Tb.Table.get(S.Ue, key, ues), P.Bool.not_true(Tb.Table.has(S.Ue, key, ues), P.Bool.and_true_l(Bool.not(Tb.Table.has(S.Ue, key, ues)), S.Ids.odd(key), Fresh.of(st, key, em))))

def Fresh.ne(+ues: Tb.Table(S.Ue), +key: U32, +k: U32, +u: S.Ue, +x: Bool, +ex: {U32.is_eq(k, key) == x : Bool}, +eg: {Tb.Table.get(S.Ue, key, ues) == None{} : Maybe<&2, S.Ue>}, +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}) -> {x == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      kk = P.U32.eq_of_is_eq(k, key, ex)
      g : {Tb.Table.get(S.Ue, key, ues) == Some{u} : Maybe<&2, S.Ue>} = (%kk : {Tb.Table.get(S.Ue, _, ues) == Some{u} : Maybe<&2, S.Ue>}; eu)
      Empty.absurd({True{} == False{} : Bool}, P.Refute.none_some(S.Ue, u, Equal.trans(Maybe<&2, S.Ue>, None{}, Tb.Table.get(S.Ue, key, ues), Some{u}, Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, ues), None{}, eg), g)))

# u's key is not the one given.
def Fresh.apart(+st: S.State, +key: U32, +k: U32, +u: S.Ue, +em: {S.State.fresh(st) == Some{key} : Maybe<&2, U32>}, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}) -> {U32.is_eq(k, key) == False{} : Bool}:
  Fresh.ne(S.State.ues(st), key, k, u, U32.is_eq(k, key), {==}, Fresh.none(st, key, em), eu)

# Contexts put
# ------------
# What a put needs: the context does not conflict with u, or it holds a
# security context for u's SUPI.

def Tk.h_apart(+v: S.Ue, +u: S.Ue, +nc: {S.Ue.conflicts(v, u) == False{} : Bool}) -> {Bool.or(Bool.not(S.Ue.conflicts(v, u)), S.Ue.secures(v, S.Ue.supi(u))) == True{} : Bool}:
  snc = Equal.sym(Bool, S.Ue.conflicts(v, u), False{}, nc)
  %snc : {Bool.or(Bool.not(_), S.Ue.secures(v, S.Ue.supi(u))) == True{} : Bool}
  {==}

def Tk.c_dl(+ue: S.Ue, +p: S.Phase, +dl: B.Bytes(), +u: S.Ue) -> {S.Ue.conflicts(S.Ue.with_dl(ue, p, dl), u) == S.Ue.conflicts(ue, u) : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Tk.c_phase(+ue: S.Ue, +p: S.Phase, +u: S.Ue) -> {S.Ue.conflicts(S.Ue.with_phase(ue, p), u) == S.Ue.conflicts(ue, u) : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Tk.h_dl(+ue: S.Ue, +p: S.Phase, +dl: B.Bytes(), +u: S.Ue, +h2: {S.Ue.conflicts(ue, u) == False{} : Bool}) -> {Bool.or(Bool.not(S.Ue.conflicts(S.Ue.with_dl(ue, p, dl), u)), S.Ue.secures(S.Ue.with_dl(ue, p, dl), S.Ue.supi(u))) == True{} : Bool}:
  Tk.h_apart(S.Ue.with_dl(ue, p, dl), u, Equal.trans(Bool, S.Ue.conflicts(S.Ue.with_dl(ue, p, dl), u), S.Ue.conflicts(ue, u), False{}, Tk.c_dl(ue, p, dl, u), h2))

def Tk.h_phase(+ue: S.Ue, +p: S.Phase, +u: S.Ue, +h2: {S.Ue.conflicts(ue, u) == False{} : Bool}) -> {Bool.or(Bool.not(S.Ue.conflicts(S.Ue.with_phase(ue, p), u)), S.Ue.secures(S.Ue.with_phase(ue, p), S.Ue.supi(u))) == True{} : Bool}:
  Tk.h_apart(S.Ue.with_phase(ue, p), u, Equal.trans(Bool, S.Ue.conflicts(S.Ue.with_phase(ue, p), u), S.Ue.conflicts(ue, u), False{}, Tk.c_phase(ue, p, u), h2))

def Tk.or_and(+x: Bool, +r: Bool, +er: {r == False{} : Bool}) -> {Bool.or(Bool.not(Bool.or(x, r)), Bool.and(x, True{})) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      ser = Equal.sym(Bool, r, False{}, er)
      %ser : {Bool.or(Bool.not(_), False{}) == True{} : Bool}
      {==}

# Authentication succeeded: the context takes the verified SUPI and a
# security context, so if it conflicts with u it does so by u's SUPI.
def Tk.h_secure(+ue: S.Ue, +s: B.Digits(), +g: S.Guard, +c: Sec.Nas.Ctx, +ka: B.Bytes(), +dl: B.Bytes(), +u: S.Ue, +h2: {S.Ue.conflicts(ue, u) == False{} : Bool}) -> {Bool.or(Bool.not(S.Ue.conflicts(S.Ue.with_dl(S.Ue.with_supi(ue, s), S.SecurityMode{g, c, ka}, dl), u)), S.Ue.secures(S.Ue.with_dl(S.Ue.with_supi(ue, s), S.SecurityMode{g, c, ka}, dl), S.Ue.supi(u))) == True{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      +rest = Bool.or(S.Maybe.same_u32(tmsi, S.Ue.tmsi(u)), Bool.and(U32.is_eq(assoc, S.Ue.assoc(u)), B.bytes_eq(ran_id, S.Ue.ran_id(u))))
      Tk.or_and(S.Maybe.same_bytes(Some{s}, S.Ue.supi(u)), rest, P.Bool.or_false_r(S.Maybe.same_bytes(supi, S.Ue.supi(u)), rest, h2))

def Tk.or3(+x: Bool, +y: Bool, +z: Bool, +ex: {x == False{} : Bool}, +ey: {y == False{} : Bool}, +ez: {z == False{} : Bool}) -> {Bool.or(x, Bool.or(y, z)) == False{} : Bool}:
  sx = Equal.sym(Bool, x, False{}, ex)
  %sx : {Bool.or(_, Bool.or(y, z)) == False{} : Bool}
  sy = Equal.sym(Bool, y, False{}, ey)
  %sy : {Bool.or(False{}, Bool.or(_, z)) == False{} : Bool}
  sz = Equal.sym(Bool, z, False{}, ez)
  %sz : {Bool.or(False{}, Bool.or(False{}, _)) == False{} : Bool}
  {==}

# Security mode completed: the context takes a 5G-TMSI no context holds.
def Tk.h_tmsi(+ue: S.Ue, +p: S.Phase, +dl: B.Bytes(), +reg: B.Bytes(), +t: U32, +u: S.Ue, +h2: {S.Ue.conflicts(ue, u) == False{} : Bool}, +ht: {S.Maybe.same_u32(Some{t}, S.Ue.tmsi(u)) == False{} : Bool}) -> {Bool.or(Bool.not(S.Ue.conflicts(S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(ue, p, dl), reg), t), u)), S.Ue.secures(S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(ue, p, dl), reg), t), S.Ue.supi(u))) == True{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg0, ngksi, phase, last_dl}:
      +x = S.Maybe.same_bytes(supi, S.Ue.supi(u))
      +z = Bool.and(U32.is_eq(assoc, S.Ue.assoc(u)), B.bytes_eq(ran_id, S.Ue.ran_id(u)))
      +yz = Bool.or(S.Maybe.same_u32(tmsi, S.Ue.tmsi(u)), z)
      ex = P.Bool.or_false_l(x, yz, h2)
      ez = P.Bool.or_false_r(S.Maybe.same_u32(tmsi, S.Ue.tmsi(u)), z, P.Bool.or_false_r(x, yz, h2))
      Tk.h_apart(S.Ue{assoc, ran_id, stream, supi, Some{t}, reg, ngksi, p, dl}, u, Tk.or3(x, S.Maybe.same_u32(Some{t}, S.Ue.tmsi(u)), z, ex, ht, ez))

# A context the InitialUEMessage creates has no SUPI, no 5G-TMSI and another association.
def Tk.fresh(+assoc: U32, +ran: B.Bytes(), +stream: U32, +nas: B.Bytes(), +u: S.Ue, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> {S.Ue.conflicts(S.Ue{assoc, ran, stream, None{}, None{}, nas, 0, S.Created{}, []}, u) == False{} : Bool}:
  e = Equal.sym(Bool, U32.is_eq(assoc, S.Ue.assoc(u)), False{}, Equal.trans(Bool, U32.is_eq(assoc, S.Ue.assoc(u)), U32.is_eq(S.Ue.assoc(u), assoc), False{}, P.U32.sym(assoc, S.Ue.assoc(u)), ea))
  %e : {Bool.or(S.Maybe.same_bytes(None{}, S.Ue.supi(u)), Bool.or(S.Maybe.same_u32(None{}, S.Ue.tmsi(u)), Bool.and(_, B.bytes_eq(ran, S.Ue.ran_id(u))))) == False{} : Bool}
  {==}

# Walking every NGAP path
# -----------------------
# Each lemma follows one procedure: a context put either conflicts with no
# other context or holds a security context for its SUPI; anything else
# touches only the context the message names, owned by its association.

def Tk.sp_rephase(+k: U32, +u: S.Ue, +key: U32, +p: S.Phase, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.spares(k, u, S.Rephase{key, p}) == True{} : Bool}:
  s = Equal.sym(Bool, U32.is_eq(k, key), False{}, h1)
  %s : {Bool.not(_) == True{} : Bool}
  {==}

def Tk.sp_del(+k: U32, +u: S.Ue, +key: U32, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.spares(k, u, S.Del{key}) == True{} : Bool}:
  s = Equal.sym(Bool, U32.is_eq(k, key), False{}, h1)
  %s : {Bool.not(_) == True{} : Bool}
  {==}

def Tk.sp_verified(+k: U32, +u: S.Ue, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +why: String, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.sp(k, u, N.Out.verified(key, ue, ctx, why)) == True{} : Bool}:
  Tk.sp_rephase(k, u, key, S.Phase.with_ctx(S.Ue.phase(ue), ctx), h1)

def Tk.sp_dl(+k: U32, +u: S.Ue, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +plain: B.Bytes(), +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.sp(k, u, N.Out.dl(key, ue, ctx, plain)) == True{} : Bool}:
  Tk.sp_rephase(k, u, key, S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(Sec.Nas.protect(ctx, Sec.Ciphered{}, plain))), h1)

# 5GSM (Ws): phase changes of the UE named, and sessions.

def Ws.join(+k: U32, +u: S.Ue) -> PW.It.Join(o => {Tk.sp(k, u, o) == True{} : Bool}):
  +a => +b => ha => hb => Tk.sp_join(k, u, a, b, ha, hb)

def Ws.written(+key: U32, +ue: S.Ue, +c: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue, +hk: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.sp(k, u, Gsm.Gsm.ctx_written(key, ue, c)) == True{} : Bool}:
  match c:
    case None{}:
      {==}
    case Some{+x}:
      Tk.sp_rephase(k, u, key, S.Phase.with_ctx(S.Ue.phase(ue), x), hk)

def Ws.give_up_in(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, +t: Gsm.Tell, +seq: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue) -> {Tk.sp(k, u, Gsm.Gsm.Item.out(Gsm.Gsm.give_up_in(key, ue, skey, s, t, seq, c))) == True{} : Bool}:
  PW.It.give_up_in(o => {Tk.sp(k, u, o) == True{} : Bool}, Ws.join(k, u), key, ue, skey, s, t, seq, c, x => {==}, Tk.sp_deletions(k, u, [(skey, s)], seq))

def Ws.modify(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, +seq: U32, +tunnel: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +c: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue) -> {Tk.sp(k, u, Gsm.Gsm.Item.out(Gsm.Gsm.modify(key, ue, skey, s, seq, tunnel, c))) == True{} : Bool}:
  match tunnel:
    case None{}:
      Ws.give_up_in(key, ue, skey, s, Gsm.Release{}, seq, c, k, u)
    case Some{(t, a)}:
      {==}

def Ws.set_up_phase(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, +transfer: B.Bytes(), +seq: U32, +p: S.SPhase, +c: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue) -> {Tk.sp(k, u, Gsm.Gsm.Item.out(Gsm.Gsm.set_up_phase(key, ue, skey, s, transfer, seq, p, c))) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, pti}:
      Ws.modify(key, ue, skey, s, seq, Gsm.Gsm.tunnel_of(G.PDUSessionResourceSetupResponseTransfer.read(Ap.Cur{0n, Ap.unpack(transfer)})), c, k, u)
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Deleting{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Ws.failed_phase(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, +seq: U32, +p: S.SPhase, +c: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue) -> {Tk.sp(k, u, Gsm.Gsm.Item.out(Gsm.Gsm.failed_phase(key, ue, skey, s, seq, p, c))) == True{} : Bool}:
  match p:
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, +pti}:
      Ws.give_up_in(key, ue, skey, s, Gsm.Reply{Gsm.Gsm.reject(S.Session.psi(s), pti, 26)}, seq, c, k, u)
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Deleting{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Ws.set_up(+key: U32, +ue: S.Ue, +transfer: B.Bytes(), +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +c: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue) -> {Tk.sp(k, u, Gsm.Gsm.Item.out(Gsm.Gsm.set_up(key, ue, transfer, seq, m, c))) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Ws.set_up_phase(key, ue, skey, s, transfer, seq, S.Session.phase(s), c, k, u)

def Ws.failed(+key: U32, +ue: S.Ue, +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +c: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue) -> {Tk.sp(k, u, Gsm.Gsm.Item.out(Gsm.Gsm.failed(key, ue, seq, m, c))) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Ws.failed_phase(key, ue, skey, s, seq, S.Session.phase(s), c, k, u)

def Ws.set_up_last(+key: U32, +ue: S.Ue, +transfer: B.Bytes(), +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +again: Bool, +c: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue) -> {Tk.sp(k, u, Gsm.Gsm.Item.out(Gsm.Gsm.set_up_last(key, ue, transfer, seq, m, again, c))) == True{} : Bool}:
  match again:
    case True{}:
      {==}
    case False{}:
      Ws.set_up(key, ue, transfer, seq, m, c, k, u)

def Ws.set_ups(+st: S.State, +key: U32, +ue: S.Ue, +items: G.PDUSessionResourceSetupListSURes(), +seq: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue) -> {Tk.sp(k, u, Gsm.Gsm.Item.out(Gsm.Gsm.set_ups(st, key, ue, items, seq, c))) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case G.PDUSessionResourceSetupItemSURes{+psi, +transfer, x} <> +more:
      +m = S.Sessions.by_psi(key, psi, S.State.sessions(st))
      PW.It.then(o => {Tk.sp(k, u, o) == True{} : Bool}, Ws.join(k, u), Gsm.Gsm.after((S.BumpSeq{1}, []), Gsm.Gsm.set_up_last(key, ue, transfer, seq, m, Gsm.Gsm.named(psi, more), c)), c2 => Gsm.Gsm.set_ups(st, key, ue, more, U32.add(seq, 1), c2), PW.It.after(o => {Tk.sp(k, u, o) == True{} : Bool}, Ws.join(k, u), (S.BumpSeq{1}, []), Gsm.Gsm.set_up_last(key, ue, transfer, seq, m, Gsm.Gsm.named(psi, more), c), {==}, Ws.set_up_last(key, ue, transfer, seq, m, Gsm.Gsm.named(psi, more), c, k, u)), +c2 => Ws.set_ups(st, key, ue, more, U32.add(seq, 1), c2, k, u))

def Ws.faileds(+st: S.State, +key: U32, +ue: S.Ue, +items: G.PDUSessionResourceFailedToSetupListSURes(), +seq: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue) -> {Tk.sp(k, u, Gsm.Gsm.Item.out(Gsm.Gsm.faileds(st, key, ue, items, seq, c))) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case G.PDUSessionResourceFailedToSetupItemSURes{+psi, transfer, x} <> +more:
      +m = S.Sessions.by_psi(key, psi, S.State.sessions(st))
      PW.It.then(o => {Tk.sp(k, u, o) == True{} : Bool}, Ws.join(k, u), Gsm.Gsm.after((S.BumpSeq{1}, []), Gsm.Gsm.failed(key, ue, seq, m, c)), c2 => Gsm.Gsm.faileds(st, key, ue, more, U32.add(seq, 1), c2), PW.It.after(o => {Tk.sp(k, u, o) == True{} : Bool}, Ws.join(k, u), (S.BumpSeq{1}, []), Gsm.Gsm.failed(key, ue, seq, m, c), {==}, Ws.failed(key, ue, seq, m, c, k, u)), +c2 => Ws.faileds(st, key, ue, more, U32.add(seq, 1), c2, k, u))

def Ws.results(+st: S.State, +key: U32, +ue: S.Ue, +oks: G.PDUSessionResourceSetupListSURes(), +fails: G.PDUSessionResourceFailedToSetupListSURes(), +k: U32, +u: S.Ue, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.sp(k, u, Gsm.Gsm.results(st, key, ue, oks, fails)) == True{} : Bool}:
  +seq = S.State.pfcp_seq(st)
  +seq2 = U32.add(seq, U32.from_nat(List.length(&2, G.PDUSessionResourceSetupItemSURes, oks)))
  PW.It.under(o => {Tk.sp(k, u, o) == True{} : Bool}, Ws.join(k, u), key, ue, c => Gsm.Gsm.then(Gsm.Gsm.set_ups(st, key, ue, oks, seq, c), c2 => Gsm.Gsm.faileds(st, key, ue, fails, seq2, c2)), +c => PW.It.then(o => {Tk.sp(k, u, o) == True{} : Bool}, Ws.join(k, u), Gsm.Gsm.set_ups(st, key, ue, oks, seq, c), c2 => Gsm.Gsm.faileds(st, key, ue, fails, seq2, c2), Ws.set_ups(st, key, ue, oks, seq, c, k, u), +c2 => Ws.faileds(st, key, ue, fails, seq2, c2, k, u)), ec => +c => Ws.written(key, ue, c, k, u, h1))

def Ws.place(+st: S.State, +key: U32, +s: S.Session, +seq: U32, +k: U32, +u: S.Ue) -> {Tk.sp(k, u, Gsm.Gsm.place(st, key, s, seq)) == True{} : Bool}:
  Tk.sp_join(k, u, Up.N4.deletions(S.Sessions.evicted(key, s, S.State.sessions(st)), seq), (S.PutSession{key, s}, []), Tk.sp_deletions(k, u, S.Sessions.evicted(key, s, S.State.sessions(st)), seq), {==})

def Ws.create(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, +ip: U32, +teid: U32, +seid: U32, +v4v6: Bool, +dns: Bool, +k: U32, +u: S.Ue, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.sp(k, u, Gsm.Gsm.create(st, key, ue, ctx, cfg, psi, pti, ip, teid, seid, v4v6, dns)) == True{} : Bool}:
  +seq = S.State.pfcp_seq(st)
  +s : S.Session = S.Session{S.SId{key, psi, ip, teid}, S.SVar{[], seq, S.Creating{S.Guard{0}, pti, Gsm.Gsm.accept(cfg, psi, pti, ip, dns, v4v6), Up.N4.establish(cfg, seid, ip, teid, seq)}}}
  +ph = S.Phase.with_ctx(S.Ue.phase(ue), ctx)
  Tk.sp_join(k, u, (S.Both{S.Rephase{key, ph}, S.BumpSeq{1}}, [N.Pfcp{Some{key}, Up.N4.establish(cfg, seid, ip, teid, seq)}, N.TimerStart{Some{key}, seid, Up.N4.t1_ms()}]), Gsm.Gsm.place(st, seid, s, U32.add(seq, 1)), P.Bool.and_intro(Tk.spares(k, u, S.Rephase{key, ph}), True{}, Tk.sp_rephase(k, u, key, ph, h1), {==}), Ws.place(st, seid, s, U32.add(seq, 1), k, u))

def Ws.checked(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +cfg: S.Cfg, +psi: U32, +pti: U32, +c: Gsm.Check, +k: U32, +u: S.Ue, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.sp(k, u, Gsm.Gsm.checked(st, key, ue, ctx, cfg, psi, pti, c)) == True{} : Bool}:
  match c:
    case Gsm.Refuse{+cause}:
      Tk.sp_dl(k, u, key, ue, ctx, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.reject(psi, pti, cause)), h1)
    case Gsm.Go{+v4v6, +dns, +ip, +teid, +seid}:
      Ws.create(st, key, ue, ctx, cfg, psi, pti, ip, teid, seid, v4v6, dns, k, u, h1)

def Ws.with_cfg(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +psi: U32, +pti: U32, +mm_opts: List<&2, I.Ie>, +sm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +cfg: Maybe<&2, S.Cfg>, +k: U32, +u: S.Ue, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.sp(k, u, Gsm.Gsm.with_cfg(st, key, ue, ctx, psi, pti, mm_opts, sm_opts, entropy, cfg)) == True{} : Bool}:
  match cfg:
    case None{}:
      Tk.sp_verified(k, u, key, ue, ctx, "5GSM: no configuration", h1)
    case Some{+c}:
      Ws.checked(st, key, ue, ctx, c, psi, pti, Gsm.Gsm.validate(c, psi, mm_opts, sm_opts, Up.N4.up(st), S.State.sessions(st), entropy), k, u, h1)

def Ws.message(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +mm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Sm.Sm>, +k: U32, +u: S.Ue, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.sp(k, u, Gsm.Gsm.message(st, key, ue, ctx, mm_opts, entropy, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      Tk.sp_verified(k, u, key, ue, ctx, "5GSM: message not understood", h1)
    case Done{Sm.Sm{+psi, +pti, mt, fields, +opts}}:
      match mt:
        case Sm.EstablishmentRequest{}:
          Ws.with_cfg(st, key, ue, ctx, psi, pti, mm_opts, opts, entropy, S.State.config(st), k, u, h1)
        case Sm.EstablishmentAccept{}:
          Tk.sp_verified(k, u, key, ue, ctx, "5GSM: message not expected", h1)
        case Sm.EstablishmentReject{}:
          Tk.sp_verified(k, u, key, ue, ctx, "5GSM: message not expected", h1)
        case Sm.ModificationRequest{}:
          Tk.sp_dl(k, u, key, ue, ctx, Gsm.Gsm.dl_transport(psi, Gsm.Gsm.modification_reject(psi, pti)), h1)
        case Sm.ModificationReject{}:
          Tk.sp_verified(k, u, key, ue, ctx, "5GSM: message not expected", h1)
        case Sm.ReleaseRequest{}:
          Tk.sp_verified(k, u, key, ue, ctx, "5GSM: message not expected", h1)
        case Sm.ReleaseCommand{}:
          Tk.sp_verified(k, u, key, ue, ctx, "5GSM: message not expected", h1)
        case Sm.ReleaseComplete{}:
          Tk.sp_verified(k, u, key, ue, ctx, "5GSM: message not expected", h1)
        case Sm.SmStatus{}:
          Tk.sp_verified(k, u, key, ue, ctx, "5GSM: message not expected", h1)

def Ws.n1(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +mm_opts: List<&2, I.Ie>, +entropy: B.Bytes(), +container: B.Bytes(), +n1: Bool, +k: U32, +u: S.Ue, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.sp(k, u, Gsm.Gsm.n1(st, key, ue, ctx, mm_opts, entropy, container, n1)) == True{} : Bool}:
  match n1:
    case True{}:
      Ws.message(st, key, ue, ctx, mm_opts, entropy, Sm.Sm.read(container), k, u, h1)
    case False{}:
      Tk.sp_verified(k, u, key, ue, ctx, "5GMM: payload container not N1 SM information", h1)

def Ws.ul_transport(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +entropy: B.Bytes(), +k: U32, +u: S.Ue, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> {Tk.sp(k, u, Gsm.Gsm.ul_transport(st, key, ue, ctx, fields, opts, entropy)) == True{} : Bool}:
  Ws.n1(st, key, ue, ctx, opts, entropy, I.Fields.lve2(fields), U32.is_eq(I.Fields.byte1(fields), 1), k, u, h1)

# 5GMM (W)

def W.release(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.release(st, key, ue, cause)):
  +ur = S.Ue.with_phase(ue, S.Releasing{S.Guard{0}})
  +ts : List<&2, N.Act> = N.TimerStart{Some{key}, key, N.Ue.guard_ms()} <> Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause)
  Tk.ok_prepend(k, u, S.State.ues(st), N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}, N.Out.also(Gmm.Gmm.place(st, key, ur), ts), Tk.ok_also(k, u, S.State.ues(st), Gmm.Gmm.place(st, key, ur), ts, Tk.place(k, u, st, key, ur, eu, Tk.k1(k, key, ue, u, h2), Tk.h_phase(ue, S.Releasing{S.Guard{0}}, u, Tk.k2(k, key, ue, u, h2)))))

def W.refuse(+st: S.State, +key: U32, +ue: S.Ue, +nas: B.Bytes(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.refuse(st, key, ue, nas)):
  Tk.ok_prepend(k, u, S.State.ues(st), Gmm.Gmm.dl(key, ue, nas), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified())), W.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), k, u, eu, h2))

def W.reject(+st: S.State, +key: U32, +ue: S.Ue, +cause: U32, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.reject(st, key, ue, cause)):
  W.refuse(st, key, ue, Gmm.Gmm.registration_reject(cause), k, u, eu, h2)

def W.auth_reject(+st: S.State, +key: U32, +ue: S.Ue, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.auth_reject(st, key, ue)):
  Tk.ok_prepend(k, u, S.State.ues(st), Gmm.Gmm.dl(key, ue, Gmm.Gmm.authentication_reject()), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure())), W.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure()), k, u, eu, h2))

def W.identity_ask(+st: S.State, +key: U32, +ue: S.Ue, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.identity_ask(st, key, ue)):
  +nas = Gmm.Gmm.identity_request()
  +p : S.Phase = S.Identifying{S.Guard{0}}
  +ue2 = S.Ue.with_dl(ue, p, nas)
  Tk.ok_also(k, u, S.State.ues(st), Gmm.Gmm.place(st, key, ue2), [Gmm.Gmm.dl(key, ue2, nas), N.TimerStart{Some{key}, key, N.Ue.guard_ms()}], Tk.place(k, u, st, key, ue2, eu, Tk.k1(k, key, ue, u, h2), Tk.h_dl(ue, p, nas, u, Tk.k2(k, key, ue, u, h2))))

def W.challenge(+st: S.State, +key: U32, +ue: S.Ue, +sub: Au.Subscriber, +snn: B.Bytes(), +entropy: B.Bytes(), +resynced: Bool, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.challenge(st, key, ue, sub, snn, entropy, resynced)):
  +sub2 = Au.Subscriber.with_sqn(sub, Au.Sqn.next(Au.Subscriber.sqn(sub)))
  +av = Au.Av.make(sub2, snn, List.take(&2, U32, entropy, 16n))
  +nas = Gmm.Gmm.auth_request(0, av)
  +p : S.Phase = S.Authenticating{S.Guard{0}, av, resynced, Au.Subscriber.supi(sub2)}
  +ue2 = S.Ue.with_dl(ue, p, nas)
  Tk.ok_join(k, u, S.State.ues(st), Gmm.Gmm.place(st, key, ue2), (S.Subs{Au.Subscribers.update(sub2, S.State.subs(st))}, [Gmm.Gmm.dl(key, ue2, nas), N.TimerStart{Some{key}, key, N.Ue.guard_ms()}]), Tk.place(k, u, st, key, ue2, eu, Tk.k1(k, key, ue, u, h2), Tk.h_dl(ue, p, nas, u, Tk.k2(k, key, ue, u, h2))))

def W.by_sub(+st: S.State, +key: U32, +ue: S.Ue, +cfg: S.Cfg, +m: Maybe<&2, Au.Subscriber>, +entropy: B.Bytes(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.by_sub(st, key, ue, cfg, m, entropy)):
  match m:
    case None{}:
      W.reject(st, key, ue, 7, k, u, eu, h2)
    case Some{+sub}:
      W.challenge(st, key, ue, sub, Au.Ausf.snn(S.Cfg.plmn(cfg)), entropy, False{}, k, u, eu, h2)

def W.by_supi(+st: S.State, +key: U32, +ue: S.Ue, +cfg: S.Cfg, +r: Result<&2, &2, B.Err, Su.Supi>, +entropy: B.Bytes(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.by_supi(st, key, ue, cfg, r, entropy)):
  match r:
    case Fail{e}:
      W.reject(st, key, ue, 7, k, u, eu, h2)
    case Done{Su.Imsi{+plmn, +msin}}:
      W.by_sub(st, key, ue, cfg, Au.Subscribers.find(List.append(&2, U32, Pl.Plmn.mcc(plmn), List.append(&2, U32, Pl.Plmn.mnc(plmn), msin)), S.State.subs(st)), entropy, k, u, eu, h2)

def W.with_cfg(+st: S.State, +key: U32, +ue: S.Ue, +suci: Su.Suci, +entropy: B.Bytes(), +cfg: Maybe<&2, S.Cfg>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.with_cfg(st, key, ue, suci, entropy, cfg)):
  match cfg:
    case None{}:
      W.reject(st, key, ue, 7, k, u, eu, h2)
    case Some{+c}:
      W.by_supi(st, key, ue, c, Su.Suci.deconceal(S.Cfg.suci_key(c), suci), entropy, k, u, eu, h2)

def W.identified(+st: S.State, +key: U32, +ue: S.Ue, +suci: Su.Suci, +entropy: B.Bytes(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.identified(st, key, ue, suci, entropy)):
  W.with_cfg(st, key, ue, suci, entropy, S.State.config(st), k, u, eu, h2)

def W.proceed(+st: S.State, +key: U32, +ue: S.Ue, +how: Gmm.Start, +entropy: B.Bytes(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.proceed(st, key, ue, how, entropy)):
  match how:
    case Gmm.Identified{+suci}:
      W.identified(st, key, ue, suci, entropy, k, u, eu, h2)
    case Gmm.Ask{}:
      W.identity_ask(st, key, ue, k, u, eu, h2)
    case Gmm.Unknown{}:
      W.reject(st, key, ue, 7, k, u, eu, h2)

def W.register(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +r: Mi.MobileId.Res(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +hk: {U32.is_eq(k, key) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.register(st, key, assoc, stream, entropy, ran, nas, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{+id}:
      +fresh : S.Ue = Gmm.Gmm.fresh(assoc, ran, stream, nas)
      Tk.ok_join(k, u, S.State.ues(st), (S.BumpUe{key}, []), Gmm.Gmm.proceed(st, key, fresh, Gmm.Gmm.start_of(id), entropy), W.proceed(st, key, fresh, Gmm.Gmm.start_of(id), entropy, k, u, eu, Tk.row(k, key, fresh, u, hk, Tk.fresh(assoc, ran, stream, nas, u, ea))))

def W.serve(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +ran: B.Bytes(), +nas: B.Bytes(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +hk: {U32.is_eq(k, key) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.serve(st, key, assoc, stream, ran, nas)):
  +fresh : S.Ue = Gmm.Gmm.fresh(assoc, ran, stream, nas)
  Tk.ok_join(k, u, S.State.ues(st), (S.BumpUe{key}, []), Gmm.Gmm.refuse(st, key, fresh, Gmm.Gmm.service_reject()), W.refuse(st, key, fresh, Gmm.Gmm.service_reject(), k, u, eu, Tk.row(k, key, fresh, u, hk, Tk.fresh(assoc, ran, stream, nas, u, ea))))

def W.initial_mm(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +m: Mm.Mm, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +hk: {U32.is_eq(k, key) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.initial_mm(st, key, assoc, stream, entropy, ran, nas, m)):
  match m:
    case Mm.Mm{mt, +fields, opts}:
      match mt:
        case Mm.RegistrationRequest{}:
          W.register(st, key, assoc, stream, entropy, ran, nas, Mi.MobileId.read(I.Fields.lve2(fields)), k, u, eu, ea, hk)
        case Mm.RegistrationAccept{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.RegistrationComplete{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.RegistrationReject{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.DeregistrationRequestUe{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.DeregistrationAcceptUe{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.ConfigurationUpdateCommand{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.AuthenticationRequest{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.AuthenticationResponse{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.AuthenticationReject{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.AuthenticationFailure{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.IdentityRequest{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.IdentityResponse{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.SecurityModeCommand{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.SecurityModeComplete{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.SecurityModeReject{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.Status{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.UlNasTransport{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.DlNasTransport{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case Mm.ServiceRequest{}:
          W.serve(st, key, assoc, stream, ran, nas, k, u, eu, ea, hk)
        case Mm.ServiceReject{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)

def W.initial_nas(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +r: Result<&2, &2, B.Err, Mm.Mm>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +hk: {U32.is_eq(k, key) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.initial_nas(st, key, assoc, stream, entropy, ran, nas, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{+m}:
      W.initial_mm(st, key, assoc, stream, entropy, ran, nas, m, k, u, eu, ea, hk)

# The key the InitialUEMessage gives holds no context, so it is not u's.
def W.initial_key(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), +m: Maybe<&2, U32>, +em: {S.State.fresh(st) == m : Maybe<&2, U32>}, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.initial_key(st, assoc, stream, entropy, ran, nas, m)):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+key}:
      W.initial_nas(st, key, assoc, stream, entropy, ran, nas, Mm.Mm.read(nas), k, u, eu, ea, Fresh.apart(st, key, k, u, em, eu))

def W.initial(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +v: V.InitialUEMessage.View, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.initial(st, assoc, stream, entropy, v)):
  match v:
    case V.InitialUEMessage.View{+ran_ue_ngap_id, +nas_pdu, userlocationinformation, rrcestablishmentcause, fiveg_s_tmsi, amfsetid, allowednssai, selectedplmnidentity, iabnodeindication, cemodebsupport_indicator, npn_accessinformation}:
      W.initial_key(st, assoc, stream, entropy, ran_ue_ngap_id, Gmm.Gmm.unprotected(nas_pdu), S.State.fresh(st), {==}, k, u, eu, ea)

def W.initial_of_view(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, V.InitialUEMessage.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{+v}:
      W.initial(st, assoc, stream, entropy, v, k, u, eu, eun, ea)

def W.verified(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +why: String, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), N.Out.verified(key, ue, ctx, why)):
  Tk.ok_sp(k, u, S.State.ues(st), N.Out.verified(key, ue, ctx, why), eu, Tk.sp_verified(k, u, key, ue, ctx, why, h1))

def W.secure(+st: S.State, +key: U32, +ue: S.Ue, +supi: B.Digits(), +k_amf: B.Bytes(), +nea: Sec.Nas.Ea, +nia: Sec.Nas.Ia, +caps: B.Bytes(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.secure(st, key, ue, supi, k_amf, nea, nia, caps)):
  +ctx : Sec.Nas.Ctx = Sec.Ctx{Sec.Keys{Kd.kdf.k_nas_int(k_amf, Sec.Nas.Ia.id(nia)), Kd.kdf.k_nas_enc(k_amf, Sec.Nas.Ea.id(nea)), nea, nia, 1}, Sec.Nas.Count.zero(), None{}}
  +smc = Gmm.Gmm.security_mode_command(U32.or(U32.shln(Sec.Nas.Ea.id(nea), 4n), Sec.Nas.Ia.id(nia)), S.Ue.ngksi(ue), caps)
  +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.IntegrityNew{}, smc)
  +ue2 = S.Ue.with_dl(S.Ue.with_supi(ue, supi), S.SecurityMode{S.Guard{0}, Sec.Nas.Protected.ctx(p), k_amf}, smc)
  Tk.ok_also(k, u, S.State.ues(st), Gmm.Gmm.place(st, key, ue2), [Gmm.Gmm.dl(key, S.Ue.with_supi(ue, supi), Sec.Nas.Protected.msg(p)), N.TimerStart{Some{key}, key, N.Ue.guard_ms()}], Tk.place(k, u, st, key, ue2, eu, Tk.k1(k, key, ue, u, h2), Tk.h_secure(ue, supi, S.Guard{0}, Sec.Nas.Protected.ctx(p), k_amf, smc, u, Tk.k2(k, key, ue, u, h2))))

def W.algorithms(+st: S.State, +key: U32, +ue: S.Ue, +supi: B.Digits(), +k_amf: B.Bytes(), +caps: B.Bytes(), +mea: Maybe<&2, Sec.Nas.Ea>, +mia: Maybe<&2, Sec.Nas.Ia>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.algorithms(st, key, ue, supi, k_amf, caps, mea, mia)):
  match mea mia:
    case Some{+a} Some{+b}:
      W.secure(st, key, ue, supi, k_amf, a, b, caps, k, u, eu, h2)
    case Some{a} None{}:
      W.reject(st, key, ue, 23, k, u, eu, h2)
    case None{} Some{b}:
      W.reject(st, key, ue, 23, k, u, eu, h2)
    case None{} None{}:
      W.reject(st, key, ue, 23, k, u, eu, h2)

def W.keys(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +cfg: Maybe<&2, S.Cfg>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.keys(st, key, ue, av, supi, cfg)):
  match cfg:
    case Some{+c}:
      +caps = N.Ue.caps(ue)
      W.algorithms(st, key, ue, supi, Au.Ausf.k_amf(av, Au.Ausf.snn(S.Cfg.plmn(c)), supi), caps, Gmm.Alg.pick_ea(S.Cfg.nea(c), N.Ngap.cap_byte(caps, 0n)), Gmm.Alg.pick_ia(S.Cfg.nia(c), N.Ngap.cap_byte(caps, 1n)), k, u, eu, h2)
    case None{}:
      W.auth_reject(st, key, ue, k, u, eu, h2)

def W.verified_res(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +ok: Bool, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.verified(st, key, ue, av, supi, ok)):
  match ok:
    case True{}:
      W.keys(st, key, ue, av, supi, S.State.config(st), k, u, eu, h2)
    case False{}:
      W.auth_reject(st, key, ue, k, u, eu, h2)

def W.response(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +res: Maybe<&2, B.Bytes()>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.response(st, key, ue, av, supi, res)):
  match res:
    case None{}:
      W.auth_reject(st, key, ue, k, u, eu, h2)
    case Some{+r}:
      W.verified_res(st, key, ue, av, supi, Au.Ausf.verify(av, r), k, u, eu, h2)

def W.resynced(+st: S.State, +key: U32, +ue: S.Ue, +sub: Au.Subscriber, +cfg: S.Cfg, +entropy: B.Bytes(), +m: Maybe<&2, B.Bytes()>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.resynced(st, key, ue, sub, cfg, entropy, m)):
  match m:
    case None{}:
      W.auth_reject(st, key, ue, k, u, eu, h2)
    case Some{+sqn_ms}:
      W.challenge(st, key, ue, Au.Subscriber.with_sqn(sub, sqn_ms), Au.Ausf.snn(S.Cfg.plmn(cfg)), entropy, True{}, k, u, eu, h2)

def W.resync_sub(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +auts: B.Bytes(), +entropy: B.Bytes(), +cfg: S.Cfg, +m: Maybe<&2, Au.Subscriber>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.resync_sub(st, key, ue, av, auts, entropy, cfg, m)):
  match m:
    case None{}:
      W.auth_reject(st, key, ue, k, u, eu, h2)
    case Some{+sub}:
      W.resynced(st, key, ue, sub, cfg, entropy, Au.Ausf.resync(sub, Au.Av.rand(av), auts), k, u, eu, h2)

def W.resync(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +auts: B.Bytes(), +entropy: B.Bytes(), +supi: B.Digits(), +cfg: Maybe<&2, S.Cfg>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.resync(st, key, ue, av, auts, entropy, supi, cfg)):
  match cfg:
    case Some{+c}:
      W.resync_sub(st, key, ue, av, auts, entropy, c, Au.Subscribers.find(supi, S.State.subs(st)), k, u, eu, h2)
    case None{}:
      W.auth_reject(st, key, ue, k, u, eu, h2)

def W.failure_kind(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +supi: B.Digits(), +auts: Maybe<&2, B.Bytes()>, +entropy: B.Bytes(), +retry: Bool, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.failure_kind(st, key, ue, av, supi, auts, entropy, retry)):
  match auts retry:
    case Some{+a} True{}:
      W.resync(st, key, ue, av, a, entropy, supi, S.State.config(st), k, u, eu, h2)
    case Some{a} False{}:
      W.auth_reject(st, key, ue, k, u, eu, h2)
    case None{} True{}:
      W.auth_reject(st, key, ue, k, u, eu, h2)
    case None{} False{}:
      W.auth_reject(st, key, ue, k, u, eu, h2)

def W.failure(+st: S.State, +key: U32, +ue: S.Ue, +av: Au.Av, +resynced: Bool, +supi: B.Digits(), +cause: U32, +auts: Maybe<&2, B.Bytes()>, +entropy: B.Bytes(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.failure(st, key, ue, av, resynced, supi, cause, auts, entropy)):
  W.failure_kind(st, key, ue, av, supi, auts, entropy, Bool.and(U32.is_eq(cause, 21), Bool.not(resynced)), k, u, eu, h2)

def W.identity_answer(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Mi.MobileId.Res(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.identity_answer(st, key, ue, entropy, r)):
  match r:
    case Fail{e}:
      W.reject(st, key, ue, 7, k, u, eu, h2)
    case Done{Mi.NoId{}}:
      W.reject(st, key, ue, 7, k, u, eu, h2)
    case Done{Mi.Suci{+suci}}:
      W.identified(st, key, ue, suci, entropy, k, u, eu, h2)
    case Done{Mi.Guti{plmn, region, amf, tmsi}}:
      W.reject(st, key, ue, 7, k, u, eu, h2)
    case Done{Mi.Imei{digits}}:
      W.reject(st, key, ue, 7, k, u, eu, h2)
    case Done{Mi.Imeisv{digits}}:
      W.reject(st, key, ue, 7, k, u, eu, h2)
    case Done{Mi.STmsi{amf, tmsi}}:
      W.reject(st, key, ue, 7, k, u, eu, h2)

def W.phase(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +p: S.Phase, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.phase(st, key, ue, entropy, mt, fields, opts, p)):
  match mt:
    case Mm.RegistrationRequest{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.RegistrationAccept{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.RegistrationComplete{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.RegistrationReject{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.DeregistrationRequestUe{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.DeregistrationAcceptUe{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.ConfigurationUpdateCommand{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.AuthenticationRequest{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.AuthenticationResponse{}:
      match p:
        case S.Created{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Identifying{guard}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Authenticating{guard, +av, resynced, +supi}:
          W.response(st, key, ue, av, supi, I.Opts.find(I.Iei.authentication_response_parameter(), opts), k, u, eu, h2)
        case S.SecurityMode{guard, old, k_amf}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.ContextSetup{guard, old, nh, response, complete}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Registered{old, nh, released}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Switching{guard, old, nh, released}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Handover{old, nh, source, leg}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Releasing{guard}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.AuthenticationReject{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.AuthenticationFailure{}:
      match p:
        case S.Created{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Identifying{guard}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Authenticating{guard, +av, +resynced, +supi}:
          W.failure(st, key, ue, av, resynced, supi, I.Fields.byte1(fields), I.Opts.find(I.Iei.authentication_failure_parameter(), opts), entropy, k, u, eu, h2)
        case S.SecurityMode{guard, old, k_amf}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.ContextSetup{guard, old, nh, response, complete}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Registered{old, nh, released}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Switching{guard, old, nh, released}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Handover{old, nh, source, leg}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Releasing{guard}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.IdentityRequest{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.IdentityResponse{}:
      match p:
        case S.Created{}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Identifying{guard}:
          W.identity_answer(st, key, ue, entropy, Mi.MobileId.read(I.Fields.lve1(fields)), k, u, eu, h2)
        case S.Authenticating{guard, av, resynced, supi}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.SecurityMode{guard, old, k_amf}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.ContextSetup{guard, old, nh, response, complete}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Registered{old, nh, released}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Switching{guard, old, nh, released}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Handover{old, nh, source, leg}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
        case S.Releasing{guard}:
          Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.SecurityModeCommand{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.SecurityModeComplete{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.SecurityModeReject{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.Status{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.UlNasTransport{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.DlNasTransport{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.ServiceRequest{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Mm.ServiceReject{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)

def W.plain(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Mm.Mm>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.plain(st, key, ue, entropy, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{Mm.Mm{mt, +fields, +opts}}:
      W.phase(st, key, ue, entropy, mt, fields, opts, S.Ue.phase(ue), k, u, eu, h2)

def W.sm_complete(+st: S.State, +key: U32, +ue: S.Ue, +k_amf: B.Bytes(), +ctx: Sec.Nas.Ctx, +count: Sec.Nas.Count, +opts: List<&2, I.Ie>, +cfg: Maybe<&2, S.Cfg>, +m: Maybe<&2, U32>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}, +hm: {Tk.free(S.State.ues(st), m) == True{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.sm_complete(st, key, ue, k_amf, ctx, count, opts, cfg, m)):
  match cfg m:
    case Some{+c} Some{+tmsi}:
      +reg = I.Bytes.or(I.Opts.find(I.Iei.nas_message_container(), opts), S.Ue.reg(ue))
      +accept = Gmm.Gmm.registration_accept(c, tmsi)
      +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.Ciphered{}, accept)
      +k_gnb = Kd.kdf.k_gnb(k_amf, Sec.Nas.Count.value(count))
      +ph : S.Phase = S.ContextSetup{S.Guard{0}, Sec.Nas.Protected.ctx(p), S.Nh.initial(k_amf, k_gnb), False{}, False{}}
      +ue2 = S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(ue, ph, accept), reg), tmsi)
      ht = Tmsi.apart(tmsi, S.State.ues(st), k, u, P.Bool.not_true(S.Ues.has_tmsi(tmsi, S.State.ues(st)), hm), eu)
      Tk.ok_also(k, u, S.State.ues(st), Gmm.Gmm.place(st, key, ue2), [N.Ics{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), c, N.Ue.caps(ue), k_gnb, Sec.Nas.Protected.msg(p)}, N.TimerStart{Some{key}, key, N.Ue.guard_ms()}], Tk.place(k, u, st, key, ue2, eu, Tk.k1(k, key, ue, u, h2), Tk.h_tmsi(ue, ph, accept, reg, tmsi, u, Tk.k2(k, key, ue, u, h2), ht)))
    case Some{c} None{}:
      W.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), k, u, eu, h2)
    case None{} Some{t}:
      W.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), k, u, eu, h2)
    case None{} None{}:
      W.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), k, u, eu, h2)

def W.setup_done(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +response: Bool, +complete: Bool, +both: Bool, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.setup_done(st, key, ue, guard, ctx, nh, response, complete, both)):
  match both:
    case True{}:
      Tk.ok_sp(k, u, S.State.ues(st), (S.Rephase{key, S.Registered{ctx, nh, None{}}}, [N.TimerCancel{key}, N.Note{F.Info{}, "5GMM: UE registered"}]), eu, Tk.sp_rephase(k, u, key, S.Registered{ctx, nh, None{}}, h1))
    case False{}:
      Tk.ok_sp(k, u, S.State.ues(st), (S.Rephase{key, S.ContextSetup{guard, ctx, nh, response, complete}}, []), eu, Tk.sp_rephase(k, u, key, S.ContextSetup{guard, ctx, nh, response, complete}, h1))

def W.setup_step(+st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +response: Bool, +complete: Bool, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.setup_step(st, key, ue, guard, ctx, nh, response, complete)):
  W.setup_done(st, key, ue, guard, ctx, nh, response, complete, Bool.and(response, complete), k, u, eu, h1)

def W.dereg_answer(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +switch_off: Bool, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.dereg_answer(st, key, ue, ctx, switch_off)):
  match switch_off:
    case True{}:
      W.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister()), k, u, eu, h2)
    case False{}:
      Tk.ok_prepend(k, u, S.State.ues(st), Gmm.Gmm.dl(key, ue, Sec.Nas.Protected.msg(Sec.Nas.protect(ctx, Sec.Ciphered{}, Gmm.Gmm.deregistration_accept()))), Gmm.Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister())), W.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister()), k, u, eu, h2))

def W.deregister(+st: S.State, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +kind: U32, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.deregister(st, key, ue, ctx, kind)):
  W.dereg_answer(st, key, ue, ctx, Bool.not(U32.is_eq(U32.and(kind, 8), 0)), k, u, eu, h2)

def W.sphase(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +count: Sec.Nas.Count, +ctx: Sec.Nas.Ctx, +mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +p: S.Phase, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.sphase(st, key, ue, entropy, count, ctx, mt, fields, opts, p)):
  match mt:
    case Mm.RegistrationRequest{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.RegistrationAccept{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.RegistrationComplete{}:
      match p:
        case S.Created{}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Identifying{guard}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Authenticating{guard, av, resynced, supi}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.SecurityMode{guard, old, k_amf}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.ContextSetup{+guard, old, nh, +response, complete}:
          W.setup_step(st, key, ue, guard, ctx, nh, response, True{}, k, u, eu, h1)
        case S.Registered{old, nh, released}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Switching{guard, old, nh, released}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Handover{old, nh, source, leg}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Releasing{guard}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.RegistrationReject{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.DeregistrationRequestUe{}:
      match p:
        case S.Created{}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Identifying{guard}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Authenticating{guard, av, resynced, supi}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.SecurityMode{guard, old, k_amf}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.ContextSetup{guard, old, nh, response, complete}:
          W.deregister(st, key, ue, ctx, I.Fields.byte1(fields), k, u, eu, h2)
        case S.Registered{old, nh, released}:
          W.deregister(st, key, ue, ctx, I.Fields.byte1(fields), k, u, eu, h2)
        case S.Switching{guard, old, nh, released}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Handover{old, nh, source, leg}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Releasing{guard}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.DeregistrationAcceptUe{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.ConfigurationUpdateCommand{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.AuthenticationRequest{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.AuthenticationResponse{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.AuthenticationReject{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.AuthenticationFailure{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.IdentityRequest{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.IdentityResponse{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.SecurityModeCommand{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.SecurityModeComplete{}:
      match p:
        case S.Created{}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Identifying{guard}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Authenticating{guard, av, resynced, supi}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.SecurityMode{guard, old, +k_amf}:
          W.sm_complete(st, key, ue, k_amf, ctx, count, opts, S.State.config(st), Gmm.Gmm.tmsi(S.State.ues(st), List.drop(&2, U32, entropy, 16n)), k, u, eu, h2, Tmsi.free(S.State.ues(st), List.drop(&2, U32, entropy, 16n)))
        case S.ContextSetup{guard, old, nh, response, complete}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Registered{old, nh, released}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Switching{guard, old, nh, released}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Handover{old, nh, source, leg}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Releasing{guard}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.SecurityModeReject{}:
      match p:
        case S.Created{}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Identifying{guard}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Authenticating{guard, av, resynced, supi}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.SecurityMode{guard, old, k_amf}:
          W.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()), k, u, eu, h2)
        case S.ContextSetup{guard, old, nh, response, complete}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Registered{old, nh, released}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Switching{guard, old, nh, released}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Handover{old, nh, source, leg}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Releasing{guard}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.Status{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.UlNasTransport{}:
      match p:
        case S.Created{}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Identifying{guard}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Authenticating{guard, av, resynced, supi}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.SecurityMode{guard, old, k_amf}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.ContextSetup{guard, old, nh, response, complete}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Registered{old, nh, released}:
          Tk.ok_sp(k, u, S.State.ues(st), Gsm.Gsm.ul_transport(st, key, ue, ctx, fields, opts, entropy), eu, Ws.ul_transport(st, key, ue, ctx, fields, opts, entropy, k, u, h1))
        case S.Switching{guard, old, nh, released}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Handover{old, nh, source, leg}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
        case S.Releasing{guard}:
          W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.DlNasTransport{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.ServiceRequest{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)
    case Mm.ServiceReject{}:
      W.verified(st, key, ue, ctx, "5GMM: message not expected in this phase", k, u, eu, h1)

def W.protected(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +count: Sec.Nas.Count, +ctx: Sec.Nas.Ctx, +r: Result<&2, &2, B.Err, Mm.Mm>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.protected(st, key, ue, entropy, count, ctx, r)):
  match r:
    case Fail{e}:
      W.verified(st, key, ue, ctx, "5GMM: message not understood", k, u, eu, h1)
    case Done{Mm.Mm{mt, +fields, +opts}}:
      W.sphase(st, key, ue, entropy, count, ctx, mt, fields, opts, S.Ue.phase(ue), k, u, eu, h1, h2)

def W.opened(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, Sec.Nas.Unprotected>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.opened(st, key, ue, entropy, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{Sec.Unprotected{prot, +plain, +count, +ctx}}:
      W.protected(st, key, ue, entropy, count, ctx, Mm.Mm.read(plain), k, u, eu, h1, h2)

def W.secured(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +nas: B.Bytes(), +m: Maybe<&2, Sec.Nas.Ctx>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}, +h2: {S.Row.conflicts(key, ue, k, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.secured(st, key, ue, entropy, nas, m)):
  match m:
    case None{}:
      W.plain(st, key, ue, entropy, Mm.Mm.read(nas), k, u, eu, h2)
    case Some{+ctx}:
      W.opened(st, key, ue, entropy, Sec.Nas.unprotect(ctx, nas), k, u, eu, h1, h2)

def W.mm(+st: S.State, +key: U32, +ue: S.Ue, +entropy: B.Bytes(), +nas: B.Bytes(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, pr: {U32.is_eq(k, key) == False{} : Bool} & {S.Ue.conflicts(ue, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.mm(st, key, ue, entropy, nas)):
  match pr:
    case (+h1, +h2):
      W.secured(st, key, ue, entropy, nas, S.Phase.ctx(S.Ue.phase(ue)), k, u, eu, h1, Tk.row(k, key, ue, u, h1, h2))

def W.uplink_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +nas: B.Bytes(), +entropy: B.Bytes(), +m: Maybe<&2, S.Ue>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.uplink_ue(st, assoc, key, nas, entropy, m)):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+ue}:
      W.mm(st, key, ue, entropy, nas, k, u, eu, Own.apart(st, assoc, key, ran, ue, k, u, eun, eu, ea, eo))


def W.uplink_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +nas: B.Bytes(), +entropy: B.Bytes(), +m: Maybe<&2, U32>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.uplink_key(st, assoc, ran, nas, entropy, m)):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+key}:
      W.uplink_ue(st, assoc, key, ran, nas, entropy, Gmm.Gmm.owner(st, assoc, key, ran), k, u, eu, eun, ea, {==})

def W.uplink(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +v: V.UplinkNASTransport.View, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.uplink(st, assoc, stream, entropy, v)):
  match v:
    case V.UplinkNASTransport.View{+amf_ue_ngap_id, +ran_ue_ngap_id, +nas_pdu, userlocationinformation}:
      W.uplink_key(st, assoc, ran_ue_ngap_id, nas_pdu, entropy, N.Ngap.ue_key(amf_ue_ngap_id), k, u, eu, eun, ea)

def W.uplink_of_view(+st: S.State, +assoc: U32, +stream: U32, +entropy: B.Bytes(), +r: Result<&2, &2, B.Err, V.UplinkNASTransport.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{+v}:
      W.uplink(st, assoc, stream, entropy, v, k, u, eu, eun, ea)

def W.setup_phase(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +h1: {U32.is_eq(k, key) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.setup_phase(st, key, ue, p)):
  match p:
    case S.Created{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case S.Identifying{guard}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case S.Authenticating{guard, av, resynced, supi}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case S.SecurityMode{guard, old, k_amf}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case S.ContextSetup{+guard, +ctx, nh, response, +complete}:
      W.setup_step(st, key, ue, guard, ctx, nh, True{}, complete, k, u, eu, h1)
    case S.Registered{old, nh, released}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case S.Switching{guard, old, nh, released}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case S.Handover{old, nh, source, leg}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case S.Releasing{guard}:
      Tk.kept_get(k, u, S.State.ues(st), eu)

def W.ics_owned(+st: S.State, +key: U32, +ue: S.Ue, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, pr: {U32.is_eq(k, key) == False{} : Bool} & {S.Ue.conflicts(ue, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.setup_phase(st, key, ue, S.Ue.phase(ue))):
  match pr:
    case (+h1, h2):
      W.setup_phase(st, key, ue, S.Ue.phase(ue), k, u, eu, h1)

def W.ics_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +m: Maybe<&2, S.Ue>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.ics_response_ue(st, assoc, key, m)):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+ue}:
      W.ics_owned(st, key, ue, k, u, eu, Own.apart(st, assoc, key, ran, ue, k, u, eun, eu, ea, eo))


def W.ics_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +m: Maybe<&2, U32>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.ics_response_key(st, assoc, ran, m)):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+key}:
      W.ics_ue(st, assoc, key, ran, Gmm.Gmm.owner(st, assoc, key, ran), k, u, eu, eun, ea, {==})

def W.ics(+st: S.State, +assoc: U32, +v: V.InitialContextSetupResponse.View, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.ics_response(st, assoc, v)):
  match v:
    case V.InitialContextSetupResponse.View{+amf_ue_ngap_id, +ran_ue_ngap_id, diagnostics}:
      W.ics_key(st, assoc, ran_ue_ngap_id, N.Ngap.ue_key(amf_ue_ngap_id), k, u, eu, eun, ea)

def W.ics_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.InitialContextSetupResponse.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.ics_response_of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{+v}:
      W.ics(st, assoc, v, k, u, eu, eun, ea)

def W.release_owned(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, pr: {U32.is_eq(k, key) == False{} : Bool} & {S.Ue.conflicts(ue, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.release(st, key, ue, cause)):
  match pr:
    case (+h1, +h2):
      W.release(st, key, ue, cause, k, u, eu, Tk.row(k, key, ue, u, h1, h2))

def W.release_request_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +cause: G.Cause, +m: Maybe<&2, S.Ue>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.release_request_ue(st, assoc, key, cause, m)):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+ue}:
      W.release_owned(st, key, ue, cause, k, u, eu, Own.apart(st, assoc, key, ran, ue, k, u, eun, eu, ea, eo))


def W.release_request_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +cause: G.Cause, +m: Maybe<&2, U32>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.release_request_key(st, assoc, ran, cause, m)):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+key}:
      W.release_request_ue(st, assoc, key, ran, cause, Gmm.Gmm.owner(st, assoc, key, ran), k, u, eu, eun, ea, {==})

def W.release_request(+st: S.State, +assoc: U32, +v: V.UEContextReleaseRequest.View, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.release_request(st, assoc, v)):
  match v:
    case V.UEContextReleaseRequest.View{+amf_ue_ngap_id, +ran_ue_ngap_id, pdusessionresourcelistcxtrelreq, +cause}:
      W.release_request_key(st, assoc, ran_ue_ngap_id, cause, N.Ngap.ue_key(amf_ue_ngap_id), k, u, eu, eun, ea)

def W.release_request_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.release_request_of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{+v}:
      W.release_request(st, assoc, v, k, u, eu, eun, ea)

def W.forget(+st: S.State, +key: U32, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +ue: S.Ue, +more: List<&2, N.Act>, pr: {U32.is_eq(k, key) == False{} : Bool} & {S.Ue.conflicts(ue, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), N.Out.also(Gmm.Gmm.forget(st, key), more)):
  match pr:
    case (+h1, h2):
      Tk.ok_also(k, u, S.State.ues(st), Gmm.Gmm.forget(st, key), more, Tk.ok_sp(k, u, S.State.ues(st), Gmm.Gmm.forget(st, key), eu, Tk.sp_join(k, u, Up.N4.deletions(S.Sessions.of_ue(key, S.State.sessions(st)), S.State.pfcp_seq(st)), (S.Del{key}, []), Tk.sp_deletions(k, u, S.Sessions.of_ue(key, S.State.sessions(st)), S.State.pfcp_seq(st)), Tk.sp_del(k, u, key, h1))))

def W.release_complete_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +m: Maybe<&2, S.Ue>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.release_complete_ue(st, assoc, key, m, S.Ue.released(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran))):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+ue}:
      W.forget(st, key, k, u, eu, ue, List.append(&2, N.Act, N.Guard.cancel(key, S.Ue.guard(ue)), List.append(&2, N.Act, Ho.Ho.leg_drop(key, S.Ue.phase(ue), N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified())), [N.Note{F.Info{}, "NGAP: UE context released"}])), Own.apart(st, assoc, key, ran, ue, k, u, eun, eu, ea, eo))


def W.release_complete_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +m: Maybe<&2, U32>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.release_complete_key(st, assoc, ran, m)):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+key}:
      W.release_complete_ue(st, assoc, key, ran, Gmm.Gmm.owner(st, assoc, key, ran), k, u, eu, eun, ea, {==})

def W.release_complete(+st: S.State, +assoc: U32, +v: V.UEContextReleaseComplete.View, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.release_complete(st, assoc, v)):
  match v:
    case V.UEContextReleaseComplete.View{+amf_ue_ngap_id, +ran_ue_ngap_id, userlocationinformation, pdusessionresourcelistcxtrelcpl, diagnostics}:
      W.release_complete_key(st, assoc, ran_ue_ngap_id, N.Ngap.ue_key(amf_ue_ngap_id), k, u, eu, eun, ea)

def W.release_complete_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gmm.Gmm.release_complete_of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{+v}:
      W.release_complete(st, assoc, v, k, u, eu, eun, ea)

def W.results_owned(+st: S.State, +key: U32, +ue: S.Ue, +oks: G.PDUSessionResourceSetupListSURes(), +fails: G.PDUSessionResourceFailedToSetupListSURes(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, pr: {U32.is_eq(k, key) == False{} : Bool} & {S.Ue.conflicts(ue, u) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gsm.Gsm.results(st, key, ue, oks, fails)):
  match pr:
    case (+h1, h2):
      Tk.ok_sp(k, u, S.State.ues(st), Gsm.Gsm.results(st, key, ue, oks, fails), eu, Ws.results(st, key, ue, oks, fails, k, u, h1))

def W.setup_response_ue(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +oks: G.PDUSessionResourceSetupListSURes(), +fails: G.PDUSessionResourceFailedToSetupListSURes(), +m: Maybe<&2, S.Ue>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == m : Maybe<&2, S.Ue>}) -> Tk.Ok(k, u, S.State.ues(st), Gsm.Gsm.setup_response_ue(st, assoc, key, oks, fails, m)):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+ue}:
      W.results_owned(st, key, ue, oks, fails, k, u, eu, Own.apart(st, assoc, key, ran, ue, k, u, eun, eu, ea, eo))


def W.setup_response_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +oks: G.PDUSessionResourceSetupListSURes(), +fails: G.PDUSessionResourceFailedToSetupListSURes(), +m: Maybe<&2, U32>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gsm.Gsm.setup_response_key(st, assoc, ran, oks, fails, m)):
  match m:
    case None{}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Some{+key}:
      W.setup_response_ue(st, assoc, key, ran, oks, fails, N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran), k, u, eu, eun, ea, {==})

def W.setup_response(+st: S.State, +assoc: U32, +v: V.PDUSessionResourceSetupResponse.View, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gsm.Gsm.setup_response(st, assoc, v)):
  match v:
    case V.PDUSessionResourceSetupResponse.View{+amf_ue_ngap_id, +ran_ue_ngap_id, +oks, +fails, diagnostics, uli}:
      W.setup_response_key(st, assoc, ran_ue_ngap_id, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), Gsm.Gsm.list_or(G.PDUSessionResourceFailedToSetupItemSURes, fails), N.Ngap.ue_key(amf_ue_ngap_id), k, u, eu, eun, ea)

def W.setup_response_of_view(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Gsm.Gsm.setup_response_of_view(st, assoc, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{+v}:
      W.setup_response(st, assoc, v, k, u, eu, eun, ea)

# The router

# Path Switch
# -----------
# The target moves the context it names, under its own key; the context
# keeps its SUPI, verified by 5G-AKA, with its security context, and another
# context conflicts with it only on the target. Its sessions' changes touch
# no context.

def W.ps_session_ues(+skey: U32, +s: S.Session, +seq: U32, +t: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +x: Tb.Table(S.Ue)) -> {Tk.ues(N.Out.tx(Sw.Sw.session(skey, s, seq, t)), x) == x : Tb.Table(S.Ue)}:
  match t:
    case None{}:
      Tk.ues_deletions([(skey, s)], seq, x)
    case Some{(teid, addr)}:
      {==}

def W.ps_sessions_ues(+ts: List<&2, S.Tunnel>, +rows: Tb.Table(S.Session), +seq: U32, +x: Tb.Table(S.Ue)) -> {Tk.ues(N.Out.tx(Sw.Sw.sessions(ts, rows, seq)), x) == x : Tb.Table(S.Ue)}:
  match rows:
    case Nil{}:
      {==}
    case (+skey, +s) <> +more:
      +o = Sw.Sw.session(skey, s, seq, Sw.Sw.tunnel_for(ts, s))
      +a = N.Out.join((S.BumpSeq{1}, []), o)
      +b = Sw.Sw.sessions(ts, more, U32.add(seq, 1))
      ej = Equal.sym(S.Tx, N.Out.tx(N.Out.join(a, b)), S.Both{N.Out.tx(a), N.Out.tx(b)}, PW.Out.tx_join(a, b))
      %ej : {Tk.ues(_, x) == x : Tb.Table(S.Ue)}
      ea2 = Equal.sym(S.Tx, N.Out.tx(a), S.Both{S.BumpSeq{1}, N.Out.tx(o)}, PW.Out.tx_join((S.BumpSeq{1}, []), o))
      %ea2 : {Tk.ues(N.Out.tx(b), Tk.ues(_, x)) == x : Tb.Table(S.Ue)}
      es = Equal.sym(Tb.Table(S.Ue), Tk.ues(N.Out.tx(o), x), x, W.ps_session_ues(skey, s, seq, Sw.Sw.tunnel_for(ts, s), x))
      %es : {Tk.ues(N.Out.tx(b), _) == x : Tb.Table(S.Ue)}
      W.ps_sessions_ues(ts, more, U32.add(seq, 1), x)

# The context moved to association a conflicts with no context of another one
# that it did not conflict with before.
def W.c_moved(+ue: S.Ue, +a: U32, +r: B.Bytes(), +s: U32, +p: S.Phase, +u: S.Ue, +h2: {S.Ue.conflicts(ue, u) == False{} : Bool}, +ha: {U32.is_eq(a, S.Ue.assoc(u)) == False{} : Bool}) -> {S.Ue.conflicts(S.Ue.moved(ue, a, r, s, p), u) == False{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      +x = S.Maybe.same_bytes(supi, S.Ue.supi(u))
      +y = S.Maybe.same_u32(tmsi, S.Ue.tmsi(u))
      +z0 = Bool.and(U32.is_eq(assoc, S.Ue.assoc(u)), B.bytes_eq(ran_id, S.Ue.ran_id(u)))
      ex = P.Bool.or_false_l(x, Bool.or(y, z0), h2)
      ey = P.Bool.or_false_l(y, z0, P.Bool.or_false_r(x, Bool.or(y, z0), h2))
      sh = Equal.sym(Bool, U32.is_eq(a, S.Ue.assoc(u)), False{}, ha)
      ez : {Bool.and(U32.is_eq(a, S.Ue.assoc(u)), B.bytes_eq(r, S.Ue.ran_id(u))) == False{} : Bool} = (%sh : {Bool.and(_, B.bytes_eq(r, S.Ue.ran_id(u))) == False{} : Bool}; {==})
      Tk.or3(x, y, Bool.and(U32.is_eq(a, S.Ue.assoc(u)), B.bytes_eq(r, S.Ue.ran_id(u))), ex, ey, ez)

# A moved context keeps its verified SUPI and holds a security context.
def W.secures_moved(+ue: S.Ue, +a: U32, +r: B.Bytes(), +s: U32, +p: S.Phase, +sp: B.Digits(), +esupi: {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>}, +ec: {S.Phase.secured(p) == True{} : Bool}) -> {S.Ue.secures(S.Ue.moved(ue, a, r, s, p), S.Ue.supi(ue)) == True{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, +supi, tmsi, reg, ngksi, phase, last_dl}:
      e = Equal.sym(Maybe<&2, B.Digits()>, supi, Some{sp}, esupi)
      %e : {Bool.and(S.Maybe.same_bytes(_, _), S.Phase.secured(p)) == True{} : Bool}
      rf = Equal.sym(Bool, B.bytes_eq(sp, sp), True{}, P.Bytes.eq_refl(sp))
      %rf : {Bool.and(_, S.Phase.secured(p)) == True{} : Bool}
      ec

# A context moved to association a, in a phase with a security context, under
# the key of a context of a unique table: the row under k, of another
# association, stays, or k is that key and the moved context secures its SUPI.
def W.ps_put_case(+k: U32, +u: S.Ue, +key: U32, +ue: S.Ue, +a: U32, +r: B.Bytes(), +s: U32, +p: S.Phase, +sp: B.Digits(), +ues: Tb.Table(S.Ue), +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(ues) == True{} : Bool}, +ha: {U32.is_eq(a, S.Ue.assoc(u)) == False{} : Bool}, +em: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>}, +esupi: {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>}, +ec: {S.Phase.secured(p) == True{} : Bool}, +x: Bool, +ex: {U32.is_eq(k, key) == x : Bool}) -> Tk.Kept(k, u, S.Ues.put(key, S.Ue.moved(ue, a, r, s, p), ues)):
  match x:
    case False{}:
      +v = S.Ue.moved(ue, a, r, s, p)
      Tk.put(k, u, key, v, ues, eu, ex, Tk.h_apart(v, u, W.c_moved(ue, a, r, s, p, u, Uniq.apart(ues, key, k, ue, u, eun, em, eu, ex), ha)))
    case True{}:
      +v = S.Ue.moved(ue, a, r, s, p)
      gk = Own.at(ues, k, key, ue, Equal.sym(U32, k, key, P.U32.eq_of_is_eq(k, key, ex)), em)
      eue = P.Some.inj(S.Ue, ue, u, Equal.trans(Maybe<&2, S.Ue>, Some{ue}, Tb.Table.get(S.Ue, k, ues), Some{u}, Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, ues), Some{ue}, gk), eu))
      sec : {S.Ue.secures(v, S.Ue.supi(u)) == True{} : Bool} = (%eue : {S.Ue.secures(v, S.Ue.supi(_)) == True{} : Bool}; W.secures_moved(ue, a, r, s, p, sp, esupi, ec))
      Inr{P.Bool.or_l(S.Ue.secures(v, S.Ue.supi(u)), S.Ues.secured(S.Ue.supi(u), S.Ues.sift(S.Clear{key, v}, ues)), sec)}

def W.ps_go(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +sp: B.Digits(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +em: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +esupi: {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>}) -> Tk.Ok(k, u, S.State.ues(st), Ps.Ps.go(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, S.Sessions.of_ue(key, S.State.sessions(st)), True{})):
  +rows = S.Sessions.of_ue(key, S.State.sessions(st))
  +g : S.Guard = S.Guard{0}
  +n = S.Nh.next(nh)
  +rel = Sw.Sw.released(ts, rows)
  +v = S.Ue.moved(ue, assoc, ran, stream, S.Switching{g, ctx, n, rel})
  +a = Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st))
  +b : N.GOut() = (S.Put{key, v}, [])
  +ues = S.State.ues(st)
  ha = Equal.trans(Bool, U32.is_eq(assoc, S.Ue.assoc(u)), U32.is_eq(S.Ue.assoc(u), assoc), False{}, P.U32.sym(assoc, S.Ue.assoc(u)), ea)
  es = Equal.sym(Tb.Table(S.Ue), Tk.ues(N.Out.tx(a), ues), ues, W.ps_sessions_ues(ts, rows, S.State.pfcp_seq(st), ues))
  h : Tk.Kept(k, u, Tk.ues(N.Out.tx(b), Tk.ues(N.Out.tx(a), ues))) = (%es : Tk.Kept(k, u, S.Ues.put(key, v, _)); W.ps_put_case(k, u, key, ue, assoc, ran, stream, S.Switching{g, ctx, n, rel}, sp, ues, eu, eun, ha, em, esupi, {==}, U32.is_eq(k, key), {==}))
  Tk.ok_also(k, u, ues, N.Out.join(a, b), [N.TimerStart{Some{key}, key, Ps.Ps.guard_ms()}, N.Note{F.Info{}, "NGAP: Path Switch Request; the UE moved, its PDU sessions being switched"}], Tk.ok_join(k, u, ues, a, b, h))

def W.ps_of_view(+st: S.State, +assoc: U32, +stream: U32, +r: Result<&2, &2, B.Err, V.PathSwitchRequest.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Ps.Ps.of_view(st, assoc, stream, r)):
  match r:
    case Fail{e}:
      Tk.kept_get(k, u, S.State.ues(st), eu)
    case Done{V.PathSwitchRequest.View{+ran, +amf, uli, caps, +items, failed, rrc}}:
      +ts = Sw.Sw.path_tunnels(items)
      +m = Ps.Ps.named(st, amf)
      +h = PW.Pw.claim(o => Tk.Ok(k, u, S.State.ues(st), o), st, assoc, stream, amf, ran, items, ts, cause => Tk.kept_get(k, u, S.State.ues(st), eu), +key => +ue => +ctx => +nh => +sp => ek => +eg => +es => rel => ep => W.ps_go(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, sp, k, u, eu, eun, ea, eg, es))
      Tk.ok_also(k, u, S.State.ues(st), Ps.Ps.claim(st, assoc, stream, amf, ran, items, ts, m), Ps.Ps.caps_note(caps, m), h)

# N2 handover
# -----------
# The source speaks for a context it owns, which is not u's; the target
# rephases or moves the context with a handover pending to it, keeping its
# verified SUPI and its security context.

def W.ho_sp(+k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +o: N.GOut(), +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +es: {Tk.sp(k, u, o) == True{} : Bool}) -> Tk.Ok(k, u, ues, o):
  Tk.ok_sp(k, u, ues, o, eu, es)

def W.ho_h1(+k: U32, +key: U32, +ue: S.Ue, +u: S.Ue, pr: {U32.is_eq(k, key) == False{} : Bool} & {S.Ue.conflicts(ue, u) == False{} : Bool}) -> {U32.is_eq(k, key) == False{} : Bool}:
  match pr:
    case (+h1, h2):
      h1

# The context the source owns is not u's.

# The context the source owns is not u's.
def W.ho_owned(+st: S.State, +assoc: U32, +key: U32, +ran: B.Bytes(), +ue: S.Ue, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> {U32.is_eq(k, key) == False{} : Bool}:
  W.ho_h1(k, key, ue, u, Own.apart(st, assoc, key, ran, ue, k, u, eun, eu, ea, eo))

# A context of a unique table, with its SUPI verified, rephased into a phase
# with a security context still secures its SUPI.
def W.secures_self(+ue: S.Ue, +p: S.Phase, +ep: {Tb.Table.present(B.Digits(), S.Ue.supi(ue)) == True{} : Bool}, +ec: {S.Phase.secured(p) == True{} : Bool}) -> {S.Ue.secures(S.Ue.with_phase(ue, p), S.Ue.supi(ue)) == True{} : Bool}:
  match ue:
    case S.Ue{assoc, ran_id, stream, +supi, tmsi, reg, ngksi, phase, last_dl}:
      match supi:
        case None{}:
          Empty.absurd({S.Ue.secures(S.Ue.with_phase(S.Ue{assoc, ran_id, stream, None{}, tmsi, reg, ngksi, phase, last_dl}, p), None{}) == True{} : Bool}, P.Refute.bool(ep))
        case Some{+sp}:
          rf = Equal.sym(Bool, B.bytes_eq(sp, sp), True{}, P.Bytes.eq_refl(sp))
          %rf : {Bool.and(_, S.Phase.secured(p)) == True{} : Bool}
          ec

def W.sec_row(+s: Maybe<&2, B.Digits()>, +key: U32, +w: S.Ue, +k0: U32, +x: S.Ue, +more: Tb.Table(S.Ue), +hk: Bool, +ehk: {U32.is_eq(k0, key) == hk : Bool}, +eg: {Tb.Table.hit(S.Ue, x, Tb.Table.get(S.Ue, key, more), hk) == Some{w} : Maybe<&2, S.Ue>}, +es: {S.Ue.secures(w, s) == True{} : Bool}, ih: {Tb.Table.get(S.Ue, key, more) == Some{w} : Maybe<&2, S.Ue>} -> {S.Ues.secured(s, more) == True{} : Bool}) -> {Bool.or(S.Ue.secures(x, s), S.Ues.secured(s, more)) == True{} : Bool}:
  match hk:
    case True{}:
      exw = Equal.sym(S.Ue, x, w, P.Some.inj(S.Ue, x, w, eg))
      %exw : {Bool.or(S.Ue.secures(_, s), S.Ues.secured(s, more)) == True{} : Bool}
      P.Bool.or_l(S.Ue.secures(w, s), S.Ues.secured(s, more), es)
    case False{}:
      P.Bool.or_r(S.Ue.secures(x, s), S.Ues.secured(s, more), ih(eg))

# A context under some key that secures s makes s secured.

# A context under some key that secures s makes s secured.
def W.sec_get(+s: Maybe<&2, B.Digits()>, +key: U32, +w: S.Ue, +x: Tb.Table(S.Ue), +eg: {Tb.Table.get(S.Ue, key, x) == Some{w} : Maybe<&2, S.Ue>}, +es: {S.Ue.secures(w, s) == True{} : Bool}) -> {S.Ues.secured(s, x) == True{} : Bool}:
  match x:
    case Nil{}:
      Empty.absurd({S.Ues.secured(s, []) == True{} : Bool}, P.Refute.none_some(S.Ue, w, eg))
    case (+k0, +v) <> +more:
      W.sec_row(s, key, w, k0, v, more, U32.is_eq(k0, key), {==}, eg, es, e => W.sec_get(s, key, w, more, e, es))

# The row under k equals the context under key when k is key.

# The row under k equals the context under key when k is key.
def W.same_row(+ues: Tb.Table(S.Ue), +k: U32, +key: U32, +ue: S.Ue, +u: S.Ue, +ex: {U32.is_eq(k, key) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>}, +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}) -> {ue == u : S.Ue}:
  gk = Own.at(ues, k, key, ue, Equal.sym(U32, k, key, P.U32.eq_of_is_eq(k, key, ex)), eg)
  P.Some.inj(S.Ue, ue, u, Equal.trans(Maybe<&2, S.Ue>, Some{ue}, Tb.Table.get(S.Ue, k, ues), Some{u}, Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, ues), Some{ue}, gk), eu))

def W.ho_rephase_case(+ues: Tb.Table(S.Ue), +key: U32, +ue: S.Ue, +p: S.Phase, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, +eg: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {Tb.Table.present(B.Digits(), S.Ue.supi(ue)) == True{} : Bool}, +ec: {S.Phase.secured(p) == True{} : Bool}, +x: Bool, +ex: {U32.is_eq(k, key) == x : Bool}) -> Tk.Kept(k, u, S.Ues.rephase(key, p, ues)):
  match x:
    case False{}:
      Inl{Rephase.get(key, p, k, u, ues, eu, ex)}
    case True{}:
      eue = W.same_row(ues, k, key, ue, u, ex, eg, eu)
      sec : {S.Ue.secures(S.Ue.with_phase(ue, p), S.Ue.supi(u)) == True{} : Bool} = (%eue : {S.Ue.secures(S.Ue.with_phase(ue, p), S.Ue.supi(_)) == True{} : Bool}; W.secures_self(ue, p, ep, ec))
      Inr{W.sec_get(S.Ue.supi(u), key, S.Ue.with_phase(ue, p), S.Ues.rephase(key, p, ues), Rephase.self(key, p, ue, ues, eg), sec)}

# The context a target's answer is for: under its key, with its SUPI verified.

def W.ho_found(+ues: Tb.Table(S.Ue), +key: U32, +ue: S.Ue, +assoc: U32, pr: {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>} & {Ho.Ho.aimed(ue, assoc) == True{} : Bool}) -> {Tb.Table.get(S.Ue, key, ues) == Some{ue} : Maybe<&2, S.Ue>} & {Tb.Table.present(B.Digits(), S.Ue.supi(ue)) == True{} : Bool}:
  match pr:
    case (+eg, +ea):
      (eg, PW.Walk.aimed_supi(ue, assoc, ea))

def W.ho_target_rephase(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +acts: List<&2, N.Act>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, pr: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>} & {Tb.Table.present(B.Digits(), S.Ue.supi(ue)) == True{} : Bool}, +ec: {S.Phase.secured(p) == True{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), (S.Rephase{key, p}, acts)):
  match pr:
    case (+eg, +ep):
      W.ho_rephase_case(S.State.ues(st), key, ue, p, k, u, eu, eg, ep, ec, U32.is_eq(k, key), {==})

def W.ho_required(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverRequired.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Ho.Ho.required_of_view(st, assoc, r)):
  PW.Hw.required(o => Tk.Ok(k, u, S.State.ues(st), o), st, assoc, r, Tk.kept_get(k, u, S.State.ues(st), eu), Tk.kept_get(k, u, S.State.ues(st), eu), amf => ran => key => ue => c => ek => eo => Tk.kept_get(k, u, S.State.ues(st), eu), amf => +ran => +key => +ue => ctx => nh => t => cfg => cause => container => i => more => ek => +eo => ne => rel => eph => W.ho_sp(k, u, S.State.ues(st), Ho.Ho.prepare(key, ue, ctx, nh, t, cfg, cause, container, i <> more), eu, Tk.sp_rephase(k, u, key, S.Created{}, W.ho_owned(st, assoc, key, ran, ue, k, u, eu, eun, ea, eo))))

def W.ho_cancel(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverCancel.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Ho.Ho.cancel_of_view(st, assoc, r)):
  PW.Hw.cancel(o => Tk.Ok(k, u, S.State.ues(st), o), st, assoc, r, Tk.kept_get(k, u, S.State.ues(st), eu), Tk.kept_get(k, u, S.State.ues(st), eu), amf => ran => key => ue => ek => eo => en => Tk.kept_get(k, u, S.State.ues(st), eu), amf => +ran => +key => +ue => +ctx => +nh => +source => +leg => ek => +eo => eph => W.ho_sp(k, u, S.State.ues(st), Ho.Ho.cancel_phase(key, ue, S.Handover{ctx, nh, source, leg}), eu, Tk.sp_rephase(k, u, key, S.Created{}, W.ho_owned(st, assoc, key, ran, ue, k, u, eu, eun, ea, eo))))

def W.ho_status(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}) -> Tk.Ok(k, u, S.State.ues(st), Ho.Ho.status_of_view(st, assoc, r)):
  PW.Hw.status(o => Tk.Ok(k, u, S.State.ues(st), o), st, assoc, r, Tk.kept_get(k, u, S.State.ues(st), eu), Tk.kept_get(k, u, S.State.ues(st), eu), Tk.kept_get(k, u, S.State.ues(st), eu), amf => ran => container => key => ue => t => r2 => s => ek => eo => Tk.kept_get(k, u, S.State.ues(st), eu))

# The target's answers
# --------------------

def W.ho_ack(+st: S.State, +assoc: U32, +stream: U32, +r: Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}) -> Tk.Ok(k, u, S.State.ues(st), Ho.Ho.ack_of_view(st, assoc, stream, r)):
  PW.Hw.ack(o => Tk.Ok(k, u, S.State.ues(st), o), st, assoc, stream, r, Tk.kept_get(k, u, S.State.ues(st), eu), Tk.kept_get(k, u, S.State.ues(st), eu), amf => +ran => +admitted => container => +key => +ue => +ctx => +nh => source => t => ek => +ep => eph => W.ho_target_rephase(st, key, ue, S.Handover{ctx, nh, S.Ue.assoc(ue), S.Acked{assoc, ran, stream, Sw.Sw.admitted(admitted)}}, [], k, u, eu, W.ho_found(S.State.ues(st), key, ue, assoc, PW.Walk.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ue, ep)), {==}))

def W.ho_failure(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverFailure.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}) -> Tk.Ok(k, u, S.State.ues(st), Ho.Ho.failure_of_view(st, assoc, r)):
  PW.Hw.failure(o => Tk.Ok(k, u, S.State.ues(st), o), st, assoc, r, Tk.kept_get(k, u, S.State.ues(st), eu), Tk.kept_get(k, u, S.State.ues(st), eu), amf => cause => +key => +ue => +ctx => +nh => source => t => ek => +ep => eph => W.ho_target_rephase(st, key, ue, S.Registered{ctx, nh, None{}}, [], k, u, eu, W.ho_found(S.State.ues(st), key, ue, assoc, PW.Walk.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ue, ep)), {==}))

# Handover Notify moves the context under its key, like Path Switch.
def W.ho_complete(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +sp: B.Digits(), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +esupi: {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>}) -> Tk.Ok(k, u, S.State.ues(st), Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, True{})):
  +rows = S.Sessions.of_ue(key, S.State.sessions(st))
  +told = Gsm.Gsm.releases(key, assoc, s, r, Sw.Sw.released(ts, rows), ctx)
  +p : S.Phase = S.Registered{Gsm.Gsm.Told.ctx(told), nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}}
  +v = S.Ue.moved(ue, assoc, r, s, p)
  +a = Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st))
  +b : N.GOut() = (S.Put{key, v}, [])
  +ues = S.State.ues(st)
  ha = Equal.trans(Bool, U32.is_eq(assoc, S.Ue.assoc(u)), U32.is_eq(S.Ue.assoc(u), assoc), False{}, P.U32.sym(assoc, S.Ue.assoc(u)), ea)
  es = Equal.sym(Tb.Table(S.Ue), Tk.ues(N.Out.tx(a), ues), ues, W.ps_sessions_ues(ts, rows, S.State.pfcp_seq(st), ues))
  h : Tk.Kept(k, u, Tk.ues(N.Out.tx(b), Tk.ues(N.Out.tx(a), ues))) = (%es : Tk.Kept(k, u, S.Ues.put(key, v, _)); W.ps_put_case(k, u, key, ue, assoc, r, s, p, sp, ues, eu, eun, ha, eg, esupi, {==}, U32.is_eq(k, key), {==}))
  Tk.ok_also(k, u, ues, N.Out.join(a, b), N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), Ho.Ho.radio(G.CauseRadioNetwork.successful_handover())} <> List.append(&2, N.Act, Gsm.Gsm.Told.acts(told), [N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Handover Notify; the UE moved to the target"}]), Tk.ok_join(k, u, ues, a, b, h))

def W.ho_notify(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverNotify.View>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Ho.Ho.notify_of_view(st, assoc, r)):
  PW.Hw.notify(o => Tk.Ok(k, u, S.State.ues(st), o), st, assoc, r, Tk.kept_get(k, u, S.State.ues(st), eu), Tk.kept_get(k, u, S.State.ues(st), eu), amf => ran => +key => +ue => +ctx => +nh => source => t => +r2 => +s => +ts => +sp => ek => +ep => eph => +es => W.ho_complete(st, assoc, key, ue, ctx, nh, r2, s, ts, sp, k, u, eu, eun, ea, PW.Walk.first({Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, {Ho.Ho.aimed(ue, assoc) == True{} : Bool}, PW.Walk.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ue, ep)), es))

def W.ho_route(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), Ho.Ho.route(st, assoc, stream, kind, code, ies)):
  PW.Walk.ho(o => Tk.Ok(k, u, S.State.ues(st), o), st, assoc, stream, kind, code, ies, Tk.kept_get(k, u, S.State.ues(st), eu), +r => W.ho_required(st, assoc, r, k, u, eu, eun, ea), +r => W.ho_ack(st, assoc, stream, r, k, u, eu), +r => W.ho_failure(st, assoc, r, k, u, eu), +r => W.ho_notify(st, assoc, r, k, u, eu, eun, ea), +r => W.ho_cancel(st, assoc, r, k, u, eu, eun, ea), +r => W.ho_status(st, assoc, r, k, u, eu))

def W.d2(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), +b: Bool, +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +eun: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Ok(k, u, S.State.ues(st), R.Route.d2(st, assoc, stream, kind, code, ies, entropy, b)):
  PW.Walk.d2(o => Tk.Ok(k, u, S.State.ues(st), o), st, assoc, stream, kind, code, ies, entropy, b, W.ho_route(st, assoc, stream, kind, code, ies, k, u, eu, eun, ea), +r => W.initial_of_view(st, assoc, stream, entropy, r, k, u, eu, eun, ea), +r => W.uplink_of_view(st, assoc, stream, entropy, r, k, u, eu, eun, ea), +r => W.ics_of_view(st, assoc, r, k, u, eu, eun, ea), +r => W.release_request_of_view(st, assoc, r, k, u, eu, eun, ea), +r => W.release_complete_of_view(st, assoc, r, k, u, eu, eun, ea), +r => W.setup_response_of_view(st, assoc, r, k, u, eu, eun, ea), +r => W.ps_of_view(st, assoc, stream, r, k, u, eu, eun, ea), +r => Tk.kept_get(k, u, S.State.ues(st), eu))

def Tk.removed(+k: U32, +u: S.Ue, +x: Tb.Table(S.Ue), eg: {Tb.Table.get(S.Ue, k, x) == Some{u} : Maybe<&2, S.Ue>} -> Empty, w: Tk.Kept(k, u, x)) -> {S.Ues.secured(S.Ue.supi(u), x) == True{} : Bool}:
  match w:
    case Inl{e}:
      Empty.absurd({S.Ues.secured(S.Ue.supi(u), x) == True{} : Bool}, eg(e))
    case Inr{e}:
      e

def Tk.out(+st: S.State, +o: N.GOut(), +k: U32, +u: S.Ue, w: Tk.Ok(k, u, S.State.ues(st), o)) -> Tk.Kept(k, u, S.State.ues(K.Kernel.state(N.Step.of(st, o)))):
  se = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, o))), Tk.ues(N.Out.tx(o), S.State.ues(st)), Tk.render(st, o))
  (%se : Tk.Kept(k, u, _); w)

# NG Setup
# --------
# NG Setup re-initialises its association's contexts (R.Route.reset): the N2
# handovers it takes part in end, then its contexts go. Ending one rephases
# another association's context only when its handover is aimed at this one
# (Ho.Ho.aimed), so with its SUPI verified, into a phase holding a security
# context; a key names one row of a unique table, so that row is rephased
# once, keeps its owner, and survives the sieve.

# The row m is a context of u's owner securing u's SUPI.
def Tk.held(+u: S.Ue, m: Maybe<&2, S.Ue>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+w}:
      Bool.and(U32.is_eq(S.Ue.assoc(w), S.Ue.assoc(u)), S.Ue.secures(w, S.Ue.supi(u)))

def Tk.Down(+k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue)) -> Data:
  Either<&2, &2, {Tb.Table.get(S.Ue, k, ues) == Some{u} : Maybe<&2, S.Ue>}, {Tk.held(u, Tb.Table.get(S.Ue, k, ues)) == True{} : Bool}>

def Tk.down_join(+k: U32, +u: S.Ue, +ues: Tb.Table(S.Ue), +a: N.GOut(), +b: N.GOut(), +h: Tk.Down(k, u, Tk.ues(N.Out.tx(b), Tk.ues(N.Out.tx(a), ues)))) -> Tk.Down(k, u, Tk.ues(N.Out.tx(N.Out.join(a, b)), ues)):
  match a:
    case (ta, aa):
      match b:
        case (tb, ab):
          h

def Tk.sp_leg(+k1: U32, +u1: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +t: Bool, +s: Bool, +k: U32, +w: S.Ue, +ne: {U32.is_eq(k, k1) == False{} : Bool}) -> {Tk.sp(k, w, Ho.Ho.down_leg(k1, u1, ctx, nh, leg, t, s)) == True{} : Bool}:
  match t s:
    case True{} _:
      Tk.sp_rephase(k, w, k1, S.Registered{ctx, nh, None{}}, ne)
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def Tk.sp_row(+assoc: U32, +k1: U32, +u1: S.Ue, +p: S.Phase, +k: U32, +w: S.Ue, +ne: {U32.is_eq(k, k1) == False{} : Bool}) -> {Tk.sp(k, w, Ho.Ho.down_row(assoc, k1, u1, p)) == True{} : Bool}:
  match p:
    case S.Handover{+ctx, +nh, source, +leg}:
      Tk.sp_leg(k1, u1, ctx, nh, leg, Ho.Ho.aimed(u1, assoc), U32.is_eq(S.Ue.assoc(u1), assoc), k, w, ne)
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

# The handovers of rows clear of key k spare its row.
def Tk.sp_downs(+assoc: U32, +rows: Tb.Table(S.Ue), +k: U32, +u: S.Ue, +w: S.Ue, +hc: {S.Ues.clear(k, u, rows) == True{} : Bool}) -> {Tk.sp(k, w, Ho.Ho.downs(assoc, rows)) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k1, +u1) <> +more:
      +c = S.Row.conflicts(k, u, k1, u1)
      +n1 = P.Bool.or_false_l(U32.is_eq(k1, k), S.Ue.conflicts(u, u1), P.Bool.not_true(c, P.Bool.and_true_l(Bool.not(c), S.Ues.clear(k, u, more), hc)))
      +ne = Equal.trans(Bool, U32.is_eq(k, k1), U32.is_eq(k1, k), False{}, P.U32.sym(k, k1), n1)
      Tk.sp_join(k, w, Ho.Ho.down_row(assoc, k1, u1, S.Ue.phase(u1)), Ho.Ho.downs(assoc, more), Tk.sp_row(assoc, k1, u1, S.Ue.phase(u1), k, w, ne), Tk.sp_downs(assoc, more, k, u, w, P.Bool.and_true_r(Bool.not(c), S.Ues.clear(k, u, more), hc)))

def Tk.held_spared(+k: U32, +u: S.Ue, +tx: S.Tx, +x: Tb.Table(S.Ue), +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, k, x) == m : Maybe<&2, S.Ue>}, +e: {Tk.held(u, m) == True{} : Bool}, sp: @w:S.Ue -> {Tk.spares(k, w, tx) == True{} : Bool}) -> {Tk.held(u, Tb.Table.get(S.Ue, k, Tk.ues(tx, x))) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Tk.held(u, Tb.Table.get(S.Ue, k, Tk.ues(tx, x))) == True{} : Bool}, P.Refute.bool(e))
    case Some{+w}:
      sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, Tk.ues(tx, x)), Some{w}, Tk.spared(k, w, tx, x, em, sp(w)))
      (%sg : {Tk.held(u, _) == True{} : Bool}; e)

def Tk.down_spared(+k: U32, +u: S.Ue, +tx: S.Tx, +x: Tb.Table(S.Ue), +h: Tk.Down(k, u, x), sp: @w:S.Ue -> {Tk.spares(k, w, tx) == True{} : Bool}) -> Tk.Down(k, u, Tk.ues(tx, x)):
  match h:
    case Inl{+e}:
      Inl{Tk.spared(k, u, tx, x, e, sp(u))}
    case Inr{+e}:
      Inr{Tk.held_spared(k, u, tx, x, Tb.Table.get(S.Ue, k, x), {==}, e, sp)}

def Tk.assoc_phase(+u: S.Ue, +p: S.Phase) -> {U32.is_eq(S.Ue.assoc(S.Ue.with_phase(u, p)), S.Ue.assoc(u)) == True{} : Bool}:
  match u:
    case S.Ue{+assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      P.U32.is_eq_refl(assoc)

# The handover of u's own row: when aimed at the association, its context
# becomes Registered with its security context.
def Tk.leg_self(+assoc: U32, +k: U32, +u: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +x: Tb.Table(S.Ue), +eg: {Tb.Table.get(S.Ue, k, x) == Some{u} : Maybe<&2, S.Ue>}, +t: Bool, +et: {Ho.Ho.aimed(u, assoc) == t : Bool}, +s: Bool) -> Tk.Down(k, u, Tk.ues(N.Out.tx(Ho.Ho.down_leg(k, u, ctx, nh, leg, t, s)), x)):
  match t s:
    case True{} _:
      +p : S.Phase = S.Registered{ctx, nh, None{}}
      +v = S.Ue.with_phase(u, p)
      sr = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.Ues.rephase(k, p, x)), Some{v}, Rephase.self(k, p, u, x, eg))
      Inr{(%sr : {Tk.held(u, _) == True{} : Bool}; P.Bool.and_intro(U32.is_eq(S.Ue.assoc(v), S.Ue.assoc(u)), S.Ue.secures(v, S.Ue.supi(u)), Tk.assoc_phase(u, p), W.secures_self(u, p, PW.Walk.aimed_supi(u, assoc, et), {==})))}
    case False{} True{}:
      Inl{eg}
    case False{} False{}:
      Inl{eg}

def Tk.row_self(+assoc: U32, +k: U32, +u: S.Ue, +p: S.Phase, +x: Tb.Table(S.Ue), +eg: {Tb.Table.get(S.Ue, k, x) == Some{u} : Maybe<&2, S.Ue>}) -> Tk.Down(k, u, Tk.ues(N.Out.tx(Ho.Ho.down_row(assoc, k, u, p)), x)):
  match p:
    case S.Handover{+ctx, +nh, source, +leg}:
      Tk.leg_self(assoc, k, u, ctx, nh, leg, x, eg, Ho.Ho.aimed(u, assoc), {==}, U32.is_eq(S.Ue.assoc(u), assoc))
    case S.Created{}:
      Inl{eg}
    case S.Identifying{guard}:
      Inl{eg}
    case S.Authenticating{guard, av, resynced, supi}:
      Inl{eg}
    case S.SecurityMode{guard, ctx, k_amf}:
      Inl{eg}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      Inl{eg}
    case S.Registered{ctx, nh, released}:
      Inl{eg}
    case S.Switching{guard, ctx, nh, released}:
      Inl{eg}
    case S.Releasing{guard}:
      Inl{eg}

def Tk.downs_at(+assoc: U32, +k: U32, +u: S.Ue, +more: Tb.Table(S.Ue), +x: Tb.Table(S.Ue), +eg: {Tb.Table.get(S.Ue, k, x) == Some{u} : Maybe<&2, S.Ue>}, +hc: {S.Ues.clear(k, u, more) == True{} : Bool}) -> Tk.Down(k, u, Tk.ues(N.Out.tx(Ho.Ho.downs(assoc, (k, u) <> more)), x)):
  +a = Ho.Ho.down_row(assoc, k, u, S.Ue.phase(u))
  +b = Ho.Ho.downs(assoc, more)
  Tk.down_join(k, u, x, a, b, Tk.down_spared(k, u, N.Out.tx(b), Tk.ues(N.Out.tx(a), x), Tk.row_self(assoc, k, u, S.Ue.phase(u), x, eg), w => Tk.sp_downs(assoc, more, k, u, w, hc)))

def Tk.downs_if(+assoc: U32, +k1: U32, +u1: S.Ue, +more: Tb.Table(S.Ue), +k: U32, +u: S.Ue, +x: Tb.Table(S.Ue), +eg: {Tb.Table.get(S.Ue, k, x) == Some{u} : Maybe<&2, S.Ue>}, +b: Bool, +eb: {U32.is_eq(k1, k) == b : Bool}, +er: {Tb.Table.hit(S.Ue, u1, Tb.Table.get(S.Ue, k, more), b) == Some{u} : Maybe<&2, S.Ue>}, +un: {Bool.and(S.Ues.clear(k1, u1, more), S.Ues.unique(more)) == True{} : Bool}, ih: @y:Tb.Table(S.Ue) -> {Tb.Table.get(S.Ue, k, y) == Some{u} : Maybe<&2, S.Ue>} -> {Tb.Table.get(S.Ue, k, more) == Some{u} : Maybe<&2, S.Ue>} -> Tk.Down(k, u, Tk.ues(N.Out.tx(Ho.Ho.downs(assoc, more)), y))) -> Tk.Down(k, u, Tk.ues(N.Out.tx(Ho.Ho.downs(assoc, (k1, u1) <> more)), x)):
  match b:
    case True{}:
      +ek = P.U32.eq_of_is_eq(k1, k, eb)
      +eu = P.Some.inj(S.Ue, u1, u, er)
      hc : {S.Ues.clear(k, u, more) == True{} : Bool} = (%ek : {S.Ues.clear(_, u, more) == True{} : Bool}; (%eu : {S.Ues.clear(k1, _, more) == True{} : Bool}; P.Bool.and_true_l(S.Ues.clear(k1, u1, more), S.Ues.unique(more), un)))
      sk = Equal.sym(U32, k1, k, ek)
      su = Equal.sym(S.Ue, u1, u, eu)
      (%sk : Tk.Down(k, u, Tk.ues(N.Out.tx(Ho.Ho.downs(assoc, (_, u1) <> more)), x)); (%su : Tk.Down(k, u, Tk.ues(N.Out.tx(Ho.Ho.downs(assoc, (k, _) <> more)), x)); Tk.downs_at(assoc, k, u, more, x, eg, hc)))
    case False{}:
      +a = Ho.Ho.down_row(assoc, k1, u1, S.Ue.phase(u1))
      +ne = Equal.trans(Bool, U32.is_eq(k, k1), U32.is_eq(k1, k), False{}, P.U32.sym(k, k1), eb)
      Tk.down_join(k, u, x, a, Ho.Ho.downs(assoc, more), ih(Tk.ues(N.Out.tx(a), x), Tk.spared(k, u, N.Out.tx(a), x, eg, Tk.sp_row(assoc, k1, u1, S.Ue.phase(u1), k, u, ne)), er))

# Ending the handovers of a unique table's rows keeps the row under k, or
# rephases it once.
def Tk.downs(+assoc: U32, +rows: Tb.Table(S.Ue), +k: U32, +u: S.Ue, +x: Tb.Table(S.Ue), +eg: {Tb.Table.get(S.Ue, k, x) == Some{u} : Maybe<&2, S.Ue>}, +er: {Tb.Table.get(S.Ue, k, rows) == Some{u} : Maybe<&2, S.Ue>}, +un: {S.Ues.unique(rows) == True{} : Bool}) -> Tk.Down(k, u, Tk.ues(N.Out.tx(Ho.Ho.downs(assoc, rows)), x)):
  match rows:
    case Nil{}:
      Empty.absurd(Tk.Down(k, u, Tk.ues(N.Out.tx(Ho.Ho.downs(assoc, [])), x)), P.Refute.none_some(S.Ue, u, er))
    case (+k1, +u1) <> +more:
      Tk.downs_if(assoc, k1, u1, more, k, u, x, eg, U32.is_eq(k1, k), {==}, er, un, y => ey => em => Tk.downs(assoc, more, k, u, y, ey, em, P.Bool.and_true_r(S.Ues.clear(k1, u1, more), S.Ues.unique(more), un)))

def Tk.drop_held(+assoc: U32, +ues: Tb.Table(S.Ue), +k: U32, +u: S.Ue, +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, k, ues) == m : Maybe<&2, S.Ue>}, +e: {Tk.held(u, m) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> {S.Ues.secured(S.Ue.supi(u), S.Ues.sift(S.Others{assoc}, ues)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({S.Ues.secured(S.Ue.supi(u), S.Ues.sift(S.Others{assoc}, ues)) == True{} : Bool}, P.Refute.bool(e))
    case Some{+w}:
      +same = U32.is_eq(S.Ue.assoc(w), S.Ue.assoc(u))
      ew = Equal.sym(U32, S.Ue.assoc(w), S.Ue.assoc(u), P.U32.eq_of_is_eq(S.Ue.assoc(w), S.Ue.assoc(u), P.Bool.and_true_l(same, S.Ue.secures(w, S.Ue.supi(u)), e)))
      sa = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(w), assoc), False{}, (%ew : {U32.is_eq(_, assoc) == False{} : Bool}; ea))
      W.sec_get(S.Ue.supi(u), k, w, S.Ues.sift(S.Others{assoc}, ues), Sift.get(S.Others{assoc}, k, w, ues, em, (%sa : {Bool.not(_) == True{} : Bool}; {==})), P.Bool.and_true_r(same, S.Ue.secures(w, S.Ue.supi(u)), e))

# Its contexts going spare u, of another association, or what secures it.
def Tk.drop(+s: S.State, +assoc: U32, +as: Tb.Table(B.Bytes()), +k: U32, +u: S.Ue, +h: Tk.Down(k, u, S.State.ues(s)), +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Kept(k, u, S.State.ues(S.State.with_assocs(N.Step.state(R.Route.drop(s, assoc)), as))):
  match s:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, n4}:
      match h:
        case Inl{+eu}:
          sa = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(u), assoc), False{}, ea)
          Inl{Sift.get(S.Others{assoc}, k, u, ues, eu, (%sa : {Bool.not(_) == True{} : Bool}; {==}))}
        case Inr{+e}:
          Inr{Tk.drop_held(assoc, ues, k, u, Tb.Table.get(S.Ue, k, ues), {==}, e, ea)}

def Tk.reset(+st: S.State, +assoc: U32, +as: Tb.Table(B.Bytes()), +k: U32, +u: S.Ue, +eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +un: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +ea: {U32.is_eq(S.Ue.assoc(u), assoc) == False{} : Bool}) -> Tk.Kept(k, u, S.State.ues(S.State.with_assocs(N.Step.state(R.Route.reset(st, assoc)), as))):
  +o = Ho.Ho.down(st, assoc)
  +s1 = N.Step.state(N.Step.of(st, o))
  se = Equal.sym(Tb.Table(S.Ue), S.State.ues(s1), Tk.ues(N.Out.tx(o), S.State.ues(st)), Tk.render(st, o))
  Tk.drop(s1, assoc, as, k, u, (%se : Tk.Down(k, u, _); Tk.downs(assoc, S.State.ues(st), k, u, S.State.ues(st), eu, eu, un)), ea)

def L.amf.takeover.authenticated(st, entropy, assoc, stream, len, bytes, k, u, e, eu, ea, eg):
  +x = S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))
  Tk.removed(k, u, x, eg, PW.Walk.pdu(o => Tk.Kept(k, u, S.State.ues(K.Kernel.state(o))), o => Tk.Ok(k, u, S.State.ues(st), o), st, assoc, stream, entropy, Fr.Pdu.read(bytes), acts => h => cx => nr => Tk.kept_get(k, u, S.State.ues(st), eu), +id => +ok => acts => h => cx => er => Tk.reset(st, assoc, S.Assocs.set(assoc, id, S.State.assocs(N.Step.state(R.Route.reset(st, assoc))), ok), k, u, eu, e, ea), +o => w => Tk.out(st, o, k, u, w), +kind => +code => +ies => ea2 => W.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code), k, u, eu, e, ea)))
