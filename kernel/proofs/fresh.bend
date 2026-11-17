import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../table.bend as Tb
import ../state.bend as S
import ../amf/ngap.bend as N
import ../nas/security.bend as Sec
import ./lib.bend as P
import ../LAWS.bend as L
import ../amf/gmm.bend as Gmm
import ../smf/n4.bend as Up
import ../smf/gsm.bend as Gsm
import ../smf/switch.bend as Sw
import ../amf/handover.bend as Ho
import ../amf/path_switch.bend as Ps
import ../ngap/gen/types.bend as G
import ../frame.bend as F

# Downlink NAS COUNT freshness, outcome by outcome (nas_sec.downlink_fresh)
# -------------------------------------------------------------------------
# What every procedure's outcome keeps, whatever key: each phase it writes
# under a key holds what Ng.Fresh.holds asks of it, against the context the
# key's phase held in st and the messages the outcome's actions carry to the
# key (Fs.sealed); each such message goes to a key the transaction writes
# (Fs.sends). The liveness walk carries it (Lv.does); the law reads the row
# the key names after the step off the last write under it.

def Fs.ctx(+st: S.State, +key: U32) -> Maybe<&2, Sec.Nas.Ctx>:
  S.Ue.nas(Tb.Table.get(S.Ue, key, S.State.ues(st)))

def Fs.write(+st: S.State, +key: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +acts: List<&2, N.Act>) -> Bool:
  N.Fresh.holds(Fs.ctx(st, key), c, N.Acts.nas(key, acts))

def Fs.sealed(+st: S.State, tx: S.Tx, +acts: List<&2, N.Act>) -> Bool:
  match tx:
    case S.Put{+key, +ue}:
      Fs.write(st, key, S.Phase.nas(S.Ue.phase(ue)), acts)
    case S.Rephase{+key, +p}:
      Fs.write(st, key, S.Phase.nas(p), acts)
    case S.Del{+key}:
      Fs.write(st, key, None{}, acts)
    case S.Both{a, b}:
      Bool.and(Fs.sealed(st, a, acts), Fs.sealed(st, b, acts))
    case _:
      True{}

# The transaction writes a row under k.
def Fs.writes(+k: U32, tx: S.Tx) -> Bool:
  match tx:
    case S.Put{key, ue}:
      U32.is_eq(key, k)
    case S.Rephase{key, p}:
      U32.is_eq(key, k)
    case S.Del{key}:
      U32.is_eq(key, k)
    case S.Both{a, b}:
      Bool.or(Fs.writes(k, a), Fs.writes(k, b))
    case _:
      False{}

def Fs.sent(+tx: S.Tx, m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{(j, x)}:
      Fs.writes(j, tx)

def Fs.sends(+tx: S.Tx, acts: List<&2, N.Act>) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case a <> more:
      Bool.and(Fs.sent(tx, N.Act.nas(a)), Fs.sends(tx, more))

def Fs.nas(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>) -> Bool:
  Bool.and(Fs.sealed(st, tx, acts), Fs.sends(tx, acts))

# What nas_sec.downlink_fresh asks of an outcome where keys name one row each
# (S.Ues.unique), the premise the law has.
def Fs.ok(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>) -> Bool:
  Bool.or(Fs.nas(st, tx, acts), Bool.not(S.Ues.unique(S.State.ues(st))))

def Fs.ok_of(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +h: {Fs.nas(st, tx, acts) == True{} : Bool}) -> {Fs.ok(st, tx, acts) == True{} : Bool}:
  P.Bool.or_l(Fs.nas(st, tx, acts), Bool.not(S.Ues.unique(S.State.ues(st))), h)

def Fs.or_got(+x: Bool, +h: {Bool.or(x, False{}) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(h))

def Fs.or_map(+x: Bool, +y: Bool, +u: Bool, f: {x == True{} : Bool} -> {y == True{} : Bool}, +h: {Bool.or(x, Bool.not(u)) == True{} : Bool}) -> {Bool.or(y, Bool.not(u)) == True{} : Bool}:
  match u:
    case True{}:
      P.Bool.or_l(y, False{}, f(Fs.or_got(x, h)))
    case False{}:
      P.Bool.or_r(y, True{}, {==})

def Fs.or_map2(+x1: Bool, +x2: Bool, +y: Bool, +u: Bool, f: {x1 == True{} : Bool} -> {x2 == True{} : Bool} -> {y == True{} : Bool}, +h1: {Bool.or(x1, Bool.not(u)) == True{} : Bool}, +h2: {Bool.or(x2, Bool.not(u)) == True{} : Bool}) -> {Bool.or(y, Bool.not(u)) == True{} : Bool}:
  match u:
    case True{}:
      P.Bool.or_l(y, False{}, f(Fs.or_got(x1, h1), Fs.or_got(x2, h2)))
    case False{}:
      P.Bool.or_r(y, True{}, {==})

def Fs.ok_map(+st: S.State, +ta: S.Tx, +aa: List<&2, N.Act>, +tb: S.Tx, +ab: List<&2, N.Act>, f: {Fs.nas(st, ta, aa) == True{} : Bool} -> {Fs.nas(st, tb, ab) == True{} : Bool}, +h: {Fs.ok(st, ta, aa) == True{} : Bool}) -> {Fs.ok(st, tb, ab) == True{} : Bool}:
  Fs.or_map(Fs.nas(st, ta, aa), Fs.nas(st, tb, ab), S.Ues.unique(S.State.ues(st)), f, h)

def Fs.ok_map2(+st: S.State, +ta: S.Tx, +aa: List<&2, N.Act>, +tb: S.Tx, +ab: List<&2, N.Act>, +tc: S.Tx, +ac: List<&2, N.Act>, f: {Fs.nas(st, ta, aa) == True{} : Bool} -> {Fs.nas(st, tb, ab) == True{} : Bool} -> {Fs.nas(st, tc, ac) == True{} : Bool}, +ha: {Fs.ok(st, ta, aa) == True{} : Bool}, +hb: {Fs.ok(st, tb, ab) == True{} : Bool}) -> {Fs.ok(st, tc, ac) == True{} : Bool}:
  Fs.or_map2(Fs.nas(st, ta, aa), Fs.nas(st, tb, ab), Fs.nas(st, tc, ac), S.Ues.unique(S.State.ues(st)), f, ha, hb)

# An outcome that writes no row and carries no protected NAS message.
def Fs.tmute(tx: S.Tx) -> Bool:
  match tx:
    case S.Put{key, ue}:
      False{}
    case S.Rephase{key, p}:
      False{}
    case S.Del{key}:
      False{}
    case S.Both{a, b}:
      Bool.and(Fs.tmute(a), Fs.tmute(b))
    case _:
      True{}

def Fs.none(m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def Fs.amute(acts: List<&2, N.Act>) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case a <> more:
      Bool.and(Fs.none(N.Act.nas(a)), Fs.amute(more))

def Fs.mute(+tx: S.Tx, +acts: List<&2, N.Act>) -> Bool:
  Bool.and(Fs.tmute(tx), Fs.amute(acts))

# The messages to a key
# ---------------------

def Fs.keep_app(+x: B.Bytes(), +xs: List<&2, B.Bytes()>, +ys: List<&2, B.Bytes()>, +h: Bool) -> {N.Acts.nas_keep(x, List.append(&2, B.Bytes(), xs, ys), h) == List.append(&2, B.Bytes(), N.Acts.nas_keep(x, xs, h), ys) : List<&2, B.Bytes()>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def Fs.to_app(+k: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +xs: List<&2, B.Bytes()>, +ys: List<&2, B.Bytes()>) -> {N.Acts.nas_to(k, m, List.append(&2, B.Bytes(), xs, ys)) == List.append(&2, B.Bytes(), N.Acts.nas_to(k, m, xs), ys) : List<&2, B.Bytes()>}:
  match m:
    case None{}:
      {==}
    case Some{(+key, +x)}:
      Fs.keep_app(x, xs, ys, U32.is_eq(key, k))

def Fs.nas_app(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>) -> {N.Acts.nas(k, List.append(&2, N.Act, xs, ys)) == List.append(&2, B.Bytes(), N.Acts.nas(k, xs), N.Acts.nas(k, ys)) : List<&2, B.Bytes()>}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +more:
      +ih = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, List.append(&2, N.Act, more, ys)), List.append(&2, B.Bytes(), N.Acts.nas(k, more), N.Acts.nas(k, ys)), Fs.nas_app(k, more, ys))
      (%ih : {N.Acts.nas_to(k, N.Act.nas(a), _) == List.append(&2, B.Bytes(), N.Acts.nas_to(k, N.Act.nas(a), N.Acts.nas(k, more)), N.Acts.nas(k, ys)) : List<&2, B.Bytes()>}; Fs.to_app(k, N.Act.nas(a), N.Acts.nas(k, more), N.Acts.nas(k, ys)))

def Fs.to_none(+k: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +xs: List<&2, B.Bytes()>, +h: {Fs.none(m) == True{} : Bool}) -> {N.Acts.nas_to(k, m, xs) == xs : List<&2, B.Bytes()>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({N.Acts.nas_to(k, Some{x}, xs) == xs : List<&2, B.Bytes()>}, P.Refute.bool(h))

def Fs.amute_nas(+k: U32, +acts: List<&2, N.Act>, +h: {Fs.amute(acts) == True{} : Bool}) -> {N.Acts.nas(k, acts) == [] : List<&2, B.Bytes()>}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      +hn = P.Bool.and_true_l(Fs.none(N.Act.nas(a)), Fs.amute(more), h)
      +ih = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, more), [], Fs.amute_nas(k, more, P.Bool.and_true_r(Fs.none(N.Act.nas(a)), Fs.amute(more), h)))
      (%ih : {N.Acts.nas_to(k, N.Act.nas(a), _) == [] : List<&2, B.Bytes()>}; Fs.to_none(k, N.Act.nas(a), [], hn))

def Fs.app_nil(+xs: List<&2, B.Bytes()>) -> {List.append(&2, B.Bytes(), xs, []) == xs : List<&2, B.Bytes()>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +more:
      +e = Equal.sym(List<&2, B.Bytes()>, List.append(&2, B.Bytes(), more, []), more, Fs.app_nil(more))
      (%e : {x <> _ == x <> more : List<&2, B.Bytes()>}; {==})

# Muted actions on either side leave the messages to every key as they were.
def Fs.nas_mute_l(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Fs.amute(xs) == True{} : Bool}) -> {N.Acts.nas(k, List.append(&2, N.Act, xs, ys)) == N.Acts.nas(k, ys) : List<&2, B.Bytes()>}:
  +e = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, xs), [], Fs.amute_nas(k, xs, h))
  (%(Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, List.append(&2, N.Act, xs, ys)), List.append(&2, B.Bytes(), N.Acts.nas(k, xs), N.Acts.nas(k, ys)), Fs.nas_app(k, xs, ys))) : {_ == N.Acts.nas(k, ys) : List<&2, B.Bytes()>}; (%e : {List.append(&2, B.Bytes(), _, N.Acts.nas(k, ys)) == N.Acts.nas(k, ys) : List<&2, B.Bytes()>}; {==}))

def Fs.nas_mute_r(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Fs.amute(ys) == True{} : Bool}) -> {N.Acts.nas(k, List.append(&2, N.Act, xs, ys)) == N.Acts.nas(k, xs) : List<&2, B.Bytes()>}:
  +e = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, ys), [], Fs.amute_nas(k, ys, h))
  (%(Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, List.append(&2, N.Act, xs, ys)), List.append(&2, B.Bytes(), N.Acts.nas(k, xs), N.Acts.nas(k, ys)), Fs.nas_app(k, xs, ys))) : {_ == N.Acts.nas(k, xs) : List<&2, B.Bytes()>}; (%e : {List.append(&2, B.Bytes(), N.Acts.nas(k, xs), _) == N.Acts.nas(k, xs) : List<&2, B.Bytes()>}; Fs.app_nil(N.Acts.nas(k, xs))))

# Composing outcomes
# ------------------

# What each write asks reads the actions only through the messages to its
# key, which actions carrying none, in front or on either side, leave as
# they were.
type Fs.Ext is Data:
  Front{a: N.Act}
  Before{xs: List<&2, N.Act>}
  After{ys: List<&2, N.Act>}

def Fs.ext(e: Fs.Ext, +acts: List<&2, N.Act>) -> List<&2, N.Act>:
  match e:
    case Front{a}:
      a <> acts
    case Before{xs}:
      List.append(&2, N.Act, xs, acts)
    case After{ys}:
      List.append(&2, N.Act, acts, ys)

def Fs.ext_ok(e: Fs.Ext) -> Bool:
  match e:
    case Front{a}:
      Fs.none(N.Act.nas(a))
    case Before{xs}:
      Fs.amute(xs)
    case After{ys}:
      Fs.amute(ys)

def Fs.ext_nas(+key: U32, +e: Fs.Ext, +acts: List<&2, N.Act>, +ok: {Fs.ext_ok(e) == True{} : Bool}) -> {N.Acts.nas(key, acts) == N.Acts.nas(key, Fs.ext(e, acts)) : List<&2, B.Bytes()>}:
  match e:
    case Front{+a}:
      Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, a <> acts), N.Acts.nas(key, acts), Fs.to_none(key, N.Act.nas(a), N.Acts.nas(key, acts), ok))
    case Before{+xs}:
      Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, List.append(&2, N.Act, xs, acts)), N.Acts.nas(key, acts), Fs.nas_mute_l(key, xs, acts, ok))
    case After{+ys}:
      Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, List.append(&2, N.Act, acts, ys)), N.Acts.nas(key, acts), Fs.nas_mute_r(key, acts, ys, ok))

def Fs.sealed_to(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +x: Fs.Ext, +ok: {Fs.ext_ok(x) == True{} : Bool}, +e: {Fs.sealed(st, tx, acts) == True{} : Bool}) -> {Fs.sealed(st, tx, Fs.ext(x, acts)) == True{} : Bool}:
  match tx:
    case S.Put{+key, +ue}:
      (%Fs.ext_nas(key, x, acts, ok) : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(S.Ue.phase(ue)), _) == True{} : Bool}; e)
    case S.Rephase{+key, +p}:
      (%Fs.ext_nas(key, x, acts, ok) : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(p), _) == True{} : Bool}; e)
    case S.Del{+key}:
      (%Fs.ext_nas(key, x, acts, ok) : {N.Fresh.holds(Fs.ctx(st, key), None{}, _) == True{} : Bool}; e)
    case S.Both{+a, +b}:
      P.Bool.and_intro(Fs.sealed(st, a, Fs.ext(x, acts)), Fs.sealed(st, b, Fs.ext(x, acts)), Fs.sealed_to(st, a, acts, x, ok, P.Bool.and_true_l(Fs.sealed(st, a, acts), Fs.sealed(st, b, acts), e)), Fs.sealed_to(st, b, acts, x, ok, P.Bool.and_true_r(Fs.sealed(st, a, acts), Fs.sealed(st, b, acts), e)))
    case S.Keep{}:
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

def Fs.tmute_sealed(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +h: {Fs.tmute(tx) == True{} : Bool}) -> {Fs.sealed(st, tx, acts) == True{} : Bool}:
  match tx:
    case S.Put{key, ue}:
      Empty.absurd({Fs.sealed(st, S.Put{key, ue}, acts) == True{} : Bool}, P.Refute.bool(h))
    case S.Rephase{key, p}:
      Empty.absurd({Fs.sealed(st, S.Rephase{key, p}, acts) == True{} : Bool}, P.Refute.bool(h))
    case S.Del{key}:
      Empty.absurd({Fs.sealed(st, S.Del{key}, acts) == True{} : Bool}, P.Refute.bool(h))
    case S.Both{+a, +b}:
      P.Bool.and_intro(Fs.sealed(st, a, acts), Fs.sealed(st, b, acts), Fs.tmute_sealed(st, a, acts, P.Bool.and_true_l(Fs.tmute(a), Fs.tmute(b), h)), Fs.tmute_sealed(st, b, acts, P.Bool.and_true_r(Fs.tmute(a), Fs.tmute(b), h)))
    case S.Keep{}:
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

# A message to a key one side writes goes to a key both sides write.
type Fs.Side is Data:
  Left{}
  Right{}

def Fs.whole(s: Fs.Side, +t: S.Tx, +o: S.Tx) -> S.Tx:
  match s:
    case Left{}:
      S.Both{t, o}
    case Right{}:
      S.Both{o, t}

def Fs.writes_in(+j: U32, +s: Fs.Side, +t: S.Tx, +o: S.Tx, +e: {Fs.writes(j, t) == True{} : Bool}) -> {Fs.writes(j, Fs.whole(s, t, o)) == True{} : Bool}:
  match s:
    case Left{}:
      P.Bool.or_l(Fs.writes(j, t), Fs.writes(j, o), e)
    case Right{}:
      P.Bool.or_r(Fs.writes(j, o), Fs.writes(j, t), e)

def Fs.sent_in(+s: Fs.Side, +t: S.Tx, +o: S.Tx, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +h: {Fs.sent(t, m) == True{} : Bool}) -> {Fs.sent(Fs.whole(s, t, o), m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+j, x)}:
      Fs.writes_in(j, s, t, o, h)

def Fs.sends_in(+s: Fs.Side, +t: S.Tx, +o: S.Tx, +acts: List<&2, N.Act>, +h: {Fs.sends(t, acts) == True{} : Bool}) -> {Fs.sends(Fs.whole(s, t, o), acts) == True{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      P.Bool.and_intro(Fs.sent(Fs.whole(s, t, o), N.Act.nas(a)), Fs.sends(Fs.whole(s, t, o), more), Fs.sent_in(s, t, o, N.Act.nas(a), P.Bool.and_true_l(Fs.sent(t, N.Act.nas(a)), Fs.sends(t, more), h)), Fs.sends_in(s, t, o, more, P.Bool.and_true_r(Fs.sent(t, N.Act.nas(a)), Fs.sends(t, more), h)))

def Fs.sends_app(+tx: S.Tx, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {Fs.sends(tx, xs) == True{} : Bool}, +hy: {Fs.sends(tx, ys) == True{} : Bool}) -> {Fs.sends(tx, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      P.Bool.and_intro(Fs.sent(tx, N.Act.nas(a)), Fs.sends(tx, List.append(&2, N.Act, more, ys)), P.Bool.and_true_l(Fs.sent(tx, N.Act.nas(a)), Fs.sends(tx, more), hx), Fs.sends_app(tx, more, ys, P.Bool.and_true_r(Fs.sent(tx, N.Act.nas(a)), Fs.sends(tx, more), hx), hy))

def Fs.none_sent(+tx: S.Tx, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +h: {Fs.none(m) == True{} : Bool}) -> {Fs.sent(tx, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Fs.sent(tx, Some{x}) == True{} : Bool}, P.Refute.bool(h))

def Fs.amute_sends(+tx: S.Tx, +acts: List<&2, N.Act>, +h: {Fs.amute(acts) == True{} : Bool}) -> {Fs.sends(tx, acts) == True{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      P.Bool.and_intro(Fs.sent(tx, N.Act.nas(a)), Fs.sends(tx, more), Fs.none_sent(tx, N.Act.nas(a), P.Bool.and_true_l(Fs.none(N.Act.nas(a)), Fs.amute(more), h)), Fs.amute_sends(tx, more, P.Bool.and_true_r(Fs.none(N.Act.nas(a)), Fs.amute(more), h)))

def Fs.sealed_of(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +h: {Fs.nas(st, tx, acts) == True{} : Bool}) -> {Fs.sealed(st, tx, acts) == True{} : Bool}:
  P.Bool.and_true_l(Fs.sealed(st, tx, acts), Fs.sends(tx, acts), h)

def Fs.sends_of(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +h: {Fs.nas(st, tx, acts) == True{} : Bool}) -> {Fs.sends(tx, acts) == True{} : Bool}:
  P.Bool.and_true_r(Fs.sealed(st, tx, acts), Fs.sends(tx, acts), h)

def Fs.both_if(+st: S.State, +ta: S.Tx, +aa: List<&2, N.Act>, +tb: S.Tx, +ab: List<&2, N.Act>, +ha: {Fs.nas(st, ta, aa) == True{} : Bool}, +hb: {Fs.nas(st, tb, ab) == True{} : Bool}, +x: Bool, +ex: {Fs.mute(ta, aa) == x : Bool}, +hq: {Bool.or(x, Fs.mute(tb, ab)) == True{} : Bool}) -> {Fs.nas(st, S.Both{ta, tb}, List.append(&2, N.Act, aa, ab)) == True{} : Bool}:
  match x:
    case True{}:
      +ma = Equal.sym(Bool, Fs.mute(ta, aa), True{}, ex)
      +em : {Fs.mute(ta, aa) == True{} : Bool} = (%ma : {_ == True{} : Bool}; {==})
      +tm = P.Bool.and_true_l(Fs.tmute(ta), Fs.amute(aa), em)
      +am = P.Bool.and_true_r(Fs.tmute(ta), Fs.amute(aa), em)
      +sb = Fs.sealed_to(st, tb, ab, Before{aa}, am, Fs.sealed_of(st, tb, ab, hb))
      P.Bool.and_intro(Fs.sealed(st, S.Both{ta, tb}, List.append(&2, N.Act, aa, ab)), Fs.sends(S.Both{ta, tb}, List.append(&2, N.Act, aa, ab)), P.Bool.and_intro(Fs.sealed(st, ta, List.append(&2, N.Act, aa, ab)), Fs.sealed(st, tb, List.append(&2, N.Act, aa, ab)), Fs.tmute_sealed(st, ta, List.append(&2, N.Act, aa, ab), tm), sb), Fs.sends_app(S.Both{ta, tb}, aa, ab, Fs.amute_sends(S.Both{ta, tb}, aa, am), Fs.sends_in(Right{}, tb, ta, ab, Fs.sends_of(st, tb, ab, hb))))
    case False{}:
      +em : {Fs.mute(tb, ab) == True{} : Bool} = hq
      +tm = P.Bool.and_true_l(Fs.tmute(tb), Fs.amute(ab), em)
      +am = P.Bool.and_true_r(Fs.tmute(tb), Fs.amute(ab), em)
      +sa = Fs.sealed_to(st, ta, aa, After{ab}, am, Fs.sealed_of(st, ta, aa, ha))
      P.Bool.and_intro(Fs.sealed(st, S.Both{ta, tb}, List.append(&2, N.Act, aa, ab)), Fs.sends(S.Both{ta, tb}, List.append(&2, N.Act, aa, ab)), P.Bool.and_intro(Fs.sealed(st, ta, List.append(&2, N.Act, aa, ab)), Fs.sealed(st, tb, List.append(&2, N.Act, aa, ab)), sa, Fs.tmute_sealed(st, tb, List.append(&2, N.Act, aa, ab), tm)), Fs.sends_app(S.Both{ta, tb}, aa, ab, Fs.sends_in(Left{}, ta, tb, aa, Fs.sends_of(st, ta, aa, ha)), Fs.amute_sends(S.Both{ta, tb}, ab, am)))

# Two outcomes in order, one of them mute.
def Fs.both(+st: S.State, +ta: S.Tx, +aa: List<&2, N.Act>, +tb: S.Tx, +ab: List<&2, N.Act>, +ha: {Fs.nas(st, ta, aa) == True{} : Bool}, +hb: {Fs.nas(st, tb, ab) == True{} : Bool}, +hq: {Bool.or(Fs.mute(ta, aa), Fs.mute(tb, ab)) == True{} : Bool}) -> {Fs.nas(st, S.Both{ta, tb}, List.append(&2, N.Act, aa, ab)) == True{} : Bool}:
  Fs.both_if(st, ta, aa, tb, ab, ha, hb, Fs.mute(ta, aa), {==}, hq)

# An action in front or actions after that carry no protected NAS message.
def Fs.cons(+st: S.State, +tx: S.Tx, +a: N.Act, +acts: List<&2, N.Act>, +hn: {Fs.nas(st, tx, acts) == True{} : Bool}, +ha: {Fs.none(N.Act.nas(a)) == True{} : Bool}) -> {Fs.nas(st, tx, a <> acts) == True{} : Bool}:
  +s = Fs.sealed_to(st, tx, acts, Front{a}, ha, Fs.sealed_of(st, tx, acts, hn))
  P.Bool.and_intro(Fs.sealed(st, tx, a <> acts), Fs.sends(tx, a <> acts), s, P.Bool.and_intro(Fs.sent(tx, N.Act.nas(a)), Fs.sends(tx, acts), Fs.none_sent(tx, N.Act.nas(a), ha), Fs.sends_of(st, tx, acts, hn)))

def Fs.app_mute(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +more: List<&2, N.Act>, +hn: {Fs.nas(st, tx, acts) == True{} : Bool}, +hm: {Fs.amute(more) == True{} : Bool}) -> {Fs.nas(st, tx, List.append(&2, N.Act, acts, more)) == True{} : Bool}:
  +xs = List.append(&2, N.Act, acts, more)
  +s = Fs.sealed_to(st, tx, acts, After{more}, hm, Fs.sealed_of(st, tx, acts, hn))
  P.Bool.and_intro(Fs.sealed(st, tx, xs), Fs.sends(tx, xs), s, Fs.sends_app(tx, acts, more, Fs.sends_of(st, tx, acts, hn), Fs.amute_sends(tx, more, hm)))

# Sealing
# -------

def Fs.ea_refl(+ea: Sec.Nas.Ea) -> {U32.is_eq(Sec.Nas.Ea.id(ea), Sec.Nas.Ea.id(ea)) == True{} : Bool}:
  match ea:
    case Sec.Nea0{}:
      {==}
    case Sec.Nea2{}:
      {==}

def Fs.ia_refl(+ia: Sec.Nas.Ia) -> {U32.is_eq(Sec.Nas.Ia.id(ia), Sec.Nas.Ia.id(ia)) == True{} : Bool}:
  match ia:
    case Sec.Nia2{}:
      {==}

def Fs.keys_same(+k: Sec.Nas.Keys) -> {Sec.Nas.Keys.same(k, k) == True{} : Bool}:
  match k:
    case Sec.Keys{+i, +e, +ea, +ia, +b}:
      +r4 = U32.is_eq(b, b)
      +r3 = Bool.and(U32.is_eq(Sec.Nas.Ia.id(ia), Sec.Nas.Ia.id(ia)), r4)
      +r2 = Bool.and(U32.is_eq(Sec.Nas.Ea.id(ea), Sec.Nas.Ea.id(ea)), r3)
      +r1 = Bool.and(B.bytes_eq(e, e), r2)
      P.Bool.and_intro(B.bytes_eq(i, i), r1, P.Bytes.eq_refl(i), P.Bool.and_intro(B.bytes_eq(e, e), r2, P.Bytes.eq_refl(e), P.Bool.and_intro(U32.is_eq(Sec.Nas.Ea.id(ea), Sec.Nas.Ea.id(ea)), r3, Fs.ea_refl(ea), P.Bool.and_intro(U32.is_eq(Sec.Nas.Ia.id(ia), Sec.Nas.Ia.id(ia)), r4, Fs.ia_refl(ia), P.U32.is_eq_refl(b)))))

def Fs.count_same(+c: Sec.Nas.Count) -> {Sec.Nas.Count.same(c, c) == True{} : Bool}:
  match c:
    case Sec.Count{+o, +s}:
      P.Bool.and_intro(U32.is_eq(o, o), U32.is_eq(s, s), P.U32.is_eq_refl(o), P.U32.is_eq_refl(s))

# A downlink message sealed under keys at a COUNT is sealed there.
def Fs.sealed_seal(+keys: Sec.Nas.Keys, +prot: Sec.Nas.Protection, +c: Sec.Nas.Count, +plain: B.Bytes()) -> {Sec.Nas.sealed(keys, c, Sec.Nas.seal(keys, prot, Sec.Nas.downlink(), c, plain)) == True{} : Bool}:
  +m = Sec.Nas.seal(keys, prot, Sec.Nas.downlink(), c, plain)
  +e = Equal.sym(Result<&2, &2, B.Err, Sec.Nas.Opened>, Sec.Nas.open(keys, Sec.Nas.downlink(), c, m), Done{Sec.Opened{prot, plain}}, L.nas_sec.roundtrip(keys, prot, Sec.Nas.downlink(), c, plain))
  (%e : {Sec.Nas.resealed(keys, c, m, _) == True{} : Bool}; P.Bytes.eq_refl(m))

# What a context protects goes under its COUNT, and leaves the next.
def Fs.protect_run(+keys: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +prot: Sec.Nas.Protection, +plain: B.Bytes()) -> {N.Fresh.run([Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{keys, d, ul}, prot, plain))], keys, d) == Some{Sec.Nas.Count.next(d)} : Maybe<&2, Sec.Nas.Count>}:
  +e = Equal.sym(Bool, Sec.Nas.sealed(keys, d, Sec.Nas.seal(keys, prot, Sec.Nas.downlink(), d, plain)), True{}, Fs.sealed_seal(keys, prot, d, plain))
  (%e : {N.Fresh.then(_, u => N.Fresh.run([], keys, Sec.Nas.Count.next(d))) == Some{Sec.Nas.Count.next(d)} : Maybe<&2, Sec.Nas.Count>}; {==})

def Fs.run_then(+m: B.Bytes(), +more: List<&2, B.Bytes()>, +ms2: List<&2, B.Bytes()>, +keys: Sec.Nas.Keys, +c: Sec.Nas.Count, +c1: Sec.Nas.Count, +b: Bool, +eb: {Sec.Nas.sealed(keys, c, m) == b : Bool}, e: {N.Fresh.then(b, u => N.Fresh.run(more, keys, Sec.Nas.Count.next(c))) == Some{c1} : Maybe<&2, Sec.Nas.Count>}, ih: {N.Fresh.run(more, keys, Sec.Nas.Count.next(c)) == Some{c1} : Maybe<&2, Sec.Nas.Count>} -> {N.Fresh.run(List.append(&2, B.Bytes(), more, ms2), keys, Sec.Nas.Count.next(c)) == N.Fresh.run(ms2, keys, c1) : Maybe<&2, Sec.Nas.Count>}) -> {N.Fresh.then(b, u => N.Fresh.run(List.append(&2, B.Bytes(), more, ms2), keys, Sec.Nas.Count.next(c))) == N.Fresh.run(ms2, keys, c1) : Maybe<&2, Sec.Nas.Count>}:
  match b:
    case True{}:
      ih(e)
    case False{}:
      Empty.absurd({None{} == N.Fresh.run(ms2, keys, c1) : Maybe<&2, Sec.Nas.Count>}, P.Refute.none_some(Sec.Nas.Count, c1, e))

# Messages sealed in turn, then more from the COUNT they leave.
def Fs.run_app(+ms1: List<&2, B.Bytes()>, +ms2: List<&2, B.Bytes()>, +keys: Sec.Nas.Keys, +c: Sec.Nas.Count, +c1: Sec.Nas.Count, e: {N.Fresh.run(ms1, keys, c) == Some{c1} : Maybe<&2, Sec.Nas.Count>}) -> {N.Fresh.run(List.append(&2, B.Bytes(), ms1, ms2), keys, c) == N.Fresh.run(ms2, keys, c1) : Maybe<&2, Sec.Nas.Count>}:
  match ms1:
    case Nil{}:
      +ec = P.Some.inj(Sec.Nas.Count, c, c1, e)
      (%ec : {N.Fresh.run(ms2, keys, c) == N.Fresh.run(ms2, keys, _) : Maybe<&2, Sec.Nas.Count>}; {==})
    case +m <> +more:
      Fs.run_then(m, more, ms2, keys, c, c1, Sec.Nas.sealed(keys, c, m), {==}, e, e2 => Fs.run_app(more, ms2, keys, Sec.Nas.Count.next(c), c1, e2))

# A context unchanged, no message: what a write of it holds.
def Fs.holds_self(+b: Maybe<&2, Sec.Nas.Ctx>) -> {N.Fresh.holds(b, b, []) == True{} : Bool}:
  match b:
    case None{}:
      {==}
    case Some{Sec.Ctx{+k, +d, +ul}}:
      +e = Equal.sym(Bool, Sec.Nas.Keys.same(k, k), True{}, Fs.keys_same(k))
      (%e : {N.Fresh.at(Some{N.Fresh.start_if(d, _)}, d) == True{} : Bool}; Fs.count_same(d))

# A transaction that writes no row in front of another, or after it, the actions the same.
def Fs.pre_tmute(+st: S.State, +r: S.Tx, +t: S.Tx, +acts: List<&2, N.Act>, +hr: {Fs.tmute(r) == True{} : Bool}, +h: {Fs.nas(st, t, acts) == True{} : Bool}) -> {Fs.nas(st, S.Both{r, t}, acts) == True{} : Bool}:
  P.Bool.and_intro(Fs.sealed(st, S.Both{r, t}, acts), Fs.sends(S.Both{r, t}, acts), P.Bool.and_intro(Fs.sealed(st, r, acts), Fs.sealed(st, t, acts), Fs.tmute_sealed(st, r, acts, hr), Fs.sealed_of(st, t, acts, h)), Fs.sends_in(Right{}, t, r, acts, Fs.sends_of(st, t, acts, h)))

def Fs.post_tmute(+st: S.State, +t: S.Tx, +r: S.Tx, +acts: List<&2, N.Act>, +hr: {Fs.tmute(r) == True{} : Bool}, +h: {Fs.nas(st, t, acts) == True{} : Bool}) -> {Fs.nas(st, S.Both{t, r}, acts) == True{} : Bool}:
  P.Bool.and_intro(Fs.sealed(st, S.Both{t, r}, acts), Fs.sends(S.Both{t, r}, acts), P.Bool.and_intro(Fs.sealed(st, t, acts), Fs.sealed(st, r, acts), Fs.sealed_of(st, t, acts, h), Fs.tmute_sealed(st, r, acts, hr)), Fs.sends_in(Left{}, t, r, acts, Fs.sends_of(st, t, acts, h)))

# Mute actions
# ------------

def Fs.amute_app(+xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {Fs.amute(xs) == True{} : Bool}, +hy: {Fs.amute(ys) == True{} : Bool}) -> {Fs.amute(List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      P.Bool.and_intro(Fs.none(N.Act.nas(a)), Fs.amute(List.append(&2, N.Act, more, ys)), P.Bool.and_true_l(Fs.none(N.Act.nas(a)), Fs.amute(more), hx), Fs.amute_app(more, ys, P.Bool.and_true_r(Fs.none(N.Act.nas(a)), Fs.amute(more), hx), hy))

def Fs.drop_mute(+key: U32, +leg: S.Leg, +cause: G.Cause) -> {Fs.amute(Ho.Ho.drop(key, leg, cause)) == True{} : Bool}:
  match leg:
    case S.Asked{t}:
      {==}
    case S.Acked{t, r, s, ts}:
      {==}

def Fs.leg_mute(+key: U32, +p: S.Phase, +cause: G.Cause) -> {Fs.amute(Ho.Ho.leg_drop(key, p, cause)) == True{} : Bool}:
  match p:
    case S.Handover{ctx, nh, source, +leg}:
      Fs.drop_mute(key, leg, cause)
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

def Fs.evict_mute(+vs: Tb.Table(S.Ue)) -> {Fs.amute(Gmm.Gmm.evict(vs)) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case (+key, +v) <> +more:
      +cause = N.Ngap.nas_cause(G.CauseNas.deregister())
      Fs.amute_app(Ho.Ho.leg_drop(key, S.Ue.phase(v), cause), Gmm.Gmm.evict(more), Fs.leg_mute(key, S.Ue.phase(v), cause), Fs.evict_mute(more))

# A write of a phase that holds no NAS context, no message to its key.
def Fs.write_none(+st: S.State, +key: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +acts: List<&2, N.Act>, +ec: {c == None{} : Maybe<&2, Sec.Nas.Ctx>}, +ea: {N.Acts.nas(key, acts) == [] : List<&2, B.Bytes()>}) -> {Fs.write(st, key, c, acts) == True{} : Bool}:
  +sc = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, c, None{}, ec)
  +sa = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, acts), [], ea)
  (%sc : {N.Fresh.holds(Fs.ctx(st, key), _, N.Acts.nas(key, acts)) == True{} : Bool}; (%sa : {N.Fresh.holds(Fs.ctx(st, key), None{}, _) == True{} : Bool}; {==}))

# A mute outcome: one that writes no row and carries no protected NAS message.
def Fs.Mute(+o: N.GOut()) -> Type:
  {Fs.mute(N.Out.tx(o), N.Out.acts(o)) == True{} : Bool}

def Fs.join_mute(+a: N.GOut(), +b: N.GOut(), +ha: {Fs.mute(N.Out.tx(a), N.Out.acts(a)) == True{} : Bool}, +hb: {Fs.mute(N.Out.tx(b), N.Out.acts(b)) == True{} : Bool}) -> {Fs.mute(N.Out.tx(N.Out.join(a, b)), N.Out.acts(N.Out.join(a, b))) == True{} : Bool}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          P.Bool.and_intro(Bool.and(Fs.tmute(ta), Fs.tmute(tb)), Fs.amute(List.append(&2, N.Act, aa, ab)), P.Bool.and_intro(Fs.tmute(ta), Fs.tmute(tb), P.Bool.and_true_l(Fs.tmute(ta), Fs.amute(aa), ha), P.Bool.and_true_l(Fs.tmute(tb), Fs.amute(ab), hb)), Fs.amute_app(aa, ab, P.Bool.and_true_r(Fs.tmute(ta), Fs.amute(aa), ha), P.Bool.and_true_r(Fs.tmute(tb), Fs.amute(ab), hb)))

def Fs.del_if_mute(+key: U32, +t: S.Session, +seq: U32, +more: Tb.Table(S.Session), +b: Bool, later: @q:U32 -> {Fs.mute(N.Out.tx(Up.N4.deletions(more, q)), N.Out.acts(Up.N4.deletions(more, q))) == True{} : Bool}) -> {Fs.mute(N.Out.tx(Up.N4.delete_if(key, t, seq, q => Up.N4.deletions(more, q), b)), N.Out.acts(Up.N4.delete_if(key, t, seq, q => Up.N4.deletions(more, q), b))) == True{} : Bool}:
  match b:
    case True{}:
      +request = Up.N4.delete(S.Session.up_seid(t), seq)
      Fs.join_mute((S.Both{S.Revar{key, S.SVar{S.Session.up_seid(t), seq, S.Deleting{S.Guard{0}, request}}}, S.BumpSeq{1}}, [N.Pfcp{S.Session.tag(t), request}, N.TimerStart{None{}, key, Up.N4.t1_ms()}]), Up.N4.deletions(more, U32.add(seq, 1)), {==}, later(U32.add(seq, 1)))
    case False{}:
      Fs.join_mute((S.DelSession{key}, []), Up.N4.deletions(more, seq), {==}, later(seq))

# Deleting sessions at the UPF is mute.
def Fs.deletions_mute(rows: Tb.Table(S.Session), +seq: U32) -> {Fs.mute(N.Out.tx(Up.N4.deletions(rows, seq)), N.Out.acts(Up.N4.deletions(rows, seq))) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Fs.del_if_mute(key, t, seq, more, S.Session.known(t), +q => Fs.deletions_mute(more, q))

# Writes of a context the step got from the stored one
# ---------------------------------------------------
# A context's keys and downlink COUNT: what a write is judged by. A context a
# procedure works with has the stored context's (Fs.view equal), the uplink
# COUNT apart.

def Fs.KD() -> Data:
  Sigma<&2, &2, Sec.Nas.Keys, _ => Sec.Nas.Count>

def Fs.view(b: Maybe<&2, Sec.Nas.Ctx>) -> Maybe<&2, Fs.KD()>:
  match b:
    case None{}:
      None{}
    case Some{Sec.Ctx{k, d, u}}:
      Some{(k, d)}

def Fs.kd_keys(m: Maybe<&2, Fs.KD()>, +k0: Sec.Nas.Keys) -> Sec.Nas.Keys:
  match m:
    case None{}:
      k0
    case Some{(k, d)}:
      k

def Fs.kd_dl(m: Maybe<&2, Fs.KD()>, +d0: Sec.Nas.Count) -> Sec.Nas.Count:
  match m:
    case None{}:
      d0
    case Some{(k, d)}:
      d

def Fs.start_view(+b: Maybe<&2, Sec.Nas.Ctx>, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +e: {Fs.view(b) == Some{(k, d)} : Maybe<&2, Fs.KD()>}) -> {N.Fresh.start(b, k) == d : Sec.Nas.Count}:
  match b:
    case None{}:
      Empty.absurd({N.Fresh.start(None{}, k) == d : Sec.Nas.Count}, P.Refute.none_some(Fs.KD(), (k, d), e))
    case Some{Sec.Ctx{+kb, +db, ub}}:
      +se = Equal.sym(Maybe<&2, Fs.KD()>, Some{(kb, db)}, Some{(k, d)}, e)
      +ek : {kb == k : Sec.Nas.Keys} = (%se : {Fs.kd_keys(_, k) == k : Sec.Nas.Keys}; {==})
      +ed : {db == d : Sec.Nas.Count} = (%se : {Fs.kd_dl(_, d) == d : Sec.Nas.Count}; {==})
      +sk = Equal.sym(Sec.Nas.Keys, kb, k, ek)
      +sd = Equal.sym(Sec.Nas.Count, db, d, ed)
      +es = Equal.sym(Bool, Sec.Nas.Keys.same(k, k), True{}, Fs.keys_same(k))
      (%sk : {N.Fresh.start_if(db, Sec.Nas.Keys.same(_, k)) == d : Sec.Nas.Count}; (%es : {N.Fresh.start_if(db, _) == d : Sec.Nas.Count}; (%sd : {_ == d : Sec.Nas.Count}; {==})))

def Fs.from_view(+b: Maybe<&2, Sec.Nas.Ctx>, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ms: List<&2, B.Bytes()>, +e: {Fs.view(b) == Some{(k, d)} : Maybe<&2, Fs.KD()>}) -> {N.Fresh.from(b, ms) == Tb.Table.present(Sec.Nas.Count, N.Fresh.run(ms, k, d)) : Bool}:
  match b:
    case None{}:
      Empty.absurd({N.Fresh.from(None{}, ms) == Tb.Table.present(Sec.Nas.Count, N.Fresh.run(ms, k, d)) : Bool}, P.Refute.none_some(Fs.KD(), (k, d), e))
    case Some{Sec.Ctx{+kb, +db, ub}}:
      +se = Equal.sym(Maybe<&2, Fs.KD()>, Some{(kb, db)}, Some{(k, d)}, e)
      +ek : {kb == k : Sec.Nas.Keys} = (%se : {Fs.kd_keys(_, k) == k : Sec.Nas.Keys}; {==})
      +ed : {db == d : Sec.Nas.Count} = (%se : {Fs.kd_dl(_, d) == d : Sec.Nas.Count}; {==})
      +sk = Equal.sym(Sec.Nas.Keys, kb, k, ek)
      +sd = Equal.sym(Sec.Nas.Count, db, d, ed)
      (%sk : {Tb.Table.present(Sec.Nas.Count, N.Fresh.run(ms, _, db)) == Tb.Table.present(Sec.Nas.Count, N.Fresh.run(ms, k, d)) : Bool}; (%sd : {Tb.Table.present(Sec.Nas.Count, N.Fresh.run(ms, k, _)) == Tb.Table.present(Sec.Nas.Count, N.Fresh.run(ms, k, d)) : Bool}; {==}))

# One message sealed under the stored context's COUNT, the next written.
def Fs.told_write(+b: Maybe<&2, Sec.Nas.Ctx>, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +prot: Sec.Nas.Protection, +plain: B.Bytes(), +e: {Fs.view(b) == Some{(k, d)} : Maybe<&2, Fs.KD()>}) -> {N.Fresh.holds(b, Some{Sec.Ctx{k, Sec.Nas.Count.next(d), ul}}, [Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, prot, plain))]) == True{} : Bool}:
  +ms : List<&2, B.Bytes()> = [Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, prot, plain))]
  +sd = Equal.sym(Sec.Nas.Count, N.Fresh.start(b, k), d, Fs.start_view(b, k, d, e))
  +sr = Equal.sym(Maybe<&2, Sec.Nas.Count>, N.Fresh.run(ms, k, d), Some{Sec.Nas.Count.next(d)}, Fs.protect_run(k, d, ul, prot, plain))
  (%sd : {N.Fresh.at(N.Fresh.run(ms, k, _), Sec.Nas.Count.next(d)) == True{} : Bool}; (%sr : {N.Fresh.at(_, Sec.Nas.Count.next(d)) == True{} : Bool}; Fs.count_same(Sec.Nas.Count.next(d))))

# The stored context's keys and COUNT written back, no message.
def Fs.kept_write(+b: Maybe<&2, Sec.Nas.Ctx>, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +e: {Fs.view(b) == Some{(k, d)} : Maybe<&2, Fs.KD()>}) -> {N.Fresh.holds(b, Some{Sec.Ctx{k, d, ul}}, []) == True{} : Bool}:
  +sd = Equal.sym(Sec.Nas.Count, N.Fresh.start(b, k), d, Fs.start_view(b, k, d, e))
  (%sd : {N.Fresh.at(Some{_}, d) == True{} : Bool}; Fs.count_same(d))

# One message sealed under the stored context's COUNT, the context gone.
def Fs.gone_write(+b: Maybe<&2, Sec.Nas.Ctx>, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +prot: Sec.Nas.Protection, +plain: B.Bytes(), +e: {Fs.view(b) == Some{(k, d)} : Maybe<&2, Fs.KD()>}) -> {N.Fresh.holds(b, None{}, [Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, prot, plain))]) == True{} : Bool}:
  +ms : List<&2, B.Bytes()> = [Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, prot, plain))]
  +sf = Equal.sym(Bool, N.Fresh.from(b, ms), Tb.Table.present(Sec.Nas.Count, N.Fresh.run(ms, k, d)), Fs.from_view(b, k, d, ms, e))
  +sr = Equal.sym(Maybe<&2, Sec.Nas.Count>, N.Fresh.run(ms, k, d), Some{Sec.Nas.Count.next(d)}, Fs.protect_run(k, d, ul, prot, plain))
  (%sf : {_ == True{} : Bool}; (%sr : {Tb.Table.present(Sec.Nas.Count, _) == True{} : Bool}; {==}))

# A sealed message is security protected, and the actions carry it to its key.
def Fs.seal_protected(+k: Sec.Nas.Keys, +prot: Sec.Nas.Protection, +d: Sec.Nas.Count, +plain: B.Bytes()) -> {Sec.Nas.is_protected(Sec.Nas.seal(k, prot, Sec.Nas.downlink(), d, plain)) == True{} : Bool}:
  match k:
    case Sec.Keys{k_int, k_enc, ea, ia, bearer}:
      match prot:
        case Sec.Integrity{}:
          {==}
        case Sec.Ciphered{}:
          {==}
        case Sec.IntegrityNew{}:
          {==}
        case Sec.CipheredNew{}:
          {==}

# A phase that holds a context in force holds the one written into it.
def Fs.nas_with(+q: S.Phase, +c: Sec.Nas.Ctx, +ec: {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(q)) == True{} : Bool}) -> {S.Phase.nas(S.Phase.with_ctx(q, c)) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}:
  match q:
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Created{}:
      Empty.absurd({S.Phase.nas(S.Phase.with_ctx(S.Created{}, c)) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, P.Refute.bool(ec))
    case S.Identifying{guard}:
      Empty.absurd({S.Phase.nas(S.Phase.with_ctx(S.Identifying{guard}, c)) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, P.Refute.bool(ec))
    case S.Authenticating{guard, av, resynced, supi}:
      Empty.absurd({S.Phase.nas(S.Phase.with_ctx(S.Authenticating{guard, av, resynced, supi}, c)) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, P.Refute.bool(ec))
    case S.Handover{ctx, nh, source, leg}:
      Empty.absurd({S.Phase.nas(S.Phase.with_ctx(S.Handover{ctx, nh, source, leg}, c)) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, P.Refute.bool(ec))
    case S.Releasing{guard}:
      Empty.absurd({S.Phase.nas(S.Phase.with_ctx(S.Releasing{guard}, c)) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, P.Refute.bool(ec))

def Fs.if_true(+key: U32, +m: B.Bytes(), +h: {Sec.Nas.is_protected(m) == True{} : Bool}) -> {N.Act.nas_if(key, m, Sec.Nas.is_protected(m)) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}:
  +sh = Equal.sym(Bool, Sec.Nas.is_protected(m), True{}, h)
  (%sh : {N.Act.nas_if(key, m, _) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}; {==})

def Fs.dl_carries(+assoc: U32, +stream: U32, +key: U32, +ran: B.Bytes(), +m: B.Bytes(), +h: {Sec.Nas.is_protected(m) == True{} : Bool}) -> {N.Act.nas(N.DlNas{assoc, stream, key, ran, m}) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}:
  Fs.if_true(key, m, h)

def Fs.release_carries(+assoc: U32, +stream: U32, +key: U32, +ran: B.Bytes(), +psi: U32, +m: B.Bytes(), +h: {Sec.Nas.is_protected(m) == True{} : Bool}) -> {N.Act.nas(N.PduRelease{assoc, stream, key, ran, psi, m}) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}:
  Fs.if_true(key, m, h)

def Fs.setup_carries(+assoc: U32, +stream: U32, +key: U32, +ran: B.Bytes(), +psi: U32, +sst: B.Bytes(), +m: B.Bytes(), +transfer: B.Bytes(), +h: {Sec.Nas.is_protected(m) == True{} : Bool}) -> {N.Act.nas(N.PduSetup{assoc, stream, key, ran, psi, sst, m, transfer}) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}:
  Fs.if_true(key, m, h)

def Fs.ics_carries(+assoc: U32, +stream: U32, +key: U32, +ran: B.Bytes(), +cfg: S.Cfg, +caps: B.Bytes(), +k_gnb: B.Bytes(), +m: B.Bytes(), +h: {Sec.Nas.is_protected(m) == True{} : Bool}) -> {N.Act.nas(N.Ics{assoc, stream, key, ran, cfg, caps, k_gnb, m}) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}:
  Fs.if_true(key, m, h)

def Fs.protect_protected(+k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +prot: Sec.Nas.Protection, +plain: B.Bytes()) -> {Sec.Nas.is_protected(Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, prot, plain))) == True{} : Bool}:
  Fs.seal_protected(k, prot, d, plain)

def Fs.one_nas(+key: U32, +x: N.Act, +m: B.Bytes(), +more: List<&2, N.Act>, +ex: {N.Act.nas(x) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}) -> {N.Acts.nas(key, x <> more) == m <> N.Acts.nas(key, more) : List<&2, B.Bytes()>}:
  +sx = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, N.Act.nas(x), Some{(key, m)}, ex)
  +se = Equal.sym(Bool, U32.is_eq(key, key), True{}, P.U32.is_eq_refl(key))
  (%sx : {N.Acts.nas_to(key, _, N.Acts.nas(key, more)) == m <> N.Acts.nas(key, more) : List<&2, B.Bytes()>}; (%se : {N.Acts.nas_keep(m, N.Acts.nas(key, more), _) == m <> N.Acts.nas(key, more) : List<&2, B.Bytes()>}; {==}))

# One protected message to key under the context the key held, the next written.
def Fs.told_leaf(+st: S.State, +key: U32, +q: S.Phase, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +prot: Sec.Nas.Protection, +plain: B.Bytes(), +x: N.Act, +ex: {N.Act.nas(x) == Some{(key, Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, prot, plain)))} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, +eq: {S.Phase.nas(q) == Some{Sec.Ctx{k, Sec.Nas.Count.next(d), ul}} : Maybe<&2, Sec.Nas.Ctx>}, +ev: {Fs.view(Fs.ctx(st, key)) == Some{(k, d)} : Maybe<&2, Fs.KD()>}) -> {Fs.nas(st, S.Rephase{key, q}, [x]) == True{} : Bool}:
  +m = Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, prot, plain))
  +sn = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, [x]), [m], Fs.one_nas(key, x, m, [], ex))
  +sq = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.nas(q), Some{Sec.Ctx{k, Sec.Nas.Count.next(d), ul}}, eq)
  +sx = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, N.Act.nas(x), Some{(key, m)}, ex)
  +hw : {Fs.write(st, key, S.Phase.nas(q), [x]) == True{} : Bool} = (%sq : {N.Fresh.holds(Fs.ctx(st, key), _, N.Acts.nas(key, [x])) == True{} : Bool}; (%sn : {N.Fresh.holds(Fs.ctx(st, key), Some{Sec.Ctx{k, Sec.Nas.Count.next(d), ul}}, _) == True{} : Bool}; Fs.told_write(Fs.ctx(st, key), k, d, ul, prot, plain, ev)))
  +hs : {Fs.sent(S.Rephase{key, q}, N.Act.nas(x)) == True{} : Bool} = (%sx : {Fs.sent(S.Rephase{key, q}, _) == True{} : Bool}; P.U32.is_eq_refl(key))
  P.Bool.and_intro(Fs.write(st, key, S.Phase.nas(q), [x]), Bool.and(Fs.sent(S.Rephase{key, q}, N.Act.nas(x)), True{}), hw, P.Bool.and_intro(Fs.sent(S.Rephase{key, q}, N.Act.nas(x)), True{}, hs, {==}))

# The stored context's keys and COUNT written back into q, no message.
def Fs.kept_holds(+st: S.State, +key: U32, +q: S.Phase, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +eq: {S.Phase.nas(q) == Some{Sec.Ctx{k, d, ul}} : Maybe<&2, Sec.Nas.Ctx>}, +ev: {Fs.view(Fs.ctx(st, key)) == Some{(k, d)} : Maybe<&2, Fs.KD()>}) -> {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(q), []) == True{} : Bool}:
  +sq = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.nas(q), Some{Sec.Ctx{k, d, ul}}, eq)
  (%sq : {N.Fresh.holds(Fs.ctx(st, key), _, []) == True{} : Bool}; Fs.kept_write(Fs.ctx(st, key), k, d, ul, ev))

# Messages to one key
# -------------------

def Fs.to_key_m(+key: U32, m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{(j, x)}:
      U32.is_eq(j, key)

# Every protected message the actions carry goes to key.
def Fs.to_key(+key: U32, acts: List<&2, N.Act>) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case a <> more:
      Bool.and(Fs.to_key_m(key, N.Act.nas(a)), Fs.to_key(key, more))

def Fs.none_to(+key: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +h: {Fs.none(m) == True{} : Bool}) -> {Fs.to_key_m(key, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Fs.to_key_m(key, Some{x}) == True{} : Bool}, P.Refute.bool(h))

def Fs.amute_to_key(+key: U32, +acts: List<&2, N.Act>, +h: {Fs.amute(acts) == True{} : Bool}) -> {Fs.to_key(key, acts) == True{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      P.Bool.and_intro(Fs.to_key_m(key, N.Act.nas(a)), Fs.to_key(key, more), Fs.none_to(key, N.Act.nas(a), P.Bool.and_true_l(Fs.none(N.Act.nas(a)), Fs.amute(more), h)), Fs.amute_to_key(key, more, P.Bool.and_true_r(Fs.none(N.Act.nas(a)), Fs.amute(more), h)))

def Fs.to_key_app(+key: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {Fs.to_key(key, xs) == True{} : Bool}, +hy: {Fs.to_key(key, ys) == True{} : Bool}) -> {Fs.to_key(key, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      P.Bool.and_intro(Fs.to_key_m(key, N.Act.nas(a)), Fs.to_key(key, List.append(&2, N.Act, more, ys)), P.Bool.and_true_l(Fs.to_key_m(key, N.Act.nas(a)), Fs.to_key(key, more), hx), Fs.to_key_app(key, more, ys, P.Bool.and_true_r(Fs.to_key_m(key, N.Act.nas(a)), Fs.to_key(key, more), hx), hy))

def Fs.sent_key(+key: U32, +tx: S.Tx, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +ht: {Fs.to_key_m(key, m) == True{} : Bool}, +hw: {Fs.writes(key, tx) == True{} : Bool}) -> {Fs.sent(tx, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+j, x)}:
      +ej = Equal.sym(U32, j, key, P.U32.eq_of_is_eq(j, key, ht))
      (%ej : {Fs.writes(_, tx) == True{} : Bool}; hw)

# Messages that all go to a key the transaction writes are sent.
def Fs.to_key_sends(+key: U32, +tx: S.Tx, +acts: List<&2, N.Act>, +ht: {Fs.to_key(key, acts) == True{} : Bool}, +hw: {Fs.writes(key, tx) == True{} : Bool}) -> {Fs.sends(tx, acts) == True{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      P.Bool.and_intro(Fs.sent(tx, N.Act.nas(a)), Fs.sends(tx, more), Fs.sent_key(key, tx, N.Act.nas(a), P.Bool.and_true_l(Fs.to_key_m(key, N.Act.nas(a)), Fs.to_key(key, more), ht), hw), Fs.to_key_sends(key, tx, more, P.Bool.and_true_r(Fs.to_key_m(key, N.Act.nas(a)), Fs.to_key(key, more), ht), hw))

def Fs.keep_nil(+x: B.Bytes(), +more: List<&2, B.Bytes()>, +b: Bool, +eb: {b == True{} : Bool}, +e: {N.Acts.nas_keep(x, more, b) == [] : List<&2, B.Bytes()>}) -> Empty:
  match b:
    case True{}:
      P.Refute.none_some(B.Bytes(), x, Equal.sym(Maybe<&2, B.Bytes()>, Some{x}, None{}, (%e : {List.head(&2, B.Bytes(), x <> more) == List.head(&2, B.Bytes(), _) : Maybe<&2, B.Bytes()>}; {==})))
    case False{}:
      P.Refute.true_false(Equal.sym(Bool, False{}, True{}, eb))

def Fs.none_of(+key: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +more: List<&2, B.Bytes()>, +ht: {Fs.to_key_m(key, m) == True{} : Bool}, +e: {N.Acts.nas_to(key, m, more) == [] : List<&2, B.Bytes()>}) -> {Fs.none(m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+j, +x)}:
      Empty.absurd({Fs.none(Some{(j, x)}) == True{} : Bool}, Fs.keep_nil(x, more, U32.is_eq(j, key), ht, e))


def Fs.none_is(+m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +h: {Fs.none(m) == True{} : Bool}) -> {m == None{} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, P.Refute.bool(h))
def Fs.to_nil(+key: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +more: List<&2, B.Bytes()>, +ht: {Fs.to_key_m(key, m) == True{} : Bool}, +e: {N.Acts.nas_to(key, m, more) == [] : List<&2, B.Bytes()>}) -> {more == [] : List<&2, B.Bytes()>}:
  +em = Fs.none_is(m, Fs.none_of(key, m, more, ht, e))
  (%em : {N.Acts.nas_to(key, _, more) == [] : List<&2, B.Bytes()>}; e)

# Messages that all go to key, none of them there: none at all.
def Fs.to_key_amute(+key: U32, +acts: List<&2, N.Act>, +ht: {Fs.to_key(key, acts) == True{} : Bool}, +e: {N.Acts.nas(key, acts) == [] : List<&2, B.Bytes()>}) -> {Fs.amute(acts) == True{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      +h1 = P.Bool.and_true_l(Fs.to_key_m(key, N.Act.nas(a)), Fs.to_key(key, more), ht)
      P.Bool.and_intro(Fs.none(N.Act.nas(a)), Fs.amute(more), Fs.none_of(key, N.Act.nas(a), N.Acts.nas(key, more), h1, e), Fs.to_key_amute(key, more, P.Bool.and_true_r(Fs.to_key_m(key, N.Act.nas(a)), Fs.to_key(key, more), ht), Fs.to_nil(key, N.Act.nas(a), N.Acts.nas(key, more), h1, e)))

# What runs a UE's NAS context through parts (Gsm.Item)
# ----------------------------------------------------
# It writes no row; every protected message it carries goes to the UE's key;
# with no context it carries none and leaves none; with one, it leaves one,
# whose keys and downlink COUNT are those its messages, sealed in turn from
# the context's COUNT under its keys, leave (Fs.after).

def Fs.ictx(r: Gsm.Gsm.Item()) -> Maybe<&2, Sec.Nas.Ctx>:
  match r:
    case (c, o):
      c

def Fs.after_run(+k: Sec.Nas.Keys, m: Maybe<&2, Sec.Nas.Count>) -> Maybe<&2, Fs.KD()>:
  match m:
    case None{}:
      None{}
    case Some{d2}:
      Some{(k, d2)}

def Fs.after(c: Maybe<&2, Sec.Nas.Ctx>, +ms: List<&2, B.Bytes()>) -> Maybe<&2, Fs.KD()>:
  match c:
    case None{}:
      None{}
    case Some{Sec.Ctx{+k, +d, u}}:
      Fs.after_run(k, N.Fresh.run(ms, k, d))

def Fs.kept_if(c: Maybe<&2, Sec.Nas.Ctx>, +c2: Maybe<&2, Sec.Nas.Ctx>, +ms: List<&2, B.Bytes()>) -> Bool:
  match c:
    case None{}:
      List.is_empty(&2, B.Bytes(), ms)
    case Some{x}:
      Tb.Table.present(Sec.Nas.Ctx, c2)

def Fs.ii(+key: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +r: Gsm.Gsm.Item()) -> Bool:
  +o = Gsm.Gsm.Item.out(r)
  Bool.and(Fs.tmute(N.Out.tx(o)), Bool.and(Fs.to_key(key, N.Out.acts(o)), Fs.kept_if(c, Fs.ictx(r), N.Acts.nas(key, N.Out.acts(o)))))

def Fs.Ii(+key: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +r: Gsm.Gsm.Item()) -> Type:
  {Fs.ii(key, c, r) == True{} : Bool} & {Fs.view(Fs.ictx(r)) == Fs.after(c, N.Acts.nas(key, N.Out.acts(Gsm.Gsm.Item.out(r)))) : Maybe<&2, Fs.KD()>}

def Fs.empty_is(+ms: List<&2, B.Bytes()>, +h: {List.is_empty(&2, B.Bytes(), ms) == True{} : Bool}) -> {ms == [] : List<&2, B.Bytes()>}:
  match ms:
    case Nil{}:
      {==}
    case m <> more:
      Empty.absurd({m <> more == [] : List<&2, B.Bytes()>}, P.Refute.bool(h))

def Fs.view_none(+m: Maybe<&2, Sec.Nas.Ctx>, +e: {Fs.view(m) == None{} : Maybe<&2, Fs.KD()>}) -> {m == None{} : Maybe<&2, Sec.Nas.Ctx>}:
  match m:
    case None{}:
      {==}
    case Some{Sec.Ctx{k, d, u}}:
      Empty.absurd({Some{Sec.Ctx{k, d, u}} == None{} : Maybe<&2, Sec.Nas.Ctx>}, P.Refute.none_some(Fs.KD(), (k, d), Equal.sym(Maybe<&2, Fs.KD()>, Some{(k, d)}, None{}, e)))

def Fs.after_view(+c1: Maybe<&2, Sec.Nas.Ctx>, +ms: List<&2, B.Bytes()>, +k: Sec.Nas.Keys, +d1: Sec.Nas.Count, +e: {Fs.view(c1) == Some{(k, d1)} : Maybe<&2, Fs.KD()>}) -> {Fs.after(c1, ms) == Fs.after_run(k, N.Fresh.run(ms, k, d1)) : Maybe<&2, Fs.KD()>}:
  match c1:
    case None{}:
      Empty.absurd({Fs.after(None{}, ms) == Fs.after_run(k, N.Fresh.run(ms, k, d1)) : Maybe<&2, Fs.KD()>}, P.Refute.none_some(Fs.KD(), (k, d1), e))
    case Some{Sec.Ctx{+kb, +db, ub}}:
      +se = Equal.sym(Maybe<&2, Fs.KD()>, Some{(kb, db)}, Some{(k, d1)}, e)
      +ek : {kb == k : Sec.Nas.Keys} = (%se : {Fs.kd_keys(_, k) == k : Sec.Nas.Keys}; {==})
      +ed : {db == d1 : Sec.Nas.Count} = (%se : {Fs.kd_dl(_, d1) == d1 : Sec.Nas.Count}; {==})
      +sk = Equal.sym(Sec.Nas.Keys, kb, k, ek)
      +sd = Equal.sym(Sec.Nas.Count, db, d1, ed)
      (%sk : {Fs.after_run(_, N.Fresh.run(ms, _, db)) == Fs.after_run(k, N.Fresh.run(ms, k, d1)) : Maybe<&2, Fs.KD()>}; (%sd : {Fs.after_run(k, N.Fresh.run(ms, k, _)) == Fs.after_run(k, N.Fresh.run(ms, k, d1)) : Maybe<&2, Fs.KD()>}; {==}))

def Fs.after_nil(+c: Maybe<&2, Sec.Nas.Ctx>) -> {Fs.view(c) == Fs.after(c, []) : Maybe<&2, Fs.KD()>}:
  match c:
    case None{}:
      {==}
    case Some{Sec.Ctx{k, d, u}}:
      {==}

def Fs.kept_nil(+c: Maybe<&2, Sec.Nas.Ctx>) -> {Fs.kept_if(c, c, []) == True{} : Bool}:
  match c:
    case None{}:
      {==}
    case Some{x}:
      {==}

# A mute part leaves the context as it found it.
def Fs.ii_mute(+key: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +o: N.GOut(), +hm: {Fs.mute(N.Out.tx(o), N.Out.acts(o)) == True{} : Bool}) -> Fs.Ii(key, c, (c, o)):
  match o:
    case (+tx, +acts):
      +am = P.Bool.and_true_r(Fs.tmute(tx), Fs.amute(acts), hm)
      +sn = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, acts), [], Fs.amute_nas(key, acts, am))
      +hk : {Fs.kept_if(c, c, N.Acts.nas(key, acts)) == True{} : Bool} = (%sn : {Fs.kept_if(c, c, _) == True{} : Bool}; Fs.kept_nil(c))
      +hv : {Fs.view(c) == Fs.after(c, N.Acts.nas(key, acts)) : Maybe<&2, Fs.KD()>} = (%sn : {Fs.view(c) == Fs.after(c, _) : Maybe<&2, Fs.KD()>}; Fs.after_nil(c))
      (P.Bool.and_intro(Fs.tmute(tx), Bool.and(Fs.to_key(key, acts), Fs.kept_if(c, c, N.Acts.nas(key, acts))), P.Bool.and_true_l(Fs.tmute(tx), Fs.amute(acts), hm), P.Bool.and_intro(Fs.to_key(key, acts), Fs.kept_if(c, c, N.Acts.nas(key, acts)), Fs.amute_to_key(key, acts, am), hk)), hv)

# A mute part, then an item.
def Fs.ii_after(+key: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +o: N.GOut(), +r: Gsm.Gsm.Item(), +hm: {Fs.mute(N.Out.tx(o), N.Out.acts(o)) == True{} : Bool}, hr: Fs.Ii(key, c, r)) -> Fs.Ii(key, c, Gsm.Gsm.after(o, r)):
  match o:
    case (+ta, +aa):
      match r:
        case (+c1, +o1):
          match o1:
            case (+tb, +ab):
              match hr:
                case (+h1, +h2):
                  +am = P.Bool.and_true_r(Fs.tmute(ta), Fs.amute(aa), hm)
                  +rest = Bool.and(Fs.to_key(key, ab), Fs.kept_if(c, c1, N.Acts.nas(key, ab)))
                  +sn = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, List.append(&2, N.Act, aa, ab)), N.Acts.nas(key, ab), Fs.nas_mute_l(key, aa, ab, am))
                  +hk = P.Bool.and_true_r(Fs.to_key(key, ab), Fs.kept_if(c, c1, N.Acts.nas(key, ab)), P.Bool.and_true_r(Fs.tmute(tb), rest, h1))
                  +hk2 : {Fs.kept_if(c, c1, N.Acts.nas(key, List.append(&2, N.Act, aa, ab))) == True{} : Bool} = (%sn : {Fs.kept_if(c, c1, _) == True{} : Bool}; hk)
                  +hv : {Fs.view(c1) == Fs.after(c, N.Acts.nas(key, List.append(&2, N.Act, aa, ab))) : Maybe<&2, Fs.KD()>} = (%sn : {Fs.view(c1) == Fs.after(c, _) : Maybe<&2, Fs.KD()>}; h2)
                  +tk = Fs.to_key_app(key, aa, ab, Fs.amute_to_key(key, aa, am), P.Bool.and_true_l(Fs.to_key(key, ab), Fs.kept_if(c, c1, N.Acts.nas(key, ab)), P.Bool.and_true_r(Fs.tmute(tb), rest, h1)))
                  +xs = List.append(&2, N.Act, aa, ab)
                  (P.Bool.and_intro(Bool.and(Fs.tmute(ta), Fs.tmute(tb)), Bool.and(Fs.to_key(key, xs), Fs.kept_if(c, c1, N.Acts.nas(key, xs))), P.Bool.and_intro(Fs.tmute(ta), Fs.tmute(tb), P.Bool.and_true_l(Fs.tmute(ta), Fs.amute(aa), hm), P.Bool.and_true_l(Fs.tmute(tb), rest, h1)), P.Bool.and_intro(Fs.to_key(key, xs), Fs.kept_if(c, c1, N.Acts.nas(key, xs)), tk, hk2)), hv)

def Fs.then_run(+k: Sec.Nas.Keys, +d: Sec.Nas.Count, +c1: Maybe<&2, Sec.Nas.Ctx>, +c2: Maybe<&2, Sec.Nas.Ctx>, +na: List<&2, B.Bytes()>, +nb: List<&2, B.Bytes()>, +m: Maybe<&2, Sec.Nas.Count>, +em: {N.Fresh.run(na, k, d) == m : Maybe<&2, Sec.Nas.Count>}, +hp: {Tb.Table.present(Sec.Nas.Ctx, c1) == True{} : Bool}, +e1: {Fs.view(c1) == Fs.after_run(k, m) : Maybe<&2, Fs.KD()>}, +e2: {Fs.view(c2) == Fs.after(c1, nb) : Maybe<&2, Fs.KD()>}) -> {Fs.view(c2) == Fs.after_run(k, N.Fresh.run(List.append(&2, B.Bytes(), na, nb), k, d)) : Maybe<&2, Fs.KD()>}:
  match m:
    case None{}:
      +ec = Fs.view_none(c1, e1)
      +hn : {Tb.Table.present(Sec.Nas.Ctx, None{}) == True{} : Bool} = (%ec : {Tb.Table.present(Sec.Nas.Ctx, _) == True{} : Bool}; hp)
      Empty.absurd({Fs.view(c2) == Fs.after_run(k, N.Fresh.run(List.append(&2, B.Bytes(), na, nb), k, d)) : Maybe<&2, Fs.KD()>}, P.Refute.bool(hn))
    case Some{+d1}:
      +ea = Fs.after_view(c1, nb, k, d1, e1)
      +er = Fs.run_app(na, nb, k, d, d1, em)
      +sr = Equal.sym(Maybe<&2, Sec.Nas.Count>, N.Fresh.run(List.append(&2, B.Bytes(), na, nb), k, d), N.Fresh.run(nb, k, d1), er)
      (%sr : {Fs.view(c2) == Fs.after_run(k, _) : Maybe<&2, Fs.KD()>}; Equal.trans(Maybe<&2, Fs.KD()>, Fs.view(c2), Fs.after(c1, nb), Fs.after_run(k, N.Fresh.run(nb, k, d1)), e2, ea))

def Fs.kept_some(+c1: Maybe<&2, Sec.Nas.Ctx>, +c2: Maybe<&2, Sec.Nas.Ctx>, +nb: List<&2, B.Bytes()>, +hp: {Tb.Table.present(Sec.Nas.Ctx, c1) == True{} : Bool}, +h: {Fs.kept_if(c1, c2, nb) == True{} : Bool}) -> {Tb.Table.present(Sec.Nas.Ctx, c2) == True{} : Bool}:
  match c1:
    case None{}:
      Empty.absurd({Tb.Table.present(Sec.Nas.Ctx, c2) == True{} : Bool}, P.Refute.bool(hp))
    case Some{y}:
      h

def Fs.then2(+key: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +c1: Maybe<&2, Sec.Nas.Ctx>, +o1: N.GOut(), +r2: Gsm.Gsm.Item(), hr: Fs.Ii(key, c, (c1, o1)), h2: Fs.Ii(key, c1, r2)) -> Fs.Ii(key, c, Gsm.Gsm.after(o1, r2)):
  match c:
    case None{}:
      match o1:
        case (+ta, +aa):
          match r2:
            case (+c2, +o2):
              match o2:
                case (+tb, +ab):
                  match hr:
                    case (+h1, +v1):
                      match h2:
                        case (+g1, +v2):
                          +ra = Bool.and(Fs.to_key(key, aa), Fs.kept_if(None{}, c1, N.Acts.nas(key, aa)))
                          +na0 = Fs.empty_is(N.Acts.nas(key, aa), P.Bool.and_true_r(Fs.to_key(key, aa), Fs.kept_if(None{}, c1, N.Acts.nas(key, aa)), P.Bool.and_true_r(Fs.tmute(ta), ra, h1)))
                          +ec1 = Fs.view_none(c1, v1)
                          +g1n : {Fs.ii(key, None{}, (c2, (tb, ab))) == True{} : Bool} = (%ec1 : {Fs.ii(key, _, (c2, (tb, ab))) == True{} : Bool}; g1)
                          +v2n : {Fs.view(c2) == None{} : Maybe<&2, Fs.KD()>} = (%ec1 : {Fs.view(c2) == Fs.after(_, N.Acts.nas(key, ab)) : Maybe<&2, Fs.KD()>}; v2)
                          +rb = Bool.and(Fs.to_key(key, ab), Fs.kept_if(None{}, c2, N.Acts.nas(key, ab)))
                          +nb0 = Fs.empty_is(N.Acts.nas(key, ab), P.Bool.and_true_r(Fs.to_key(key, ab), Fs.kept_if(None{}, c2, N.Acts.nas(key, ab)), P.Bool.and_true_r(Fs.tmute(tb), rb, g1n)))
                          +xs = List.append(&2, N.Act, aa, ab)
                          +en = Equal.trans(List<&2, B.Bytes()>, N.Acts.nas(key, xs), List.append(&2, B.Bytes(), N.Acts.nas(key, aa), N.Acts.nas(key, ab)), [], Fs.nas_app(key, aa, ab), (%Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, aa), [], na0) : {List.append(&2, B.Bytes(), _, N.Acts.nas(key, ab)) == [] : List<&2, B.Bytes()>}; nb0))
                          +sen = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, xs), [], en)
                          +hk : {Fs.kept_if(None{}, c2, N.Acts.nas(key, xs)) == True{} : Bool} = (%sen : {Fs.kept_if(None{}, c2, _) == True{} : Bool}; {==})
                          +tk = Fs.to_key_app(key, aa, ab, P.Bool.and_true_l(Fs.to_key(key, aa), Fs.kept_if(None{}, c1, N.Acts.nas(key, aa)), P.Bool.and_true_r(Fs.tmute(ta), ra, h1)), P.Bool.and_true_l(Fs.to_key(key, ab), Fs.kept_if(None{}, c2, N.Acts.nas(key, ab)), P.Bool.and_true_r(Fs.tmute(tb), rb, g1n)))
                          (P.Bool.and_intro(Bool.and(Fs.tmute(ta), Fs.tmute(tb)), Bool.and(Fs.to_key(key, xs), Fs.kept_if(None{}, c2, N.Acts.nas(key, xs))), P.Bool.and_intro(Fs.tmute(ta), Fs.tmute(tb), P.Bool.and_true_l(Fs.tmute(ta), ra, h1), P.Bool.and_true_l(Fs.tmute(tb), rb, g1n)), P.Bool.and_intro(Fs.to_key(key, xs), Fs.kept_if(None{}, c2, N.Acts.nas(key, xs)), tk, hk)), v2n)
    case Some{Sec.Ctx{+k, +d, +u}}:
      match o1:
        case (+ta, +aa):
          match r2:
            case (+c2, +o2):
              match o2:
                case (+tb, +ab):
                  match hr:
                    case (+h1, +v1):
                      match h2:
                        case (+g1, +v2):
                          +c0 : Maybe<&2, Sec.Nas.Ctx> = Some{Sec.Ctx{k, d, u}}
                          +ra = Bool.and(Fs.to_key(key, aa), Fs.kept_if(c0, c1, N.Acts.nas(key, aa)))
                          +rb = Bool.and(Fs.to_key(key, ab), Fs.kept_if(c1, c2, N.Acts.nas(key, ab)))
                          +hp1 = P.Bool.and_true_r(Fs.to_key(key, aa), Fs.kept_if(c0, c1, N.Acts.nas(key, aa)), P.Bool.and_true_r(Fs.tmute(ta), ra, h1))
                          +hp2 = Fs.kept_some(c1, c2, N.Acts.nas(key, ab), hp1, P.Bool.and_true_r(Fs.to_key(key, ab), Fs.kept_if(c1, c2, N.Acts.nas(key, ab)), P.Bool.and_true_r(Fs.tmute(tb), rb, g1)))
                          +xs = List.append(&2, N.Act, aa, ab)
                          +tk = Fs.to_key_app(key, aa, ab, P.Bool.and_true_l(Fs.to_key(key, aa), Fs.kept_if(c0, c1, N.Acts.nas(key, aa)), P.Bool.and_true_r(Fs.tmute(ta), ra, h1)), P.Bool.and_true_l(Fs.to_key(key, ab), Fs.kept_if(c1, c2, N.Acts.nas(key, ab)), P.Bool.and_true_r(Fs.tmute(tb), rb, g1)))
                          +vr = Fs.then_run(k, d, c1, c2, N.Acts.nas(key, aa), N.Acts.nas(key, ab), N.Fresh.run(N.Acts.nas(key, aa), k, d), {==}, hp1, v1, v2)
                          +sap = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, xs), List.append(&2, B.Bytes(), N.Acts.nas(key, aa), N.Acts.nas(key, ab)), Fs.nas_app(key, aa, ab))
                          +hv : {Fs.view(c2) == Fs.after(c0, N.Acts.nas(key, xs)) : Maybe<&2, Fs.KD()>} = (%sap : {Fs.view(c2) == Fs.after_run(k, N.Fresh.run(_, k, d)) : Maybe<&2, Fs.KD()>}; vr)
                          (P.Bool.and_intro(Bool.and(Fs.tmute(ta), Fs.tmute(tb)), Bool.and(Fs.to_key(key, xs), Fs.kept_if(c0, c2, N.Acts.nas(key, xs))), P.Bool.and_intro(Fs.tmute(ta), Fs.tmute(tb), P.Bool.and_true_l(Fs.tmute(ta), ra, h1), P.Bool.and_true_l(Fs.tmute(tb), rb, g1)), P.Bool.and_intro(Fs.to_key(key, xs), Fs.kept_if(c0, c2, N.Acts.nas(key, xs)), tk, hp2)), hv)

def Fs.ii_then(+key: U32, +c: Maybe<&2, Sec.Nas.Ctx>, +r: Gsm.Gsm.Item(), rest: Maybe<&2, Sec.Nas.Ctx> -> Gsm.Gsm.Item(), hr: Fs.Ii(key, c, r), hrest: @c2:Maybe<&2, Sec.Nas.Ctx> -> Fs.Ii(key, c2, rest(c2))) -> Fs.Ii(key, c, Gsm.Gsm.then(r, rest)):
  match r:
    case (+c1, +o1):
      Fs.then2(key, c, c1, o1, rest(c1), hr, hrest(c1))

# One message to key under the context, then a mute part.
def Fs.told_ii(+key: U32, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +prot: Sec.Nas.Protection, +plain: B.Bytes(), +x: N.Act, +ex: {N.Act.nas(x) == Some{(key, Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, prot, plain)))} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, +o: N.GOut(), +hm: {Fs.mute(N.Out.tx(o), N.Out.acts(o)) == True{} : Bool}) -> Fs.Ii(key, Some{Sec.Ctx{k, d, ul}}, (Some{Sec.Ctx{k, Sec.Nas.Count.next(d), ul}}, N.Out.join((S.Keep{}, [x]), o))):
  match o:
    case (+tb, +ab):
      +m = Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, prot, plain))
      +am = P.Bool.and_true_r(Fs.tmute(tb), Fs.amute(ab), hm)
      +sx = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, N.Act.nas(x), Some{(key, m)}, ex)
      +tx1 : {Fs.to_key_m(key, N.Act.nas(x)) == True{} : Bool} = (%sx : {Fs.to_key_m(key, _) == True{} : Bool}; P.U32.is_eq_refl(key))
      +en = Equal.trans(List<&2, B.Bytes()>, N.Acts.nas(key, x <> ab), m <> N.Acts.nas(key, ab), [m], Fs.one_nas(key, x, m, ab, ex), (%Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, ab), [], Fs.amute_nas(key, ab, am)) : {m <> _ == [m] : List<&2, B.Bytes()>}; {==}))
      +sen = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, x <> ab), [m], en)
      +sr = Equal.sym(Maybe<&2, Sec.Nas.Count>, N.Fresh.run([m], k, d), Some{Sec.Nas.Count.next(d)}, Fs.protect_run(k, d, ul, prot, plain))
      +hv : {Some{(k, Sec.Nas.Count.next(d))} == Fs.after(Some{Sec.Ctx{k, d, ul}}, N.Acts.nas(key, x <> ab)) : Maybe<&2, Fs.KD()>} = (%sen : {Some{(k, Sec.Nas.Count.next(d))} == Fs.after(Some{Sec.Ctx{k, d, ul}}, _) : Maybe<&2, Fs.KD()>}; (%sr : {Some{(k, Sec.Nas.Count.next(d))} == Fs.after_run(k, _) : Maybe<&2, Fs.KD()>}; {==}))
      (P.Bool.and_intro(Fs.tmute(tb), Bool.and(Fs.to_key(key, x <> ab), True{}), P.Bool.and_true_l(Fs.tmute(tb), Fs.amute(ab), hm), P.Bool.and_intro(Fs.to_key(key, x <> ab), True{}, P.Bool.and_intro(Fs.to_key_m(key, N.Act.nas(x)), Fs.to_key(key, ab), tx1, Fs.amute_to_key(key, ab, am)), {==})), hv)

# A session given up, under whatever context runs through it.
def Fs.give_up_ii(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, +t: Gsm.Tell, +seq: U32, +c: Maybe<&2, Sec.Nas.Ctx>) -> Fs.Ii(key, c, Gsm.Gsm.give_up_in(key, ue, skey, s, t, seq, c)):
  match t:
    case Gsm.Reply{+sm}:
      match c:
        case None{}:
          Fs.ii_mute(key, None{}, Up.N4.deletions([(skey, s)], seq), Fs.deletions_mute([(skey, s)], seq))
        case Some{Sec.Ctx{+k, +d, +ul}}:
          +plain = Gsm.Gsm.dl_transport(S.Session.psi(s), sm)
          +m = Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, Sec.Ciphered{}, plain))
          Fs.told_ii(key, k, d, ul, Sec.Ciphered{}, plain, N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), m}, Fs.dl_carries(S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), m, Fs.protect_protected(k, d, ul, Sec.Ciphered{}, plain)), Up.N4.deletions([(skey, s)], seq), Fs.deletions_mute([(skey, s)], seq))
    case Gsm.Release{}:
      match c:
        case None{}:
          Fs.ii_mute(key, None{}, Up.N4.deletions([(skey, s)], seq), Fs.deletions_mute([(skey, s)], seq))
        case Some{Sec.Ctx{+k, +d, +ul}}:
          +psi = S.Session.psi(s)
          +plain = Gsm.Gsm.dl_transport(psi, Gsm.Gsm.release_command(psi))
          +m = Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, Sec.Ciphered{}, plain))
          Fs.told_ii(key, k, d, ul, Sec.Ciphered{}, plain, N.PduRelease{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), psi, m}, Fs.release_carries(S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), psi, m, Fs.protect_protected(k, d, ul, Sec.Ciphered{}, plain)), Up.N4.deletions([(skey, s)], seq), Fs.deletions_mute([(skey, s)], seq))

# The context a phase has in force is one it holds.
def Fs.nas_of_ctx(+q: S.Phase, +c: Sec.Nas.Ctx, +e: {S.Phase.ctx(q) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}) -> {S.Phase.nas(q) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}:
  match q:
    case S.Handover{ctx, nh, source, leg}:
      Empty.absurd({S.Phase.nas(S.Handover{ctx, nh, source, leg}) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, P.Refute.none_some(Sec.Nas.Ctx, c, e))
    case S.Created{}:
      e
    case S.Identifying{guard}:
      e
    case S.Authenticating{guard, av, resynced, supi}:
      e
    case S.SecurityMode{guard, ctx, k_amf}:
      e
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      e
    case S.Registered{ctx, nh, released}:
      e
    case S.Switching{guard, ctx, nh, released}:
      e
    case S.Releasing{guard}:
      e

def Fs.ctx_of(+st: S.State, +key: U32, +ue: S.Ue, +c: Sec.Nas.Ctx, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {S.Phase.ctx(S.Ue.phase(ue)) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}) -> {Fs.ctx(st, key) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}:
  +sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, S.State.ues(st)), Some{ue}, eg)
  (%sg : {S.Ue.nas(_) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}; Fs.nas_of_ctx(S.Ue.phase(ue), c, ec))

# Messages sealed in turn from the key's COUNT, the COUNT after them written.
def Fs.holds_run(+b: Maybe<&2, Sec.Nas.Ctx>, +k: Sec.Nas.Keys, +d0: Sec.Nas.Count, +dn: Sec.Nas.Count, +un: Maybe<&2, Sec.Nas.Count>, +ms: List<&2, B.Bytes()>, +eb: {Fs.view(b) == Some{(k, d0)} : Maybe<&2, Fs.KD()>}, +er: {N.Fresh.run(ms, k, d0) == Some{dn} : Maybe<&2, Sec.Nas.Count>}) -> {N.Fresh.holds(b, Some{Sec.Ctx{k, dn, un}}, ms) == True{} : Bool}:
  +sd = Equal.sym(Sec.Nas.Count, N.Fresh.start(b, k), d0, Fs.start_view(b, k, d0, eb))
  +sr = Equal.sym(Maybe<&2, Sec.Nas.Count>, N.Fresh.run(ms, k, d0), Some{dn}, er)
  (%sd : {N.Fresh.at(N.Fresh.run(ms, k, _), dn) == True{} : Bool}; (%sr : {N.Fresh.at(_, dn) == True{} : Bool}; Fs.count_same(dn)))

def Fs.pair_l(-A: Type, -B: Type, pr: A & B) -> A:
  match pr:
    case (a, b):
      a

def Fs.pair_r(-A: Type, -B: Type, pr: A & B) -> B:
  match pr:
    case (a, b):
      b

def Fs.run_of_view(+k: Sec.Nas.Keys, +k1: Sec.Nas.Keys, +d1: Sec.Nas.Count, +m: Maybe<&2, Sec.Nas.Count>, +e: {Some{(k1, d1)} == Fs.after_run(k, m) : Maybe<&2, Fs.KD()>}) -> {m == Some{d1} : Maybe<&2, Sec.Nas.Count>} & {k1 == k : Sec.Nas.Keys}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{d1} : Maybe<&2, Sec.Nas.Count>} & {k1 == k : Sec.Nas.Keys}, P.Refute.none_some(Fs.KD(), (k1, d1), Equal.sym(Maybe<&2, Fs.KD()>, Some{(k1, d1)}, None{}, e)))
    case Some{+d2}:
      +ek : {k1 == k : Sec.Nas.Keys} = (%e : {Fs.kd_keys(Some{(k1, d1)}, k) == Fs.kd_keys(_, k) : Sec.Nas.Keys}; {==})
      +ed : {d1 == d2 : Sec.Nas.Count} = (%e : {Fs.kd_dl(Some{(k1, d1)}, d1) == Fs.kd_dl(_, d1) : Sec.Nas.Count}; {==})
      ((%ed : {Some{_} == Some{d1} : Maybe<&2, Sec.Nas.Count>}; {==}), ek)

# The context the items leave, written once after them.
def Fs.settled_c(+st: S.State, +key: U32, +ue: S.Ue, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +u: Maybe<&2, Sec.Nas.Count>, +c1: Maybe<&2, Sec.Nas.Ctx>, +tb: S.Tx, +ab: List<&2, N.Act>, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ex: {S.Phase.ctx(S.Ue.phase(ue)) == Some{Sec.Ctx{k, d, u}} : Maybe<&2, Sec.Nas.Ctx>}, +h1: {Fs.ii(key, Some{Sec.Ctx{k, d, u}}, (c1, (tb, ab))) == True{} : Bool}, +v1: {Fs.view(c1) == Fs.after(Some{Sec.Ctx{k, d, u}}, N.Acts.nas(key, ab)) : Maybe<&2, Fs.KD()>}) -> {Fs.nas(st, N.Out.tx(Gsm.Gsm.settled(key, ue, (c1, (tb, ab)))), N.Out.acts(Gsm.Gsm.settled(key, ue, (c1, (tb, ab))))) == True{} : Bool}:
  match c1:
    case None{}:
      Empty.absurd({Fs.nas(st, N.Out.tx(Gsm.Gsm.settled(key, ue, (None{}, (tb, ab)))), N.Out.acts(Gsm.Gsm.settled(key, ue, (None{}, (tb, ab))))) == True{} : Bool}, P.Refute.bool(P.Bool.and_true_r(Fs.to_key(key, ab), False{}, P.Bool.and_true_r(Fs.tmute(tb), Bool.and(Fs.to_key(key, ab), False{}), h1))))
    case Some{Sec.Ctx{+k1, +d1, +u1}}:
      +ms = N.Acts.nas(key, ab)
      +rest = Bool.and(Fs.to_key(key, ab), True{})
      +tm = P.Bool.and_true_l(Fs.tmute(tb), rest, h1)
      +tk = P.Bool.and_true_l(Fs.to_key(key, ab), True{}, P.Bool.and_true_r(Fs.tmute(tb), rest, h1))
      +q1 = S.Phase.with_ctx(S.Ue.phase(ue), Sec.Ctx{k1, d1, u1})
      +hp : {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(S.Ue.phase(ue))) == True{} : Bool} = (%Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.ctx(S.Ue.phase(ue)), Some{Sec.Ctx{k, d, u}}, ex) : {Tb.Table.present(Sec.Nas.Ctx, _) == True{} : Bool}; {==})
      +er = Fs.pair_l({N.Fresh.run(ms, k, d) == Some{d1} : Maybe<&2, Sec.Nas.Count>}, {k1 == k : Sec.Nas.Keys}, Fs.run_of_view(k, k1, d1, N.Fresh.run(ms, k, d), v1))
      +ek = Fs.pair_r({N.Fresh.run(ms, k, d) == Some{d1} : Maybe<&2, Sec.Nas.Count>}, {k1 == k : Sec.Nas.Keys}, Fs.run_of_view(k, k1, d1, N.Fresh.run(ms, k, d), v1))
      +sk = Equal.sym(Sec.Nas.Keys, k1, k, ek)
      +eb = Fs.ctx_of(st, key, ue, Sec.Ctx{k, d, u}, eg, ex)
      +sb = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, Fs.ctx(st, key), Some{Sec.Ctx{k, d, u}}, eb)
      +sq = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.nas(q1), Some{Sec.Ctx{k1, d1, u1}}, Fs.nas_with(S.Ue.phase(ue), Sec.Ctx{k1, d1, u1}, hp))
      +hw : {Fs.write(st, key, S.Phase.nas(q1), ab) == True{} : Bool} = (%sq : {N.Fresh.holds(Fs.ctx(st, key), _, ms) == True{} : Bool}; (%sb : {N.Fresh.holds(_, Some{Sec.Ctx{k1, d1, u1}}, ms) == True{} : Bool}; (%sk : {N.Fresh.holds(Some{Sec.Ctx{k, d, u}}, Some{Sec.Ctx{_, d1, u1}}, ms) == True{} : Bool}; Fs.holds_run(Some{Sec.Ctx{k, d, u}}, k, d, d1, u1, ms, {==}, er))))
      +tx : S.Tx = S.Both{S.Rephase{key, q1}, tb}
      P.Bool.and_intro(Fs.sealed(st, tx, ab), Fs.sends(tx, ab), P.Bool.and_intro(Fs.write(st, key, S.Phase.nas(q1), ab), Fs.sealed(st, tb, ab), hw, Fs.tmute_sealed(st, tb, ab, tm)), Fs.to_key_sends(key, tx, ab, tk, P.Bool.or_l(U32.is_eq(key, key), Fs.writes(key, tb), P.U32.is_eq_refl(key))))

def Fs.settled_nas(+st: S.State, +key: U32, +ue: S.Ue, +x: Sec.Nas.Ctx, +r: Gsm.Gsm.Item(), +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ex: {S.Phase.ctx(S.Ue.phase(ue)) == Some{x} : Maybe<&2, Sec.Nas.Ctx>}, hr: Fs.Ii(key, Some{x}, r)) -> {Fs.nas(st, N.Out.tx(Gsm.Gsm.settled(key, ue, r)), N.Out.acts(Gsm.Gsm.settled(key, ue, r))) == True{} : Bool}:
  match x:
    case Sec.Ctx{+k, +d, +u}:
      match r:
        case (+c1, +o1):
          match o1:
            case (+tb, +ab):
              match hr:
                case (+h1, +v1):
                  Fs.settled_c(st, key, ue, k, d, u, c1, tb, ab, eg, ex, h1, v1)

# With no context, the items carry no message and write nothing.
def Fs.none_nas(+st: S.State, +key: U32, +r: Gsm.Gsm.Item(), hr: Fs.Ii(key, None{}, r)) -> {Fs.nas(st, N.Out.tx(Gsm.Gsm.Item.out(r)), N.Out.acts(Gsm.Gsm.Item.out(r))) == True{} : Bool}:
  match r:
    case (+c1, +o1):
      match o1:
        case (+tb, +ab):
          match hr:
            case (+h1, +v1):
              +rest = Bool.and(Fs.to_key(key, ab), List.is_empty(&2, B.Bytes(), N.Acts.nas(key, ab)))
              +tm = P.Bool.and_true_l(Fs.tmute(tb), rest, h1)
              +tk = P.Bool.and_true_l(Fs.to_key(key, ab), List.is_empty(&2, B.Bytes(), N.Acts.nas(key, ab)), P.Bool.and_true_r(Fs.tmute(tb), rest, h1))
              +en = Fs.empty_is(N.Acts.nas(key, ab), P.Bool.and_true_r(Fs.to_key(key, ab), List.is_empty(&2, B.Bytes(), N.Acts.nas(key, ab)), P.Bool.and_true_r(Fs.tmute(tb), rest, h1)))
              +am = Fs.to_key_amute(key, ab, tk, en)
              P.Bool.and_intro(Fs.sealed(st, tb, ab), Fs.sends(tb, ab), Fs.tmute_sealed(st, tb, ab, tm), Fs.amute_sends(tb, ab, am))

def Fs.under_ctx_nas(+st: S.State, +key: U32, +ue: S.Ue, f: Maybe<&2, Sec.Nas.Ctx> -> Gsm.Gsm.Item(), +c0: Maybe<&2, Sec.Nas.Ctx>, +e0: {S.Phase.ctx(S.Ue.phase(ue)) == c0 : Maybe<&2, Sec.Nas.Ctx>}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, hf: @c:Maybe<&2, Sec.Nas.Ctx> -> Fs.Ii(key, c, f(c))) -> {Fs.nas(st, N.Out.tx(Gsm.Gsm.under_ctx(key, ue, f, c0)), N.Out.acts(Gsm.Gsm.under_ctx(key, ue, f, c0))) == True{} : Bool}:
  match c0:
    case None{}:
      Fs.none_nas(st, key, f(None{}), hf(None{}))
    case Some{+x}:
      Fs.settled_nas(st, key, ue, x, f(Some{x}), eg, e0, hf(Some{x}))

# What f does under the UE's NAS context, the context it leaves written once:
# nas_sec.downlink_fresh's part of the outcome.
def Fs.under_nas(+st: S.State, +key: U32, +ue: S.Ue, f: Maybe<&2, Sec.Nas.Ctx> -> Gsm.Gsm.Item(), +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, hf: @c:Maybe<&2, Sec.Nas.Ctx> -> Fs.Ii(key, c, f(c))) -> {Fs.nas(st, N.Out.tx(Gsm.Gsm.under(key, ue, f)), N.Out.acts(Gsm.Gsm.under(key, ue, f))) == True{} : Bool}:
  Fs.under_ctx_nas(st, key, ue, f, S.Phase.ctx(S.Ue.phase(ue)), {==}, eg, hf)

# A context with the stored one's keys and COUNT written back, no message.
def Fs.kept_any(+st: S.State, +key: U32, +q: S.Phase, +c: Sec.Nas.Ctx, +eq: {S.Phase.nas(q) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, +ev: {Fs.view(Fs.ctx(st, key)) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}) -> {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(q), []) == True{} : Bool}:
  match c:
    case Sec.Ctx{+k, +d, +ul}:
      Fs.kept_holds(st, key, q, k, d, ul, eq, ev)

# The stored context, read off the UE's phase.
def Fs.view_of(+st: S.State, +key: U32, +ue: S.Ue, +c: Sec.Nas.Ctx, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {S.Phase.ctx(S.Ue.phase(ue)) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}) -> {Fs.view(Fs.ctx(st, key)) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}:
  +sc = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, Fs.ctx(st, key), Some{c}, Fs.ctx_of(st, key, ue, c, eg, ec))
  (%sc : {Fs.view(_) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}; {==})

def Fs.present_of(+q: S.Phase, +c: Sec.Nas.Ctx, +ec: {S.Phase.ctx(q) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}) -> {Tb.Table.present(Sec.Nas.Ctx, S.Phase.ctx(q)) == True{} : Bool}:
  +sc = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.ctx(q), Some{c}, ec)
  (%sc : {Tb.Table.present(Sec.Nas.Ctx, _) == True{} : Bool}; {==})

def Fs.protected_any(+c: Sec.Nas.Ctx, +prot: Sec.Nas.Protection, +plain: B.Bytes()) -> {Sec.Nas.is_protected(Sec.Nas.Protected.msg(Sec.Nas.protect(c, prot, plain))) == True{} : Bool}:
  match c:
    case Sec.Ctx{+k, +d, +ul}:
      Fs.protect_protected(k, d, ul, prot, plain)

# One protected message under the context the UE's phase holds, then an
# action carrying none, the context moved on written and a transaction that
# writes no row.
def Fs.told_pair(+st: S.State, +key: U32, +ue: S.Ue, +c: Sec.Nas.Ctx, +prot: Sec.Nas.Protection, +plain: B.Bytes(), +x: N.Act, +y: N.Act, +r: S.Tx, +ex: {N.Act.nas(x) == Some{(key, Sec.Nas.Protected.msg(Sec.Nas.protect(c, prot, plain)))} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, +ey: {Fs.none(N.Act.nas(y)) == True{} : Bool}, +hr: {Fs.tmute(r) == True{} : Bool}, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ec: {S.Phase.ctx(S.Ue.phase(ue)) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}) -> {Fs.nas(st, S.Both{S.Rephase{key, S.Phase.with_ctx(S.Ue.phase(ue), Sec.Nas.Protected.ctx(Sec.Nas.protect(c, prot, plain)))}, r}, [x, y]) == True{} : Bool}:
  match c:
    case Sec.Ctx{+k, +d, +ul}:
      +c0 : Sec.Nas.Ctx = Sec.Ctx{k, d, ul}
      +c2 : Sec.Nas.Ctx = Sec.Ctx{k, Sec.Nas.Count.next(d), ul}
      +q = S.Phase.with_ctx(S.Ue.phase(ue), c2)
      +hl = Fs.told_leaf(st, key, q, k, d, ul, prot, plain, x, ex, Fs.nas_with(S.Ue.phase(ue), c2, Fs.present_of(S.Ue.phase(ue), c0, ec)), Fs.view_of(st, key, ue, c0, eg, ec))
      Fs.post_tmute(st, S.Rephase{key, q}, r, [x, y], hr, Fs.app_mute(st, S.Rephase{key, q}, [x], [y], hl, P.Bool.and_intro(Fs.none(N.Act.nas(y)), True{}, ey, {==})))

# A plain NAS message is no protected one.
def Fs.plain_none(+key: U32, +nas: B.Bytes(), +e: {Sec.Nas.is_protected(nas) == False{} : Bool}) -> {Fs.none(N.Act.nas_if(key, nas, Sec.Nas.is_protected(nas))) == True{} : Bool}:
  +se = Equal.sym(Bool, Sec.Nas.is_protected(nas), False{}, e)
  (%se : {Fs.none(N.Act.nas_if(key, nas, _)) == True{} : Bool}; {==})

# A context put, mute deletions before it and mute evictions after, then a
# protected message to its key and an action carrying none.
def Fs.place_told(+st: S.State, +key: U32, +ue2: S.Ue, +del: N.GOut(), +ev: List<&2, N.Act>, +x: N.Act, +y: N.Act, +m: B.Bytes(), +hdel: {Fs.mute(N.Out.tx(del), N.Out.acts(del)) == True{} : Bool}, +hev: {Fs.amute(ev) == True{} : Bool}, +hy: {Fs.none(N.Act.nas(y)) == True{} : Bool}, +ex: {N.Act.nas(x) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, +hw: {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(S.Ue.phase(ue2)), [m]) == True{} : Bool}) -> {Fs.nas(st, N.Out.tx(N.Out.also(N.Out.join(del, (S.Put{key, ue2}, ev)), [x, y])), N.Out.acts(N.Out.also(N.Out.join(del, (S.Put{key, ue2}, ev)), [x, y]))) == True{} : Bool}:
  match del:
    case (+td, +ad):
      +pre = List.append(&2, N.Act, ad, ev)
      +acts = List.append(&2, N.Act, pre, [x, y])
      +tx : S.Tx = S.Both{td, S.Put{key, ue2}}
      +tm = P.Bool.and_true_l(Fs.tmute(td), Fs.amute(ad), hdel)
      +am = Fs.amute_app(ad, ev, P.Bool.and_true_r(Fs.tmute(td), Fs.amute(ad), hdel), hev)
      +e1 = Fs.nas_mute_l(key, pre, [x, y], am)
      +e2 = Fs.one_nas(key, x, m, [y], ex)
      +e3 : {m <> N.Acts.nas(key, [y]) == [m] : List<&2, B.Bytes()>} = (%Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, [y]), [], Fs.to_none(key, N.Act.nas(y), [], hy)) : {m <> _ == [m] : List<&2, B.Bytes()>}; {==})
      +en = Equal.trans(List<&2, B.Bytes()>, N.Acts.nas(key, acts), N.Acts.nas(key, [x, y]), [m], e1, Equal.trans(List<&2, B.Bytes()>, N.Acts.nas(key, [x, y]), m <> N.Acts.nas(key, [y]), [m], e2, e3))
      +sen = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, acts), [m], en)
      +hw2 : {Fs.write(st, key, S.Phase.nas(S.Ue.phase(ue2)), acts) == True{} : Bool} = (%sen : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(S.Ue.phase(ue2)), _) == True{} : Bool}; hw)
      +sx = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, N.Act.nas(x), Some{(key, m)}, ex)
      +hsx : {Fs.sent(tx, N.Act.nas(x)) == True{} : Bool} = (%sx : {Fs.sent(tx, _) == True{} : Bool}; P.Bool.or_r(Fs.writes(key, td), U32.is_eq(key, key), P.U32.is_eq_refl(key)))
      +hs2 = P.Bool.and_intro(Fs.sent(tx, N.Act.nas(x)), Fs.sends(tx, [y]), hsx, P.Bool.and_intro(Fs.sent(tx, N.Act.nas(y)), True{}, Fs.none_sent(tx, N.Act.nas(y), hy), {==}))
      P.Bool.and_intro(Fs.sealed(st, tx, acts), Fs.sends(tx, acts), P.Bool.and_intro(Fs.sealed(st, td, acts), Fs.write(st, key, S.Phase.nas(S.Ue.phase(ue2)), acts), Fs.tmute_sealed(st, td, acts, tm), hw2), Fs.sends_app(tx, pre, [x, y], Fs.amute_sends(tx, pre, am), hs2))

# A first context, its Security Mode Command under COUNT 0.
def Fs.smc_holds(+b: Maybe<&2, Sec.Nas.Ctx>, +k: Sec.Nas.Keys, +plain: B.Bytes(), +eb: {b == None{} : Maybe<&2, Sec.Nas.Ctx>}) -> {N.Fresh.holds(b, Some{Sec.Ctx{k, Sec.Nas.Count.next(Sec.Nas.Count.zero()), None{}}}, [Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, Sec.Nas.Count.zero(), None{}}, Sec.IntegrityNew{}, plain))]) == True{} : Bool}:
  +sb = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, b, None{}, eb)
  +ms : List<&2, B.Bytes()> = [Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, Sec.Nas.Count.zero(), None{}}, Sec.IntegrityNew{}, plain))]
  +sr = Equal.sym(Maybe<&2, Sec.Nas.Count>, N.Fresh.run(ms, k, Sec.Nas.Count.zero()), Some{Sec.Nas.Count.next(Sec.Nas.Count.zero())}, Fs.protect_run(k, Sec.Nas.Count.zero(), None{}, Sec.IntegrityNew{}, plain))
  (%sb : {N.Fresh.holds(_, Some{Sec.Ctx{k, Sec.Nas.Count.next(Sec.Nas.Count.zero()), None{}}}, ms) == True{} : Bool}; (%sr : {N.Fresh.at(_, Sec.Nas.Count.next(Sec.Nas.Count.zero())) == True{} : Bool}; Fs.count_same(Sec.Nas.Count.next(Sec.Nas.Count.zero()))))

# The UE's phase read under its key.
def Fs.ctx_phase(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == p : S.Phase}) -> {Fs.ctx(st, key) == S.Phase.nas(p) : Maybe<&2, Sec.Nas.Ctx>}:
  +sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, S.State.ues(st)), Some{ue}, eg)
  (%sg : {S.Ue.nas(_) == S.Phase.nas(p) : Maybe<&2, Sec.Nas.Ctx>}; (%Equal.sym(S.Phase, S.Ue.phase(ue), p, ep) : {S.Phase.nas(_) == S.Phase.nas(p) : Maybe<&2, Sec.Nas.Ctx>}; {==}))

def Fs.view_at(+st: S.State, +key: U32, +ue: S.Ue, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +ep: {S.Ue.phase(ue) == p : S.Phase}) -> {Fs.view(Fs.ctx(st, key)) == Fs.view(S.Phase.nas(p)) : Maybe<&2, Fs.KD()>}:
  +sc = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, Fs.ctx(st, key), S.Phase.nas(p), Fs.ctx_phase(st, key, ue, p, eg, ep))
  (%sc : {Fs.view(_) == Fs.view(S.Phase.nas(p)) : Maybe<&2, Fs.KD()>}; {==})

# Fs.both, on outcomes.
def Fs.both_out(+st: S.State, +a: N.GOut(), +b: N.GOut(), +ha: {Fs.nas(st, N.Out.tx(a), N.Out.acts(a)) == True{} : Bool}, +hb: {Fs.nas(st, N.Out.tx(b), N.Out.acts(b)) == True{} : Bool}, +hq: {Bool.or(Fs.mute(N.Out.tx(a), N.Out.acts(a)), Fs.mute(N.Out.tx(b), N.Out.acts(b))) == True{} : Bool}) -> {Fs.nas(st, N.Out.tx(N.Out.join(a, b)), N.Out.acts(N.Out.join(a, b))) == True{} : Bool}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          Fs.both(st, ta, aa, tb, ab, ha, hb, hq)

# One message protected under a context with the stored one's keys and
# COUNT, the context it leaves written.
def Fs.told_any(+b: Maybe<&2, Sec.Nas.Ctx>, +c: Sec.Nas.Ctx, +prot: Sec.Nas.Protection, +plain: B.Bytes(), +ev: {Fs.view(b) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}) -> {N.Fresh.holds(b, Some{Sec.Nas.Protected.ctx(Sec.Nas.protect(c, prot, plain))}, [Sec.Nas.Protected.msg(Sec.Nas.protect(c, prot, plain))]) == True{} : Bool}:
  match c:
    case Sec.Ctx{+k, +d, +ul}:
      Fs.told_write(b, k, d, ul, prot, plain, ev)

def Fs.gone_any(+b: Maybe<&2, Sec.Nas.Ctx>, +c: Sec.Nas.Ctx, +prot: Sec.Nas.Protection, +plain: B.Bytes(), +ev: {Fs.view(b) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}) -> {N.Fresh.holds(b, None{}, [Sec.Nas.Protected.msg(Sec.Nas.protect(c, prot, plain))]) == True{} : Bool}:
  match c:
    case Sec.Ctx{+k, +d, +ul}:
      Fs.gone_write(b, k, d, ul, prot, plain, ev)

# Context Setup takes the context the Registration Accept leaves.
def Fs.cs_write(+st: S.State, +key: U32, +ue2: S.Ue, +ctx: Sec.Nas.Ctx, +accept: B.Bytes(), +nh: S.Nh, +epc: {S.Ue.phase(ue2) == S.ContextSetup{S.Guard{0}, Sec.Nas.Protected.ctx(Sec.Nas.protect(ctx, Sec.Ciphered{}, accept)), nh, False{}, False{}} : S.Phase}, +ev: {Fs.view(Fs.ctx(st, key)) == Fs.view(Some{ctx}) : Maybe<&2, Fs.KD()>}) -> {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(S.Ue.phase(ue2)), [Sec.Nas.Protected.msg(Sec.Nas.protect(ctx, Sec.Ciphered{}, accept))]) == True{} : Bool}:
  +ph : S.Phase = S.ContextSetup{S.Guard{0}, Sec.Nas.Protected.ctx(Sec.Nas.protect(ctx, Sec.Ciphered{}, accept)), nh, False{}, False{}}
  (%Equal.sym(S.Phase, S.Ue.phase(ue2), ph, epc) : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(_), [Sec.Nas.Protected.msg(Sec.Nas.protect(ctx, Sec.Ciphered{}, accept))]) == True{} : Bool}; Fs.told_any(Fs.ctx(st, key), ctx, Sec.Ciphered{}, accept, ev))

# Security Mode Complete: Initial Context Setup with the Registration Accept
# under the stored context's COUNT, Context Setup taking the next.
def Fs.sm_nas(+st: S.State, +key: U32, +ue2: S.Ue, +del: N.GOut(), +ev: List<&2, N.Act>, +x: N.Act, +y: N.Act, +ctx: Sec.Nas.Ctx, +accept: B.Bytes(), +nh: S.Nh, +hdel: {Fs.mute(N.Out.tx(del), N.Out.acts(del)) == True{} : Bool}, +hev: {Fs.amute(ev) == True{} : Bool}, +hy: {Fs.none(N.Act.nas(y)) == True{} : Bool}, +ex: {N.Act.nas(x) == Some{(key, Sec.Nas.Protected.msg(Sec.Nas.protect(ctx, Sec.Ciphered{}, accept)))} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, +epc: {S.Ue.phase(ue2) == S.ContextSetup{S.Guard{0}, Sec.Nas.Protected.ctx(Sec.Nas.protect(ctx, Sec.Ciphered{}, accept)), nh, False{}, False{}} : S.Phase}, +evw: {Fs.view(Fs.ctx(st, key)) == Fs.view(Some{ctx}) : Maybe<&2, Fs.KD()>}) -> {Fs.nas(st, N.Out.tx(N.Out.also(N.Out.join(del, (S.Put{key, ue2}, ev)), [x, y])), N.Out.acts(N.Out.also(N.Out.join(del, (S.Put{key, ue2}, ev)), [x, y]))) == True{} : Bool}:
  Fs.place_told(st, key, ue2, del, ev, x, y, Sec.Nas.Protected.msg(Sec.Nas.protect(ctx, Sec.Ciphered{}, accept)), hdel, hev, hy, ex, Fs.cs_write(st, key, ue2, ctx, accept, nh, epc, evw))

# A protected message to key in front of actions carrying none, the row key
# written beside a transaction that writes no row.
def Fs.front_put(+st: S.State, +td: S.Tx, +key: U32, +ue2: S.Ue, +x: N.Act, +m: B.Bytes(), +rest: List<&2, N.Act>, +ht: {Fs.tmute(td) == True{} : Bool}, +hr: {Fs.amute(rest) == True{} : Bool}, +ex: {N.Act.nas(x) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, +hw: {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(S.Ue.phase(ue2)), [m]) == True{} : Bool}) -> {Fs.nas(st, S.Both{td, S.Put{key, ue2}}, x <> rest) == True{} : Bool}:
  +tx : S.Tx = S.Both{td, S.Put{key, ue2}}
  +acts : List<&2, N.Act> = x <> rest
  +en : {N.Acts.nas(key, acts) == [m] : List<&2, B.Bytes()>} = (%Fs.amute_nas(key, rest, hr) : {N.Acts.nas(key, acts) == m <> _ : List<&2, B.Bytes()>}; Fs.one_nas(key, x, m, rest, ex))
  +sen = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, acts), [m], en)
  +hw2 : {Fs.write(st, key, S.Phase.nas(S.Ue.phase(ue2)), acts) == True{} : Bool} = (%sen : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(S.Ue.phase(ue2)), _) == True{} : Bool}; hw)
  +sx = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, N.Act.nas(x), Some{(key, m)}, ex)
  +hsx : {Fs.sent(tx, N.Act.nas(x)) == True{} : Bool} = (%sx : {Fs.sent(tx, _) == True{} : Bool}; P.Bool.or_r(Fs.writes(key, td), U32.is_eq(key, key), P.U32.is_eq_refl(key)))
  P.Bool.and_intro(Fs.sealed(st, tx, acts), Fs.sends(tx, acts), P.Bool.and_intro(Fs.sealed(st, td, acts), Fs.write(st, key, S.Phase.nas(S.Ue.phase(ue2)), acts), Fs.tmute_sealed(st, td, acts, ht), hw2), P.Bool.and_intro(Fs.sent(tx, N.Act.nas(x)), Fs.sends(tx, rest), hsx, Fs.amute_sends(tx, rest, hr)))

def Fs.front_place(+st: S.State, +key: U32, +ue2: S.Ue, +del: N.GOut(), +ev: List<&2, N.Act>, +x: N.Act, +rel: N.Act, +more: List<&2, N.Act>, +m: B.Bytes(), +hdel: {Fs.mute(N.Out.tx(del), N.Out.acts(del)) == True{} : Bool}, +hev: {Fs.amute(ev) == True{} : Bool}, +hrel: {Fs.none(N.Act.nas(rel)) == True{} : Bool}, +hmore: {Fs.amute(more) == True{} : Bool}, +ex: {N.Act.nas(x) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, +hw: {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(S.Ue.phase(ue2)), [m]) == True{} : Bool}) -> {Fs.nas(st, N.Out.tx(N.Out.prepend(rel, N.Out.also(N.Out.join(del, (S.Put{key, ue2}, ev)), more))), x <> N.Out.acts(N.Out.prepend(rel, N.Out.also(N.Out.join(del, (S.Put{key, ue2}, ev)), more)))) == True{} : Bool}:
  match del:
    case (+td, +ad):
      +pre = List.append(&2, N.Act, ad, ev)
      +hp = Fs.amute_app(ad, ev, P.Bool.and_true_r(Fs.tmute(td), Fs.amute(ad), hdel), hev)
      +hr = P.Bool.and_intro(Fs.none(N.Act.nas(rel)), Fs.amute(List.append(&2, N.Act, pre, more)), hrel, Fs.amute_app(pre, more, hp, hmore))
      Fs.front_put(st, td, key, ue2, x, m, rel <> List.append(&2, N.Act, pre, more), P.Bool.and_true_l(Fs.tmute(td), Fs.amute(ad), hdel), hr, ex, hw)

# A protected message in front of UE Context Release Command: the context ends
# with it.
def Fs.release_front(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause, +x: N.Act, +m: B.Bytes(), +ex: {N.Act.nas(x) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, +hw: {N.Fresh.holds(Fs.ctx(st, key), None{}, [m]) == True{} : Bool}, +ep: {S.Ue.phase(S.Ue.with_phase(ue, S.Releasing{S.Guard{0}})) == S.Releasing{S.Guard{0}} : S.Phase}) -> {Fs.nas(st, N.Out.tx(Gmm.Gmm.release(st, key, ue, cause)), x <> N.Out.acts(Gmm.Gmm.release(st, key, ue, cause))) == True{} : Bool}:
  +ur = S.Ue.with_phase(ue, S.Releasing{S.Guard{0}})
  +vs = S.Ues.evicted(key, ur, S.State.ues(st))
  +rel : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}
  +more : List<&2, N.Act> = N.TimerStart{Some{key}, key, N.Ue.guard_ms()} <> Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause)
  Fs.front_place(st, key, ur, Up.N4.deletions(Gmm.Gmm.sessions(vs, S.State.sessions(st)), S.State.pfcp_seq(st)), Gmm.Gmm.evict(vs), x, rel, more, m, Fs.deletions_mute(Gmm.Gmm.sessions(vs, S.State.sessions(st)), S.State.pfcp_seq(st)), Fs.evict_mute(vs), {==}, P.Bool.and_intro(True{}, Fs.amute(Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause)), {==}, Fs.leg_mute(key, S.Ue.phase(ue), cause)), ex, (%Equal.sym(S.Phase, S.Ue.phase(ur), S.Releasing{S.Guard{0}}, ep) : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(_), [m]) == True{} : Bool}; hw))

# Verifying an uplink message moves only the uplink COUNT: the context it
# leaves has the keys and downlink COUNT it had.
def Fs.Keeps(+c: Sec.Nas.Ctx, r: Result<&2, &2, B.Err, Sec.Nas.Unprotected>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{Sec.Unprotected{prot, plain, count, c2}}:
      {Fs.view(Some{c2}) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}

def Fs.open_keeps(+k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +count: Sec.Nas.Count, r: Result<&2, &2, B.Err, Sec.Nas.Opened>) -> Fs.Keeps(Sec.Ctx{k, d, ul}, Sec.Nas.u_open(k, d, count, r)):
  match r:
    case Fail{e}:
      Unit{}
    case Done{Sec.Opened{prot, plain}}:
      {==}

def Fs.count_keeps(+k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +msg: B.Bytes(), r: Result<&2, &2, B.Err, Sec.Nas.Count>) -> Fs.Keeps(Sec.Ctx{k, d, ul}, Sec.Nas.u_count(k, d, msg, r)):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+count}:
      Fs.open_keeps(k, d, ul, count, Sec.Nas.open(k, Sec.Nas.uplink(), count, msg))

def Fs.sqn_keeps(+c: Sec.Nas.Ctx, +msg: B.Bytes(), r: B.Read(U32)) -> Fs.Keeps(c, Sec.Nas.u_sqn(c, msg, r)):
  match c:
    case Sec.Ctx{+k, +d, +ul}:
      match r:
        case Fail{e}:
          Unit{}
        case Done{(sqn, rest)}:
          Fs.count_keeps(k, d, ul, msg, Sec.Nas.estimate(ul, sqn))

def Fs.unprotect_keeps(+c: Sec.Nas.Ctx, +msg: B.Bytes()) -> Fs.Keeps(c, Sec.Nas.unprotect(c, msg)):
  Fs.sqn_keeps(c, msg, B.u8(List.drop(&2, U32, msg, 6n)))

def Fs.cancel_mute(+key: U32, g: Maybe<&2, S.Guard>) -> {Fs.amute(N.Guard.cancel(key, g)) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{guard}:
      {==}

def Fs.expiry_mute(+key: U32, +ue: S.Ue, +leg: S.Leg) -> {Fs.amute(Ho.Ho.expiry(key, ue, leg)) == True{} : Bool}:
  match leg:
    case S.Asked{+t}:
      Fs.drop_mute(key, S.Asked{t}, Ho.Ho.radio(G.CauseRadioNetwork.tngrelocprep_expiry()))
    case S.Acked{+t, +r, +s, +ts}:
      Fs.drop_mute(key, S.Acked{t, r, s, ts}, Ho.Ho.radio(G.CauseRadioNetwork.tngrelocoverall_expiry()))

# A phase that keeps the context the key held, beside actions carrying no
# protected NAS message.
def Fs.kept_rephase(+st: S.State, +key: U32, +q: S.Phase, +c: Sec.Nas.Ctx, +acts: List<&2, N.Act>, +eq: {S.Phase.nas(q) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, +ev: {Fs.view(Fs.ctx(st, key)) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}, +ha: {Fs.amute(acts) == True{} : Bool}) -> {Fs.nas(st, S.Rephase{key, q}, acts) == True{} : Bool}:
  +sn = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, acts), [], Fs.amute_nas(key, acts, ha))
  +hw : {Fs.write(st, key, S.Phase.nas(q), acts) == True{} : Bool} = (%sn : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(q), _) == True{} : Bool}; Fs.kept_any(st, key, q, c, eq, ev))
  P.Bool.and_intro(Fs.write(st, key, S.Phase.nas(q), acts), Fs.sends(S.Rephase{key, q}, acts), hw, Fs.amute_sends(S.Rephase{key, q}, acts, ha))

def Fs.rephase_none(+st: S.State, +key: U32, +q: S.Phase, +en: {S.Phase.nas(q) == None{} : Maybe<&2, Sec.Nas.Ctx>}) -> {Fs.nas(st, S.Rephase{key, q}, []) == True{} : Bool}:
  (%Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.nas(q), None{}, en) : {Bool.and(N.Fresh.holds(Fs.ctx(st, key), _, []), True{}) == True{} : Bool}; {==})

# A context c1 whose keys and COUNT are those messages leave, sealed in turn
# from the COUNT b held under its keys: what writing c1 after them holds.
def Fs.holds_after(+b: Maybe<&2, Sec.Nas.Ctx>, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +c1: Sec.Nas.Ctx, +ms: List<&2, B.Bytes()>, +eb: {Fs.view(b) == Some{(k, d)} : Maybe<&2, Fs.KD()>}, +v1: {Fs.view(Some{c1}) == Fs.after_run(k, N.Fresh.run(ms, k, d)) : Maybe<&2, Fs.KD()>}) -> {N.Fresh.holds(b, Some{c1}, ms) == True{} : Bool}:
  match c1:
    case Sec.Ctx{+k1, +d1, +u1}:
      +er = Fs.pair_l({N.Fresh.run(ms, k, d) == Some{d1} : Maybe<&2, Sec.Nas.Count>}, {k1 == k : Sec.Nas.Keys}, Fs.run_of_view(k, k1, d1, N.Fresh.run(ms, k, d), v1))
      +ek = Fs.pair_r({N.Fresh.run(ms, k, d) == Some{d1} : Maybe<&2, Sec.Nas.Count>}, {k1 == k : Sec.Nas.Keys}, Fs.run_of_view(k, k1, d1, N.Fresh.run(ms, k, d), v1))
      (%Equal.sym(Sec.Nas.Keys, k1, k, ek) : {N.Fresh.holds(b, Some{Sec.Ctx{_, d1, u1}}, ms) == True{} : Bool}; Fs.holds_run(b, k, d, d1, u1, ms, eb, er))

# A phase holding c, after messages that all go to key and leave c.
def Fs.rephase_told(+st: S.State, +key: U32, +q: S.Phase, +c: Sec.Nas.Ctx, +acts: List<&2, N.Act>, +eq: {S.Phase.nas(q) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, +hw: {N.Fresh.holds(Fs.ctx(st, key), Some{c}, N.Acts.nas(key, acts)) == True{} : Bool}, +ht: {Fs.to_key(key, acts) == True{} : Bool}) -> {Fs.nas(st, S.Rephase{key, q}, acts) == True{} : Bool}:
  +sq = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.nas(q), Some{c}, eq)
  +hw2 : {Fs.write(st, key, S.Phase.nas(q), acts) == True{} : Bool} = (%sq : {N.Fresh.holds(Fs.ctx(st, key), _, N.Acts.nas(key, acts)) == True{} : Bool}; hw)
  P.Bool.and_intro(Fs.write(st, key, S.Phase.nas(q), acts), Fs.sends(S.Rephase{key, q}, acts), hw2, Fs.to_key_sends(key, S.Rephase{key, q}, acts, ht, P.U32.is_eq_refl(key)))

# Gsm.releases: one PDU Session Release Command after another, each under the
# COUNT the one before leaves.
def Fs.rel_step(+key: U32, +x: N.Act, +m: B.Bytes(), +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +r: N.Told(), +ex: {N.Act.nas(x) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, +es: {Sec.Nas.sealed(k, d, m) == True{} : Bool}, +ih: {Fs.view(Some{Gsm.Gsm.Told.ctx(r)}) == Fs.after_run(k, N.Fresh.run(N.Acts.nas(key, Gsm.Gsm.Told.acts(r)), k, Sec.Nas.Count.next(d))) : Maybe<&2, Fs.KD()>}) -> {Fs.view(Some{Gsm.Gsm.Told.ctx(N.Out.told_after([x], r))}) == Fs.after_run(k, N.Fresh.run(N.Acts.nas(key, Gsm.Gsm.Told.acts(N.Out.told_after([x], r))), k, d)) : Maybe<&2, Fs.KD()>}:
  match r:
    case (+c, +acts):
      +ms = N.Acts.nas(key, acts)
      +t1 : {Fs.view(Some{c}) == Fs.after_run(k, N.Fresh.run(m <> ms, k, d)) : Maybe<&2, Fs.KD()>} = (%Equal.sym(Bool, Sec.Nas.sealed(k, d, m), True{}, es) : {Fs.view(Some{c}) == Fs.after_run(k, N.Fresh.then(_, u => N.Fresh.run(ms, k, Sec.Nas.Count.next(d)))) : Maybe<&2, Fs.KD()>}; ih)
      (%Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, x <> acts), m <> ms, Fs.one_nas(key, x, m, acts, ex)) : {Fs.view(Some{c}) == Fs.after_run(k, N.Fresh.run(_, k, d)) : Maybe<&2, Fs.KD()>}; t1)

def Fs.releases_view(+key: U32, +assoc: U32, +stream: U32, +ran: B.Bytes(), +psis: List<&2, U32>, +k: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>) -> {Fs.view(Some{Gsm.Gsm.Told.ctx(Gsm.Gsm.releases(key, assoc, stream, ran, psis, Sec.Ctx{k, d, ul}))}) == Fs.after_run(k, N.Fresh.run(N.Acts.nas(key, Gsm.Gsm.Told.acts(Gsm.Gsm.releases(key, assoc, stream, ran, psis, Sec.Ctx{k, d, ul}))), k, d)) : Maybe<&2, Fs.KD()>}:
  match psis:
    case Nil{}:
      {==}
    case +p <> +more:
      +plain = Gsm.Gsm.dl_transport(p, Gsm.Gsm.release_command(p))
      +m = Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{k, d, ul}, Sec.Ciphered{}, Gsm.Gsm.release_plain(p)))
      +x : N.Act = N.DlNas{assoc, stream, key, ran, m}
      Fs.rel_step(key, x, m, k, d, Gsm.Gsm.releases(key, assoc, stream, ran, more, Sec.Ctx{k, Sec.Nas.Count.next(d), ul}), Fs.dl_carries(assoc, stream, key, ran, m, Fs.protect_protected(k, d, ul, Sec.Ciphered{}, plain)), Fs.sealed_seal(k, Sec.Ciphered{}, d, plain), Fs.releases_view(key, assoc, stream, ran, more, k, Sec.Nas.Count.next(d), ul))

def Fs.rel_to_step(+key: U32, +x: N.Act, +m: B.Bytes(), +r: N.Told(), +ex: {N.Act.nas(x) == Some{(key, m)} : Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>}, +ih: {Fs.to_key(key, Gsm.Gsm.Told.acts(r)) == True{} : Bool}) -> {Fs.to_key(key, Gsm.Gsm.Told.acts(N.Out.told_after([x], r))) == True{} : Bool}:
  match r:
    case (c, +acts):
      +sx = Equal.sym(Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, N.Act.nas(x), Some{(key, m)}, ex)
      P.Bool.and_intro(Fs.to_key_m(key, N.Act.nas(x)), Fs.to_key(key, acts), (%sx : {Fs.to_key_m(key, _) == True{} : Bool}; P.U32.is_eq_refl(key)), ih)

def Fs.releases_to(+key: U32, +assoc: U32, +stream: U32, +ran: B.Bytes(), +psis: List<&2, U32>, +c: Sec.Nas.Ctx) -> {Fs.to_key(key, Gsm.Gsm.Told.acts(Gsm.Gsm.releases(key, assoc, stream, ran, psis, c))) == True{} : Bool}:
  match psis:
    case Nil{}:
      {==}
    case +p <> +more:
      +q = Sec.Nas.protect(c, Sec.Ciphered{}, Gsm.Gsm.release_plain(p))
      +m = Sec.Nas.Protected.msg(q)
      Fs.rel_to_step(key, N.DlNas{assoc, stream, key, ran, m}, m, Gsm.Gsm.releases(key, assoc, stream, ran, more, Sec.Nas.Protected.ctx(q)), Fs.dl_carries(assoc, stream, key, ran, m, Fs.protected_any(c, Sec.Ciphered{}, Gsm.Gsm.dl_transport(p, Gsm.Gsm.release_command(p)))), Fs.releases_to(key, assoc, stream, ran, more, Sec.Nas.Protected.ctx(q)))

# The releases under the context the key held, the context they leave written.
def Fs.releases_write(+st: S.State, +key: U32, +assoc: U32, +stream: U32, +ran: B.Bytes(), +psis: List<&2, U32>, +c: Sec.Nas.Ctx, +ev: {Fs.view(Fs.ctx(st, key)) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}) -> {N.Fresh.holds(Fs.ctx(st, key), Some{Gsm.Gsm.Told.ctx(Gsm.Gsm.releases(key, assoc, stream, ran, psis, c))}, N.Acts.nas(key, Gsm.Gsm.Told.acts(Gsm.Gsm.releases(key, assoc, stream, ran, psis, c)))) == True{} : Bool}:
  match c:
    case Sec.Ctx{+k, +d, +ul}:
      +r = Gsm.Gsm.releases(key, assoc, stream, ran, psis, Sec.Ctx{k, d, ul})
      Fs.holds_after(Fs.ctx(st, key), k, d, Gsm.Gsm.Told.ctx(r), N.Acts.nas(key, Gsm.Gsm.Told.acts(r)), ev, Fs.releases_view(key, assoc, stream, ran, psis, k, d, ul))

# The items of a PDU Session Resource Setup Response
# --------------------------------------------------

def Fs.modify_ii(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, +seq: U32, +tunnel: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>, +c: Maybe<&2, Sec.Nas.Ctx>) -> Fs.Ii(key, c, Gsm.Gsm.modify(key, ue, skey, s, seq, tunnel, c)):
  match tunnel:
    case None{}:
      Fs.give_up_ii(key, ue, skey, s, Gsm.Release{}, seq, c)
    case Some{(+gnb_teid, +gnb_addr)}:
      +request = Up.N4.modify(S.Session.up_seid(s), gnb_teid, gnb_addr, seq)
      Fs.ii_mute(key, c, (S.Both{S.Revar{skey, S.SVar{S.Session.up_seid(s), seq, S.Modifying{S.Guard{0}, request}}}, S.BumpSeq{1}}, [N.Pfcp{S.Session.tag(s), request}, N.TimerStart{S.Session.tag(s), skey, Up.N4.t1_ms()}]), {==})

def Fs.set_up_phase_ii(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, +transfer: B.Bytes(), +seq: U32, +p: S.SPhase, +c: Maybe<&2, Sec.Nas.Ctx>) -> Fs.Ii(key, c, Gsm.Gsm.set_up_phase(key, ue, skey, s, transfer, seq, p, c)):
  match p:
    case S.Setting{guard, pti}:
      Fs.modify_ii(key, ue, skey, s, seq, Gsm.Gsm.tunnel_of(G.PDUSessionResourceSetupResponseTransfer.read(Ap.Cur{0n, Ap.unpack(transfer)})), c)
    case S.Creating{guard, pti, accept, request}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session set up at the gNB while not being set up"), {==})
    case S.Modifying{guard, request}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session set up at the gNB while not being set up"), {==})
    case S.Repointing{guard, request}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session set up at the gNB while not being set up"), {==})
    case S.Deleting{guard, request}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session set up at the gNB while not being set up"), {==})
    case S.Active{}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session set up at the gNB while not being set up"), {==})

def Fs.set_up_ii(+key: U32, +ue: S.Ue, +transfer: B.Bytes(), +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +c: Maybe<&2, Sec.Nas.Ctx>) -> Fs.Ii(key, c, Gsm.Gsm.set_up(key, ue, transfer, seq, m, c)):
  match m:
    case None{}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session set up at the gNB for no session"), {==})
    case Some{(+skey, +s)}:
      Fs.set_up_phase_ii(key, ue, skey, s, transfer, seq, S.Session.phase(s), c)

def Fs.set_up_last_ii(+key: U32, +ue: S.Ue, +transfer: B.Bytes(), +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +again: Bool, +c: Maybe<&2, Sec.Nas.Ctx>) -> Fs.Ii(key, c, Gsm.Gsm.set_up_last(key, ue, transfer, seq, m, again, c)):
  match again:
    case True{}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session named again later in the setup list; this naming ignored"), {==})
    case False{}:
      Fs.set_up_ii(key, ue, transfer, seq, m, c)

def Fs.set_ups_ii(+st: S.State, +key: U32, +ue: S.Ue, +items: G.PDUSessionResourceSetupListSURes(), +seq: U32, +c: Maybe<&2, Sec.Nas.Ctx>) -> Fs.Ii(key, c, Gsm.Gsm.set_ups(st, key, ue, items, seq, c)):
  match items:
    case Nil{}:
      Fs.ii_mute(key, c, (S.Keep{}, []), {==})
    case G.PDUSessionResourceSetupItemSURes{+psi, +transfer, x} <> +more:
      +a = Gsm.Gsm.set_up_last(key, ue, transfer, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), Gsm.Gsm.named(psi, more), c)
      Fs.ii_then(key, c, Gsm.Gsm.after((S.BumpSeq{1}, []), a), c2 => Gsm.Gsm.set_ups(st, key, ue, more, U32.add(seq, 1), c2), Fs.ii_after(key, c, (S.BumpSeq{1}, []), a, {==}, Fs.set_up_last_ii(key, ue, transfer, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), Gsm.Gsm.named(psi, more), c)), +c2 => Fs.set_ups_ii(st, key, ue, more, U32.add(seq, 1), c2))

def Fs.failed_phase_ii(+key: U32, +ue: S.Ue, +skey: U32, +s: S.Session, +seq: U32, +p: S.SPhase, +c: Maybe<&2, Sec.Nas.Ctx>) -> Fs.Ii(key, c, Gsm.Gsm.failed_phase(key, ue, skey, s, seq, p, c)):
  match p:
    case S.Setting{guard, +pti}:
      Fs.give_up_ii(key, ue, skey, s, Gsm.Reply{Gsm.Gsm.reject(S.Session.psi(s), pti, 26)}, seq, c)
    case S.Creating{guard, pti, accept, request}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session failed at the gNB while not being set up"), {==})
    case S.Modifying{guard, request}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session failed at the gNB while not being set up"), {==})
    case S.Repointing{guard, request}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session failed at the gNB while not being set up"), {==})
    case S.Deleting{guard, request}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session failed at the gNB while not being set up"), {==})
    case S.Active{}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session failed at the gNB while not being set up"), {==})

def Fs.failed_ii(+key: U32, +ue: S.Ue, +seq: U32, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>, +c: Maybe<&2, Sec.Nas.Ctx>) -> Fs.Ii(key, c, Gsm.Gsm.failed(key, ue, seq, m, c)):
  match m:
    case None{}:
      Fs.ii_mute(key, c, N.Out.warn("NGAP: PDU session failed at the gNB for no session"), {==})
    case Some{(+skey, +s)}:
      Fs.failed_phase_ii(key, ue, skey, s, seq, S.Session.phase(s), c)

def Fs.faileds_ii(+st: S.State, +key: U32, +ue: S.Ue, +items: G.PDUSessionResourceFailedToSetupListSURes(), +seq: U32, +c: Maybe<&2, Sec.Nas.Ctx>) -> Fs.Ii(key, c, Gsm.Gsm.faileds(st, key, ue, items, seq, c)):
  match items:
    case Nil{}:
      Fs.ii_mute(key, c, (S.Keep{}, []), {==})
    case G.PDUSessionResourceFailedToSetupItemSURes{+psi, transfer, x} <> +more:
      +a = Gsm.Gsm.failed(key, ue, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), c)
      Fs.ii_then(key, c, Gsm.Gsm.after((S.BumpSeq{1}, []), a), c2 => Gsm.Gsm.faileds(st, key, ue, more, U32.add(seq, 1), c2), Fs.ii_after(key, c, (S.BumpSeq{1}, []), a, {==}, Fs.failed_ii(key, ue, seq, S.Sessions.by_psi(key, psi, S.State.sessions(st)), c)), +c2 => Fs.faileds_ii(st, key, ue, more, U32.add(seq, 1), c2))

def Fs.results_ii(+st: S.State, +key: U32, +ue: S.Ue, +oks: G.PDUSessionResourceSetupListSURes(), +fails: G.PDUSessionResourceFailedToSetupListSURes(), +seq: U32, +seq2: U32, +c: Maybe<&2, Sec.Nas.Ctx>) -> Fs.Ii(key, c, Gsm.Gsm.then(Gsm.Gsm.set_ups(st, key, ue, oks, seq, c), c2 => Gsm.Gsm.faileds(st, key, ue, fails, seq2, c2))):
  Fs.ii_then(key, c, Gsm.Gsm.set_ups(st, key, ue, oks, seq, c), c2 => Gsm.Gsm.faileds(st, key, ue, fails, seq2, c2), Fs.set_ups_ii(st, key, ue, oks, seq, c), +c2 => Fs.faileds_ii(st, key, ue, fails, seq2, c2))

# Path Switch: what the UPF is asked is mute.
def Fs.sw_session_mute(+skey: U32, +s: S.Session, +seq: U32, +t: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>) -> Fs.Mute(Sw.Sw.session(skey, s, seq, t)):
  match t:
    case None{}:
      Fs.deletions_mute([(skey, s)], seq)
    case Some{(teid, addr)}:
      {==}

def Fs.sw_sessions_mute(+ts: List<&2, S.Tunnel>, +rows: Tb.Table(S.Session), +seq: U32) -> Fs.Mute(Sw.Sw.sessions(ts, rows, seq)):
  match rows:
    case Nil{}:
      {==}
    case (+skey, +s) <> +more:
      +o = Sw.Sw.session(skey, s, seq, Sw.Sw.tunnel_for(ts, s))
      Fs.join_mute(N.Out.join((S.BumpSeq{1}, []), o), Sw.Sw.sessions(ts, more, U32.add(seq, 1)), Fs.join_mute((S.BumpSeq{1}, []), o, {==}, Fs.sw_session_mute(skey, s, seq, Sw.Sw.tunnel_for(ts, s))), Fs.sw_sessions_mute(ts, more, U32.add(seq, 1)))

# A row put whose phase q keeps the context the key held, beside actions
# carrying no protected NAS message.
def Fs.kept_put(+st: S.State, +key: U32, +v: S.Ue, +q: S.Phase, +c: Sec.Nas.Ctx, +acts: List<&2, N.Act>, +ep: {S.Ue.phase(v) == q : S.Phase}, +eq: {S.Phase.nas(q) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, +ev: {Fs.view(Fs.ctx(st, key)) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}, +ha: {Fs.amute(acts) == True{} : Bool}) -> {Fs.nas(st, S.Put{key, v}, acts) == True{} : Bool}:
  +sn = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, acts), [], Fs.amute_nas(key, acts, ha))
  +sp = Equal.sym(S.Phase, S.Ue.phase(v), q, ep)
  +hw : {Fs.write(st, key, S.Phase.nas(S.Ue.phase(v)), acts) == True{} : Bool} = (%sp : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(_), N.Acts.nas(key, acts)) == True{} : Bool}; (%sn : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(q), _) == True{} : Bool}; Fs.kept_any(st, key, q, c, eq, ev)))
  P.Bool.and_intro(Fs.write(st, key, S.Phase.nas(S.Ue.phase(v)), acts), Fs.sends(S.Put{key, v}, acts), hw, Fs.amute_sends(S.Put{key, v}, acts, ha))

def Fs.same_mute(+ok: Bool) -> {Fs.amute(Ps.Ps.caps_same(ok)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Fs.caps_mute(+caps: G.UESecurityCapabilities, +m: Maybe<&2, N.Keyed()>) -> {Fs.amute(Ps.Ps.caps_note(caps, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+key, +ue)}:
      Fs.same_mute(B.bytes_eq(Ap.pack(G.UESecurityCapabilities.write(N.Ngap.ue_caps(N.Ue.caps(ue)), 0n, [])), Ap.pack(G.UESecurityCapabilities.write(caps, 0n, []))))

# Mute work, a row put under key, then actions whose messages all go to key.
def Fs.put_also(+st: S.State, +a: N.GOut(), +key: U32, +v: S.Ue, +more: List<&2, N.Act>, +ha: {Fs.mute(N.Out.tx(a), N.Out.acts(a)) == True{} : Bool}, +ht: {Fs.to_key(key, more) == True{} : Bool}, +hw: {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(S.Ue.phase(v)), N.Acts.nas(key, more)) == True{} : Bool}) -> {Fs.nas(st, N.Out.tx(N.Out.also(N.Out.join(a, (S.Put{key, v}, [])), more)), N.Out.acts(N.Out.also(N.Out.join(a, (S.Put{key, v}, [])), more))) == True{} : Bool}:
  match a:
    case (+td, +ad):
      +pre = List.append(&2, N.Act, ad, [])
      +acts = List.append(&2, N.Act, pre, more)
      +tx : S.Tx = S.Both{td, S.Put{key, v}}
      +am = Fs.amute_app(ad, [], P.Bool.and_true_r(Fs.tmute(td), Fs.amute(ad), ha), {==})
      +sn = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, acts), N.Acts.nas(key, more), Fs.nas_mute_l(key, pre, more, am))
      +hw2 : {Fs.write(st, key, S.Phase.nas(S.Ue.phase(v)), acts) == True{} : Bool} = (%sn : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(S.Ue.phase(v)), _) == True{} : Bool}; hw)
      +hs = Fs.sends_app(tx, pre, more, Fs.amute_sends(tx, pre, am), Fs.to_key_sends(key, tx, more, ht, P.Bool.or_r(Fs.writes(key, td), U32.is_eq(key, key), P.U32.is_eq_refl(key))))
      P.Bool.and_intro(Fs.sealed(st, tx, acts), Fs.sends(tx, acts), P.Bool.and_intro(Fs.sealed(st, td, acts), Fs.write(st, key, S.Phase.nas(S.Ue.phase(v)), acts), Fs.tmute_sealed(st, td, acts, P.Bool.and_true_l(Fs.tmute(td), Fs.amute(ad), ha)), hw2), hs)

# Handover Notify: the source released, then the sessions whose tunnels the
# target did not take, each under the COUNT the one before leaves, the context
# after them written.
def Fs.ho_complete_nas(+st: S.State, +assoc: U32, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +ev: {Fs.view(Fs.ctx(st, key)) == Fs.view(Some{ctx}) : Maybe<&2, Fs.KD()>}, +ep: {S.Ue.phase(S.Ue.moved(ue, assoc, r, s, S.Registered{Gsm.Gsm.Told.ctx(Gsm.Gsm.releases(key, assoc, s, r, Sw.Sw.released(ts, S.Sessions.of_ue(key, S.State.sessions(st))), ctx)), nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}})) == S.Registered{Gsm.Gsm.Told.ctx(Gsm.Gsm.releases(key, assoc, s, r, Sw.Sw.released(ts, S.Sessions.of_ue(key, S.State.sessions(st))), ctx)), nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}} : S.Phase}) -> {Fs.nas(st, N.Out.tx(Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, True{})), N.Out.acts(Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, True{}))) == True{} : Bool}:
  +rows = S.Sessions.of_ue(key, S.State.sessions(st))
  +psis = Sw.Sw.released(ts, rows)
  +told = Gsm.Gsm.releases(key, assoc, s, r, psis, ctx)
  +ph : S.Phase = S.Registered{Gsm.Gsm.Told.ctx(told), nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}}
  +v = S.Ue.moved(ue, assoc, r, s, ph)
  +ta = Gsm.Gsm.Told.acts(told)
  +tail : List<&2, N.Act> = [N.TimerCancel{key}, N.Note{F.Info{}, "NGAP: Handover Notify; the UE moved to the target"}]
  +x : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), Ho.Ho.radio(G.CauseRadioNetwork.successful_handover())}
  +more : List<&2, N.Act> = x <> List.append(&2, N.Act, ta, tail)
  +ht = P.Bool.and_intro(True{}, Fs.to_key(key, List.append(&2, N.Act, ta, tail)), {==}, Fs.to_key_app(key, ta, tail, Fs.releases_to(key, assoc, s, r, psis, ctx), {==}))
  +h0 = Fs.releases_write(st, key, assoc, s, r, psis, ctx, ev)
  +h1 : {N.Fresh.holds(Fs.ctx(st, key), Some{Gsm.Gsm.Told.ctx(told)}, N.Acts.nas(key, more)) == True{} : Bool} = (%Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(key, List.append(&2, N.Act, ta, tail)), N.Acts.nas(key, ta), Fs.nas_mute_r(key, ta, tail, {==})) : {N.Fresh.holds(Fs.ctx(st, key), Some{Gsm.Gsm.Told.ctx(told)}, _) == True{} : Bool}; h0)
  +hw : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(S.Ue.phase(v)), N.Acts.nas(key, more)) == True{} : Bool} = (%Equal.sym(S.Phase, S.Ue.phase(v), ph, ep) : {N.Fresh.holds(Fs.ctx(st, key), S.Phase.nas(_), N.Acts.nas(key, more)) == True{} : Bool}; h1)
  Fs.put_also(st, Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st)), key, v, more, Fs.sw_sessions_mute(ts, rows, S.State.pfcp_seq(st)), ht, hw)

# Rows of a table with every key once
# -----------------------------------
# Each row is the one its key reads.
def Fs.Got(+t: Tb.Table(S.Ue), rows: Tb.Table(S.Ue)) -> Data:
  match rows:
    case Nil{}:
      Unit
    case (k, u) <> more:
      Sigma<&2, &2, {Tb.Table.get(S.Ue, k, t) == Some{u} : Maybe<&2, S.Ue>}, _ => Fs.Got(t, more)>

def Fs.GotIf(b: Bool, +t: Tb.Table(S.Ue), +rows: Tb.Table(S.Ue)) -> Data:
  match b:
    case True{}:
      Fs.Got(t, rows)
    case False{}:
      Unit

def Fs.got_row(+u0: S.Ue, +more: Tb.Table(S.Ue), +k: U32, +u: S.Ue, +b: Bool, +ne: {b == False{} : Bool}, +e: {Tb.Table.get(S.Ue, k, more) == Some{u} : Maybe<&2, S.Ue>}) -> {Tb.Table.hit(S.Ue, u0, Tb.Table.get(S.Ue, k, more), b) == Some{u} : Maybe<&2, S.Ue>}:
  match b:
    case True{}:
      Empty.absurd({Some{u0} == Some{u} : Maybe<&2, S.Ue>}, P.Refute.true_false(ne))
    case False{}:
      e

# Rows clear of a row under k0 are found past it.
def Fs.got_cons(+k0: U32, +u0: S.Ue, +more: Tb.Table(S.Ue), +rows: Tb.Table(S.Ue), +hc: {S.Ues.clear(k0, u0, rows) == True{} : Bool}, +h: Fs.Got(more, rows)) -> Fs.Got((k0, u0) <> more, rows):
  match rows:
    case Nil{}:
      Unit{}
    case (+k, +u) <> +rest:
      match h:
        case (+e, +h2):
          +nc = Bool.not(S.Row.conflicts(k0, u0, k, u))
          +nr = P.Bool.or_false_l(U32.is_eq(k, k0), S.Ue.conflicts(u0, u), P.Bool.not_true(S.Row.conflicts(k0, u0, k, u), P.Bool.and_true_l(nc, S.Ues.clear(k0, u0, rest), hc)))
          +ne = Equal.trans(Bool, U32.is_eq(k0, k), U32.is_eq(k, k0), False{}, P.U32.sym(k0, k), nr)
          (Fs.got_row(u0, more, k, u, U32.is_eq(k0, k), ne, e), Fs.got_cons(k0, u0, more, rest, P.Bool.and_true_r(nc, S.Ues.clear(k0, u0, rest), hc), h2))

def Fs.got_self(+t: Tb.Table(S.Ue), +eu: {S.Ues.unique(t) == True{} : Bool}) -> Fs.Got(t, t):
  match t:
    case Nil{}:
      Unit{}
    case (+k0, +u0) <> +more:
      +hc = P.Bool.and_true_l(S.Ues.clear(k0, u0, more), S.Ues.unique(more), eu)
      +e = Equal.sym(Bool, U32.is_eq(k0, k0), True{}, P.U32.is_eq_refl(k0))
      +hd : {Tb.Table.hit(S.Ue, u0, Tb.Table.get(S.Ue, k0, more), U32.is_eq(k0, k0)) == Some{u0} : Maybe<&2, S.Ue>} = (%e : {Tb.Table.hit(S.Ue, u0, Tb.Table.get(S.Ue, k0, more), _) == Some{u0} : Maybe<&2, S.Ue>}; {==})
      (hd, Fs.got_cons(k0, u0, more, more, hc, Fs.got_self(more, P.Bool.and_true_r(S.Ues.clear(k0, u0, more), S.Ues.unique(more), eu))))

def Fs.got_if(+t: Tb.Table(S.Ue), +b: Bool, +eb: {S.Ues.unique(t) == b : Bool}) -> Fs.GotIf(b, t, t):
  match b:
    case True{}:
      Fs.got_self(t, eb)
    case False{}:
      Unit{}

def Fs.got_all(+st: S.State) -> Fs.GotIf(S.Ues.unique(S.State.ues(st)), S.State.ues(st), S.State.ues(st)):
  Fs.got_if(S.State.ues(st), S.Ues.unique(S.State.ues(st)), {==})

def Fs.got_rest(+b: Bool, +t: Tb.Table(S.Ue), +k: U32, +u: S.Ue, +more: Tb.Table(S.Ue), +w: Fs.GotIf(b, t, (k, u) <> more)) -> Fs.GotIf(b, t, more):
  match b:
    case True{}:
      match w:
        case (e, +w2):
          w2
    case False{}:
      Unit{}

# A row rewritten with the context it holds, its key sent nothing.
def Fs.row_ok(+st: S.State, +k: U32, +u: S.Ue, +more: Tb.Table(S.Ue), +q: S.Phase, +c: Sec.Nas.Ctx, +acts: List<&2, N.Act>, +b: Bool, +eb: {S.Ues.unique(S.State.ues(st)) == b : Bool}, +w: Fs.GotIf(b, S.State.ues(st), (k, u) <> more), +ep: {S.Phase.nas(S.Ue.phase(u)) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, +eq: {S.Phase.nas(q) == Some{c} : Maybe<&2, Sec.Nas.Ctx>}, +ha: {Fs.amute(acts) == True{} : Bool}) -> {Fs.ok(st, S.Rephase{k, q}, acts) == True{} : Bool}:
  match b:
    case True{}:
      match w:
        case (+eg, w2):
          +sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{u}, eg)
          +sp = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.nas(S.Ue.phase(u)), Some{c}, ep)
          +ev : {Fs.view(Fs.ctx(st, k)) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>} = (%sg : {Fs.view(S.Ue.nas(_)) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}; (%sp : {Fs.view(_) == Fs.view(Some{c}) : Maybe<&2, Fs.KD()>}; {==}))
          Fs.ok_of(st, S.Rephase{k, q}, acts, Fs.kept_rephase(st, k, q, c, acts, eq, ev, ha))
    case False{}:
      +sb = Equal.sym(Bool, S.Ues.unique(S.State.ues(st)), False{}, eb)
      P.Bool.or_r(Fs.nas(st, S.Rephase{k, q}, acts), Bool.not(S.Ues.unique(S.State.ues(st))), (%sb : {Bool.not(_) == True{} : Bool}; {==}))

def Fs.lost_mute(+k: U32, +u: S.Ue, +leg: S.Leg) -> {Fs.amute(Ho.Ho.lost(k, u, leg)) == True{} : Bool}:
  match leg:
    case S.Asked{t}:
      {==}
    case S.Acked{t, r, s, ts}:
      {==}

# A mute outcome holds what the law asks.
def Fs.mute_nas(+st: S.State, +tx: S.Tx, +acts: List<&2, N.Act>, +hm: {Fs.mute(tx, acts) == True{} : Bool}) -> {Fs.nas(st, tx, acts) == True{} : Bool}:
  P.Bool.and_intro(Fs.sealed(st, tx, acts), Fs.sends(tx, acts), Fs.tmute_sealed(st, tx, acts, P.Bool.and_true_l(Fs.tmute(tx), Fs.amute(acts), hm)), Fs.amute_sends(tx, acts, P.Bool.and_true_r(Fs.tmute(tx), Fs.amute(acts), hm)))

# Two outcomes in order, neither carrying a protected NAS message.
def Fs.both_amute(+st: S.State, +ta: S.Tx, +aa: List<&2, N.Act>, +tb: S.Tx, +ab: List<&2, N.Act>, +ha: {Fs.nas(st, ta, aa) == True{} : Bool}, +hb: {Fs.nas(st, tb, ab) == True{} : Bool}, +haa: {Fs.amute(aa) == True{} : Bool}, +hab: {Fs.amute(ab) == True{} : Bool}) -> {Fs.nas(st, S.Both{ta, tb}, List.append(&2, N.Act, aa, ab)) == True{} : Bool}:
  +xs = List.append(&2, N.Act, aa, ab)
  +sa = Fs.sealed_to(st, ta, aa, After{ab}, hab, Fs.sealed_of(st, ta, aa, ha))
  +sb = Fs.sealed_to(st, tb, ab, Before{aa}, haa, Fs.sealed_of(st, tb, ab, hb))
  P.Bool.and_intro(Fs.sealed(st, S.Both{ta, tb}, xs), Fs.sends(S.Both{ta, tb}, xs), P.Bool.and_intro(Fs.sealed(st, ta, xs), Fs.sealed(st, tb, xs), sa, sb), Fs.sends_app(S.Both{ta, tb}, aa, ab, Fs.amute_sends(S.Both{ta, tb}, aa, haa), Fs.amute_sends(S.Both{ta, tb}, ab, hab)))

# An association's reset carries no protected NAS message.
def Fs.down_leg_mute(+k: U32, +u: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +target: Bool, +source: Bool) -> {Fs.amute(N.Out.acts(Ho.Ho.down_leg(k, u, ctx, nh, leg, target, source))) == True{} : Bool}:
  match target source:
    case True{} _:
      Fs.amute_app(Ho.Ho.lost(k, u, leg), [N.TimerCancel{k}, N.Note{F.Warn{}, "NGAP: the target's UE contexts were re-initialised; N2 handover ended"}], Fs.lost_mute(k, u, leg), {==})
    case False{} True{}:
      Fs.drop_mute(k, leg, Ho.Ho.radio(G.CauseRadioNetwork.unspecified()))
    case False{} False{}:
      {==}

def Fs.down_row_mute(+assoc: U32, +k: U32, +u: S.Ue, +p: S.Phase) -> {Fs.amute(N.Out.acts(Ho.Ho.down_row(assoc, k, u, p))) == True{} : Bool}:
  match p:
    case S.Handover{+ctx, +nh, source, +leg}:
      Fs.down_leg_mute(k, u, ctx, nh, leg, Ho.Ho.aimed(u, assoc), U32.is_eq(S.Ue.assoc(u), assoc))
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

def Fs.acts_join(+a: N.GOut(), +b: N.GOut()) -> {N.Out.acts(N.Out.join(a, b)) == List.append(&2, N.Act, N.Out.acts(a), N.Out.acts(b)) : List<&2, N.Act>}:
  match a:
    case (ta, aa):
      match b:
        case (tb, ab):
          {==}

def Fs.downs_mute(+assoc: U32, +rows: Tb.Table(S.Ue)) -> {Fs.amute(N.Out.acts(Ho.Ho.downs(assoc, rows))) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      +a = Ho.Ho.down_row(assoc, k, u, S.Ue.phase(u))
      +b = Ho.Ho.downs(assoc, more)
      (%Equal.sym(List<&2, N.Act>, N.Out.acts(N.Out.join(a, b)), List.append(&2, N.Act, N.Out.acts(a), N.Out.acts(b)), Fs.acts_join(a, b)) : {Fs.amute(_) == True{} : Bool}; Fs.amute_app(N.Out.acts(a), N.Out.acts(b), Fs.down_row_mute(assoc, k, u, S.Ue.phase(u)), Fs.downs_mute(assoc, more)))
