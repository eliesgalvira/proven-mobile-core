import Base
import ../bytes.bend as B
import ../table.bend as Tb
import ../state.bend as S
import ../amf/ngap.bend as N
import ../nas/security.bend as Sec
import ./lib.bend as P
import ../LAWS.bend as L

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
      ih = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, List.append(&2, N.Act, more, ys)), List.append(&2, B.Bytes(), N.Acts.nas(k, more), N.Acts.nas(k, ys)), Fs.nas_app(k, more, ys))
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
      ih = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, more), [], Fs.amute_nas(k, more, P.Bool.and_true_r(Fs.none(N.Act.nas(a)), Fs.amute(more), h)))
      (%ih : {N.Acts.nas_to(k, N.Act.nas(a), _) == [] : List<&2, B.Bytes()>}; Fs.to_none(k, N.Act.nas(a), [], hn))

def Fs.app_nil(+xs: List<&2, B.Bytes()>) -> {List.append(&2, B.Bytes(), xs, []) == xs : List<&2, B.Bytes()>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +more:
      e = Equal.sym(List<&2, B.Bytes()>, List.append(&2, B.Bytes(), more, []), more, Fs.app_nil(more))
      (%e : {x <> _ == x <> more : List<&2, B.Bytes()>}; {==})

# Muted actions on either side leave the messages to every key as they were.
def Fs.nas_mute_l(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Fs.amute(xs) == True{} : Bool}) -> {N.Acts.nas(k, List.append(&2, N.Act, xs, ys)) == N.Acts.nas(k, ys) : List<&2, B.Bytes()>}:
  e = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, xs), [], Fs.amute_nas(k, xs, h))
  (%(Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, List.append(&2, N.Act, xs, ys)), List.append(&2, B.Bytes(), N.Acts.nas(k, xs), N.Acts.nas(k, ys)), Fs.nas_app(k, xs, ys))) : {_ == N.Acts.nas(k, ys) : List<&2, B.Bytes()>}; (%e : {List.append(&2, B.Bytes(), _, N.Acts.nas(k, ys)) == N.Acts.nas(k, ys) : List<&2, B.Bytes()>}; {==}))

def Fs.nas_mute_r(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {Fs.amute(ys) == True{} : Bool}) -> {N.Acts.nas(k, List.append(&2, N.Act, xs, ys)) == N.Acts.nas(k, xs) : List<&2, B.Bytes()>}:
  e = Equal.sym(List<&2, B.Bytes()>, N.Acts.nas(k, ys), [], Fs.amute_nas(k, ys, h))
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
  e = Equal.sym(Result<&2, &2, B.Err, Sec.Nas.Opened>, Sec.Nas.open(keys, Sec.Nas.downlink(), c, m), Done{Sec.Opened{prot, plain}}, L.nas_sec.roundtrip(keys, prot, Sec.Nas.downlink(), c, plain))
  (%e : {Sec.Nas.resealed(keys, c, m, _) == True{} : Bool}; P.Bytes.eq_refl(m))

# What a context protects goes under its COUNT, and leaves the next.
def Fs.protect_run(+keys: Sec.Nas.Keys, +d: Sec.Nas.Count, +ul: Maybe<&2, Sec.Nas.Count>, +prot: Sec.Nas.Protection, +plain: B.Bytes()) -> {N.Fresh.run([Sec.Nas.Protected.msg(Sec.Nas.protect(Sec.Ctx{keys, d, ul}, prot, plain))], keys, d) == Some{Sec.Nas.Count.next(d)} : Maybe<&2, Sec.Nas.Count>}:
  e = Equal.sym(Bool, Sec.Nas.sealed(keys, d, Sec.Nas.seal(keys, prot, Sec.Nas.downlink(), d, plain)), True{}, Fs.sealed_seal(keys, prot, d, plain))
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
      ec = P.Some.inj(Sec.Nas.Count, c, c1, e)
      (%ec : {N.Fresh.run(ms2, keys, c) == N.Fresh.run(ms2, keys, _) : Maybe<&2, Sec.Nas.Count>}; {==})
    case +m <> +more:
      Fs.run_then(m, more, ms2, keys, c, c1, Sec.Nas.sealed(keys, c, m), {==}, e, e2 => Fs.run_app(more, ms2, keys, Sec.Nas.Count.next(c), c1, e2))

# A context unchanged, no message: what a write of it holds.
def Fs.holds_self(+b: Maybe<&2, Sec.Nas.Ctx>) -> {N.Fresh.holds(b, b, []) == True{} : Bool}:
  match b:
    case None{}:
      {==}
    case Some{Sec.Ctx{+k, +d, +ul}}:
      e = Equal.sym(Bool, Sec.Nas.Keys.same(k, k), True{}, Fs.keys_same(k))
      (%e : {N.Fresh.at(Some{N.Fresh.start_if(d, _)}, d) == True{} : Bool}; Fs.count_same(d))
