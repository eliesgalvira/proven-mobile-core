import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../LAWS.bend as L
import ./lib.bend as P

# Results
# -------

def Rd.value(-A: Data, r: Ap.Rd(A), d: A) -> A:
  match r:
    case Fail{e}:
      d
    case Done{(v, c)}:
      v

def Rd.cur(-A: Data, r: Ap.Rd(A), d: Ap.Cur) -> Ap.Cur:
  match r:
    case Fail{e}:
      d
    case Done{(v, c)}:
      c

def Cur.rem(c: Ap.Cur) -> Nat:
  match c:
    case Ap.Cur{rem, bits}:
      rem

def Cur.bits(c: Ap.Cur) -> Ap.Bits():
  match c:
    case Ap.Cur{rem, bits}:
      bits

def Rd.absurd(-A: Data, -G: Type, err: B.Err, v: A, c: Ap.Cur, e: {Fail{err} == Done{(v, c)} : Ap.Rd(A)}) -> G:
  Empty.absurd(G, P.Refute.fail_done(B.Err, Sigma<&2, &2, A, _ => Ap.Cur>, err, (v, c), e))

# Bit lists
# ---------

def Bits.app_assoc(xs: Ap.Bits(), +ys: Ap.Bits(), +zs: Ap.Bits()) -> {List.append(&2, Bool, xs, List.append(&2, Bool, ys, zs)) == List.append(&2, Bool, List.append(&2, Bool, xs, ys), zs) : Ap.Bits()}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      Equal.cong(Ap.Bits(), Ap.Bits(), l => x <> l, List.append(&2, Bool, t, List.append(&2, Bool, ys, zs)), List.append(&2, Bool, List.append(&2, Bool, t, ys), zs), Bits.app_assoc(t, ys, zs))

def Bits.app_len(xs: Ap.Bits(), +ys: Ap.Bits()) -> {Nat.add(List.length(&2, Bool, xs), List.length(&2, Bool, ys)) == List.length(&2, Bool, List.append(&2, Bool, xs, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(List.length(&2, Bool, t), List.length(&2, Bool, ys)), List.length(&2, Bool, List.append(&2, Bool, t, ys)), Bits.app_len(t, ys))

def Nat.add_one(a: Nat) -> {1n+a == Nat.add(a, 1n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, 1n+p, Nat.add(p, 1n), Nat.add_one(p))

def Bits.rev_go(xs: Ap.Bits(), +acc: Ap.Bits()) -> {List.append(&2, Bool, List.reverse(&2, Bool, xs), acc) == List.reverse.go(&2, Bool, xs, acc) : Ap.Bits()}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      ih1 = Bits.rev_go(t, x <> acc)
      %ih1 : {List.append(&2, Bool, List.reverse.go(&2, Bool, t, [x]), acc) == _ : Ap.Bits()}
      ih2 = Bits.rev_go(t, [x])
      %ih2 : {List.append(&2, Bool, _, acc) == List.append(&2, Bool, List.reverse(&2, Bool, t), x <> acc) : Ap.Bits()}
      Equal.sym(Ap.Bits(), List.append(&2, Bool, List.reverse(&2, Bool, t), x <> acc), List.append(&2, Bool, List.append(&2, Bool, List.reverse(&2, Bool, t), [x]), acc), Bits.app_assoc(List.reverse(&2, Bool, t), [x], acc))

def Bits.rev_snoc(ys: Ap.Bits(), +x: Bool) -> {x <> List.reverse(&2, Bool, ys) == List.reverse(&2, Bool, List.append(&2, Bool, ys, [x])) : Ap.Bits()}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      r1 = Bits.rev_go(List.append(&2, Bool, t, [x]), [y])
      %r1 : {x <> List.reverse(&2, Bool, y <> t) == _ : Ap.Bits()}
      ih = Bits.rev_snoc(t, x)
      %ih : {x <> List.reverse(&2, Bool, y <> t) == List.append(&2, Bool, _, [y]) : Ap.Bits()}
      r2 = Bits.rev_go(t, [y])
      %r2 : {x <> _ == x <> List.append(&2, Bool, List.reverse(&2, Bool, t), [y]) : Ap.Bits()}
      {==}

def Bits.rev_rev(xs: Ap.Bits()) -> {xs == List.reverse(&2, Bool, List.reverse(&2, Bool, xs)) : Ap.Bits()}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      r = Bits.rev_go(t, [x])
      %r : {x <> t == List.reverse(&2, Bool, _) : Ap.Bits()}
      s = Bits.rev_snoc(List.reverse(&2, Bool, t), x)
      %s : {x <> t == _ : Ap.Bits()}
      Equal.cong(Ap.Bits(), Ap.Bits(), l => x <> l, t, List.reverse(&2, Bool, List.reverse(&2, Bool, t)), Bits.rev_rev(t))

def Bits.rev_len(xs: Ap.Bits()) -> {List.length(&2, Bool, xs) == List.length(&2, Bool, List.reverse(&2, Bool, xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      r = Bits.rev_go(t, [x])
      %r : {1n+List.length(&2, Bool, t) == List.length(&2, Bool, _) : Nat}
      al = Bits.app_len(List.reverse(&2, Bool, t), [x])
      %al : {1n+List.length(&2, Bool, t) == _ : Nat}
      ao = Nat.add_one(List.length(&2, Bool, List.reverse(&2, Bool, t)))
      %ao : {1n+List.length(&2, Bool, t) == _ : Nat}
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Bool, t), List.length(&2, Bool, List.reverse(&2, Bool, t)), Bits.rev_len(t))

# Reading bits
# ------------

def Bits.go_app(bs: Ap.Bits(), +r: Nat, +rest: Ap.Bits()) -> {Done{(bs, Ap.Cur{r, rest})} == Ap.Bits.go(List.length(&2, Bool, bs), r, List.append(&2, Bool, bs, rest)) : Ap.Rd(Ap.Bits())}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +t:
      ih = Bits.go_app(t, r, rest)
      %ih : {Done{(b <> t, Ap.Cur{r, rest})} == Ap.Bits.cons(b, _) : Ap.Rd(Ap.Bits())}
      {==}

def Bits.Spec(bs: Ap.Bits(), c: Ap.Cur, n: Nat, r: Nat) -> Type:
  {List.length(&2, Bool, bs) == n : Nat} & {r == Cur.rem(c) : Nat}

def Bits.spec.finish(+p: Nat, +b: Bool, +bs2: Ap.Bits(), +c2: Ap.Cur, +r: Nat, s: Bits.Spec(bs2, c2, p, r)) -> Bits.Spec(b <> bs2, c2, 1n+p, r):
  (len, rm) = s
  (Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Bool, bs2), p, len), rm)

def Bits.spec.step(+p: Nat, +b: Bool, +r: Nat, rb: Ap.Rd(Ap.Bits()), ih: @bs2: Ap.Bits() -> @c2: Ap.Cur -> {rb == Done{(bs2, c2)} : Ap.Rd(Ap.Bits())} -> Bits.Spec(bs2, c2, p, r), +bs: Ap.Bits(), +c: Ap.Cur, +e: {Ap.Bits.cons(b, rb) == Done{(bs, c)} : Ap.Rd(Ap.Bits())}) -> Bits.Spec(bs, c, 1n+p, r):
  match rb:
    case Fail{err}:
      Rd.absurd(Ap.Bits(), Bits.Spec(bs, c, 1n+p, r), err, bs, c, e)
    case Done{(+bs2, +c2)}:
      ev = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Bits(), x => Rd.value(Ap.Bits(), x, bs), Done{(b <> bs2, c2)}, Done{(bs, c)}, e)
      ec = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Cur, x => Rd.cur(Ap.Bits(), x, c), Done{(b <> bs2, c2)}, Done{(bs, c)}, e)
      %ev : Bits.Spec(_, c, 1n+p, r)
      %ec : Bits.Spec(b <> bs2, _, 1n+p, r)
      Bits.spec.finish(p, b, bs2, c2, r, ih(bs2, c2, {==}))

# What Bits.go read has the length it was asked for, and ends at the rem it was given.
def Bits.spec(n: Nat, +r: Nat, bits: Ap.Bits(), +bs: Ap.Bits(), +c: Ap.Cur, +e: {Ap.Bits.go(n, r, bits) == Done{(bs, c)} : Ap.Rd(Ap.Bits())}) -> Bits.Spec(bs, c, n, r):
  match n bits:
    case 0n rest:
      ev = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Bits(), x => Rd.value(Ap.Bits(), x, bs), Done{([], Ap.Cur{r, rest})}, Done{(bs, c)}, e)
      ec = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Cur, x => Rd.cur(Ap.Bits(), x, c), Done{([], Ap.Cur{r, rest})}, Done{(bs, c)}, e)
      %ev : Bits.Spec(_, c, 0n, r)
      %ec : Bits.Spec([], _, 0n, r)
      ({==}, {==})
    case 1n++p Nil{}:
      Rd.absurd(Ap.Bits(), Bits.Spec(bs, c, 1n+p, r), B.Short{}, bs, c, e)
    case 1n+p b <> +t:
      Bits.spec.step(p, b, r, Ap.Bits.go(p, r, t), bs2 => c2 => e2 => Bits.spec(p, r, t, bs2, c2, e2), bs, c, e)

def Bits.len(+bs: Ap.Bits(), +c: Ap.Cur, +n: Nat, +r: Nat, s: Bits.Spec(bs, c, n, r)) -> {List.length(&2, Bool, bs) == n : Nat}:
  (len, rm) = s
  len

def Bits.rem(+bs: Ap.Bits(), +c: Ap.Cur, +n: Nat, +r: Nat, s: Bits.Spec(bs, c, n, r)) -> {r == Cur.rem(c) : Nat}:
  (len, rm) = s
  rm

# Alignment
# ---------

def Align.rt(rem: Nat, +rest: Ap.Bits()) -> {Done{(Unit{}, Ap.Cur{0n, rest})} == Ap.Align.go(rem, Ap.Align.write(rem, rest)) : Ap.Rd(Unit)}:
  match rem:
    case 0n:
      {==}
    case 1n+p:
      Align.rt(p, rest)

def Align.pad(rem: Nat, bits: Ap.Bits(), +r2: Nat, +rest: Ap.Bits(), +e: {Ap.Align.go(rem, bits) == Done{(Unit{}, Ap.Cur{r2, rest})} : Ap.Rd(Unit)}) -> {bits == Ap.Align.write(rem, rest) : Ap.Bits()}:
  match rem bits:
    case 0n bs:
      Equal.cong(Ap.Rd(Unit), Ap.Bits(), x => Cur.bits(Rd.cur(Unit, x, Ap.Cur{0n, []})), Done{(Unit{}, Ap.Cur{0n, bs})}, Done{(Unit{}, Ap.Cur{r2, rest})}, e)
    case 1n+p Nil{}:
      Rd.absurd(Unit, {[] == Ap.Align.write(1n+p, rest) : Ap.Bits()}, B.Short{}, Unit{}, Ap.Cur{r2, rest}, e)
    case 1n+p b <> +t:
      match b:
        case True{}:
          Rd.absurd(Unit, {True{} <> t == Ap.Align.write(1n+p, rest) : Ap.Bits()}, B.Invalid{0}, Unit{}, Ap.Cur{r2, rest}, e)
        case False{}:
          Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, t, Ap.Align.write(p, rest), Align.pad(p, t, r2, rest, e))

# Words
# -----

def Nat.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Word.of_prefix.zero(+q: Nat, b: Bool, +t: Word(q), hz: {Bool.and(Bool.not(b), Ap.Word.high_zero(q, t, 0n)) == True{} : Bool}, ih: {Ap.Word.high_zero(q, t, 0n) == True{} : Bool} -> {t == Ap.Word.of_lsb(q, []) : Word(q)}) -> {WCon{b, t} == WCon{False{}, Ap.Word.of_lsb(q, [])} : Word(1n+q)}:
  match b:
    case True{}:
      Empty.absurd({WCon{True{}, t} == WCon{False{}, Ap.Word.of_lsb(q, [])} : Word(1n+q)}, P.Refute.bool(P.Bool.and_true_l(Bool.not(True{}), Ap.Word.high_zero(q, t, 0n), hz)))
    case False{}:
      Equal.cong(Word(q), Word(1n+q), x => WCon{False{}, x}, t, Ap.Word.of_lsb(q, []), ih(P.Bool.and_true_r(Bool.not(False{}), Ap.Word.high_zero(q, t, 0n), hz)))

def Word.of_prefix(m: Nat, w: Word(m), n: Nat, hz: {Ap.Word.high_zero(m, w, n) == True{} : Bool}) -> {w == Ap.Word.of_lsb(m, Ap.Word.prefix(n, m, w)) : Word(m)}:
  match m:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++q:
      match w:
        case WCon{b, +t}:
          match n:
            case 0n:
              Word.of_prefix.zero(q, b, t, hz, h => Word.of_prefix(q, t, 0n, h))
            case 1n+p:
              Equal.cong(Word(q), Word(1n+q), x => WCon{b, x}, t, Ap.Word.of_lsb(q, Ap.Word.prefix(p, q, t)), Word.of_prefix(q, t, p, hz))

def Word.prefix_of(m: Nat, ls: Ap.Bits(), le: {Nat.is_le(List.length(&2, Bool, ls), m) == True{} : Bool}) -> {ls == Ap.Word.prefix(List.length(&2, Bool, ls), m, Ap.Word.of_lsb(m, ls)) : Ap.Bits()}:
  match m ls:
    case 0n Nil{}:
      {==}
    case 0n b <> t:
      Empty.absurd({b <> t == Ap.Word.prefix(List.length(&2, Bool, b <> t), 0n, Ap.Word.of_lsb(0n, b <> t)) : Ap.Bits()}, P.Refute.bool(le))
    case 1n+q Nil{}:
      {==}
    case 1n+q b <> +t:
      Equal.cong(Ap.Bits(), Ap.Bits(), l => b <> l, t, Ap.Word.prefix(List.length(&2, Bool, t), q, Ap.Word.of_lsb(q, t)), Word.prefix_of(q, t, le))

def Word.prefix_len(n: Nat, m: Nat, w: Word(m)) -> {List.length(&2, Bool, Ap.Word.prefix(n, m, w)) == n : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+p 0n:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Bool, Ap.Word.prefix(p, 0n, w)), p, Word.prefix_len(p, 0n, w))
    case 1n+p 1n+q:
      match w:
        case WCon{b, t}:
          Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Bool, Ap.Word.prefix(p, q, t)), p, Word.prefix_len(p, q, t))

def Word.high_zero_of(m: Nat, n: Nat, ls: Ap.Bits(), le: {Nat.is_le(List.length(&2, Bool, ls), n) == True{} : Bool}) -> {Ap.Word.high_zero(m, Ap.Word.of_lsb(m, ls), n) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      match n ls:
        case 0n Nil{}:
          Word.high_zero_of(q, 0n, [], {==})
        case 0n b <> t:
          Empty.absurd({Ap.Word.high_zero(1n+q, Ap.Word.of_lsb(1n+q, b <> t), 0n) == True{} : Bool}, P.Refute.bool(le))
        case 1n++p Nil{}:
          Word.high_zero_of(q, p, [], Nat.le_zero(p))
        case 1n+p b <> t:
          Word.high_zero_of(q, p, t, le)

def U32.of_to(+n: Nat, x: U32, f: {Ap.U32.fits(n, x) == True{} : Bool}) -> {x == Ap.U32.of_bits(Ap.U32.to_bits(n, x)) : U32}:
  match x:
    case U32{+w}:
      rr = Bits.rev_rev(Ap.Word.prefix(n, 32n, w))
      %rr : {U32{w} == U32{Ap.Word.of_lsb(32n, _)} : U32}
      Equal.cong(Word(32n), U32, v => U32{v}, w, Ap.Word.of_lsb(32n, Ap.Word.prefix(n, 32n, w)), Word.of_prefix(32n, w, n, f))

def U32.to_bits_len(+n: Nat, x: U32) -> {List.length(&2, Bool, Ap.U32.to_bits(n, x)) == n : Nat}:
  match x:
    case U32{+w}:
      rl = Bits.rev_len(Ap.Word.prefix(n, 32n, w))
      %rl : {_ == n : Nat}
      Word.prefix_len(n, 32n, w)

def U32.fits_of(+n: Nat, +bs: Ap.Bits(), e: {List.length(&2, Bool, bs) == n : Nat}) -> {Ap.U32.fits(n, Ap.U32.of_bits(bs)) == True{} : Bool}:
  rl = Bits.rev_len(bs)
  se = Equal.sym(Nat, List.length(&2, Bool, bs), n, e)
  Word.high_zero_of(32n, n, List.reverse(&2, Bool, bs), (%rl : {Nat.is_le(_, n) == True{} : Bool}; (%se : {Nat.is_le(_, n) == True{} : Bool}; P.Nat.le_refl(n))))

def U32.byte_fits.go(d: U32, +d2: U32, same: {d == d2 : U32}, m8: {U32.and(255, d2) == d2 : U32}) -> {Ap.U32.fits(8n, d2) == True{} : Bool}:
  match d:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %m8 : {Ap.U32.fits(8n, _) == True{} : Bool}
      %same : {Ap.U32.fits(8n, U32.and(255, _)) == True{} : Bool}
      {==}

# A byte fits eight bits.
def U32.byte_fits(+b: U32, e: {B.is_byte(b) == True{} : Bool}) -> {Ap.U32.fits(8n, b) == True{} : Bool}:
  U32.byte_fits.go(b, b, {==}, P.U32.lt256_mask8(b, e))

# Constrained whole numbers
# -------------------------

def L.aper.bit.roundtrip(b, rem, rest):
  {==}

def L.aper.bits.roundtrip(bs, rem, rest):
  Equal.sym(Ap.Rd(Ap.Bits()), Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), rem), rest})}, Ap.Bits.go(List.length(&2, Bool, bs), Ap.Rem.add(List.length(&2, Bool, bs), rem), List.append(&2, Bool, bs, rest)), Bits.go_app(bs, Ap.Rem.add(List.length(&2, Bool, bs), rem), rest))

def L.aper.align.roundtrip(rem, rest):
  Equal.sym(Ap.Rd(Unit), Done{(Unit{}, Ap.Cur{0n, rest})}, Ap.Align.go(rem, Ap.Align.write(rem, rest)), Align.rt(rem, rest))

def L.aper.padding_zero(rem, bits, r2, rest, e):
  Align.pad(rem, bits, r2, rest, e)

def Int.rt(+n: Nat, +diff: U32, +x: U32, +r: Nat, +rest: Ap.Bits(), +v: {Ap.Int.valid(n, diff, x) == True{} : Bool}) -> {Ap.Int.bits(diff, Ap.Bits.go(n, r, List.append(&2, Bool, Ap.U32.to_bits(n, x), rest))) == Done{(x, Ap.Cur{r, rest})} : Ap.Rd(U32)}:
  tl = U32.to_bits_len(n, x)
  %tl : {Ap.Int.bits(diff, Ap.Bits.go(_, r, List.append(&2, Bool, Ap.U32.to_bits(n, x), rest))) == Done{(x, Ap.Cur{r, rest})} : Ap.Rd(U32)}
  ga = Bits.go_app(Ap.U32.to_bits(n, x), r, rest)
  %ga : {Ap.Int.bits(diff, _) == Done{(x, Ap.Cur{r, rest})} : Ap.Rd(U32)}
  ot = U32.of_to(n, x, P.Bool.and_true_l(Ap.U32.fits(n, x), U32.is_le(x, diff), v))
  %ot : {Ap.Int.of(_, Ap.Cur{r, rest}, U32.is_le(_, diff)) == Done{(x, Ap.Cur{r, rest})} : Ap.Rd(U32)}
  sle = Equal.sym(Bool, U32.is_le(x, diff), True{}, P.Bool.and_true_r(Ap.U32.fits(n, x), U32.is_le(x, diff), v))
  %sle : {Ap.Int.of(x, Ap.Cur{r, rest}, _) == Done{(x, Ap.Cur{r, rest})} : Ap.Rd(U32)}
  {==}

def L.aper.int.roundtrip(n, diff, x, rem, rest, v):
  Int.rt(n, diff, x, Ap.Rem.add(n, rem), rest, v)

def Int.dv.ok(+n: Nat, +diff: U32, +bs: Ap.Bits(), +c: Ap.Cur, ok: Bool, eok: {U32.is_le(Ap.U32.of_bits(bs), diff) == ok : Bool}, +x: U32, +c2: Ap.Cur, +e: {Ap.Int.of(Ap.U32.of_bits(bs), c, ok) == Done{(x, c2)} : Ap.Rd(U32)}, len: {List.length(&2, Bool, bs) == n : Nat}) -> {Ap.Int.valid(n, diff, x) == True{} : Bool}:
  match ok:
    case False{}:
      Rd.absurd(U32, {Ap.Int.valid(n, diff, x) == True{} : Bool}, B.Invalid{Ap.U32.of_bits(bs)}, x, c2, e)
    case True{}:
      ev = Equal.cong(Ap.Rd(U32), U32, y => Rd.value(U32, y, x), Done{(Ap.U32.of_bits(bs), c)}, Done{(x, c2)}, e)
      %ev : {Ap.Int.valid(n, diff, _) == True{} : Bool}
      P.Bool.and_intro(Ap.U32.fits(n, Ap.U32.of_bits(bs)), U32.is_le(Ap.U32.of_bits(bs), diff), U32.fits_of(n, bs, len), eok)

def Int.dv.bits(+n: Nat, +diff: U32, +r: Nat, +bits: Ap.Bits(), rb: Ap.Rd(Ap.Bits()), +erb: {Ap.Bits.go(n, r, bits) == rb : Ap.Rd(Ap.Bits())}, +x: U32, +c2: Ap.Cur, +e: {Ap.Int.bits(diff, rb) == Done{(x, c2)} : Ap.Rd(U32)}) -> {Ap.Int.valid(n, diff, x) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(U32, {Ap.Int.valid(n, diff, x) == True{} : Bool}, err, x, c2, e)
    case Done{(+bs, +c)}:
      Int.dv.ok(n, diff, bs, c, U32.is_le(Ap.U32.of_bits(bs), diff), {==}, x, c2, e, Bits.len(bs, c, n, r, Bits.spec(n, r, bits, bs, c, erb)))

def Int.dv(+n: Nat, +diff: U32, c: Ap.Cur, +x: U32, +c2: Ap.Cur, +e: {Ap.Int.read(n, diff, c) == Done{(x, c2)} : Ap.Rd(U32)}) -> {Ap.Int.valid(n, diff, x) == True{} : Bool}:
  match c:
    case Ap.Cur{+rem, +bits}:
      Int.dv.bits(n, diff, Ap.Rem.add(n, rem), bits, Ap.Bits.go(n, Ap.Rem.add(n, rem), bits), {==}, x, c2, e)

def L.aper.int.decode_valid(n, diff, c, x, c2, e):
  Int.dv(n, diff, c, x, c2, e)

def L.aper.aint.roundtrip(n, diff, x, rem, rest, v):
  ar = Align.rt(rem, Ap.Int.write(n, x, 0n, rest))
  %ar : {Ap.AInt.aligned(n, diff, _) == Done{(x, Ap.Cur{Ap.Rem.add(n, 0n), rest})} : Ap.Rd(U32)}
  Int.rt(n, diff, x, Ap.Rem.add(n, 0n), rest, v)

def AInt.dv(+n: Nat, +diff: U32, ra: Ap.Rd(Unit), +x: U32, +c2: Ap.Cur, +e: {Ap.AInt.aligned(n, diff, ra) == Done{(x, c2)} : Ap.Rd(U32)}) -> {Ap.Int.valid(n, diff, x) == True{} : Bool}:
  match ra:
    case Fail{err}:
      Rd.absurd(U32, {Ap.Int.valid(n, diff, x) == True{} : Bool}, err, x, c2, e)
    case Done{(u, c)}:
      Int.dv(n, diff, c, x, c2, e)

def L.aper.aint.decode_valid(n, diff, c, x, c2, e):
  AInt.dv(n, diff, Ap.Align.read(c), x, c2, e)

def L.aper.small.roundtrip(v, rem, rest, ok):
  Int.rt(6n, 63, v, Ap.Rem.add(6n, Ap.Rem.next(rem)), rest, ok)

def Small.dv(rb: Ap.Rd(Bool), +v: U32, +c2: Ap.Cur, +e: {Ap.Small.form(rb) == Done{(v, c2)} : Ap.Rd(U32)}) -> {Ap.Small.valid(v) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(U32, {Ap.Small.valid(v) == True{} : Bool}, err, v, c2, e)
    case Done{(b, c)}:
      match b:
        case True{}:
          Rd.absurd(U32, {Ap.Small.valid(v) == True{} : Bool}, B.Unsupported{64}, v, c2, e)
        case False{}:
          Int.dv(6n, 63, c, v, c2, e)

def L.aper.small.decode_valid(c, v, c2, e):
  Small.dv(Ap.Bit.read(c), v, c2, e)

# Nat
# ---

def Nat.not_lt_zero(-G: Type, p: Nat, e: {Nat.is_lt(p, 0n) == True{} : Bool}) -> G:
  match p:
    case 0n:
      Empty.absurd(G, P.Refute.bool(e))
    case 1n+q:
      Empty.absurd(G, P.Refute.bool(e))

def Nat.add_succ(a: Nat, +b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, 1n+Nat.add(p, b), Nat.add(p, 1n+b), Nat.add_succ(p, b))

def Nat.bit(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def Nat.of_lsb_cons(b: Bool, +rest: Ap.Bits()) -> {Nat.add(Nat.bit(b), Nat.double(Ap.Nat.of_lsb(rest))) == Ap.Nat.of_lsb(b <> rest) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Nat.odd_half(k: Nat) -> {k == Nat.add(Nat.bit(Ap.Nat.is_odd(k)), Nat.double(Ap.Nat.half(k))) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n++j:
      a1 = Nat.add_succ(Nat.bit(Ap.Nat.is_odd(j)), 1n+Nat.double(Ap.Nat.half(j)))
      %a1 : {2n+j == _ : Nat}
      a2 = Nat.add_succ(Nat.bit(Ap.Nat.is_odd(j)), Nat.double(Ap.Nat.half(j)))
      %a2 : {2n+j == 1n+_ : Nat}
      Equal.cong(Nat, Nat, n => 2n+n, j, Nat.add(Nat.bit(Ap.Nat.is_odd(j)), Nat.double(Ap.Nat.half(j))), Nat.odd_half(j))

def Nat.double_lt(a: Nat, m: Nat, e: {Nat.is_lt(a, m) == True{} : Bool}) -> {Nat.is_lt(Nat.double(a), Nat.double(m)) == True{} : Bool}:
  match a m:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, P.Refute.bool(e))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(Nat.double(1n+p), 0n) == True{} : Bool}, P.Refute.bool(e))
    case 1n+p 1n+q:
      Nat.double_lt(p, q, e)

def Nat.double_lt1(a: Nat, m: Nat, e: {Nat.is_lt(a, m) == True{} : Bool}) -> {Nat.is_lt(1n+Nat.double(a), Nat.double(m)) == True{} : Bool}:
  match a m:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, P.Refute.bool(e))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+Nat.double(1n+p), 0n) == True{} : Bool}, P.Refute.bool(e))
    case 1n+p 1n+q:
      Nat.double_lt1(p, q, e)

def Nat.half_lt(k: Nat, m: Nat, e: {Nat.is_lt(k, Nat.double(m)) == True{} : Bool}) -> {Nat.is_lt(Ap.Nat.half(k), m) == True{} : Bool}:
  match k m:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, P.Refute.bool(e))
    case 0n 1n+q:
      {==}
    case 1n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, P.Refute.bool(e))
    case 1n 1n+q:
      {==}
    case 2n+j 0n:
      Empty.absurd({Nat.is_lt(1n+Ap.Nat.half(j), 0n) == True{} : Bool}, P.Refute.bool(e))
    case 2n+j 1n+q:
      Nat.half_lt(j, q, e)

def Nat.double_pos(x: Nat, e: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, P.Refute.bool(e))
    case 1n+p:
      {==}

def Nat.pow2_pos(n: Nat) -> {Nat.is_lt(0n, Ap.Nat.pow2(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      Nat.double_pos(Ap.Nat.pow2(p), Nat.pow2_pos(p))

def Nat.of_to(n: Nat, +k: Nat, lt: {Nat.is_lt(k, Ap.Nat.pow2(n)) == True{} : Bool}) -> {k == Ap.Nat.of_lsb(Ap.Nat.to_lsb(n, k)) : Nat}:
  match n:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+p:
          Nat.not_lt_zero({1n+p == 0n : Nat}, p, lt)
    case 1n++p:
      oc = Nat.of_lsb_cons(Ap.Nat.is_odd(k), Ap.Nat.to_lsb(p, Ap.Nat.half(k)))
      %oc : {k == _ : Nat}
      ih = Nat.of_to(p, Ap.Nat.half(k), Nat.half_lt(k, Ap.Nat.pow2(p), lt))
      %ih : {k == Nat.add(Nat.bit(Ap.Nat.is_odd(k)), Nat.double(_)) : Nat}
      Nat.odd_half(k)

def Nat.of_lsb_lt(ls: Ap.Bits()) -> {Nat.is_lt(Ap.Nat.of_lsb(ls), Ap.Nat.pow2(List.length(&2, Bool, ls))) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case b <> +t:
      match b:
        case False{}:
          Nat.double_lt(Ap.Nat.of_lsb(t), Ap.Nat.pow2(List.length(&2, Bool, t)), Nat.of_lsb_lt(t))
        case True{}:
          Nat.double_lt1(Ap.Nat.of_lsb(t), Ap.Nat.pow2(List.length(&2, Bool, t)), Nat.of_lsb_lt(t))

def Nat.le_lt_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_le(a, b) == True{} : Bool}, e2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n b2 0n:
      Nat.not_lt_zero({Nat.is_lt(0n, 0n) == True{} : Bool}, b2, e2)
    case 0n b2 1n+r:
      {==}
    case 1n+p 0n c2:
      Empty.absurd({Nat.is_lt(1n+p, c2) == True{} : Bool}, P.Refute.bool(e1))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, P.Refute.bool(e2))
    case 1n+p 1n+q 1n+r:
      Nat.le_lt_trans(p, q, r, e1, e2)

def Nat.lt_le_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_lt(a, b) == True{} : Bool}, e2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case a2 0n c2:
      Nat.not_lt_zero({Nat.is_lt(a2, c2) == True{} : Bool}, a2, e1)
    case 0n 1n+q 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, P.Refute.bool(e2))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, P.Refute.bool(e2))
    case 1n+p 1n+q 1n+r:
      Nat.lt_le_trans(p, q, r, e1, e2)

def Nat.sub_zero(k: Nat) -> {k == Nat.sub(k, 0n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Nat.add_sub(lo: Nat, k: Nat, e: {Nat.is_le(lo, k) == True{} : Bool}) -> {k == Nat.add(lo, Nat.sub(k, lo)) : Nat}:
  match lo k:
    case 0n k2:
      Nat.sub_zero(k2)
    case 1n+l 0n:
      Empty.absurd({0n == Nat.add(1n+l, Nat.sub(0n, 1n+l)) : Nat}, P.Refute.bool(e))
    case 1n+l 1n+k2:
      Equal.cong(Nat, Nat, n => 1n+n, k2, Nat.add(l, Nat.sub(k2, l)), Nat.add_sub(l, k2, e))

def Nat.sub_le(lo: Nat, k: Nat, +hi: Nat, e1: {Nat.is_le(lo, k) == True{} : Bool}, e2: {Nat.is_le(k, Nat.add(lo, hi)) == True{} : Bool}) -> {Nat.is_le(Nat.sub(k, lo), hi) == True{} : Bool}:
  match lo k:
    case 0n k2:
      sz = Nat.sub_zero(k2)
      %sz : {Nat.is_le(_, hi) == True{} : Bool}
      e2
    case 1n+l 0n:
      Empty.absurd({Nat.is_le(Nat.sub(0n, 1n+l), hi) == True{} : Bool}, P.Refute.bool(e1))
    case 1n+l 1n+k2:
      Nat.sub_le(l, k2, hi, e1, e2)

def Nat.le_add(lo: Nat, +x: Nat) -> {Nat.is_le(lo, Nat.add(lo, x)) == True{} : Bool}:
  match lo:
    case 0n:
      Nat.le_zero(x)
    case 1n+l:
      Nat.le_add(l, x)

def Nat.add_le(lo: Nat, +x: Nat, +d: Nat, e: {Nat.is_le(x, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(lo, x), Nat.add(lo, d)) == True{} : Bool}:
  match lo:
    case 0n:
      e
    case 1n+l:
      Nat.add_le(l, x, d, e)

def Nat.le_of_not_lt(a: Nat, b: Nat, e: {Nat.is_lt(b, a) == False{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n b2:
      Nat.le_zero(b2)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, P.Refute.true_false(e))
    case 1n+p 1n+q:
      Nat.le_of_not_lt(p, q, e)

def Nat.to_lsb_len(n: Nat, +k: Nat) -> {List.length(&2, Bool, Ap.Nat.to_lsb(n, k)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, m => 1n+m, List.length(&2, Bool, Ap.Nat.to_lsb(p, Ap.Nat.half(k))), p, Nat.to_lsb_len(p, Ap.Nat.half(k)))

def Nat.to_bits_len(+n: Nat, +k: Nat) -> {List.length(&2, Bool, Ap.Nat.to_bits(n, k)) == n : Nat}:
  rl = Bits.rev_len(Ap.Nat.to_lsb(n, k))
  %rl : {_ == n : Nat}
  Nat.to_lsb_len(n, k)

def Nat.of_to_bits(+n: Nat, +k: Nat, lt: {Nat.is_lt(k, Ap.Nat.pow2(n)) == True{} : Bool}) -> {k == Ap.Nat.of_bits(Ap.Nat.to_bits(n, k)) : Nat}:
  rr = Bits.rev_rev(Ap.Nat.to_lsb(n, k))
  %rr : {k == Ap.Nat.of_lsb(_) : Nat}
  Nat.of_to(n, k, lt)

# Length determinants
# -------------------

def Len.rt.body(+n: Nat, short: Bool, es: {Nat.is_lt(n, 128n) == short : Bool}, +rest: Ap.Bits(), +v: {Nat.is_lt(n, 16384n) == True{} : Bool}) -> {Ap.Len.first(Ap.Len.body(n, short, rest)) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}:
  match short:
    case True{}:
      tl = Nat.to_bits_len(7n, n)
      %tl : {Ap.Len.short(Ap.Bits.go(_, 0n, List.append(&2, Bool, Ap.Nat.to_bits(7n, n), rest))) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      ga = Bits.go_app(Ap.Nat.to_bits(7n, n), 0n, rest)
      %ga : {Ap.Len.short(_) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      ot = Nat.of_to_bits(7n, n, Nat.lt_le_trans(n, 128n, Ap.Nat.pow2(7n), es, {==}))
      %ot : {Done{(_, Ap.Cur{0n, rest})} == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      {==}
    case False{}:
      tl = Nat.to_bits_len(14n, n)
      %tl : {Ap.Len.long(Ap.Bits.go(_, 0n, List.append(&2, Bool, Ap.Nat.to_bits(14n, n), rest))) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      ga = Bits.go_app(Ap.Nat.to_bits(14n, n), 0n, rest)
      %ga : {Ap.Len.long(_) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      ot = Nat.of_to_bits(14n, n, Nat.lt_le_trans(n, 16384n, Ap.Nat.pow2(14n), v, {==}))
      %ot : {Ap.Len.of(_, Ap.Cur{0n, rest}, Nat.is_le(128n, _)) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      sle = Equal.sym(Bool, Nat.is_le(128n, n), True{}, Nat.le_of_not_lt(128n, n, es))
      %sle : {Ap.Len.of(n, Ap.Cur{0n, rest}, _) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      {==}

def L.aper.len.roundtrip(n, rem, rest, v):
  ar = Align.rt(rem, Ap.Len.body(n, Nat.is_lt(n, 128n), rest))
  %ar : {Ap.Len.aligned(_) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
  Len.rt.body(n, Nat.is_lt(n, 128n), {==}, rest, v)

# The value of w bits read is below 2^w.
def Len.bound(+bs: Ap.Bits(), +w: Nat, len: {List.length(&2, Bool, bs) == w : Nat}) -> {Nat.is_lt(Ap.Nat.of_bits(bs), Ap.Nat.pow2(w)) == True{} : Bool}:
  srl = Equal.sym(Nat, List.length(&2, Bool, bs), List.length(&2, Bool, List.reverse(&2, Bool, bs)), Bits.rev_len(bs))
  %len : {Nat.is_lt(Ap.Nat.of_lsb(List.reverse(&2, Bool, bs)), Ap.Nat.pow2(_)) == True{} : Bool}
  %srl : {Nat.is_lt(Ap.Nat.of_lsb(List.reverse(&2, Bool, bs)), Ap.Nat.pow2(_)) == True{} : Bool}
  Nat.of_lsb_lt(List.reverse(&2, Bool, bs))

# What a length determinant yields: below 16384, and an aligned cursor.
def Len.Spec(n: Nat, c: Ap.Cur) -> Type:
  {Nat.is_lt(n, 16384n) == True{} : Bool} & {0n == Cur.rem(c) : Nat}

def Len.dv.short(rb: Ap.Rd(Ap.Bits()), +bits: Ap.Bits(), +erb: {Ap.Bits.go(7n, 0n, bits) == rb : Ap.Rd(Ap.Bits())}, +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.short(rb) == Done{(n, c2)} : Ap.Rd(Nat)}) -> Len.Spec(n, c2):
  match rb:
    case Fail{err}:
      Rd.absurd(Nat, Len.Spec(n, c2), err, n, c2, e)
    case Done{(+bs, +c)}:
      ev = Equal.cong(Ap.Rd(Nat), Nat, y => Rd.value(Nat, y, n), Done{(Ap.Nat.of_bits(bs), c)}, Done{(n, c2)}, e)
      ec = Equal.cong(Ap.Rd(Nat), Ap.Cur, y => Rd.cur(Nat, y, c2), Done{(Ap.Nat.of_bits(bs), c)}, Done{(n, c2)}, e)
      %ev : Len.Spec(_, c2)
      %ec : Len.Spec(Ap.Nat.of_bits(bs), _)
      (Nat.lt_le_trans(Ap.Nat.of_bits(bs), Ap.Nat.pow2(7n), 16384n, Len.bound(bs, 7n, Bits.len(bs, c, 7n, 0n, Bits.spec(7n, 0n, bits, bs, c, erb))), {==}), Bits.rem(bs, c, 7n, 0n, Bits.spec(7n, 0n, bits, bs, c, erb)))

def Len.dv.long.ok(+bs: Ap.Bits(), +c: Ap.Cur, ok: Bool, +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.of(Ap.Nat.of_bits(bs), c, ok) == Done{(n, c2)} : Ap.Rd(Nat)}, len: {List.length(&2, Bool, bs) == 14n : Nat}, rm: {0n == Cur.rem(c) : Nat}) -> Len.Spec(n, c2):
  match ok:
    case False{}:
      Rd.absurd(Nat, Len.Spec(n, c2), B.Invalid{128}, n, c2, e)
    case True{}:
      ev = Equal.cong(Ap.Rd(Nat), Nat, y => Rd.value(Nat, y, n), Done{(Ap.Nat.of_bits(bs), c)}, Done{(n, c2)}, e)
      ec = Equal.cong(Ap.Rd(Nat), Ap.Cur, y => Rd.cur(Nat, y, c2), Done{(Ap.Nat.of_bits(bs), c)}, Done{(n, c2)}, e)
      %ev : Len.Spec(_, c2)
      %ec : Len.Spec(Ap.Nat.of_bits(bs), _)
      (Nat.lt_le_trans(Ap.Nat.of_bits(bs), Ap.Nat.pow2(14n), 16384n, Len.bound(bs, 14n, len), {==}), rm)

def Len.dv.long(rb: Ap.Rd(Ap.Bits()), +bits: Ap.Bits(), +erb: {Ap.Bits.go(14n, 0n, bits) == rb : Ap.Rd(Ap.Bits())}, +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.long(rb) == Done{(n, c2)} : Ap.Rd(Nat)}) -> Len.Spec(n, c2):
  match rb:
    case Fail{err}:
      Rd.absurd(Nat, Len.Spec(n, c2), err, n, c2, e)
    case Done{(+bs, +c)}:
      Len.dv.long.ok(bs, c, Nat.is_le(128n, Ap.Nat.of_bits(bs)), n, c2, e, Bits.len(bs, c, 14n, 0n, Bits.spec(14n, 0n, bits, bs, c, erb)), Bits.rem(bs, c, 14n, 0n, Bits.spec(14n, 0n, bits, bs, c, erb)))

def Len.dv.second(bits: Ap.Bits(), +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.second(bits) == Done{(n, c2)} : Ap.Rd(Nat)}) -> Len.Spec(n, c2):
  match bits:
    case Nil{}:
      Rd.absurd(Nat, Len.Spec(n, c2), B.Short{}, n, c2, e)
    case b <> +rest:
      match b:
        case True{}:
          Rd.absurd(Nat, Len.Spec(n, c2), B.Unsupported{192}, n, c2, e)
        case False{}:
          Len.dv.long(Ap.Bits.go(14n, 0n, rest), rest, {==}, n, c2, e)

def Len.dv.first(bits: Ap.Bits(), +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.first(bits) == Done{(n, c2)} : Ap.Rd(Nat)}) -> Len.Spec(n, c2):
  match bits:
    case Nil{}:
      Rd.absurd(Nat, Len.Spec(n, c2), B.Short{}, n, c2, e)
    case b <> +rest:
      match b:
        case False{}:
          Len.dv.short(Ap.Bits.go(7n, 0n, rest), rest, {==}, n, c2, e)
        case True{}:
          Len.dv.second(rest, n, c2, e)

def Len.dv(ra: Ap.Rd(Unit), +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.aligned(ra) == Done{(n, c2)} : Ap.Rd(Nat)}) -> Len.Spec(n, c2):
  match ra:
    case Fail{err}:
      Rd.absurd(Nat, Len.Spec(n, c2), err, n, c2, e)
    case Done{(u, c)}:
      match c:
        case Ap.Cur{rem, bits}:
          Len.dv.first(bits, n, c2, e)

def Len.lt(+n: Nat, +c: Ap.Cur, s: Len.Spec(n, c)) -> {Nat.is_lt(n, 16384n) == True{} : Bool}:
  (lt, rm) = s
  lt

def Len.aligned_end(+n: Nat, +c: Ap.Cur, s: Len.Spec(n, c)) -> {0n == Cur.rem(c) : Nat}:
  (lt, rm) = s
  rm

def L.aper.no_big_nat(c, n, c2, e):
  Len.lt(n, c2, Len.dv(Ap.Align.read(c), n, c2, e))

# Constrained lengths
# -------------------

def Size.rt.bits(+n: Nat, +lo: Nat, +diff: Nat, +k: Nat, +r: Nat, +rest: Ap.Bits(), +v: {Ap.Size.valid(lo, diff, k) == True{} : Bool}, w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}) -> {Ap.Size.bits(lo, diff, Ap.Bits.go(n, r, List.append(&2, Bool, Ap.Nat.to_bits(n, Nat.sub(k, lo)), rest))) == Done{(k, Ap.Cur{r, rest})} : Ap.Rd(Nat)}:
  tl = Nat.to_bits_len(n, Nat.sub(k, lo))
  %tl : {Ap.Size.bits(lo, diff, Ap.Bits.go(_, r, List.append(&2, Bool, Ap.Nat.to_bits(n, Nat.sub(k, lo)), rest))) == Done{(k, Ap.Cur{r, rest})} : Ap.Rd(Nat)}
  ga = Bits.go_app(Ap.Nat.to_bits(n, Nat.sub(k, lo)), r, rest)
  %ga : {Ap.Size.bits(lo, diff, _) == Done{(k, Ap.Cur{r, rest})} : Ap.Rd(Nat)}
  +le1 = P.Bool.and_true_l(Nat.is_le(lo, k), Nat.is_le(k, Nat.add(lo, diff)), v)
  +kd = Nat.sub_le(lo, k, diff, le1, P.Bool.and_true_r(Nat.is_le(lo, k), Nat.is_le(k, Nat.add(lo, diff)), v))
  ot = Nat.of_to_bits(n, Nat.sub(k, lo), Nat.le_lt_trans(Nat.sub(k, lo), diff, Ap.Nat.pow2(n), kd, w))
  %ot : {Ap.Size.of(lo, _, Ap.Cur{r, rest}, Nat.is_le(_, diff)) == Done{(k, Ap.Cur{r, rest})} : Ap.Rd(Nat)}
  skd = Equal.sym(Bool, Nat.is_le(Nat.sub(k, lo), diff), True{}, kd)
  %skd : {Ap.Size.of(lo, Nat.sub(k, lo), Ap.Cur{r, rest}, _) == Done{(k, Ap.Cur{r, rest})} : Ap.Rd(Nat)}
  as = Nat.add_sub(lo, k, le1)
  %as : {Done{(_, Ap.Cur{r, rest})} == Done{(k, Ap.Cur{r, rest})} : Ap.Rd(Nat)}
  {==}

def Size.rt(al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +k: Nat, +rem: Nat, +rest: Ap.Bits(), +v: {Ap.Size.valid(lo, diff, k) == True{} : Bool}, w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}) -> {Ap.Size.read(al, n, lo, diff, Ap.Cur{rem, Ap.Size.write(al, n, lo, k, rem, rest)}) == Done{(k, Ap.Cur{Ap.Size.after(al, n, rem), rest})} : Ap.Rd(Nat)}:
  match al:
    case False{}:
      Size.rt.bits(n, lo, diff, k, Ap.Rem.add(n, rem), rest, v, w)
    case True{}:
      ar = Align.rt(rem, List.append(&2, Bool, Ap.Nat.to_bits(n, Nat.sub(k, lo)), rest))
      %ar : {Ap.Size.aligned(n, lo, diff, _) == Done{(k, Ap.Cur{Ap.Rem.add(n, 0n), rest})} : Ap.Rd(Nat)}
      Size.rt.bits(n, lo, diff, k, Ap.Rem.add(n, 0n), rest, v, w)

def L.aper.size.roundtrip(al, n, lo, diff, k, rem, rest, v, w):
  Size.rt(al, n, lo, diff, k, rem, rest, v, w)

def Size.dv.ok(+lo: Nat, +diff: Nat, +x: Nat, +c: Ap.Cur, ok: Bool, eok: {Nat.is_le(x, diff) == ok : Bool}, +k: Nat, +c2: Ap.Cur, +e: {Ap.Size.of(lo, x, c, ok) == Done{(k, c2)} : Ap.Rd(Nat)}) -> {Ap.Size.valid(lo, diff, k) == True{} : Bool}:
  match ok:
    case False{}:
      Rd.absurd(Nat, {Ap.Size.valid(lo, diff, k) == True{} : Bool}, B.Invalid{U32.from_nat(x)}, k, c2, e)
    case True{}:
      ev = Equal.cong(Ap.Rd(Nat), Nat, y => Rd.value(Nat, y, k), Done{(Nat.add(lo, x), c)}, Done{(k, c2)}, e)
      %ev : {Ap.Size.valid(lo, diff, _) == True{} : Bool}
      P.Bool.and_intro(Nat.is_le(lo, Nat.add(lo, x)), Nat.is_le(Nat.add(lo, x), Nat.add(lo, diff)), Nat.le_add(lo, x), Nat.add_le(lo, x, diff, eok))

def Size.dv.bits(+lo: Nat, +diff: Nat, rb: Ap.Rd(Ap.Bits()), +k: Nat, +c2: Ap.Cur, +e: {Ap.Size.bits(lo, diff, rb) == Done{(k, c2)} : Ap.Rd(Nat)}) -> {Ap.Size.valid(lo, diff, k) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(Nat, {Ap.Size.valid(lo, diff, k) == True{} : Bool}, err, k, c2, e)
    case Done{(+bs, c)}:
      Size.dv.ok(lo, diff, Ap.Nat.of_bits(bs), c, Nat.is_le(Ap.Nat.of_bits(bs), diff), {==}, k, c2, e)

def Size.dv.al(+n: Nat, +lo: Nat, +diff: Nat, ra: Ap.Rd(Unit), +k: Nat, +c2: Ap.Cur, +e: {Ap.Size.aligned(n, lo, diff, ra) == Done{(k, c2)} : Ap.Rd(Nat)}) -> {Ap.Size.valid(lo, diff, k) == True{} : Bool}:
  match ra:
    case Fail{err}:
      Rd.absurd(Nat, {Ap.Size.valid(lo, diff, k) == True{} : Bool}, err, k, c2, e)
    case Done{(u, c)}:
      Size.dv.bits(lo, diff, Ap.Bits.read(n, c), k, c2, e)

def Size.dv(al: Bool, +n: Nat, +lo: Nat, +diff: Nat, c: Ap.Cur, +k: Nat, +c2: Ap.Cur, +e: {Ap.Size.read(al, n, lo, diff, c) == Done{(k, c2)} : Ap.Rd(Nat)}) -> {Ap.Size.valid(lo, diff, k) == True{} : Bool}:
  match al:
    case False{}:
      Size.dv.bits(lo, diff, Ap.Bits.read(n, c), k, c2, e)
    case True{}:
      Size.dv.al(n, lo, diff, Ap.Align.read(c), k, c2, e)

def L.aper.size.decode_valid(al, n, lo, diff, c, k, c2, e):
  Size.dv(al, n, lo, diff, c, k, c2, e)

# Octets
# ------

# Reading eight bits of a byte's wire form gives the byte back.
def Octets.step.go(d: U32, +d2: U32, same: {d == d2 : U32}, m8: {U32.and(255, d2) == d2 : U32}, +W: Ap.Bits(), +n: Nat, +r: Nat) -> {Ap.Octets.cons(d2, Ap.Octets.go(n, r, W)) == Ap.Octets.go(1n+n, r, List.append(&2, Bool, Ap.U32.to_bits(8n, d2), W)) : Ap.Rd(B.Bytes())}:
  match d:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %m8 : {Ap.Octets.cons(_, Ap.Octets.go(n, r, W)) == Ap.Octets.go(1n+n, r, List.append(&2, Bool, Ap.U32.to_bits(8n, _), W)) : Ap.Rd(B.Bytes())}
      %same : {Ap.Octets.cons(U32.and(255, _), Ap.Octets.go(n, r, W)) == Ap.Octets.go(1n+n, r, List.append(&2, Bool, Ap.U32.to_bits(8n, U32.and(255, _)), W)) : Ap.Rd(B.Bytes())}
      {==}

def Octets.step(+b: U32, ib: {B.is_byte(b) == True{} : Bool}, +W: Ap.Bits(), +n: Nat, +r: Nat) -> {Ap.Octets.cons(b, Ap.Octets.go(n, r, W)) == Ap.Octets.go(1n+n, r, List.append(&2, Bool, Ap.U32.to_bits(8n, b), W)) : Ap.Rd(B.Bytes())}:
  Octets.step.go(b, b, {==}, P.U32.lt256_mask8(b, ib), W, n, r)

def Octets.rt(bs: B.Bytes(), +r: Nat, +rest: Ap.Bits(), +ab: {B.all_bytes(bs) == True{} : Bool}) -> {Done{(bs, Ap.Cur{r, rest})} == Ap.Octets.go(List.length(&2, U32, bs), r, Ap.Octets.write(bs, r, rest)) : Ap.Rd(B.Bytes())}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +t:
      st = Octets.step(b, P.Bool.and_true_l(B.is_byte(b), B.all_bytes(t), ab), Ap.Octets.write(t, r, rest), List.length(&2, U32, t), r)
      %st : {Done{(b <> t, Ap.Cur{r, rest})} == _ : Ap.Rd(B.Bytes())}
      ih = Octets.rt(t, r, rest, P.Bool.and_true_r(B.is_byte(b), B.all_bytes(t), ab))
      %ih : {Done{(b <> t, Ap.Cur{r, rest})} == Ap.Octets.cons(b, _) : Ap.Rd(B.Bytes())}
      {==}

def L.aper.octets.roundtrip(bs, rem, rest, ab):
  Equal.sym(Ap.Rd(B.Bytes()), Done{(bs, Ap.Cur{rem, rest})}, Ap.Octets.go(List.length(&2, U32, bs), rem, Ap.Octets.write(bs, rem, rest)), Octets.rt(bs, rem, rest, ab))

# What Octets.go read: bytes, as many as asked, and exactly the bits it consumed.
def Octets.Spec(bs: B.Bytes(), c: Ap.Cur, n: Nat, r: Nat, bits: Ap.Bits()) -> Type:
  {B.all_bytes(bs) == True{} : Bool} & ({List.length(&2, U32, bs) == n : Nat} & {bits == Ap.Octets.write(bs, r, Cur.bits(c)) : Ap.Bits()})

def Octets.spec.finish(+p: Nat, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool, +rest: Ap.Bits(), +r: Nat, +bs2: B.Bytes(), +c2: Ap.Cur, s: Octets.Spec(bs2, c2, p, r, rest)) -> Octets.Spec(Ap.U32.of_bits([b7, b6, b5, b4, b3, b2, b1, b0]) <> bs2, c2, 1n+p, r, b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> rest):
  (al, s2) = s
  (len, be) = s2
  sbe = Equal.sym(Ap.Bits(), rest, Ap.Octets.write(bs2, r, Cur.bits(c2)), be)
  (P.Bool.and_intro(B.is_byte(Ap.U32.of_bits([b7, b6, b5, b4, b3, b2, b1, b0])), B.all_bytes(bs2), {==}, al), (Equal.cong(Nat, Nat, m => 1n+m, List.length(&2, U32, bs2), p, len), (%sbe : {b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> _ == b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> Ap.Octets.write(bs2, r, Cur.bits(c2)) : Ap.Bits()}; {==})))

def Octets.spec.step(+p: Nat, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool, +rest: Ap.Bits(), +r: Nat, rb: Ap.Rd(B.Bytes()), ih: @bs2: B.Bytes() -> @c2: Ap.Cur -> {rb == Done{(bs2, c2)} : Ap.Rd(B.Bytes())} -> Octets.Spec(bs2, c2, p, r, rest), +bs: B.Bytes(), +c: Ap.Cur, +e: {Ap.Octets.cons(Ap.U32.of_bits([b7, b6, b5, b4, b3, b2, b1, b0]), rb) == Done{(bs, c)} : Ap.Rd(B.Bytes())}) -> Octets.Spec(bs, c, 1n+p, r, b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> rest):
  match rb:
    case Fail{err}:
      Rd.absurd(B.Bytes(), Octets.Spec(bs, c, 1n+p, r, b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> rest), err, bs, c, e)
    case Done{(+bs2, +c2)}:
      ev = Equal.cong(Ap.Rd(B.Bytes()), B.Bytes(), x => Rd.value(B.Bytes(), x, bs), Done{(Ap.U32.of_bits([b7, b6, b5, b4, b3, b2, b1, b0]) <> bs2, c2)}, Done{(bs, c)}, e)
      ec = Equal.cong(Ap.Rd(B.Bytes()), Ap.Cur, x => Rd.cur(B.Bytes(), x, c), Done{(Ap.U32.of_bits([b7, b6, b5, b4, b3, b2, b1, b0]) <> bs2, c2)}, Done{(bs, c)}, e)
      %ev : Octets.Spec(_, c, 1n+p, r, b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> rest)
      %ec : Octets.Spec(Ap.U32.of_bits([b7, b6, b5, b4, b3, b2, b1, b0]) <> bs2, _, 1n+p, r, b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> rest)
      Octets.spec.finish(p, b7, b6, b5, b4, b3, b2, b1, b0, rest, r, bs2, c2, ih(bs2, c2, {==}))

def Octets.spec(n: Nat, +r: Nat, bits: Ap.Bits(), +bs: B.Bytes(), +c: Ap.Cur, +e: {Ap.Octets.go(n, r, bits) == Done{(bs, c)} : Ap.Rd(B.Bytes())}) -> Octets.Spec(bs, c, n, r, bits):
  match n bits:
    case 0n rest:
      ev = Equal.cong(Ap.Rd(B.Bytes()), B.Bytes(), x => Rd.value(B.Bytes(), x, bs), Done{([], Ap.Cur{r, rest})}, Done{(bs, c)}, e)
      ec = Equal.cong(Ap.Rd(B.Bytes()), Ap.Cur, x => Rd.cur(B.Bytes(), x, c), Done{([], Ap.Cur{r, rest})}, Done{(bs, c)}, e)
      %ev : Octets.Spec(_, c, 0n, r, rest)
      %ec : Octets.Spec([], _, 0n, r, rest)
      ({==}, ({==}, {==}))
    case 1n++p b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> b0 <> +rest:
      Octets.spec.step(p, b7, b6, b5, b4, b3, b2, b1, b0, rest, r, Ap.Octets.go(p, r, rest), bs2 => c2 => e2 => Octets.spec(p, r, rest, bs2, c2, e2), bs, c, e)
    case 1n+p Nil{}:
      Rd.absurd(B.Bytes(), Octets.Spec(bs, c, 1n+p, r, Nil{}), B.Short{}, bs, c, e)
    case 1n+p b7 <> Nil{}:
      Rd.absurd(B.Bytes(), Octets.Spec(bs, c, 1n+p, r, b7 <> Nil{}), B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> Nil{}:
      Rd.absurd(B.Bytes(), Octets.Spec(bs, c, 1n+p, r, b7 <> b6 <> Nil{}), B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> b5 <> Nil{}:
      Rd.absurd(B.Bytes(), Octets.Spec(bs, c, 1n+p, r, b7 <> b6 <> b5 <> Nil{}), B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> b5 <> b4 <> Nil{}:
      Rd.absurd(B.Bytes(), Octets.Spec(bs, c, 1n+p, r, b7 <> b6 <> b5 <> b4 <> Nil{}), B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> b5 <> b4 <> b3 <> Nil{}:
      Rd.absurd(B.Bytes(), Octets.Spec(bs, c, 1n+p, r, b7 <> b6 <> b5 <> b4 <> b3 <> Nil{}), B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> Nil{}:
      Rd.absurd(B.Bytes(), Octets.Spec(bs, c, 1n+p, r, b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> Nil{}), B.Short{}, bs, c, e)
    case 1n+p b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> Nil{}:
      Rd.absurd(B.Bytes(), Octets.Spec(bs, c, 1n+p, r, b7 <> b6 <> b5 <> b4 <> b3 <> b2 <> b1 <> Nil{}), B.Short{}, bs, c, e)

def Octets.all(+bs: B.Bytes(), +c: Ap.Cur, +n: Nat, +r: Nat, +bits: Ap.Bits(), s: Octets.Spec(bs, c, n, r, bits)) -> {B.all_bytes(bs) == True{} : Bool}:
  (al, s2) = s
  al

def Octets.len(+bs: B.Bytes(), +c: Ap.Cur, +n: Nat, +r: Nat, +bits: Ap.Bits(), s: Octets.Spec(bs, c, n, r, bits)) -> {List.length(&2, U32, bs) == n : Nat}:
  (al, s2) = s
  (len, be) = s2
  len

def Octets.exact(+bs: B.Bytes(), +c: Ap.Cur, +n: Nat, +r: Nat, +bits: Ap.Bits(), s: Octets.Spec(bs, c, n, r, bits)) -> {bits == Ap.Octets.write(bs, r, Cur.bits(c)) : Ap.Bits()}:
  (al, s2) = s
  (len, be) = s2
  be

def Octets.dv(+n: Nat, c: Ap.Cur, +bs: B.Bytes(), +c2: Ap.Cur, +e: {Ap.Octets.read(n, c) == Done{(bs, c2)} : Ap.Rd(B.Bytes())}) -> {B.all_bytes(bs) == True{} : Bool}:
  match c:
    case Ap.Cur{+rem, +bits}:
      Octets.all(bs, c2, n, rem, bits, Octets.spec(n, rem, bits, bs, c2, e))

def L.aper.octets.decode_valid(n, c, bs, c2, e):
  Octets.dv(n, c, bs, c2, e)

def Pack.step.go(d: U32, +d2: U32, same: {d == d2 : U32}, m8: {U32.and(255, d2) == d2 : U32}, +W: Ap.Bits()) -> {d2 <> Ap.pack(W) == Ap.pack(List.append(&2, Bool, Ap.U32.to_bits(8n, d2), W)) : B.Bytes()}:
  match d:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %m8 : {_ <> Ap.pack(W) == Ap.pack(List.append(&2, Bool, Ap.U32.to_bits(8n, _), W)) : B.Bytes()}
      %same : {U32.and(255, _) <> Ap.pack(W) == Ap.pack(List.append(&2, Bool, Ap.U32.to_bits(8n, U32.and(255, _)), W)) : B.Bytes()}
      {==}

def Pack.rt(bs: B.Bytes(), +ab: {B.all_bytes(bs) == True{} : Bool}) -> {bs == Ap.pack(Ap.unpack(bs)) : B.Bytes()}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +t:
      st = Pack.step.go(b, b, {==}, P.U32.lt256_mask8(b, P.Bool.and_true_l(B.is_byte(b), B.all_bytes(t), ab)), Ap.Octets.write(t, 0n, []))
      %st : {b <> t == _ : B.Bytes()}
      Equal.cong(B.Bytes(), B.Bytes(), l => b <> l, t, Ap.pack(Ap.Octets.write(t, 0n, [])), Pack.rt(t, P.Bool.and_true_r(B.is_byte(b), B.all_bytes(t), ab)))

def L.aper.pack.roundtrip(bs, ab):
  Equal.sym(B.Bytes(), bs, Ap.pack(Ap.unpack(bs)), Pack.rt(bs, ab))

def L.aper.aoctets.roundtrip(bs, rem, rest, ab):
  ar = Align.rt(rem, Ap.Octets.write(bs, 0n, rest))
  %ar : {Ap.AOctets.aligned(List.length(&2, U32, bs), _) == Done{(bs, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  Equal.sym(Ap.Rd(B.Bytes()), Done{(bs, Ap.Cur{0n, rest})}, Ap.Octets.go(List.length(&2, U32, bs), 0n, Ap.Octets.write(bs, 0n, rest)), Octets.rt(bs, 0n, rest, ab))

def L.aper.abits.roundtrip(bs, rem, rest):
  ar = Align.rt(rem, List.append(&2, Bool, bs, rest))
  %ar : {Ap.ABits.aligned(List.length(&2, Bool, bs), _) == Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})} : Ap.Rd(Ap.Bits())}
  Equal.sym(Ap.Rd(Ap.Bits()), Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})}, Ap.Bits.go(List.length(&2, Bool, bs), Ap.Rem.add(List.length(&2, Bool, bs), 0n), List.append(&2, Bool, bs, rest)), Bits.go_app(bs, Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest))

# Indefinite-length numbers
# -------------------------

def Big.nonempty(bs: B.Bytes(), canon: {Ap.Big.canonical(bs) == True{} : Bool}) -> {Nat.is_le(1n, List.length(&2, U32, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, P.Refute.bool(canon))
    case b <> t:
      Nat.le_zero(List.length(&2, U32, t))

def L.aper.big.roundtrip(n, diff, bs, rem, rest, v, w):
  +canon = P.Bool.and_true_l(Ap.Big.canonical(bs), Bool.and(Nat.is_le(List.length(&2, U32, bs), 1n+diff), B.all_bytes(bs)), v)
  +v2 = P.Bool.and_true_r(Ap.Big.canonical(bs), Bool.and(Nat.is_le(List.length(&2, U32, bs), 1n+diff), B.all_bytes(bs)), v)
  ln = P.Bool.and_true_l(Nat.is_le(List.length(&2, U32, bs), 1n+diff), B.all_bytes(bs), v2)
  ab = P.Bool.and_true_r(Nat.is_le(List.length(&2, U32, bs), 1n+diff), B.all_bytes(bs), v2)
  sr = Equal.sym(Ap.Rd(Nat), Ap.Size.read(False{}, n, 1n, diff, Ap.Cur{rem, Ap.Size.write(False{}, n, 1n, List.length(&2, U32, bs), rem, Ap.AOctets.write(bs, Ap.Size.after(False{}, n, rem), rest))}), Done{(List.length(&2, U32, bs), Ap.Cur{Ap.Size.after(False{}, n, rem), Ap.AOctets.write(bs, Ap.Size.after(False{}, n, rem), rest)})}, Size.rt(False{}, n, 1n, diff, List.length(&2, U32, bs), rem, Ap.AOctets.write(bs, Ap.Size.after(False{}, n, rem), rest), P.Bool.and_intro(Nat.is_le(1n, List.length(&2, U32, bs)), Nat.is_le(List.length(&2, U32, bs), 1n+diff), Big.nonempty(bs, canon), ln), w))
  %sr : {Ap.Big.count(_) == Done{(bs, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  ar = Align.rt(Ap.Rem.add(n, rem), Ap.Octets.write(bs, 0n, rest))
  %ar : {Ap.Big.octets(Ap.AOctets.aligned(List.length(&2, U32, bs), _)) == Done{(bs, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  ort = Octets.rt(bs, 0n, rest, ab)
  %ort : {Ap.Big.octets(_) == Done{(bs, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  scanon = Equal.sym(Bool, Ap.Big.canonical(bs), True{}, canon)
  %scanon : {Ap.Big.of(bs, Ap.Cur{0n, rest}, _) == Done{(bs, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  {==}

def Big.dv.check(+diff: Nat, +bs: B.Bytes(), +c: Ap.Cur, ok: Bool, eok: {Ap.Big.canonical(bs) == ok : Bool}, +out: B.Bytes(), +c2: Ap.Cur, +e: {Ap.Big.of(bs, c, ok) == Done{(out, c2)} : Ap.Rd(B.Bytes())}, ab: {B.all_bytes(bs) == True{} : Bool}, ln: {Nat.is_le(List.length(&2, U32, bs), 1n+diff) == True{} : Bool}) -> {Ap.Big.valid(diff, out) == True{} : Bool}:
  match ok:
    case False{}:
      Rd.absurd(B.Bytes(), {Ap.Big.valid(diff, out) == True{} : Bool}, B.Invalid{0}, out, c2, e)
    case True{}:
      ev = Equal.cong(Ap.Rd(B.Bytes()), B.Bytes(), x => Rd.value(B.Bytes(), x, out), Done{(bs, c)}, Done{(out, c2)}, e)
      %ev : {Ap.Big.valid(diff, _) == True{} : Bool}
      P.Bool.and_intro(Ap.Big.canonical(bs), Bool.and(Nat.is_le(List.length(&2, U32, bs), 1n+diff), B.all_bytes(bs)), eok, P.Bool.and_intro(Nat.is_le(List.length(&2, U32, bs), 1n+diff), B.all_bytes(bs), ln, ab))

def Big.dv.oct(+diff: Nat, +l: Nat, +r: Nat, +bits: Ap.Bits(), ro: Ap.Rd(B.Bytes()), +ero: {Ap.Octets.go(l, r, bits) == ro : Ap.Rd(B.Bytes())}, +out: B.Bytes(), +c2: Ap.Cur, +e: {Ap.Big.octets(ro) == Done{(out, c2)} : Ap.Rd(B.Bytes())}, ll: {Nat.is_le(l, 1n+diff) == True{} : Bool}) -> {Ap.Big.valid(diff, out) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.Big.valid(diff, out) == True{} : Bool}, err, out, c2, e)
    case Done{(+bs, +c)}:
      slen = Equal.sym(Nat, List.length(&2, U32, bs), l, Octets.len(bs, c, l, r, bits, Octets.spec(l, r, bits, bs, c, ero)))
      Big.dv.check(diff, bs, c, Ap.Big.canonical(bs), {==}, out, c2, e, Octets.all(bs, c, l, r, bits, Octets.spec(l, r, bits, bs, c, ero)), (%slen : {Nat.is_le(_, 1n+diff) == True{} : Bool}; ll))

def Big.dv.al(+diff: Nat, +l: Nat, ra: Ap.Rd(Unit), +out: B.Bytes(), +c2: Ap.Cur, +e: {Ap.Big.octets(Ap.AOctets.aligned(l, ra)) == Done{(out, c2)} : Ap.Rd(B.Bytes())}, ll: {Nat.is_le(l, 1n+diff) == True{} : Bool}) -> {Ap.Big.valid(diff, out) == True{} : Bool}:
  match ra:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.Big.valid(diff, out) == True{} : Bool}, err, out, c2, e)
    case Done{(u, c)}:
      match c:
        case Ap.Cur{+rem, +bits}:
          Big.dv.oct(diff, l, rem, bits, Ap.Octets.go(l, rem, bits), {==}, out, c2, e, ll)

def Big.dv.count(+n: Nat, +diff: Nat, +c0: Ap.Cur, rl: Ap.Rd(Nat), +ers: {Ap.Size.read(False{}, n, 1n, diff, c0) == rl : Ap.Rd(Nat)}, +out: B.Bytes(), +c2: Ap.Cur, +e: {Ap.Big.count(rl) == Done{(out, c2)} : Ap.Rd(B.Bytes())}) -> {Ap.Big.valid(diff, out) == True{} : Bool}:
  match rl:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.Big.valid(diff, out) == True{} : Bool}, err, out, c2, e)
    case Done{(+l, +c)}:
      Big.dv.al(diff, l, Ap.Align.read(c), out, c2, e, P.Bool.and_true_r(Nat.is_le(1n, l), Nat.is_le(l, Nat.add(1n, diff)), Size.dv(False{}, n, 1n, diff, c0, l, c, ers)))

def L.aper.big.decode_valid(n, diff, c, bs, c2, e):
  Big.dv.count(n, diff, c, Ap.Size.read(False{}, n, 1n, diff, c), {==}, bs, c2, e)

# Strings and open types
# ----------------------

def L.aper.octstr.roundtrip(al, n, lo, diff, bs, rem, rest, v, w):
  sr = Equal.sym(Ap.Rd(Nat), Ap.Size.read(al, n, lo, diff, Ap.Cur{rem, Ap.Size.write(al, n, lo, List.length(&2, U32, bs), rem, Ap.AOctets.write(bs, Ap.Size.after(al, n, rem), rest))}), Done{(List.length(&2, U32, bs), Ap.Cur{Ap.Size.after(al, n, rem), Ap.AOctets.write(bs, Ap.Size.after(al, n, rem), rest)})}, Size.rt(al, n, lo, diff, List.length(&2, U32, bs), rem, Ap.AOctets.write(bs, Ap.Size.after(al, n, rem), rest), P.Bool.and_true_l(Ap.Size.valid(lo, diff, List.length(&2, U32, bs)), B.all_bytes(bs), v), w))
  %sr : {Ap.OctStr.count(_) == Done{(bs, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  ar = Align.rt(Ap.Size.after(al, n, rem), Ap.Octets.write(bs, 0n, rest))
  %ar : {Ap.AOctets.aligned(List.length(&2, U32, bs), _) == Done{(bs, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  Equal.sym(Ap.Rd(B.Bytes()), Done{(bs, Ap.Cur{0n, rest})}, Ap.Octets.go(List.length(&2, U32, bs), 0n, Ap.Octets.write(bs, 0n, rest)), Octets.rt(bs, 0n, rest, P.Bool.and_true_r(Ap.Size.valid(lo, diff, List.length(&2, U32, bs)), B.all_bytes(bs), v)))

def OctStr.dv.al(ra: Ap.Rd(Unit), +l: Nat, +lo: Nat, +diff: Nat, +bs: B.Bytes(), +c2: Ap.Cur, +e: {Ap.AOctets.aligned(l, ra) == Done{(bs, c2)} : Ap.Rd(B.Bytes())}, sv: {Ap.Size.valid(lo, diff, l) == True{} : Bool}) -> {Ap.OctStr.valid(lo, diff, bs) == True{} : Bool}:
  match ra:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.OctStr.valid(lo, diff, bs) == True{} : Bool}, err, bs, c2, e)
    case Done{(u, c)}:
      match c:
        case Ap.Cur{+rem, +bits}:
          slen = Equal.sym(Nat, List.length(&2, U32, bs), l, Octets.len(bs, c2, l, rem, bits, Octets.spec(l, rem, bits, bs, c2, e)))
          P.Bool.and_intro(Ap.Size.valid(lo, diff, List.length(&2, U32, bs)), B.all_bytes(bs), (%slen : {Ap.Size.valid(lo, diff, _) == True{} : Bool}; sv), Octets.all(bs, c2, l, rem, bits, Octets.spec(l, rem, bits, bs, c2, e)))

def OctStr.dv(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +c0: Ap.Cur, rl: Ap.Rd(Nat), +ers: {Ap.Size.read(al, n, lo, diff, c0) == rl : Ap.Rd(Nat)}, +bs: B.Bytes(), +c2: Ap.Cur, +e: {Ap.OctStr.count(rl) == Done{(bs, c2)} : Ap.Rd(B.Bytes())}) -> {Ap.OctStr.valid(lo, diff, bs) == True{} : Bool}:
  match rl:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.OctStr.valid(lo, diff, bs) == True{} : Bool}, err, bs, c2, e)
    case Done{(+l, +c)}:
      OctStr.dv.al(Ap.Align.read(c), l, lo, diff, bs, c2, e, Size.dv(al, n, lo, diff, c0, l, c, ers))

def L.aper.octstr.decode_valid(al, n, lo, diff, c, bs, c2, e):
  OctStr.dv(al, n, lo, diff, c, Ap.Size.read(al, n, lo, diff, c), {==}, bs, c2, e)

def L.aper.bitstr.roundtrip(al, n, lo, diff, bs, rem, rest, v, w):
  sr = Equal.sym(Ap.Rd(Nat), Ap.Size.read(al, n, lo, diff, Ap.Cur{rem, Ap.Size.write(al, n, lo, List.length(&2, Bool, bs), rem, Ap.ABits.write(bs, Ap.Size.after(al, n, rem), rest))}), Done{(List.length(&2, Bool, bs), Ap.Cur{Ap.Size.after(al, n, rem), Ap.ABits.write(bs, Ap.Size.after(al, n, rem), rest)})}, Size.rt(al, n, lo, diff, List.length(&2, Bool, bs), rem, Ap.ABits.write(bs, Ap.Size.after(al, n, rem), rest), v, w))
  %sr : {Ap.BitStr.count(_) == Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})} : Ap.Rd(Ap.Bits())}
  ar = Align.rt(Ap.Size.after(al, n, rem), List.append(&2, Bool, bs, rest))
  %ar : {Ap.ABits.aligned(List.length(&2, Bool, bs), _) == Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})} : Ap.Rd(Ap.Bits())}
  Equal.sym(Ap.Rd(Ap.Bits()), Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})}, Ap.Bits.go(List.length(&2, Bool, bs), Ap.Rem.add(List.length(&2, Bool, bs), 0n), List.append(&2, Bool, bs, rest)), Bits.go_app(bs, Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest))

def BitStr.dv.al(ra: Ap.Rd(Unit), +l: Nat, +lo: Nat, +diff: Nat, +bs: Ap.Bits(), +c2: Ap.Cur, +e: {Ap.ABits.aligned(l, ra) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}, sv: {Ap.Size.valid(lo, diff, l) == True{} : Bool}) -> {Ap.BitStr.valid(lo, diff, bs) == True{} : Bool}:
  match ra:
    case Fail{err}:
      Rd.absurd(Ap.Bits(), {Ap.BitStr.valid(lo, diff, bs) == True{} : Bool}, err, bs, c2, e)
    case Done{(u, c)}:
      match c:
        case Ap.Cur{+rem, +bits}:
          slen = Equal.sym(Nat, List.length(&2, Bool, bs), l, Bits.len(bs, c2, l, Ap.Rem.add(l, rem), Bits.spec(l, Ap.Rem.add(l, rem), bits, bs, c2, e)))
          %slen : {Ap.Size.valid(lo, diff, _) == True{} : Bool}
          sv

def BitStr.dv(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +c0: Ap.Cur, rl: Ap.Rd(Nat), +ers: {Ap.Size.read(al, n, lo, diff, c0) == rl : Ap.Rd(Nat)}, +bs: Ap.Bits(), +c2: Ap.Cur, +e: {Ap.BitStr.count(rl) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}) -> {Ap.BitStr.valid(lo, diff, bs) == True{} : Bool}:
  match rl:
    case Fail{err}:
      Rd.absurd(Ap.Bits(), {Ap.BitStr.valid(lo, diff, bs) == True{} : Bool}, err, bs, c2, e)
    case Done{(+l, +c)}:
      BitStr.dv.al(Ap.Align.read(c), l, lo, diff, bs, c2, e, Size.dv(al, n, lo, diff, c0, l, c, ers))

def L.aper.bitstr.decode_valid(al, n, lo, diff, c, bs, c2, e):
  BitStr.dv(al, n, lo, diff, c, Ap.Size.read(al, n, lo, diff, c), {==}, bs, c2, e)

def L.aper.ubitstr.roundtrip(bs, rem, rest, v):
  lr = Equal.sym(Ap.Rd(Nat), Ap.Len.read(Ap.Cur{rem, Ap.Len.write(List.length(&2, Bool, bs), rem, List.append(&2, Bool, bs, rest))}), Done{(List.length(&2, Bool, bs), Ap.Cur{0n, List.append(&2, Bool, bs, rest)})}, L.aper.len.roundtrip(List.length(&2, Bool, bs), rem, List.append(&2, Bool, bs, rest), v))
  %lr : {Ap.UBitStr.count(_) == Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})} : Ap.Rd(Ap.Bits())}
  Equal.sym(Ap.Rd(Ap.Bits()), Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})}, Ap.Bits.go(List.length(&2, Bool, bs), Ap.Rem.add(List.length(&2, Bool, bs), 0n), List.append(&2, Bool, bs, rest)), Bits.go_app(bs, Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest))

def UBitStr.dv(rl: Ap.Rd(Nat), +c0: Ap.Cur, +erl: {Ap.Len.read(c0) == rl : Ap.Rd(Nat)}, +bs: Ap.Bits(), +c2: Ap.Cur, +e: {Ap.UBitStr.count(rl) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}) -> {Ap.UBitStr.valid(bs) == True{} : Bool}:
  match rl:
    case Fail{err}:
      Rd.absurd(Ap.Bits(), {Ap.UBitStr.valid(bs) == True{} : Bool}, err, bs, c2, e)
    case Done{(+l, c)}:
      match c:
        case Ap.Cur{+rem, +bits}:
          slen = Equal.sym(Nat, List.length(&2, Bool, bs), l, Bits.len(bs, c2, l, Ap.Rem.add(l, rem), Bits.spec(l, Ap.Rem.add(l, rem), bits, bs, c2, e)))
          %slen : {Nat.is_lt(_, 16384n) == True{} : Bool}
          L.aper.no_big_nat(c0, l, Ap.Cur{rem, bits}, erl)

def L.aper.ubitstr.decode_valid(c, bs, c2, e):
  UBitStr.dv(Ap.Len.read(c), c, {==}, bs, c2, e)

def L.aper.open.roundtrip(bs, rem, rest, v):
  lr = Equal.sym(Ap.Rd(Nat), Ap.Len.read(Ap.Cur{rem, Ap.Len.write(List.length(&2, U32, bs), rem, Ap.Octets.write(bs, 0n, rest))}), Done{(List.length(&2, U32, bs), Ap.Cur{0n, Ap.Octets.write(bs, 0n, rest)})}, L.aper.len.roundtrip(List.length(&2, U32, bs), rem, Ap.Octets.write(bs, 0n, rest), P.Bool.and_true_l(Ap.Len.valid(List.length(&2, U32, bs)), B.all_bytes(bs), v)))
  %lr : {Ap.Open.count(_) == Done{(bs, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  Equal.sym(Ap.Rd(B.Bytes()), Done{(bs, Ap.Cur{0n, rest})}, Ap.Octets.go(List.length(&2, U32, bs), 0n, Ap.Octets.write(bs, 0n, rest)), Octets.rt(bs, 0n, rest, P.Bool.and_true_r(Ap.Len.valid(List.length(&2, U32, bs)), B.all_bytes(bs), v)))

def Open.dv(rl: Ap.Rd(Nat), +c0: Ap.Cur, +erl: {Ap.Len.read(c0) == rl : Ap.Rd(Nat)}, +bs: B.Bytes(), +c2: Ap.Cur, +e: {Ap.Open.count(rl) == Done{(bs, c2)} : Ap.Rd(B.Bytes())}) -> {Ap.Open.valid(bs) == True{} : Bool}:
  match rl:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.Open.valid(bs) == True{} : Bool}, err, bs, c2, e)
    case Done{(+l, c)}:
      match c:
        case Ap.Cur{+rem, +bits}:
          slen = Equal.sym(Nat, List.length(&2, U32, bs), l, Octets.len(bs, c2, l, rem, bits, Octets.spec(l, rem, bits, bs, c2, e)))
          P.Bool.and_intro(Ap.Len.valid(List.length(&2, U32, bs)), B.all_bytes(bs), (%slen : {Nat.is_lt(_, 16384n) == True{} : Bool}; L.aper.no_big_nat(c0, l, Ap.Cur{rem, bits}, erl)), Octets.all(bs, c2, l, rem, bits, Octets.spec(l, rem, bits, bs, c2, e)))

def L.aper.open.decode_valid(c, bs, c2, e):
  Open.dv(Ap.Len.read(c), c, {==}, bs, c2, e)

def Open.exact(rl: Ap.Rd(Nat), +c0: Ap.Cur, +erl: {Ap.Len.read(c0) == rl : Ap.Rd(Nat)}, +body: B.Bytes(), +r2: Nat, +rest: Ap.Bits(), +e: {Ap.Open.count(rl) == Done{(body, Ap.Cur{r2, rest})} : Ap.Rd(B.Bytes())}) -> {Ap.Len.read(c0) == Done{(List.length(&2, U32, body), Ap.Cur{0n, Ap.Octets.write(body, 0n, rest)})} : Ap.Rd(Nat)}:
  match rl:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.Len.read(c0) == Done{(List.length(&2, U32, body), Ap.Cur{0n, Ap.Octets.write(body, 0n, rest)})} : Ap.Rd(Nat)}, err, body, Ap.Cur{r2, rest}, e)
    case Done{(+l, c)}:
      match c:
        case Ap.Cur{+rem, +bits}:
          serl = Equal.sym(Ap.Rd(Nat), Ap.Len.read(c0), Done{(l, Ap.Cur{rem, bits})}, erl)
          %serl : {_ == Done{(List.length(&2, U32, body), Ap.Cur{0n, Ap.Octets.write(body, 0n, rest)})} : Ap.Rd(Nat)}
          slen = Equal.sym(Nat, List.length(&2, U32, body), l, Octets.len(body, Ap.Cur{r2, rest}, l, rem, bits, Octets.spec(l, rem, bits, body, Ap.Cur{r2, rest}, e)))
          %slen : {Done{(l, Ap.Cur{rem, bits})} == Done{(_, Ap.Cur{0n, Ap.Octets.write(body, 0n, rest)})} : Ap.Rd(Nat)}
          sbe = Equal.sym(Ap.Bits(), bits, Ap.Octets.write(body, rem, rest), Octets.exact(body, Ap.Cur{r2, rest}, l, rem, bits, Octets.spec(l, rem, bits, body, Ap.Cur{r2, rest}, e)))
          %sbe : {Done{(l, Ap.Cur{rem, _})} == Done{(l, Ap.Cur{0n, Ap.Octets.write(body, 0n, rest)})} : Ap.Rd(Nat)}
          rm = Len.aligned_end(l, Ap.Cur{rem, bits}, Len.dv(Ap.Align.read(c0), l, Ap.Cur{rem, bits}, erl))
          %rm : {Done{(l, Ap.Cur{_, Ap.Octets.write(body, _, rest)})} == Done{(l, Ap.Cur{0n, Ap.Octets.write(body, 0n, rest)})} : Ap.Rd(Nat)}
          {==}

def L.aper.open_type.exact(c, body, r2, rest, e):
  Open.exact(Ap.Len.read(c), c, {==}, body, r2, rest, e)

def Str.all_bytes(s: B.Bytes(), +e: {Ap.Str.all(s) == True{} : Bool}) -> {B.all_bytes(s) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +c <> +t:
      P.Bool.and_intro(B.is_byte(c), B.all_bytes(t), P.Bool.and_true_l(B.is_byte(c), Ap.Str.alphabet(c), P.Bool.and_true_l(Ap.Str.printable(c), Ap.Str.all(t), e)), Str.all_bytes(t, P.Bool.and_true_r(Ap.Str.printable(c), Ap.Str.all(t), e)))

def L.aper.str.roundtrip(al, n, lo, diff, s, rem, rest, v, w):
  sv = P.Bool.and_true_l(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Str.all(s), v)
  +pr = P.Bool.and_true_r(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Str.all(s), v)
  or = Equal.sym(Ap.Rd(B.Bytes()), Ap.OctStr.read(al, n, lo, diff, Ap.Cur{rem, Ap.OctStr.write(al, n, lo, s, rem, rest)}), Done{(s, Ap.Cur{0n, rest})}, L.aper.octstr.roundtrip(al, n, lo, diff, s, rem, rest, P.Bool.and_intro(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), B.all_bytes(s), sv, Str.all_bytes(s, pr)), w))
  %or : {Ap.Str.check(_) == Done{(s, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  spr = Equal.sym(Bool, Ap.Str.all(s), True{}, pr)
  %spr : {Ap.Str.of(s, Ap.Cur{0n, rest}, _) == Done{(s, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  {==}

def Str.dv.ok(+lo: Nat, +diff: Nat, +s0: B.Bytes(), +c: Ap.Cur, ok: Bool, eok: {Ap.Str.all(s0) == ok : Bool}, +s: B.Bytes(), +c2: Ap.Cur, +e: {Ap.Str.of(s0, c, ok) == Done{(s, c2)} : Ap.Rd(B.Bytes())}, ov: {Ap.OctStr.valid(lo, diff, s0) == True{} : Bool}) -> {Ap.Str.valid(lo, diff, s) == True{} : Bool}:
  match ok:
    case False{}:
      Rd.absurd(B.Bytes(), {Ap.Str.valid(lo, diff, s) == True{} : Bool}, B.Invalid{1}, s, c2, e)
    case True{}:
      ev = Equal.cong(Ap.Rd(B.Bytes()), B.Bytes(), y => Rd.value(B.Bytes(), y, s), Done{(s0, c)}, Done{(s, c2)}, e)
      %ev : {Ap.Str.valid(lo, diff, _) == True{} : Bool}
      P.Bool.and_intro(Ap.Size.valid(lo, diff, List.length(&2, U32, s0)), Ap.Str.all(s0), P.Bool.and_true_l(Ap.Size.valid(lo, diff, List.length(&2, U32, s0)), B.all_bytes(s0), ov), eok)

def Str.dv(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +c0: Ap.Cur, ro: Ap.Rd(B.Bytes()), +ero: {Ap.OctStr.read(al, n, lo, diff, c0) == ro : Ap.Rd(B.Bytes())}, +s: B.Bytes(), +c2: Ap.Cur, +e: {Ap.Str.check(ro) == Done{(s, c2)} : Ap.Rd(B.Bytes())}) -> {Ap.Str.valid(lo, diff, s) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.Str.valid(lo, diff, s) == True{} : Bool}, err, s, c2, e)
    case Done{(+s0, +c)}:
      Str.dv.ok(lo, diff, s0, c, Ap.Str.all(s0), {==}, s, c2, e, L.aper.octstr.decode_valid(al, n, lo, diff, c0, s0, c, ero))

def L.aper.str.decode_valid(al, n, lo, diff, c, s, c2, e):
  Str.dv(al, n, lo, diff, c, Ap.OctStr.read(al, n, lo, diff, c), {==}, s, c2, e)

def L.aper.ustr.roundtrip(s, rem, rest, v):
  lv = P.Bool.and_true_l(Ap.Len.valid(List.length(&2, U32, s)), Ap.Str.all(s), v)
  +pr = P.Bool.and_true_r(Ap.Len.valid(List.length(&2, U32, s)), Ap.Str.all(s), v)
  or = Equal.sym(Ap.Rd(B.Bytes()), Ap.Open.read(Ap.Cur{rem, Ap.Open.write(s, rem, rest)}), Done{(s, Ap.Cur{0n, rest})}, L.aper.open.roundtrip(s, rem, rest, P.Bool.and_intro(Ap.Len.valid(List.length(&2, U32, s)), B.all_bytes(s), lv, Str.all_bytes(s, pr))))
  %or : {Ap.Str.check(_) == Done{(s, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  spr = Equal.sym(Bool, Ap.Str.all(s), True{}, pr)
  %spr : {Ap.Str.of(s, Ap.Cur{0n, rest}, _) == Done{(s, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
  {==}

def UStr.dv.ok(+s0: B.Bytes(), +c: Ap.Cur, ok: Bool, eok: {Ap.Str.all(s0) == ok : Bool}, +s: B.Bytes(), +c2: Ap.Cur, +e: {Ap.Str.of(s0, c, ok) == Done{(s, c2)} : Ap.Rd(B.Bytes())}, ov: {Ap.Open.valid(s0) == True{} : Bool}) -> {Ap.UStr.valid(s) == True{} : Bool}:
  match ok:
    case False{}:
      Rd.absurd(B.Bytes(), {Ap.UStr.valid(s) == True{} : Bool}, B.Invalid{1}, s, c2, e)
    case True{}:
      ev = Equal.cong(Ap.Rd(B.Bytes()), B.Bytes(), y => Rd.value(B.Bytes(), y, s), Done{(s0, c)}, Done{(s, c2)}, e)
      %ev : {Ap.UStr.valid(_) == True{} : Bool}
      P.Bool.and_intro(Ap.Len.valid(List.length(&2, U32, s0)), Ap.Str.all(s0), P.Bool.and_true_l(Ap.Len.valid(List.length(&2, U32, s0)), B.all_bytes(s0), ov), eok)

def UStr.dv(+c0: Ap.Cur, ro: Ap.Rd(B.Bytes()), +ero: {Ap.Open.read(c0) == ro : Ap.Rd(B.Bytes())}, +s: B.Bytes(), +c2: Ap.Cur, +e: {Ap.Str.check(ro) == Done{(s, c2)} : Ap.Rd(B.Bytes())}) -> {Ap.UStr.valid(s) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.UStr.valid(s) == True{} : Bool}, err, s, c2, e)
    case Done{(+s0, +c)}:
      UStr.dv.ok(s0, c, Ap.Str.all(s0), {==}, s, c2, e, L.aper.open.decode_valid(c0, s0, c, ero))

def L.aper.ustr.decode_valid(c, s, c2, e):
  UStr.dv(c, Ap.Open.read(c), {==}, s, c2, e)

# Enumerations
# ------------

def L.aper.enum.roundtrip(n, diff, ext, e, rem, rest, v):
  match ext e:
    case False{} Ap.Root{i}:
      ir = Equal.sym(Ap.Rd(U32), Ap.Int.read(n, diff, Ap.Cur{rem, Ap.Int.write(n, i, rem, rest)}), Done{(i, Ap.Cur{Ap.Int.after(n, rem), rest})}, L.aper.int.roundtrip(n, diff, i, rem, rest, v))
      %ir : {Ap.Enum.root(_) == Done{(Ap.Root{i}, Ap.Cur{Ap.Rem.add(n, rem), rest})} : Ap.Rd(Ap.Enum)}
      {==}
    case False{} Ap.Ext{i}:
      Empty.absurd({Ap.Enum.read(n, diff, False{}, Ap.Cur{rem, Ap.Enum.write(n, False{}, Ap.Ext{i}, rem, rest)}) == Done{(Ap.Ext{i}, Ap.Cur{Ap.Enum.after(n, False{}, Ap.Ext{i}, rem), rest})} : Ap.Rd(Ap.Enum)}, P.Refute.bool(v))
    case True{} Ap.Root{i}:
      ir = Equal.sym(Ap.Rd(U32), Ap.Int.read(n, diff, Ap.Cur{Ap.Rem.next(rem), Ap.Int.write(n, i, Ap.Rem.next(rem), rest)}), Done{(i, Ap.Cur{Ap.Int.after(n, Ap.Rem.next(rem)), rest})}, L.aper.int.roundtrip(n, diff, i, Ap.Rem.next(rem), rest, v))
      %ir : {Ap.Enum.root(_) == Done{(Ap.Root{i}, Ap.Cur{Ap.Rem.add(n, Ap.Rem.next(rem)), rest})} : Ap.Rd(Ap.Enum)}
      {==}
    case True{} Ap.Ext{i}:
      sr = Equal.sym(Ap.Rd(U32), Ap.Small.read(Ap.Cur{Ap.Rem.next(rem), Ap.Small.write(i, Ap.Rem.next(rem), rest)}), Done{(i, Ap.Cur{Ap.Small.after(Ap.Rem.next(rem)), rest})}, L.aper.small.roundtrip(i, Ap.Rem.next(rem), rest, v))
      %sr : {Ap.Enum.ext(_) == Done{(Ap.Ext{i}, Ap.Cur{Ap.Rem.add(7n, Ap.Rem.next(rem)), rest})} : Ap.Rd(Ap.Enum)}
      {==}

def Enum.dv.root(+n: Nat, +diff: U32, +ext: Bool, +c0: Ap.Cur, ri: Ap.Rd(U32), +eri: {Ap.Int.read(n, diff, c0) == ri : Ap.Rd(U32)}, +e: Ap.Enum, +c2: Ap.Cur, +d: {Ap.Enum.root(ri) == Done{(e, c2)} : Ap.Rd(Ap.Enum)}) -> {Ap.Enum.valid(n, diff, ext, e) == True{} : Bool}:
  match ri:
    case Fail{err}:
      Rd.absurd(Ap.Enum, {Ap.Enum.valid(n, diff, ext, e) == True{} : Bool}, err, e, c2, d)
    case Done{(+i, +c)}:
      ev = Equal.cong(Ap.Rd(Ap.Enum), Ap.Enum, y => Rd.value(Ap.Enum, y, e), Done{(Ap.Root{i}, c)}, Done{(e, c2)}, d)
      %ev : {Ap.Enum.valid(n, diff, ext, _) == True{} : Bool}
      Int.dv(n, diff, c0, i, c, eri)

def Enum.dv.ext(+n: Nat, +diff: U32, +c0: Ap.Cur, rs: Ap.Rd(U32), +ers: {Ap.Small.read(c0) == rs : Ap.Rd(U32)}, +e: Ap.Enum, +c2: Ap.Cur, +d: {Ap.Enum.ext(rs) == Done{(e, c2)} : Ap.Rd(Ap.Enum)}) -> {Ap.Enum.valid(n, diff, True{}, e) == True{} : Bool}:
  match rs:
    case Fail{err}:
      Rd.absurd(Ap.Enum, {Ap.Enum.valid(n, diff, True{}, e) == True{} : Bool}, err, e, c2, d)
    case Done{(+i, +c)}:
      ev = Equal.cong(Ap.Rd(Ap.Enum), Ap.Enum, y => Rd.value(Ap.Enum, y, e), Done{(Ap.Ext{i}, c)}, Done{(e, c2)}, d)
      %ev : {Ap.Enum.valid(n, diff, True{}, _) == True{} : Bool}
      Small.dv(Ap.Bit.read(c0), i, c, ers)

def Enum.dv.bit(+n: Nat, +diff: U32, rb: Ap.Rd(Bool), +e: Ap.Enum, +c2: Ap.Cur, +d: {Ap.Enum.bit(n, diff, rb) == Done{(e, c2)} : Ap.Rd(Ap.Enum)}) -> {Ap.Enum.valid(n, diff, True{}, e) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(Ap.Enum, {Ap.Enum.valid(n, diff, True{}, e) == True{} : Bool}, err, e, c2, d)
    case Done{(b, +c)}:
      match b:
        case False{}:
          Enum.dv.root(n, diff, True{}, c, Ap.Int.read(n, diff, c), {==}, e, c2, d)
        case True{}:
          Enum.dv.ext(n, diff, c, Ap.Small.read(c), {==}, e, c2, d)

def L.aper.enum.decode_valid(n, diff, ext, c, e, c2, d):
  match ext:
    case False{}:
      Enum.dv.root(n, diff, False{}, c, Ap.Int.read(n, diff, c), {==}, e, c2, d)
    case True{}:
      Enum.dv.bit(n, diff, Ap.Bit.read(c), e, c2, d)

# Extensible values
# -----------------

def Bool.or_intro_l(a: Bool, +b: Bool, ea: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, P.Refute.bool(ea))

def Bool.or_intro_r(a: Bool, +b: Bool, eb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      eb

def Bool.or_true_r(a: Bool, +b: Bool, ea: {a == False{} : Bool}, e: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, P.Refute.true_false(ea))
    case False{}:
      e

def L.aper.xint.roundtrip(n, diff, x, rem, rest, v):
  match x:
    case Ap.IRoot{i}:
      ir = Equal.sym(Ap.Rd(U32), Ap.Int.read(n, diff, Ap.Cur{Ap.Rem.next(rem), Ap.Int.write(n, i, Ap.Rem.next(rem), rest)}), Done{(i, Ap.Cur{Ap.Int.after(n, Ap.Rem.next(rem)), rest})}, L.aper.int.roundtrip(n, diff, i, Ap.Rem.next(rem), rest, v))
      %ir : {Ap.XInt.root(_) == Done{(Ap.IRoot{i}, Ap.Cur{Ap.Rem.add(n, Ap.Rem.next(rem)), rest})} : Ap.Rd(Ap.XInt)}
      {==}
    case Ap.IExt{bs}:
      orr = Equal.sym(Ap.Rd(B.Bytes()), Ap.Open.read(Ap.Cur{Ap.Rem.next(rem), Ap.Open.write(bs, Ap.Rem.next(rem), rest)}), Done{(bs, Ap.Cur{0n, rest})}, L.aper.open.roundtrip(bs, Ap.Rem.next(rem), rest, v))
      %orr : {Ap.XInt.ext(_) == Done{(Ap.IExt{bs}, Ap.Cur{0n, rest})} : Ap.Rd(Ap.XInt)}
      {==}

def XInt.dv.root(+n: Nat, +diff: U32, +c0: Ap.Cur, ri: Ap.Rd(U32), +eri: {Ap.Int.read(n, diff, c0) == ri : Ap.Rd(U32)}, +x: Ap.XInt, +c2: Ap.Cur, +e: {Ap.XInt.root(ri) == Done{(x, c2)} : Ap.Rd(Ap.XInt)}) -> {Ap.XInt.valid(n, diff, x) == True{} : Bool}:
  match ri:
    case Fail{err}:
      Rd.absurd(Ap.XInt, {Ap.XInt.valid(n, diff, x) == True{} : Bool}, err, x, c2, e)
    case Done{(+i, +c)}:
      ev = Equal.cong(Ap.Rd(Ap.XInt), Ap.XInt, y => Rd.value(Ap.XInt, y, x), Done{(Ap.IRoot{i}, c)}, Done{(x, c2)}, e)
      %ev : {Ap.XInt.valid(n, diff, _) == True{} : Bool}
      Int.dv(n, diff, c0, i, c, eri)

def XInt.dv.ext(+n: Nat, +diff: U32, +c0: Ap.Cur, ro: Ap.Rd(B.Bytes()), +ero: {Ap.Open.read(c0) == ro : Ap.Rd(B.Bytes())}, +x: Ap.XInt, +c2: Ap.Cur, +e: {Ap.XInt.ext(ro) == Done{(x, c2)} : Ap.Rd(Ap.XInt)}) -> {Ap.XInt.valid(n, diff, x) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Rd.absurd(Ap.XInt, {Ap.XInt.valid(n, diff, x) == True{} : Bool}, err, x, c2, e)
    case Done{(+bs, +c)}:
      ev = Equal.cong(Ap.Rd(Ap.XInt), Ap.XInt, y => Rd.value(Ap.XInt, y, x), Done{(Ap.IExt{bs}, c)}, Done{(x, c2)}, e)
      %ev : {Ap.XInt.valid(n, diff, _) == True{} : Bool}
      L.aper.open.decode_valid(c0, bs, c, ero)

def XInt.dv(+n: Nat, +diff: U32, rb: Ap.Rd(Bool), +x: Ap.XInt, +c2: Ap.Cur, +e: {Ap.XInt.bit(n, diff, rb) == Done{(x, c2)} : Ap.Rd(Ap.XInt)}) -> {Ap.XInt.valid(n, diff, x) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(Ap.XInt, {Ap.XInt.valid(n, diff, x) == True{} : Bool}, err, x, c2, e)
    case Done{(b, +c)}:
      match b:
        case False{}:
          XInt.dv.root(n, diff, c, Ap.Int.read(n, diff, c), {==}, x, c2, e)
        case True{}:
          XInt.dv.ext(n, diff, c, Ap.Open.read(c), {==}, x, c2, e)

def L.aper.xint.decode_valid(n, diff, c, x, c2, e):
  XInt.dv(n, diff, Ap.Bit.read(c), x, c2, e)

def L.aper.xbig.roundtrip(n, diff, x, rem, rest, v, w):
  match x:
    case Ap.BRoot{bs}:
      br = Equal.sym(Ap.Rd(B.Bytes()), Ap.Big.read(n, diff, Ap.Cur{Ap.Rem.next(rem), Ap.Big.write(n, bs, Ap.Rem.next(rem), rest)}), Done{(bs, Ap.Cur{0n, rest})}, L.aper.big.roundtrip(n, diff, bs, Ap.Rem.next(rem), rest, v, w))
      %br : {Ap.XBig.root(_) == Done{(Ap.BRoot{bs}, Ap.Cur{0n, rest})} : Ap.Rd(Ap.XBig)}
      {==}
    case Ap.BExt{bs}:
      orr = Equal.sym(Ap.Rd(B.Bytes()), Ap.Open.read(Ap.Cur{Ap.Rem.next(rem), Ap.Open.write(bs, Ap.Rem.next(rem), rest)}), Done{(bs, Ap.Cur{0n, rest})}, L.aper.open.roundtrip(bs, Ap.Rem.next(rem), rest, v))
      %orr : {Ap.XBig.ext(_) == Done{(Ap.BExt{bs}, Ap.Cur{0n, rest})} : Ap.Rd(Ap.XBig)}
      {==}

def XBig.dv.root(+n: Nat, +diff: Nat, +c0: Ap.Cur, ri: Ap.Rd(B.Bytes()), +eri: {Ap.Big.read(n, diff, c0) == ri : Ap.Rd(B.Bytes())}, +x: Ap.XBig, +c2: Ap.Cur, +e: {Ap.XBig.root(ri) == Done{(x, c2)} : Ap.Rd(Ap.XBig)}) -> {Ap.XBig.valid(diff, x) == True{} : Bool}:
  match ri:
    case Fail{err}:
      Rd.absurd(Ap.XBig, {Ap.XBig.valid(diff, x) == True{} : Bool}, err, x, c2, e)
    case Done{(+bs, +c)}:
      ev = Equal.cong(Ap.Rd(Ap.XBig), Ap.XBig, y => Rd.value(Ap.XBig, y, x), Done{(Ap.BRoot{bs}, c)}, Done{(x, c2)}, e)
      %ev : {Ap.XBig.valid(diff, _) == True{} : Bool}
      L.aper.big.decode_valid(n, diff, c0, bs, c, eri)

def XBig.dv.ext(+diff: Nat, +c0: Ap.Cur, ro: Ap.Rd(B.Bytes()), +ero: {Ap.Open.read(c0) == ro : Ap.Rd(B.Bytes())}, +x: Ap.XBig, +c2: Ap.Cur, +e: {Ap.XBig.ext(ro) == Done{(x, c2)} : Ap.Rd(Ap.XBig)}) -> {Ap.XBig.valid(diff, x) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Rd.absurd(Ap.XBig, {Ap.XBig.valid(diff, x) == True{} : Bool}, err, x, c2, e)
    case Done{(+bs, +c)}:
      ev = Equal.cong(Ap.Rd(Ap.XBig), Ap.XBig, y => Rd.value(Ap.XBig, y, x), Done{(Ap.BExt{bs}, c)}, Done{(x, c2)}, e)
      %ev : {Ap.XBig.valid(diff, _) == True{} : Bool}
      L.aper.open.decode_valid(c0, bs, c, ero)

def XBig.dv(+n: Nat, +diff: Nat, rb: Ap.Rd(Bool), +x: Ap.XBig, +c2: Ap.Cur, +e: {Ap.XBig.bit(n, diff, rb) == Done{(x, c2)} : Ap.Rd(Ap.XBig)}) -> {Ap.XBig.valid(diff, x) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(Ap.XBig, {Ap.XBig.valid(diff, x) == True{} : Bool}, err, x, c2, e)
    case Done{(b, +c)}:
      match b:
        case False{}:
          XBig.dv.root(n, diff, c, Ap.Big.read(n, diff, c), {==}, x, c2, e)
        case True{}:
          XBig.dv.ext(diff, c, Ap.Open.read(c), {==}, x, c2, e)

def L.aper.xbig.decode_valid(n, diff, c, x, c2, e):
  XBig.dv(n, diff, Ap.Bit.read(c), x, c2, e)

def XBits.rt(+n: Nat, +bs: Ap.Bits(), +rem: Nat, +rest: Ap.Bits(), root: Bool, +er: {Nat.is_eq(List.length(&2, Bool, bs), n) == root : Bool}, +v: {Ap.XBits.valid(n, bs) == True{} : Bool}) -> {Ap.XBits.bit(n, Ap.Bit.read(Ap.Cur{rem, Ap.XBits.body(bs, rem, rest, root)})) == Done{(bs, Ap.Cur{Ap.XBits.rem(bs, rem, root), rest})} : Ap.Rd(Ap.Bits())}:
  match root:
    case True{}:
      el = P.Nat.eq_of_is_eq(List.length(&2, Bool, bs), n, er)
      %el : {Ap.Bits.go(_, Ap.Rem.add(_, Ap.Rem.next(rem)), List.append(&2, Bool, bs, rest)) == Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), Ap.Rem.next(rem)), rest})} : Ap.Rd(Ap.Bits())}
      Equal.sym(Ap.Rd(Ap.Bits()), Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), Ap.Rem.next(rem)), rest})}, Ap.Bits.go(List.length(&2, Bool, bs), Ap.Rem.add(List.length(&2, Bool, bs), Ap.Rem.next(rem)), List.append(&2, Bool, bs, rest)), Bits.go_app(bs, Ap.Rem.add(List.length(&2, Bool, bs), Ap.Rem.next(rem)), rest))
    case False{}:
      ur = Equal.sym(Ap.Rd(Ap.Bits()), Ap.UBitStr.read(Ap.Cur{Ap.Rem.next(rem), Ap.UBitStr.write(bs, Ap.Rem.next(rem), rest)}), Done{(bs, Ap.Cur{Ap.UBitStr.after(bs, Ap.Rem.next(rem)), rest})}, L.aper.ubitstr.roundtrip(bs, Ap.Rem.next(rem), rest, Bool.or_true_r(Nat.is_eq(List.length(&2, Bool, bs), n), Ap.UBitStr.valid(bs), er, v)))
      %ur : {Ap.XBits.outside(n, _) == Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})} : Ap.Rd(Ap.Bits())}
      ser = Equal.sym(Bool, Nat.is_eq(List.length(&2, Bool, bs), n), False{}, er)
      %ser : {Ap.XBits.of(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest}, Bool.not(_)) == Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})} : Ap.Rd(Ap.Bits())}
      {==}

def L.aper.xbits.roundtrip(n, bs, rem, rest, v):
  XBits.rt(n, bs, rem, rest, Nat.is_eq(List.length(&2, Bool, bs), n), {==}, v)

def XBits.dv.out(+n: Nat, +bs0: Ap.Bits(), +c: Ap.Cur, ok: Bool, +bs: Ap.Bits(), +c2: Ap.Cur, +e: {Ap.XBits.of(bs0, c, ok) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}, uv: {Ap.UBitStr.valid(bs0) == True{} : Bool}) -> {Ap.XBits.valid(n, bs) == True{} : Bool}:
  match ok:
    case False{}:
      Rd.absurd(Ap.Bits(), {Ap.XBits.valid(n, bs) == True{} : Bool}, B.Invalid{2}, bs, c2, e)
    case True{}:
      ev = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Bits(), y => Rd.value(Ap.Bits(), y, bs), Done{(bs0, c)}, Done{(bs, c2)}, e)
      %ev : {Ap.XBits.valid(n, _) == True{} : Bool}
      Bool.or_intro_r(Nat.is_eq(List.length(&2, Bool, bs0), n), Ap.UBitStr.valid(bs0), uv)

def XBits.dv.ext(+n: Nat, +c0: Ap.Cur, ru: Ap.Rd(Ap.Bits()), +eru: {Ap.UBitStr.read(c0) == ru : Ap.Rd(Ap.Bits())}, +bs: Ap.Bits(), +c2: Ap.Cur, +e: {Ap.XBits.outside(n, ru) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}) -> {Ap.XBits.valid(n, bs) == True{} : Bool}:
  match ru:
    case Fail{err}:
      Rd.absurd(Ap.Bits(), {Ap.XBits.valid(n, bs) == True{} : Bool}, err, bs, c2, e)
    case Done{(+bs0, +c)}:
      XBits.dv.out(n, bs0, c, Bool.not(Nat.is_eq(List.length(&2, Bool, bs0), n)), bs, c2, e, L.aper.ubitstr.decode_valid(c0, bs0, c, eru))

def XBits.dv.root(+n: Nat, c0: Ap.Cur, +bs: Ap.Bits(), +c2: Ap.Cur, +e: {Ap.Bits.read(n, c0) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}) -> {Ap.XBits.valid(n, bs) == True{} : Bool}:
  match c0:
    case Ap.Cur{+rem, +bits}:
      slen = Equal.sym(Nat, List.length(&2, Bool, bs), n, Bits.len(bs, c2, n, Ap.Rem.add(n, rem), Bits.spec(n, Ap.Rem.add(n, rem), bits, bs, c2, e)))
      %slen : {Bool.or(Nat.is_eq(_, n), Ap.UBitStr.valid(bs)) == True{} : Bool}
      Bool.or_intro_l(Nat.is_eq(n, n), Ap.UBitStr.valid(bs), P.Nat.is_eq_refl(n))

def XBits.dv(+n: Nat, rb: Ap.Rd(Bool), +bs: Ap.Bits(), +c2: Ap.Cur, +e: {Ap.XBits.bit(n, rb) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}) -> {Ap.XBits.valid(n, bs) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(Ap.Bits(), {Ap.XBits.valid(n, bs) == True{} : Bool}, err, bs, c2, e)
    case Done{(b, +c)}:
      match b:
        case False{}:
          XBits.dv.root(n, c, bs, c2, e)
        case True{}:
          XBits.dv.ext(n, c, Ap.UBitStr.read(c), {==}, bs, c2, e)

def L.aper.xbits.decode_valid(n, c, bs, c2, e):
  XBits.dv(n, Ap.Bit.read(c), bs, c2, e)

def XBitStr.rt(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +bs: Ap.Bits(), +rem: Nat, +rest: Ap.Bits(), root: Bool, +er: {Ap.Size.valid(lo, diff, List.length(&2, Bool, bs)) == root : Bool}, +v: {Ap.XBitStr.valid(lo, diff, bs) == True{} : Bool}, +w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}) -> {Ap.XBitStr.bit(al, n, lo, diff, Ap.Bit.read(Ap.Cur{rem, Ap.XBitStr.body(al, n, lo, bs, rem, rest, root)})) == Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})} : Ap.Rd(Ap.Bits())}:
  match root:
    case True{}:
      L.aper.bitstr.roundtrip(al, n, lo, diff, bs, Ap.Rem.next(rem), rest, er, w)
    case False{}:
      ur = Equal.sym(Ap.Rd(Ap.Bits()), Ap.UBitStr.read(Ap.Cur{Ap.Rem.next(rem), Ap.UBitStr.write(bs, Ap.Rem.next(rem), rest)}), Done{(bs, Ap.Cur{Ap.UBitStr.after(bs, Ap.Rem.next(rem)), rest})}, L.aper.ubitstr.roundtrip(bs, Ap.Rem.next(rem), rest, Bool.or_true_r(Ap.Size.valid(lo, diff, List.length(&2, Bool, bs)), Ap.UBitStr.valid(bs), er, v)))
      %ur : {Ap.XBitStr.outside(lo, diff, _) == Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})} : Ap.Rd(Ap.Bits())}
      ser = Equal.sym(Bool, Ap.Size.valid(lo, diff, List.length(&2, Bool, bs)), False{}, er)
      %ser : {Ap.XBits.of(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest}, Bool.not(_)) == Done{(bs, Ap.Cur{Ap.Rem.add(List.length(&2, Bool, bs), 0n), rest})} : Ap.Rd(Ap.Bits())}
      {==}

def L.aper.xbitstr.roundtrip(al, n, lo, diff, bs, rem, rest, v, w):
  XBitStr.rt(al, n, lo, diff, bs, rem, rest, Ap.Size.valid(lo, diff, List.length(&2, Bool, bs)), {==}, v, w)

def XBitStr.dv.out(+lo: Nat, +diff: Nat, +bs0: Ap.Bits(), +c: Ap.Cur, ok: Bool, +bs: Ap.Bits(), +c2: Ap.Cur, +e: {Ap.XBits.of(bs0, c, ok) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}, uv: {Ap.UBitStr.valid(bs0) == True{} : Bool}) -> {Ap.XBitStr.valid(lo, diff, bs) == True{} : Bool}:
  match ok:
    case False{}:
      Rd.absurd(Ap.Bits(), {Ap.XBitStr.valid(lo, diff, bs) == True{} : Bool}, B.Invalid{2}, bs, c2, e)
    case True{}:
      ev = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Bits(), y => Rd.value(Ap.Bits(), y, bs), Done{(bs0, c)}, Done{(bs, c2)}, e)
      %ev : {Ap.XBitStr.valid(lo, diff, _) == True{} : Bool}
      Bool.or_intro_r(Ap.Size.valid(lo, diff, List.length(&2, Bool, bs0)), Ap.UBitStr.valid(bs0), uv)

def XBitStr.dv.ext(+lo: Nat, +diff: Nat, +c0: Ap.Cur, ru: Ap.Rd(Ap.Bits()), +eru: {Ap.UBitStr.read(c0) == ru : Ap.Rd(Ap.Bits())}, +bs: Ap.Bits(), +c2: Ap.Cur, +e: {Ap.XBitStr.outside(lo, diff, ru) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}) -> {Ap.XBitStr.valid(lo, diff, bs) == True{} : Bool}:
  match ru:
    case Fail{err}:
      Rd.absurd(Ap.Bits(), {Ap.XBitStr.valid(lo, diff, bs) == True{} : Bool}, err, bs, c2, e)
    case Done{(+bs0, +c)}:
      XBitStr.dv.out(lo, diff, bs0, c, Bool.not(Ap.Size.valid(lo, diff, List.length(&2, Bool, bs0))), bs, c2, e, L.aper.ubitstr.decode_valid(c0, bs0, c, eru))

def XBitStr.dv(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, rb: Ap.Rd(Bool), +bs: Ap.Bits(), +c2: Ap.Cur, +e: {Ap.XBitStr.bit(al, n, lo, diff, rb) == Done{(bs, c2)} : Ap.Rd(Ap.Bits())}) -> {Ap.XBitStr.valid(lo, diff, bs) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(Ap.Bits(), {Ap.XBitStr.valid(lo, diff, bs) == True{} : Bool}, err, bs, c2, e)
    case Done{(b, +c)}:
      match b:
        case False{}:
          Bool.or_intro_l(Ap.Size.valid(lo, diff, List.length(&2, Bool, bs)), Ap.UBitStr.valid(bs), L.aper.bitstr.decode_valid(al, n, lo, diff, c, bs, c2, e))
        case True{}:
          XBitStr.dv.ext(lo, diff, c, Ap.UBitStr.read(c), {==}, bs, c2, e)

def L.aper.xbitstr.decode_valid(al, n, lo, diff, c, bs, c2, e):
  XBitStr.dv(al, n, lo, diff, Ap.Bit.read(c), bs, c2, e)

def XStr.rt(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, +s: B.Bytes(), +rem: Nat, +rest: Ap.Bits(), root: Bool, +er: {Ap.Size.valid(lo, diff, List.length(&2, U32, s)) == root : Bool}, +v: {Ap.XStr.valid(lo, diff, s) == True{} : Bool}, +w: {Nat.is_lt(diff, Ap.Nat.pow2(n)) == True{} : Bool}) -> {Ap.XStr.bit(al, n, lo, diff, Ap.Bit.read(Ap.Cur{rem, Ap.XStr.body(al, n, lo, s, rem, rest, root)})) == Done{(s, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}:
  match root:
    case True{}:
      L.aper.str.roundtrip(al, n, lo, diff, s, Ap.Rem.next(rem), rest, P.Bool.and_intro(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Str.all(s), er, P.Bool.and_true_r(Bool.or(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Len.valid(List.length(&2, U32, s))), Ap.Str.all(s), v)), w)
    case False{}:
      lv = Bool.or_true_r(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Len.valid(List.length(&2, U32, s)), er, P.Bool.and_true_l(Bool.or(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Len.valid(List.length(&2, U32, s))), Ap.Str.all(s), v))
      ur = Equal.sym(Ap.Rd(B.Bytes()), Ap.UStr.read(Ap.Cur{Ap.Rem.next(rem), Ap.UStr.write(s, Ap.Rem.next(rem), rest)}), Done{(s, Ap.Cur{0n, rest})}, L.aper.ustr.roundtrip(s, Ap.Rem.next(rem), rest, P.Bool.and_intro(Ap.Len.valid(List.length(&2, U32, s)), Ap.Str.all(s), lv, P.Bool.and_true_r(Bool.or(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Len.valid(List.length(&2, U32, s))), Ap.Str.all(s), v))))
      %ur : {Ap.XStr.outside(lo, diff, _) == Done{(s, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
      ser = Equal.sym(Bool, Ap.Size.valid(lo, diff, List.length(&2, U32, s)), False{}, er)
      %ser : {Ap.XStr.of(s, Ap.Cur{0n, rest}, Bool.not(_)) == Done{(s, Ap.Cur{0n, rest})} : Ap.Rd(B.Bytes())}
      {==}

def L.aper.xstr.roundtrip(al, n, lo, diff, s, rem, rest, v, w):
  XStr.rt(al, n, lo, diff, s, rem, rest, Ap.Size.valid(lo, diff, List.length(&2, U32, s)), {==}, v, w)

def XStr.dv.out(+lo: Nat, +diff: Nat, +s0: B.Bytes(), +c: Ap.Cur, ok: Bool, +s: B.Bytes(), +c2: Ap.Cur, +e: {Ap.XStr.of(s0, c, ok) == Done{(s, c2)} : Ap.Rd(B.Bytes())}, +uv: {Ap.UStr.valid(s0) == True{} : Bool}) -> {Ap.XStr.valid(lo, diff, s) == True{} : Bool}:
  match ok:
    case False{}:
      Rd.absurd(B.Bytes(), {Ap.XStr.valid(lo, diff, s) == True{} : Bool}, B.Invalid{2}, s, c2, e)
    case True{}:
      ev = Equal.cong(Ap.Rd(B.Bytes()), B.Bytes(), y => Rd.value(B.Bytes(), y, s), Done{(s0, c)}, Done{(s, c2)}, e)
      %ev : {Ap.XStr.valid(lo, diff, _) == True{} : Bool}
      P.Bool.and_intro(Bool.or(Ap.Size.valid(lo, diff, List.length(&2, U32, s0)), Ap.Len.valid(List.length(&2, U32, s0))), Ap.Str.all(s0), Bool.or_intro_r(Ap.Size.valid(lo, diff, List.length(&2, U32, s0)), Ap.Len.valid(List.length(&2, U32, s0)), P.Bool.and_true_l(Ap.Len.valid(List.length(&2, U32, s0)), Ap.Str.all(s0), uv)), P.Bool.and_true_r(Ap.Len.valid(List.length(&2, U32, s0)), Ap.Str.all(s0), uv))

def XStr.dv.ext(+lo: Nat, +diff: Nat, +c0: Ap.Cur, ru: Ap.Rd(B.Bytes()), +eru: {Ap.UStr.read(c0) == ru : Ap.Rd(B.Bytes())}, +s: B.Bytes(), +c2: Ap.Cur, +e: {Ap.XStr.outside(lo, diff, ru) == Done{(s, c2)} : Ap.Rd(B.Bytes())}) -> {Ap.XStr.valid(lo, diff, s) == True{} : Bool}:
  match ru:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.XStr.valid(lo, diff, s) == True{} : Bool}, err, s, c2, e)
    case Done{(+s0, +c)}:
      XStr.dv.out(lo, diff, s0, c, Bool.not(Ap.Size.valid(lo, diff, List.length(&2, U32, s0))), s, c2, e, L.aper.ustr.decode_valid(c0, s0, c, eru))

def XStr.dv.root(+lo: Nat, +diff: Nat, +s: B.Bytes(), +sv: {Ap.Str.valid(lo, diff, s) == True{} : Bool}) -> {Ap.XStr.valid(lo, diff, s) == True{} : Bool}:
  P.Bool.and_intro(Bool.or(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Len.valid(List.length(&2, U32, s))), Ap.Str.all(s), Bool.or_intro_l(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Len.valid(List.length(&2, U32, s)), P.Bool.and_true_l(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Str.all(s), sv)), P.Bool.and_true_r(Ap.Size.valid(lo, diff, List.length(&2, U32, s)), Ap.Str.all(s), sv))

def XStr.dv(+al: Bool, +n: Nat, +lo: Nat, +diff: Nat, rb: Ap.Rd(Bool), +s: B.Bytes(), +c2: Ap.Cur, +e: {Ap.XStr.bit(al, n, lo, diff, rb) == Done{(s, c2)} : Ap.Rd(B.Bytes())}) -> {Ap.XStr.valid(lo, diff, s) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(B.Bytes(), {Ap.XStr.valid(lo, diff, s) == True{} : Bool}, err, s, c2, e)
    case Done{(b, +c)}:
      match b:
        case False{}:
          XStr.dv.root(lo, diff, s, L.aper.str.decode_valid(al, n, lo, diff, c, s, c2, e))
        case True{}:
          XStr.dv.ext(lo, diff, c, Ap.UStr.read(c), {==}, s, c2, e)

def L.aper.xstr.decode_valid(al, n, lo, diff, c, s, c2, e):
  XStr.dv(al, n, lo, diff, Ap.Bit.read(c), s, c2, e)
