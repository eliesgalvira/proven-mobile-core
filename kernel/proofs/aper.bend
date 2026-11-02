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

def Bits.len.step(+p: Nat, +b: Bool, r: Ap.Rd(Ap.Bits()), ih: @bs2: Ap.Bits() -> @c2: Ap.Cur -> {r == Done{(bs2, c2)} : Ap.Rd(Ap.Bits())} -> {List.length(&2, Bool, bs2) == p : Nat}, +bs: Ap.Bits(), +c: Ap.Cur, +e: {Ap.Bits.cons(b, r) == Done{(bs, c)} : Ap.Rd(Ap.Bits())}) -> {List.length(&2, Bool, bs) == 1n+p : Nat}:
  match r:
    case Fail{err}:
      Rd.absurd(Ap.Bits(), {List.length(&2, Bool, bs) == 1n+p : Nat}, err, bs, c, e)
    case Done{(+bs2, +c2)}:
      ev = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Bits(), x => Rd.value(Ap.Bits(), x, bs), Done{(b <> bs2, c2)}, Done{(bs, c)}, e)
      %ev : {List.length(&2, Bool, _) == 1n+p : Nat}
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Bool, bs2), p, ih(bs2, c2, {==}))

# What Bits.go read has the length it was asked for.
def Bits.len(n: Nat, +r: Nat, bits: Ap.Bits(), +bs: Ap.Bits(), +c: Ap.Cur, +e: {Ap.Bits.go(n, r, bits) == Done{(bs, c)} : Ap.Rd(Ap.Bits())}) -> {List.length(&2, Bool, bs) == n : Nat}:
  match n bits:
    case 0n rest:
      ev = Equal.cong(Ap.Rd(Ap.Bits()), Ap.Bits(), x => Rd.value(Ap.Bits(), x, bs), Done{([], Ap.Cur{r, rest})}, Done{(bs, c)}, e)
      %ev : {List.length(&2, Bool, _) == 0n : Nat}
      {==}
    case 1n++p Nil{}:
      Rd.absurd(Ap.Bits(), {List.length(&2, Bool, bs) == 1n+p : Nat}, B.Short{}, bs, c, e)
    case 1n+p b <> +t:
      Bits.len.step(p, b, Ap.Bits.go(p, r, t), bs2 => c2 => e2 => Bits.len(p, r, t, bs2, c2, e2), bs, c, e)

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

def U32.to_of(+bs: Ap.Bits(), le: {Nat.is_le(List.length(&2, Bool, bs), 32n) == True{} : Bool}) -> {bs == Ap.U32.to_bits(List.length(&2, Bool, bs), Ap.U32.of_bits(bs)) : Ap.Bits()}:
  rl = Bits.rev_len(bs)
  srl = Equal.sym(Nat, List.length(&2, Bool, bs), List.length(&2, Bool, List.reverse(&2, Bool, bs)), Bits.rev_len(bs))
  %srl : {bs == Ap.U32.to_bits(_, Ap.U32.of_bits(bs)) : Ap.Bits()}
  po = Word.prefix_of(32n, List.reverse(&2, Bool, bs), (%rl : {Nat.is_le(_, 32n) == True{} : Bool}; le))
  %po : {bs == List.reverse(&2, Bool, _) : Ap.Bits()}
  Bits.rev_rev(bs)

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
      Int.dv.ok(n, diff, bs, c, U32.is_le(Ap.U32.of_bits(bs), diff), {==}, x, c2, e, Bits.len(n, r, bits, bs, c, erb))

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

def Len.rt.body(+n: Nat, short: Bool, es: {Nat.is_lt(n, 128n) == short : Bool}, +rest: Ap.Bits(), +v: {Nat.is_lt(n, 16384n) == True{} : Bool}) -> {Ap.Len.first(Ap.Bit.read(Ap.Cur{0n, Ap.Len.body(n, short, rest)})) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}:
  match short:
    case True{}:
      tl = Nat.to_bits_len(7n, n)
      %tl : {Ap.Len.short(Ap.Bits.go(_, 0n, List.append(&2, Bool, Ap.Nat.to_bits(7n, n), rest))) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      ga = Bits.go_app(Ap.Nat.to_bits(7n, n), 0n, rest)
      %ga : {Ap.Len.short(_) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      ot = Nat.of_to_bits(7n, n, es)
      %ot : {Done{(_, Ap.Cur{0n, rest})} == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      {==}
    case False{}:
      tl = Nat.to_bits_len(14n, n)
      %tl : {Ap.Len.long(Ap.Bits.go(_, 0n, List.append(&2, Bool, Ap.Nat.to_bits(14n, n), rest))) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      ga = Bits.go_app(Ap.Nat.to_bits(14n, n), 0n, rest)
      %ga : {Ap.Len.long(_) == Done{(n, Ap.Cur{0n, rest})} : Ap.Rd(Nat)}
      ot = Nat.of_to_bits(14n, n, v)
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

def Len.dv.short(rb: Ap.Rd(Ap.Bits()), +r: Nat, +bits: Ap.Bits(), +erb: {Ap.Bits.go(7n, r, bits) == rb : Ap.Rd(Ap.Bits())}, +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.short(rb) == Done{(n, c2)} : Ap.Rd(Nat)}) -> {Nat.is_lt(n, 16384n) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(Nat, {Nat.is_lt(n, 16384n) == True{} : Bool}, err, n, c2, e)
    case Done{(+bs, +c)}:
      ev = Equal.cong(Ap.Rd(Nat), Nat, y => Rd.value(Nat, y, n), Done{(Ap.Nat.of_bits(bs), c)}, Done{(n, c2)}, e)
      %ev : {Nat.is_lt(_, 16384n) == True{} : Bool}
      Nat.lt_le_trans(Ap.Nat.of_bits(bs), 128n, 16384n, Len.bound(bs, 7n, Bits.len(7n, r, bits, bs, c, erb)), {==})

def Len.dv.long.ok(+bs: Ap.Bits(), +c: Ap.Cur, ok: Bool, +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.of(Ap.Nat.of_bits(bs), c, ok) == Done{(n, c2)} : Ap.Rd(Nat)}, len: {List.length(&2, Bool, bs) == 14n : Nat}) -> {Nat.is_lt(n, 16384n) == True{} : Bool}:
  match ok:
    case False{}:
      Rd.absurd(Nat, {Nat.is_lt(n, 16384n) == True{} : Bool}, B.Invalid{128}, n, c2, e)
    case True{}:
      ev = Equal.cong(Ap.Rd(Nat), Nat, y => Rd.value(Nat, y, n), Done{(Ap.Nat.of_bits(bs), c)}, Done{(n, c2)}, e)
      %ev : {Nat.is_lt(_, 16384n) == True{} : Bool}
      Len.bound(bs, 14n, len)

def Len.dv.long(rb: Ap.Rd(Ap.Bits()), +r: Nat, +bits: Ap.Bits(), +erb: {Ap.Bits.go(14n, r, bits) == rb : Ap.Rd(Ap.Bits())}, +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.long(rb) == Done{(n, c2)} : Ap.Rd(Nat)}) -> {Nat.is_lt(n, 16384n) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Rd.absurd(Nat, {Nat.is_lt(n, 16384n) == True{} : Bool}, err, n, c2, e)
    case Done{(+bs, +c)}:
      Len.dv.long.ok(bs, c, Nat.is_le(128n, Ap.Nat.of_bits(bs)), n, c2, e, Bits.len(14n, r, bits, bs, c, erb))

def Len.dv.second(r2: Ap.Rd(Bool), +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.second(r2) == Done{(n, c2)} : Ap.Rd(Nat)}) -> {Nat.is_lt(n, 16384n) == True{} : Bool}:
  match r2:
    case Fail{err}:
      Rd.absurd(Nat, {Nat.is_lt(n, 16384n) == True{} : Bool}, err, n, c2, e)
    case Done{(b, c)}:
      match b:
        case True{}:
          Rd.absurd(Nat, {Nat.is_lt(n, 16384n) == True{} : Bool}, B.Unsupported{192}, n, c2, e)
        case False{}:
          match c:
            case Ap.Cur{+rem, +bits}:
              Len.dv.long(Ap.Bits.go(14n, Ap.Rem.add(14n, rem), bits), Ap.Rem.add(14n, rem), bits, {==}, n, c2, e)

def Len.dv.first(r1: Ap.Rd(Bool), +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.first(r1) == Done{(n, c2)} : Ap.Rd(Nat)}) -> {Nat.is_lt(n, 16384n) == True{} : Bool}:
  match r1:
    case Fail{err}:
      Rd.absurd(Nat, {Nat.is_lt(n, 16384n) == True{} : Bool}, err, n, c2, e)
    case Done{(b, c)}:
      match b:
        case False{}:
          match c:
            case Ap.Cur{+rem, +bits}:
              Len.dv.short(Ap.Bits.go(7n, Ap.Rem.add(7n, rem), bits), Ap.Rem.add(7n, rem), bits, {==}, n, c2, e)
        case True{}:
          Len.dv.second(Ap.Bit.read(c), n, c2, e)

def Len.dv(ra: Ap.Rd(Unit), +n: Nat, +c2: Ap.Cur, +e: {Ap.Len.aligned(ra) == Done{(n, c2)} : Ap.Rd(Nat)}) -> {Nat.is_lt(n, 16384n) == True{} : Bool}:
  match ra:
    case Fail{err}:
      Rd.absurd(Nat, {Nat.is_lt(n, 16384n) == True{} : Bool}, err, n, c2, e)
    case Done{(u, c)}:
      Len.dv.first(Ap.Bit.read(c), n, c2, e)

def L.aper.no_big_nat(c, n, c2, e):
  Len.dv(Ap.Align.read(c), n, c2, e)

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
