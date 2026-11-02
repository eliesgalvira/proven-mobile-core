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
