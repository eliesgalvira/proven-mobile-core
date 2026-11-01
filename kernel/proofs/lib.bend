import Base
import ../bytes.bend as B

# Proof helpers shared by kernel/proofs/*.bend.

# Refutations
# -----------

def Lift(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def Refute.bool(e: {False{} == True{} : Bool}) -> Empty:
  s = Equal.sym(Bool, False{}, True{}, e)
  %s : Lift(_)
  Unit{}

def Res.disc(-E: Data, -A: Data, r: Result<&2, &2, E, A>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{v}:
      Empty

def Refute.fail_done(-E: Data, -A: Data, err: E, v: A, e: {Fail{err} == Done{v} : Result<&2, &2, E, A>}) -> Empty:
  %e : Res.disc(E, A, _)
  Unit{}

# Projections, for injectivity of Done
# ------------------------------------

def Res.value(-E: Data, -A: Data, r: Result<&2, &2, E, A>, d: A) -> A:
  match r:
    case Fail{e}:
      d
    case Done{v}:
      v

def Read.value(-A: Data, r: B.Read(A), d: A) -> A:
  match r:
    case Fail{e}:
      d
    case Done{(v, rest)}:
      v

def Read.rest(-A: Data, r: B.Read(A), d: B.Bytes()) -> B.Bytes():
  match r:
    case Fail{e}:
      d
    case Done{(v, rest)}:
      rest

# Bool
# ----

def Bool.and_true_l(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def Bool.and_true_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, Refute.bool(e))

# Cmp
# ---

def Cmp.not_eq_t(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Empty
    case LT{}:
      Unit
    case GT{}:
      Unit

def Refute.lt_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : Cmp.not_eq_t(_)
  Unit{}

def Refute.gt_eq(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : Cmp.not_eq_t(_)
  Unit{}

def Cmp.eq_of_is_eq(c: Cmp, e: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, Refute.bool(e))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, Refute.bool(e))

# U32 equality reflects: is_eq(a, b) == True gives a == b.

def Word.cmp_eq.step(-p: Nat, r: Cmp, ab: Bool, bb: Bool, at: Word(p), bt: Word(p), ih: {r == EQ{} : Cmp} -> {at == bt : Word(p)}, e: {Word.cmp.fin(ab, bb, r) == EQ{} : Cmp}) -> {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}:
  match r:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}, Refute.lt_eq(e))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}, Refute.gt_eq(e))
    case EQ{}:
      match ab bb:
        case False{} False{}:
          t = ih({==})
          %t : {WCon{False{}, at} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case True{} True{}:
          t = ih({==})
          %t : {WCon{True{}, at} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case False{} True{}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)}, Refute.lt_eq(e))
        case True{} False{}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)}, Refute.gt_eq(e))

def Word.cmp_eq(+n: Nat, a: Word(n), b: Word(n), e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          Word.cmp_eq.step(p, Word.cmp(p, at, bt), ab, bb, at, bt, r_e => Word.cmp_eq(p, at, bt, r_e), e)

def U32.eq_of_is_eq(a: U32, b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, Word.cmp_eq(32n, x, y, Cmp.eq_of_is_eq(Word.cmp(32n, x, y), e)))

# A digit below 10 fits four bits: refute every higher bit from the comparison.

def U32.lt10_mask4.hi(b31: Bool, b30: Bool, b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool, +d2: U32, same: {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == d2 : U32}, e: {U32.is_lt(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 10) == True{} : Bool}) -> {U32.and(15, d2) == d2 : U32}:
  match b31:
    case True{}:
      Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
    case False{}:
      match b30:
        case True{}:
          Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
        case False{}:
          match b29:
            case True{}:
              Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
            case False{}:
              match b28:
                case True{}:
                  Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                case False{}:
                  match b27:
                    case True{}:
                      Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                    case False{}:
                      match b26:
                        case True{}:
                          Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                        case False{}:
                          match b25:
                            case True{}:
                              Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                            case False{}:
                              match b24:
                                case True{}:
                                  Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                case False{}:
                                  match b23:
                                    case True{}:
                                      Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                    case False{}:
                                      match b22:
                                        case True{}:
                                          Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                        case False{}:
                                          match b21:
                                            case True{}:
                                              Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                            case False{}:
                                              match b20:
                                                case True{}:
                                                  Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                case False{}:
                                                  match b19:
                                                    case True{}:
                                                      Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                    case False{}:
                                                      match b18:
                                                        case True{}:
                                                          Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                        case False{}:
                                                          match b17:
                                                            case True{}:
                                                              Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                            case False{}:
                                                              match b16:
                                                                case True{}:
                                                                  Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                case False{}:
                                                                  match b15:
                                                                    case True{}:
                                                                      Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                    case False{}:
                                                                      match b14:
                                                                        case True{}:
                                                                          Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                        case False{}:
                                                                          match b13:
                                                                            case True{}:
                                                                              Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                            case False{}:
                                                                              match b12:
                                                                                case True{}:
                                                                                  Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                                case False{}:
                                                                                  match b11:
                                                                                    case True{}:
                                                                                      Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                                    case False{}:
                                                                                      match b10:
                                                                                        case True{}:
                                                                                          Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                                        case False{}:
                                                                                          match b9:
                                                                                            case True{}:
                                                                                              Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                                            case False{}:
                                                                                              match b8:
                                                                                                case True{}:
                                                                                                  Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                                                case False{}:
                                                                                                  match b7:
                                                                                                    case True{}:
                                                                                                      Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                                                    case False{}:
                                                                                                      match b6:
                                                                                                        case True{}:
                                                                                                          Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                                                        case False{}:
                                                                                                          match b5:
                                                                                                            case True{}:
                                                                                                              Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                                                            case False{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  Empty.absurd({U32.and(15, d2) == d2 : U32}, Refute.bool(e))
                                                                                                                case False{}:
                                                                                                                  %same : {U32.and(15, _) == _ : U32}
                                                                                                                  {==}

def U32.lt10_mask4.go(d: U32, +d2: U32, same: {d == d2 : U32}, e: {U32.is_lt(d, 10) == True{} : Bool}) -> {U32.and(15, d2) == d2 : U32}:
  match d:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      U32.lt10_mask4.hi(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, d2, same, e)

def U32.lt10_mask4(+d: U32, e: {U32.is_lt(d, 10) == True{} : Bool}) -> {U32.and(15, d) == d : U32}:
  U32.lt10_mask4.go(d, d, {==}, e)

# List
# ----

def List.drop0(xs: B.Bytes()) -> {List.drop(&2, U32, xs, 0n) == xs : B.Bytes()}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

# Nibbles: the low nibble of cat4(a, and(15, b)) is a, the high nibble is b,
# when each fits four bits.

def U32.cat4_lo(a: U32, b: U32, ma: {U32.and(15, a) == a : U32}) -> {U32.and(15, B.cat4(a, U32.and(15, b))) == a : U32}:
  match a b:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      ma

def U32.cat4_hi(a: U32, b: U32, mb: {U32.and(15, b) == b : U32}) -> {U32.and(15, U32.shrn(B.cat4(a, U32.and(15, b)), 4n)) == b : U32}:
  match a b:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      mb

def List.cons_eq(h1: U32, h2: U32, t1: B.Bytes(), t2: B.Bytes(), eh: {h1 == h2 : U32}, et: {t1 == t2 : B.Bytes()}) -> {h1 <> t1 == h2 <> t2 : B.Bytes()}:
  %eh : {h1 <> t1 == _ <> t2 : B.Bytes()}
  %et : {h1 <> t1 == h1 <> _ : B.Bytes()}
  {==}

def List.take_len(xs: B.Bytes(), n: Nat) -> {List.length(&2, U32, List.take(&2, U32, xs, n)) == Nat.min(List.length(&2, U32, xs), n) : Nat}:
  match xs n:
    case Nil{} _:
      {==}
    case x <> xt 0n:
      {==}
    case x <> xt 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, U32, List.take(&2, U32, xt, p)), Nat.min(List.length(&2, U32, xt), p), List.take_len(xt, p))

# bytes_eq reflects: bytes_eq(xs, ys) == True gives xs == ys.
def Bytes.eq_of_bytes_eq(xs: B.Bytes(), ys: B.Bytes(), +e: {B.bytes_eq(xs, ys) == True{} : Bool}) -> {xs == ys : B.Bytes()}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yt:
      Empty.absurd({Nil{} == y <> yt : B.Bytes()}, Refute.bool(e))
    case x <> xt Nil{}:
      Empty.absurd({x <> xt == Nil{} : B.Bytes()}, Refute.bool(e))
    case +x <> +xt +y <> +yt:
      List.cons_eq(x, y, xt, yt, U32.eq_of_is_eq(x, y, Bool.and_true_l(U32.is_eq(x, y), B.bytes_eq(xt, yt), e)), Bytes.eq_of_bytes_eq(xt, yt, Bool.and_true_r(U32.is_eq(x, y), B.bytes_eq(xt, yt), e)))

def Cmp.ge_false_of_lt(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_ge(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_ge(EQ{}) == False{} : Bool}, Refute.bool(e))
    case GT{}:
      Empty.absurd({Cmp.is_ge(GT{}) == False{} : Bool}, Refute.bool(e))

def Nat.ge_false_of_lt(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_ge(a, b) == False{} : Bool}:
  Cmp.ge_false_of_lt(Nat.cmp(a, b), e)

# Reflexivity and inequality of U32 comparisons
# ----------------------------------------------

def Bool.cmp_refl(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Word.cmp_refl(+n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          ih = Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, Word.cmp_refl(p, t))
          %ih : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          Bool.cmp_refl(b)

def U32.is_eq_refl(x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  match x:
    case U32{+w}:
      r = Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, Word.cmp_refl(32n, w))
      %r : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def Bytes.eq_refl(xs: B.Bytes()) -> {B.bytes_eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      e = Equal.sym(Bool, U32.is_eq(x, x), True{}, U32.is_eq_refl(x))
      %e : {Bool.and(_, B.bytes_eq(t, t)) == True{} : Bool}
      Bytes.eq_refl(t)

def Cmp.fin_tf_ne(r: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, r)) == False{} : Bool}:
  match r:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# A word never equals its increment (for at least one bit).
def Word.inc_ne(+n: Nat, w: Word(1n+n)) -> {Cmp.is_eq(Word.cmp(1n+n, w, Word.inc(1n+n, w))) == False{} : Bool}:
  match w:
    case WCon{b, +t}:
      match b:
        case False{}:
          r = Equal.sym(Cmp, Word.cmp(n, t, t), EQ{}, Word.cmp_refl(n, t))
          %r : {Cmp.is_eq(Word.cmp.fin(False{}, True{}, _)) == False{} : Bool}
          {==}
        case True{}:
          Cmp.fin_tf_ne(Word.cmp(n, t, Word.inc(n, t)))

def U32.inc_ne(x: U32) -> {U32.is_eq(x, U32.inc(x)) == False{} : Bool}:
  match x:
    case U32{w}:
      Word.inc_ne(31n, w)

def Cmp.eq_false_of_lt(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, Refute.bool(e))
    case GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == False{} : Bool}, Refute.bool(e))

def U32.eq_false_of_lt(a: U32, b: U32, e: {U32.is_lt(a, b) == True{} : Bool}) -> {U32.is_eq(a, b) == False{} : Bool}:
  Cmp.eq_false_of_lt(U32.cmp(a, b), e)

# Maybe
# -----

def Maybe.disc(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      Empty

def Refute.none_some(-A: Data, v: A, e: {None{} == Some{v} : Maybe<&2, A>}) -> Empty:
  %e : Maybe.disc(A, _)
  Unit{}

def Maybe.value(-A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{v}:
      v

# Nat ordering and equality
# -------------------------

def Nat.eq_of_is_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, Refute.bool(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, Refute.bool(e))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, Nat.eq_of_is_eq(p, q, e))

def Nat.is_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Nat.is_eq_refl(p)

def Nat.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Nat.le_refl(p)

def Nat.le_succ(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, Refute.bool(e))
    case 1n+p 1n+q:
      Nat.le_succ(p, q, e)

def Nat.le_add_left(a: Nat, +b: Nat, c: Nat, e: {Nat.is_le(Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_le(b, c) == True{} : Bool}:
  match a c:
    case 0n _:
      e
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(b, 0n) == True{} : Bool}, Refute.bool(e))
    case 1n+p 1n++q:
      Nat.le_succ(b, q, Nat.le_add_left(p, b, q, e))

def List.append_len(+xs: B.Bytes(), +ys: B.Bytes()) -> {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> xt:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, U32, List.append(&2, U32, xt, ys)), Nat.add(List.length(&2, U32, xt), List.length(&2, U32, ys)), List.append_len(xt, ys))


def Nat.le_app(body: B.Bytes(), W: B.Bytes(), f: Nat, h: {Nat.is_le(List.length(&2, U32, List.append(&2, U32, body, W)), f) == True{} : Bool}) -> {Nat.is_le(Nat.add(List.length(&2, U32, body), List.length(&2, U32, W)), f) == True{} : Bool}:
  al = List.append_len(body, W)
  %al : {Nat.is_le(_, f) == True{} : Bool}
  h

# c + |body ++ W| <= f gives |W| <= f.
def Nat.le_of_append(+body: B.Bytes(), +W: B.Bytes(), c: Nat, +f: Nat, e: {Nat.is_le(Nat.add(c, List.length(&2, U32, List.append(&2, U32, body, W))), f) == True{} : Bool}) -> {Nat.is_le(List.length(&2, U32, W), f) == True{} : Bool}:
  Nat.le_add_left(List.length(&2, U32, body), List.length(&2, U32, W), f, Nat.le_app(body, W, f, Nat.le_add_left(c, List.length(&2, U32, List.append(&2, U32, body, W)), f, e)))

def Bool.and_intro(a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  sa = Equal.sym(Bool, a, True{}, ea)
  sb = Equal.sym(Bool, b, True{}, eb)
  %sa : {Bool.and(_, b) == True{} : Bool}
  %sb : {Bool.and(True{}, _) == True{} : Bool}
  {==}

def Refute.true_false(e: {True{} == False{} : Bool}) -> Empty:
  Refute.bool(Equal.sym(Bool, True{}, False{}, e))

def Cmp.lt_of_not_ge(c: Cmp, e: {Cmp.is_ge(c) == False{} : Bool}) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, Refute.true_false(e))
    case GT{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, Refute.true_false(e))

def U32.lt_of_not_ge(a: U32, b: U32, e: {U32.is_ge(a, b) == False{} : Bool}) -> {U32.is_lt(a, b) == True{} : Bool}:
  Cmp.lt_of_not_ge(U32.cmp(a, b), e)

# take of an appended prefix
def Take.append(xs: B.Bytes(), +rest: B.Bytes()) -> {B.take(List.length(&2, U32, xs), List.append(&2, U32, xs, rest)) == Done{(xs, rest)} : B.Read(B.Bytes())}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      ih = Equal.sym(B.Read(B.Bytes()), B.take(List.length(&2, U32, t), List.append(&2, U32, t, rest)), Done{(t, rest)}, Take.append(t, rest))
      %ih : {B.Take.cons(x, _) == Done{(x <> t, rest)} : B.Read(B.Bytes())}
      {==}

# Bytes of cat8: the low byte is lo, the high byte is hi, when each fits a byte.
def U32.cat8_lo(a: U32, b: U32, ma: {U32.and(255, a) == a : U32}) -> {U32.and(255, B.cat8(a, b)) == a : U32}:
  match a b:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      ma

def U32.cat8_hi(a: U32, b: U32, mb: {U32.and(255, b) == b : U32}) -> {U32.and(255, U32.shrn(B.cat8(a, b), 8n)) == b : U32}:
  match a b:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      mb

# A byte is never below zero.
def U32.lt256_mask8.low(b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool, e: {Cmp.is_lt(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, False{}, Word.cmp.fin(b3, False{}, Word.cmp.fin(b4, False{}, Word.cmp.fin(b5, False{}, Word.cmp.fin(b6, False{}, Bool.cmp(b7, False{}))))))))) == True{} : Bool}) -> Empty:
  match b7:
    case True{}:
      Refute.bool(e)
    case False{}:
      match b6:
        case True{}:
          Refute.bool(e)
        case False{}:
          match b5:
            case True{}:
              Refute.bool(e)
            case False{}:
              match b4:
                case True{}:
                  Refute.bool(e)
                case False{}:
                  match b3:
                    case True{}:
                      Refute.bool(e)
                    case False{}:
                      match b2:
                        case True{}:
                          Refute.bool(e)
                        case False{}:
                          match b1:
                            case True{}:
                              Refute.bool(e)
                            case False{}:
                              match b0:
                                case True{}:
                                  Refute.bool(e)
                                case False{}:
                                  Refute.bool(e)

# A byte (below 256) fits eight bits.
def U32.lt256_mask8.hi(b31: Bool, b30: Bool, b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool, +d2: U32, same: {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == d2 : U32}, e: {U32.is_lt(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 256) == True{} : Bool}) -> {U32.and(255, d2) == d2 : U32}:
  match b31:
    case True{}:
      Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
    case False{}:
      match b30:
        case True{}:
          Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
        case False{}:
          match b29:
            case True{}:
              Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
            case False{}:
              match b28:
                case True{}:
                  Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                case False{}:
                  match b27:
                    case True{}:
                      Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                    case False{}:
                      match b26:
                        case True{}:
                          Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                        case False{}:
                          match b25:
                            case True{}:
                              Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                            case False{}:
                              match b24:
                                case True{}:
                                  Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                case False{}:
                                  match b23:
                                    case True{}:
                                      Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                    case False{}:
                                      match b22:
                                        case True{}:
                                          Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                        case False{}:
                                          match b21:
                                            case True{}:
                                              Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                            case False{}:
                                              match b20:
                                                case True{}:
                                                  Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                case False{}:
                                                  match b19:
                                                    case True{}:
                                                      Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                    case False{}:
                                                      match b18:
                                                        case True{}:
                                                          Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                        case False{}:
                                                          match b17:
                                                            case True{}:
                                                              Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                            case False{}:
                                                              match b16:
                                                                case True{}:
                                                                  Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                                case False{}:
                                                                  match b15:
                                                                    case True{}:
                                                                      Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                                    case False{}:
                                                                      match b14:
                                                                        case True{}:
                                                                          Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                                        case False{}:
                                                                          match b13:
                                                                            case True{}:
                                                                              Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                                            case False{}:
                                                                              match b12:
                                                                                case True{}:
                                                                                  Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                                                case False{}:
                                                                                  match b11:
                                                                                    case True{}:
                                                                                      Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                                                    case False{}:
                                                                                      match b10:
                                                                                        case True{}:
                                                                                          Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                                                        case False{}:
                                                                                          match b9:
                                                                                            case True{}:
                                                                                              Empty.absurd({U32.and(255, d2) == d2 : U32}, Refute.bool(e))
                                                                                            case False{}:
                                                                                              match b8:
                                                                                                case True{}:
                                                                                                  Empty.absurd({U32.and(255, d2) == d2 : U32}, U32.lt256_mask8.low(b7, b6, b5, b4, b3, b2, b1, b0, e))
                                                                                                case False{}:
                                                                                                  %same : {U32.and(255, _) == _ : U32}
                                                                                                  {==}

def U32.lt256_mask8.go(d: U32, +d2: U32, same: {d == d2 : U32}, e: {U32.is_lt(d, 256) == True{} : Bool}) -> {U32.and(255, d2) == d2 : U32}:
  match d:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      U32.lt256_mask8.hi(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, d2, same, e)

def U32.lt256_mask8(+d: U32, e: {U32.is_lt(d, 256) == True{} : Bool}) -> {U32.and(255, d) == d : U32}:
  U32.lt256_mask8.go(d, d, {==}, e)
