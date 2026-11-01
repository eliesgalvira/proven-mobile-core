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
