import Base
import ../LAWS.bend as L
import ../bytes.bend as B
import ./lib.bend as P

# Proofs of the bytes laws (ticket 02).

# Roundtrips: bit layouts computed on a fully destructured U32
# ------------------------------------------------------------

def L.bytes.u8.roundtrip(v, rest, e):
  %e : {B.u8(B.write_u8(v, rest)) == Done{(_, rest)} : B.Read(U32)}
  {==}

def Bits.u16(v: U32, rest: B.Bytes()) -> {B.u16(B.write_u16(v, rest)) == Done{(U32.and(65535, v), rest)} : B.Read(U32)}:
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def L.bytes.u16.roundtrip(v, rest, e):
  %e : {B.u16(B.write_u16(v, rest)) == Done{(_, rest)} : B.Read(U32)}
  Bits.u16(v, rest)

def Bits.u24(v: U32, rest: B.Bytes()) -> {B.u24(B.write_u24(v, rest)) == Done{(U32.and(16777215, v), rest)} : B.Read(U32)}:
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def L.bytes.u24.roundtrip(v, rest, e):
  %e : {B.u24(B.write_u24(v, rest)) == Done{(_, rest)} : B.Read(U32)}
  Bits.u24(v, rest)

def L.bytes.u32.roundtrip(v, rest):
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Bits.nibbles(hi: U32, lo: U32, rest: B.Bytes()) -> {B.nibbles(B.write_nibbles(hi, lo, rest)) == Done{((U32.and(15, hi), U32.and(15, lo)), rest)} : B.Read(B.Nibbles())}:
  match hi lo:
    case U32{WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def L.bytes.nibbles.roundtrip(hi, lo, rest, eh, el):
  %eh : {B.nibbles(B.write_nibbles(hi, lo, rest)) == Done{((_, lo), rest)} : B.Read(B.Nibbles())}
  %el : {B.nibbles(B.write_nibbles(hi, lo, rest)) == Done{((U32.and(15, hi), _), rest)} : B.Read(B.Nibbles())}
  Bits.nibbles(hi, lo, rest)

# Short inputs
# ------------

def Short.u8(bs: B.Bytes(), e: {Nat.is_lt(List.length(&2, U32, bs), 1n) == True{} : Bool}) -> {B.u8(bs) == Fail{B.Short{}} : B.Read(U32)}:
  match bs:
    case Nil{}:
      {==}
    case b <> Nil{}:
      Empty.absurd({B.u8([b]) == Fail{B.Short{}} : B.Read(U32)}, P.Refute.bool(e))
    case b <> c <> t:
      Empty.absurd({B.u8(b <> c <> t) == Fail{B.Short{}} : B.Read(U32)}, P.Refute.bool(e))

def Short.u16(bs: B.Bytes(), e: {Nat.is_lt(List.length(&2, U32, bs), 2n) == True{} : Bool}) -> {B.u16(bs) == Fail{B.Short{}} : B.Read(U32)}:
  match bs:
    case Nil{}:
      {==}
    case b <> Nil{}:
      {==}
    case b <> c <> Nil{}:
      Empty.absurd({B.u16([b, c]) == Fail{B.Short{}} : B.Read(U32)}, P.Refute.bool(e))
    case b <> c <> d <> t:
      Empty.absurd({B.u16(b <> c <> d <> t) == Fail{B.Short{}} : B.Read(U32)}, P.Refute.bool(e))

def Short.u24(bs: B.Bytes(), e: {Nat.is_lt(List.length(&2, U32, bs), 3n) == True{} : Bool}) -> {B.u24(bs) == Fail{B.Short{}} : B.Read(U32)}:
  match bs:
    case Nil{}:
      {==}
    case b <> Nil{}:
      {==}
    case b <> c <> Nil{}:
      {==}
    case b <> c <> d <> Nil{}:
      Empty.absurd({B.u24([b, c, d]) == Fail{B.Short{}} : B.Read(U32)}, P.Refute.bool(e))
    case b <> c <> d <> f <> t:
      Empty.absurd({B.u24(b <> c <> d <> f <> t) == Fail{B.Short{}} : B.Read(U32)}, P.Refute.bool(e))

def Short.u32(bs: B.Bytes(), e: {Nat.is_lt(List.length(&2, U32, bs), 4n) == True{} : Bool}) -> {B.u32(bs) == Fail{B.Short{}} : B.Read(U32)}:
  match bs:
    case Nil{}:
      {==}
    case b <> Nil{}:
      {==}
    case b <> c <> Nil{}:
      {==}
    case b <> c <> d <> Nil{}:
      {==}
    case b <> c <> d <> f <> Nil{}:
      Empty.absurd({B.u32([b, c, d, f]) == Fail{B.Short{}} : B.Read(U32)}, P.Refute.bool(e))
    case b <> c <> d <> f <> g <> t:
      Empty.absurd({B.u32(b <> c <> d <> f <> g <> t) == Fail{B.Short{}} : B.Read(U32)}, P.Refute.bool(e))

def Short.nibbles(bs: B.Bytes(), e: {Nat.is_lt(List.length(&2, U32, bs), 1n) == True{} : Bool}) -> {B.nibbles(bs) == Fail{B.Short{}} : B.Read(B.Nibbles())}:
  match bs:
    case Nil{}:
      {==}
    case b <> Nil{}:
      Empty.absurd({B.nibbles([b]) == Fail{B.Short{}} : B.Read(B.Nibbles())}, P.Refute.bool(e))
    case b <> c <> t:
      Empty.absurd({B.nibbles(b <> c <> t) == Fail{B.Short{}} : B.Read(B.Nibbles())}, P.Refute.bool(e))

def Short.take(n: Nat, bs: B.Bytes(), e: {Nat.is_lt(List.length(&2, U32, bs), n) == True{} : Bool}) -> {B.take(n, bs) == Fail{B.Short{}} : B.Read(B.Bytes())}:
  match n bs:
    case 0n Nil{}:
      Empty.absurd({B.take(0n, []) == Fail{B.Short{}} : B.Read(B.Bytes())}, P.Refute.bool(e))
    case 0n b <> t:
      Empty.absurd({B.take(0n, b <> t) == Fail{B.Short{}} : B.Read(B.Bytes())}, P.Refute.bool(e))
    case 1n+p Nil{}:
      {==}
    case 1n+p b <> t:
      ih = Equal.sym(B.Read(B.Bytes()), B.take(p, t), Fail{B.Short{}}, Short.take(p, t, e))
      %ih : {B.Take.cons(b, _) == Fail{B.Short{}} : B.Read(B.Bytes())}
      {==}

def Short.tbcd(n: Nat, bs: B.Bytes(), e: {Nat.is_lt(List.length(&2, U32, bs), n) == True{} : Bool}) -> {B.tbcd_digits(bs, n) == Fail{B.Short{}} : B.Read(B.Digits())}:
  ih = Equal.sym(B.Read(B.Bytes()), B.take(n, bs), Fail{B.Short{}}, Short.take(n, bs, e))
  %ih : {B.Tbcd.after_take(_) == Fail{B.Short{}} : B.Read(B.Digits())}
  {==}

def L.bytes.short_input_fails(bs):
  (e => Short.u8(bs, e), (e => Short.u16(bs, e), (e => Short.u24(bs, e), (e => Short.u32(bs, e), (e => Short.nibbles(bs, e), (n => e => Short.take(n, bs, e), n => e => Short.tbcd(n, bs, e)))))))

# take
# ----

def Take.Spec(taken: B.Bytes(), rest: B.Bytes(), n: Nat, bs: B.Bytes()) -> Type:
  {List.length(&2, U32, taken) == n : Nat} & {List.append(&2, U32, taken, rest) == bs : B.Bytes()}

def Take.finish(+p: Nat, +b: U32, +t: B.Bytes(), +tk: B.Bytes(), +rs: B.Bytes(), la: Take.Spec(tk, rs, p, t)) -> Take.Spec(b <> tk, rs, 1n+p, b <> t):
  (l, a) = la
  (Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, U32, tk), p, l), Equal.cong(B.Bytes(), B.Bytes(), x => b <> x, List.append(&2, U32, tk, rs), t, a))

def Take.step(+p: Nat, +b: U32, +t: B.Bytes(), +taken: B.Bytes(), +rest: B.Bytes(), r: B.Read(B.Bytes()),
  ih: @tk: B.Bytes() -> @rs: B.Bytes() -> {r == Done{(tk, rs)} : B.Read(B.Bytes())} -> Take.Spec(tk, rs, p, t),
  +e: {B.Take.cons(b, r) == Done{(taken, rest)} : B.Read(B.Bytes())}) -> Take.Spec(taken, rest, 1n+p, b <> t):
  match r:
    case Fail{err}:
      Empty.absurd(Take.Spec(taken, rest, 1n+p, b <> t), P.Refute.fail_done(B.Err, B.ReadValue(B.Bytes()), err, (taken, rest), e))
    case Done{(+tk, +rs)}:
      et = Equal.cong(B.Read(B.Bytes()), B.Bytes(), x => P.Read.value(B.Bytes(), x, taken), Done{(b <> tk, rs)}, Done{(taken, rest)}, e)
      er = Equal.cong(B.Read(B.Bytes()), B.Bytes(), x => P.Read.rest(B.Bytes(), x, rest), Done{(b <> tk, rs)}, Done{(taken, rest)}, e)
      %et : Take.Spec(_, rest, 1n+p, b <> t)
      %er : Take.Spec(b <> tk, _, 1n+p, b <> t)
      Take.finish(p, b, t, tk, rs, ih(tk, rs, {==}))

def L.bytes.take.length(n, bs, taken, rest, e):
  match n bs:
    case 0n bs2:
      et = Equal.cong(B.Read(B.Bytes()), B.Bytes(), x => P.Read.value(B.Bytes(), x, taken), Done{([], bs2)}, Done{(taken, rest)}, e)
      er = Equal.cong(B.Read(B.Bytes()), B.Bytes(), x => P.Read.rest(B.Bytes(), x, rest), Done{([], bs2)}, Done{(taken, rest)}, e)
      %et : Take.Spec(_, rest, 0n, bs2)
      %er : Take.Spec([], _, 0n, bs2)
      ({==}, {==})
    case 1n+p Nil{}:
      Empty.absurd(Take.Spec(taken, rest, 1n+p, []), P.Refute.fail_done(B.Err, B.ReadValue(B.Bytes()), B.Short{}, (taken, rest), e))
    case 1n+p b <> t:
      Take.step(p, b, t, taken, rest, B.take(p, t), tk => rs => e2 => L.bytes.take.length(p, t, tk, rs, e2), e)

# TBCD
# ----

def Tbcd.Res() -> Data:
  Result<&2, &2, B.Err, B.Digits()>

def Tbcd.Spec(ds: B.Digits(), n: Nat) -> Type:
  {Nat.is_le(List.length(&2, U32, ds), Nat.double(n)) == True{} : Bool} & {B.Tbcd.all_digits(ds) == True{} : Bool}

def Tbcd.cons2_finish(+lo: U32, +hi: U32, +rest: B.Bytes(), +ds2: B.Digits(), el: {B.Tbcd.is_digit(lo) == True{} : Bool}, eh: {B.Tbcd.is_digit(hi) == True{} : Bool},
  la: Tbcd.Spec(ds2, List.length(&2, U32, rest))) -> Tbcd.Spec(lo <> hi <> ds2, 1n+List.length(&2, U32, rest)):
  (le, all) = la
  sl = Equal.sym(Bool, B.Tbcd.is_digit(lo), True{}, el)
  sh = Equal.sym(Bool, B.Tbcd.is_digit(hi), True{}, eh)
  %sl : {Nat.is_le(List.length(&2, U32, ds2), Nat.double(List.length(&2, U32, rest))) == True{} : Bool} & {Bool.and(_, Bool.and(B.Tbcd.is_digit(hi), B.Tbcd.all_digits(ds2))) == True{} : Bool}
  %sh : {Nat.is_le(List.length(&2, U32, ds2), Nat.double(List.length(&2, U32, rest))) == True{} : Bool} & {Bool.and(_, B.Tbcd.all_digits(ds2)) == True{} : Bool}
  (le, all)

def Tbcd.cons2_spec(+lo: U32, +hi: U32, +rest: B.Bytes(), +ds: B.Digits(), m: Tbcd.Res(),
  ih: @ds2: B.Digits() -> {m == Done{ds2} : Tbcd.Res()} -> Tbcd.Spec(ds2, List.length(&2, U32, rest)),
  el: {B.Tbcd.is_digit(lo) == True{} : Bool}, eh: {B.Tbcd.is_digit(hi) == True{} : Bool},
  e: {B.Tbcd.cons2(lo, hi, m) == Done{ds} : Tbcd.Res()}) -> Tbcd.Spec(ds, 1n+List.length(&2, U32, rest)):
  match m:
    case Fail{err}:
      Empty.absurd(Tbcd.Spec(ds, 1n+List.length(&2, U32, rest)), P.Refute.fail_done(B.Err, B.Digits(), err, ds, e))
    case Done{+ds2}:
      et = Equal.cong(Tbcd.Res(), B.Digits(), x => P.Res.value(B.Err, B.Digits(), x, ds), Done{lo <> hi <> ds2}, Done{ds}, e)
      %et : Tbcd.Spec(_, 1n+List.length(&2, U32, rest))
      Tbcd.cons2_finish(lo, hi, rest, ds2, el, eh, ih(ds2, {==}))

def Tbcd.filler_spec(+lo: U32, +ds: B.Digits(), rest: B.Bytes(), el: {B.Tbcd.is_digit(lo) == True{} : Bool},
  e: {B.Tbcd.filler(lo, rest) == Done{ds} : Tbcd.Res()}) -> Tbcd.Spec(ds, 1n+List.length(&2, U32, rest)):
  match rest:
    case Nil{}:
      et = Equal.cong(Tbcd.Res(), B.Digits(), x => P.Res.value(B.Err, B.Digits(), x, ds), Done{[lo]}, Done{ds}, e)
      %et : Tbcd.Spec(_, 1n)
      sl = Equal.sym(Bool, B.Tbcd.is_digit(lo), True{}, el)
      %sl : {Nat.is_le(1n, 2n) == True{} : Bool} & {Bool.and(_, True{}) == True{} : Bool}
      ({==}, {==})
    case x <> t:
      Empty.absurd(Tbcd.Spec(ds, 1n+List.length(&2, U32, x <> t)), P.Refute.fail_done(B.Err, B.Digits(), B.Invalid{15}, ds, e))

def Tbcd.high_spec(+lo: U32, +hi: U32, +rest: B.Bytes(), +ds: B.Digits(), more: Unit -> Tbcd.Res(),
  ih: @ds2: B.Digits() -> {more(Unit{}) == Done{ds2} : Tbcd.Res()} -> Tbcd.Spec(ds2, List.length(&2, U32, rest)),
  hi_digit: Bool, hi_filler: Bool, el: {B.Tbcd.is_digit(lo) == True{} : Bool}, eh: {B.Tbcd.is_digit(hi) == hi_digit : Bool},
  e: {B.Tbcd.high(lo, hi, rest, more, hi_digit, hi_filler) == Done{ds} : Tbcd.Res()}) -> Tbcd.Spec(ds, 1n+List.length(&2, U32, rest)):
  match hi_digit:
    case True{}:
      Tbcd.cons2_spec(lo, hi, rest, ds, more(Unit{}), ih, el, eh, e)
    case False{}:
      match hi_filler:
        case True{}:
          Tbcd.filler_spec(lo, ds, rest, el, e)
        case False{}:
          Empty.absurd(Tbcd.Spec(ds, 1n+List.length(&2, U32, rest)), P.Refute.fail_done(B.Err, B.Digits(), B.Invalid{hi}, ds, e))

def Tbcd.low_spec(+lo: U32, +hi: U32, +rest: B.Bytes(), +ds: B.Digits(), more: Unit -> Tbcd.Res(),
  ih: @ds2: B.Digits() -> {more(Unit{}) == Done{ds2} : Tbcd.Res()} -> Tbcd.Spec(ds2, List.length(&2, U32, rest)),
  lo_digit: Bool, el: {B.Tbcd.is_digit(lo) == lo_digit : Bool},
  e: {B.Tbcd.low(lo, hi, rest, more, lo_digit) == Done{ds} : Tbcd.Res()}) -> Tbcd.Spec(ds, 1n+List.length(&2, U32, rest)):
  match lo_digit:
    case True{}:
      Tbcd.high_spec(lo, hi, rest, ds, more, ih, B.Tbcd.is_digit(hi), U32.is_eq(hi, 15), el, {==}, e)
    case False{}:
      Empty.absurd(Tbcd.Spec(ds, 1n+List.length(&2, U32, rest)), P.Refute.fail_done(B.Err, B.Digits(), B.Invalid{lo}, ds, e))

def Tbcd.decode_len(bs: B.Bytes(), +ds: B.Digits(), e: {B.Tbcd.decode(bs) == Done{ds} : Tbcd.Res()}) -> Tbcd.Spec(ds, List.length(&2, U32, bs)):
  match bs:
    case Nil{}:
      et = Equal.cong(Tbcd.Res(), B.Digits(), x => P.Res.value(B.Err, B.Digits(), x, ds), Done{[]}, Done{ds}, e)
      %et : Tbcd.Spec(_, 0n)
      ({==}, {==})
    case +b <> +rest:
      Tbcd.low_spec(U32.and(15, b), U32.and(15, U32.shrn(b, 4n)), rest, ds, u => B.Tbcd.decode(rest), ds2 => e2 => Tbcd.decode_len(rest, ds2, e2), B.Tbcd.is_digit(U32.and(15, b)), {==}, e)

def Tbcd.main2(+k: Nat, +digits: B.Digits(), +rest: B.Bytes(), +bytes: B.Bytes(), +rs: B.Bytes(), d: Tbcd.Res(),
  dl: @ds: B.Digits() -> {d == Done{ds} : Tbcd.Res()} -> Tbcd.Spec(ds, List.length(&2, U32, bytes)),
  lenk: {List.length(&2, U32, bytes) == k : Nat},
  e: {B.Tbcd.with_rest(d, rs) == Done{(digits, rest)} : B.Read(B.Digits())}) -> Tbcd.Spec(digits, k):
  match d:
    case Fail{err}:
      Empty.absurd(Tbcd.Spec(digits, k), P.Refute.fail_done(B.Err, B.ReadValue(B.Digits()), err, (digits, rest), e))
    case Done{+ds}:
      et = Equal.cong(B.Read(B.Digits()), B.Digits(), x => P.Read.value(B.Digits(), x, digits), Done{(ds, rs)}, Done{(digits, rest)}, e)
      %et : Tbcd.Spec(_, k)
      %lenk : Tbcd.Spec(ds, _)
      dl(ds, {==})

def Tbcd.main1(+k: Nat, +digits: B.Digits(), +rest: B.Bytes(), +bs: B.Bytes(), +bytes: B.Bytes(), +rs: B.Bytes(), la: Take.Spec(bytes, rs, k, bs),
  e: {B.Tbcd.with_rest(B.Tbcd.decode(bytes), rs) == Done{(digits, rest)} : B.Read(B.Digits())}) -> Tbcd.Spec(digits, k):
  (lenk, app) = la
  Tbcd.main2(k, digits, rest, bytes, rs, B.Tbcd.decode(bytes), ds => e2 => Tbcd.decode_len(bytes, ds, e2), lenk, e)

def Tbcd.main(+k: Nat, +digits: B.Digits(), +rest: B.Bytes(), +bs: B.Bytes(), r: B.Read(B.Bytes()),
  tl: @tk: B.Bytes() -> @rs: B.Bytes() -> {r == Done{(tk, rs)} : B.Read(B.Bytes())} -> Take.Spec(tk, rs, k, bs),
  e: {B.Tbcd.after_take(r) == Done{(digits, rest)} : B.Read(B.Digits())}) -> Tbcd.Spec(digits, k):
  match r:
    case Fail{err}:
      Empty.absurd(Tbcd.Spec(digits, k), P.Refute.fail_done(B.Err, B.ReadValue(B.Digits()), err, (digits, rest), e))
    case Done{(+bytes, +rs)}:
      Tbcd.main1(k, digits, rest, bs, bytes, rs, tl(bytes, rs, {==}), e)

def Tbcd.encode_len(ds: B.Digits(), out: B.Bytes()) -> {List.length(&2, U32, B.write_tbcd(ds, out)) == Nat.add(B.Tbcd.byte_count(List.length(&2, U32, ds)), List.length(&2, U32, out)) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> Nil{}:
      {==}
    case d1 <> d2 <> more:
      Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, U32, B.write_tbcd(more, out)), Nat.add(B.Tbcd.byte_count(List.length(&2, U32, more)), List.length(&2, U32, out)), Tbcd.encode_len(more, out))

def Tbcd.assemble(+digits: B.Digits(), +k: Nat, la: Tbcd.Spec(digits, k)) -> {Nat.is_le(List.length(&2, U32, digits), Nat.double(k)) == True{} : Bool} & ({B.Tbcd.all_digits(digits) == True{} : Bool} & (@ds: B.Digits() -> @out: B.Bytes() -> {List.length(&2, U32, B.write_tbcd(ds, out)) == Nat.add(B.Tbcd.byte_count(List.length(&2, U32, ds)), List.length(&2, U32, out)) : Nat})):
  (le, all) = la
  (le, (all, ds => out => Tbcd.encode_len(ds, out)))

def L.bytes.tbcd.length(bs, k, digits, rest, e):
  Tbcd.assemble(digits, k, Tbcd.main(k, digits, rest, bs, B.take(k, bs), tk => rs => e2 => L.bytes.take.length(k, bs, tk, rs, e2), e))
