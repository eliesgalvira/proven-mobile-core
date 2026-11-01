import Base
import ../bytes.bend as B

# X25519 (RFC 7748 §5) over GF(2^255 - 19). A field element is sixteen
# little-endian limbs of 16 bits (a value below 2^256, not always reduced), so
# every intermediate fits a U32: a limb product is below 2^32 and a column of
# the schoolbook product below 2^21. Carries are propagated after every
# operation; 2^256 = 38 (mod p) folds the upper limbs back.

def Fe.zero() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def Fe.one() -> List<&2, U32>:
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

# 4p, each limb with a 2^16 of headroom so that 4p - b never underflows.
def Fe.four_p() -> List<&2, U32>:
  [130996, 131070, 131070, 131070, 131070, 131070, 131070, 131070, 131070, 131070, 131070, 131070, 131070, 131070, 131070, 131070]

# Propagate carries into 16-bit limbs; the final carry becomes a last limb.
def Fe.carry(xs: List<&2, U32>, c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [c]
    case x <> rest:
      +s = U32.add(x, c)
      U32.and(65535, s) <> Fe.carry(rest, U32.shrn(s, 16n))

def Fe.add_cols(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case Nil{} ys2:
      ys2
    case x <> xt Nil{}:
      x <> xt
    case x <> xt y <> yt:
      U32.add(x, y) <> Fe.add_cols(xt, yt)

def Fe.sub_cols(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case Nil{} ys2:
      Nil{}
    case x <> xt Nil{}:
      x <> xt
    case x <> xt y <> yt:
      U32.sub(x, y) <> Fe.sub_cols(xt, yt)

def Fe.scale(xs: List<&2, U32>, +k: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      U32.mul(x, k) <> Fe.scale(rest, k)

# Limbs at index 16 and above weigh 2^256 = 38 (mod p).
def Fe.fold(+xs: List<&2, U32>) -> List<&2, U32>:
  Fe.add_cols(List.take(&2, U32, xs, 16n), Fe.scale(List.drop(&2, U32, xs, 16n), 38))

# Sixteen 16-bit limbs from any limb list whose entries are below 2^22.
def Fe.normalize(xs: List<&2, U32>) -> List<&2, U32>:
  List.take(&2, U32, Fe.carry(Fe.fold(Fe.carry(Fe.fold(Fe.carry(Fe.fold(Fe.carry(xs, 0)), 0)), 0)), 0), 16n)

def Fe.add(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  Fe.normalize(Fe.add_cols(a, b))

def Fe.sub(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  Fe.normalize(Fe.add_cols(a, Fe.sub_cols(Fe.four_p(), b)))

# ai times b, as 17 columns below 2^17: the low half of each product plus the
# high half of the previous one.
def Fe.row(+ai: U32, b: List<&2, U32>, hi: U32) -> List<&2, U32>:
  match b:
    case Nil{}:
      [hi]
    case bj <> rest:
      +p = U32.mul(ai, bj)
      U32.add(U32.and(65535, p), hi) <> Fe.row(ai, rest, U32.shrn(p, 16n))

def Fe.rows(a: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      Nil{}
    case ai <> rest:
      Fe.add_cols(Fe.row(ai, b, 0), 0 <> Fe.rows(rest, b))

def Fe.mul(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  Fe.normalize(Fe.rows(a, b))

def Fe.sqr(+a: List<&2, U32>) -> List<&2, U32>:
  Fe.mul(a, a)

def Fe.inv.step(z: List<&2, U32>, a: List<&2, U32>, skip: Bool) -> List<&2, U32>:
  match skip:
    case True{}:
      z
    case False{}:
      Fe.mul(z, a)

# a^(p - 2): square 255 times, multiplying by a except at bits 2 and 4.
def Fe.inv.go(+i: Nat, +z: List<&2, U32>, +a: List<&2, U32>) -> List<&2, U32>:
  match i:
    case 0n:
      Fe.mul(Fe.sqr(z), a)
    case 1n+p:
      Fe.inv.go(p, Fe.inv.step(Fe.sqr(z), a, Bool.or(Nat.is_eq(1n+p, 2n), Nat.is_eq(1n+p, 4n))), a)

def Fe.inv(+a: List<&2, U32>) -> List<&2, U32>:
  Fe.inv.go(253n, a, a)

# a - p when a >= p (a + 2^255 + 19 carries out of 16 limbs), else a.
def Fe.pick(a: List<&2, U32>, t: List<&2, U32>, ge: Bool) -> List<&2, U32>:
  match ge:
    case True{}:
      List.take(&2, U32, t, 16n)
    case False{}:
      a

def Fe.sub_p(+a: List<&2, U32>) -> List<&2, U32>:
  +t = Fe.carry(Fe.add_cols(a, [19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32768]), 0)
  Fe.pick(a, t, U32.is_eq(Maybe.default(&2, U32, List.get(&2, U32, t, 16n), 0), 1))

def Fe.freeze(a: List<&2, U32>) -> List<&2, U32>:
  Fe.sub_p(Fe.sub_p(a))

def Fe.to_bytes(fe: List<&2, U32>) -> List<&2, U32>:
  match fe:
    case +l0 <> +l1 <> +l2 <> +l3 <> +l4 <> +l5 <> +l6 <> +l7 <> +l8 <> +l9 <> +l10 <> +l11 <> +l12 <> +l13 <> +l14 <> +l15 <> rest:
      [U32.and(255, l0), U32.shrn(l0, 8n), U32.and(255, l1), U32.shrn(l1, 8n), U32.and(255, l2), U32.shrn(l2, 8n), U32.and(255, l3), U32.shrn(l3, 8n), U32.and(255, l4), U32.shrn(l4, 8n), U32.and(255, l5), U32.shrn(l5, 8n), U32.and(255, l6), U32.shrn(l6, 8n), U32.and(255, l7), U32.shrn(l7, 8n), U32.and(255, l8), U32.shrn(l8, 8n), U32.and(255, l9), U32.shrn(l9, 8n), U32.and(255, l10), U32.shrn(l10, 8n), U32.and(255, l11), U32.shrn(l11, 8n), U32.and(255, l12), U32.shrn(l12, 8n), U32.and(255, l13), U32.shrn(l13, 8n), U32.and(255, l14), U32.shrn(l14, 8n), U32.and(255, l15), U32.shrn(l15, 8n)]
    case _:
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

# The u-coordinate: 32 little-endian bytes, the top bit masked.
def Fe.from_bytes(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> rest:
      [B.cat8(b0, b1), B.cat8(b2, b3), B.cat8(b4, b5), B.cat8(b6, b7), B.cat8(b8, b9), B.cat8(b10, b11), B.cat8(b12, b13), B.cat8(b14, b15), B.cat8(b16, b17), B.cat8(b18, b19), B.cat8(b20, b21), B.cat8(b22, b23), B.cat8(b24, b25), B.cat8(b26, b27), B.cat8(b28, b29), B.cat8(b30, U32.and(127, b31))]
    case _:
      Fe.zero()

# Constant-time conditional swap: a xor (mask and (a xor b)).
def Fe.cswap(a: List<&2, U32>, b: List<&2, U32>, +mask: U32) -> List<&2, U32>:
  match a b:
    case +x <> xt y <> yt:
      U32.xor(x, U32.and(mask, U32.xor(x, y))) <> Fe.cswap(xt, yt, mask)
    case _ _:
      Nil{}

def Fe.a24() -> List<&2, U32>:
  [56129, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

type X25519.State is Data:
  St{x2: List<&2, U32>, z2: List<&2, U32>, x3: List<&2, U32>, z3: List<&2, U32>, swap: U32}

def X25519.bit(k: List<&2, U32>, +t: Nat) -> U32:
  U32.and(1, U32.shrn(Maybe.default(&2, U32, List.get(&2, U32, k, Nat.div(t, 8n)), 0), Nat.mod(t, 8n)))

# One ladder step for scalar bit kt (RFC 7748 §5).
def X25519.step(st: X25519.State, +x1: List<&2, U32>, +kt: U32) -> X25519.State:
  match st:
    case St{+x2, +z2, +x3, +z3, swap}:
      +mask = U32.sub(0, U32.xor(swap, kt))
      +x2s = Fe.cswap(x2, x3, mask)
      +x3s = Fe.cswap(x3, x2, mask)
      +z2s = Fe.cswap(z2, z3, mask)
      +z3s = Fe.cswap(z3, z2, mask)
      +a = Fe.add(x2s, z2s)
      +aa = Fe.sqr(a)
      +b = Fe.sub(x2s, z2s)
      +bb = Fe.sqr(b)
      +e = Fe.sub(aa, bb)
      +c = Fe.add(x3s, z3s)
      +d = Fe.sub(x3s, z3s)
      +da = Fe.mul(d, a)
      +cb = Fe.mul(c, b)
      St{Fe.mul(aa, bb), Fe.mul(e, Fe.add(aa, Fe.mul(Fe.a24(), e))), Fe.sqr(Fe.add(da, cb)), Fe.mul(x1, Fe.sqr(Fe.sub(da, cb))), kt}

def X25519.ladder(+t: Nat, st: X25519.State, +x1: List<&2, U32>, +k: List<&2, U32>) -> X25519.State:
  match t:
    case 0n:
      X25519.step(st, x1, X25519.bit(k, 0n))
    case 1n+p:
      X25519.ladder(p, X25519.step(st, x1, X25519.bit(k, 1n+p)), x1, k)

def X25519.finish(st: X25519.State) -> List<&2, U32>:
  match st:
    case St{+x2, +z2, +x3, +z3, +swap}:
      +mask = U32.sub(0, swap)
      Fe.to_bytes(Fe.freeze(Fe.mul(Fe.cswap(x2, x3, mask), Fe.inv(Fe.cswap(z2, z3, mask)))))

# Clamp the scalar: clear bits 0-2 and 255, set bit 254.
def X25519.clamp(k: List<&2, U32>) -> List<&2, U32>:
  match k:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> rest:
      [U32.and(248, b0), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, U32.or(64, U32.and(127, b31))]
    case _:
      Nil{}

def x25519(scalar: List<&2, U32>, u: List<&2, U32>) -> List<&2, U32>:
  +x1 = Fe.from_bytes(u)
  X25519.finish(X25519.ladder(254n, St{Fe.one(), Fe.zero(), x1, Fe.one(), 0}, x1, X25519.clamp(scalar)))

def x25519.base() -> List<&2, U32>:
  [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
