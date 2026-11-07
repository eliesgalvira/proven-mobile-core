import Base
import ../bytes.bend as B

# SHA-256 (FIPS 180-4) over byte lists.

type Sha256.State is Data:
  St{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

def Sha256.h0() -> Sha256.State:
  St{1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225}

def Sha256.k() -> List<&2, U32>:
  [1116352408, 1899447441, 3049323471, 3921009573, 961987163, 1508970993, 2453635748, 2870763221,
   3624381080, 310598401, 607225278, 1426881987, 1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895,
   666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344,
   430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298]

def Sha256.rotr(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shrn(x, n), U32.shln(x, Nat.sub(32n, n)))

def Sha256.ch(+e: U32, f: U32, g: U32) -> U32:
  U32.xor(U32.and(e, f), U32.and(U32.not(e), g))

def Sha256.maj(+a: U32, +b: U32, +c: U32) -> U32:
  U32.xor(U32.xor(U32.and(a, b), U32.and(a, c)), U32.and(b, c))

def Sha256.big0(+a: U32) -> U32:
  U32.xor(U32.xor(Sha256.rotr(a, 2n), Sha256.rotr(a, 13n)), Sha256.rotr(a, 22n))

def Sha256.big1(+e: U32) -> U32:
  U32.xor(U32.xor(Sha256.rotr(e, 6n), Sha256.rotr(e, 11n)), Sha256.rotr(e, 25n))

def Sha256.small0(+x: U32) -> U32:
  U32.xor(U32.xor(Sha256.rotr(x, 7n), Sha256.rotr(x, 18n)), U32.shrn(x, 3n))

def Sha256.small1(+x: U32) -> U32:
  U32.xor(U32.xor(Sha256.rotr(x, 17n), Sha256.rotr(x, 19n)), U32.shrn(x, 10n))

def Sha256.at(ws: List<&2, U32>, i: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, ws, i), 0)

# The message schedule, newest word first; adds n words.
def Sha256.schedule(n: Nat, +ws: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      ws
    case 1n+p:
      w = U32.add(U32.add(Sha256.small1(Sha256.at(ws, 1n)), Sha256.at(ws, 6n)), U32.add(Sha256.small0(Sha256.at(ws, 14n)), Sha256.at(ws, 15n)))
      Sha256.schedule(p, w <> ws)

def Sha256.round(st: Sha256.State, w: U32, k: U32) -> Sha256.State:
  match st:
    case St{+a, +b, +c, +d, +e, +f, +g, h}:
      +t1 = U32.add(U32.add(U32.add(h, Sha256.big1(e)), U32.add(Sha256.ch(e, f, g), k)), w)
      t2 = U32.add(Sha256.big0(a), Sha256.maj(a, b, c))
      St{U32.add(t1, t2), a, b, c, U32.add(d, t1), e, f, g}

def Sha256.rounds(ws: List<&2, U32>, ks: List<&2, U32>, st: Sha256.State) -> Sha256.State:
  match ws ks:
    case w <> wt k <> kt:
      Sha256.rounds(wt, kt, Sha256.round(st, w, k))
    case _ _:
      st

def Sha256.add_state(x: Sha256.State, y: Sha256.State) -> Sha256.State:
  match x y:
    case St{a, b, c, d, e, f, g, h} St{a2, b2, c2, d2, e2, f2, g2, h2}:
      St{U32.add(a, a2), U32.add(b, b2), U32.add(c, c2), U32.add(d, d2), U32.add(e, e2), U32.add(f, f2), U32.add(g, g2), U32.add(h, h2)}

def Sha256.compress(+st: Sha256.State, w0: List<&2, U32>) -> Sha256.State:
  ws = List.reverse(&2, U32, Sha256.schedule(48n, List.reverse(&2, U32, w0)))
  Sha256.add_state(st, Sha256.rounds(ws, Sha256.k(), st))

# One 64-byte block at a time; anything shorter than a block is ignored, and
# padding guarantees there is none.
def Sha256.blocks(bs: List<&2, U32>, st: Sha256.State) -> Sha256.State:
  match bs:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> x16 <> x17 <> x18 <> x19 <> x20 <> x21 <> x22 <> x23 <> x24 <> x25 <> x26 <> x27 <> x28 <> x29 <> x30 <> x31 <> x32 <> x33 <> x34 <> x35 <> x36 <> x37 <> x38 <> x39 <> x40 <> x41 <> x42 <> x43 <> x44 <> x45 <> x46 <> x47 <> x48 <> x49 <> x50 <> x51 <> x52 <> x53 <> x54 <> x55 <> x56 <> x57 <> x58 <> x59 <> x60 <> x61 <> x62 <> x63 <> rest:
      Sha256.blocks(rest, Sha256.compress(st, [B.cat8(x3, B.cat8(x2, B.cat8(x1, x0))), B.cat8(x7, B.cat8(x6, B.cat8(x5, x4))), B.cat8(x11, B.cat8(x10, B.cat8(x9, x8))), B.cat8(x15, B.cat8(x14, B.cat8(x13, x12))), B.cat8(x19, B.cat8(x18, B.cat8(x17, x16))), B.cat8(x23, B.cat8(x22, B.cat8(x21, x20))), B.cat8(x27, B.cat8(x26, B.cat8(x25, x24))), B.cat8(x31, B.cat8(x30, B.cat8(x29, x28))), B.cat8(x35, B.cat8(x34, B.cat8(x33, x32))), B.cat8(x39, B.cat8(x38, B.cat8(x37, x36))), B.cat8(x43, B.cat8(x42, B.cat8(x41, x40))), B.cat8(x47, B.cat8(x46, B.cat8(x45, x44))), B.cat8(x51, B.cat8(x50, B.cat8(x49, x48))), B.cat8(x55, B.cat8(x54, B.cat8(x53, x52))), B.cat8(x59, B.cat8(x58, B.cat8(x57, x56))), B.cat8(x63, B.cat8(x62, B.cat8(x61, x60)))]))
    case _:
      st

def Sha256.count(bs: List<&2, U32>, acc: U32) -> U32:
  match bs:
    case Nil{}:
      acc
    case b <> rest:
      Sha256.count(rest, U32.add(acc, 1))

# Zero bytes so that the padded length is 56 mod 64.
def Sha256.zeros(+len_mod_64: Nat) -> List<&2, U32>:
  List.replicate(U32, Nat.mod(Nat.sub(119n, len_mod_64), 64n), 0)

def Sha256.pad(+msg: List<&2, U32>) -> List<&2, U32>:
  +len = Sha256.count(msg, 0)
  tail = B.write_u32(U32.shrn(len, 29n), B.write_u32(U32.shln(len, 3n), []))
  List.append(&2, U32, msg, 128 <> List.append(&2, U32, Sha256.zeros(Nat.mod(U32.to_nat(len), 64n)), tail))

def Sha256.serialize(st: Sha256.State) -> List<&2, U32>:
  match st:
    case St{a, b, c, d, e, f, g, h}:
      B.write_u32(a, B.write_u32(b, B.write_u32(c, B.write_u32(d, B.write_u32(e, B.write_u32(f, B.write_u32(g, B.write_u32(h, []))))))))

def Sha256.digest_state(msg: List<&2, U32>) -> Sha256.State:
  Sha256.blocks(Sha256.pad(msg), Sha256.h0())

def sha256(msg: List<&2, U32>) -> List<&2, U32>:
  Sha256.serialize(Sha256.digest_state(msg))
