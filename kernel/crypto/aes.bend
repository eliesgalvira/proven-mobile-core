import Base
import ../bytes.bend as B

# AES-128 block encryption (FIPS 197), on a 16-byte block record. State byte
# s[4c + r] is row r of column c, as the bytes arrive on the wire.

type Aes.Block is Data:
  Blk{s0: U32, s1: U32, s2: U32, s3: U32, s4: U32, s5: U32, s6: U32, s7: U32, s8: U32, s9: U32, s10: U32, s11: U32, s12: U32, s13: U32, s14: U32, s15: U32}

def Aes.zero() -> Aes.Block:
  Blk{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}

# The first 16 bytes; anything else is the zero block.
def Aes.block_of(bs: List<&2, U32>) -> Aes.Block:
  match bs:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> rest:
      Blk{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}
    case _:
      Aes.zero()

def Aes.to_bytes(b: Aes.Block) -> List<&2, U32>:
  match b:
    case Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15]

def Aes.sbox() -> List<&2, U32>:
  [99, 124, 119, 123, 242, 107, 111, 197, 48, 1, 103, 43, 254, 215, 171, 118,
   202, 130, 201, 125, 250, 89, 71, 240, 173, 212, 162, 175, 156, 164, 114, 192,
   183, 253, 147, 38, 54, 63, 247, 204, 52, 165, 229, 241, 113, 216, 49, 21,
   4, 199, 35, 195, 24, 150, 5, 154, 7, 18, 128, 226, 235, 39, 178, 117,
   9, 131, 44, 26, 27, 110, 90, 160, 82, 59, 214, 179, 41, 227, 47, 132,
   83, 209, 0, 237, 32, 252, 177, 91, 106, 203, 190, 57, 74, 76, 88, 207,
   208, 239, 170, 251, 67, 77, 51, 133, 69, 249, 2, 127, 80, 60, 159, 168,
   81, 163, 64, 143, 146, 157, 56, 245, 188, 182, 218, 33, 16, 255, 243, 210,
   205, 12, 19, 236, 95, 151, 68, 23, 196, 167, 126, 61, 100, 93, 25, 115,
   96, 129, 79, 220, 34, 42, 144, 136, 70, 238, 184, 20, 222, 94, 11, 219,
   224, 50, 58, 10, 73, 6, 36, 92, 194, 211, 172, 98, 145, 149, 228, 121,
   231, 200, 55, 109, 141, 213, 78, 169, 108, 86, 244, 234, 101, 122, 174, 8,
   186, 120, 37, 46, 28, 166, 180, 198, 232, 221, 116, 31, 75, 189, 139, 138,
   112, 62, 181, 102, 72, 3, 246, 14, 97, 53, 87, 185, 134, 193, 29, 158,
   225, 248, 152, 17, 105, 217, 142, 148, 155, 30, 135, 233, 206, 85, 40, 223,
   140, 161, 137, 13, 191, 230, 66, 104, 65, 153, 45, 15, 176, 84, 187, 22]

# The S-box as a tree a byte indexes by its bits, high bit first; one is
# built per key schedule and per block.
type Aes.Sbox is Data:
  SLeaf{v: U32}
  SNode{lo: Aes.Sbox, hi: Aes.Sbox}

def Aes.Sbox.of(n: Nat, +xs: List<&2, U32>) -> Aes.Sbox:
  match n:
    case 0n:
      SLeaf{Maybe.default(&2, U32, List.get(&2, U32, xs, 0n), 0)}
    case 1n+(+p):
      +half = U32.to_nat(U32.shln(1, p))
      SNode{Aes.Sbox.of(p, List.take(&2, U32, xs, half)), Aes.Sbox.of(p, List.drop(&2, U32, xs, half))}

def Aes.Sbox.high(+b: U32, +bit: U32) -> Bool:
  Bool.not(U32.is_eq(U32.and(b, bit), 0))

def Aes.Sbox.at(t: Aes.Sbox, +b: U32, +bit: U32, high: Bool) -> U32:
  match t:
    case SLeaf{v}:
      v
    case SNode{lo, hi}:
      match high:
        case True{}:
          Aes.Sbox.at(hi, b, U32.shrn(bit, 1n), Aes.Sbox.high(b, U32.shrn(bit, 1n)))
        case False{}:
          Aes.Sbox.at(lo, b, U32.shrn(bit, 1n), Aes.Sbox.high(b, U32.shrn(bit, 1n)))

def Aes.table() -> Aes.Sbox:
  Aes.Sbox.of(8n, Aes.sbox())

def Aes.sub(+t: Aes.Sbox, +b: U32) -> U32:
  Aes.Sbox.at(t, b, 128, Aes.Sbox.high(b, 128))

# Multiplication by x in GF(2^8).
def Aes.xtime(+a: U32) -> U32:
  U32.xor(U32.and(255, U32.shln(a, 1n)), U32.mul(27, U32.shrn(a, 7n)))

def Aes.xor(x: Aes.Block, y: Aes.Block) -> Aes.Block:
  match x y:
    case Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15} Blk{k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15}:
      Blk{U32.xor(s0, k0), U32.xor(s1, k1), U32.xor(s2, k2), U32.xor(s3, k3), U32.xor(s4, k4), U32.xor(s5, k5), U32.xor(s6, k6), U32.xor(s7, k7), U32.xor(s8, k8), U32.xor(s9, k9), U32.xor(s10, k10), U32.xor(s11, k11), U32.xor(s12, k12), U32.xor(s13, k13), U32.xor(s14, k14), U32.xor(s15, k15)}

def Aes.sub_bytes(+t: Aes.Sbox, b: Aes.Block) -> Aes.Block:
  match b:
    case Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      Blk{Aes.sub(t, s0), Aes.sub(t, s1), Aes.sub(t, s2), Aes.sub(t, s3), Aes.sub(t, s4), Aes.sub(t, s5), Aes.sub(t, s6), Aes.sub(t, s7), Aes.sub(t, s8), Aes.sub(t, s9), Aes.sub(t, s10), Aes.sub(t, s11), Aes.sub(t, s12), Aes.sub(t, s13), Aes.sub(t, s14), Aes.sub(t, s15)}

def Aes.shift_rows(b: Aes.Block) -> Aes.Block:
  match b:
    case Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      Blk{s0, s5, s10, s15, s4, s9, s14, s3, s8, s13, s2, s7, s12, s1, s6, s11}

def Aes.mix_columns(b: Aes.Block) -> Aes.Block:
  match b:
    case Blk{+s0, +s1, +s2, +s3, +s4, +s5, +s6, +s7, +s8, +s9, +s10, +s11, +s12, +s13, +s14, +s15}:
      Blk{U32.xor(U32.xor(Aes.xtime(s0), U32.xor(Aes.xtime(s1), s1)), U32.xor(s2, s3)), U32.xor(U32.xor(s0, Aes.xtime(s1)), U32.xor(U32.xor(Aes.xtime(s2), s2), s3)), U32.xor(U32.xor(s0, s1), U32.xor(Aes.xtime(s2), U32.xor(Aes.xtime(s3), s3))), U32.xor(U32.xor(U32.xor(Aes.xtime(s0), s0), s1), U32.xor(s2, Aes.xtime(s3))), U32.xor(U32.xor(Aes.xtime(s4), U32.xor(Aes.xtime(s5), s5)), U32.xor(s6, s7)), U32.xor(U32.xor(s4, Aes.xtime(s5)), U32.xor(U32.xor(Aes.xtime(s6), s6), s7)), U32.xor(U32.xor(s4, s5), U32.xor(Aes.xtime(s6), U32.xor(Aes.xtime(s7), s7))), U32.xor(U32.xor(U32.xor(Aes.xtime(s4), s4), s5), U32.xor(s6, Aes.xtime(s7))), U32.xor(U32.xor(Aes.xtime(s8), U32.xor(Aes.xtime(s9), s9)), U32.xor(s10, s11)), U32.xor(U32.xor(s8, Aes.xtime(s9)), U32.xor(U32.xor(Aes.xtime(s10), s10), s11)), U32.xor(U32.xor(s8, s9), U32.xor(Aes.xtime(s10), U32.xor(Aes.xtime(s11), s11))), U32.xor(U32.xor(U32.xor(Aes.xtime(s8), s8), s9), U32.xor(s10, Aes.xtime(s11))), U32.xor(U32.xor(Aes.xtime(s12), U32.xor(Aes.xtime(s13), s13)), U32.xor(s14, s15)), U32.xor(U32.xor(s12, Aes.xtime(s13)), U32.xor(U32.xor(Aes.xtime(s14), s14), s15)), U32.xor(U32.xor(s12, s13), U32.xor(Aes.xtime(s14), U32.xor(Aes.xtime(s15), s15))), U32.xor(U32.xor(U32.xor(Aes.xtime(s12), s12), s13), U32.xor(s14, Aes.xtime(s15)))}

# The next round key (FIPS 197 §5.2): column 0 takes the substituted, rotated
# last column and the round constant; each later column takes the one before.
def Aes.next_key(+t: Aes.Sbox, k: Aes.Block, rcon: U32) -> Aes.Block:
  match k:
    case Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, +s12, +s13, +s14, +s15}:
      +t0 = U32.xor(U32.xor(s0, Aes.sub(t, s13)), rcon)
      +t1 = U32.xor(s1, Aes.sub(t, s14))
      +t2 = U32.xor(s2, Aes.sub(t, s15))
      +t3 = U32.xor(s3, Aes.sub(t, s12))
      +t4 = U32.xor(s4, t0)
      +t5 = U32.xor(s5, t1)
      +t6 = U32.xor(s6, t2)
      +t7 = U32.xor(s7, t3)
      +t8 = U32.xor(s8, t4)
      +t9 = U32.xor(s9, t5)
      +t10 = U32.xor(s10, t6)
      +t11 = U32.xor(s11, t7)
      Blk{t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, U32.xor(s12, t8), U32.xor(s13, t9), U32.xor(s14, t10), U32.xor(s15, t11)}

def Aes.expand(+t: Aes.Sbox, n: Nat, +k: Aes.Block, +rcon: U32) -> List<&2, Aes.Block>:
  match n:
    case 0n:
      [k]
    case 1n+p:
      k <> Aes.expand(t, p, Aes.next_key(t, k, rcon), Aes.xtime(rcon))

# The eleven round keys of AES-128.
def Aes.round_keys(key: List<&2, U32>) -> List<&2, Aes.Block>:
  Aes.expand(Aes.table(), 10n, Aes.block_of(key), 1)

def Aes.rounds(+t: Aes.Sbox, rks: List<&2, Aes.Block>, st: Aes.Block) -> Aes.Block:
  match rks:
    case Nil{}:
      st
    case k <> Nil{}:
      Aes.xor(Aes.shift_rows(Aes.sub_bytes(t, st)), k)
    case k <> more:
      Aes.rounds(t, more, Aes.xor(Aes.mix_columns(Aes.shift_rows(Aes.sub_bytes(t, st))), k))

def Aes.encrypt(rks: List<&2, Aes.Block>, blk: Aes.Block) -> Aes.Block:
  match rks:
    case Nil{}:
      blk
    case k0 <> rest:
      Aes.rounds(Aes.table(), rest, Aes.xor(blk, k0))

def aes128(key: List<&2, U32>, block: List<&2, U32>) -> List<&2, U32>:
  Aes.to_bytes(Aes.encrypt(Aes.round_keys(key), Aes.block_of(block)))
