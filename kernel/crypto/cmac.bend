import Base
import ../bytes.bend as B
import ./aes.bend as A

# AES-CMAC (RFC 4493) on byte lists.

def Cmac.shl1(b: A.Aes.Block) -> A.Aes.Block:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      +w0 = B.cat8(s3, B.cat8(s2, B.cat8(s1, s0)))
      +w1 = B.cat8(s7, B.cat8(s6, B.cat8(s5, s4)))
      +w2 = B.cat8(s11, B.cat8(s10, B.cat8(s9, s8)))
      +w3 = B.cat8(s15, B.cat8(s14, B.cat8(s13, s12)))
      A.Aes.block_of(B.write_u32(U32.or(U32.shl(w0), U32.shrn(w1, 31n)), B.write_u32(U32.or(U32.shl(w1), U32.shrn(w2, 31n)), B.write_u32(U32.or(U32.shl(w2), U32.shrn(w3, 31n)), B.write_u32(U32.shl(w3), [])))))

# K1 from L, or K2 from K1: shift left, and fold the carried-out bit into Rb = 0x87.
def Cmac.subkey(+l: A.Aes.Block) -> A.Aes.Block:
  match l:
    case A.Blk{+s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      A.Aes.xor(Cmac.shl1(A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}), A.Blk{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, U32.mul(135, U32.shrn(s0, 7n))})

# A partial last block: 1, then zeros to 16 bytes.
def Cmac.pad(+bs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, bs, 128 <> List.replicate(U32, Nat.sub(15n, List.length(&2, U32, bs)), 0))

def Cmac.finish(rks: List<&2, A.Aes.Block>, x: A.Aes.Block, last: A.Aes.Block, k: A.Aes.Block) -> List<&2, U32>:
  A.Aes.to_bytes(A.Aes.encrypt(rks, A.Aes.xor(A.Aes.xor(x, last), k)))

# `cur` is the block before `rest`: complete and last (K1), followed by more
# blocks, or followed by a partial last block (padded, K2).
def Cmac.go(rest: List<&2, U32>, +rks: List<&2, A.Aes.Block>, x: A.Aes.Block, cur: A.Aes.Block, k1: A.Aes.Block, k2: A.Aes.Block) -> List<&2, U32>:
  match rest:
    case Nil{}:
      Cmac.finish(rks, x, cur, k1)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> more:
      Cmac.go(more, rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Blk{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}, k1, k2)
    case short:
      Cmac.finish(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(Cmac.pad(short)), k2)

def Cmac.start(msg: List<&2, U32>, +rks: List<&2, A.Aes.Block>, k1: A.Aes.Block, k2: A.Aes.Block) -> List<&2, U32>:
  match msg:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> rest:
      Cmac.go(rest, rks, A.Aes.zero(), A.Blk{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}, k1, k2)
    case short:
      Cmac.finish(rks, A.Aes.zero(), A.Aes.block_of(Cmac.pad(short)), k2)

def cmac(key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  +rks = A.Aes.round_keys(key)
  +k1 = Cmac.subkey(A.Aes.encrypt(rks, A.Aes.zero()))
  Cmac.start(msg, rks, k1, Cmac.subkey(k1))
