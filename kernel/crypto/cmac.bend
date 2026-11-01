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

# A partial last block whose padding bit is already in place: zeros to 16 bytes.
def Cmac.zero_pad(+bs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, bs, List.replicate(U32, Nat.sub(16n, List.length(&2, U32, bs)), 0))

def Cmac.finish(rks: List<&2, A.Aes.Block>, x: A.Aes.Block, last: A.Aes.Block, k: A.Aes.Block) -> List<&2, U32>:
  A.Aes.to_bytes(A.Aes.encrypt(rks, A.Aes.xor(A.Aes.xor(x, last), k)))

# `cur` is the block before `rest`: complete and last (k_last), followed by
# more blocks, or followed by a partial last block (padded with `pad`, k_part).
def Cmac.go(~pad: List<&2, U32> -> List<&2, U32>, rest: List<&2, U32>, +rks: List<&2, A.Aes.Block>, x: A.Aes.Block, cur: A.Aes.Block, k_last: A.Aes.Block, k_part: A.Aes.Block) -> List<&2, U32>:
  match rest:
    case Nil{}:
      Cmac.finish(rks, x, cur, k_last)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> more:
      Cmac.go(~pad, more, rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Blk{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}, k_last, k_part)
    case short:
      Cmac.finish(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad(short)), k_part)

def Cmac.start(~pad: List<&2, U32> -> List<&2, U32>, msg: List<&2, U32>, +rks: List<&2, A.Aes.Block>, k_last: A.Aes.Block, k_part: A.Aes.Block) -> List<&2, U32>:
  match msg:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> rest:
      Cmac.go(~pad, rest, rks, A.Aes.zero(), A.Blk{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}, k_last, k_part)
    case short:
      Cmac.finish(rks, A.Aes.zero(), A.Aes.block_of(pad(short)), k_part)

def cmac(key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  +rks = A.Aes.round_keys(key)
  +k1 = Cmac.subkey(A.Aes.encrypt(rks, A.Aes.zero()))
  Cmac.start(~(bs => Cmac.pad(bs)), msg, rks, k1, Cmac.subkey(k1))

# The last byte of a message with v extra bits (1 to 7): its top v bits, then the padding bit.
def Cmac.partial_byte(+b: U32, +v: Nat) -> U32:
  U32.or(U32.and(b, U32.and(255, U32.shln(255, Nat.sub(8n, v)))), U32.shrn(128, v))

def Cmac.with_partial(full: List<&2, U32>, b: U32, v: Nat) -> List<&2, U32>:
  match v:
    case 0n:
      full
    case 1n+p:
      List.append(&2, U32, full, [Cmac.partial_byte(b, 1n+p)])

# A message of `bits` bits, left-aligned in its bytes, with the RFC 4493
# padding bit placed after the last bit.
def Cmac.bit_padded(+msg: List<&2, U32>, +bits: Nat) -> List<&2, U32>:
  Cmac.with_partial(List.take(&2, U32, msg, Nat.div(bits, 8n)), Maybe.default(&2, U32, List.get(&2, U32, msg, Nat.div(bits, 8n)), 0), Nat.mod(bits, 8n))

def Cmac.bits_go(key: List<&2, U32>, msg: List<&2, U32>, bits: Nat, whole_bytes: Bool) -> List<&2, U32>:
  match whole_bytes:
    case True{}:
      cmac(key, List.take(&2, U32, msg, Nat.div(bits, 8n)))
    case False{}:
      +rks = A.Aes.round_keys(key)
      +k2 = Cmac.subkey(Cmac.subkey(A.Aes.encrypt(rks, A.Aes.zero())))
      Cmac.start(~(bs => Cmac.zero_pad(bs)), Cmac.bit_padded(msg, bits), rks, k2, k2)

# AES-CMAC of the first `bits` bits of `msg` (TS 33.401 Annex B uses bit lengths).
def cmac_bits(key: List<&2, U32>, +msg: List<&2, U32>, +bits: Nat) -> List<&2, U32>:
  Cmac.bits_go(key, msg, bits, Nat.is_eq(Nat.mod(bits, 8n), 0n))
