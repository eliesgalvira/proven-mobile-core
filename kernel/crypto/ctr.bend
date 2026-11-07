import Base
import ../bytes.bend as B
import ./aes.bend as A

# AES-128 in counter mode (SP 800-38A §6.5): the keystream is the encryption
# of successive counter blocks, and the low 64 bits of the counter increment
# (TS 33.401 B.1.3). The keystream always covers the message, so `xor_zip`
# never runs out of keystream; if it did, the output would be truncated.

def Ctr.inc(c: A.Aes.Block) -> A.Aes.Block:
  match c:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      +lo = U32.add(B.cat8(s15, B.cat8(s14, B.cat8(s13, s12))), 1)
      hi = U32.add(B.cat8(s11, B.cat8(s10, B.cat8(s9, s8))), Bool.to_u32(U32.is_zero(lo)))
      A.Aes.block_of(List.append(&2, U32, [s0, s1, s2, s3, s4, s5, s6, s7], B.write_u32(hi, B.write_u32(lo, []))))

# 16 bytes per block, enough for n message bytes.
def Ctr.blocks16(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 16n+p:
      16n+Ctr.blocks16(p)
    case q:
      16n

def Ctr.keystream(n: Nat, +rks: A.Aes.Keys, +c: A.Aes.Block) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 16n+p:
      List.append(&2, U32, A.Aes.to_bytes(A.Aes.encrypt(rks, c)), Ctr.keystream(p, rks, Ctr.inc(c)))
    case q:
      A.Aes.to_bytes(A.Aes.encrypt(rks, c))

def Ctr.xor_zip(m: List<&2, U32>, ks: List<&2, U32>) -> List<&2, U32>:
  match m ks:
    case Nil{} _:
      Nil{}
    case b <> mt Nil{}:
      Nil{}
    case b <> mt k <> kt:
      U32.xor(b, k) <> Ctr.xor_zip(mt, kt)

def ctr(key: List<&2, U32>, iv: List<&2, U32>, +m: List<&2, U32>) -> List<&2, U32>:
  Ctr.xor_zip(m, Ctr.keystream(List.length(&2, U32, m), A.Aes.round_keys(key), A.Aes.block_of(iv)))
