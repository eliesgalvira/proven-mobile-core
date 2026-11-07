import Base
import ../bytes.bend as B
import ./aes.bend as A

# MILENAGE (TS 35.206 §4) with OPc given. rot moves byte (j + r) to position j,
# as the reference algorithm rotates towards the most significant end.

def Milenage.rot4(b: A.Aes.Block) -> A.Aes.Block:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      A.Blk{s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s0, s1, s2, s3}

def Milenage.rot8(b: A.Aes.Block) -> A.Aes.Block:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      A.Blk{s8, s9, s10, s11, s12, s13, s14, s15, s0, s1, s2, s3, s4, s5, s6, s7}

def Milenage.rot12(b: A.Aes.Block) -> A.Aes.Block:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      A.Blk{s12, s13, s14, s15, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11}

def Milenage.c(n: U32) -> A.Aes.Block:
  A.Blk{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, n}

def Milenage.low8(b: A.Aes.Block) -> List<&2, U32>:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      [s0, s1, s2, s3, s4, s5, s6, s7]

def Milenage.high8(b: A.Aes.Block) -> List<&2, U32>:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      [s8, s9, s10, s11, s12, s13, s14, s15]

def Milenage.low6(b: A.Aes.Block) -> List<&2, U32>:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      [s0, s1, s2, s3, s4, s5]

# OPc = OP xor E_K(OP)
def milenage.opc(key: List<&2, U32>, +op: List<&2, U32>) -> List<&2, U32>:
  A.Aes.to_bytes(A.Aes.xor(A.Aes.block_of(op), A.Aes.encrypt(A.Aes.round_keys(key), A.Aes.block_of(op))))

def Milenage.temp(rks: List<&2, A.Aes.Block>, opc: A.Aes.Block, rand: List<&2, U32>) -> A.Aes.Block:
  A.Aes.encrypt(rks, A.Aes.xor(A.Aes.block_of(rand), opc))

# OUT1 = E_K(TEMP xor rot(IN1 xor OPc, r1) xor c1) xor OPc, IN1 = SQN || AMF || SQN || AMF
def Milenage.out1(key: List<&2, U32>, +opc: List<&2, U32>, rand: List<&2, U32>, +sqn: List<&2, U32>, +amf: List<&2, U32>) -> A.Aes.Block:
  +rks = A.Aes.round_keys(key)
  +opcb = A.Aes.block_of(opc)
  in1 = A.Aes.block_of(List.append(&2, U32, sqn, List.append(&2, U32, amf, List.append(&2, U32, sqn, amf))))
  A.Aes.xor(A.Aes.encrypt(rks, A.Aes.xor(Milenage.temp(rks, opcb, rand), Milenage.rot8(A.Aes.xor(in1, opcb)))), opcb)

# OUTn = E_K(rot(TEMP xor OPc, rn) xor cn) xor OPc
def Milenage.out(key: List<&2, U32>, +opc: List<&2, U32>, rand: List<&2, U32>, rotated: A.Aes.Block -> A.Aes.Block, c: U32) -> A.Aes.Block:
  +rks = A.Aes.round_keys(key)
  +opcb = A.Aes.block_of(opc)
  A.Aes.xor(A.Aes.encrypt(rks, A.Aes.xor(rotated(A.Aes.xor(Milenage.temp(rks, opcb, rand), opcb)), Milenage.c(c))), opcb)

def milenage.f1(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>, sqn: List<&2, U32>, amf: List<&2, U32>) -> List<&2, U32>:
  Milenage.low8(Milenage.out1(key, opc, rand, sqn, amf))

def milenage.f1_star(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>, sqn: List<&2, U32>, amf: List<&2, U32>) -> List<&2, U32>:
  Milenage.high8(Milenage.out1(key, opc, rand, sqn, amf))

def milenage.f2(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> List<&2, U32>:
  Milenage.high8(Milenage.out(key, opc, rand, b => b, 1))

def milenage.f3(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> List<&2, U32>:
  A.Aes.to_bytes(Milenage.out(key, opc, rand, b => Milenage.rot4(b), 2))

def milenage.f4(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> List<&2, U32>:
  A.Aes.to_bytes(Milenage.out(key, opc, rand, b => Milenage.rot8(b), 4))

def milenage.f5(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> List<&2, U32>:
  Milenage.low6(Milenage.out(key, opc, rand, b => b, 1))

def milenage.f5_star(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> List<&2, U32>:
  Milenage.low6(Milenage.out(key, opc, rand, b => Milenage.rot12(b), 8))
