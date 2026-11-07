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

# One run for a key, OPc and RAND: the key schedule, OPc and TEMP =
# E_K(RAND xor OPc), computed once for every output.
type Milenage.Run is Data:
  Run{rks: A.Aes.Keys, opc: A.Aes.Block, temp: A.Aes.Block}

def milenage.run(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> Milenage.Run:
  +rks = A.Aes.round_keys(key)
  +opcb = A.Aes.block_of(opc)
  Run{rks, opcb, A.Aes.encrypt(rks, A.Aes.xor(A.Aes.block_of(rand), opcb))}

# OUT1 = E_K(TEMP xor rot(IN1 xor OPc, r1) xor c1) xor OPc, IN1 = SQN || AMF || SQN || AMF
def Milenage.out1(r: Milenage.Run, +sqn: List<&2, U32>, +amf: List<&2, U32>) -> A.Aes.Block:
  match r:
    case Run{rks, +opc, temp}:
      in1 = A.Aes.block_of(List.append(&2, U32, sqn, List.append(&2, U32, amf, List.append(&2, U32, sqn, amf))))
      A.Aes.xor(A.Aes.encrypt(rks, A.Aes.xor(temp, Milenage.rot8(A.Aes.xor(in1, opc)))), opc)

# OUTn = E_K(rot(TEMP xor OPc, rn) xor cn) xor OPc
def Milenage.out(r: Milenage.Run, rotated: A.Aes.Block -> A.Aes.Block, c: U32) -> A.Aes.Block:
  match r:
    case Run{rks, +opc, temp}:
      A.Aes.xor(A.Aes.encrypt(rks, A.Aes.xor(rotated(A.Aes.xor(temp, opc)), Milenage.c(c))), opc)

def Milenage.f1(r: Milenage.Run, sqn: List<&2, U32>, amf: List<&2, U32>) -> List<&2, U32>:
  Milenage.low8(Milenage.out1(r, sqn, amf))

def Milenage.f1_star(r: Milenage.Run, sqn: List<&2, U32>, amf: List<&2, U32>) -> List<&2, U32>:
  Milenage.high8(Milenage.out1(r, sqn, amf))

def Milenage.f2(r: Milenage.Run) -> List<&2, U32>:
  Milenage.high8(Milenage.out(r, b => b, 1))

def Milenage.f3(r: Milenage.Run) -> List<&2, U32>:
  A.Aes.to_bytes(Milenage.out(r, b => Milenage.rot4(b), 2))

def Milenage.f4(r: Milenage.Run) -> List<&2, U32>:
  A.Aes.to_bytes(Milenage.out(r, b => Milenage.rot8(b), 4))

def Milenage.f5(r: Milenage.Run) -> List<&2, U32>:
  Milenage.low6(Milenage.out(r, b => b, 1))

def Milenage.f5_star(r: Milenage.Run) -> List<&2, U32>:
  Milenage.low6(Milenage.out(r, b => Milenage.rot12(b), 8))

# The functions of TS 35.206, each on its own run.
def milenage.f1(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>, sqn: List<&2, U32>, amf: List<&2, U32>) -> List<&2, U32>:
  Milenage.f1(milenage.run(key, opc, rand), sqn, amf)

def milenage.f1_star(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>, sqn: List<&2, U32>, amf: List<&2, U32>) -> List<&2, U32>:
  Milenage.f1_star(milenage.run(key, opc, rand), sqn, amf)

def milenage.f2(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> List<&2, U32>:
  Milenage.f2(milenage.run(key, opc, rand))

def milenage.f3(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> List<&2, U32>:
  Milenage.f3(milenage.run(key, opc, rand))

def milenage.f4(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> List<&2, U32>:
  Milenage.f4(milenage.run(key, opc, rand))

def milenage.f5(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> List<&2, U32>:
  Milenage.f5(milenage.run(key, opc, rand))

def milenage.f5_star(key: List<&2, U32>, opc: List<&2, U32>, rand: List<&2, U32>) -> List<&2, U32>:
  Milenage.f5_star(milenage.run(key, opc, rand))
