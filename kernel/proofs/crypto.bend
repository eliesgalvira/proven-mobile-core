import Base
import ../LAWS.bend as L
import ../bytes.bend as B
import ./lib.bend as P
import ../crypto/sha256.bend as S
import ../crypto/hmac.bend as H
import ../crypto/aes.bend as A
import ../crypto/ctr.bend as CT
import ../crypto/cmac.bend as M
import ../crypto/milenage.bend as Mil
import ../crypto/kdf.bend as K

# Proofs of the crypto laws (tickets 04 to 08).

# Serialising any state writes eight words of four bytes.
def Sha256.serialize_len(st: S.Sha256.State) -> {List.length(&2, U32, S.Sha256.serialize(st)) == 32n : Nat}:
  match st:
    case S.St{a, b, c, d, e, f, g, h}:
      {==}

def L.sha256.length(msg):
  Sha256.serialize_len(S.Sha256.digest_state(msg))

def L.hmac.length(key, msg):
  L.sha256.length(H.Hmac.outer(key, msg))

# AES
# ---

def Aes.to_bytes_len(b: A.Aes.Block) -> {List.length(&2, U32, A.Aes.to_bytes(b)) == 16n : Nat}:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      {==}

def L.aes.block_length(key, block):
  Aes.to_bytes_len(A.Aes.encrypt(A.Aes.round_keys(key), A.Aes.block_of(block)))

# CTR
# ---

# The keystream for n bytes has blocks16(n) bytes.
def Ctr.keystream_len(+n: Nat, +rks: List<&2, A.Aes.Block>, +c: A.Aes.Block) -> {List.length(&2, U32, CT.Ctr.keystream(n, rks, c)) == CT.Ctr.blocks16(n) : Nat}:
  match n:
    case 0n:
      {==}
    case 16n+p:
      al = Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, A.Aes.to_bytes(A.Aes.encrypt(rks, c)), CT.Ctr.keystream(p, rks, CT.Ctr.inc(c)))), Nat.add(List.length(&2, U32, A.Aes.to_bytes(A.Aes.encrypt(rks, c))), List.length(&2, U32, CT.Ctr.keystream(p, rks, CT.Ctr.inc(c)))), P.List.append_len(A.Aes.to_bytes(A.Aes.encrypt(rks, c)), CT.Ctr.keystream(p, rks, CT.Ctr.inc(c))))
      bl = Equal.sym(Nat, List.length(&2, U32, A.Aes.to_bytes(A.Aes.encrypt(rks, c))), 16n, Aes.to_bytes_len(A.Aes.encrypt(rks, c)))
      ih = Equal.sym(Nat, List.length(&2, U32, CT.Ctr.keystream(p, rks, CT.Ctr.inc(c))), CT.Ctr.blocks16(p), Ctr.keystream_len(p, rks, CT.Ctr.inc(c)))
      %al : {_ == 16n+CT.Ctr.blocks16(p) : Nat}
      %bl : {Nat.add(_, List.length(&2, U32, CT.Ctr.keystream(p, rks, CT.Ctr.inc(c)))) == 16n+CT.Ctr.blocks16(p) : Nat}
      %ih : {Nat.add(16n, _) == 16n+CT.Ctr.blocks16(p) : Nat}
      {==}
    case 1n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 2n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 3n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 4n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 5n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 6n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 7n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 8n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 9n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 10n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 11n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 12n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 13n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 14n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))
    case 15n:
      Aes.to_bytes_len(A.Aes.encrypt(rks, c))

# n <= blocks16(n)
def Ctr.le_blocks16(n: Nat) -> {Nat.is_le(n, CT.Ctr.blocks16(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n+p:
      Ctr.le_blocks16(p)

# The keystream covers the message.
def Ctr.covers(+m: B.Bytes(), +rks: List<&2, A.Aes.Block>, +c: A.Aes.Block) -> {Nat.is_le(List.length(&2, U32, m), List.length(&2, U32, CT.Ctr.keystream(List.length(&2, U32, m), rks, c))) == True{} : Bool}:
  kl = Ctr.keystream_len(List.length(&2, U32, m), rks, c)
  sl = Equal.sym(Nat, List.length(&2, U32, CT.Ctr.keystream(List.length(&2, U32, m), rks, c)), CT.Ctr.blocks16(List.length(&2, U32, m)), kl)
  %sl : {Nat.is_le(List.length(&2, U32, m), _) == True{} : Bool}
  Ctr.le_blocks16(List.length(&2, U32, m))

def Ctr.xor_zip_len(+m: B.Bytes(), +ks: B.Bytes(), e: {Nat.is_le(List.length(&2, U32, m), List.length(&2, U32, ks)) == True{} : Bool}) -> {List.length(&2, U32, CT.Ctr.xor_zip(m, ks)) == List.length(&2, U32, m) : Nat}:
  match m ks:
    case Nil{} _:
      {==}
    case b <> mt Nil{}:
      Empty.absurd({List.length(&2, U32, CT.Ctr.xor_zip(b <> mt, [])) == List.length(&2, U32, b <> mt) : Nat}, P.Refute.bool(e))
    case b <> mt k <> kt:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, U32, CT.Ctr.xor_zip(mt, kt)), List.length(&2, U32, mt), Ctr.xor_zip_len(mt, kt, e))

def L.ctr.length(key, iv, m):
  Ctr.xor_zip_len(m, CT.Ctr.keystream(List.length(&2, U32, m), A.Aes.round_keys(key), A.Aes.block_of(iv)), Ctr.covers(m, A.Aes.round_keys(key), A.Aes.block_of(iv)))

def Bool.xor_xor(a: Bool, b: Bool) -> {Bool.xor(Bool.xor(a, b), b) == a : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Word.xor_xor(n: Nat, a: Word(n), b: Word(n)) -> {Word.xor(n, Word.xor(n, a, b), b) == a : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          h = Bool.xor_xor(ab, bb)
          t = Word.xor_xor(p, at, bt)
          %h : {WCon{Bool.xor(Bool.xor(ab, bb), bb), Word.xor(p, Word.xor(p, at, bt), bt)} == WCon{_, at} : Word(1n+p)}
          %t : {WCon{Bool.xor(Bool.xor(ab, bb), bb), Word.xor(p, Word.xor(p, at, bt), bt)} == WCon{Bool.xor(Bool.xor(ab, bb), bb), _} : Word(1n+p)}
          {==}

def U32.xor_xor(a: U32, b: U32) -> {U32.xor(U32.xor(a, b), b) == a : U32}:
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, Word.xor(32n, x, y), y), x, Word.xor_xor(32n, x, y))

def Ctr.xor_zip_inv(m: B.Bytes(), ks: B.Bytes(), e: {Nat.is_le(List.length(&2, U32, m), List.length(&2, U32, ks)) == True{} : Bool}) -> {CT.Ctr.xor_zip(CT.Ctr.xor_zip(m, ks), ks) == m : B.Bytes()}:
  match m ks:
    case Nil{} _:
      {==}
    case b <> mt Nil{}:
      Empty.absurd({CT.Ctr.xor_zip(CT.Ctr.xor_zip(b <> mt, []), []) == b <> mt : B.Bytes()}, P.Refute.bool(e))
    case +b <> +mt +k <> +kt:
      P.List.cons_eq(U32.xor(U32.xor(b, k), k), b, CT.Ctr.xor_zip(CT.Ctr.xor_zip(mt, kt), kt), mt, U32.xor_xor(b, k), Ctr.xor_zip_inv(mt, kt, e))

def L.ctr.involution(key, iv, m):
  ll = L.ctr.length(key, iv, m)
  sl = Equal.sym(Nat, List.length(&2, U32, CT.Ctr.xor_zip(m, CT.Ctr.keystream(List.length(&2, U32, m), A.Aes.round_keys(key), A.Aes.block_of(iv)))), List.length(&2, U32, m), ll)
  %sl : {CT.Ctr.xor_zip(CT.Ctr.xor_zip(m, CT.Ctr.keystream(List.length(&2, U32, m), A.Aes.round_keys(key), A.Aes.block_of(iv))), CT.Ctr.keystream(_, A.Aes.round_keys(key), A.Aes.block_of(iv))) == m : B.Bytes()}
  Ctr.xor_zip_inv(m, CT.Ctr.keystream(List.length(&2, U32, m), A.Aes.round_keys(key), A.Aes.block_of(iv)), Ctr.covers(m, A.Aes.round_keys(key), A.Aes.block_of(iv)))

# CMAC
# ----

def Cmac.finish_len(rks: List<&2, A.Aes.Block>, x: A.Aes.Block, last: A.Aes.Block, k: A.Aes.Block) -> {List.length(&2, U32, M.Cmac.finish(rks, x, last, k)) == 16n : Nat}:
  Aes.to_bytes_len(A.Aes.encrypt(rks, A.Aes.xor(A.Aes.xor(x, last), k)))

def Cmac.go_len(~pad: List<&2, U32> -> List<&2, U32>, rest: B.Bytes(), +rks: List<&2, A.Aes.Block>, x: A.Aes.Block, cur: A.Aes.Block, k_last: A.Aes.Block, k_part: A.Aes.Block) -> {List.length(&2, U32, M.Cmac.go(~pad, rest, rks, x, cur, k_last, k_part)) == 16n : Nat}:
  match rest:
    case Nil{}:
      Cmac.finish_len(rks, x, cur, k_last)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> more:
      Cmac.go_len(~pad, more, rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Blk{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}, k_last, k_part)
    case b0 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0])), k_part)
    case b0 <> b1 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1])), k_part)
    case b0 <> b1 <> b2 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2])), k_part)
    case b0 <> b1 <> b2 <> b3 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.encrypt(rks, A.Aes.xor(x, cur)), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14])), k_part)

def Cmac.start_len(~pad: List<&2, U32> -> List<&2, U32>, msg: B.Bytes(), +rks: List<&2, A.Aes.Block>, k_last: A.Aes.Block, k_part: A.Aes.Block) -> {List.length(&2, U32, M.Cmac.start(~pad, msg, rks, k_last, k_part)) == 16n : Nat}:
  match msg:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> rest:
      Cmac.go_len(~pad, rest, rks, A.Aes.zero(), A.Blk{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}, k_last, k_part)
    case Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([])), k_part)
    case b0 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0])), k_part)
    case b0 <> b1 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1])), k_part)
    case b0 <> b1 <> b2 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2])), k_part)
    case b0 <> b1 <> b2 <> b3 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13])), k_part)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}:
      Cmac.finish_len(rks, A.Aes.zero(), A.Aes.block_of(pad([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14])), k_part)

def L.cmac.length(key, msg):
  Cmac.start_len(~(bs => M.Cmac.pad(bs)), msg, A.Aes.round_keys(key), M.Cmac.subkey(A.Aes.encrypt(A.Aes.round_keys(key), A.Aes.zero())), M.Cmac.subkey(M.Cmac.subkey(A.Aes.encrypt(A.Aes.round_keys(key), A.Aes.zero()))))

# MILENAGE
# --------

def Milenage.low8_len(b: A.Aes.Block) -> {List.length(&2, U32, Mil.Milenage.low8(b)) == 8n : Nat}:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      {==}

def Milenage.high8_len(b: A.Aes.Block) -> {List.length(&2, U32, Mil.Milenage.high8(b)) == 8n : Nat}:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      {==}

def Milenage.low6_len(b: A.Aes.Block) -> {List.length(&2, U32, Mil.Milenage.low6(b)) == 6n : Nat}:
  match b:
    case A.Blk{s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15}:
      {==}

def L.milenage.lengths(key, opc, rand, sqn, amf):
  +r = Mil.milenage.run(key, opc, rand)
  (Milenage.low8_len(Mil.Milenage.out1(r, sqn, amf)),
   (Milenage.high8_len(Mil.Milenage.out1(r, sqn, amf)),
   (Milenage.high8_len(Mil.Milenage.out(r, b => b, 1)),
   (Aes.to_bytes_len(Mil.Milenage.out(r, b => Mil.Milenage.rot4(b), 2)),
   (Aes.to_bytes_len(Mil.Milenage.out(r, b => Mil.Milenage.rot8(b), 4)),
   (Milenage.low6_len(Mil.Milenage.out(r, b => b, 1)),
   Milenage.low6_len(Mil.Milenage.out(r, b => Mil.Milenage.rot12(b), 8))))))))

# KDF
# ---

def List.drop_len(xs: B.Bytes(), n: Nat) -> {List.length(&2, U32, List.drop(&2, U32, xs, n)) == Nat.sub(List.length(&2, U32, xs), n) : Nat}:
  match xs n:
    case Nil{} _:
      {==}
    case x <> xt 0n:
      {==}
    case x <> xt 1n+p:
      List.drop_len(xt, p)

def Kdf.len(key: B.Bytes(), fc: U32, ps: List<&2, B.Bytes()>) -> {List.length(&2, U32, K.kdf(key, fc, ps)) == 32n : Nat}:
  L.hmac.length(key, fc <> K.Kdf.params(ps))

# The last 16 of 32 bytes are 16 bytes.
def Kdf.last16_len(+bs: B.Bytes(), e: {List.length(&2, U32, bs) == 32n : Nat}) -> {List.length(&2, U32, K.Kdf.last16(bs)) == 16n : Nat}:
  dl = Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, bs, 16n)), Nat.sub(List.length(&2, U32, bs), 16n), List.drop_len(bs, 16n))
  se = Equal.sym(Nat, List.length(&2, U32, bs), 32n, e)
  %dl : {_ == 16n : Nat}
  %se : {Nat.sub(_, 16n) == 16n : Nat}
  {==}

def L.kdf.length(key, fc, ps, ck, ik, snn, sqn_xor_ak, rand, res, res_star, k_ausf, k_seaf, supi, abba, k_amf, alg, count):
  (Kdf.len(key, fc, ps),
   (Kdf.len(List.append(&2, U32, ck, ik), 106, [snn, sqn_xor_ak]),
   (Kdf.last16_len(K.kdf(List.append(&2, U32, ck, ik), 107, [snn, rand, res]), Kdf.len(List.append(&2, U32, ck, ik), 107, [snn, rand, res])),
   (Kdf.last16_len(S.sha256(List.append(&2, U32, rand, res_star)), L.sha256.length(List.append(&2, U32, rand, res_star))),
   (Kdf.len(k_ausf, 108, [snn]),
   (Kdf.len(k_seaf, 109, [supi, abba]),
   (Kdf.last16_len(K.kdf(k_amf, 105, [[1], [alg]]), Kdf.len(k_amf, 105, [[1], [alg]])),
   (Kdf.last16_len(K.kdf(k_amf, 105, [[2], [alg]]), Kdf.len(k_amf, 105, [[2], [alg]])),
   Kdf.len(k_amf, 110, [B.write_u32(count, []), [1]])))))))))
