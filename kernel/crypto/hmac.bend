import Base
import ./sha256.bend as S

# HMAC-SHA-256 (RFC 2104) over byte lists.

def Hmac.shorten(key: List<&2, U32>, long: Bool) -> List<&2, U32>:
  match long:
    case True{}:
      S.sha256(key)
    case False{}:
      key

# The key hashed if longer than a block, then zero-padded to 64 bytes.
def Hmac.block_key(+key: List<&2, U32>) -> List<&2, U32>:
  +k0 = Hmac.shorten(key, Nat.is_gt(List.length(&2, U32, key), 64n))
  List.append(&2, U32, k0, List.replicate(U32, Nat.sub(64n, List.length(&2, U32, k0)), 0))

def Hmac.xor_each(bs: List<&2, U32>, +pad: U32) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      U32.xor(b, pad) <> Hmac.xor_each(rest, pad)

def Hmac.outer(key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  +k = Hmac.block_key(key)
  List.append(&2, U32, Hmac.xor_each(k, 92), S.sha256(List.append(&2, U32, Hmac.xor_each(k, 54), msg)))

def hmac(key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  S.sha256(Hmac.outer(key, msg))
