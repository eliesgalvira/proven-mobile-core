import Base
import ../LAWS.bend as L
import ../bytes.bend as B
import ../crypto/sha256.bend as S
import ../crypto/hmac.bend as H

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
