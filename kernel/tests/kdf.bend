import Base
import ../crypto/milenage.bend as M
import ../crypto/kdf.bend as K
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture

# The captured registration: every derived key from K, OPc, RAND, SQN and the SNN.

def xor_bytes(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case x <> xt y <> yt:
      U32.xor(x, y) <> xor_bytes(xt, yt)
    case _ _:
      Nil{}

def main() -> IO(Unit):
  do IO<Unit>:
    +s : V.Vec = V.Vec.field(Capture.data(), "secrets")
    +k : List<&2, U32> = V.Vec.secret(s, "k")
    +opc : List<&2, U32> = V.Vec.secret(s, "opc")
    +rand : List<&2, U32> = V.Vec.secret(s, "rand")
    +ck : List<&2, U32> = M.milenage.f3(k, opc, rand)
    +ik : List<&2, U32> = M.milenage.f4(k, opc, rand)
    +res : List<&2, U32> = M.milenage.f2(k, opc, rand)
    +snn : List<&2, U32> = K.kdf.serving_network_name([0, 0, 1], [0, 1])
    C.Check.report("serving network name", C.Check.bytes_eq(snn, K.Kdf.ascii(V.Vec.text(V.Vec.field(s, "serving_network_name")))))
    C.Check.report("SQN xor AK", C.Check.bytes_eq(xor_bytes(V.Vec.secret(s, "sqn"), M.milenage.f5(k, opc, rand)), V.Vec.bytes(V.Vec.field(V.Vec.field(s, "sqn"), "sqn_xor_ak"))))
    +k_ausf : List<&2, U32> = K.kdf.k_ausf(ck, ik, snn, xor_bytes(V.Vec.secret(s, "sqn"), M.milenage.f5(k, opc, rand)))
    C.Check.report("KAUSF", C.Check.bytes_eq(k_ausf, V.Vec.secret(s, "k_ausf")))
    +res_star : List<&2, U32> = K.kdf.res_star(ck, ik, snn, rand, res)
    C.Check.report("RES*", C.Check.bytes_eq(res_star, V.Vec.secret(s, "res_star")))
    C.Check.report("HRES*", C.Check.bytes_eq(K.kdf.hres_star(rand, res_star), V.Vec.secret(s, "hres_star")))
    +k_seaf : List<&2, U32> = K.kdf.k_seaf(k_ausf, snn)
    C.Check.report("KSEAF", C.Check.bytes_eq(k_seaf, V.Vec.secret(s, "k_seaf")))
    +k_amf : List<&2, U32> = K.kdf.k_amf(k_seaf, K.Kdf.ascii("001010000000001"), V.Vec.secret(s, "abba"))
    C.Check.report("KAMF", C.Check.bytes_eq(k_amf, V.Vec.secret(s, "k_amf")))
    C.Check.report("KNASint (NIA2)", C.Check.bytes_eq(K.kdf.k_nas_int(k_amf, 2), V.Vec.secret(s, "k_nas_int")))
    C.Check.report("KNASenc (NEA0)", C.Check.bytes_eq(K.kdf.k_nas_enc(k_amf, 0), V.Vec.secret(s, "k_nas_enc")))
    C.Check.report("KgNB (uplink NAS COUNT 0)", C.Check.bytes_eq(K.kdf.k_gnb(k_amf, 0), V.Vec.secret(s, "k_gnb")))
