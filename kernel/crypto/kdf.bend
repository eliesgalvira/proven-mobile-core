import Base
import ../bytes.bend as B
import ./sha256.bend as S
import ./hmac.bend as H

# The 3GPP key derivation function (TS 33.220 Annex B.2) and the 5G keys of
# TS 33.501 Annex A. A 128-bit key is the last 128 bits of the 256-bit output.

# P0 || L0 || P1 || L1 || ...
def Kdf.params(ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      List.append(&2, U32, p, B.write_u16(U32.from_nat(List.length(&2, U32, p)), Kdf.params(rest)))

def kdf(key: List<&2, U32>, fc: U32, ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  H.hmac(key, fc <> Kdf.params(ps))

def Kdf.last16(bs: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, bs, 16n)

def Kdf.ascii(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{code}, rest}:
      code <> Kdf.ascii(rest)

def Kdf.digits_ascii(ds: B.Digits()) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> rest:
      U32.add(48, d) <> Kdf.digits_ascii(rest)

# A two-digit MNC is written with a leading zero.
def Kdf.mnc3(mnc: B.Digits()) -> B.Digits():
  match mnc:
    case a <> b <> Nil{}:
      [0, a, b]
    case other:
      other

# 5G:mnc<MNC>.mcc<MCC>.3gppnetwork.org (TS 24.501 §9.12.1)
def kdf.serving_network_name(mcc: B.Digits(), mnc: B.Digits()) -> List<&2, U32>:
  List.append(&2, U32, Kdf.ascii("5G:mnc"), List.append(&2, U32, Kdf.digits_ascii(Kdf.mnc3(mnc)), List.append(&2, U32, Kdf.ascii(".mcc"), List.append(&2, U32, Kdf.digits_ascii(mcc), Kdf.ascii(".3gppnetwork.org")))))

# A.2: KAUSF from CK || IK, the serving network name and SQN xor AK
def kdf.k_ausf(ck: List<&2, U32>, ik: List<&2, U32>, snn: List<&2, U32>, sqn_xor_ak: List<&2, U32>) -> List<&2, U32>:
  kdf(List.append(&2, U32, ck, ik), 106, [snn, sqn_xor_ak])

# A.4: RES* (or XRES*) from CK || IK, the serving network name, RAND and RES
def kdf.res_star(ck: List<&2, U32>, ik: List<&2, U32>, snn: List<&2, U32>, rand: List<&2, U32>, res: List<&2, U32>) -> List<&2, U32>:
  Kdf.last16(kdf(List.append(&2, U32, ck, ik), 107, [snn, rand, res]))

# A.5: HRES* (or HXRES*) from RAND and RES*
def kdf.hres_star(rand: List<&2, U32>, res_star: List<&2, U32>) -> List<&2, U32>:
  Kdf.last16(S.sha256(List.append(&2, U32, rand, res_star)))

# A.6: KSEAF
def kdf.k_seaf(k_ausf: List<&2, U32>, snn: List<&2, U32>) -> List<&2, U32>:
  kdf(k_ausf, 108, [snn])

# A.7: KAMF from the SUPI (the IMSI digits as text) and ABBA
def kdf.k_amf(k_seaf: List<&2, U32>, supi: List<&2, U32>, abba: List<&2, U32>) -> List<&2, U32>:
  kdf(k_seaf, 109, [supi, abba])

# A.8: NAS keys; distinguisher 1 is encryption, 2 is integrity
def kdf.k_nas_enc(k_amf: List<&2, U32>, alg: U32) -> List<&2, U32>:
  Kdf.last16(kdf(k_amf, 105, [[1], [alg]]))

def kdf.k_nas_int(k_amf: List<&2, U32>, alg: U32) -> List<&2, U32>:
  Kdf.last16(kdf(k_amf, 105, [[2], [alg]]))

# A.9: KgNB from the uplink NAS COUNT, 3GPP access
def kdf.k_gnb(k_amf: List<&2, U32>, ul_nas_count: U32) -> List<&2, U32>:
  kdf(k_amf, 110, [B.write_u32(ul_nas_count, []), [1]])

# A.10: NH from the SYNC-input, KgNB for the first NH and the previous NH after
def kdf.nh(k_amf: List<&2, U32>, sync: List<&2, U32>) -> List<&2, U32>:
  kdf(k_amf, 111, [sync])
