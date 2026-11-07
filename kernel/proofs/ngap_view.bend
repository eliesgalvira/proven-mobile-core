import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/gen/types.bend as G
import ../LAWS.bend as L
import ./lib.bend as P
import ../ngap/gen/laws.bend as GL
import ../ngap/gen/proofs.bend as PG

# Mandatory IEs
# -------------

def L.ngap.initial_ue_message.mandatory(ies, v, e):
  GL.ngap.InitialUEMessage.mandatory(ies, v, e)

def L.ngap.path_switch_request.mandatory(ies, v, e):
  GL.ngap.PathSwitchRequest.mandatory(ies, v, e)

def L.ngap.handover_request_acknowledge.mandatory(ies, v, e):
  GL.ngap.HandoverRequestAcknowledge.mandatory(ies, v, e)

def L.ngap.handover_required.mandatory(ies, v, e):
  GL.ngap.HandoverRequired.mandatory(ies, v, e)

# No big Nat
# ----------
# The two wide integers are byte lists by type; what the laws add is the
# bound and the byte range their validity predicates carry.

def NoBig.amf(+c: Ap.Cur, +c2: Ap.Cur, +v: B.Bytes(), e: {G.AMF_UE_NGAP_ID.read(c) == Done{(v, c2)} : Ap.Rd(G.AMF_UE_NGAP_ID())}) -> {Nat.is_le(List.length(&2, U32, v), 5n) == True{} : Bool} & {B.all_bytes(v) == True{} : Bool}:
  +ok : {Bool.and(Ap.Big.canonical(v), Bool.and(Nat.is_le(List.length(&2, U32, v), 5n), B.all_bytes(v))) == True{} : Bool} = GL.ngap.AMF_UE_NGAP_ID.decode_valid(c, v, c2, e)
  +rest : {Bool.and(Nat.is_le(List.length(&2, U32, v), 5n), B.all_bytes(v)) == True{} : Bool} = P.Bool.and_true_r(Ap.Big.canonical(v), Bool.and(Nat.is_le(List.length(&2, U32, v), 5n), B.all_bytes(v)), ok)
  (P.Bool.and_true_l(Nat.is_le(List.length(&2, U32, v), 5n), B.all_bytes(v), rest), P.Bool.and_true_r(Nat.is_le(List.length(&2, U32, v), 5n), B.all_bytes(v), rest))

def NoBig.xbig(+v: Ap.XBig, ok: {Ap.XBig.valid(5n, v) == True{} : Bool}) -> {B.all_bytes(Ap.XBig.octets(v)) == True{} : Bool}:
  match v:
    case Ap.BRoot{bs}:
      P.Bool.and_true_r(Nat.is_le(List.length(&2, U32, bs), 6n), B.all_bytes(bs), P.Bool.and_true_r(Ap.Big.canonical(bs), Bool.and(Nat.is_le(List.length(&2, U32, bs), 6n), B.all_bytes(bs)), ok))
    case Ap.BExt{bs}:
      P.Bool.and_true_r(Ap.Len.valid(List.length(&2, U32, bs)), B.all_bytes(bs), ok)

def NoBig.rate(+c: Ap.Cur, +c2: Ap.Cur, +v: Ap.XBig, e: {G.BitRate.read(c) == Done{(v, c2)} : Ap.Rd(G.BitRate())}) -> {B.all_bytes(Ap.XBig.octets(v)) == True{} : Bool}:
  NoBig.xbig(v, GL.ngap.BitRate.decode_valid(c, v, c2, e))

def L.ngap.no_big_nat(c, c2):
  (v => e => NoBig.amf(c, c2, v, e), v => e => NoBig.rate(c, c2, v, e))
