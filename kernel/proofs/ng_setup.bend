import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/route.bend as R
import ../LAWS.bend as L
import ./lib.bend as P
import ./liveness.bend as PL

# Proof of amf.ng_setup.requires_supported_plmn: every other path of the
# NgapData step is a UE procedure, and no action of a UE procedure is an NG
# Setup Response (PL.Lw).

def Req.answer(cfg: S.Cfg, +assoc: U32, b: Bool, e: {N.Ngap.is_ng_setup_response(N.Setup{assoc, N.NgSetup.answer(cfg, b)}) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))

def Req.reply(config: Maybe<&2, S.Cfg>, +assoc: U32, v: V.NGSetupRequest.View, e: {N.Ngap.is_ng_setup_response(N.Setup{assoc, N.NgSetup.reply(config, v)}) == True{} : Bool}) -> {N.NgSetup.supported_view(config, v) == True{} : Bool}:
  match config:
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Some{+cfg}:
      match v:
        case V.NGSetupRequest.View{globalrannodeid, +supportedtalist, defaultpagingdrx}:
          Req.answer(cfg, assoc, N.Ta.supported(S.Cfg.plmn(cfg), S.Cfg.tac(cfg), supportedtalist), e)

def Req.view(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.NGSetupRequest.View>, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(N.NgSetup.of_view(st, assoc, r))) == True{} : Bool}) -> {N.NgSetup.supported_of_view(S.State.config(st), r) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Done{+v}:
      Req.reply(S.State.config(st), assoc, v, P.Bool.or_true_l(N.Ngap.is_ng_setup_response(N.Setup{assoc, N.NgSetup.reply(S.State.config(st), v)}), False{}, {==}, e))

def Req.ready(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), b: Bool, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.ready(st, assoc, stream, kind, code, ies, entropy, b))) == True{} : Bool}) -> {False{} == True{} : Bool}:
  match b:
    case True{}:
      +o = R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code))
      ar = PL.Lv.no_response(st, K.Kernel.actions(N.Step.of(st, o)), PL.Lv.step_acts(st, o, PL.Lw.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code))))
      (%ar : {_ == True{} : Bool}; e)
    case False{}:
      e

def Req.d1(+st: S.State, +assoc: U32, +stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, +entropy: B.Bytes(), ok: Bool, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, ok))) == True{} : Bool}) -> {N.NgSetup.supported_d1(S.State.config(st), ies, ok) == True{} : Bool}:
  match ok:
    case True{}:
      Req.view(st, assoc, V.NGSetupRequest.view(ies), e)
    case False{}:
      Req.ready(st, assoc, stream, kind, code, ies, entropy, S.Assocs.has(assoc, S.State.assocs(st)), e)

def Req.ies(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, entropy: B.Bytes(), r: Ap.Rd(List<&2, Fr.Ie>), e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r))) == True{} : Bool}) -> {N.NgSetup.supported_ies(S.State.config(st), kind, code, r) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Done{(+ies, c)}:
      Req.d1(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_ng_setup(kind, code), e)

def Req.pdu(+st: S.State, +assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Fr.Pdu>, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.of_pdu(st, assoc, stream, entropy, r))) == True{} : Bool}) -> {N.NgSetup.supported_pdu(S.State.config(st), r) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Req.ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), e)

def L.amf.ng_setup.requires_supported_plmn(st, entropy, assoc, stream, len, bytes, e):
  Req.pdu(st, assoc, stream, entropy, Fr.Pdu.read(bytes), e)
