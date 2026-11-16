import Base
import ../ngap/frame.bend as Fr
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/route.bend as R
import ../amf/handover.bend as Ho
import ../LAWS.bend as L
import ./lib.bend as P
import ./liveness.bend as PL
import ./walk.bend as PW

# Proof of amf.ng_setup.requires_supported_plmn: walked from the bytes, a
# step answers NG Setup only on the NG Setup path, with a Response exactly
# when the request is supported (PW.Walk.Ready); no other action of the step
# is an NG Setup Response (PL.Lw).

# A setup response among xs ++ ys, none among xs, is among ys.
def Req.skip(+xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Ngap.any_ng_setup_response(xs) == False{} : Bool}, +e: {N.Ngap.any_ng_setup_response(List.append(&2, N.Act, xs, ys)) == True{} : Bool}) -> {N.Ngap.any_ng_setup_response(ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      e
    case +a <> +more:
      +ha = P.Bool.or_false_l(N.Ngap.is_ng_setup_response(a), N.Ngap.any_ng_setup_response(more), h)
      Req.skip(more, ys, P.Bool.or_false_r(N.Ngap.is_ng_setup_response(a), N.Ngap.any_ng_setup_response(more), h), P.Bool.or_true_r(N.Ngap.is_ng_setup_response(a), N.Ngap.any_ng_setup_response(List.append(&2, N.Act, more, ys)), ha, e))

# No setup response among xs nor ys, none among xs ++ ys.
def Req.app(+xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {N.Ngap.any_ng_setup_response(xs) == False{} : Bool}, +hy: {N.Ngap.any_ng_setup_response(ys) == False{} : Bool}) -> {N.Ngap.any_ng_setup_response(List.append(&2, N.Act, xs, ys)) == False{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      +x = N.Ngap.is_ng_setup_response(a)
      P.Bool.or_false(x, N.Ngap.any_ng_setup_response(List.append(&2, N.Act, more, ys)), P.Bool.or_false_l(x, N.Ngap.any_ng_setup_response(more), hx), Req.app(more, ys, P.Bool.or_false_r(x, N.Ngap.any_ng_setup_response(more), hx), hy))

# Re-initialising an association's contexts answers no NG Setup.
def Req.reset(+st: S.State, +assoc: U32) -> {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.reset(st, assoc))) == False{} : Bool}:
  +o = Ho.Ho.down(st, assoc)
  +s1 = K.Kernel.state(N.Step.of(st, o))
  +a = K.Kernel.actions(N.Step.of(st, o))
  +b = K.Kernel.actions(R.Route.drop(s1, assoc))
  Req.app(a, b, PL.Lv.no_response(st, a, PL.Lv.step_acts(st, o, PL.Lv.ok_w(st, o, PL.Lw.ho_down(st, assoc)))), PL.Lv.no_response(s1, b, PL.Lv.drop_acts(s1, assoc)))

# Actions with no setup response, said to have one: refuted.
def Req.none(+acts: List<&2, N.Act>, +h: {N.Ngap.any_ng_setup_response(acts) == False{} : Bool}, +e: {N.Ngap.any_ng_setup_response(acts) == True{} : Bool}, -T: Type) -> T:
  P.Bool.contra(T, N.Ngap.any_ng_setup_response(acts), e, h)

def L.amf.ng_setup.requires_supported_plmn(st, entropy, assoc, stream, len, bytes, e):
  +reset = K.Kernel.actions(R.Route.reset(st, assoc))
  PW.Walk.pdu(o => {N.Ngap.any_ng_setup_response(K.Kernel.actions(o)) == True{} : Bool} -> {N.NgSetup.supported_request(S.State.config(st), bytes) == True{} : Bool}, o => {PL.Lv.okw(st, o) == True{} : Bool}, st, assoc, stream, entropy, Fr.Pdu.read(bytes), +acts => sp => to => +nr => +e1 => Req.none(acts, nr, e1, {N.NgSetup.supported_request(S.State.config(st), bytes) == True{} : Bool}), +id => +ok => +acts => sp => to => er => e1 => Equal.trans(Bool, N.NgSetup.supported_request(S.State.config(st), bytes), N.Ngap.any_ng_setup_response(acts), True{}, Equal.sym(Bool, N.Ngap.any_ng_setup_response(acts), N.NgSetup.supported_request(S.State.config(st), bytes), er), Req.skip(reset, acts, Req.reset(st, assoc), e1)), +o => w => e1 => Req.none(K.Kernel.actions(N.Step.of(st, o)), PL.Lv.no_response(st, K.Kernel.actions(N.Step.of(st, o)), PL.Lv.step_acts(st, o, w)), e1, {N.NgSetup.supported_request(S.State.config(st), bytes) == True{} : Bool}), +kind => +code => +ies => +ea => PL.Lv.ok_w(st, R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code)), PL.Lw.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_initial_ue_message(kind, code), ea)))(e)
