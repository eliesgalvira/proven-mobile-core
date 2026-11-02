import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ../LAWS.bend as L
import ./lib.bend as P

# Proofs of the step function's laws (ticket 16).

def Bool.or_false(a: Bool, e: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))

# An undecodable PDU
# ------------------

def L.kernel.bad_pdu.only_error_indication(st, entropy, assoc, stream, len, bytes, err, e):
  se = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Fail{err}, e)
  %se : {N.Ngap.of_pdu(st, assoc, stream, _) == (st, N.Ngap.bad_pdu(assoc)) : S.Out()}
  {==}

# An association going down
# -------------------------

def Ues.drop_none.row(+a: U32, key: U32, +u: S.Ue, rest: Tb.Table(S.Ue), ih: {S.Ues.none_assoc(a, rest) == True{} : Bool}, other: Bool, eo: {Bool.not(U32.is_eq(S.Ue.assoc(u), a)) == other : Bool}) -> {S.Ues.none_assoc(a, S.Ues.keep_row(key, u, rest, other)) == True{} : Bool}:
  match other:
    case True{}:
      P.Bool.and_intro(Bool.not(U32.is_eq(S.Ue.assoc(u), a)), S.Ues.none_assoc(a, rest), eo, ih)
    case False{}:
      ih

def Ues.drop_none(+a: U32, ues: Tb.Table(S.Ue)) -> {S.Ues.none_assoc(a, S.Ues.drop_assoc(a, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (key, +u) <> +more:
      Ues.drop_none.row(a, key, u, S.Ues.drop_assoc(a, more), Ues.drop_none(a, more), Bool.not(U32.is_eq(S.Ue.assoc(u), a)), {==})

def Kernel.released_out_ues(config: Maybe<&2, S.Cfg>, assocs: List<&2, U32>, +ues: Tb.Table(S.Ue), kept: Tb.Table(S.Session), nu: U32, nt: U32, rec: B.Bytes(), r: Sigma<&2, &2, List<&2, F.Action>, _ => U32>) -> {S.State.ues(K.Kernel.state(K.Kernel.released_out(config, assocs, ues, kept, nu, nt, rec, r))) == ues : Tb.Table(S.Ue)}:
  match r:
    case (actions, seq):
      {==}

def Kernel.released_ues(config: Maybe<&2, S.Cfg>, assocs: List<&2, U32>, +ues: Tb.Table(S.Ue), nu: U32, nt: U32, rec: B.Bytes(), split: Sigma<&2, &2, Tb.Table(S.Session), _ => List<&2, S.Session>>, seq: U32) -> {S.State.ues(K.Kernel.state(K.Kernel.released(config, assocs, ues, nu, nt, rec, split, seq))) == ues : Tb.Table(S.Ue)}:
  match split:
    case (kept, gone):
      Kernel.released_out_ues(config, assocs, ues, kept, nu, nt, rec, K.Kernel.deletions(gone, seq))

def L.amf.assoc_down.releases_all(st, entropy, assoc):
  match st:
    case S.State{config, assocs, +ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      +left = S.Ues.drop_assoc(assoc, ues)
      ru = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(K.Kernel.released(config, S.Assocs.drop(assoc, assocs), left, next_ue, next_timer, recovery, S.Sessions.partition(left, sessions), pfcp_seq))), left, Kernel.released_ues(config, S.Assocs.drop(assoc, assocs), left, next_ue, next_timer, recovery, S.Sessions.partition(left, sessions), pfcp_seq))
      %ru : {S.Ues.none_assoc(assoc, _) == True{} : Bool}
      Ues.drop_none(assoc, ues)

# NG Setup answers only a supported request
# -----------------------------------------
# Every other path of the NgapData step emits a closed list of actions, none of
# which is an NG Setup Response; the checker evaluates those.

def Req.answer(cfg: S.Cfg, +assoc: U32, b: Bool, e: {N.Ngap.is_ng_setup_response(N.Ngap.send(assoc, 0, N.NgSetup.answer(cfg, b))) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))

def Req.reply(config: Maybe<&2, S.Cfg>, +assoc: U32, v: V.NGSetupRequest.View, e: {N.Ngap.is_ng_setup_response(N.Ngap.send(assoc, 0, N.NgSetup.reply(config, v))) == True{} : Bool}) -> {N.NgSetup.supported_view(config, v) == True{} : Bool}:
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
      Req.reply(S.State.config(st), assoc, v, Bool.or_false(N.Ngap.is_ng_setup_response(N.Ngap.send(assoc, 0, N.NgSetup.reply(S.State.config(st), v))), e))

def Req.d1(+st: S.State, +assoc: U32, stream: U32, ies: List<&2, Fr.Ie>, ok: Bool, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(N.Ngap.d1(st, assoc, stream, ies, ok))) == True{} : Bool}) -> {N.NgSetup.supported_d1(S.State.config(st), ies, ok) == True{} : Bool}:
  match ok:
    case True{}:
      Req.view(st, assoc, V.NGSetupRequest.view(ies), e)
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))

def Req.ies(+st: S.State, +assoc: U32, stream: U32, kind: Nat, code: Nat, r: Ap.Rd(List<&2, Fr.Ie>), e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(N.Ngap.of_ies(st, assoc, stream, kind, code, r))) == True{} : Bool}) -> {N.NgSetup.supported_ies(S.State.config(st), kind, code, r) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Done{(ies, c)}:
      Req.d1(st, assoc, stream, ies, N.Ngap.is_procedure(kind, code, 0n, 21n), e)

def Req.pdu(+st: S.State, +assoc: U32, stream: U32, r: Result<&2, &2, B.Err, Fr.Pdu>, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(N.Ngap.of_pdu(st, assoc, stream, r))) == True{} : Bool}) -> {N.NgSetup.supported_pdu(S.State.config(st), r) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Req.ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), e)

def L.amf.ng_setup.requires_supported_plmn(st, entropy, assoc, stream, len, bytes, e):
  Req.pdu(st, assoc, stream, Fr.Pdu.read(bytes), e)
