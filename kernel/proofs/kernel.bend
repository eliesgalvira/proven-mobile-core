import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../ausf.bend as Au
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/gmm.bend as Gmm
import ../amf/route.bend as R
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
  %se : {R.Route.of_pdu(st, assoc, stream, entropy, _) == (st, N.Ngap.bad_pdu(assoc)) : S.Out()}
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

def Kernel.released_out_ues(config: Maybe<&2, S.Cfg>, subs: List<&2, Au.Subscriber>, assocs: List<&2, U32>, +ues: Tb.Table(S.Ue), kept: Tb.Table(S.Session), nu: U32, nt: U32, rec: B.Bytes(), r: Sigma<&2, &2, List<&2, F.Action>, _ => U32>) -> {S.State.ues(K.Kernel.state(K.Kernel.released_out(config, subs, assocs, ues, kept, nu, nt, rec, r))) == ues : Tb.Table(S.Ue)}:
  match r:
    case (actions, seq):
      {==}

def Kernel.released_ues(config: Maybe<&2, S.Cfg>, subs: List<&2, Au.Subscriber>, assocs: List<&2, U32>, +ues: Tb.Table(S.Ue), nu: U32, nt: U32, rec: B.Bytes(), split: Sigma<&2, &2, Tb.Table(S.Session), _ => List<&2, S.Session>>, seq: U32) -> {S.State.ues(K.Kernel.state(K.Kernel.released(config, subs, assocs, ues, nu, nt, rec, split, seq))) == ues : Tb.Table(S.Ue)}:
  match split:
    case (kept, gone):
      Kernel.released_out_ues(config, subs, assocs, ues, kept, nu, nt, rec, K.Kernel.deletions(gone, seq))

def L.amf.assoc_down.releases_all(st, entropy, assoc):
  match st:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, next_timer, recovery}:
      +left = S.Ues.drop_assoc(assoc, ues)
      ru = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(K.Kernel.released(config, subs, S.Assocs.drop(assoc, assocs), left, next_ue, next_timer, recovery, S.Sessions.partition(left, sessions), pfcp_seq))), left, Kernel.released_ues(config, subs, S.Assocs.drop(assoc, assocs), left, next_ue, next_timer, recovery, S.Sessions.partition(left, sessions), pfcp_seq))
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

# Every semantic action of a UE procedure renders to something other than an
# NG Setup Response: one lemma covers every branch of those procedures.
def Act.no_response(a: N.Act) -> {N.Ngap.is_ng_setup_response(N.Act.render(a)) == False{} : Bool}:
  match a:
    case N.DlNas{assoc, stream, key, ran_id, nas}:
      {==}
    case N.Release{assoc, stream, key, ran_id, cause}:
      {==}
    case N.ErrInd{assoc, cause}:
      {==}
    case N.Note{level, text}:
      {==}
    case N.TimerStart{timer, ms}:
      {==}
    case N.TimerCancel{timer}:
      {==}

def Acts.no_response(acts: List<&2, N.Act>) -> {N.Ngap.any_ng_setup_response(N.Acts.render(acts)) == False{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case a <> more:
      ea = Equal.sym(Bool, N.Ngap.is_ng_setup_response(N.Act.render(a)), False{}, Act.no_response(a))
      %ea : {Bool.or(_, N.Ngap.any_ng_setup_response(N.Acts.render(more))) == False{} : Bool}
      Acts.no_response(more)

def Render.no_response(o: N.GOut()) -> {N.Ngap.any_ng_setup_response(K.Kernel.actions(N.render_out(o))) == False{} : Bool}:
  match o:
    case (st, acts):
      Acts.no_response(acts)

def Req.d3(+st: S.State, +assoc: U32, stream: U32, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.d3(st, assoc, stream, ies, entropy, ok))) == True{} : Bool}) -> Empty:
  match ok:
    case True{}:
      ar = Render.no_response(Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, V.UplinkNASTransport.view(ies)))
      P.Refute.bool((%ar : {_ == True{} : Bool}; e))
    case False{}:
      P.Refute.bool(e)

def Req.d2(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.d2(st, assoc, stream, kind, code, ies, entropy, ok))) == True{} : Bool}) -> Empty:
  match ok:
    case True{}:
      ar = Render.no_response(Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, V.InitialUEMessage.view(ies)))
      P.Refute.bool((%ar : {_ == True{} : Bool}; e))
    case False{}:
      Req.d3(st, assoc, stream, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 46n), e)

def Req.d1(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, ok))) == True{} : Bool}) -> {N.NgSetup.supported_d1(S.State.config(st), ies, ok) == True{} : Bool}:
  match ok:
    case True{}:
      Req.view(st, assoc, V.NGSetupRequest.view(ies), e)
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Req.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n), e))

def Req.ies(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, entropy: B.Bytes(), r: Ap.Rd(List<&2, Fr.Ie>), e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r))) == True{} : Bool}) -> {N.NgSetup.supported_ies(S.State.config(st), kind, code, r) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Done{(+ies, c)}:
      Req.d1(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 21n), e)

def Req.pdu(+st: S.State, +assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Fr.Pdu>, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.of_pdu(st, assoc, stream, entropy, r))) == True{} : Bool}) -> {N.NgSetup.supported_pdu(S.State.config(st), r) == True{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Req.ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), e)

def L.amf.ng_setup.requires_supported_plmn(st, entropy, assoc, stream, len, bytes, e):
  Req.pdu(st, assoc, stream, entropy, Fr.Pdu.read(bytes), e)
