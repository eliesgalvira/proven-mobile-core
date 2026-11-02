import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../nas/security.bend as Sec
import ../tlv.bend as T
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../ausf.bend as Au
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/gmm.bend as Gmm
import ../amf/route.bend as R
import ../smf/n4.bend as Up
import ../smf/gsm.bend as Gsm
import ../LAWS.bend as L
import ./lib.bend as P
import ../crypto/kdf.bend as Kd

# Proofs of the step function's laws (tickets 16 to 18).

def Bool.or_false(a: Bool, e: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool(e))

def Bool.not_true(a: Bool, e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.Refute.bool(e))
    case False{}:
      {==}

# An undecodable PDU
# ------------------

def L.kernel.bad_pdu.only_error_indication(st, entropy, assoc, stream, len, bytes, err, e):
  se = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Fail{err}, e)
  %se : {R.Route.of_pdu(st, assoc, stream, entropy, _) == (st, N.Acts.render(N.Ngap.bad_pdu(assoc))) : S.Out()}
  {==}

# Sieves
# ------
# A row kept by a sieve is a row of the table, so what holds of every row of a
# table holds of every row of its sifting.

def Ues.none_keep(+a: U32, k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), b: Bool, eb: {Bool.not(U32.is_eq(S.Ue.assoc(v), a)) == b : Bool}, ih: {S.Ues.none_assoc(a, rest) == True{} : Bool}) -> {S.Ues.none_assoc(a, Tb.Table.keep(S.Ue, k, v, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Bool.not(U32.is_eq(S.Ue.assoc(v), a)), S.Ues.none_assoc(a, rest), eb, ih)
    case False{}:
      ih

def Ues.drop_none(+a: U32, ues: Tb.Table(S.Ue)) -> {S.Ues.none_assoc(a, S.Ues.drop_assoc(a, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (k, +v) <> +more:
      Ues.none_keep(a, k, v, S.Ues.drop_assoc(a, more), Bool.not(U32.is_eq(S.Ue.assoc(v), a)), {==}, Ues.drop_none(a, more))

def Clear.keep(+key: U32, +u: S.Ue, +k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), b: Bool, e1: {Bool.not(S.Row.conflicts(key, u, k, v)) == True{} : Bool}, ih: {S.Ues.clear(key, u, rest) == True{} : Bool}) -> {S.Ues.clear(key, u, Tb.Table.keep(S.Ue, k, v, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Bool.not(S.Row.conflicts(key, u, k, v)), S.Ues.clear(key, u, rest), e1, ih)
    case False{}:
      ih

def Clear.sift(+key: U32, +u: S.Ue, +s: S.Sieve, ues: Tb.Table(S.Ue), +e: {S.Ues.clear(key, u, ues) == True{} : Bool}) -> {S.Ues.clear(key, u, S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      Clear.keep(key, u, k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), P.Bool.and_true_l(Bool.not(S.Row.conflicts(key, u, k, v)), S.Ues.clear(key, u, more), e), Clear.sift(key, u, s, more, P.Bool.and_true_r(Bool.not(S.Row.conflicts(key, u, k, v)), S.Ues.clear(key, u, more), e)))

def Unique.keep(+key: U32, +u: S.Ue, +rest: Tb.Table(S.Ue), b: Bool, ec: {S.Ues.clear(key, u, rest) == True{} : Bool}, eu: {S.Ues.unique(rest) == True{} : Bool}) -> {S.Ues.unique(Tb.Table.keep(S.Ue, key, u, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(S.Ues.clear(key, u, rest), S.Ues.unique(rest), ec, eu)
    case False{}:
      eu

def Unique.sift(+s: S.Sieve, ues: Tb.Table(S.Ue), +e: {S.Ues.unique(ues) == True{} : Bool}) -> {S.Ues.unique(S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+key, +u) <> +more:
      Unique.keep(key, u, S.Ues.sift(s, more), S.Sieve.keeps(s, key, u), Clear.sift(key, u, s, more, P.Bool.and_true_l(S.Ues.clear(key, u, more), S.Ues.unique(more), e)), Unique.sift(s, more, P.Bool.and_true_r(S.Ues.clear(key, u, more), S.Ues.unique(more), e)))

# The rows the Clear sieve keeps are, by its definition, clear of the context.
def Clear.own_keep(+key: U32, +u: S.Ue, +k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), b: Bool, eb: {Bool.not(S.Row.conflicts(key, u, k, v)) == b : Bool}, ih: {S.Ues.clear(key, u, rest) == True{} : Bool}) -> {S.Ues.clear(key, u, Tb.Table.keep(S.Ue, k, v, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(Bool.not(S.Row.conflicts(key, u, k, v)), S.Ues.clear(key, u, rest), eb, ih)
    case False{}:
      ih

def Clear.own(+key: U32, +u: S.Ue, ues: Tb.Table(S.Ue)) -> {S.Ues.clear(key, u, S.Ues.sift(S.Clear{key, u}, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      Clear.own_keep(key, u, k, v, S.Ues.sift(S.Clear{key, u}, more), S.Sieve.keeps(S.Clear{key, u}, k, v), {==}, Clear.own(key, u, more))

# The Except sieve leaves no row under its key.
def Del.keep(+key: U32, +k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), b: Bool, eb: {Bool.not(U32.is_eq(k, key)) == b : Bool}, ih: {Tb.Table.get(S.Ue, key, rest) == None{} : Maybe<&2, S.Ue>}) -> {Tb.Table.get(S.Ue, key, Tb.Table.keep(S.Ue, k, v, rest, b)) == None{} : Maybe<&2, S.Ue>}:
  match b:
    case True{}:
      ne = Equal.sym(Bool, U32.is_eq(k, key), False{}, Bool.not_true(U32.is_eq(k, key), eb))
      %ne : {Tb.Table.hit(S.Ue, v, Tb.Table.get(S.Ue, key, rest), _) == None{} : Maybe<&2, S.Ue>}
      ih
    case False{}:
      ih

def Del.get(+key: U32, ues: Tb.Table(S.Ue)) -> {Tb.Table.get(S.Ue, key, S.Ues.del(key, ues)) == None{} : Maybe<&2, S.Ue>}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      Del.keep(key, k, v, S.Ues.sift(S.Except{key}, more), S.Sieve.keeps(S.Except{key}, k, v), {==}, Del.get(key, more))

def Sessions.drop_keep(+ue: U32, +k: U32, +s: S.Session, +rest: Tb.Table(S.Session), b: Bool, eb: {Bool.not(U32.is_eq(S.Session.ue(s), ue)) == b : Bool}, ih: {S.Sessions.sift(S.SOf{ue}, rest) == [] : Tb.Table(S.Session)}) -> {S.Sessions.sift(S.SOf{ue}, Tb.Table.keep(S.Session, k, s, rest, b)) == [] : Tb.Table(S.Session)}:
  match b:
    case True{}:
      ne = Equal.sym(Bool, U32.is_eq(S.Session.ue(s), ue), False{}, Bool.not_true(U32.is_eq(S.Session.ue(s), ue), eb))
      %ne : {Tb.Table.keep(S.Session, k, s, S.Sessions.sift(S.SOf{ue}, rest), _) == [] : Tb.Table(S.Session)}
      ih
    case False{}:
      ih

# No session of a UE is left once its sessions are dropped.
def Sessions.drop_none(+ue: U32, sessions: Tb.Table(S.Session)) -> {S.Sessions.of_ue(ue, S.Sessions.drop_ue(ue, sessions)) == [] : Tb.Table(S.Session)}:
  match sessions:
    case Nil{}:
      {==}
    case (+k, +s) <> +more:
      Sessions.drop_keep(ue, k, s, S.Sessions.sift(S.SOthers{ue}, more), S.SSieve.keeps(S.SOthers{ue}, k, s), {==}, Sessions.drop_none(ue, more))

# An association going down
# -------------------------

def L.amf.assoc_down.releases_all(st, entropy, assoc):
  match st:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      Ues.drop_none(assoc, ues)

# NG Setup answers only a supported request
# -----------------------------------------
# Every other path of the NgapData step is a UE procedure, whose actions are
# rendered from a type none of whose members is an NG Setup Response.

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

def Act.no_response(a: N.Act) -> {N.Ngap.is_ng_setup_response(N.Act.render(a)) == False{} : Bool}:
  match a:
    case N.DlNas{assoc, stream, key, ran_id, nas}:
      {==}
    case N.Ics{assoc, stream, key, ran_id, cfg, caps, k_gnb, nas}:
      {==}
    case N.PduSetup{assoc, stream, key, ran_id, psi, sst, nas, transfer}:
      {==}
    case N.Release{assoc, stream, key, ran_id, cause}:
      {==}
    case N.ErrInd{assoc, cause}:
      {==}
    case N.Pfcp{bytes}:
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

def Render.no_response(st: S.State, o: N.GOut()) -> {N.Ngap.any_ng_setup_response(K.Kernel.actions(N.render_out(st, o))) == False{} : Bool}:
  match o:
    case (tx, acts):
      Acts.no_response(acts)

def Req.d1(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool, e: {N.Ngap.any_ng_setup_response(K.Kernel.actions(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, ok))) == True{} : Bool}) -> {N.NgSetup.supported_d1(S.State.config(st), ies, ok) == True{} : Bool}:
  match ok:
    case True{}:
      Req.view(st, assoc, V.NGSetupRequest.view(ies), e)
    case False{}:
      ar = Render.no_response(st, R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n)))
      Empty.absurd({False{} == True{} : Bool}, P.Refute.bool((%ar : {_ == True{} : Bool}; e)))

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

# Registration, part 1 (ticket 17)
# --------------------------------

def L.amf.initial_ue.reject_leaves_state(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, err, ep, ei, ev):
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{0, 15, crit, value}}, ep)
  %sep : {R.Route.of_pdu(st, assoc, stream, entropy, _) == (st, N.Acts.render(N.Ngap.bad_view(assoc))) : S.Out()}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {R.Route.of_ies(st, assoc, stream, U32.to_nat(0), U32.to_nat(15), entropy, _) == (st, N.Acts.render(N.Ngap.bad_view(assoc))) : S.Out()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.InitialUEMessage.View>, V.InitialUEMessage.view(ies), Fail{err}, ev)
  %sev : {N.render_out(st, Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, _)) == (st, N.Acts.render(N.Ngap.bad_view(assoc))) : S.Out()}
  {==}

def L.ausf.res_star.full_length(av, res, e):
  match av:
    case Au.Av{+rand, autn, +xres_star, +hxres_star, k_ausf}:
      +R = Bool.and(B.bytes_eq(Kd.kdf.hres_star(rand, res), hxres_star), B.bytes_eq(res, xres_star))
      +e2 = P.Bool.and_true_r(Nat.is_eq(List.length(&2, U32, res), 16n), R, e)
      (P.Bool.and_true_l(Nat.is_eq(List.length(&2, U32, res), 16n), R, e), (P.Bool.and_true_l(B.bytes_eq(Kd.kdf.hres_star(rand, res), hxres_star), B.bytes_eq(res, xres_star), e2), P.Bool.and_true_r(B.bytes_eq(Kd.kdf.hres_star(rand, res), hxres_star), B.bytes_eq(res, xres_star), e2)))

# Every phase before registration carries its guard, so no context is left hanging.
def Ue.guarded(u: S.Ue) -> {S.Ue.guarded(u) == True{} : Bool}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      match phase:
        case S.Identifying{guard}:
          {==}
        case S.Authenticating{guard, av, resynced}:
          {==}
        case S.SecurityMode{guard, ctx, k_amf}:
          {==}
        case S.ContextSetup{guard, ctx, response, complete}:
          {==}
        case S.Registered{ctx}:
          {==}
        case S.Releasing{}:
          {==}

def Ues.guarded(ues: Tb.Table(S.Ue)) -> {S.Ues.guarded(ues) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (key, +u) <> +more:
      P.Bool.and_intro(S.Ue.guarded(u), S.Ues.guarded(more), Ue.guarded(u), Ues.guarded(more))

def L.amf.auth.guarded(st, ev, entropy):
  Ues.guarded(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))))

# Registration, part 2 (ticket 18)
# --------------------------------

def L.amf.registration.completes_or_releases(st, ev, entropy):
  Ues.guarded(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))))

# Only the owner releases
# -----------------------

def Owner.request(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), pdus: Maybe<&2, G.PDUSessionResourceListCxtRelReq()>, +cause: G.Cause, +ue: S.Ue, eu: {Tb.Table.get(S.Ue, N.Ngap.of_big(amf), S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, ea: {U32.is_eq(S.Ue.assoc(ue), assoc) == False{} : Bool}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 42, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.UEContextReleaseRequest.view(ies) == Done{V.UEContextReleaseRequest.View{amf, ran, pdus, cause}} : Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{0, 42, crit, value}}, ep)
  %sep : {K.Kernel.state(R.Route.of_pdu(st, assoc, stream, entropy, _)) == st : S.State}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {K.Kernel.state(R.Route.of_ies(st, assoc, stream, U32.to_nat(0), U32.to_nat(42), entropy, _)) == st : S.State}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>, V.UEContextReleaseRequest.view(ies), Done{V.UEContextReleaseRequest.View{amf, ran, pdus, cause}}, ev)
  %sev : {K.Kernel.state(N.render_out(st, Gmm.Gmm.release_request_of_view(st, assoc, _))) == st : S.State}
  seu = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, N.Ngap.of_big(amf), S.State.ues(st)), Some{ue}, eu)
  %seu : {K.Kernel.state(N.render_out(st, Gmm.Gmm.release_request_ue(st, assoc, N.Ngap.of_big(amf), cause, Gmm.Gmm.owner_of(_, assoc, ran)))) == st : S.State}
  sea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, ea)
  %sea : {K.Kernel.state(N.render_out(st, Gmm.Gmm.release_request_ue(st, assoc, N.Ngap.of_big(amf), cause, Gmm.Gmm.owner_if(ue, Bool.and(_, B.bytes_eq(S.Ue.ran_id(ue), ran)))))) == st : S.State}
  {==}

def Owner.complete(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), uli: Maybe<&2, G.UserLocationInformation>, rel: Maybe<&2, G.PDUSessionResourceListCxtRelCpl()>, diag: Maybe<&2, G.CriticalityDiagnostics>, +ue: S.Ue, eu: {Tb.Table.get(S.Ue, N.Ngap.of_big(amf), S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, ea: {U32.is_eq(S.Ue.assoc(ue), assoc) == False{} : Bool}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 41, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.UEContextReleaseComplete.view(ies) == Done{V.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}} : Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{1, 41, crit, value}}, ep)
  %sep : {K.Kernel.state(R.Route.of_pdu(st, assoc, stream, entropy, _)) == st : S.State}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {K.Kernel.state(R.Route.of_ies(st, assoc, stream, U32.to_nat(1), U32.to_nat(41), entropy, _)) == st : S.State}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>, V.UEContextReleaseComplete.view(ies), Done{V.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}}, ev)
  %sev : {K.Kernel.state(N.render_out(st, Gmm.Gmm.release_complete_of_view(st, assoc, _))) == st : S.State}
  seu = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, N.Ngap.of_big(amf), S.State.ues(st)), Some{ue}, eu)
  %seu : {K.Kernel.state(N.render_out(st, Gmm.Gmm.release_complete_ue(st, assoc, N.Ngap.of_big(amf), Gmm.Gmm.owner_of(_, assoc, ran)))) == st : S.State}
  sea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, ea)
  %sea : {K.Kernel.state(N.render_out(st, Gmm.Gmm.release_complete_ue(st, assoc, N.Ngap.of_big(amf), Gmm.Gmm.owner_if(ue, Bool.and(_, B.bytes_eq(S.Ue.ran_id(ue), ran)))))) == st : S.State}
  {==}

def L.amf.ue_context_release.owner_only(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, pdus, cause, uli, rel, diag, ue, eu, ea, ei):
  (ep => ev => Owner.request(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, pdus, cause, ue, eu, ea, ei, ep, ev), ep => ev => Owner.complete(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, uli, rel, diag, ue, eu, ea, ei, ep, ev))

# Release forgets
# ---------------

def Tx.forget_ue(+key: U32, n: U32, st: S.State) -> {Tb.Table.get(S.Ue, key, S.State.ues(S.Tx.apply(S.Both{S.Del{key}, S.BumpSeq{n}}, st))) == None{} : Maybe<&2, S.Ue>}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      Del.get(key, ues)

def Tx.forget_sessions(+key: U32, n: U32, st: S.State) -> {S.Sessions.of_ue(key, S.State.sessions(S.Tx.apply(S.Both{S.Del{key}, S.BumpSeq{n}}, st))) == [] : Tb.Table(S.Session)}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      Sessions.drop_none(key, sessions)

def L.amf.release.forgets_ue(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, uli, rel, diag, ue, ep, ei, ev, eo):
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{1, 41, crit, value}}, ep)
  %sep : {Tb.Table.get(S.Ue, N.Ngap.of_big(amf), S.State.ues(K.Kernel.state(R.Route.of_pdu(st, assoc, stream, entropy, _)))) == None{} : Maybe<&2, S.Ue>} & {S.Sessions.of_ue(N.Ngap.of_big(amf), S.State.sessions(K.Kernel.state(R.Route.of_pdu(st, assoc, stream, entropy, _)))) == [] : Tb.Table(S.Session)}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {Tb.Table.get(S.Ue, N.Ngap.of_big(amf), S.State.ues(K.Kernel.state(R.Route.of_ies(st, assoc, stream, U32.to_nat(1), U32.to_nat(41), entropy, _)))) == None{} : Maybe<&2, S.Ue>} & {S.Sessions.of_ue(N.Ngap.of_big(amf), S.State.sessions(K.Kernel.state(R.Route.of_ies(st, assoc, stream, U32.to_nat(1), U32.to_nat(41), entropy, _)))) == [] : Tb.Table(S.Session)}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>, V.UEContextReleaseComplete.view(ies), Done{V.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}}, ev)
  %sev : {Tb.Table.get(S.Ue, N.Ngap.of_big(amf), S.State.ues(K.Kernel.state(N.render_out(st, Gmm.Gmm.release_complete_of_view(st, assoc, _))))) == None{} : Maybe<&2, S.Ue>} & {S.Sessions.of_ue(N.Ngap.of_big(amf), S.State.sessions(K.Kernel.state(N.render_out(st, Gmm.Gmm.release_complete_of_view(st, assoc, _))))) == [] : Tb.Table(S.Session)}
  seo = Equal.sym(Maybe<&2, S.Ue>, Gmm.Gmm.owner(st, assoc, N.Ngap.of_big(amf), ran), Some{ue}, eo)
  %seo : {Tb.Table.get(S.Ue, N.Ngap.of_big(amf), S.State.ues(K.Kernel.state(N.render_out(st, Gmm.Gmm.release_complete_ue(st, assoc, N.Ngap.of_big(amf), _))))) == None{} : Maybe<&2, S.Ue>} & {S.Sessions.of_ue(N.Ngap.of_big(amf), S.State.sessions(K.Kernel.state(N.render_out(st, Gmm.Gmm.release_complete_ue(st, assoc, N.Ngap.of_big(amf), _))))) == [] : Tb.Table(S.Session)}
  (Tx.forget_ue(N.Ngap.of_big(amf), Up.N4.deletion_count(S.Sessions.of_ue(N.Ngap.of_big(amf), S.State.sessions(st))), st), Tx.forget_sessions(N.Ngap.of_big(amf), Up.N4.deletion_count(S.Sessions.of_ue(N.Ngap.of_big(amf), S.State.sessions(st))), st))

# A phase change in place leaves every conflict as it was.
def Ue.conflicts_rephase(hit: Bool, u: S.Ue, v: S.Ue, p: S.Phase) -> {S.Ue.conflicts(u, S.Ue.rephase_if(v, p, hit)) == S.Ue.conflicts(u, v) : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      match v:
        case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
          {==}

def Ue.conflicts_rephase_l(hit: Bool, u: S.Ue, v: S.Ue, p: S.Phase) -> {S.Ue.conflicts(S.Ue.rephase_if(u, p, hit), v) == S.Ue.conflicts(u, v) : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      match u:
        case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
          {==}

def Row.conflicts_rephase(key: U32, u: S.Ue, k: U32, v: S.Ue, p: S.Phase, hit: Bool) -> {S.Row.conflicts(key, u, k, S.Ue.rephase_if(v, p, hit)) == S.Row.conflicts(key, u, k, v) : Bool}:
  e = Equal.sym(Bool, S.Ue.conflicts(u, S.Ue.rephase_if(v, p, hit)), S.Ue.conflicts(u, v), Ue.conflicts_rephase(hit, u, v, p))
  %e : {Bool.or(U32.is_eq(k, key), _) == Bool.or(U32.is_eq(k, key), S.Ue.conflicts(u, v)) : Bool}
  {==}

def Row.conflicts_rephase_l(key: U32, u: S.Ue, k: U32, v: S.Ue, p: S.Phase, hit: Bool) -> {S.Row.conflicts(key, S.Ue.rephase_if(u, p, hit), k, v) == S.Row.conflicts(key, u, k, v) : Bool}:
  e = Equal.sym(Bool, S.Ue.conflicts(S.Ue.rephase_if(u, p, hit), v), S.Ue.conflicts(u, v), Ue.conflicts_rephase_l(hit, u, v, p))
  %e : {Bool.or(U32.is_eq(k, key), _) == Bool.or(U32.is_eq(k, key), S.Ue.conflicts(u, v)) : Bool}
  {==}

def Clear.rephase(+key2: U32, +u: S.Ue, +key: U32, +p: S.Phase, ues: Tb.Table(S.Ue)) -> {S.Ues.clear(key2, u, S.Ues.rephase(key, p, ues)) == S.Ues.clear(key2, u, ues) : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      e1 = Equal.sym(Bool, S.Row.conflicts(key2, u, k, S.Ue.rephase_if(v, p, U32.is_eq(k, key))), S.Row.conflicts(key2, u, k, v), Row.conflicts_rephase(key2, u, k, v, p, U32.is_eq(k, key)))
      %e1 : {Bool.and(Bool.not(_), S.Ues.clear(key2, u, S.Ues.rephase(key, p, more))) == Bool.and(Bool.not(S.Row.conflicts(key2, u, k, v)), S.Ues.clear(key2, u, more)) : Bool}
      e2 = Equal.sym(Bool, S.Ues.clear(key2, u, S.Ues.rephase(key, p, more)), S.Ues.clear(key2, u, more), Clear.rephase(key2, u, key, p, more))
      %e2 : {Bool.and(Bool.not(S.Row.conflicts(key2, u, k, v)), _) == Bool.and(Bool.not(S.Row.conflicts(key2, u, k, v)), S.Ues.clear(key2, u, more)) : Bool}
      {==}

def Clear.subject_rephase(+key: U32, +u: S.Ue, +p: S.Phase, +hit: Bool, ues: Tb.Table(S.Ue)) -> {S.Ues.clear(key, S.Ue.rephase_if(u, p, hit), ues) == S.Ues.clear(key, u, ues) : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      e1 = Equal.sym(Bool, S.Row.conflicts(key, S.Ue.rephase_if(u, p, hit), k, v), S.Row.conflicts(key, u, k, v), Row.conflicts_rephase_l(key, u, k, v, p, hit))
      %e1 : {Bool.and(Bool.not(_), S.Ues.clear(key, S.Ue.rephase_if(u, p, hit), more)) == Bool.and(Bool.not(S.Row.conflicts(key, u, k, v)), S.Ues.clear(key, u, more)) : Bool}
      e2 = Equal.sym(Bool, S.Ues.clear(key, S.Ue.rephase_if(u, p, hit), more), S.Ues.clear(key, u, more), Clear.subject_rephase(key, u, p, hit, more))
      %e2 : {Bool.and(Bool.not(S.Row.conflicts(key, u, k, v)), _) == Bool.and(Bool.not(S.Row.conflicts(key, u, k, v)), S.Ues.clear(key, u, more)) : Bool}
      {==}

def Unique.rephase(+key: U32, +p: S.Phase, ues: Tb.Table(S.Ue)) -> {S.Ues.unique(S.Ues.rephase(key, p, ues)) == S.Ues.unique(ues) : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      e1 = Equal.sym(Bool, S.Ues.clear(k, S.Ue.rephase_if(u, p, U32.is_eq(k, key)), S.Ues.rephase(key, p, more)), S.Ues.clear(k, u, S.Ues.rephase(key, p, more)), Clear.subject_rephase(k, u, p, U32.is_eq(k, key), S.Ues.rephase(key, p, more)))
      %e1 : {Bool.and(_, S.Ues.unique(S.Ues.rephase(key, p, more))) == Bool.and(S.Ues.clear(k, u, more), S.Ues.unique(more)) : Bool}
      e2 = Equal.sym(Bool, S.Ues.clear(k, u, S.Ues.rephase(key, p, more)), S.Ues.clear(k, u, more), Clear.rephase(k, u, key, p, more))
      %e2 : {Bool.and(_, S.Ues.unique(S.Ues.rephase(key, p, more))) == Bool.and(S.Ues.clear(k, u, more), S.Ues.unique(more)) : Bool}
      e3 = Equal.sym(Bool, S.Ues.unique(S.Ues.rephase(key, p, more)), S.Ues.unique(more), Unique.rephase(key, p, more))
      %e3 : {Bool.and(S.Ues.clear(k, u, more), _) == Bool.and(S.Ues.clear(k, u, more), S.Ues.unique(more)) : Bool}
      {==}

# Indexes stay unique
# -------------------
# Every state change of a UE procedure is a transaction, and each transaction
# keeps the table unique: a Put is a clear row in front of a sifting, a
# Rephase changes no identity, a Del a sifting, the rest leave the table alone.

def Tx.unique(tx: S.Tx, +st: S.State, e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(S.Tx.apply(tx, st))) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      e
    case S.Put{+key, +ue}:
      match st:
        case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          P.Bool.and_intro(S.Ues.clear(key, ue, S.Ues.sift(S.Clear{key, ue}, ues)), S.Ues.unique(S.Ues.sift(S.Clear{key, ue}, ues)), Clear.own(key, ue, ues), Unique.sift(S.Clear{key, ue}, ues, e))
    case S.Rephase{+key, +phase}:
      match st:
        case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          er = Equal.sym(Bool, S.Ues.unique(S.Ues.rephase(key, phase, ues)), S.Ues.unique(ues), Unique.rephase(key, phase, ues))
          %er : {_ == True{} : Bool}
          e
    case S.Del{+key}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          Unique.sift(S.Except{key}, ues, e)
    case S.PutSession{key, s}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.Revar{key, v}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.DelSession{key}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.Subs{new}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.SetLink{link}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.BumpUe{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.BumpTimer{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.BumpSeq{n}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e
    case S.Both{+first, second}:
      Tx.unique(second, S.Tx.apply(first, st), Tx.unique(first, st, e))

def Render.unique(st: S.State, o: N.GOut(), e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(K.Kernel.state(N.render_out(st, o)))) == True{} : Bool}:
  match o:
    case (tx, acts):
      Tx.unique(tx, st, e)

def Setup.unique(+st: S.State, +assoc: U32, r: Result<&2, &2, B.Err, V.NGSetupRequest.View>, e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(K.Kernel.state(N.NgSetup.of_view(st, assoc, r)))) == True{} : Bool}:
  match r:
    case Fail{err}:
      e
    case Done{v}:
      e

def Route.d1_unique(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, +ies: List<&2, Fr.Ie>, entropy: B.Bytes(), ok: Bool, e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(K.Kernel.state(R.Route.d1(st, assoc, stream, kind, code, ies, entropy, ok)))) == True{} : Bool}:
  match ok:
    case True{}:
      Setup.unique(st, assoc, V.NGSetupRequest.view(ies), e)
    case False{}:
      Render.unique(st, R.Route.d2(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 15n)), e)

def Route.ies_unique(+st: S.State, +assoc: U32, stream: U32, +kind: Nat, +code: Nat, entropy: B.Bytes(), r: Ap.Rd(List<&2, Fr.Ie>), e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(K.Kernel.state(R.Route.of_ies(st, assoc, stream, kind, code, entropy, r)))) == True{} : Bool}:
  match r:
    case Fail{err}:
      e
    case Done{(+ies, c)}:
      Route.d1_unique(st, assoc, stream, kind, code, ies, entropy, N.Ngap.is_procedure(kind, code, 0n, 21n), e)

def Route.pdu_unique(+st: S.State, +assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Fr.Pdu>, e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(K.Kernel.state(R.Route.of_pdu(st, assoc, stream, entropy, r)))) == True{} : Bool}:
  match r:
    case Fail{err}:
      e
    case Done{Fr.Pdu{kind, code, crit, value}}:
      Route.ies_unique(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), e)

def Config.unique(complete: Bool, st: S.State, tlvs: List<&2, T.Tlv>, entropy: B.Bytes(), e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(K.Kernel.state(K.Kernel.config(complete, st, tlvs, entropy)))) == True{} : Bool}:
  match complete:
    case False{}:
      e
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
          e

def AssocUp.unique(st: S.State, assoc: U32, e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(K.Kernel.state(K.Kernel.assoc_up(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      e

def Down.unique(st: S.State, +assoc: U32, e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(K.Kernel.state(K.Kernel.assoc_down(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, n4}:
      Unique.sift(S.Others{assoc}, ues, e)

def Step.unique(+st: S.State, ev: F.Evt, +entropy: B.Bytes(), e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy)))) == True{} : Bool}:
  match ev:
    case F.Config{len, +tlvs}:
      Config.unique(S.Cfg.complete(tlvs), st, tlvs, entropy, e)
    case F.NgapAssocUp{assoc}:
      AssocUp.unique(st, assoc, e)
    case F.NgapAssocDown{assoc}:
      Down.unique(st, assoc, e)
    case F.NgapData{assoc, stream, len, bytes}:
      Route.pdu_unique(st, assoc, stream, entropy, Fr.Pdu.read(bytes), e)
    case F.PfcpData{len, bytes}:
      Render.unique(st, Gsm.Gsm.pfcp_data(st, bytes), e)
    case F.TimerFired{timer}:
      Render.unique(st, K.Kernel.fired(st, timer), e)

def L.amf.indexes.unique(st, ev, entropy, e):
  ({==}, Step.unique(st, ev, entropy, e))

# Plaintext after security
# ------------------------

def L.amf.nas.plaintext_after_security(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, nas, uli, ue, ctx, err, ep, ei, ev, eo, ec, ef):
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{0, 46, crit, value}}, ep)
  %sep : {K.Kernel.state(R.Route.of_pdu(st, assoc, stream, entropy, _)) == st : S.State}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {K.Kernel.state(R.Route.of_ies(st, assoc, stream, U32.to_nat(0), U32.to_nat(46), entropy, _)) == st : S.State}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UplinkNASTransport.View>, V.UplinkNASTransport.view(ies), Done{V.UplinkNASTransport.View{amf, ran, nas, uli}}, ev)
  %sev : {K.Kernel.state(N.render_out(st, Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, _))) == st : S.State}
  seo = Equal.sym(Maybe<&2, S.Ue>, Gmm.Gmm.owner(st, assoc, N.Ngap.of_big(amf), ran), Some{ue}, eo)
  %seo : {K.Kernel.state(N.render_out(st, Gmm.Gmm.uplink_ue(st, assoc, N.Ngap.of_big(amf), nas, entropy, _))) == st : S.State}
  sec = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.ctx(S.Ue.phase(ue)), Some{ctx}, ec)
  %sec : {K.Kernel.state(N.render_out(st, Gmm.Gmm.secured(st, N.Ngap.of_big(amf), ue, entropy, nas, _))) == st : S.State}
  sef = Equal.sym(Result<&2, &2, B.Err, Sec.Nas.Unprotected>, Sec.Nas.unprotect(ctx, nas), Fail{err}, ef)
  %sef : {K.Kernel.state(N.render_out(st, Gmm.Gmm.opened(st, N.Ngap.of_big(amf), ue, entropy, _))) == st : S.State}
  {==}
