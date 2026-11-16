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
import ../amf/handover.bend as Ho
import ../smf/n4.bend as Up
import ../smf/gsm.bend as Gsm
import ../LAWS.bend as L
import ./lib.bend as P
import ./walk.bend as PW
import ../crypto/kdf.bend as Kd
import ../plmn.bend as Pl

# Proofs of the step function's laws (tickets 16 to 18).

# A transaction that keeps every session row
# -------------------------------------------
# A key no session row holds after it held none before.

def Re.none_row(+r: S.Session, +t: S.Session, +a: Maybe<&2, S.Session>, +b: Maybe<&2, S.Session>, +c: Bool, +eh: {Tb.Table.hit(S.Session, r, a, c) == None{} : Maybe<&2, S.Session>}, ih: {a == None{} : Maybe<&2, S.Session>} -> {b == None{} : Maybe<&2, S.Session>}) -> {Tb.Table.hit(S.Session, t, b, c) == None{} : Maybe<&2, S.Session>}:
  match c:
    case True{}:
      Empty.absurd({Some{t} == None{} : Maybe<&2, S.Session>}, P.Refute.none_some(S.Session, r, Equal.sym(Maybe<&2, S.Session>, Some{r}, None{}, eh)))
    case False{}:
      ih(eh)

def Re.none(+key: U32, +v: S.SVar, ss: Tb.Table(S.Session), +k: U32, +eh: {Tb.Table.get(S.Session, k, S.Sessions.revar(key, v, ss)) == None{} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, k, ss) == None{} : Maybe<&2, S.Session>}:
  match ss:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      Re.none_row(S.Session.revar_if(t, v, Bool.and(U32.is_eq(k0, key), S.SVar.follows(v, t))), t, Tb.Table.get(S.Session, k, S.Sessions.revar(key, v, more)), Tb.Table.get(S.Session, k, more), U32.is_eq(k0, k), eh, e => Re.none(key, v, more, k, e))

def Tx.kept(+tx: S.Tx, +st: S.State, +e: {S.Tx.keeps_sessions(tx) == True{} : Bool}, +k: U32, +eh: {Tb.Table.get(S.Session, k, S.State.sessions(S.Tx.apply(tx, st))) == None{} : Maybe<&2, S.Session>}) -> {Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}:
  match tx:
    case S.Keep{}:
      eh
    case S.Put{key, ue}:
      Empty.absurd({Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}, P.Refute.bool(e))
    case S.Rephase{key, phase}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          eh
    case S.Del{key}:
      Empty.absurd({Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}, P.Refute.bool(e))
    case S.PutSession{key, s}:
      Empty.absurd({Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}, P.Refute.bool(e))
    case S.Revar{+key, +v}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          Re.none(key, v, sessions, k, eh)
    case S.DelSession{key}:
      Empty.absurd({Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}, P.Refute.bool(e))
    case S.Subs{new}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          eh
    case S.SetLink{link}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          eh
    case S.BumpUe{bk}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          eh
    case S.BumpSeq{n}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          eh
    case S.Both{+first, +second}:
      +ef = P.Bool.and_true_l(S.Tx.keeps_sessions(first), S.Tx.keeps_sessions(second), e)
      +es = P.Bool.and_true_r(S.Tx.keeps_sessions(first), S.Tx.keeps_sessions(second), e)
      Tx.kept(first, st, ef, k, Tx.kept(second, S.Tx.apply(first, st), es, k, eh))

# An undecodable PDU
# ------------------

def L.kernel.bad_pdu.only_error_indication(st, entropy, assoc, stream, len, bytes, err, e):
  se = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Fail{err}, e)
  %se : {R.Route.of_pdu(st, assoc, stream, entropy, _) == (st, N.Ngap.bad_pdu(assoc)) : N.Step()}
  {==}

def L.amf.ng_setup.first(st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, ep, ei, en, ea):
  PW.Rt.refused(st, entropy, assoc, stream, len, bytes, kind, code, crit, value, ies, c, ep, ei, en, ea)

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
      ne = Equal.sym(Bool, U32.is_eq(k, key), False{}, P.Bool.not_true(U32.is_eq(k, key), eb))
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

def Sessions.drop_keep(+ue: U32, +k: U32, +s: S.Session, +rest: Tb.Table(S.Session), b: Bool, eb: {Bool.not(S.Maybe.same_u32(S.Session.tag(s), Some{ue})) == b : Bool}, ih: {S.Sessions.sift(S.SOf{ue}, rest) == [] : Tb.Table(S.Session)}) -> {S.Sessions.sift(S.SOf{ue}, Tb.Table.keep(S.Session, k, s, rest, b)) == [] : Tb.Table(S.Session)}:
  match b:
    case True{}:
      ne = Equal.sym(Bool, S.Maybe.same_u32(S.Session.tag(s), Some{ue}), False{}, P.Bool.not_true(S.Maybe.same_u32(S.Session.tag(s), Some{ue}), eb))
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

def Down.none(+st: S.State, +assoc: U32) -> {S.Ues.none_assoc(assoc, S.State.ues(K.Kernel.state(R.Route.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, n4}:
      Ues.drop_none(assoc, ues)

# The handovers the association takes part in end first (Ho.Ho.down); then
# its contexts go.
def L.amf.assoc_down.releases_all(st, entropy, assoc):
  Down.none(K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, assoc))), assoc)

# Registration, part 1 (ticket 17)
# --------------------------------

def L.amf.initial_ue.reject_leaves_state(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, err, ep, ei, ev, eup):
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(0), U32.to_nat(15), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(0), U32.to_nat(15)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 0, 15, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {_ == (st, N.Ngap.bad_view(assoc)) : N.Step()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.InitialUEMessage.View>, V.InitialUEMessage.view(ies), Fail{err}, ev)
  %sev : {N.Step.of(st, Gmm.Gmm.initial_of_view(st, assoc, stream, entropy, _)) == (st, N.Ngap.bad_view(assoc)) : N.Step()}
  {==}

def L.ausf.res_star.full_length(av, res, e):
  match av:
    case Au.Av{+rand, autn, +xres_star, +hxres_star, k_ausf}:
      +R = Bool.and(B.bytes_eq(Kd.kdf.hres_star(rand, res), hxres_star), B.bytes_eq(res, xres_star))
      +e2 = P.Bool.and_true_r(Nat.is_eq(List.length(&2, U32, res), 16n), R, e)
      (P.Bool.and_true_l(Nat.is_eq(List.length(&2, U32, res), 16n), R, e), (P.Bool.and_true_l(B.bytes_eq(Kd.kdf.hres_star(rand, res), hxres_star), B.bytes_eq(res, xres_star), e2), P.Bool.and_true_r(B.bytes_eq(Kd.kdf.hres_star(rand, res), hxres_star), B.bytes_eq(res, xres_star), e2)))

# An AMF-UE-NGAP-ID ue_key gives no key for
# ------------------------------------------

def Unknown.request(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), pdus: Maybe<&2, G.PDUSessionResourceListCxtRelReq()>, +cause: G.Cause, eid: {N.Ngap.ue_key(amf) == None{} : Maybe<&2, U32>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 42, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.UEContextReleaseRequest.view(ies) == Done{V.UEContextReleaseRequest.View{amf, ran, pdus, cause}} : Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(0), U32.to_nat(42), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(0), U32.to_nat(42)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 0, 42, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {_ == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>, V.UEContextReleaseRequest.view(ies), Done{V.UEContextReleaseRequest.View{amf, ran, pdus, cause}}, ev)
  %sev : {N.Step.of(st, Gmm.Gmm.release_request_of_view(st, assoc, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), None{}, eid)
  %sek : {N.Step.of(st, Gmm.Gmm.release_request_key(st, assoc, ran, cause, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  {==}

def Unknown.complete(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), uli: Maybe<&2, G.UserLocationInformation>, rel: Maybe<&2, G.PDUSessionResourceListCxtRelCpl()>, diag: Maybe<&2, G.CriticalityDiagnostics>, eid: {N.Ngap.ue_key(amf) == None{} : Maybe<&2, U32>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 41, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.UEContextReleaseComplete.view(ies) == Done{V.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}} : Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(1), U32.to_nat(41), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(1), U32.to_nat(41)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 1, 41, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {_ == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>, V.UEContextReleaseComplete.view(ies), Done{V.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}}, ev)
  %sev : {N.Step.of(st, Gmm.Gmm.release_complete_of_view(st, assoc, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), None{}, eid)
  %sek : {N.Step.of(st, Gmm.Gmm.release_complete_key(st, assoc, ran, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  {==}

def Unknown.ics(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), diag: Maybe<&2, G.CriticalityDiagnostics>, eid: {N.Ngap.ue_key(amf) == None{} : Maybe<&2, U32>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 14, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.InitialContextSetupResponse.view(ies) == Done{V.InitialContextSetupResponse.View{amf, ran, diag}} : Result<&2, &2, B.Err, V.InitialContextSetupResponse.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(1), U32.to_nat(14), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(1), U32.to_nat(14)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 1, 14, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {_ == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.InitialContextSetupResponse.View>, V.InitialContextSetupResponse.view(ies), Done{V.InitialContextSetupResponse.View{amf, ran, diag}}, ev)
  %sev : {N.Step.of(st, Gmm.Gmm.ics_response_of_view(st, assoc, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), None{}, eid)
  %sek : {N.Step.of(st, Gmm.Gmm.ics_response_key(st, assoc, ran, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  {==}

def Unknown.setup(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +oks: Maybe<&2, G.PDUSessionResourceSetupListSURes()>, +fails: Maybe<&2, G.PDUSessionResourceFailedToSetupListSURes()>, diag: Maybe<&2, G.CriticalityDiagnostics>, uli: Maybe<&2, G.UserLocationInformation>, eid: {N.Ngap.ue_key(amf) == None{} : Maybe<&2, U32>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 29, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.PDUSessionResourceSetupResponse.view(ies) == Done{V.PDUSessionResourceSetupResponse.View{amf, ran, oks, fails, diag, uli}} : Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(1), U32.to_nat(29), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(1), U32.to_nat(29)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 1, 29, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {_ == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>, V.PDUSessionResourceSetupResponse.view(ies), Done{V.PDUSessionResourceSetupResponse.View{amf, ran, oks, fails, diag, uli}}, ev)
  %sev : {N.Step.of(st, Gsm.Gsm.setup_response_of_view(st, assoc, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), None{}, eid)
  %sek : {N.Step.of(st, Gsm.Gsm.setup_response_key(st, assoc, ran, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), Gsm.Gsm.list_or(G.PDUSessionResourceFailedToSetupItemSURes, fails), _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  {==}

def Unknown.uplink(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +nas: B.Bytes(), loc: G.UserLocationInformation, eid: {N.Ngap.ue_key(amf) == None{} : Maybe<&2, U32>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.UplinkNASTransport.view(ies) == Done{V.UplinkNASTransport.View{amf, ran, nas, loc}} : Result<&2, &2, B.Err, V.UplinkNASTransport.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(0), U32.to_nat(46), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(0), U32.to_nat(46)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 0, 46, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {_ == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UplinkNASTransport.View>, V.UplinkNASTransport.view(ies), Done{V.UplinkNASTransport.View{amf, ran, nas, loc}}, ev)
  %sev : {N.Step.of(st, Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), None{}, eid)
  %sek : {N.Step.of(st, Gmm.Gmm.uplink_key(st, assoc, ran, nas, entropy, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  {==}

def L.amf.ue_key.unknown(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, pdus, cause, uli, rel, diag, oks, fails, nas, loc, eid, ei, eup):
  (ep => ev => Unknown.request(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, pdus, cause, eid, ei, ep, ev, eup), (ep => ev => Unknown.complete(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, uli, rel, diag, eid, ei, ep, ev, eup), (ep => ev => Unknown.ics(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, diag, eid, ei, ep, ev, eup), (ep => ev => Unknown.setup(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, oks, fails, diag, uli, eid, ei, ep, ev, eup), ep => ev => Unknown.uplink(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, nas, loc, eid, ei, ep, ev, eup)))))

# Such a step keeps the state.
def Unknown.kept(+r: N.Step(), +st: S.State, +assoc: U32, +e: {r == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}) -> {K.Kernel.state(r) == st : S.State}:
  Equal.cong(N.Step(), S.State, x => K.Kernel.state(x), r, (st, N.Ngap.unknown_ue(assoc)), e)

# The key ue_key gives: the AMF-UE-NGAP-ID's value when it fits four octets,
# none when it does not.
def Key.split_if(-P: Type, +amf: B.Bytes(), +b: Bool, +eb: {Nat.is_le(List.length(&2, U32, amf), 4n) == b : Bool}, some: {N.Ngap.ue_key(amf) == Some{N.Ngap.of_big(amf)} : Maybe<&2, U32>} -> P, none: {N.Ngap.ue_key(amf) == None{} : Maybe<&2, U32>} -> P) -> P:
  match b:
    case True{}:
      seb = Equal.sym(Bool, Nat.is_le(List.length(&2, U32, amf), 4n), True{}, eb)
      some((%seb : {N.Ngap.key_if(amf, _) == Some{N.Ngap.of_big(amf)} : Maybe<&2, U32>}; {==}))
    case False{}:
      seb = Equal.sym(Bool, Nat.is_le(List.length(&2, U32, amf), 4n), False{}, eb)
      none((%seb : {N.Ngap.key_if(amf, _) == None{} : Maybe<&2, U32>}; {==}))

def Key.split(-P: Type, +amf: B.Bytes(), some: {N.Ngap.ue_key(amf) == Some{N.Ngap.of_big(amf)} : Maybe<&2, U32>} -> P, none: {N.Ngap.ue_key(amf) == None{} : Maybe<&2, U32>} -> P) -> P:
  Key.split_if(P, amf, Nat.is_le(List.length(&2, U32, amf), 4n), {==}, some, none)

# Only the owner releases
# -----------------------

def Owner.request(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +k: U32, +ran: B.Bytes(), pdus: Maybe<&2, G.PDUSessionResourceListCxtRelReq()>, +cause: G.Cause, +ue: S.Ue, eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, ea: {U32.is_eq(S.Ue.assoc(ue), assoc) == False{} : Bool}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 42, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.UEContextReleaseRequest.view(ies) == Done{V.UEContextReleaseRequest.View{amf, ran, pdus, cause}} : Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(0), U32.to_nat(42), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(0), U32.to_nat(42)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 0, 42, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {K.Kernel.state(_) == st : S.State}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>, V.UEContextReleaseRequest.view(ies), Done{V.UEContextReleaseRequest.View{amf, ran, pdus, cause}}, ev)
  %sev : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_request_of_view(st, assoc, _))) == st : S.State}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sek : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_request_key(st, assoc, ran, cause, _))) == st : S.State}
  seu = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{ue}, eu)
  %seu : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_request_ue(st, assoc, k, cause, N.Owner.of(_, assoc, ran)))) == st : S.State}
  sea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, ea)
  %sea : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_request_ue(st, assoc, k, cause, N.Owner.check(ue, Bool.and(_, B.bytes_eq(S.Ue.ran_id(ue), ran)))))) == st : S.State}
  {==}

def Owner.complete(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +k: U32, +ran: B.Bytes(), uli: Maybe<&2, G.UserLocationInformation>, rel: Maybe<&2, G.PDUSessionResourceListCxtRelCpl()>, diag: Maybe<&2, G.CriticalityDiagnostics>, +ue: S.Ue, eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, ea: {U32.is_eq(S.Ue.assoc(ue), assoc) == False{} : Bool}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 41, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.UEContextReleaseComplete.view(ies) == Done{V.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}} : Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(1), U32.to_nat(41), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(1), U32.to_nat(41)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 1, 41, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {K.Kernel.state(_) == st : S.State}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>, V.UEContextReleaseComplete.view(ies), Done{V.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}}, ev)
  %sev : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_complete_of_view(st, assoc, _))) == st : S.State}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sek : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_complete_key(st, assoc, ran, _))) == st : S.State}
  seu = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{ue}, eu)
  %seu : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_complete_ue(st, assoc, k, N.Owner.of(_, assoc, ran), S.Ue.released(_, assoc, ran)))) == st : S.State}
  sea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, ea)
  %sea : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_complete_ue(st, assoc, k, N.Owner.check(ue, Bool.and(_, B.bytes_eq(S.Ue.ran_id(ue), ran))), S.Ue.released(Some{ue}, assoc, ran)))) == st : S.State}
  {==}

def Owner.ics(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +k: U32, +ran: B.Bytes(), diag: Maybe<&2, G.CriticalityDiagnostics>, +ue: S.Ue, eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, ea: {U32.is_eq(S.Ue.assoc(ue), assoc) == False{} : Bool}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 14, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.InitialContextSetupResponse.view(ies) == Done{V.InitialContextSetupResponse.View{amf, ran, diag}} : Result<&2, &2, B.Err, V.InitialContextSetupResponse.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(1), U32.to_nat(14), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(1), U32.to_nat(14)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 1, 14, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {K.Kernel.state(_) == st : S.State}
  sev = Equal.sym(Result<&2, &2, B.Err, V.InitialContextSetupResponse.View>, V.InitialContextSetupResponse.view(ies), Done{V.InitialContextSetupResponse.View{amf, ran, diag}}, ev)
  %sev : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.ics_response_of_view(st, assoc, _))) == st : S.State}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sek : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.ics_response_key(st, assoc, ran, _))) == st : S.State}
  seu = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{ue}, eu)
  %seu : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.ics_response_ue(st, assoc, k, N.Owner.of(_, assoc, ran)))) == st : S.State}
  sea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, ea)
  %sea : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.ics_response_ue(st, assoc, k, N.Owner.check(ue, Bool.and(_, B.bytes_eq(S.Ue.ran_id(ue), ran)))))) == st : S.State}
  {==}

def Owner.setup(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +k: U32, +ran: B.Bytes(), +oks: Maybe<&2, G.PDUSessionResourceSetupListSURes()>, +fails: Maybe<&2, G.PDUSessionResourceFailedToSetupListSURes()>, diag: Maybe<&2, G.CriticalityDiagnostics>, uli: Maybe<&2, G.UserLocationInformation>, +ue: S.Ue, eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, ea: {U32.is_eq(S.Ue.assoc(ue), assoc) == False{} : Bool}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 29, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.PDUSessionResourceSetupResponse.view(ies) == Done{V.PDUSessionResourceSetupResponse.View{amf, ran, oks, fails, diag, uli}} : Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(1), U32.to_nat(29), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(1), U32.to_nat(29)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 1, 29, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {K.Kernel.state(_) == st : S.State}
  sev = Equal.sym(Result<&2, &2, B.Err, V.PDUSessionResourceSetupResponse.View>, V.PDUSessionResourceSetupResponse.view(ies), Done{V.PDUSessionResourceSetupResponse.View{amf, ran, oks, fails, diag, uli}}, ev)
  %sev : {K.Kernel.state(N.Step.of(st, Gsm.Gsm.setup_response_of_view(st, assoc, _))) == st : S.State}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sek : {K.Kernel.state(N.Step.of(st, Gsm.Gsm.setup_response_key(st, assoc, ran, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), Gsm.Gsm.list_or(G.PDUSessionResourceFailedToSetupItemSURes, fails), _))) == st : S.State}
  seu = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{ue}, eu)
  %seu : {K.Kernel.state(N.Step.of(st, Gsm.Gsm.setup_response_ue(st, assoc, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), Gsm.Gsm.list_or(G.PDUSessionResourceFailedToSetupItemSURes, fails), N.Owner.of(_, assoc, ran)))) == st : S.State}
  sea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, ea)
  %sea : {K.Kernel.state(N.Step.of(st, Gsm.Gsm.setup_response_ue(st, assoc, k, Gsm.Gsm.list_or(G.PDUSessionResourceSetupItemSURes, oks), Gsm.Gsm.list_or(G.PDUSessionResourceFailedToSetupItemSURes, fails), N.Owner.check(ue, Bool.and(_, B.bytes_eq(S.Ue.ran_id(ue), ran)))))) == st : S.State}
  {==}

def Owner.uplink(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +k: U32, +ran: B.Bytes(), +nas: B.Bytes(), loc: G.UserLocationInformation, +ue: S.Ue, eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, eu: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, ea: {U32.is_eq(S.Ue.assoc(ue), assoc) == False{} : Bool}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ev: {V.UplinkNASTransport.view(ies) == Done{V.UplinkNASTransport.View{amf, ran, nas, loc}} : Result<&2, &2, B.Err, V.UplinkNASTransport.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(0), U32.to_nat(46), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(0), U32.to_nat(46)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 0, 46, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {K.Kernel.state(_) == st : S.State}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UplinkNASTransport.View>, V.UplinkNASTransport.view(ies), Done{V.UplinkNASTransport.View{amf, ran, nas, loc}}, ev)
  %sev : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, _))) == st : S.State}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sek : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.uplink_key(st, assoc, ran, nas, entropy, _))) == st : S.State}
  seu = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{ue}, eu)
  %seu : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.uplink_ue(st, assoc, k, nas, entropy, N.Owner.of(_, assoc, ran)))) == st : S.State}
  sea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, ea)
  %sea : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.uplink_ue(st, assoc, k, nas, entropy, N.Owner.check(ue, Bool.and(_, B.bytes_eq(S.Ue.ran_id(ue), ran)))))) == st : S.State}
  {==}

def L.amf.ue_context_release.owner_only(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, pdus, cause, uli, rel, diag, oks, fails, nas, loc, ue, eu, ea, ei):
  (+ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 0, 42, crit, value, ies, c, ep, ei, {==}, +eup => Key.split({K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}, amf, eid => Owner.request(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, N.Ngap.of_big(amf), ran, pdus, cause, ue, eid, eu, ea, ei, ep, ev, eup), en => Unknown.kept(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), st, assoc, Unknown.request(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, pdus, cause, en, ei, ep, ev, eup)))), (+ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 1, 41, crit, value, ies, c, ep, ei, {==}, +eup => Key.split({K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}, amf, eid => Owner.complete(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, N.Ngap.of_big(amf), ran, uli, rel, diag, ue, eid, eu, ea, ei, ep, ev, eup), en => Unknown.kept(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), st, assoc, Unknown.complete(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, uli, rel, diag, en, ei, ep, ev, eup)))), (+ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 1, 14, crit, value, ies, c, ep, ei, {==}, +eup => Key.split({K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}, amf, eid => Owner.ics(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, N.Ngap.of_big(amf), ran, diag, ue, eid, eu, ea, ei, ep, ev, eup), en => Unknown.kept(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), st, assoc, Unknown.ics(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, diag, en, ei, ep, ev, eup)))), (+ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 1, 29, crit, value, ies, c, ep, ei, {==}, +eup => Key.split({K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}, amf, eid => Owner.setup(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, N.Ngap.of_big(amf), ran, oks, fails, diag, uli, ue, eid, eu, ea, ei, ep, ev, eup), en => Unknown.kept(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), st, assoc, Unknown.setup(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, oks, fails, diag, uli, en, ei, ep, ev, eup)))), +ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 0, 46, crit, value, ies, c, ep, ei, {==}, +eup => Key.split({K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}, amf, eid => Owner.uplink(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, N.Ngap.of_big(amf), ran, nas, loc, ue, eid, eu, ea, ei, ep, ev, eup), en => Unknown.kept(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), st, assoc, Unknown.uplink(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, nas, loc, en, ei, ep, ev, eup))))))))

# Release forgets
# ---------------

def Tx.forget_ue(+key: U32, +st: S.State) -> {Tb.Table.get(S.Ue, key, S.State.ues(S.Tx.apply(S.Del{key}, st))) == None{} : Maybe<&2, S.Ue>}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      Del.get(key, ues)

def Tx.forget_sessions(+key: U32, +st: S.State) -> {S.Sessions.of_ue(key, S.State.sessions(S.Tx.apply(S.Del{key}, st))) == [] : Tb.Table(S.Session)}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      Sessions.drop_none(key, sessions)

# A context forgotten after its sessions' deletions: no context under its key
# and no session of it.
def Tx.forget(+key: U32, +o: N.GOut(), +more: List<&2, N.Act>, +st: S.State) -> {Tb.Table.get(S.Ue, key, S.State.ues(K.Kernel.state(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more))))) == None{} : Maybe<&2, S.Ue>} & {S.Sessions.of_ue(key, S.State.sessions(K.Kernel.state(N.Step.of(st, N.Out.also(N.Out.join(o, (S.Del{key}, [])), more))))) == [] : Tb.Table(S.Session)}:
  match o:
    case (+tx, acts):
      (Tx.forget_ue(key, S.Tx.apply(tx, st)), Tx.forget_sessions(key, S.Tx.apply(tx, st)))

def L.amf.release.complete_forgets(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, ran, uli, rel, diag, ue, ep, ei, ev, eid, eo, eup):
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(1), U32.to_nat(41), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(1), U32.to_nat(41)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 1, 41, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(_))) == None{} : Maybe<&2, S.Ue>} & {S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(_))) == [] : Tb.Table(S.Session)}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>, V.UEContextReleaseComplete.view(ies), Done{V.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}}, ev)
  %sev : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_complete_of_view(st, assoc, _))))) == None{} : Maybe<&2, S.Ue>} & {S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_complete_of_view(st, assoc, _))))) == [] : Tb.Table(S.Session)}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sek : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_complete_key(st, assoc, ran, _))))) == None{} : Maybe<&2, S.Ue>} & {S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_complete_key(st, assoc, ran, _))))) == [] : Tb.Table(S.Session)}
  seo = Equal.sym(Maybe<&2, S.Ue>, Gmm.Gmm.owner(st, assoc, k, ran), Some{ue}, eo)
  %seo : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_complete_ue(st, assoc, k, _, S.Ue.released(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran)))))) == None{} : Maybe<&2, S.Ue>} & {S.Sessions.of_ue(k, S.State.sessions(K.Kernel.state(N.Step.of(st, Gmm.Gmm.release_complete_ue(st, assoc, k, _, S.Ue.released(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran)))))) == [] : Tb.Table(S.Session)}
  +gone = S.Sessions.of_ue(k, S.State.sessions(st))
  Tx.forget(k, Up.N4.deletions(gone, S.State.pfcp_seq(st)), List.append(&2, N.Act, N.Guard.cancel(k, S.Ue.guard(ue)), List.append(&2, N.Act, Ho.Ho.leg_drop(k, S.Ue.phase(ue), N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified())), [N.Note{F.Info{}, "NGAP: UE context released"}])), st)

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
# A Put is a clear row in front of a sifting, a Rephase changes no identity,
# a Del and an association going down are siftings (amf.indexes.unique, in
# liveness.bend).

def Down.unique(st: S.State, +assoc: U32, e: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> {S.Ues.unique(S.State.ues(K.Kernel.state(R.Route.drop(st, assoc)))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      Unique.sift(S.Others{assoc}, ues, e)

# Plaintext after security
# ------------------------

def Plain.keyed(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, len: U32, +bytes: B.Bytes(), crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, c: Ap.Cur, +amf: B.Bytes(), +k: U32, +ran: B.Bytes(), +nas: B.Bytes(), uli: G.UserLocationInformation, +ue: S.Ue, +ctx: Sec.Nas.Ctx, err: B.Err, ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 46, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, ev: {V.UplinkNASTransport.view(ies) == Done{V.UplinkNASTransport.View{amf, ran, nas, uli}} : Result<&2, &2, B.Err, V.UplinkNASTransport.View>}, eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, eo: {Gmm.Gmm.owner(st, assoc, k, ran) == Some{ue} : Maybe<&2, S.Ue>}, ec: {S.Phase.ctx(S.Ue.phase(ue)) == Some{ctx} : Maybe<&2, Sec.Nas.Ctx>}, ef: {Sec.Nas.unprotect(ctx, nas) == Fail{err} : Result<&2, &2, B.Err, Sec.Nas.Unprotected>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, R.Route.d2(st, assoc, stream, U32.to_nat(0), U32.to_nat(46), ies, entropy, N.Ngap.is_initial_ue_message(U32.to_nat(0), U32.to_nat(46)))), PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 0, 46, crit, value, ies, c, ep, ei, {==}, eup))
  %sr : {K.Kernel.state(_) == st : S.State}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UplinkNASTransport.View>, V.UplinkNASTransport.view(ies), Done{V.UplinkNASTransport.View{amf, ran, nas, uli}}, ev)
  %sev : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.uplink_of_view(st, assoc, stream, entropy, _))) == st : S.State}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sek : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.uplink_key(st, assoc, ran, nas, entropy, _))) == st : S.State}
  seo = Equal.sym(Maybe<&2, S.Ue>, Gmm.Gmm.owner(st, assoc, k, ran), Some{ue}, eo)
  %seo : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.uplink_ue(st, assoc, k, nas, entropy, _))) == st : S.State}
  sec = Equal.sym(Maybe<&2, Sec.Nas.Ctx>, S.Phase.ctx(S.Ue.phase(ue)), Some{ctx}, ec)
  %sec : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.secured(st, k, ue, entropy, nas, _))) == st : S.State}
  sef = Equal.sym(Result<&2, &2, B.Err, Sec.Nas.Unprotected>, Sec.Nas.unprotect(ctx, nas), Fail{err}, ef)
  %sef : {K.Kernel.state(N.Step.of(st, Gmm.Gmm.opened(st, k, ue, entropy, _))) == st : S.State}
  {==}

def L.amf.nas.plaintext_after_security(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, nas, uli, ue, ctx, err, ep, ei, ev, eo, ec, ef):
  PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 0, 46, crit, value, ies, c, ep, ei, {==}, +eup => Key.split({K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}, amf, eid => Plain.keyed(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, N.Ngap.of_big(amf), ran, nas, uli, ue, ctx, err, ep, ei, ev, eid, eo, ec, ef, eup), en => Unknown.kept(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), st, assoc, Unknown.uplink(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, nas, uli, en, ei, ep, ev, eup))))

# The configuration
# -----------------
# Only Config sets it, and only when complete; every other step keeps it.

def Cfgv.tx(tx: S.Tx, +st: S.State) -> {S.State.config(S.Tx.apply(tx, st)) == S.State.config(st) : Maybe<&2, S.Cfg>}:
  match tx:
    case S.Keep{}:
      {==}
    case S.Put{key, ue}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Rephase{key, phase}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Del{key}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.PutSession{key, s}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Revar{key, v}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.DelSession{key}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Subs{new}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.SetLink{link}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.BumpUe{bk}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.BumpSeq{n}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          {==}
    case S.Both{+first, second}:
      Equal.trans(Maybe<&2, S.Cfg>, S.State.config(S.Tx.apply(second, S.Tx.apply(first, st))), S.State.config(S.Tx.apply(first, st)), S.State.config(st), Cfgv.tx(second, S.Tx.apply(first, st)), Cfgv.tx(first, st))

def Cfgv.render(+st: S.State, o: N.GOut()) -> {S.State.config(K.Kernel.state(N.Step.of(st, o))) == S.State.config(st) : Maybe<&2, S.Cfg>}:
  match o:
    case (tx, acts):
      Cfgv.tx(tx, st)

def Cfgv.assocs(st: S.State, as: Tb.Table(B.Bytes())) -> {S.State.config(S.State.with_assocs(st, as)) == S.State.config(st) : Maybe<&2, S.Cfg>}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      {==}

def Cfgv.down(st: S.State, +assoc: U32) -> {S.State.config(K.Kernel.state(R.Route.drop(st, assoc))) == S.State.config(st) : Maybe<&2, S.Cfg>}:
  match st:
    case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
      {==}

def Cfgv.down_all(+st: S.State, +assoc: U32) -> {S.State.config(K.Kernel.state(R.Route.down(st, assoc))) == S.State.config(st) : Maybe<&2, S.Cfg>}:
  Equal.trans(Maybe<&2, S.Cfg>, S.State.config(K.Kernel.state(R.Route.down(st, assoc))), S.State.config(K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, assoc)))), S.State.config(st), Cfgv.down(K.Kernel.state(N.Step.of(st, Ho.Ho.down(st, assoc))), assoc), Cfgv.render(st, Ho.Ho.down(st, assoc)))

# The configuration a state holds is valid, if it holds one.
def Cfgv.held(m: Maybe<&2, S.Cfg>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{c}:
      S.Cfg.valid(c)

def Cfgv.Held(o: N.Step()) -> Data:
  {Cfgv.held(S.State.config(K.Kernel.state(o))) == True{} : Bool}

def Cfgv.of(+m: Maybe<&2, S.Cfg>, e: @c: S.Cfg -> {m == Some{c} : Maybe<&2, S.Cfg>} -> {S.Cfg.valid(c) == True{} : Bool}) -> {Cfgv.held(m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      e(c, {==})

def Cfgv.kept(+st: S.State, +st2: S.State, eq: {S.State.config(st2) == S.State.config(st) : Maybe<&2, S.Cfg>}, h: {Cfgv.held(S.State.config(st)) == True{} : Bool}) -> {Cfgv.held(S.State.config(st2)) == True{} : Bool}:
  se = Equal.sym(Maybe<&2, S.Cfg>, S.State.config(st2), S.State.config(st), eq)
  (%se : {Cfgv.held(_) == True{} : Bool}; h)

# A complete Config is valid, and it is what the state then holds.
def Cfgv.config(complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), ek: {S.Cfg.complete(tlvs) == complete : Bool}, h: {Cfgv.held(S.State.config(st)) == True{} : Bool}) -> Cfgv.Held(K.Kernel.config(complete, st, tlvs, entropy)):
  match complete:
    case False{}:
      h
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}:
          +st2 : S.State = S.State{Some{S.Cfg.of(tlvs)}, Au.Subscribers.of(S.Cfg.subscribers(S.Cfg.of(tlvs))), assocs, ues, sessions, pfcp_seq, next_ue, S.N4{List.take(&2, U32, entropy, 4n), S.Idle{}}}
          +o : N.GOut() = N.Out.also(Up.N4.start(st2), [N.Note{F.Info{}, "Config: loaded; PFCP association requested"}])
          Cfgv.kept(st2, K.Kernel.state(N.Step.of(st2, o)), Cfgv.render(st2, o), P.Bool.and_true_r(S.Cfg.given_all(tlvs), S.Cfg.valid(S.Cfg.of(tlvs)), ek))

def L.kernel.config.valid(st, ev, entropy, cfg, e, ec):
  +h = Cfgv.of(S.State.config(st), e)
  +held = PW.Walk.any(o => Cfgv.Held(o), st, ev, entropy, acts => x => cx => h, +a => +id => +ok => acts => x => cx => Cfgv.kept(st, S.State.with_assocs(N.Step.state(R.Route.drop(st, a)), S.Assocs.set(a, id, S.State.assocs(N.Step.state(R.Route.drop(st, a))), ok)), Equal.trans(Maybe<&2, S.Cfg>, S.State.config(S.State.with_assocs(N.Step.state(R.Route.drop(st, a)), S.Assocs.set(a, id, S.State.assocs(N.Step.state(R.Route.drop(st, a))), ok))), S.State.config(N.Step.state(R.Route.drop(st, a))), S.State.config(st), Cfgv.assocs(N.Step.state(R.Route.drop(st, a)), S.Assocs.set(a, id, S.State.assocs(N.Step.state(R.Route.drop(st, a))), ok)), Cfgv.down(st, a)), h), +tlvs => Cfgv.config(S.Cfg.complete(tlvs), st, tlvs, entropy, {==}, h), +a => Cfgv.kept(st, K.Kernel.state(R.Route.down(st, a)), Cfgv.down_all(st, a), h), +o => Cfgv.kept(st, K.Kernel.state(N.Step.of(st, o)), Cfgv.render(st, o), h))
  ({==}, (%ec : {Cfgv.held(_) == True{} : Bool}; held))

# GHSA-f9c2-535p-3mwc: a PLMN that decodes names a serving network.
def Snn.of(r: B.Read(Pl.Plmn), e: {F.Result.ok(B.ReadValue(Pl.Plmn), r) == True{} : Bool}) -> {List.is_empty(&2, U32, Au.Ausf.snn_of(r)) == False{} : Bool}:
  match r:
    case Fail{err}:
      Empty.absurd({List.is_empty(&2, U32, Au.Ausf.snn_of(Fail{err})) == False{} : Bool}, P.Refute.bool(e))
    case Done{(p, rest)}:
      {==}

def L.kdf.snn.nonempty(cfg, e):
  +rest = Bool.and(F.Len.is(S.Cfg.dns(cfg), 4n), S.Cfg.fits(cfg))
  Snn.of(Pl.Plmn.read(S.Cfg.plmn(cfg)), P.Bool.and_true_l(F.Result.ok(B.ReadValue(Pl.Plmn), Pl.Plmn.read(S.Cfg.plmn(cfg))), rest, P.Bool.and_true_r(F.Len.is(S.Cfg.plmn(cfg), 3n), Bool.and(F.Result.ok(B.ReadValue(Pl.Plmn), Pl.Plmn.read(S.Cfg.plmn(cfg))), rest), e)))
