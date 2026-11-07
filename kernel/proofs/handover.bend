import Base
import ../bytes.bend as B
import ../table.bend as Tb
import ../state.bend as S
import ../ngap/gen/types.bend as G
import ../frame.bend as F
import ../step.bend as K
import ../amf/ngap.bend as N
import ../amf/gmm.bend as Gmm
import ../nas/security.bend as Sec
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../amf/route.bend as R
import ../smf/switch.bend as Sw
import ../amf/handover.bend as Ho
import ../LAWS.bend as L
import ./lib.bend as P
import ./walk.bend as PW
import ./takeover.bend as PT
import ./path_switch.bend as PPs
import ./liveness.bend as PL
import ./kernel.bend as PK

# Proofs of the N2 handover laws (ticket 28).

# The route
# ---------

# A PDU whose IEs read is dispatched by its kind and procedure code.
def Hp.dispatch(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == R.Route.dispatch(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy) : N.Step()}:
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{kind, code, crit, value}}, ep)
  %sep : {R.Route.of_pdu(st, assoc, stream, entropy, _) == R.Route.dispatch(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy) : N.Step()}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {R.Route.of_ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, _) == R.Route.dispatch(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy) : N.Step()}
  {==}

# A PDU that reads: its IEs read or not.
def Hp.Pdu(-Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +kind: U32, +code: U32) -> Type:
  @ies:List<&2, Fr.Ie> -> Q(R.Route.dispatch(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), ies, entropy))

def Hp.ies(-Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +kind: U32, +code: U32, +r: Ap.Rd(List<&2, Fr.Ie>), bad: Q((st, N.Ngap.bad_pdu(assoc))), h: Hp.Pdu(Q, st, entropy, assoc, stream, kind, code)) -> Q(R.Route.of_ies(st, assoc, stream, U32.to_nat(kind), U32.to_nat(code), entropy, r)):
  match r:
    case Fail{e}:
      bad
    case Done{(+ies, c)}:
      h(ies)

def Hp.pdu(-Q: N.Step() -> Type, +st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, bad: Q((st, N.Ngap.bad_pdu(assoc))), h: Hp.Pdu(Q, st, entropy, assoc, stream, kind, code)) -> Q(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)):
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{kind, code, crit, value}}, ep)
  %sep : Q(R.Route.of_pdu(st, assoc, stream, entropy, _))
  Hp.ies(Q, st, entropy, assoc, stream, kind, code, Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), bad, h)

# Owners
# ------
# A transaction that keeps or rephases contexts keeps every context's owner.

def Hp.still(tx: S.Tx) -> Bool:
  match tx:
    case S.Keep{}:
      True{}
    case S.Rephase{key, p}:
      True{}
    case _:
      False{}

def Hp.calm(o: N.GOut()) -> Bool:
  Hp.still(PT.Tk.tx(o))

def Hp.same_refl(+m: Maybe<&2, S.Ue>) -> {S.Ue.same_owner(m, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+u}:
      ea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(u), S.Ue.assoc(u)), True{}, P.U32.is_eq_refl(S.Ue.assoc(u)))
      %ea : {Bool.and(_, B.bytes_eq(S.Ue.ran_id(u), S.Ue.ran_id(u))) == True{} : Bool}
      P.Bytes.eq_refl(S.Ue.ran_id(u))

def Hp.same_if(+w: S.Ue, +p: S.Phase, +b: Bool) -> {S.Ue.same_owner(Some{w}, Some{S.Ue.rephase_if(w, p, b)}) == True{} : Bool}:
  match w:
    case S.Ue{+assoc, +ran_id, +stream, +supi, +tmsi, +reg, +ngksi, +phase, +last_dl}:
      match b:
        case True{}:
          Hp.same_refl(Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, p, last_dl}})
        case False{}:
          Hp.same_refl(Some{S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}})

def Hp.same_row(+j: U32, +key: U32, +p: S.Phase, +k0: U32, +w: S.Ue, +more: Tb.Table(S.Ue), +b: Bool, +eb: {U32.is_eq(k0, j) == b : Bool}, ih: {S.Ue.same_owner(Tb.Table.get(S.Ue, j, more), Tb.Table.get(S.Ue, j, S.Ues.rephase(key, p, more))) == True{} : Bool}) -> {S.Ue.same_owner(Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, j, more), U32.is_eq(k0, j)), Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, U32.is_eq(k0, key)), Tb.Table.get(S.Ue, j, S.Ues.rephase(key, p, more)), U32.is_eq(k0, j))) == True{} : Bool}:
  match b:
    case True{}:
      se = Equal.sym(Bool, U32.is_eq(k0, j), True{}, eb)
      %se : {S.Ue.same_owner(Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, j, more), _), Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, U32.is_eq(k0, key)), Tb.Table.get(S.Ue, j, S.Ues.rephase(key, p, more)), _)) == True{} : Bool}
      Hp.same_if(w, p, U32.is_eq(k0, key))
    case False{}:
      se = Equal.sym(Bool, U32.is_eq(k0, j), False{}, eb)
      %se : {S.Ue.same_owner(Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, j, more), _), Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, U32.is_eq(k0, key)), Tb.Table.get(S.Ue, j, S.Ues.rephase(key, p, more)), _)) == True{} : Bool}
      ih

def Hp.same_rephase(+j: U32, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue)) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, S.Ues.rephase(key, p, ues))) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k0, +w) <> +more:
      Hp.same_row(j, key, p, k0, w, more, U32.is_eq(k0, j), {==}, Hp.same_rephase(j, key, p, more))

def Hp.same_still(+tx: S.Tx, +ues: Tb.Table(S.Ue), +j: U32, +e: {Hp.still(tx) == True{} : Bool}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(tx, ues))) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      Hp.same_refl(Tb.Table.get(S.Ue, j, ues))
    case S.Rephase{+key, +p}:
      Hp.same_rephase(j, key, p, ues)
    case S.Put{key, ue}:
      Empty.absurd({S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(S.Put{key, ue}, ues))) == True{} : Bool}, P.Refute.bool(e))
    case S.Del{key}:
      Empty.absurd({S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(S.Del{key}, ues))) == True{} : Bool}, P.Refute.bool(e))
    case S.PutSession{key, s}:
      Empty.absurd({S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(S.PutSession{key, s}, ues))) == True{} : Bool}, P.Refute.bool(e))
    case S.Revar{key, v}:
      Empty.absurd({S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(S.Revar{key, v}, ues))) == True{} : Bool}, P.Refute.bool(e))
    case S.DelSession{key}:
      Empty.absurd({S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(S.DelSession{key}, ues))) == True{} : Bool}, P.Refute.bool(e))
    case S.Subs{subs}:
      Empty.absurd({S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(S.Subs{subs}, ues))) == True{} : Bool}, P.Refute.bool(e))
    case S.SetLink{link}:
      Empty.absurd({S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(S.SetLink{link}, ues))) == True{} : Bool}, P.Refute.bool(e))
    case S.BumpUe{bk}:
      Empty.absurd({S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(S.BumpUe{bk}, ues))) == True{} : Bool}, P.Refute.bool(e))
    case S.BumpSeq{n}:
      Empty.absurd({S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(S.BumpSeq{n}, ues))) == True{} : Bool}, P.Refute.bool(e))
    case S.Both{a, b}:
      Empty.absurd({S.Ue.same_owner(Tb.Table.get(S.Ue, j, ues), Tb.Table.get(S.Ue, j, PT.Tk.ues(S.Both{a, b}, ues))) == True{} : Bool}, P.Refute.bool(e))

# The step a calm outcome makes leaves every context's owner.
def Hp.same_step(+st: S.State, +o: N.GOut(), +j: U32, +e: {Hp.calm(o) == True{} : Bool}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(N.Step.of(st, o))))) == True{} : Bool}:
  sr = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, o))), PT.Tk.ues(PT.Tk.tx(o), S.State.ues(st)), PT.Tk.render(st, o))
  %sr : {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, _)) == True{} : Bool}
  Hp.same_still(PT.Tk.tx(o), S.State.ues(st), j, e)

# The handover procedures
# -----------------------
# Each outcome of Handover Request Acknowledge, Handover Failure, Handover
# Cancel and Uplink RAN Status Transfer keeps the state or rephases one
# context (calm); Handover Required and Handover Request Acknowledge also
# start the guard of the context they rephase (fine).

def Hp.starts_if(+k: U32, tx: S.Tx, +acts: List<&2, N.Act>) -> Bool:
  match tx:
    case S.Keep{}:
      True{}
    case S.Rephase{key, p}:
      Bool.or(Bool.not(U32.is_eq(key, k)), N.Acts.starts(k, acts))
    case _:
      False{}

def Hp.fine(+k: U32, o: N.GOut()) -> Bool:
  match o:
    case (+tx, +acts):
      Bool.and(Hp.still(tx), Hp.starts_if(k, tx, acts))

def Hp.calm_of_fine(+k: U32, +o: N.GOut(), +e: {Hp.fine(k, o) == True{} : Bool}) -> {Hp.calm(o) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      P.Bool.and_true_l(Hp.still(tx), Hp.starts_if(k, tx, acts), e)

def Hp.second(+x: Bool) -> {Bool.or(Bool.not(x), Bool.or(x, False{})) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def Hp.r_prepare(+k: U32, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +t: U32, +cfg: S.Cfg, +cause: G.Cause, +container: B.Bytes(), +items: G.PDUSessionResourceSetupListHOReq()) -> {Hp.fine(k, Ho.Ho.prepare(key, ue, ctx, nh, t, cfg, cause, container, items)) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case i <> more:
      Hp.second(U32.is_eq(key, k))

def Hp.r_cfg(+st: S.State, +k: U32, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +t: U32, +cause: G.Cause, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +m: Maybe<&2, S.Cfg>) -> {Hp.fine(k, Ho.Ho.required_cfg(st, key, ue, ctx, nh, t, cause, items, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+cfg}:
      Hp.r_prepare(k, key, ue, ctx, nh, t, cfg, cause, container, Ho.Ho.setup_items(cfg, items, S.Sessions.of_ue(key, S.State.sessions(st))))

def Hp.r_other(+st: S.State, +k: U32, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +t: U32, +cause: G.Cause, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +same: Bool) -> {Hp.fine(k, Ho.Ho.required_other(st, key, ue, ctx, nh, t, cause, items, container, same)) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      Hp.r_cfg(st, k, key, ue, ctx, nh, t, cause, items, container, S.State.config(st))

def Hp.r_target(+st: S.State, +k: U32, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +cause: G.Cause, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +m: Maybe<&2, U32>) -> {Hp.fine(k, Ho.Ho.required_target(st, key, ue, ctx, nh, cause, items, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+t}:
      Hp.r_other(st, k, key, ue, ctx, nh, t, cause, items, container, U32.is_eq(t, S.Ue.assoc(ue)))

def Hp.r_phase(+st: S.State, +k: U32, +assoc: U32, +key: U32, +ue: S.Ue, +kind: G.HandoverType(), +cause: G.Cause, +id: G.TargetID, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +p: S.Phase) -> {Hp.fine(k, Ho.Ho.required_phase(st, assoc, key, ue, kind, cause, id, items, container, p)) == True{} : Bool}:
  match p:
    case S.Registered{+ctx, +nh, released}:
      Hp.r_target(st, k, key, ue, ctx, nh, cause, items, container, Ho.Ho.target(st, Ho.Ho.intra_type(kind), Ho.Ho.node(id)))
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Handover{ctx, nh, source, leg}:
      {==}
    case S.Releasing{guard}:
      {==}

def Hp.r_ue(+st: S.State, +k: U32, +assoc: U32, +key: U32, +kind: G.HandoverType(), +cause: G.Cause, +id: G.TargetID, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +m: Maybe<&2, S.Ue>) -> {Hp.fine(k, Ho.Ho.required_ue(st, assoc, key, kind, cause, id, items, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Hp.r_phase(st, k, assoc, key, ue, kind, cause, id, items, container, S.Ue.phase(ue))

def Hp.r_key(+st: S.State, +k: U32, +assoc: U32, +ran: B.Bytes(), +kind: G.HandoverType(), +cause: G.Cause, +id: G.TargetID, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +m: Maybe<&2, U32>) -> {Hp.fine(k, Ho.Ho.required_key(st, assoc, ran, kind, cause, id, items, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Hp.r_ue(st, k, assoc, key, kind, cause, id, items, container, N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran))

def Hp.required(+st: S.State, +k: U32, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverRequired.View>) -> {Hp.fine(k, Ho.Ho.required_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.HandoverRequired.View{+amf, +ran, +kind, +cause, +id, direct, +items, +container}}:
      Hp.r_key(st, k, assoc, ran, kind, cause, id, items, container, N.Ngap.ue_key(amf))

def Hp.a_phase(+k: U32, +assoc: U32, +stream: U32, +key: U32, +ue: S.Ue, +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes(), +p: S.Phase) -> {Hp.fine(k, Ho.Ho.ack_phase(assoc, stream, key, ue, ran, admitted, container, p)) == True{} : Bool}:
  match p:
    case S.Handover{ctx, nh, source, leg}:
      match leg:
        case S.Asked{t}:
          Hp.second(U32.is_eq(key, k))
        case S.Acked{t, r, s, ts}:
          {==}
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Hp.a_ue(+k: U32, +assoc: U32, +stream: U32, +key: U32, +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes(), +m: Maybe<&2, S.Ue>) -> {Hp.fine(k, Ho.Ho.ack_ue(assoc, stream, key, ran, admitted, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Hp.a_phase(k, assoc, stream, key, ue, ran, admitted, container, S.Ue.phase(ue))

def Hp.a_key(+st: S.State, +k: U32, +assoc: U32, +stream: U32, +ran: B.Bytes(), +admitted: G.PDUSessionResourceAdmittedList(), +container: B.Bytes(), +m: Maybe<&2, U32>) -> {Hp.fine(k, Ho.Ho.ack_key(st, assoc, stream, ran, admitted, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Hp.a_ue(k, assoc, stream, key, ran, admitted, container, Ho.Ho.for_target(st, assoc, key))

def Hp.ack(+st: S.State, +k: U32, +assoc: U32, +stream: U32, +r: Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View>) -> {Hp.fine(k, Ho.Ho.ack_of_view(st, assoc, stream, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.HandoverRequestAcknowledge.View{+amf, +ran, +admitted, failed, +container, diag, npn}}:
      Hp.a_key(st, k, assoc, stream, ran, admitted, container, N.Ngap.ue_key(amf))

def Hp.f_phase(+assoc: U32, +key: U32, +ue: S.Ue, +cause: G.Cause, +p: S.Phase) -> {Hp.calm(Ho.Ho.failure_phase(assoc, key, ue, cause, p)) == True{} : Bool}:
  match p:
    case S.Handover{ctx, nh, source, leg}:
      match leg:
        case S.Asked{t}:
          {==}
        case S.Acked{t, r, s, ts}:
          {==}
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Hp.f_ue(+assoc: U32, +key: U32, +cause: G.Cause, +m: Maybe<&2, S.Ue>) -> {Hp.calm(Ho.Ho.failure_ue(assoc, key, cause, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Hp.f_phase(assoc, key, ue, cause, S.Ue.phase(ue))

def Hp.f_key(+st: S.State, +assoc: U32, +cause: G.Cause, +m: Maybe<&2, U32>) -> {Hp.calm(Ho.Ho.failure_key(st, assoc, cause, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Hp.f_ue(assoc, key, cause, Ho.Ho.for_target(st, assoc, key))

def Hp.failure(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverFailure.View>) -> {Hp.calm(Ho.Ho.failure_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.HandoverFailure.View{+amf, +cause, diag}}:
      Hp.f_key(st, assoc, cause, N.Ngap.ue_key(amf))

def Hp.c_phase(+key: U32, +ue: S.Ue, +p: S.Phase) -> {Hp.calm(Ho.Ho.cancel_phase(key, ue, p)) == True{} : Bool}:
  match p:
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Handover{ctx, nh, source, leg}:
      {==}
    case S.Releasing{guard}:
      {==}

def Hp.c_ue(+assoc: U32, +key: U32, +m: Maybe<&2, S.Ue>) -> {Hp.calm(Ho.Ho.cancel_ue(assoc, key, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Hp.c_phase(key, ue, S.Ue.phase(ue))

def Hp.c_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +m: Maybe<&2, U32>) -> {Hp.calm(Ho.Ho.cancel_key(st, assoc, ran, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Hp.c_ue(assoc, key, N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran))

def Hp.cancel(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverCancel.View>) -> {Hp.calm(Ho.Ho.cancel_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.HandoverCancel.View{+amf, +ran, cause}}:
      Hp.c_key(st, assoc, ran, N.Ngap.ue_key(amf))

def Hp.s_phase(+key: U32, +container: G.RANStatusTransfer_TransparentContainer, +p: S.Phase) -> {Hp.calm(Ho.Ho.status_phase(key, container, p)) == True{} : Bool}:
  match p:
    case S.Handover{ctx, nh, source, leg}:
      match leg:
        case S.Asked{t}:
          {==}
        case S.Acked{t, r, s, ts}:
          {==}
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Releasing{guard}:
      {==}

def Hp.s_ue(+assoc: U32, +key: U32, +container: G.RANStatusTransfer_TransparentContainer, +m: Maybe<&2, S.Ue>) -> {Hp.calm(Ho.Ho.status_ue(assoc, key, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+ue}:
      Hp.s_phase(key, container, S.Ue.phase(ue))

def Hp.s_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), +container: G.RANStatusTransfer_TransparentContainer, +m: Maybe<&2, U32>) -> {Hp.calm(Ho.Ho.status_key(st, assoc, ran, container, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+key}:
      Hp.s_ue(assoc, key, container, N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran))

def Hp.status(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View>) -> {Hp.calm(Ho.Ho.status_of_view(st, assoc, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{V.UplinkRANStatusTransfer.View{+amf, +ran, +container}}:
      Hp.s_key(st, assoc, ran, container, N.Ngap.ue_key(amf))

# Small facts
# -----------

def Hp.phase_with(+u: S.Ue, +p: S.Phase) -> {S.Ue.phase(S.Ue.with_phase(u, p)) == p : S.Phase}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

def Hp.assoc_moved(+u: S.Ue, +a: U32, +r: B.Bytes(), +s: U32, +p: S.Phase) -> {S.Ue.assoc(S.Ue.moved(u, a, r, s, p)) == a : U32}:
  match u:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      {==}

# No context has a handover pending to assoc: the target's answer finds none.
def Hp.not_aimed(+m: Maybe<&2, S.Ue>, +assoc: U32, +e: {S.Maybe.same_u32(S.Ue.pending(m), Some{assoc}) == False{} : Bool}) -> {Ho.Ho.pending(m, assoc) == None{} : Maybe<&2, S.Ue>}:
  match m:
    case None{}:
      {==}
    case Some{+u}:
      se = Equal.sym(Bool, S.Maybe.same_u32(S.Phase.pending(S.Ue.phase(u)), Some{assoc}), False{}, e)
      %se : {N.Owner.check(u, Bool.and(_, Bool.and(Tb.Table.present(B.Digits(), S.Ue.supi(u)), Bool.not(U32.is_eq(S.Ue.assoc(u), assoc))))) == None{} : Maybe<&2, S.Ue>}
      {==}

def Hp.none_aimed(+m: Maybe<&2, S.Ue>, +assoc: U32, +e: {S.Ue.pending(m) == None{} : Maybe<&2, U32>}) -> {Ho.Ho.pending(m, assoc) == None{} : Maybe<&2, S.Ue>}:
  match m:
    case None{}:
      {==}
    case Some{+u}:
      se = Equal.sym(Maybe<&2, U32>, S.Phase.pending(S.Ue.phase(u)), None{}, e)
      %se : {N.Owner.check(u, Bool.and(S.Maybe.same_u32(_, Some{assoc}), Bool.and(Tb.Table.present(B.Digits(), S.Ue.supi(u)), Bool.not(U32.is_eq(S.Ue.assoc(u), assoc))))) == None{} : Maybe<&2, S.Ue>}
      {==}

# amf.handover.owner_only
# -----------------------

def Hp.oo_required(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +kind: G.HandoverType(), +cause: G.Cause, +id: G.TargetID, +direct: Maybe<&2, G.DirectForwardingPathAvailability()>, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 12, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverRequired.view(ies) == Done{V.HandoverRequired.View{amf, ran, kind, cause, id, direct, items, container}} : Result<&2, &2, B.Err, V.HandoverRequired.View>}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), R.Route.dispatch(st, assoc, stream, U32.to_nat(0), U32.to_nat(12), ies, entropy), Hp.dispatch(st, entropy, assoc, stream, len, bytes, 0, 12, crit, value, ies, c, ep, ei))
  %sr : {K.Kernel.state(_) == st : S.State}
  sv = Equal.sym(Result<&2, &2, B.Err, V.HandoverRequired.View>, V.HandoverRequired.view(ies), Done{V.HandoverRequired.View{amf, ran, kind, cause, id, direct, items, container}}, ev)
  %sv : {K.Kernel.state(N.Step.of(st, Ho.Ho.required_of_view(st, assoc, _))) == st : S.State}
  sid = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sid : {K.Kernel.state(N.Step.of(st, Ho.Ho.required_key(st, assoc, ran, kind, cause, id, items, container, _))) == st : S.State}
  so = Equal.sym(Maybe<&2, S.Ue>, N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran), None{}, eo)
  %so : {K.Kernel.state(N.Step.of(st, Ho.Ho.required_ue(st, assoc, k, kind, cause, id, items, container, _))) == st : S.State}
  {==}

def Hp.oo_cancel(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +cause: G.Cause, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 10, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverCancel.view(ies) == Done{V.HandoverCancel.View{amf, ran, cause}} : Result<&2, &2, B.Err, V.HandoverCancel.View>}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), R.Route.dispatch(st, assoc, stream, U32.to_nat(0), U32.to_nat(10), ies, entropy), Hp.dispatch(st, entropy, assoc, stream, len, bytes, 0, 10, crit, value, ies, c, ep, ei))
  %sr : {K.Kernel.state(_) == st : S.State}
  sv = Equal.sym(Result<&2, &2, B.Err, V.HandoverCancel.View>, V.HandoverCancel.view(ies), Done{V.HandoverCancel.View{amf, ran, cause}}, ev)
  %sv : {K.Kernel.state(N.Step.of(st, Ho.Ho.cancel_of_view(st, assoc, _))) == st : S.State}
  sid = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sid : {K.Kernel.state(N.Step.of(st, Ho.Ho.cancel_key(st, assoc, ran, _))) == st : S.State}
  so = Equal.sym(Maybe<&2, S.Ue>, N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran), None{}, eo)
  %so : {K.Kernel.state(N.Step.of(st, Ho.Ho.cancel_ue(assoc, k, _))) == st : S.State}
  {==}

def Hp.oo_status(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +status: G.RANStatusTransfer_TransparentContainer, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 49, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.UplinkRANStatusTransfer.view(ies) == Done{V.UplinkRANStatusTransfer.View{amf, ran, status}} : Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View>}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), R.Route.dispatch(st, assoc, stream, U32.to_nat(0), U32.to_nat(49), ies, entropy), Hp.dispatch(st, entropy, assoc, stream, len, bytes, 0, 49, crit, value, ies, c, ep, ei))
  %sr : {K.Kernel.state(_) == st : S.State}
  sv = Equal.sym(Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View>, V.UplinkRANStatusTransfer.view(ies), Done{V.UplinkRANStatusTransfer.View{amf, ran, status}}, ev)
  %sv : {K.Kernel.state(N.Step.of(st, Ho.Ho.status_of_view(st, assoc, _))) == st : S.State}
  sid = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sid : {K.Kernel.state(N.Step.of(st, Ho.Ho.status_key(st, assoc, ran, status, _))) == st : S.State}
  so = Equal.sym(Maybe<&2, S.Ue>, N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran), None{}, eo)
  %so : {K.Kernel.state(N.Step.of(st, Ho.Ho.status_ue(assoc, k, status, _))) == st : S.State}
  {==}

# The target's answers name a context; with no handover pending to the
# association they come from, the context is not found.
def Hp.oo_ack(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +admitted: G.PDUSessionResourceAdmittedList(), +failed: Maybe<&2, G.PDUSessionResourceFailedToSetupListHOAck()>, +back: B.Bytes(), +diag: Maybe<&2, G.CriticalityDiagnostics>, +npn: Maybe<&2, G.NPN_AccessInformation>, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {Ho.Ho.for_target(st, assoc, k) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverRequestAcknowledge.view(ies) == Done{V.HandoverRequestAcknowledge.View{amf, ran, admitted, failed, back, diag, npn}} : Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View>}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), R.Route.dispatch(st, assoc, stream, U32.to_nat(1), U32.to_nat(13), ies, entropy), Hp.dispatch(st, entropy, assoc, stream, len, bytes, 1, 13, crit, value, ies, c, ep, ei))
  %sr : {_ == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sv = Equal.sym(Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View>, V.HandoverRequestAcknowledge.view(ies), Done{V.HandoverRequestAcknowledge.View{amf, ran, admitted, failed, back, diag, npn}}, ev)
  %sv : {N.Step.of(st, Ho.Ho.ack_of_view(st, assoc, stream, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sid = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sid : {N.Step.of(st, Ho.Ho.ack_key(st, assoc, stream, ran, admitted, back, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sn = Equal.sym(Maybe<&2, S.Ue>, Ho.Ho.for_target(st, assoc, k), None{}, en)
  %sn : {N.Step.of(st, Ho.Ho.ack_ue(assoc, stream, k, ran, admitted, back, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  {==}

def Hp.oo_failure(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +k: U32, +cause: G.Cause, +diag: Maybe<&2, G.CriticalityDiagnostics>, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {Ho.Ho.for_target(st, assoc, k) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{2, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverFailure.view(ies) == Done{V.HandoverFailure.View{amf, cause, diag}} : Result<&2, &2, B.Err, V.HandoverFailure.View>}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), R.Route.dispatch(st, assoc, stream, U32.to_nat(2), U32.to_nat(13), ies, entropy), Hp.dispatch(st, entropy, assoc, stream, len, bytes, 2, 13, crit, value, ies, c, ep, ei))
  %sr : {_ == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sv = Equal.sym(Result<&2, &2, B.Err, V.HandoverFailure.View>, V.HandoverFailure.view(ies), Done{V.HandoverFailure.View{amf, cause, diag}}, ev)
  %sv : {N.Step.of(st, Ho.Ho.failure_of_view(st, assoc, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sid = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sid : {N.Step.of(st, Ho.Ho.failure_key(st, assoc, cause, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sn = Equal.sym(Maybe<&2, S.Ue>, Ho.Ho.for_target(st, assoc, k), None{}, en)
  %sn : {N.Step.of(st, Ho.Ho.failure_ue(assoc, k, cause, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  {==}

def Hp.oo_notify(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +uli: G.UserLocationInformation, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {Ho.Ho.for_target(st, assoc, k) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 11, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverNotify.view(ies) == Done{V.HandoverNotify.View{amf, ran, uli}} : Result<&2, &2, B.Err, V.HandoverNotify.View>}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), R.Route.dispatch(st, assoc, stream, U32.to_nat(0), U32.to_nat(11), ies, entropy), Hp.dispatch(st, entropy, assoc, stream, len, bytes, 0, 11, crit, value, ies, c, ep, ei))
  %sr : {_ == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sv = Equal.sym(Result<&2, &2, B.Err, V.HandoverNotify.View>, V.HandoverNotify.view(ies), Done{V.HandoverNotify.View{amf, ran, uli}}, ev)
  %sv : {N.Step.of(st, Ho.Ho.notify_of_view(st, assoc, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sid = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sid : {N.Step.of(st, Ho.Ho.notify_key(st, assoc, ran, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  sn = Equal.sym(Maybe<&2, S.Ue>, Ho.Ho.for_target(st, assoc, k), None{}, en)
  %sn : {N.Step.of(st, Ho.Ho.notify_ue(st, assoc, k, ran, _)) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}
  {==}


def Hp.oo_state(+st: S.State, +assoc: U32, +o: N.Step(), +e: {o == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}) -> {K.Kernel.state(o) == st : S.State}:
  se = Equal.sym(N.Step(), o, (st, N.Ngap.unknown_ue(assoc)), e)
  %se : {K.Kernel.state(_) == st : S.State}
  {==}

def L.amf.handover.owner_only(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, kind, cause, id, direct, items, container, status, admitted, failed, back, diag, npn, uli, eid, ei):
  +m = Tb.Table.get(S.Ue, k, S.State.ues(st))
  (+eo => (ep => ev => Hp.oo_required(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, kind, cause, id, direct, items, container, eid, ei, eo, ep, ev), (ep => ev => Hp.oo_cancel(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, cause, eid, ei, eo, ep, ev), ep => ev => Hp.oo_status(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, status, eid, ei, eo, ep, ev))), +en => (ep => ev => Hp.oo_state(st, assoc, K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), Hp.oo_ack(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, admitted, failed, back, diag, npn, eid, ei, Hp.not_aimed(m, assoc, en), ep, ev)), (ep => ev => Hp.oo_state(st, assoc, K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), Hp.oo_failure(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, cause, diag, eid, ei, Hp.not_aimed(m, assoc, en), ep, ev)), ep => ev => Hp.oo_state(st, assoc, K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), Hp.oo_notify(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, uli, eid, ei, Hp.not_aimed(m, assoc, en), ep, ev)))))

# amf.handover.responses_correlated
# ---------------------------------

def Hp.pair_l(+m: Maybe<&2, S.Ue>, +u: S.Ue, -Q: Type, pr: {m == Some{u} : Maybe<&2, S.Ue>} & Q) -> {m == Some{u} : Maybe<&2, S.Ue>}:
  match pr:
    case (+e, q):
      e

# A context whose phase holds no pending handover.
def Hp.kept_none(+st: S.State, +k: U32, +u: S.Ue, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +epu: {S.Ue.phase(u) == p : S.Phase}, +en: {S.Phase.pending(p) == None{} : Maybe<&2, U32>}) -> {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(st))) == None{} : Maybe<&2, U32>}:
  sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{u}, eg)
  %sg : {S.Ue.pending(_) == None{} : Maybe<&2, U32>}
  sp = Equal.sym(S.Phase, S.Ue.phase(u), p, epu)
  %sp : {S.Phase.pending(_) == None{} : Maybe<&2, U32>}
  en

# The context rephased under its key into a phase with no handover pending.
def Hp.rephased_none(+st: S.State, +k: U32, +u: S.Ue, +q: S.Phase, +acts: List<&2, N.Act>, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +en: {S.Phase.pending(q) == None{} : Maybe<&2, U32>}) -> {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, (S.Rephase{k, q}, acts)))))) == None{} : Maybe<&2, U32>}:
  sr = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, (S.Rephase{k, q}, acts)))), PT.Tk.ues(S.Rephase{k, q}, S.State.ues(st)), PT.Tk.render(st, (S.Rephase{k, q}, acts)))
  %sr : {S.Ue.pending(Tb.Table.get(S.Ue, k, _)) == None{} : Maybe<&2, U32>}
  sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.Ues.rephase(k, q, S.State.ues(st))), Some{S.Ue.with_phase(u, q)}, PT.Rephase.self(k, q, u, S.State.ues(st), eg))
  %sg : {S.Ue.pending(_) == None{} : Maybe<&2, U32>}
  sp = Equal.sym(S.Phase, S.Ue.phase(S.Ue.with_phase(u, q)), q, Hp.phase_with(u, q))
  %sp : {S.Phase.pending(_) == None{} : Maybe<&2, U32>}
  en

def Hp.cancel_pending(+st: S.State, +k: U32, +u: S.Ue, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +epu: {S.Ue.phase(u) == p : S.Phase}) -> {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Ho.Ho.cancel_phase(k, u, p)))))) == None{} : Maybe<&2, U32>}:
  match p:
    case S.Handover{+ctx, +nh, source, +leg}:
      +x : N.Act = N.UeSend{S.Ue.assoc(u), S.Ue.stream(u), k, Ho.Ho.cancel_ack(k, S.Ue.ran_id(u))}
      Hp.rephased_none(st, k, u, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}, x <> List.append(&2, N.Act, Ho.Ho.drop(k, leg, Ho.Ho.radio(G.CauseRadioNetwork.handover_cancelled())), [N.TimerCancel{k}, N.Note{F.Info{}, "NGAP: Handover Cancel; the target released"}]), eg, {==})
    case S.Created{}:
      Hp.kept_none(st, k, u, S.Created{}, eg, epu, {==})
    case S.Identifying{guard}:
      Hp.kept_none(st, k, u, S.Identifying{guard}, eg, epu, {==})
    case S.Authenticating{guard, av, resynced, supi}:
      Hp.kept_none(st, k, u, S.Authenticating{guard, av, resynced, supi}, eg, epu, {==})
    case S.SecurityMode{guard, ctx, k_amf}:
      Hp.kept_none(st, k, u, S.SecurityMode{guard, ctx, k_amf}, eg, epu, {==})
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      Hp.kept_none(st, k, u, S.ContextSetup{guard, ctx, nh, response, complete}, eg, epu, {==})
    case S.Registered{ctx, nh, released}:
      Hp.kept_none(st, k, u, S.Registered{ctx, nh, released}, eg, epu, {==})
    case S.Switching{guard, ctx, nh, released}:
      Hp.kept_none(st, k, u, S.Switching{guard, ctx, nh, released}, eg, epu, {==})
    case S.Releasing{guard}:
      Hp.kept_none(st, k, u, S.Releasing{guard}, eg, epu, {==})

def Hp.rc_cancel(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +u: S.Ue, +cause: G.Cause, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 10, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverCancel.view(ies) == Done{V.HandoverCancel.View{amf, ran, cause}} : Result<&2, &2, B.Err, V.HandoverCancel.View>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == Some{u} : Maybe<&2, S.Ue>}) -> {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == None{} : Maybe<&2, U32>}:
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), R.Route.dispatch(st, assoc, stream, U32.to_nat(0), U32.to_nat(10), ies, entropy), Hp.dispatch(st, entropy, assoc, stream, len, bytes, 0, 10, crit, value, ies, c, ep, ei))
  %sr : {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(_)))) == None{} : Maybe<&2, U32>}
  sv = Equal.sym(Result<&2, &2, B.Err, V.HandoverCancel.View>, V.HandoverCancel.view(ies), Done{V.HandoverCancel.View{amf, ran, cause}}, ev)
  %sv : {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Ho.Ho.cancel_of_view(st, assoc, _)))))) == None{} : Maybe<&2, U32>}
  sid = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sid : {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Ho.Ho.cancel_key(st, assoc, ran, _)))))) == None{} : Maybe<&2, U32>}
  so = Equal.sym(Maybe<&2, S.Ue>, N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran), Some{u}, eo)
  %so : {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Ho.Ho.cancel_ue(assoc, k, _)))))) == None{} : Maybe<&2, U32>}
  Hp.cancel_pending(st, k, u, S.Ue.phase(u), Hp.pair_l(Tb.Table.get(S.Ue, k, S.State.ues(st)), u, {U32.is_eq(S.Ue.assoc(u), assoc) == True{} : Bool}, PT.Own.get(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran, u, eo)), {==})

def L.amf.handover.responses_correlated(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, u, cause, admitted, failed, back, diag, npn, uli, eid, ei):
  +m = Tb.Table.get(S.Ue, k, S.State.ues(st))
  (+en => (ep => ev => Hp.oo_ack(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, admitted, failed, back, diag, npn, eid, ei, Hp.none_aimed(m, assoc, en), ep, ev), (ep => ev => Hp.oo_failure(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, cause, diag, eid, ei, Hp.none_aimed(m, assoc, en), ep, ev), ep => ev => Hp.oo_notify(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, uli, eid, ei, Hp.none_aimed(m, assoc, en), ep, ev))), ep => ev => eo => Hp.rc_cancel(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, u, cause, eid, ei, ep, ev, eo))

# One owner
# ---------
# In every reachable state no two contexts share a key or an identity, and a
# context with a pending handover is owned by the source it started from,
# which is not its target. Contexts are written only by Put, with a phase that
# keeps this (Lv.homed), and by Rephase, into a phase that fits the context
# it rephases: so no step, of any procedure, moves a context with a handover
# pending to another association.

def So.inv(+st0: S.State, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session)) -> Bool:
  Bool.and(S.Ues.unique(ues), S.Ues.single(ues))

def So.keep(+k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), +b: Bool, +hv: {S.Ue.single(v) == True{} : Bool}, +hr: {S.Ues.single(rest) == True{} : Bool}) -> {S.Ues.single(Tb.Table.keep(S.Ue, k, v, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      P.Bool.and_intro(S.Ue.single(v), S.Ues.single(rest), hv, hr)
    case False{}:
      hr

def So.sift(+s: S.Sieve, +ues: Tb.Table(S.Ue), +e: {S.Ues.single(ues) == True{} : Bool}) -> {S.Ues.single(S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      So.keep(k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), P.Bool.and_true_l(S.Ue.single(v), S.Ues.single(more), e), So.sift(s, more, P.Bool.and_true_r(S.Ue.single(v), S.Ues.single(more), e)))

# A key no row holds is rephased nowhere.
def So.untouched_row(+key: U32, +w: S.Ue, +p: S.Phase, +k: U32, +v: S.Ue, +more: Tb.Table(S.Ue), +b: Bool, +eb: {U32.is_eq(k, key) == b : Bool}, +ec: {Bool.not(S.Row.conflicts(key, w, k, v)) == True{} : Bool}, ih: {S.Ues.rephase(key, p, more) == more : Tb.Table(S.Ue)}) -> {(k, S.Ue.rephase_if(v, p, U32.is_eq(k, key))) <> S.Ues.rephase(key, p, more) == (k, v) <> more : Tb.Table(S.Ue)}:
  match b:
    case True{}:
      en : {Bool.not(Bool.or(True{}, S.Ue.conflicts(w, v))) == True{} : Bool} = (%eb : {Bool.not(Bool.or(_, S.Ue.conflicts(w, v))) == True{} : Bool}; ec)
      Empty.absurd({(k, S.Ue.rephase_if(v, p, U32.is_eq(k, key))) <> S.Ues.rephase(key, p, more) == (k, v) <> more : Tb.Table(S.Ue)}, P.Refute.bool(en))
    case False{}:
      sb = Equal.sym(Bool, U32.is_eq(k, key), False{}, eb)
      si = Equal.sym(Tb.Table(S.Ue), S.Ues.rephase(key, p, more), more, ih)
      %sb : {(k, S.Ue.rephase_if(v, p, _)) <> S.Ues.rephase(key, p, more) == (k, v) <> more : Tb.Table(S.Ue)}
      %si : {(k, v) <> _ == (k, v) <> more : Tb.Table(S.Ue)}
      {==}

def So.untouched(+key: U32, +w: S.Ue, +p: S.Phase, +more: Tb.Table(S.Ue), +ec: {S.Ues.clear(key, w, more) == True{} : Bool}) -> {S.Ues.rephase(key, p, more) == more : Tb.Table(S.Ue)}:
  match more:
    case Nil{}:
      {==}
    case (+k, +v) <> +rest:
      So.untouched_row(key, w, p, k, v, rest, U32.is_eq(k, key), {==}, P.Bool.and_true_l(Bool.not(S.Row.conflicts(key, w, k, v)), S.Ues.clear(key, w, rest), ec), So.untouched(key, w, p, rest, P.Bool.and_true_r(Bool.not(S.Row.conflicts(key, w, k, v)), S.Ues.clear(key, w, rest), ec)))

def So.rephase_row(+key: U32, +p: S.Phase, +k0: U32, +w: S.Ue, +more: Tb.Table(S.Ue), +b: Bool, +eb: {U32.is_eq(k0, key) == b : Bool}, +ec: {S.Ues.clear(k0, w, more) == True{} : Bool}, +ew: {S.Ue.single(w) == True{} : Bool}, +em: {S.Ues.single(more) == True{} : Bool}, +ef: {S.Ue.fits(p, Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, key, more), b)) == True{} : Bool}, ih: {S.Ue.fits(p, Tb.Table.get(S.Ue, key, more)) == True{} : Bool} -> {S.Ues.single(S.Ues.rephase(key, p, more)) == True{} : Bool}) -> {Bool.and(S.Ue.single(S.Ue.rephase_if(w, p, U32.is_eq(k0, key))), S.Ues.single(S.Ues.rephase(key, p, more))) == True{} : Bool}:
  match b:
    case True{}:
      sb = Equal.sym(Bool, U32.is_eq(k0, key), True{}, eb)
      %sb : {Bool.and(S.Ue.single(S.Ue.rephase_if(w, p, _)), S.Ues.single(S.Ues.rephase(key, p, more))) == True{} : Bool}
      ek = P.U32.eq_of_is_eq(k0, key, eb)
      ec2 : {S.Ues.clear(key, w, more) == True{} : Bool} = (%ek : {S.Ues.clear(_, w, more) == True{} : Bool}; ec)
      ss = Equal.sym(Tb.Table(S.Ue), S.Ues.rephase(key, p, more), more, So.untouched(key, w, p, more, ec2))
      %ss : {Bool.and(S.Ue.single(S.Ue.with_phase(w, p)), S.Ues.single(_)) == True{} : Bool}
      sw = Equal.sym(Bool, S.Ue.single(S.Ue.with_phase(w, p)), S.Phase.owned_by(p, S.Ue.assoc(w)), PL.Lv.s_phase(w, p))
      %sw : {Bool.and(_, S.Ues.single(more)) == True{} : Bool}
      P.Bool.and_intro(S.Phase.owned_by(p, S.Ue.assoc(w)), S.Ues.single(more), ef, em)
    case False{}:
      sb = Equal.sym(Bool, U32.is_eq(k0, key), False{}, eb)
      %sb : {Bool.and(S.Ue.single(S.Ue.rephase_if(w, p, _)), S.Ues.single(S.Ues.rephase(key, p, more))) == True{} : Bool}
      P.Bool.and_intro(S.Ue.single(w), S.Ues.single(S.Ues.rephase(key, p, more)), ew, ih(ef))

def So.rephase(+key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +eu: {S.Ues.unique(ues) == True{} : Bool}, +es: {S.Ues.single(ues) == True{} : Bool}, +ef: {S.Ue.fits(p, Tb.Table.get(S.Ue, key, ues)) == True{} : Bool}) -> {S.Ues.single(S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k0, +w) <> +more:
      +ecl = P.Bool.and_true_l(S.Ues.clear(k0, w, more), S.Ues.unique(more), eu)
      +eum = P.Bool.and_true_r(S.Ues.clear(k0, w, more), S.Ues.unique(more), eu)
      +ew = P.Bool.and_true_l(S.Ue.single(w), S.Ues.single(more), es)
      +em = P.Bool.and_true_r(S.Ue.single(w), S.Ues.single(more), es)
      So.rephase_row(key, p, k0, w, more, U32.is_eq(k0, key), {==}, ecl, ew, em, ef, e => So.rephase(key, p, more, eum, em, e))

def So.parts(+ues: Tb.Table(S.Ue), +e: {Bool.and(S.Ues.unique(ues), S.Ues.single(ues)) == True{} : Bool}) -> {S.Ues.unique(ues) == True{} : Bool}:
  P.Bool.and_true_l(S.Ues.unique(ues), S.Ues.single(ues), e)

def So.part2(+ues: Tb.Table(S.Ue), +e: {Bool.and(S.Ues.unique(ues), S.Ues.single(ues)) == True{} : Bool}) -> {S.Ues.single(ues) == True{} : Bool}:
  P.Bool.and_true_r(S.Ues.unique(ues), S.Ues.single(ues), e)

def So.tx_put(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {So.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  +hs = P.Bool.and_true_r(S.Phase.guarded(S.Ue.phase(ue)), S.Ue.single(ue), P.Bool.and_true_r(PL.Lv.keyed(st0, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), S.Ue.single(ue)), h))
  P.Bool.and_intro(S.Ues.unique(S.Ues.put(key, ue, ues)), S.Ues.single(S.Ues.put(key, ue, ues)), PL.Un.tx_put(st0, ep, key, ue, ues, ss, So.parts(ues, e), h), P.Bool.and_intro(S.Ue.single(ue), S.Ues.single(S.Ues.sift(S.Clear{key, ue}, ues)), hs, So.sift(S.Clear{key, ue}, ues, So.part2(ues, e))))

def So.tx_rephase(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {So.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.unique(S.Ues.rephase(key, p, ues)), S.Ues.single(S.Ues.rephase(key, p, ues)), PL.Un.tx_rephase(st0, ep, key, p, ues, ss, So.parts(ues, e), h), So.rephase(key, p, ues, So.parts(ues, e), So.part2(ues, e), P.Bool.and_true_r(S.Phase.guarded(p), S.Ue.fits(p, Tb.Table.get(S.Ue, key, ues)), h)))

def So.tx_del(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}) -> {So.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.unique(S.Ues.del(key, ues)), S.Ues.single(S.Ues.del(key, ues)), PL.Un.tx_del(st0, ep, key, ues, ss, So.parts(ues, e)), So.sift(S.Except{key}, ues, So.part2(ues, e)))

def So.tx_put_session(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homed(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {So.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  e

def So.tx_revar(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.revar_ok(st0, v) == True{} : Bool}) -> {So.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  e

def So.tx_del_session(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}) -> {So.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  e

def So.down(+st: S.State, +assoc: U32, +e: {Bool.and(S.Ues.unique(S.State.ues(st)), S.Ues.single(S.State.ues(st))) == True{} : Bool}) -> {Bool.and(S.Ues.unique(S.State.ues(K.Kernel.state(K.Kernel.drop(st, assoc)))), S.Ues.single(S.State.ues(K.Kernel.state(K.Kernel.drop(st, assoc))))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, n4}:
      P.Bool.and_intro(S.Ues.unique(S.Ues.sift(S.Others{assoc}, ues)), S.Ues.single(S.Ues.sift(S.Others{assoc}, ues)), PK.Unique.sift(S.Others{assoc}, ues, So.parts(ues, e)), So.sift(S.Others{assoc}, ues, So.part2(ues, e)))

def So.step(+st: S.State, +ev: F.Evt, +entropy: B.Bytes(), +e: {Bool.and(S.Ues.unique(S.State.ues(st)), S.Ues.single(S.State.ues(st))) == True{} : Bool}) -> {Bool.and(S.Ues.unique(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy)))), S.Ues.single(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))))) == True{} : Bool}:
  PL.Inv.step(ues => ss => Bool.and(S.Ues.unique(ues), S.Ues.single(ues)), st, ev, entropy, e, tx => st2 => e2 => h => PL.Inv.tx(~So.inv, ~PL.Inv.none, ~So.tx_put, ~So.tx_rephase, ~So.tx_del, ~So.tx_put_session, ~So.tx_revar, ~So.tx_del_session, st, {==}, tx, st2, e2, h), tx => st2 => e2 => h => PL.Inv.tx(~So.inv, ~PL.Inv.none, ~So.tx_put, ~So.tx_rephase, ~So.tx_del, ~So.tx_put_session, ~So.tx_revar, ~So.tx_del_session, st, {==}, tx, st2, e2, h), a => s => e1 => So.down(s, a, e1))

# amf.handover.single_owner
# -------------------------

def Hp.so_required(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +j: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 12, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool}:
  Hp.pdu(o => {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(o)))) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 0, 12, crit, value, ep, Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), +ies => Hp.same_step(st, Ho.Ho.required_of_view(st, assoc, V.HandoverRequired.view(ies)), j, Hp.calm_of_fine(j, Ho.Ho.required_of_view(st, assoc, V.HandoverRequired.view(ies)), Hp.required(st, j, assoc, V.HandoverRequired.view(ies)))))

def Hp.so_ack(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +j: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool}:
  Hp.pdu(o => {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(o)))) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 1, 13, crit, value, ep, Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), +ies => Hp.same_step(st, Ho.Ho.ack_of_view(st, assoc, stream, V.HandoverRequestAcknowledge.view(ies)), j, Hp.calm_of_fine(j, Ho.Ho.ack_of_view(st, assoc, stream, V.HandoverRequestAcknowledge.view(ies)), Hp.ack(st, j, assoc, stream, V.HandoverRequestAcknowledge.view(ies)))))

def Hp.so_failure(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +j: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{2, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool}:
  Hp.pdu(o => {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(o)))) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 2, 13, crit, value, ep, Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), +ies => Hp.same_step(st, Ho.Ho.failure_of_view(st, assoc, V.HandoverFailure.view(ies)), j, Hp.failure(st, assoc, V.HandoverFailure.view(ies))))

def Hp.so_cancel(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +j: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 10, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool}:
  Hp.pdu(o => {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(o)))) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 0, 10, crit, value, ep, Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), +ies => Hp.same_step(st, Ho.Ho.cancel_of_view(st, assoc, V.HandoverCancel.view(ies)), j, Hp.cancel(st, assoc, V.HandoverCancel.view(ies))))

def Hp.so_status(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +j: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 49, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool}:
  Hp.pdu(o => {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(o)))) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 0, 49, crit, value, ep, Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), +ies => Hp.same_step(st, Ho.Ho.status_of_view(st, assoc, V.UplinkRANStatusTransfer.view(ies)), j, Hp.status(st, assoc, V.UplinkRANStatusTransfer.view(ies))))

# The guard of a pending handover only rephases its context.
def Hp.expired_calm(+st: S.State, +k: U32, +u: S.Ue, +t: U32, +p: S.Phase, +e: {S.Phase.pending(p) == Some{t} : Maybe<&2, U32>}) -> {Hp.calm(Gmm.Gmm.expired(st, k, u, p)) == True{} : Bool}:
  match p:
    case S.Handover{+ctx, +nh, source, +leg}:
      {==}
    case S.Created{}:
      Empty.absurd({Hp.calm(Gmm.Gmm.expired(st, k, u, S.Created{})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.Identifying{guard}:
      Empty.absurd({Hp.calm(Gmm.Gmm.expired(st, k, u, S.Identifying{guard})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.Authenticating{guard, av, resynced, supi}:
      Empty.absurd({Hp.calm(Gmm.Gmm.expired(st, k, u, S.Authenticating{guard, av, resynced, supi})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.SecurityMode{guard, ctx, k_amf}:
      Empty.absurd({Hp.calm(Gmm.Gmm.expired(st, k, u, S.SecurityMode{guard, ctx, k_amf})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      Empty.absurd({Hp.calm(Gmm.Gmm.expired(st, k, u, S.ContextSetup{guard, ctx, nh, response, complete})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.Registered{ctx, nh, released}:
      Empty.absurd({Hp.calm(Gmm.Gmm.expired(st, k, u, S.Registered{ctx, nh, released})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.Switching{guard, ctx, nh, released}:
      Empty.absurd({Hp.calm(Gmm.Gmm.expired(st, k, u, S.Switching{guard, ctx, nh, released})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.Releasing{guard}:
      Empty.absurd({Hp.calm(Gmm.Gmm.expired(st, k, u, S.Releasing{guard})) == True{} : Bool}, P.Refute.none_some(U32, t, e))

def Hp.fired_calm(+st: S.State, +k: U32, +t: U32, +m: Maybe<&2, S.Ue>, +e: {S.Ue.pending(m) == Some{t} : Maybe<&2, U32>}) -> {Hp.calm(K.Kernel.fired_ue(st, k, m)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Hp.calm(K.Kernel.fired_ue(st, k, None{})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case Some{+u}:
      Hp.expired_calm(st, k, u, t, S.Ue.phase(u), e)

def Hp.so_timer(+st: S.State, +entropy: B.Bytes(), +k: U32, +t: U32, +j: U32, +e: {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(st))) == Some{t} : Maybe<&2, U32>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.TimerFired{k}, entropy))))) == True{} : Bool}:
  Hp.same_step(st, K.Kernel.fired(st, k), j, Hp.fired_calm(st, k, t, Tb.Table.get(S.Ue, k, S.State.ues(st)), e))

# Handover Notify: the context keeps its owner, or moves to the target of the
# handover pending.
def Hp.Moved(+st: S.State, +k: U32, +t: U32, +o: N.GOut()) -> Type:
  {Bool.or(S.Ue.same_owner(Tb.Table.get(S.Ue, k, S.State.ues(st)), Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, o))))), S.Ue.on(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, o)))), t)) == True{} : Bool}

def Hp.moved_keep(+st: S.State, +k: U32, +t: U32, +acts: List<&2, N.Act>) -> Hp.Moved(st, k, t, (S.Keep{}, acts)):
  +g = Tb.Table.get(S.Ue, k, S.State.ues(st))
  P.Bool.or_l(S.Ue.same_owner(g, g), S.Ue.on(g, t), Hp.same_refl(g))

def Hp.complete_moved(+st: S.State, +assoc: U32, +k: U32, +t: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +ok: Bool, +eat: {U32.is_eq(assoc, t) == True{} : Bool}) -> Hp.Moved(st, k, t, Ho.Ho.complete(st, assoc, k, ue, ctx, nh, r, s, ts, ok)):
  match ok:
    case False{}:
      Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))
    case True{}:
      +ues = S.State.ues(st)
      +g = Tb.Table.get(S.Ue, k, ues)
      +rows = S.Sessions.of_ue(k, S.State.sessions(st))
      +v = S.Ue.moved(ue, assoc, r, s, S.Registered{ctx, nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}})
      +a = Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st))
      +b : N.GOut() = (S.Put{k, v}, [])
      +more : List<&2, N.Act> = [N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), k, S.Ue.ran_id(ue), Ho.Ho.radio(G.CauseRadioNetwork.successful_handover())}, N.TimerCancel{k}, N.Note{F.Info{}, "NGAP: Handover Notify; the UE moved to the target"}]
      +o = N.Out.also(N.Out.join(a, b), more)
      e12 = Equal.trans(S.Tx, PT.Tk.tx(o), PT.Tk.tx(N.Out.join(a, b)), S.Both{PT.Tk.tx(a), S.Put{k, v}}, PL.Lv.tx_also(N.Out.join(a, b), more), PT.Tk.tx_join(a, b))
      sr = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, o))), PT.Tk.ues(PT.Tk.tx(o), ues), PT.Tk.render(st, o))
      %sr : {Bool.or(S.Ue.same_owner(g, Tb.Table.get(S.Ue, k, _)), S.Ue.on(Tb.Table.get(S.Ue, k, _), t)) == True{} : Bool}
      se = Equal.sym(S.Tx, PT.Tk.tx(o), S.Both{PT.Tk.tx(a), S.Put{k, v}}, e12)
      %se : {Bool.or(S.Ue.same_owner(g, Tb.Table.get(S.Ue, k, PT.Tk.ues(_, ues))), S.Ue.on(Tb.Table.get(S.Ue, k, PT.Tk.ues(_, ues)), t)) == True{} : Bool}
      sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.Ues.put(k, v, PT.Tk.ues(PT.Tk.tx(a), ues))), Some{v}, PPs.Mv.get_put(k, v, PT.Tk.ues(PT.Tk.tx(a), ues)))
      %sg : {Bool.or(S.Ue.same_owner(g, _), S.Ue.on(_, t)) == True{} : Bool}
      sa = Equal.sym(U32, S.Ue.assoc(v), assoc, Hp.assoc_moved(ue, assoc, r, s, S.Registered{ctx, nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}}))
      %sa : {Bool.or(S.Ue.same_owner(g, Some{v}), U32.is_eq(_, t)) == True{} : Bool}
      P.Bool.or_r(S.Ue.same_owner(g, Some{v}), U32.is_eq(assoc, t), eat)

def Hp.notify_moved_phase(+st: S.State, +assoc: U32, +k: U32, +t: U32, +ue: S.Ue, +ran: B.Bytes(), +p: S.Phase, +eat: {U32.is_eq(assoc, t) == True{} : Bool}) -> Hp.Moved(st, k, t, Ho.Ho.notify_phase(st, assoc, k, ue, ran, p)):
  match p:
    case S.Handover{+ctx, +nh, source, leg}:
      match leg:
        case S.Asked{t2}:
          Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))
        case S.Acked{t2, +r, +s, +ts}:
          Hp.complete_moved(st, assoc, k, t, ue, ctx, nh, r, s, ts, Bool.and(B.bytes_eq(r, ran), S.Ues.ran_free(k, assoc, r, S.State.ues(st))), eat)
    case S.Created{}:
      Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))
    case S.Identifying{guard}:
      Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))
    case S.Authenticating{guard, av, resynced, supi}:
      Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))
    case S.SecurityMode{guard, ctx, k_amf}:
      Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))
    case S.Registered{ctx, nh, released}:
      Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))
    case S.Switching{guard, ctx, nh, released}:
      Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))
    case S.Releasing{guard}:
      Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))

def Hp.notify_found(+st: S.State, +assoc: U32, +k: U32, +t: U32, +ue: S.Ue, +ran: B.Bytes(), +ep: {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(st))) == Some{t} : Maybe<&2, U32>}, pr: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>} & {Ho.Ho.aimed(ue, assoc) == True{} : Bool}) -> Hp.Moved(st, k, t, Ho.Ho.notify_phase(st, assoc, k, ue, ran, S.Ue.phase(ue))):
  match pr:
    case (+eg, +ea):
      ep2 : {S.Ue.pending(Some{ue}) == Some{t} : Maybe<&2, U32>} = (%eg : {S.Ue.pending(_) == Some{t} : Maybe<&2, U32>}; ep)
      h1 = P.Bool.and_true_l(S.Maybe.same_u32(S.Phase.pending(S.Ue.phase(ue)), Some{assoc}), Bool.and(Tb.Table.present(B.Digits(), S.Ue.supi(ue)), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc))), ea)
      eta : {U32.is_eq(t, assoc) == True{} : Bool} = (%ep2 : {S.Maybe.same_u32(_, Some{assoc}) == True{} : Bool}; h1)
      Hp.notify_moved_phase(st, assoc, k, t, ue, ran, S.Ue.phase(ue), Equal.trans(Bool, U32.is_eq(assoc, t), U32.is_eq(t, assoc), True{}, P.U32.sym(assoc, t), eta))

def Hp.notify_moved_ue(+st: S.State, +assoc: U32, +k: U32, +t: U32, +ran: B.Bytes(), +m: Maybe<&2, S.Ue>, +em: {Ho.Ho.for_target(st, assoc, k) == m : Maybe<&2, S.Ue>}, +ep: {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(st))) == Some{t} : Maybe<&2, U32>}) -> Hp.Moved(st, k, t, Ho.Ho.notify_ue(st, assoc, k, ran, m)):
  match m:
    case None{}:
      Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc))
    case Some{+ue}:
      Hp.notify_found(st, assoc, k, t, ue, ran, ep, PW.Walk.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ue, em))

def Hp.so_notify(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +uli: G.UserLocationInformation, +k: U32, +t: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 11, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +ev: {V.HandoverNotify.view(ies) == Done{V.HandoverNotify.View{amf, ran, uli}} : Result<&2, &2, B.Err, V.HandoverNotify.View>}, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +epend: {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(st))) == Some{t} : Maybe<&2, U32>}) -> {Bool.or(S.Ue.same_owner(Tb.Table.get(S.Ue, k, S.State.ues(st)), Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))), S.Ue.on(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))), t)) == True{} : Bool}:
  +g = Tb.Table.get(S.Ue, k, S.State.ues(st))
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), R.Route.dispatch(st, assoc, stream, U32.to_nat(0), U32.to_nat(11), ies, entropy), Hp.dispatch(st, entropy, assoc, stream, len, bytes, 0, 11, crit, value, ies, c, ep, ei))
  %sr : {Bool.or(S.Ue.same_owner(g, Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(_)))), S.Ue.on(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(_))), t)) == True{} : Bool}
  sv = Equal.sym(Result<&2, &2, B.Err, V.HandoverNotify.View>, V.HandoverNotify.view(ies), Done{V.HandoverNotify.View{amf, ran, uli}}, ev)
  %sv : Hp.Moved(st, k, t, Ho.Ho.notify_of_view(st, assoc, _))
  sid = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sid : Hp.Moved(st, k, t, Ho.Ho.notify_key(st, assoc, ran, _))
  Hp.notify_moved_ue(st, assoc, k, t, ran, Ho.Ho.for_target(st, assoc, k), {==}, epend)

def L.amf.handover.single_owner(st, ev, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, uli, j, k, t):
  ({==}, (e0 => So.step(st, ev, entropy, e0), (ep => Hp.so_required(st, entropy, assoc, stream, len, bytes, crit, value, j, ep), (ep => Hp.so_ack(st, entropy, assoc, stream, len, bytes, crit, value, j, ep), (ep => Hp.so_failure(st, entropy, assoc, stream, len, bytes, crit, value, j, ep), (ep => Hp.so_cancel(st, entropy, assoc, stream, len, bytes, crit, value, j, ep), (ep => Hp.so_status(st, entropy, assoc, stream, len, bytes, crit, value, j, ep), (e => Hp.so_timer(st, entropy, k, t, j, e), ep => ei => ev => eid => epend => Hp.so_notify(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, uli, k, t, ep, ei, ev, eid, epend)))))))))

# amf.handover.guarded
# --------------------

# Every phase with a handover pending holds its guard.
def Hp.timed_p(+p: S.Phase) -> {Bool.or(S.Phase.idle(p), Tb.Table.present(S.Guard, S.Phase.guard(p))) == True{} : Bool}:
  match p:
    case S.Created{}:
      {==}
    case S.Identifying{guard}:
      {==}
    case S.Authenticating{guard, av, resynced, supi}:
      {==}
    case S.SecurityMode{guard, ctx, k_amf}:
      {==}
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      {==}
    case S.Registered{ctx, nh, released}:
      {==}
    case S.Switching{guard, ctx, nh, released}:
      {==}
    case S.Handover{ctx, nh, source, leg}:
      {==}
    case S.Releasing{guard}:
      {==}

def Hp.timed(+ues: Tb.Table(S.Ue)) -> {S.Ues.timed(ues) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (k, +u) <> +more:
      P.Bool.and_intro(Bool.or(S.Phase.idle(S.Ue.phase(u)), Tb.Table.present(S.Guard, S.Ue.guard(u))), S.Ues.timed(more), Hp.timed_p(S.Ue.phase(u)), Hp.timed(more))

# The guard timers stay unique (state.ids.free), every step.
def Hp.timed_step(+st: S.State, +ev: F.Evt, +entropy: B.Bytes(), +e: {Bool.and(S.Ids.free(S.State.ues(st), S.State.sessions(st)), S.Sessions.owned(S.State.sessions(st), S.State.ues(st))) == True{} : Bool}) -> {Bool.and(S.Ues.timed(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy)))), S.Ids.free(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))), S.State.sessions(K.Kernel.state(K.Kernel.step(st, ev, entropy))))) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.timed(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy)))), S.Ids.free(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))), S.State.sessions(K.Kernel.state(K.Kernel.step(st, ev, entropy)))), Hp.timed(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy)))), PL.Inv.step(ues => ss => S.Ids.free(ues, ss), st, ev, entropy, P.Bool.and_true_l(S.Ids.free(S.State.ues(st), S.State.sessions(st)), S.Sessions.owned(S.State.sessions(st), S.State.ues(st)), e), tx => st2 => e2 => h => PL.Inv.tx(~PL.Id.inv, ~PL.Id.pre, ~PL.Id.tx_put, ~PL.Id.tx_rephase, ~PL.Id.tx_del, ~PL.Id.tx_put_session, ~PL.Id.tx_revar, ~PL.Id.tx_del_session, st, e, tx, st2, e2, h), tx => st2 => e2 => h => PL.Inv.tx(~PL.Id.inv, ~PL.Id.pre, ~PL.Id.tx_put, ~PL.Id.tx_rephase, ~PL.Id.tx_del, ~PL.Id.tx_put_session, ~PL.Id.tx_revar, ~PL.Id.tx_del_session, st, e, tx, st2, e2, h), a => s => e1 => PL.Id.down(s, a, e1)))

def Hp.g_guard(+p: S.Phase, +t: U32, +e: {S.Phase.pending(p) == Some{t} : Maybe<&2, U32>}) -> {Tb.Table.present(S.Guard, S.Phase.guard(p)) == True{} : Bool}:
  match p:
    case S.Handover{ctx, nh, source, leg}:
      {==}
    case S.Created{}:
      Empty.absurd({Tb.Table.present(S.Guard, S.Phase.guard(S.Created{})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.Identifying{guard}:
      Empty.absurd({Tb.Table.present(S.Guard, S.Phase.guard(S.Identifying{guard})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.Authenticating{guard, av, resynced, supi}:
      Empty.absurd({Tb.Table.present(S.Guard, S.Phase.guard(S.Authenticating{guard, av, resynced, supi})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.SecurityMode{guard, ctx, k_amf}:
      Empty.absurd({Tb.Table.present(S.Guard, S.Phase.guard(S.SecurityMode{guard, ctx, k_amf})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      Empty.absurd({Tb.Table.present(S.Guard, S.Phase.guard(S.ContextSetup{guard, ctx, nh, response, complete})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.Registered{ctx, nh, released}:
      Empty.absurd({Tb.Table.present(S.Guard, S.Phase.guard(S.Registered{ctx, nh, released})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.Switching{guard, ctx, nh, released}:
      Empty.absurd({Tb.Table.present(S.Guard, S.Phase.guard(S.Switching{guard, ctx, nh, released})) == True{} : Bool}, P.Refute.none_some(U32, t, e))
    case S.Releasing{guard}:
      Empty.absurd({Tb.Table.present(S.Guard, S.Phase.guard(S.Releasing{guard})) == True{} : Bool}, P.Refute.none_some(U32, t, e))

def Hp.or_mono(+x: Bool, +y: Bool, +z: Bool, +h: {Bool.or(x, y) == True{} : Bool}, f: {y == True{} : Bool} -> {z == True{} : Bool}) -> {Bool.or(x, z) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      f(h)

def Hp.starts_app(+k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +h: {N.Acts.starts(k, xs) == True{} : Bool}) -> {N.Acts.starts(k, List.append(&2, N.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, [], ys)) == True{} : Bool}, P.Refute.bool(h))
    case +a <> +more:
      Hp.or_mono(N.Act.starts(k, a), N.Acts.starts(k, more), N.Acts.starts(k, List.append(&2, N.Act, more, ys)), h, hm => Hp.starts_app(k, more, ys, hm))

# A phase change of another key leaves the row under k.
def Hp.other_row(+key: U32, +p: S.Phase, +k: U32, +k0: U32, +w: S.Ue, +more: Tb.Table(S.Ue), +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +ne: {U32.is_eq(key, k) == False{} : Bool}, ih: {Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, more)) == Tb.Table.get(S.Ue, k, more) : Maybe<&2, S.Ue>}) -> {Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, U32.is_eq(k0, key)), Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, more)), U32.is_eq(k0, k)) == Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, k, more), U32.is_eq(k0, k)) : Maybe<&2, S.Ue>}:
  match b:
    case True{}:
      se = Equal.sym(Bool, U32.is_eq(k0, k), True{}, eb)
      %se : {Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, U32.is_eq(k0, key)), Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, more)), _) == Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, k, more), _) : Maybe<&2, S.Ue>}
      sk = Equal.sym(U32, k0, k, P.U32.eq_of_is_eq(k0, k, eb))
      %sk : {Some{S.Ue.rephase_if(w, p, U32.is_eq(_, key))} == Some{w} : Maybe<&2, S.Ue>}
      e2 = Equal.trans(Bool, U32.is_eq(k, key), U32.is_eq(key, k), False{}, P.U32.sym(k, key), ne)
      s2 = Equal.sym(Bool, U32.is_eq(k, key), False{}, e2)
      %s2 : {Some{S.Ue.rephase_if(w, p, _)} == Some{w} : Maybe<&2, S.Ue>}
      {==}
    case False{}:
      se = Equal.sym(Bool, U32.is_eq(k0, k), False{}, eb)
      %se : {Tb.Table.hit(S.Ue, S.Ue.rephase_if(w, p, U32.is_eq(k0, key)), Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, more)), _) == Tb.Table.hit(S.Ue, w, Tb.Table.get(S.Ue, k, more), _) : Maybe<&2, S.Ue>}
      ih

def Hp.get_other(+key: U32, +p: S.Phase, +k: U32, +ues: Tb.Table(S.Ue), +ne: {U32.is_eq(key, k) == False{} : Bool}) -> {Tb.Table.get(S.Ue, k, S.Ues.rephase(key, p, ues)) == Tb.Table.get(S.Ue, k, ues) : Maybe<&2, S.Ue>}:
  match ues:
    case Nil{}:
      {==}
    case (+k0, +w) <> +more:
      Hp.other_row(key, p, k, k0, w, more, U32.is_eq(k0, k), {==}, ne, Hp.get_other(key, p, k, more, ne))

def Hp.g_rephase(+st: S.State, +k: U32, +key: U32, +p: S.Phase, +acts: List<&2, N.Act>, +b: Bool, +eb: {U32.is_eq(key, k) == b : Bool}, +e: {Bool.or(Bool.not(U32.is_eq(key, k)), N.Acts.starts(k, acts)) == True{} : Bool}) -> ({Tb.Table.get(S.Ue, k, S.State.ues(S.Tx.apply(S.Rephase{key, p}, st))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} -> Empty) -> {N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.Rephase{key, p}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.Rephase{key, p}, st))))) == True{} : Bool}:
  match b:
    case True{}:
      es : {Bool.or(Bool.not(True{}), N.Acts.starts(k, acts)) == True{} : Bool} = (%eb : {Bool.or(Bool.not(_), N.Acts.starts(k, acts)) == True{} : Bool}; e)
      ne => Hp.starts_app(k, acts, [], es)
    case False{}:
      ua = Equal.sym(Tb.Table(S.Ue), S.State.ues(S.Tx.apply(S.Rephase{key, p}, st)), PT.Tk.ues(S.Rephase{key, p}, S.State.ues(st)), PT.Tk.ues_apply(S.Rephase{key, p}, st))
      same : {Tb.Table.get(S.Ue, k, S.State.ues(S.Tx.apply(S.Rephase{key, p}, st))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} = (%ua : {Tb.Table.get(S.Ue, k, _) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>}; Hp.get_other(key, p, k, S.State.ues(st), eb))
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.Rephase{key, p}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.Rephase{key, p}, st))))) == True{} : Bool}, ne(same))

def Hp.g_tx(+st: S.State, +k: U32, +tx: S.Tx, +acts: List<&2, N.Act>, +e: {Bool.and(Hp.still(tx), Hp.starts_if(k, tx, acts)) == True{} : Bool}) -> ({Tb.Table.get(S.Ue, k, S.State.ues(S.Tx.apply(tx, st))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} -> Empty) -> {N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st))))) == True{} : Bool}:
  match tx:
    case S.Keep{}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.Keep{}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.Keep{}, st))))) == True{} : Bool}, ne({==}))
    case S.Rephase{+key, +p}:
      Hp.g_rephase(st, k, key, p, acts, U32.is_eq(key, k), {==}, e)
    case S.Put{key, ue}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.Put{key, ue}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.Put{key, ue}, st))))) == True{} : Bool}, P.Refute.bool(e))
    case S.Del{key}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.Del{key}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.Del{key}, st))))) == True{} : Bool}, P.Refute.bool(e))
    case S.PutSession{key, s}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.PutSession{key, s}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.PutSession{key, s}, st))))) == True{} : Bool}, P.Refute.bool(e))
    case S.Revar{key, v}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.Revar{key, v}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.Revar{key, v}, st))))) == True{} : Bool}, P.Refute.bool(e))
    case S.DelSession{key}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.DelSession{key}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.DelSession{key}, st))))) == True{} : Bool}, P.Refute.bool(e))
    case S.Subs{subs}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.Subs{subs}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.Subs{subs}, st))))) == True{} : Bool}, P.Refute.bool(e))
    case S.SetLink{link}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.SetLink{link}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.SetLink{link}, st))))) == True{} : Bool}, P.Refute.bool(e))
    case S.BumpUe{bk}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.BumpUe{bk}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.BumpUe{bk}, st))))) == True{} : Bool}, P.Refute.bool(e))
    case S.BumpSeq{n}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.BumpSeq{n}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.BumpSeq{n}, st))))) == True{} : Bool}, P.Refute.bool(e))
    case S.Both{a, b}:
      ne => Empty.absurd({N.Acts.starts(k, List.append(&2, N.Act, acts, N.Gone.when(S.Tx.keeps_sessions(S.Both{a, b}), S.State.sessions(st), S.State.sessions(S.Tx.apply(S.Both{a, b}, st))))) == True{} : Bool}, P.Refute.bool(e))

def Hp.g_step(+st: S.State, +k: U32, +o: N.GOut(), +e: {Hp.fine(k, o) == True{} : Bool}) -> ({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, o)))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} -> Empty) -> {N.Acts.starts(k, K.Kernel.actions(N.Step.of(st, o))) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      Hp.g_tx(st, k, tx, acts, e)

def Hp.g_required(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +k: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 12, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> ({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} -> Empty) -> {N.Acts.starts(k, K.Kernel.actions(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == True{} : Bool}:
  Hp.pdu(o => ({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(o))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} -> Empty) -> {N.Acts.starts(k, K.Kernel.actions(o)) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 0, 12, crit, value, ep, ne => Empty.absurd({N.Acts.starts(k, N.Ngap.bad_pdu(assoc)) == True{} : Bool}, ne({==})), +ies => Hp.g_step(st, k, Ho.Ho.required_of_view(st, assoc, V.HandoverRequired.view(ies)), Hp.required(st, k, assoc, V.HandoverRequired.view(ies))))

def Hp.g_ack(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +k: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> ({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} -> Empty) -> {N.Acts.starts(k, K.Kernel.actions(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == True{} : Bool}:
  Hp.pdu(o => ({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(o))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} -> Empty) -> {N.Acts.starts(k, K.Kernel.actions(o)) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 1, 13, crit, value, ep, ne => Empty.absurd({N.Acts.starts(k, N.Ngap.bad_pdu(assoc)) == True{} : Bool}, ne({==})), +ies => Hp.g_step(st, k, Ho.Ho.ack_of_view(st, assoc, stream, V.HandoverRequestAcknowledge.view(ies)), Hp.ack(st, k, assoc, stream, V.HandoverRequestAcknowledge.view(ies))))

# The guard of a pending handover ends it.
def Hp.ho_expired_ends(+st: S.State, +k: U32, +u: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +leg: S.Leg, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}) -> {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Ho.Ho.expired(k, u, ctx, nh, leg)))))) == None{} : Maybe<&2, U32>}:
  Hp.rephased_none(st, k, u, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}, List.append(&2, N.Act, Ho.Ho.expiry(k, u, leg), [N.Note{F.Warn{}, "NGAP: N2 handover guard expired; the UE stays with its owner"}]), eg, {==})

def Hp.expired_ends(+st: S.State, +k: U32, +u: S.Ue, +t: U32, +p: S.Phase, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{u} : Maybe<&2, S.Ue>}, +e: {S.Phase.pending(p) == Some{t} : Maybe<&2, U32>}) -> {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, p)))))) == None{} : Maybe<&2, U32>}:
  match p:
    case S.Handover{+ctx, +nh, source, +leg}:
      Hp.ho_expired_ends(st, k, u, ctx, nh, leg, eg)
    case S.Created{}:
      Empty.absurd({S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, S.Created{})))))) == None{} : Maybe<&2, U32>}, P.Refute.none_some(U32, t, e))
    case S.Identifying{guard}:
      Empty.absurd({S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, S.Identifying{guard})))))) == None{} : Maybe<&2, U32>}, P.Refute.none_some(U32, t, e))
    case S.Authenticating{guard, av, resynced, supi}:
      Empty.absurd({S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, S.Authenticating{guard, av, resynced, supi})))))) == None{} : Maybe<&2, U32>}, P.Refute.none_some(U32, t, e))
    case S.SecurityMode{guard, ctx, k_amf}:
      Empty.absurd({S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, S.SecurityMode{guard, ctx, k_amf})))))) == None{} : Maybe<&2, U32>}, P.Refute.none_some(U32, t, e))
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      Empty.absurd({S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, S.ContextSetup{guard, ctx, nh, response, complete})))))) == None{} : Maybe<&2, U32>}, P.Refute.none_some(U32, t, e))
    case S.Registered{ctx, nh, released}:
      Empty.absurd({S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, S.Registered{ctx, nh, released})))))) == None{} : Maybe<&2, U32>}, P.Refute.none_some(U32, t, e))
    case S.Switching{guard, ctx, nh, released}:
      Empty.absurd({S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, S.Switching{guard, ctx, nh, released})))))) == None{} : Maybe<&2, U32>}, P.Refute.none_some(U32, t, e))
    case S.Releasing{guard}:
      Empty.absurd({S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Gmm.Gmm.expired(st, k, u, S.Releasing{guard})))))) == None{} : Maybe<&2, U32>}, P.Refute.none_some(U32, t, e))

def Hp.fired_ends(+st: S.State, +k: U32, +t: U32, +m: Maybe<&2, S.Ue>, +em: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == m : Maybe<&2, S.Ue>}, +e: {S.Ue.pending(m) == Some{t} : Maybe<&2, U32>}) -> {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, k, m)))))) == None{} : Maybe<&2, U32>}:
  match m:
    case None{}:
      Empty.absurd({S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, K.Kernel.fired_ue(st, k, None{})))))) == None{} : Maybe<&2, U32>}, P.Refute.none_some(U32, t, e))
    case Some{+u}:
      Hp.expired_ends(st, k, u, t, S.Ue.phase(u), em, e)

def L.amf.handover.guarded(st, ev, entropy, assoc, stream, len, bytes, crit, value, k, t, p):
  (Hp.timed(S.State.ues(S.State.initial())), (e0 => Hp.timed_step(st, ev, entropy, e0), (e => Hp.g_guard(p, t, e), (ep => Hp.g_required(st, entropy, assoc, stream, len, bytes, crit, value, k, ep), (ep => Hp.g_ack(st, entropy, assoc, stream, len, bytes, crit, value, k, ep), e => Hp.fired_ends(st, k, t, Tb.Table.get(S.Ue, k, S.State.ues(st)), {==}, e))))))

# amf.handover.released_side_completes
# ------------------------------------

def L.amf.handover.released_side_completes(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, ran, uli, rel, diag, ue, ep, ei, ev, eid, eu, ea, er):
  +done : N.Step() = (st, [N.Note{F.Info{}, "NGAP: UE Context Release Complete from the side a handover released"}])
  sep = Equal.sym(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu.read(bytes), Done{Fr.Pdu{1, 41, crit, value}}, ep)
  %sep : {R.Route.of_pdu(st, assoc, stream, entropy, _) == done : N.Step()}
  sei = Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}), Done{(ies, c)}, ei)
  %sei : {R.Route.of_ies(st, assoc, stream, U32.to_nat(1), U32.to_nat(41), entropy, _) == done : N.Step()}
  sev = Equal.sym(Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>, V.UEContextReleaseComplete.view(ies), Done{V.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}}, ev)
  %sev : {N.Step.of(st, Gmm.Gmm.release_complete_of_view(st, assoc, _)) == done : N.Step()}
  sek = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %sek : {N.Step.of(st, Gmm.Gmm.release_complete_key(st, assoc, ran, _)) == done : N.Step()}
  seu = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{ue}, eu)
  %seu : {N.Step.of(st, Gmm.Gmm.release_complete_ue(st, assoc, k, N.Owner.of(_, assoc, ran), S.Ue.released(_, assoc, ran))) == done : N.Step()}
  sea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, ea)
  %sea : {N.Step.of(st, Gmm.Gmm.release_complete_ue(st, assoc, k, N.Owner.check(ue, Bool.and(_, B.bytes_eq(S.Ue.ran_id(ue), ran))), S.Phase.released(S.Ue.phase(ue), assoc, ran))) == done : N.Step()}
  ser = Equal.sym(Bool, S.Phase.released(S.Ue.phase(ue), assoc, ran), True{}, er)
  %ser : {N.Step.of(st, Gmm.Gmm.release_complete_ue(st, assoc, k, None{}, _)) == done : N.Step()}
  {==}
