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
import ../smf/gsm.bend as Gsm
import ../smf/n4.bend as Up
import ../pfcp.bend as Pf
import ../tlv.bend as T
import ../ausf.bend as Au
import ../crypto/kdf.bend as Kd
import ../LAWS.bend as L
import ./lib.bend as P
import ./walk.bend as PW
import ./takeover.bend as PT
import ./path_switch.bend as PPs
import ./liveness.bend as PL
import ./kernel.bend as PK
import ./smf.bend as PSm
import ./fresh.bend as PF

# Proofs of the N2 handover laws (ticket 28).

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
  Hp.still(N.Out.tx(o))

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
  sr = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, o))), PT.Tk.ues(N.Out.tx(o), S.State.ues(st)), PT.Tk.render(st, o))
  %sr : {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, _)) == True{} : Bool}
  Hp.same_still(N.Out.tx(o), S.State.ues(st), j, e)

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

def Hp.required(+st: S.State, +k: U32, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverRequired.View>) -> {Hp.fine(k, Ho.Ho.required_of_view(st, assoc, r)) == True{} : Bool}:
  PW.Hw.required(o => {Hp.fine(k, o) == True{} : Bool}, st, assoc, r, {==}, {==}, amf => ran => key => ue => c => ek => eo => {==}, amf => ran => +key => ue => ctx => nh => t => cfg => cause => container => i => more => ek => eo => ne => rel => eph => Hp.second(U32.is_eq(key, k)))

def Hp.ack(+st: S.State, +k: U32, +assoc: U32, +stream: U32, +r: Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View>) -> {Hp.fine(k, Ho.Ho.ack_of_view(st, assoc, stream, r)) == True{} : Bool}:
  PW.Hw.ack(o => {Hp.fine(k, o) == True{} : Bool}, st, assoc, stream, r, {==}, {==}, amf => ran => admitted => container => +key => ue => ctx => nh => source => t => ek => ep => eph => Hp.second(U32.is_eq(key, k)))

def Hp.failure(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverFailure.View>) -> {Hp.calm(Ho.Ho.failure_of_view(st, assoc, r)) == True{} : Bool}:
  PW.Hw.failure(o => {Hp.calm(o) == True{} : Bool}, st, assoc, r, {==}, {==}, amf => cause => key => ue => ctx => nh => source => t => ek => ep => eph => {==})

def Hp.cancel(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.HandoverCancel.View>) -> {Hp.calm(Ho.Ho.cancel_of_view(st, assoc, r)) == True{} : Bool}:
  PW.Hw.cancel(o => {Hp.calm(o) == True{} : Bool}, st, assoc, r, {==}, {==}, amf => ran => key => ue => ek => eo => en => {==}, amf => ran => key => ue => ctx => nh => source => leg => ek => eo => eph => {==})

def Hp.status(+st: S.State, +assoc: U32, +r: Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View>) -> {Hp.calm(Ho.Ho.status_of_view(st, assoc, r)) == True{} : Bool}:
  PW.Hw.status(o => {Hp.calm(o) == True{} : Bool}, st, assoc, r, {==}, {==}, {==}, amf => ran => container => key => ue => t => r2 => s => ek => eo => {==})

# Small facts
# -----------

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

# The key a message names is k.
def Hp.same_key(+amf: B.Bytes(), +k: U32, +key: U32, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}) -> {key == k : U32}:
  P.Some.inj(U32, key, k, Equal.trans(Maybe<&2, U32>, Some{key}, N.Ngap.ue_key(amf), Some{k}, Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{key}, ek), eid))

# The association does not own the context under k: no message of its finds it.
def Hp.no_owner(+st: S.State, +assoc: U32, +ran: B.Bytes(), +amf: B.Bytes(), +k: U32, +key: U32, +ue: S.Ue, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == None{} : Maybe<&2, S.Ue>}, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eo2: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> Empty:
  kk = Hp.same_key(amf, k, key, eid, ek)
  e2 : {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>} = (%kk : {N.Owner.of(Tb.Table.get(S.Ue, _, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}; eo2)
  P.Refute.none_some(S.Ue, ue, Equal.trans(Maybe<&2, S.Ue>, None{}, N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran), Some{ue}, Equal.sym(Maybe<&2, S.Ue>, N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran), None{}, eo), e2))

# No handover is pending to the association for the context under k: no answer of its finds it.
def Hp.no_target(+st: S.State, +assoc: U32, +amf: B.Bytes(), +k: U32, +key: U32, +ue: S.Ue, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +en: {Ho.Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc) == None{} : Maybe<&2, S.Ue>}, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}) -> Empty:
  kk = Hp.same_key(amf, k, key, eid, ek)
  e2 : {Ho.Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>} = (%kk : {Ho.Ho.pending(Tb.Table.get(S.Ue, _, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}; ep)
  P.Refute.none_some(S.Ue, ue, Equal.trans(Maybe<&2, S.Ue>, None{}, Ho.Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc), Some{ue}, Equal.sym(Maybe<&2, S.Ue>, Ho.Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc), None{}, en), e2))

def Hp.Kept(+st: S.State, +o: N.GOut()) -> Type:
  {K.Kernel.state(N.Step.of(st, o)) == st : S.State}

def Hp.oo_required(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +kind: G.HandoverType(), +cause: G.Cause, +id: G.TargetID, +direct: Maybe<&2, G.DirectForwardingPathAvailability()>, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 12, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverRequired.view(ies) == Done{V.HandoverRequired.View{amf, ran, kind, cause, id, direct, items, container}} : Result<&2, &2, B.Err, V.HandoverRequired.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  PW.Rt.view(V.HandoverRequired.View, x => {K.Kernel.state(x) == st : S.State}, st, entropy, assoc, stream, len, bytes, 0, 12, crit, value, ies, c, i => V.HandoverRequired.view(i), r => Ho.Ho.required_of_view(st, assoc, r), Done{V.HandoverRequired.View{amf, ran, kind, cause, id, direct, items, container}}, ep, ei, {==}, eup, {==}, ev, PW.Hw.required_found(o => Hp.Kept(st, o), st, assoc, amf, ran, kind, cause, id, items, container, {==}, key => ue => cx => ek => eo2 => {==}, +key => +ue => ctx => nh => t => cfg => cause2 => container2 => i => more => +ek => +eo2 => ne => rel => eph => Empty.absurd(Hp.Kept(st, Ho.Ho.prepare(key, ue, ctx, nh, t, cfg, cause2, container2, i <> more)), Hp.no_owner(st, assoc, ran, amf, k, key, ue, eid, eo, ek, eo2))))

def Hp.oo_cancel(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +cause: G.Cause, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 10, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverCancel.view(ies) == Done{V.HandoverCancel.View{amf, ran, cause}} : Result<&2, &2, B.Err, V.HandoverCancel.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  PW.Rt.view(V.HandoverCancel.View, x => {K.Kernel.state(x) == st : S.State}, st, entropy, assoc, stream, len, bytes, 0, 10, crit, value, ies, c, i => V.HandoverCancel.view(i), r => Ho.Ho.cancel_of_view(st, assoc, r), Done{V.HandoverCancel.View{amf, ran, cause}}, ep, ei, {==}, eup, {==}, ev, PW.Hw.cancel_found(o => Hp.Kept(st, o), st, assoc, amf, ran, {==}, key => ue => ek => eo2 => en => {==}, +key => +ue => +ctx => +nh => +source => +leg => +ek => +eo2 => eph => Empty.absurd(Hp.Kept(st, Ho.Ho.cancel_phase(key, ue, S.Handover{ctx, nh, source, leg})), Hp.no_owner(st, assoc, ran, amf, k, key, ue, eid, eo, ek, eo2))))

def Hp.oo_status(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +status: G.RANStatusTransfer_TransparentContainer, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 49, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.UplinkRANStatusTransfer.view(ies) == Done{V.UplinkRANStatusTransfer.View{amf, ran, status}} : Result<&2, &2, B.Err, V.UplinkRANStatusTransfer.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  PW.Rt.view(V.UplinkRANStatusTransfer.View, x => {K.Kernel.state(x) == st : S.State}, st, entropy, assoc, stream, len, bytes, 0, 49, crit, value, ies, c, i => V.UplinkRANStatusTransfer.view(i), r => Ho.Ho.status_of_view(st, assoc, r), Done{V.UplinkRANStatusTransfer.View{amf, ran, status}}, ep, ei, {==}, eup, {==}, ev, PW.Hw.status_found(o => Hp.Kept(st, o), st, assoc, amf, ran, status, {==}, {==}, key => ue => t => r => s => ek => eo2 => {==}))

def Hp.Unk(+st: S.State, +assoc: U32, +o: N.GOut()) -> Type:
  {N.Step.of(st, o) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}

# The target's answers name a context; with no handover pending to the
# association they come from, the context is not found.
def Hp.oo_ack(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +admitted: G.PDUSessionResourceAdmittedList(), +failed: Maybe<&2, G.PDUSessionResourceFailedToSetupListHOAck()>, +back: B.Bytes(), +diag: Maybe<&2, G.CriticalityDiagnostics>, +npn: Maybe<&2, G.NPN_AccessInformation>, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {Ho.Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverRequestAcknowledge.view(ies) == Done{V.HandoverRequestAcknowledge.View{amf, ran, admitted, failed, back, diag, npn}} : Result<&2, &2, B.Err, V.HandoverRequestAcknowledge.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  PW.Rt.view(V.HandoverRequestAcknowledge.View, x => {x == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}, st, entropy, assoc, stream, len, bytes, 1, 13, crit, value, ies, c, i => V.HandoverRequestAcknowledge.view(i), r => Ho.Ho.ack_of_view(st, assoc, stream, r), Done{V.HandoverRequestAcknowledge.View{amf, ran, admitted, failed, back, diag, npn}}, ep, ei, {==}, eup, {==}, ev, PW.Hw.ack_found(o => Hp.Unk(st, assoc, o), st, assoc, stream, amf, ran, admitted, back, {==}, +key => +ue => ctx => nh => source => t => +ek => +ep2 => eph => Empty.absurd(Hp.Unk(st, assoc, Ho.Ho.ack_phase(assoc, stream, key, ue, ran, admitted, back, S.Handover{ctx, nh, source, S.Asked{t}})), Hp.no_target(st, assoc, amf, k, key, ue, eid, en, ek, ep2))))

def Hp.oo_failure(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +k: U32, +cause: G.Cause, +diag: Maybe<&2, G.CriticalityDiagnostics>, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {Ho.Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{2, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverFailure.view(ies) == Done{V.HandoverFailure.View{amf, cause, diag}} : Result<&2, &2, B.Err, V.HandoverFailure.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  PW.Rt.view(V.HandoverFailure.View, x => {x == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}, st, entropy, assoc, stream, len, bytes, 2, 13, crit, value, ies, c, i => V.HandoverFailure.view(i), r => Ho.Ho.failure_of_view(st, assoc, r), Done{V.HandoverFailure.View{amf, cause, diag}}, ep, ei, {==}, eup, {==}, ev, PW.Hw.failure_found(o => Hp.Unk(st, assoc, o), st, assoc, amf, cause, {==}, +key => +ue => ctx => nh => source => t => +ek => +ep2 => eph => Empty.absurd(Hp.Unk(st, assoc, Ho.Ho.failure_phase(assoc, key, ue, cause, S.Handover{ctx, nh, source, S.Asked{t}})), Hp.no_target(st, assoc, amf, k, key, ue, eid, en, ek, ep2))))

def Hp.oo_notify(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +uli: G.UserLocationInformation, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +en: {Ho.Ho.pending(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc) == None{} : Maybe<&2, S.Ue>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 11, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverNotify.view(ies) == Done{V.HandoverNotify.View{amf, ran, uli}} : Result<&2, &2, B.Err, V.HandoverNotify.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}:
  PW.Rt.view(V.HandoverNotify.View, x => {x == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}, st, entropy, assoc, stream, len, bytes, 0, 11, crit, value, ies, c, i => V.HandoverNotify.view(i), r => Ho.Ho.notify_of_view(st, assoc, r), Done{V.HandoverNotify.View{amf, ran, uli}}, ep, ei, {==}, eup, {==}, ev, PW.Hw.notify_found(o => Hp.Unk(st, assoc, o), st, assoc, amf, ran, {==}, +key => +ue => ctx => nh => source => t => r => s => ts => sp => +ek => +ep2 => eph => es => Empty.absurd(Hp.Unk(st, assoc, Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, True{})), Hp.no_target(st, assoc, amf, k, key, ue, eid, en, ek, ep2))))

def Hp.oo_state(+st: S.State, +assoc: U32, +o: N.Step(), +e: {o == (st, N.Ngap.unknown_ue(assoc)) : N.Step()}) -> {K.Kernel.state(o) == st : S.State}:
  se = Equal.sym(N.Step(), o, (st, N.Ngap.unknown_ue(assoc)), e)
  %se : {K.Kernel.state(_) == st : S.State}
  {==}

def L.amf.handover.owner_only(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, kind, cause, id, direct, items, container, status, admitted, failed, back, diag, npn, uli, eid, ei):
  +m = Tb.Table.get(S.Ue, k, S.State.ues(st))
  (+eo => (+ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 0, 12, crit, value, ies, c, ep, ei, {==}, +eup => Hp.oo_required(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, kind, cause, id, direct, items, container, eid, ei, eo, ep, ev, eup)), (+ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 0, 10, crit, value, ies, c, ep, ei, {==}, +eup => Hp.oo_cancel(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, cause, eid, ei, eo, ep, ev, eup)), +ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 0, 49, crit, value, ies, c, ep, ei, {==}, +eup => Hp.oo_status(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, status, eid, ei, eo, ep, ev, eup)))), +en => (+ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 1, 13, crit, value, ies, c, ep, ei, {==}, +eup => Hp.oo_state(st, assoc, K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), Hp.oo_ack(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, admitted, failed, back, diag, npn, eid, ei, Hp.not_aimed(m, assoc, en), ep, ev, eup))), (+ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 2, 13, crit, value, ies, c, ep, ei, {==}, +eup => Hp.oo_state(st, assoc, K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), Hp.oo_failure(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, cause, diag, eid, ei, Hp.not_aimed(m, assoc, en), ep, ev, eup))), +ep => +ev => PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 0, 11, crit, value, ies, c, ep, ei, {==}, +eup => Hp.oo_state(st, assoc, K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), Hp.oo_notify(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, uli, eid, ei, Hp.not_aimed(m, assoc, en), ep, ev, eup))))))

# amf.handover.responses_correlated
# ---------------------------------

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
  sp = Equal.sym(S.Phase, S.Ue.phase(S.Ue.with_phase(u, q)), q, PL.Lv.p_phase(u, q))
  %sp : {S.Phase.pending(_) == None{} : Maybe<&2, U32>}
  en

def Hp.Settled(+st: S.State, +k: U32, +o: N.GOut()) -> Type:
  {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, o))))) == None{} : Maybe<&2, U32>}

# The owner's context under k, found by the key it names.
def Hp.owned_get(+st: S.State, +assoc: U32, +ran: B.Bytes(), +amf: B.Bytes(), +k: U32, +key: U32, +ue: S.Ue, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}:
  kk = Hp.same_key(amf, k, key, eid, ek)
  eg = PL.Lv.owned_get(st, assoc, key, ran, ue, eo)
  (%kk : {Tb.Table.get(S.Ue, _, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}; eg)

def Hp.cancel_go(+st: S.State, +assoc: U32, +ran: B.Bytes(), +amf: B.Bytes(), +k: U32, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +source: U32, +leg: S.Leg, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran) == Some{ue} : Maybe<&2, S.Ue>}) -> Hp.Settled(st, k, Ho.Ho.cancel_phase(key, ue, S.Handover{ctx, nh, source, leg})):
  kk = Equal.sym(U32, key, k, Hp.same_key(amf, k, key, eid, ek))
  +x : N.Act = N.UeSend{S.Ue.assoc(ue), S.Ue.stream(ue), k, Ho.Ho.cancel_ack(k, S.Ue.ran_id(ue))}
  (%kk : Hp.Settled(st, k, Ho.Ho.cancel_phase(_, ue, S.Handover{ctx, nh, source, leg})); Hp.rephased_none(st, k, ue, S.Registered{ctx, nh, Some{S.Leg.side(leg)}}, x <> List.append(&2, N.Act, Ho.Ho.drop(k, leg, Ho.Ho.radio(G.CauseRadioNetwork.handover_cancelled())), [N.TimerCancel{k}, N.Note{F.Info{}, "NGAP: Handover Cancel; the target released"}]), Hp.owned_get(st, assoc, ran, amf, k, key, ue, eid, ek, eo), {==}))

def Hp.rc_cancel(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +u: S.Ue, +cause: G.Cause, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 10, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverCancel.view(ies) == Done{V.HandoverCancel.View{amf, ran, cause}} : Result<&2, &2, B.Err, V.HandoverCancel.View>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == Some{u} : Maybe<&2, S.Ue>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == None{} : Maybe<&2, U32>}:
  sf = Equal.sym(N.GOut(), N.Ue.found(N.Ue.keyed(N.Ngap.ue_key(amf), (k2 => N.Owner.of(Tb.Table.get(S.Ue, k2, S.State.ues(st)), assoc, ran))), (S.Keep{}, N.Ngap.unknown_ue(assoc)), (+key => +ue => Ho.Ho.cancel_phase(key, ue, S.Ue.phase(ue)))), Ho.Ho.cancel_phase(k, u, S.Ue.phase(u)), PW.Walk.keyed_eq(N.Ngap.ue_key(amf), (k2 => N.Owner.of(Tb.Table.get(S.Ue, k2, S.State.ues(st)), assoc, ran)), k, u, (S.Keep{}, N.Ngap.unknown_ue(assoc)), (+key => +ue => Ho.Ho.cancel_phase(key, ue, S.Ue.phase(ue))), eid, eo))
  PW.Rt.view(V.HandoverCancel.View, x => {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(x)))) == None{} : Maybe<&2, U32>}, st, entropy, assoc, stream, len, bytes, 0, 10, crit, value, ies, c, i => V.HandoverCancel.view(i), r => Ho.Ho.cancel_of_view(st, assoc, r), Done{V.HandoverCancel.View{amf, ran, cause}}, ep, ei, {==}, eup, {==}, ev, (%sf : Hp.Settled(st, k, _); PW.Hw.cancel_phase(o => Hp.Settled(st, k, o), st, assoc, amf, ran, k, u, S.Ue.phase(u), eid, eo, {==}, +key => +ue => +ek => +eo2 => +en => Hp.kept_none(st, k, ue, S.Ue.phase(ue), Hp.owned_get(st, assoc, ran, amf, k, key, ue, eid, ek, eo2), {==}, en), +key => +ue => +ctx => +nh => +source => +leg => +ek => +eo2 => eph => Hp.cancel_go(st, assoc, ran, amf, k, key, ue, ctx, nh, source, leg, eid, ek, eo2))))

# A Handover Required to a target released before it answered is refused.
def Hp.rc_crossing(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +k: U32, +u: S.Ue, +kind: G.HandoverType(), +hcause: G.Cause, +id: G.TargetID, +direct: Maybe<&2, G.DirectForwardingPathAvailability()>, +items: G.PDUSessionResourceListHORqd(), +container: B.Bytes(), +ctx: Sec.Nas.Ctx, +nh: S.Nh, +t: U32, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +er: {S.Ue.phase(u) == S.Registered{ctx, nh, Some{S.Side{t, None{}}}} : S.Phase}, +et: {Ho.Ho.target(st, Ho.Ho.intra_type(kind), Ho.Ho.node(id)) == Some{t} : Maybe<&2, U32>}, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 12, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ev: {V.HandoverRequired.view(ies) == Done{V.HandoverRequired.View{amf, ran, kind, hcause, id, direct, items, container}} : Result<&2, &2, B.Err, V.HandoverRequired.View>}, +eo: {N.Owner.of(Tb.Table.get(S.Ue, k, S.State.ues(st)), assoc, ran) == Some{u} : Maybe<&2, S.Ue>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == (st, [Ho.Ho.preparation_failure(k, u, Ho.Ho.radio(G.CauseRadioNetwork.ho_target_not_allowed())), N.Note{F.Warn{}, "NGAP: Handover Required refused"}]) : N.Step()}:
  sf = Equal.sym(N.GOut(), N.Ue.found(N.Ue.keyed(N.Ngap.ue_key(amf), (k2 => N.Owner.of(Tb.Table.get(S.Ue, k2, S.State.ues(st)), assoc, ran))), (S.Keep{}, N.Ngap.unknown_ue(assoc)), (+key => +ue => Ho.Ho.required_phase(st, key, ue, kind, hcause, id, items, container, S.Ue.phase(ue)))), Ho.Ho.required_phase(st, k, u, kind, hcause, id, items, container, S.Ue.phase(u)), PW.Walk.keyed_eq(N.Ngap.ue_key(amf), (k2 => N.Owner.of(Tb.Table.get(S.Ue, k2, S.State.ues(st)), assoc, ran)), k, u, (S.Keep{}, N.Ngap.unknown_ue(assoc)), (+key => +ue => Ho.Ho.required_phase(st, key, ue, kind, hcause, id, items, container, S.Ue.phase(ue))), eid, eo))
  ser = Equal.sym(S.Phase, S.Ue.phase(u), S.Registered{ctx, nh, Some{S.Side{t, None{}}}}, er)
  set = Equal.sym(Maybe<&2, U32>, Ho.Ho.target(st, Ho.Ho.intra_type(kind), Ho.Ho.node(id)), Some{t}, et)
  ert = Equal.sym(Bool, U32.is_eq(t, t), True{}, P.U32.is_eq_refl(t))
  PW.Rt.view(V.HandoverRequired.View, x => {x == (st, [Ho.Ho.preparation_failure(k, u, Ho.Ho.radio(G.CauseRadioNetwork.ho_target_not_allowed())), N.Note{F.Warn{}, "NGAP: Handover Required refused"}]) : N.Step()}, st, entropy, assoc, stream, len, bytes, 0, 12, crit, value, ies, c, i => V.HandoverRequired.view(i), r => Ho.Ho.required_of_view(st, assoc, r), Done{V.HandoverRequired.View{amf, ran, kind, hcause, id, direct, items, container}}, ep, ei, {==}, eup, {==}, ev, (%sf : {N.Step.of(st, _) == (st, [Ho.Ho.preparation_failure(k, u, Ho.Ho.radio(G.CauseRadioNetwork.ho_target_not_allowed())), N.Note{F.Warn{}, "NGAP: Handover Required refused"}]) : N.Step()}; (%ser : {N.Step.of(st, Ho.Ho.required_phase(st, k, u, kind, hcause, id, items, container, _)) == (st, [Ho.Ho.preparation_failure(k, u, Ho.Ho.radio(G.CauseRadioNetwork.ho_target_not_allowed())), N.Note{F.Warn{}, "NGAP: Handover Required refused"}]) : N.Step()}; (%set : {N.Step.of(st, Ho.Ho.required_target(st, k, u, ctx, nh, Some{S.Side{t, None{}}}, hcause, items, container, _)) == (st, [Ho.Ho.preparation_failure(k, u, Ho.Ho.radio(G.CauseRadioNetwork.ho_target_not_allowed())), N.Note{F.Warn{}, "NGAP: Handover Required refused"}]) : N.Step()}; (%ert : {N.Step.of(st, Ho.Ho.required_other(st, k, u, ctx, nh, t, hcause, items, container, Bool.or(_, U32.is_eq(t, S.Ue.assoc(u))))) == (st, [Ho.Ho.preparation_failure(k, u, Ho.Ho.radio(G.CauseRadioNetwork.ho_target_not_allowed())), N.Note{F.Warn{}, "NGAP: Handover Required refused"}]) : N.Step()}; {==})))))

def L.amf.handover.responses_correlated(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, u, cause, admitted, failed, back, diag, npn, uli, kind, hcause, id, direct, items, container, ctx, nh, t, eid, ei, eup):
  +m = Tb.Table.get(S.Ue, k, S.State.ues(st))
  (+en => (ep => ev => Hp.oo_ack(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, admitted, failed, back, diag, npn, eid, ei, Hp.none_aimed(m, assoc, en), ep, ev, eup), (ep => ev => Hp.oo_failure(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, cause, diag, eid, ei, Hp.none_aimed(m, assoc, en), ep, ev, eup), ep => ev => Hp.oo_notify(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, uli, eid, ei, Hp.none_aimed(m, assoc, en), ep, ev, eup))), (ep => ev => eo => Hp.rc_cancel(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, u, cause, eid, ei, ep, ev, eo, eup), er => et => ep => ev => eo => Hp.rc_crossing(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, k, u, kind, hcause, id, direct, items, container, ctx, nh, t, eid, ei, er, et, ep, ev, eo, eup)))

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

def So.sift(+s: S.Sieve, +ues: Tb.Table(S.Ue), +e: {S.Ues.single(ues) == True{} : Bool}) -> {S.Ues.single(S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      P.Keep.by(S.Ue, tb => {S.Ues.single(tb) == True{} : Bool}, k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), e1 => h => P.Bool.and_intro(S.Ue.single(v), S.Ues.single(S.Ues.sift(s, more)), P.Bool.and_true_l(S.Ue.single(v), S.Ues.single(more), e), h), So.sift(s, more, P.Bool.and_true_r(S.Ue.single(v), S.Ues.single(more), e)))

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

def So.tx_put(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ue: S.Ue, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.Put{key, ue}, ues) == True{} : Bool}) -> {So.inv(st0, S.Ues.put(key, ue, ues), S.Sessions.sift(S.SOwned{S.Ues.put(key, ue, ues)}, ss)) == True{} : Bool}:
  +hs = P.Bool.and_true_l(S.Ue.single(ue), PL.Lv.home(st0, ue), P.Bool.and_true_r(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), PL.Lv.home(st0, ue)), P.Bool.and_true_r(PL.Lv.keyed(st0, key), Bool.and(S.Phase.guarded(S.Ue.phase(ue)), Bool.and(S.Ue.single(ue), PL.Lv.home(st0, ue))), h)))
  P.Bool.and_intro(S.Ues.unique(S.Ues.put(key, ue, ues)), S.Ues.single(S.Ues.put(key, ue, ues)), PL.Un.tx_put(st0, ep, key, ue, ues, ss, So.parts(ues, e), h), P.Bool.and_intro(S.Ue.single(ue), S.Ues.single(S.Ues.sift(S.Clear{key, ue}, ues)), hs, So.sift(S.Clear{key, ue}, ues, So.part2(ues, e))))

def So.tx_rephase(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.Rephase{key, p}, ues) == True{} : Bool}) -> {So.inv(st0, S.Ues.rephase(key, p, ues), ss) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.unique(S.Ues.rephase(key, p, ues)), S.Ues.single(S.Ues.rephase(key, p, ues)), PL.Un.tx_rephase(st0, ep, key, p, ues, ss, So.parts(ues, e), h), So.rephase(key, p, ues, So.parts(ues, e), So.part2(ues, e), P.Bool.and_true_r(S.Phase.guarded(p), S.Ue.fits(p, Tb.Table.get(S.Ue, key, ues)), h)))

def So.tx_del(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}) -> {So.inv(st0, S.Ues.del(key, ues), S.Sessions.drop_ue(key, ss)) == True{} : Bool}:
  P.Bool.and_intro(S.Ues.unique(S.Ues.del(key, ues)), S.Ues.single(S.Ues.del(key, ues)), PL.Un.tx_del(st0, ep, key, ues, ss, So.parts(ues, e)), So.sift(S.Except{key}, ues, So.part2(ues, e)))

def So.tx_put_session(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +s: S.Session, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.homedw(st0, S.PutSession{key, s}, ues) == True{} : Bool}) -> {So.inv(st0, ues, S.Sessions.put(key, s, ss)) == True{} : Bool}:
  e

def So.tx_revar(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +v: S.SVar, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}, +h: {PL.Lv.revar_ok(st0, v) == True{} : Bool}) -> {So.inv(st0, ues, S.Sessions.revar(key, v, ss)) == True{} : Bool}:
  e

def So.tx_del_session(+st0: S.State, +ep: {PL.Inv.none(st0) == True{} : Bool}, +key: U32, +ues: Tb.Table(S.Ue), +ss: Tb.Table(S.Session), +e: {So.inv(st0, ues, ss) == True{} : Bool}) -> {So.inv(st0, ues, S.Sessions.del(key, ss)) == True{} : Bool}:
  e

def So.down(+st: S.State, +assoc: U32, +e: {Bool.and(S.Ues.unique(S.State.ues(st)), S.Ues.single(S.State.ues(st))) == True{} : Bool}) -> {Bool.and(S.Ues.unique(S.State.ues(K.Kernel.state(R.Route.drop(st, assoc)))), S.Ues.single(S.State.ues(K.Kernel.state(R.Route.drop(st, assoc))))) == True{} : Bool}:
  match st:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, n4}:
      P.Bool.and_intro(S.Ues.unique(S.Ues.sift(S.Others{assoc}, ues)), S.Ues.single(S.Ues.sift(S.Others{assoc}, ues)), PK.Unique.sift(S.Others{assoc}, ues, So.parts(ues, e)), So.sift(S.Others{assoc}, ues, So.part2(ues, e)))

def So.step(+st: S.State, +ev: F.Evt, +entropy: B.Bytes(), +e: {Bool.and(S.Ues.unique(S.State.ues(st)), S.Ues.single(S.State.ues(st))) == True{} : Bool}) -> {Bool.and(S.Ues.unique(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy)))), S.Ues.single(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))))) == True{} : Bool}:
  PL.Inv.step(~So.inv, ~PL.Inv.none, ~So.tx_put, ~So.tx_rephase, ~So.tx_del, ~So.tx_put_session, ~So.tx_revar, ~So.tx_del_session, ~(st0 => a => s => e1 => So.down(s, a, e1)), st, ev, entropy, {==}, e)

# amf.handover.single_owner
# -------------------------

def Hp.so_required(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +j: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 12, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool}:
  PW.Rt.read(o => {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(o)))) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 0, 12, crit, value, ep, {==}, Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), +ies => Hp.same_step(st, Ho.Ho.required_of_view(st, assoc, V.HandoverRequired.view(ies)), j, Hp.calm_of_fine(j, Ho.Ho.required_of_view(st, assoc, V.HandoverRequired.view(ies)), Hp.required(st, j, assoc, V.HandoverRequired.view(ies)))))

def Hp.so_ack(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +j: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool}:
  PW.Rt.read(o => {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(o)))) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 1, 13, crit, value, ep, {==}, Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), +ies => Hp.same_step(st, Ho.Ho.ack_of_view(st, assoc, stream, V.HandoverRequestAcknowledge.view(ies)), j, Hp.calm_of_fine(j, Ho.Ho.ack_of_view(st, assoc, stream, V.HandoverRequestAcknowledge.view(ies)), Hp.ack(st, j, assoc, stream, V.HandoverRequestAcknowledge.view(ies)))))

def Hp.so_failure(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +j: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{2, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool}:
  PW.Rt.read(o => {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(o)))) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 2, 13, crit, value, ep, {==}, Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), +ies => Hp.same_step(st, Ho.Ho.failure_of_view(st, assoc, V.HandoverFailure.view(ies)), j, Hp.failure(st, assoc, V.HandoverFailure.view(ies))))

def Hp.so_cancel(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +j: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 10, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool}:
  PW.Rt.read(o => {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(o)))) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 0, 10, crit, value, ep, {==}, Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), +ies => Hp.same_step(st, Ho.Ho.cancel_of_view(st, assoc, V.HandoverCancel.view(ies)), j, Hp.cancel(st, assoc, V.HandoverCancel.view(ies))))

def Hp.so_status(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +j: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 49, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))) == True{} : Bool}:
  PW.Rt.read(o => {S.Ue.same_owner(Tb.Table.get(S.Ue, j, S.State.ues(st)), Tb.Table.get(S.Ue, j, S.State.ues(K.Kernel.state(o)))) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 0, 49, crit, value, ep, {==}, Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), Hp.same_refl(Tb.Table.get(S.Ue, j, S.State.ues(st))), +ies => Hp.same_step(st, Ho.Ho.status_of_view(st, assoc, V.UplinkRANStatusTransfer.view(ies)), j, Hp.status(st, assoc, V.UplinkRANStatusTransfer.view(ies))))

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

def Hp.complete_moved(+st: S.State, +assoc: U32, +k: U32, +t: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +eat: {U32.is_eq(assoc, t) == True{} : Bool}) -> Hp.Moved(st, k, t, Ho.Ho.complete(st, assoc, k, ue, ctx, nh, r, s, ts, True{})):
  +ues = S.State.ues(st)
  +g = Tb.Table.get(S.Ue, k, ues)
  +rows = S.Sessions.of_ue(k, S.State.sessions(st))
  +told = Gsm.Gsm.releases(k, assoc, s, r, Sw.Sw.released(ts, rows), ctx)
  +ph : S.Phase = S.Registered{Gsm.Gsm.Told.ctx(told), nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}}
  +v = S.Ue.moved(ue, assoc, r, s, ph)
  +a = Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st))
  +b : N.GOut() = (S.Put{k, v}, [])
  +more : List<&2, N.Act> = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), k, S.Ue.ran_id(ue), Ho.Ho.radio(G.CauseRadioNetwork.successful_handover())} <> List.append(&2, N.Act, Gsm.Gsm.Told.acts(told), [N.TimerCancel{k}, N.Note{F.Info{}, "NGAP: Handover Notify; the UE moved to the target"}])
  +o = N.Out.also(N.Out.join(a, b), more)
  e12 = Equal.trans(S.Tx, N.Out.tx(o), N.Out.tx(N.Out.join(a, b)), S.Both{N.Out.tx(a), S.Put{k, v}}, PL.Lv.tx_also(N.Out.join(a, b), more), PW.Out.tx_join(a, b))
  sr = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, o))), PT.Tk.ues(N.Out.tx(o), ues), PT.Tk.render(st, o))
  %sr : {Bool.or(S.Ue.same_owner(g, Tb.Table.get(S.Ue, k, _)), S.Ue.on(Tb.Table.get(S.Ue, k, _), t)) == True{} : Bool}
  se = Equal.sym(S.Tx, N.Out.tx(o), S.Both{N.Out.tx(a), S.Put{k, v}}, e12)
  %se : {Bool.or(S.Ue.same_owner(g, Tb.Table.get(S.Ue, k, PT.Tk.ues(_, ues))), S.Ue.on(Tb.Table.get(S.Ue, k, PT.Tk.ues(_, ues)), t)) == True{} : Bool}
  sg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.Ues.put(k, v, PT.Tk.ues(N.Out.tx(a), ues))), Some{v}, PPs.Mv.get_put(k, v, PT.Tk.ues(N.Out.tx(a), ues)))
  %sg : {Bool.or(S.Ue.same_owner(g, _), S.Ue.on(_, t)) == True{} : Bool}
  sa = Equal.sym(U32, S.Ue.assoc(v), assoc, Hp.assoc_moved(ue, assoc, r, s, ph))
  %sa : {Bool.or(S.Ue.same_owner(g, Some{v}), U32.is_eq(_, t)) == True{} : Bool}
  P.Bool.or_r(S.Ue.same_owner(g, Some{v}), U32.is_eq(assoc, t), eat)

# The target of the handover pending for the context under k is the
# association its answer comes from.
def Hp.eat(+st: S.State, +assoc: U32, +amf: B.Bytes(), +k: U32, +t: U32, +key: U32, +ue: S.Ue, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +epend: {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(st))) == Some{t} : Maybe<&2, U32>}, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}) -> {U32.is_eq(assoc, t) == True{} : Bool}:
  kk = Hp.same_key(amf, k, key, eid, ek)
  eg = PW.Walk.first({Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, {Ho.Ho.aimed(ue, assoc) == True{} : Bool}, PW.Walk.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ue, ep))
  ea = PW.Walk.second({Tb.Table.get(S.Ue, key, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, {Ho.Ho.aimed(ue, assoc) == True{} : Bool}, PW.Walk.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ue, ep))
  egk : {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>} = (%kk : {Tb.Table.get(S.Ue, _, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}; eg)
  ep2 : {S.Ue.pending(Some{ue}) == Some{t} : Maybe<&2, U32>} = (%egk : {S.Ue.pending(_) == Some{t} : Maybe<&2, U32>}; epend)
  h1 = P.Bool.and_true_l(S.Maybe.same_u32(S.Phase.pending(S.Ue.phase(ue)), Some{assoc}), Bool.and(Tb.Table.present(B.Digits(), S.Ue.supi(ue)), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc))), ea)
  eta : {U32.is_eq(t, assoc) == True{} : Bool} = (%ep2 : {S.Maybe.same_u32(_, Some{assoc}) == True{} : Bool}; h1)
  Equal.trans(Bool, U32.is_eq(assoc, t), U32.is_eq(t, assoc), True{}, P.U32.sym(assoc, t), eta)

def Hp.notify_go(+st: S.State, +assoc: U32, +amf: B.Bytes(), +k: U32, +t: U32, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +epend: {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(st))) == Some{t} : Maybe<&2, U32>}, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}, +ep: {Ho.Ho.pending(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc) == Some{ue} : Maybe<&2, S.Ue>}) -> Hp.Moved(st, k, t, Ho.Ho.complete(st, assoc, key, ue, ctx, nh, r, s, ts, True{})):
  kk = Equal.sym(U32, key, k, Hp.same_key(amf, k, key, eid, ek))
  (%kk : Hp.Moved(st, k, t, Ho.Ho.complete(st, assoc, _, ue, ctx, nh, r, s, ts, True{})); Hp.complete_moved(st, assoc, k, t, ue, ctx, nh, r, s, ts, Hp.eat(st, assoc, amf, k, t, key, ue, eid, epend, ek, ep)))

def Hp.so_notify(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +amf: B.Bytes(), +ran: B.Bytes(), +uli: G.UserLocationInformation, +k: U32, +t: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 11, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +ev: {V.HandoverNotify.view(ies) == Done{V.HandoverNotify.View{amf, ran, uli}} : Result<&2, &2, B.Err, V.HandoverNotify.View>}, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +epend: {S.Ue.pending(Tb.Table.get(S.Ue, k, S.State.ues(st))) == Some{t} : Maybe<&2, U32>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {Bool.or(S.Ue.same_owner(Tb.Table.get(S.Ue, k, S.State.ues(st)), Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))))), S.Ue.on(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))), t)) == True{} : Bool}:
  +g = Tb.Table.get(S.Ue, k, S.State.ues(st))
  PW.Rt.view(V.HandoverNotify.View, x => {Bool.or(S.Ue.same_owner(g, Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(x)))), S.Ue.on(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(x))), t)) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 0, 11, crit, value, ies, c, i => V.HandoverNotify.view(i), r => Ho.Ho.notify_of_view(st, assoc, r), Done{V.HandoverNotify.View{amf, ran, uli}}, ep, ei, {==}, eup, {==}, ev, PW.Hw.notify_found(o => Hp.Moved(st, k, t, o), st, assoc, amf, ran, Hp.moved_keep(st, k, t, N.Ngap.unknown_ue(assoc)), +key => +ue => +ctx => +nh => source => t2 => +r => +s => +ts => sp => +ek => +ep2 => eph => es => Hp.notify_go(st, assoc, amf, k, t, key, ue, ctx, nh, r, s, ts, eid, epend, ek, ep2)))

def L.amf.handover.single_owner(st, ev, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, uli, j, k, t):
  ({==}, (e0 => So.step(st, ev, entropy, e0), (ep => Hp.so_required(st, entropy, assoc, stream, len, bytes, crit, value, j, ep), (ep => Hp.so_ack(st, entropy, assoc, stream, len, bytes, crit, value, j, ep), (ep => Hp.so_failure(st, entropy, assoc, stream, len, bytes, crit, value, j, ep), (ep => Hp.so_cancel(st, entropy, assoc, stream, len, bytes, crit, value, j, ep), (ep => Hp.so_status(st, entropy, assoc, stream, len, bytes, crit, value, j, ep), (e => Hp.so_timer(st, entropy, k, t, j, e), +ep => +ei => +ev => +eid => +epend => PW.Rt.cases(x => {Bool.or(S.Ue.same_owner(Tb.Table.get(S.Ue, k, S.State.ues(st)), Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(x)))), S.Ue.on(Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(x))), t)) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 0, 11, crit, value, ies, c, ep, ei, {==}, Hp.moved_keep(st, k, t, N.Ngap.unhandled(assoc)), +eup => Hp.so_notify(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, uli, k, t, ep, ei, ev, eid, epend, eup))))))))))

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
  P.Bool.and_intro(S.Ues.timed(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy)))), S.Ids.free(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))), S.State.sessions(K.Kernel.state(K.Kernel.step(st, ev, entropy)))), Hp.timed(S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy)))), PL.Inv.step(~PL.Id.inv, ~PL.Id.pre, ~PL.Id.tx_put, ~PL.Id.tx_rephase, ~PL.Id.tx_del, ~PL.Id.tx_put_session, ~PL.Id.tx_revar, ~PL.Id.tx_del_session, ~(st0 => a => s => e1 => PL.Id.down(s, a, e1)), st, ev, entropy, e, P.Bool.and_true_l(S.Ids.free(S.State.ues(st), S.State.sessions(st)), S.Sessions.owned(S.State.sessions(st), S.State.ues(st)), e)))

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
      ne => PL.Lv.starts_l(k, acts, [], es)
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
  PW.Rt.read(o => ({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(o))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} -> Empty) -> {N.Acts.starts(k, K.Kernel.actions(o)) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 0, 12, crit, value, ep, {==}, ne => Empty.absurd({N.Acts.starts(k, N.Ngap.bad_pdu(assoc)) == True{} : Bool}, ne({==})), ne => Empty.absurd({N.Acts.starts(k, N.Ngap.unhandled(assoc)) == True{} : Bool}, ne({==})), +ies => Hp.g_step(st, k, Ho.Ho.required_of_view(st, assoc, V.HandoverRequired.view(ies)), Hp.required(st, k, assoc, V.HandoverRequired.view(ies))))

def Hp.g_ack(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +k: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{1, 13, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}) -> ({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} -> Empty) -> {N.Acts.starts(k, K.Kernel.actions(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == True{} : Bool}:
  PW.Rt.read(o => ({Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(o))) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} -> Empty) -> {N.Acts.starts(k, K.Kernel.actions(o)) == True{} : Bool}, st, entropy, assoc, stream, len, bytes, 1, 13, crit, value, ep, {==}, ne => Empty.absurd({N.Acts.starts(k, N.Ngap.bad_pdu(assoc)) == True{} : Bool}, ne({==})), ne => Empty.absurd({N.Acts.starts(k, N.Ngap.unhandled(assoc)) == True{} : Bool}, ne({==})), +ies => Hp.g_step(st, k, Ho.Ho.ack_of_view(st, assoc, stream, V.HandoverRequestAcknowledge.view(ies)), Hp.ack(st, k, assoc, stream, V.HandoverRequestAcknowledge.view(ies))))

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

# No step stops a pending handover's guard
# ----------------------------------------
# A step that stops timer k, a key no session holds, leaves no row under k
# with a handover pending: a UE procedure stops a guard only with a
# transaction that ends its key's handover (PL.Lv.stops), a session settled
# or gone has its own row's guard stopped, and nothing else stops a guard.

# What every row under a key holds: no handover pending; or a pair the
# context m held before the step chains to (PL.Lv.chains), or, where m held
# none, the first pair the actions send key's KgNB for (PL.Lv.firsts); or a
# NAS context the messages msgs leave, sealed in turn from what b held
# (N.Fresh.holds).
type Rw is Data:
  Idle{}
  From{m: Maybe<&2, S.Ue>, key: U32, acts: List<&2, N.Act>}
  Fresh{b: Maybe<&2, Sec.Nas.Ctx>, msgs: List<&2, B.Bytes()>}

def Hs.holds(+r: Rw, +p: S.Phase) -> Bool:
  match r:
    case Idle{}:
      S.Phase.idle(p)
    case From{+m, +key, +acts}:
      Bool.or(PL.Lv.chains(S.Phase.nh(p), S.Ue.nh(m)), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(m))), PL.Lv.firsts(S.Phase.nh(p), S.Ue.mode_k_amf(m), key, acts)))
    case Fresh{+b, +msgs}:
      N.Fresh.holds(b, S.Phase.nas(p), msgs)

def Hs.rows(+t: U32, +r: Rw, ues: Tb.Table(S.Ue)) -> Bool:
  match ues:
    case Nil{}:
      True{}
    case (+k0, +v) <> more:
      Bool.and(Bool.or(Bool.not(U32.is_eq(k0, t)), Hs.holds(r, S.Ue.phase(v))), Hs.rows(t, r, more))

def Hs.unpend(+m: Maybe<&2, U32>, +e: {Bool.not(Tb.Table.present(U32, m)) == True{} : Bool}) -> {m == None{} : Maybe<&2, U32>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, U32>}, P.Refute.bool(e))

def Hs.none_row(+t: U32, +k0: U32, +v: S.Ue, +more: Tb.Table(S.Ue), +b: Bool, +e: {Bool.and(Bool.or(Bool.not(b), S.Phase.idle(S.Ue.phase(v))), Hs.rows(t, Idle{}, more)) == True{} : Bool}, ih: {Hs.rows(t, Idle{}, more) == True{} : Bool} -> {S.Ue.pending(Tb.Table.get(S.Ue, t, more)) == None{} : Maybe<&2, U32>}) -> {S.Ue.pending(Tb.Table.hit(S.Ue, v, Tb.Table.get(S.Ue, t, more), b)) == None{} : Maybe<&2, U32>}:
  match b:
    case True{}:
      Hs.unpend(S.Phase.pending(S.Ue.phase(v)), P.Bool.and_true_l(S.Phase.idle(S.Ue.phase(v)), Hs.rows(t, Idle{}, more), e))
    case False{}:
      ih(P.Bool.and_true_r(True{}, Hs.rows(t, Idle{}, more), e))

def Hs.none(+t: U32, +ues: Tb.Table(S.Ue), +e: {Hs.rows(t, Idle{}, ues) == True{} : Bool}) -> {S.Ue.pending(Tb.Table.get(S.Ue, t, ues)) == None{} : Maybe<&2, U32>}:
  match ues:
    case Nil{}:
      {==}
    case (+k0, +v) <> +more:
      Hs.none_row(t, k0, v, more, U32.is_eq(k0, t), e, e2 => Hs.none(t, more, e2))

# Rows a sieve keeps keep it; a context put or forgotten under t takes every
# row under t with it.
def Hs.sift(+t: U32, +r: Rw, +s: S.Sieve, +ues: Tb.Table(S.Ue), +e: {Hs.rows(t, r, ues) == True{} : Bool}) -> {Hs.rows(t, r, S.Ues.sift(s, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      +x = Bool.or(Bool.not(U32.is_eq(k, t)), Hs.holds(r, S.Ue.phase(v)))
      +h0 = P.Bool.and_true_l(x, Hs.rows(t, r, more), e)
      P.Keep.by(S.Ue, tb => {Hs.rows(t, r, tb) == True{} : Bool}, k, v, S.Ues.sift(s, more), S.Sieve.keeps(s, k, v), ek => h => P.Bool.and_intro(x, Hs.rows(t, r, S.Ues.sift(s, more)), h0, h), Hs.sift(t, r, s, more, P.Bool.and_true_r(x, Hs.rows(t, r, more), e)))

def Hs.other(+t: U32, +r: Rw, +k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), +ne: {U32.is_eq(k, t) == False{} : Bool}, +h: {Hs.rows(t, r, rest) == True{} : Bool}) -> {Hs.rows(t, r, (k, v) <> rest) == True{} : Bool}:
  sn = Equal.sym(Bool, U32.is_eq(k, t), False{}, ne)
  (%sn : {Bool.and(Bool.or(Bool.not(_), Hs.holds(r, S.Ue.phase(v))), Hs.rows(t, r, rest)) == True{} : Bool}; h)

def Hs.cleared(+t: U32, +r: Rw, +u: S.Ue, +k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), +b: Bool, +eb: {S.Sieve.keeps(S.Clear{t, u}, k, v) == b : Bool}, +h: {Hs.rows(t, r, rest) == True{} : Bool}) -> {Hs.rows(t, r, Tb.Table.keep(S.Ue, k, v, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      +nc = P.Bool.not_true(Bool.or(U32.is_eq(k, t), S.Ue.conflicts(u, v)), eb)
      Hs.other(t, r, k, v, rest, P.Bool.or_false_l(U32.is_eq(k, t), S.Ue.conflicts(u, v), nc), h)
    case False{}:
      h

def Hs.clear(+t: U32, +r: Rw, +u: S.Ue, +ues: Tb.Table(S.Ue)) -> {Hs.rows(t, r, S.Ues.sift(S.Clear{t, u}, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      Hs.cleared(t, r, u, k, v, S.Ues.sift(S.Clear{t, u}, more), S.Sieve.keeps(S.Clear{t, u}, k, v), {==}, Hs.clear(t, r, u, more))

def Hs.excepted(+t: U32, +r: Rw, +k: U32, +v: S.Ue, +rest: Tb.Table(S.Ue), +b: Bool, +eb: {S.Sieve.keeps(S.Except{t}, k, v) == b : Bool}, +h: {Hs.rows(t, r, rest) == True{} : Bool}) -> {Hs.rows(t, r, Tb.Table.keep(S.Ue, k, v, rest, b)) == True{} : Bool}:
  match b:
    case True{}:
      Hs.other(t, r, k, v, rest, P.Bool.not_true(U32.is_eq(k, t), eb), h)
    case False{}:
      h

def Hs.except(+t: U32, +r: Rw, +ues: Tb.Table(S.Ue)) -> {Hs.rows(t, r, S.Ues.sift(S.Except{t}, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +v) <> +more:
      Hs.excepted(t, r, k, v, S.Ues.sift(S.Except{t}, more), S.Sieve.keeps(S.Except{t}, k, v), {==}, Hs.except(t, r, more))

# A phase change: under t, into a phase that holds; into such a phase
# anywhere; or under another key.
def Hs.on_row(+r: Rw, +p: S.Phase, +u: S.Ue, +b: Bool, +ei: {Hs.holds(r, p) == True{} : Bool}) -> {Bool.or(Bool.not(b), Hs.holds(r, S.Ue.phase(S.Ue.rephase_if(u, p, b)))) == True{} : Bool}:
  match b:
    case True{}:
      sp = Equal.sym(S.Phase, S.Ue.phase(S.Ue.with_phase(u, p)), p, PL.Lv.p_phase(u, p))
      (%sp : {Bool.or(False{}, Hs.holds(r, _)) == True{} : Bool}; ei)
    case False{}:
      {==}

def Hs.rephase_on(+t: U32, +r: Rw, +p: S.Phase, +ues: Tb.Table(S.Ue), +ei: {Hs.holds(r, p) == True{} : Bool}) -> {Hs.rows(t, r, S.Ues.rephase(t, p, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k, t)), Hs.holds(r, S.Ue.phase(S.Ue.rephase_if(u, p, U32.is_eq(k, t))))), Hs.rows(t, r, S.Ues.rephase(t, p, more)), Hs.on_row(r, p, u, U32.is_eq(k, t), ei), Hs.rephase_on(t, r, p, more, ei))

def Hs.holds_row(+r: Rw, +x: Bool, +u: S.Ue, +p: S.Phase, +c: Bool, +ei: {Hs.holds(r, p) == True{} : Bool}, +er: {Bool.or(x, Hs.holds(r, S.Ue.phase(u))) == True{} : Bool}) -> {Bool.or(x, Hs.holds(r, S.Ue.phase(S.Ue.rephase_if(u, p, c)))) == True{} : Bool}:
  match c:
    case True{}:
      sp = Equal.sym(S.Phase, S.Ue.phase(S.Ue.with_phase(u, p)), p, PL.Lv.p_phase(u, p))
      P.Bool.or_r(x, Hs.holds(r, S.Ue.phase(S.Ue.with_phase(u, p))), (%sp : {Hs.holds(r, _) == True{} : Bool}; ei))
    case False{}:
      er

def Hs.rephase_holds(+t: U32, +r: Rw, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ei: {Hs.holds(r, p) == True{} : Bool}, +e: {Hs.rows(t, r, ues) == True{} : Bool}) -> {Hs.rows(t, r, S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      +x = Bool.not(U32.is_eq(k, t))
      P.Bool.and_intro(Bool.or(x, Hs.holds(r, S.Ue.phase(S.Ue.rephase_if(u, p, U32.is_eq(k, key))))), Hs.rows(t, r, S.Ues.rephase(key, p, more)), Hs.holds_row(r, x, u, p, U32.is_eq(k, key), ei, P.Bool.and_true_l(Bool.or(x, Hs.holds(r, S.Ue.phase(u))), Hs.rows(t, r, more), e)), Hs.rephase_holds(t, r, key, p, more, ei, P.Bool.and_true_r(Bool.or(x, Hs.holds(r, S.Ue.phase(u))), Hs.rows(t, r, more), e)))

def Hs.other_row(+t: U32, +r: Rw, +key: U32, +k: U32, +u: S.Ue, +p: S.Phase, +b: Bool, +eb: {U32.is_eq(k, t) == b : Bool}, +ne: {U32.is_eq(key, t) == False{} : Bool}, +er: {Bool.or(Bool.not(b), Hs.holds(r, S.Ue.phase(u))) == True{} : Bool}) -> {Bool.or(Bool.not(b), Hs.holds(r, S.Ue.phase(S.Ue.rephase_if(u, p, U32.is_eq(k, key))))) == True{} : Bool}:
  match b:
    case True{}:
      ek = Equal.sym(U32, k, t, P.U32.eq_of_is_eq(k, t, eb))
      nk = Equal.trans(Bool, U32.is_eq(t, key), U32.is_eq(key, t), False{}, P.U32.sym(t, key), ne)
      snk = Equal.sym(Bool, U32.is_eq(t, key), False{}, nk)
      (%ek : {Bool.or(False{}, Hs.holds(r, S.Ue.phase(S.Ue.rephase_if(u, p, U32.is_eq(_, key))))) == True{} : Bool}; (%snk : {Bool.or(False{}, Hs.holds(r, S.Ue.phase(S.Ue.rephase_if(u, p, _)))) == True{} : Bool}; er))
    case False{}:
      {==}

def Hs.rephase_other(+t: U32, +r: Rw, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +ne: {U32.is_eq(key, t) == False{} : Bool}, +e: {Hs.rows(t, r, ues) == True{} : Bool}) -> {Hs.rows(t, r, S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match ues:
    case Nil{}:
      {==}
    case (+k, +u) <> +more:
      +x = Bool.or(Bool.not(U32.is_eq(k, t)), Hs.holds(r, S.Ue.phase(u)))
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k, t)), Hs.holds(r, S.Ue.phase(S.Ue.rephase_if(u, p, U32.is_eq(k, key))))), Hs.rows(t, r, S.Ues.rephase(key, p, more)), Hs.other_row(t, r, key, k, u, p, U32.is_eq(k, t), {==}, ne, P.Bool.and_true_l(x, Hs.rows(t, r, more), e)), Hs.rephase_other(t, r, key, p, more, ne, P.Bool.and_true_r(x, Hs.rows(t, r, more), e)))

def Hs.keeps_rephase(+t: U32, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +x: Bool, +ex: {S.Phase.idle(p) == x : Bool}, +h: {Bool.or(x, Bool.not(U32.is_eq(key, t))) == True{} : Bool}, +e: {Hs.rows(t, Idle{}, ues) == True{} : Bool}) -> {Hs.rows(t, Idle{}, S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match x:
    case True{}:
      Hs.rephase_holds(t, Idle{}, key, p, ues, ex, e)
    case False{}:
      Hs.rephase_other(t, Idle{}, key, p, ues, P.Bool.not_true(U32.is_eq(key, t), h), e)

# A transaction that makes no handover pending under t keeps every row under
# t with none pending; one that idles t leaves none whatever the table.
def Hs.keeps(+t: U32, +tx: S.Tx, +ues: Tb.Table(S.Ue), +h: {PL.Lv.keeps(t, tx) == True{} : Bool}, +e: {Hs.rows(t, Idle{}, ues) == True{} : Bool}) -> {Hs.rows(t, Idle{}, PT.Tk.ues(tx, ues)) == True{} : Bool}:
  match tx:
    case S.Rephase{+key, +p}:
      Hs.keeps_rephase(t, key, p, ues, S.Phase.idle(p), {==}, h, e)
    case S.Put{+key, +u}:
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(key, t)), S.Phase.idle(S.Ue.phase(u))), Hs.rows(t, Idle{}, S.Ues.sift(S.Clear{key, u}, ues)), P.Bool.or_swap(S.Phase.idle(S.Ue.phase(u)), Bool.not(U32.is_eq(key, t)), h), Hs.sift(t, Idle{}, S.Clear{key, u}, ues, e))
    case S.Del{+key}:
      Hs.sift(t, Idle{}, S.Except{key}, ues, e)
    case S.Both{+a, +b}:
      Hs.keeps(t, b, PT.Tk.ues(a, ues), P.Bool.and_true_r(PL.Lv.keeps(t, a), PL.Lv.keeps(t, b), h), Hs.keeps(t, a, ues, P.Bool.and_true_l(PL.Lv.keeps(t, a), PL.Lv.keeps(t, b), h), e))
    case S.Keep{}:
      e
    case S.PutSession{key, s}:
      e
    case S.Revar{key, v}:
      e
    case S.DelSession{key}:
      e
    case S.Subs{subs}:
      e
    case S.SetLink{link}:
      e
    case S.BumpUe{bk}:
      e
    case S.BumpSeq{n}:
      e

def Hs.idles_both(+t: U32, +a: S.Tx, +b: S.Tx, +ues: Tb.Table(S.Ue), +x: Bool, +ex: {PL.Lv.idles(t, b) == x : Bool}, +h: {Bool.or(x, Bool.and(PL.Lv.idles(t, a), PL.Lv.keeps(t, b))) == True{} : Bool}, rb: {PL.Lv.idles(t, b) == True{} : Bool} -> {Hs.rows(t, Idle{}, PT.Tk.ues(b, PT.Tk.ues(a, ues))) == True{} : Bool}, ra: {PL.Lv.idles(t, a) == True{} : Bool} -> {Hs.rows(t, Idle{}, PT.Tk.ues(a, ues)) == True{} : Bool}) -> {Hs.rows(t, Idle{}, PT.Tk.ues(b, PT.Tk.ues(a, ues))) == True{} : Bool}:
  match x:
    case True{}:
      rb(ex)
    case False{}:
      Hs.keeps(t, b, PT.Tk.ues(a, ues), P.Bool.and_true_r(PL.Lv.idles(t, a), PL.Lv.keeps(t, b), h), ra(P.Bool.and_true_l(PL.Lv.idles(t, a), PL.Lv.keeps(t, b), h)))

def Hs.idles(+t: U32, +tx: S.Tx, +ues: Tb.Table(S.Ue), +h: {PL.Lv.idles(t, tx) == True{} : Bool}) -> {Hs.rows(t, Idle{}, PT.Tk.ues(tx, ues)) == True{} : Bool}:
  match tx:
    case S.Rephase{+key, +p}:
      ek = Equal.sym(U32, key, t, P.U32.eq_of_is_eq(key, t, P.Bool.and_true_l(U32.is_eq(key, t), S.Phase.idle(p), h)))
      (%ek : {Hs.rows(t, Idle{}, S.Ues.rephase(_, p, ues)) == True{} : Bool}; Hs.rephase_on(t, Idle{}, p, ues, P.Bool.and_true_r(U32.is_eq(key, t), S.Phase.idle(p), h)))
    case S.Put{+key, +u}:
      ek = Equal.sym(U32, key, t, P.U32.eq_of_is_eq(key, t, P.Bool.and_true_l(U32.is_eq(key, t), S.Phase.idle(S.Ue.phase(u)), h)))
      ht = P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(t, t)), S.Phase.idle(S.Ue.phase(u))), Hs.rows(t, Idle{}, S.Ues.sift(S.Clear{t, u}, ues)), P.Bool.or_r(Bool.not(U32.is_eq(t, t)), S.Phase.idle(S.Ue.phase(u)), P.Bool.and_true_r(U32.is_eq(key, t), S.Phase.idle(S.Ue.phase(u)), h)), Hs.clear(t, Idle{}, u, ues))
      (%ek : {Hs.rows(t, Idle{}, S.Ues.put(_, u, ues)) == True{} : Bool}; ht)
    case S.Del{+key}:
      ek = Equal.sym(U32, key, t, P.U32.eq_of_is_eq(key, t, h))
      (%ek : {Hs.rows(t, Idle{}, S.Ues.del(_, ues)) == True{} : Bool}; Hs.except(t, Idle{}, ues))
    case S.Both{+a, +b}:
      Hs.idles_both(t, a, b, ues, PL.Lv.idles(t, b), {==}, h, e2 => Hs.idles(t, b, PT.Tk.ues(a, ues), e2), e2 => Hs.idles(t, a, ues, e2))
    case S.Keep{}:
      Empty.absurd({Hs.rows(t, Idle{}, ues) == True{} : Bool}, P.Refute.bool(h))
    case S.PutSession{key, s}:
      Empty.absurd({Hs.rows(t, Idle{}, ues) == True{} : Bool}, P.Refute.bool(h))
    case S.Revar{key, v}:
      Empty.absurd({Hs.rows(t, Idle{}, ues) == True{} : Bool}, P.Refute.bool(h))
    case S.DelSession{key}:
      Empty.absurd({Hs.rows(t, Idle{}, ues) == True{} : Bool}, P.Refute.bool(h))
    case S.Subs{subs}:
      Empty.absurd({Hs.rows(t, Idle{}, ues) == True{} : Bool}, P.Refute.bool(h))
    case S.SetLink{link}:
      Empty.absurd({Hs.rows(t, Idle{}, ues) == True{} : Bool}, P.Refute.bool(h))
    case S.BumpUe{bk}:
      Empty.absurd({Hs.rows(t, Idle{}, ues) == True{} : Bool}, P.Refute.bool(h))
    case S.BumpSeq{n}:
      Empty.absurd({Hs.rows(t, Idle{}, ues) == True{} : Bool}, P.Refute.bool(h))

# The actions of a step
# ---------------------

def Hs.Q(+k: U32, o: N.Step()) -> Type:
  {N.Acts.stops(k, K.Kernel.actions(o)) == True{} : Bool} -> {Hs.rows(k, Idle{}, S.State.ues(K.Kernel.state(o))) == True{} : Bool}

# A stop of timer k among actions each idled by tx: tx idles k.
def Hs.act(+k: U32, +tx: S.Tx, +a: N.Act, +e1: {N.Act.stops(k, a) == True{} : Bool}, +e2: {PL.Lv.stop(tx, PL.Lv.cancelled(a)) == True{} : Bool}) -> {PL.Lv.idles(k, tx) == True{} : Bool}:
  match a:
    case N.TimerCancel{+t}:
      ek = P.U32.eq_of_is_eq(t, k, e1)
      (%ek : {PL.Lv.idles(_, tx) == True{} : Bool}; e2)
    case N.DlNas{assoc, stream, key, ran_id, nas}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.Ics{assoc, stream, key, ran_id, cfg, caps, k_gnb, nas}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.PduSetup{assoc, stream, key, ran_id, psi, sst, nas, transfer}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.Release{assoc, stream, key, ran_id, cause}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.SwitchAck{assoc, stream, key, ran_id, caps, nh, switched, released, sst}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.SwitchFail{assoc, stream, ue, amf, ran_id, psis, cause}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.UeSend{assoc, stream, key, bytes}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.PduRelease{assoc, stream, key, ran_id, psi, nas}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.ErrInd{assoc, cause}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.Setup{assoc, answer}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.Pfcp{ue, bytes}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.Note{level, text}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case N.TimerStart{ue, timer, ms}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))

def Hs.acts_or(+k: U32, +tx: S.Tx, +a: N.Act, +more: List<&2, N.Act>, +x: Bool, +ex: {N.Act.stops(k, a) == x : Bool}, +e1: {Bool.or(x, N.Acts.stops(k, more)) == True{} : Bool}, +e2: {PL.Lv.stops(tx, a <> more) == True{} : Bool}, ih: {N.Acts.stops(k, more) == True{} : Bool} -> {PL.Lv.stops(tx, more) == True{} : Bool} -> {PL.Lv.idles(k, tx) == True{} : Bool}) -> {PL.Lv.idles(k, tx) == True{} : Bool}:
  match x:
    case True{}:
      Hs.act(k, tx, a, ex, P.Bool.and_true_l(PL.Lv.stop(tx, PL.Lv.cancelled(a)), PL.Lv.stops(tx, more), e2))
    case False{}:
      ih(e1, P.Bool.and_true_r(PL.Lv.stop(tx, PL.Lv.cancelled(a)), PL.Lv.stops(tx, more), e2))

def Hs.acts(+k: U32, +tx: S.Tx, +acts: List<&2, N.Act>, +e1: {N.Acts.stops(k, acts) == True{} : Bool}, +e2: {PL.Lv.stops(tx, acts) == True{} : Bool}) -> {PL.Lv.idles(k, tx) == True{} : Bool}:
  match acts:
    case Nil{}:
      Empty.absurd({PL.Lv.idles(k, tx) == True{} : Bool}, P.Refute.bool(e1))
    case +a <> +more:
      Hs.acts_or(k, tx, a, more, N.Act.stops(k, a), {==}, e1, e2, f1 => f2 => Hs.acts(k, tx, more, f1, f2))

# A stop in actions appended is a stop in one part.
def Hs.app_or(-R: Type, +k: U32, +a: N.Act, +more: List<&2, N.Act>, +ys: List<&2, N.Act>, +x: Bool, +ex: {N.Act.stops(k, a) == x : Bool}, +e: {Bool.or(x, N.Acts.stops(k, List.append(&2, N.Act, more, ys))) == True{} : Bool}, l: {N.Acts.stops(k, a <> more) == True{} : Bool} -> R, ih: {N.Acts.stops(k, List.append(&2, N.Act, more, ys)) == True{} : Bool} -> ({N.Acts.stops(k, more) == True{} : Bool} -> R) -> R) -> R:
  match x:
    case True{}:
      sx = Equal.sym(Bool, N.Act.stops(k, a), True{}, ex)
      l((%sx : {Bool.or(_, N.Acts.stops(k, more)) == True{} : Bool}; {==}))
    case False{}:
      sx = Equal.sym(Bool, N.Act.stops(k, a), False{}, ex)
      ih(e, h => l((%sx : {Bool.or(_, N.Acts.stops(k, more)) == True{} : Bool}; h)))

def Hs.app(-R: Type, +k: U32, +xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +e: {N.Acts.stops(k, List.append(&2, N.Act, xs, ys)) == True{} : Bool}, l: {N.Acts.stops(k, xs) == True{} : Bool} -> R, r: {N.Acts.stops(k, ys) == True{} : Bool} -> R) -> R:
  match xs:
    case Nil{}:
      r(e)
    case +a <> +more:
      Hs.app_or(R, k, a, more, ys, N.Act.stops(k, a), {==}, e, l, e2 => l2 => Hs.app(R, k, more, ys, e2, l2, r))

# Actions that touch no timer stop none.
def Hs.untouched(+k: U32, +acts: List<&2, N.Act>, +e: {N.Acts.touches(k, acts) == False{} : Bool}) -> {N.Acts.stops(k, acts) == False{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      +t = Bool.or(N.Act.starts(k, a), N.Act.stops(k, a))
      P.Bool.or_false(N.Act.stops(k, a), N.Acts.stops(k, more), P.Bool.or_false_r(N.Act.starts(k, a), N.Act.stops(k, a), P.Bool.or_false_l(t, N.Acts.touches(k, more), e)), Hs.untouched(k, more, P.Bool.or_false_r(t, N.Acts.touches(k, more), e)))

# A transaction of the session side idles no key, so actions it idles stop
# no timer.
def Hs.sx_idles(+t: U32, +tx: S.Tx, +e: {PW.Sx.only(tx) == True{} : Bool}) -> {PL.Lv.idles(t, tx) == False{} : Bool}:
  match tx:
    case S.Both{+a, +b}:
      +ea = P.Bool.and_true_l(PW.Sx.only(a), PW.Sx.only(b), e)
      +eb = Hs.sx_idles(t, b, P.Bool.and_true_r(PW.Sx.only(a), PW.Sx.only(b), e))
      sb = Equal.sym(Bool, PL.Lv.idles(t, b), False{}, eb)
      sa = Equal.sym(Bool, PL.Lv.idles(t, a), False{}, Hs.sx_idles(t, a, ea))
      (%sb : {Bool.or(_, Bool.and(PL.Lv.idles(t, a), PL.Lv.keeps(t, b))) == False{} : Bool}; (%sa : {Bool.or(False{}, Bool.and(_, PL.Lv.keeps(t, b))) == False{} : Bool}; {==}))
    case S.Rephase{key, phase}:
      Empty.absurd({PL.Lv.idles(t, S.Rephase{key, phase}) == False{} : Bool}, P.Refute.bool(e))
    case S.Put{key, ue}:
      Empty.absurd({PL.Lv.idles(t, S.Put{key, ue}) == False{} : Bool}, P.Refute.bool(e))
    case S.Del{key}:
      Empty.absurd({PL.Lv.idles(t, S.Del{key}) == False{} : Bool}, P.Refute.bool(e))
    case S.PutSession{key, s}:
      Empty.absurd({PL.Lv.idles(t, S.PutSession{key, s}) == False{} : Bool}, P.Refute.bool(e))
    case S.Subs{subs}:
      Empty.absurd({PL.Lv.idles(t, S.Subs{subs}) == False{} : Bool}, P.Refute.bool(e))
    case S.BumpUe{bk}:
      Empty.absurd({PL.Lv.idles(t, S.BumpUe{bk}) == False{} : Bool}, P.Refute.bool(e))
    case S.Keep{}:
      {==}
    case S.Revar{key, v}:
      {==}
    case S.DelSession{key}:
      {==}
    case S.SetLink{link}:
      {==}
    case S.BumpSeq{n}:
      {==}

def Hs.quiet_if(+k: U32, +tx: S.Tx, +acts: List<&2, N.Act>, +x: Bool, +ex: {N.Acts.stops(k, acts) == x : Bool}, +hs: {PL.Lv.stops(tx, acts) == True{} : Bool}, +hx: {PW.Sx.only(tx) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      ei = Equal.trans(Bool, True{}, PL.Lv.idles(k, tx), False{}, Equal.sym(Bool, PL.Lv.idles(k, tx), True{}, Hs.acts(k, tx, acts, ex, hs)), Hs.sx_idles(k, tx, hx))
      Empty.absurd({True{} == False{} : Bool}, P.Refute.true_false(ei))
    case False{}:
      {==}

def Hs.quiet(+k: U32, +tx: S.Tx, +acts: List<&2, N.Act>, +hs: {PL.Lv.stops(tx, acts) == True{} : Bool}, +hx: {PW.Sx.only(tx) == True{} : Bool}) -> {N.Acts.stops(k, acts) == False{} : Bool}:
  Hs.quiet_if(k, tx, acts, N.Acts.stops(k, acts), {==}, hs, hx)

# The guards of the sessions gone are those of rows of the session table.
def Hs.gone_if(+k: U32, +k0: U32, +t: S.Session, +more: Tb.Table(S.Session), +after: Tb.Table(S.Session), +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +es: {Tb.Table.hit(S.Session, t, Tb.Table.get(S.Session, k, more), b) == None{} : Maybe<&2, S.Session>}, ih: {Tb.Table.get(S.Session, k, more) == None{} : Maybe<&2, S.Session>} -> {N.Acts.touches(k, N.Gone.cancels(more, after)) == False{} : Bool}) -> {N.Acts.touches(k, N.Gone.cancels((k0, t) <> more, after)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({N.Acts.touches(k, N.Gone.cancels((k0, t) <> more, after)) == False{} : Bool}, P.Refute.none_some(S.Session, t, Equal.sym(Maybe<&2, S.Session>, Some{t}, None{}, es)))
    case False{}:
      PSm.Run.app(k, N.Gone.row(k0, t, Tb.Table.has(S.Session, k0, after)), N.Gone.cancels(more, after), PSm.Run.row(k0, t, Tb.Table.has(S.Session, k0, after), k, eb), ih(es))

def Hs.gone(+k: U32, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session), +es: {Tb.Table.get(S.Session, k, before) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.touches(k, N.Gone.cancels(before, after)) == False{} : Bool}:
  match before:
    case Nil{}:
      {==}
    case (+k0, +t) <> +more:
      Hs.gone_if(k, k0, t, more, after, U32.is_eq(k0, k), {==}, es, e2 => Hs.gone(k, more, after, e2))

def Hs.when(+k: U32, +keeps: Bool, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session), +es: {Tb.Table.get(S.Session, k, before) == None{} : Maybe<&2, S.Session>}) -> {N.Acts.stops(k, N.Gone.when(keeps, before, after)) == False{} : Bool}:
  match keeps:
    case True{}:
      {==}
    case False{}:
      Hs.untouched(k, N.Gone.cancels(before, after), Hs.gone(k, before, after, es))

# The outcome of a procedure, rendered: what its actions stop, its
# transaction idles; the guards of sessions gone are not k.
def Hs.out(+st: S.State, +k: U32, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}, +o: N.GOut(), +h: {PL.Lv.ok(st, o) == True{} : Bool}) -> Hs.Q(k, N.Step.of(st, o)):
  match o:
    case (+tx, +acts):
      +st2 = S.Tx.apply(tx, st)
      +hs = PL.Lv.ok_stops(st, (tx, acts), h)
      eu = Equal.sym(Tb.Table(S.Ue), S.State.ues(st2), PT.Tk.ues(tx, S.State.ues(st)), PT.Tk.ues_apply(tx, st))
      e => Hs.app({Hs.rows(k, Idle{}, S.State.ues(st2)) == True{} : Bool}, k, acts, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(st2)), e, l => (%eu : {Hs.rows(k, Idle{}, _) == True{} : Bool}; Hs.idles(k, tx, S.State.ues(st), Hs.acts(k, tx, acts, l, hs))), r => P.Bool.contra({Hs.rows(k, Idle{}, S.State.ues(st2)) == True{} : Bool}, N.Acts.stops(k, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(st2))), r, Hs.when(k, S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(st2), es)))

# An outcome whose actions stop no k, rendered.
def Hs.quiet_out(+st: S.State, +k: U32, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}, +o: N.GOut(), +hq: {N.Acts.stops(k, N.Out.acts(o)) == False{} : Bool}) -> Hs.Q(k, N.Step.of(st, o)):
  match o:
    case (+tx, +acts):
      +st2 = S.Tx.apply(tx, st)
      +g = N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(st2))
      -G = {Hs.rows(k, Idle{}, S.State.ues(st2)) == True{} : Bool}
      e => Hs.app(G, k, acts, g, e, l => P.Bool.contra(G, N.Acts.stops(k, acts), l, hq), r => P.Bool.contra(G, N.Acts.stops(k, g), r, Hs.when(k, S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(st2), es)))

# An association's contexts going: they go by a sieve, and only the guards of
# sessions stop.
def Hs.drop_quiet(-R: Type, +st: S.State, +assoc: U32, +k: U32, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}, +e: {N.Acts.stops(k, K.Kernel.actions(R.Route.drop(st, assoc))) == True{} : Bool}) -> R:
  match st:
    case S.State{+config, +subs, +assocs, +ues, +sessions, +pfcp_seq, +next_ue, +n4}:
      +s0 : S.State = S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, n4}
      +gone = S.Sessions.sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions)
      +d = Up.N4.deletions(gone, pfcp_seq)
      +kept = S.Sessions.sift(S.SOwned{S.Ues.drop_assoc(assoc, ues)}, S.State.sessions(S.Tx.apply(N.Out.tx(d), s0)))
      +hd = PL.Lv.dels(s0, gone, pfcp_seq, PL.Lv.srows_sift(S.SOrphan{S.Ues.drop_assoc(assoc, ues)}, sessions), PL.Lv.krows_orphan(s0, S.Ues.drop_assoc(assoc, ues)))
      +g = N.Gone.cancels(sessions, kept)
      Hs.app(R, k, N.Out.acts(d), g, e, l => P.Bool.contra(R, N.Acts.stops(k, N.Out.acts(d)), l, Hs.quiet(k, N.Out.tx(d), N.Out.acts(d), PL.Lv.does_stops(s0, N.Out.tx(d), N.Out.acts(d), PL.Lv.free(s0, N.Out.tx(d)), hd), PW.Sx.deletions(gone, pfcp_seq))), r => P.Bool.contra(R, N.Acts.stops(k, g), r, Hs.untouched(k, g, Hs.gone(k, sessions, kept, es))))

def Hs.drop_rows(+s: S.State, +assoc: U32, +k: U32, +r: Rw, +e: {Hs.rows(k, r, S.State.ues(s)) == True{} : Bool}) -> {Hs.rows(k, r, S.State.ues(K.Kernel.state(R.Route.drop(s, assoc)))) == True{} : Bool}:
  match s:
    case S.State{config, subs, assocs, +ues, sessions, pfcp_seq, next_ue, n4}:
      Hs.sift(k, r, S.Others{assoc}, ues, e)

def Hs.config(+complete: Bool, +st: S.State, +tlvs: List<&2, T.Tlv>, +entropy: B.Bytes(), +k: U32, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}) -> Hs.Q(k, K.Kernel.config(complete, st, tlvs, entropy)):
  match complete:
    case False{}:
      e => P.Bool.contra({Hs.rows(k, Idle{}, S.State.ues(st)) == True{} : Bool}, N.Acts.stops(k, [N.Note{F.Error{}, "Config: a required tag is missing or invalid; configuration unchanged"}]), e, {==})
    case True{}:
      match st:
        case S.State{config, subs, assocs, ues, +sessions, pfcp_seq, next_ue, n4}:
          +cfg = S.Cfg.of(tlvs)
          +st2 : S.State = S.State{Some{cfg}, Au.Subscribers.of(S.Cfg.subscribers(cfg)), assocs, ues, sessions, pfcp_seq, next_ue, S.N4{List.take(&2, U32, entropy, 4n), S.Idle{}}}
          +n : List<&2, N.Act> = [N.Note{F.Info{}, "Config: loaded; PFCP association requested"}]
          +o = N.Out.also(Up.N4.start(st2), n)
          Hs.out(st2, k, es, o, PL.Lv.ok_of(st2, o, PL.Lv.also(st2, Up.N4.start(st2), n, PL.Lw.n4_start(st2), {==}, {==}, {==})))

def Hs.reset(+st: S.State, +assoc: U32, +k: U32, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}) -> Hs.Q(k, R.Route.reset(st, assoc)):
  +o = Ho.Ho.down(st, assoc)
  +s1 = N.Step.of(st, o)
  +s2 = R.Route.drop(N.Step.state(s1), assoc)
  -G = {Hs.rows(k, Idle{}, S.State.ues(N.Step.state(s2))) == True{} : Bool}
  q1 = Hs.out(st, k, es, o, PL.Lw.ho_down(st, assoc))
  ds = Equal.sym(Tb.Table(S.Session), S.State.sessions(N.Step.state(s1)), S.State.sessions(st), PL.Lw.down_sessions(st, assoc))
  es1 : {Tb.Table.get(S.Session, k, S.State.sessions(N.Step.state(s1))) == None{} : Maybe<&2, S.Session>} = (%ds : {Tb.Table.get(S.Session, k, _) == None{} : Maybe<&2, S.Session>}; es)
  e => Hs.app(G, k, N.Step.acts(s1), N.Step.acts(s2), e, l => Hs.drop_rows(N.Step.state(s1), assoc, k, Idle{}, q1(l)), r => Hs.drop_quiet(G, N.Step.state(s1), assoc, k, es1, r))

# NG Setup: its association's contexts re-initialised; the rest stops no k.
def Hs.ready(+st: S.State, +assoc: U32, +id: B.Bytes(), +ok: Bool, +acts: List<&2, N.Act>, +k: U32, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}, +tc: {N.Acts.touches(k, acts) == False{} : Bool}) -> Hs.Q(k, (S.State.ready(N.Step.state(R.Route.reset(st, assoc)), assoc, id, ok), List.append(&2, N.Act, N.Step.acts(R.Route.reset(st, assoc)), acts))):
  +s = N.Step.state(R.Route.reset(st, assoc))
  -G = {Hs.rows(k, Idle{}, S.State.ues(S.State.ready(s, assoc, id, ok))) == True{} : Bool}
  +xs = N.Step.acts(R.Route.reset(st, assoc))
  e => Hs.app(G, k, xs, acts, e, l => PW.Walk.assocs(ues => ss => Hs.rows(k, Idle{}, ues), s, S.Assocs.set(assoc, id, S.State.assocs(s), ok), [], Hs.reset(st, assoc, k, es)(l)), r => P.Bool.contra(G, N.Acts.stops(k, acts), r, Hs.untouched(k, acts, tc)))

# A session's guard firing while it is being deleted, and the UPF's answer to
# a deletion, stop no guard of their own.
def Hs.resend_quiet(+k: U32, +k1: U32, +t: S.Session, +p: S.SPhase, +request: B.Bytes(), +more: Bool) -> {N.Acts.stops(k, N.Out.acts(Gsm.Gsm.resend_if(k1, t, p, request, (S.DelSession{k1}, [N.Note{F.Warn{}, "PFCP: no Session Deletion Response; deletion given up"}]), more))) == False{} : Bool}:
  match more:
    case True{}:
      {==}
    case False{}:
      {==}

def Hs.dphase_quiet(+k: U32, +skey: U32, +msg: Pf.Msg, +p: S.SPhase) -> {N.Acts.stops(k, N.Out.acts(Gsm.Gsm.deleted_phase(skey, msg, p))) == False{} : Bool}:
  match p:
    case S.Deleting{guard, request}:
      Hs.untouched(k, Gsm.Gsm.deleted_notes(Up.N4.accepted(Up.N4.cause(msg))), PSm.Run.notes(k, Up.N4.accepted(Up.N4.cause(msg))))
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Hs.deleted_quiet(+k: U32, +msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> {N.Acts.stops(k, N.Out.acts(Gsm.Gsm.deleted(msg, m))) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Hs.dphase_quiet(k, skey, msg, S.Session.phase(s))

# A session the UPF settles has the guard of a row of the session table
# stopped, so not k.
def Hs.settled_if(+st: S.State, +k: U32, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}, +k1: U32, +tx: S.Tx, +more: List<&2, N.Act>, +x: Bool, +ex: {U32.is_eq(k1, k) == x : Bool}, +eh: {Tb.Table.has(S.Session, k1, S.State.sessions(st)) == True{} : Bool}, +h: {PL.Lv.ok(st, (tx, more)) == True{} : Bool}) -> {Bool.or(x, N.Acts.stops(k, List.append(&2, N.Act, more, N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)))))) == True{} : Bool} -> {Hs.rows(k, Idle{}, S.State.ues(S.Tx.apply(tx, st))) == True{} : Bool}:
  match x:
    case True{}:
      ek = P.U32.eq_of_is_eq(k1, k, ex)
      eh2 : {Tb.Table.has(S.Session, k, S.State.sessions(st)) == True{} : Bool} = (%ek : {Tb.Table.has(S.Session, _, S.State.sessions(st)) == True{} : Bool}; eh)
      se = Equal.sym(Maybe<&2, S.Session>, Tb.Table.get(S.Session, k, S.State.sessions(st)), None{}, es)
      e => P.Bool.contra({Hs.rows(k, Idle{}, S.State.ues(S.Tx.apply(tx, st))) == True{} : Bool}, Tb.Table.has(S.Session, k, S.State.sessions(st)), eh2, (%se : {Tb.Table.present(S.Session, _) == False{} : Bool}; {==}))
    case False{}:
      e => Hs.out(st, k, es, (tx, more), h)(e)

def Hs.ends(+st: S.State, +ev: F.Evt, +entropy: B.Bytes(), +k: U32, +es: {Tb.Table.get(S.Session, k, S.State.sessions(st)) == None{} : Maybe<&2, S.Session>}) -> Hs.Q(k, K.Kernel.step(st, ev, entropy)):
  PL.Dw.walk(o => Hs.Q(k, o), o => Hs.Q(k, N.Step.of(st, o)), st, ev, entropy, +acts => sp => tc => nr => e => P.Bool.contra({Hs.rows(k, Idle{}, S.State.ues(st)) == True{} : Bool}, N.Acts.stops(k, acts), e, Hs.untouched(k, acts, tc(k))), +assoc => ns => +id => +ok => +acts => sp => tc => nr => Hs.ready(st, assoc, id, ok, acts, k, es, tc(k)), +tlvs => Hs.config(S.Cfg.complete(tlvs), st, tlvs, entropy, k, es), +assoc => Hs.reset(st, assoc, k, es), o => h => h, +o => +h => Hs.out(st, k, es, o, h), +k1 => +t => +g => +r => ek => eu => em => ep => Hs.quiet_out(st, k, es, Gsm.Gsm.expired(st, k1, t, S.Deleting{g, r}), Hs.resend_quiet(k, k1, t, S.Deleting{S.Guard{U32.add(S.Guard.retries(g), 1)}, r}, r, U32.is_lt(S.Guard.retries(g), Up.N4.n1()))), +len => +bytes => +msg => +rest => ev2 => er => ek => Hs.quiet_out(st, k, es, Gsm.Gsm.deleted(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st))), Hs.deleted_quiet(k, msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))), +k1 => +tx => +more => ekd => eh => h => Hs.settled_if(st, k, es, k1, tx, more, U32.is_eq(k1, k), {==}, eh, h))

# amf.ncc.step
# ------------
# Every row under k holds a pair that chains to the one k held before the
# step, or the first one the step's actions send k's KgNB for: where no two
# contexts share a key, the table's row under k is the context k names, every
# phase a step writes under k chains to it (PL.Lv.chain) unless it is put
# over a context that held none and starts the chain the step sends
# (PL.Lv.seeds), and nothing else writes a phase.

def Nc.vacant(+k: U32, +k0: U32, +u0: S.Ue, +r: Rw, +rows: Tb.Table(S.Ue), +hc: {S.Ues.clear(k0, u0, rows) == True{} : Bool}, +ek: {k0 == k : U32}) -> {Hs.rows(k, r, rows) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+k1, +v) <> +more:
      +nc = Bool.not(S.Row.conflicts(k0, u0, k1, v))
      +n1 = P.Bool.or_false_l(U32.is_eq(k1, k0), S.Ue.conflicts(u0, v), P.Bool.not_true(S.Row.conflicts(k0, u0, k1, v), P.Bool.and_true_l(nc, S.Ues.clear(k0, u0, more), hc)))
      n2 : {U32.is_eq(k1, k) == False{} : Bool} = (%ek : {U32.is_eq(k1, _) == False{} : Bool}; n1)
      Hs.other(k, r, k1, v, more, n2, Nc.vacant(k, k0, u0, r, more, P.Bool.and_true_r(nc, S.Ues.clear(k0, u0, more), hc), ek))

# What a row holds before the step, read off the context m under its key.
type Rk is Data:
  Chain{key: U32, acts: List<&2, N.Act>}
  Kept{}

def Hs.from(s: Rk, +m: Maybe<&2, S.Ue>) -> Rw:
  match s:
    case Chain{key, acts}:
      From{m, key, acts}
    case Kept{}:
      Fresh{S.Ue.nas(m), []}

def Hs.self(+s: Rk, +u: S.Ue) -> {Hs.holds(Hs.from(s, Some{u}), S.Ue.phase(u)) == True{} : Bool}:
  match s:
    case Chain{+key, +acts}:
      +n = S.Phase.nh(S.Ue.phase(u))
      P.Bool.or_l(PL.Lv.chains(n, n), Bool.and(Bool.not(Tb.Table.present(S.Nh, n)), PL.Lv.firsts(n, S.Phase.mode_k_amf(S.Ue.phase(u)), key, acts)), PL.Lv.chains_self(n))
    case Kept{}:
      PF.Fs.holds_self(S.Phase.nas(S.Ue.phase(u)))

def Nc.base_row(+k: U32, +k0: U32, +u0: S.Ue, +more: Tb.Table(S.Ue), +s: Rk, +b: Bool, +eb: {U32.is_eq(k0, k) == b : Bool}, +hc: {S.Ues.clear(k0, u0, more) == True{} : Bool}, ih: {Hs.rows(k, Hs.from(s, Tb.Table.get(S.Ue, k, more)), more) == True{} : Bool}) -> {Hs.rows(k, Hs.from(s, Tb.Table.hit(S.Ue, u0, Tb.Table.get(S.Ue, k, more), b)), (k0, u0) <> more) == True{} : Bool}:
  match b:
    case True{}:
      +r = Hs.from(s, Some{u0})
      +h = Hs.holds(r, S.Ue.phase(u0))
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(k0, k)), h), Hs.rows(k, r, more), P.Bool.or_r(Bool.not(U32.is_eq(k0, k)), h, Hs.self(s, u0)), Nc.vacant(k, k0, u0, r, more, hc, P.U32.eq_of_is_eq(k0, k, eb)))
    case False{}:
      Hs.other(k, Hs.from(s, Tb.Table.get(S.Ue, k, more)), k0, u0, more, eb, ih)

# Where no two contexts share a key, every row under k is the context k names.
def Nc.base(+k: U32, +t: Tb.Table(S.Ue), +s: Rk, +eu: {S.Ues.unique(t) == True{} : Bool}) -> {Hs.rows(k, Hs.from(s, Tb.Table.get(S.Ue, k, t)), t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case (+k0, +u0) <> +more:
      Nc.base_row(k, k0, u0, more, s, U32.is_eq(k0, k), {==}, P.Bool.and_true_l(S.Ues.clear(k0, u0, more), S.Ues.unique(more), eu), Nc.base(k, more, s, P.Bool.and_true_r(S.Ues.clear(k0, u0, more), S.Ues.unique(more), eu)))

# A write under key, where no two contexts share a key: it chains to what key
# held, or, put over a context that held none, takes the first pair the
# actions send.
def Nc.unique_or(+st: S.State, +x: Bool, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +h: {Bool.or(x, Bool.not(S.Ues.unique(S.State.ues(st)))) == True{} : Bool}) -> {x == True{} : Bool}:
  se = Equal.sym(Bool, S.Ues.unique(S.State.ues(st)), True{}, eu)
  P.Bool.or_true_l(x, Bool.not(S.Ues.unique(S.State.ues(st))), (%se : {Bool.not(_) == False{} : Bool}; {==}), h)

def Nc.held(+st: S.State, +key: U32, +n: Maybe<&2, S.Nh>, +acts: List<&2, N.Act>, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +h: {PL.Lv.chain(st, key, n) == True{} : Bool}) -> {Bool.or(PL.Lv.chains(n, S.Ue.nh(Tb.Table.get(S.Ue, key, S.State.ues(st)))), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(Tb.Table.get(S.Ue, key, S.State.ues(st))))), PL.Lv.firsts(n, S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st))), key, acts))) == True{} : Bool}:
  +m = Tb.Table.get(S.Ue, key, S.State.ues(st))
  P.Bool.or_l(PL.Lv.chains(n, S.Ue.nh(m)), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(m))), PL.Lv.firsts(n, S.Ue.mode_k_amf(m), key, acts)), Nc.unique_or(st, PL.Lv.chains(n, S.Ue.nh(m)), eu, h))

def Nc.put_if(+st: S.State, +key: U32, +n: Maybe<&2, S.Nh>, +acts: List<&2, N.Act>, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +u: Bool, +eu2: {PL.Lv.unpaired(st, key) == u : Bool}, +hc: {Bool.or(PL.Lv.chain(st, key, n), u) == True{} : Bool}, +hs: {Bool.or(PL.Lv.firsts(n, S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st))), key, acts), Bool.not(u)) == True{} : Bool}) -> {Bool.or(PL.Lv.chains(n, S.Ue.nh(Tb.Table.get(S.Ue, key, S.State.ues(st)))), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(Tb.Table.get(S.Ue, key, S.State.ues(st))))), PL.Lv.firsts(n, S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st))), key, acts))) == True{} : Bool}:
  match u:
    case True{}:
      +m = Tb.Table.get(S.Ue, key, S.State.ues(st))
      +f = PL.Lv.firsts(n, S.Ue.mode_k_amf(m), key, acts)
      P.Bool.or_r(PL.Lv.chains(n, S.Ue.nh(m)), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(m))), f), P.Bool.and_intro(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(m))), f, eu2, P.Bool.or_true_l(f, False{}, {==}, hs)))
    case False{}:
      Nc.held(st, key, n, acts, eu, P.Bool.or_true_l(PL.Lv.chain(st, key, n), False{}, {==}, hc))

# Under k, or under another key.
def Nc.at(+st: S.State, +k: U32, +key: U32, +n: Maybe<&2, S.Nh>, +acts: List<&2, N.Act>, +x: Bool, +ex: {U32.is_eq(key, k) == x : Bool}, +h: {Bool.or(PL.Lv.chains(n, S.Ue.nh(Tb.Table.get(S.Ue, key, S.State.ues(st)))), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(Tb.Table.get(S.Ue, key, S.State.ues(st))))), PL.Lv.firsts(n, S.Ue.mode_k_amf(Tb.Table.get(S.Ue, key, S.State.ues(st))), key, acts))) == True{} : Bool}) -> {Bool.or(Bool.not(x), Bool.or(PL.Lv.chains(n, S.Ue.nh(Tb.Table.get(S.Ue, k, S.State.ues(st)))), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(Tb.Table.get(S.Ue, k, S.State.ues(st))))), PL.Lv.firsts(n, S.Ue.mode_k_amf(Tb.Table.get(S.Ue, k, S.State.ues(st))), k, acts)))) == True{} : Bool}:
  match x:
    case True{}:
      ek = P.U32.eq_of_is_eq(key, k, ex)
      (%ek : {Bool.or(PL.Lv.chains(n, S.Ue.nh(Tb.Table.get(S.Ue, _, S.State.ues(st)))), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(Tb.Table.get(S.Ue, _, S.State.ues(st))))), PL.Lv.firsts(n, S.Ue.mode_k_amf(Tb.Table.get(S.Ue, _, S.State.ues(st))), _, acts))) == True{} : Bool}; h)
    case False{}:
      {==}

def Nc.rephase(+st: S.State, +k: U32, +acts: List<&2, N.Act>, +key: U32, +p: S.Phase, +ues: Tb.Table(S.Ue), +x: Bool, +ex: {U32.is_eq(key, k) == x : Bool}, +h: {Bool.or(Bool.not(x), Hs.holds(From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, p)) == True{} : Bool}, +e: {Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, ues) == True{} : Bool}) -> {Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, S.Ues.rephase(key, p, ues)) == True{} : Bool}:
  match x:
    case True{}:
      Hs.rephase_holds(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, key, p, ues, h, e)
    case False{}:
      Hs.rephase_other(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, key, p, ues, ex, e)

# Every transaction a procedure writes keeps the rows under k chained.
def Nc.tx(+st: S.State, +k: U32, +acts: List<&2, N.Act>, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +tx: S.Tx, +ues: Tb.Table(S.Ue), +h: {PL.Lv.homed(st, tx, ues) == True{} : Bool}, +hw: {PL.Lv.seeds(st, tx, acts) == True{} : Bool}, +e: {Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, ues) == True{} : Bool}) -> {Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, PT.Tk.ues(tx, ues)) == True{} : Bool}:
  match tx:
    case S.Rephase{+key, +p}:
      +c = PL.Lv.chain(st, key, S.Phase.nh(p))
      +hc = P.Bool.and_true_l(c, Bool.and(S.Phase.guarded(p), S.Ue.fits(p, Tb.Table.get(S.Ue, key, ues))), h)
      Nc.rephase(st, k, acts, key, p, ues, U32.is_eq(key, k), {==}, Nc.at(st, k, key, S.Phase.nh(p), acts, U32.is_eq(key, k), {==}, Nc.held(st, key, S.Phase.nh(p), acts, eu, hc)), e)
    case S.Put{+key, +u}:
      +n = S.Phase.nh(S.Ue.phase(u))
      +c = PL.Lv.chain_put(st, key, n)
      +hc = P.Bool.and_true_l(c, Bool.and(PL.Lv.keyed(st, key), Bool.and(S.Phase.guarded(S.Ue.phase(u)), Bool.and(S.Ue.single(u), PL.Lv.home(st, u)))), h)
      P.Bool.and_intro(Bool.or(Bool.not(U32.is_eq(key, k)), Hs.holds(From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, S.Ue.phase(u))), Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, S.Ues.sift(S.Clear{key, u}, ues)), Nc.at(st, k, key, n, acts, U32.is_eq(key, k), {==}, Nc.put_if(st, key, n, acts, eu, PL.Lv.unpaired(st, key), {==}, hc, hw)), Hs.sift(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, S.Clear{key, u}, ues, e))
    case S.Del{+key}:
      Hs.sift(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, S.Except{key}, ues, e)
    case S.Both{+a, +b}:
      Nc.tx(st, k, acts, eu, b, PT.Tk.ues(a, ues), P.Bool.and_true_r(PL.Lv.homed(st, a, ues), PL.Lv.homed(st, b, PT.Tk.ues(a, ues)), h), P.Bool.and_true_r(PL.Lv.seeds(st, a, acts), PL.Lv.seeds(st, b, acts), hw), Nc.tx(st, k, acts, eu, a, ues, P.Bool.and_true_l(PL.Lv.homed(st, a, ues), PL.Lv.homed(st, b, PT.Tk.ues(a, ues)), h), P.Bool.and_true_l(PL.Lv.seeds(st, a, acts), PL.Lv.seeds(st, b, acts), hw), e))
    case S.Keep{}:
      e
    case S.PutSession{key, s}:
      e
    case S.Revar{key, v}:
      e
    case S.DelSession{key}:
      e
    case S.Subs{subs}:
      e
    case S.SetLink{link}:
      e
    case S.BumpUe{bk}:
      e
    case S.BumpSeq{n}:
      e

def Nc.Q(+st: S.State, +k: U32, o: N.Step()) -> Type:
  {Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, K.Kernel.actions(o)}, S.State.ues(K.Kernel.state(o))) == True{} : Bool}

# An outcome rendered, judged against acts its own actions are part of.
def Nc.out_with(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +o: N.GOut(), +h: {PL.Lv.ok(st, o) == True{} : Bool}, +acts: List<&2, N.Act>, +hw: {PL.Lv.seeds(st, N.Out.tx(o), acts) == True{} : Bool}) -> {Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, S.State.ues(K.Kernel.state(N.Step.of(st, o)))) == True{} : Bool}:
  sr = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, o))), PT.Tk.ues(N.Out.tx(o), S.State.ues(st)), PT.Tk.render(st, o))
  (%sr : {Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, _) == True{} : Bool}; Nc.tx(st, k, acts, eu, N.Out.tx(o), S.State.ues(st), PL.Lv.ok_homed(st, o, h), hw, Nc.base(k, S.State.ues(st), Chain{k, acts}, eu)))

def Nc.out(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +o: N.GOut(), +h: {PL.Lv.ok(st, o) == True{} : Bool}) -> Nc.Q(st, k, N.Step.of(st, o)):
  match o:
    case (+tx, +acts):
      +g = N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)))
      Nc.out_with(st, k, eu, (tx, acts), h, List.append(&2, N.Act, acts, g), PL.Lv.seeds_l(st, tx, acts, g, PL.Lv.ok_seeds(st, (tx, acts), h)))

# The session side writes no phase.
def Nc.sx(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +o: N.GOut(), +hx: {PW.Sx.only(N.Out.tx(o)) == True{} : Bool}) -> Nc.Q(st, k, N.Step.of(st, o)):
  +acts = K.Kernel.actions(N.Step.of(st, o))
  sr = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, o))), PT.Tk.ues(N.Out.tx(o), S.State.ues(st)), PT.Tk.render(st, o))
  sx = Equal.sym(Tb.Table(S.Ue), PT.Tk.ues(N.Out.tx(o), S.State.ues(st)), S.State.ues(st), PT.Tk.ues_sx(N.Out.tx(o), S.State.ues(st), hx))
  (%sr : {Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, _) == True{} : Bool}; (%sx : {Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, _) == True{} : Bool}; Nc.base(k, S.State.ues(st), Chain{k, acts}, eu)))

def Nc.resend_sx(+k1: U32, +t: S.Session, +p: S.SPhase, +request: B.Bytes(), +more: Bool) -> {PW.Sx.only(N.Out.tx(Gsm.Gsm.resend_if(k1, t, p, request, (S.DelSession{k1}, [N.Note{F.Warn{}, "PFCP: no Session Deletion Response; deletion given up"}]), more))) == True{} : Bool}:
  match more:
    case True{}:
      {==}
    case False{}:
      {==}

def Nc.dphase_sx(+skey: U32, +msg: Pf.Msg, +p: S.SPhase) -> {PW.Sx.only(N.Out.tx(Gsm.Gsm.deleted_phase(skey, msg, p))) == True{} : Bool}:
  match p:
    case S.Deleting{guard, request}:
      {==}
    case S.Creating{guard, pti, accept, request}:
      {==}
    case S.Setting{guard, pti}:
      {==}
    case S.Modifying{guard, request}:
      {==}
    case S.Repointing{guard, request}:
      {==}
    case S.Active{}:
      {==}

def Nc.deleted_sx(+msg: Pf.Msg, +m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> {PW.Sx.only(N.Out.tx(Gsm.Gsm.deleted(msg, m))) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+skey, +s)}:
      Nc.dphase_sx(skey, msg, S.Session.phase(s))

def Nc.down_seeds(+st: S.State, +o: N.GOut(), +more: List<&2, N.Act>, +h: {PL.Lv.ok(st, o) == True{} : Bool}) -> {PL.Lv.seeds(st, N.Out.tx(o), List.append(&2, N.Act, K.Kernel.actions(N.Step.of(st, o)), more)) == True{} : Bool}:
  match o:
    case (+tx, +acts):
      +g = N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)))
      PL.Lv.seeds_l(st, tx, List.append(&2, N.Act, acts, g), more, PL.Lv.seeds_l(st, tx, acts, g, PL.Lv.ok_seeds(st, (tx, acts), h)))

# A session the UPF settles: its guard's stop is one more action.
def Nc.settled(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +k1: U32, +tx: S.Tx, +more: List<&2, N.Act>, +h: {PL.Lv.ok(st, (tx, more)) == True{} : Bool}) -> Nc.Q(st, k, N.Step.of(st, (tx, N.TimerCancel{k1} <> more))):
  +g = N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(S.Tx.apply(tx, st)))
  Nc.out_with(st, k, eu, (tx, more), h, N.TimerCancel{k1} <> List.append(&2, N.Act, more, g), PL.Lv.seeds_r(st, tx, [N.TimerCancel{k1}], List.append(&2, N.Act, more, g), PL.Lv.seeds_l(st, tx, more, g, PL.Lv.ok_seeds(st, (tx, more), h))))

# An association's contexts re-initialised, judged against acts its
# handovers' ending seeds: they end, then the association's contexts go.
def Nc.reset(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +assoc: U32, +acts: List<&2, N.Act>, +hw: {PL.Lv.seeds(st, N.Out.tx(Ho.Ho.down(st, assoc)), acts) == True{} : Bool}) -> {Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, S.State.ues(K.Kernel.state(R.Route.reset(st, assoc)))) == True{} : Bool}:
  +o = Ho.Ho.down(st, assoc)
  Hs.drop_rows(K.Kernel.state(N.Step.of(st, o)), assoc, k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, acts}, Nc.out_with(st, k, eu, o, PL.Lw.ho_down(st, assoc), acts, hw))

def Nc.down(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +assoc: U32) -> Nc.Q(st, k, R.Route.down(st, assoc)):
  +o = Ho.Ho.down(st, assoc)
  +b = K.Kernel.actions(R.Route.drop(K.Kernel.state(N.Step.of(st, o)), assoc))
  +xs = List.append(&2, N.Act, K.Kernel.actions(N.Step.of(st, o)), b)
  Nc.reset(st, k, eu, assoc, N.Note{F.Info{}, "NGAP: association down; its UE contexts and sessions released"} <> xs, PL.Lv.seeds_r(st, N.Out.tx(o), [N.Note{F.Info{}, "NGAP: association down; its UE contexts and sessions released"}], xs, Nc.down_seeds(st, o, b, PL.Lw.ho_down(st, assoc))))

def Nc.ready(+st: S.State, +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}, +assoc: U32, +id: B.Bytes(), +ok: Bool, +acts: List<&2, N.Act>) -> Nc.Q(st, k, (S.State.ready(N.Step.state(R.Route.reset(st, assoc)), assoc, id, ok), List.append(&2, N.Act, N.Step.acts(R.Route.reset(st, assoc)), acts))):
  +o = Ho.Ho.down(st, assoc)
  +x = K.Kernel.state(R.Route.reset(st, assoc))
  +xs = List.append(&2, N.Act, K.Kernel.actions(R.Route.reset(st, assoc)), acts)
  +hw = PL.Lv.seeds_l(st, N.Out.tx(o), K.Kernel.actions(R.Route.reset(st, assoc)), acts, Nc.down_seeds(st, o, K.Kernel.actions(R.Route.drop(K.Kernel.state(N.Step.of(st, o)), assoc)), PL.Lw.ho_down(st, assoc)))
  PW.Walk.assocs(ues => ss => Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, xs}, ues), x, S.Assocs.set(assoc, id, S.State.assocs(x), ok), [], Nc.reset(st, k, eu, assoc, xs, hw))

def Nc.step(+st: S.State, +ev: F.Evt, +entropy: B.Bytes(), +k: U32, +eu: {S.Ues.unique(S.State.ues(st)) == True{} : Bool}) -> Nc.Q(st, k, K.Kernel.step(st, ev, entropy)):
  PL.Dw.walk(o => Nc.Q(st, k, o), o => Nc.Q(st, k, N.Step.of(st, o)), st, ev, entropy, +acts => sp => tc => nr => Nc.base(k, S.State.ues(st), Chain{k, acts}, eu), +assoc => ns => +id => +ok => +acts => sp => tc => nr => Nc.ready(st, k, eu, assoc, id, ok, acts), +tlvs => PW.Walk.config(ues => ss => Hs.rows(k, From{Tb.Table.get(S.Ue, k, S.State.ues(st)), k, K.Kernel.actions(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy))}, ues), S.Cfg.complete(tlvs), st, tlvs, entropy, Nc.base(k, S.State.ues(st), Chain{k, K.Kernel.actions(K.Kernel.config(S.Cfg.complete(tlvs), st, tlvs, entropy))}, eu)), +assoc => Nc.down(st, k, eu, assoc), o => h => h, +o => +h => Nc.out(st, k, eu, o, h), +k1 => +t => +g => +r => ek => eu2 => em => ep => Nc.sx(st, k, eu, Gsm.Gsm.expired(st, k1, t, S.Deleting{g, r}), Nc.resend_sx(k1, t, S.Deleting{S.Guard{U32.add(S.Guard.retries(g), 1)}, r}, r, U32.is_lt(S.Guard.retries(g), Up.N4.n1()))), +len => +bytes => +msg => +rest => ev2 => er => ek => Nc.sx(st, k, eu, Gsm.Gsm.deleted(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st))), Nc.deleted_sx(msg, S.Sessions.by_seq(Pf.Msg.seq(msg), S.State.sessions(st)))), +k1 => +tx => +more => ekd => eh => h => Nc.settled(st, k, eu, k1, tx, more, h))

# The row the key names after the step holds what its rows hold.
def Nc.found_row(+k: U32, +r: Rw, +u0: S.Ue, +more: Tb.Table(S.Ue), +b: Bool, +e: {Bool.and(Bool.or(Bool.not(b), Hs.holds(r, S.Ue.phase(u0))), Hs.rows(k, r, more)) == True{} : Bool}, +v: S.Ue, +eg: {Tb.Table.hit(S.Ue, u0, Tb.Table.get(S.Ue, k, more), b) == Some{v} : Maybe<&2, S.Ue>}, ih: {Hs.rows(k, r, more) == True{} : Bool} -> {Tb.Table.get(S.Ue, k, more) == Some{v} : Maybe<&2, S.Ue>} -> {Hs.holds(r, S.Ue.phase(v)) == True{} : Bool}) -> {Hs.holds(r, S.Ue.phase(v)) == True{} : Bool}:
  match b:
    case True{}:
      eu = P.Some.inj(S.Ue, u0, v, eg)
      (%eu : {Hs.holds(r, S.Ue.phase(_)) == True{} : Bool}; P.Bool.and_true_l(Hs.holds(r, S.Ue.phase(u0)), Hs.rows(k, r, more), e))
    case False{}:
      ih(P.Bool.and_true_r(True{}, Hs.rows(k, r, more), e), eg)

def Nc.found(+k: U32, +r: Rw, +ues: Tb.Table(S.Ue), +e: {Hs.rows(k, r, ues) == True{} : Bool}, +v: S.Ue, +eg: {Tb.Table.get(S.Ue, k, ues) == Some{v} : Maybe<&2, S.Ue>}) -> {Hs.holds(r, S.Ue.phase(v)) == True{} : Bool}:
  match ues:
    case Nil{}:
      Empty.absurd({Hs.holds(r, S.Ue.phase(v)) == True{} : Bool}, P.Refute.none_some(S.Ue, v, eg))
    case (+k0, +u0) <> +more:
      Nc.found_row(k, r, u0, more, U32.is_eq(k0, k), e, v, eg, e2 => g2 => Nc.found(k, r, more, e2, v, g2))

# What the law reads off the chain.
def Nc.pair(+k: U32, +b: Maybe<&2, S.Ue>, +acts: List<&2, N.Act>, +ues: Tb.Table(S.Ue), +e: {Hs.rows(k, From{b, k, acts}, ues) == True{} : Bool}, +n: S.Nh, +mm: Maybe<&2, S.Ue>, +emm: {Tb.Table.get(S.Ue, k, ues) == mm : Maybe<&2, S.Ue>}, +en: {S.Ue.nh(mm) == Some{n} : Maybe<&2, S.Nh>}) -> {Bool.or(PL.Lv.chains(Some{n}, S.Ue.nh(b)), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(b))), PL.Lv.firsts(Some{n}, S.Ue.mode_k_amf(b), k, acts))) == True{} : Bool}:
  match mm:
    case None{}:
      Empty.absurd({Bool.or(PL.Lv.chains(Some{n}, S.Ue.nh(b)), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(b))), PL.Lv.firsts(Some{n}, S.Ue.mode_k_amf(b), k, acts))) == True{} : Bool}, P.Refute.none_some(S.Nh, n, en))
    case Some{+v}:
      (%en : {Bool.or(PL.Lv.chains(_, S.Ue.nh(b)), Bool.and(Bool.not(Tb.Table.present(S.Nh, S.Ue.nh(b))), PL.Lv.firsts(_, S.Ue.mode_k_amf(b), k, acts))) == True{} : Bool}; Nc.found(k, From{b, k, acts}, ues, e, v, emm))

def Nc.nh_eq(+x: S.Nh, +y: S.Nh, +e: {S.Nh.same(x, y) == True{} : Bool}) -> {x == y : S.Nh}:
  match x y:
    case S.Nh{+a, +h, +c} S.Nh{+a2, +h2, +c2}:
      +r = Bool.and(B.bytes_eq(h, h2), U32.is_eq(c, c2))
      +er = P.Bool.and_true_r(B.bytes_eq(a, a2), r, e)
      ea = P.Bytes.eq_of_bytes_eq(a, a2, P.Bool.and_true_l(B.bytes_eq(a, a2), r, e))
      eh = P.Bytes.eq_of_bytes_eq(h, h2, P.Bool.and_true_l(B.bytes_eq(h, h2), U32.is_eq(c, c2), er))
      ec = P.U32.eq_of_is_eq(c, c2, P.Bool.and_true_r(B.bytes_eq(h, h2), U32.is_eq(c, c2), er))
      (%ea : {S.Nh{a, h, c} == S.Nh{_, h2, c2} : S.Nh}; (%eh : {S.Nh{a, h, c} == S.Nh{a, _, c2} : S.Nh}; (%ec : {S.Nh{a, h, c} == S.Nh{a, h, _} : S.Nh}; {==})))

def Nc.next_or(+n: S.Nh, +m: S.Nh, +x: Bool, +ex: {S.Nh.same(n, m) == x : Bool}, +h: {Bool.or(x, S.Nh.same(n, S.Nh.next(m))) == True{} : Bool}) -> {n == m : S.Nh} | {n == S.Nh.next(m) : S.Nh}:
  match x:
    case True{}:
      Inl{Nc.nh_eq(n, m, ex)}
    case False{}:
      Inr{Nc.nh_eq(n, S.Nh.next(m), h)}

# A pair the actions start a chain at has the K_AMF the chain is from.
def Nc.act_amf(+ka: B.Bytes(), +k: U32, +k_amf: B.Bytes(), +nh: B.Bytes(), +ncc: U32, +a: N.Act, +e: {N.Act.seeds(ka, k, S.Nh{k_amf, nh, ncc}, a) == True{} : Bool}) -> {ka == k_amf : B.Bytes()}:
  match a:
    case N.Ics{assoc, stream, +key, ran_id, cfg, caps, +k_gnb, nas}:
      +rest = S.Nh.same(S.Nh{k_amf, nh, ncc}, S.Nh.initial(ka, k_gnb))
      +es = P.Bool.and_true_r(U32.is_eq(key, k), rest, e)
      Equal.sym(B.Bytes(), k_amf, ka, P.Bytes.eq_of_bytes_eq(k_amf, ka, P.Bool.and_true_l(B.bytes_eq(k_amf, ka), Bool.and(B.bytes_eq(nh, Kd.kdf.nh(ka, k_gnb)), U32.is_eq(ncc, 1)), es)))
    case N.DlNas{assoc, stream, key, ran_id, nas}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.PduSetup{assoc, stream, key, ran_id, psi, sst, nas, transfer}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.Release{assoc, stream, key, ran_id, cause}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.SwitchAck{assoc, stream, key, ran_id, caps, nh2, switched, released, sst}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.SwitchFail{assoc, stream, ue, amf, ran_id, psis, cause}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.UeSend{assoc, stream, key, bytes}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.PduRelease{assoc, stream, key, ran_id, psi, nas}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.ErrInd{assoc, cause}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.Setup{assoc, answer}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.Pfcp{ue, bytes}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.Note{level, text}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.TimerStart{ue, timer, ms}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))
    case N.TimerCancel{timer}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(e))

def Nc.seeds_or(+ka: B.Bytes(), +k: U32, +k_amf: B.Bytes(), +nh: B.Bytes(), +ncc: U32, +a: N.Act, +more: List<&2, N.Act>, +x: Bool, +ex: {N.Act.seeds(ka, k, S.Nh{k_amf, nh, ncc}, a) == x : Bool}, +h: {Bool.or(x, N.Acts.seeds(ka, k, S.Nh{k_amf, nh, ncc}, more)) == True{} : Bool}, ih: {N.Acts.seeds(ka, k, S.Nh{k_amf, nh, ncc}, more) == True{} : Bool} -> {ka == k_amf : B.Bytes()}) -> {ka == k_amf : B.Bytes()}:
  match x:
    case True{}:
      Nc.act_amf(ka, k, k_amf, nh, ncc, a, ex)
    case False{}:
      ih(h)

def Nc.seeds_amf(+ka: B.Bytes(), +k: U32, +k_amf: B.Bytes(), +nh: B.Bytes(), +ncc: U32, +acts: List<&2, N.Act>, +h: {N.Acts.seeds(ka, k, S.Nh{k_amf, nh, ncc}, acts) == True{} : Bool}) -> {ka == k_amf : B.Bytes()}:
  match acts:
    case Nil{}:
      Empty.absurd({ka == k_amf : B.Bytes()}, P.Refute.bool(h))
    case +a <> +more:
      Nc.seeds_or(ka, k, k_amf, nh, ncc, a, more, N.Act.seeds(ka, k, S.Nh{k_amf, nh, ncc}, a), {==}, h, e => Nc.seeds_amf(ka, k, k_amf, nh, ncc, more, e))

def Nc.begun(+kb: Maybe<&2, B.Bytes()>, +k: U32, +k_amf: B.Bytes(), +nh: B.Bytes(), +ncc: U32, +acts: List<&2, N.Act>, +h: {PL.Lv.from_mode(kb, k, S.Nh{k_amf, nh, ncc}, acts) == True{} : Bool}) -> {kb == Some{k_amf} : Maybe<&2, B.Bytes()>} & {N.Acts.seeds(k_amf, k, S.Nh{k_amf, nh, ncc}, acts) == True{} : Bool}:
  match kb:
    case None{}:
      Empty.absurd({None{} == Some{k_amf} : Maybe<&2, B.Bytes()>} & {N.Acts.seeds(k_amf, k, S.Nh{k_amf, nh, ncc}, acts) == True{} : Bool}, P.Refute.bool(h))
    case Some{+ka}:
      ea = Nc.seeds_amf(ka, k, k_amf, nh, ncc, acts, h)
      (%ea : {Some{ka} == Some{_} : Maybe<&2, B.Bytes()>} & {N.Acts.seeds(_, k, S.Nh{k_amf, nh, ncc}, acts) == True{} : Bool}; ({==}, h))

def L.amf.ncc.step(st, ev, entropy, k, m, k_amf, nh, ncc, eu, en):
  +b = Tb.Table.get(S.Ue, k, S.State.ues(st))
  +after = S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy)))
  +acts = K.Kernel.actions(K.Kernel.step(st, ev, entropy))
  +n : S.Nh = S.Nh{k_amf, nh, ncc}
  +kb = S.Ue.mode_k_amf(b)
  +hc = Nc.pair(k, b, acts, after, Nc.step(st, ev, entropy, k, eu), n, Tb.Table.get(S.Ue, k, after), {==}, en)
  (em => Nc.next_or(n, m, S.Nh.same(n, m), {==}, P.Bool.or_true_l(PL.Lv.chains(Some{n}, Some{m}), Bool.and(False{}, PL.Lv.firsts(Some{n}, kb, k, acts)), {==}, (%em : {Bool.or(PL.Lv.chains(Some{n}, _), Bool.and(Bool.not(Tb.Table.present(S.Nh, _)), PL.Lv.firsts(Some{n}, kb, k, acts))) == True{} : Bool}; hc))), em => Nc.begun(kb, k, k_amf, nh, ncc, acts, (%em : {Bool.or(PL.Lv.chains(Some{n}, _), Bool.and(Bool.not(Tb.Table.present(S.Nh, _)), PL.Lv.firsts(Some{n}, kb, k, acts))) == True{} : Bool}; hc)))

def L.amf.handover.guarded(st, ev, entropy, assoc, stream, len, bytes, crit, value, k, t, p):
  (Hp.timed(S.State.ues(S.State.initial())), (e0 => Hp.timed_step(st, ev, entropy, e0), (e => Hp.g_guard(p, t, e), (ep => Hp.g_required(st, entropy, assoc, stream, len, bytes, crit, value, k, ep), (ep => Hp.g_ack(st, entropy, assoc, stream, len, bytes, crit, value, k, ep), (e => Hp.fired_ends(st, k, t, Tb.Table.get(S.Ue, k, S.State.ues(st)), {==}, e), es => ex => Hs.none(k, S.State.ues(K.Kernel.state(K.Kernel.step(st, ev, entropy))), Hs.ends(st, ev, entropy, k, es)(ex))))))))

# amf.handover.released_side_completes
# ------------------------------------

def L.amf.handover.released_side_completes(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, k, ran, uli, rel, diag, ue, ep, ei, ev, eid, eu, ea, er, eup):
  +done : N.Step() = (st, [N.Note{F.Info{}, "NGAP: UE Context Release Complete from the side a handover released"}])
  seu = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{ue}, eu)
  sea = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, ea)
  ser = Equal.sym(Bool, S.Phase.released(S.Ue.phase(ue), assoc, ran), True{}, er)
  PW.Rt.ue(V.UEContextReleaseComplete.View, x => {x == done : N.Step()}, st, entropy, assoc, stream, len, bytes, 1, 41, crit, value, ies, c, i => V.UEContextReleaseComplete.view(i), r => Gmm.Gmm.release_complete_of_view(st, assoc, r), m => Gmm.Gmm.release_complete_key(st, assoc, ran, m), V.UEContextReleaseComplete.View{amf, ran, uli, rel, diag}, amf, Some{k}, ep, ei, {==}, eup, {==}, ev, {==}, eid, (%seu : {N.Step.of(st, Gmm.Gmm.release_complete_ue(st, assoc, k, N.Owner.of(_, assoc, ran), S.Ue.released(_, assoc, ran))) == done : N.Step()}; (%sea : {N.Step.of(st, Gmm.Gmm.release_complete_ue(st, assoc, k, N.Owner.check(ue, Bool.and(_, B.bytes_eq(S.Ue.ran_id(ue), ran))), S.Phase.released(S.Ue.phase(ue), assoc, ran))) == done : N.Step()}; (%ser : {N.Step.of(st, Gmm.Gmm.release_complete_ue(st, assoc, k, None{}, _)) == done : N.Step()}; {==}))))

# Handover Notify completing
# --------------------------
# A Handover Notify that completes its handover is that handover's outcome,
# which puts the UE on the target with the NAS context the release commands
# to it leave.

def Hn.aimed(+ue: S.Ue, +assoc: U32, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +source: U32, +ran: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +sp: B.Digits(), +eph: {S.Ue.phase(ue) == S.Handover{ctx, nh, source, S.Acked{assoc, ran, s, ts}} : S.Phase}, +es: {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>}, +eo: {U32.is_eq(S.Ue.assoc(ue), assoc) == False{} : Bool}) -> {Ho.Ho.aimed(ue, assoc) == True{} : Bool}:
  seph = Equal.sym(S.Phase, S.Ue.phase(ue), S.Handover{ctx, nh, source, S.Acked{assoc, ran, s, ts}}, eph)
  %seph : {Bool.and(S.Maybe.same_u32(S.Phase.pending(_), Some{assoc}), Bool.and(Tb.Table.present(B.Digits(), S.Ue.supi(ue)), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc)))) == True{} : Bool}
  ses = Equal.sym(Maybe<&2, B.Digits()>, S.Ue.supi(ue), Some{sp}, es)
  %ses : {Bool.and(U32.is_eq(assoc, assoc), Bool.and(Tb.Table.present(B.Digits(), _), Bool.not(U32.is_eq(S.Ue.assoc(ue), assoc)))) == True{} : Bool}
  seo = Equal.sym(Bool, U32.is_eq(S.Ue.assoc(ue), assoc), False{}, eo)
  %seo : {Bool.and(U32.is_eq(assoc, assoc), Bool.not(_)) == True{} : Bool}
  ser = Equal.sym(Bool, U32.is_eq(assoc, assoc), True{}, P.U32.is_eq_refl(assoc))
  %ser : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def Hn.found(+st: S.State, +assoc: U32, +amf: B.Bytes(), +ran: B.Bytes(), +uli: G.UserLocationInformation, +k: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +source: U32, +s: U32, +ts: List<&2, S.Tunnel>, +sp: B.Digits(), +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +eg: {Tb.Table.get(S.Ue, k, S.State.ues(st)) == Some{ue} : Maybe<&2, S.Ue>}, +eph: {S.Ue.phase(ue) == S.Handover{ctx, nh, source, S.Acked{assoc, ran, s, ts}} : S.Phase}, +es: {S.Ue.supi(ue) == Some{sp} : Maybe<&2, B.Digits()>}, +eo: {U32.is_eq(S.Ue.assoc(ue), assoc) == False{} : Bool}, +ef: {S.Ues.ran_free(k, assoc, ran, S.State.ues(st)) == True{} : Bool}) -> {N.Step.of(st, Ho.Ho.notify_of_view(st, assoc, Done{V.HandoverNotify.View{amf, ran, uli}})) == N.Step.of(st, Ho.Ho.complete(st, assoc, k, ue, ctx, nh, ran, s, ts, True{})) : N.Step()}:
  +T : N.Step() = N.Step.of(st, Ho.Ho.complete(st, assoc, k, ue, ctx, nh, ran, s, ts, True{}))
  +none : N.GOut() = (S.Keep{}, N.Ngap.unknown_ue(assoc))
  seid = Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{k}, eid)
  %seid : {N.Step.of(st, N.Ue.found(N.Ue.keyed(_, k2 => Ho.Ho.pending(Tb.Table.get(S.Ue, k2, S.State.ues(st)), assoc)), none, +key => +u => Ho.Ho.notify_phase(st, assoc, key, u, ran, S.Ue.phase(u)))) == T : N.Step()}
  seg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, k, S.State.ues(st)), Some{ue}, eg)
  %seg : {N.Step.of(st, N.Ue.found(N.Ue.with_key(k, Ho.Ho.pending(_, assoc)), none, +key => +u => Ho.Ho.notify_phase(st, assoc, key, u, ran, S.Ue.phase(u)))) == T : N.Step()}
  sea = Equal.sym(Bool, Ho.Ho.aimed(ue, assoc), True{}, Hn.aimed(ue, assoc, ctx, nh, source, ran, s, ts, sp, eph, es, eo))
  %sea : {N.Step.of(st, N.Ue.found(N.Ue.with_key(k, N.Owner.check(ue, _)), none, +key => +u => Ho.Ho.notify_phase(st, assoc, key, u, ran, S.Ue.phase(u)))) == T : N.Step()}
  seph = Equal.sym(S.Phase, S.Ue.phase(ue), S.Handover{ctx, nh, source, S.Acked{assoc, ran, s, ts}}, eph)
  %seph : {N.Step.of(st, Ho.Ho.notify_phase(st, assoc, k, ue, ran, _)) == T : N.Step()}
  sb = Equal.sym(Bool, B.bytes_eq(ran, ran), True{}, P.Bytes.eq_refl(ran))
  %sb : {N.Step.of(st, Ho.Ho.complete(st, assoc, k, ue, ctx, nh, ran, s, ts, Bool.and(_, S.Ues.ran_free(k, assoc, ran, S.State.ues(st))))) == T : N.Step()}
  sef = Equal.sym(Bool, S.Ues.ran_free(k, assoc, ran, S.State.ues(st)), True{}, ef)
  %sef : {N.Step.of(st, Ho.Ho.complete(st, assoc, k, ue, ctx, nh, ran, s, ts, Bool.and(True{}, _))) == T : N.Step()}
  {==}

def Hn.of(+st: S.State, +assoc: U32, +k: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +r: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>) -> {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, Ho.Ho.complete(st, assoc, k, ue, ctx, nh, r, s, ts, True{}))))) == Some{S.Ue.moved(ue, assoc, r, s, S.Registered{Gsm.Gsm.Told.ctx(Gsm.Gsm.releases(k, assoc, s, r, Sw.Sw.released(ts, S.Sessions.of_ue(k, S.State.sessions(st))), ctx)), nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}})} : Maybe<&2, S.Ue>}:
  +ues = S.State.ues(st)
  +rows = S.Sessions.of_ue(k, S.State.sessions(st))
  +told = Gsm.Gsm.releases(k, assoc, s, r, Sw.Sw.released(ts, rows), ctx)
  +v = S.Ue.moved(ue, assoc, r, s, S.Registered{Gsm.Gsm.Told.ctx(told), nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}})
  +a = Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st))
  +b : N.GOut() = (S.Put{k, v}, [])
  +x : N.Act = N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), k, S.Ue.ran_id(ue), Ho.Ho.radio(G.CauseRadioNetwork.successful_handover())}
  +l : List<&2, N.Act> = [N.TimerCancel{k}, N.Note{F.Info{}, "NGAP: Handover Notify; the UE moved to the target"}]
  +o = N.Out.also(N.Out.join(a, b), x <> List.append(&2, N.Act, Gsm.Gsm.Told.acts(told), l))
  e12 = Equal.trans(S.Tx, N.Out.tx(o), N.Out.tx(N.Out.join(a, b)), S.Both{N.Out.tx(a), S.Put{k, v}}, PL.Lv.tx_also(N.Out.join(a, b), x <> List.append(&2, N.Act, Gsm.Gsm.Told.acts(told), l)), PW.Out.tx_join(a, b))
  sr = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(N.Step.of(st, o))), PT.Tk.ues(N.Out.tx(o), ues), PT.Tk.render(st, o))
  se = Equal.sym(S.Tx, N.Out.tx(o), S.Both{N.Out.tx(a), S.Put{k, v}}, e12)
  g : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(N.Step.of(st, o)))) == Some{v} : Maybe<&2, S.Ue>} = (%sr : {Tb.Table.get(S.Ue, k, _) == Some{v} : Maybe<&2, S.Ue>}; (%se : {Tb.Table.get(S.Ue, k, PT.Tk.ues(_, ues)) == Some{v} : Maybe<&2, S.Ue>}; PPs.Mv.get_put(k, v, PT.Tk.ues(N.Out.tx(a), ues))))
  g

def Hn.at(+st: S.State, +assoc: U32, +k: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +ran: B.Bytes(), +s: U32, +ts: List<&2, S.Tunnel>, +x: N.Step(), +e: {x == N.Step.of(st, Ho.Ho.complete(st, assoc, k, ue, ctx, nh, ran, s, ts, True{})) : N.Step()}) -> {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(x))) == Some{S.Ue.moved(ue, assoc, ran, s, S.Registered{Gsm.Gsm.Told.ctx(Gsm.Gsm.releases(k, assoc, s, ran, Sw.Sw.released(ts, S.Sessions.of_ue(k, S.State.sessions(st))), ctx)), nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}})} : Maybe<&2, S.Ue>}:
  se = Equal.sym(N.Step(), x, N.Step.of(st, Ho.Ho.complete(st, assoc, k, ue, ctx, nh, ran, s, ts, True{})), e)
  %se : {Tb.Table.get(S.Ue, k, S.State.ues(K.Kernel.state(_))) == Some{S.Ue.moved(ue, assoc, ran, s, S.Registered{Gsm.Gsm.Told.ctx(Gsm.Gsm.releases(k, assoc, s, ran, Sw.Sw.released(ts, S.Sessions.of_ue(k, S.State.sessions(st))), ctx)), nh, Some{S.Side{S.Ue.assoc(ue), Some{S.Ue.ran_id(ue)}}}})} : Maybe<&2, S.Ue>}
  Hn.of(st, assoc, k, ue, ctx, nh, ran, s, ts)

def L.amf.handover.notify_releases(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, amf, ran, uli, k, ue, ctx, nh, source, s, ts, sp, ep, ei, ev, eid, eg, eph, es, eo, ef, eup):
  +T = N.Step.of(st, Ho.Ho.complete(st, assoc, k, ue, ctx, nh, ran, s, ts, True{}))
  +e = PW.Rt.view(V.HandoverNotify.View, x => {x == T : N.Step()}, st, entropy, assoc, stream, len, bytes, 0, 11, crit, value, ies, c, i => V.HandoverNotify.view(i), r => Ho.Ho.notify_of_view(st, assoc, r), Done{V.HandoverNotify.View{amf, ran, uli}}, ep, ei, {==}, eup, {==}, ev, Hn.found(st, assoc, amf, ran, uli, k, ue, ctx, nh, source, s, ts, sp, eid, eg, eph, es, eo, ef))
  (Hn.at(st, assoc, k, ue, ctx, nh, ran, s, ts, K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), e), e)
