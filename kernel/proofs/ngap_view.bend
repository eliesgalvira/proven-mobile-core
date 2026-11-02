import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as GV
import ../LAWS.bend as L
import ./lib.bend as P

def View.absurd(-A: Data, -G: Type, err: B.Err, v: A, e: {Fail{err} == Done{v} : Result<&2, &2, B.Err, A>}) -> G:
  Empty.absurd(G, P.Refute.fail_done(B.Err, A, err, v, e))

def Bool.not_true(x: Bool, e: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.Refute.bool(e))
    case False{}:
      {==}

def Bool.or_false_l(a: Bool, +b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.Refute.true_false(e))
    case False{}:
      {==}

def Bool.or_false_r(a: Bool, +b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, P.Refute.true_false(e))
    case False{}:
      e

# The prelude
# -----------

def Prelude.dv(+known: List<&2, U32>, +ies: List<&2, Fr.Ie>, ok: Bool, eok: {Bool.and(Fr.Ies.no_dups(ies), Fr.Ies.comprehended(known, ies)) == ok : Bool}, +ies2: List<&2, Fr.Ie>, +e: {Fr.View.gate(ies, ok) == Done{ies2} : Result<&2, &2, B.Err, List<&2, Fr.Ie>>}) -> {Fr.Ies.no_dups(ies) == True{} : Bool}:
  match ok:
    case False{}:
      View.absurd(List<&2, Fr.Ie>, {Fr.Ies.no_dups(ies) == True{} : Bool}, B.Invalid{0}, ies2, e)
    case True{}:
      P.Bool.and_true_l(Fr.Ies.no_dups(ies), Fr.Ies.comprehended(known, ies), eok)

def L.ngap.view.duplicate_rejected(known, ies, ies2, e):
  Prelude.dv(known, ies, Bool.and(Fr.Ies.no_dups(ies), Fr.Ies.comprehended(known, ies)), {==}, ies2, e)

# Lookups
# -------

def Ies.absent(+id: U32, ies: List<&2, Fr.Ie>, +h: {Fr.Ies.has(id, ies) == False{} : Bool}) -> {Fr.Ies.occurrences(id, ies) == 0n : Nat}:
  match ies:
    case Nil{}:
      {==}
    case +ie <> +more:
      sh = Equal.sym(Bool, U32.is_eq(Fr.Ie.id(ie), id), False{}, Bool.or_false_l(U32.is_eq(Fr.Ie.id(ie), id), Fr.Ies.has(id, more), h))
      %sh : {Fr.Ies.bump(Fr.Ies.occurrences(id, more), _) == 0n : Nat}
      Ies.absent(id, more, Bool.or_false_r(U32.is_eq(Fr.Ie.id(ie), id), Fr.Ies.has(id, more), h))

def Ies.lookup_step(+id: U32, +ie: Fr.Ie, +more: List<&2, Fr.Ie>, +v: B.Bytes(), hit: Bool, +eh: {U32.is_eq(Fr.Ie.id(ie), id) == hit : Bool}, +nd: {Bool.and(Bool.not(Fr.Ies.has(Fr.Ie.id(ie), more)), Fr.Ies.no_dups(more)) == True{} : Bool}, +e: {Fr.Ies.pick(ie, Fr.Ies.lookup(id, more), hit) == Some{v} : Maybe<&2, B.Bytes()>}, ih: {Fr.Ies.lookup(id, more) == Some{v} : Maybe<&2, B.Bytes()>} -> {Fr.Ies.occurrences(id, more) == 1n : Nat}) -> {Fr.Ies.bump(Fr.Ies.occurrences(id, more), U32.is_eq(Fr.Ie.id(ie), id)) == 1n : Nat}:
  match hit:
    case True{}:
      seh = Equal.sym(Bool, U32.is_eq(Fr.Ie.id(ie), id), True{}, eh)
      %seh : {Fr.Ies.bump(Fr.Ies.occurrences(id, more), _) == 1n : Nat}
      hid = P.U32.eq_of_is_eq(Fr.Ie.id(ie), id, eh)
      h0 = Bool.not_true(Fr.Ies.has(Fr.Ie.id(ie), more), P.Bool.and_true_l(Bool.not(Fr.Ies.has(Fr.Ie.id(ie), more)), Fr.Ies.no_dups(more), nd))
      Equal.cong(Nat, Nat, n => 1n+n, Fr.Ies.occurrences(id, more), 0n, Ies.absent(id, more, (%hid : {Fr.Ies.has(_, more) == False{} : Bool}; h0)))
    case False{}:
      seh = Equal.sym(Bool, U32.is_eq(Fr.Ie.id(ie), id), False{}, eh)
      %seh : {Fr.Ies.bump(Fr.Ies.occurrences(id, more), _) == 1n : Nat}
      ih(e)

# With no duplicate ids, a successful lookup means exactly one occurrence.
def Ies.lookup_count(+id: U32, ies: List<&2, Fr.Ie>, +v: B.Bytes(), +nd: {Fr.Ies.no_dups(ies) == True{} : Bool}, +e: {Fr.Ies.lookup(id, ies) == Some{v} : Maybe<&2, B.Bytes()>}) -> {Fr.Ies.occurrences(id, ies) == 1n : Nat}:
  match ies:
    case Nil{}:
      Empty.absurd({0n == 1n : Nat}, P.Refute.none_some(B.Bytes(), v, e))
    case +ie <> +more:
      Ies.lookup_step(id, ie, more, v, U32.is_eq(Fr.Ie.id(ie), id), {==}, nd, e, e2 => Ies.lookup_count(id, more, v, P.Bool.and_true_r(Bool.not(Fr.Ies.has(Fr.Ie.id(ie), more)), Fr.Ies.no_dups(more), nd), e2))

# InitialUEMessage: the four mandatory IEs
# ----------------------------------------

def IUM.Goal(ies: List<&2, Fr.Ie>) -> Type:
  {Fr.Ies.occurrences(85, ies) == 1n : Nat} & ({Fr.Ies.occurrences(38, ies) == 1n : Nat} & ({Fr.Ies.occurrences(121, ies) == 1n : Nat} & {Fr.Ies.occurrences(90, ies) == 1n : Nat}))

def IUM.m4(+ies: List<&2, Fr.Ie>, +x1: G.RAN_UE_NGAP_ID(), +x2: G.NAS_PDU(), +x3: G.UserLocationInformation, m: Maybe<&2, B.Bytes()>, +em: {Fr.Ies.lookup(90, ies) == m : Maybe<&2, B.Bytes()>}, +v: GV.InitialUEMessage.View, +e: {GV.InitialUEMessage.v_rrcestablishmentcause(ies, x1, x2, x3, m) == Done{v} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}, +nd: {Fr.Ies.no_dups(ies) == True{} : Bool}) -> {Fr.Ies.occurrences(90, ies) == 1n : Nat}:
  match m:
    case None{}:
      View.absurd(GV.InitialUEMessage.View, {Fr.Ies.occurrences(90, ies) == 1n : Nat}, B.Invalid{90}, v, e)
    case Some{+bs}:
      Ies.lookup_count(90, ies, bs, nd, em)

def IUM.d3(+ies: List<&2, Fr.Ie>, +x1: G.RAN_UE_NGAP_ID(), +x2: G.NAS_PDU(), r: Result<&2, &2, B.Err, G.UserLocationInformation>, +v: GV.InitialUEMessage.View, +e: {GV.InitialUEMessage.d_userlocationinformation(ies, x1, x2, r) == Done{v} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}, +nd: {Fr.Ies.no_dups(ies) == True{} : Bool}) -> {Fr.Ies.occurrences(90, ies) == 1n : Nat}:
  match r:
    case Fail{err}:
      View.absurd(GV.InitialUEMessage.View, {Fr.Ies.occurrences(90, ies) == 1n : Nat}, err, v, e)
    case Done{+x3}:
      IUM.m4(ies, x1, x2, x3, Fr.Ies.lookup(90, ies), {==}, v, e, nd)

def IUM.m3(+ies: List<&2, Fr.Ie>, +x1: G.RAN_UE_NGAP_ID(), +x2: G.NAS_PDU(), m: Maybe<&2, B.Bytes()>, +em: {Fr.Ies.lookup(121, ies) == m : Maybe<&2, B.Bytes()>}, +v: GV.InitialUEMessage.View, +e: {GV.InitialUEMessage.v_userlocationinformation(ies, x1, x2, m) == Done{v} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}, +nd: {Fr.Ies.no_dups(ies) == True{} : Bool}) -> {Fr.Ies.occurrences(121, ies) == 1n : Nat} & {Fr.Ies.occurrences(90, ies) == 1n : Nat}:
  match m:
    case None{}:
      View.absurd(GV.InitialUEMessage.View, {Fr.Ies.occurrences(121, ies) == 1n : Nat} & {Fr.Ies.occurrences(90, ies) == 1n : Nat}, B.Invalid{121}, v, e)
    case Some{+bs}:
      (Ies.lookup_count(121, ies, bs, nd, em), IUM.d3(ies, x1, x2, Fr.View.exact(G.UserLocationInformation, G.UserLocationInformation.read(Ap.Cur{0n, Ap.unpack(bs)})), v, e, nd))

def IUM.d2(+ies: List<&2, Fr.Ie>, +x1: G.RAN_UE_NGAP_ID(), r: Result<&2, &2, B.Err, G.NAS_PDU()>, +v: GV.InitialUEMessage.View, +e: {GV.InitialUEMessage.d_nas_pdu(ies, x1, r) == Done{v} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}, +nd: {Fr.Ies.no_dups(ies) == True{} : Bool}) -> {Fr.Ies.occurrences(121, ies) == 1n : Nat} & {Fr.Ies.occurrences(90, ies) == 1n : Nat}:
  match r:
    case Fail{err}:
      View.absurd(GV.InitialUEMessage.View, {Fr.Ies.occurrences(121, ies) == 1n : Nat} & {Fr.Ies.occurrences(90, ies) == 1n : Nat}, err, v, e)
    case Done{+x2}:
      IUM.m3(ies, x1, x2, Fr.Ies.lookup(121, ies), {==}, v, e, nd)

def IUM.m2(+ies: List<&2, Fr.Ie>, +x1: G.RAN_UE_NGAP_ID(), m: Maybe<&2, B.Bytes()>, +em: {Fr.Ies.lookup(38, ies) == m : Maybe<&2, B.Bytes()>}, +v: GV.InitialUEMessage.View, +e: {GV.InitialUEMessage.v_nas_pdu(ies, x1, m) == Done{v} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}, +nd: {Fr.Ies.no_dups(ies) == True{} : Bool}) -> {Fr.Ies.occurrences(38, ies) == 1n : Nat} & ({Fr.Ies.occurrences(121, ies) == 1n : Nat} & {Fr.Ies.occurrences(90, ies) == 1n : Nat}):
  match m:
    case None{}:
      View.absurd(GV.InitialUEMessage.View, {Fr.Ies.occurrences(38, ies) == 1n : Nat} & ({Fr.Ies.occurrences(121, ies) == 1n : Nat} & {Fr.Ies.occurrences(90, ies) == 1n : Nat}), B.Invalid{38}, v, e)
    case Some{+bs}:
      (Ies.lookup_count(38, ies, bs, nd, em), IUM.d2(ies, x1, Fr.View.exact(G.NAS_PDU(), G.NAS_PDU.read(Ap.Cur{0n, Ap.unpack(bs)})), v, e, nd))

def IUM.d1(+ies: List<&2, Fr.Ie>, r: Result<&2, &2, B.Err, G.RAN_UE_NGAP_ID()>, +v: GV.InitialUEMessage.View, +e: {GV.InitialUEMessage.d_ran_ue_ngap_id(ies, r) == Done{v} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}, +nd: {Fr.Ies.no_dups(ies) == True{} : Bool}) -> {Fr.Ies.occurrences(38, ies) == 1n : Nat} & ({Fr.Ies.occurrences(121, ies) == 1n : Nat} & {Fr.Ies.occurrences(90, ies) == 1n : Nat}):
  match r:
    case Fail{err}:
      View.absurd(GV.InitialUEMessage.View, {Fr.Ies.occurrences(38, ies) == 1n : Nat} & ({Fr.Ies.occurrences(121, ies) == 1n : Nat} & {Fr.Ies.occurrences(90, ies) == 1n : Nat}), err, v, e)
    case Done{+x1}:
      IUM.m2(ies, x1, Fr.Ies.lookup(38, ies), {==}, v, e, nd)

def IUM.m1(+ies: List<&2, Fr.Ie>, m: Maybe<&2, B.Bytes()>, +em: {Fr.Ies.lookup(85, ies) == m : Maybe<&2, B.Bytes()>}, +v: GV.InitialUEMessage.View, +e: {GV.InitialUEMessage.v_ran_ue_ngap_id(ies, m) == Done{v} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}, +nd: {Fr.Ies.no_dups(ies) == True{} : Bool}) -> IUM.Goal(ies):
  match m:
    case None{}:
      View.absurd(GV.InitialUEMessage.View, IUM.Goal(ies), B.Invalid{85}, v, e)
    case Some{+bs}:
      (Ies.lookup_count(85, ies, bs, nd, em), IUM.d1(ies, Fr.View.exact(G.RAN_UE_NGAP_ID(), G.RAN_UE_NGAP_ID.read(Ap.Cur{0n, Ap.unpack(bs)})), v, e, nd))

def IUM.gate(+ies: List<&2, Fr.Ie>, ok: Bool, +eok: {Bool.and(Fr.Ies.no_dups(ies), Fr.Ies.comprehended(GV.InitialUEMessage.known(), ies)) == ok : Bool}, +ies2: List<&2, Fr.Ie>, +eg: {Fr.View.gate(ies, ok) == Done{ies2} : Result<&2, &2, B.Err, List<&2, Fr.Ie>>}, +v: GV.InitialUEMessage.View, +e: {GV.InitialUEMessage.v_ran_ue_ngap_id(ies2, Fr.Ies.lookup(85, ies2)) == Done{v} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}) -> IUM.Goal(ies):
  match ok:
    case False{}:
      View.absurd(List<&2, Fr.Ie>, IUM.Goal(ies), B.Invalid{0}, ies2, eg)
    case True{}:
      +same = Equal.cong(Result<&2, &2, B.Err, List<&2, Fr.Ie>>, List<&2, Fr.Ie>, y => P.Res.value(B.Err, List<&2, Fr.Ie>, y, ies), Done{ies}, Done{ies2}, eg)
      seq = Equal.sym(List<&2, Fr.Ie>, ies, ies2, same)
      %seq : IUM.Goal(_)
      IUM.m1(ies2, Fr.Ies.lookup(85, ies2), {==}, v, e, (%same : {Fr.Ies.no_dups(_) == True{} : Bool}; P.Bool.and_true_l(Fr.Ies.no_dups(ies), Fr.Ies.comprehended(GV.InitialUEMessage.known(), ies), eok)))

def IUM.prelude(+ies: List<&2, Fr.Ie>, rp: Result<&2, &2, B.Err, List<&2, Fr.Ie>>, +erp: {Fr.View.prelude(GV.InitialUEMessage.known(), ies) == rp : Result<&2, &2, B.Err, List<&2, Fr.Ie>>}, +v: GV.InitialUEMessage.View, +e: {GV.InitialUEMessage.v_prelude(rp) == Done{v} : Result<&2, &2, B.Err, GV.InitialUEMessage.View>}) -> IUM.Goal(ies):
  match rp:
    case Fail{err}:
      View.absurd(GV.InitialUEMessage.View, IUM.Goal(ies), err, v, e)
    case Done{+ies2}:
      IUM.gate(ies, Bool.and(Fr.Ies.no_dups(ies), Fr.Ies.comprehended(GV.InitialUEMessage.known(), ies)), {==}, ies2, erp, v, e)

def L.ngap.initial_ue_message.mandatory(ies, v, e):
  IUM.prelude(ies, Fr.View.prelude(GV.InitialUEMessage.known(), ies), {==}, v, e)
