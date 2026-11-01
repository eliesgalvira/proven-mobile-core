import Base
import ../LAWS.bend as L
import ../bytes.bend as B
import ../nas/ie.bend as I
import ../nas/sm.bend as Sm
import ./lib.bend as P
import ./mm.bend as PM

# Proofs of the 5GSM message laws (ticket 11). The field and optional-IE
# lemmas are those of kernel/proofs/mm.bend.

def SmMsg.Res() -> Data:
  Result<&2, &2, B.Err, Sm.Sm>

def SmType.code8(t: Sm.Sm.Type) -> {U32.and(255, Sm.Sm.Type.code(t)) == Sm.Sm.Type.code(t) : U32}:
  match t:
    case Sm.EstablishmentRequest{}:
      {==}
    case Sm.EstablishmentAccept{}:
      {==}
    case Sm.EstablishmentReject{}:
      {==}
    case Sm.ModificationRequest{}:
      {==}
    case Sm.ModificationReject{}:
      {==}
    case Sm.ReleaseRequest{}:
      {==}
    case Sm.ReleaseCommand{}:
      {==}
    case Sm.ReleaseComplete{}:
      {==}
    case Sm.SmStatus{}:
      {==}

def SmType.of_code(t: Sm.Sm.Type) -> {Sm.Sm.Type.of(Sm.Sm.Type.code(t)) == Some{t} : Maybe<&2, Sm.Sm.Type>}:
  match t:
    case Sm.EstablishmentRequest{}:
      {==}
    case Sm.EstablishmentAccept{}:
      {==}
    case Sm.EstablishmentReject{}:
      {==}
    case Sm.ModificationRequest{}:
      {==}
    case Sm.ModificationReject{}:
      {==}
    case Sm.ReleaseRequest{}:
      {==}
    case Sm.ReleaseCommand{}:
      {==}
    case Sm.ReleaseComplete{}:
      {==}
    case Sm.SmStatus{}:
      {==}

def SmType.inv8(+b: U32, +mt: Sm.Sm.Type, hit: Bool, ev: {U32.is_eq(b, 214) == hit : Bool}, e: {Sm.Sm.Type.of8.pick(b, hit) == Some{mt} : Maybe<&2, Sm.Sm.Type>}) -> {Sm.Sm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Sm.Sm.Type>, Sm.Sm.Type, x => P.Maybe.value(Sm.Sm.Type, x, mt), Some{Sm.SmStatus{}}, Some{mt}, e)
      %em : {Sm.Sm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 214, P.U32.eq_of_is_eq(b, 214, ev))
    case False{}:
      Empty.absurd({Sm.Sm.Type.code(mt) == b : U32}, P.Refute.none_some(Sm.Sm.Type, mt, e))

def SmType.inv7(+b: U32, +mt: Sm.Sm.Type, hit: Bool, ev: {U32.is_eq(b, 212) == hit : Bool}, e: {Sm.Sm.Type.of7.pick(b, hit) == Some{mt} : Maybe<&2, Sm.Sm.Type>}) -> {Sm.Sm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Sm.Sm.Type>, Sm.Sm.Type, x => P.Maybe.value(Sm.Sm.Type, x, mt), Some{Sm.ReleaseComplete{}}, Some{mt}, e)
      %em : {Sm.Sm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 212, P.U32.eq_of_is_eq(b, 212, ev))
    case False{}:
      SmType.inv8(b, mt, U32.is_eq(b, 214), {==}, e)

def SmType.inv6(+b: U32, +mt: Sm.Sm.Type, hit: Bool, ev: {U32.is_eq(b, 211) == hit : Bool}, e: {Sm.Sm.Type.of6.pick(b, hit) == Some{mt} : Maybe<&2, Sm.Sm.Type>}) -> {Sm.Sm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Sm.Sm.Type>, Sm.Sm.Type, x => P.Maybe.value(Sm.Sm.Type, x, mt), Some{Sm.ReleaseCommand{}}, Some{mt}, e)
      %em : {Sm.Sm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 211, P.U32.eq_of_is_eq(b, 211, ev))
    case False{}:
      SmType.inv7(b, mt, U32.is_eq(b, 212), {==}, e)

def SmType.inv5(+b: U32, +mt: Sm.Sm.Type, hit: Bool, ev: {U32.is_eq(b, 209) == hit : Bool}, e: {Sm.Sm.Type.of5.pick(b, hit) == Some{mt} : Maybe<&2, Sm.Sm.Type>}) -> {Sm.Sm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Sm.Sm.Type>, Sm.Sm.Type, x => P.Maybe.value(Sm.Sm.Type, x, mt), Some{Sm.ReleaseRequest{}}, Some{mt}, e)
      %em : {Sm.Sm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 209, P.U32.eq_of_is_eq(b, 209, ev))
    case False{}:
      SmType.inv6(b, mt, U32.is_eq(b, 211), {==}, e)

def SmType.inv4(+b: U32, +mt: Sm.Sm.Type, hit: Bool, ev: {U32.is_eq(b, 202) == hit : Bool}, e: {Sm.Sm.Type.of4.pick(b, hit) == Some{mt} : Maybe<&2, Sm.Sm.Type>}) -> {Sm.Sm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Sm.Sm.Type>, Sm.Sm.Type, x => P.Maybe.value(Sm.Sm.Type, x, mt), Some{Sm.ModificationReject{}}, Some{mt}, e)
      %em : {Sm.Sm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 202, P.U32.eq_of_is_eq(b, 202, ev))
    case False{}:
      SmType.inv5(b, mt, U32.is_eq(b, 209), {==}, e)

def SmType.inv3(+b: U32, +mt: Sm.Sm.Type, hit: Bool, ev: {U32.is_eq(b, 201) == hit : Bool}, e: {Sm.Sm.Type.of3.pick(b, hit) == Some{mt} : Maybe<&2, Sm.Sm.Type>}) -> {Sm.Sm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Sm.Sm.Type>, Sm.Sm.Type, x => P.Maybe.value(Sm.Sm.Type, x, mt), Some{Sm.ModificationRequest{}}, Some{mt}, e)
      %em : {Sm.Sm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 201, P.U32.eq_of_is_eq(b, 201, ev))
    case False{}:
      SmType.inv4(b, mt, U32.is_eq(b, 202), {==}, e)

def SmType.inv2(+b: U32, +mt: Sm.Sm.Type, hit: Bool, ev: {U32.is_eq(b, 195) == hit : Bool}, e: {Sm.Sm.Type.of2.pick(b, hit) == Some{mt} : Maybe<&2, Sm.Sm.Type>}) -> {Sm.Sm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Sm.Sm.Type>, Sm.Sm.Type, x => P.Maybe.value(Sm.Sm.Type, x, mt), Some{Sm.EstablishmentReject{}}, Some{mt}, e)
      %em : {Sm.Sm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 195, P.U32.eq_of_is_eq(b, 195, ev))
    case False{}:
      SmType.inv3(b, mt, U32.is_eq(b, 201), {==}, e)

def SmType.inv1(+b: U32, +mt: Sm.Sm.Type, hit: Bool, ev: {U32.is_eq(b, 194) == hit : Bool}, e: {Sm.Sm.Type.of1.pick(b, hit) == Some{mt} : Maybe<&2, Sm.Sm.Type>}) -> {Sm.Sm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Sm.Sm.Type>, Sm.Sm.Type, x => P.Maybe.value(Sm.Sm.Type, x, mt), Some{Sm.EstablishmentAccept{}}, Some{mt}, e)
      %em : {Sm.Sm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 194, P.U32.eq_of_is_eq(b, 194, ev))
    case False{}:
      SmType.inv2(b, mt, U32.is_eq(b, 195), {==}, e)

def SmType.inv0(+b: U32, +mt: Sm.Sm.Type, hit: Bool, ev: {U32.is_eq(b, 193) == hit : Bool}, e: {Sm.Sm.Type.of0.pick(b, hit) == Some{mt} : Maybe<&2, Sm.Sm.Type>}) -> {Sm.Sm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Sm.Sm.Type>, Sm.Sm.Type, x => P.Maybe.value(Sm.Sm.Type, x, mt), Some{Sm.EstablishmentRequest{}}, Some{mt}, e)
      %em : {Sm.Sm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 193, P.U32.eq_of_is_eq(b, 193, ev))
    case False{}:
      SmType.inv1(b, mt, U32.is_eq(b, 194), {==}, e)

def SmType.of_inv(+b: U32, +mt: Sm.Sm.Type, e: {Sm.Sm.Type.of(b) == Some{mt} : Maybe<&2, Sm.Sm.Type>}) -> {Sm.Sm.Type.code(mt) == b : U32}:
  SmType.inv0(b, mt, U32.is_eq(b, 193), {==}, e)

# Roundtrip
# ---------

def SmMsg.rt(+psi: U32, +pti: U32, +mt: Sm.Sm.Type, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +v: {Sm.Sm.valid(Sm.Sm{psi, pti, mt, fields, opts}) == True{} : Bool}) -> {Sm.Sm.read(Sm.Sm.write(Sm.Sm{psi, pti, mt, fields, opts})) == Done{Sm.Sm{psi, pti, mt, fields, opts}} : SmMsg.Res()}:
  +W = I.Ies.write(opts, [])
  +F = I.Fields.write(fields, W)
  +fp = P.Bool.and_true_l(I.fits8(psi), Bool.and(I.fits8(pti), Bool.and(I.Fields.valid(Sm.Sm.layout(mt), fields), I.Opts.valid(Sm.Sm.table(mt), opts))), v)
  +r1 = P.Bool.and_true_r(I.fits8(psi), Bool.and(I.fits8(pti), Bool.and(I.Fields.valid(Sm.Sm.layout(mt), fields), I.Opts.valid(Sm.Sm.table(mt), opts))), v)
  +ft = P.Bool.and_true_l(I.fits8(pti), Bool.and(I.Fields.valid(Sm.Sm.layout(mt), fields), I.Opts.valid(Sm.Sm.table(mt), opts)), r1)
  +r2 = P.Bool.and_true_r(I.fits8(pti), Bool.and(I.Fields.valid(Sm.Sm.layout(mt), fields), I.Opts.valid(Sm.Sm.table(mt), opts)), r1)
  mp = Equal.sym(U32, U32.and(255, psi), psi, P.U32.eq_of_is_eq(U32.and(255, psi), psi, fp))
  %mp : {Sm.Sm.r_psi_ok(_, U32.and(255, pti) <> U32.and(255, Sm.Sm.Type.code(mt)) <> F, I.fits8(_)) == Done{Sm.Sm{psi, pti, mt, fields, opts}} : SmMsg.Res()}
  sp = Equal.sym(Bool, I.fits8(psi), True{}, fp)
  %sp : {Sm.Sm.r_psi_ok(psi, U32.and(255, pti) <> U32.and(255, Sm.Sm.Type.code(mt)) <> F, _) == Done{Sm.Sm{psi, pti, mt, fields, opts}} : SmMsg.Res()}
  mq = Equal.sym(U32, U32.and(255, pti), pti, P.U32.eq_of_is_eq(U32.and(255, pti), pti, ft))
  %mq : {Sm.Sm.r_pti_ok(psi, _, U32.and(255, Sm.Sm.Type.code(mt)) <> F, I.fits8(_)) == Done{Sm.Sm{psi, pti, mt, fields, opts}} : SmMsg.Res()}
  sq = Equal.sym(Bool, I.fits8(pti), True{}, ft)
  %sq : {Sm.Sm.r_pti_ok(psi, pti, U32.and(255, Sm.Sm.Type.code(mt)) <> F, _) == Done{Sm.Sm{psi, pti, mt, fields, opts}} : SmMsg.Res()}
  sc = Equal.sym(U32, U32.and(255, Sm.Sm.Type.code(mt)), Sm.Sm.Type.code(mt), SmType.code8(mt))
  %sc : {Sm.Sm.r_type(psi, pti, _, F, Sm.Sm.Type.of(_)) == Done{Sm.Sm{psi, pti, mt, fields, opts}} : SmMsg.Res()}
  so = Equal.sym(Maybe<&2, Sm.Sm.Type>, Sm.Sm.Type.of(Sm.Sm.Type.code(mt)), Some{mt}, SmType.of_code(mt))
  %so : {Sm.Sm.r_type(psi, pti, Sm.Sm.Type.code(mt), F, _) == Done{Sm.Sm{psi, pti, mt, fields, opts}} : SmMsg.Res()}
  fr = Equal.sym(B.Read(List<&2, I.Field>), I.Fields.read(Sm.Sm.layout(mt), F), Done{(fields, W)}, PM.Fields.rt(Sm.Sm.layout(mt), fields, W, P.Bool.and_true_l(I.Fields.valid(Sm.Sm.layout(mt), fields), I.Opts.valid(Sm.Sm.table(mt), opts), r2)))
  %fr : {Sm.Sm.r_fields(psi, pti, mt, _) == Done{Sm.Sm{psi, pti, mt, fields, opts}} : SmMsg.Res()}
  orr = Equal.sym(PM.Opts.Res(), I.Opts.read(List.length(&2, U32, W), Sm.Sm.table(mt), W), Done{opts}, PM.Opts.rt(Sm.Sm.table(mt), opts, List.length(&2, U32, W), P.Bool.and_true_r(I.Fields.valid(Sm.Sm.layout(mt), fields), I.Opts.valid(Sm.Sm.table(mt), opts), r2), P.Nat.le_refl(List.length(&2, U32, W))))
  %orr : {Sm.Sm.r_opts(psi, pti, mt, fields, _) == Done{Sm.Sm{psi, pti, mt, fields, opts}} : SmMsg.Res()}
  {==}

def L.nas.sm.roundtrip(m, v):
  match m:
    case Sm.Sm{+psi, +pti, +mt, +fields, +opts}:
      SmMsg.rt(psi, pti, mt, fields, opts, v)

# Decoding gives valid messages
# -----------------------------

def SmMsg.dv_opts(+psi: U32, +pti: U32, +mt: Sm.Sm.Type, +fields: List<&2, I.Field>, ro: PM.Opts.Res(), +m: Sm.Sm, +e: {Sm.Sm.r_opts(psi, pti, mt, fields, ro) == Done{m} : SmMsg.Res()}, fp: {I.fits8(psi) == True{} : Bool}, ft: {I.fits8(pti) == True{} : Bool}, hf: {I.Fields.valid(Sm.Sm.layout(mt), fields) == True{} : Bool}, ho: @opts: List<&2, I.Ie> -> {ro == Done{opts} : PM.Opts.Res()} -> {I.Opts.valid(Sm.Sm.table(mt), opts) == True{} : Bool}) -> {Sm.Sm.valid(m) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Empty.absurd({Sm.Sm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Sm.Sm, err, m, e))
    case Done{+opts}:
      em = Equal.cong(SmMsg.Res(), Sm.Sm, x => P.Res.value(B.Err, Sm.Sm, x, m), Done{Sm.Sm{psi, pti, mt, fields, opts}}, Done{m}, e)
      %em : {Sm.Sm.valid(_) == True{} : Bool}
      P.Bool.and_intro(I.fits8(psi), Bool.and(I.fits8(pti), Bool.and(I.Fields.valid(Sm.Sm.layout(mt), fields), I.Opts.valid(Sm.Sm.table(mt), opts))), fp, P.Bool.and_intro(I.fits8(pti), Bool.and(I.Fields.valid(Sm.Sm.layout(mt), fields), I.Opts.valid(Sm.Sm.table(mt), opts)), ft, P.Bool.and_intro(I.Fields.valid(Sm.Sm.layout(mt), fields), I.Opts.valid(Sm.Sm.table(mt), opts), hf, ho(opts, {==}))))

def SmMsg.dv_fields(+psi: U32, +pti: U32, +mt: Sm.Sm.Type, rf: B.Read(List<&2, I.Field>), +m: Sm.Sm, +e: {Sm.Sm.r_fields(psi, pti, mt, rf) == Done{m} : SmMsg.Res()}, fp: {I.fits8(psi) == True{} : Bool}, ft: {I.fits8(pti) == True{} : Bool}, hf: @fs: List<&2, I.Field> -> @r: B.Bytes() -> {rf == Done{(fs, r)} : B.Read(List<&2, I.Field>)} -> {I.Fields.valid(Sm.Sm.layout(mt), fs) == True{} : Bool}) -> {Sm.Sm.valid(m) == True{} : Bool}:
  match rf:
    case Fail{err}:
      Empty.absurd({Sm.Sm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Sm.Sm, err, m, e))
    case Done{(+fields, +rest)}:
      SmMsg.dv_opts(psi, pti, mt, fields, I.Opts.read(List.length(&2, U32, rest), Sm.Sm.table(mt), rest), m, e, fp, ft, hf(fields, rest, {==}), opts => e2 => PM.Opts.dv(Sm.Sm.table(mt), List.length(&2, U32, rest), rest, opts, e2))

def SmMsg.dv_type(+psi: U32, +pti: U32, +code: U32, +r: B.Bytes(), +m: Sm.Sm, tm: Maybe<&2, Sm.Sm.Type>, +e: {Sm.Sm.r_type(psi, pti, code, r, tm) == Done{m} : SmMsg.Res()}, fp: {I.fits8(psi) == True{} : Bool}, ft: {I.fits8(pti) == True{} : Bool}) -> {Sm.Sm.valid(m) == True{} : Bool}:
  match tm:
    case None{}:
      Empty.absurd({Sm.Sm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Sm.Sm, B.Unsupported{code}, m, e))
    case Some{+mt}:
      SmMsg.dv_fields(psi, pti, mt, I.Fields.read(Sm.Sm.layout(mt), r), m, e, fp, ft, fs => r2 => e2 => PM.Fields.dv(Sm.Sm.layout(mt), r, fs, r2, e2))

def SmMsg.dv_pti_ok(ok: Bool, +psi: U32, +pti: U32, +r: B.Bytes(), +m: Sm.Sm, ev: {I.fits8(pti) == ok : Bool}, +e: {Sm.Sm.r_pti_ok(psi, pti, r, ok) == Done{m} : SmMsg.Res()}, fp: {I.fits8(psi) == True{} : Bool}) -> {Sm.Sm.valid(m) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Sm.Sm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Sm.Sm, B.Invalid{pti}, m, e))
    case True{}:
      match r:
        case Nil{}:
          Empty.absurd({Sm.Sm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Sm.Sm, B.Short{}, m, e))
        case +code <> +r2:
          SmMsg.dv_type(psi, pti, code, r2, m, Sm.Sm.Type.of(code), e, fp, ev)

def SmMsg.dv_psi_ok(ok: Bool, +psi: U32, +r: B.Bytes(), +m: Sm.Sm, ev: {I.fits8(psi) == ok : Bool}, +e: {Sm.Sm.r_psi_ok(psi, r, ok) == Done{m} : SmMsg.Res()}) -> {Sm.Sm.valid(m) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Sm.Sm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Sm.Sm, B.Invalid{psi}, m, e))
    case True{}:
      match r:
        case Nil{}:
          Empty.absurd({Sm.Sm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Sm.Sm, B.Short{}, m, e))
        case +pti <> +r2:
          SmMsg.dv_pti_ok(I.fits8(pti), psi, pti, r2, m, {==}, e, ev)

def SmMsg.dv_epd(ok: Bool, +r: B.Bytes(), +epd: U32, +m: Sm.Sm, +e: {Sm.Sm.r_epd(r, epd, ok) == Done{m} : SmMsg.Res()}) -> {Sm.Sm.valid(m) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Sm.Sm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Sm.Sm, B.Invalid{epd}, m, e))
    case True{}:
      match r:
        case Nil{}:
          Empty.absurd({Sm.Sm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Sm.Sm, B.Short{}, m, e))
        case +psi <> +r2:
          SmMsg.dv_psi_ok(I.fits8(psi), psi, r2, m, {==}, e)

def SmMsg.dv(bs: B.Bytes(), +m: Sm.Sm, +e: {Sm.Sm.read(bs) == Done{m} : SmMsg.Res()}) -> {Sm.Sm.valid(m) == True{} : Bool}:
  match bs:
    case Nil{}:
      Empty.absurd({Sm.Sm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Sm.Sm, B.Short{}, m, e))
    case +epd <> +r:
      SmMsg.dv_epd(U32.is_eq(epd, Sm.Sm.epd()), r, epd, m, e)

def L.nas.sm.decode_valid(bs, m, e):
  SmMsg.dv(bs, m, e)

# The bytes a decoded message came from are its encoding
# ----------------------------------------------------

def SmMsg.sx_fin(+epd: U32, +psi: U32, +pti: U32, +code: U32, +r: B.Bytes(), +mt: Sm.Sm.Type, +fields: List<&2, I.Field>, +rest: B.Bytes(), +opts: List<&2, I.Ie>, +m: Sm.Sm, e46: {epd == 46 : U32}, mp: {U32.and(255, psi) == psi : U32}, mq: {U32.and(255, pti) == pti : U32}, ec: {Sm.Sm.Type.code(mt) == code : U32}, em: {Sm.Sm{psi, pti, mt, fields, opts} == m : Sm.Sm}, wf: {I.Fields.write(fields, rest) == r : B.Bytes()}, wo: {I.Ies.write(opts, []) == rest : B.Bytes()}) -> {Sm.Sm.write(m) == epd <> psi <> pti <> code <> r : B.Bytes()}:
  %em : {Sm.Sm.write(_) == epd <> psi <> pti <> code <> r : B.Bytes()}
  s46 = Equal.sym(U32, epd, 46, e46)
  %s46 : {Sm.Sm.write(Sm.Sm{psi, pti, mt, fields, opts}) == _ <> psi <> pti <> code <> r : B.Bytes()}
  sp = Equal.sym(U32, U32.and(255, psi), psi, mp)
  %sp : {46 <> _ <> U32.and(255, pti) <> U32.and(255, Sm.Sm.Type.code(mt)) <> I.Fields.write(fields, I.Ies.write(opts, [])) == 46 <> psi <> pti <> code <> r : B.Bytes()}
  sq = Equal.sym(U32, U32.and(255, pti), pti, mq)
  %sq : {46 <> psi <> _ <> U32.and(255, Sm.Sm.Type.code(mt)) <> I.Fields.write(fields, I.Ies.write(opts, [])) == 46 <> psi <> pti <> code <> r : B.Bytes()}
  c8 = Equal.sym(U32, U32.and(255, Sm.Sm.Type.code(mt)), Sm.Sm.Type.code(mt), SmType.code8(mt))
  %c8 : {46 <> psi <> pti <> _ <> I.Fields.write(fields, I.Ies.write(opts, [])) == 46 <> psi <> pti <> code <> r : B.Bytes()}
  %ec : {46 <> psi <> pti <> Sm.Sm.Type.code(mt) <> I.Fields.write(fields, I.Ies.write(opts, [])) == 46 <> psi <> pti <> _ <> r : B.Bytes()}
  swo = Equal.sym(B.Bytes(), I.Ies.write(opts, []), rest, wo)
  %swo : {46 <> psi <> pti <> Sm.Sm.Type.code(mt) <> I.Fields.write(fields, _) == 46 <> psi <> pti <> Sm.Sm.Type.code(mt) <> r : B.Bytes()}
  swf = Equal.sym(B.Bytes(), I.Fields.write(fields, rest), r, wf)
  %swf : {46 <> psi <> pti <> Sm.Sm.Type.code(mt) <> _ == 46 <> psi <> pti <> Sm.Sm.Type.code(mt) <> r : B.Bytes()}
  {==}

def SmMsg.sx_opts(ro: PM.Opts.Res(), +epd: U32, +psi: U32, +pti: U32, +code: U32, +r: B.Bytes(), +mt: Sm.Sm.Type, +fields: List<&2, I.Field>, +rest: B.Bytes(), +m: Sm.Sm, e46: {epd == 46 : U32}, mp: {U32.and(255, psi) == psi : U32}, mq: {U32.and(255, pti) == pti : U32}, ec: {Sm.Sm.Type.code(mt) == code : U32}, ero: {I.Opts.read(List.length(&2, U32, rest), Sm.Sm.table(mt), rest) == ro : PM.Opts.Res()}, +e: {Sm.Sm.r_opts(psi, pti, mt, fields, ro) == Done{m} : SmMsg.Res()}, s: PM.Fields.Sx(fields, rest, r)) -> {Sm.Sm.write(m) == epd <> psi <> pti <> code <> r : B.Bytes()}:
  match ro:
    case Fail{err}:
      Empty.absurd({Sm.Sm.write(m) == epd <> psi <> pti <> code <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Sm.Sm, err, m, e))
    case Done{+opts}:
      (wf, ar) = s
      SmMsg.sx_fin(epd, psi, pti, code, r, mt, fields, rest, opts, m, e46, mp, mq, ec, Equal.cong(SmMsg.Res(), Sm.Sm, x => P.Res.value(B.Err, Sm.Sm, x, m), Done{Sm.Sm{psi, pti, mt, fields, opts}}, Done{m}, e), wf, PM.Opts.sx(Sm.Sm.table(mt), List.length(&2, U32, rest), rest, opts, ero, ar))

def SmMsg.sx_fields(rf: B.Read(List<&2, I.Field>), +epd: U32, +psi: U32, +pti: U32, +code: U32, +r: B.Bytes(), +mt: Sm.Sm.Type, +m: Sm.Sm, e46: {epd == 46 : U32}, mp: {U32.and(255, psi) == psi : U32}, mq: {U32.and(255, pti) == pti : U32}, ec: {Sm.Sm.Type.code(mt) == code : U32}, erf: {I.Fields.read(Sm.Sm.layout(mt), r) == rf : B.Read(List<&2, I.Field>)}, +e: {Sm.Sm.r_fields(psi, pti, mt, rf) == Done{m} : SmMsg.Res()}, ab: {B.all_bytes(r) == True{} : Bool}) -> {Sm.Sm.write(m) == epd <> psi <> pti <> code <> r : B.Bytes()}:
  match rf:
    case Fail{err}:
      Empty.absurd({Sm.Sm.write(m) == epd <> psi <> pti <> code <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Sm.Sm, err, m, e))
    case Done{(+fields, +rest)}:
      SmMsg.sx_opts(I.Opts.read(List.length(&2, U32, rest), Sm.Sm.table(mt), rest), epd, psi, pti, code, r, mt, fields, rest, m, e46, mp, mq, ec, {==}, e, PM.Fields.sx(Sm.Sm.layout(mt), r, fields, rest, erf, ab))

def SmMsg.sx_type(tm: Maybe<&2, Sm.Sm.Type>, +epd: U32, +psi: U32, +pti: U32, +code: U32, +r: B.Bytes(), +m: Sm.Sm, e46: {epd == 46 : U32}, mp: {U32.and(255, psi) == psi : U32}, mq: {U32.and(255, pti) == pti : U32}, etm: {Sm.Sm.Type.of(code) == tm : Maybe<&2, Sm.Sm.Type>}, +e: {Sm.Sm.r_type(psi, pti, code, r, tm) == Done{m} : SmMsg.Res()}, ab: {B.all_bytes(code <> r) == True{} : Bool}) -> {Sm.Sm.write(m) == epd <> psi <> pti <> code <> r : B.Bytes()}:
  match tm:
    case None{}:
      Empty.absurd({Sm.Sm.write(m) == epd <> psi <> pti <> code <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Sm.Sm, B.Unsupported{code}, m, e))
    case Some{+mt}:
      SmMsg.sx_fields(I.Fields.read(Sm.Sm.layout(mt), r), epd, psi, pti, code, r, mt, m, e46, mp, mq, SmType.of_inv(code, mt, etm), {==}, e, P.Bool.and_true_r(B.is_byte(code), B.all_bytes(r), ab))

def SmMsg.sx_pti_ok(ok: Bool, +epd: U32, +psi: U32, +pti: U32, +r: B.Bytes(), +m: Sm.Sm, e46: {epd == 46 : U32}, mp: {U32.and(255, psi) == psi : U32}, ev: {I.fits8(pti) == ok : Bool}, +e: {Sm.Sm.r_pti_ok(psi, pti, r, ok) == Done{m} : SmMsg.Res()}, ab: {B.all_bytes(pti <> r) == True{} : Bool}) -> {Sm.Sm.write(m) == epd <> psi <> pti <> r : B.Bytes()}:
  match ok:
    case False{}:
      Empty.absurd({Sm.Sm.write(m) == epd <> psi <> pti <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Sm.Sm, B.Invalid{pti}, m, e))
    case True{}:
      match r:
        case Nil{}:
          Empty.absurd({Sm.Sm.write(m) == epd <> psi <> pti <> [] : B.Bytes()}, P.Refute.fail_done(B.Err, Sm.Sm, B.Short{}, m, e))
        case +code <> +r2:
          SmMsg.sx_type(Sm.Sm.Type.of(code), epd, psi, pti, code, r2, m, e46, mp, P.U32.eq_of_is_eq(U32.and(255, pti), pti, ev), {==}, e, P.Bool.and_true_r(B.is_byte(pti), B.all_bytes(code <> r2), ab))

def SmMsg.sx_psi_ok(ok: Bool, +epd: U32, +psi: U32, +r: B.Bytes(), +m: Sm.Sm, e46: {epd == 46 : U32}, ev: {I.fits8(psi) == ok : Bool}, +e: {Sm.Sm.r_psi_ok(psi, r, ok) == Done{m} : SmMsg.Res()}, ab: {B.all_bytes(psi <> r) == True{} : Bool}) -> {Sm.Sm.write(m) == epd <> psi <> r : B.Bytes()}:
  match ok:
    case False{}:
      Empty.absurd({Sm.Sm.write(m) == epd <> psi <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Sm.Sm, B.Invalid{psi}, m, e))
    case True{}:
      match r:
        case Nil{}:
          Empty.absurd({Sm.Sm.write(m) == epd <> psi <> [] : B.Bytes()}, P.Refute.fail_done(B.Err, Sm.Sm, B.Short{}, m, e))
        case +pti <> +r2:
          SmMsg.sx_pti_ok(I.fits8(pti), epd, psi, pti, r2, m, e46, P.U32.eq_of_is_eq(U32.and(255, psi), psi, ev), {==}, e, P.Bool.and_true_r(B.is_byte(psi), B.all_bytes(pti <> r2), ab))

def SmMsg.sx_epd(ok: Bool, +epd: U32, +r: B.Bytes(), +m: Sm.Sm, ev: {U32.is_eq(epd, 46) == ok : Bool}, +e: {Sm.Sm.r_epd(r, epd, ok) == Done{m} : SmMsg.Res()}, ab: {B.all_bytes(epd <> r) == True{} : Bool}) -> {Sm.Sm.write(m) == epd <> r : B.Bytes()}:
  match ok:
    case False{}:
      Empty.absurd({Sm.Sm.write(m) == epd <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Sm.Sm, B.Invalid{epd}, m, e))
    case True{}:
      match r:
        case Nil{}:
          Empty.absurd({Sm.Sm.write(m) == [epd] : B.Bytes()}, P.Refute.fail_done(B.Err, Sm.Sm, B.Short{}, m, e))
        case +psi <> +r2:
          SmMsg.sx_psi_ok(I.fits8(psi), epd, psi, r2, m, P.U32.eq_of_is_eq(epd, 46, ev), {==}, e, P.Bool.and_true_r(B.is_byte(epd), B.all_bytes(psi <> r2), ab))

def SmMsg.sx(bs: B.Bytes(), +m: Sm.Sm, +e: {Sm.Sm.read(bs) == Done{m} : SmMsg.Res()}, ab: {B.all_bytes(bs) == True{} : Bool}) -> {Sm.Sm.write(m) == bs : B.Bytes()}:
  match bs:
    case Nil{}:
      Empty.absurd({Sm.Sm.write(m) == [] : B.Bytes()}, P.Refute.fail_done(B.Err, Sm.Sm, B.Short{}, m, e))
    case +epd <> +r:
      SmMsg.sx_epd(U32.is_eq(epd, 46), epd, r, m, {==}, e, ab)

def L.nas.sm.suffix(bs, m, e, ab):
  SmMsg.sx(bs, m, e, ab)
