import Base
import ../LAWS.bend as L
import ../bytes.bend as B
import ../nas/ie.bend as I
import ../nas/mm.bend as Mm
import ./lib.bend as P
import ./bytes.bend as PB

# Proofs of the 5GMM message laws (ticket 10).

def Opts.Res() -> Data:
  Result<&2, &2, B.Err, List<&2, I.Ie>>

def Msg.Res() -> Data:
  Result<&2, &2, B.Err, Mm.Mm>

def Fmt.eq_of_is_eq(a: I.Fmt, b: I.Fmt, e: {I.Fmt.eq(a, b) == True{} : Bool}) -> {a == b : I.Fmt}:
  match a b:
    case I.T1{} I.T1{}:
      {==}
    case I.T1{} I.Tv{n}:
      Empty.absurd({I.T1{} == I.Tv{n} : I.Fmt}, P.Refute.bool(e))
    case I.T1{} I.Tlv{}:
      Empty.absurd({I.T1{} == I.Tlv{} : I.Fmt}, P.Refute.bool(e))
    case I.T1{} I.TlvE{}:
      Empty.absurd({I.T1{} == I.TlvE{} : I.Fmt}, P.Refute.bool(e))
    case I.Tv{m} I.T1{}:
      Empty.absurd({I.Tv{m} == I.T1{} : I.Fmt}, P.Refute.bool(e))
    case I.Tv{m} I.Tv{n}:
      Equal.cong(Nat, I.Fmt, k => I.Tv{k}, m, n, P.Nat.eq_of_is_eq(m, n, e))
    case I.Tv{m} I.Tlv{}:
      Empty.absurd({I.Tv{m} == I.Tlv{} : I.Fmt}, P.Refute.bool(e))
    case I.Tv{m} I.TlvE{}:
      Empty.absurd({I.Tv{m} == I.TlvE{} : I.Fmt}, P.Refute.bool(e))
    case I.Tlv{} I.T1{}:
      Empty.absurd({I.Tlv{} == I.T1{} : I.Fmt}, P.Refute.bool(e))
    case I.Tlv{} I.Tv{n}:
      Empty.absurd({I.Tlv{} == I.Tv{n} : I.Fmt}, P.Refute.bool(e))
    case I.Tlv{} I.Tlv{}:
      {==}
    case I.Tlv{} I.TlvE{}:
      Empty.absurd({I.Tlv{} == I.TlvE{} : I.Fmt}, P.Refute.bool(e))
    case I.TlvE{} I.T1{}:
      Empty.absurd({I.TlvE{} == I.T1{} : I.Fmt}, P.Refute.bool(e))
    case I.TlvE{} I.Tv{n}:
      Empty.absurd({I.TlvE{} == I.Tv{n} : I.Fmt}, P.Refute.bool(e))
    case I.TlvE{} I.Tlv{}:
      Empty.absurd({I.TlvE{} == I.Tlv{} : I.Fmt}, P.Refute.bool(e))
    case I.TlvE{} I.TlvE{}:
      {==}

def List.nil_of_is_empty(xs: B.Bytes(), e: {List.is_empty(&2, U32, xs) == True{} : Bool}) -> {xs == [] : B.Bytes()}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      Empty.absurd({x <> t == [] : B.Bytes()}, P.Refute.bool(e))

# Message type codes are bytes and the type table inverts them.
def Type.code8(t: Mm.Mm.Type) -> {U32.and(255, Mm.Mm.Type.code(t)) == Mm.Mm.Type.code(t) : U32}:
  match t:
    case Mm.RegistrationRequest{}:
      {==}
    case Mm.RegistrationAccept{}:
      {==}
    case Mm.RegistrationComplete{}:
      {==}
    case Mm.RegistrationReject{}:
      {==}
    case Mm.DeregistrationRequestUe{}:
      {==}
    case Mm.DeregistrationAcceptUe{}:
      {==}
    case Mm.ConfigurationUpdateCommand{}:
      {==}
    case Mm.AuthenticationRequest{}:
      {==}
    case Mm.AuthenticationResponse{}:
      {==}
    case Mm.AuthenticationReject{}:
      {==}
    case Mm.AuthenticationFailure{}:
      {==}
    case Mm.IdentityRequest{}:
      {==}
    case Mm.IdentityResponse{}:
      {==}
    case Mm.SecurityModeCommand{}:
      {==}
    case Mm.SecurityModeComplete{}:
      {==}
    case Mm.SecurityModeReject{}:
      {==}
    case Mm.Status{}:
      {==}
    case Mm.UlNasTransport{}:
      {==}
    case Mm.DlNasTransport{}:
      {==}

def Type.of_code(t: Mm.Mm.Type) -> {Mm.Mm.Type.of(Mm.Mm.Type.code(t)) == Some{t} : Maybe<&2, Mm.Mm.Type>}:
  match t:
    case Mm.RegistrationRequest{}:
      {==}
    case Mm.RegistrationAccept{}:
      {==}
    case Mm.RegistrationComplete{}:
      {==}
    case Mm.RegistrationReject{}:
      {==}
    case Mm.DeregistrationRequestUe{}:
      {==}
    case Mm.DeregistrationAcceptUe{}:
      {==}
    case Mm.ConfigurationUpdateCommand{}:
      {==}
    case Mm.AuthenticationRequest{}:
      {==}
    case Mm.AuthenticationResponse{}:
      {==}
    case Mm.AuthenticationReject{}:
      {==}
    case Mm.AuthenticationFailure{}:
      {==}
    case Mm.IdentityRequest{}:
      {==}
    case Mm.IdentityResponse{}:
      {==}
    case Mm.SecurityModeCommand{}:
      {==}
    case Mm.SecurityModeComplete{}:
      {==}
    case Mm.SecurityModeReject{}:
      {==}
    case Mm.Status{}:
      {==}
    case Mm.UlNasTransport{}:
      {==}
    case Mm.DlNasTransport{}:
      {==}

# Length prefixes
# ---------------

def Len.rt(+len: U32, +body: B.Bytes(), +W: B.Bytes(), ok: Bool, eok: {ok == True{} : Bool}, tn: {U32.to_nat(len) == List.length(&2, U32, body) : Nat}) -> {I.Len.take(len, List.append(&2, U32, body, W), ok) == Done{(I.LenBody{len, body}, W)} : B.Read(I.LenBody)}:
  match ok:
    case False{}:
      Empty.absurd({I.Len.take(len, List.append(&2, U32, body, W), False{}) == Done{(I.LenBody{len, body}, W)} : B.Read(I.LenBody)}, P.Refute.bool(eok))
    case True{}:
      stn = Equal.sym(Nat, U32.to_nat(len), List.length(&2, U32, body), tn)
      %stn : {I.Len.join(len, B.take(_, List.append(&2, U32, body, W))) == Done{(I.LenBody{len, body}, W)} : B.Read(I.LenBody)}
      ta = Equal.sym(B.Read(B.Bytes()), B.take(List.length(&2, U32, body), List.append(&2, U32, body, W)), Done{(body, W)}, P.Take.append(body, W))
      %ta : {I.Len.join(len, _) == Done{(I.LenBody{len, body}, W)} : B.Read(I.LenBody)}
      {==}

# Mandatory fields
# ----------------

def Field.rt(lay: I.Lay, f: I.Field, +W: B.Bytes(), +v: {I.Field.valid(lay, f) == True{} : Bool}) -> {I.Field.read(lay, I.Field.write(f, W)) == Done{(f, W)} : B.Read(I.Field)}:
  match lay f:
    case I.V1{} I.FByte{+x}:
      mx = Equal.sym(U32, U32.and(255, x), x, P.U32.eq_of_is_eq(U32.and(255, x), x, v))
      %mx : {I.Field.byte_ok(_, W, I.fits8(_)) == Done{(I.FByte{x}, W)} : B.Read(I.Field)}
      sv = Equal.sym(Bool, I.fits8(x), True{}, v)
      %sv : {I.Field.byte_ok(x, W, _) == Done{(I.FByte{x}, W)} : B.Read(I.Field)}
      {==}
    case I.Lv{} I.FLv{I.LenBody{+len, +body}}:
      +fl = P.Bool.and_true_l(I.fits8(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v)
      tn = P.Nat.eq_of_is_eq(U32.to_nat(len), List.length(&2, U32, body), P.Bool.and_true_r(I.fits8(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v))
      ml = Equal.sym(U32, U32.and(255, len), len, P.U32.eq_of_is_eq(U32.and(255, len), len, fl))
      %ml : {I.Field.of_lv(I.Len.take(_, List.append(&2, U32, body, W), I.fits8(_))) == Done{(I.FLv{I.LenBody{len, body}}, W)} : B.Read(I.Field)}
      lr = Equal.sym(B.Read(I.LenBody), I.Len.take(len, List.append(&2, U32, body, W), I.fits8(len)), Done{(I.LenBody{len, body}, W)}, Len.rt(len, body, W, I.fits8(len), fl, tn))
      %lr : {I.Field.of_lv(_) == Done{(I.FLv{I.LenBody{len, body}}, W)} : B.Read(I.Field)}
      {==}
    case I.LvE{} I.FLvE{I.LenBody{+len, +body}}:
      +fl = P.Bool.and_true_l(I.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v)
      tn = P.Nat.eq_of_is_eq(U32.to_nat(len), List.length(&2, U32, body), P.Bool.and_true_r(I.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v))
      ru = Equal.sym(B.Read(U32), B.u16(B.write_u16(len, List.append(&2, U32, body, W))), Done{(len, List.append(&2, U32, body, W))}, L.bytes.u16.roundtrip(len, List.append(&2, U32, body, W), P.U32.eq_of_is_eq(U32.and(65535, len), len, fl)))
      %ru : {I.Field.of_lve(I.Lve.body(_)) == Done{(I.FLvE{I.LenBody{len, body}}, W)} : B.Read(I.Field)}
      lr = Equal.sym(B.Read(I.LenBody), I.Len.take(len, List.append(&2, U32, body, W), I.fits16(len)), Done{(I.LenBody{len, body}, W)}, Len.rt(len, body, W, I.fits16(len), fl, tn))
      %lr : {I.Field.of_lve(_) == Done{(I.FLvE{I.LenBody{len, body}}, W)} : B.Read(I.Field)}
      {==}
    case I.V1{} I.FLv{lb}:
      Empty.absurd({I.Field.read(I.V1{}, I.Field.write(I.FLv{lb}, W)) == Done{(I.FLv{lb}, W)} : B.Read(I.Field)}, P.Refute.bool(v))
    case I.V1{} I.FLvE{lb}:
      Empty.absurd({I.Field.read(I.V1{}, I.Field.write(I.FLvE{lb}, W)) == Done{(I.FLvE{lb}, W)} : B.Read(I.Field)}, P.Refute.bool(v))
    case I.Lv{} I.FByte{x}:
      Empty.absurd({I.Field.read(I.Lv{}, I.Field.write(I.FByte{x}, W)) == Done{(I.FByte{x}, W)} : B.Read(I.Field)}, P.Refute.bool(v))
    case I.Lv{} I.FLvE{lb}:
      Empty.absurd({I.Field.read(I.Lv{}, I.Field.write(I.FLvE{lb}, W)) == Done{(I.FLvE{lb}, W)} : B.Read(I.Field)}, P.Refute.bool(v))
    case I.LvE{} I.FByte{x}:
      Empty.absurd({I.Field.read(I.LvE{}, I.Field.write(I.FByte{x}, W)) == Done{(I.FByte{x}, W)} : B.Read(I.Field)}, P.Refute.bool(v))
    case I.LvE{} I.FLv{lb}:
      Empty.absurd({I.Field.read(I.LvE{}, I.Field.write(I.FLv{lb}, W)) == Done{(I.FLv{lb}, W)} : B.Read(I.Field)}, P.Refute.bool(v))

def Fields.rt(lays: List<&2, I.Lay>, fs: List<&2, I.Field>, +rest: B.Bytes(), +v: {I.Fields.valid(lays, fs) == True{} : Bool}) -> {I.Fields.read(lays, I.Fields.write(fs, rest)) == Done{(fs, rest)} : B.Read(List<&2, I.Field>)}:
  match lays fs:
    case Nil{} Nil{}:
      {==}
    case Nil{} f <> fr:
      Empty.absurd({I.Fields.read([], I.Fields.write(f <> fr, rest)) == Done{(f <> fr, rest)} : B.Read(List<&2, I.Field>)}, P.Refute.bool(v))
    case l <> ls Nil{}:
      Empty.absurd({I.Fields.read(l <> ls, I.Fields.write([], rest)) == Done{([], rest)} : B.Read(List<&2, I.Field>)}, P.Refute.bool(v))
    case +l <> +ls +f <> +fr:
      fr1 = Equal.sym(B.Read(I.Field), I.Field.read(l, I.Field.write(f, I.Fields.write(fr, rest))), Done{(f, I.Fields.write(fr, rest))}, Field.rt(l, f, I.Fields.write(fr, rest), P.Bool.and_true_l(I.Field.valid(l, f), I.Fields.valid(ls, fr), v)))
      %fr1 : {I.Fields.next(_, r => I.Fields.read(ls, r)) == Done{(f <> fr, rest)} : B.Read(List<&2, I.Field>)}
      ih = Equal.sym(B.Read(List<&2, I.Field>), I.Fields.read(ls, I.Fields.write(fr, rest)), Done{(fr, rest)}, Fields.rt(ls, fr, rest, P.Bool.and_true_r(I.Field.valid(l, f), I.Fields.valid(ls, fr), v)))
      %ih : {I.Fields.cons(f, _) == Done{(f <> fr, rest)} : B.Read(List<&2, I.Field>)}
      {==}

# Optional IEs
# ------------

def Opts.step_t1(+f: Nat, +t: Mm.Mm.Type, +iei: U32, +len: U32, +body: B.Bytes(), +R: B.Bytes(), ok: Bool, eok: {ok == True{} : Bool}, fe: {I.T1{} == Mm.Mm.format(t, iei) : I.Fmt}, l0: {len == 0 : U32}, b0: {body == [] : B.Bytes()}) -> {Mm.Opts.iei(t, iei, R, left => Mm.Opts.read(f, t, left), ok) == Mm.Opts.cons(I.Ie{iei, I.T1{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}:
  match ok:
    case False{}:
      Empty.absurd({Mm.Opts.iei(t, iei, R, left => Mm.Opts.read(f, t, left), False{}) == Mm.Opts.cons(I.Ie{iei, I.T1{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}, P.Refute.bool(eok))
    case True{}:
      %fe : {Mm.Opts.next(I.Ie.read_body(iei, _, R), left => Mm.Opts.read(f, t, left)) == Mm.Opts.cons(I.Ie{iei, I.T1{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      %l0 : {Mm.Opts.cons(I.Ie{iei, I.T1{}, _, []}, Mm.Opts.read(f, t, R)) == Mm.Opts.cons(I.Ie{iei, I.T1{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      %b0 : {Mm.Opts.cons(I.Ie{iei, I.T1{}, len, _}, Mm.Opts.read(f, t, R)) == Mm.Opts.cons(I.Ie{iei, I.T1{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      {==}

def Opts.step_tv(+f: Nat, +t: Mm.Mm.Type, +iei: U32, +n: Nat, +len: U32, +body: B.Bytes(), +R: B.Bytes(), ok: Bool, eok: {ok == True{} : Bool}, fe: {I.Tv{n} == Mm.Mm.format(t, iei) : I.Fmt}, ln: {List.length(&2, U32, body) == n : Nat}, l0: {len == 0 : U32}) -> {Mm.Opts.iei(t, iei, List.append(&2, U32, body, R), left => Mm.Opts.read(f, t, left), ok) == Mm.Opts.cons(I.Ie{iei, I.Tv{n}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}:
  match ok:
    case False{}:
      Empty.absurd({Mm.Opts.iei(t, iei, List.append(&2, U32, body, R), left => Mm.Opts.read(f, t, left), False{}) == Mm.Opts.cons(I.Ie{iei, I.Tv{n}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}, P.Refute.bool(eok))
    case True{}:
      %fe : {Mm.Opts.next(I.Ie.read_body(iei, _, List.append(&2, U32, body, R)), left => Mm.Opts.read(f, t, left)) == Mm.Opts.cons(I.Ie{iei, I.Tv{n}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      %ln : {Mm.Opts.next(I.Ie.of_tv(iei, _, B.take(_, List.append(&2, U32, body, R))), left => Mm.Opts.read(f, t, left)) == Mm.Opts.cons(I.Ie{iei, I.Tv{_}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      ta = Equal.sym(B.Read(B.Bytes()), B.take(List.length(&2, U32, body), List.append(&2, U32, body, R)), Done{(body, R)}, P.Take.append(body, R))
      %ta : {Mm.Opts.next(I.Ie.of_tv(iei, List.length(&2, U32, body), _), left => Mm.Opts.read(f, t, left)) == Mm.Opts.cons(I.Ie{iei, I.Tv{List.length(&2, U32, body)}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      %l0 : {Mm.Opts.cons(I.Ie{iei, I.Tv{List.length(&2, U32, body)}, _, body}, Mm.Opts.read(f, t, R)) == Mm.Opts.cons(I.Ie{iei, I.Tv{List.length(&2, U32, body)}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      {==}

def Opts.step_tlv(+f: Nat, +t: Mm.Mm.Type, +iei: U32, +len: U32, +body: B.Bytes(), +R: B.Bytes(), ok: Bool, eok: {ok == True{} : Bool}, fe: {I.Tlv{} == Mm.Mm.format(t, iei) : I.Fmt}, lr: {I.Len.take(len, List.append(&2, U32, body, R), I.fits8(len)) == Done{(I.LenBody{len, body}, R)} : B.Read(I.LenBody)}) -> {Mm.Opts.iei(t, iei, len <> List.append(&2, U32, body, R), left => Mm.Opts.read(f, t, left), ok) == Mm.Opts.cons(I.Ie{iei, I.Tlv{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}:
  match ok:
    case False{}:
      Empty.absurd({Mm.Opts.iei(t, iei, len <> List.append(&2, U32, body, R), left => Mm.Opts.read(f, t, left), False{}) == Mm.Opts.cons(I.Ie{iei, I.Tlv{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}, P.Refute.bool(eok))
    case True{}:
      %fe : {Mm.Opts.next(I.Ie.read_body(iei, _, len <> List.append(&2, U32, body, R)), left => Mm.Opts.read(f, t, left)) == Mm.Opts.cons(I.Ie{iei, I.Tlv{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      slr = Equal.sym(B.Read(I.LenBody), I.Len.take(len, List.append(&2, U32, body, R), I.fits8(len)), Done{(I.LenBody{len, body}, R)}, lr)
      %slr : {Mm.Opts.next(I.Ie.of_len(iei, I.Tlv{}, _), left => Mm.Opts.read(f, t, left)) == Mm.Opts.cons(I.Ie{iei, I.Tlv{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      {==}

def Opts.step_tlve(+f: Nat, +t: Mm.Mm.Type, +iei: U32, +len: U32, +body: B.Bytes(), +R: B.Bytes(), ok: Bool, eok: {ok == True{} : Bool}, fe: {I.TlvE{} == Mm.Mm.format(t, iei) : I.Fmt}, ru: {B.u16(B.write_u16(len, List.append(&2, U32, body, R))) == Done{(len, List.append(&2, U32, body, R))} : B.Read(U32)}, lr: {I.Len.take(len, List.append(&2, U32, body, R), I.fits16(len)) == Done{(I.LenBody{len, body}, R)} : B.Read(I.LenBody)}) -> {Mm.Opts.iei(t, iei, B.write_u16(len, List.append(&2, U32, body, R)), left => Mm.Opts.read(f, t, left), ok) == Mm.Opts.cons(I.Ie{iei, I.TlvE{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}:
  match ok:
    case False{}:
      Empty.absurd({Mm.Opts.iei(t, iei, B.write_u16(len, List.append(&2, U32, body, R)), left => Mm.Opts.read(f, t, left), False{}) == Mm.Opts.cons(I.Ie{iei, I.TlvE{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}, P.Refute.bool(eok))
    case True{}:
      %fe : {Mm.Opts.next(I.Ie.read_body(iei, _, B.write_u16(len, List.append(&2, U32, body, R))), left => Mm.Opts.read(f, t, left)) == Mm.Opts.cons(I.Ie{iei, I.TlvE{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      sru = Equal.sym(B.Read(U32), B.u16(B.write_u16(len, List.append(&2, U32, body, R))), Done{(len, List.append(&2, U32, body, R))}, ru)
      %sru : {Mm.Opts.next(I.Ie.of_len(iei, I.TlvE{}, I.Lve.body(_)), left => Mm.Opts.read(f, t, left)) == Mm.Opts.cons(I.Ie{iei, I.TlvE{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      slr = Equal.sym(B.Read(I.LenBody), I.Len.take(len, List.append(&2, U32, body, R), I.fits16(len)), Done{(I.LenBody{len, body}, R)}, lr)
      %slr : {Mm.Opts.next(I.Ie.of_len(iei, I.TlvE{}, _), left => Mm.Opts.read(f, t, left)) == Mm.Opts.cons(I.Ie{iei, I.TlvE{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      {==}

# One valid optional IE reads back from its encoding and leaves the rest.
def Opts.step(+f: Nat, +t: Mm.Mm.Type, +iei: U32, fmt: I.Fmt, +len: U32, +body: B.Bytes(), +R: B.Bytes(), +v: {I.Ie.valid(Mm.Mm.format(t, iei), I.Ie{iei, fmt, len, body}) == True{} : Bool}) -> {Mm.Opts.read(1n+f, t, I.Ie.write(I.Ie{iei, fmt, len, body}, R)) == Mm.Opts.cons(I.Ie{iei, fmt, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}:
  match fmt:
    case I.T1{}:
      fe = Fmt.eq_of_is_eq(I.T1{}, Mm.Mm.format(t, iei), P.Bool.and_true_l(I.Fmt.eq(I.T1{}, Mm.Mm.format(t, iei)), Bool.and(I.fits8(iei), I.Ie.valid_body(I.T1{}, iei, len, body)), v))
      +r1 = P.Bool.and_true_r(I.Fmt.eq(I.T1{}, Mm.Mm.format(t, iei)), Bool.and(I.fits8(iei), I.Ie.valid_body(I.T1{}, iei, len, body)), v)
      +f8 = P.Bool.and_true_l(I.fits8(iei), I.Ie.valid_body(I.T1{}, iei, len, body), r1)
      +rr = P.Bool.and_true_r(U32.is_ge(iei, 128), Bool.and(List.is_empty(&2, U32, body), U32.is_eq(len, 0)), P.Bool.and_true_r(I.fits8(iei), I.Ie.valid_body(I.T1{}, iei, len, body), r1))
      b0 = List.nil_of_is_empty(body, P.Bool.and_true_l(List.is_empty(&2, U32, body), U32.is_eq(len, 0), rr))
      l0 = P.U32.eq_of_is_eq(len, 0, P.Bool.and_true_r(List.is_empty(&2, U32, body), U32.is_eq(len, 0), rr))
      mi = Equal.sym(U32, U32.and(255, iei), iei, P.U32.eq_of_is_eq(U32.and(255, iei), iei, f8))
      %mi : {Mm.Opts.iei(t, _, R, left => Mm.Opts.read(f, t, left), I.fits8(_)) == Mm.Opts.cons(I.Ie{iei, I.T1{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      Opts.step_t1(f, t, iei, len, body, R, I.fits8(iei), f8, fe, l0, b0)
    case I.Tv{+n}:
      fe = Fmt.eq_of_is_eq(I.Tv{n}, Mm.Mm.format(t, iei), P.Bool.and_true_l(I.Fmt.eq(I.Tv{n}, Mm.Mm.format(t, iei)), Bool.and(I.fits8(iei), I.Ie.valid_body(I.Tv{n}, iei, len, body)), v))
      +r1 = P.Bool.and_true_r(I.Fmt.eq(I.Tv{n}, Mm.Mm.format(t, iei)), Bool.and(I.fits8(iei), I.Ie.valid_body(I.Tv{n}, iei, len, body)), v)
      +f8 = P.Bool.and_true_l(I.fits8(iei), I.Ie.valid_body(I.Tv{n}, iei, len, body), r1)
      +rr = P.Bool.and_true_r(U32.is_lt(iei, 128), Bool.and(Nat.is_eq(List.length(&2, U32, body), n), U32.is_eq(len, 0)), P.Bool.and_true_r(I.fits8(iei), I.Ie.valid_body(I.Tv{n}, iei, len, body), r1))
      ln = P.Nat.eq_of_is_eq(List.length(&2, U32, body), n, P.Bool.and_true_l(Nat.is_eq(List.length(&2, U32, body), n), U32.is_eq(len, 0), rr))
      l0 = P.U32.eq_of_is_eq(len, 0, P.Bool.and_true_r(Nat.is_eq(List.length(&2, U32, body), n), U32.is_eq(len, 0), rr))
      mi = Equal.sym(U32, U32.and(255, iei), iei, P.U32.eq_of_is_eq(U32.and(255, iei), iei, f8))
      %mi : {Mm.Opts.iei(t, _, List.append(&2, U32, body, R), left => Mm.Opts.read(f, t, left), I.fits8(_)) == Mm.Opts.cons(I.Ie{iei, I.Tv{n}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      Opts.step_tv(f, t, iei, n, len, body, R, I.fits8(iei), f8, fe, ln, l0)
    case I.Tlv{}:
      fe = Fmt.eq_of_is_eq(I.Tlv{}, Mm.Mm.format(t, iei), P.Bool.and_true_l(I.Fmt.eq(I.Tlv{}, Mm.Mm.format(t, iei)), Bool.and(I.fits8(iei), I.Ie.valid_body(I.Tlv{}, iei, len, body)), v))
      +r1 = P.Bool.and_true_r(I.Fmt.eq(I.Tlv{}, Mm.Mm.format(t, iei)), Bool.and(I.fits8(iei), I.Ie.valid_body(I.Tlv{}, iei, len, body)), v)
      +f8 = P.Bool.and_true_l(I.fits8(iei), I.Ie.valid_body(I.Tlv{}, iei, len, body), r1)
      +v8 = P.Bool.and_true_r(U32.is_lt(iei, 128), I.LenBody.valid8(I.LenBody{len, body}), P.Bool.and_true_r(I.fits8(iei), I.Ie.valid_body(I.Tlv{}, iei, len, body), r1))
      +fl = P.Bool.and_true_l(I.fits8(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v8)
      tn = P.Nat.eq_of_is_eq(U32.to_nat(len), List.length(&2, U32, body), P.Bool.and_true_r(I.fits8(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v8))
      mi = Equal.sym(U32, U32.and(255, iei), iei, P.U32.eq_of_is_eq(U32.and(255, iei), iei, f8))
      ml = Equal.sym(U32, U32.and(255, len), len, P.U32.eq_of_is_eq(U32.and(255, len), len, fl))
      %mi : {Mm.Opts.iei(t, _, U32.and(255, len) <> List.append(&2, U32, body, R), left => Mm.Opts.read(f, t, left), I.fits8(_)) == Mm.Opts.cons(I.Ie{iei, I.Tlv{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      %ml : {Mm.Opts.iei(t, iei, _ <> List.append(&2, U32, body, R), left => Mm.Opts.read(f, t, left), I.fits8(iei)) == Mm.Opts.cons(I.Ie{iei, I.Tlv{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      Opts.step_tlv(f, t, iei, len, body, R, I.fits8(iei), f8, fe, Len.rt(len, body, R, I.fits8(len), fl, tn))
    case I.TlvE{}:
      fe = Fmt.eq_of_is_eq(I.TlvE{}, Mm.Mm.format(t, iei), P.Bool.and_true_l(I.Fmt.eq(I.TlvE{}, Mm.Mm.format(t, iei)), Bool.and(I.fits8(iei), I.Ie.valid_body(I.TlvE{}, iei, len, body)), v))
      +r1 = P.Bool.and_true_r(I.Fmt.eq(I.TlvE{}, Mm.Mm.format(t, iei)), Bool.and(I.fits8(iei), I.Ie.valid_body(I.TlvE{}, iei, len, body)), v)
      +f8 = P.Bool.and_true_l(I.fits8(iei), I.Ie.valid_body(I.TlvE{}, iei, len, body), r1)
      +v16 = P.Bool.and_true_r(U32.is_lt(iei, 128), I.LenBody.valid16(I.LenBody{len, body}), P.Bool.and_true_r(I.fits8(iei), I.Ie.valid_body(I.TlvE{}, iei, len, body), r1))
      +fl = P.Bool.and_true_l(I.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v16)
      tn = P.Nat.eq_of_is_eq(U32.to_nat(len), List.length(&2, U32, body), P.Bool.and_true_r(I.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), v16))
      mi = Equal.sym(U32, U32.and(255, iei), iei, P.U32.eq_of_is_eq(U32.and(255, iei), iei, f8))
      %mi : {Mm.Opts.iei(t, _, B.write_u16(len, List.append(&2, U32, body, R)), left => Mm.Opts.read(f, t, left), I.fits8(_)) == Mm.Opts.cons(I.Ie{iei, I.TlvE{}, len, body}, Mm.Opts.read(f, t, R)) : Opts.Res()}
      Opts.step_tlve(f, t, iei, len, body, R, I.fits8(iei), f8, fe, L.bytes.u16.roundtrip(len, List.append(&2, U32, body, R), P.U32.eq_of_is_eq(U32.and(65535, len), len, fl)), Len.rt(len, body, R, I.fits16(len), fl, tn))

# Every IE takes at least one byte.
def Ie.write_pos(ie: I.Ie, +W: B.Bytes(), e: {Nat.is_le(List.length(&2, U32, I.Ie.write(ie, W)), 0n) == True{} : Bool}) -> Empty:
  match ie:
    case I.Ie{iei, fmt, len, body}:
      match fmt:
        case I.T1{}:
          P.Refute.bool(e)
        case I.Tv{n}:
          P.Refute.bool(e)
        case I.Tlv{}:
          P.Refute.bool(e)
        case I.TlvE{}:
          P.Refute.bool(e)

def Ie.write_bound(ie: I.Ie, +W: B.Bytes(), +f: Nat, e: {Nat.is_le(List.length(&2, U32, I.Ie.write(ie, W)), 1n+f) == True{} : Bool}) -> {Nat.is_le(List.length(&2, U32, W), f) == True{} : Bool}:
  match ie:
    case I.Ie{iei, fmt, len, +body}:
      match fmt:
        case I.T1{}:
          e
        case I.Tv{n}:
          P.Nat.le_of_append(body, W, 0n, f, e)
        case I.Tlv{}:
          P.Nat.le_of_append(body, W, 1n, f, e)
        case I.TlvE{}:
          P.Nat.le_of_append(body, W, 2n, f, e)

def Opts.rt(+t: Mm.Mm.Type, opts: List<&2, I.Ie>, fuel: Nat, +v: {Mm.Opts.valid(t, opts) == True{} : Bool}, +bound: {Nat.is_le(List.length(&2, U32, I.Ies.write(opts, [])), fuel) == True{} : Bool}) -> {Mm.Opts.read(fuel, t, I.Ies.write(opts, [])) == Done{opts} : Opts.Res()}:
  match opts fuel:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+f:
      {==}
    case I.Ie{+iei, +fmt, +len, +body} <> +more 0n:
      Empty.absurd({Mm.Opts.read(0n, t, I.Ies.write(I.Ie{iei, fmt, len, body} <> more, [])) == Done{I.Ie{iei, fmt, len, body} <> more} : Opts.Res()}, Ie.write_pos(I.Ie{iei, fmt, len, body}, I.Ies.write(more, []), bound))
    case I.Ie{+iei, +fmt, +len, +body} <> +more 1n++f:
      +W = I.Ies.write(more, [])
      st = Equal.sym(Opts.Res(), Mm.Opts.read(1n+f, t, I.Ie.write(I.Ie{iei, fmt, len, body}, W)), Mm.Opts.cons(I.Ie{iei, fmt, len, body}, Mm.Opts.read(f, t, W)), Opts.step(f, t, iei, fmt, len, body, W, P.Bool.and_true_l(I.Ie.valid(Mm.Mm.format(t, iei), I.Ie{iei, fmt, len, body}), Mm.Opts.valid(t, more), v)))
      %st : {_ == Done{I.Ie{iei, fmt, len, body} <> more} : Opts.Res()}
      ih = Equal.sym(Opts.Res(), Mm.Opts.read(f, t, W), Done{more}, Opts.rt(t, more, f, P.Bool.and_true_r(I.Ie.valid(Mm.Mm.format(t, iei), I.Ie{iei, fmt, len, body}), Mm.Opts.valid(t, more), v), Ie.write_bound(I.Ie{iei, fmt, len, body}, W, f, bound)))
      %ih : {Mm.Opts.cons(I.Ie{iei, fmt, len, body}, _) == Done{I.Ie{iei, fmt, len, body} <> more} : Opts.Res()}
      {==}

# Roundtrip
# ---------

def Msg.rt(+mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +opts: List<&2, I.Ie>, +v: {Mm.Mm.valid(Mm.Mm{mt, fields, opts}) == True{} : Bool}) -> {Mm.Mm.read(Mm.Mm.write(Mm.Mm{mt, fields, opts})) == Done{Mm.Mm{mt, fields, opts}} : Msg.Res()}:
  +W = I.Ies.write(opts, [])
  +F = I.Fields.write(fields, W)
  sc = Equal.sym(U32, U32.and(255, Mm.Mm.Type.code(mt)), Mm.Mm.Type.code(mt), Type.code8(mt))
  %sc : {Mm.Mm.r_type(_, F, Mm.Mm.Type.of(_)) == Done{Mm.Mm{mt, fields, opts}} : Msg.Res()}
  so = Equal.sym(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type.of(Mm.Mm.Type.code(mt)), Some{mt}, Type.of_code(mt))
  %so : {Mm.Mm.r_type(Mm.Mm.Type.code(mt), F, _) == Done{Mm.Mm{mt, fields, opts}} : Msg.Res()}
  fr = Equal.sym(B.Read(List<&2, I.Field>), I.Fields.read(Mm.Mm.layout(mt), F), Done{(fields, W)}, Fields.rt(Mm.Mm.layout(mt), fields, W, P.Bool.and_true_l(I.Fields.valid(Mm.Mm.layout(mt), fields), Mm.Opts.valid(mt, opts), v)))
  %fr : {Mm.Mm.r_fields(mt, _) == Done{Mm.Mm{mt, fields, opts}} : Msg.Res()}
  orr = Equal.sym(Opts.Res(), Mm.Opts.read(List.length(&2, U32, W), mt, W), Done{opts}, Opts.rt(mt, opts, List.length(&2, U32, W), P.Bool.and_true_r(I.Fields.valid(Mm.Mm.layout(mt), fields), Mm.Opts.valid(mt, opts), v), P.Nat.le_refl(List.length(&2, U32, W))))
  %orr : {Mm.Mm.r_opts(mt, fields, _) == Done{Mm.Mm{mt, fields, opts}} : Msg.Res()}
  {==}

def L.nas.mm.roundtrip(m, v):
  match m:
    case Mm.Mm{+mt, +fields, +opts}:
      Msg.rt(mt, fields, opts, v)

# Decoding gives valid values
# ---------------------------

def Fmt.not_t1(f: I.Fmt) -> Type:
  match f:
    case I.T1{}:
      Empty
    case I.Tv{n}:
      Unit
    case I.Tlv{}:
      Unit
    case I.TlvE{}:
      Unit

def Fmt.of_low_ne_t1(l: I.Low, e: {I.Fmt.of_low(l) == I.T1{} : I.Fmt}) -> Empty:
  match l:
    case I.LowTv{n}:
      %e : Fmt.not_t1(_)
      Unit{}
    case I.LowTlv{}:
      %e : Fmt.not_t1(_)
      Unit{}
    case I.LowTlvE{}:
      %e : Fmt.not_t1(_)
      Unit{}

# A one-octet format means an IEI of 0x80 or more; any other format means less.
def Format.go_t1(+t: Mm.Mm.Type, +n: Nat, oo: Bool, e: {Mm.Mm.format.go(t, n, oo) == I.T1{} : I.Fmt}) -> {oo == True{} : Bool}:
  match oo:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Fmt.of_low_ne_t1(Mm.Mm.format.low(t, n), e))

def Format.t1(+t: Mm.Mm.Type, +iei: U32, e: {Mm.Mm.format(t, iei) == I.T1{} : I.Fmt}) -> {U32.is_ge(iei, 128) == True{} : Bool}:
  Format.go_t1(t, U32.to_nat(iei), U32.is_ge(iei, 128), e)

def Format.go_low(+t: Mm.Mm.Type, +n: Nat, oo: Bool, +x: I.Fmt, e: {Mm.Mm.format.go(t, n, oo) == x : I.Fmt}, nt: Fmt.not_t1(x)) -> {oo == False{} : Bool}:
  match oo:
    case False{}:
      {==}
    case True{}:
      se = Equal.sym(I.Fmt, I.T1{}, x, e)
      Empty.absurd({True{} == False{} : Bool}, (%se : Fmt.not_t1(_); nt))

def Format.low(+t: Mm.Mm.Type, +iei: U32, +x: I.Fmt, e: {Mm.Mm.format(t, iei) == x : I.Fmt}, nt: Fmt.not_t1(x)) -> {U32.is_lt(iei, 128) == True{} : Bool}:
  P.U32.lt_of_not_ge(iei, 128, Format.go_low(t, U32.to_nat(iei), U32.is_ge(iei, 128), x, e, nt))

# What take read has the length it was asked for.
def Take.len_eq.go(+n: Nat, +body: B.Bytes(), +r: B.Bytes(), +rest: B.Bytes(), la: {List.length(&2, U32, body) == n : Nat} & {List.append(&2, U32, body, rest) == r : B.Bytes()}) -> {Nat.is_eq(List.length(&2, U32, body), n) == True{} : Bool}:
  (l, a) = la
  sl = Equal.sym(Nat, List.length(&2, U32, body), n, l)
  %sl : {Nat.is_eq(_, n) == True{} : Bool}
  P.Nat.is_eq_refl(n)

def Take.len_eq(+n: Nat, +r: B.Bytes(), +body: B.Bytes(), +rest: B.Bytes(), e: {B.take(n, r) == Done{(body, rest)} : B.Read(B.Bytes())}) -> {Nat.is_eq(List.length(&2, U32, body), n) == True{} : Bool}:
  Take.len_eq.go(n, body, r, rest, L.bytes.take.length(n, r, body, rest, e))

def Take.len_eq2.go(+n: Nat, +body: B.Bytes(), +r: B.Bytes(), +rest: B.Bytes(), la: {List.length(&2, U32, body) == n : Nat} & {List.append(&2, U32, body, rest) == r : B.Bytes()}) -> {Nat.is_eq(n, List.length(&2, U32, body)) == True{} : Bool}:
  (l, a) = la
  sl = Equal.sym(Nat, List.length(&2, U32, body), n, l)
  %sl : {Nat.is_eq(n, _) == True{} : Bool}
  P.Nat.is_eq_refl(n)

def Take.len_eq2(+n: Nat, +r: B.Bytes(), +body: B.Bytes(), +rest: B.Bytes(), e: {B.take(n, r) == Done{(body, rest)} : B.Read(B.Bytes())}) -> {Nat.is_eq(n, List.length(&2, U32, body)) == True{} : Bool}:
  Take.len_eq2.go(n, body, r, rest, L.bytes.take.length(n, r, body, rest, e))

def Len.dv8_join(+len: U32, +r: B.Bytes(), +lb: I.LenBody, +rest: B.Bytes(), +rt: B.Read(B.Bytes()), ert: {B.take(U32.to_nat(len), r) == rt : B.Read(B.Bytes())}, e: {I.Len.join(len, rt) == Done{(lb, rest)} : B.Read(I.LenBody)}, fl: {I.fits8(len) == True{} : Bool}) -> {I.LenBody.valid8(lb) == True{} : Bool}:
  match rt:
    case Fail{err}:
      Empty.absurd({I.LenBody.valid8(lb) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), err, (lb, rest), e))
    case Done{(+body, rest2)}:
      el = Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, lb), Done{(I.LenBody{len, body}, rest2)}, Done{(lb, rest)}, e)
      %el : {I.LenBody.valid8(_) == True{} : Bool}
      P.Bool.and_intro(I.fits8(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), fl, Take.len_eq2(U32.to_nat(len), r, body, rest2, ert))

def Len.dv8(+len: U32, +r: B.Bytes(), +lb: I.LenBody, +rest: B.Bytes(), ok: Bool, ev: {I.fits8(len) == ok : Bool}, e: {I.Len.take(len, r, ok) == Done{(lb, rest)} : B.Read(I.LenBody)}) -> {I.LenBody.valid8(lb) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({I.LenBody.valid8(lb) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Invalid{len}, (lb, rest), e))
    case True{}:
      Len.dv8_join(len, r, lb, rest, B.take(U32.to_nat(len), r), {==}, e, ev)

def Len.dv16_join(+len: U32, +r: B.Bytes(), +lb: I.LenBody, +rest: B.Bytes(), +rt: B.Read(B.Bytes()), ert: {B.take(U32.to_nat(len), r) == rt : B.Read(B.Bytes())}, e: {I.Len.join(len, rt) == Done{(lb, rest)} : B.Read(I.LenBody)}, fl: {I.fits16(len) == True{} : Bool}) -> {I.LenBody.valid16(lb) == True{} : Bool}:
  match rt:
    case Fail{err}:
      Empty.absurd({I.LenBody.valid16(lb) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), err, (lb, rest), e))
    case Done{(+body, rest2)}:
      el = Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, lb), Done{(I.LenBody{len, body}, rest2)}, Done{(lb, rest)}, e)
      %el : {I.LenBody.valid16(_) == True{} : Bool}
      P.Bool.and_intro(I.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, body)), fl, Take.len_eq2(U32.to_nat(len), r, body, rest2, ert))

def Len.dv16(+len: U32, +r: B.Bytes(), +lb: I.LenBody, +rest: B.Bytes(), ok: Bool, ev: {I.fits16(len) == ok : Bool}, e: {I.Len.take(len, r, ok) == Done{(lb, rest)} : B.Read(I.LenBody)}) -> {I.LenBody.valid16(lb) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({I.LenBody.valid16(lb) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Invalid{len}, (lb, rest), e))
    case True{}:
      Len.dv16_join(len, r, lb, rest, B.take(U32.to_nat(len), r), {==}, e, ev)

def Lv.dv(+bs: B.Bytes(), +lb: I.LenBody, +rest: B.Bytes(), e: {I.lv(bs) == Done{(lb, rest)} : B.Read(I.LenBody)}) -> {I.LenBody.valid8(lb) == True{} : Bool}:
  match bs:
    case Nil{}:
      Empty.absurd({I.LenBody.valid8(lb) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Short{}, (lb, rest), e))
    case +len <> r:
      Len.dv8(len, r, lb, rest, I.fits8(len), {==}, e)

def Lve.dv(+bs: B.Bytes(), +lb: I.LenBody, +rest: B.Bytes(), e: {I.lve(bs) == Done{(lb, rest)} : B.Read(I.LenBody)}) -> {I.LenBody.valid16(lb) == True{} : Bool}:
  match bs:
    case Nil{}:
      Empty.absurd({I.LenBody.valid16(lb) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Short{}, (lb, rest), e))
    case b <> Nil{}:
      Empty.absurd({I.LenBody.valid16(lb) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Short{}, (lb, rest), e))
    case +b1 <> +b0 <> r:
      Len.dv16(B.cat8(b0, b1), r, lb, rest, I.fits16(B.cat8(b0, b1)), {==}, e)

def Field.dv_byte(+b: U32, +r: B.Bytes(), +f: I.Field, +rest: B.Bytes(), ok: Bool, ev: {I.fits8(b) == ok : Bool}, e: {I.Field.byte_ok(b, r, ok) == Done{(f, rest)} : B.Read(I.Field)}) -> {I.Field.valid(I.V1{}, f) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({I.Field.valid(I.V1{}, f) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.Field), B.Invalid{b}, (f, rest), e))
    case True{}:
      ef = Equal.cong(B.Read(I.Field), I.Field, x => P.Read.value(I.Field, x, f), Done{(I.FByte{b}, r)}, Done{(f, rest)}, e)
      %ef : {I.Field.valid(I.V1{}, _) == True{} : Bool}
      ev

def Field.dv_lv(+rl: B.Read(I.LenBody), +f: I.Field, +rest: B.Bytes(), e: {I.Field.of_lv(rl) == Done{(f, rest)} : B.Read(I.Field)}, h: @lb: I.LenBody -> @r: B.Bytes() -> {rl == Done{(lb, r)} : B.Read(I.LenBody)} -> {I.LenBody.valid8(lb) == True{} : Bool}) -> {I.Field.valid(I.Lv{}, f) == True{} : Bool}:
  match rl:
    case Fail{err}:
      Empty.absurd({I.Field.valid(I.Lv{}, f) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.Field), err, (f, rest), e))
    case Done{(+lb, +r)}:
      ef = Equal.cong(B.Read(I.Field), I.Field, x => P.Read.value(I.Field, x, f), Done{(I.FLv{lb}, r)}, Done{(f, rest)}, e)
      %ef : {I.Field.valid(I.Lv{}, _) == True{} : Bool}
      h(lb, r, {==})

def Field.dv_lve(+rl: B.Read(I.LenBody), +f: I.Field, +rest: B.Bytes(), e: {I.Field.of_lve(rl) == Done{(f, rest)} : B.Read(I.Field)}, h: @lb: I.LenBody -> @r: B.Bytes() -> {rl == Done{(lb, r)} : B.Read(I.LenBody)} -> {I.LenBody.valid16(lb) == True{} : Bool}) -> {I.Field.valid(I.LvE{}, f) == True{} : Bool}:
  match rl:
    case Fail{err}:
      Empty.absurd({I.Field.valid(I.LvE{}, f) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.Field), err, (f, rest), e))
    case Done{(+lb, +r)}:
      ef = Equal.cong(B.Read(I.Field), I.Field, x => P.Read.value(I.Field, x, f), Done{(I.FLvE{lb}, r)}, Done{(f, rest)}, e)
      %ef : {I.Field.valid(I.LvE{}, _) == True{} : Bool}
      h(lb, r, {==})

def Field.dv(lay: I.Lay, +bs: B.Bytes(), +f: I.Field, +rest: B.Bytes(), e: {I.Field.read(lay, bs) == Done{(f, rest)} : B.Read(I.Field)}) -> {I.Field.valid(lay, f) == True{} : Bool}:
  match lay:
    case I.V1{}:
      match bs:
        case Nil{}:
          Empty.absurd({I.Field.valid(I.V1{}, f) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(I.Field), B.Short{}, (f, rest), e))
        case +b <> r:
          Field.dv_byte(b, r, f, rest, I.fits8(b), {==}, e)
    case I.Lv{}:
      Field.dv_lv(I.lv(bs), f, rest, e, lb => r => e2 => Lv.dv(bs, lb, r, e2))
    case I.LvE{}:
      Field.dv_lve(I.lve(bs), f, rest, e, lb => r => e2 => Lve.dv(bs, lb, r, e2))

def Fields.dv_cons(l: I.Lay, +ls: List<&2, I.Lay>, +f: I.Field, +r2: B.Read(List<&2, I.Field>), +fs: List<&2, I.Field>, +rest: B.Bytes(), e: {I.Fields.cons(f, r2) == Done{(fs, rest)} : B.Read(List<&2, I.Field>)}, hf: {I.Field.valid(l, f) == True{} : Bool}, h2: @fs2: List<&2, I.Field> -> @r: B.Bytes() -> {r2 == Done{(fs2, r)} : B.Read(List<&2, I.Field>)} -> {I.Fields.valid(ls, fs2) == True{} : Bool}) -> {I.Fields.valid(l <> ls, fs) == True{} : Bool}:
  match r2:
    case Fail{err}:
      Empty.absurd({I.Fields.valid(l <> ls, fs) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(List<&2, I.Field>), err, (fs, rest), e))
    case Done{(+fs2, +r)}:
      ef = Equal.cong(B.Read(List<&2, I.Field>), List<&2, I.Field>, x => P.Read.value(List<&2, I.Field>, x, fs), Done{(f <> fs2, r)}, Done{(fs, rest)}, e)
      %ef : {I.Fields.valid(l <> ls, _) == True{} : Bool}
      P.Bool.and_intro(I.Field.valid(l, f), I.Fields.valid(ls, fs2), hf, h2(fs2, r, {==}))

def Fields.dv_next(l: I.Lay, +ls: List<&2, I.Lay>, +r1: B.Read(I.Field), +fs: List<&2, I.Field>, +rest: B.Bytes(), e: {I.Fields.next(r1, r => I.Fields.read(ls, r)) == Done{(fs, rest)} : B.Read(List<&2, I.Field>)}, h1: @f: I.Field -> @r: B.Bytes() -> {r1 == Done{(f, r)} : B.Read(I.Field)} -> {I.Field.valid(l, f) == True{} : Bool}, h2: @bs2: B.Bytes() -> @fs2: List<&2, I.Field> -> @r: B.Bytes() -> {I.Fields.read(ls, bs2) == Done{(fs2, r)} : B.Read(List<&2, I.Field>)} -> {I.Fields.valid(ls, fs2) == True{} : Bool}) -> {I.Fields.valid(l <> ls, fs) == True{} : Bool}:
  match r1:
    case Fail{err}:
      Empty.absurd({I.Fields.valid(l <> ls, fs) == True{} : Bool}, P.Refute.fail_done(B.Err, B.ReadValue(List<&2, I.Field>), err, (fs, rest), e))
    case Done{(+f, +r)}:
      Fields.dv_cons(l, ls, f, I.Fields.read(ls, r), fs, rest, e, h1(f, r, {==}), fs2 => r3 => e2 => h2(r, fs2, r3, e2))

def Fields.dv(+lays: List<&2, I.Lay>, +bs: B.Bytes(), +fs: List<&2, I.Field>, +rest: B.Bytes(), e: {I.Fields.read(lays, bs) == Done{(fs, rest)} : B.Read(List<&2, I.Field>)}) -> {I.Fields.valid(lays, fs) == True{} : Bool}:
  match lays:
    case Nil{}:
      ef = Equal.cong(B.Read(List<&2, I.Field>), List<&2, I.Field>, x => P.Read.value(List<&2, I.Field>, x, fs), Done{([], bs)}, Done{(fs, rest)}, e)
      %ef : {I.Fields.valid([], _) == True{} : Bool}
      {==}
    case +l <> +ls:
      Fields.dv_next(l, ls, I.Field.read(l, bs), fs, rest, e, f => r => e2 => Field.dv(l, bs, f, r, e2), bs2 => fs2 => r => e2 => Fields.dv(ls, bs2, fs2, r, e2))

# A decoded optional IE is valid for the format its message assigns to it.
def Ie.Valid(+t: Mm.Mm.Type, +ie: I.Ie) -> Type:
  {I.Ie.valid(Mm.Mm.format(t, I.Ie.iei(ie)), ie) == True{} : Bool}

def Ie.dv_t1(+t: Mm.Mm.Type, +iei: U32, +r: B.Bytes(), +ie: I.Ie, +rest: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, +hx: {Mm.Mm.format(t, iei) == I.T1{} : I.Fmt}, e: {Done{(I.Ie{iei, I.T1{}, 0, []}, r)} == Done{(ie, rest)} : B.Read(I.Ie)}) -> Ie.Valid(t, ie):
  ei = Equal.cong(B.Read(I.Ie), I.Ie, x => P.Read.value(I.Ie, x, ie), Done{(I.Ie{iei, I.T1{}, 0, []}, r)}, Done{(ie, rest)}, e)
  %ei : Ie.Valid(t, _)
  shx = Equal.sym(I.Fmt, Mm.Mm.format(t, iei), I.T1{}, hx)
  %shx : {I.Ie.valid(_, I.Ie{iei, I.T1{}, 0, []}) == True{} : Bool}
  P.Bool.and_intro(I.fits8(iei), Bool.and(U32.is_ge(iei, 128), True{}), f8, P.Bool.and_intro(U32.is_ge(iei, 128), True{}, Format.t1(t, iei, hx), {==}))

def Ie.dv_tv(+t: Mm.Mm.Type, +iei: U32, +n: Nat, +r: B.Bytes(), +ie: I.Ie, +rest: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, +hx: {Mm.Mm.format(t, iei) == I.Tv{n} : I.Fmt}, +rt: B.Read(B.Bytes()), ert: {B.take(n, r) == rt : B.Read(B.Bytes())}, e: {I.Ie.of_tv(iei, n, rt) == Done{(ie, rest)} : B.Read(I.Ie)}) -> Ie.Valid(t, ie):
  match rt:
    case Fail{err}:
      Empty.absurd(Ie.Valid(t, ie), P.Refute.fail_done(B.Err, B.ReadValue(I.Ie), err, (ie, rest), e))
    case Done{(+body, rest2)}:
      ei = Equal.cong(B.Read(I.Ie), I.Ie, x => P.Read.value(I.Ie, x, ie), Done{(I.Ie{iei, I.Tv{n}, 0, body}, rest2)}, Done{(ie, rest)}, e)
      %ei : Ie.Valid(t, _)
      shx = Equal.sym(I.Fmt, Mm.Mm.format(t, iei), I.Tv{n}, hx)
      %shx : {I.Ie.valid(_, I.Ie{iei, I.Tv{n}, 0, body}) == True{} : Bool}
      P.Bool.and_intro(Nat.is_eq(n, n), Bool.and(I.fits8(iei), Bool.and(U32.is_lt(iei, 128), Bool.and(Nat.is_eq(List.length(&2, U32, body), n), True{}))), P.Nat.is_eq_refl(n), P.Bool.and_intro(I.fits8(iei), Bool.and(U32.is_lt(iei, 128), Bool.and(Nat.is_eq(List.length(&2, U32, body), n), True{})), f8, P.Bool.and_intro(U32.is_lt(iei, 128), Bool.and(Nat.is_eq(List.length(&2, U32, body), n), True{}), Format.low(t, iei, I.Tv{n}, hx, Unit{}), P.Bool.and_intro(Nat.is_eq(List.length(&2, U32, body), n), True{}, Take.len_eq(n, r, body, rest2, ert), {==}))))

def Ie.dv_tlv(+t: Mm.Mm.Type, +iei: U32, +r: B.Bytes(), +ie: I.Ie, +rest: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, +hx: {Mm.Mm.format(t, iei) == I.Tlv{} : I.Fmt}, +rl: B.Read(I.LenBody), erl: {I.lv(r) == rl : B.Read(I.LenBody)}, e: {I.Ie.of_len(iei, I.Tlv{}, rl) == Done{(ie, rest)} : B.Read(I.Ie)}) -> Ie.Valid(t, ie):
  match rl:
    case Fail{err}:
      Empty.absurd(Ie.Valid(t, ie), P.Refute.fail_done(B.Err, B.ReadValue(I.Ie), err, (ie, rest), e))
    case Done{(I.LenBody{+len, +body}, rest2)}:
      ei = Equal.cong(B.Read(I.Ie), I.Ie, x => P.Read.value(I.Ie, x, ie), Done{(I.Ie{iei, I.Tlv{}, len, body}, rest2)}, Done{(ie, rest)}, e)
      %ei : Ie.Valid(t, _)
      shx = Equal.sym(I.Fmt, Mm.Mm.format(t, iei), I.Tlv{}, hx)
      %shx : {I.Ie.valid(_, I.Ie{iei, I.Tlv{}, len, body}) == True{} : Bool}
      P.Bool.and_intro(I.fits8(iei), Bool.and(U32.is_lt(iei, 128), I.LenBody.valid8(I.LenBody{len, body})), f8, P.Bool.and_intro(U32.is_lt(iei, 128), I.LenBody.valid8(I.LenBody{len, body}), Format.low(t, iei, I.Tlv{}, hx, Unit{}), Lv.dv(r, I.LenBody{len, body}, rest2, erl)))

def Ie.dv_tlve(+t: Mm.Mm.Type, +iei: U32, +r: B.Bytes(), +ie: I.Ie, +rest: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, +hx: {Mm.Mm.format(t, iei) == I.TlvE{} : I.Fmt}, +rl: B.Read(I.LenBody), erl: {I.lve(r) == rl : B.Read(I.LenBody)}, e: {I.Ie.of_len(iei, I.TlvE{}, rl) == Done{(ie, rest)} : B.Read(I.Ie)}) -> Ie.Valid(t, ie):
  match rl:
    case Fail{err}:
      Empty.absurd(Ie.Valid(t, ie), P.Refute.fail_done(B.Err, B.ReadValue(I.Ie), err, (ie, rest), e))
    case Done{(I.LenBody{+len, +body}, rest2)}:
      ei = Equal.cong(B.Read(I.Ie), I.Ie, x => P.Read.value(I.Ie, x, ie), Done{(I.Ie{iei, I.TlvE{}, len, body}, rest2)}, Done{(ie, rest)}, e)
      %ei : Ie.Valid(t, _)
      shx = Equal.sym(I.Fmt, Mm.Mm.format(t, iei), I.TlvE{}, hx)
      %shx : {I.Ie.valid(_, I.Ie{iei, I.TlvE{}, len, body}) == True{} : Bool}
      P.Bool.and_intro(I.fits8(iei), Bool.and(U32.is_lt(iei, 128), I.LenBody.valid16(I.LenBody{len, body})), f8, P.Bool.and_intro(U32.is_lt(iei, 128), I.LenBody.valid16(I.LenBody{len, body}), Format.low(t, iei, I.TlvE{}, hx, Unit{}), Lve.dv(r, I.LenBody{len, body}, rest2, erl)))

def Ie.dv(+t: Mm.Mm.Type, +iei: U32, +x: I.Fmt, +r: B.Bytes(), +ie: I.Ie, +rest: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, hx: {Mm.Mm.format(t, iei) == x : I.Fmt}, e: {I.Ie.read_body(iei, x, r) == Done{(ie, rest)} : B.Read(I.Ie)}) -> Ie.Valid(t, ie):
  match x:
    case I.T1{}:
      Ie.dv_t1(t, iei, r, ie, rest, f8, hx, e)
    case I.Tv{+n}:
      Ie.dv_tv(t, iei, n, r, ie, rest, f8, hx, B.take(n, r), {==}, e)
    case I.Tlv{}:
      Ie.dv_tlv(t, iei, r, ie, rest, f8, hx, I.lv(r), {==}, e)
    case I.TlvE{}:
      Ie.dv_tlve(t, iei, r, ie, rest, f8, hx, I.lve(r), {==}, e)

def Opts.dv_cons(+t: Mm.Mm.Type, +ie: I.Ie, +ro: Opts.Res(), +opts: List<&2, I.Ie>, e: {Mm.Opts.cons(ie, ro) == Done{opts} : Opts.Res()}, hv: Ie.Valid(t, ie), ho: @opts2: List<&2, I.Ie> -> {ro == Done{opts2} : Opts.Res()} -> {Mm.Opts.valid(t, opts2) == True{} : Bool}) -> {Mm.Opts.valid(t, opts) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Empty.absurd({Mm.Opts.valid(t, opts) == True{} : Bool}, P.Refute.fail_done(B.Err, List<&2, I.Ie>, err, opts, e))
    case Done{+opts2}:
      eo = Equal.cong(Opts.Res(), List<&2, I.Ie>, x => P.Res.value(B.Err, List<&2, I.Ie>, x, opts), Done{ie <> opts2}, Done{opts}, e)
      %eo : {Mm.Opts.valid(t, _) == True{} : Bool}
      P.Bool.and_intro(I.Ie.valid(Mm.Mm.format(t, I.Ie.iei(ie)), ie), Mm.Opts.valid(t, opts2), hv, ho(opts2, {==}))

def Opts.dv_next(+t: Mm.Mm.Type, +f: Nat, +rb: B.Read(I.Ie), +opts: List<&2, I.Ie>, e: {Mm.Opts.next(rb, left => Mm.Opts.read(f, t, left)) == Done{opts} : Opts.Res()}, hb: @ie: I.Ie -> @r: B.Bytes() -> {rb == Done{(ie, r)} : B.Read(I.Ie)} -> Ie.Valid(t, ie), ih: @left: B.Bytes() -> @opts2: List<&2, I.Ie> -> {Mm.Opts.read(f, t, left) == Done{opts2} : Opts.Res()} -> {Mm.Opts.valid(t, opts2) == True{} : Bool}) -> {Mm.Opts.valid(t, opts) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Empty.absurd({Mm.Opts.valid(t, opts) == True{} : Bool}, P.Refute.fail_done(B.Err, List<&2, I.Ie>, err, opts, e))
    case Done{(+ie, +r)}:
      Opts.dv_cons(t, ie, Mm.Opts.read(f, t, r), opts, e, hb(ie, r, {==}), opts2 => e2 => ih(r, opts2, e2))

def Opts.dv_iei(+t: Mm.Mm.Type, +f: Nat, +iei: U32, +r: B.Bytes(), +opts: List<&2, I.Ie>, ok: Bool, ev: {I.fits8(iei) == ok : Bool}, e: {Mm.Opts.iei(t, iei, r, left => Mm.Opts.read(f, t, left), ok) == Done{opts} : Opts.Res()}, ih: @left: B.Bytes() -> @opts2: List<&2, I.Ie> -> {Mm.Opts.read(f, t, left) == Done{opts2} : Opts.Res()} -> {Mm.Opts.valid(t, opts2) == True{} : Bool}) -> {Mm.Opts.valid(t, opts) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Mm.Opts.valid(t, opts) == True{} : Bool}, P.Refute.fail_done(B.Err, List<&2, I.Ie>, B.Invalid{iei}, opts, e))
    case True{}:
      Opts.dv_next(t, f, I.Ie.read_body(iei, Mm.Mm.format(t, iei), r), opts, e, ie => r2 => e2 => Ie.dv(t, iei, Mm.Mm.format(t, iei), r, ie, r2, ev, {==}, e2), ih)

def Opts.dv(+t: Mm.Mm.Type, +fuel: Nat, +bs: B.Bytes(), +opts: List<&2, I.Ie>, e: {Mm.Opts.read(fuel, t, bs) == Done{opts} : Opts.Res()}) -> {Mm.Opts.valid(t, opts) == True{} : Bool}:
  match fuel bs:
    case 0n Nil{}:
      eo = Equal.cong(Opts.Res(), List<&2, I.Ie>, x => P.Res.value(B.Err, List<&2, I.Ie>, x, opts), Done{[]}, Done{opts}, e)
      %eo : {Mm.Opts.valid(t, _) == True{} : Bool}
      {==}
    case 1n+f Nil{}:
      eo = Equal.cong(Opts.Res(), List<&2, I.Ie>, x => P.Res.value(B.Err, List<&2, I.Ie>, x, opts), Done{[]}, Done{opts}, e)
      %eo : {Mm.Opts.valid(t, _) == True{} : Bool}
      {==}
    case 0n b <> r:
      Empty.absurd({Mm.Opts.valid(t, opts) == True{} : Bool}, P.Refute.fail_done(B.Err, List<&2, I.Ie>, B.Invalid{b}, opts, e))
    case 1n++f +iei <> +r:
      Opts.dv_iei(t, f, iei, r, opts, I.fits8(iei), {==}, e, left => opts2 => e2 => Opts.dv(t, f, left, opts2, e2))

def Msg.dv_opts(+mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +ro: Opts.Res(), +m: Mm.Mm, e: {Mm.Mm.r_opts(mt, fields, ro) == Done{m} : Msg.Res()}, hf: {I.Fields.valid(Mm.Mm.layout(mt), fields) == True{} : Bool}, ho: @opts: List<&2, I.Ie> -> {ro == Done{opts} : Opts.Res()} -> {Mm.Opts.valid(mt, opts) == True{} : Bool}) -> {Mm.Mm.valid(m) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Empty.absurd({Mm.Mm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Mm.Mm, err, m, e))
    case Done{+opts}:
      em = Equal.cong(Msg.Res(), Mm.Mm, x => P.Res.value(B.Err, Mm.Mm, x, m), Done{Mm.Mm{mt, fields, opts}}, Done{m}, e)
      %em : {Mm.Mm.valid(_) == True{} : Bool}
      P.Bool.and_intro(I.Fields.valid(Mm.Mm.layout(mt), fields), Mm.Opts.valid(mt, opts), hf, ho(opts, {==}))

def Msg.dv_fields(+mt: Mm.Mm.Type, +rf: B.Read(List<&2, I.Field>), +m: Mm.Mm, e: {Mm.Mm.r_fields(mt, rf) == Done{m} : Msg.Res()}, hf: @fs: List<&2, I.Field> -> @r: B.Bytes() -> {rf == Done{(fs, r)} : B.Read(List<&2, I.Field>)} -> {I.Fields.valid(Mm.Mm.layout(mt), fs) == True{} : Bool}) -> {Mm.Mm.valid(m) == True{} : Bool}:
  match rf:
    case Fail{err}:
      Empty.absurd({Mm.Mm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Mm.Mm, err, m, e))
    case Done{(+fields, +rest)}:
      Msg.dv_opts(mt, fields, Mm.Opts.read(List.length(&2, U32, rest), mt, rest), m, e, hf(fields, rest, {==}), opts => e2 => Opts.dv(mt, List.length(&2, U32, rest), rest, opts, e2))

def Msg.dv_type(+code: U32, +r: B.Bytes(), +m: Mm.Mm, +tm: Maybe<&2, Mm.Mm.Type>, e: {Mm.Mm.r_type(code, r, tm) == Done{m} : Msg.Res()}) -> {Mm.Mm.valid(m) == True{} : Bool}:
  match tm:
    case None{}:
      Empty.absurd({Mm.Mm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Mm.Mm, B.Unsupported{code}, m, e))
    case Some{+mt}:
      Msg.dv_fields(mt, I.Fields.read(Mm.Mm.layout(mt), r), m, e, fs => r2 => e2 => Fields.dv(Mm.Mm.layout(mt), r, fs, r2, e2))

def Msg.dv_sht(ok: Bool, +r: B.Bytes(), +sht: U32, +m: Mm.Mm, e: {Mm.Mm.r_sht(r, sht, ok) == Done{m} : Msg.Res()}) -> {Mm.Mm.valid(m) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Mm.Mm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Mm.Mm, B.Invalid{sht}, m, e))
    case True{}:
      match r:
        case Nil{}:
          Empty.absurd({Mm.Mm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Mm.Mm, B.Short{}, m, e))
        case +code <> +r2:
          Msg.dv_type(code, r2, m, Mm.Mm.Type.of(code), e)

def Msg.dv_epd(ok: Bool, +r: B.Bytes(), +epd: U32, +m: Mm.Mm, e: {Mm.Mm.r_epd(r, epd, ok) == Done{m} : Msg.Res()}) -> {Mm.Mm.valid(m) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Mm.Mm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Mm.Mm, B.Invalid{epd}, m, e))
    case True{}:
      match r:
        case Nil{}:
          Empty.absurd({Mm.Mm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Mm.Mm, B.Short{}, m, e))
        case +sht <> +r2:
          Msg.dv_sht(U32.is_eq(sht, 0), r2, sht, m, e)

def Msg.dv(+bs: B.Bytes(), +m: Mm.Mm, e: {Mm.Mm.read(bs) == Done{m} : Msg.Res()}) -> {Mm.Mm.valid(m) == True{} : Bool}:
  match bs:
    case Nil{}:
      Empty.absurd({Mm.Mm.valid(m) == True{} : Bool}, P.Refute.fail_done(B.Err, Mm.Mm, B.Short{}, m, e))
    case +epd <> +r:
      Msg.dv_epd(U32.is_eq(epd, 126), r, epd, m, e)

def L.nas.mm.decode_valid(bs, m, e):
  Msg.dv(bs, m, e)

# The bytes a decoded value came from are its encoding
# ----------------------------------------------------

def Bytes.all_app(+xs: B.Bytes(), +ys: B.Bytes(), +e: {B.all_bytes(List.append(&2, U32, xs, ys)) == True{} : Bool}) -> {B.all_bytes(ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      e
    case x <> xt:
      Bytes.all_app(xt, ys, P.Bool.and_true_r(B.is_byte(x), B.all_bytes(List.append(&2, U32, xt, ys)), e))

def Take.sx.fin(-G: Type, +body: B.Bytes(), +r3: B.Bytes(), +r: B.Bytes(), +a: {List.append(&2, U32, body, r3) == r : B.Bytes()}, +ab: {B.all_bytes(r) == True{} : Bool}, k: {List.append(&2, U32, body, r3) == r : B.Bytes()} -> {B.all_bytes(r3) == True{} : Bool} -> G) -> G:
  sa = Equal.sym(B.Bytes(), List.append(&2, U32, body, r3), r, a)
  k(a, Bytes.all_app(body, r3, (%sa : {B.all_bytes(_) == True{} : Bool}; ab)))

def Take.sx.go(-G: Type, +n: Nat, +body: B.Bytes(), +r3: B.Bytes(), +r: B.Bytes(), la: {List.length(&2, U32, body) == n : Nat} & {List.append(&2, U32, body, r3) == r : B.Bytes()}, +ab: {B.all_bytes(r) == True{} : Bool}, k: {List.append(&2, U32, body, r3) == r : B.Bytes()} -> {B.all_bytes(r3) == True{} : Bool} -> G) -> G:
  (l, a) = la
  Take.sx.fin(G, body, r3, r, a, ab, k)

# What take leaves is a suffix of all-byte input, and the taken part is a prefix.
def Take.sx(-G: Type, +n: Nat, +r: B.Bytes(), +body: B.Bytes(), +r3: B.Bytes(), +e: {B.take(n, r) == Done{(body, r3)} : B.Read(B.Bytes())}, +ab: {B.all_bytes(r) == True{} : Bool}, k: {List.append(&2, U32, body, r3) == r : B.Bytes()} -> {B.all_bytes(r3) == True{} : Bool} -> G) -> G:
  Take.sx.go(G, n, body, r3, r, L.bytes.take.length(n, r, body, r3, e), ab, k)

def Len.sx_join(-G: Type, +len0: U32, +r: B.Bytes(), +lb: I.LenBody, +r2: B.Bytes(), +rt: B.Read(B.Bytes()), ert: {B.take(U32.to_nat(len0), r) == rt : B.Read(B.Bytes())}, +e: {I.Len.join(len0, rt) == Done{(lb, r2)} : B.Read(I.LenBody)}, +ab: {B.all_bytes(r) == True{} : Bool}, k: @body: B.Bytes() -> @r3: B.Bytes() -> {Done{(I.LenBody{len0, body}, r3)} == Done{(lb, r2)} : B.Read(I.LenBody)} -> {List.append(&2, U32, body, r3) == r : B.Bytes()} -> {B.all_bytes(r3) == True{} : Bool} -> G) -> G:
  match rt:
    case Fail{err}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), err, (lb, r2), e))
    case Done{(+body, +r3)}:
      Take.sx(G, U32.to_nat(len0), r, body, r3, ert, ab, ap => al => k(body, r3, e, ap, al))

def Len.sx(-G: Type, +len0: U32, +r: B.Bytes(), +lb: I.LenBody, +r2: B.Bytes(), ok: Bool, fits: Bool, +ev: {fits == ok : Bool}, +e: {I.Len.take(len0, r, ok) == Done{(lb, r2)} : B.Read(I.LenBody)}, +ab: {B.all_bytes(r) == True{} : Bool}, k: {fits == True{} : Bool} -> @body: B.Bytes() -> @r3: B.Bytes() -> {Done{(I.LenBody{len0, body}, r3)} == Done{(lb, r2)} : B.Read(I.LenBody)} -> {List.append(&2, U32, body, r3) == r : B.Bytes()} -> {B.all_bytes(r3) == True{} : Bool} -> G) -> G:
  match ok:
    case False{}:
      Empty.absurd(G, P.Refute.fail_done(B.Err, B.ReadValue(I.LenBody), B.Invalid{len0}, (lb, r2), e))
    case True{}:
      Len.sx_join(G, len0, r, lb, r2, B.take(U32.to_nat(len0), r), {==}, e, ab, k(ev))

def Field.Sx(+f: I.Field, +rest: B.Bytes(), +bs: B.Bytes()) -> Type:
  {I.Field.write(f, rest) == bs : B.Bytes()} & {B.all_bytes(rest) == True{} : Bool}

def Field.sx_byte(+b: U32, +r: B.Bytes(), +f: I.Field, +rest: B.Bytes(), ok: Bool, +ev: {I.fits8(b) == ok : Bool}, +e: {I.Field.byte_ok(b, r, ok) == Done{(f, rest)} : B.Read(I.Field)}, +ab: {B.all_bytes(b <> r) == True{} : Bool}) -> Field.Sx(f, rest, b <> r):
  match ok:
    case False{}:
      Empty.absurd(Field.Sx(f, rest, b <> r), P.Refute.fail_done(B.Err, B.ReadValue(I.Field), B.Invalid{b}, (f, rest), e))
    case True{}:
      ef = Equal.cong(B.Read(I.Field), I.Field, x => P.Read.value(I.Field, x, f), Done{(I.FByte{b}, r)}, Done{(f, rest)}, e)
      er = Equal.cong(B.Read(I.Field), B.Bytes(), x => P.Read.rest(I.Field, x, rest), Done{(I.FByte{b}, r)}, Done{(f, rest)}, e)
      %ef : Field.Sx(_, rest, b <> r)
      %er : Field.Sx(I.FByte{b}, _, b <> r)
      mb = Equal.sym(U32, U32.and(255, b), b, P.U32.eq_of_is_eq(U32.and(255, b), b, ev))
      %mb : {_ <> r == b <> r : B.Bytes()} & {B.all_bytes(r) == True{} : Bool}
      ({==}, P.Bool.and_true_r(B.is_byte(b), B.all_bytes(r), ab))

def Field.sx_lv_fin(+len0: U32, +r: B.Bytes(), +lb: I.LenBody, +r2: B.Bytes(), +body: B.Bytes(), +r3: B.Bytes(), f8: {I.fits8(len0) == True{} : Bool}, +e2: {Done{(I.LenBody{len0, body}, r3)} == Done{(lb, r2)} : B.Read(I.LenBody)}, ap: {List.append(&2, U32, body, r3) == r : B.Bytes()}, al: {B.all_bytes(r3) == True{} : Bool}) -> Field.Sx(I.FLv{lb}, r2, len0 <> r):
  el = Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, lb), Done{(I.LenBody{len0, body}, r3)}, Done{(lb, r2)}, e2)
  er = Equal.cong(B.Read(I.LenBody), B.Bytes(), x => P.Read.rest(I.LenBody, x, r2), Done{(I.LenBody{len0, body}, r3)}, Done{(lb, r2)}, e2)
  %el : Field.Sx(I.FLv{_}, r2, len0 <> r)
  %er : Field.Sx(I.FLv{I.LenBody{len0, body}}, _, len0 <> r)
  ml = Equal.sym(U32, U32.and(255, len0), len0, P.U32.eq_of_is_eq(U32.and(255, len0), len0, f8))
  %ml : {_ <> List.append(&2, U32, body, r3) == len0 <> r : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, body, r3), r, ap)
  %sap : {len0 <> _ == len0 <> r : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  ({==}, al)

def Field.sx_lv(+len0: U32, +r: B.Bytes(), +f: I.Field, +rest: B.Bytes(), +rl: B.Read(I.LenBody), erl: {I.Len.take(len0, r, I.fits8(len0)) == rl : B.Read(I.LenBody)}, +e: {I.Field.of_lv(rl) == Done{(f, rest)} : B.Read(I.Field)}, +ab: {B.all_bytes(len0 <> r) == True{} : Bool}) -> Field.Sx(f, rest, len0 <> r):
  match rl:
    case Fail{err}:
      Empty.absurd(Field.Sx(f, rest, len0 <> r), P.Refute.fail_done(B.Err, B.ReadValue(I.Field), err, (f, rest), e))
    case Done{(+lb, +r2)}:
      ef = Equal.cong(B.Read(I.Field), I.Field, x => P.Read.value(I.Field, x, f), Done{(I.FLv{lb}, r2)}, Done{(f, rest)}, e)
      er = Equal.cong(B.Read(I.Field), B.Bytes(), x => P.Read.rest(I.Field, x, rest), Done{(I.FLv{lb}, r2)}, Done{(f, rest)}, e)
      %ef : Field.Sx(_, rest, len0 <> r)
      %er : Field.Sx(I.FLv{lb}, _, len0 <> r)
      Len.sx(Field.Sx(I.FLv{lb}, r2, len0 <> r), len0, r, lb, r2, I.fits8(len0), I.fits8(len0), {==}, erl, P.Bool.and_true_r(B.is_byte(len0), B.all_bytes(r), ab), f8 => body => r3 => e2 => ap => al => Field.sx_lv_fin(len0, r, lb, r2, body, r3, f8, e2, ap, al))

def Field.sx_lve_fin(+b1: U32, +b0: U32, +r: B.Bytes(), +lb: I.LenBody, +r2: B.Bytes(), +body: B.Bytes(), +r3: B.Bytes(), +e2: {Done{(I.LenBody{B.cat8(b0, b1), body}, r3)} == Done{(lb, r2)} : B.Read(I.LenBody)}, ap: {List.append(&2, U32, body, r3) == r : B.Bytes()}, al: {B.all_bytes(r3) == True{} : Bool}, m1: {U32.and(255, b1) == b1 : U32}, m0: {U32.and(255, b0) == b0 : U32}) -> Field.Sx(I.FLvE{lb}, r2, b1 <> b0 <> r):
  el = Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, lb), Done{(I.LenBody{B.cat8(b0, b1), body}, r3)}, Done{(lb, r2)}, e2)
  er = Equal.cong(B.Read(I.LenBody), B.Bytes(), x => P.Read.rest(I.LenBody, x, r2), Done{(I.LenBody{B.cat8(b0, b1), body}, r3)}, Done{(lb, r2)}, e2)
  %el : Field.Sx(I.FLvE{_}, r2, b1 <> b0 <> r)
  %er : Field.Sx(I.FLvE{I.LenBody{B.cat8(b0, b1), body}}, _, b1 <> b0 <> r)
  hi = Equal.sym(U32, U32.and(255, U32.shrn(B.cat8(b0, b1), 8n)), b1, P.U32.cat8_hi(b0, b1, m1))
  %hi : {_ <> U32.and(255, B.cat8(b0, b1)) <> List.append(&2, U32, body, r3) == b1 <> b0 <> r : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  lo = Equal.sym(U32, U32.and(255, B.cat8(b0, b1)), b0, P.U32.cat8_lo(b0, b1, m0))
  %lo : {b1 <> _ <> List.append(&2, U32, body, r3) == b1 <> b0 <> r : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, body, r3), r, ap)
  %sap : {b1 <> b0 <> _ == b1 <> b0 <> r : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  ({==}, al)

def Field.sx_lve(+b1: U32, +b0: U32, +r: B.Bytes(), +f: I.Field, +rest: B.Bytes(), +rl: B.Read(I.LenBody), erl: {I.Len.take(B.cat8(b0, b1), r, I.fits16(B.cat8(b0, b1))) == rl : B.Read(I.LenBody)}, +e: {I.Field.of_lve(rl) == Done{(f, rest)} : B.Read(I.Field)}, +ab: {B.all_bytes(b1 <> b0 <> r) == True{} : Bool}) -> Field.Sx(f, rest, b1 <> b0 <> r):
  match rl:
    case Fail{err}:
      Empty.absurd(Field.Sx(f, rest, b1 <> b0 <> r), P.Refute.fail_done(B.Err, B.ReadValue(I.Field), err, (f, rest), e))
    case Done{(+lb, +r2)}:
      ef = Equal.cong(B.Read(I.Field), I.Field, x => P.Read.value(I.Field, x, f), Done{(I.FLvE{lb}, r2)}, Done{(f, rest)}, e)
      er = Equal.cong(B.Read(I.Field), B.Bytes(), x => P.Read.rest(I.Field, x, rest), Done{(I.FLvE{lb}, r2)}, Done{(f, rest)}, e)
      %ef : Field.Sx(_, rest, b1 <> b0 <> r)
      %er : Field.Sx(I.FLvE{lb}, _, b1 <> b0 <> r)
      +ab0 = P.Bool.and_true_r(B.is_byte(b1), Bool.and(B.is_byte(b0), B.all_bytes(r)), ab)
      Len.sx(Field.Sx(I.FLvE{lb}, r2, b1 <> b0 <> r), B.cat8(b0, b1), r, lb, r2, I.fits16(B.cat8(b0, b1)), I.fits16(B.cat8(b0, b1)), {==}, erl, P.Bool.and_true_r(B.is_byte(b0), B.all_bytes(r), ab0), f16 => body => r3 => e2 => ap => al => Field.sx_lve_fin(b1, b0, r, lb, r2, body, r3, e2, ap, al, P.U32.lt256_mask8(b1, P.Bool.and_true_l(B.is_byte(b1), Bool.and(B.is_byte(b0), B.all_bytes(r)), ab)), P.U32.lt256_mask8(b0, P.Bool.and_true_l(B.is_byte(b0), B.all_bytes(r), ab0))))

def Field.sx(+lay: I.Lay, +bs: B.Bytes(), +f: I.Field, +rest: B.Bytes(), +e: {I.Field.read(lay, bs) == Done{(f, rest)} : B.Read(I.Field)}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> Field.Sx(f, rest, bs):
  match lay:
    case I.V1{}:
      match bs:
        case Nil{}:
          Empty.absurd(Field.Sx(f, rest, []), P.Refute.fail_done(B.Err, B.ReadValue(I.Field), B.Short{}, (f, rest), e))
        case +b <> +r:
          Field.sx_byte(b, r, f, rest, I.fits8(b), {==}, e, ab)
    case I.Lv{}:
      match bs:
        case Nil{}:
          Empty.absurd(Field.Sx(f, rest, []), P.Refute.fail_done(B.Err, B.ReadValue(I.Field), B.Short{}, (f, rest), e))
        case +len0 <> +r:
          Field.sx_lv(len0, r, f, rest, I.Len.take(len0, r, I.fits8(len0)), {==}, e, ab)
    case I.LvE{}:
      match bs:
        case Nil{}:
          Empty.absurd(Field.Sx(f, rest, []), P.Refute.fail_done(B.Err, B.ReadValue(I.Field), B.Short{}, (f, rest), e))
        case b <> Nil{}:
          Empty.absurd(Field.Sx(f, rest, [b]), P.Refute.fail_done(B.Err, B.ReadValue(I.Field), B.Short{}, (f, rest), e))
        case +b1 <> +b0 <> +r:
          Field.sx_lve(b1, b0, r, f, rest, I.Len.take(B.cat8(b0, b1), r, I.fits16(B.cat8(b0, b1))), {==}, e, ab)

def Fields.Sx(+fs: List<&2, I.Field>, +rest: B.Bytes(), +bs: B.Bytes()) -> Type:
  {I.Fields.write(fs, rest) == bs : B.Bytes()} & {B.all_bytes(rest) == True{} : Bool}

def Fields.sx_fin(+bs: B.Bytes(), +f: I.Field, +r: B.Bytes(), +fs2: List<&2, I.Field>, +r3: B.Bytes(), w1: {I.Field.write(f, r) == bs : B.Bytes()}, s2: Fields.Sx(fs2, r3, r)) -> Fields.Sx(f <> fs2, r3, bs):
  (w2, a2) = s2
  sw2 = Equal.sym(B.Bytes(), I.Fields.write(fs2, r3), r, w2)
  %sw2 : {I.Field.write(f, _) == bs : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  (w1, a2)

def Fields.sx_cons(+ls: List<&2, I.Lay>, +bs: B.Bytes(), +f: I.Field, +r: B.Bytes(), +r2: B.Read(List<&2, I.Field>), er2: {I.Fields.read(ls, r) == r2 : B.Read(List<&2, I.Field>)}, +fs: List<&2, I.Field>, +rest: B.Bytes(), +e: {I.Fields.cons(f, r2) == Done{(fs, rest)} : B.Read(List<&2, I.Field>)}, s1: Field.Sx(f, r, bs), h2: @fs2: List<&2, I.Field> -> @r3: B.Bytes() -> {I.Fields.read(ls, r) == Done{(fs2, r3)} : B.Read(List<&2, I.Field>)} -> {B.all_bytes(r) == True{} : Bool} -> Fields.Sx(fs2, r3, r)) -> Fields.Sx(fs, rest, bs):
  match r2:
    case Fail{err}:
      Empty.absurd(Fields.Sx(fs, rest, bs), P.Refute.fail_done(B.Err, B.ReadValue(List<&2, I.Field>), err, (fs, rest), e))
    case Done{(+fs2, +r3)}:
      (w1, a1) = s1
      et = Equal.cong(B.Read(List<&2, I.Field>), List<&2, I.Field>, x => P.Read.value(List<&2, I.Field>, x, fs), Done{(f <> fs2, r3)}, Done{(fs, rest)}, e)
      er = Equal.cong(B.Read(List<&2, I.Field>), B.Bytes(), x => P.Read.rest(List<&2, I.Field>, x, rest), Done{(f <> fs2, r3)}, Done{(fs, rest)}, e)
      %et : Fields.Sx(_, rest, bs)
      %er : Fields.Sx(f <> fs2, _, bs)
      Fields.sx_fin(bs, f, r, fs2, r3, w1, h2(fs2, r3, er2, a1))

def Fields.sx_next(+ls: List<&2, I.Lay>, +bs: B.Bytes(), +r1: B.Read(I.Field), +fs: List<&2, I.Field>, +rest: B.Bytes(), +e: {I.Fields.next(r1, r => I.Fields.read(ls, r)) == Done{(fs, rest)} : B.Read(List<&2, I.Field>)}, h1: @f: I.Field -> @r: B.Bytes() -> {r1 == Done{(f, r)} : B.Read(I.Field)} -> Field.Sx(f, r, bs), h2: @bs2: B.Bytes() -> @fs2: List<&2, I.Field> -> @r: B.Bytes() -> {I.Fields.read(ls, bs2) == Done{(fs2, r)} : B.Read(List<&2, I.Field>)} -> {B.all_bytes(bs2) == True{} : Bool} -> Fields.Sx(fs2, r, bs2)) -> Fields.Sx(fs, rest, bs):
  match r1:
    case Fail{err}:
      Empty.absurd(Fields.Sx(fs, rest, bs), P.Refute.fail_done(B.Err, B.ReadValue(List<&2, I.Field>), err, (fs, rest), e))
    case Done{(+f, +r)}:
      Fields.sx_cons(ls, bs, f, r, I.Fields.read(ls, r), {==}, fs, rest, e, h1(f, r, {==}), fs2 => r3 => e2 => ab2 => h2(r, fs2, r3, e2, ab2))

def Fields.sx(+lays: List<&2, I.Lay>, +bs: B.Bytes(), +fs: List<&2, I.Field>, +rest: B.Bytes(), +e: {I.Fields.read(lays, bs) == Done{(fs, rest)} : B.Read(List<&2, I.Field>)}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> Fields.Sx(fs, rest, bs):
  match lays:
    case Nil{}:
      et = Equal.cong(B.Read(List<&2, I.Field>), List<&2, I.Field>, x => P.Read.value(List<&2, I.Field>, x, fs), Done{([], bs)}, Done{(fs, rest)}, e)
      er = Equal.cong(B.Read(List<&2, I.Field>), B.Bytes(), x => P.Read.rest(List<&2, I.Field>, x, rest), Done{([], bs)}, Done{(fs, rest)}, e)
      %et : Fields.Sx(_, rest, bs)
      %er : Fields.Sx([], _, bs)
      ({==}, ab)
    case +l <> +ls:
      Fields.sx_next(ls, bs, I.Field.read(l, bs), fs, rest, e, f => r => e2 => Field.sx(l, bs, f, r, e2, ab), bs2 => fs2 => r => e2 => ab2 => Fields.sx(ls, bs2, fs2, r, e2, ab2))

def Ie.Sx(+ie: I.Ie, +rest: B.Bytes(), +bs: B.Bytes()) -> Type:
  {I.Ie.write(ie, rest) == bs : B.Bytes()} & {B.all_bytes(rest) == True{} : Bool}

def Ie.sx_tv_fin(+iei: U32, +n: Nat, +r: B.Bytes(), +body: B.Bytes(), +r3: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, ap: {List.append(&2, U32, body, r3) == r : B.Bytes()}, al: {B.all_bytes(r3) == True{} : Bool}) -> Ie.Sx(I.Ie{iei, I.Tv{n}, 0, body}, r3, iei <> r):
  mi = Equal.sym(U32, U32.and(255, iei), iei, P.U32.eq_of_is_eq(U32.and(255, iei), iei, f8))
  %mi : {_ <> List.append(&2, U32, body, r3) == iei <> r : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, body, r3), r, ap)
  %sap : {iei <> _ == iei <> r : B.Bytes()} & {B.all_bytes(r3) == True{} : Bool}
  ({==}, al)

def Ie.sx_tv(+iei: U32, +n: Nat, +r: B.Bytes(), +ie: I.Ie, +r2: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, +rt: B.Read(B.Bytes()), ert: {B.take(n, r) == rt : B.Read(B.Bytes())}, +e: {I.Ie.of_tv(iei, n, rt) == Done{(ie, r2)} : B.Read(I.Ie)}, +ab: {B.all_bytes(r) == True{} : Bool}) -> Ie.Sx(ie, r2, iei <> r):
  match rt:
    case Fail{err}:
      Empty.absurd(Ie.Sx(ie, r2, iei <> r), P.Refute.fail_done(B.Err, B.ReadValue(I.Ie), err, (ie, r2), e))
    case Done{(+body, +r3)}:
      ei = Equal.cong(B.Read(I.Ie), I.Ie, x => P.Read.value(I.Ie, x, ie), Done{(I.Ie{iei, I.Tv{n}, 0, body}, r3)}, Done{(ie, r2)}, e)
      er = Equal.cong(B.Read(I.Ie), B.Bytes(), x => P.Read.rest(I.Ie, x, r2), Done{(I.Ie{iei, I.Tv{n}, 0, body}, r3)}, Done{(ie, r2)}, e)
      %ei : Ie.Sx(_, r2, iei <> r)
      %er : Ie.Sx(I.Ie{iei, I.Tv{n}, 0, body}, _, iei <> r)
      Take.sx(Ie.Sx(I.Ie{iei, I.Tv{n}, 0, body}, r3, iei <> r), n, r, body, r3, ert, ab, ap => al => Ie.sx_tv_fin(iei, n, r, body, r3, f8, ap, al))

def Ie.sx_tlv_fin(+iei: U32, +len0: U32, +r1: B.Bytes(), +len1: U32, +body: B.Bytes(), +r3: B.Bytes(), +body2: B.Bytes(), +r4: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, fl: {I.fits8(len0) == True{} : Bool}, +e2: {Done{(I.LenBody{len0, body2}, r4)} == Done{(I.LenBody{len1, body}, r3)} : B.Read(I.LenBody)}, ap: {List.append(&2, U32, body2, r4) == r1 : B.Bytes()}, al: {B.all_bytes(r4) == True{} : Bool}) -> Ie.Sx(I.Ie{iei, I.Tlv{}, len1, body}, r3, iei <> len0 <> r1):
  +elb = Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, I.LenBody{len1, body}), Done{(I.LenBody{len0, body2}, r4)}, Done{(I.LenBody{len1, body}, r3)}, e2)
  el = Equal.cong(I.LenBody, U32, x => P.Lb.len(x), I.LenBody{len0, body2}, I.LenBody{len1, body}, elb)
  eb = Equal.cong(I.LenBody, B.Bytes(), x => P.Lb.body(x), I.LenBody{len0, body2}, I.LenBody{len1, body}, elb)
  er = Equal.cong(B.Read(I.LenBody), B.Bytes(), x => P.Read.rest(I.LenBody, x, r3), Done{(I.LenBody{len0, body2}, r4)}, Done{(I.LenBody{len1, body}, r3)}, e2)
  %el : Ie.Sx(I.Ie{iei, I.Tlv{}, _, body}, r3, iei <> len0 <> r1)
  %eb : Ie.Sx(I.Ie{iei, I.Tlv{}, len0, _}, r3, iei <> len0 <> r1)
  %er : Ie.Sx(I.Ie{iei, I.Tlv{}, len0, body2}, _, iei <> len0 <> r1)
  mi = Equal.sym(U32, U32.and(255, iei), iei, P.U32.eq_of_is_eq(U32.and(255, iei), iei, f8))
  %mi : {_ <> U32.and(255, len0) <> List.append(&2, U32, body2, r4) == iei <> len0 <> r1 : B.Bytes()} & {B.all_bytes(r4) == True{} : Bool}
  ml = Equal.sym(U32, U32.and(255, len0), len0, P.U32.eq_of_is_eq(U32.and(255, len0), len0, fl))
  %ml : {iei <> _ <> List.append(&2, U32, body2, r4) == iei <> len0 <> r1 : B.Bytes()} & {B.all_bytes(r4) == True{} : Bool}
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, body2, r4), r1, ap)
  %sap : {iei <> len0 <> _ == iei <> len0 <> r1 : B.Bytes()} & {B.all_bytes(r4) == True{} : Bool}
  ({==}, al)

def Ie.sx_tlv(+iei: U32, +len0: U32, +r1: B.Bytes(), +ie: I.Ie, +r2: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, +rl: B.Read(I.LenBody), erl: {I.Len.take(len0, r1, I.fits8(len0)) == rl : B.Read(I.LenBody)}, +e: {I.Ie.of_len(iei, I.Tlv{}, rl) == Done{(ie, r2)} : B.Read(I.Ie)}, +ab: {B.all_bytes(len0 <> r1) == True{} : Bool}) -> Ie.Sx(ie, r2, iei <> len0 <> r1):
  match rl:
    case Fail{err}:
      Empty.absurd(Ie.Sx(ie, r2, iei <> len0 <> r1), P.Refute.fail_done(B.Err, B.ReadValue(I.Ie), err, (ie, r2), e))
    case Done{(I.LenBody{+len1, +body}, +r3)}:
      ei = Equal.cong(B.Read(I.Ie), I.Ie, x => P.Read.value(I.Ie, x, ie), Done{(I.Ie{iei, I.Tlv{}, len1, body}, r3)}, Done{(ie, r2)}, e)
      er = Equal.cong(B.Read(I.Ie), B.Bytes(), x => P.Read.rest(I.Ie, x, r2), Done{(I.Ie{iei, I.Tlv{}, len1, body}, r3)}, Done{(ie, r2)}, e)
      %ei : Ie.Sx(_, r2, iei <> len0 <> r1)
      %er : Ie.Sx(I.Ie{iei, I.Tlv{}, len1, body}, _, iei <> len0 <> r1)
      Len.sx(Ie.Sx(I.Ie{iei, I.Tlv{}, len1, body}, r3, iei <> len0 <> r1), len0, r1, I.LenBody{len1, body}, r3, I.fits8(len0), I.fits8(len0), {==}, erl, P.Bool.and_true_r(B.is_byte(len0), B.all_bytes(r1), ab), fl => body2 => r4 => e2 => ap => al => Ie.sx_tlv_fin(iei, len0, r1, len1, body, r3, body2, r4, f8, fl, e2, ap, al))

def Ie.sx_tlve_fin(+iei: U32, +b1: U32, +b0: U32, +r1: B.Bytes(), +len1: U32, +body: B.Bytes(), +r3: B.Bytes(), +body2: B.Bytes(), +r4: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, +e2: {Done{(I.LenBody{B.cat8(b0, b1), body2}, r4)} == Done{(I.LenBody{len1, body}, r3)} : B.Read(I.LenBody)}, ap: {List.append(&2, U32, body2, r4) == r1 : B.Bytes()}, al: {B.all_bytes(r4) == True{} : Bool}, m1: {U32.and(255, b1) == b1 : U32}, m0: {U32.and(255, b0) == b0 : U32}) -> Ie.Sx(I.Ie{iei, I.TlvE{}, len1, body}, r3, iei <> b1 <> b0 <> r1):
  +elb = Equal.cong(B.Read(I.LenBody), I.LenBody, x => P.Read.value(I.LenBody, x, I.LenBody{len1, body}), Done{(I.LenBody{B.cat8(b0, b1), body2}, r4)}, Done{(I.LenBody{len1, body}, r3)}, e2)
  el = Equal.cong(I.LenBody, U32, x => P.Lb.len(x), I.LenBody{B.cat8(b0, b1), body2}, I.LenBody{len1, body}, elb)
  eb = Equal.cong(I.LenBody, B.Bytes(), x => P.Lb.body(x), I.LenBody{B.cat8(b0, b1), body2}, I.LenBody{len1, body}, elb)
  er = Equal.cong(B.Read(I.LenBody), B.Bytes(), x => P.Read.rest(I.LenBody, x, r3), Done{(I.LenBody{B.cat8(b0, b1), body2}, r4)}, Done{(I.LenBody{len1, body}, r3)}, e2)
  %el : Ie.Sx(I.Ie{iei, I.TlvE{}, _, body}, r3, iei <> b1 <> b0 <> r1)
  %eb : Ie.Sx(I.Ie{iei, I.TlvE{}, B.cat8(b0, b1), _}, r3, iei <> b1 <> b0 <> r1)
  %er : Ie.Sx(I.Ie{iei, I.TlvE{}, B.cat8(b0, b1), body2}, _, iei <> b1 <> b0 <> r1)
  mi = Equal.sym(U32, U32.and(255, iei), iei, P.U32.eq_of_is_eq(U32.and(255, iei), iei, f8))
  %mi : {_ <> B.write_u16(B.cat8(b0, b1), List.append(&2, U32, body2, r4)) == iei <> b1 <> b0 <> r1 : B.Bytes()} & {B.all_bytes(r4) == True{} : Bool}
  hi = Equal.sym(U32, U32.and(255, U32.shrn(B.cat8(b0, b1), 8n)), b1, P.U32.cat8_hi(b0, b1, m1))
  %hi : {iei <> _ <> U32.and(255, B.cat8(b0, b1)) <> List.append(&2, U32, body2, r4) == iei <> b1 <> b0 <> r1 : B.Bytes()} & {B.all_bytes(r4) == True{} : Bool}
  lo = Equal.sym(U32, U32.and(255, B.cat8(b0, b1)), b0, P.U32.cat8_lo(b0, b1, m0))
  %lo : {iei <> b1 <> _ <> List.append(&2, U32, body2, r4) == iei <> b1 <> b0 <> r1 : B.Bytes()} & {B.all_bytes(r4) == True{} : Bool}
  sap = Equal.sym(B.Bytes(), List.append(&2, U32, body2, r4), r1, ap)
  %sap : {iei <> b1 <> b0 <> _ == iei <> b1 <> b0 <> r1 : B.Bytes()} & {B.all_bytes(r4) == True{} : Bool}
  ({==}, al)

def Ie.sx_tlve(+iei: U32, +b1: U32, +b0: U32, +r1: B.Bytes(), +ie: I.Ie, +r2: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, +rl: B.Read(I.LenBody), erl: {I.Len.take(B.cat8(b0, b1), r1, I.fits16(B.cat8(b0, b1))) == rl : B.Read(I.LenBody)}, +e: {I.Ie.of_len(iei, I.TlvE{}, rl) == Done{(ie, r2)} : B.Read(I.Ie)}, +ab: {B.all_bytes(b1 <> b0 <> r1) == True{} : Bool}) -> Ie.Sx(ie, r2, iei <> b1 <> b0 <> r1):
  match rl:
    case Fail{err}:
      Empty.absurd(Ie.Sx(ie, r2, iei <> b1 <> b0 <> r1), P.Refute.fail_done(B.Err, B.ReadValue(I.Ie), err, (ie, r2), e))
    case Done{(I.LenBody{+len1, +body}, +r3)}:
      ei = Equal.cong(B.Read(I.Ie), I.Ie, x => P.Read.value(I.Ie, x, ie), Done{(I.Ie{iei, I.TlvE{}, len1, body}, r3)}, Done{(ie, r2)}, e)
      er = Equal.cong(B.Read(I.Ie), B.Bytes(), x => P.Read.rest(I.Ie, x, r2), Done{(I.Ie{iei, I.TlvE{}, len1, body}, r3)}, Done{(ie, r2)}, e)
      %ei : Ie.Sx(_, r2, iei <> b1 <> b0 <> r1)
      %er : Ie.Sx(I.Ie{iei, I.TlvE{}, len1, body}, _, iei <> b1 <> b0 <> r1)
      +ab0 = P.Bool.and_true_r(B.is_byte(b1), Bool.and(B.is_byte(b0), B.all_bytes(r1)), ab)
      Len.sx(Ie.Sx(I.Ie{iei, I.TlvE{}, len1, body}, r3, iei <> b1 <> b0 <> r1), B.cat8(b0, b1), r1, I.LenBody{len1, body}, r3, I.fits16(B.cat8(b0, b1)), I.fits16(B.cat8(b0, b1)), {==}, erl, P.Bool.and_true_r(B.is_byte(b0), B.all_bytes(r1), ab0), f16 => body2 => r4 => e2 => ap => al => Ie.sx_tlve_fin(iei, b1, b0, r1, len1, body, r3, body2, r4, f8, e2, ap, al, P.U32.lt256_mask8(b1, P.Bool.and_true_l(B.is_byte(b1), Bool.and(B.is_byte(b0), B.all_bytes(r1)), ab)), P.U32.lt256_mask8(b0, P.Bool.and_true_l(B.is_byte(b0), B.all_bytes(r1), ab0))))

def Ie.sx(+iei: U32, +x: I.Fmt, +r: B.Bytes(), +ie: I.Ie, +r2: B.Bytes(), f8: {I.fits8(iei) == True{} : Bool}, +e: {I.Ie.read_body(iei, x, r) == Done{(ie, r2)} : B.Read(I.Ie)}, +ab: {B.all_bytes(r) == True{} : Bool}) -> Ie.Sx(ie, r2, iei <> r):
  match x:
    case I.T1{}:
      ei = Equal.cong(B.Read(I.Ie), I.Ie, y => P.Read.value(I.Ie, y, ie), Done{(I.Ie{iei, I.T1{}, 0, []}, r)}, Done{(ie, r2)}, e)
      er = Equal.cong(B.Read(I.Ie), B.Bytes(), y => P.Read.rest(I.Ie, y, r2), Done{(I.Ie{iei, I.T1{}, 0, []}, r)}, Done{(ie, r2)}, e)
      %ei : Ie.Sx(_, r2, iei <> r)
      %er : Ie.Sx(I.Ie{iei, I.T1{}, 0, []}, _, iei <> r)
      mi = Equal.sym(U32, U32.and(255, iei), iei, P.U32.eq_of_is_eq(U32.and(255, iei), iei, f8))
      %mi : {_ <> r == iei <> r : B.Bytes()} & {B.all_bytes(r) == True{} : Bool}
      ({==}, ab)
    case I.Tv{+n}:
      Ie.sx_tv(iei, n, r, ie, r2, f8, B.take(n, r), {==}, e, ab)
    case I.Tlv{}:
      match r:
        case Nil{}:
          Empty.absurd(Ie.Sx(ie, r2, [iei]), P.Refute.fail_done(B.Err, B.ReadValue(I.Ie), B.Short{}, (ie, r2), e))
        case +len0 <> +r1:
          Ie.sx_tlv(iei, len0, r1, ie, r2, f8, I.Len.take(len0, r1, I.fits8(len0)), {==}, e, ab)
    case I.TlvE{}:
      match r:
        case Nil{}:
          Empty.absurd(Ie.Sx(ie, r2, [iei]), P.Refute.fail_done(B.Err, B.ReadValue(I.Ie), B.Short{}, (ie, r2), e))
        case b <> Nil{}:
          Empty.absurd(Ie.Sx(ie, r2, [iei, b]), P.Refute.fail_done(B.Err, B.ReadValue(I.Ie), B.Short{}, (ie, r2), e))
        case +b1 <> +b0 <> +r1:
          Ie.sx_tlve(iei, b1, b0, r1, ie, r2, f8, I.Len.take(B.cat8(b0, b1), r1, I.fits16(B.cat8(b0, b1))), {==}, e, ab)

def Opts.sx_cons(+t: Mm.Mm.Type, +f: Nat, +iei: U32, +r: B.Bytes(), +ie: I.Ie, +r2: B.Bytes(), +ro: Opts.Res(), ero: {Mm.Opts.read(f, t, r2) == ro : Opts.Res()}, +opts: List<&2, I.Ie>, +e: {Mm.Opts.cons(ie, ro) == Done{opts} : Opts.Res()}, s: Ie.Sx(ie, r2, iei <> r), ih: @left: B.Bytes() -> @opts2: List<&2, I.Ie> -> {Mm.Opts.read(f, t, left) == Done{opts2} : Opts.Res()} -> {B.all_bytes(left) == True{} : Bool} -> {I.Ies.write(opts2, []) == left : B.Bytes()}) -> {I.Ies.write(opts, []) == iei <> r : B.Bytes()}:
  match ro:
    case Fail{err}:
      Empty.absurd({I.Ies.write(opts, []) == iei <> r : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, I.Ie>, err, opts, e))
    case Done{+opts2}:
      (w, a) = s
      eo = Equal.cong(Opts.Res(), List<&2, I.Ie>, x => P.Res.value(B.Err, List<&2, I.Ie>, x, opts), Done{ie <> opts2}, Done{opts}, e)
      %eo : {I.Ies.write(_, []) == iei <> r : B.Bytes()}
      sw = Equal.sym(B.Bytes(), I.Ies.write(opts2, []), r2, ih(r2, opts2, ero, a))
      %sw : {I.Ie.write(ie, _) == iei <> r : B.Bytes()}
      w

def Opts.sx_next(+t: Mm.Mm.Type, +f: Nat, +iei: U32, +r: B.Bytes(), +rb: B.Read(I.Ie), erb: {I.Ie.read_body(iei, Mm.Mm.format(t, iei), r) == rb : B.Read(I.Ie)}, +opts: List<&2, I.Ie>, +e: {Mm.Opts.next(rb, left => Mm.Opts.read(f, t, left)) == Done{opts} : Opts.Res()}, f8: {I.fits8(iei) == True{} : Bool}, +ab: {B.all_bytes(r) == True{} : Bool}, ih: @left: B.Bytes() -> @opts2: List<&2, I.Ie> -> {Mm.Opts.read(f, t, left) == Done{opts2} : Opts.Res()} -> {B.all_bytes(left) == True{} : Bool} -> {I.Ies.write(opts2, []) == left : B.Bytes()}) -> {I.Ies.write(opts, []) == iei <> r : B.Bytes()}:
  match rb:
    case Fail{err}:
      Empty.absurd({I.Ies.write(opts, []) == iei <> r : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, I.Ie>, err, opts, e))
    case Done{(+ie, +r2)}:
      Opts.sx_cons(t, f, iei, r, ie, r2, Mm.Opts.read(f, t, r2), {==}, opts, e, Ie.sx(iei, Mm.Mm.format(t, iei), r, ie, r2, f8, erb, ab), ih)

def Opts.sx_iei(+t: Mm.Mm.Type, +f: Nat, +iei: U32, +r: B.Bytes(), +opts: List<&2, I.Ie>, ok: Bool, +ev: {I.fits8(iei) == ok : Bool}, +e: {Mm.Opts.iei(t, iei, r, left => Mm.Opts.read(f, t, left), ok) == Done{opts} : Opts.Res()}, +ab: {B.all_bytes(iei <> r) == True{} : Bool}, ih: @left: B.Bytes() -> @opts2: List<&2, I.Ie> -> {Mm.Opts.read(f, t, left) == Done{opts2} : Opts.Res()} -> {B.all_bytes(left) == True{} : Bool} -> {I.Ies.write(opts2, []) == left : B.Bytes()}) -> {I.Ies.write(opts, []) == iei <> r : B.Bytes()}:
  match ok:
    case False{}:
      Empty.absurd({I.Ies.write(opts, []) == iei <> r : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, I.Ie>, B.Invalid{iei}, opts, e))
    case True{}:
      Opts.sx_next(t, f, iei, r, I.Ie.read_body(iei, Mm.Mm.format(t, iei), r), {==}, opts, e, ev, P.Bool.and_true_r(B.is_byte(iei), B.all_bytes(r), ab), ih)

def Opts.sx(+t: Mm.Mm.Type, +fuel: Nat, +bs: B.Bytes(), +opts: List<&2, I.Ie>, +e: {Mm.Opts.read(fuel, t, bs) == Done{opts} : Opts.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> {I.Ies.write(opts, []) == bs : B.Bytes()}:
  match fuel bs:
    case 0n Nil{}:
      eo = Equal.cong(Opts.Res(), List<&2, I.Ie>, x => P.Res.value(B.Err, List<&2, I.Ie>, x, opts), Done{[]}, Done{opts}, e)
      %eo : {I.Ies.write(_, []) == [] : B.Bytes()}
      {==}
    case 1n+f Nil{}:
      eo = Equal.cong(Opts.Res(), List<&2, I.Ie>, x => P.Res.value(B.Err, List<&2, I.Ie>, x, opts), Done{[]}, Done{opts}, e)
      %eo : {I.Ies.write(_, []) == [] : B.Bytes()}
      {==}
    case 0n b <> r:
      Empty.absurd({I.Ies.write(opts, []) == b <> r : B.Bytes()}, P.Refute.fail_done(B.Err, List<&2, I.Ie>, B.Invalid{b}, opts, e))
    case 1n++f +iei <> +r:
      Opts.sx_iei(t, f, iei, r, opts, I.fits8(iei), {==}, e, ab, left => opts2 => e2 => ab2 => Opts.sx(t, f, left, opts2, e2, ab2))

# The type table inverts: a recognised code is the type's code.
def Type.inv18(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 104) == hit : Bool}, +e: {Mm.Mm.Type.of18.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.DlNasTransport{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 104, P.U32.eq_of_is_eq(b, 104, ev))
    case False{}:
      Empty.absurd({Mm.Mm.Type.code(mt) == b : U32}, P.Refute.none_some(Mm.Mm.Type, mt, e))

def Type.inv17(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 103) == hit : Bool}, +e: {Mm.Mm.Type.of17.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.UlNasTransport{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 103, P.U32.eq_of_is_eq(b, 103, ev))
    case False{}:
      Type.inv18(b, mt, U32.is_eq(b, 104), {==}, e)

def Type.inv16(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 100) == hit : Bool}, +e: {Mm.Mm.Type.of16.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.Status{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 100, P.U32.eq_of_is_eq(b, 100, ev))
    case False{}:
      Type.inv17(b, mt, U32.is_eq(b, 103), {==}, e)

def Type.inv15(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 95) == hit : Bool}, +e: {Mm.Mm.Type.of15.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.SecurityModeReject{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 95, P.U32.eq_of_is_eq(b, 95, ev))
    case False{}:
      Type.inv16(b, mt, U32.is_eq(b, 100), {==}, e)

def Type.inv14(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 94) == hit : Bool}, +e: {Mm.Mm.Type.of14.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.SecurityModeComplete{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 94, P.U32.eq_of_is_eq(b, 94, ev))
    case False{}:
      Type.inv15(b, mt, U32.is_eq(b, 95), {==}, e)

def Type.inv13(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 93) == hit : Bool}, +e: {Mm.Mm.Type.of13.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.SecurityModeCommand{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 93, P.U32.eq_of_is_eq(b, 93, ev))
    case False{}:
      Type.inv14(b, mt, U32.is_eq(b, 94), {==}, e)

def Type.inv12(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 92) == hit : Bool}, +e: {Mm.Mm.Type.of12.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.IdentityResponse{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 92, P.U32.eq_of_is_eq(b, 92, ev))
    case False{}:
      Type.inv13(b, mt, U32.is_eq(b, 93), {==}, e)

def Type.inv11(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 91) == hit : Bool}, +e: {Mm.Mm.Type.of11.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.IdentityRequest{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 91, P.U32.eq_of_is_eq(b, 91, ev))
    case False{}:
      Type.inv12(b, mt, U32.is_eq(b, 92), {==}, e)

def Type.inv10(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 89) == hit : Bool}, +e: {Mm.Mm.Type.of10.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.AuthenticationFailure{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 89, P.U32.eq_of_is_eq(b, 89, ev))
    case False{}:
      Type.inv11(b, mt, U32.is_eq(b, 91), {==}, e)

def Type.inv9(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 88) == hit : Bool}, +e: {Mm.Mm.Type.of9.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.AuthenticationReject{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 88, P.U32.eq_of_is_eq(b, 88, ev))
    case False{}:
      Type.inv10(b, mt, U32.is_eq(b, 89), {==}, e)

def Type.inv8(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 87) == hit : Bool}, +e: {Mm.Mm.Type.of8.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.AuthenticationResponse{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 87, P.U32.eq_of_is_eq(b, 87, ev))
    case False{}:
      Type.inv9(b, mt, U32.is_eq(b, 88), {==}, e)

def Type.inv7(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 86) == hit : Bool}, +e: {Mm.Mm.Type.of7.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.AuthenticationRequest{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 86, P.U32.eq_of_is_eq(b, 86, ev))
    case False{}:
      Type.inv8(b, mt, U32.is_eq(b, 87), {==}, e)

def Type.inv6(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 84) == hit : Bool}, +e: {Mm.Mm.Type.of6.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.ConfigurationUpdateCommand{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 84, P.U32.eq_of_is_eq(b, 84, ev))
    case False{}:
      Type.inv7(b, mt, U32.is_eq(b, 86), {==}, e)

def Type.inv5(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 70) == hit : Bool}, +e: {Mm.Mm.Type.of5.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.DeregistrationAcceptUe{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 70, P.U32.eq_of_is_eq(b, 70, ev))
    case False{}:
      Type.inv6(b, mt, U32.is_eq(b, 84), {==}, e)

def Type.inv4(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 69) == hit : Bool}, +e: {Mm.Mm.Type.of4.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.DeregistrationRequestUe{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 69, P.U32.eq_of_is_eq(b, 69, ev))
    case False{}:
      Type.inv5(b, mt, U32.is_eq(b, 70), {==}, e)

def Type.inv3(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 68) == hit : Bool}, +e: {Mm.Mm.Type.of3.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.RegistrationReject{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 68, P.U32.eq_of_is_eq(b, 68, ev))
    case False{}:
      Type.inv4(b, mt, U32.is_eq(b, 69), {==}, e)

def Type.inv2(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 67) == hit : Bool}, +e: {Mm.Mm.Type.of2.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.RegistrationComplete{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 67, P.U32.eq_of_is_eq(b, 67, ev))
    case False{}:
      Type.inv3(b, mt, U32.is_eq(b, 68), {==}, e)

def Type.inv1(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 66) == hit : Bool}, +e: {Mm.Mm.Type.of1.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.RegistrationAccept{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 66, P.U32.eq_of_is_eq(b, 66, ev))
    case False{}:
      Type.inv2(b, mt, U32.is_eq(b, 67), {==}, e)

def Type.inv0(+b: U32, +mt: Mm.Mm.Type, hit: Bool, +ev: {U32.is_eq(b, 65) == hit : Bool}, +e: {Mm.Mm.Type.of0.pick(b, hit) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  match hit:
    case True{}:
      em = Equal.cong(Maybe<&2, Mm.Mm.Type>, Mm.Mm.Type, x => P.Maybe.value(Mm.Mm.Type, x, mt), Some{Mm.RegistrationRequest{}}, Some{mt}, e)
      %em : {Mm.Mm.Type.code(_) == b : U32}
      Equal.sym(U32, b, 65, P.U32.eq_of_is_eq(b, 65, ev))
    case False{}:
      Type.inv1(b, mt, U32.is_eq(b, 66), {==}, e)

def Type.of_inv(+b: U32, +mt: Mm.Mm.Type, +e: {Mm.Mm.Type.of(b) == Some{mt} : Maybe<&2, Mm.Mm.Type>}) -> {Mm.Mm.Type.code(mt) == b : U32}:
  Type.inv0(b, mt, U32.is_eq(b, 65), {==}, e)

def Msg.sx_fin(+epd: U32, +sht: U32, +code: U32, +r: B.Bytes(), +mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +rest: B.Bytes(), +opts: List<&2, I.Ie>, +m: Mm.Mm, e126: {epd == 126 : U32}, e0: {sht == 0 : U32}, ec: {Mm.Mm.Type.code(mt) == code : U32}, em: {Mm.Mm{mt, fields, opts} == m : Mm.Mm}, wf: {I.Fields.write(fields, rest) == r : B.Bytes()}, wo: {I.Ies.write(opts, []) == rest : B.Bytes()}) -> {Mm.Mm.write(m) == epd <> sht <> code <> r : B.Bytes()}:
  %em : {Mm.Mm.write(_) == epd <> sht <> code <> r : B.Bytes()}
  s126 = Equal.sym(U32, epd, 126, e126)
  %s126 : {Mm.Mm.write(Mm.Mm{mt, fields, opts}) == _ <> sht <> code <> r : B.Bytes()}
  s0 = Equal.sym(U32, sht, 0, e0)
  %s0 : {Mm.Mm.write(Mm.Mm{mt, fields, opts}) == 126 <> _ <> code <> r : B.Bytes()}
  c8 = Equal.sym(U32, U32.and(255, Mm.Mm.Type.code(mt)), Mm.Mm.Type.code(mt), Type.code8(mt))
  %c8 : {126 <> 0 <> _ <> I.Fields.write(fields, I.Ies.write(opts, [])) == 126 <> 0 <> code <> r : B.Bytes()}
  %ec : {126 <> 0 <> Mm.Mm.Type.code(mt) <> I.Fields.write(fields, I.Ies.write(opts, [])) == 126 <> 0 <> _ <> r : B.Bytes()}
  swo = Equal.sym(B.Bytes(), I.Ies.write(opts, []), rest, wo)
  %swo : {126 <> 0 <> Mm.Mm.Type.code(mt) <> I.Fields.write(fields, _) == 126 <> 0 <> Mm.Mm.Type.code(mt) <> r : B.Bytes()}
  swf = Equal.sym(B.Bytes(), I.Fields.write(fields, rest), r, wf)
  %swf : {126 <> 0 <> Mm.Mm.Type.code(mt) <> _ == 126 <> 0 <> Mm.Mm.Type.code(mt) <> r : B.Bytes()}
  {==}

def Msg.sx_opts(+ro: Opts.Res(), +epd: U32, +sht: U32, +code: U32, +r: B.Bytes(), +mt: Mm.Mm.Type, +fields: List<&2, I.Field>, +rest: B.Bytes(), +m: Mm.Mm, e126: {epd == 126 : U32}, e0: {sht == 0 : U32}, ec: {Mm.Mm.Type.code(mt) == code : U32}, ero: {Mm.Opts.read(List.length(&2, U32, rest), mt, rest) == ro : Opts.Res()}, +e: {Mm.Mm.r_opts(mt, fields, ro) == Done{m} : Msg.Res()}, s: Fields.Sx(fields, rest, r)) -> {Mm.Mm.write(m) == epd <> sht <> code <> r : B.Bytes()}:
  match ro:
    case Fail{err}:
      Empty.absurd({Mm.Mm.write(m) == epd <> sht <> code <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Mm.Mm, err, m, e))
    case Done{+opts}:
      (wf, ar) = s
      Msg.sx_fin(epd, sht, code, r, mt, fields, rest, opts, m, e126, e0, ec, Equal.cong(Msg.Res(), Mm.Mm, x => P.Res.value(B.Err, Mm.Mm, x, m), Done{Mm.Mm{mt, fields, opts}}, Done{m}, e), wf, Opts.sx(mt, List.length(&2, U32, rest), rest, opts, ero, ar))

def Msg.sx_fields(+rf: B.Read(List<&2, I.Field>), +epd: U32, +sht: U32, +code: U32, +r: B.Bytes(), +mt: Mm.Mm.Type, +m: Mm.Mm, e126: {epd == 126 : U32}, e0: {sht == 0 : U32}, ec: {Mm.Mm.Type.code(mt) == code : U32}, erf: {I.Fields.read(Mm.Mm.layout(mt), r) == rf : B.Read(List<&2, I.Field>)}, +e: {Mm.Mm.r_fields(mt, rf) == Done{m} : Msg.Res()}, +ab: {B.all_bytes(r) == True{} : Bool}) -> {Mm.Mm.write(m) == epd <> sht <> code <> r : B.Bytes()}:
  match rf:
    case Fail{err}:
      Empty.absurd({Mm.Mm.write(m) == epd <> sht <> code <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Mm.Mm, err, m, e))
    case Done{(+fields, +rest)}:
      Msg.sx_opts(Mm.Opts.read(List.length(&2, U32, rest), mt, rest), epd, sht, code, r, mt, fields, rest, m, e126, e0, ec, {==}, e, Fields.sx(Mm.Mm.layout(mt), r, fields, rest, erf, ab))

def Msg.sx_type(+tm: Maybe<&2, Mm.Mm.Type>, +epd: U32, +sht: U32, +code: U32, +r: B.Bytes(), +m: Mm.Mm, e126: {epd == 126 : U32}, e0: {sht == 0 : U32}, etm: {Mm.Mm.Type.of(code) == tm : Maybe<&2, Mm.Mm.Type>}, +e: {Mm.Mm.r_type(code, r, tm) == Done{m} : Msg.Res()}, +ab: {B.all_bytes(code <> r) == True{} : Bool}) -> {Mm.Mm.write(m) == epd <> sht <> code <> r : B.Bytes()}:
  match tm:
    case None{}:
      Empty.absurd({Mm.Mm.write(m) == epd <> sht <> code <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Mm.Mm, B.Unsupported{code}, m, e))
    case Some{+mt}:
      Msg.sx_fields(I.Fields.read(Mm.Mm.layout(mt), r), epd, sht, code, r, mt, m, e126, e0, Type.of_inv(code, mt, etm), {==}, e, P.Bool.and_true_r(B.is_byte(code), B.all_bytes(r), ab))

def Msg.sx_sht(ok: Bool, +epd: U32, +sht: U32, +r: B.Bytes(), +m: Mm.Mm, e126: {epd == 126 : U32}, +ev: {U32.is_eq(sht, 0) == ok : Bool}, +e: {Mm.Mm.r_sht(r, sht, ok) == Done{m} : Msg.Res()}, +ab: {B.all_bytes(sht <> r) == True{} : Bool}) -> {Mm.Mm.write(m) == epd <> sht <> r : B.Bytes()}:
  match ok:
    case False{}:
      Empty.absurd({Mm.Mm.write(m) == epd <> sht <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Mm.Mm, B.Invalid{sht}, m, e))
    case True{}:
      match r:
        case Nil{}:
          Empty.absurd({Mm.Mm.write(m) == epd <> sht <> [] : B.Bytes()}, P.Refute.fail_done(B.Err, Mm.Mm, B.Short{}, m, e))
        case +code <> +r2:
          Msg.sx_type(Mm.Mm.Type.of(code), epd, sht, code, r2, m, e126, P.U32.eq_of_is_eq(sht, 0, ev), {==}, e, P.Bool.and_true_r(B.is_byte(sht), B.all_bytes(code <> r2), ab))

def Msg.sx_epd(ok: Bool, +epd: U32, +r: B.Bytes(), +m: Mm.Mm, +ev: {U32.is_eq(epd, 126) == ok : Bool}, +e: {Mm.Mm.r_epd(r, epd, ok) == Done{m} : Msg.Res()}, +ab: {B.all_bytes(epd <> r) == True{} : Bool}) -> {Mm.Mm.write(m) == epd <> r : B.Bytes()}:
  match ok:
    case False{}:
      Empty.absurd({Mm.Mm.write(m) == epd <> r : B.Bytes()}, P.Refute.fail_done(B.Err, Mm.Mm, B.Invalid{epd}, m, e))
    case True{}:
      match r:
        case Nil{}:
          Empty.absurd({Mm.Mm.write(m) == [epd] : B.Bytes()}, P.Refute.fail_done(B.Err, Mm.Mm, B.Short{}, m, e))
        case +sht <> +r2:
          Msg.sx_sht(U32.is_eq(sht, 0), epd, sht, r2, m, P.U32.eq_of_is_eq(epd, 126, ev), {==}, e, P.Bool.and_true_r(B.is_byte(epd), B.all_bytes(sht <> r2), ab))

def Msg.sx(+bs: B.Bytes(), +m: Mm.Mm, +e: {Mm.Mm.read(bs) == Done{m} : Msg.Res()}, +ab: {B.all_bytes(bs) == True{} : Bool}) -> {Mm.Mm.write(m) == bs : B.Bytes()}:
  match bs:
    case Nil{}:
      Empty.absurd({Mm.Mm.write(m) == [] : B.Bytes()}, P.Refute.fail_done(B.Err, Mm.Mm, B.Short{}, m, e))
    case +epd <> +r:
      Msg.sx_epd(U32.is_eq(epd, 126), epd, r, m, {==}, e, ab)

def L.nas.mm.suffix(bs, m, e, ab):
  Msg.sx(bs, m, e, ab)
