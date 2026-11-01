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
