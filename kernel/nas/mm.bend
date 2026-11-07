import Base
import ../bytes.bend as B
import ./ie.bend as I

# Plain 5GMM messages (TS 24.501 §8.2): the message type, its mandatory
# fields in the order and formats of its table, then the optional IEs in wire
# order. Protected messages are opened by kernel/nas/security.bend first.

type Mm.Type is Data:
  RegistrationRequest{}
  RegistrationAccept{}
  RegistrationComplete{}
  RegistrationReject{}
  DeregistrationRequestUe{}
  DeregistrationAcceptUe{}
  ConfigurationUpdateCommand{}
  AuthenticationRequest{}
  AuthenticationResponse{}
  AuthenticationReject{}
  AuthenticationFailure{}
  IdentityRequest{}
  IdentityResponse{}
  SecurityModeCommand{}
  SecurityModeComplete{}
  SecurityModeReject{}
  Status{}
  UlNasTransport{}
  DlNasTransport{}
  ServiceRequest{}
  ServiceReject{}

def Mm.Type.code(t: Mm.Type) -> U32:
  match t:
    case RegistrationRequest{}:
      65
    case RegistrationAccept{}:
      66
    case RegistrationComplete{}:
      67
    case RegistrationReject{}:
      68
    case DeregistrationRequestUe{}:
      69
    case DeregistrationAcceptUe{}:
      70
    case ConfigurationUpdateCommand{}:
      84
    case AuthenticationRequest{}:
      86
    case AuthenticationResponse{}:
      87
    case AuthenticationReject{}:
      88
    case AuthenticationFailure{}:
      89
    case IdentityRequest{}:
      91
    case IdentityResponse{}:
      92
    case SecurityModeCommand{}:
      93
    case SecurityModeComplete{}:
      94
    case SecurityModeReject{}:
      95
    case Status{}:
      100
    case UlNasTransport{}:
      103
    case DlNasTransport{}:
      104
    case ServiceRequest{}:
      76
    case ServiceReject{}:
      77

def Mm.Type.of20.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{ServiceReject{}}
    case False{}:
      None{}

def Mm.Type.of20(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of20.pick(b, U32.is_eq(b, 77))

def Mm.Type.of19.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{ServiceRequest{}}
    case False{}:
      Mm.Type.of20(b)

def Mm.Type.of19(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of19.pick(b, U32.is_eq(b, 76))

def Mm.Type.of18.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{DlNasTransport{}}
    case False{}:
      Mm.Type.of19(b)

def Mm.Type.of18(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of18.pick(b, U32.is_eq(b, 104))

def Mm.Type.of17.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{UlNasTransport{}}
    case False{}:
      Mm.Type.of18(b)

def Mm.Type.of17(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of17.pick(b, U32.is_eq(b, 103))

def Mm.Type.of16.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{Status{}}
    case False{}:
      Mm.Type.of17(b)

def Mm.Type.of16(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of16.pick(b, U32.is_eq(b, 100))

def Mm.Type.of15.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{SecurityModeReject{}}
    case False{}:
      Mm.Type.of16(b)

def Mm.Type.of15(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of15.pick(b, U32.is_eq(b, 95))

def Mm.Type.of14.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{SecurityModeComplete{}}
    case False{}:
      Mm.Type.of15(b)

def Mm.Type.of14(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of14.pick(b, U32.is_eq(b, 94))

def Mm.Type.of13.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{SecurityModeCommand{}}
    case False{}:
      Mm.Type.of14(b)

def Mm.Type.of13(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of13.pick(b, U32.is_eq(b, 93))

def Mm.Type.of12.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{IdentityResponse{}}
    case False{}:
      Mm.Type.of13(b)

def Mm.Type.of12(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of12.pick(b, U32.is_eq(b, 92))

def Mm.Type.of11.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{IdentityRequest{}}
    case False{}:
      Mm.Type.of12(b)

def Mm.Type.of11(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of11.pick(b, U32.is_eq(b, 91))

def Mm.Type.of10.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{AuthenticationFailure{}}
    case False{}:
      Mm.Type.of11(b)

def Mm.Type.of10(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of10.pick(b, U32.is_eq(b, 89))

def Mm.Type.of9.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{AuthenticationReject{}}
    case False{}:
      Mm.Type.of10(b)

def Mm.Type.of9(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of9.pick(b, U32.is_eq(b, 88))

def Mm.Type.of8.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{AuthenticationResponse{}}
    case False{}:
      Mm.Type.of9(b)

def Mm.Type.of8(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of8.pick(b, U32.is_eq(b, 87))

def Mm.Type.of7.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{AuthenticationRequest{}}
    case False{}:
      Mm.Type.of8(b)

def Mm.Type.of7(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of7.pick(b, U32.is_eq(b, 86))

def Mm.Type.of6.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{ConfigurationUpdateCommand{}}
    case False{}:
      Mm.Type.of7(b)

def Mm.Type.of6(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of6.pick(b, U32.is_eq(b, 84))

def Mm.Type.of5.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{DeregistrationAcceptUe{}}
    case False{}:
      Mm.Type.of6(b)

def Mm.Type.of5(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of5.pick(b, U32.is_eq(b, 70))

def Mm.Type.of4.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{DeregistrationRequestUe{}}
    case False{}:
      Mm.Type.of5(b)

def Mm.Type.of4(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of4.pick(b, U32.is_eq(b, 69))

def Mm.Type.of3.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{RegistrationReject{}}
    case False{}:
      Mm.Type.of4(b)

def Mm.Type.of3(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of3.pick(b, U32.is_eq(b, 68))

def Mm.Type.of2.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{RegistrationComplete{}}
    case False{}:
      Mm.Type.of3(b)

def Mm.Type.of2(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of2.pick(b, U32.is_eq(b, 67))

def Mm.Type.of1.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{RegistrationAccept{}}
    case False{}:
      Mm.Type.of2(b)

def Mm.Type.of1(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of1.pick(b, U32.is_eq(b, 66))

def Mm.Type.of0.pick(b: U32, hit: Bool) -> Maybe<&2, Mm.Type>:
  match hit:
    case True{}:
      Some{RegistrationRequest{}}
    case False{}:
      Mm.Type.of1(b)

def Mm.Type.of0(+b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of0.pick(b, U32.is_eq(b, 65))

# The message type of a message type byte (TS 24.501 Table 9.7.1).
def Mm.Type.of(b: U32) -> Maybe<&2, Mm.Type>:
  Mm.Type.of0(b)

# Mandatory fields of each message (TS 24.501 Tables 8.2.x.1.1).
def Mm.layout(t: Mm.Type) -> List<&2, I.Lay>:
  match t:
    case RegistrationRequest{}:
      [I.V1{}, I.LvE{}]
    case RegistrationAccept{}:
      [I.Lv{}]
    case RegistrationComplete{}:
      []
    case RegistrationReject{}:
      [I.V1{}]
    case DeregistrationRequestUe{}:
      [I.V1{}, I.LvE{}]
    case DeregistrationAcceptUe{}:
      []
    case ConfigurationUpdateCommand{}:
      []
    case AuthenticationRequest{}:
      [I.V1{}, I.Lv{}]
    case AuthenticationResponse{}:
      []
    case AuthenticationReject{}:
      []
    case AuthenticationFailure{}:
      [I.V1{}]
    case IdentityRequest{}:
      [I.V1{}]
    case IdentityResponse{}:
      [I.LvE{}]
    case SecurityModeCommand{}:
      [I.V1{}, I.V1{}, I.Lv{}]
    case SecurityModeComplete{}:
      []
    case SecurityModeReject{}:
      [I.V1{}]
    case Status{}:
      [I.V1{}]
    case UlNasTransport{}:
      [I.V1{}, I.LvE{}]
    case DlNasTransport{}:
      [I.V1{}, I.LvE{}]
    case ServiceRequest{}:
      [I.V1{}, I.LvE{}]
    case ServiceReject{}:
      [I.V1{}]

# Optional IEs below 0x80 that are not TLV (TS 24.501 Tables 8.2.x.1.1).
def Mm.table(t: Mm.Type) -> List<&2, I.Rule>:
  match t:
    case RegistrationRequest{}:
      [I.Rule{82, I.LowTv{6n}}, I.Rule{112, I.LowTlvE{}}, I.Rule{113, I.LowTlvE{}}, I.Rule{116, I.LowTlvE{}}, I.Rule{119, I.LowTlvE{}}, I.Rule{123, I.LowTlvE{}}]
    case RegistrationAccept{}:
      [I.Rule{118, I.LowTlvE{}}, I.Rule{119, I.LowTlvE{}}, I.Rule{121, I.LowTlvE{}}]
    case RegistrationComplete{}:
      [I.Rule{115, I.LowTlvE{}}]
    case RegistrationReject{}:
      [I.Rule{120, I.LowTlvE{}}]
    case DeregistrationRequestUe{}:
      []
    case DeregistrationAcceptUe{}:
      []
    case ConfigurationUpdateCommand{}:
      [I.Rule{70, I.LowTv{1n}}, I.Rule{71, I.LowTv{7n}}, I.Rule{118, I.LowTlvE{}}, I.Rule{119, I.LowTlvE{}}, I.Rule{121, I.LowTlvE{}}]
    case AuthenticationRequest{}:
      [I.Rule{33, I.LowTv{16n}}, I.Rule{120, I.LowTlvE{}}]
    case AuthenticationResponse{}:
      [I.Rule{120, I.LowTlvE{}}]
    case AuthenticationReject{}:
      [I.Rule{120, I.LowTlvE{}}]
    case AuthenticationFailure{}:
      []
    case IdentityRequest{}:
      []
    case IdentityResponse{}:
      []
    case SecurityModeCommand{}:
      [I.Rule{87, I.LowTv{1n}}, I.Rule{120, I.LowTlvE{}}]
    case SecurityModeComplete{}:
      [I.Rule{113, I.LowTlvE{}}, I.Rule{119, I.LowTlvE{}}]
    case SecurityModeReject{}:
      []
    case Status{}:
      []
    case UlNasTransport{}:
      [I.Rule{18, I.LowTv{1n}}, I.Rule{89, I.LowTv{1n}}]
    case DlNasTransport{}:
      [I.Rule{18, I.LowTv{1n}}, I.Rule{88, I.LowTv{1n}}]
    case ServiceRequest{}:
      [I.Rule{113, I.LowTlvE{}}]
    case ServiceReject{}:
      [I.Rule{117, I.LowTlvE{}}, I.Rule{120, I.LowTlvE{}}]

type Mm is Data:
  Mm{mt: Mm.Type, fields: List<&2, I.Field>, opts: List<&2, I.Ie>}

def Mm.mt(m: Mm) -> Mm.Type:
  match m:
    case Mm{mt, fields, opts}:
      mt

def Mm.fields(m: Mm) -> List<&2, I.Field>:
  match m:
    case Mm{mt, fields, opts}:
      fields

def Mm.opts(m: Mm) -> List<&2, I.Ie>:
  match m:
    case Mm{mt, fields, opts}:
      opts

def Mm.valid(m: Mm) -> Bool:
  match m:
    case Mm{+mt, fields, opts}:
      Bool.and(I.Fields.valid(Mm.layout(mt), fields), I.Opts.valid(Mm.table(mt), opts))

def Mm.write(m: Mm) -> B.Bytes():
  match m:
    case Mm{mt, fields, opts}:
      126 <> 0 <> B.write_u8(Mm.Type.code(mt), I.Fields.write(fields, I.Ies.write(opts, [])))

def Mm.r_opts(mt: Mm.Type, fields: List<&2, I.Field>, r: Result<&2, &2, B.Err, List<&2, I.Ie>>) -> Result<&2, &2, B.Err, Mm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{opts}:
      Done{Mm{mt, fields, opts}}

def Mm.r_fields(+mt: Mm.Type, r: B.Read(List<&2, I.Field>)) -> Result<&2, &2, B.Err, Mm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(fields, +rest)}:
      Mm.r_opts(mt, fields, I.Opts.read(List.length(&2, U32, rest), Mm.table(mt), rest))

def Mm.r_type(code: U32, rest: B.Bytes(), t: Maybe<&2, Mm.Type>) -> Result<&2, &2, B.Err, Mm>:
  match t:
    case None{}:
      Fail{B.Unsupported{code}}
    case Some{+mt}:
      Mm.r_fields(mt, I.Fields.read(Mm.layout(mt), rest))

def Mm.r_mt(r: B.Read(U32)) -> Result<&2, &2, B.Err, Mm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+code, rest)}:
      Mm.r_type(code, rest, Mm.Type.of(code))

def Mm.r_sht(rest: B.Bytes(), sht: U32, plain: Bool) -> Result<&2, &2, B.Err, Mm>:
  match plain:
    case True{}:
      Mm.r_mt(B.u8(rest))
    case False{}:
      Fail{B.Invalid{sht}}

def Mm.r_header(r: B.Read(U32)) -> Result<&2, &2, B.Err, Mm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+sht, rest)}:
      Mm.r_sht(rest, sht, U32.is_eq(sht, 0))

def Mm.r_epd(rest: B.Bytes(), epd: U32, ok: Bool) -> Result<&2, &2, B.Err, Mm>:
  match ok:
    case True{}:
      Mm.r_header(B.u8(rest))
    case False{}:
      Fail{B.Invalid{epd}}

def Mm.r_start(r: B.Read(U32)) -> Result<&2, &2, B.Err, Mm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+epd, rest)}:
      Mm.r_epd(rest, epd, U32.is_eq(epd, 126))

# A plain 5GMM message: EPD 0x7e, security header type 0, message type, fields, optional IEs.
def Mm.read(bs: B.Bytes()) -> Result<&2, &2, B.Err, Mm>:
  Mm.r_start(B.u8(bs))
