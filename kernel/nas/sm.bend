import Base
import ../bytes.bend as B
import ./ie.bend as I

# Plain 5GSM messages (TS 24.501 §8.3): EPD 0x2e, PDU session identity,
# procedure transaction identity, message type, the mandatory fields of the
# message's table, then the optional IEs in wire order.

type Sm.Type is Data:
  EstablishmentRequest{}
  EstablishmentAccept{}
  EstablishmentReject{}
  ModificationRequest{}
  ModificationReject{}
  ReleaseRequest{}
  ReleaseCommand{}
  ReleaseComplete{}
  SmStatus{}

def Sm.epd() -> U32:
  46

def Sm.Type.code(t: Sm.Type) -> U32:
  match t:
    case EstablishmentRequest{}:
      193
    case EstablishmentAccept{}:
      194
    case EstablishmentReject{}:
      195
    case ModificationRequest{}:
      201
    case ModificationReject{}:
      202
    case ReleaseRequest{}:
      209
    case ReleaseCommand{}:
      211
    case ReleaseComplete{}:
      212
    case SmStatus{}:
      214

def Sm.Type.of8.pick(b: U32, hit: Bool) -> Maybe<&2, Sm.Type>:
  match hit:
    case True{}:
      Some{SmStatus{}}
    case False{}:
      None{}

def Sm.Type.of8(+b: U32) -> Maybe<&2, Sm.Type>:
  Sm.Type.of8.pick(b, U32.is_eq(b, 214))

def Sm.Type.of7.pick(b: U32, hit: Bool) -> Maybe<&2, Sm.Type>:
  match hit:
    case True{}:
      Some{ReleaseComplete{}}
    case False{}:
      Sm.Type.of8(b)

def Sm.Type.of7(+b: U32) -> Maybe<&2, Sm.Type>:
  Sm.Type.of7.pick(b, U32.is_eq(b, 212))

def Sm.Type.of6.pick(b: U32, hit: Bool) -> Maybe<&2, Sm.Type>:
  match hit:
    case True{}:
      Some{ReleaseCommand{}}
    case False{}:
      Sm.Type.of7(b)

def Sm.Type.of6(+b: U32) -> Maybe<&2, Sm.Type>:
  Sm.Type.of6.pick(b, U32.is_eq(b, 211))

def Sm.Type.of5.pick(b: U32, hit: Bool) -> Maybe<&2, Sm.Type>:
  match hit:
    case True{}:
      Some{ReleaseRequest{}}
    case False{}:
      Sm.Type.of6(b)

def Sm.Type.of5(+b: U32) -> Maybe<&2, Sm.Type>:
  Sm.Type.of5.pick(b, U32.is_eq(b, 209))

def Sm.Type.of4.pick(b: U32, hit: Bool) -> Maybe<&2, Sm.Type>:
  match hit:
    case True{}:
      Some{ModificationReject{}}
    case False{}:
      Sm.Type.of5(b)

def Sm.Type.of4(+b: U32) -> Maybe<&2, Sm.Type>:
  Sm.Type.of4.pick(b, U32.is_eq(b, 202))

def Sm.Type.of3.pick(b: U32, hit: Bool) -> Maybe<&2, Sm.Type>:
  match hit:
    case True{}:
      Some{ModificationRequest{}}
    case False{}:
      Sm.Type.of4(b)

def Sm.Type.of3(+b: U32) -> Maybe<&2, Sm.Type>:
  Sm.Type.of3.pick(b, U32.is_eq(b, 201))

def Sm.Type.of2.pick(b: U32, hit: Bool) -> Maybe<&2, Sm.Type>:
  match hit:
    case True{}:
      Some{EstablishmentReject{}}
    case False{}:
      Sm.Type.of3(b)

def Sm.Type.of2(+b: U32) -> Maybe<&2, Sm.Type>:
  Sm.Type.of2.pick(b, U32.is_eq(b, 195))

def Sm.Type.of1.pick(b: U32, hit: Bool) -> Maybe<&2, Sm.Type>:
  match hit:
    case True{}:
      Some{EstablishmentAccept{}}
    case False{}:
      Sm.Type.of2(b)

def Sm.Type.of1(+b: U32) -> Maybe<&2, Sm.Type>:
  Sm.Type.of1.pick(b, U32.is_eq(b, 194))

def Sm.Type.of0.pick(b: U32, hit: Bool) -> Maybe<&2, Sm.Type>:
  match hit:
    case True{}:
      Some{EstablishmentRequest{}}
    case False{}:
      Sm.Type.of1(b)

def Sm.Type.of0(+b: U32) -> Maybe<&2, Sm.Type>:
  Sm.Type.of0.pick(b, U32.is_eq(b, 193))

# The message type of a message type byte (TS 24.501 Table 9.7.2).
def Sm.Type.of(b: U32) -> Maybe<&2, Sm.Type>:
  Sm.Type.of0(b)

# Mandatory fields of each message (TS 24.501 Tables 8.3.x.1.1). The
# establishment request's integrity protection maximum data rate is two bytes.
def Sm.layout(t: Sm.Type) -> List<&2, I.Lay>:
  match t:
    case EstablishmentRequest{}:
      [I.V1{}, I.V1{}]
    case EstablishmentAccept{}:
      [I.V1{}, I.LvE{}, I.Lv{}]
    case EstablishmentReject{}:
      [I.V1{}]
    case ModificationRequest{}:
      []
    case ModificationReject{}:
      [I.V1{}]
    case ReleaseRequest{}:
      []
    case ReleaseCommand{}:
      [I.V1{}]
    case ReleaseComplete{}:
      []
    case SmStatus{}:
      [I.V1{}]

# Optional IEs below 0x80 that are not TLV.
def Sm.table(t: Sm.Type) -> List<&2, I.Rule>:
  match t:
    case EstablishmentRequest{}:
      [I.Rule{85, I.LowTv{2n}}, I.Rule{123, I.LowTlvE{}}, I.Rule{31, I.LowTlvE{}}]
    case EstablishmentAccept{}:
      [I.Rule{89, I.LowTv{1n}}, I.Rule{86, I.LowTv{1n}}, I.Rule{117, I.LowTlvE{}}, I.Rule{120, I.LowTlvE{}}, I.Rule{121, I.LowTlvE{}}, I.Rule{123, I.LowTlvE{}}, I.Rule{119, I.LowTlvE{}}, I.Rule{31, I.LowTlvE{}}]
    case EstablishmentReject{}:
      [I.Rule{120, I.LowTlvE{}}, I.Rule{123, I.LowTlvE{}}]
    case ModificationRequest{}:
      [I.Rule{89, I.LowTv{1n}}, I.Rule{85, I.LowTv{2n}}, I.Rule{19, I.LowTv{2n}}, I.Rule{122, I.LowTlvE{}}, I.Rule{121, I.LowTlvE{}}, I.Rule{117, I.LowTlvE{}}, I.Rule{123, I.LowTlvE{}}, I.Rule{116, I.LowTlvE{}}]
    case ModificationReject{}:
      [I.Rule{123, I.LowTlvE{}}]
    case ReleaseRequest{}:
      [I.Rule{89, I.LowTv{1n}}, I.Rule{123, I.LowTlvE{}}]
    case ReleaseCommand{}:
      [I.Rule{120, I.LowTlvE{}}, I.Rule{123, I.LowTlvE{}}]
    case ReleaseComplete{}:
      [I.Rule{89, I.LowTv{1n}}, I.Rule{123, I.LowTlvE{}}]
    case SmStatus{}:
      []

type Sm is Data:
  Sm{psi: U32, pti: U32, mt: Sm.Type, fields: List<&2, I.Field>, opts: List<&2, I.Ie>}

def Sm.psi(m: Sm) -> U32:
  match m:
    case Sm{psi, pti, mt, fields, opts}:
      psi

def Sm.pti(m: Sm) -> U32:
  match m:
    case Sm{psi, pti, mt, fields, opts}:
      pti

def Sm.mt(m: Sm) -> Sm.Type:
  match m:
    case Sm{psi, pti, mt, fields, opts}:
      mt

def Sm.fields(m: Sm) -> List<&2, I.Field>:
  match m:
    case Sm{psi, pti, mt, fields, opts}:
      fields

def Sm.opts(m: Sm) -> List<&2, I.Ie>:
  match m:
    case Sm{psi, pti, mt, fields, opts}:
      opts

def Sm.valid(m: Sm) -> Bool:
  match m:
    case Sm{psi, pti, +mt, fields, opts}:
      Bool.and(B.fits8(psi), Bool.and(B.fits8(pti), Bool.and(I.Fields.valid(Sm.layout(mt), fields), I.Opts.valid(Sm.table(mt), opts))))

def Sm.write(m: Sm) -> B.Bytes():
  match m:
    case Sm{psi, pti, mt, fields, opts}:
      Sm.epd() <> B.write_u8(psi, B.write_u8(pti, B.write_u8(Sm.Type.code(mt), I.Fields.write(fields, I.Ies.write(opts, [])))))

def Sm.r_opts(psi: U32, pti: U32, mt: Sm.Type, fields: List<&2, I.Field>, r: Result<&2, &2, B.Err, List<&2, I.Ie>>) -> Result<&2, &2, B.Err, Sm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{opts}:
      Done{Sm{psi, pti, mt, fields, opts}}

def Sm.r_fields(psi: U32, pti: U32, +mt: Sm.Type, r: B.Read(List<&2, I.Field>)) -> Result<&2, &2, B.Err, Sm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(fields, +rest)}:
      Sm.r_opts(psi, pti, mt, fields, I.Opts.read(List.length(&2, U32, rest), Sm.table(mt), rest))

def Sm.r_type(psi: U32, pti: U32, code: U32, rest: B.Bytes(), t: Maybe<&2, Sm.Type>) -> Result<&2, &2, B.Err, Sm>:
  match t:
    case None{}:
      Fail{B.Unsupported{code}}
    case Some{+mt}:
      Sm.r_fields(psi, pti, mt, I.Fields.read(Sm.layout(mt), rest))

def Sm.r_mt(psi: U32, pti: U32, r: B.Read(U32)) -> Result<&2, &2, B.Err, Sm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+code, rest)}:
      Sm.r_type(psi, pti, code, rest, Sm.Type.of(code))

def Sm.r_pti_ok(psi: U32, pti: U32, rest: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, Sm>:
  match ok:
    case True{}:
      Sm.r_mt(psi, pti, B.u8(rest))
    case False{}:
      Fail{B.Invalid{pti}}

def Sm.r_pti(psi: U32, r: B.Read(U32)) -> Result<&2, &2, B.Err, Sm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+pti, rest)}:
      Sm.r_pti_ok(psi, pti, rest, B.fits8(pti))

def Sm.r_psi_ok(psi: U32, rest: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, Sm>:
  match ok:
    case True{}:
      Sm.r_pti(psi, B.u8(rest))
    case False{}:
      Fail{B.Invalid{psi}}

def Sm.r_psi(r: B.Read(U32)) -> Result<&2, &2, B.Err, Sm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+psi, rest)}:
      Sm.r_psi_ok(psi, rest, B.fits8(psi))

def Sm.r_epd(rest: B.Bytes(), epd: U32, ok: Bool) -> Result<&2, &2, B.Err, Sm>:
  match ok:
    case True{}:
      Sm.r_psi(B.u8(rest))
    case False{}:
      Fail{B.Invalid{epd}}

def Sm.r_start(r: B.Read(U32)) -> Result<&2, &2, B.Err, Sm>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+epd, rest)}:
      Sm.r_epd(rest, epd, U32.is_eq(epd, Sm.epd()))

def Sm.read(bs: B.Bytes()) -> Result<&2, &2, B.Err, Sm>:
  Sm.r_start(B.u8(bs))
