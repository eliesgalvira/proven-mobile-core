import Base
import ../bytes.bend as B
import ../plmn.bend as P
import ../suci.bend as S
import ./ie.bend as I

# 5GS mobile identity (TS 24.501 §9.11.3.4): the content of the IE after its
# length. The AMF set identifier and pointer stay packed in `amf` as on the
# wire: set identifier in the high ten bits, pointer in the low six.

type MobileId is Data:
  NoId{}
  Suci{suci: S.Suci}
  Guti{plmn: P.Plmn, region: U32, amf: U32, tmsi: U32}
  Imei{digits: B.Digits()}
  Imeisv{digits: B.Digits()}
  STmsi{amf: U32, tmsi: U32}

def MobileId.Res() -> Data:
  Result<&2, &2, B.Err, MobileId>

# First octets: 1111 0 010, 1111 0 100; low nibbles odd 011, even 101.
def MobileId.guti() -> U32:
  242

def MobileId.s_tmsi() -> U32:
  244

def MobileId.imei() -> U32:
  11

def MobileId.imeisv() -> U32:
  5

def MobileId.amf_set(amf: U32) -> U32:
  U32.shrn(amf, 6n)

def MobileId.amf_pointer(amf: U32) -> U32:
  U32.and(63, amf)

def MobileId.valid(id: MobileId) -> Bool:
  match id:
    case NoId{}:
      True{}
    case Suci{S.Suci{plmn, routing, scheme, key_id, output}}:
      Bool.and(P.Plmn.valid(plmn), S.Routing.valid(routing))
    case Guti{plmn, region, amf, tmsi}:
      Bool.and(P.Plmn.valid(plmn), Bool.and(B.fits8(region), B.fits16(amf)))
    case Imei{+ds}:
      Bool.and(B.Tbcd.all_digits(ds), Nat.is_eq(List.length(&2, U32, ds), 15n))
    case Imeisv{+ds}:
      Bool.and(B.Tbcd.all_digits(ds), Nat.is_eq(List.length(&2, U32, ds), 16n))
    case STmsi{amf, tmsi}:
      B.fits16(amf)

# Encoding
# --------

def MobileId.write_digits(lo: U32, ds: B.Digits()) -> B.Bytes():
  match ds:
    case Nil{}:
      [lo]
    case d <> more:
      B.write_nibbles(d, lo, B.write_tbcd(more, []))

def MobileId.write(id: MobileId) -> B.Bytes():
  match id:
    case NoId{}:
      [0]
    case Suci{s}:
      S.Suci.write(s)
    case Guti{plmn, region, amf, tmsi}:
      MobileId.guti() <> P.Plmn.write(plmn, B.write_u8(region, B.write_u16(amf, B.write_u32(tmsi, []))))
    case Imei{ds}:
      MobileId.write_digits(MobileId.imei(), ds)
    case Imeisv{ds}:
      MobileId.write_digits(MobileId.imeisv(), ds)
    case STmsi{amf, tmsi}:
      MobileId.s_tmsi() <> B.write_u16(amf, B.write_u32(tmsi, []))

# Decoding
# --------

# Nothing may follow the identity.
def MobileId.end(id: MobileId, rest: B.Bytes()) -> MobileId.Res():
  match rest:
    case Nil{}:
      Done{id}
    case b <> more:
      Fail{B.Invalid{b}}

# The first digit sits in the high nibble of the first octet; the odd/even
# bit and the digit count must agree, so the counts are fixed.
def MobileId.imeisv_of(+h: U32, r: Result<&2, &2, B.Err, B.Digits()>) -> MobileId.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+ds}:
      +d = U32.and(15, U32.shrn(h, 4n))
      B.guard(MobileId, Imeisv{d <> ds}, h, Bool.and(B.Tbcd.is_digit(d), Nat.is_eq(List.length(&2, U32, ds), 15n)))

def MobileId.imei_of(+h: U32, r: Result<&2, &2, B.Err, B.Digits()>) -> MobileId.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+ds}:
      +d = U32.and(15, U32.shrn(h, 4n))
      B.guard(MobileId, Imei{d <> ds}, h, Bool.and(B.Tbcd.is_digit(d), Nat.is_eq(List.length(&2, U32, ds), 14n)))

def MobileId.r5(+h: U32, rest: B.Bytes(), hit: Bool) -> MobileId.Res():
  match hit:
    case True{}:
      MobileId.imeisv_of(h, B.Tbcd.decode(rest))
    case False{}:
      Fail{B.Unsupported{h}}

def MobileId.r3(+h: U32, rest: B.Bytes(), hit: Bool) -> MobileId.Res():
  match hit:
    case True{}:
      MobileId.imei_of(h, B.Tbcd.decode(rest))
    case False{}:
      MobileId.r5(h, rest, U32.is_eq(U32.and(15, h), MobileId.imeisv()))

def MobileId.s_tmsi_tmsi(amf: U32, r: B.Read(U32)) -> MobileId.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(tmsi, rest)}:
      MobileId.end(STmsi{amf, tmsi}, rest)

def MobileId.s_tmsi_ok(amf: U32, rest: B.Bytes(), ok: Bool) -> MobileId.Res():
  match ok:
    case True{}:
      MobileId.s_tmsi_tmsi(amf, B.u32(rest))
    case False{}:
      Fail{B.Invalid{amf}}

def MobileId.s_tmsi_amf(r: B.Read(U32)) -> MobileId.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+amf, rest)}:
      MobileId.s_tmsi_ok(amf, rest, B.fits16(amf))

def MobileId.r4(+h: U32, rest: B.Bytes(), hit: Bool) -> MobileId.Res():
  match hit:
    case True{}:
      MobileId.s_tmsi_amf(B.u16(rest))
    case False{}:
      MobileId.r3(h, rest, U32.is_eq(U32.and(15, h), MobileId.imei()))

def MobileId.guti_tmsi(plmn: P.Plmn, region: U32, amf: U32, r: B.Read(U32)) -> MobileId.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(tmsi, rest)}:
      MobileId.end(Guti{plmn, region, amf, tmsi}, rest)

def MobileId.guti_amf_ok(plmn: P.Plmn, region: U32, amf: U32, rest: B.Bytes(), ok: Bool) -> MobileId.Res():
  match ok:
    case True{}:
      MobileId.guti_tmsi(plmn, region, amf, B.u32(rest))
    case False{}:
      Fail{B.Invalid{amf}}

def MobileId.guti_amf(plmn: P.Plmn, region: U32, r: B.Read(U32)) -> MobileId.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+amf, rest)}:
      MobileId.guti_amf_ok(plmn, region, amf, rest, B.fits16(amf))

def MobileId.guti_region_ok(plmn: P.Plmn, region: U32, rest: B.Bytes(), ok: Bool) -> MobileId.Res():
  match ok:
    case True{}:
      MobileId.guti_amf(plmn, region, B.u16(rest))
    case False{}:
      Fail{B.Invalid{region}}

def MobileId.guti_region(plmn: P.Plmn, r: B.Read(U32)) -> MobileId.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+region, rest)}:
      MobileId.guti_region_ok(plmn, region, rest, B.fits8(region))

def MobileId.guti_plmn(r: B.Read(P.Plmn)) -> MobileId.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(plmn, rest)}:
      MobileId.guti_region(plmn, B.u8(rest))

def MobileId.r2(+h: U32, rest: B.Bytes(), hit: Bool) -> MobileId.Res():
  match hit:
    case True{}:
      MobileId.guti_plmn(P.Plmn.read(rest))
    case False{}:
      MobileId.r4(h, rest, U32.is_eq(h, MobileId.s_tmsi()))

def MobileId.suci_of(r: Result<&2, &2, B.Err, S.Suci>) -> MobileId.Res():
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      Done{Suci{s}}

def MobileId.r1(+h: U32, rest: B.Bytes(), hit: Bool) -> MobileId.Res():
  match hit:
    case True{}:
      MobileId.suci_of(S.Suci.read(h <> rest))
    case False{}:
      MobileId.r2(h, rest, U32.is_eq(h, MobileId.guti()))

def MobileId.r0(+h: U32, rest: B.Bytes(), hit: Bool) -> MobileId.Res():
  match hit:
    case True{}:
      MobileId.end(NoId{}, rest)
    case False{}:
      MobileId.r1(h, rest, U32.is_eq(h, S.Suci.header()))

def MobileId.read(bs: B.Bytes()) -> MobileId.Res():
  match bs:
    case Nil{}:
      Fail{B.Short{}}
    case +h <> rest:
      MobileId.r0(h, rest, U32.is_eq(h, 0))
