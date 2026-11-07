import Base
import ../bytes.bend as B
import ../plmn.bend as P
import ./ie.bend as I
import ./mm.bend as M

# Typed views of the 5GMM information elements the capture carries
# (TS 24.501 §9.11.3 and the TS 24.008 elements it reuses). Each reader takes
# the content of an IE as the generic codec sliced it and must consume all of
# it; each writer gives the content back.

# The whole content, when it has an acceptable length.
def Bytes.exactly(+bs: B.Bytes(), n: Nat) -> B.Res(B.Bytes()):
  B.guard(B.Bytes(), bs, 0, Nat.is_eq(List.length(&2, U32, bs), n))

def Bytes.between(+bs: B.Bytes(), lo: Nat, hi: Nat) -> B.Res(B.Bytes()):
  B.guard(B.Bytes(), bs, 0, Bool.and(Nat.is_ge(List.length(&2, U32, bs), lo), Nat.is_le(List.length(&2, U32, bs), hi)))

# A one-byte content whose spare bits (under `mask`) are zero.
def Byte.one(bs: B.Bytes(), mask: U32) -> B.Res(U32):
  match bs:
    case +v <> Nil{}:
      B.guard(U32, v, v, U32.is_eq(U32.and(mask, v), 0))
    case _:
      Fail{B.Invalid{0}}

def Bit.of(v: U32, +bit: U32) -> Bool:
  U32.is_eq(U32.and(bit, v), bit)

def Bit.to(flag: Bool, bit: U32) -> U32:
  match flag:
    case True{}:
      bit
    case False{}:
      0

# Half octets (§9.11.3.7 registration type, §9.11.3.32 ngKSI)
# -----------------------------------------------------------

# A flag bit and a three-bit value: TSC with the key set identifier, or
# follow-on request with the registration type.
type Half is Data:
  Half{flag: Bool, value: U32}

def Half.of(+n: U32) -> Half:
  Half{Bit.of(n, 8), U32.and(7, n)}

def Half.nibble(h: Half) -> U32:
  match h:
    case Half{flag, value}:
      U32.add(Bit.to(flag, 8), U32.and(7, value))

# The first byte of a Registration request: ngKSI high, registration type low.
def RegHeader.ksi(v: U32) -> Half:
  Half.of(U32.and(15, U32.shrn(v, 4n)))

def RegHeader.reg(v: U32) -> Half:
  Half.of(U32.and(15, v))

def RegHeader.write(ksi: Half, reg: Half) -> U32:
  B.cat4(Half.nibble(reg), Half.nibble(ksi))

def Half.ok(v: U32, ok: Bool) -> B.Res(Half):
  match ok:
    case True{}:
      Done{Half.of(v)}
    case False{}:
      Fail{B.Invalid{v}}

# A byte holding ngKSI in its low nibble and a spare high nibble.
def Ksi.read(+v: U32) -> B.Res(Half):
  Half.ok(v, U32.is_eq(U32.and(240, v), 0))

# NAS security algorithms (§9.11.3.34)
# ------------------------------------

type SecAlgs is Data:
  SecAlgs{ciphering: U32, integrity: U32}

def SecAlgs.of(+v: U32) -> SecAlgs:
  SecAlgs{U32.and(15, U32.shrn(v, 4n)), U32.and(15, v)}

def SecAlgs.write(a: SecAlgs) -> U32:
  match a:
    case SecAlgs{ciphering, integrity}:
      B.cat4(integrity, ciphering)

# Payload container type (§9.11.3.40): the low nibble of its byte.
def ContainerType.read(+v: U32) -> B.Res(U32):
  B.guard(U32, U32.and(15, v), U32.and(15, v), U32.is_eq(U32.and(240, v), 0))

# UE security capability (§9.11.3.54)
# -----------------------------------

# 5G algorithms, then up to six bytes of E-UTRA algorithms and spare.
type SecCap is Data:
  SecCap{ea: U32, ia: U32, eutra: B.Bytes()}

def SecCap.tail(+ea: U32, ia: U32, rest: B.Bytes(), ok: Bool) -> B.Res(SecCap):
  match ok:
    case True{}:
      Done{SecCap{ea, ia, rest}}
    case False{}:
      Fail{B.Invalid{ea}}

def SecCap.read(bs: B.Bytes()) -> B.Res(SecCap):
  match bs:
    case ea <> ia <> +rest:
      SecCap.tail(ea, ia, rest, Nat.is_le(List.length(&2, U32, rest), 6n))
    case _:
      Fail{B.Short{}}

def SecCap.write(c: SecCap) -> B.Bytes():
  match c:
    case SecCap{ea, ia, eutra}:
      ea <> ia <> eutra

# 5GMM capability (§9.11.3.1): one byte of flags, up to twelve more.
type MmCap is Data:
  MmCap{flags: U32, more: B.Bytes()}

def MmCap.tail(+flags: U32, more: B.Bytes(), ok: Bool) -> B.Res(MmCap):
  match ok:
    case True{}:
      Done{MmCap{flags, more}}
    case False{}:
      Fail{B.Invalid{flags}}

def MmCap.read(bs: B.Bytes()) -> B.Res(MmCap):
  match bs:
    case flags <> +more:
      MmCap.tail(flags, more, Nat.is_le(List.length(&2, U32, more), 12n))
    case Nil{}:
      Fail{B.Short{}}

def MmCap.write(c: MmCap) -> B.Bytes():
  match c:
    case MmCap{flags, more}:
      flags <> more

# S-NSSAI (§9.11.2.8) and NSSAI (§9.11.3.37)
# ------------------------------------------

# The five shapes the length allows: SST, with a mapped SST, with an SD, with
# both, and with a mapped SD as well.
type SNssai is Data:
  Sst{sst: U32}
  SstMapped{sst: U32, msst: U32}
  SstSd{sst: U32, sd: U32}
  SstSdMapped{sst: U32, sd: U32, msst: U32}
  SstFull{sst: U32, sd: U32, msst: U32, msd: U32}

def SNssai.read(bs: B.Bytes()) -> B.Res(SNssai):
  match bs:
    case sst <> Nil{}:
      Done{Sst{sst}}
    case sst <> msst <> Nil{}:
      Done{SstMapped{sst, msst}}
    case sst <> s2 <> s1 <> s0 <> Nil{}:
      Done{SstSd{sst, B.cat8(s0, B.cat8(s1, s2))}}
    case sst <> s2 <> s1 <> s0 <> msst <> Nil{}:
      Done{SstSdMapped{sst, B.cat8(s0, B.cat8(s1, s2)), msst}}
    case sst <> s2 <> s1 <> s0 <> msst <> m2 <> m1 <> m0 <> Nil{}:
      Done{SstFull{sst, B.cat8(s0, B.cat8(s1, s2)), msst, B.cat8(m0, B.cat8(m1, m2))}}
    case _:
      Fail{B.Invalid{0}}

def SNssai.write(s: SNssai) -> B.Bytes():
  match s:
    case Sst{sst}:
      [sst]
    case SstMapped{sst, msst}:
      [sst, msst]
    case SstSd{sst, sd}:
      sst <> B.write_u24(sd, [])
    case SstSdMapped{sst, sd, msst}:
      sst <> B.write_u24(sd, [msst])
    case SstFull{sst, sd, msst, msd}:
      sst <> B.write_u24(sd, msst <> B.write_u24(msd, []))

def Nssai.cons(s: B.Res(SNssai), more: B.Res(List<&2, SNssai>)) -> B.Res(List<&2, SNssai>):
  match s:
    case Fail{e}:
      Fail{e}
    case Done{one}:
      match more:
        case Fail{e}:
          Fail{e}
        case Done{list}:
          Done{one <> list}

def Nssai.item(r: B.Read(B.Bytes()), more: B.Bytes() -> B.Res(List<&2, SNssai>)) -> B.Res(List<&2, SNssai>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(body, rest)}:
      Nssai.cons(SNssai.read(body), more(rest))

# Length-prefixed S-NSSAIs to the end of the content; the fuel is the byte count.
def Nssai.go(fuel: Nat, bs: B.Bytes()) -> B.Res(List<&2, SNssai>):
  match fuel bs:
    case _ Nil{}:
      Done{[]}
    case 0n b <> rest:
      Fail{B.Invalid{b}}
    case 1n+f +len <> rest:
      Nssai.item(B.take(U32.to_nat(len), rest), left => Nssai.go(f, left))

def Nssai.read(+bs: B.Bytes()) -> B.Res(List<&2, SNssai>):
  Nssai.go(List.length(&2, U32, bs), bs)

def Nssai.write(ss: List<&2, SNssai>) -> B.Bytes():
  match ss:
    case Nil{}:
      []
    case s <> more:
      +body = SNssai.write(s)
      U32.from_nat(List.length(&2, U32, body)) <> List.append(&2, U32, body, Nssai.write(more))

# 5GS update type (§9.11.3.9A)
# ----------------------------

type UpdateType is Data:
  UpdateType{sms_requested: Bool, ng_ran_rcu: Bool, pnb_ciot: U32, eps_pnb_ciot: U32}

def UpdateType.of(+v: U32) -> UpdateType:
  UpdateType{Bit.of(v, 1), Bit.of(v, 2), U32.and(3, U32.shrn(v, 2n)), U32.and(3, U32.shrn(v, 4n))}

def UpdateType.ok(r: B.Res(U32)) -> B.Res(UpdateType):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      Done{UpdateType.of(v)}

def UpdateType.read(bs: B.Bytes()) -> B.Res(UpdateType):
  UpdateType.ok(Byte.one(bs, 192))

def UpdateType.write(u: UpdateType) -> B.Bytes():
  match u:
    case UpdateType{sms, rcu, pnb, eps}:
      [U32.add(Bit.to(sms, 1), U32.add(Bit.to(rcu, 2), U32.add(U32.shln(U32.and(3, pnb), 2n), U32.shln(U32.and(3, eps), 4n))))]

# Authentication parameters
# -------------------------

# ABBA (§9.11.3.10): at least two bytes.
def Abba.read(bs: B.Bytes()) -> B.Res(B.Bytes()):
  Bytes.between(bs, 2n, 255n)

# RAND, AUTN (§9.11.3.16, §9.11.3.15) and RES* (§9.11.3.17): sixteen bytes.
def Fixed16.read(bs: B.Bytes()) -> B.Res(B.Bytes()):
  Bytes.exactly(bs, 16n)

# IMEISV request (§9.11.3.28): the low nibble of a one-octet IE; 1 means requested.
def ImeisvRequest.read(+nibble: U32) -> B.Res(U32):
  B.guard(U32, U32.and(7, nibble), U32.and(7, nibble), U32.is_eq(U32.and(8, nibble), 0))

# Additional 5G security information (§9.11.3.12)
type AddSecInfo is Data:
  AddSecInfo{hdp: Bool, rinmr: Bool}

def AddSecInfo.ok(r: B.Res(U32)) -> B.Res(AddSecInfo):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+v}:
      Done{AddSecInfo{Bit.of(v, 1), Bit.of(v, 2)}}

def AddSecInfo.read(bs: B.Bytes()) -> B.Res(AddSecInfo):
  AddSecInfo.ok(Byte.one(bs, 252))

def AddSecInfo.write(a: AddSecInfo) -> B.Bytes():
  match a:
    case AddSecInfo{hdp, rinmr}:
      [U32.add(Bit.to(hdp, 1), Bit.to(rinmr, 2))]

# NAS message container (§9.11.3.33): a plain 5GMM message.
def Container.read(bs: B.Bytes()) -> B.Res(M.Mm):
  M.Mm.read(bs)

# 5GS registration result (§9.11.3.6)
# -----------------------------------

type RegResult is Data:
  RegResult{value: U32, sms_allowed: Bool, nssaa: Bool, emergency: Bool}

def RegResult.ok(r: B.Res(U32)) -> B.Res(RegResult):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+v}:
      Done{RegResult{U32.and(7, v), Bit.of(v, 8), Bit.of(v, 16), Bit.of(v, 32)}}

def RegResult.read(bs: B.Bytes()) -> B.Res(RegResult):
  RegResult.ok(Byte.one(bs, 192))

def RegResult.write(r: RegResult) -> B.Bytes():
  match r:
    case RegResult{value, sms, nssaa, emergency}:
      [U32.add(U32.and(7, value), U32.add(Bit.to(sms, 8), U32.add(Bit.to(nssaa, 16), Bit.to(emergency, 32))))]

# 5GS tracking area identity list (§9.11.3.9)
# -------------------------------------------

type Tai is Data:
  Tai{plmn: P.Plmn, tac: U32}

# Partial lists: one PLMN with listed TACs (type 00), one PLMN with `count`
# consecutive TACs from `first` (type 01), or explicit TAIs (type 10).
type TaiPartial is Data:
  Tai00{plmn: P.Plmn, tacs: List<&2, U32>}
  Tai01{plmn: P.Plmn, first: U32, count: Nat}
  Tai10{tais: List<&2, Tai>}

def Tacs.next(r: B.Read(U32), more: B.Bytes() -> B.Read(List<&2, U32>)) -> B.Read(List<&2, U32>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(tac, rest)}:
      B.Read.cons(U32, tac, more(rest))

def Tacs.read(n: Nat, bs: B.Bytes()) -> B.Read(List<&2, U32>):
  match n:
    case 0n:
      Done{([], bs)}
    case 1n+p:
      Tacs.next(B.u24(bs), rest => Tacs.read(p, rest))

def Tais.tac(plmn: P.Plmn, r: B.Read(U32), more: B.Bytes() -> B.Read(List<&2, Tai>)) -> B.Read(List<&2, Tai>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(tac, rest)}:
      B.Read.cons(Tai, Tai{plmn, tac}, more(rest))

def Tais.plmn(r: B.Read(P.Plmn), more: B.Bytes() -> B.Read(List<&2, Tai>)) -> B.Read(List<&2, Tai>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(plmn, rest)}:
      Tais.tac(plmn, B.u24(rest), more)

def Tais.read(n: Nat, bs: B.Bytes()) -> B.Read(List<&2, Tai>):
  match n:
    case 0n:
      Done{([], bs)}
    case 1n+p:
      Tais.plmn(P.Plmn.read(bs), rest => Tais.read(p, rest))

def TaiList.push(item: TaiPartial, r: B.Res(List<&2, TaiPartial>)) -> B.Res(List<&2, TaiPartial>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{list}:
      Done{item <> list}

def TaiList.tacs(plmn: P.Plmn, r: B.Read(List<&2, U32>), more: B.Bytes() -> B.Res(List<&2, TaiPartial>)) -> B.Res(List<&2, TaiPartial>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(tacs, rest)}:
      TaiList.push(Tai00{plmn, tacs}, more(rest))

def TaiList.first(plmn: P.Plmn, n: Nat, r: B.Read(U32), more: B.Bytes() -> B.Res(List<&2, TaiPartial>)) -> B.Res(List<&2, TaiPartial>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(tac, rest)}:
      TaiList.push(Tai01{plmn, tac, n}, more(rest))

def TaiList.tais(r: B.Read(List<&2, Tai>), more: B.Bytes() -> B.Res(List<&2, TaiPartial>)) -> B.Res(List<&2, TaiPartial>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(tais, rest)}:
      TaiList.push(Tai10{tais}, more(rest))

def TaiList.plmn00(n: Nat, r: B.Read(P.Plmn), more: B.Bytes() -> B.Res(List<&2, TaiPartial>)) -> B.Res(List<&2, TaiPartial>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(plmn, rest)}:
      TaiList.tacs(plmn, Tacs.read(n, rest), more)

def TaiList.plmn01(n: Nat, r: B.Read(P.Plmn), more: B.Bytes() -> B.Res(List<&2, TaiPartial>)) -> B.Res(List<&2, TaiPartial>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(plmn, rest)}:
      TaiList.first(plmn, n, B.u24(rest), more)

def TaiList.kind(+h: U32, rest: B.Bytes(), more: B.Bytes() -> B.Res(List<&2, TaiPartial>), kind: Nat) -> B.Res(List<&2, TaiPartial>):
  match kind:
    case 0n:
      TaiList.plmn00(1n+U32.to_nat(U32.and(31, h)), P.Plmn.read(rest), more)
    case 1n:
      TaiList.plmn01(1n+U32.to_nat(U32.and(31, h)), P.Plmn.read(rest), more)
    case 2n:
      TaiList.tais(Tais.read(1n+U32.to_nat(U32.and(31, h)), rest), more)
    case 3n+p:
      Fail{B.Unsupported{h}}

def TaiList.go(fuel: Nat, bs: B.Bytes()) -> B.Res(List<&2, TaiPartial>):
  match fuel bs:
    case _ Nil{}:
      Done{[]}
    case 0n b <> rest:
      Fail{B.Invalid{b}}
    case 1n+f +h <> rest:
      TaiList.kind(h, rest, left => TaiList.go(f, left), U32.to_nat(U32.and(3, U32.shrn(h, 5n))))

def TaiList.read(+bs: B.Bytes()) -> B.Res(List<&2, TaiPartial>):
  TaiList.go(List.length(&2, U32, bs), bs)

def Tacs.write(tacs: List<&2, U32>, rest: B.Bytes()) -> B.Bytes():
  match tacs:
    case Nil{}:
      rest
    case tac <> more:
      B.write_u24(tac, Tacs.write(more, rest))

def Tais.write(tais: List<&2, Tai>, rest: B.Bytes()) -> B.Bytes():
  match tais:
    case Nil{}:
      rest
    case Tai{plmn, tac} <> more:
      P.Plmn.write(plmn, B.write_u24(tac, Tais.write(more, rest)))

# The header byte: list type in bits 7-6, element count minus one below.
def TaiList.header(kind: U32, count: Nat) -> U32:
  U32.add(U32.shln(kind, 5n), U32.from_nat(Nat.sub(count, 1n)))

def TaiList.write(list: List<&2, TaiPartial>) -> B.Bytes():
  match list:
    case Nil{}:
      []
    case Tai00{plmn, +tacs} <> more:
      TaiList.header(0, List.length(&2, U32, tacs)) <> P.Plmn.write(plmn, Tacs.write(tacs, TaiList.write(more)))
    case Tai01{plmn, first, count} <> more:
      TaiList.header(1, count) <> P.Plmn.write(plmn, B.write_u24(first, TaiList.write(more)))
    case Tai10{+tais} <> more:
      TaiList.header(2, List.length(&2, Tai, tais)) <> Tais.write(tais, TaiList.write(more))

# 5GS network feature support (§9.11.3.5): one to three bytes of flags.
def NetFeature.read(bs: B.Bytes()) -> B.Res(B.Bytes()):
  Bytes.between(bs, 1n, 3n)

# GPRS timer 3 (TS 24.008 §10.5.7.4a): a unit in the high three bits, a value below.
type Timer3 is Data:
  Timer3{unit: U32, value: U32}

def Timer3.ok(r: B.Res(U32)) -> B.Res(Timer3):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+v}:
      Done{Timer3{U32.shrn(v, 5n), U32.and(31, v)}}

def Timer3.read(bs: B.Bytes()) -> B.Res(Timer3):
  Timer3.ok(Byte.one(bs, 0))

def Timer3.write(t: Timer3) -> B.Bytes():
  match t:
    case Timer3{unit, value}:
      [U32.add(U32.shln(U32.and(7, unit), 5n), U32.and(31, value))]

# PDU session identity 2 (§9.11.3.41): one byte.
def PduSessionId.read(bs: B.Bytes()) -> B.Res(U32):
  Byte.one(bs, 0)

# Request type (§9.11.3.47): the low nibble of a one-octet IE.
def RequestType.read(+nibble: U32) -> B.Res(U32):
  B.guard(U32, U32.and(7, nibble), U32.and(7, nibble), U32.is_eq(U32.and(8, nibble), 0))

# DNN (§9.11.2.1A): length-prefixed labels
# ----------------------------------------

def Dnn.label(r: B.Read(B.Bytes()), more: B.Bytes() -> B.Res(List<&2, B.Bytes()>)) -> B.Res(List<&2, B.Bytes()>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(label, rest)}:
      B.Res.cons(B.Bytes(), label, more(rest))

def Dnn.go(fuel: Nat, bs: B.Bytes()) -> B.Res(List<&2, B.Bytes()>):
  match fuel bs:
    case _ Nil{}:
      Done{[]}
    case 0n b <> rest:
      Fail{B.Invalid{b}}
    case 1n+f +len <> rest:
      Dnn.label(B.take(U32.to_nat(len), rest), left => Dnn.go(f, left))

def Dnn.read(+bs: B.Bytes()) -> B.Res(List<&2, B.Bytes()>):
  Dnn.go(List.length(&2, U32, bs), bs)

def Dnn.write(labels: List<&2, B.Bytes()>) -> B.Bytes():
  match labels:
    case Nil{}:
      []
    case +label <> more:
      U32.from_nat(List.length(&2, U32, label)) <> List.append(&2, U32, label, Dnn.write(more))

# Network name (TS 24.008 §10.5.3.5a)
# ----------------------------------

# Coding scheme, "add country initials", the count of spare bits in the last
# byte, then the packed text.
type NetName is Data:
  NetName{scheme: U32, add_ci: Bool, spare_bits: U32, text: B.Bytes()}

def NetName.ext(+h: U32, text: B.Bytes(), ok: Bool) -> B.Res(NetName):
  match ok:
    case True{}:
      Done{NetName{U32.and(7, U32.shrn(h, 4n)), Bit.of(h, 8), U32.and(7, h), text}}
    case False{}:
      Fail{B.Invalid{h}}

def NetName.read(bs: B.Bytes()) -> B.Res(NetName):
  match bs:
    case Nil{}:
      Fail{B.Short{}}
    case +h <> text:
      NetName.ext(h, text, Bit.of(h, 128))

def NetName.write(n: NetName) -> B.Bytes():
  match n:
    case NetName{scheme, add_ci, spare, text}:
      U32.add(128, U32.add(U32.shln(U32.and(7, scheme), 4n), U32.add(Bit.to(add_ci, 8), U32.and(7, spare)))) <> text

# Time zone (TS 24.008 §10.5.3.8), time zone and time (§10.5.3.9), daylight saving time (§10.5.3.12)
def TimeZone.read(bs: B.Bytes()) -> B.Res(U32):
  Byte.one(bs, 0)

def TimeZoneTime.read(bs: B.Bytes()) -> B.Res(B.Bytes()):
  Bytes.exactly(bs, 7n)

def Dst.read(bs: B.Bytes()) -> B.Res(U32):
  Byte.one(bs, 252)
