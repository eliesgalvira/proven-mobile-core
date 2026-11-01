import Base
import ../bytes.bend as B
import ../plmn.bend as P
import ../suci.bend as S
import ../nas/ie.bend as I
import ../nas/mm.bend as M
import ../nas/mobile_id.bend as Mi
import ../nas/ies.bend as E
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture

# Typed views of the IEs carried by the captured 5GMM messages: each decodes
# to the expected value and re-encodes to the bytes it came from.

def message_pick(more: Unit -> V.Vec, found: V.Vec, hit: Bool) -> V.Vec:
  match hit:
    case True{}:
      found
    case False{}:
      more(Unit{})

def message(msgs: List<&2, V.Vec>, +index: Nat) -> V.Vec:
  match msgs:
    case Nil{}:
      V.VNull{}
    case +m <> rest:
      message_pick(u => message(rest, index), m, Nat.is_eq(V.Vec.nat(V.Vec.field(m, "index")), index))

def plain(+index: Nat) -> List<&2, U32>:
  V.Vec.bytes(V.Vec.field(message(V.Vec.items(V.Vec.field(Capture.data(), "messages")), index), "plaintext_hex"))

def decoded(r: Result<&2, &2, B.Err, M.Mm>) -> M.Mm:
  match r:
    case Fail{e}:
      M.Mm{M.Status{}, [], []}
    case Done{m}:
      m

def msg(+index: Nat) -> M.Mm:
  decoded(M.Mm.read(plain(index)))

def field_bytes(f: I.Field) -> List<&2, U32>:
  match f:
    case I.FByte{v}:
      [v]
    case I.FLv{I.LenBody{len, body}}:
      body
    case I.FLvE{I.LenBody{len, body}}:
      body

def field_of(mf: Maybe<&2, I.Field>) -> List<&2, U32>:
  match mf:
    case None{}:
      []
    case Some{f}:
      field_bytes(f)

# The content of mandatory field `n`.
def field(m: M.Mm, n: Nat) -> List<&2, U32>:
  field_of(List.get(&2, I.Field, M.Mm.fields(m), n))

def opt_pick(more: Unit -> List<&2, U32>, ie: I.Ie, hit: Bool) -> List<&2, U32>:
  match hit:
    case True{}:
      I.Ie.body(ie)
    case False{}:
      more(Unit{})

def opt_in(ies: List<&2, I.Ie>, +iei: U32) -> List<&2, U32>:
  match ies:
    case Nil{}:
      []
    case +ie <> rest:
      opt_pick(u => opt_in(rest, iei), ie, U32.is_eq(I.Ie.iei(ie), iei))

# The content of the optional IE with this IEI.
def opt(m: M.Mm, iei: U32) -> List<&2, U32>:
  opt_in(M.Mm.opts(m), iei)

def digits_eq(+xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  B.bytes_eq(xs, ys)

def plmn_is(+p: P.Plmn, mcc: List<&2, U32>, mnc: List<&2, U32>) -> Bool:
  Bool.and(digits_eq(P.Plmn.mcc(p), mcc), digits_eq(P.Plmn.mnc(p), mnc))

# Mobile identity
# ---------------

def is_suci(r: Mi.MobileId.Res()) -> Bool:
  match r:
    case Done{Mi.Suci{S.Suci{plmn, routing, scheme, key_id, output}}}:
      Bool.and(plmn_is(plmn, [0, 0, 1], [0, 1]), Bool.and(digits_eq(routing, [0, 0, 0, 0]), Bool.and(U32.is_eq(scheme, 1), Bool.and(U32.is_eq(key_id, 1), Nat.is_eq(List.length(&2, U32, output), 45n)))))
    case _:
      False{}

def is_imeisv(r: Mi.MobileId.Res(), expected: List<&2, U32>) -> Bool:
  match r:
    case Done{Mi.Imeisv{ds}}:
      digits_eq(ds, expected)
    case _:
      False{}

def is_imei(r: Mi.MobileId.Res(), expected: List<&2, U32>) -> Bool:
  match r:
    case Done{Mi.Imei{ds}}:
      digits_eq(ds, expected)
    case _:
      False{}

def is_guti(r: Mi.MobileId.Res()) -> Bool:
  match r:
    case Done{Mi.Guti{plmn, region, +amf, tmsi}}:
      Bool.and(plmn_is(plmn, [0, 0, 1], [0, 1]), Bool.and(U32.is_eq(region, 2), Bool.and(U32.is_eq(Mi.MobileId.amf_set(amf), 1), Bool.and(U32.is_eq(Mi.MobileId.amf_pointer(amf), 0), U32.is_eq(tmsi, 3221226703)))))
    case _:
      False{}

def is_s_tmsi(r: Mi.MobileId.Res()) -> Bool:
  match r:
    case Done{Mi.STmsi{amf, tmsi}}:
      Bool.and(U32.is_eq(amf, 64), U32.is_eq(tmsi, 3221226703))
    case _:
      False{}

def is_no_id(r: Mi.MobileId.Res()) -> Bool:
  match r:
    case Done{Mi.NoId{}}:
      True{}
    case _:
      False{}

def written(r: Mi.MobileId.Res()) -> List<&2, U32>:
  match r:
    case Fail{e}:
      []
    case Done{id}:
      Mi.MobileId.write(id)

def valid(r: Mi.MobileId.Res()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{id}:
      Mi.MobileId.valid(id)

def fails(r: Mi.MobileId.Res()) -> Bool:
  Result.is_fail(&2, &2, B.Err, Mi.MobileId, r)

def identity(+name: String, +bs: List<&2, U32>, shape: Mi.MobileId.Res() -> Bool) -> IO(Unit):
  do IO<Unit>:
    C.Check.report(name ++ " decodes", shape(Mi.MobileId.read(bs)))
    C.Check.report(name ++ " is valid", valid(Mi.MobileId.read(bs)))
    C.Check.report(name ++ " re-encodes to its bytes", C.Check.bytes_eq(written(Mi.MobileId.read(bs)), bs))

def mobile_identity() -> IO(Unit):
  do IO<Unit>:
    identity("the SUCI of the Registration request", field(msg(15n), 1n), r => is_suci(r))
    identity("the IMEISV of the Security mode complete", opt(msg(23n), 119), r => is_imeisv(r, [4, 3, 7, 0, 8, 1, 6, 1, 2, 5, 8, 1, 6, 1, 5, 1]))
    identity("the 5G-GUTI of the Registration accept", opt(msg(26n), 119), r => is_guti(r))
    identity("a 5G-S-TMSI", [244, 0, 64, 192, 0, 4, 207], r => is_s_tmsi(r))
    identity("no identity", [0], r => is_no_id(r))
    identity("an IMEI", [75, 9, 81, 36, 48, 50, 87, 129], r => is_imei(r, [4, 9, 0, 1, 5, 4, 2, 0, 3, 2, 3, 7, 5, 1, 8]))
    C.Check.report("an IMEISV flagged odd is rejected", fails(Mi.MobileId.read([77, 115, 128, 97, 33, 133, 97, 81, 241])))
    C.Check.report("an IMEISV with 17 digits is rejected", fails(Mi.MobileId.read([69, 115, 128, 97, 33, 133, 97, 81, 241, 241])))
    C.Check.report("a 5G-GUTI short of its TMSI is rejected", fails(Mi.MobileId.read([242, 0, 241, 16, 2, 0, 64, 192, 0])))
    C.Check.report("a 5G-GUTI with a trailing byte is rejected", fails(Mi.MobileId.read([242, 0, 241, 16, 2, 0, 64, 192, 0, 4, 207, 0])))
    C.Check.report("an empty identity is Short", fails(Mi.MobileId.read([])))
    C.Check.report("a MAC address identity is Unsupported", fails(Mi.MobileId.read([6, 1, 2, 3, 4, 5, 6])))

# A one-octet IE (T1) with this whole byte is present.
def has_t1(ies: List<&2, I.Ie>, +byte: U32) -> Bool:
  match ies:
    case Nil{}:
      False{}
    case +ie <> rest:
      Bool.or(U32.is_eq(I.Ie.iei(ie), byte), has_t1(rest, byte))

def first_byte(bs: List<&2, U32>) -> U32:
  match bs:
    case Nil{}:
      0
    case b <> rest:
      b

# Expected shapes
# ---------------

def half_is(h: E.Half, flag: Bool, value: U32) -> Bool:
  match h:
    case E.Half{+f, +v}:
      Bool.and(Bool.not(Bool.xor(f, flag)), U32.is_eq(v, value))

def ksi_is(r: E.Res(E.Half), flag: Bool, value: U32) -> Bool:
  match r:
    case Done{+h}:
      half_is(h, flag, value)
    case Fail{e}:
      False{}

def algs_is(a: E.SecAlgs, c: U32, i: U32) -> Bool:
  match a:
    case E.SecAlgs{+ciphering, +integrity}:
      Bool.and(U32.is_eq(ciphering, c), U32.is_eq(integrity, i))

def seccap_is(r: E.Res(E.SecCap), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.SecCap{+ea, +ia, +eutra}}:
      Bool.and(Bool.and(U32.is_eq(ea, 240), U32.is_eq(ia, 240)), Bool.and(digits_eq(eutra, [240, 240]), C.Check.bytes_eq(E.SecCap.write(E.SecCap{ea, ia, eutra}), bs)))
    case Fail{e}:
      False{}

def mmcap_is(r: E.Res(E.MmCap), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.MmCap{+flags, +more}}:
      Bool.and(Bool.and(U32.is_eq(flags, 0), List.is_empty(&2, U32, more)), C.Check.bytes_eq(E.MmCap.write(E.MmCap{flags, more}), bs))
    case Fail{e}:
      False{}

def snssai_sst1(s: E.SNssai) -> Bool:
  match s:
    case E.Sst{sst}:
      U32.is_eq(sst, 1)
    case _:
      False{}

def nssai_is_sst1(r: E.Res(List<&2, E.SNssai>), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{+s <> Nil{}}:
      Bool.and(snssai_sst1(s), C.Check.bytes_eq(E.Nssai.write([s]), bs))
    case _:
      False{}

def snssai_is_sst1(r: E.Res(E.SNssai), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{+s}:
      Bool.and(snssai_sst1(s), C.Check.bytes_eq(E.SNssai.write(s), bs))
    case Fail{e}:
      False{}

def snssai_full(r: E.Res(E.SNssai), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.SstFull{+sst, +sd, +msst, +msd}}:
      Bool.and(Bool.and(U32.is_eq(sst, 1), U32.is_eq(sd, 65794)), Bool.and(Bool.and(U32.is_eq(msst, 2), U32.is_eq(msd, 263172)), C.Check.bytes_eq(E.SNssai.write(E.SstFull{sst, sd, msst, msd}), bs)))
    case _:
      False{}

def update_zero(r: E.Res(E.UpdateType), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.UpdateType{+sms, +rcu, +pnb, +eps}}:
      Bool.and(Bool.and(Bool.not(sms), Bool.not(rcu)), Bool.and(Bool.and(U32.is_eq(pnb, 0), U32.is_eq(eps, 0)), C.Check.bytes_eq(E.UpdateType.write(E.UpdateType{sms, rcu, pnb, eps}), bs)))
    case Fail{e}:
      False{}

def bytes_len(r: E.Res(List<&2, U32>), n: Nat) -> Bool:
  match r:
    case Done{+bs}:
      Nat.is_eq(List.length(&2, U32, bs), n)
    case Fail{e}:
      False{}

def u32_is(r: E.Res(U32), v: U32) -> Bool:
  match r:
    case Done{+x}:
      U32.is_eq(x, v)
    case Fail{e}:
      False{}

def addsec_is(r: E.Res(E.AddSecInfo), hdp: Bool, rinmr: Bool, +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.AddSecInfo{+h, +m}}:
      Bool.and(Bool.and(Bool.not(Bool.xor(h, hdp)), Bool.not(Bool.xor(m, rinmr))), C.Check.bytes_eq(E.AddSecInfo.write(E.AddSecInfo{h, m}), bs))
    case Fail{e}:
      False{}

def container_is(r: E.Res(M.Mm), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{+m}:
      Bool.and(U32.is_eq(M.Mm.Type.code(M.Mm.mt(m)), 65), C.Check.bytes_eq(M.Mm.write(m), bs))
    case Fail{e}:
      False{}

def result_is(r: E.Res(E.RegResult), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.RegResult{+value, +sms, +nssaa, +emergency}}:
      Bool.and(Bool.and(U32.is_eq(value, 1), Bool.not(sms)), Bool.and(Bool.and(Bool.not(nssaa), Bool.not(emergency)), C.Check.bytes_eq(E.RegResult.write(E.RegResult{value, sms, nssaa, emergency}), bs)))
    case Fail{e}:
      False{}

def tai_single(tais: List<&2, E.Tai>, +bs: List<&2, U32>) -> Bool:
  match tais:
    case E.Tai{+plmn, +tac} <> Nil{}:
      Bool.and(Bool.and(plmn_is(plmn, [0, 0, 1], [0, 1]), U32.is_eq(tac, 1)), C.Check.bytes_eq(E.TaiList.write([E.Tai10{[E.Tai{plmn, tac}]}]), bs))
    case _:
      False{}

def tai_one(item: E.TaiPartial, +bs: List<&2, U32>) -> Bool:
  match item:
    case E.Tai10{tais}:
      tai_single(tais, bs)
    case _:
      False{}

def tai01_is(r: E.Res(List<&2, E.TaiPartial>), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.Tai01{+plmn, +first, +count} <> Nil{}}:
      Bool.and(Bool.and(U32.is_eq(first, 1), Nat.is_eq(count, 3n)), C.Check.bytes_eq(E.TaiList.write([E.Tai01{plmn, first, count}]), bs))
    case _:
      False{}

def tai_is(r: E.Res(List<&2, E.TaiPartial>), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{item <> Nil{}}:
      tai_one(item, bs)
    case _:
      False{}

def tai00_is(r: E.Res(List<&2, E.TaiPartial>), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.Tai00{+plmn, +tacs} <> Nil{}}:
      Bool.and(digits_eq(tacs, [1, 2]), C.Check.bytes_eq(E.TaiList.write([E.Tai00{plmn, tacs}]), bs))
    case _:
      False{}

def tai10_is(r: E.Res(List<&2, E.TaiPartial>), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.Tai10{+tais} <> Nil{}}:
      Bool.and(Nat.is_eq(List.length(&2, E.Tai, tais), 2n), C.Check.bytes_eq(E.TaiList.write([E.Tai10{tais}]), bs))
    case _:
      False{}

def timer_is(r: E.Res(E.Timer3), unit: U32, value: U32, +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.Timer3{+u, +v}}:
      Bool.and(Bool.and(U32.is_eq(u, unit), U32.is_eq(v, value)), C.Check.bytes_eq(E.Timer3.write(E.Timer3{u, v}), bs))
    case Fail{e}:
      False{}

def dnn_is(r: E.Res(List<&2, List<&2, U32>>), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{+label <> Nil{}}:
      Bool.and(C.Check.bytes_eq(label, [105, 110, 116, 101, 114, 110, 101, 116]), C.Check.bytes_eq(E.Dnn.write([label]), bs))
    case _:
      False{}

def name_is(r: E.Res(E.NetName), chars: Nat, +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{E.NetName{+scheme, +ci, +spare, +text}}:
      Bool.and(Bool.and(U32.is_eq(scheme, 1), Bool.not(ci)), Bool.and(Bool.and(U32.is_eq(spare, 0), Nat.is_eq(List.length(&2, U32, text), chars)), C.Check.bytes_eq(E.NetName.write(E.NetName{scheme, ci, spare, text}), bs)))
    case Fail{e}:
      False{}

def fails_res(-A: Data, r: E.Res(A)) -> Bool:
  Result.is_fail(&2, &2, B.Err, A, r)

def typed_ies() -> IO(Unit):
  do IO<Unit>:
    +reg1 : M.Mm = msg(15n)
    C.Check.report("Registration request: ngKSI is no key (7), native", half_is(E.RegHeader.ksi(first_byte(field(reg1, 0n))), False{}, 7))
    C.Check.report("Registration request: initial registration with follow-on request", half_is(E.RegHeader.reg(first_byte(field(reg1, 0n))), True{}, 1))
    C.Check.report("Registration request: the first byte re-encodes", U32.is_eq(E.RegHeader.write(E.RegHeader.ksi(first_byte(field(reg1, 0n))), E.RegHeader.reg(first_byte(field(reg1, 0n)))), first_byte(field(reg1, 0n))))
    C.Check.report("Registration request: UE security capability", seccap_is(E.SecCap.read(opt(reg1, 46)), opt(reg1, 46)))
    +auth : M.Mm = msg(17n)
    C.Check.report("Authentication request: ngKSI 0", ksi_is(E.Ksi.read(first_byte(field(auth, 0n))), False{}, 0))
    C.Check.report("Authentication request: ABBA has two bytes", bytes_len(E.Abba.read(field(auth, 1n)), 2n))
    C.Check.report("Authentication request: RAND has sixteen bytes", bytes_len(E.Fixed16.read(opt(auth, 33)), 16n))
    C.Check.report("Authentication request: AUTN has sixteen bytes", bytes_len(E.Fixed16.read(opt(auth, 32)), 16n))
    C.Check.report("Authentication response: RES* has sixteen bytes", bytes_len(E.Fixed16.read(opt(msg(19n), 45)), 16n))
    +smc : M.Mm = msg(21n)
    C.Check.report("Security mode command: NEA0 and NIA2", algs_is(E.SecAlgs.of(first_byte(field(smc, 0n))), 0, 2))
    C.Check.report("Security mode command: the algorithms byte re-encodes", U32.is_eq(E.SecAlgs.write(E.SecAlgs.of(first_byte(field(smc, 0n)))), first_byte(field(smc, 0n))))
    C.Check.report("Security mode command: ngKSI 0", ksi_is(E.Ksi.read(first_byte(field(smc, 1n))), False{}, 0))
    C.Check.report("Security mode command: replayed UE security capability", seccap_is(E.SecCap.read(field(smc, 2n)), field(smc, 2n)))
    C.Check.report("Security mode command: IMEISV requested", Bool.and(has_t1(M.Mm.opts(smc), 225), u32_is(E.ImeisvRequest.read(1), 1)))
    C.Check.report("Security mode command: additional security information asks for the retransmitted request", addsec_is(E.AddSecInfo.read(opt(smc, 54)), False{}, True{}, opt(smc, 54)))
    +complete : M.Mm = msg(23n)
    C.Check.report("Security mode complete: the NAS message container holds the Registration request", container_is(E.Container.read(opt(complete, 113)), opt(complete, 113)))
    +reg2 : M.Mm = msg(24n)
    C.Check.report("Registration request: 5GMM capability", mmcap_is(E.MmCap.read(opt(reg2, 16)), opt(reg2, 16)))
    C.Check.report("Registration request: requested NSSAI is SST 1", nssai_is_sst1(E.Nssai.read(opt(reg2, 47)), opt(reg2, 47)))
    C.Check.report("Registration request: 5GS update type", update_zero(E.UpdateType.read(opt(reg2, 83)), opt(reg2, 83)))
    +accept : M.Mm = msg(26n)
    C.Check.report("Registration accept: registered over 3GPP access", result_is(E.RegResult.read(field(accept, 0n)), field(accept, 0n)))
    C.Check.report("Registration accept: TAI list is the single TAI 001/01, TAC 1", tai_is(E.TaiList.read(opt(accept, 84)), opt(accept, 84)))
    C.Check.report("Registration accept: allowed NSSAI is SST 1", nssai_is_sst1(E.Nssai.read(opt(accept, 21)), opt(accept, 21)))
    C.Check.report("Registration accept: network feature support has two bytes", bytes_len(E.NetFeature.read(opt(accept, 33)), 2n))
    C.Check.report("Registration accept: T3512 is 18 units of 10 hours", timer_is(E.Timer3.read(opt(accept, 94)), 4, 18, opt(accept, 94)))
    +ul : M.Mm = msg(31n)
    C.Check.report("UL NAS transport: payload container type N1 SM", u32_is(E.ContainerType.read(first_byte(field(ul, 0n))), 1))
    C.Check.report("UL NAS transport: payload container is the 5GSM message", Bool.and(Nat.is_eq(List.length(&2, U32, field(ul, 1n)), 21n), U32.is_eq(first_byte(field(ul, 1n)), 46)))
    C.Check.report("UL NAS transport: PDU session 1", u32_is(E.PduSessionId.read(opt(ul, 18)), 1))
    C.Check.report("UL NAS transport: initial request", Bool.and(has_t1(M.Mm.opts(ul), 129), u32_is(E.RequestType.read(1), 1)))
    C.Check.report("UL NAS transport: S-NSSAI SST 1", snssai_is_sst1(E.SNssai.read(opt(ul, 34)), opt(ul, 34)))
    C.Check.report("UL NAS transport: DNN internet", dnn_is(E.Dnn.read(opt(ul, 37)), opt(ul, 37)))
    +config : M.Mm = msg(34n)
    C.Check.report("Configuration update: full network name in UCS2", name_is(E.NetName.read(opt(config, 67)), 20n, opt(config, 67)))
    C.Check.report("Configuration update: short network name in UCS2", name_is(E.NetName.read(opt(config, 69)), 10n, opt(config, 69)))
    C.Check.report("Configuration update: local time zone", u32_is(E.TimeZone.read(opt(config, 70)), 0))
    C.Check.report("Configuration update: universal time and time zone", bytes_len(E.TimeZoneTime.read(opt(config, 71)), 7n))
    C.Check.report("Configuration update: no daylight saving", u32_is(E.Dst.read(opt(config, 73)), 0))
    +dl : M.Mm = msg(38n)
    C.Check.report("DL NAS transport: payload container type N1 SM", u32_is(E.ContainerType.read(first_byte(field(dl, 0n))), 1))
    C.Check.report("DL NAS transport: payload container is the 5GSM message", Bool.and(Nat.is_eq(List.length(&2, U32, field(dl, 1n)), 64n), U32.is_eq(first_byte(field(dl, 1n)), 46)))
    C.Check.report("DL NAS transport: PDU session 1", u32_is(E.PduSessionId.read(opt(dl, 18)), 1))
    C.Check.report("an S-NSSAI with SD and mapped values", snssai_full(E.SNssai.read([1, 1, 1, 2, 2, 4, 4, 4]), [1, 1, 1, 2, 2, 4, 4, 4]))
    C.Check.report("a three-byte S-NSSAI is rejected", fails_res(E.SNssai, E.SNssai.read([1, 2, 3])))
    C.Check.report("a two-byte registration result is rejected", fails_res(E.RegResult, E.RegResult.read([1, 0])))
    C.Check.report("a TAI list of type 00 with two TACs", tai00_is(E.TaiList.read([1, 0, 241, 16, 0, 0, 1, 0, 0, 2]), [1, 0, 241, 16, 0, 0, 1, 0, 0, 2]))
    C.Check.report("a TAI list of type 01 with three consecutive TACs", tai01_is(E.TaiList.read([34, 0, 241, 16, 0, 0, 1]), [34, 0, 241, 16, 0, 0, 1]))
    C.Check.report("a TAI list of type 10 with two TAIs", tai10_is(E.TaiList.read([65, 0, 241, 16, 0, 0, 1, 0, 241, 16, 0, 0, 2]), [65, 0, 241, 16, 0, 0, 1, 0, 241, 16, 0, 0, 2]))
    C.Check.report("a TAI list of a reserved type is Unsupported", fails_res(List<&2, E.TaiPartial>, E.TaiList.read([96, 0, 241, 16, 0, 0, 1])))
    C.Check.report("a TAI list short of a TAC is Short", fails_res(List<&2, E.TaiPartial>, E.TaiList.read([1, 0, 241, 16, 0, 0, 1, 0, 0])))
    C.Check.report("a fifteen-byte RAND is rejected", fails_res(List<&2, U32>, E.Fixed16.read(List.take(&2, U32, opt(auth, 33), 15n))))
    C.Check.report("a DNN label longer than its content is Short", fails_res(List<&2, List<&2, U32>>, E.Dnn.read([9, 105, 110, 116])))
    C.Check.report("a network name without its extension bit is rejected", fails_res(E.NetName, E.NetName.read([16, 0, 83])))
    C.Check.report("a payload container type with spare bits is rejected", fails_res(U32, E.ContainerType.read(17)))

def main() -> IO(Unit):
  do IO<Unit>:
    mobile_identity()
    typed_ies()
