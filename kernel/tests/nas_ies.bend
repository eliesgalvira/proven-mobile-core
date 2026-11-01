import Base
import ../bytes.bend as B
import ../plmn.bend as P
import ../suci.bend as S
import ../nas/ie.bend as I
import ../nas/mm.bend as M
import ../nas/mobile_id.bend as Mi
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

def main() -> IO(Unit):
  do IO<Unit>:
    mobile_identity()
