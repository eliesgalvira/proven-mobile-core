import Base
import ../bytes.bend as B
import ../pfcp.bend as Pf
import ../tlv.bend as T
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture

# Every PFCP message of the capture decodes, is valid, re-encodes to the same
# octets and carries the type, sequence number and IE count the capture says;
# the typed views decode the IEs of the association and the session; short,
# truncated and malformed inputs fail.

def ies_count(ies: List<&2, T.Tlv>) -> Nat:
  List.length(&2, T.Tlv, ies)

def check_msg(+name: String, +bs: B.Bytes(), +kind: Nat, +seq: Nat, +count: Nat, r: B.Read(Pf.Msg)) -> IO(Unit):
  match r:
    case Fail{e}:
      C.Check.report(name ++ ": decodes", False{})
    case Done{(+m, rest)}:
      do IO<Unit>:
        C.Check.report(name ++ ": decodes to the end", B.bytes_eq(rest, []))
        C.Check.report(name ++ ": is valid", Pf.Msg.valid(m))
        C.Check.report(name ++ ": re-encodes to the captured octets", B.bytes_eq(Pf.Msg.write(m, []), bs))
        C.Check.report(name ++ ": type, sequence number and IE count match the capture", Bool.and(Nat.is_eq(U32.to_nat(Pf.Msg.kind(m)), kind), Bool.and(Nat.is_eq(U32.to_nat(Pf.Msg.seq(m)), seq), Nat.is_eq(ies_count(Pf.Msg.ies(m)), count))))

def one(+m: V.Vec, protocol: String) -> IO(Unit):
  match protocol:
    case "PFCP":
      +bs : B.Bytes() = V.Vec.bytes(V.Vec.field(m, "hex"))
      check_msg(V.Vec.text(V.Vec.field(m, "message")), bs, V.Vec.nat(V.Vec.field(m, "message_type")), V.Vec.nat(V.Vec.field(m, "sequence")), List.length(&2, V.Vec, V.Vec.items(V.Vec.field(m, "ies"))), Pf.Msg.read(bs))
    case _:
      IO.pure(Unit, Unit{})

def run(msgs: List<&2, V.Vec>) -> IO(Unit):
  match msgs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +m <> rest:
      do IO<Unit>:
        one(m, V.Vec.text(V.Vec.field(m, "protocol")))
        run(rest)

def first_pick(+m: V.Vec, kind: Nat, protocol: String, mt: Nat, rest: Maybe<&2, B.Bytes()>) -> Maybe<&2, B.Bytes()>:
  match protocol:
    case "PFCP":
      V.Vec.hex_if(m, Nat.is_eq(mt, kind), rest)
    case _:
      rest

# The first PFCP message of a type (the later ones are kept behind it).
def first_of(+kind: Nat, msgs: List<&2, V.Vec>) -> Maybe<&2, B.Bytes()>:
  match msgs:
    case Nil{}:
      None{}
    case +m <> rest:
      first_pick(m, kind, V.Vec.text(V.Vec.field(m, "protocol")), V.Vec.nat(V.Vec.field(m, "message_type")), first_of(kind, rest))

def ies_read(r: B.Read(Pf.Msg)) -> List<&2, T.Tlv>:
  match r:
    case Fail{e}:
      []
    case Done{(m, rest)}:
      Pf.Msg.ies(m)

def ies_of(bs: Maybe<&2, B.Bytes()>) -> List<&2, T.Tlv>:
  match bs:
    case None{}:
      []
    case Some{b}:
      ies_read(Pf.Msg.read(b))

def body_or(found: Maybe<&2, T.Tlv>) -> B.Bytes():
  match found:
    case None{}:
      []
    case Some{ie}:
      T.Tlv.body(ie)

def body_of(+kind: U32, ies: List<&2, T.Tlv>) -> B.Bytes():
  body_or(T.Tlvs.find(kind, ies))

def group_read(r: Result<&2, &2, B.Err, List<&2, T.Tlv>>) -> List<&2, T.Tlv>:
  match r:
    case Fail{e}:
      []
    case Done{ies}:
      ies

def grouped(+kind: U32, ies: List<&2, T.Tlv>) -> List<&2, T.Tlv>:
  group_read(T.Tlvs.decode(body_of(kind, ies)))

def keep_ie(ie: T.Tlv, rest: List<&2, T.Tlv>, hit: Bool) -> List<&2, T.Tlv>:
  match hit:
    case True{}:
      ie <> rest
    case False{}:
      rest

def same_kind(+kind: U32, ies: List<&2, T.Tlv>) -> List<&2, T.Tlv>:
  match ies:
    case Nil{}:
      []
    case +ie <> more:
      keep_ie(ie, same_kind(kind, more), U32.is_eq(T.Tlv.kind(ie), kind))

def nth_body(ies: List<&2, T.Tlv>) -> B.Bytes():
  match ies:
    case Nil{}:
      []
    case ie <> more:
      T.Tlv.body(ie)

# The IEs inside the n-th IE of a kind (zero-based).
def nth_of(+kind: U32, n: Nat, ies: List<&2, T.Tlv>) -> List<&2, T.Tlv>:
  group_read(T.Tlvs.decode(nth_body(List.drop(&2, T.Tlv, same_kind(kind, ies), n))))

def bytes_or(mb: Maybe<&2, B.Bytes()>) -> B.Bytes():
  match mb:
    case None{}:
      []
    case Some{b}:
      b

def node_v4(r: Result<&2, &2, B.Err, Pf.NodeId>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{n}:
      match n:
        case Pf.NodeV4{addr}:
          B.bytes_eq(addr, [10, 33, 0, 12])
        case Pf.NodeV6{addr}:
          False{}
        case Pf.NodeFqdn{name}:
          False{}

def word_is(r: Result<&2, &2, B.Err, U32>, v: U32) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      U32.is_eq(x, v)

def fseid_v4(r: Result<&2, &2, B.Err, Pf.Fseid>, seid: B.Bytes()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{f}:
      match f:
        case Pf.Fseid{s, v4, v6}:
          Bool.and(B.bytes_eq(s, seid), Bool.and(Pf.Addr.present(v4), Bool.not(Pf.Addr.present(v6))))

def fseid_rewrites(r: Result<&2, &2, B.Err, Pf.Fseid>, body: B.Bytes()) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{f}:
      B.bytes_eq(Pf.Fseid.write(f), body)

def fteid_fixed(r: Result<&2, &2, B.Err, Pf.Fteid>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{f}:
      match f:
        case Pf.Teid{teid, v4, v6}:
          Bool.and(Pf.Addr.present(v4), Bool.not(Pf.Addr.present(v6)))
        case Pf.Choose{v4, v6, chid}:
          False{}

def fteid_choose(r: Result<&2, &2, B.Err, Pf.Fteid>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{f}:
      match f:
        case Pf.Teid{teid, v4, v6}:
          False{}
        case Pf.Choose{v4, v6, chid}:
          Bool.and(v4, Bool.not(v6))

def no_port(port: Maybe<&2, U32>) -> Bool:
  match port:
    case None{}:
      True{}
    case Some{p}:
      False{}

def ohc_gtp_v4(r: Result<&2, &2, B.Err, Pf.Ohc>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{o}:
      match o:
        case Pf.Ohc{desc, teid, v4, v6, port}:
          Bool.and(U32.is_eq(desc, 256), Bool.and(Pf.Addr.present(v4), no_port(port)))

def mbr_ok(r: Result<&2, &2, B.Err, Pf.Mbr>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{m}:
      Pf.Mbr.valid(m)

def ueip_v4(r: Result<&2, &2, B.Err, Pf.UeIp>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{u}:
      match u:
        case Pf.UeIp{source, v4, v6}:
          Bool.and(Pf.Addr.present(v4), Bool.not(Pf.Addr.present(v6)))

def fails(-A: Data, r: Result<&2, &2, B.Err, A>) -> Bool:
  Result.is_fail(&2, &2, B.Err, A, r)

def read_fails(-A: Data, r: B.Read(A)) -> Bool:
  Result.is_fail(&2, &2, B.Err, B.ReadValue(A), r)

def drop_last(+bs: B.Bytes()) -> B.Bytes():
  List.take(&2, U32, bs, Nat.sub(List.length(&2, U32, bs), 1n))

def main() -> IO(Unit):
  do IO<Unit>:
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    run(msgs)
    +assoc : List<&2, T.Tlv> = ies_of(first_of(5n, msgs))
    +resp : List<&2, T.Tlv> = ies_of(first_of(51n, msgs))
    +sess : List<&2, T.Tlv> = ies_of(first_of(50n, msgs))
    +pdr : List<&2, T.Tlv> = grouped(1, sess)
    +pdi : List<&2, T.Tlv> = grouped(2, pdr)
    C.Check.report("Association Setup Request: Node ID is the SMF's IPv4 address", node_v4(Pf.NodeId.read(body_of(60, assoc))))
    C.Check.report("Association Setup Request: Recovery Time Stamp decodes", word_is(Pf.Word.read(body_of(96, assoc)), 4002546532))
    C.Check.report("Session Establishment Response: Cause is accepted", word_is(Pf.Byte.read(body_of(19, resp)), 1))
    C.Check.report("Session Establishment Response: F-SEID carries the UP SEID and an IPv4 address", fseid_v4(Pf.Fseid.read(body_of(57, resp)), [0, 0, 0, 0, 0, 0, 0, 2]))
    C.Check.report("Session Establishment Request: the first Create PDR has six IEs", Nat.is_eq(ies_count(pdr), 6n))
    C.Check.report("Session Establishment Request: PDR ID decodes", word_is(Pf.Short.read(body_of(56, pdr)), 1))
    C.Check.report("Session Establishment Request: the PDI's UE IP Address is IPv4", ueip_v4(Pf.UeIp.read(body_of(93, pdi))))
    C.Check.report("Session Establishment Request: Source Interface is Core", word_is(Pf.Byte.read(body_of(20, pdi)), 1))
    C.Check.report("Session Establishment Request: the uplink PDI's F-TEID has a TEID and an IPv4 address", fteid_fixed(Pf.Fteid.read(body_of(21, grouped(2, nth_of(1, 1n, sess))))))
    C.Check.report("Session Establishment Request: the downlink FAR's Outer Header Creation is GTP-U/UDP/IPv4", ohc_gtp_v4(Pf.Ohc.read(body_of(84, grouped(4, nth_of(3, 2n, sess))))))
    C.Check.report("Session Establishment Request: the QER's MBR decodes", mbr_ok(Pf.Mbr.read(body_of(26, grouped(7, sess)))))
    C.Check.report("an IE header of three octets is Short", Bool.and(read_fails(T.Tlv, T.Tlv.read([0, 1, 0])), read_fails(T.Tlv, T.Tlv.read([0, 1, 0, 5, 1, 2]))))
    C.Check.report("a truncated message fails", read_fails(Pf.Msg, Pf.Msg.read(drop_last(bytes_or(first_of(5n, msgs))))))
    C.Check.report("version 0 is unsupported", read_fails(Pf.Msg, Pf.Msg.read([0, 1, 0, 12, 0, 0, 2, 0, 0, 96, 0, 4, 238, 146, 3, 94])))
    C.Check.report("an F-TEID with CH and an IPv4 request decodes without a TEID", fteid_choose(Pf.Fteid.read([5])))
    C.Check.report("an F-TEID with CH carrying a TEID is rejected", fails(Pf.Fteid, Pf.Fteid.read([5, 0, 0, 0, 1])))
    C.Check.report("an F-TEID whose flags promise an address it lacks is rejected", fails(Pf.Fteid, Pf.Fteid.read([1, 0, 0, 0, 1])))
    C.Check.report("an F-TEID with a TEID and an IPv4 address decodes", fteid_fixed(Pf.Fteid.read([1, 0, 0, 0, 1, 10, 33, 0, 12])))
    C.Check.report("an F-TEID with a spare flag bit is rejected", fails(Pf.Fteid, Pf.Fteid.read([17, 0, 0, 0, 1, 10, 33, 0, 12])))
    C.Check.report("Session Establishment Response: the F-SEID re-encodes to its body", fseid_rewrites(Pf.Fseid.read(body_of(57, resp)), body_of(57, resp)))
    C.Check.report("an F-SEID with a spare flag bit is rejected", fails(Pf.Fseid, Pf.Fseid.read([6, 0, 0, 0, 0, 0, 0, 0, 2, 10, 33, 0, 12])))
