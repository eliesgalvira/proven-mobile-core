import Base
import ./bytes.bend as B
import ./tlv.bend as T

# PFCP (TS 29.244), the subset the milestone's SMF speaks to the UPF: the message
# header over TLV information elements (`tlv.bend`), bytes in and bytes out. A
# grouped IE's body is a list of IEs; the typed views at the end decode the IEs
# the SMF sends and receives, each over the whole body of its IE. Anything else
# stays raw.

# Message types and IE types (TS 29.244 §7.2, §8.1.2)
# ----------------------------------------------------

def Type.heartbeat_request() -> U32:
  1

def Type.heartbeat_response() -> U32:
  2

def Type.association_setup_request() -> U32:
  5

def Type.association_setup_response() -> U32:
  6

def Type.session_establishment_request() -> U32:
  50

def Type.session_establishment_response() -> U32:
  51

def Type.session_modification_request() -> U32:
  52

def Type.session_modification_response() -> U32:
  53

def Type.session_deletion_request() -> U32:
  54

def Type.session_deletion_response() -> U32:
  55

def Ie.create_pdr() -> U32:
  1

def Ie.pdi() -> U32:
  2

def Ie.create_far() -> U32:
  3

def Ie.forwarding() -> U32:
  4

def Ie.create_qer() -> U32:
  7

def Ie.update_far() -> U32:
  10

def Ie.update_forwarding() -> U32:
  11

def Ie.cause() -> U32:
  19

def Ie.source_interface() -> U32:
  20

def Ie.fteid() -> U32:
  21

def Ie.gate_status() -> U32:
  25

def Ie.mbr() -> U32:
  26

def Ie.precedence() -> U32:
  29

def Ie.destination_interface() -> U32:
  42

def Ie.apply_action() -> U32:
  44

def Ie.pdr_id() -> U32:
  56

def Ie.fseid() -> U32:
  57

def Ie.node_id() -> U32:
  60

def Ie.outer_header_creation() -> U32:
  84

def Ie.ue_ip() -> U32:
  93

def Ie.outer_header_removal() -> U32:
  95

def Ie.recovery() -> U32:
  96

def Ie.far_id() -> U32:
  108

def Ie.qer_id() -> U32:
  109

def Ie.qfi() -> U32:
  124

# Messages
# --------

# Header (§7.2.2): version 1, the S flag, the message type, the length of what
# follows the length field, the SEID when S is set, a 24-bit sequence number
# and a spare octet (the message priority is not used).
type Msg is Data:
  Msg{kind: U32, len: U32, seid: Maybe<&2, B.Bytes()>, seq: U32, ies: List<&2, T.Tlv>}

def Msg.kind(m: Msg) -> U32:
  match m:
    case Msg{kind, len, seid, seq, ies}:
      kind

def Msg.len(m: Msg) -> U32:
  match m:
    case Msg{kind, len, seid, seq, ies}:
      len

def Msg.seid(m: Msg) -> Maybe<&2, B.Bytes()>:
  match m:
    case Msg{kind, len, seid, seq, ies}:
      seid

def Msg.seq(m: Msg) -> U32:
  match m:
    case Msg{kind, len, seid, seq, ies}:
      seq

def Msg.ies(m: Msg) -> List<&2, T.Tlv>:
  match m:
    case Msg{kind, len, seid, seq, ies}:
      ies

def Addr.write(a: Maybe<&2, B.Bytes()>, rest: B.Bytes()) -> B.Bytes():
  match a:
    case None{}:
      rest
    case Some{bs}:
      List.append(&2, U32, bs, rest)

def Seid.valid(seid: Maybe<&2, B.Bytes()>) -> Bool:
  match seid:
    case None{}:
      True{}
    case Some{bs}:
      Nat.is_eq(List.length(&2, U32, bs), 8n)

def Seid.size(seid: Maybe<&2, B.Bytes()>) -> Nat:
  match seid:
    case None{}:
      0n
    case Some{bs}:
      List.length(&2, U32, bs)

def Seid.flags(seid: Maybe<&2, B.Bytes()>) -> U32:
  match seid:
    case None{}:
      32
    case Some{bs}:
      33

# The octets the length field counts: SEID, sequence number, spare, IEs.
def Msg.body_size(seid: Maybe<&2, B.Bytes()>, ies: List<&2, T.Tlv>) -> Nat:
  Nat.add(Seid.size(seid), Nat.add(4n, T.Tlvs.size(ies)))

def Msg.valid(m: Msg) -> Bool:
  match m:
    case Msg{kind, +len, +seid, seq, +ies}:
      Bool.and(B.fits8(kind), Bool.and(B.fits16(len), Bool.and(Seid.valid(seid), Bool.and(B.fits24(seq), Bool.and(Nat.is_eq(U32.to_nat(len), Msg.body_size(seid, ies)), T.Tlvs.valid(ies))))))

def Msg.of_ies(kind: U32, len: U32, seid: Maybe<&2, B.Bytes()>, seq: U32, r: Result<&2, &2, B.Err, List<&2, T.Tlv>>) -> Result<&2, &2, B.Err, Msg>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ies}:
      Done{Msg{kind, len, seid, seq, ies}}

def Msg.spare_ok(kind: U32, len: U32, seid: Maybe<&2, B.Bytes()>, seq: U32, +sp: U32, rest: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, Msg>:
  match ok:
    case True{}:
      Msg.of_ies(kind, len, seid, seq, T.Tlvs.decode(rest))
    case False{}:
      Fail{B.Invalid{sp}}

def Msg.of_spare(kind: U32, len: U32, seid: Maybe<&2, B.Bytes()>, seq: U32, r: B.Read(U32)) -> Result<&2, &2, B.Err, Msg>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+sp, rest)}:
      Msg.spare_ok(kind, len, seid, seq, sp, rest, U32.is_eq(sp, 0))

def Msg.seq_ok(kind: U32, len: U32, seid: Maybe<&2, B.Bytes()>, +seq: U32, rest: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, Msg>:
  match ok:
    case True{}:
      Msg.of_spare(kind, len, seid, seq, B.u8(rest))
    case False{}:
      Fail{B.Invalid{seq}}

def Msg.of_seq(kind: U32, len: U32, seid: Maybe<&2, B.Bytes()>, r: B.Read(U32)) -> Result<&2, &2, B.Err, Msg>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+seq, rest)}:
      Msg.seq_ok(kind, len, seid, seq, rest, B.fits24(seq))

def Msg.of_seid(kind: U32, len: U32, r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, Msg>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(seid, rest)}:
      Msg.of_seq(kind, len, Some{seid}, B.u24(rest))

# The octets after the length field.
def Msg.parse(s: Bool, kind: U32, len: U32, body: B.Bytes()) -> Result<&2, &2, B.Err, Msg>:
  match s:
    case True{}:
      Msg.of_seid(kind, len, B.take(8n, body))
    case False{}:
      Msg.of_seq(kind, len, None{}, B.u24(body))

def Msg.with_rest(r: Result<&2, &2, B.Err, Msg>, rest: B.Bytes()) -> B.Read(Msg):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{m}:
      Done{(m, rest)}

def Msg.of_body(s: Bool, kind: U32, len: U32, r: B.Read(B.Bytes())) -> B.Read(Msg):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(body, rest)}:
      Msg.with_rest(Msg.parse(s, kind, len, body), rest)

def Msg.len_ok(s: Bool, kind: U32, +len: U32, rest: B.Bytes(), ok: Bool) -> B.Read(Msg):
  match ok:
    case True{}:
      Msg.of_body(s, kind, len, B.take(U32.to_nat(len), rest))
    case False{}:
      Fail{B.Invalid{len}}

def Msg.of_len(s: Bool, kind: U32, r: B.Read(U32)) -> B.Read(Msg):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+len, rest)}:
      Msg.len_ok(s, kind, len, rest, B.fits16(len))

def Msg.type_ok(s: Bool, +kind: U32, rest: B.Bytes(), ok: Bool) -> B.Read(Msg):
  match ok:
    case True{}:
      Msg.of_len(s, kind, B.u16(rest))
    case False{}:
      Fail{B.Invalid{kind}}

def Msg.of_type(s: Bool, r: B.Read(U32)) -> B.Read(Msg):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+kind, rest)}:
      Msg.type_ok(s, kind, rest, B.fits8(kind))

# Version 1 with the S flag clear (0x20) or set (0x21); anything else is unsupported.
def Msg.flags_ok(+flags: U32, rest: B.Bytes(), plain: Bool, with_seid: Bool) -> B.Read(Msg):
  match plain:
    case True{}:
      Msg.of_type(False{}, B.u8(rest))
    case False{}:
      match with_seid:
        case True{}:
          Msg.of_type(True{}, B.u8(rest))
        case False{}:
          Fail{B.Unsupported{flags}}

def Msg.of_flags(r: B.Read(U32)) -> B.Read(Msg):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+flags, rest)}:
      Msg.flags_ok(flags, rest, U32.is_eq(flags, 32), U32.is_eq(flags, 33))

def Msg.read(bs: B.Bytes()) -> B.Read(Msg):
  Msg.of_flags(B.u8(bs))

def Msg.write(m: Msg, rest: B.Bytes()) -> B.Bytes():
  match m:
    case Msg{kind, len, +seid, seq, ies}:
      B.write_u8(Seid.flags(seid), B.write_u8(kind, B.write_u16(len, Addr.write(seid, B.write_u24(seq, B.write_u8(0, T.Tlvs.write(ies, rest)))))))

# A message over its content, with the length word it needs.
def Msg.make(kind: U32, +seid: Maybe<&2, B.Bytes()>, seq: U32, +ies: List<&2, T.Tlv>) -> Msg:
  Msg{kind, U32.from_nat(Msg.body_size(seid, ies)), seid, seq, ies}

# Typed views of IE bodies
# ------------------------
# Each decodes the whole body of its IE, or fails.

def exact(-A: Data, r: B.Read(A)) -> Result<&2, &2, B.Err, A>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(x, rest)}:
      B.end(A, x, rest)

# One-octet values: Cause, Source and Destination Interface, QFI, Gate Status, PDN Type.
def Byte.read(body: B.Bytes()) -> Result<&2, &2, B.Err, U32>:
  exact(U32, B.u8(body))

def Byte.write(v: U32) -> B.Bytes():
  B.write_u8(v, [])

# Two-octet values: PDR ID.
def Short.read(body: B.Bytes()) -> Result<&2, &2, B.Err, U32>:
  exact(U32, B.u16(body))

def Short.write(v: U32) -> B.Bytes():
  B.write_u16(v, [])

# Four-octet values: Recovery Time Stamp, Precedence, FAR ID, QER ID, URR ID.
def Word.read(body: B.Bytes()) -> Result<&2, &2, B.Err, U32>:
  exact(U32, B.u32(body))

def Word.write(v: U32) -> B.Bytes():
  B.write_u32(v, [])

# Node ID (§8.2.38): an IPv4 or IPv6 address, or an FQDN.
type NodeId is Data:
  NodeV4{addr: B.Bytes()}
  NodeV6{addr: B.Bytes()}
  NodeFqdn{name: B.Bytes()}

def NodeId.v4(r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, NodeId>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(addr, rest)}:
      B.end(NodeId, NodeV4{addr}, rest)

def NodeId.v6(r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, NodeId>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(addr, rest)}:
      B.end(NodeId, NodeV6{addr}, rest)

def NodeId.kind(kind: U32, rest: B.Bytes()) -> Result<&2, &2, B.Err, NodeId>:
  match kind:
    case 0:
      NodeId.v4(B.take(4n, rest))
    case 1:
      NodeId.v6(B.take(16n, rest))
    case 2:
      Done{NodeFqdn{rest}}
    case _:
      Fail{B.Unsupported{kind}}

def NodeId.of_kind(r: B.Read(U32)) -> Result<&2, &2, B.Err, NodeId>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(kind, rest)}:
      NodeId.kind(kind, rest)

def NodeId.read(body: B.Bytes()) -> Result<&2, &2, B.Err, NodeId>:
  NodeId.of_kind(B.u8(body))

def NodeId.write(n: NodeId) -> B.Bytes():
  match n:
    case NodeV4{addr}:
      0 <> addr
    case NodeV6{addr}:
      1 <> addr
    case NodeFqdn{name}:
      2 <> name

# Optional addresses, by a flag bit.
def Addr.valid(a: Maybe<&2, B.Bytes()>, n: Nat) -> Bool:
  match a:
    case None{}:
      True{}
    case Some{bs}:
      Nat.is_eq(List.length(&2, U32, bs), n)

def Addr.present(a: Maybe<&2, B.Bytes()>) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{bs}:
      True{}

def Addr.some(r: B.Read(B.Bytes())) -> B.Read(Maybe<&2, B.Bytes()>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bs, rest)}:
      Done{(Some{bs}, rest)}

def Addr.read(flag: Bool, n: Nat, bs: B.Bytes()) -> B.Read(Maybe<&2, B.Bytes()>):
  match flag:
    case False{}:
      Done{(None{}, bs)}
    case True{}:
      Addr.some(B.take(n, bs))

def bit(x: U32, mask: U32) -> Bool:
  Bool.not(U32.is_eq(U32.and(mask, x), 0))

def Flag.bit(b: Bool, mask: U32) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      mask

# F-SEID (§8.2.37): the SEID, then an IPv4 and/or IPv6 address.
type Fseid is Data:
  Fseid{seid: B.Bytes(), v4: Maybe<&2, B.Bytes()>, v6: Maybe<&2, B.Bytes()>}

def Fseid.valid(f: Fseid) -> Bool:
  match f:
    case Fseid{seid, v4, v6}:
      Bool.and(Nat.is_eq(List.length(&2, U32, seid), 8n), Bool.and(Addr.valid(v4, 4n), Addr.valid(v6, 16n)))

# Flag bits: V6 1, V4 2.
def Fseid.flags(v4: Bool, v6: Bool) -> U32:
  U32.or(Flag.bit(v4, 2), Flag.bit(v6, 1))

def Fseid.of_v6(seid: B.Bytes(), v4: Maybe<&2, B.Bytes()>, r: B.Read(Maybe<&2, B.Bytes()>)) -> Result<&2, &2, B.Err, Fseid>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v6, rest)}:
      B.end(Fseid, Fseid{seid, v4, v6}, rest)

def Fseid.of_v4(+flags: U32, seid: B.Bytes(), r: B.Read(Maybe<&2, B.Bytes()>)) -> Result<&2, &2, B.Err, Fseid>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v4, rest)}:
      Fseid.of_v6(seid, v4, Addr.read(bit(flags, 1), 16n, rest))

def Fseid.of_seid(+flags: U32, r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, Fseid>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(seid, rest)}:
      Fseid.of_v4(flags, seid, Addr.read(bit(flags, 2), 4n, rest))

def Fseid.flags_ok(+flags: U32, rest: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, Fseid>:
  match ok:
    case True{}:
      Fseid.of_seid(flags, B.take(8n, rest))
    case False{}:
      Fail{B.Invalid{flags}}

# The spare bits must be zero: the octet is what its two flag bits write.
def Fseid.of_flags(r: B.Read(U32)) -> Result<&2, &2, B.Err, Fseid>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+flags, rest)}:
      Fseid.flags_ok(flags, rest, U32.is_eq(Fseid.flags(bit(flags, 2), bit(flags, 1)), flags))

def Fseid.read(body: B.Bytes()) -> Result<&2, &2, B.Err, Fseid>:
  Fseid.of_flags(B.u8(body))

def Fseid.write(f: Fseid) -> B.Bytes():
  match f:
    case Fseid{seid, +v4, +v6}:
      Fseid.flags(Addr.present(v4), Addr.present(v6)) <> List.append(&2, U32, seid, Addr.write(v4, Addr.write(v6, [])))

# F-TEID (§8.2.3): either a TEID with its address(es), or a request that the
# UP function choose them (CH), optionally tagged with a CHOOSE ID. The CH
# form carries no TEID and no address by construction.
type Fteid is Data:
  Teid{teid: U32, v4: Maybe<&2, B.Bytes()>, v6: Maybe<&2, B.Bytes()>}
  Choose{v4: Bool, v6: Bool, chid: Maybe<&2, U32>}

def Fteid.valid(f: Fteid) -> Bool:
  match f:
    case Teid{teid, +v4, +v6}:
      Bool.and(Bool.or(Addr.present(v4), Addr.present(v6)), Bool.and(Addr.valid(v4, 4n), Addr.valid(v6, 16n)))
    case Choose{v4, v6, chid}:
      Bool.or(v4, v6)

def Fteid.of_v6(teid: U32, v4: Maybe<&2, B.Bytes()>, r: B.Read(Maybe<&2, B.Bytes()>)) -> Result<&2, &2, B.Err, Fteid>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v6, rest)}:
      B.end(Fteid, Teid{teid, v4, v6}, rest)

def Fteid.of_v4(+flags: U32, teid: U32, r: B.Read(Maybe<&2, B.Bytes()>)) -> Result<&2, &2, B.Err, Fteid>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v4, rest)}:
      Fteid.of_v6(teid, v4, Addr.read(bit(flags, 2), 16n, rest))

def Fteid.of_teid(+flags: U32, r: B.Read(U32)) -> Result<&2, &2, B.Err, Fteid>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(teid, rest)}:
      Fteid.of_v4(flags, teid, Addr.read(bit(flags, 1), 4n, rest))

def Fteid.of_chid(v4: Bool, v6: Bool, r: B.Read(U32)) -> Result<&2, &2, B.Err, Fteid>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(chid, rest)}:
      B.end(Fteid, Choose{v4, v6, Some{chid}}, rest)

def Fteid.choose(+flags: U32, rest: B.Bytes(), chid: Bool) -> Result<&2, &2, B.Err, Fteid>:
  match chid:
    case True{}:
      Fteid.of_chid(bit(flags, 1), bit(flags, 2), B.u8(rest))
    case False{}:
      B.end(Fteid, Choose{bit(flags, 1), bit(flags, 2), None{}}, rest)

def Fteid.form(+flags: U32, rest: B.Bytes(), ch: Bool) -> Result<&2, &2, B.Err, Fteid>:
  match ch:
    case True{}:
      Fteid.choose(flags, rest, bit(flags, 8))
    case False{}:
      Fteid.of_teid(flags, B.u32(rest))

# Flag bits: V4 1, V6 2, CH 4, CHID 8.
def Fteid.flags(v4: Bool, v6: Bool, ch: Bool, chid: Bool) -> U32:
  U32.or(Flag.bit(v4, 1), U32.or(Flag.bit(v6, 2), U32.or(Flag.bit(ch, 4), Flag.bit(chid, 8))))

# The spare bits must be zero (the octet is what its four flag bits write), an
# address must be named, and CHID needs CH.
def Fteid.flags_valid(+flags: U32) -> Bool:
  Bool.and(U32.is_eq(Fteid.flags(bit(flags, 1), bit(flags, 2), bit(flags, 4), bit(flags, 8)), flags), Bool.and(Bool.or(bit(flags, 1), bit(flags, 2)), Bool.or(bit(flags, 4), Bool.not(bit(flags, 8)))))

def Fteid.flags_ok(+flags: U32, rest: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, Fteid>:
  match ok:
    case True{}:
      Fteid.form(flags, rest, bit(flags, 4))
    case False{}:
      Fail{B.Invalid{flags}}

def Fteid.of_flags(r: B.Read(U32)) -> Result<&2, &2, B.Err, Fteid>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+flags, rest)}:
      Fteid.flags_ok(flags, rest, Fteid.flags_valid(flags))

def Fteid.read(body: B.Bytes()) -> Result<&2, &2, B.Err, Fteid>:
  Fteid.of_flags(B.u8(body))

def Chid.write(chid: Maybe<&2, U32>) -> B.Bytes():
  match chid:
    case None{}:
      []
    case Some{c}:
      [c]

def Chid.present(chid: Maybe<&2, U32>) -> Bool:
  match chid:
    case None{}:
      False{}
    case Some{c}:
      True{}

def Fteid.write(f: Fteid) -> B.Bytes():
  match f:
    case Teid{teid, +v4, +v6}:
      Fteid.flags(Addr.present(v4), Addr.present(v6), False{}, False{}) <> B.write_u32(teid, Addr.write(v4, Addr.write(v6, [])))
    case Choose{v4, v6, +chid}:
      Fteid.flags(v4, v6, True{}, Chid.present(chid)) <> Chid.write(chid)

# UE IP Address (§8.2.62): an IPv4 and/or IPv6 address, destination or source.
# The choose and prefix forms are not supported.
type UeIp is Data:
  UeIp{source: Bool, v4: Maybe<&2, B.Bytes()>, v6: Maybe<&2, B.Bytes()>}

def UeIp.of_v6(source: Bool, v4: Maybe<&2, B.Bytes()>, r: B.Read(Maybe<&2, B.Bytes()>)) -> Result<&2, &2, B.Err, UeIp>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v6, rest)}:
      B.end(UeIp, UeIp{source, v4, v6}, rest)

def UeIp.of_v4(+flags: U32, r: B.Read(Maybe<&2, B.Bytes()>)) -> Result<&2, &2, B.Err, UeIp>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v4, rest)}:
      UeIp.of_v6(bit(flags, 4), v4, Addr.read(bit(flags, 1), 16n, rest))

def UeIp.flags_ok(+flags: U32, rest: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, UeIp>:
  match ok:
    case True{}:
      UeIp.of_v4(flags, Addr.read(bit(flags, 2), 4n, rest))
    case False{}:
      Fail{B.Unsupported{flags}}

def UeIp.of_flags(r: B.Read(U32)) -> Result<&2, &2, B.Err, UeIp>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+flags, rest)}:
      UeIp.flags_ok(flags, rest, U32.is_lt(flags, 8))

def UeIp.read(body: B.Bytes()) -> Result<&2, &2, B.Err, UeIp>:
  UeIp.of_flags(B.u8(body))

def UeIp.write(u: UeIp) -> B.Bytes():
  match u:
    case UeIp{source, +v4, +v6}:
      U32.or(Flag.bit(source, 4), U32.or(Flag.bit(Addr.present(v4), 2), Flag.bit(Addr.present(v6), 1))) <> Addr.write(v4, Addr.write(v6, []))

# Outer Header Creation (§8.2.56): a two-octet description, then the TEID,
# the address(es) and the UDP port the description calls for. GTP-U/UDP/IPv4
# is 0x0100, GTP-U/UDP/IPv6 0x0200, UDP/IPv4 0x0400, UDP/IPv6 0x0800, IPv4
# 0x1000, IPv6 0x2000; the VLAN tags (0x4000, 0x8000) are not supported.
type Ohc is Data:
  Ohc{desc: U32, teid: Maybe<&2, U32>, v4: Maybe<&2, B.Bytes()>, v6: Maybe<&2, B.Bytes()>, port: Maybe<&2, U32>}

def Ohc.teid_needed(+desc: U32) -> Bool:
  bit(desc, 768)

def Ohc.v4_needed(+desc: U32) -> Bool:
  bit(desc, 5376)

def Ohc.v6_needed(+desc: U32) -> Bool:
  bit(desc, 10752)

def Ohc.port_needed(+desc: U32) -> Bool:
  bit(desc, 3072)

def Ohc.of_port(desc: U32, teid: Maybe<&2, U32>, v4: Maybe<&2, B.Bytes()>, v6: Maybe<&2, B.Bytes()>, r: B.Read(Maybe<&2, U32>)) -> Result<&2, &2, B.Err, Ohc>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(port, rest)}:
      B.end(Ohc, Ohc{desc, teid, v4, v6, port}, rest)

def Word.some(r: B.Read(U32)) -> B.Read(Maybe<&2, U32>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v, rest)}:
      Done{(Some{v}, rest)}

def Word.opt(flag: Bool, r: B.Read(U32), bs: B.Bytes()) -> B.Read(Maybe<&2, U32>):
  match flag:
    case False{}:
      Done{(None{}, bs)}
    case True{}:
      Word.some(r)

def Ohc.of_v6(+desc: U32, teid: Maybe<&2, U32>, v4: Maybe<&2, B.Bytes()>, r: B.Read(Maybe<&2, B.Bytes()>)) -> Result<&2, &2, B.Err, Ohc>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v6, +rest)}:
      Ohc.of_port(desc, teid, v4, v6, Word.opt(Ohc.port_needed(desc), B.u16(rest), rest))

def Ohc.of_v4(+desc: U32, teid: Maybe<&2, U32>, r: B.Read(Maybe<&2, B.Bytes()>)) -> Result<&2, &2, B.Err, Ohc>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v4, rest)}:
      Ohc.of_v6(desc, teid, v4, Addr.read(Ohc.v6_needed(desc), 16n, rest))

def Ohc.of_teid(+desc: U32, r: B.Read(Maybe<&2, U32>)) -> Result<&2, &2, B.Err, Ohc>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(teid, rest)}:
      Ohc.of_v4(desc, teid, Addr.read(Ohc.v4_needed(desc), 4n, rest))

def Ohc.desc_ok(+desc: U32, +rest: B.Bytes(), ok: Bool) -> Result<&2, &2, B.Err, Ohc>:
  match ok:
    case True{}:
      Ohc.of_teid(desc, Word.opt(Ohc.teid_needed(desc), B.u32(rest), rest))
    case False{}:
      Fail{B.Unsupported{desc}}

def Ohc.of_desc(r: B.Read(U32)) -> Result<&2, &2, B.Err, Ohc>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+desc, rest)}:
      Ohc.desc_ok(desc, rest, Bool.not(bit(desc, 49152)))

def Ohc.read(body: B.Bytes()) -> Result<&2, &2, B.Err, Ohc>:
  Ohc.of_desc(B.u16(body))

def Word.write_opt(v: Maybe<&2, U32>, width: Nat, rest: B.Bytes()) -> B.Bytes():
  match v:
    case None{}:
      rest
    case Some{x}:
      match width:
        case 2n:
          B.write_u16(x, rest)
        case _:
          B.write_u32(x, rest)

def Ohc.write(o: Ohc) -> B.Bytes():
  match o:
    case Ohc{desc, teid, v4, v6, port}:
      B.write_u16(desc, Word.write_opt(teid, 4n, Addr.write(v4, Addr.write(v6, Word.write_opt(port, 2n, [])))))

# MBR (§8.2.9): uplink then downlink, 40 bits each in kbit/s, kept as octets.
type Mbr is Data:
  Mbr{ul: B.Bytes(), dl: B.Bytes()}

def Mbr.valid(m: Mbr) -> Bool:
  match m:
    case Mbr{ul, dl}:
      Bool.and(Nat.is_eq(List.length(&2, U32, ul), 5n), Nat.is_eq(List.length(&2, U32, dl), 5n))

def Mbr.of_dl(ul: B.Bytes(), r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, Mbr>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(dl, rest)}:
      B.end(Mbr, Mbr{ul, dl}, rest)

def Mbr.of_ul(r: B.Read(B.Bytes())) -> Result<&2, &2, B.Err, Mbr>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(ul, rest)}:
      Mbr.of_dl(ul, B.take(5n, rest))

def Mbr.read(body: B.Bytes()) -> Result<&2, &2, B.Err, Mbr>:
  Mbr.of_ul(B.take(5n, body))

def Mbr.write(m: Mbr) -> B.Bytes():
  match m:
    case Mbr{ul, dl}:
      List.append(&2, U32, ul, dl)
