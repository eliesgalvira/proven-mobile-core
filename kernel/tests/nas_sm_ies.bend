import Base
import ../bytes.bend as B
import ../nas/ie.bend as I
import ../nas/sm.bend as S
import ../nas/sm_ies.bend as Q
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture

# Typed views of the IEs in the captured 5GSM messages, and malformed cases:
# a truncated rule, a non-contiguous mask, a five-byte Session-AMBR, an ePCO
# of 300 containers.

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

def decoded(r: Result<&2, &2, B.Err, S.Sm>) -> S.Sm:
  match r:
    case Fail{e}:
      S.Sm{0, 0, S.SmStatus{}, [], []}
    case Done{m}:
      m

def msg(+index: Nat) -> S.Sm:
  decoded(S.Sm.read(V.Vec.bytes(V.Vec.field(message(V.Vec.items(V.Vec.field(Capture.data(), "messages")), index), "hex"))))

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

def field(m: S.Sm, n: Nat) -> List<&2, U32>:
  field_of(List.get(&2, I.Field, S.Sm.fields(m), n))

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

def opt(m: S.Sm, iei: U32) -> List<&2, U32>:
  opt_in(S.Sm.opts(m), iei)

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

def fails_res(-A: Data, r: Q.Res(A)) -> Bool:
  Result.is_fail(&2, &2, B.Err, A, r)

def fails_read(-A: Data, r: B.Read(A)) -> Bool:
  Result.is_fail(&2, &2, B.Err, B.ReadValue(A), r)

# Expected shapes
# ---------------

def comp_match_all(c: Q.Comp) -> Bool:
  match c:
    case Q.Comp{+kind, Q.PNone{}}:
      U32.is_eq(kind, 1)
    case _:
      False{}

def filter_is(f: Q.Filter) -> Bool:
  match f:
    case Q.Filter{+hdr, +len, +c <> Nil{}}:
      Bool.and(Bool.and(U32.is_eq(Q.Filter.direction(Q.Filter{hdr, len, [c]}), 3), U32.is_eq(Q.Filter.id(Q.Filter{hdr, len, [c]}), 1)), Bool.and(U32.is_eq(len, 1), comp_match_all(c)))
    case _:
      False{}

def rule_filters(fs: Q.RuleFilters) -> Bool:
  match fs:
    case Q.Whole{+f <> Nil{}}:
      filter_is(f)
    case _:
      False{}

def rule_tail(t: Q.RuleTail) -> Bool:
  match t:
    case Q.Tail{+precedence, +qfi}:
      Bool.and(U32.is_eq(precedence, 255), U32.is_eq(qfi, 1))
    case Q.NoTail{}:
      False{}

def rule_is(r: Q.Rule) -> Bool:
  match r:
    case Q.Rule{+qri, +len, +op, +fs, +t}:
      Bool.and(Bool.and(U32.is_eq(qri, 1), U32.is_eq(len, 6)), Bool.and(Bool.and(Nat.is_eq(Q.Rule.code(op), 1n), Bool.and(Q.Rule.dqr(op), Nat.is_eq(Q.Rule.count(op), 1n))), Bool.and(rule_filters(fs), rule_tail(t))))

def rules_is(r: Q.Res(List<&2, Q.Rule>), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{+rule <> Nil{}}:
      Bool.and(Bool.and(rule_is(rule), Q.Rules.valid([rule])), C.Check.bytes_eq(Q.Rules.write([rule]), bs))
    case _:
      False{}

def ambr_is(r: Q.Res(Q.Ambr), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{Q.Ambr{+du, +dl, +uu, +ul}}:
      Bool.and(Bool.and(Bool.and(U32.is_eq(du, 3), U32.is_eq(dl, 62500)), Bool.and(U32.is_eq(uu, 3), U32.is_eq(ul, 62500))), Bool.and(Q.Ambr.valid(Q.Ambr{du, dl, uu, ul}), C.Check.bytes_eq(Q.Ambr.write(Q.Ambr{du, dl, uu, ul}), bs)))
    case Fail{e}:
      False{}

def addr_is(r: Q.Res(Q.PduAddr), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{Q.Ipv4{+addr}}:
      Bool.and(U32.is_eq(addr, 170721282), C.Check.bytes_eq(Q.PduAddr.write(Q.Ipv4{addr}), bs))
    case _:
      False{}

def param_is(p: Q.Param) -> Bool:
  match p:
    case Q.Param{+id, I.LenBody{+len, +body}}:
      Bool.and(Bool.and(U32.is_eq(id, 1), U32.is_eq(len, 1)), C.Check.bytes_eq(body, [9]))

def flow_is(f: Q.Flow) -> Bool:
  match f:
    case Q.Flow{+qfi, +op, +count, +p <> Nil{}}:
      Bool.and(Bool.and(U32.is_eq(Q.Flow.qfi_value(Q.Flow{qfi, op, count, [p]}), 1), Nat.is_eq(Q.Flow.code(Q.Flow{qfi, op, count, [p]}), 1n)), Bool.and(U32.is_eq(count, 65), param_is(p)))
    case _:
      False{}

def flows_is(r: Q.Res(List<&2, Q.Flow>), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{+f <> Nil{}}:
      Bool.and(flow_is(f), C.Check.bytes_eq(Q.Flows.write([f]), bs))
    case _:
      False{}

def container_is(c: Q.Container, id: U32, +content: List<&2, U32>) -> Bool:
  match c:
    case Q.Container{+i, I.LenBody{+len, +body}}:
      Bool.and(U32.is_eq(i, id), C.Check.bytes_eq(body, content))

def epco_req(r: Q.Res(Q.Epco), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{Q.Epco{+a <> +b <> Nil{}}}:
      Bool.and(Bool.and(container_is(a, 10, []), container_is(b, 13, [])), Bool.and(Q.Epco.valid(Q.Epco{[a, b]}), C.Check.bytes_eq(Q.Epco.write(Q.Epco{[a, b]}), bs)))
    case _:
      False{}

def epco_accept(r: Q.Res(Q.Epco), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{Q.Epco{+a <> Nil{}}}:
      Bool.and(container_is(a, 13, [8, 8, 8, 8]), Bool.and(Q.Epco.valid(Q.Epco{[a]}), C.Check.bytes_eq(Q.Epco.write(Q.Epco{[a]}), bs)))
    case _:
      False{}

def epco_count(r: Q.Res(Q.Epco), n: Nat) -> Bool:
  match r:
    case Done{Q.Epco{+cs}}:
      Nat.is_eq(List.length(&2, Q.Container, cs), n)
    case Fail{e}:
      False{}

def rate_is(r: Q.Res(Q.MaxRate)) -> Bool:
  match r:
    case Done{Q.MaxRate{+ul, +dl}}:
      Bool.and(U32.is_eq(ul, 255), U32.is_eq(dl, 255))
    case Fail{e}:
      False{}

def u32_is(r: Q.Res(U32), v: U32) -> Bool:
  match r:
    case Done{+x}:
      U32.is_eq(x, v)
    case Fail{e}:
      False{}

def bytes_is(r: Q.Res(List<&2, U32>), +bs: List<&2, U32>) -> Bool:
  match r:
    case Done{+x}:
      C.Check.bytes_eq(x, bs)
    case Fail{e}:
      False{}

# All masks of k leading ones, k from 32 down to 0, are contiguous.
def masks_ok(k: Nat, +m: U32) -> Bool:
  match k:
    case 0n:
      Q.Mask.contiguous(0)
    case 1n+p:
      Bool.and(Q.Mask.contiguous(m), masks_ok(p, U32.shln(m, 1n)))

# `n` empty containers with identifier 0x000a.
def containers(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+p:
      0 <> 10 <> 0 <> containers(p)

def main() -> IO(Unit):
  do IO<Unit>:
    +req : S.Sm = msg(32n)
    C.Check.report("Establishment request: integrity protection maximum data rate is full rate", rate_is(Q.MaxRate.of(List.append(&2, U32, field(req, 0n), field(req, 1n)))))
    C.Check.report("Establishment request: PDU session type IPv4", Bool.and(has_t1(S.Sm.opts(req), 145), u32_is(Q.Nibble3.read(1), 1)))
    C.Check.report("Establishment request: SSC mode 1", Bool.and(has_t1(S.Sm.opts(req), 161), u32_is(Q.Nibble3.read(1), 1)))
    C.Check.report("Establishment request: 5GSM capability", bytes_is(Q.SmCap.read(opt(req, 40)), [0]))
    C.Check.report("Establishment request: ePCO asks for an IP address and a DNS server", epco_req(Q.Epco.read(opt(req, 123)), opt(req, 123)))
    +acc : S.Sm = msg(39n)
    C.Check.report("Establishment accept: selected PDU session type IPv4 and SSC mode 1", U32.is_eq(first_byte(field(acc, 0n)), 17))
    C.Check.report("Establishment accept: one authorized QoS rule, match-all, QFI 1", rules_is(Q.Rules.read(field(acc, 1n)), field(acc, 1n)))
    C.Check.report("Establishment accept: Session-AMBR 1 Gbps both ways", ambr_is(Q.Ambr.read(field(acc, 2n)), field(acc, 2n)))
    C.Check.report("Establishment accept: PDU address 10.45.0.2", addr_is(Q.PduAddr.read(opt(acc, 41)), opt(acc, 41)))
    C.Check.report("Establishment accept: one QoS flow description, 5QI 9", flows_is(Q.Flows.read(opt(acc, 121)), opt(acc, 121)))
    C.Check.report("Establishment accept: ePCO carries DNS server 8.8.8.8", epco_accept(Q.Epco.read(opt(acc, 123)), opt(acc, 123)))
    C.Check.report("a rule cut short of its declared length is Short", fails_res(List<&2, Q.Rule>, Q.Rules.read([1, 0, 6, 49, 49, 1, 1])))
    C.Check.report("a rule with a byte beyond its contents is rejected", fails_res(List<&2, Q.Rule>, Q.Rules.read([1, 0, 7, 49, 49, 1, 1, 255, 1, 0])))
    C.Check.report("a rule whose filter overruns the rule is rejected", fails_res(List<&2, Q.Rule>, Q.Rules.read([1, 0, 6, 49, 49, 9, 1, 255, 1])))
    C.Check.report("a filter with spare bits set is rejected", fails_read(Q.Filter, Q.Filter.read([241, 1, 1])))
    C.Check.report("an IPv4 remote address with a contiguous mask decodes", Bool.not(fails_read(Q.Comp, Q.Comp.read([16, 10, 0, 0, 1, 255, 255, 255, 0]))))
    C.Check.report("an IPv4 remote address with a non-contiguous mask is rejected", fails_read(Q.Comp, Q.Comp.read([16, 10, 0, 0, 1, 255, 255, 0, 255])))
    C.Check.report("every mask of leading ones is contiguous", masks_ok(33n, 4294967295))
    C.Check.report("a mask with a hole is not contiguous", Bool.not(Q.Mask.contiguous(4294901855)))
    C.Check.report("an unknown component type is Unsupported", fails_read(Q.Comp, Q.Comp.read([2, 0])))
    C.Check.report("a Session-AMBR of five bytes is rejected", fails_res(Q.Ambr, Q.Ambr.read([3, 244, 36, 3, 244])))
    C.Check.report("a Session-AMBR with an undefined unit is rejected", fails_res(Q.Ambr, Q.Ambr.read([27, 244, 36, 3, 244, 36])))
    C.Check.report("an ePCO of 255 containers decodes", epco_count(Q.Epco.read(128 <> containers(255n)), 255n))
    C.Check.report("an ePCO of 300 containers is rejected", fails_res(Q.Epco, Q.Epco.read(128 <> containers(300n))))
    C.Check.report("an ePCO without its extension bit is rejected", fails_res(Q.Epco, Q.Epco.read([0, 0, 10, 0])))
    C.Check.report("a PDU address of the wrong length is rejected", fails_res(Q.PduAddr, Q.PduAddr.read([1, 10, 45, 0])))
    C.Check.report("an IPv4v6 PDU address decodes", Bool.not(fails_res(Q.PduAddr, Q.PduAddr.read([3, 10, 45, 0, 2, 1, 2, 3, 4, 5, 6, 7, 8]))))
