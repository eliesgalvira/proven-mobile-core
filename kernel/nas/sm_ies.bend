import Base
import ../bytes.bend as B
import ./ie.bend as I

# Typed views of the 5GSM information elements (TS 24.501 §9.11.4 and the
# TS 24.008 elements it reuses). Readers take the content of an IE as the
# generic codec sliced it; those over lists return what is left.

def Res(-A: Data) -> Data:
  Result<&2, &2, B.Err, A>

def Ok(-A: Data, v: A, tag: U32, ok: Bool) -> Res(A):
  match ok:
    case True{}:
      Done{v}
    case False{}:
      Fail{B.Invalid{tag}}

# Packet filter components (§9.11.4.13, Table 9.11.4.13.1)
# -------------------------------------------------------

# What follows a component type byte. The type byte itself is kept, so a
# component is written back as it came; `Comp.shape` says which payload each
# type carries.
type Payload is Data:
  PNone{}
  PIpv4{addr: U32, mask: U32}
  PIpv6{addr: B.Bytes(), prefix: U32}
  POne{v: U32}
  PTwo{v: U32}
  PThree{v: U32}
  PFour{v: U32}
  PSix{bytes: B.Bytes()}

type Shape is Data:
  SNone{}
  SIpv4{}
  SIpv6{}
  SOne{}
  STwo{}
  SThree{}
  SFour{}
  SSix{}

type Comp is Data:
  Comp{kind: U32, payload: Payload}

def Comp.match_all() -> U32:
  1

def Comp.ipv4_remote() -> U32:
  16

def Comp.ipv4_local() -> U32:
  17

def Shape.of(kind: Nat) -> Maybe<&2, Shape>:
  match kind:
    case 1n:
      Some{SNone{}}
    case 16n:
      Some{SIpv4{}}
    case 17n:
      Some{SIpv4{}}
    case 33n:
      Some{SIpv6{}}
    case 35n:
      Some{SIpv6{}}
    case 48n:
      Some{SOne{}}
    case 64n:
      Some{STwo{}}
    case 65n:
      Some{SFour{}}
    case 80n:
      Some{STwo{}}
    case 81n:
      Some{SFour{}}
    case 96n:
      Some{SFour{}}
    case 112n:
      Some{STwo{}}
    case 128n:
      Some{SThree{}}
    case 129n:
      Some{SSix{}}
    case 130n:
      Some{SSix{}}
    case 131n:
      Some{STwo{}}
    case 132n:
      Some{STwo{}}
    case 133n:
      Some{SOne{}}
    case 134n:
      Some{SOne{}}
    case 135n:
      Some{STwo{}}
    case other:
      None{}

def Comp.shape(kind: U32) -> Maybe<&2, Shape>:
  Shape.of(U32.to_nat(kind))

def Payload.shape(p: Payload) -> Shape:
  match p:
    case PNone{}:
      SNone{}
    case PIpv4{addr, mask}:
      SIpv4{}
    case PIpv6{addr, prefix}:
      SIpv6{}
    case POne{v}:
      SOne{}
    case PTwo{v}:
      STwo{}
    case PThree{v}:
      SThree{}
    case PFour{v}:
      SFour{}
    case PSix{bytes}:
      SSix{}

def Shape.eq(a: Shape, b: Shape) -> Bool:
  match a b:
    case SNone{} SNone{}:
      True{}
    case SIpv4{} SIpv4{}:
      True{}
    case SIpv6{} SIpv6{}:
      True{}
    case SOne{} SOne{}:
      True{}
    case STwo{} STwo{}:
      True{}
    case SThree{} SThree{}:
      True{}
    case SFour{} SFour{}:
      True{}
    case SSix{} SSix{}:
      True{}
    case _ _:
      False{}

# A mask is a run of ones from the top bit: the ones of its complement are
# the low bits, so the complement plus one has no bit in common with it.
def Mask.contiguous(+m: U32) -> Bool:
  U32.is_eq(U32.and(U32.not(m), U32.add(U32.not(m), 1)), 0)

def Payload.valid(p: Payload) -> Bool:
  match p:
    case PIpv4{addr, mask}:
      Mask.contiguous(mask)
    case PIpv6{addr, prefix}:
      Bool.and(Nat.is_eq(List.length(&2, U32, addr), 16n), U32.is_le(prefix, 128))
    case PSix{bytes}:
      Nat.is_eq(List.length(&2, U32, bytes), 6n)
    case _:
      True{}

def Comp.shape_ok(p: Payload, s: Maybe<&2, Shape>) -> Bool:
  match s:
    case None{}:
      False{}
    case Some{shape}:
      Shape.eq(Payload.shape(p), shape)

def Comp.valid(c: Comp) -> Bool:
  match c:
    case Comp{kind, +p}:
      Bool.and(Comp.shape_ok(p, Comp.shape(kind)), Payload.valid(p))

def Payload.write(p: Payload, rest: B.Bytes()) -> B.Bytes():
  match p:
    case PNone{}:
      rest
    case PIpv4{addr, mask}:
      B.write_u32(addr, B.write_u32(mask, rest))
    case PIpv6{addr, prefix}:
      List.append(&2, U32, addr, B.write_u8(prefix, rest))
    case POne{v}:
      B.write_u8(v, rest)
    case PTwo{v}:
      B.write_u16(v, rest)
    case PThree{v}:
      B.write_u24(v, rest)
    case PFour{v}:
      B.write_u32(v, rest)
    case PSix{bytes}:
      List.append(&2, U32, bytes, rest)

def Comp.write(c: Comp, rest: B.Bytes()) -> B.Bytes():
  match c:
    case Comp{kind, p}:
      kind <> Payload.write(p, rest)

def Comps.write(cs: List<&2, Comp>, rest: B.Bytes()) -> B.Bytes():
  match cs:
    case Nil{}:
      rest
    case c <> more:
      Comp.write(c, Comps.write(more, rest))

def Payload.ipv4(addr: U32, r: B.Read(U32)) -> B.Read(Payload):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+mask, rest)}:
      Ok(B.ReadValue(Payload), (PIpv4{addr, mask}, rest), mask, Mask.contiguous(mask))

def Payload.ipv4_addr(r: B.Read(U32)) -> B.Read(Payload):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(addr, rest)}:
      Payload.ipv4(addr, B.u32(rest))

def Payload.ipv6_prefix(addr: B.Bytes(), r: B.Read(U32)) -> B.Read(Payload):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+prefix, rest)}:
      Ok(B.ReadValue(Payload), (PIpv6{addr, prefix}, rest), prefix, U32.is_le(prefix, 128))

def Payload.ipv6(r: B.Read(B.Bytes())) -> B.Read(Payload):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(addr, rest)}:
      Payload.ipv6_prefix(addr, B.u8(rest))

def Payload.one(r: B.Read(U32)) -> B.Read(Payload):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v, rest)}:
      Done{(POne{v}, rest)}

def Payload.two(r: B.Read(U32)) -> B.Read(Payload):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v, rest)}:
      Done{(PTwo{v}, rest)}

def Payload.three(r: B.Read(U32)) -> B.Read(Payload):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v, rest)}:
      Done{(PThree{v}, rest)}

def Payload.four(r: B.Read(U32)) -> B.Read(Payload):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v, rest)}:
      Done{(PFour{v}, rest)}

def Payload.six(r: B.Read(B.Bytes())) -> B.Read(Payload):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(bytes, rest)}:
      Done{(PSix{bytes}, rest)}

def Payload.read(s: Shape, bs: B.Bytes()) -> B.Read(Payload):
  match s:
    case SNone{}:
      Done{(PNone{}, bs)}
    case SIpv4{}:
      Payload.ipv4_addr(B.u32(bs))
    case SIpv6{}:
      Payload.ipv6(B.take(16n, bs))
    case SOne{}:
      Payload.one(B.u8(bs))
    case STwo{}:
      Payload.two(B.u16(bs))
    case SThree{}:
      Payload.three(B.u24(bs))
    case SFour{}:
      Payload.four(B.u32(bs))
    case SSix{}:
      Payload.six(B.take(6n, bs))

def Comp.of(kind: U32, r: B.Read(Payload)) -> B.Read(Comp):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(p, rest)}:
      Done{(Comp{kind, p}, rest)}

def Comp.kind(+kind: U32, rest: B.Bytes(), s: Maybe<&2, Shape>) -> B.Read(Comp):
  match s:
    case None{}:
      Fail{B.Unsupported{kind}}
    case Some{shape}:
      Comp.of(kind, Payload.read(shape, rest))

def Comp.read(bs: B.Bytes()) -> B.Read(Comp):
  match bs:
    case Nil{}:
      Fail{B.Short{}}
    case +kind <> rest:
      Comp.kind(kind, rest, Comp.shape(kind))

def Comps.cons(c: Comp, r: Result<&2, &2, B.Err, List<&2, Comp>>) -> Result<&2, &2, B.Err, List<&2, Comp>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cs}:
      Done{c <> cs}

def Comps.next(r: B.Read(Comp), more: B.Bytes() -> Result<&2, &2, B.Err, List<&2, Comp>>) -> Result<&2, &2, B.Err, List<&2, Comp>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(c, rest)}:
      Comps.cons(c, more(rest))

# Components to the end of a packet filter's contents.
def Comps.go(fuel: Nat, bs: B.Bytes()) -> Result<&2, &2, B.Err, List<&2, Comp>>:
  match fuel bs:
    case _ Nil{}:
      Done{[]}
    case 0n b <> rest:
      Fail{B.Invalid{b}}
    case 1n+f b <> rest:
      Comps.next(Comp.read(b <> rest), left => Comps.go(f, left))

def Comps.read(+bs: B.Bytes()) -> Result<&2, &2, B.Err, List<&2, Comp>>:
  Comps.go(List.length(&2, U32, bs), bs)

def Comps.valid(cs: List<&2, Comp>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> more:
      Bool.and(Comp.valid(c), Comps.valid(more))

# Packet filters
# --------------

# The first byte keeps its spare bits, direction and identifier as read
# (views below); the contents are the components under a one-byte length.
type Filter is Data:
  Filter{hdr: U32, len: U32, comps: List<&2, Comp>}

def Filter.direction(f: Filter) -> U32:
  match f:
    case Filter{hdr, len, comps}:
      U32.and(3, U32.shrn(hdr, 4n))

def Filter.id(f: Filter) -> U32:
  match f:
    case Filter{hdr, len, comps}:
      U32.and(15, hdr)

def Filter.valid(f: Filter) -> Bool:
  match f:
    case Filter{+hdr, +len, +comps}:
      Bool.and(Bool.and(I.fits8(hdr), U32.is_eq(U32.and(192, hdr), 0)), Bool.and(I.fits8(len), Bool.and(Nat.is_eq(U32.to_nat(len), List.length(&2, U32, Comps.write(comps, []))), Comps.valid(comps))))

def Filter.write(f: Filter, rest: B.Bytes()) -> B.Bytes():
  match f:
    case Filter{hdr, len, comps}:
      hdr <> B.write_u8(len, List.append(&2, U32, Comps.write(comps, []), rest))

def Filter.of(hdr: U32, len: U32, r: Result<&2, &2, B.Err, List<&2, Comp>>, rest: B.Bytes()) -> B.Read(Filter):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{comps}:
      Done{(Filter{hdr, len, comps}, rest)}

def Filter.body(hdr: U32, r: B.Read(I.LenBody)) -> B.Read(Filter):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(I.LenBody{len, body}, rest)}:
      Filter.of(hdr, len, Comps.read(body), rest)

def Filter.hdr_ok(hdr: U32, rest: B.Bytes(), ok: Bool) -> B.Read(Filter):
  match ok:
    case True{}:
      Filter.body(hdr, I.lv(rest))
    case False{}:
      Fail{B.Invalid{hdr}}

def Filter.read(bs: B.Bytes()) -> B.Read(Filter):
  match bs:
    case Nil{}:
      Fail{B.Short{}}
    case +hdr <> rest:
      Filter.hdr_ok(hdr, rest, Bool.and(I.fits8(hdr), U32.is_eq(U32.and(192, hdr), 0)))

def Filters.cons(f: Filter, r: B.Read(List<&2, Filter>)) -> B.Read(List<&2, Filter>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(fs, rest)}:
      Done{(f <> fs, rest)}

def Filters.next(r: B.Read(Filter), more: B.Bytes() -> B.Read(List<&2, Filter>)) -> B.Read(List<&2, Filter>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(f, rest)}:
      Filters.cons(f, more(rest))

# Exactly n packet filters.
def Filters.read(n: Nat, bs: B.Bytes()) -> B.Read(List<&2, Filter>):
  match n:
    case 0n:
      Done{([], bs)}
    case 1n+p:
      Filters.next(Filter.read(bs), rest => Filters.read(p, rest))

def Filters.write(fs: List<&2, Filter>, rest: B.Bytes()) -> B.Bytes():
  match fs:
    case Nil{}:
      rest
    case f <> more:
      Filter.write(f, Filters.write(more, rest))

def Filters.valid(fs: List<&2, Filter>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case f <> more:
      Bool.and(Filter.valid(f), Filters.valid(more))

# QoS rules (§9.11.4.13)
# ----------------------

# The filter list a rule carries depends on its operation: whole filters
# (create, add, replace), identifiers only (delete filters) or none.
type RuleFilters is Data:
  Whole{filters: List<&2, Filter>}
  Only{ids: List<&2, U32>}
  NoFilters{}

# Precedence and the segregation/QFI byte, absent when a rule is deleted.
type RuleTail is Data:
  Tail{precedence: U32, qfi: U32}
  NoTail{}

# QRI, the two-byte length, the operation byte (operation code, DQR bit and
# packet filter count, kept as read), the filters and the tail.
type Rule is Data:
  Rule{qri: U32, len: U32, op: U32, filters: RuleFilters, tail: RuleTail}

def Rule.code(op: U32) -> Nat:
  U32.to_nat(U32.shrn(op, 5n))

def Rule.dqr(op: U32) -> Bool:
  U32.is_eq(U32.and(16, op), 16)

def Rule.count(op: U32) -> Nat:
  U32.to_nat(U32.and(15, op))

def Rule.qfi(t: RuleTail) -> Maybe<&2, U32>:
  match t:
    case Tail{precedence, qfi}:
      Some{U32.and(63, qfi)}
    case NoTail{}:
      None{}

def RuleFilters.write(fs: RuleFilters, rest: B.Bytes()) -> B.Bytes():
  match fs:
    case Whole{filters}:
      Filters.write(filters, rest)
    case Only{ids}:
      List.append(&2, U32, ids, rest)
    case NoFilters{}:
      rest

def RuleTail.write(t: RuleTail, rest: B.Bytes()) -> B.Bytes():
  match t:
    case Tail{precedence, qfi}:
      B.write_u8(precedence, B.write_u8(qfi, rest))
    case NoTail{}:
      rest

def Rule.body_write(op: U32, fs: RuleFilters, t: RuleTail) -> B.Bytes():
  op <> RuleFilters.write(fs, RuleTail.write(t, []))

def Rule.write(r: Rule, rest: B.Bytes()) -> B.Bytes():
  match r:
    case Rule{qri, len, op, fs, t}:
      qri <> B.write_u16(len, List.append(&2, U32, Rule.body_write(op, fs, t), rest))

def Rules.write(rs: List<&2, Rule>) -> B.Bytes():
  match rs:
    case Nil{}:
      []
    case r <> more:
      Rule.write(r, Rules.write(more))

def RuleFilters.count(fs: RuleFilters) -> Nat:
  match fs:
    case Whole{filters}:
      List.length(&2, Filter, filters)
    case Only{ids}:
      List.length(&2, U32, ids)
    case NoFilters{}:
      0n

def RuleFilters.valid(fs: RuleFilters) -> Bool:
  match fs:
    case Whole{filters}:
      Filters.valid(filters)
    case Only{ids}:
      B.all_bytes(ids)
    case NoFilters{}:
      True{}

def RuleTail.valid(t: RuleTail) -> Bool:
  match t:
    case Tail{precedence, qfi}:
      Bool.and(I.fits8(precedence), I.fits8(qfi))
    case NoTail{}:
      True{}

# Which filter list and tail each operation code has.
def Rule.shape_ok(code: Nat, fs: RuleFilters, t: RuleTail) -> Bool:
  match code fs t:
    case 1n Whole{filters} Tail{precedence, qfi}:
      True{}
    case 2n NoFilters{} NoTail{}:
      True{}
    case 3n Whole{filters} Tail{precedence, qfi}:
      True{}
    case 4n Whole{filters} Tail{precedence, qfi}:
      True{}
    case 5n Only{ids} Tail{precedence, qfi}:
      True{}
    case 6n NoFilters{} Tail{precedence, qfi}:
      True{}
    case _ _ _:
      False{}

def Rule.valid(r: Rule) -> Bool:
  match r:
    case Rule{+qri, +len, +op, +fs, +t}:
      Bool.and(Bool.and(I.fits8(qri), I.fits8(op)), Bool.and(Bool.and(I.fits16(len), Nat.is_eq(U32.to_nat(len), List.length(&2, U32, Rule.body_write(op, fs, t)))), Bool.and(Bool.and(Rule.shape_ok(Rule.code(op), fs, t), Nat.is_eq(Rule.count(op), RuleFilters.count(fs))), Bool.and(RuleFilters.valid(fs), RuleTail.valid(t)))))

def Rules.valid(rs: List<&2, Rule>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> more:
      Bool.and(Rule.valid(r), Rules.valid(more))

# Reading a rule body: operation byte, filters, tail; nothing may be left.

def Rule.end(qri: U32, len: U32, op: U32, fs: RuleFilters, t: RuleTail, rest: B.Bytes()) -> Res(Rule):
  match rest:
    case Nil{}:
      Done{Rule{qri, len, op, fs, t}}
    case b <> more:
      Fail{B.Invalid{b}}

def Rule.tail_qfi(qri: U32, len: U32, op: U32, fs: RuleFilters, precedence: U32, r: B.Read(U32)) -> Res(Rule):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(qfi, rest)}:
      Rule.end(qri, len, op, fs, Tail{precedence, qfi}, rest)

def Rule.tail(qri: U32, len: U32, op: U32, fs: RuleFilters, r: B.Read(U32)) -> Res(Rule):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(precedence, rest)}:
      Rule.tail_qfi(qri, len, op, fs, precedence, B.u8(rest))

def Rule.whole(qri: U32, len: U32, op: U32, r: B.Read(List<&2, Filter>)) -> Res(Rule):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(filters, rest)}:
      Rule.tail(qri, len, op, Whole{filters}, B.u8(rest))

def Rule.only(qri: U32, len: U32, op: U32, r: B.Read(List<&2, U32>)) -> Res(Rule):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(ids, rest)}:
      Rule.tail(qri, len, op, Only{ids}, B.u8(rest))

def Rule.by_code(qri: U32, len: U32, +op: U32, rest: B.Bytes(), code: Nat) -> Res(Rule):
  match code:
    case 1n:
      Rule.whole(qri, len, op, Filters.read(Rule.count(op), rest))
    case 2n:
      Rule.end(qri, len, op, NoFilters{}, NoTail{}, rest)
    case 3n:
      Rule.whole(qri, len, op, Filters.read(Rule.count(op), rest))
    case 4n:
      Rule.whole(qri, len, op, Filters.read(Rule.count(op), rest))
    case 5n:
      Rule.only(qri, len, op, B.take(Rule.count(op), rest))
    case 6n:
      Rule.tail(qri, len, op, NoFilters{}, B.u8(rest))
    case other:
      Fail{B.Unsupported{op}}

def Rule.body(qri: U32, len: U32, body: B.Bytes()) -> Res(Rule):
  match body:
    case Nil{}:
      Fail{B.Short{}}
    case +op <> rest:
      Rule.by_code(qri, len, op, rest, Rule.code(op))

def Rule.cons(r: Res(Rule), rest: B.Bytes()) -> B.Read(Rule):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{rule}:
      Done{(rule, rest)}

def Rule.len(qri: U32, r: B.Read(I.LenBody)) -> B.Read(Rule):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(I.LenBody{len, body}, rest)}:
      Rule.cons(Rule.body(qri, len, body), rest)

def Rule.read(bs: B.Bytes()) -> B.Read(Rule):
  match bs:
    case Nil{}:
      Fail{B.Short{}}
    case qri <> rest:
      Rule.len(qri, I.lve(rest))

def Rules.cons(r: Rule, more: Res(List<&2, Rule>)) -> Res(List<&2, Rule>):
  match more:
    case Fail{e}:
      Fail{e}
    case Done{rs}:
      Done{r <> rs}

def Rules.next(r: B.Read(Rule), more: B.Bytes() -> Res(List<&2, Rule>)) -> Res(List<&2, Rule>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(rule, rest)}:
      Rules.cons(rule, more(rest))

# Rules to the end of the IE content.
def Rules.go(fuel: Nat, bs: B.Bytes()) -> Res(List<&2, Rule>):
  match fuel bs:
    case _ Nil{}:
      Done{[]}
    case 0n b <> rest:
      Fail{B.Invalid{b}}
    case 1n+f b <> rest:
      Rules.next(Rule.read(b <> rest), left => Rules.go(f, left))

def Rules.read(+bs: B.Bytes()) -> Res(List<&2, Rule>):
  Rules.go(List.length(&2, U32, bs), bs)

# QoS flow descriptions (§9.11.4.12)
# ----------------------------------

type Param is Data:
  Param{id: U32, body: I.LenBody}

# QFI byte, operation byte and the E-bit/parameter-count byte as read, then
# exactly that many parameters.
type Flow is Data:
  Flow{qfi: U32, op: U32, count: U32, params: List<&2, Param>}

def Flow.qfi_value(f: Flow) -> U32:
  match f:
    case Flow{qfi, op, count, params}:
      U32.and(63, qfi)

def Flow.code(f: Flow) -> Nat:
  match f:
    case Flow{qfi, op, count, params}:
      U32.to_nat(U32.shrn(op, 5n))

def Params.cons(p: Param, r: B.Read(List<&2, Param>)) -> B.Read(List<&2, Param>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(ps, rest)}:
      Done{(p <> ps, rest)}

def Param.of(id: U32, r: B.Read(I.LenBody), more: B.Bytes() -> B.Read(List<&2, Param>)) -> B.Read(List<&2, Param>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(lb, rest)}:
      Params.cons(Param{id, lb}, more(rest))

def Params.read(n: Nat, bs: B.Bytes()) -> B.Read(List<&2, Param>):
  match n bs:
    case 0n rest:
      Done{([], rest)}
    case 1n+p Nil{}:
      Fail{B.Short{}}
    case 1n+p id <> rest:
      Param.of(id, I.lv(rest), left => Params.read(p, left))

def Flow.params(qfi: U32, op: U32, count: U32, r: B.Read(List<&2, Param>)) -> B.Read(Flow):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(params, rest)}:
      Done{(Flow{qfi, op, count, params}, rest)}

def Flow.read(bs: B.Bytes()) -> B.Read(Flow):
  match bs:
    case qfi <> op <> +count <> rest:
      Flow.params(qfi, op, count, Params.read(U32.to_nat(U32.and(63, count)), rest))
    case _:
      Fail{B.Short{}}

def Params.write(ps: List<&2, Param>, rest: B.Bytes()) -> B.Bytes():
  match ps:
    case Nil{}:
      rest
    case Param{id, lb} <> more:
      id <> I.write_lv(lb, Params.write(more, rest))

def Flow.write(f: Flow, rest: B.Bytes()) -> B.Bytes():
  match f:
    case Flow{qfi, op, count, params}:
      qfi <> op <> count <> Params.write(params, rest)

def Flows.cons(f: Flow, more: Res(List<&2, Flow>)) -> Res(List<&2, Flow>):
  match more:
    case Fail{e}:
      Fail{e}
    case Done{fs}:
      Done{f <> fs}

def Flows.next(r: B.Read(Flow), more: B.Bytes() -> Res(List<&2, Flow>)) -> Res(List<&2, Flow>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(f, rest)}:
      Flows.cons(f, more(rest))

def Flows.go(fuel: Nat, bs: B.Bytes()) -> Res(List<&2, Flow>):
  match fuel bs:
    case _ Nil{}:
      Done{[]}
    case 0n b <> rest:
      Fail{B.Invalid{b}}
    case 1n+f b <> rest:
      Flows.next(Flow.read(b <> rest), left => Flows.go(f, left))

def Flows.read(+bs: B.Bytes()) -> Res(List<&2, Flow>):
  Flows.go(List.length(&2, U32, bs), bs)

def Flows.write(fs: List<&2, Flow>) -> B.Bytes():
  match fs:
    case Nil{}:
      []
    case f <> more:
      Flow.write(f, Flows.write(more))

# Session-AMBR (§9.11.4.14)
# -------------------------

# Units are defined up to 26 (multiples of 256 Pbps).
type Ambr is Data:
  Ambr{dl_unit: U32, dl: U32, ul_unit: U32, ul: U32}

def Ambr.unit_ok(u: U32) -> Bool:
  U32.is_le(u, 26)

def Ambr.valid(a: Ambr) -> Bool:
  match a:
    case Ambr{du, dl, uu, ul}:
      Bool.and(Ambr.unit_ok(du), Ambr.unit_ok(uu))

def Ambr.read(bs: B.Bytes()) -> Res(Ambr):
  match bs:
    case +du <> d1 <> d0 <> +uu <> u1 <> u0 <> Nil{}:
      Ok(Ambr, Ambr{du, B.cat8(d0, d1), uu, B.cat8(u0, u1)}, du, Bool.and(Ambr.unit_ok(du), Ambr.unit_ok(uu)))
    case _:
      Fail{B.Invalid{0}}

def Ambr.write(a: Ambr) -> B.Bytes():
  match a:
    case Ambr{du, dl, uu, ul}:
      du <> B.write_u16(dl, uu <> B.write_u16(ul, []))

# PDU address (§9.11.4.10)
# ------------------------

type PduAddr is Data:
  Ipv4{addr: U32}
  Ipv6{iid: B.Bytes()}
  Ipv4v6{addr: U32, iid: B.Bytes()}

def PduAddr.type(a: PduAddr) -> U32:
  match a:
    case Ipv4{addr}:
      1
    case Ipv6{iid}:
      2
    case Ipv4v6{addr, iid}:
      3

def PduAddr.write(a: PduAddr) -> B.Bytes():
  match a:
    case Ipv4{addr}:
      1 <> B.write_u32(addr, [])
    case Ipv6{iid}:
      2 <> iid
    case Ipv4v6{addr, iid}:
      3 <> B.write_u32(addr, iid)

def PduAddr.ipv4v6(a3: U32, a2: U32, a1: U32, a0: U32, +iid: B.Bytes()) -> Res(PduAddr):
  Ok(PduAddr, Ipv4v6{B.cat8(a0, B.cat8(a1, B.cat8(a2, a3))), iid}, 3, Nat.is_eq(List.length(&2, U32, iid), 8n))

def PduAddr.ipv6(+iid: B.Bytes()) -> Res(PduAddr):
  Ok(PduAddr, Ipv6{iid}, 2, Nat.is_eq(List.length(&2, U32, iid), 8n))

def PduAddr.body(h: U32, kind: Nat, rest: B.Bytes()) -> Res(PduAddr):
  match kind rest:
    case 1n a3 <> a2 <> a1 <> a0 <> Nil{}:
      Done{Ipv4{B.cat8(a0, B.cat8(a1, B.cat8(a2, a3)))}}
    case 2n iid:
      PduAddr.ipv6(iid)
    case 3n a3 <> a2 <> a1 <> a0 <> iid:
      PduAddr.ipv4v6(a3, a2, a1, a0, iid)
    case _ _:
      Fail{B.Unsupported{h}}

def PduAddr.read(bs: B.Bytes()) -> Res(PduAddr):
  match bs:
    case Nil{}:
      Fail{B.Short{}}
    case +h <> rest:
      PduAddr.body(h, U32.to_nat(h), rest)

# Extended protocol configuration options (TS 24.008 §10.5.6.3A)
# --------------------------------------------------------------

# One leading byte (extension bit set, configuration protocol PPP), then up
# to 255 containers: a two-byte identifier and a one-byte length each.
type Container is Data:
  Container{id: U32, body: I.LenBody}

type Epco is Data:
  Epco{containers: List<&2, Container>}

def Epco.containers(e: Epco) -> List<&2, Container>:
  match e:
    case Epco{cs}:
      cs

def Epco.header() -> U32:
  128

def Epco.limit() -> Nat:
  255n

def Container.valid(c: Container) -> Bool:
  match c:
    case Container{id, lb}:
      Bool.and(I.fits16(id), I.LenBody.valid8(lb))

def Containers.valid(cs: List<&2, Container>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> more:
      Bool.and(Container.valid(c), Containers.valid(more))

def Containers.write(cs: List<&2, Container>) -> B.Bytes():
  match cs:
    case Nil{}:
      []
    case Container{id, lb} <> more:
      B.write_u16(id, I.write_lv(lb, Containers.write(more)))

def Epco.write(e: Epco) -> B.Bytes():
  match e:
    case Epco{cs}:
      Epco.header() <> Containers.write(cs)

# The encoded size: one header byte, then three bytes plus the content per container.
def Containers.size(cs: List<&2, Container>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Container{id, I.LenBody{len, body}} <> more:
      Nat.add(3n, Nat.add(List.length(&2, U32, body), Containers.size(more)))

def Epco.size(e: Epco) -> Nat:
  match e:
    case Epco{cs}:
      1n+Containers.size(cs)

def Epco.valid(e: Epco) -> Bool:
  match e:
    case Epco{+cs}:
      Bool.and(Nat.is_le(List.length(&2, Container, cs), Epco.limit()), Bool.and(Containers.valid(cs), Nat.is_le(Containers.size(cs), 65534n)))

def Containers.cons(c: Container, r: Res(List<&2, Container>)) -> Res(List<&2, Container>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cs}:
      Done{c <> cs}

def Container.body(id: U32, r: B.Read(I.LenBody), more: B.Bytes() -> Res(List<&2, Container>)) -> Res(List<&2, Container>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(lb, rest)}:
      Containers.cons(Container{id, lb}, more(rest))

def Container.id_ok(id: U32, rest: B.Bytes(), more: B.Bytes() -> Res(List<&2, Container>), ok: Bool) -> Res(List<&2, Container>):
  match ok:
    case True{}:
      Container.body(id, I.lv(rest), more)
    case False{}:
      Fail{B.Invalid{id}}

def Container.id(r: B.Read(U32), more: B.Bytes() -> Res(List<&2, Container>)) -> Res(List<&2, Container>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(+id, rest)}:
      Container.id_ok(id, rest, more, I.fits16(id))

# Containers to the end of the content, at most `budget` of them.
def Containers.go(fuel: Nat, budget: Nat, bs: B.Bytes()) -> Res(List<&2, Container>):
  match fuel budget bs:
    case _ _ Nil{}:
      Done{[]}
    case 0n _ b <> rest:
      Fail{B.Invalid{b}}
    case 1n+f 0n b <> rest:
      Fail{B.Invalid{b}}
    case 1n+f 1n+k b <> rest:
      Container.id(B.u16(b <> rest), left => Containers.go(f, k, left))

def Epco.of(r: Res(List<&2, Container>)) -> Res(Epco):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cs}:
      Done{Epco{cs}}

def Epco.hdr(h: U32, +rest: B.Bytes(), ok: Bool) -> Res(Epco):
  match ok:
    case True{}:
      Epco.of(Containers.go(List.length(&2, U32, rest), Epco.limit(), rest))
    case False{}:
      Fail{B.Invalid{h}}

def Epco.read(bs: B.Bytes()) -> Res(Epco):
  match bs:
    case Nil{}:
      Fail{B.Short{}}
    case +h <> +rest:
      Epco.hdr(h, rest, Bool.and(U32.is_eq(h, Epco.header()), Nat.is_le(List.length(&2, U32, rest), 65534n)))

# Small 5GSM elements
# -------------------

# 5GSM capability (§9.11.4.1): one byte of flags, up to twelve more.
def SmCap.read(bs: B.Bytes()) -> Res(B.Bytes()):
  match bs:
    case Nil{}:
      Fail{B.Short{}}
    case +b <> +more:
      Ok(B.Bytes(), b <> more, b, Nat.is_le(List.length(&2, U32, more), 12n))

# PDU session type (§9.11.4.11) and SSC mode (§9.11.4.16): the low three bits of a one-octet IE.
def Nibble3.read(+nibble: U32) -> Res(U32):
  Ok(U32, U32.and(7, nibble), nibble, U32.is_eq(U32.and(8, nibble), 0))

# 5GSM cause (§9.11.4.2): one byte.
def Cause.read(bs: B.Bytes()) -> Res(U32):
  match bs:
    case +c <> Nil{}:
      Done{c}
    case _:
      Fail{B.Invalid{0}}

# Integrity protection maximum data rate (§9.11.4.7): uplink then downlink.
type MaxRate is Data:
  MaxRate{ul: U32, dl: U32}

def MaxRate.of(bs: B.Bytes()) -> Res(MaxRate):
  match bs:
    case ul <> dl <> Nil{}:
      Done{MaxRate{ul, dl}}
    case _:
      Fail{B.Invalid{0}}

def MaxRate.write(r: MaxRate) -> B.Bytes():
  match r:
    case MaxRate{ul, dl}:
      [ul, dl]
