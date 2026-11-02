import Base
import ../bytes.bend as B
import ../aper.bend as Ap

# NGAP framing (TS 38.413 §9.3): the PDU wrapper, protocol IE fields and
# their containers, and extension containers. IE values stay open-type
# octets here; the generated codec decodes each one by its type.

def Criticality.reject() -> U32:
  0

def Criticality.ignore() -> U32:
  1

def Criticality.notify() -> U32:
  2

def Criticality.read(c: Ap.Cur) -> Ap.Rd(U32):
  Ap.Int.read(2n, 2, c)

def Criticality.write(v: U32, rem: Nat, rest: Ap.Bits()) -> Ap.Bits():
  Ap.Int.write(2n, v, rem, rest)

def Criticality.after(rem: Nat) -> Nat:
  Ap.Int.after(2n, rem)

def Criticality.valid(v: U32) -> Bool:
  Ap.Int.valid(2n, 2, v)

# Whether an OPTIONAL component is present (its bit in a SEQUENCE preamble).
def Present(-A: Data, m: Maybe<&2, A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

# ProtocolIE-Field and ProtocolExtensionField: a 16-bit id, a criticality
# and an open type.
type Ie is Data:
  Ie{id: U32, crit: U32, value: B.Bytes()}

def Ie.id(ie: Ie) -> U32:
  match ie:
    case Ie{id, crit, value}:
      id

def Ie.crit(ie: Ie) -> U32:
  match ie:
    case Ie{id, crit, value}:
      crit

def Ie.value(ie: Ie) -> B.Bytes():
  match ie:
    case Ie{id, crit, value}:
      value

def Ie.valid(ie: Ie) -> Bool:
  match ie:
    case Ie{id, crit, value}:
      Bool.and(Ap.Int.valid(16n, 65535, id), Bool.and(Criticality.valid(crit), Ap.Open.valid(value)))

def Ie.r_value(id: U32, crit: U32, r: Ap.Rd(B.Bytes())) -> Ap.Rd(Ie):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(value, c)}:
      Done{(Ie{id, crit, value}, c)}

def Ie.r_crit(id: U32, r: Ap.Rd(U32)) -> Ap.Rd(Ie):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(crit, c)}:
      Ie.r_value(id, crit, Ap.Open.read(c))

def Ie.r_id(r: Ap.Rd(U32)) -> Ap.Rd(Ie):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(id, c)}:
      Ie.r_crit(id, Criticality.read(c))

def Ie.read(c: Ap.Cur) -> Ap.Rd(Ie):
  Ie.r_id(Ap.AInt.read(16n, 65535, c))

def Ie.write(ie: Ie, +rem: Nat, rest: Ap.Bits()) -> Ap.Bits():
  match ie:
    case Ie{id, crit, value}:
      Ap.AInt.write(16n, id, rem, Criticality.write(crit, Ap.AInt.after(16n, rem), Ap.Open.write(value, Criticality.after(Ap.AInt.after(16n, rem)), rest)))

def Ie.after(rem: Nat) -> Nat:
  0n

def Ies.all_valid(ies: List<&2, Ie>) -> Bool:
  match ies:
    case Nil{}:
      True{}
    case ie <> more:
      Bool.and(Ie.valid(ie), Ies.all_valid(more))

def Ies.cons(ie: Ie, r: Ap.Rd(List<&2, Ie>)) -> Ap.Rd(List<&2, Ie>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(ies, c)}:
      Done{(ie <> ies, c)}

def Ies.next(r: Ap.Rd(Ie), more: Ap.Cur -> Ap.Rd(List<&2, Ie>)) -> Ap.Rd(List<&2, Ie>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(ie, c)}:
      Ies.cons(ie, more(c))

# Exactly n fields.
def Ies.items(n: Nat, c: Ap.Cur) -> Ap.Rd(List<&2, Ie>):
  match n:
    case 0n:
      Done{([], c)}
    case 1n+p:
      Ies.next(Ie.read(c), c2 => Ies.items(p, c2))

def Ies.items_write(ies: List<&2, Ie>, +rem: Nat, rest: Ap.Bits()) -> Ap.Bits():
  match ies:
    case Nil{}:
      rest
    case ie <> more:
      Ie.write(ie, rem, Ies.items_write(more, Ie.after(rem), rest))

def Ies.count(r: Ap.Rd(Nat)) -> Ap.Rd(List<&2, Ie>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(n, c)}:
      Ies.items(n, c)

# ProtocolIE-Container: SEQUENCE (SIZE(0..65535)) OF ProtocolIE-Field.
def Ies.valid(+ies: List<&2, Ie>) -> Bool:
  Bool.and(Ap.Size.valid(0n, 65535n, List.length(&2, Ie, ies)), Ies.all_valid(ies))

def Ies.read(c: Ap.Cur) -> Ap.Rd(List<&2, Ie>):
  Ies.count(Ap.Size.read(True{}, 16n, 0n, 65535n, c))

def Ies.write(+ies: List<&2, Ie>, +rem: Nat, rest: Ap.Bits()) -> Ap.Bits():
  Ap.Size.write(True{}, 16n, 0n, List.length(&2, Ie, ies), rem, Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), rest))

def Ies.after(rem: Nat) -> Nat:
  0n

# ProtocolExtensionContainer: SEQUENCE (SIZE(1..65535)) OF ProtocolExtensionField.
def Exts.valid(+ies: List<&2, Ie>) -> Bool:
  Bool.and(Ap.Size.valid(1n, 65534n, List.length(&2, Ie, ies)), Ies.all_valid(ies))

def Exts.read(c: Ap.Cur) -> Ap.Rd(List<&2, Ie>):
  Ies.count(Ap.Size.read(True{}, 16n, 1n, 65534n, c))

def Exts.write(+ies: List<&2, Ie>, +rem: Nat, rest: Ap.Bits()) -> Ap.Bits():
  Ap.Size.write(True{}, 16n, 1n, List.length(&2, Ie, ies), rem, Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), rest))

def Exts.after(rem: Nat) -> Nat:
  0n

# NGAP-PDU: an extensible CHOICE of InitiatingMessage (0), SuccessfulOutcome
# (1) and UnsuccessfulOutcome (2), each a procedure code, a criticality and
# the message as an open type. The extension alternatives are Unsupported.
type Pdu is Data:
  Pdu{kind: U32, code: U32, crit: U32, value: B.Bytes()}

def Pdu.initiating() -> U32:
  0

def Pdu.successful() -> U32:
  1

def Pdu.unsuccessful() -> U32:
  2

def Pdu.kind(p: Pdu) -> U32:
  match p:
    case Pdu{kind, code, crit, value}:
      kind

def Pdu.code(p: Pdu) -> U32:
  match p:
    case Pdu{kind, code, crit, value}:
      code

def Pdu.crit(p: Pdu) -> U32:
  match p:
    case Pdu{kind, code, crit, value}:
      crit

def Pdu.value(p: Pdu) -> B.Bytes():
  match p:
    case Pdu{kind, code, crit, value}:
      value

def Pdu.valid(p: Pdu) -> Bool:
  match p:
    case Pdu{kind, code, crit, value}:
      Bool.and(Ap.Int.valid(2n, 2, kind), Bool.and(Ap.Int.valid(8n, 255, code), Bool.and(Criticality.valid(crit), Ap.Open.valid(value))))

def Pdu.tail(p: Pdu, ok: Bool) -> Result<&2, &2, B.Err, Pdu>:
  match ok:
    case True{}:
      Done{p}
    case False{}:
      Fail{B.Invalid{3}}

def Pdu.end(p: Pdu, c: Ap.Cur) -> Result<&2, &2, B.Err, Pdu>:
  match c:
    case Ap.Cur{rem, bits}:
      Pdu.tail(p, Ap.Tail.zero(bits))

def Pdu.r_value(kind: U32, code: U32, crit: U32, r: Ap.Rd(B.Bytes())) -> Result<&2, &2, B.Err, Pdu>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(value, c)}:
      Pdu.end(Pdu{kind, code, crit, value}, c)

def Pdu.r_crit(kind: U32, code: U32, r: Ap.Rd(U32)) -> Result<&2, &2, B.Err, Pdu>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(crit, c)}:
      Pdu.r_value(kind, code, crit, Ap.Open.read(c))

def Pdu.r_code(kind: U32, r: Ap.Rd(U32)) -> Result<&2, &2, B.Err, Pdu>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(code, c)}:
      Pdu.r_crit(kind, code, Criticality.read(c))

def Pdu.r_kind(r: Ap.Rd(U32)) -> Result<&2, &2, B.Err, Pdu>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(kind, c)}:
      Pdu.r_code(kind, Ap.AInt.read(8n, 255, c))

def Pdu.r_ext(r: Ap.Rd(Bool)) -> Result<&2, &2, B.Err, Pdu>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(ext, c)}:
      match ext:
        case True{}:
          Fail{B.Unsupported{0}}
        case False{}:
          Pdu.r_kind(Ap.Int.read(2n, 2, c))

def Pdu.read(bs: B.Bytes()) -> Result<&2, &2, B.Err, Pdu>:
  Pdu.r_ext(Ap.Bit.read(Ap.Cur{0n, Ap.unpack(bs)}))

def Pdu.bits(p: Pdu, rest: Ap.Bits()) -> Ap.Bits():
  match p:
    case Pdu{kind, code, crit, value}:
      Ap.Bit.write(False{}, 0n, Ap.Int.write(2n, kind, 7n, Ap.AInt.write(8n, code, 5n, Criticality.write(crit, 0n, Ap.Open.write(value, 6n, rest)))))

def Pdu.write(p: Pdu) -> B.Bytes():
  Ap.pack(Pdu.bits(p, []))

# Message views (TS 38.413 §10.3): a view of a container succeeds only when
# no IE id repeats (§10.3.6), every IE with criticality reject is one the
# view comprehends (§10.3.4), and each mandatory IE is present. The ids a
# view comprehends are its `known` list.
def Ies.has(+id: U32, ies: List<&2, Ie>) -> Bool:
  match ies:
    case Nil{}:
      False{}
    case ie <> more:
      Bool.or(U32.is_eq(Ie.id(ie), id), Ies.has(id, more))

def Ies.no_dups(ies: List<&2, Ie>) -> Bool:
  match ies:
    case Nil{}:
      True{}
    case +ie <> +more:
      Bool.and(Bool.not(Ies.has(Ie.id(ie), more)), Ies.no_dups(more))

def Ids.has(+id: U32, ids: List<&2, U32>) -> Bool:
  match ids:
    case Nil{}:
      False{}
    case k <> more:
      Bool.or(U32.is_eq(k, id), Ids.has(id, more))

def Ies.comprehended(+known: List<&2, U32>, ies: List<&2, Ie>) -> Bool:
  match ies:
    case Nil{}:
      True{}
    case +ie <> more:
      Bool.and(Bool.or(Bool.not(U32.is_eq(Ie.crit(ie), Criticality.reject())), Ids.has(Ie.id(ie), known)), Ies.comprehended(known, more))

def Ies.bump(c: Nat, hit: Bool) -> Nat:
  match hit:
    case True{}:
      1n+c
    case False{}:
      c

def Ies.occurrences(+id: U32, ies: List<&2, Ie>) -> Nat:
  match ies:
    case Nil{}:
      0n
    case ie <> more:
      Ies.bump(Ies.occurrences(id, more), U32.is_eq(Ie.id(ie), id))

def Ies.pick(ie: Ie, rest: Maybe<&2, B.Bytes()>, hit: Bool) -> Maybe<&2, B.Bytes()>:
  match hit:
    case True{}:
      Some{Ie.value(ie)}
    case False{}:
      rest

# The value of the first IE with this id.
def Ies.lookup(+id: U32, ies: List<&2, Ie>) -> Maybe<&2, B.Bytes()>:
  match ies:
    case Nil{}:
      None{}
    case +ie <> more:
      Ies.pick(ie, Ies.lookup(id, more), U32.is_eq(Ie.id(ie), id))

def View.gate(ies: List<&2, Ie>, ok: Bool) -> Result<&2, &2, B.Err, List<&2, Ie>>:
  match ok:
    case True{}:
      Done{ies}
    case False{}:
      Fail{B.Invalid{0}}

def View.prelude(+known: List<&2, U32>, +ies: List<&2, Ie>) -> Result<&2, &2, B.Err, List<&2, Ie>>:
  View.gate(ies, Bool.and(Ies.no_dups(ies), Ies.comprehended(known, ies)))

def View.whole(-A: Data, v: A, ok: Bool) -> Result<&2, &2, B.Err, A>:
  match ok:
    case True{}:
      Done{v}
    case False{}:
      Fail{B.Invalid{4}}

# An IE value is a complete encoding: the type's decoder consumes all but padding.
def View.exact(-A: Data, r: Ap.Rd(A)) -> Result<&2, &2, B.Err, A>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(v, c)}:
      match c:
        case Ap.Cur{rem, bits}:
          View.whole(A, v, Ap.Tail.zero(bits))

