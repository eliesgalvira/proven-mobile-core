import Base

# A JSON document from test-vectors/, as scripts/gen-vectors.py emits it.
# Numbers above 4294967295 and floats arrive as VText.
type Vec is Data:
  VText{text: String}
  VNat{n: Nat}
  VBool{b: Bool}
  VNull{}
  VList{items: List<&2, Vec>}
  VObj{fields: List<&2, Vec.Field>}

type Vec.Field is Data:
  Field{key: String, val: Vec}

def Vec.lookup.hit(rest: Unit -> Maybe<&2, Vec>, v: Vec, hit: Bool) -> Maybe<&2, Vec>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      rest(Unit{})

def Vec.lookup(fields: List<&2, Vec.Field>, +key: String) -> Maybe<&2, Vec>:
  match fields:
    case Nil{}:
      None{}
    case Field{k, v} <> rest:
      Vec.lookup.hit(u => Vec.lookup(rest, key), v, String.eq(k, key))

def Vec.get(v: Vec, +key: String) -> Maybe<&2, Vec>:
  match v:
    case VObj{fields}:
      Vec.lookup(fields, key)
    case VText{t}:
      None{}
    case VNat{n}:
      None{}
    case VBool{b}:
      None{}
    case VNull{}:
      None{}
    case VList{items}:
      None{}

# Field access by name: a missing field reads as VNull.
def Vec.field(v: Vec, +key: String) -> Vec:
  Maybe.default(&2, Vec, Vec.get(v, key), VNull{})

def Vec.items(v: Vec) -> List<&2, Vec>:
  match v:
    case VList{items}:
      items
    case VText{t}:
      Nil{}
    case VNat{n}:
      Nil{}
    case VBool{b}:
      Nil{}
    case VNull{}:
      Nil{}
    case VObj{fields}:
      Nil{}

def Vec.text(v: Vec) -> String:
  match v:
    case VText{t}:
      t
    case VNat{n}:
      ""
    case VBool{b}:
      ""
    case VNull{}:
      ""
    case VList{items}:
      ""
    case VObj{fields}:
      ""

def Vec.nat(v: Vec) -> Nat:
  match v:
    case VNat{n}:
      n
    case VText{t}:
      0n
    case VBool{b}:
      0n
    case VNull{}:
      0n
    case VList{items}:
      0n
    case VObj{fields}:
      0n

def Vec.hex_digit.go(code: U32, lower: Bool, upper: Bool) -> U32:
  match lower:
    case True{}:
      (code - 87 : U32)
    case False{}:
      match upper:
        case True{}:
          (code - 55 : U32)
        case False{}:
          (code - 48 : U32)

def Vec.hex_digit(c: Char) -> U32:
  match c:
    case Chr{+code}:
      Vec.hex_digit.go(code, U32.is_ge(code, 97), U32.is_ge(code, 65))

# Lowercase or uppercase hex text to bytes; an odd trailing digit is dropped.
def Vec.hex(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{hi, rest}:
      match rest:
        case SNil{}:
          Nil{}
        case SCon{lo, tail}:
          (Vec.hex_digit(hi) * 16 + Vec.hex_digit(lo) : U32) <> Vec.hex(tail)

def Vec.bytes(v: Vec) -> List<&2, U32>:
  Vec.hex(Vec.text(v))

# The bytes of a hex field, and of the "value" of a field.
# The bytes of a captured message under "hex" when hit holds, or rest.
def Vec.hex_if(+m: Vec, hit: Bool, rest: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match hit:
    case True{}:
      Some{Vec.bytes(Vec.field(m, "hex"))}
    case False{}:
      rest

def Vec.bytes_at(v: Vec, +key: String) -> List<&2, U32>:
  Vec.bytes(Vec.field(v, key))

def Vec.secret(+v: Vec, +key: String) -> List<&2, U32>:
  Vec.bytes(Vec.field(Vec.field(v, key), "value"))

# The captured message with the given "index", or VNull.
def Vec.message.pick(more: Unit -> Vec, found: Vec, hit: Bool) -> Vec:
  match hit:
    case True{}:
      found
    case False{}:
      more(Unit{})

def Vec.message(msgs: List<&2, Vec>, +index: Nat) -> Vec:
  match msgs:
    case Nil{}:
      VNull{}
    case +m <> rest:
      Vec.message.pick(u => Vec.message(rest, index), m, Nat.is_eq(Vec.nat(Vec.field(m, "index")), index))
