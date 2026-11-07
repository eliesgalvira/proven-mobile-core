import Base
import ../../bytes.bend as B
import ../../nas/ie.bend as I

# NAS fields and optional IEs as bytes, for the NAS tests.

def Nas.field_bytes(f: I.Field) -> List<&2, U32>:
  match f:
    case I.FByte{v}:
      [v]
    case I.FLv{I.LenBody{len, body}}:
      body
    case I.FLvE{I.LenBody{len, body}}:
      body

def Nas.field_of(mf: Maybe<&2, I.Field>) -> List<&2, U32>:
  match mf:
    case None{}:
      []
    case Some{f}:
      Nas.field_bytes(f)

def Nas.first_byte(bs: List<&2, U32>) -> U32:
  match bs:
    case Nil{}:
      0
    case b <> rest:
      b

def Nas.u32_is(r: B.Res(U32), v: U32) -> Bool:
  match r:
    case Done{+x}:
      U32.is_eq(x, v)
    case Fail{e}:
      False{}

def Nas.has_t1(ies: List<&2, I.Ie>, +byte: U32) -> Bool:
  match ies:
    case Nil{}:
      False{}
    case +ie <> rest:
      Bool.or(U32.is_eq(I.Ie.iei(ie), byte), Nas.has_t1(rest, byte))

def Nas.opt_pick(more: Unit -> List<&2, U32>, ie: I.Ie, hit: Bool) -> List<&2, U32>:
  match hit:
    case True{}:
      I.Ie.body(ie)
    case False{}:
      more(Unit{})

def Nas.opt_in(ies: List<&2, I.Ie>, +iei: U32) -> List<&2, U32>:
  match ies:
    case Nil{}:
      []
    case +ie <> rest:
      Nas.opt_pick(u => Nas.opt_in(rest, iei), ie, U32.is_eq(I.Ie.iei(ie), iei))
