import Base
import ../bytes.bend as B

# Proof helpers shared by kernel/proofs/*.bend.

# Refutations
# -----------

def Lift(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def Refute.bool(e: {False{} == True{} : Bool}) -> Empty:
  s = Equal.sym(Bool, False{}, True{}, e)
  %s : Lift(_)
  Unit{}

def Res.disc(-E: Data, -A: Data, r: Result<&2, &2, E, A>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{v}:
      Empty

def Refute.fail_done(-E: Data, -A: Data, err: E, v: A, e: {Fail{err} == Done{v} : Result<&2, &2, E, A>}) -> Empty:
  %e : Res.disc(E, A, _)
  Unit{}

# Projections, for injectivity of Done
# ------------------------------------

def Res.value(-E: Data, -A: Data, r: Result<&2, &2, E, A>, d: A) -> A:
  match r:
    case Fail{e}:
      d
    case Done{v}:
      v

def Read.value(-A: Data, r: B.Read(A), d: A) -> A:
  match r:
    case Fail{e}:
      d
    case Done{(v, rest)}:
      v

def Read.rest(-A: Data, r: B.Read(A), d: B.Bytes()) -> B.Bytes():
  match r:
    case Fail{e}:
      d
    case Done{(v, rest)}:
      rest
