import Base

# A table keyed by U32: rows in insertion order, at most one per key.

def Table(-V: Data) -> Data:
  List<&2, Sigma<&2, &2, U32, _ => V>>

def Table.hit(-V: Data, v: V, later: Maybe<&2, V>, hit: Bool) -> Maybe<&2, V>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      later

def Table.get(-V: Data, +k: U32, t: Table(V)) -> Maybe<&2, V>:
  match t:
    case Nil{}:
      None{}
    case (key, v) <> more:
      Table.hit(V, v, Table.get(V, k, more), U32.is_eq(key, k))

def Table.present(-V: Data, m: Maybe<&2, V>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def Table.has(-V: Data, +k: U32, t: Table(V)) -> Bool:
  Table.present(V, Table.get(V, k, t))

def Table.set_row(-V: Data, k: U32, v: V, key: U32, w: V, more: Table(V), later: Table(V), hit: Bool) -> Table(V):
  match hit:
    case True{}:
      (k, v) <> more
    case False{}:
      (key, w) <> later

# Replaces the row with that key, or appends one.
def Table.set(-V: Data, +k: U32, +v: V, t: Table(V)) -> Table(V):
  match t:
    case Nil{}:
      [(k, v)]
    case (+key, w) <> +more:
      Table.set_row(V, k, v, key, w, more, Table.set(V, k, v, more), U32.is_eq(key, k))

# The row, kept or dropped, in front of the rest.
def Table.keep(-V: Data, key: U32, v: V, rest: Table(V), keep: Bool) -> Table(V):
  match keep:
    case True{}:
      (key, v) <> rest
    case False{}:
      rest
