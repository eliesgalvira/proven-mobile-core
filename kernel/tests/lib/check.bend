import Base

# Test harness: scripts/test-kernel.sh reads the PASS, FAIL and SKIP lines.

def Check.bytes_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yt:
      False{}
    case x <> xt Nil{}:
      False{}
    case x <> xt y <> yt:
      Bool.and(U32.is_eq(x, y), Check.bytes_eq(xt, yt))

def Check.report(name: String, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("PASS " ++ name)
    case False{}:
      IO.print("FAIL " ++ name)

def Check.skip(reason: String) -> IO(Unit):
  IO.print("SKIP " ++ reason)
