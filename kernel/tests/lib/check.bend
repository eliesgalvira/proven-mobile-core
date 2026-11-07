import Base
import ../../bytes.bend as B

# Test harness: scripts/test-kernel.nu reads the PASS, FAIL and SKIP lines.

def Check.bytes_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  B.bytes_eq(xs, ys)

def Check.report(name: String, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("PASS " ++ name)
    case False{}:
      IO.print("FAIL " ++ name)

def Check.skip(reason: String) -> IO(Unit):
  IO.print("SKIP " ++ reason)

def Check.fails(-A: Data, r: B.Res(A)) -> Bool:
  Result.is_fail(&2, &2, B.Err, A, r)
