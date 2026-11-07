import Base
import ./bytes.bend as B

# PLMN identity (TS 24.008 §10.5.1.3, used by TS 24.501 and TS 38.413): three
# bytes, two digits each, low nibble first: MCC1|MCC2, MCC3|MNC3, MNC1|MNC2.
# A two-digit MNC has mnc3 = 15.

type Plmn is Data:
  Plmn{mcc1: U32, mcc2: U32, mcc3: U32, mnc1: U32, mnc2: U32, mnc3: U32}

def Plmn.digit(d: U32) -> Bool:
  U32.is_lt(d, 10)

def Plmn.valid(p: Plmn) -> Bool:
  match p:
    case Plmn{a, b, c, d, e, +f}:
      Bool.and(Plmn.digit(a), Bool.and(Plmn.digit(b), Bool.and(Plmn.digit(c), Bool.and(Plmn.digit(d), Bool.and(Plmn.digit(e), Bool.or(Plmn.digit(f), U32.is_eq(f, 15)))))))

def Plmn.mcc(p: Plmn) -> B.Digits():
  match p:
    case Plmn{a, b, c, d, e, f}:
      [a, b, c]

def Plmn.mnc.pick(d: U32, e: U32, f: U32, two: Bool) -> B.Digits():
  match two:
    case True{}:
      [d, e]
    case False{}:
      [d, e, f]

def Plmn.mnc(p: Plmn) -> B.Digits():
  match p:
    case Plmn{a, b, c, d, e, +f}:
      Plmn.mnc.pick(d, e, f, U32.is_eq(f, 15))

def Plmn.write(p: Plmn, rest: B.Bytes()) -> B.Bytes():
  match p:
    case Plmn{a, b, c, d, e, f}:
      B.write_nibbles(b, a, B.write_nibbles(f, c, B.write_nibbles(e, d, rest)))

def Plmn.check(p: Plmn, rest: B.Bytes(), ok: Bool) -> B.Read(Plmn):
  match ok:
    case True{}:
      Done{(p, rest)}
    case False{}:
      Fail{B.Invalid{1}}

def Plmn.r3(a: U32, b: U32, c: U32, f: U32, r: B.Read(B.Nibbles())) -> B.Read(Plmn):
  match r:
    case Fail{err}:
      Fail{err}
    case Done{((hi, lo), rest)}:
      +p = {Plmn{a, b, c, lo, hi, f} : Plmn}
      Plmn.check(p, rest, Plmn.valid(p))

def Plmn.r2(a: U32, b: U32, r: B.Read(B.Nibbles())) -> B.Read(Plmn):
  match r:
    case Fail{err}:
      Fail{err}
    case Done{((hi, lo), rest)}:
      Plmn.r3(a, b, lo, hi, B.nibbles(rest))

def Plmn.r1(r: B.Read(B.Nibbles())) -> B.Read(Plmn):
  match r:
    case Fail{err}:
      Fail{err}
    case Done{((hi, lo), rest)}:
      Plmn.r2(lo, hi, B.nibbles(rest))

def Plmn.read(bs: B.Bytes()) -> B.Read(Plmn):
  Plmn.r1(B.nibbles(bs))
