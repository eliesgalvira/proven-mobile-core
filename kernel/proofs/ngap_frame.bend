import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../LAWS.bend as L
import ./lib.bend as P
import ./aper.bend as PA
import ./canon.bend as PC

# Writers prepend, so appending after the rest is appending after the value.
def App.align(rem: Nat, +x: Ap.Bits(), +t: Ap.Bits()) -> {List.append(&2, Bool, Ap.Align.write(rem, x), t) == Ap.Align.write(rem, List.append(&2, Bool, x, t)) : Ap.Bits()}:
  match rem:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, List.append(&2, Bool, Ap.Align.write(p, x), t), Ap.Align.write(p, List.append(&2, Bool, x, t)), App.align(p, x, t))

def App.int(+n: Nat, +v: U32, rem: Nat, +x: Ap.Bits(), +t: Ap.Bits()) -> {List.append(&2, Bool, Ap.Int.write(n, v, rem, x), t) == Ap.Int.write(n, v, rem, List.append(&2, Bool, x, t)) : Ap.Bits()}:
  Equal.sym(Ap.Bits(), List.append(&2, Bool, Ap.U32.to_bits(n, v), List.append(&2, Bool, x, t)), List.append(&2, Bool, List.append(&2, Bool, Ap.U32.to_bits(n, v), x), t), PA.Bits.app_assoc(Ap.U32.to_bits(n, v), x, t))

def App.aint(+n: Nat, +v: U32, +rem: Nat, +x: Ap.Bits(), +t: Ap.Bits()) -> {List.append(&2, Bool, Ap.AInt.write(n, v, rem, x), t) == Ap.AInt.write(n, v, rem, List.append(&2, Bool, x, t)) : Ap.Bits()}:
  ai = App.int(n, v, 0n, x, t)
  %ai : {List.append(&2, Bool, Ap.AInt.write(n, v, rem, x), t) == Ap.Align.write(rem, _) : Ap.Bits()}
  App.align(rem, Ap.Int.write(n, v, 0n, x), t)

def App.octets(bs: B.Bytes(), +r: Nat, +x: Ap.Bits(), +t: Ap.Bits()) -> {List.append(&2, Bool, Ap.Octets.write(bs, r, x), t) == Ap.Octets.write(bs, r, List.append(&2, Bool, x, t)) : Ap.Bits()}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +more:
      ih = App.octets(more, r, x, t)
      %ih : {List.append(&2, Bool, Ap.Octets.write(b <> more, r, x), t) == List.append(&2, Bool, Ap.U32.to_bits(8n, b), _) : Ap.Bits()}
      Equal.sym(Ap.Bits(), List.append(&2, Bool, Ap.U32.to_bits(8n, b), List.append(&2, Bool, Ap.Octets.write(more, r, x), t)), List.append(&2, Bool, List.append(&2, Bool, Ap.U32.to_bits(8n, b), Ap.Octets.write(more, r, x)), t), PA.Bits.app_assoc(Ap.U32.to_bits(8n, b), Ap.Octets.write(more, r, x), t))

def App.len_body(+n: Nat, short: Bool, +x: Ap.Bits(), +t: Ap.Bits()) -> {List.append(&2, Bool, Ap.Len.body(n, short, x), t) == Ap.Len.body(n, short, List.append(&2, Bool, x, t)) : Ap.Bits()}:
  match short:
    case True{}:
      Equal.cong(Ap.Bits(), Ap.Bits(), l => False{} <> l, List.append(&2, Bool, List.append(&2, Bool, Ap.Nat.to_bits(7n, n), x), t), List.append(&2, Bool, Ap.Nat.to_bits(7n, n), List.append(&2, Bool, x, t)), Equal.sym(Ap.Bits(), List.append(&2, Bool, Ap.Nat.to_bits(7n, n), List.append(&2, Bool, x, t)), List.append(&2, Bool, List.append(&2, Bool, Ap.Nat.to_bits(7n, n), x), t), PA.Bits.app_assoc(Ap.Nat.to_bits(7n, n), x, t)))
    case False{}:
      Equal.cong(Ap.Bits(), Ap.Bits(), l => True{} <> False{} <> l, List.append(&2, Bool, List.append(&2, Bool, Ap.Nat.to_bits(14n, n), x), t), List.append(&2, Bool, Ap.Nat.to_bits(14n, n), List.append(&2, Bool, x, t)), Equal.sym(Ap.Bits(), List.append(&2, Bool, Ap.Nat.to_bits(14n, n), List.append(&2, Bool, x, t)), List.append(&2, Bool, List.append(&2, Bool, Ap.Nat.to_bits(14n, n), x), t), PA.Bits.app_assoc(Ap.Nat.to_bits(14n, n), x, t)))

def App.len(+n: Nat, +rem: Nat, +x: Ap.Bits(), +t: Ap.Bits()) -> {List.append(&2, Bool, Ap.Len.write(n, rem, x), t) == Ap.Len.write(n, rem, List.append(&2, Bool, x, t)) : Ap.Bits()}:
  lb = App.len_body(n, Nat.is_lt(n, 128n), x, t)
  %lb : {List.append(&2, Bool, Ap.Len.write(n, rem, x), t) == Ap.Align.write(rem, _) : Ap.Bits()}
  App.align(rem, Ap.Len.body(n, Nat.is_lt(n, 128n), x), t)

def App.open(+bs: B.Bytes(), +rem: Nat, +x: Ap.Bits(), +t: Ap.Bits()) -> {List.append(&2, Bool, Ap.Open.write(bs, rem, x), t) == Ap.Open.write(bs, rem, List.append(&2, Bool, x, t)) : Ap.Bits()}:
  ao = App.octets(bs, 0n, x, t)
  %ao : {List.append(&2, Bool, Ap.Open.write(bs, rem, x), t) == Ap.Len.write(List.length(&2, U32, bs), rem, _) : Ap.Bits()}
  App.len(List.length(&2, U32, bs), rem, Ap.Octets.write(bs, 0n, x), t)

def App.pdu(p: Fr.Pdu, +x: Ap.Bits(), +t: Ap.Bits()) -> {Fr.Pdu.bits(p, List.append(&2, Bool, x, t)) == List.append(&2, Bool, Fr.Pdu.bits(p, x), t) : Ap.Bits()}:
  match p:
    case Fr.Pdu{+kind, +code, +crit, +value}:
      a1 = App.open(value, 6n, x, t)
      %a1 : {Ap.Bit.write(False{}, 0n, Ap.Int.write(2n, kind, 7n, Ap.AInt.write(8n, code, 5n, Fr.Criticality.write(crit, 0n, _)))) == List.append(&2, Bool, Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, x), t) : Ap.Bits()}
      a2 = App.int(2n, crit, 0n, Ap.Open.write(value, 6n, x), t)
      %a2 : {Ap.Bit.write(False{}, 0n, Ap.Int.write(2n, kind, 7n, Ap.AInt.write(8n, code, 5n, _))) == List.append(&2, Bool, Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, x), t) : Ap.Bits()}
      a3 = App.aint(8n, code, 5n, Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, x)), t)
      %a3 : {Ap.Bit.write(False{}, 0n, Ap.Int.write(2n, kind, 7n, _)) == List.append(&2, Bool, Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, x), t) : Ap.Bits()}
      a4 = App.int(2n, kind, 7n, Ap.AInt.write(8n, code, 5n, Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, x))), t)
      %a4 : {Ap.Bit.write(False{}, 0n, _) == List.append(&2, Bool, Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, x), t) : Ap.Bits()}
      {==}

# Protocol IE fields
# ------------------

def Ie.rt(+id: U32, +crit: U32, +value: B.Bytes(), +rem: Nat, +rest: Ap.Bits(), +v: {Fr.Ie.valid(Fr.Ie{id, crit, value}) == True{} : Bool}) -> {Fr.Ie.read(Ap.Cur{rem, Fr.Ie.write(Fr.Ie{id, crit, value}, rem, rest)}) == Done{(Fr.Ie{id, crit, value}, Ap.Cur{0n, rest})} : Ap.Rd(Fr.Ie)}:
  vi = P.Bool.and_true_l(Ap.Int.valid(16n, 65535, id), Bool.and(Fr.Criticality.valid(crit), Ap.Open.valid(value)), v)
  +v2 = P.Bool.and_true_r(Ap.Int.valid(16n, 65535, id), Bool.and(Fr.Criticality.valid(crit), Ap.Open.valid(value)), v)
  r1 = Equal.sym(Ap.Rd(U32), Ap.AInt.read(16n, 65535, Ap.Cur{rem, Ap.AInt.write(16n, id, rem, Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, rest)))}), Done{(id, Ap.Cur{Ap.AInt.after(16n, rem), Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, rest))})}, L.aper.aint.roundtrip(16n, 65535, id, rem, Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, rest)), vi))
  %r1 : {Fr.Ie.r_id(_) == Done{(Fr.Ie{id, crit, value}, Ap.Cur{0n, rest})} : Ap.Rd(Fr.Ie)}
  r2 = Equal.sym(Ap.Rd(U32), Ap.Int.read(2n, 2, Ap.Cur{0n, Ap.Int.write(2n, crit, 0n, Ap.Open.write(value, 6n, rest))}), Done{(crit, Ap.Cur{Ap.Int.after(2n, 0n), Ap.Open.write(value, 6n, rest)})}, L.aper.int.roundtrip(2n, 2, crit, 0n, Ap.Open.write(value, 6n, rest), P.Bool.and_true_l(Fr.Criticality.valid(crit), Ap.Open.valid(value), v2)))
  %r2 : {Fr.Ie.r_crit(id, _) == Done{(Fr.Ie{id, crit, value}, Ap.Cur{0n, rest})} : Ap.Rd(Fr.Ie)}
  r3 = Equal.sym(Ap.Rd(B.Bytes()), Ap.Open.read(Ap.Cur{6n, Ap.Open.write(value, 6n, rest)}), Done{(value, Ap.Cur{0n, rest})}, L.aper.open.roundtrip(value, 6n, rest, P.Bool.and_true_r(Fr.Criticality.valid(crit), Ap.Open.valid(value), v2)))
  %r3 : {Fr.Ie.r_value(id, crit, _) == Done{(Fr.Ie{id, crit, value}, Ap.Cur{0n, rest})} : Ap.Rd(Fr.Ie)}
  {==}

def L.ngap.ie.roundtrip(ie, rem, rest, v):
  match ie:
    case Fr.Ie{id, crit, value}:
      Ie.rt(id, crit, value, rem, rest, v)

def Ie.dv.value(+id: U32, +crit: U32, +c2: Ap.Cur, ro: Ap.Rd(B.Bytes()), +ero: {Ap.Open.read(c2) == ro : Ap.Rd(B.Bytes())}, +ie: Fr.Ie, +c3: Ap.Cur, +e: {Fr.Ie.r_value(id, crit, ro) == Done{(ie, c3)} : Ap.Rd(Fr.Ie)}, vi: {Ap.Int.valid(16n, 65535, id) == True{} : Bool}, vc: {Fr.Criticality.valid(crit) == True{} : Bool}) -> {Fr.Ie.valid(ie) == True{} : Bool}:
  match ro:
    case Fail{err}:
      PA.Rd.absurd(Fr.Ie, {Fr.Ie.valid(ie) == True{} : Bool}, err, ie, c3, e)
    case Done{(+value, +c)}:
      ev = Equal.cong(Ap.Rd(Fr.Ie), Fr.Ie, y => PA.Rd.value(Fr.Ie, y, ie), Done{(Fr.Ie{id, crit, value}, c)}, Done{(ie, c3)}, e)
      %ev : {Fr.Ie.valid(_) == True{} : Bool}
      P.Bool.and_intro(Ap.Int.valid(16n, 65535, id), Bool.and(Fr.Criticality.valid(crit), Ap.Open.valid(value)), vi, P.Bool.and_intro(Fr.Criticality.valid(crit), Ap.Open.valid(value), vc, L.aper.open.decode_valid(c2, value, c, ero)))

def Ie.dv.crit(+id: U32, +c1: Ap.Cur, rc: Ap.Rd(U32), +erc: {Fr.Criticality.read(c1) == rc : Ap.Rd(U32)}, +ie: Fr.Ie, +c3: Ap.Cur, +e: {Fr.Ie.r_crit(id, rc) == Done{(ie, c3)} : Ap.Rd(Fr.Ie)}, vi: {Ap.Int.valid(16n, 65535, id) == True{} : Bool}) -> {Fr.Ie.valid(ie) == True{} : Bool}:
  match rc:
    case Fail{err}:
      PA.Rd.absurd(Fr.Ie, {Fr.Ie.valid(ie) == True{} : Bool}, err, ie, c3, e)
    case Done{(+crit, +c2)}:
      Ie.dv.value(id, crit, c2, Ap.Open.read(c2), {==}, ie, c3, e, vi, L.aper.int.decode_valid(2n, 2, c1, crit, c2, erc))

def Ie.dv(+c: Ap.Cur, ri: Ap.Rd(U32), +eri: {Ap.AInt.read(16n, 65535, c) == ri : Ap.Rd(U32)}, +ie: Fr.Ie, +c3: Ap.Cur, +e: {Fr.Ie.r_id(ri) == Done{(ie, c3)} : Ap.Rd(Fr.Ie)}) -> {Fr.Ie.valid(ie) == True{} : Bool}:
  match ri:
    case Fail{err}:
      PA.Rd.absurd(Fr.Ie, {Fr.Ie.valid(ie) == True{} : Bool}, err, ie, c3, e)
    case Done{(+id, +c1)}:
      Ie.dv.crit(id, c1, Fr.Criticality.read(c1), {==}, ie, c3, e, L.aper.aint.decode_valid(16n, 65535, c, id, c1, eri))

def L.ngap.ie.decode_valid(c, ie, c2, e):
  Ie.dv(c, Ap.AInt.read(16n, 65535, c), {==}, ie, c2, e)

# Containers
# ----------

def Ies.items_rt(ies: List<&2, Fr.Ie>, +rest: Ap.Bits(), +av: {Fr.Ies.all_valid(ies) == True{} : Bool}) -> {Done{(ies, Ap.Cur{0n, rest})} == Fr.Ies.items(List.length(&2, Fr.Ie, ies), Ap.Cur{0n, Fr.Ies.items_write(ies, 0n, rest)}) : Ap.Rd(List<&2, Fr.Ie>)}:
  match ies:
    case Nil{}:
      {==}
    case +ie <> +more:
      ir = Equal.sym(Ap.Rd(Fr.Ie), Fr.Ie.read(Ap.Cur{0n, Fr.Ie.write(ie, 0n, Fr.Ies.items_write(more, 0n, rest))}), Done{(ie, Ap.Cur{0n, Fr.Ies.items_write(more, 0n, rest)})}, L.ngap.ie.roundtrip(ie, 0n, Fr.Ies.items_write(more, 0n, rest), P.Bool.and_true_l(Fr.Ie.valid(ie), Fr.Ies.all_valid(more), av)))
      %ir : {Done{(ie <> more, Ap.Cur{0n, rest})} == Fr.Ies.next(_, c2 => Fr.Ies.items(List.length(&2, Fr.Ie, more), c2)) : Ap.Rd(List<&2, Fr.Ie>)}
      ih = Ies.items_rt(more, rest, P.Bool.and_true_r(Fr.Ie.valid(ie), Fr.Ies.all_valid(more), av))
      %ih : {Done{(ie <> more, Ap.Cur{0n, rest})} == Fr.Ies.cons(ie, _) : Ap.Rd(List<&2, Fr.Ie>)}
      {==}

def Ies.rt(+lo: Nat, +diff: Nat, +ies: List<&2, Fr.Ie>, +rem: Nat, +rest: Ap.Bits(), sv: {Ap.Size.valid(lo, diff, List.length(&2, Fr.Ie, ies)) == True{} : Bool}, av: {Fr.Ies.all_valid(ies) == True{} : Bool}, w: {Nat.is_lt(diff, Ap.Nat.pow2(16n)) == True{} : Bool}) -> {Fr.Ies.count(Ap.Size.read(True{}, 16n, lo, diff, Ap.Cur{rem, Ap.Size.write(True{}, 16n, lo, List.length(&2, Fr.Ie, ies), rem, Fr.Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), rest))})) == Done{(ies, Ap.Cur{0n, rest})} : Ap.Rd(List<&2, Fr.Ie>)}:
  sr = Equal.sym(Ap.Rd(Nat), Ap.Size.read(True{}, 16n, lo, diff, Ap.Cur{rem, Ap.Size.write(True{}, 16n, lo, List.length(&2, Fr.Ie, ies), rem, Fr.Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), rest))}), Done{(List.length(&2, Fr.Ie, ies), Ap.Cur{Ap.Size.after(True{}, 16n, rem), Fr.Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), rest)})}, L.aper.size.roundtrip(True{}, 16n, lo, diff, List.length(&2, Fr.Ie, ies), rem, Fr.Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), rest), sv, w))
  %sr : {Fr.Ies.count(_) == Done{(ies, Ap.Cur{0n, rest})} : Ap.Rd(List<&2, Fr.Ie>)}
  Equal.sym(Ap.Rd(List<&2, Fr.Ie>), Done{(ies, Ap.Cur{0n, rest})}, Fr.Ies.items(List.length(&2, Fr.Ie, ies), Ap.Cur{0n, Fr.Ies.items_write(ies, 0n, rest)}), Ies.items_rt(ies, rest, av))

def L.ngap.ies.roundtrip(ies, rem, rest, v):
  Ies.rt(0n, 65535n, ies, rem, rest, P.Bool.and_true_l(Ap.Size.valid(0n, 65535n, List.length(&2, Fr.Ie, ies)), Fr.Ies.all_valid(ies), v), P.Bool.and_true_r(Ap.Size.valid(0n, 65535n, List.length(&2, Fr.Ie, ies)), Fr.Ies.all_valid(ies), v), {==})

def L.ngap.exts.roundtrip(ies, rem, rest, v):
  Ies.rt(1n, 65534n, ies, rem, rest, P.Bool.and_true_l(Ap.Size.valid(1n, 65534n, List.length(&2, Fr.Ie, ies)), Fr.Ies.all_valid(ies), v), P.Bool.and_true_r(Ap.Size.valid(1n, 65534n, List.length(&2, Fr.Ie, ies)), Fr.Ies.all_valid(ies), v), {==})

def Ies.Spec(ies: List<&2, Fr.Ie>, n: Nat) -> Type:
  {Fr.Ies.all_valid(ies) == True{} : Bool} & {List.length(&2, Fr.Ie, ies) == n : Nat}

def Ies.spec.finish(+p: Nat, +ie: Fr.Ie, +ies2: List<&2, Fr.Ie>, vi: {Fr.Ie.valid(ie) == True{} : Bool}, s: Ies.Spec(ies2, p)) -> Ies.Spec(ie <> ies2, 1n+p):
  (av, len) = s
  (P.Bool.and_intro(Fr.Ie.valid(ie), Fr.Ies.all_valid(ies2), vi, av), Equal.cong(Nat, Nat, m => 1n+m, List.length(&2, Fr.Ie, ies2), p, len))

def Ies.spec.cons(+p: Nat, +ie: Fr.Ie, +c3: Ap.Cur, rl: Ap.Rd(List<&2, Fr.Ie>), +erl: {Fr.Ies.items(p, c3) == rl : Ap.Rd(List<&2, Fr.Ie>)}, ih: @c4: Ap.Cur -> @ies2: List<&2, Fr.Ie> -> @c5: Ap.Cur -> {Fr.Ies.items(p, c4) == Done{(ies2, c5)} : Ap.Rd(List<&2, Fr.Ie>)} -> Ies.Spec(ies2, p), +ies: List<&2, Fr.Ie>, +c2: Ap.Cur, +e: {Fr.Ies.cons(ie, rl) == Done{(ies, c2)} : Ap.Rd(List<&2, Fr.Ie>)}, vi: {Fr.Ie.valid(ie) == True{} : Bool}) -> Ies.Spec(ies, 1n+p):
  match rl:
    case Fail{err}:
      PA.Rd.absurd(List<&2, Fr.Ie>, Ies.Spec(ies, 1n+p), err, ies, c2, e)
    case Done{(+ies2, +c5)}:
      ev = Equal.cong(Ap.Rd(List<&2, Fr.Ie>), List<&2, Fr.Ie>, y => PA.Rd.value(List<&2, Fr.Ie>, y, ies), Done{(ie <> ies2, c5)}, Done{(ies, c2)}, e)
      %ev : Ies.Spec(_, 1n+p)
      Ies.spec.finish(p, ie, ies2, vi, ih(c3, ies2, c5, erl))

def Ies.spec.step(+p: Nat, +c: Ap.Cur, ri: Ap.Rd(Fr.Ie), +eri: {Fr.Ie.read(c) == ri : Ap.Rd(Fr.Ie)}, ih: @c4: Ap.Cur -> @ies2: List<&2, Fr.Ie> -> @c5: Ap.Cur -> {Fr.Ies.items(p, c4) == Done{(ies2, c5)} : Ap.Rd(List<&2, Fr.Ie>)} -> Ies.Spec(ies2, p), +ies: List<&2, Fr.Ie>, +c2: Ap.Cur, +e: {Fr.Ies.next(ri, c4 => Fr.Ies.items(p, c4)) == Done{(ies, c2)} : Ap.Rd(List<&2, Fr.Ie>)}) -> Ies.Spec(ies, 1n+p):
  match ri:
    case Fail{err}:
      PA.Rd.absurd(List<&2, Fr.Ie>, Ies.Spec(ies, 1n+p), err, ies, c2, e)
    case Done{(+ie, +c3)}:
      Ies.spec.cons(p, ie, c3, Fr.Ies.items(p, c3), {==}, ih, ies, c2, e, L.ngap.ie.decode_valid(c, ie, c3, eri))

def Ies.spec(n: Nat, +c: Ap.Cur, +ies: List<&2, Fr.Ie>, +c2: Ap.Cur, +e: {Fr.Ies.items(n, c) == Done{(ies, c2)} : Ap.Rd(List<&2, Fr.Ie>)}) -> Ies.Spec(ies, n):
  match n:
    case 0n:
      ev = Equal.cong(Ap.Rd(List<&2, Fr.Ie>), List<&2, Fr.Ie>, y => PA.Rd.value(List<&2, Fr.Ie>, y, ies), Done{([], c)}, Done{(ies, c2)}, e)
      %ev : Ies.Spec(_, 0n)
      ({==}, {==})
    case 1n++p:
      Ies.spec.step(p, c, Fr.Ie.read(c), {==}, c4 => ies2 => c5 => e2 => Ies.spec(p, c4, ies2, c5, e2), ies, c2, e)

def Ies.dv.finish(+lo: Nat, +diff: Nat, +n: Nat, +ies: List<&2, Fr.Ie>, sv: {Ap.Size.valid(lo, diff, n) == True{} : Bool}, s: Ies.Spec(ies, n)) -> {Bool.and(Ap.Size.valid(lo, diff, List.length(&2, Fr.Ie, ies)), Fr.Ies.all_valid(ies)) == True{} : Bool}:
  (av, len) = s
  slen = Equal.sym(Nat, List.length(&2, Fr.Ie, ies), n, len)
  P.Bool.and_intro(Ap.Size.valid(lo, diff, List.length(&2, Fr.Ie, ies)), Fr.Ies.all_valid(ies), (%slen : {Ap.Size.valid(lo, diff, _) == True{} : Bool}; sv), av)

def Ies.dv(+lo: Nat, +diff: Nat, +c0: Ap.Cur, rn: Ap.Rd(Nat), +ern: {Ap.Size.read(True{}, 16n, lo, diff, c0) == rn : Ap.Rd(Nat)}, +ies: List<&2, Fr.Ie>, +c2: Ap.Cur, +e: {Fr.Ies.count(rn) == Done{(ies, c2)} : Ap.Rd(List<&2, Fr.Ie>)}) -> {Bool.and(Ap.Size.valid(lo, diff, List.length(&2, Fr.Ie, ies)), Fr.Ies.all_valid(ies)) == True{} : Bool}:
  match rn:
    case Fail{err}:
      PA.Rd.absurd(List<&2, Fr.Ie>, {Bool.and(Ap.Size.valid(lo, diff, List.length(&2, Fr.Ie, ies)), Fr.Ies.all_valid(ies)) == True{} : Bool}, err, ies, c2, e)
    case Done{(+n, +c)}:
      Ies.dv.finish(lo, diff, n, ies, L.aper.size.decode_valid(True{}, 16n, lo, diff, c0, n, c, ern), Ies.spec(n, c, ies, c2, e))

def L.ngap.ies.decode_valid(c, ies, c2, e):
  Ies.dv(0n, 65535n, c, Ap.Size.read(True{}, 16n, 0n, 65535n, c), {==}, ies, c2, e)

def L.ngap.exts.decode_valid(c, ies, c2, e):
  Ies.dv(1n, 65534n, c, Ap.Size.read(True{}, 16n, 1n, 65534n, c), {==}, ies, c2, e)

# The PDU
# -------

def Pdu.rt.bits(+kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +tail: Ap.Bits(), tz: {Ap.Tail.zero(tail) == True{} : Bool}, vk: {Ap.Int.valid(2n, 2, kind) == True{} : Bool}, vc: {Ap.Int.valid(8n, 255, code) == True{} : Bool}, vr: {Fr.Criticality.valid(crit) == True{} : Bool}, vo: {Ap.Open.valid(value) == True{} : Bool}) -> {Fr.Pdu.r_ext(Ap.Bit.read(Ap.Cur{0n, Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, tail)})) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}:
  r1 = Equal.sym(Ap.Rd(U32), Ap.Int.read(2n, 2, Ap.Cur{7n, Ap.Int.write(2n, kind, 7n, Ap.AInt.write(8n, code, 5n, Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, tail))))}), Done{(kind, Ap.Cur{Ap.Int.after(2n, 7n), Ap.AInt.write(8n, code, 5n, Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, tail)))})}, L.aper.int.roundtrip(2n, 2, kind, 7n, Ap.AInt.write(8n, code, 5n, Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, tail))), vk))
  %r1 : {Fr.Pdu.r_kind(_) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  r2 = Equal.sym(Ap.Rd(U32), Ap.AInt.read(8n, 255, Ap.Cur{5n, Ap.AInt.write(8n, code, 5n, Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, tail)))}), Done{(code, Ap.Cur{Ap.AInt.after(8n, 5n), Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, tail))})}, L.aper.aint.roundtrip(8n, 255, code, 5n, Fr.Criticality.write(crit, 0n, Ap.Open.write(value, 6n, tail)), vc))
  %r2 : {Fr.Pdu.r_code(kind, _) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  r3 = Equal.sym(Ap.Rd(U32), Ap.Int.read(2n, 2, Ap.Cur{0n, Ap.Int.write(2n, crit, 0n, Ap.Open.write(value, 6n, tail))}), Done{(crit, Ap.Cur{Ap.Int.after(2n, 0n), Ap.Open.write(value, 6n, tail)})}, L.aper.int.roundtrip(2n, 2, crit, 0n, Ap.Open.write(value, 6n, tail), vr))
  %r3 : {Fr.Pdu.r_crit(kind, code, _) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  r4 = Equal.sym(Ap.Rd(B.Bytes()), Ap.Open.read(Ap.Cur{6n, Ap.Open.write(value, 6n, tail)}), Done{(value, Ap.Cur{0n, tail})}, L.aper.open.roundtrip(value, 6n, tail, vo))
  %r4 : {Fr.Pdu.r_value(kind, code, crit, _) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  stz = Equal.sym(Bool, Ap.Tail.zero(tail), True{}, tz)
  %stz : {Fr.Pdu.tail(Fr.Pdu{kind, code, crit, value}, _) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  {==}

def Pdu.rt(+kind: U32, +code: U32, +crit: U32, +value: B.Bytes(), +v: {Fr.Pdu.valid(Fr.Pdu{kind, code, crit, value}) == True{} : Bool}) -> {Fr.Pdu.read(Fr.Pdu.write(Fr.Pdu{kind, code, crit, value})) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}:
  vk = P.Bool.and_true_l(Ap.Int.valid(2n, 2, kind), Bool.and(Ap.Int.valid(8n, 255, code), Bool.and(Fr.Criticality.valid(crit), Ap.Open.valid(value))), v)
  +v2 = P.Bool.and_true_r(Ap.Int.valid(2n, 2, kind), Bool.and(Ap.Int.valid(8n, 255, code), Bool.and(Fr.Criticality.valid(crit), Ap.Open.valid(value))), v)
  vc = P.Bool.and_true_l(Ap.Int.valid(8n, 255, code), Bool.and(Fr.Criticality.valid(crit), Ap.Open.valid(value)), v2)
  +v3 = P.Bool.and_true_r(Ap.Int.valid(8n, 255, code), Bool.and(Fr.Criticality.valid(crit), Ap.Open.valid(value)), v2)
  vr = P.Bool.and_true_l(Fr.Criticality.valid(crit), Ap.Open.valid(value), v3)
  vo = P.Bool.and_true_r(Fr.Criticality.valid(crit), Ap.Open.valid(value), v3)
  pp = Equal.sym(Ap.Bits(), Ap.unpack(Ap.pack(Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, []))), List.append(&2, Bool, Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, []), Ap.padding(Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, []))), L.aper.pack.padding(Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, [])))
  %pp : {Fr.Pdu.r_ext(Ap.Bit.read(Ap.Cur{0n, _})) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  ap = App.pdu(Fr.Pdu{kind, code, crit, value}, [], Ap.padding(Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, [])))
  %ap : {Fr.Pdu.r_ext(Ap.Bit.read(Ap.Cur{0n, _})) == Done{Fr.Pdu{kind, code, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}
  Pdu.rt.bits(kind, code, crit, value, Ap.padding(Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, [])), L.aper.pack.padding_zero(Fr.Pdu.bits(Fr.Pdu{kind, code, crit, value}, [])), vk, vc, vr, vo)

def L.ngap.pdu.roundtrip(p, v):
  match p:
    case Fr.Pdu{kind, code, crit, value}:
      Pdu.rt(kind, code, crit, value, v)

def Pdu.absurd(-G: Type, err: B.Err, p: Fr.Pdu, e: {Fail{err} == Done{p} : Result<&2, &2, B.Err, Fr.Pdu>}) -> G:
  Empty.absurd(G, P.Refute.fail_done(B.Err, Fr.Pdu, err, p, e))

def Pdu.dv.tail(+q: Fr.Pdu, ok: Bool, +p: Fr.Pdu, +e: {Fr.Pdu.tail(q, ok) == Done{p} : Result<&2, &2, B.Err, Fr.Pdu>}, vq: {Fr.Pdu.valid(q) == True{} : Bool}) -> {Fr.Pdu.valid(p) == True{} : Bool}:
  match ok:
    case False{}:
      Pdu.absurd({Fr.Pdu.valid(p) == True{} : Bool}, B.Invalid{3}, p, e)
    case True{}:
      ev = Equal.cong(Result<&2, &2, B.Err, Fr.Pdu>, Fr.Pdu, y => P.Res.value(B.Err, Fr.Pdu, y, p), Done{q}, Done{p}, e)
      %ev : {Fr.Pdu.valid(_) == True{} : Bool}
      vq

def Pdu.dv.value(+kind: U32, +code: U32, +crit: U32, +c3: Ap.Cur, ro: Ap.Rd(B.Bytes()), +ero: {Ap.Open.read(c3) == ro : Ap.Rd(B.Bytes())}, +p: Fr.Pdu, +e: {Fr.Pdu.r_value(kind, code, crit, ro) == Done{p} : Result<&2, &2, B.Err, Fr.Pdu>}, vk: {Ap.Int.valid(2n, 2, kind) == True{} : Bool}, vc: {Ap.Int.valid(8n, 255, code) == True{} : Bool}, vr: {Fr.Criticality.valid(crit) == True{} : Bool}) -> {Fr.Pdu.valid(p) == True{} : Bool}:
  match ro:
    case Fail{err}:
      Pdu.absurd({Fr.Pdu.valid(p) == True{} : Bool}, err, p, e)
    case Done{(+value, c)}:
      match c:
        case Ap.Cur{rem, +bits}:
          Pdu.dv.tail(Fr.Pdu{kind, code, crit, value}, Ap.Tail.zero(bits), p, e, P.Bool.and_intro(Ap.Int.valid(2n, 2, kind), Bool.and(Ap.Int.valid(8n, 255, code), Bool.and(Fr.Criticality.valid(crit), Ap.Open.valid(value))), vk, P.Bool.and_intro(Ap.Int.valid(8n, 255, code), Bool.and(Fr.Criticality.valid(crit), Ap.Open.valid(value)), vc, P.Bool.and_intro(Fr.Criticality.valid(crit), Ap.Open.valid(value), vr, L.aper.open.decode_valid(c3, value, Ap.Cur{rem, bits}, ero)))))

def Pdu.dv.crit(+kind: U32, +code: U32, +c2: Ap.Cur, rc: Ap.Rd(U32), +erc: {Fr.Criticality.read(c2) == rc : Ap.Rd(U32)}, +p: Fr.Pdu, +e: {Fr.Pdu.r_crit(kind, code, rc) == Done{p} : Result<&2, &2, B.Err, Fr.Pdu>}, vk: {Ap.Int.valid(2n, 2, kind) == True{} : Bool}, vc: {Ap.Int.valid(8n, 255, code) == True{} : Bool}) -> {Fr.Pdu.valid(p) == True{} : Bool}:
  match rc:
    case Fail{err}:
      Pdu.absurd({Fr.Pdu.valid(p) == True{} : Bool}, err, p, e)
    case Done{(+crit, +c3)}:
      Pdu.dv.value(kind, code, crit, c3, Ap.Open.read(c3), {==}, p, e, vk, vc, L.aper.int.decode_valid(2n, 2, c2, crit, c3, erc))

def Pdu.dv.code(+kind: U32, +c1: Ap.Cur, rc: Ap.Rd(U32), +erc: {Ap.AInt.read(8n, 255, c1) == rc : Ap.Rd(U32)}, +p: Fr.Pdu, +e: {Fr.Pdu.r_code(kind, rc) == Done{p} : Result<&2, &2, B.Err, Fr.Pdu>}, vk: {Ap.Int.valid(2n, 2, kind) == True{} : Bool}) -> {Fr.Pdu.valid(p) == True{} : Bool}:
  match rc:
    case Fail{err}:
      Pdu.absurd({Fr.Pdu.valid(p) == True{} : Bool}, err, p, e)
    case Done{(+code, +c2)}:
      Pdu.dv.crit(kind, code, c2, Fr.Criticality.read(c2), {==}, p, e, vk, L.aper.aint.decode_valid(8n, 255, c1, code, c2, erc))

def Pdu.dv.kind(+c0: Ap.Cur, rk: Ap.Rd(U32), +erk: {Ap.Int.read(2n, 2, c0) == rk : Ap.Rd(U32)}, +p: Fr.Pdu, +e: {Fr.Pdu.r_kind(rk) == Done{p} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {Fr.Pdu.valid(p) == True{} : Bool}:
  match rk:
    case Fail{err}:
      Pdu.absurd({Fr.Pdu.valid(p) == True{} : Bool}, err, p, e)
    case Done{(+kind, +c1)}:
      Pdu.dv.code(kind, c1, Ap.AInt.read(8n, 255, c1), {==}, p, e, L.aper.int.decode_valid(2n, 2, c0, kind, c1, erk))

def Pdu.dv(rb: Ap.Rd(Bool), +p: Fr.Pdu, +e: {Fr.Pdu.r_ext(rb) == Done{p} : Result<&2, &2, B.Err, Fr.Pdu>}) -> {Fr.Pdu.valid(p) == True{} : Bool}:
  match rb:
    case Fail{err}:
      Pdu.absurd({Fr.Pdu.valid(p) == True{} : Bool}, err, p, e)
    case Done{(ext, +c)}:
      match ext:
        case True{}:
          Pdu.absurd({Fr.Pdu.valid(p) == True{} : Bool}, B.Unsupported{0}, p, e)
        case False{}:
          Pdu.dv.kind(c, Ap.Int.read(2n, 2, c), {==}, p, e)

def L.ngap.pdu.decode_valid(bs, p, e):
  Pdu.dv(Ap.Bit.read(Ap.Cur{0n, Ap.unpack(bs)}), p, e)

# Canonical decoding (the suffix laws of the generated types rest on these)
# -----------------------------------------------------------------------

def Ie.sx.go(+rem: Nat, +bits: Ap.Bits(), +id: U32, +r1: Nat, +b1: Ap.Bits(), +crit: U32, +r2: Nat, +b2: Ap.Bits(), +value: B.Bytes(), +r3: Nat, +b3: Ap.Bits(), +ie: Fr.Ie, +rem2: Nat, +bits2: Ap.Bits(), +e: {Done{(Fr.Ie{id, crit, value}, Ap.Cur{r3, b3})} == Done{(ie, Ap.Cur{rem2, bits2})} : Ap.Rd(Fr.Ie)}, sa: PC.Canon(bits, Ap.AInt.write(16n, id, rem, b1), r1, Ap.AInt.after(16n, rem)), sc: PC.Canon(b1, Ap.Int.write(2n, crit, r1, b2), r2, Ap.Int.after(2n, r1)), so: PC.Canon(b2, Ap.Open.write(value, r2, b3), r3, 0n)) -> PC.Canon(bits, Fr.Ie.write(ie, rem, bits2), rem2, Fr.Ie.after(rem)):
  (a1, +a2) = sa
  (c1e, c2e) = sc
  (o1, o2) = so
  ev = Equal.cong(Ap.Rd(Fr.Ie), Fr.Ie, x => PA.Rd.value(Fr.Ie, x, ie), Done{(Fr.Ie{id, crit, value}, Ap.Cur{r3, b3})}, Done{(ie, Ap.Cur{rem2, bits2})}, e)
  +ec = Equal.cong(Ap.Rd(Fr.Ie), Ap.Cur, x => PA.Rd.cur(Fr.Ie, x, Ap.Cur{rem2, bits2}), Done{(Fr.Ie{id, crit, value}, Ap.Cur{r3, b3})}, Done{(ie, Ap.Cur{rem2, bits2})}, e)
  eb = Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  er = Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r3, b3}, Ap.Cur{rem2, bits2}, ec)
  %ev : PC.Canon(bits, Fr.Ie.write(_, rem, bits2), rem2, Fr.Ie.after(rem))
  ((%a2 : {bits == Ap.AInt.write(16n, id, rem, Ap.Int.write(2n, crit, _, Ap.Open.write(value, Ap.Rem.add(2n, _), bits2))) : Ap.Bits()}; (%c2e : {bits == Ap.AInt.write(16n, id, rem, Ap.Int.write(2n, crit, r1, Ap.Open.write(value, _, bits2))) : Ap.Bits()}; (%eb : {bits == Ap.AInt.write(16n, id, rem, Ap.Int.write(2n, crit, r1, Ap.Open.write(value, r2, _))) : Ap.Bits()}; (%o1 : {bits == Ap.AInt.write(16n, id, rem, Ap.Int.write(2n, crit, r1, _)) : Ap.Bits()}; (%c1e : {bits == Ap.AInt.write(16n, id, rem, _) : Ap.Bits()}; a1))))), (%er : {_ == 0n : Nat}; o2))

def Ie.sx.value(+rem: Nat, +bits: Ap.Bits(), +id: U32, +r1: Nat, +b1: Ap.Bits(), +crit: U32, +r2: Nat, +b2: Ap.Bits(), ro: Ap.Rd(B.Bytes()), +ero: {Ap.Open.read(Ap.Cur{r2, b2}) == ro : Ap.Rd(B.Bytes())}, +ie: Fr.Ie, +rem2: Nat, +bits2: Ap.Bits(), +e: {Fr.Ie.r_value(id, crit, ro) == Done{(ie, Ap.Cur{rem2, bits2})} : Ap.Rd(Fr.Ie)}, sa: PC.Canon(bits, Ap.AInt.write(16n, id, rem, b1), r1, Ap.AInt.after(16n, rem)), sc: PC.Canon(b1, Ap.Int.write(2n, crit, r1, b2), r2, Ap.Int.after(2n, r1))) -> PC.Canon(bits, Fr.Ie.write(ie, rem, bits2), rem2, Fr.Ie.after(rem)):
  match ro:
    case Fail{err}:
      PA.Rd.absurd(Fr.Ie, PC.Canon(bits, Fr.Ie.write(ie, rem, bits2), rem2, Fr.Ie.after(rem)), err, ie, Ap.Cur{rem2, bits2}, e)
    case Done{(+value, c3)}:
      match c3:
        case Ap.Cur{+r3, +b3}:
          Ie.sx.go(rem, bits, id, r1, b1, crit, r2, b2, value, r3, b3, ie, rem2, bits2, e, sa, sc, PC.Open.sx(r2, b2, value, r3, b3, ero))

def Ie.sx.crit(+rem: Nat, +bits: Ap.Bits(), +id: U32, +r1: Nat, +b1: Ap.Bits(), rc: Ap.Rd(U32), +erc: {Fr.Criticality.read(Ap.Cur{r1, b1}) == rc : Ap.Rd(U32)}, +ie: Fr.Ie, +rem2: Nat, +bits2: Ap.Bits(), +e: {Fr.Ie.r_crit(id, rc) == Done{(ie, Ap.Cur{rem2, bits2})} : Ap.Rd(Fr.Ie)}, sa: PC.Canon(bits, Ap.AInt.write(16n, id, rem, b1), r1, Ap.AInt.after(16n, rem))) -> PC.Canon(bits, Fr.Ie.write(ie, rem, bits2), rem2, Fr.Ie.after(rem)):
  match rc:
    case Fail{err}:
      PA.Rd.absurd(Fr.Ie, PC.Canon(bits, Fr.Ie.write(ie, rem, bits2), rem2, Fr.Ie.after(rem)), err, ie, Ap.Cur{rem2, bits2}, e)
    case Done{(+crit, c2)}:
      match c2:
        case Ap.Cur{+r2, +b2}:
          Ie.sx.value(rem, bits, id, r1, b1, crit, r2, b2, Ap.Open.read(Ap.Cur{r2, b2}), {==}, ie, rem2, bits2, e, sa, PC.Int.sx(2n, 2, r1, b1, crit, r2, b2, erc, {==}))

def Ie.sx.id(+rem: Nat, +bits: Ap.Bits(), ri: Ap.Rd(U32), +eri: {Ap.AInt.read(16n, 65535, Ap.Cur{rem, bits}) == ri : Ap.Rd(U32)}, +ie: Fr.Ie, +rem2: Nat, +bits2: Ap.Bits(), +e: {Fr.Ie.r_id(ri) == Done{(ie, Ap.Cur{rem2, bits2})} : Ap.Rd(Fr.Ie)}) -> PC.Canon(bits, Fr.Ie.write(ie, rem, bits2), rem2, Fr.Ie.after(rem)):
  match ri:
    case Fail{err}:
      PA.Rd.absurd(Fr.Ie, PC.Canon(bits, Fr.Ie.write(ie, rem, bits2), rem2, Fr.Ie.after(rem)), err, ie, Ap.Cur{rem2, bits2}, e)
    case Done{(+id, c1)}:
      match c1:
        case Ap.Cur{+r1, +b1}:
          Ie.sx.crit(rem, bits, id, r1, b1, Fr.Criticality.read(Ap.Cur{r1, b1}), {==}, ie, rem2, bits2, e, PC.AInt.sx(16n, 65535, rem, bits, id, r1, b1, eri, {==}))

def Ie.sx(+rem: Nat, +bits: Ap.Bits(), +ie: Fr.Ie, +rem2: Nat, +bits2: Ap.Bits(), e: {Fr.Ie.read(Ap.Cur{rem, bits}) == Done{(ie, Ap.Cur{rem2, bits2})} : Ap.Rd(Fr.Ie)}) -> PC.Canon(bits, Fr.Ie.write(ie, rem, bits2), rem2, Fr.Ie.after(rem)):
  Ie.sx.id(rem, bits, Ap.AInt.read(16n, 65535, Ap.Cur{rem, bits}), {==}, ie, rem2, bits2, e)

# The items of a container, read from an octet boundary.
def Ies.Sx(bits: Ap.Bits(), ies: List<&2, Fr.Ie>, rem2: Nat, bits2: Ap.Bits(), k: Nat) -> Type:
  PC.Canon(bits, Fr.Ies.items_write(ies, 0n, bits2), rem2, 0n) & {List.length(&2, Fr.Ie, ies) == k : Nat}

def Ies.sx.finish(+p: Nat, +bits: Ap.Bits(), +ie: Fr.Ie, +b3: Ap.Bits(), +ies2: List<&2, Fr.Ie>, +r5: Nat, +b5: Ap.Bits(), +rem2: Nat, +bits2: Ap.Bits(), si: PC.Canon(bits, Fr.Ie.write(ie, 0n, b3), 0n, 0n), s: Ies.Sx(b3, ies2, r5, b5, p), eb: {b5 == bits2 : Ap.Bits()}, er: {r5 == rem2 : Nat}) -> Ies.Sx(bits, ie <> ies2, rem2, bits2, 1n+p):
  (i1, i2) = si
  (cn, len) = s
  (h1, h2) = cn
  (((%eb : {bits == Fr.Ie.write(ie, 0n, Fr.Ies.items_write(ies2, 0n, _)) : Ap.Bits()}; (%h1 : {bits == Fr.Ie.write(ie, 0n, _) : Ap.Bits()}; i1)), (%er : {_ == 0n : Nat}; h2)), Equal.cong(Nat, Nat, m => 1n+m, List.length(&2, Fr.Ie, ies2), p, len))

def Ies.sx.cons(+p: Nat, +bits: Ap.Bits(), +ie: Fr.Ie, +r3: Nat, +b3: Ap.Bits(), rl: Ap.Rd(List<&2, Fr.Ie>), +erl: {Fr.Ies.items(p, Ap.Cur{r3, b3}) == rl : Ap.Rd(List<&2, Fr.Ie>)}, ih: @b4: Ap.Bits() -> @ies2: List<&2, Fr.Ie> -> @r5: Nat -> @b5: Ap.Bits() -> {Fr.Ies.items(p, Ap.Cur{0n, b4}) == Done{(ies2, Ap.Cur{r5, b5})} : Ap.Rd(List<&2, Fr.Ie>)} -> Ies.Sx(b4, ies2, r5, b5, p), +ies: List<&2, Fr.Ie>, +rem2: Nat, +bits2: Ap.Bits(), +e: {Fr.Ies.cons(ie, rl) == Done{(ies, Ap.Cur{rem2, bits2})} : Ap.Rd(List<&2, Fr.Ie>)}, si: PC.Canon(bits, Fr.Ie.write(ie, 0n, b3), r3, 0n)) -> Ies.Sx(bits, ies, rem2, bits2, 1n+p):
  match rl:
    case Fail{err}:
      PA.Rd.absurd(List<&2, Fr.Ie>, Ies.Sx(bits, ies, rem2, bits2, 1n+p), err, ies, Ap.Cur{rem2, bits2}, e)
    case Done{(+ies2, c5)}:
      match c5:
        case Ap.Cur{+r5, +b5}:
          (i1, +i2) = si
          ev = Equal.cong(Ap.Rd(List<&2, Fr.Ie>), List<&2, Fr.Ie>, x => PA.Rd.value(List<&2, Fr.Ie>, x, ies), Done{(ie <> ies2, Ap.Cur{r5, b5})}, Done{(ies, Ap.Cur{rem2, bits2})}, e)
          +ec = Equal.cong(Ap.Rd(List<&2, Fr.Ie>), Ap.Cur, x => PA.Rd.cur(List<&2, Fr.Ie>, x, Ap.Cur{rem2, bits2}), Done{(ie <> ies2, Ap.Cur{r5, b5})}, Done{(ies, Ap.Cur{rem2, bits2})}, e)
          %ev : Ies.Sx(bits, _, rem2, bits2, 1n+p)
          Ies.sx.finish(p, bits, ie, b3, ies2, r5, b5, rem2, bits2, (%i2 : PC.Canon(bits, Fr.Ie.write(ie, 0n, b3), _, 0n); si), ih(b3, ies2, r5, b5, (%i2 : {Fr.Ies.items(p, Ap.Cur{_, b3}) == Done{(ies2, Ap.Cur{r5, b5})} : Ap.Rd(List<&2, Fr.Ie>)}; erl)), Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{r5, b5}, Ap.Cur{rem2, bits2}, ec), Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{r5, b5}, Ap.Cur{rem2, bits2}, ec))

def Ies.sx.step(+p: Nat, +bits: Ap.Bits(), ri: Ap.Rd(Fr.Ie), +eri: {Fr.Ie.read(Ap.Cur{0n, bits}) == ri : Ap.Rd(Fr.Ie)}, ih: @b4: Ap.Bits() -> @ies2: List<&2, Fr.Ie> -> @r5: Nat -> @b5: Ap.Bits() -> {Fr.Ies.items(p, Ap.Cur{0n, b4}) == Done{(ies2, Ap.Cur{r5, b5})} : Ap.Rd(List<&2, Fr.Ie>)} -> Ies.Sx(b4, ies2, r5, b5, p), +ies: List<&2, Fr.Ie>, +rem2: Nat, +bits2: Ap.Bits(), +e: {Fr.Ies.next(ri, c4 => Fr.Ies.items(p, c4)) == Done{(ies, Ap.Cur{rem2, bits2})} : Ap.Rd(List<&2, Fr.Ie>)}) -> Ies.Sx(bits, ies, rem2, bits2, 1n+p):
  match ri:
    case Fail{err}:
      PA.Rd.absurd(List<&2, Fr.Ie>, Ies.Sx(bits, ies, rem2, bits2, 1n+p), err, ies, Ap.Cur{rem2, bits2}, e)
    case Done{(+ie, c3)}:
      match c3:
        case Ap.Cur{+r3, +b3}:
          Ies.sx.cons(p, bits, ie, r3, b3, Fr.Ies.items(p, Ap.Cur{r3, b3}), {==}, ih, ies, rem2, bits2, e, Ie.sx(0n, bits, ie, r3, b3, eri))

def Ies.sx.items(k: Nat, +bits: Ap.Bits(), +ies: List<&2, Fr.Ie>, +rem2: Nat, +bits2: Ap.Bits(), +e: {Fr.Ies.items(k, Ap.Cur{0n, bits}) == Done{(ies, Ap.Cur{rem2, bits2})} : Ap.Rd(List<&2, Fr.Ie>)}) -> Ies.Sx(bits, ies, rem2, bits2, k):
  match k:
    case 0n:
      ev = Equal.cong(Ap.Rd(List<&2, Fr.Ie>), List<&2, Fr.Ie>, x => PA.Rd.value(List<&2, Fr.Ie>, x, ies), Done{([], Ap.Cur{0n, bits})}, Done{(ies, Ap.Cur{rem2, bits2})}, e)
      +ec = Equal.cong(Ap.Rd(List<&2, Fr.Ie>), Ap.Cur, x => PA.Rd.cur(List<&2, Fr.Ie>, x, Ap.Cur{rem2, bits2}), Done{([], Ap.Cur{0n, bits})}, Done{(ies, Ap.Cur{rem2, bits2})}, e)
      %ev : Ies.Sx(bits, _, rem2, bits2, 0n)
      ((Equal.cong(Ap.Cur, Ap.Bits(), x => PA.Cur.bits(x), Ap.Cur{0n, bits}, Ap.Cur{rem2, bits2}, ec), Equal.sym(Nat, 0n, rem2, Equal.cong(Ap.Cur, Nat, x => PA.Cur.rem(x), Ap.Cur{0n, bits}, Ap.Cur{rem2, bits2}, ec))), {==})
    case 1n++p:
      Ies.sx.step(p, bits, Fr.Ie.read(Ap.Cur{0n, bits}), {==}, b4 => ies2 => r5 => b5 => e2 => Ies.sx.items(p, b4, ies2, r5, b5, e2), ies, rem2, bits2, e)

def Ies.sx.go(+lo: Nat, +rem: Nat, +bits: Ap.Bits(), +k: Nat, +r1: Nat, +b1: Ap.Bits(), +ies: List<&2, Fr.Ie>, +rem2: Nat, +bits2: Ap.Bits(), ss: PC.Canon(bits, Ap.Size.write(True{}, 16n, lo, k, rem, b1), r1, Ap.Size.after(True{}, 16n, rem)), s: Ies.Sx(b1, ies, rem2, bits2, k)) -> PC.Canon(bits, Ap.Size.write(True{}, 16n, lo, List.length(&2, Fr.Ie, ies), rem, Fr.Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), bits2)), rem2, 0n):
  (s1, s2) = ss
  (cn, len) = s
  (h1, h2) = cn
  slen = Equal.sym(Nat, List.length(&2, Fr.Ie, ies), k, len)
  ((%slen : {bits == Ap.Size.write(True{}, 16n, lo, _, rem, Fr.Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), bits2)) : Ap.Bits()}; (%h1 : {bits == Ap.Size.write(True{}, 16n, lo, k, rem, _) : Ap.Bits()}; s1)), h2)

def Ies.sx.go.al(+lo: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), +k: Nat, +r1: Nat, +b1: Ap.Bits(), +ies: List<&2, Fr.Ie>, +rem2: Nat, +bits2: Ap.Bits(), +e: {Fr.Ies.items(k, Ap.Cur{r1, b1}) == Done{(ies, Ap.Cur{rem2, bits2})} : Ap.Rd(List<&2, Fr.Ie>)}, ss: PC.Canon(bits, Ap.Size.write(True{}, 16n, lo, k, rem, b1), r1, Ap.Size.after(True{}, 16n, rem))) -> PC.Canon(bits, Ap.Size.write(True{}, 16n, lo, List.length(&2, Fr.Ie, ies), rem, Fr.Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), bits2)), rem2, 0n):
  (s1, +s2) = ss
  Ies.sx.go(lo, rem, bits, k, r1, b1, ies, rem2, bits2, (s1, s2), Ies.sx.items(k, b1, ies, rem2, bits2, (%s2 : {Fr.Ies.items(k, Ap.Cur{_, b1}) == Done{(ies, Ap.Cur{rem2, bits2})} : Ap.Rd(List<&2, Fr.Ie>)}; e)))

def Ies.sx.count(+lo: Nat, +diff: Nat, +rem: Nat, +bits: Ap.Bits(), rl: Ap.Rd(Nat), +erl: {Ap.Size.read(True{}, 16n, lo, diff, Ap.Cur{rem, bits}) == rl : Ap.Rd(Nat)}, +ies: List<&2, Fr.Ie>, +rem2: Nat, +bits2: Ap.Bits(), +e: {Fr.Ies.count(rl) == Done{(ies, Ap.Cur{rem2, bits2})} : Ap.Rd(List<&2, Fr.Ie>)}) -> PC.Canon(bits, Ap.Size.write(True{}, 16n, lo, List.length(&2, Fr.Ie, ies), rem, Fr.Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), bits2)), rem2, 0n):
  match rl:
    case Fail{err}:
      PA.Rd.absurd(List<&2, Fr.Ie>, PC.Canon(bits, Ap.Size.write(True{}, 16n, lo, List.length(&2, Fr.Ie, ies), rem, Fr.Ies.items_write(ies, Ap.Size.after(True{}, 16n, rem), bits2)), rem2, 0n), err, ies, Ap.Cur{rem2, bits2}, e)
    case Done{(+k, c1)}:
      match c1:
        case Ap.Cur{+r1, +b1}:
          Ies.sx.go.al(lo, diff, rem, bits, k, r1, b1, ies, rem2, bits2, e, PC.Size.sx(True{}, 16n, lo, diff, rem, bits, k, r1, b1, erl))

def Ies.sx(+rem: Nat, +bits: Ap.Bits(), +ies: List<&2, Fr.Ie>, +rem2: Nat, +bits2: Ap.Bits(), e: {Fr.Ies.read(Ap.Cur{rem, bits}) == Done{(ies, Ap.Cur{rem2, bits2})} : Ap.Rd(List<&2, Fr.Ie>)}) -> PC.Canon(bits, Fr.Ies.write(ies, rem, bits2), rem2, Fr.Ies.after(rem)):
  Ies.sx.count(0n, 65535n, rem, bits, Ap.Size.read(True{}, 16n, 0n, 65535n, Ap.Cur{rem, bits}), {==}, ies, rem2, bits2, e)

def Exts.sx(+rem: Nat, +bits: Ap.Bits(), +ies: List<&2, Fr.Ie>, +rem2: Nat, +bits2: Ap.Bits(), e: {Fr.Exts.read(Ap.Cur{rem, bits}) == Done{(ies, Ap.Cur{rem2, bits2})} : Ap.Rd(List<&2, Fr.Ie>)}) -> PC.Canon(bits, Fr.Exts.write(ies, rem, bits2), rem2, Fr.Exts.after(rem)):
  Ies.sx.count(1n, 65534n, rem, bits, Ap.Size.read(True{}, 16n, 1n, 65534n, Ap.Cur{rem, bits}), {==}, ies, rem2, bits2, e)

# Views
# -----

def View.absurd(-A: Data, -G: Type, err: B.Err, v: A, e: {Fail{err} == Done{v} : Result<&2, &2, B.Err, A>}) -> G:
  Empty.absurd(G, P.Refute.fail_done(B.Err, A, err, v, e))

def Prelude.dv(+known: List<&2, U32>, +ies: List<&2, Fr.Ie>, ok: Bool, eok: {Bool.and(Fr.Ies.no_dups(ies), Fr.Ies.comprehended(known, ies)) == ok : Bool}, +ies2: List<&2, Fr.Ie>, +e: {Fr.View.gate(ies, ok) == Done{ies2} : Result<&2, &2, B.Err, List<&2, Fr.Ie>>}) -> {Fr.Ies.no_dups(ies) == True{} : Bool}:
  match ok:
    case False{}:
      View.absurd(List<&2, Fr.Ie>, {Fr.Ies.no_dups(ies) == True{} : Bool}, B.Invalid{0}, ies2, e)
    case True{}:
      P.Bool.and_true_l(Fr.Ies.no_dups(ies), Fr.Ies.comprehended(known, ies), eok)

def L.ngap.view.duplicate_rejected(known, ies, ies2, e):
  Prelude.dv(known, ies, Bool.and(Fr.Ies.no_dups(ies), Fr.Ies.comprehended(known, ies)), {==}, ies2, e)

def Prelude.gate(+ies: List<&2, Fr.Ie>, ok: Bool, +ies2: List<&2, Fr.Ie>, +e: {Fr.View.gate(ies, ok) == Done{ies2} : Result<&2, &2, B.Err, List<&2, Fr.Ie>>}) -> {ies == ies2 : List<&2, Fr.Ie>}:
  match ok:
    case False{}:
      View.absurd(List<&2, Fr.Ie>, {ies == ies2 : List<&2, Fr.Ie>}, B.Invalid{0}, ies2, e)
    case True{}:
      Equal.cong(Result<&2, &2, B.Err, List<&2, Fr.Ie>>, List<&2, Fr.Ie>, y => P.Res.value(B.Err, List<&2, Fr.Ie>, y, ies), Done{ies}, Done{ies2}, e)

# What a view's prelude passes on is the container it was given, so without duplicate ids.
def Prelude.same(+known: List<&2, U32>, +ies: List<&2, Fr.Ie>, +ies2: List<&2, Fr.Ie>, +e: {Fr.View.prelude(known, ies) == Done{ies2} : Result<&2, &2, B.Err, List<&2, Fr.Ie>>}) -> {ies == ies2 : List<&2, Fr.Ie>}:
  Prelude.gate(ies, Bool.and(Fr.Ies.no_dups(ies), Fr.Ies.comprehended(known, ies)), ies2, e)

def Prelude.nd(+known: List<&2, U32>, +ies: List<&2, Fr.Ie>, +ies2: List<&2, Fr.Ie>, +e: {Fr.View.prelude(known, ies) == Done{ies2} : Result<&2, &2, B.Err, List<&2, Fr.Ie>>}) -> {Fr.Ies.no_dups(ies2) == True{} : Bool}:
  +same = Prelude.same(known, ies, ies2, e)
  (%same : {Fr.Ies.no_dups(_) == True{} : Bool}; L.ngap.view.duplicate_rejected(known, ies, ies2, e))

# Lookups
# -------

def Ies.absent(+id: U32, ies: List<&2, Fr.Ie>, +h: {Fr.Ies.has(id, ies) == False{} : Bool}) -> {Fr.Ies.occurrences(id, ies) == 0n : Nat}:
  match ies:
    case Nil{}:
      {==}
    case +ie <> +more:
      sh = Equal.sym(Bool, U32.is_eq(Fr.Ie.id(ie), id), False{}, P.Bool.or_false_l(U32.is_eq(Fr.Ie.id(ie), id), Fr.Ies.has(id, more), h))
      %sh : {Fr.Ies.bump(Fr.Ies.occurrences(id, more), _) == 0n : Nat}
      Ies.absent(id, more, P.Bool.or_false_r(U32.is_eq(Fr.Ie.id(ie), id), Fr.Ies.has(id, more), h))

def Ies.lookup_step(+id: U32, +ie: Fr.Ie, +more: List<&2, Fr.Ie>, +v: B.Bytes(), hit: Bool, +eh: {U32.is_eq(Fr.Ie.id(ie), id) == hit : Bool}, +nd: {Bool.and(Bool.not(Fr.Ies.has(Fr.Ie.id(ie), more)), Fr.Ies.no_dups(more)) == True{} : Bool}, +e: {Fr.Ies.pick(ie, Fr.Ies.lookup(id, more), hit) == Some{v} : Maybe<&2, B.Bytes()>}, ih: {Fr.Ies.lookup(id, more) == Some{v} : Maybe<&2, B.Bytes()>} -> {Fr.Ies.occurrences(id, more) == 1n : Nat}) -> {Fr.Ies.bump(Fr.Ies.occurrences(id, more), U32.is_eq(Fr.Ie.id(ie), id)) == 1n : Nat}:
  match hit:
    case True{}:
      seh = Equal.sym(Bool, U32.is_eq(Fr.Ie.id(ie), id), True{}, eh)
      %seh : {Fr.Ies.bump(Fr.Ies.occurrences(id, more), _) == 1n : Nat}
      hid = P.U32.eq_of_is_eq(Fr.Ie.id(ie), id, eh)
      h0 = P.Bool.not_true(Fr.Ies.has(Fr.Ie.id(ie), more), P.Bool.and_true_l(Bool.not(Fr.Ies.has(Fr.Ie.id(ie), more)), Fr.Ies.no_dups(more), nd))
      Equal.cong(Nat, Nat, n => 1n+n, Fr.Ies.occurrences(id, more), 0n, Ies.absent(id, more, (%hid : {Fr.Ies.has(_, more) == False{} : Bool}; h0)))
    case False{}:
      seh = Equal.sym(Bool, U32.is_eq(Fr.Ie.id(ie), id), False{}, eh)
      %seh : {Fr.Ies.bump(Fr.Ies.occurrences(id, more), _) == 1n : Nat}
      ih(e)

# With no duplicate ids, a successful lookup means exactly one occurrence.
def Ies.lookup_count(+id: U32, ies: List<&2, Fr.Ie>, +v: B.Bytes(), +nd: {Fr.Ies.no_dups(ies) == True{} : Bool}, +e: {Fr.Ies.lookup(id, ies) == Some{v} : Maybe<&2, B.Bytes()>}) -> {Fr.Ies.occurrences(id, ies) == 1n : Nat}:
  match ies:
    case Nil{}:
      Empty.absurd({0n == 1n : Nat}, P.Refute.none_some(B.Bytes(), v, e))
    case +ie <> +more:
      Ies.lookup_step(id, ie, more, v, U32.is_eq(Fr.Ie.id(ie), id), {==}, nd, e, e2 => Ies.lookup_count(id, more, v, P.Bool.and_true_r(Bool.not(Fr.Ies.has(Fr.Ie.id(ie), more)), Fr.Ies.no_dups(more), nd), e2))
