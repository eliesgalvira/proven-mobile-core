import Base
import ../LAWS.bend as L
import ../bytes.bend as B
import ../crypto/cmac.bend as M
import ../crypto/ctr.bend as CT
import ../nas/security.bend as N
import ./lib.bend as P

# Proofs of the NAS security laws (ticket 09).

# A MAC is 4 bytes.
def Nas.mac_len(ia: N.Nas.Ia, +k: B.Bytes(), +c: U32, +bearer: U32, +dir: U32, +m: B.Bytes()) -> {List.length(&2, U32, N.Nas.mac(ia, k, c, bearer, dir, m)) == 4n : Nat}:
  match ia:
    case N.Nia2{}:
      tl = Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, M.cmac(k, N.Nas.header8(c, bearer, dir, m)), 4n)), Nat.min(List.length(&2, U32, M.cmac(k, N.Nas.header8(c, bearer, dir, m))), 4n), P.List.take_len(M.cmac(k, N.Nas.header8(c, bearer, dir, m)), 4n))
      cl = Equal.sym(Nat, List.length(&2, U32, M.cmac(k, N.Nas.header8(c, bearer, dir, m))), 16n, L.cmac.length(k, N.Nas.header8(c, bearer, dir, m)))
      %tl : {_ == 4n : Nat}
      %cl : {Nat.min(_, 4n) == 4n : Nat}
      {==}

# A 4-byte list has four elements.
def Nas.mac4(-G: Type, mac: B.Bytes(), e: {List.length(&2, U32, mac) == 4n : Nat}, k: @a: U32 -> @b: U32 -> @c: U32 -> @d: U32 -> {mac == [a, b, c, d] : B.Bytes()} -> G) -> G:
  match mac:
    case Nil{}:
      Empty.absurd(G, (%e : P.Lift(Nat.is_eq(0n, _)); Unit{}))
    case a <> Nil{}:
      Empty.absurd(G, (%e : P.Lift(Nat.is_eq(1n, _)); Unit{}))
    case a <> b <> Nil{}:
      Empty.absurd(G, (%e : P.Lift(Nat.is_eq(2n, _)); Unit{}))
    case a <> b <> c <> Nil{}:
      Empty.absurd(G, (%e : P.Lift(Nat.is_eq(3n, _)); Unit{}))
    case a <> b <> c <> d <> Nil{}:
      k(a, b, c, d, {==})
    case a <> b <> c <> d <> f <> t:
      Empty.absurd(G, (%e : P.Lift(Nat.is_lt(4n, _)); Unit{}))

# Short messages
# --------------

def Nas.short(+keys: N.Nas.Keys, +dir: U32, +count: N.Nas.Count, msg: B.Bytes(), e: {Nat.is_lt(List.length(&2, U32, msg), 7n) == True{} : Bool}) -> {N.Nas.open(keys, dir, count, msg) == Fail{B.Short{}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  match msg:
    case Nil{}:
      {==}
    case x0 <> Nil{}:
      {==}
    case x0 <> x1 <> Nil{}:
      {==}
    case x0 <> x1 <> x2 <> Nil{}:
      {==}
    case x0 <> x1 <> x2 <> x3 <> Nil{}:
      {==}
    case x0 <> x1 <> x2 <> x3 <> x4 <> Nil{}:
      {==}
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> Nil{}:
      {==}
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> Nil{}:
      Empty.absurd({N.Nas.open(keys, dir, count, [x0, x1, x2, x3, x4, x5, x6]) == Fail{B.Short{}} : Result<&2, &2, B.Err, N.Nas.Opened>}, P.Refute.bool(e))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> t:
      Empty.absurd({N.Nas.open(keys, dir, count, x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> t) == Fail{B.Short{}} : Result<&2, &2, B.Err, N.Nas.Opened>}, P.Refute.bool(e))

# The MAC is compared in full
# ---------------------------

def Nas.MacEq(ia: N.Nas.Ia, k_int: B.Bytes(), count32: U32, bearer: U32, dir: U32, m0: U32, m1: U32, m2: U32, m3: U32, sqn: U32, body: B.Bytes()) -> Type:
  {[m0, m1, m2, m3] == N.Nas.mac(ia, k_int, count32, bearer, dir, sqn <> body) : B.Bytes()}

def Nas.mac_spec(+ia: N.Nas.Ia, +k_int: B.Bytes(), k_enc: B.Bytes(), ea: N.Nas.Ea, +count32: U32, +bearer: U32, +dir: U32, +m0: U32, +m1: U32, +m2: U32, +m3: U32, +sqn: U32, +body: B.Bytes(), p: N.Nas.Protection, o: N.Nas.Opened, ok: Bool,
  ev: {B.bytes_eq([m0, m1, m2, m3], N.Nas.mac(ia, k_int, count32, bearer, dir, sqn <> body)) == ok : Bool},
  e: {N.Nas.o_body(ea, k_enc, count32, bearer, dir, p, body, ok) == Done{o} : Result<&2, &2, B.Err, N.Nas.Opened>}) -> Nas.MacEq(ia, k_int, count32, bearer, dir, m0, m1, m2, m3, sqn, body):
  match ok:
    case True{}:
      P.Bytes.eq_of_bytes_eq([m0, m1, m2, m3], N.Nas.mac(ia, k_int, count32, bearer, dir, sqn <> body), ev)
    case False{}:
      Empty.absurd(Nas.MacEq(ia, k_int, count32, bearer, dir, m0, m1, m2, m3, sqn, body), P.Refute.fail_done(B.Err, N.Nas.Opened, B.Invalid{N.Nas.Protection.code(p)}, o, e))

def Nas.prot_spec(+ia: N.Nas.Ia, +k_int: B.Bytes(), +k_enc: B.Bytes(), +ea: N.Nas.Ea, +count32: U32, +bearer: U32, +dir: U32, +m0: U32, +m1: U32, +m2: U32, +m3: U32, +sqn: U32, +body: B.Bytes(), +o: N.Nas.Opened, pm: Maybe<&2, N.Nas.Protection>,
  e: {N.Nas.o_prot(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count32, [m0, m1, m2, m3], sqn, body, pm) == Done{o} : Result<&2, &2, B.Err, N.Nas.Opened>}) -> Nas.MacEq(ia, k_int, count32, bearer, dir, m0, m1, m2, m3, sqn, body):
  match pm:
    case None{}:
      Empty.absurd(Nas.MacEq(ia, k_int, count32, bearer, dir, m0, m1, m2, m3, sqn, body), P.Refute.fail_done(B.Err, N.Nas.Opened, B.Unsupported{0}, o, e))
    case Some{+p}:
      Nas.mac_spec(ia, k_int, k_enc, ea, count32, bearer, dir, m0, m1, m2, m3, sqn, body, p, o, B.bytes_eq([m0, m1, m2, m3], N.Nas.mac(ia, k_int, count32, bearer, dir, sqn <> body)), {==}, e)

def Nas.epd_spec(+ia: N.Nas.Ia, +k_int: B.Bytes(), +k_enc: B.Bytes(), +ea: N.Nas.Ea, +count32: U32, +bearer: U32, +dir: U32, +code: U32, +m0: U32, +m1: U32, +m2: U32, +m3: U32, +sqn: U32, +body: B.Bytes(), +o: N.Nas.Opened, ok: Bool,
  e: {N.Nas.o_epd(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count32, code, [m0, m1, m2, m3], sqn, body, ok) == Done{o} : Result<&2, &2, B.Err, N.Nas.Opened>}) -> Nas.MacEq(ia, k_int, count32, bearer, dir, m0, m1, m2, m3, sqn, body):
  match ok:
    case True{}:
      Nas.prot_spec(ia, k_int, k_enc, ea, count32, bearer, dir, m0, m1, m2, m3, sqn, body, o, N.Nas.Protection.of(code), e)
    case False{}:
      Empty.absurd(Nas.MacEq(ia, k_int, count32, bearer, dir, m0, m1, m2, m3, sqn, body), P.Refute.fail_done(B.Err, N.Nas.Opened, B.Invalid{code}, o, e))

def Nas.Full(keys: N.Nas.Keys, dir: U32, count: N.Nas.Count, msg: B.Bytes()) -> Type:
  {N.Nas.received_mac(msg) == N.Nas.mac(N.Nas.Keys.ia(keys), N.Nas.Keys.k_int(keys), N.Nas.Count.value(count), N.Nas.Keys.bearer(keys), dir, List.drop(&2, U32, msg, 6n)) : B.Bytes()} & {List.length(&2, U32, N.Nas.received_mac(msg)) == 4n : Nat}

def Nas.full(+k_int: B.Bytes(), +k_enc: B.Bytes(), +ea: N.Nas.Ea, +ia: N.Nas.Ia, +bearer: U32, +dir: U32, +count: N.Nas.Count, msg: B.Bytes(), +o: N.Nas.Opened, e: {N.Nas.open(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count, msg) == Done{o} : Result<&2, &2, B.Err, N.Nas.Opened>}) -> Nas.Full(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count, msg):
  match msg:
    case Nil{}:
      Empty.absurd(Nas.Full(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count, Nil{}), P.Refute.fail_done(B.Err, N.Nas.Opened, B.Short{}, o, e))
    case x0 <> Nil{}:
      Empty.absurd(Nas.Full(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count, x0 <> Nil{}), P.Refute.fail_done(B.Err, N.Nas.Opened, B.Short{}, o, e))
    case x0 <> x1 <> Nil{}:
      Empty.absurd(Nas.Full(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count, x0 <> x1 <> Nil{}), P.Refute.fail_done(B.Err, N.Nas.Opened, B.Short{}, o, e))
    case x0 <> x1 <> x2 <> Nil{}:
      Empty.absurd(Nas.Full(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count, x0 <> x1 <> x2 <> Nil{}), P.Refute.fail_done(B.Err, N.Nas.Opened, B.Short{}, o, e))
    case x0 <> x1 <> x2 <> x3 <> Nil{}:
      Empty.absurd(Nas.Full(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count, x0 <> x1 <> x2 <> x3 <> Nil{}), P.Refute.fail_done(B.Err, N.Nas.Opened, B.Short{}, o, e))
    case x0 <> x1 <> x2 <> x3 <> x4 <> Nil{}:
      Empty.absurd(Nas.Full(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count, x0 <> x1 <> x2 <> x3 <> x4 <> Nil{}), P.Refute.fail_done(B.Err, N.Nas.Opened, B.Short{}, o, e))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> Nil{}:
      Empty.absurd(Nas.Full(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count, x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> Nil{}), P.Refute.fail_done(B.Err, N.Nas.Opened, B.Short{}, o, e))
    case +epd <> +code <> +m0 <> +m1 <> +m2 <> +m3 <> +sqn <> +body:
      (Nas.epd_spec(ia, k_int, k_enc, ea, N.Nas.Count.value(count), bearer, dir, code, m0, m1, m2, m3, sqn, body, o, U32.is_eq(epd, N.Nas.epd()), e), {==})

def L.nas_sec.mac_full_length(keys, dir, count, msg, o):
  match keys:
    case N.Keys{k_int, k_enc, ea, ia, bearer}:
      (e => Nas.short(N.Keys{k_int, k_enc, ea, ia, bearer}, dir, count, msg, e), e => Nas.full(k_int, k_enc, ea, ia, bearer, dir, count, msg, o, e))

# Roundtrip
# ---------

def Nas.rt_Integrity_Nea0.body(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, eq: {N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{}))) == [a, b, c, d] : B.Bytes()}) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.Integrity{}) <> List.append(&2, U32, N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{}))), N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{})))) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  +se = Equal.sym(B.Bytes(), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{}))), [a, b, c, d], eq)
  %se : {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.Integrity{}) <> List.append(&2, U32, _, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{})))) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  %se : {N.Nas.o_body(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.Integrity{}, N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{})), B.bytes_eq([a, b, c, d], _)) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  re = Equal.sym(Bool, B.bytes_eq([a, b, c, d], [a, b, c, d]), True{}, P.Bytes.eq_refl([a, b, c, d]))
  %re : {N.Nas.o_body(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.Integrity{}, N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{})), _) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  {==}

def Nas.rt_Integrity_Nea0(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes()) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, N.Integrity{}, dir, count, plain)) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  Nas.mac4(({N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, N.Integrity{}, dir, count, plain)) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{}))), Nas.mac_len(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{}))), a => b => c => d => eq => Nas.rt_Integrity_Nea0.body(k_int, k_enc, bearer, dir, count, plain, a, b, c, d, eq))

def Nas.rt_Integrity_Nea2.body(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, eq: {N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{}))) == [a, b, c, d] : B.Bytes()}) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.Integrity{}) <> List.append(&2, U32, N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{}))), N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{})))) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  +se = Equal.sym(B.Bytes(), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{}))), [a, b, c, d], eq)
  %se : {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.Integrity{}) <> List.append(&2, U32, _, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{})))) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  %se : {N.Nas.o_body(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.Integrity{}, N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{})), B.bytes_eq([a, b, c, d], _)) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  re = Equal.sym(Bool, B.bytes_eq([a, b, c, d], [a, b, c, d]), True{}, P.Bytes.eq_refl([a, b, c, d]))
  %re : {N.Nas.o_body(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.Integrity{}, N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{})), _) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  {==}

def Nas.rt_Integrity_Nea2(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes()) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, N.Integrity{}, dir, count, plain)) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  Nas.mac4(({N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, N.Integrity{}, dir, count, plain)) == Done{N.Opened{N.Integrity{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{}))), Nas.mac_len(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Integrity{}))), a => b => c => d => eq => Nas.rt_Integrity_Nea2.body(k_int, k_enc, bearer, dir, count, plain, a, b, c, d, eq))

def Nas.rt_Ciphered_Nea0.body(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, eq: {N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{}))) == [a, b, c, d] : B.Bytes()}) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.Ciphered{}) <> List.append(&2, U32, N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{}))), N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{})))) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  +se = Equal.sym(B.Bytes(), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{}))), [a, b, c, d], eq)
  %se : {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.Ciphered{}) <> List.append(&2, U32, _, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{})))) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  %se : {N.Nas.o_body(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.Ciphered{}, N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{})), B.bytes_eq([a, b, c, d], _)) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  re = Equal.sym(Bool, B.bytes_eq([a, b, c, d], [a, b, c, d]), True{}, P.Bytes.eq_refl([a, b, c, d]))
  %re : {N.Nas.o_body(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.Ciphered{}, N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{})), _) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  {==}

def Nas.rt_Ciphered_Nea0(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes()) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, N.Ciphered{}, dir, count, plain)) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  Nas.mac4(({N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, N.Ciphered{}, dir, count, plain)) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{}))), Nas.mac_len(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{}))), a => b => c => d => eq => Nas.rt_Ciphered_Nea0.body(k_int, k_enc, bearer, dir, count, plain, a, b, c, d, eq))

def Nas.rt_Ciphered_Nea2.body(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, eq: {N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{}))) == [a, b, c, d] : B.Bytes()}) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.Ciphered{}) <> List.append(&2, U32, N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{}))), N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{})))) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  +se = Equal.sym(B.Bytes(), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{}))), [a, b, c, d], eq)
  %se : {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.Ciphered{}) <> List.append(&2, U32, _, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{})))) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  %se : {N.Nas.o_body(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.Ciphered{}, N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{})), B.bytes_eq([a, b, c, d], _)) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  re = Equal.sym(Bool, B.bytes_eq([a, b, c, d], [a, b, c, d]), True{}, P.Bytes.eq_refl([a, b, c, d]))
  %re : {N.Nas.o_body(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.Ciphered{}, N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{})), _) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  inv = Equal.sym(B.Bytes(), CT.ctr(k_enc, N.Nas.header8(N.Nas.Count.value(count), bearer, dir, [0, 0, 0, 0, 0, 0, 0, 0]), CT.ctr(k_enc, N.Nas.header8(N.Nas.Count.value(count), bearer, dir, [0, 0, 0, 0, 0, 0, 0, 0]), plain)), plain, L.ctr.involution(k_enc, N.Nas.header8(N.Nas.Count.value(count), bearer, dir, [0, 0, 0, 0, 0, 0, 0, 0]), plain))
  %inv : {Done{N.Opened{N.Ciphered{}, _}} == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  {==}

def Nas.rt_Ciphered_Nea2(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes()) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, N.Ciphered{}, dir, count, plain)) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  Nas.mac4(({N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, N.Ciphered{}, dir, count, plain)) == Done{N.Opened{N.Ciphered{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{}))), Nas.mac_len(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.Ciphered{}))), a => b => c => d => eq => Nas.rt_Ciphered_Nea2.body(k_int, k_enc, bearer, dir, count, plain, a, b, c, d, eq))

def Nas.rt_IntegrityNew_Nea0.body(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, eq: {N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{}))) == [a, b, c, d] : B.Bytes()}) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.IntegrityNew{}) <> List.append(&2, U32, N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{}))), N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{})))) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  +se = Equal.sym(B.Bytes(), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{}))), [a, b, c, d], eq)
  %se : {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.IntegrityNew{}) <> List.append(&2, U32, _, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{})))) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  %se : {N.Nas.o_body(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.IntegrityNew{}, N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{})), B.bytes_eq([a, b, c, d], _)) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  re = Equal.sym(Bool, B.bytes_eq([a, b, c, d], [a, b, c, d]), True{}, P.Bytes.eq_refl([a, b, c, d]))
  %re : {N.Nas.o_body(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.IntegrityNew{}, N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{})), _) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  {==}

def Nas.rt_IntegrityNew_Nea0(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes()) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, N.IntegrityNew{}, dir, count, plain)) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  Nas.mac4(({N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, N.IntegrityNew{}, dir, count, plain)) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{}))), Nas.mac_len(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{}))), a => b => c => d => eq => Nas.rt_IntegrityNew_Nea0.body(k_int, k_enc, bearer, dir, count, plain, a, b, c, d, eq))

def Nas.rt_IntegrityNew_Nea2.body(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, eq: {N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{}))) == [a, b, c, d] : B.Bytes()}) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.IntegrityNew{}) <> List.append(&2, U32, N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{}))), N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{})))) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  +se = Equal.sym(B.Bytes(), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{}))), [a, b, c, d], eq)
  %se : {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.IntegrityNew{}) <> List.append(&2, U32, _, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{})))) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  %se : {N.Nas.o_body(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.IntegrityNew{}, N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{})), B.bytes_eq([a, b, c, d], _)) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  re = Equal.sym(Bool, B.bytes_eq([a, b, c, d], [a, b, c, d]), True{}, P.Bytes.eq_refl([a, b, c, d]))
  %re : {N.Nas.o_body(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.IntegrityNew{}, N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{})), _) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  {==}

def Nas.rt_IntegrityNew_Nea2(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes()) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, N.IntegrityNew{}, dir, count, plain)) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  Nas.mac4(({N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, N.IntegrityNew{}, dir, count, plain)) == Done{N.Opened{N.IntegrityNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{}))), Nas.mac_len(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.IntegrityNew{}))), a => b => c => d => eq => Nas.rt_IntegrityNew_Nea2.body(k_int, k_enc, bearer, dir, count, plain, a, b, c, d, eq))

def Nas.rt_CipheredNew_Nea0.body(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, eq: {N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{}))) == [a, b, c, d] : B.Bytes()}) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.CipheredNew{}) <> List.append(&2, U32, N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{}))), N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{})))) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  +se = Equal.sym(B.Bytes(), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{}))), [a, b, c, d], eq)
  %se : {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.CipheredNew{}) <> List.append(&2, U32, _, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{})))) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  %se : {N.Nas.o_body(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.CipheredNew{}, N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{})), B.bytes_eq([a, b, c, d], _)) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  re = Equal.sym(Bool, B.bytes_eq([a, b, c, d], [a, b, c, d]), True{}, P.Bytes.eq_refl([a, b, c, d]))
  %re : {N.Nas.o_body(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.CipheredNew{}, N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{})), _) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  {==}

def Nas.rt_CipheredNew_Nea0(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes()) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, N.CipheredNew{}, dir, count, plain)) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  Nas.mac4(({N.Nas.open(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea0{}, N.Nia2{}, bearer}, N.CipheredNew{}, dir, count, plain)) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{}))), Nas.mac_len(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea0{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{}))), a => b => c => d => eq => Nas.rt_CipheredNew_Nea0.body(k_int, k_enc, bearer, dir, count, plain, a, b, c, d, eq))

def Nas.rt_CipheredNew_Nea2.body(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes(), +a: U32, +b: U32, +c: U32, +d: U32, eq: {N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{}))) == [a, b, c, d] : B.Bytes()}) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.CipheredNew{}) <> List.append(&2, U32, N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{}))), N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{})))) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  +se = Equal.sym(B.Bytes(), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{}))), [a, b, c, d], eq)
  %se : {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.epd() <> N.Nas.Protection.code(N.CipheredNew{}) <> List.append(&2, U32, _, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{})))) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  %se : {N.Nas.o_body(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.CipheredNew{}, N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{})), B.bytes_eq([a, b, c, d], _)) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  re = Equal.sym(Bool, B.bytes_eq([a, b, c, d], [a, b, c, d]), True{}, P.Bytes.eq_refl([a, b, c, d]))
  %re : {N.Nas.o_body(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, N.CipheredNew{}, N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{})), _) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  inv = Equal.sym(B.Bytes(), CT.ctr(k_enc, N.Nas.header8(N.Nas.Count.value(count), bearer, dir, [0, 0, 0, 0, 0, 0, 0, 0]), CT.ctr(k_enc, N.Nas.header8(N.Nas.Count.value(count), bearer, dir, [0, 0, 0, 0, 0, 0, 0, 0]), plain)), plain, L.ctr.involution(k_enc, N.Nas.header8(N.Nas.Count.value(count), bearer, dir, [0, 0, 0, 0, 0, 0, 0, 0]), plain))
  %inv : {Done{N.Opened{N.CipheredNew{}, _}} == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}
  {==}

def Nas.rt_CipheredNew_Nea2(+k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes()) -> {N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, N.CipheredNew{}, dir, count, plain)) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  Nas.mac4(({N.Nas.open(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, N.Nea2{}, N.Nia2{}, bearer}, N.CipheredNew{}, dir, count, plain)) == Done{N.Opened{N.CipheredNew{}, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}), N.Nas.mac(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{}))), Nas.mac_len(N.Nia2{}, k_int, N.Nas.Count.value(count), bearer, dir, N.Nas.Count.sqn(count) <> N.Nas.cipher_if(N.Nea2{}, k_enc, N.Nas.Count.value(count), bearer, dir, plain, N.Nas.Protection.ciphers(N.CipheredNew{}))), a => b => c => d => eq => Nas.rt_CipheredNew_Nea2.body(k_int, k_enc, bearer, dir, count, plain, a, b, c, d, eq))

def Nas.rt_dispatch(ea: N.Nas.Ea, prot: N.Nas.Protection, +k_int: B.Bytes(), +k_enc: B.Bytes(), +bearer: U32, +dir: U32, +count: N.Nas.Count, +plain: B.Bytes()) -> {N.Nas.open(N.Keys{k_int, k_enc, ea, N.Nia2{}, bearer}, dir, count, N.Nas.seal(N.Keys{k_int, k_enc, ea, N.Nia2{}, bearer}, prot, dir, count, plain)) == Done{N.Opened{prot, plain}} : Result<&2, &2, B.Err, N.Nas.Opened>}:
  match ea:
    case N.Nea0{}:
      match prot:
        case N.Integrity{}:
          Nas.rt_Integrity_Nea0(k_int, k_enc, bearer, dir, count, plain)
        case N.Ciphered{}:
          Nas.rt_Ciphered_Nea0(k_int, k_enc, bearer, dir, count, plain)
        case N.IntegrityNew{}:
          Nas.rt_IntegrityNew_Nea0(k_int, k_enc, bearer, dir, count, plain)
        case N.CipheredNew{}:
          Nas.rt_CipheredNew_Nea0(k_int, k_enc, bearer, dir, count, plain)
    case N.Nea2{}:
      match prot:
        case N.Integrity{}:
          Nas.rt_Integrity_Nea2(k_int, k_enc, bearer, dir, count, plain)
        case N.Ciphered{}:
          Nas.rt_Ciphered_Nea2(k_int, k_enc, bearer, dir, count, plain)
        case N.IntegrityNew{}:
          Nas.rt_IntegrityNew_Nea2(k_int, k_enc, bearer, dir, count, plain)
        case N.CipheredNew{}:
          Nas.rt_CipheredNew_Nea2(k_int, k_enc, bearer, dir, count, plain)

def L.nas_sec.roundtrip(keys, prot, dir, count, plain):
  match keys:
    case N.Keys{k_int, k_enc, ea, ia, bearer}:
      match ia:
        case N.Nia2{}:
          Nas.rt_dispatch(ea, prot, k_int, k_enc, bearer, dir, count, plain)

# COUNT
# -----

def Nas.Mono(last: N.Nas.Count, c: N.Nas.Count) -> Type:
  {N.Nas.Count.advanced(last, c) == True{} : Bool} & {U32.is_eq(N.Nas.Count.sqn(last), N.Nas.Count.sqn(c)) == False{} : Bool}

def Nas.fin_ft_ne(r: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, True{}, r)) == False{} : Bool}:
  match r:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Nas.inc_ne_word(+n: Nat, w: Word(1n+n)) -> {Cmp.is_eq(Word.cmp(1n+n, Word.inc(1n+n, w), w)) == False{} : Bool}:
  match w:
    case WCon{b, +t}:
      match b:
        case False{}:
          r = Equal.sym(Cmp, Word.cmp(n, t, t), EQ{}, P.Word.cmp_refl(n, t))
          %r : {Cmp.is_eq(Word.cmp.fin(True{}, False{}, _)) == False{} : Bool}
          {==}
        case True{}:
          Nas.fin_ft_ne(Word.cmp(n, Word.inc(n, t), t))

def Nas.inc_ne_flip(+o: U32) -> {U32.is_eq(U32.inc(o), o) == False{} : Bool}:
  match o:
    case U32{+w}:
      Nas.inc_ne_word(31n, w)

def Nas.adv_same(+o: U32, +ls: U32, +sqn: U32, ro: {True{} == U32.is_eq(o, o) : Bool}, sg: {True{} == U32.is_lt(ls, sqn) : Bool}) -> {N.Nas.Count.advanced(N.Count{o, ls}, N.Count{o, sqn}) == True{} : Bool}:
  %ro : {Bool.or(Bool.and(_, U32.is_lt(ls, sqn)), Bool.and(U32.is_eq(o, U32.inc(o)), U32.is_lt(o, 65535))) == True{} : Bool}
  %sg : {Bool.or(Bool.and(True{}, _), Bool.and(U32.is_eq(o, U32.inc(o)), U32.is_lt(o, 65535))) == True{} : Bool}
  {==}

def Nas.adv_next(+o: U32, +ls: U32, +sqn: U32, er: {U32.is_lt(o, 65535) == True{} : Bool}) -> {N.Nas.Count.advanced(N.Count{o, ls}, N.Count{U32.inc(o), sqn}) == True{} : Bool}:
  ne = Equal.sym(Bool, U32.is_eq(U32.inc(o), o), False{}, Nas.inc_ne_flip(o))
  %ne : {Bool.or(Bool.and(_, U32.is_lt(ls, sqn)), Bool.and(U32.is_eq(U32.inc(o), U32.inc(o)), U32.is_lt(o, 65535))) == True{} : Bool}
  re = Equal.sym(Bool, U32.is_eq(U32.inc(o), U32.inc(o)), True{}, P.U32.is_eq_refl(U32.inc(o)))
  %re : {Bool.or(False{}, Bool.and(_, U32.is_lt(o, 65535))) == True{} : Bool}
  sr = Equal.sym(Bool, U32.is_lt(o, 65535), True{}, er)
  %sr : {Bool.or(False{}, Bool.and(True{}, _)) == True{} : Bool}
  {==}

def Nas.open_spec(+keys: N.Nas.Keys, +dl: N.Nas.Count, +c: N.Nas.Count, +u: N.Nas.Unprotected, ro: Result<&2, &2, B.Err, N.Nas.Opened>, e: {N.Nas.u_open(keys, dl, c, ro) == Done{u} : Result<&2, &2, B.Err, N.Nas.Unprotected>}) -> {N.Nas.Unprotected.count(u) == c : N.Nas.Count}:
  match ro:
    case Fail{err}:
      Empty.absurd({N.Nas.Unprotected.count(u) == c : N.Nas.Count}, P.Refute.fail_done(B.Err, N.Nas.Unprotected, err, u, e))
    case Done{N.Opened{p, pl}}:
      eq = Equal.cong(Result<&2, &2, B.Err, N.Nas.Unprotected>, N.Nas.Unprotected, x => P.Res.value(B.Err, N.Nas.Unprotected, x, u), Done{N.Unprotected{p, pl, c, N.Ctx{keys, dl, Some{c}}}}, Done{u}, e)
      %eq : {N.Nas.Unprotected.count(_) == c : N.Nas.Count}
      {==}

def Nas.mono_of(+last: N.Nas.Count, +c: N.Nas.Count, +u: N.Nas.Unprotected, eq: {N.Nas.Unprotected.count(u) == c : N.Nas.Count}, m: Nas.Mono(last, c)) -> Nas.Mono(last, N.Nas.Unprotected.count(u)):
  se = Equal.sym(N.Nas.Count, N.Nas.Unprotected.count(u), c, eq)
  %se : Nas.Mono(last, _)
  m

def Nas.est_spec(+keys: N.Nas.Keys, +dl: N.Nas.Count, +msg: B.Bytes(), +u: N.Nas.Unprotected, +o: U32, +ls: U32, +sqn: U32, greater: Bool, same: Bool, room: Bool,
  +eg: {U32.is_lt(ls, sqn) == greater : Bool}, +es: {U32.is_eq(ls, sqn) == same : Bool}, +er: {U32.is_lt(o, 65535) == room : Bool},
  e: {N.Nas.u_count(keys, dl, msg, N.Nas.estimate.step(o, sqn, greater, same, room)) == Done{u} : Result<&2, &2, B.Err, N.Nas.Unprotected>}) -> Nas.Mono(N.Count{o, ls}, N.Nas.Unprotected.count(u)):
  match greater:
    case True{}:
      eqc = Nas.open_spec(keys, dl, N.Count{o, sqn}, u, N.Nas.open(keys, N.Nas.uplink(), N.Count{o, sqn}, msg), e)
      ro = Equal.sym(Bool, U32.is_eq(o, o), True{}, P.U32.is_eq_refl(o))
      sg = Equal.sym(Bool, U32.is_lt(ls, sqn), True{}, eg)
      Nas.mono_of(N.Count{o, ls}, N.Count{o, sqn}, u, eqc, (Nas.adv_same(o, ls, sqn, ro, sg), P.U32.eq_false_of_lt(ls, sqn, eg)))
    case False{}:
      match same:
        case True{}:
          Empty.absurd(Nas.Mono(N.Count{o, ls}, N.Nas.Unprotected.count(u)), P.Refute.fail_done(B.Err, N.Nas.Unprotected, B.Invalid{sqn}, u, e))
        case False{}:
          match room:
            case True{}:
              eqc = Nas.open_spec(keys, dl, N.Count{U32.inc(o), sqn}, u, N.Nas.open(keys, N.Nas.uplink(), N.Count{U32.inc(o), sqn}, msg), e)
              Nas.mono_of(N.Count{o, ls}, N.Count{U32.inc(o), sqn}, u, eqc, (Nas.adv_next(o, ls, sqn, er), es))
            case False{}:
              Empty.absurd(Nas.Mono(N.Count{o, ls}, N.Nas.Unprotected.count(u)), P.Refute.fail_done(B.Err, N.Nas.Unprotected, B.Unsupported{sqn}, u, e))

def Nas.sqn_spec(+keys: N.Nas.Keys, +dl: N.Nas.Count, +o: U32, +ls: U32, +msg: B.Bytes(), +u: N.Nas.Unprotected, r: B.Read(U32), e: {N.Nas.u_sqn(N.Ctx{keys, dl, Some{N.Count{o, ls}}}, msg, r) == Done{u} : Result<&2, &2, B.Err, N.Nas.Unprotected>}) -> Nas.Mono(N.Count{o, ls}, N.Nas.Unprotected.count(u)):
  match r:
    case Fail{err}:
      Empty.absurd(Nas.Mono(N.Count{o, ls}, N.Nas.Unprotected.count(u)), P.Refute.fail_done(B.Err, N.Nas.Unprotected, err, u, e))
    case Done{(+sqn, rest)}:
      Nas.est_spec(keys, dl, msg, u, o, ls, sqn, U32.is_lt(ls, sqn), U32.is_eq(ls, sqn), U32.is_lt(o, 65535), {==}, {==}, {==}, e)

def Nas.ul_last(+keys: N.Nas.Keys, +dl: N.Nas.Count, l: N.Nas.Count, +msg: B.Bytes(), +u: N.Nas.Unprotected, e: {N.Nas.unprotect(N.Ctx{keys, dl, Some{l}}, msg) == Done{u} : Result<&2, &2, B.Err, N.Nas.Unprotected>}) -> Nas.Mono(l, N.Nas.Unprotected.count(u)):
  match l:
    case N.Count{+o, +ls}:
      Nas.sqn_spec(keys, dl, o, ls, msg, u, B.u8(List.drop(&2, U32, msg, 6n)), e)

def Nas.ul_spec(+keys: N.Nas.Keys, +dl: N.Nas.Count, ul: Maybe<&2, N.Nas.Count>, +msg: B.Bytes(), +u: N.Nas.Unprotected, +last: N.Nas.Count, e: {N.Nas.unprotect(N.Ctx{keys, dl, ul}, msg) == Done{u} : Result<&2, &2, B.Err, N.Nas.Unprotected>}, s: {ul == Some{last} : Maybe<&2, N.Nas.Count>}) -> Nas.Mono(last, N.Nas.Unprotected.count(u)):
  match ul:
    case None{}:
      Empty.absurd(Nas.Mono(last, N.Nas.Unprotected.count(u)), P.Refute.none_some(N.Nas.Count, last, s))
    case Some{+l}:
      eq = Equal.cong(Maybe<&2, N.Nas.Count>, N.Nas.Count, x => P.Maybe.value(N.Nas.Count, x, l), Some{l}, Some{last}, s)
      %eq : Nas.Mono(_, N.Nas.Unprotected.count(u))
      Nas.ul_last(keys, dl, l, msg, u, e)

def L.nas_sec.count_monotonic(ctx, msg, u, last, e, s):
  match ctx:
    case N.Ctx{keys, dl, ul}:
      Nas.ul_spec(keys, dl, ul, msg, u, last, e, s)
