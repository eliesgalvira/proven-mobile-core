import Base
import ./bytes.bend as B
import ./plmn.bend as P
import ./crypto/milenage.bend as Mil
import ./crypto/kdf.bend as K
import ./frame.bend as F

# AUSF and UDM in one module: the subscriber records, the 5G-AKA vector
# (TS 33.501 §6.1.3.2) over Milenage (TS 35.206), its checks and SQN
# re-synchronisation (TS 33.102 §6.3.5).

# Subscribers
# -----------

type Subscriber is Data:
  Subscriber{supi: B.Digits(), k: B.Bytes(), opc: B.Bytes(), amf: B.Bytes(), sqn: B.Bytes()}

def Subscriber.supi(s: Subscriber) -> B.Digits():
  match s:
    case Subscriber{supi, k, opc, amf, sqn}:
      supi

def Subscriber.sqn(s: Subscriber) -> B.Bytes():
  match s:
    case Subscriber{supi, k, opc, amf, sqn}:
      sqn

def Subscriber.with_sqn(s: Subscriber, new: B.Bytes()) -> Subscriber:
  match s:
    case Subscriber{supi, k, opc, amf, sqn}:
      Subscriber{supi, k, opc, amf, new}

def Digits.of_ascii(bs: B.Bytes()) -> B.Digits():
  match bs:
    case Nil{}:
      []
    case b <> rest:
      U32.sub(b, 48) <> Digits.of_ascii(rest)

def Subscriber.of(s: F.Sub) -> Subscriber:
  match s:
    case F.Sub{supi, k, opc, amf, sqn}:
      Subscriber{Digits.of_ascii(supi), k, opc, amf, sqn}

def Subscribers.cons(r: Result<&2, &2, B.Err, F.Sub>, more: List<&2, Subscriber>) -> List<&2, Subscriber>:
  match r:
    case Fail{e}:
      more
    case Done{s}:
      Subscriber.of(s) <> more

# The Config's subscriber TLV values, each already known to parse.
def Subscribers.of(raws: List<&2, B.Bytes()>) -> List<&2, Subscriber>:
  match raws:
    case Nil{}:
      []
    case raw <> more:
      Subscribers.cons(F.Sub.read(raw), Subscribers.of(more))

def Subscribers.pick(s: Subscriber, later: Maybe<&2, Subscriber>, hit: Bool) -> Maybe<&2, Subscriber>:
  match hit:
    case True{}:
      Some{s}
    case False{}:
      later

def Subscribers.find(+supi: B.Digits(), subs: List<&2, Subscriber>) -> Maybe<&2, Subscriber>:
  match subs:
    case Nil{}:
      None{}
    case +s <> more:
      Subscribers.pick(s, Subscribers.find(supi, more), B.bytes_eq(Subscriber.supi(s), supi))

def Subscribers.swap(s: Subscriber, new: Subscriber, rest: List<&2, Subscriber>, hit: Bool) -> List<&2, Subscriber>:
  match hit:
    case True{}:
      new <> rest
    case False{}:
      s <> rest

# The subscriber with that SUPI replaced.
def Subscribers.update(+new: Subscriber, subs: List<&2, Subscriber>) -> List<&2, Subscriber>:
  match subs:
    case Nil{}:
      []
    case +s <> more:
      Subscribers.swap(s, new, Subscribers.update(new, more), B.bytes_eq(Subscriber.supi(s), Subscriber.supi(new)))

# Bytes
# -----

def Bytes.xor(xs: B.Bytes(), ys: B.Bytes()) -> B.Bytes():
  match xs ys:
    case Nil{} Nil{}:
      []
    case Nil{} y <> yt:
      []
    case x <> xt Nil{}:
      []
    case x <> xt y <> yt:
      U32.xor(x, y) <> Bytes.xor(xt, yt)

def Bytes.carry(rev: B.Bytes(), +c: U32) -> B.Bytes():
  match rev:
    case Nil{}:
      []
    case b <> rest:
      +s = U32.add(b, c)
      U32.and(255, s) <> Bytes.carry(rest, U32.shrn(s, 8n))

# SQN + 32 over 48 bits (TS 33.102 Annex C.3.2, a 5-bit IND): the next sequence number.
def Sqn.next(sqn: B.Bytes()) -> B.Bytes():
  List.reverse(&2, U32, Bytes.carry(List.reverse(&2, U32, sqn), 32))

# The authentication vector
# -------------------------

type Av is Data:
  Av{rand: B.Bytes(), autn: B.Bytes(), xres_star: B.Bytes(), hxres_star: B.Bytes(), k_ausf: B.Bytes()}

def Av.rand(av: Av) -> B.Bytes():
  match av:
    case Av{rand, autn, xres_star, hxres_star, k_ausf}:
      rand

def Av.autn(av: Av) -> B.Bytes():
  match av:
    case Av{rand, autn, xres_star, hxres_star, k_ausf}:
      autn

def Av.xres_star(av: Av) -> B.Bytes():
  match av:
    case Av{rand, autn, xres_star, hxres_star, k_ausf}:
      xres_star

def Av.hxres_star(av: Av) -> B.Bytes():
  match av:
    case Av{rand, autn, xres_star, hxres_star, k_ausf}:
      hxres_star

def Av.k_ausf(av: Av) -> B.Bytes():
  match av:
    case Av{rand, autn, xres_star, hxres_star, k_ausf}:
      k_ausf

# The serving network name of a PLMN in TS 24.501 encoding.
def Ausf.snn_of(r: B.Read(P.Plmn)) -> B.Bytes():
  match r:
    case Fail{e}:
      []
    case Done{(+p, rest)}:
      K.kdf.serving_network_name(P.Plmn.mcc(p), P.Plmn.mnc(p))

def Ausf.snn(plmn: B.Bytes()) -> B.Bytes():
  Ausf.snn_of(P.Plmn.read(plmn))

# The vector for a subscriber whose SQN was just advanced, with the RAND given.
def Av.make(sub: Subscriber, +snn: B.Bytes(), +rand: B.Bytes()) -> Av:
  match sub:
    case Subscriber{supi, +k, +opc, +amf, +sqn}:
      +ck = Mil.milenage.f3(k, opc, rand)
      +ik = Mil.milenage.f4(k, opc, rand)
      +sqn_ak = Bytes.xor(sqn, Mil.milenage.f5(k, opc, rand))
      +res_star = K.kdf.res_star(ck, ik, snn, rand, Mil.milenage.f2(k, opc, rand))
      Av{rand, List.append(&2, U32, sqn_ak, List.append(&2, U32, amf, Mil.milenage.f1(k, opc, rand, sqn, amf))), res_star, K.kdf.hres_star(rand, res_star), K.kdf.k_ausf(ck, ik, snn, sqn_ak)}

# The UE's answer is accepted only over all sixteen octets, twice: the SEAF
# compares HRES* with HXRES*, the AUSF compares RES* with XRES*.
def Ausf.verify(av: Av, +res_star: B.Bytes()) -> Bool:
  match av:
    case Av{+rand, autn, xres_star, hxres_star, k_ausf}:
      Bool.and(Nat.is_eq(List.length(&2, U32, res_star), 16n), Bool.and(B.bytes_eq(K.kdf.hres_star(rand, res_star), hxres_star), B.bytes_eq(res_star, xres_star)))

# The keys after a successful authentication: KSEAF, then KAMF from the SUPI and ABBA.
def Ausf.k_amf(av: Av, snn: B.Bytes(), supi: B.Digits()) -> B.Bytes():
  K.kdf.k_amf(K.kdf.k_seaf(Av.k_ausf(av), snn), K.Kdf.digits_ascii(supi), [0, 0])

# Re-synchronisation: the SQN the UE holds, if the AUTS authenticates (TS 33.102 §6.3.5).
def Ausf.resync_if(sqn_ms: B.Bytes(), ok: Bool) -> Maybe<&2, B.Bytes()>:
  match ok:
    case True{}:
      Some{sqn_ms}
    case False{}:
      None{}

def Ausf.resync(sub: Subscriber, +rand: B.Bytes(), +auts: B.Bytes()) -> Maybe<&2, B.Bytes()>:
  match sub:
    case Subscriber{supi, +k, +opc, amf, sqn}:
      +sqn_ms = Bytes.xor(List.take(&2, U32, auts, 6n), Mil.milenage.f5_star(k, opc, rand))
      Ausf.resync_if(sqn_ms, Bool.and(Nat.is_eq(List.length(&2, U32, auts), 14n), B.bytes_eq(Mil.milenage.f1_star(k, opc, rand, sqn_ms, [0, 0]), List.drop(&2, U32, auts, 6n))))
