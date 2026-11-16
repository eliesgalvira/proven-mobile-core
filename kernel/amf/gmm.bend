import Base
import ../bytes.bend as B
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../nas/ie.bend as I
import ../nas/mm.bend as Mm
import ../nas/mobile_id.bend as Mi
import ../nas/security.bend as Sec
import ../crypto/kdf.bend as Kd
import ../suci.bend as Su
import ../plmn.bend as P
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../ausf.bend as Au
import ../smf/n4.bend as Up
import ../smf/gsm.bend as Gsm
import ./ngap.bend as N
import ./handover.bend as Ho

# Registration (TS 24.501 §5.5.1, §5.4.1 to §5.4.3, §5.5.2) and UE context
# release (TS 38.413 §8.3.2, §8.3.3): the UE is identified by its SUCI,
# authenticated with 5G-AKA, given a NAS security context, set up at the gNB,
# accepted, and later released. Every outcome is a transaction on the state and
# a list of semantic actions (`N.Act`), applied and rendered at the boundary.

def Gmm.max_retries() -> U32:
  4

# 5GMM messages
# -------------

def Gmm.nas(mt: Mm.Mm.Type, fields: List<&2, I.Field>, opts: List<&2, I.Ie>) -> B.Bytes():
  Mm.Mm.write(Mm.Mm{mt, fields, opts})

def Gmm.auth_request(ngksi: U32, +av: Au.Av) -> B.Bytes():
  Gmm.nas(Mm.AuthenticationRequest{}, [I.FByte{ngksi}, I.FLv{I.LenBody{2, [0, 0]}}], [I.Ie{33, I.Tv{16n}, 0, Au.Av.rand(av)}, I.Ie{32, I.Tlv{}, 16, Au.Av.autn(av)}])

def Gmm.identity_request() -> B.Bytes():
  Gmm.nas(Mm.IdentityRequest{}, [I.FByte{1}], [])

def Gmm.registration_reject(cause: U32) -> B.Bytes():
  Gmm.nas(Mm.RegistrationReject{}, [I.FByte{cause}], [])

# #9, UE identity cannot be derived by the network: the UE registers again.
def Gmm.service_reject() -> B.Bytes():
  Gmm.nas(Mm.ServiceReject{}, [I.FByte{9}], [])

def Gmm.authentication_reject() -> B.Bytes():
  Gmm.nas(Mm.AuthenticationReject{}, [], [])

# Security Mode Command: the selected algorithms, ngKSI, the UE's capabilities
# replayed, an IMEISV request and RINMR (the Registration Request again, whole).
def Gmm.security_mode_command(alg: U32, ngksi: U32, +caps: B.Bytes()) -> B.Bytes():
  Gmm.nas(Mm.SecurityModeCommand{}, [I.FByte{alg}, I.FByte{ngksi}, I.FLv{I.LenBody{U32.from_nat(List.length(&2, U32, caps)), caps}}], [I.Ie{225, I.T1{}, 0, []}, I.Ie{54, I.Tlv{}, 1, [2]}])

# 5G-GUTI (TS 24.501 §9.11.3.4): the AMF set identifier above the pointer.
def Gmm.guti(+cfg: S.Cfg, tmsi: U32) -> B.Bytes():
  Mi.MobileId.guti() <> List.append(&2, U32, S.Cfg.plmn(cfg), List.append(&2, U32, S.Cfg.region(cfg), B.write_u16(U32.or(U32.shln(N.Ngap.of_big(S.Cfg.set_id(cfg)), 6n), N.Ngap.of_big(S.Cfg.pointer(cfg))), B.write_u32(tmsi, []))))

# T3512 (TS 24.008 §10.5.7.4a): five units of ten minutes, the closest to the fifty-four minutes asked for.
def Gmm.t3512() -> U32:
  5

# Registration Accept: 3GPP access, the 5G-GUTI, the TAI, the slice, T3512.
def Gmm.registration_accept(+cfg: S.Cfg, tmsi: U32) -> B.Bytes():
  Gmm.nas(Mm.RegistrationAccept{}, [I.FLv{I.LenBody{1, [1]}}], [I.Ie{119, I.TlvE{}, 11, Gmm.guti(cfg, tmsi)}, I.Ie{84, I.Tlv{}, 7, 0 <> List.append(&2, U32, S.Cfg.plmn(cfg), S.Cfg.tac(cfg))}, I.Ie{21, I.Tlv{}, 2, 1 <> S.Cfg.sst(cfg)}, I.Ie{94, I.Tlv{}, 1, [Gmm.t3512()]}])

def Gmm.deregistration_accept() -> B.Bytes():
  Gmm.nas(Mm.DeregistrationAcceptUe{}, [], [])

# Outcomes
# --------

def Gmm.dl(key: U32, +ue: S.Ue, nas: B.Bytes()) -> N.Act:
  N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), nas}

# Forgetting contexts
# -------------------

# A context forgotten, its sessions deleted at the UPF first.
def Gmm.forget(+st: S.State, +key: U32) -> N.GOut():
  N.Out.join(Up.N4.deletions(S.Sessions.of_ue(key, S.State.sessions(st)), S.State.pfcp_seq(st)), (S.Del{key}, []))

def Gmm.evict(victims: Tb.Table(S.Ue)) -> List<&2, N.Act>:
  match victims:
    case Nil{}:
      []
    case (+key, +v) <> more:
      +cause = N.Ngap.nas_cause(G.CauseNas.deregister())
      N.Release{S.Ue.assoc(v), S.Ue.stream(v), key, S.Ue.ran_id(v), cause} <> List.append(&2, N.Act, Ho.Ho.leg_drop(key, S.Ue.phase(v), cause), Gmm.evict(more))

# The sessions of the contexts given.
def Gmm.sessions(ues: Tb.Table(S.Ue), +sessions: Tb.Table(S.Session)) -> Tb.Table(S.Session):
  match ues:
    case Nil{}:
      []
    case (key, u) <> more:
      List.append(&2, Sigma<&2, &2, U32, _ => S.Session>, S.Sessions.of_ue(key, sessions), Gmm.sessions(more, sessions))

# The one write of a context's identity: it takes its place, and every live
# context it conflicts with (the same SUPI, 5G-TMSI or RAN id on the
# association) goes with its sessions, deleted at the UPF first, and with the
# target of its pending handover, released. A SUPI enters a context
# only once 5G-AKA has verified it (Gmm.secure) and a 5G-TMSI is drawn free
# (Gmm.tmsi), so another gNB's UE is taken over only after authentication.
def Gmm.place(+st: S.State, +key: U32, +ue: S.Ue) -> N.GOut():
  +victims = S.Ues.evicted(key, ue, S.State.ues(st))
  N.Out.join(Up.N4.deletions(Gmm.sessions(victims, S.State.sessions(st)), S.State.pfcp_seq(st)), (S.Put{key, ue}, Gmm.evict(victims)))

# UE Context Release Command; the context waits, releasing, for the gNB, and
# its guard, started again, bounds the wait; the target of its pending
# handover is released.
def Gmm.release(+st: S.State, +key: U32, +ue: S.Ue, +cause: G.Cause) -> N.GOut():
  N.Out.prepend(N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}, N.Out.also(Gmm.place(st, key, S.Ue.with_phase(ue, S.Releasing{S.Guard{0}})), N.TimerStart{Some{key}, key, N.Ue.guard_ms()} <> Ho.Ho.leg_drop(key, S.Ue.phase(ue), cause)))

# A 5GMM reject, then release.
def Gmm.refuse(st: S.State, +key: U32, +ue: S.Ue, nas: B.Bytes()) -> N.GOut():
  N.Out.prepend(Gmm.dl(key, ue, nas), Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified())))

def Gmm.reject(st: S.State, +key: U32, +ue: S.Ue, cause: U32) -> N.GOut():
  Gmm.refuse(st, key, ue, Gmm.registration_reject(cause))

def Gmm.auth_reject(st: S.State, +key: U32, +ue: S.Ue) -> N.GOut():
  N.Out.prepend(Gmm.dl(key, ue, Gmm.authentication_reject()), Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure())))

# Identification
# --------------

# A Registration Request carrying a SUCI, a 5G-GUTI we do not know, or no usable identity.
type Start is Data:
  Identified{suci: Su.Suci}
  Ask{}
  Unknown{}

def Gmm.start_of(id: Mi.MobileId) -> Start:
  match id:
    case Mi.Suci{suci}:
      Identified{suci}
    case Mi.Guti{plmn, region, amf, tmsi}:
      Ask{}
    case Mi.STmsi{amf, tmsi}:
      Ask{}
    case _:
      Unknown{}

def Gmm.identity_ask(+st: S.State, +key: U32, ue: S.Ue) -> N.GOut():
  +nas = Gmm.identity_request()
  +ue2 = S.Ue.with_dl(ue, S.Identifying{S.Guard{0}}, nas)
  N.Out.also(Gmm.place(st, key, ue2), [Gmm.dl(key, ue2, nas), N.TimerStart{Some{key}, key, N.Ue.guard_ms()}])

# Authentication Request from a fresh vector, its guard started again.
def Gmm.challenge(+st: S.State, +key: U32, +ue: S.Ue, +sub: Au.Subscriber, snn: B.Bytes(), entropy: B.Bytes(), resynced: Bool) -> N.GOut():
  +sub2 = Au.Subscriber.with_sqn(sub, Au.Sqn.next(Au.Subscriber.sqn(sub)))
  +av = Au.Av.make(sub2, snn, List.take(&2, U32, entropy, 16n))
  +nas = Gmm.auth_request(0, av)
  +ue2 = S.Ue.with_dl(ue, S.Authenticating{S.Guard{0}, av, resynced, Au.Subscriber.supi(sub2)}, nas)
  N.Out.join(Gmm.place(st, key, ue2), (S.Subs{Au.Subscribers.update(sub2, S.State.subs(st))}, [Gmm.dl(key, ue2, nas), N.TimerStart{Some{key}, key, N.Ue.guard_ms()}]))

def Gmm.by_sub(+st: S.State, key: U32, +ue: S.Ue, cfg: S.Cfg, m: Maybe<&2, Au.Subscriber>, entropy: B.Bytes()) -> N.GOut():
  match m:
    case None{}:
      Gmm.reject(st, key, ue, 7)
    case Some{sub}:
      Gmm.challenge(st, key, ue, sub, Au.Ausf.snn(S.Cfg.plmn(cfg)), entropy, False{})

def Gmm.by_supi(+st: S.State, key: U32, +ue: S.Ue, cfg: S.Cfg, r: Result<&2, &2, B.Err, Su.Supi>, entropy: B.Bytes()) -> N.GOut():
  match r:
    case Fail{e}:
      Gmm.reject(st, key, ue, 7)
    case Done{Su.Imsi{+plmn, msin}}:
      Gmm.by_sub(st, key, ue, cfg, Au.Subscribers.find(List.append(&2, U32, P.Plmn.mcc(plmn), List.append(&2, U32, P.Plmn.mnc(plmn), msin)), S.State.subs(st)), entropy)

def Gmm.with_cfg(+st: S.State, key: U32, +ue: S.Ue, suci: Su.Suci, entropy: B.Bytes(), cfg: Maybe<&2, S.Cfg>) -> N.GOut():
  match cfg:
    case None{}:
      Gmm.reject(st, key, ue, 7)
    case Some{+c}:
      Gmm.by_supi(st, key, ue, c, Su.Suci.deconceal(S.Cfg.suci_key(c), suci), entropy)

def Gmm.identified(+st: S.State, key: U32, ue: S.Ue, suci: Su.Suci, entropy: B.Bytes()) -> N.GOut():
  Gmm.with_cfg(st, key, ue, suci, entropy, S.State.config(st))

def Gmm.proceed(st: S.State, key: U32, ue: S.Ue, how: Start, entropy: B.Bytes()) -> N.GOut():
  match how:
    case Identified{suci}:
      Gmm.identified(st, key, ue, suci, entropy)
    case Ask{}:
      Gmm.identity_ask(st, key, ue)
    case Unknown{}:
      Gmm.reject(st, key, ue, 7)

# A new context, owned by the association, keyed by the AMF-UE-NGAP-ID the step gives.
def Gmm.fresh(assoc: U32, ran: B.Bytes(), stream: U32, nas: B.Bytes()) -> S.Ue:
  S.Ue{assoc, ran, stream, None{}, None{}, nas, 0, S.Created{}, []}

def Gmm.register(+st: S.State, +key: U32, assoc: U32, stream: U32, entropy: B.Bytes(), ran: B.Bytes(), nas: B.Bytes(), r: Mi.MobileId.Res()) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_nas(assoc))
    case Done{id}:
      N.Out.join((S.BumpUe{key}, []), Gmm.proceed(st, key, Gmm.fresh(assoc, ran, stream, nas), Gmm.start_of(id), entropy))

# A Service Request finds no context, as there is no CM-IDLE: the UE is told
# to register again.
def Gmm.serve(+st: S.State, +key: U32, assoc: U32, stream: U32, ran: B.Bytes(), nas: B.Bytes()) -> N.GOut():
  N.Out.join((S.BumpUe{key}, []), Gmm.refuse(st, key, Gmm.fresh(assoc, ran, stream, nas), Gmm.service_reject()))

def Gmm.initial_mm(+st: S.State, +key: U32, assoc: U32, stream: U32, entropy: B.Bytes(), ran: B.Bytes(), nas: B.Bytes(), m: Mm.Mm) -> N.GOut():
  match m:
    case Mm.Mm{mt, fields, opts}:
      match mt:
        case Mm.RegistrationRequest{}:
          Gmm.register(st, key, assoc, stream, entropy, ran, nas, Mi.MobileId.read(I.Fields.lve2(fields)))
        case Mm.ServiceRequest{}:
          Gmm.serve(st, key, assoc, stream, ran, nas)
        case _:
          (S.Keep{}, N.Ngap.bad_nas(assoc))

def Gmm.initial_nas(st: S.State, key: U32, assoc: U32, stream: U32, entropy: B.Bytes(), ran: B.Bytes(), nas: B.Bytes(), r: Result<&2, &2, B.Err, Mm.Mm>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_nas(assoc))
    case Done{m}:
      Gmm.initial_mm(st, key, assoc, stream, entropy, ran, nas, m)

# A returning UE protects its initial message with a security context the AMF
# no longer holds (security header type 1): it is read without verification
# (TS 24.501 §4.4.6) and leads to identification and authentication anew.
def Gmm.unprotected(nas: B.Bytes()) -> B.Bytes():
  match nas:
    case 126 <> 1 <> m0 <> m1 <> m2 <> m3 <> sqn <> plain:
      plain
    case _:
      nas

# No AMF-UE-NGAP-ID is free: the InitialUEMessage is refused.
def Gmm.initial_key(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), ran: B.Bytes(), +nas: B.Bytes(), m: Maybe<&2, U32>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.no_key(assoc))
    case Some{key}:
      Gmm.initial_nas(st, key, assoc, stream, entropy, ran, nas, Mm.Mm.read(nas))

# InitialUEMessage: a context is created only once its Registration Request or
# Service Request parses.
def Gmm.initial(+st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), v: V.InitialUEMessage.View) -> N.GOut():
  match v:
    case V.InitialUEMessage.View{ran_ue_ngap_id, nas_pdu, userlocationinformation, rrcestablishmentcause, fiveg_s_tmsi, amfsetid, allowednssai, selectedplmnidentity, iabnodeindication, cemodebsupport_indicator, npn_accessinformation}:
      Gmm.initial_key(st, assoc, stream, entropy, ran_ue_ngap_id, Gmm.unprotected(nas_pdu), S.State.fresh(st))

def Gmm.initial_of_view(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, V.InitialUEMessage.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Gmm.initial(st, assoc, stream, entropy, v)

# Security mode
# -------------

# The UE supports algorithm id (0 to 7) when its bit is set in the capability
# octet, bit 8 being algorithm 0 (TS 24.501 §9.11.3.54).
def Alg.supported(+byte: U32, +id: U32) -> Bool:
  Bool.not(U32.is_eq(U32.and(byte, U32.shrn(128, U32.to_nat(id))), 0))

def Alg.ea_or(m: Maybe<&2, Sec.Nas.Ea>, ok: Bool, later: Maybe<&2, Sec.Nas.Ea>) -> Maybe<&2, Sec.Nas.Ea>:
  match m ok:
    case Some{ea} True{}:
      Some{ea}
    case _ _:
      later

def Alg.ia_or(m: Maybe<&2, Sec.Nas.Ia>, ok: Bool, later: Maybe<&2, Sec.Nas.Ia>) -> Maybe<&2, Sec.Nas.Ia>:
  match m ok:
    case Some{ia} True{}:
      Some{ia}
    case _ _:
      later

# The first preferred algorithm the UE supports among those the kernel
# implements; NIA0 is not one of them.
def Alg.pick_ea(prefs: B.Bytes(), +byte: U32) -> Maybe<&2, Sec.Nas.Ea>:
  match prefs:
    case Nil{}:
      None{}
    case +id <> more:
      Alg.ea_or(Sec.Nas.Ea.of(id), Alg.supported(byte, id), Alg.pick_ea(more, byte))

def Alg.pick_ia(prefs: B.Bytes(), +byte: U32) -> Maybe<&2, Sec.Nas.Ia>:
  match prefs:
    case Nil{}:
      None{}
    case +id <> more:
      Alg.ia_or(Sec.Nas.Ia.of(id), Alg.supported(byte, id), Alg.pick_ia(more, byte))

# Security Mode Command, integrity protected with the new context, its guard
# started again; the verified SUPI takes its place in the index.
def Gmm.secure(+st: S.State, +key: U32, +ue: S.Ue, supi: B.Digits(), +k_amf: B.Bytes(), +ea: Sec.Nas.Ea, +ia: Sec.Nas.Ia, caps: B.Bytes()) -> N.GOut():
  +ctx : Sec.Nas.Ctx = Sec.Ctx{Sec.Keys{Kd.kdf.k_nas_int(k_amf, Sec.Nas.Ia.id(ia)), Kd.kdf.k_nas_enc(k_amf, Sec.Nas.Ea.id(ea)), ea, ia, 1}, Sec.Nas.Count.zero(), None{}}
  +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.IntegrityNew{}, Gmm.security_mode_command(U32.or(U32.shln(Sec.Nas.Ea.id(ea), 4n), Sec.Nas.Ia.id(ia)), S.Ue.ngksi(ue), caps))
  +ue2 = S.Ue.with_dl(S.Ue.with_supi(ue, supi), S.SecurityMode{S.Guard{0}, Sec.Nas.Protected.ctx(p), k_amf}, Sec.Nas.Protected.msg(p))
  N.Out.also(Gmm.place(st, key, ue2), [Gmm.dl(key, ue2, Sec.Nas.Protected.msg(p)), N.TimerStart{Some{key}, key, N.Ue.guard_ms()}])

# No algorithm in common is a UE security capabilities mismatch (cause #23).
def Gmm.algorithms(st: S.State, key: U32, ue: S.Ue, supi: B.Digits(), k_amf: B.Bytes(), caps: B.Bytes(), mea: Maybe<&2, Sec.Nas.Ea>, mia: Maybe<&2, Sec.Nas.Ia>) -> N.GOut():
  match mea mia:
    case Some{ea} Some{ia}:
      Gmm.secure(st, key, ue, supi, k_amf, ea, ia, caps)
    case _ _:
      Gmm.reject(st, key, ue, 23)

# Authentication
# --------------

def Gmm.keys(st: S.State, key: U32, +ue: S.Ue, av: Au.Av, +supi: B.Digits(), cfg: Maybe<&2, S.Cfg>) -> N.GOut():
  match cfg:
    case Some{+c}:
      +caps = N.Ue.caps(ue)
      Gmm.algorithms(st, key, ue, supi, Au.Ausf.k_amf(av, Au.Ausf.snn(S.Cfg.plmn(c)), supi), caps, Alg.pick_ea(S.Cfg.nea(c), N.Ngap.cap_byte(caps, 0n)), Alg.pick_ia(S.Cfg.nia(c), N.Ngap.cap_byte(caps, 1n)))
    case None{}:
      Gmm.auth_reject(st, key, ue)

def Gmm.verified(+st: S.State, key: U32, +ue: S.Ue, av: Au.Av, supi: B.Digits(), ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.keys(st, key, ue, av, supi, S.State.config(st))
    case False{}:
      Gmm.auth_reject(st, key, ue)

def Gmm.response(st: S.State, key: U32, ue: S.Ue, +av: Au.Av, supi: B.Digits(), res: Maybe<&2, B.Bytes()>) -> N.GOut():
  match res:
    case None{}:
      Gmm.auth_reject(st, key, ue)
    case Some{r}:
      Gmm.verified(st, key, ue, av, supi, Au.Ausf.verify(av, r))

def Gmm.resynced(st: S.State, key: U32, ue: S.Ue, sub: Au.Subscriber, cfg: S.Cfg, entropy: B.Bytes(), m: Maybe<&2, B.Bytes()>) -> N.GOut():
  match m:
    case None{}:
      Gmm.auth_reject(st, key, ue)
    case Some{sqn_ms}:
      Gmm.challenge(st, key, ue, Au.Subscriber.with_sqn(sub, sqn_ms), Au.Ausf.snn(S.Cfg.plmn(cfg)), entropy, True{})

def Gmm.resync_sub(st: S.State, key: U32, ue: S.Ue, av: Au.Av, auts: B.Bytes(), entropy: B.Bytes(), cfg: S.Cfg, m: Maybe<&2, Au.Subscriber>) -> N.GOut():
  match m:
    case None{}:
      Gmm.auth_reject(st, key, ue)
    case Some{+sub}:
      Gmm.resynced(st, key, ue, sub, cfg, entropy, Au.Ausf.resync(sub, Au.Av.rand(av), auts))

def Gmm.resync(+st: S.State, key: U32, ue: S.Ue, av: Au.Av, auts: B.Bytes(), entropy: B.Bytes(), supi: B.Digits(), cfg: Maybe<&2, S.Cfg>) -> N.GOut():
  match cfg:
    case Some{+c}:
      Gmm.resync_sub(st, key, ue, av, auts, entropy, c, Au.Subscribers.find(supi, S.State.subs(st)))
    case None{}:
      Gmm.auth_reject(st, key, ue)

# Synch failure with an AUTS re-synchronises once; anything else rejects.
def Gmm.failure_kind(+st: S.State, key: U32, +ue: S.Ue, av: Au.Av, supi: B.Digits(), auts: Maybe<&2, B.Bytes()>, entropy: B.Bytes(), retry: Bool) -> N.GOut():
  match auts retry:
    case Some{a} True{}:
      Gmm.resync(st, key, ue, av, a, entropy, supi, S.State.config(st))
    case _ _:
      Gmm.auth_reject(st, key, ue)

def Gmm.failure(st: S.State, key: U32, ue: S.Ue, av: Au.Av, resynced: Bool, supi: B.Digits(), cause: U32, auts: Maybe<&2, B.Bytes()>, entropy: B.Bytes()) -> N.GOut():
  Gmm.failure_kind(st, key, ue, av, supi, auts, entropy, Bool.and(U32.is_eq(cause, 21), Bool.not(resynced)))

def Gmm.identity_answer(st: S.State, key: U32, ue: S.Ue, entropy: B.Bytes(), r: Mi.MobileId.Res()) -> N.GOut():
  match r:
    case Fail{e}:
      Gmm.reject(st, key, ue, 7)
    case Done{Mi.Suci{suci}}:
      Gmm.identified(st, key, ue, suci, entropy)
    case Done{other}:
      Gmm.reject(st, key, ue, 7)

# A plain 5GMM message from a UE without a security context, read against its phase.
def Gmm.phase(st: S.State, key: U32, ue: S.Ue, entropy: B.Bytes(), mt: Mm.Mm.Type, fields: List<&2, I.Field>, opts: List<&2, I.Ie>, p: S.Phase) -> N.GOut():
  match mt p:
    case Mm.AuthenticationResponse{} S.Authenticating{guard, av, resynced, supi}:
      Gmm.response(st, key, ue, av, supi, I.Opts.find(I.Iei.authentication_response_parameter(), opts))
    case Mm.AuthenticationFailure{} S.Authenticating{guard, av, resynced, supi}:
      Gmm.failure(st, key, ue, av, resynced, supi, I.Fields.byte1(fields), I.Opts.find(I.Iei.authentication_failure_parameter(), opts), entropy)
    case Mm.IdentityResponse{} S.Identifying{guard}:
      Gmm.identity_answer(st, key, ue, entropy, Mi.MobileId.read(I.Fields.lve1(fields)))
    case _ _:
      N.Out.warn("5GMM: message not expected in this phase")

def Gmm.plain(st: S.State, key: U32, +ue: S.Ue, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Mm.Mm>) -> N.GOut():
  match r:
    case Fail{e}:
      N.Out.warn("5GMM: message not understood")
    case Done{Mm.Mm{mt, fields, opts}}:
      Gmm.phase(st, key, ue, entropy, mt, fields, opts, S.Ue.phase(ue))

# Completing registration
# -----------------------

# The 5G-TMSI: the first word of entropy that no context holds, since a
# 5G-GUTI names one UE (TS 23.003 §2.10); a collision never evicts.
def Gmm.tmsi(+ues: Tb.Table(S.Ue), words: B.Bytes()) -> Maybe<&2, U32>:
  match words:
    case a <> b <> c <> d <> more:
      +t = N.Ngap.of_big([a, b, c, d])
      Tb.Table.hit(U32, t, Gmm.tmsi(ues, more), Bool.not(S.Ues.has_tmsi(t, ues)))
    case _:
      None{}

# Security Mode Complete: the Registration Request in its NAS message container
# replaces the initial one; KgNB comes from the uplink COUNT of this message
# and starts the UE's NH chain; Initial Context Setup carries Registration
# Accept, ciphered, and T3550 guards it.
def Gmm.sm_complete(+st: S.State, +key: U32, +ue: S.Ue, +k_amf: B.Bytes(), ctx: Sec.Nas.Ctx, count: Sec.Nas.Count, opts: List<&2, I.Ie>, cfg: Maybe<&2, S.Cfg>, m: Maybe<&2, U32>) -> N.GOut():
  match cfg m:
    case Some{+c} Some{+tmsi}:
      +reg = I.Bytes.or(I.Opts.find(I.Iei.nas_message_container(), opts), S.Ue.reg(ue))
      +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.Ciphered{}, Gmm.registration_accept(c, tmsi))
      +k_gnb = Kd.kdf.k_gnb(k_amf, Sec.Nas.Count.value(count))
      +ue2 = S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(ue, S.ContextSetup{S.Guard{0}, Sec.Nas.Protected.ctx(p), S.Nh.initial(k_amf, k_gnb), False{}, False{}}, Sec.Nas.Protected.msg(p)), reg), tmsi)
      N.Out.also(Gmm.place(st, key, ue2), [N.Ics{S.Ue.assoc(ue2), S.Ue.stream(ue2), key, S.Ue.ran_id(ue2), c, N.Ue.caps(ue2), k_gnb, Sec.Nas.Protected.msg(p)}, N.TimerStart{Some{key}, key, N.Ue.guard_ms()}])
    case _ _:
      Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()))

# Registered once both Initial Context Setup Response and Registration Complete are in.
def Gmm.setup_done(st: S.State, +key: U32, +ue: S.Ue, guard: S.Guard, ctx: Sec.Nas.Ctx, nh: S.Nh, response: Bool, complete: Bool, both: Bool) -> N.GOut():
  match both:
    case True{}:
      (S.Rephase{key, S.Registered{ctx, nh, None{}}}, [N.TimerCancel{key}, N.Note{F.Info{}, "5GMM: UE registered"}])
    case False{}:
      (S.Rephase{key, S.ContextSetup{guard, ctx, nh, response, complete}}, [])

def Gmm.setup_step(st: S.State, key: U32, ue: S.Ue, guard: S.Guard, ctx: Sec.Nas.Ctx, nh: S.Nh, +response: Bool, +complete: Bool) -> N.GOut():
  Gmm.setup_done(st, key, ue, guard, ctx, nh, response, complete, Bool.and(response, complete))

# Deregistration Request from the UE: Accept unless it is switching off, then release.
def Gmm.dereg_answer(st: S.State, +key: U32, +ue: S.Ue, ctx: Sec.Nas.Ctx, switch_off: Bool) -> N.GOut():
  match switch_off:
    case True{}:
      Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister()))
    case False{}:
      N.Out.prepend(Gmm.dl(key, ue, Sec.Nas.Protected.msg(Sec.Nas.protect(ctx, Sec.Ciphered{}, Gmm.deregistration_accept()))), Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.deregister())))

def Gmm.deregister(st: S.State, key: U32, ue: S.Ue, ctx: Sec.Nas.Ctx, kind: U32) -> N.GOut():
  Gmm.dereg_answer(st, key, ue, ctx, Bool.not(U32.is_eq(U32.and(kind, 8), 0)))

# A verified 5GMM message, read against the UE's phase, with the context that verified it.
def Gmm.sphase(+st: S.State, key: U32, ue: S.Ue, entropy: B.Bytes(), count: Sec.Nas.Count, ctx: Sec.Nas.Ctx, mt: Mm.Mm.Type, fields: List<&2, I.Field>, opts: List<&2, I.Ie>, p: S.Phase) -> N.GOut():
  match mt p:
    case Mm.SecurityModeComplete{} S.SecurityMode{guard, old, k_amf}:
      Gmm.sm_complete(st, key, ue, k_amf, ctx, count, opts, S.State.config(st), Gmm.tmsi(S.State.ues(st), List.drop(&2, U32, entropy, 16n)))
    case Mm.SecurityModeReject{} S.SecurityMode{guard, old, k_amf}:
      Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()))
    case Mm.RegistrationComplete{} S.ContextSetup{guard, old, nh, response, complete}:
      Gmm.setup_step(st, key, ue, guard, ctx, nh, response, True{})
    case Mm.DeregistrationRequestUe{} S.ContextSetup{guard, old, nh, response, complete}:
      Gmm.deregister(st, key, ue, ctx, I.Fields.byte1(fields))
    case Mm.DeregistrationRequestUe{} S.Registered{old, nh, released}:
      Gmm.deregister(st, key, ue, ctx, I.Fields.byte1(fields))
    case Mm.UlNasTransport{} S.Registered{old, nh, released}:
      Gsm.Gsm.ul_transport(st, key, ue, ctx, fields, opts, entropy)
    case _ _:
      N.Out.verified(key, ue, ctx, "5GMM: message not expected in this phase")

def Gmm.protected(st: S.State, key: U32, +ue: S.Ue, entropy: B.Bytes(), count: Sec.Nas.Count, ctx: Sec.Nas.Ctx, r: Result<&2, &2, B.Err, Mm.Mm>) -> N.GOut():
  match r:
    case Fail{e}:
      N.Out.verified(key, ue, ctx, "5GMM: message not understood")
    case Done{Mm.Mm{mt, fields, opts}}:
      Gmm.sphase(st, key, ue, entropy, count, ctx, mt, fields, opts, S.Ue.phase(ue))

# With a security context in force, only a message that verifies under it is read.
def Gmm.opened(st: S.State, key: U32, ue: S.Ue, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Sec.Nas.Unprotected>) -> N.GOut():
  match r:
    case Fail{e}:
      N.Out.warn("NAS: message fails integrity verification")
    case Done{Sec.Unprotected{prot, plain, count, ctx}}:
      Gmm.protected(st, key, ue, entropy, count, ctx, Mm.Mm.read(plain))

def Gmm.secured(st: S.State, key: U32, ue: S.Ue, entropy: B.Bytes(), nas: B.Bytes(), m: Maybe<&2, Sec.Nas.Ctx>) -> N.GOut():
  match m:
    case None{}:
      Gmm.plain(st, key, ue, entropy, Mm.Mm.read(nas))
    case Some{ctx}:
      Gmm.opened(st, key, ue, entropy, Sec.Nas.unprotect(ctx, nas))

def Gmm.mm(st: S.State, key: U32, +ue: S.Ue, entropy: B.Bytes(), nas: B.Bytes()) -> N.GOut():
  Gmm.secured(st, key, ue, entropy, nas, S.Phase.ctx(S.Ue.phase(ue)))

# UE-associated NGAP
# ------------------

def Gmm.owner(st: S.State, assoc: U32, key: U32, ran: B.Bytes()) -> Maybe<&2, S.Ue>:
  N.Owner.of(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran)

def Gmm.uplink_ue(st: S.State, assoc: U32, key: U32, nas: B.Bytes(), entropy: B.Bytes(), m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{ue}:
      Gmm.mm(st, key, ue, entropy, nas)

def Gmm.uplink_key(+st: S.State, +assoc: U32, ran: B.Bytes(), nas: B.Bytes(), entropy: B.Bytes(), m: Maybe<&2, U32>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{+key}:
      Gmm.uplink_ue(st, assoc, key, nas, entropy, Gmm.owner(st, assoc, key, ran))

def Gmm.uplink(+st: S.State, +assoc: U32, stream: U32, entropy: B.Bytes(), v: V.UplinkNASTransport.View) -> N.GOut():
  match v:
    case V.UplinkNASTransport.View{amf_ue_ngap_id, ran_ue_ngap_id, nas_pdu, userlocationinformation}:
      Gmm.uplink_key(st, assoc, ran_ue_ngap_id, nas_pdu, entropy, N.Ngap.ue_key(amf_ue_ngap_id))

def Gmm.uplink_of_view(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, V.UplinkNASTransport.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Gmm.uplink(st, assoc, stream, entropy, v)

def Gmm.setup_phase(st: S.State, key: U32, ue: S.Ue, p: S.Phase) -> N.GOut():
  match p:
    case S.ContextSetup{guard, ctx, nh, response, complete}:
      Gmm.setup_step(st, key, ue, guard, ctx, nh, True{}, complete)
    case _:
      N.Out.warn("NGAP: Initial Context Setup Response not expected in this phase")

def Gmm.ics_response_ue(st: S.State, assoc: U32, key: U32, m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{+ue}:
      Gmm.setup_phase(st, key, ue, S.Ue.phase(ue))

def Gmm.ics_response_key(+st: S.State, +assoc: U32, ran: B.Bytes(), m: Maybe<&2, U32>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{+key}:
      Gmm.ics_response_ue(st, assoc, key, Gmm.owner(st, assoc, key, ran))

def Gmm.ics_response(+st: S.State, +assoc: U32, v: V.InitialContextSetupResponse.View) -> N.GOut():
  match v:
    case V.InitialContextSetupResponse.View{amf_ue_ngap_id, ran_ue_ngap_id, diagnostics}:
      Gmm.ics_response_key(st, assoc, ran_ue_ngap_id, N.Ngap.ue_key(amf_ue_ngap_id))

def Gmm.ics_response_of_view(st: S.State, assoc: U32, r: Result<&2, &2, B.Err, V.InitialContextSetupResponse.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Gmm.ics_response(st, assoc, v)

# UE Context Release Request from the owner: Release Command with its cause.
def Gmm.release_request_ue(st: S.State, assoc: U32, key: U32, cause: G.Cause, m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{ue}:
      Gmm.release(st, key, ue, cause)

def Gmm.release_request_key(+st: S.State, +assoc: U32, ran: B.Bytes(), cause: G.Cause, m: Maybe<&2, U32>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{+key}:
      Gmm.release_request_ue(st, assoc, key, cause, Gmm.owner(st, assoc, key, ran))

def Gmm.release_request(+st: S.State, +assoc: U32, v: V.UEContextReleaseRequest.View) -> N.GOut():
  match v:
    case V.UEContextReleaseRequest.View{amf_ue_ngap_id, ran_ue_ngap_id, pdusessionresourcelistcxtrelreq, cause}:
      Gmm.release_request_key(st, assoc, ran_ue_ngap_id, cause, N.Ngap.ue_key(amf_ue_ngap_id))

def Gmm.release_request_of_view(st: S.State, assoc: U32, r: Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Gmm.release_request(st, assoc, v)

# UE Context Release Complete from another association: the answer of the
# side a handover released, or an unknown UE.
def Gmm.unowned(assoc: U32, released: Bool) -> List<&2, N.Act>:
  match released:
    case True{}:
      [N.Note{F.Info{}, "NGAP: UE Context Release Complete from the side a handover released"}]
    case False{}:
      N.Ngap.unknown_ue(assoc)

# UE Context Release Complete from the owner: the context is forgotten, its guard stopped.
def Gmm.release_complete_ue(+st: S.State, assoc: U32, +key: U32, m: Maybe<&2, S.Ue>, released: Bool) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, Gmm.unowned(assoc, released))
    case Some{+ue}:
      N.Out.also(Gmm.forget(st, key), List.append(&2, N.Act, N.Guard.cancel(key, S.Ue.guard(ue)), List.append(&2, N.Act, Ho.Ho.leg_drop(key, S.Ue.phase(ue), N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified())), [N.Note{F.Info{}, "NGAP: UE context released"}])))

def Gmm.release_complete_key(+st: S.State, +assoc: U32, +ran: B.Bytes(), m: Maybe<&2, U32>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{+key}:
      Gmm.release_complete_ue(st, assoc, key, Gmm.owner(st, assoc, key, ran), S.Ue.released(Tb.Table.get(S.Ue, key, S.State.ues(st)), assoc, ran))

def Gmm.release_complete(+st: S.State, +assoc: U32, v: V.UEContextReleaseComplete.View) -> N.GOut():
  match v:
    case V.UEContextReleaseComplete.View{amf_ue_ngap_id, ran_ue_ngap_id, userlocationinformation, pdusessionresourcelistcxtrelcpl, diagnostics}:
      Gmm.release_complete_key(st, assoc, ran_ue_ngap_id, N.Ngap.ue_key(amf_ue_ngap_id))

def Gmm.release_complete_of_view(st: S.State, assoc: U32, r: Result<&2, &2, B.Err, V.UEContextReleaseComplete.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Gmm.release_complete(st, assoc, v)

# Guard timers
# ------------

def Gmm.retry_if(st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, p: S.Phase, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      (S.Rephase{key, S.Phase.with_guard(p, S.Guard{U32.add(S.Guard.retries(guard), 1)})}, [Gmm.dl(key, ue, S.Ue.last_dl(ue)), N.TimerStart{Some{key}, key, N.Ue.guard_ms()}])
    case False{}:
      Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()))

# The guard fired: retransmit the last downlink message, or give up and
# release; a Path Switch the UPF never finished is given up at once; an N2
# handover ends with the UE at its owner; a release the gNB never completed
# ends here, sessions deleted.
def Gmm.expired(st: S.State, key: U32, ue: S.Ue, +p: S.Phase) -> N.GOut():
  match p:
    case S.Created{}:
      (S.Keep{}, [])
    case S.Identifying{+guard}:
      Gmm.retry_if(st, key, ue, guard, p, U32.is_lt(S.Guard.retries(guard), Gmm.max_retries()))
    case S.Authenticating{+guard, av, resynced, supi}:
      Gmm.retry_if(st, key, ue, guard, p, U32.is_lt(S.Guard.retries(guard), Gmm.max_retries()))
    case S.SecurityMode{+guard, ctx, k_amf}:
      Gmm.retry_if(st, key, ue, guard, p, U32.is_lt(S.Guard.retries(guard), Gmm.max_retries()))
    case S.ContextSetup{+guard, ctx, nh, response, complete}:
      Gmm.retry_if(st, key, ue, guard, p, U32.is_lt(S.Guard.retries(guard), Gmm.max_retries()))
    case S.Registered{ctx, nh, released}:
      (S.Keep{}, [])
    case S.Switching{guard, ctx, nh, released}:
      Gmm.release(st, key, ue, N.Ngap.radio_cause(G.CauseRadioNetwork.unspecified()))
    case S.Handover{ctx, nh, source, leg}:
      Ho.Ho.expired(key, ue, ctx, nh, leg)
    case S.Releasing{guard}:
      N.Out.also(Gmm.forget(st, key), [N.Note{F.Warn{}, "NGAP: no UE Context Release Complete; UE context released"}])
