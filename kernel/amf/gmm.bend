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

# Registration (TS 24.501 §5.5.1, §5.4.1 to §5.4.3, §5.5.2) and UE context
# release (TS 38.413 §8.3.2, §8.3.3): the UE is identified by its SUCI,
# authenticated with 5G-AKA, given a NAS security context, set up at the gNB,
# accepted, and later released. Every outcome is a transaction on the state and
# a list of semantic actions (`N.Act`), applied and rendered at the boundary.

# T3570, T3560 and T3550 all default to 6 s.
def Gmm.guard_ms() -> U32:
  6000

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

# The UE security capability of the Registration Request held for the UE.
def Gmm.caps_of(r: Result<&2, &2, B.Err, Mm.Mm>) -> B.Bytes():
  match r:
    case Fail{e}:
      []
    case Done{Mm.Mm{mt, fields, opts}}:
      I.Bytes.or(I.Opts.find(46, opts), [])

def Gmm.caps(ue: S.Ue) -> B.Bytes():
  Gmm.caps_of(Mm.Mm.read(S.Ue.reg(ue)))

# Outcomes
# --------

def Gmm.dl(key: U32, +ue: S.Ue, nas: B.Bytes()) -> N.Act:
  N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), nas}

# Forgetting contexts
# -------------------

# A context forgotten, its sessions released at eUPF.
def Gmm.forget(+st: S.State, +key: U32) -> N.GOut():
  +gone = S.Sessions.of_ue(key, S.State.sessions(st))
  (S.Both{S.Del{key}, S.BumpSeq{Up.N4.deletion_count(gone)}}, Up.N4.deletions(gone, S.State.pfcp_seq(st)))

def Gmm.evict(victims: Tb.Table(S.Ue), +sessions: Tb.Table(S.Session), +seq: U32) -> N.GOut():
  match victims:
    case Nil{}:
      (S.Keep{}, [])
    case (+key, +v) <> more:
      +gone = S.Sessions.of_ue(key, sessions)
      +n = Up.N4.deletion_count(gone)
      N.Out.join((S.Both{S.Del{key}, S.BumpSeq{n}}, N.Release{S.Ue.assoc(v), S.Ue.stream(v), key, S.Ue.ran_id(v), N.Ngap.nas_cause(G.CauseNas.deregister())} <> Up.N4.deletions(gone, seq)), Gmm.evict(more, sessions, U32.add(seq, n)))

# The one write of a context's identity: it takes its place, and every live
# context it conflicts with (the same SUPI, 5G-TMSI or RAN id on the
# association) is released, sessions included, first.
def Gmm.place(+st: S.State, +key: U32, +ue: S.Ue) -> N.GOut():
  N.Out.join((S.Put{key, ue}, []), Gmm.evict(S.Ues.evicted(key, ue, S.State.ues(st)), S.State.sessions(st), S.State.pfcp_seq(st)))

# UE Context Release Command; the context waits, releasing, for the gNB.
def Gmm.release(st: S.State, +key: U32, +ue: S.Ue, cause: G.Cause) -> N.GOut():
  N.Out.prepend(N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause}, N.Out.also(Gmm.place(st, key, S.Ue.with_phase(ue, S.Releasing{})), N.Guard.cancel(S.Ue.guard(ue))))

def Gmm.reject(st: S.State, +key: U32, +ue: S.Ue, cause: U32) -> N.GOut():
  N.Out.prepend(Gmm.dl(key, ue, Gmm.registration_reject(cause)), Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified())))

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
  +timer = S.State.next_timer(st)
  +nas = Gmm.identity_request()
  +ue2 = S.Ue.with_dl(ue, S.Identifying{S.Guard{timer, 0}}, nas)
  N.Out.join(Gmm.place(st, key, ue2), (S.BumpTimer{}, [Gmm.dl(key, ue2, nas), N.TimerStart{timer, Gmm.guard_ms()}]))

# Authentication Request from a fresh vector, replacing any guard in force.
def Gmm.challenge(+st: S.State, +key: U32, +ue: S.Ue, +sub: Au.Subscriber, snn: B.Bytes(), entropy: B.Bytes(), resynced: Bool) -> N.GOut():
  +timer = S.State.next_timer(st)
  +sub2 = Au.Subscriber.with_sqn(sub, Au.Sqn.next(Au.Subscriber.sqn(sub)))
  +av = Au.Av.make(sub2, snn, List.take(&2, U32, entropy, 16n))
  +nas = Gmm.auth_request(0, av)
  +ue2 = S.Ue.with_dl(S.Ue.with_supi(ue, Au.Subscriber.supi(sub2)), S.Authenticating{S.Guard{timer, 0}, av, resynced}, nas)
  N.Out.join(Gmm.place(st, key, ue2), (S.Both{S.Subs{Au.Subscribers.update(sub2, S.State.subs(st))}, S.BumpTimer{}}, List.append(&2, N.Act, N.Guard.cancel(S.Ue.guard(ue)), [Gmm.dl(key, ue2, nas), N.TimerStart{timer, Gmm.guard_ms()}])))

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

# A new context, owned by the association, keyed by a fresh AMF-UE-NGAP-ID.
def Gmm.register(+st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), ran: B.Bytes(), nas: B.Bytes(), r: Mi.MobileId.Res()) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_nas(assoc))
    case Done{id}:
      N.Out.join((S.BumpUe{}, []), Gmm.proceed(st, S.State.next_ue(st), S.Ue{assoc, ran, stream, None{}, None{}, nas, 0, S.Releasing{}, []}, Gmm.start_of(id), entropy))

def Gmm.initial_mm(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), ran: B.Bytes(), nas: B.Bytes(), m: Mm.Mm) -> N.GOut():
  match m:
    case Mm.Mm{mt, fields, opts}:
      match mt:
        case Mm.RegistrationRequest{}:
          Gmm.register(st, assoc, stream, entropy, ran, nas, Mi.MobileId.read(I.Fields.lve2(fields)))
        case _:
          (S.Keep{}, N.Ngap.bad_nas(assoc))

def Gmm.initial_nas(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), ran: B.Bytes(), nas: B.Bytes(), r: Result<&2, &2, B.Err, Mm.Mm>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_nas(assoc))
    case Done{m}:
      Gmm.initial_mm(st, assoc, stream, entropy, ran, nas, m)

# InitialUEMessage: a context is created only once its Registration Request parses.
def Gmm.initial(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), v: V.InitialUEMessage.View) -> N.GOut():
  match v:
    case V.InitialUEMessage.View{ran_ue_ngap_id, +nas_pdu, userlocationinformation, rrcestablishmentcause, fiveg_s_tmsi, amfsetid, allowednssai, selectedplmnidentity, iabnodeindication, cemodebsupport_indicator, npn_accessinformation}:
      Gmm.initial_nas(st, assoc, stream, entropy, ran_ue_ngap_id, nas_pdu, Mm.Mm.read(nas_pdu))

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

# Security Mode Command, integrity protected with the new context, replacing the guard.
def Gmm.secure(+st: S.State, +key: U32, +ue: S.Ue, +k_amf: B.Bytes(), +ea: Sec.Nas.Ea, +ia: Sec.Nas.Ia, caps: B.Bytes()) -> N.GOut():
  +timer = S.State.next_timer(st)
  +ctx : Sec.Nas.Ctx = Sec.Ctx{Sec.Keys{Kd.kdf.k_nas_int(k_amf, Sec.Nas.Ia.id(ia)), Kd.kdf.k_nas_enc(k_amf, Sec.Nas.Ea.id(ea)), ea, ia, 1}, Sec.Nas.Count.zero(), None{}}
  +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.IntegrityNew{}, Gmm.security_mode_command(U32.or(U32.shln(Sec.Nas.Ea.id(ea), 4n), Sec.Nas.Ia.id(ia)), S.Ue.ngksi(ue), caps))
  +ue2 = S.Ue.with_dl(ue, S.SecurityMode{S.Guard{timer, 0}, Sec.Nas.Protected.ctx(p), k_amf}, Sec.Nas.Protected.msg(p))
  N.Out.join(Gmm.place(st, key, ue2), (S.BumpTimer{}, List.append(&2, N.Act, N.Guard.cancel(S.Ue.guard(ue)), [Gmm.dl(key, ue2, Sec.Nas.Protected.msg(p)), N.TimerStart{timer, Gmm.guard_ms()}])))

# No algorithm in common is a UE security capabilities mismatch (cause #23).
def Gmm.algorithms(st: S.State, key: U32, ue: S.Ue, k_amf: B.Bytes(), caps: B.Bytes(), mea: Maybe<&2, Sec.Nas.Ea>, mia: Maybe<&2, Sec.Nas.Ia>) -> N.GOut():
  match mea mia:
    case Some{ea} Some{ia}:
      Gmm.secure(st, key, ue, k_amf, ea, ia, caps)
    case _ _:
      Gmm.reject(st, key, ue, 23)

# Authentication
# --------------

def Gmm.keys(st: S.State, key: U32, +ue: S.Ue, av: Au.Av, cfg: Maybe<&2, S.Cfg>, supi: Maybe<&2, B.Digits()>) -> N.GOut():
  match cfg supi:
    case Some{+c} Some{s}:
      +caps = Gmm.caps(ue)
      Gmm.algorithms(st, key, ue, Au.Ausf.k_amf(av, Au.Ausf.snn(S.Cfg.plmn(c)), s), caps, Alg.pick_ea(S.Cfg.nea(c), N.Ngap.cap_byte(caps, 0n)), Alg.pick_ia(S.Cfg.nia(c), N.Ngap.cap_byte(caps, 1n)))
    case _ _:
      Gmm.auth_reject(st, key, ue)

def Gmm.verified(+st: S.State, key: U32, +ue: S.Ue, av: Au.Av, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.keys(st, key, ue, av, S.State.config(st), S.Ue.supi(ue))
    case False{}:
      Gmm.auth_reject(st, key, ue)

def Gmm.response(st: S.State, key: U32, ue: S.Ue, +av: Au.Av, res: Maybe<&2, B.Bytes()>) -> N.GOut():
  match res:
    case None{}:
      Gmm.auth_reject(st, key, ue)
    case Some{r}:
      Gmm.verified(st, key, ue, av, Au.Ausf.verify(av, r))

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

def Gmm.resync(+st: S.State, key: U32, ue: S.Ue, av: Au.Av, auts: B.Bytes(), entropy: B.Bytes(), cfg: Maybe<&2, S.Cfg>, supi: Maybe<&2, B.Digits()>) -> N.GOut():
  match cfg supi:
    case Some{+c} Some{s}:
      Gmm.resync_sub(st, key, ue, av, auts, entropy, c, Au.Subscribers.find(s, S.State.subs(st)))
    case _ _:
      Gmm.auth_reject(st, key, ue)

# Synch failure with an AUTS re-synchronises once; anything else rejects.
def Gmm.failure_kind(+st: S.State, key: U32, +ue: S.Ue, av: Au.Av, auts: Maybe<&2, B.Bytes()>, entropy: B.Bytes(), retry: Bool) -> N.GOut():
  match auts retry:
    case Some{a} True{}:
      Gmm.resync(st, key, ue, av, a, entropy, S.State.config(st), S.Ue.supi(ue))
    case _ _:
      Gmm.auth_reject(st, key, ue)

def Gmm.failure(st: S.State, key: U32, ue: S.Ue, av: Au.Av, resynced: Bool, cause: U32, auts: Maybe<&2, B.Bytes()>, entropy: B.Bytes()) -> N.GOut():
  Gmm.failure_kind(st, key, ue, av, auts, entropy, Bool.and(U32.is_eq(cause, 21), Bool.not(resynced)))

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
    case Mm.AuthenticationResponse{} S.Authenticating{guard, av, resynced}:
      Gmm.response(st, key, ue, av, I.Opts.find(45, opts))
    case Mm.AuthenticationFailure{} S.Authenticating{guard, av, resynced}:
      Gmm.failure(st, key, ue, av, resynced, I.Fields.byte1(fields), I.Opts.find(48, opts), entropy)
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

# Security Mode Complete: the Registration Request in its NAS message container
# replaces the initial one; the 5G-TMSI comes from entropy; KgNB from the
# uplink COUNT of this message; Initial Context Setup carries Registration
# Accept, ciphered, and T3550 guards it.
def Gmm.sm_complete(+st: S.State, +key: U32, +ue: S.Ue, guard: S.Guard, k_amf: B.Bytes(), ctx: Sec.Nas.Ctx, count: Sec.Nas.Count, opts: List<&2, I.Ie>, entropy: B.Bytes(), cfg: Maybe<&2, S.Cfg>) -> N.GOut():
  match cfg:
    case None{}:
      Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()))
    case Some{+c}:
      +timer = S.State.next_timer(st)
      +tmsi = N.Ngap.of_big(List.take(&2, U32, List.drop(&2, U32, entropy, 16n), 4n))
      +reg = I.Bytes.or(I.Opts.find(113, opts), S.Ue.reg(ue))
      +p : Sec.Nas.Protected = Sec.Nas.protect(ctx, Sec.Ciphered{}, Gmm.registration_accept(c, tmsi))
      +ue2 = S.Ue.with_tmsi(S.Ue.with_reg(S.Ue.with_dl(ue, S.ContextSetup{S.Guard{timer, 0}, Sec.Nas.Protected.ctx(p), False{}, False{}}, Sec.Nas.Protected.msg(p)), reg), tmsi)
      N.Out.join(Gmm.place(st, key, ue2), (S.BumpTimer{}, [N.TimerCancel{S.Guard.timer(guard)}, N.Ics{S.Ue.assoc(ue2), S.Ue.stream(ue2), key, S.Ue.ran_id(ue2), c, Gmm.caps(ue2), Kd.kdf.k_gnb(k_amf, Sec.Nas.Count.value(count)), Sec.Nas.Protected.msg(p)}, N.TimerStart{timer, Gmm.guard_ms()}]))

# Registered once both Initial Context Setup Response and Registration Complete are in.
def Gmm.setup_done(st: S.State, +key: U32, +ue: S.Ue, guard: S.Guard, ctx: Sec.Nas.Ctx, response: Bool, complete: Bool, both: Bool) -> N.GOut():
  match both:
    case True{}:
      (S.Rephase{key, S.Registered{ctx}}, [N.TimerCancel{S.Guard.timer(guard)}, N.Note{F.Info{}, "5GMM: UE registered"}])
    case False{}:
      (S.Rephase{key, S.ContextSetup{guard, ctx, response, complete}}, [])

def Gmm.setup_step(st: S.State, key: U32, ue: S.Ue, guard: S.Guard, ctx: Sec.Nas.Ctx, +response: Bool, +complete: Bool) -> N.GOut():
  Gmm.setup_done(st, key, ue, guard, ctx, response, complete, Bool.and(response, complete))

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
      Gmm.sm_complete(st, key, ue, guard, k_amf, ctx, count, opts, entropy, S.State.config(st))
    case Mm.SecurityModeReject{} S.SecurityMode{guard, old, k_amf}:
      Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()))
    case Mm.RegistrationComplete{} S.ContextSetup{guard, old, response, complete}:
      Gmm.setup_step(st, key, ue, guard, ctx, response, True{})
    case Mm.DeregistrationRequestUe{} S.ContextSetup{guard, old, response, complete}:
      Gmm.deregister(st, key, ue, ctx, I.Fields.byte1(fields))
    case Mm.DeregistrationRequestUe{} S.Registered{old}:
      Gmm.deregister(st, key, ue, ctx, I.Fields.byte1(fields))
    case Mm.UlNasTransport{} S.Registered{old}:
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

def Gmm.uplink(+st: S.State, +assoc: U32, stream: U32, entropy: B.Bytes(), v: V.UplinkNASTransport.View) -> N.GOut():
  match v:
    case V.UplinkNASTransport.View{amf_ue_ngap_id, ran_ue_ngap_id, nas_pdu, userlocationinformation}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Gmm.uplink_ue(st, assoc, key, nas_pdu, entropy, Gmm.owner(st, assoc, key, ran_ue_ngap_id))

def Gmm.uplink_of_view(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, V.UplinkNASTransport.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Gmm.uplink(st, assoc, stream, entropy, v)

def Gmm.setup_phase(st: S.State, key: U32, ue: S.Ue, p: S.Phase) -> N.GOut():
  match p:
    case S.ContextSetup{guard, ctx, response, complete}:
      Gmm.setup_step(st, key, ue, guard, ctx, True{}, complete)
    case _:
      N.Out.warn("NGAP: Initial Context Setup Response not expected in this phase")

def Gmm.ics_response_ue(st: S.State, assoc: U32, key: U32, m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{+ue}:
      Gmm.setup_phase(st, key, ue, S.Ue.phase(ue))

def Gmm.ics_response(+st: S.State, +assoc: U32, v: V.InitialContextSetupResponse.View) -> N.GOut():
  match v:
    case V.InitialContextSetupResponse.View{amf_ue_ngap_id, ran_ue_ngap_id, diagnostics}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Gmm.ics_response_ue(st, assoc, key, Gmm.owner(st, assoc, key, ran_ue_ngap_id))

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

def Gmm.release_request(+st: S.State, +assoc: U32, v: V.UEContextReleaseRequest.View) -> N.GOut():
  match v:
    case V.UEContextReleaseRequest.View{amf_ue_ngap_id, ran_ue_ngap_id, pdusessionresourcelistcxtrelreq, cause}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Gmm.release_request_ue(st, assoc, key, cause, Gmm.owner(st, assoc, key, ran_ue_ngap_id))

def Gmm.release_request_of_view(st: S.State, assoc: U32, r: Result<&2, &2, B.Err, V.UEContextReleaseRequest.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (S.Keep{}, N.Ngap.bad_view(assoc))
    case Done{v}:
      Gmm.release_request(st, assoc, v)

# UE Context Release Complete from the owner: the context is forgotten.
def Gmm.release_complete_ue(st: S.State, assoc: U32, key: U32, m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      (S.Keep{}, N.Ngap.unknown_ue(assoc))
    case Some{ue}:
      N.Out.also(Gmm.forget(st, key), [N.Note{F.Info{}, "NGAP: UE context released"}])

def Gmm.release_complete(+st: S.State, +assoc: U32, v: V.UEContextReleaseComplete.View) -> N.GOut():
  match v:
    case V.UEContextReleaseComplete.View{amf_ue_ngap_id, ran_ue_ngap_id, userlocationinformation, pdusessionresourcelistcxtrelcpl, diagnostics}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Gmm.release_complete_ue(st, assoc, key, Gmm.owner(st, assoc, key, ran_ue_ngap_id))

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
      (S.Rephase{key, S.Phase.with_guard(p, S.Guard{S.Guard.timer(guard), U32.add(S.Guard.retries(guard), 1)})}, [Gmm.dl(key, ue, S.Ue.last_dl(ue)), N.TimerStart{S.Guard.timer(guard), Gmm.guard_ms()}])
    case False{}:
      Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()))

# The guard fired: retransmit the last downlink message, or give up and release.
def Gmm.expired(st: S.State, key: U32, ue: S.Ue, +p: S.Phase) -> N.GOut():
  match p:
    case S.Identifying{+guard}:
      Gmm.retry_if(st, key, ue, guard, p, U32.is_lt(S.Guard.retries(guard), Gmm.max_retries()))
    case S.Authenticating{+guard, av, resynced}:
      Gmm.retry_if(st, key, ue, guard, p, U32.is_lt(S.Guard.retries(guard), Gmm.max_retries()))
    case S.SecurityMode{+guard, ctx, k_amf}:
      Gmm.retry_if(st, key, ue, guard, p, U32.is_lt(S.Guard.retries(guard), Gmm.max_retries()))
    case S.ContextSetup{+guard, ctx, response, complete}:
      Gmm.retry_if(st, key, ue, guard, p, U32.is_lt(S.Guard.retries(guard), Gmm.max_retries()))
    case S.Registered{ctx}:
      (S.Keep{}, [])
    case S.Releasing{}:
      (S.Keep{}, [])
