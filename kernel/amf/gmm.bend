import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as V
import ../nas/ie.bend as I
import ../nas/mm.bend as Mm
import ../nas/mobile_id.bend as Mi
import ../suci.bend as Su
import ../plmn.bend as P
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../ausf.bend as Au
import ./ngap.bend as N

# Registration, part 1 (TS 24.501 §5.5.1, §5.4.1, §5.4.3): the UE is
# identified by its SUCI, then authenticated with 5G-AKA. Every outcome is a
# state and a list of semantic actions (`N.Act`), rendered at the boundary.

def Gmm.t3560_ms() -> U32:
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

# The body of the second field when it is LV-E (the mobile identity of a
# Registration Request), of the first when it is LV-E (an Identity Response),
# and the first byte field (a cause).
def Gmm.field2(fields: List<&2, I.Field>) -> B.Bytes():
  match fields:
    case f1 <> I.FLvE{I.LenBody{len, body}} <> rest:
      body
    case _:
      []

def Gmm.field1(fields: List<&2, I.Field>) -> B.Bytes():
  match fields:
    case I.FLvE{I.LenBody{len, body}} <> rest:
      body
    case _:
      []

def Gmm.byte1(fields: List<&2, I.Field>) -> U32:
  match fields:
    case I.FByte{v} <> rest:
      v
    case _:
      0

def Gmm.opt_pick(body: B.Bytes(), later: Maybe<&2, B.Bytes()>, hit: Bool) -> Maybe<&2, B.Bytes()>:
  match hit:
    case True{}:
      Some{body}
    case False{}:
      later

def Gmm.opt(+iei: U32, opts: List<&2, I.Ie>) -> Maybe<&2, B.Bytes()>:
  match opts:
    case Nil{}:
      None{}
    case I.Ie{id, fmt, len, +body} <> more:
      Gmm.opt_pick(body, Gmm.opt(iei, more), U32.is_eq(id, iei))

# Outcomes
# --------

def Gmm.dl(key: U32, +ue: S.Ue, nas: B.Bytes()) -> N.Act:
  N.DlNas{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), nas}

def Gmm.cancel(g: Maybe<&2, S.Guard>) -> List<&2, N.Act>:
  match g:
    case None{}:
      []
    case Some{guard}:
      [N.TimerCancel{S.Guard.timer(guard)}]

def Gmm.prepend(a: N.Act, o: N.GOut()) -> N.GOut():
  match o:
    case (st, acts):
      (st, a <> acts)

# UE Context Release Command; the context waits, releasing, for the gNB.
def Gmm.release(st: S.State, +key: U32, +ue: S.Ue, cause: G.Cause) -> N.GOut():
  (S.State.put_ue(st, key, S.Ue.with_phase(ue, S.Releasing{})), N.Release{S.Ue.assoc(ue), S.Ue.stream(ue), key, S.Ue.ran_id(ue), cause} <> Gmm.cancel(S.Ue.guard(ue)))

def Gmm.reject(st: S.State, +key: U32, +ue: S.Ue, cause: U32) -> N.GOut():
  Gmm.prepend(Gmm.dl(key, ue, Gmm.registration_reject(cause)), Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified())))

def Gmm.auth_reject(st: S.State, +key: U32, +ue: S.Ue) -> N.GOut():
  Gmm.prepend(Gmm.dl(key, ue, Gmm.authentication_reject()), Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure())))

def Gmm.ignore(st: S.State, why: String) -> N.GOut():
  (st, [N.Note{F.Warn{}, why}])

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

def Gmm.identity_ask(r: Sigma<&2, &2, U32, _ => S.State>, +key: U32, ue: S.Ue) -> N.GOut():
  match r:
    case (+timer, st):
      +nas = Gmm.identity_request()
      +ue2 = S.Ue.with_dl(ue, S.Identifying{S.Guard{timer, 0}}, nas)
      (S.State.put_ue(st, key, ue2), [Gmm.dl(key, ue2, nas), N.TimerStart{timer, Gmm.t3560_ms()}])

# Authentication Request from a fresh vector, replacing any guard in force.
def Gmm.challenge(r: Sigma<&2, &2, U32, _ => S.State>, +key: U32, +ue: S.Ue, +sub: Au.Subscriber, snn: B.Bytes(), entropy: B.Bytes(), resynced: Bool) -> N.GOut():
  match r:
    case (+timer, +st):
      +sub2 = Au.Subscriber.with_sqn(sub, Au.Sqn.next(Au.Subscriber.sqn(sub)))
      +av = Au.Av.make(sub2, snn, List.take(&2, U32, entropy, 16n))
      +nas = Gmm.auth_request(0, av)
      +ue2 = S.Ue.with_dl(S.Ue.with_supi(ue, Au.Subscriber.supi(sub2)), S.Authenticating{S.Guard{timer, 0}, av, resynced}, nas)
      (S.State.put_ue(S.State.put_subs(st, Au.Subscribers.update(sub2, S.State.subs(st))), key, ue2), List.append(&2, N.Act, Gmm.cancel(S.Ue.guard(ue)), [Gmm.dl(key, ue2, nas), N.TimerStart{timer, Gmm.t3560_ms()}]))

def Gmm.by_sub(+st: S.State, key: U32, +ue: S.Ue, cfg: S.Cfg, m: Maybe<&2, Au.Subscriber>, entropy: B.Bytes()) -> N.GOut():
  match m:
    case None{}:
      Gmm.reject(st, key, ue, 7)
    case Some{sub}:
      Gmm.challenge(S.State.fresh_timer(st), key, ue, sub, Au.Ausf.snn(S.Cfg.plmn(cfg)), entropy, False{})

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
      Gmm.identity_ask(S.State.fresh_timer(st), key, ue)
    case Unknown{}:
      Gmm.reject(st, key, ue, 7)

# A new context, owned by the association, keyed by a fresh AMF-UE-NGAP-ID.
def Gmm.created(r: Sigma<&2, &2, U32, _ => S.State>, assoc: U32, stream: U32, ran: B.Bytes(), nas: B.Bytes(), how: Start, entropy: B.Bytes()) -> N.GOut():
  match r:
    case (+key, st):
      Gmm.proceed(st, key, S.Ue{assoc, ran, stream, None{}, nas, 0, S.Releasing{}, []}, how, entropy)

def Gmm.register(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), ran: B.Bytes(), nas: B.Bytes(), r: Mi.MobileId.Res()) -> N.GOut():
  match r:
    case Fail{e}:
      (st, N.Ngap.bad_nas(assoc))
    case Done{id}:
      Gmm.created(S.State.fresh_ue(st), assoc, stream, ran, nas, Gmm.start_of(id), entropy)

def Gmm.initial_mm(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), ran: B.Bytes(), nas: B.Bytes(), m: Mm.Mm) -> N.GOut():
  match m:
    case Mm.Mm{mt, fields, opts}:
      match mt:
        case Mm.RegistrationRequest{}:
          Gmm.register(st, assoc, stream, entropy, ran, nas, Mi.MobileId.read(Gmm.field2(fields)))
        case _:
          (st, N.Ngap.bad_nas(assoc))

def Gmm.initial_nas(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), ran: B.Bytes(), nas: B.Bytes(), r: Result<&2, &2, B.Err, Mm.Mm>) -> N.GOut():
  match r:
    case Fail{e}:
      (st, N.Ngap.bad_nas(assoc))
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
      (st, N.Ngap.bad_view_acts(assoc))
    case Done{v}:
      Gmm.initial(st, assoc, stream, entropy, v)

# Authentication
# --------------

def Gmm.keys(st: S.State, key: U32, +ue: S.Ue, guard: S.Guard, av: Au.Av, cfg: Maybe<&2, S.Cfg>, supi: Maybe<&2, B.Digits()>) -> N.GOut():
  match cfg supi:
    case Some{c} Some{s}:
      (S.State.put_ue(st, key, S.Ue.with_phase(ue, S.Authenticated{guard, Au.Ausf.k_amf(av, Au.Ausf.snn(S.Cfg.plmn(c)), s)})), [N.Note{F.Info{}, "5G-AKA: UE authenticated"}])
    case _ _:
      Gmm.auth_reject(st, key, ue)

def Gmm.verified(+st: S.State, key: U32, +ue: S.Ue, guard: S.Guard, av: Au.Av, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.keys(st, key, ue, guard, av, S.State.config(st), S.Ue.supi(ue))
    case False{}:
      Gmm.auth_reject(st, key, ue)

def Gmm.response(st: S.State, key: U32, ue: S.Ue, guard: S.Guard, +av: Au.Av, res: Maybe<&2, B.Bytes()>) -> N.GOut():
  match res:
    case None{}:
      Gmm.auth_reject(st, key, ue)
    case Some{r}:
      Gmm.verified(st, key, ue, guard, av, Au.Ausf.verify(av, r))

def Gmm.resynced(+st: S.State, key: U32, +ue: S.Ue, sub: Au.Subscriber, cfg: S.Cfg, entropy: B.Bytes(), m: Maybe<&2, B.Bytes()>) -> N.GOut():
  match m:
    case None{}:
      Gmm.auth_reject(st, key, ue)
    case Some{sqn_ms}:
      Gmm.challenge(S.State.fresh_timer(st), key, ue, Au.Subscriber.with_sqn(sub, sqn_ms), Au.Ausf.snn(S.Cfg.plmn(cfg)), entropy, True{})

def Gmm.resync_sub(+st: S.State, key: U32, +ue: S.Ue, av: Au.Av, auts: B.Bytes(), entropy: B.Bytes(), cfg: S.Cfg, m: Maybe<&2, Au.Subscriber>) -> N.GOut():
  match m:
    case None{}:
      Gmm.auth_reject(st, key, ue)
    case Some{+sub}:
      Gmm.resynced(st, key, ue, sub, cfg, entropy, Au.Ausf.resync(sub, Au.Av.rand(av), auts))

def Gmm.resync(+st: S.State, key: U32, +ue: S.Ue, av: Au.Av, auts: B.Bytes(), entropy: B.Bytes(), cfg: Maybe<&2, S.Cfg>, supi: Maybe<&2, B.Digits()>) -> N.GOut():
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

# A plain 5GMM message from a UE, read against its phase.
def Gmm.phase(st: S.State, key: U32, ue: S.Ue, entropy: B.Bytes(), mt: Mm.Mm.Type, fields: List<&2, I.Field>, opts: List<&2, I.Ie>, p: S.Phase) -> N.GOut():
  match mt p:
    case Mm.AuthenticationResponse{} S.Authenticating{guard, av, resynced}:
      Gmm.response(st, key, ue, guard, av, Gmm.opt(45, opts))
    case Mm.AuthenticationFailure{} S.Authenticating{guard, av, resynced}:
      Gmm.failure(st, key, ue, av, resynced, Gmm.byte1(fields), Gmm.opt(48, opts), entropy)
    case Mm.IdentityResponse{} S.Identifying{guard}:
      Gmm.identity_answer(st, key, ue, entropy, Mi.MobileId.read(Gmm.field1(fields)))
    case _ _:
      Gmm.ignore(st, "5GMM: message not expected in this phase")

def Gmm.mm(st: S.State, key: U32, +ue: S.Ue, entropy: B.Bytes(), r: Result<&2, &2, B.Err, Mm.Mm>) -> N.GOut():
  match r:
    case Fail{e}:
      Gmm.ignore(st, "5GMM: message not understood")
    case Done{Mm.Mm{mt, fields, opts}}:
      Gmm.phase(st, key, ue, entropy, mt, fields, opts, S.Ue.phase(ue))

def Gmm.owned(st: S.State, assoc: U32, key: U32, ue: S.Ue, nas: B.Bytes(), entropy: B.Bytes(), ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      Gmm.mm(st, key, ue, entropy, Mm.Mm.read(nas))
    case False{}:
      (st, N.Ngap.unknown_ue(assoc))

def Gmm.uplink_ue(st: S.State, +assoc: U32, key: U32, ran: B.Bytes(), nas: B.Bytes(), entropy: B.Bytes(), m: Maybe<&2, S.Ue>) -> N.GOut():
  match m:
    case None{}:
      (st, N.Ngap.unknown_ue(assoc))
    case Some{+ue}:
      Gmm.owned(st, assoc, key, ue, nas, entropy, Bool.and(U32.is_eq(S.Ue.assoc(ue), assoc), B.bytes_eq(S.Ue.ran_id(ue), ran)))

# UplinkNASTransport: only from the association that owns the UE, with its RAN id.
def Gmm.uplink(+st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), v: V.UplinkNASTransport.View) -> N.GOut():
  match v:
    case V.UplinkNASTransport.View{amf_ue_ngap_id, ran_ue_ngap_id, nas_pdu, userlocationinformation}:
      +key = N.Ngap.of_big(amf_ue_ngap_id)
      Gmm.uplink_ue(st, assoc, key, ran_ue_ngap_id, nas_pdu, entropy, Tb.Table.get(S.Ue, key, S.State.ues(st)))

def Gmm.uplink_of_view(st: S.State, assoc: U32, stream: U32, entropy: B.Bytes(), r: Result<&2, &2, B.Err, V.UplinkNASTransport.View>) -> N.GOut():
  match r:
    case Fail{e}:
      (st, N.Ngap.bad_view_acts(assoc))
    case Done{v}:
      Gmm.uplink(st, assoc, stream, entropy, v)

# Guard timers
# ------------

def Gmm.retry_if(st: S.State, +key: U32, +ue: S.Ue, +guard: S.Guard, p: S.Phase, ok: Bool) -> N.GOut():
  match ok:
    case True{}:
      +ue2 = S.Ue.with_phase(ue, S.Phase.with_guard(p, S.Guard{S.Guard.timer(guard), U32.add(S.Guard.retries(guard), 1)}))
      (S.State.put_ue(st, key, ue2), [Gmm.dl(key, ue2, S.Ue.last_dl(ue2)), N.TimerStart{S.Guard.timer(guard), Gmm.t3560_ms()}])
    case False{}:
      Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.authentication_failure()))

# The guard fired: retransmit, or give up and release.
def Gmm.expired(st: S.State, key: U32, ue: S.Ue, +p: S.Phase) -> N.GOut():
  match p:
    case S.Identifying{+guard}:
      Gmm.retry_if(st, key, ue, guard, p, U32.is_lt(S.Guard.retries(guard), Gmm.max_retries()))
    case S.Authenticating{+guard, av, resynced}:
      Gmm.retry_if(st, key, ue, guard, p, U32.is_lt(S.Guard.retries(guard), Gmm.max_retries()))
    case S.Authenticated{guard, k_amf}:
      Gmm.release(st, key, ue, N.Ngap.nas_cause(G.CauseNas.unspecified()))
    case S.Releasing{}:
      (st, [])

def Gmm.fired(st: S.State, m: Maybe<&2, Sigma<&2, &2, U32, _ => S.Ue>>) -> N.GOut():
  match m:
    case None{}:
      (st, [])
    case Some{(key, +ue)}:
      Gmm.expired(st, key, ue, S.Ue.phase(ue))

def Gmm.timer(+st: S.State, timer: U32) -> N.GOut():
  Gmm.fired(st, S.Ues.by_timer(timer, S.State.ues(st)))
