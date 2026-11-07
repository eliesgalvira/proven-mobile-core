import Base
import ../bytes.bend as B
import ../table.bend as Tb
import ../state.bend as S
import ../ngap/gen/types.bend as G
import ../frame.bend as F
import ../step.bend as K
import ../amf/ngap.bend as N
import ../smf/n4.bend as Up
import ../smf/switch.bend as Sw
import ../nas/security.bend as Sec
import ../aper.bend as Ap
import ../ngap/frame.bend as Fr
import ../ngap/gen/views.bend as V
import ../amf/route.bend as R
import ../amf/path_switch.bend as Ps
import ../LAWS.bend as L
import ./lib.bend as P
import ./walk.bend as PW
import ./takeover.bend as PT
import ./liveness.bend as PL

# Proofs of the Path Switch laws (ticket 27).

# The route
# ---------

# A Path Switch Request is handled by Ps.Ps.of_view.
def Psw.route(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 25, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == N.Step.of(st, Ps.Ps.of_view(st, assoc, stream, V.PathSwitchRequest.view(ies))) : N.Step()}:
  PW.Rt.routed(st, entropy, assoc, stream, len, bytes, 0, 25, crit, value, ies, c, ep, ei, {==}, eup)

def Psw.route_view(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +v: V.PathSwitchRequest.View, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 25, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +ev: {V.PathSwitchRequest.view(ies) == Done{v} : Result<&2, &2, B.Err, V.PathSwitchRequest.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == N.Step.of(st, Ps.Ps.of_view(st, assoc, stream, Done{v})) : N.Step()}:
  (%ev : {K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy) == N.Step.of(st, Ps.Ps.of_view(st, assoc, stream, _)) : N.Step()}; Psw.route(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, ep, ei, eup))

# Failure leaves the state
# ------------------------
# An outcome keeps the state, or none of its actions is a Path Switch Request
# Failure; nor is any guard stopped or Session Deletion that N.Step.of adds.

def Fl.as(o: N.GOut()) -> List<&2, N.Act>:
  match o:
    case (tx, acts):
      acts

def Fl.Cls(+o: N.GOut()) -> Data:
  Either<&2, &2, {PT.Tk.tx(o) == S.Keep{} : S.Tx}, {N.Ngap.any_switch_failure(Fl.as(o)) == False{} : Bool}>

def Fl.app(+xs: List<&2, N.Act>, +ys: List<&2, N.Act>, +hx: {N.Ngap.any_switch_failure(xs) == False{} : Bool}, +hy: {N.Ngap.any_switch_failure(ys) == False{} : Bool}) -> {N.Ngap.any_switch_failure(List.append(&2, N.Act, xs, ys)) == False{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      ea = Equal.sym(Bool, N.Ngap.is_switch_failure(a), False{}, P.Bool.or_false_l(N.Ngap.is_switch_failure(a), N.Ngap.any_switch_failure(more), hx))
      %ea : {Bool.or(_, N.Ngap.any_switch_failure(List.append(&2, N.Act, more, ys))) == False{} : Bool}
      Fl.app(more, ys, P.Bool.or_false_r(N.Ngap.is_switch_failure(a), N.Ngap.any_switch_failure(more), hx), hy)

def Fl.join(+a: N.GOut(), +b: N.GOut(), +ha: {N.Ngap.any_switch_failure(Fl.as(a)) == False{} : Bool}, +hb: {N.Ngap.any_switch_failure(Fl.as(b)) == False{} : Bool}) -> {N.Ngap.any_switch_failure(Fl.as(N.Out.join(a, b))) == False{} : Bool}:
  match a:
    case (+ta, +aa):
      match b:
        case (+tb, +ab):
          Fl.app(aa, ab, ha, hb)

def Fl.also(+o: N.GOut(), +more: List<&2, N.Act>, +h: {N.Ngap.any_switch_failure(Fl.as(o)) == False{} : Bool}, +hm: {N.Ngap.any_switch_failure(more) == False{} : Bool}) -> {N.Ngap.any_switch_failure(Fl.as(N.Out.also(o, more))) == False{} : Bool}:
  match o:
    case (+tx, +acts):
      Fl.app(acts, more, h, hm)

def Fl.del_if(+t: S.Session, +seq: U32, +more: Tb.Table(S.Session), +b: Bool, later: @q:U32 -> {N.Ngap.any_switch_failure(Up.N4.deletions(more, q)) == False{} : Bool}) -> {N.Ngap.any_switch_failure(Up.N4.delete_if(t, seq, q => Up.N4.deletions(more, q), b)) == False{} : Bool}:
  match b:
    case True{}:
      later(U32.add(seq, 1))
    case False{}:
      later(seq)

def Fl.dels(+rows: Tb.Table(S.Session), +seq: U32) -> {N.Ngap.any_switch_failure(Up.N4.deletions(rows, seq)) == False{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+key, +t) <> +more:
      Fl.del_if(t, seq, more, S.Session.known(t), +q => Fl.dels(more, q))

def Fl.cancel(+key: U32, +m: Maybe<&2, S.Guard>) -> {N.Ngap.any_switch_failure(N.Guard.cancel(key, m)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{g}:
      {==}

def Fl.row(+k: U32, +s: S.Session, +kept: Bool) -> {N.Ngap.any_switch_failure(N.Gone.row(k, s, kept)) == False{} : Bool}:
  match kept:
    case True{}:
      {==}
    case False{}:
      Fl.cancel(k, S.SPhase.guard(S.Session.phase(s)))

def Fl.cancels(+before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> {N.Ngap.any_switch_failure(N.Gone.cancels(before, after)) == False{} : Bool}:
  match before:
    case Nil{}:
      {==}
    case (+k, +s) <> +more:
      Fl.app(N.Gone.row(k, s, Tb.Table.has(S.Session, k, after)), N.Gone.cancels(more, after), Fl.row(k, s, Tb.Table.has(S.Session, k, after)), Fl.cancels(more, after))

def Fl.gone(+keeps: Bool, +before: Tb.Table(S.Session), +after: Tb.Table(S.Session)) -> {N.Ngap.any_switch_failure(N.Gone.when(keeps, before, after)) == False{} : Bool}:
  match keeps:
    case True{}:
      {==}
    case False{}:
      Fl.cancels(before, after)

def Fl.session(+skey: U32, +s: S.Session, +seq: U32, +t: Maybe<&2, Sigma<&2, &2, U32, _ => B.Bytes()>>) -> {N.Ngap.any_switch_failure(Fl.as(Sw.Sw.session(skey, s, seq, t))) == False{} : Bool}:
  match t:
    case None{}:
      Fl.dels([(skey, s)], seq)
    case Some{(teid, addr)}:
      {==}

def Fl.sessions(+ts: List<&2, S.Tunnel>, +rows: Tb.Table(S.Session), +seq: U32) -> {N.Ngap.any_switch_failure(Fl.as(Sw.Sw.sessions(ts, rows, seq))) == False{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case (+skey, +s) <> +more:
      +o = Sw.Sw.session(skey, s, seq, Sw.Sw.tunnel_for(ts, s))
      Fl.join(N.Out.join((S.BumpSeq{1}, []), o), Sw.Sw.sessions(ts, more, U32.add(seq, 1)), Fl.join((S.BumpSeq{1}, []), o, {==}, Fl.session(skey, s, seq, Sw.Sw.tunnel_for(ts, s))), Fl.sessions(ts, more, U32.add(seq, 1)))

def Fl.caps_same(+ok: Bool) -> {N.Ngap.any_switch_failure(Ps.Ps.caps_same(ok)) == False{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Fl.caps_note(+caps: G.UESecurityCapabilities, +m: Maybe<&2, N.Keyed()>) -> {N.Ngap.any_switch_failure(Ps.Ps.caps_note(caps, m)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{(+key, +ue)}:
      Fl.caps_same(B.bytes_eq(Ap.pack(G.UESecurityCapabilities.write(N.Ngap.ue_caps(N.Ue.caps(ue)), 0n, [])), Ap.pack(G.UESecurityCapabilities.write(caps, 0n, []))))

def Fl.go(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh) -> Fl.Cls(Ps.Ps.go(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, S.Sessions.of_ue(key, S.State.sessions(st)), True{})):
  +rows = S.Sessions.of_ue(key, S.State.sessions(st))
  +v = S.Ue.moved(ue, assoc, ran, stream, S.Switching{S.Guard{0}, ctx, S.Nh.next(nh), Sw.Sw.released(ts, rows)})
  +a = Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st))
  +b : N.GOut() = (S.Put{key, v}, [])
  +more : List<&2, N.Act> = [N.TimerStart{Some{key}, key, Ps.Ps.guard_ms()}, N.Note{F.Info{}, "NGAP: Path Switch Request; the UE moved, its PDU sessions being switched"}]
  Inr{Fl.also(N.Out.join(a, b), more, Fl.join(a, b, Fl.sessions(ts, rows, S.State.pfcp_seq(st)), {==}), {==})}

def Fl.also_cls(+o: N.GOut(), +more: List<&2, N.Act>, +h: Fl.Cls(o), +hm: {N.Ngap.any_switch_failure(more) == False{} : Bool}) -> Fl.Cls(N.Out.also(o, more)):
  match o:
    case (+tx, +acts):
      match h:
        case Inl{e}:
          Inl{e}
        case Inr{e}:
          Inr{Fl.app(acts, more, e, hm)}

def Fl.of_view(+st: S.State, +assoc: U32, +stream: U32, +r: Result<&2, &2, B.Err, V.PathSwitchRequest.View>) -> Fl.Cls(Ps.Ps.of_view(st, assoc, stream, r)):
  match r:
    case Fail{e}:
      Inl{{==}}
    case Done{V.PathSwitchRequest.View{+ran, +amf, uli, +caps, +items, failed, rrc}}:
      +ts = Sw.Sw.path_tunnels(items)
      +m = Ps.Ps.named(st, amf)
      +h = PW.Pw.claim(o => Fl.Cls(o), st, assoc, stream, amf, ran, items, ts, cause => Inl{{==}}, +key => +ue => +ctx => +nh => sp => ek => eg => es => Fl.go(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh))
      Fl.also_cls(Ps.Ps.claim(st, assoc, stream, amf, ran, items, ts, m), Ps.Ps.caps_note(caps, m), h, Fl.caps_note(caps, m))

def Fl.final(+st: S.State, +o: N.GOut(), +h: Fl.Cls(o), +ef: {N.Ngap.any_switch_failure(K.Kernel.actions(N.Step.of(st, o))) == True{} : Bool}) -> {K.Kernel.state(N.Step.of(st, o)) == st : S.State}:
  match o:
    case (+tx, +acts):
      match h:
        case Inl{e}:
          se = Equal.sym(S.Tx, tx, S.Keep{}, e)
          (%se : {S.Tx.apply(_, st) == st : S.State}; {==})
        case Inr{e}:
          +st2 = S.Tx.apply(tx, st)
          +gone = N.Gone.when(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(st2))
          nf = Fl.app(acts, gone, e, Fl.gone(S.Tx.keeps_sessions(tx), S.State.sessions(st), S.State.sessions(st2)))
          Empty.absurd({st2 == st : S.State}, P.Refute.true_false(Equal.trans(Bool, True{}, N.Ngap.any_switch_failure(List.append(&2, N.Act, acts, gone)), False{}, Equal.sym(Bool, N.Ngap.any_switch_failure(List.append(&2, N.Act, acts, gone)), True{}, ef), nf)))

def Fl.routed(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 25, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +ef: {N.Ngap.any_switch_failure(K.Kernel.actions(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy))) == True{} : Bool}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)) == st : S.State}:
  +o = Ps.Ps.of_view(st, assoc, stream, V.PathSwitchRequest.view(ies))
  +r = Psw.route(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, ep, ei, eup)
  sr = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy), N.Step.of(st, o), r)
  ef2 : {N.Ngap.any_switch_failure(K.Kernel.actions(N.Step.of(st, o))) == True{} : Bool} = (%r : {N.Ngap.any_switch_failure(K.Kernel.actions(_)) == True{} : Bool}; ef)
  %sr : {K.Kernel.state(_) == st : S.State}
  Fl.final(st, o, Fl.of_view(st, assoc, stream, V.PathSwitchRequest.view(ies)), ef2)

def L.amf.path_switch.failure_leaves_state(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, ep, ei, ef):
  PW.Rt.keeps(st, entropy, assoc, stream, len, bytes, 0, 25, crit, value, ies, c, ep, ei, {==}, +eup => Fl.routed(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, ep, ei, ef, eup))

# The context moves to the requester
# ----------------------------------

def Mv.Qu(+st: S.State, +k: U32, +assoc: U32, +ran: B.Bytes(), +t: Tb.Table(S.Ue)) -> Type:
  {Tb.Table.get(S.Ue, k, t) == Tb.Table.get(S.Ue, k, S.State.ues(st)) : Maybe<&2, S.Ue>} | ({Tb.Table.has(S.Ue, k, t) == True{} : Bool} & {N.Owner.of(Tb.Table.get(S.Ue, k, t), assoc, ran) == Tb.Table.get(S.Ue, k, t) : Maybe<&2, S.Ue>})

def Mv.Qt(+st: S.State, +k: U32, +assoc: U32, +ran: B.Bytes(), +tx: S.Tx) -> Type:
  Mv.Qu(st, k, assoc, ran, PT.Tk.ues(tx, S.State.ues(st)))

def Mv.get_put(+key: U32, +v: S.Ue, +x: Tb.Table(S.Ue)) -> {Tb.Table.get(S.Ue, key, S.Ues.put(key, v, x)) == Some{v} : Maybe<&2, S.Ue>}:
  e = Equal.sym(Bool, U32.is_eq(key, key), True{}, P.U32.is_eq_refl(key))
  (%e : {Tb.Table.hit(S.Ue, v, Tb.Table.get(S.Ue, key, S.Ues.sift(S.Clear{key, v}, x)), _) == Some{v} : Maybe<&2, S.Ue>}; {==})

def Mv.owner(+ue: S.Ue, +a: U32, +r: B.Bytes(), +s: U32, +p: S.Phase) -> {N.Owner.of(Some{S.Ue.moved(ue, a, r, s, p)}, a, r) == Some{S.Ue.moved(ue, a, r, s, p)} : Maybe<&2, S.Ue>}:
  match ue:
    case S.Ue{assoc, ran_id, stream, supi, tmsi, reg, ngksi, phase, last_dl}:
      +w : S.Ue = S.Ue{a, r, s, supi, tmsi, reg, ngksi, p, last_dl}
      ea = Equal.sym(Bool, U32.is_eq(a, a), True{}, P.U32.is_eq_refl(a))
      %ea : {N.Owner.check(w, Bool.and(_, B.bytes_eq(r, r))) == Some{w} : Maybe<&2, S.Ue>}
      er = Equal.sym(Bool, B.bytes_eq(r, r), True{}, P.Bytes.eq_refl(r))
      %er : {N.Owner.check(w, Bool.and(True{}, _)) == Some{w} : Maybe<&2, S.Ue>}
      {==}

def Mv.put(+key: U32, +ue: S.Ue, +a: U32, +r: B.Bytes(), +s: U32, +p: S.Phase, +x: Tb.Table(S.Ue)) -> {Tb.Table.has(S.Ue, key, S.Ues.put(key, S.Ue.moved(ue, a, r, s, p), x)) == True{} : Bool} & {N.Owner.of(Tb.Table.get(S.Ue, key, S.Ues.put(key, S.Ue.moved(ue, a, r, s, p), x)), a, r) == Tb.Table.get(S.Ue, key, S.Ues.put(key, S.Ue.moved(ue, a, r, s, p), x)) : Maybe<&2, S.Ue>}:
  +v = S.Ue.moved(ue, a, r, s, p)
  seg = Equal.sym(Maybe<&2, S.Ue>, Tb.Table.get(S.Ue, key, S.Ues.put(key, v, x)), Some{v}, Mv.get_put(key, v, x))
  %seg : {Tb.Table.present(S.Ue, _) == True{} : Bool} & {N.Owner.of(_, a, r) == _ : Maybe<&2, S.Ue>}
  ({==}, Mv.owner(ue, a, r, s, p))

def Mv.go(+st: S.State, +assoc: U32, +stream: U32, +amf: B.Bytes(), +ran: B.Bytes(), +items: G.PDUSessionResourceToBeSwitchedDLList(), +ts: List<&2, S.Tunnel>, +k: U32, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +key: U32, +ue: S.Ue, +ctx: Sec.Nas.Ctx, +nh: S.Nh, +ek: {N.Ngap.ue_key(amf) == Some{key} : Maybe<&2, U32>}) -> Mv.Qt(st, k, assoc, ran, PT.Tk.tx(Ps.Ps.go(st, assoc, stream, amf, ran, items, ts, key, ue, ctx, nh, S.Sessions.of_ue(key, S.State.sessions(st)), True{}))):
  +rows = S.Sessions.of_ue(key, S.State.sessions(st))
  +p : S.Phase = S.Switching{S.Guard{0}, ctx, S.Nh.next(nh), Sw.Sw.released(ts, rows)}
  +v = S.Ue.moved(ue, assoc, ran, stream, p)
  +a = Sw.Sw.sessions(ts, rows, S.State.pfcp_seq(st))
  +b : N.GOut() = (S.Put{key, v}, [])
  +more : List<&2, N.Act> = [N.TimerStart{Some{key}, key, Ps.Ps.guard_ms()}, N.Note{F.Info{}, "NGAP: Path Switch Request; the UE moved, its PDU sessions being switched"}]
  e12 = Equal.trans(S.Tx, PT.Tk.tx(N.Out.also(N.Out.join(a, b), more)), PT.Tk.tx(N.Out.join(a, b)), S.Both{PT.Tk.tx(a), S.Put{key, v}}, PL.Lv.tx_also(N.Out.join(a, b), more), PT.Tk.tx_join(a, b))
  se = Equal.sym(S.Tx, PT.Tk.tx(N.Out.also(N.Out.join(a, b), more)), S.Both{PT.Tk.tx(a), S.Put{key, v}}, e12)
  %se : Mv.Qt(st, k, assoc, ran, _)
  ekk = P.Some.inj(U32, key, k, Equal.trans(Maybe<&2, U32>, Some{key}, N.Ngap.ue_key(amf), Some{k}, Equal.sym(Maybe<&2, U32>, N.Ngap.ue_key(amf), Some{key}, ek), eid))
  %ekk : Mv.Qt(st, _, assoc, ran, S.Both{PT.Tk.tx(a), S.Put{key, v}})
  Inr{Mv.put(key, ue, assoc, ran, stream, p, PT.Tk.ues(PT.Tk.tx(a), S.State.ues(st)))}

def Mv.routed(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len: U32, +bytes: B.Bytes(), +crit: U32, +value: B.Bytes(), +ies: List<&2, Fr.Ie>, +c: Ap.Cur, +ran: B.Bytes(), +amf: B.Bytes(), +uli: G.UserLocationInformation, +caps: G.UESecurityCapabilities, +items: G.PDUSessionResourceToBeSwitchedDLList(), +failed: Maybe<&2, G.PDUSessionResourceFailedToSetupListPSReq()>, +rrc: Maybe<&2, G.RRCEstablishmentCause()>, +k: U32, +ep: {Fr.Pdu.read(bytes) == Done{Fr.Pdu{0, 25, crit, value}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value), 1n)}) == Done{(ies, c)} : Ap.Rd(List<&2, Fr.Ie>)}, +ev: {V.PathSwitchRequest.view(ies) == Done{V.PathSwitchRequest.View{ran, amf, uli, caps, items, failed, rrc}} : Result<&2, &2, B.Err, V.PathSwitchRequest.View>}, +eid: {N.Ngap.ue_key(amf) == Some{k} : Maybe<&2, U32>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> Mv.Qu(st, k, assoc, ran, S.State.ues(K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)))):
  +v : V.PathSwitchRequest.View = V.PathSwitchRequest.View{ran, amf, uli, caps, items, failed, rrc}
  +o = Ps.Ps.of_view(st, assoc, stream, Done{v})
  +ts = Sw.Sw.path_tunnels(items)
  +rr = Ps.Ps.claim(st, assoc, stream, amf, ran, items, ts, Ps.Ps.named(st, amf))
  +n = Ps.Ps.caps_note(caps, Ps.Ps.named(st, amf))
  +step = K.Kernel.step(st, F.NgapData{assoc, stream, len, bytes}, entropy)
  sr = Equal.sym(N.Step(), step, N.Step.of(st, o), Psw.route_view(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, v, ep, ei, ev, eup))
  eu : {S.State.ues(K.Kernel.state(step)) == PT.Tk.ues(PT.Tk.tx(o), S.State.ues(st)) : Tb.Table(S.Ue)} = (%sr : {S.State.ues(K.Kernel.state(_)) == PT.Tk.ues(PT.Tk.tx(o), S.State.ues(st)) : Tb.Table(S.Ue)}; PT.Tk.render(st, o))
  seu = Equal.sym(Tb.Table(S.Ue), S.State.ues(K.Kernel.state(step)), PT.Tk.ues(PT.Tk.tx(o), S.State.ues(st)), eu)
  %seu : Mv.Qu(st, k, assoc, ran, _)
  sa = Equal.sym(S.Tx, PT.Tk.tx(N.Out.also(rr, n)), PT.Tk.tx(rr), PL.Lv.tx_also(rr, n))
  %sa : Mv.Qt(st, k, assoc, ran, _)
  PW.Pw.claim(x => Mv.Qt(st, k, assoc, ran, PT.Tk.tx(x)), st, assoc, stream, amf, ran, items, ts, cause => Inl{{==}}, +key => +ue => +ctx => +nh => sp => ek => eg => es => Mv.go(st, assoc, stream, amf, ran, items, ts, k, eid, key, ue, ctx, nh, ek))

def L.amf.path_switch.moves_owner(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, ran, amf, uli, caps, items, failed, rrc, k, ep, ei, ev, eid):
  PW.Rt.cases(x => Mv.Qu(st, k, assoc, ran, S.State.ues(K.Kernel.state(x))), st, entropy, assoc, stream, len, bytes, 0, 25, crit, value, ies, c, ep, ei, {==}, Inl{{==}}, +eup => Mv.routed(st, entropy, assoc, stream, len, bytes, crit, value, ies, c, ran, amf, uli, caps, items, failed, rrc, k, ep, ei, ev, eid, eup))

# The request's capabilities change nothing
# -----------------------------------------

def Psw.also_state(+st: S.State, +o: N.GOut(), +n: List<&2, N.Act>) -> {K.Kernel.state(N.Step.of(st, N.Out.also(o, n))) == K.Kernel.state(N.Step.of(st, o)) : S.State}:
  match o:
    case (tx, acts):
      {==}

def Psw.same_state(+st: S.State, +entropy: B.Bytes(), +assoc: U32, +stream: U32, +len1: U32, +bytes1: B.Bytes(), +crit1: U32, +value1: B.Bytes(), +ies1: List<&2, Fr.Ie>, +c1: Ap.Cur, +len2: U32, +bytes2: B.Bytes(), +crit2: U32, +value2: B.Bytes(), +ies2: List<&2, Fr.Ie>, +c2: Ap.Cur, +ran: B.Bytes(), +amf: B.Bytes(), +uli: G.UserLocationInformation, +caps1: G.UESecurityCapabilities, +caps2: G.UESecurityCapabilities, +items: G.PDUSessionResourceToBeSwitchedDLList(), +failed: Maybe<&2, G.PDUSessionResourceFailedToSetupListPSReq()>, +rrc: Maybe<&2, G.RRCEstablishmentCause()>, +ep1: {Fr.Pdu.read(bytes1) == Done{Fr.Pdu{0, 25, crit1, value1}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei1: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value1), 1n)}) == Done{(ies1, c1)} : Ap.Rd(List<&2, Fr.Ie>)}, +ev1: {V.PathSwitchRequest.view(ies1) == Done{V.PathSwitchRequest.View{ran, amf, uli, caps1, items, failed, rrc}} : Result<&2, &2, B.Err, V.PathSwitchRequest.View>}, +ep2: {Fr.Pdu.read(bytes2) == Done{Fr.Pdu{0, 25, crit2, value2}} : Result<&2, &2, B.Err, Fr.Pdu>}, +ei2: {Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(value2), 1n)}) == Done{(ies2, c2)} : Ap.Rd(List<&2, Fr.Ie>)}, +ev2: {V.PathSwitchRequest.view(ies2) == Done{V.PathSwitchRequest.View{ran, amf, uli, caps2, items, failed, rrc}} : Result<&2, &2, B.Err, V.PathSwitchRequest.View>}, +eup: {S.Assocs.has(assoc, S.State.assocs(st)) == True{} : Bool}) -> {K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len1, bytes1}, entropy)) == K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len2, bytes2}, entropy)) : S.State}:
  +v1 : V.PathSwitchRequest.View = V.PathSwitchRequest.View{ran, amf, uli, caps1, items, failed, rrc}
  +v2 : V.PathSwitchRequest.View = V.PathSwitchRequest.View{ran, amf, uli, caps2, items, failed, rrc}
  +rr = Ps.Ps.claim(st, assoc, stream, amf, ran, items, Sw.Sw.path_tunnels(items), Ps.Ps.named(st, amf))
  +n1 = Ps.Ps.caps_note(caps1, Ps.Ps.named(st, amf))
  +n2 = Ps.Ps.caps_note(caps2, Ps.Ps.named(st, amf))
  +step2 = K.Kernel.step(st, F.NgapData{assoc, stream, len2, bytes2}, entropy)
  s1 = Equal.sym(N.Step(), K.Kernel.step(st, F.NgapData{assoc, stream, len1, bytes1}, entropy), N.Step.of(st, Ps.Ps.of_view(st, assoc, stream, Done{v1})), Psw.route_view(st, entropy, assoc, stream, len1, bytes1, crit1, value1, ies1, c1, v1, ep1, ei1, ev1, eup))
  %s1 : {K.Kernel.state(_) == K.Kernel.state(step2) : S.State}
  s2 = Equal.sym(N.Step(), step2, N.Step.of(st, Ps.Ps.of_view(st, assoc, stream, Done{v2})), Psw.route_view(st, entropy, assoc, stream, len2, bytes2, crit2, value2, ies2, c2, v2, ep2, ei2, ev2, eup))
  %s2 : {K.Kernel.state(N.Step.of(st, Ps.Ps.of_view(st, assoc, stream, Done{v1}))) == K.Kernel.state(_) : S.State}
  Equal.trans(S.State, K.Kernel.state(N.Step.of(st, N.Out.also(rr, n1))), K.Kernel.state(N.Step.of(st, rr)), K.Kernel.state(N.Step.of(st, N.Out.also(rr, n2))), Psw.also_state(st, rr, n1), Equal.sym(S.State, K.Kernel.state(N.Step.of(st, N.Out.also(rr, n2))), K.Kernel.state(N.Step.of(st, rr)), Psw.also_state(st, rr, n2)))

def L.amf.path_switch.stored_capabilities(st, entropy, assoc, stream, len1, bytes1, crit1, value1, ies1, c1, len2, bytes2, crit2, value2, ies2, c2, ran, amf, uli, caps1, caps2, items, failed, rrc, key, ue, ctx, nh, released, p, more, cfg, ep1, ei1, ev1, ep2, ei2, ev2):
  (PW.Rt.split({K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len1, bytes1}, entropy)) == K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len2, bytes2}, entropy)) : S.State}, assoc, S.State.assocs(st), +ea => PW.Rt.at(x => {K.Kernel.state(x) == K.Kernel.state(K.Kernel.step(st, F.NgapData{assoc, stream, len2, bytes2}, entropy)) : S.State}, st, entropy, assoc, stream, len1, bytes1, 0, 25, crit1, value1, ies1, c1, ep1, ei1, {==}, ea, PW.Rt.at(x => {st == K.Kernel.state(x) : S.State}, st, entropy, assoc, stream, len2, bytes2, 0, 25, crit2, value2, ies2, c2, ep2, ei2, {==}, ea, {==})), +eup => Psw.same_state(st, entropy, assoc, stream, len1, bytes1, crit1, value1, ies1, c1, len2, bytes2, crit2, value2, ies2, c2, ran, amf, uli, caps1, caps2, items, failed, rrc, ep1, ei1, ev1, ep2, ei2, ev2, eup)), {==})
