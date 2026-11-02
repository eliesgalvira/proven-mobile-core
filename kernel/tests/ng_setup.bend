import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../tlv.bend as T
import ../pfcp.bend as Pf
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as W
import ../frame.bend as F
import ../state.bend as S
import ../step.bend as K
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture

# Drives step with Config, NgapAssocUp and the captured NG Setup Request: the
# answer is the captured NG Setup Response, byte for byte. Then the failure
# cases: an unsupported TAC, no configuration, an undecodable PDU, an
# incomplete Config; and an association going down releases its UEs.

def entropy() -> B.Bytes():
  [45, 202, 228, 29, 52, 210, 168, 148, 210, 151, 160, 24, 229, 85, 66, 153, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def sixteen() -> B.Bytes():
  [70, 91, 92, 232, 177, 153, 180, 159, 170, 95, 10, 46, 226, 56, 166, 188]

def subscriber() -> B.Bytes():
  F.Sub.write(F.Sub{[48, 48, 49, 48, 49, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49], sixteen(), [232, 237, 40, 157, 235, 169, 82, 228, 40, 59, 84, 232, 142, 97, 131, 202], [128, 0], [0, 0, 0, 0, 0, 64]})

def key32() -> B.Bytes():
  [88, 47, 147, 31, 207, 143, 43, 127, 145, 29, 235, 182, 34, 79, 113, 231, 43, 157, 74, 98, 238, 211, 141, 18, 159, 253, 119, 140, 48, 22, 211, 106]

# The capture's network (test-vectors/capture/vectors.json § network), with a TAC of choice.
def config(tac: B.Bytes()) -> List<&2, T.Tlv>:
  [T.Tlv.make(1, [0, 241, 16]), T.Tlv.make(2, [2]), T.Tlv.make(3, [0, 1]), T.Tlv.make(4, [0]), T.Tlv.make(5, tac), T.Tlv.make(6, [115, 112, 101, 99, 107, 45, 97, 109, 102, 48]), T.Tlv.make(7, [1]), T.Tlv.make(8, [105, 110, 116, 101, 114, 110, 101, 116]), T.Tlv.make(9, [10, 45, 0, 0]), T.Tlv.make(10, [16]), T.Tlv.make(11, [8, 8, 8, 8]), T.Tlv.make(12, [10, 33, 0, 12]), T.Tlv.make(13, [10, 33, 0, 20]), T.Tlv.make(14, [10, 33, 0, 20]), T.Tlv.make(15, key32()), T.Tlv.make(16, [1]), T.Tlv.make(17, [0]), T.Tlv.make(18, [2]), T.Tlv.make(32, subscriber())]

def config_event(tac: B.Bytes()) -> F.Evt:
  F.Evt.config_make(config(tac))

def data_event(assoc: U32, bytes: B.Bytes()) -> F.Evt:
  F.Evt.data_make(assoc, 0, bytes)

# The capture
# -----------

def keep(+m: V.Vec, hit: Bool, rest: Maybe<&2, B.Bytes()>) -> Maybe<&2, B.Bytes()>:
  match hit:
    case True{}:
      Some{V.Vec.bytes(V.Vec.field(m, "hex"))}
    case False{}:
      rest

def first_of(+name: String, msgs: List<&2, V.Vec>) -> Maybe<&2, B.Bytes()>:
  match msgs:
    case Nil{}:
      None{}
    case +m <> rest:
      keep(m, String.eq(V.Vec.text(V.Vec.field(m, "message")), name), first_of(name, rest))

def bytes_or(m: Maybe<&2, B.Bytes()>) -> B.Bytes():
  match m:
    case None{}:
      []
    case Some{bs}:
      bs

# Looking at actions
# ------------------

def sends_keep(a: F.Action, more: List<&2, F.Action>) -> List<&2, F.Action>:
  match a:
    case F.NgapSend{assoc, stream, len, bytes}:
      F.NgapSend{assoc, stream, len, bytes} <> more
    case _:
      more

def sends(actions: List<&2, F.Action>) -> List<&2, F.Action>:
  match actions:
    case Nil{}:
      []
    case a <> more:
      sends_keep(a, sends(more))

def pfcp_keep(a: F.Action, more: List<&2, B.Bytes()>) -> List<&2, B.Bytes()>:
  match a:
    case F.PfcpSend{len, bytes}:
      bytes <> more
    case _:
      more

def pfcp_sends(actions: List<&2, F.Action>) -> List<&2, B.Bytes()>:
  match actions:
    case Nil{}:
      []
    case a <> more:
      pfcp_keep(a, pfcp_sends(more))

def count_logs(actions: List<&2, F.Action>) -> Nat:
  match actions:
    case Nil{}:
      0n
    case F.Log{level, len, text} <> more:
      1n+count_logs(more)
    case a <> more:
      count_logs(more)

def one_of(ss: List<&2, F.Action>) -> Maybe<&2, F.Action>:
  match ss:
    case F.NgapSend{assoc, stream, len, bytes} <> Nil{}:
      Some{F.NgapSend{assoc, stream, len, bytes}}
    case _:
      None{}

def one_send(actions: List<&2, F.Action>) -> Maybe<&2, F.Action>:
  one_of(sends(actions))

def bool_eq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def bits_eq(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yt:
      False{}
    case x <> xt Nil{}:
      False{}
    case +x <> xt +y <> yt:
      Bool.and(bool_eq(x, y), bits_eq(xt, yt))

def send_bytes(a: Maybe<&2, F.Action>) -> B.Bytes():
  match a:
    case Some{F.NgapSend{assoc, stream, len, bytes}}:
      bytes
    case _:
      []

def send_on(a: Maybe<&2, F.Action>, +assoc: U32, +stream: U32) -> Bool:
  match a:
    case Some{F.NgapSend{a2, s2, len, bytes}}:
      Bool.and(U32.is_eq(a2, assoc), U32.is_eq(s2, stream))
    case _:
      False{}

def pdu_is(r: Result<&2, &2, B.Err, Fr.Pdu>, +kind: U32, +code: U32) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{+p}:
      Bool.and(U32.is_eq(Fr.Pdu.kind(p), kind), U32.is_eq(Fr.Pdu.code(p), code))

def ies_rd(r: Ap.Rd(List<&2, Fr.Ie>)) -> List<&2, Fr.Ie>:
  match r:
    case Fail{e}:
      []
    case Done{(ies, c)}:
      ies

def ies_of(r: Result<&2, &2, B.Err, Fr.Pdu>) -> List<&2, Fr.Ie>:
  match r:
    case Fail{e}:
      []
    case Done{p}:
      ies_rd(Fr.Ies.read(Ap.Cur{7n, List.drop(&2, Bool, Ap.unpack(Fr.Pdu.value(p)), 1n)}))

def guami_ok(r: Result<&2, &2, B.Err, W.NGSetupResponse.View>) -> Bool:
  match r:
    case Done{W.NGSetupResponse.View{amfname, G.ServedGUAMIItem{G.GUAMI{plmn, region, set_id, pointer, ext}, backup, ext2} <> Nil{}, capacity, plmns}}:
      Bool.and(B.bytes_eq(plmn, [0, 241, 16]), Bool.and(bits_eq(region, Ap.unpack([2])), Bool.and(Nat.is_eq(List.length(&2, Bool, set_id), 10n), B.bytes_eq(amfname, [115, 112, 101, 99, 107, 45, 97, 109, 102, 48]))))
    case _:
      False{}

def Tb_present(m: Maybe<&2, B.Bytes()>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def pfcp_type(r: B.Read(Pf.Msg), +kind: U32, with_seid: Bool) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(+m, rest)}:
      Bool.and(U32.is_eq(Pf.Msg.kind(m), kind), Bool.and(bool_eq(Tb_present(Pf.Msg.seid(m)), with_seid), B.bytes_eq(rest, [])))

def first_pfcp(bs: List<&2, B.Bytes()>) -> B.Bytes():
  match bs:
    case Nil{}:
      []
    case b <> more:
      b

def Tb_present_cfg(m: Maybe<&2, S.Cfg>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      True{}

def configured(st: S.State) -> Bool:
  Tb_present_cfg(S.State.config(st))

def Tb_keys(t: List<&2, Sigma<&2, &2, U32, _ => S.Ue>>) -> List<&2, U32>:
  match t:
    case Nil{}:
      []
    case (k, u) <> more:
      k <> Tb_keys(more)

def ue_keys(st: S.State) -> List<&2, U32>:
  Tb_keys(S.State.ues(st))

def with_ues(st: S.State, ues: List<&2, Sigma<&2, &2, U32, _ => S.Ue>>, sessions: List<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> S.State:
  match st:
    case S.State{config, assocs, old_ues, old_sessions, pfcp_seq, next_ue, next_timer, recovery}:
      S.State{config, assocs, ues, sessions, pfcp_seq, next_ue, next_timer, recovery}

def main() -> IO(Unit):
  do IO<Unit>:
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    +request : B.Bytes() = bytes_or(first_of("NGSetupRequest", msgs))
    +response : B.Bytes() = bytes_or(first_of("NGSetupResponse", msgs))
    +o1 : S.Out() = K.Kernel.step(S.State.initial(), config_event([0, 0, 1]), entropy())
    +st1 : S.State = K.Kernel.state(o1)
    +a1 : List<&2, F.Action> = K.Kernel.actions(o1)
    +st2 : S.State = K.Kernel.state(K.Kernel.step(st1, F.NgapAssocUp{1}, entropy()))
    +o3 : S.Out() = K.Kernel.step(st2, data_event(1, request), entropy())
    +a3 : List<&2, F.Action> = K.Kernel.actions(o3)
    +reply : B.Bytes() = send_bytes(one_send(a3))
    C.Check.report("Config: the configuration is kept", configured(st1))
    C.Check.report("Config: a PFCP Association Setup Request goes to eUPF", pfcp_type(Pf.Msg.read(first_pfcp(pfcp_sends(a1))), 5, False{}))
    C.Check.report("NgapAssocUp: the association is known", S.Assocs.has(1, S.State.assocs(st2)))
    C.Check.report("NG Setup Request: exactly one NGAP message answers, on stream 0", send_on(one_send(a3), 1, 0))
    C.Check.report("NG Setup Request: the answer is an NG Setup Response", pdu_is(Fr.Pdu.read(reply), Fr.Pdu.successful(), 21))
    C.Check.report("NG Setup Request: the response carries the configured GUAMI and AMF name", guami_ok(W.NGSetupResponse.view(ies_of(Fr.Pdu.read(reply)))))
    C.Check.report("NG Setup Request: the response is the captured one, byte for byte", B.bytes_eq(reply, response))
    C.Check.report("NG Setup Request: no state changes", Nat.is_eq(List.length(&2, U32, ue_keys(K.Kernel.state(o3))), 0n))
    +st_tac : S.State = K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(S.State.initial(), config_event([0, 0, 2]), entropy())), F.NgapAssocUp{1}, entropy()))
    +reply_tac : B.Bytes() = send_bytes(one_send(K.Kernel.actions(K.Kernel.step(st_tac, data_event(1, request), entropy()))))
    C.Check.report("NG Setup Request for another TAC: NG Setup Failure", pdu_is(Fr.Pdu.read(reply_tac), Fr.Pdu.unsuccessful(), 21))
    +reply_none : B.Bytes() = send_bytes(one_send(K.Kernel.actions(K.Kernel.step(S.State.initial(), data_event(1, request), entropy()))))
    C.Check.report("NG Setup Request before Config: NG Setup Failure", pdu_is(Fr.Pdu.read(reply_none), Fr.Pdu.unsuccessful(), 21))
    +o_bad : S.Out() = K.Kernel.step(st2, data_event(1, [1, 2, 3]), entropy())
    +a_bad : List<&2, F.Action> = K.Kernel.actions(o_bad)
    C.Check.report("an undecodable PDU: Error Indication on stream 0 and one log line", Bool.and(pdu_is(Fr.Pdu.read(send_bytes(one_send(a_bad))), Fr.Pdu.initiating(), 7), Bool.and(send_on(one_send(a_bad), 1, 0), Bool.and(Nat.is_eq(count_logs(a_bad), 1n), Nat.is_eq(List.length(&2, F.Action, a_bad), 2n)))))
    C.Check.report("an undecodable PDU: the association stays known", S.Assocs.has(1, S.State.assocs(K.Kernel.state(o_bad))))
    +o_inc : S.Out() = K.Kernel.step(S.State.initial(), F.Evt.config_make([T.Tlv.make(1, [0, 241, 16])]), entropy())
    C.Check.report("an incomplete Config: not kept, one log line", Bool.and(Bool.not(configured(K.Kernel.state(o_inc))), Nat.is_eq(count_logs(K.Kernel.actions(o_inc)), 1n)))
    +st_ues : S.State = with_ues(st2, [(7, S.Ue{1, [1], 1}), (8, S.Ue{2, [1], 1}), (9, S.Ue{1, [2], 2})], [(1, S.Session{7, [0, 0, 0, 0, 0, 0, 0, 1]}), (2, S.Session{8, [0, 0, 0, 0, 0, 0, 0, 2]})])
    +o_down : S.Out() = K.Kernel.step(st_ues, F.NgapAssocDown{1}, entropy())
    C.Check.report("NgapAssocDown: only the other association's UE remains", B.bytes_eq(ue_keys(K.Kernel.state(o_down)), [8]))
    C.Check.report("NgapAssocDown: the released UE's session is deleted at eUPF", Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), pfcp_sends(K.Kernel.actions(o_down))), 1n), pfcp_type(Pf.Msg.read(first_pfcp(pfcp_sends(K.Kernel.actions(o_down)))), 54, True{})))
    C.Check.report("NgapAssocDown: the association is forgotten", Bool.not(S.Assocs.has(1, S.State.assocs(K.Kernel.state(o_down)))))
