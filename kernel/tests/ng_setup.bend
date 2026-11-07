import Base
import ../bytes.bend as B
import ../aper.bend as Ap
import ../tlv.bend as T
import ../pfcp.bend as Pf
import ../ngap/frame.bend as Fr
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as W
import ../frame.bend as F
import ../table.bend as Tb
import ../state.bend as S
import ../step.bend as K
import ../amf/ngap.bend as N
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./vectors/capture-vectors.bend as Capture
import ./lib/amf.bend as A
import ./lib/pfcp.bend as P

# Drives step with Config, NgapAssocUp and the captured NG Setup Request: the
# answer is the captured NG Setup Response, byte for byte. Then the failure
# cases: an unsupported TAC, no configuration, an undecodable PDU, an
# incomplete Config; and an association going down releases its UEs.

def sixteen() -> B.Bytes():
  [70, 91, 92, 232, 177, 153, 180, 159, 170, 95, 10, 46, 226, 56, 166, 188]

def subscriber() -> B.Bytes():
  F.Sub.write(F.Sub{[48, 48, 49, 48, 49, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49], sixteen(), [232, 237, 40, 157, 235, 169, 82, 228, 40, 59, 84, 232, 142, 97, 131, 202], [128, 0], [0, 0, 0, 0, 0, 64]})

# The capture's network (test-vectors/capture/vectors.json § network), with a TAC of choice.
def config(tac: B.Bytes()) -> List<&2, T.Tlv>:
  [T.Tlv.make(1, [0, 241, 16]), T.Tlv.make(2, [2]), T.Tlv.make(3, [0, 1]), T.Tlv.make(4, [0]), T.Tlv.make(5, tac), T.Tlv.make(6, [115, 112, 101, 99, 107, 45, 97, 109, 102, 48]), T.Tlv.make(7, [1]), T.Tlv.make(8, [105, 110, 116, 101, 114, 110, 101, 116]), T.Tlv.make(9, [10, 45, 0, 0]), T.Tlv.make(10, [16]), T.Tlv.make(11, [8, 8, 8, 8]), T.Tlv.make(12, [10, 33, 0, 12]), T.Tlv.make(13, [10, 33, 0, 20]), T.Tlv.make(14, [10, 33, 0, 20]), T.Tlv.make(15, A.key32()), T.Tlv.make(16, [1]), T.Tlv.make(17, [0]), T.Tlv.make(18, [2]), T.Tlv.make(32, subscriber())]

def config_event(tac: B.Bytes()) -> F.Evt:
  F.Evt.config_make(config(tac))

def data_event(assoc: U32, bytes: B.Bytes()) -> F.Evt:
  F.Evt.data_make(assoc, 0, bytes)

# The capture
# -----------

def first_of(+name: String, msgs: List<&2, V.Vec>) -> Maybe<&2, B.Bytes()>:
  match msgs:
    case Nil{}:
      None{}
    case +m <> rest:
      V.Vec.hex_if(m, String.eq(V.Vec.text(V.Vec.field(m, "message")), name), first_of(name, rest))

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

def guami_ok(r: Result<&2, &2, B.Err, W.NGSetupResponse.View>) -> Bool:
  match r:
    case Done{W.NGSetupResponse.View{amfname, G.ServedGUAMIItem{G.GUAMI{plmn, region, set_id, pointer, ext}, backup, ext2} <> Nil{}, capacity, plmns, diagnostics}}:
      Bool.and(B.bytes_eq(plmn, [0, 241, 16]), Bool.and(bits_eq(region, Ap.unpack([2])), Bool.and(Nat.is_eq(List.length(&2, Bool, set_id), 10n), B.bytes_eq(amfname, [115, 112, 101, 99, 107, 45, 97, 109, 102, 48]))))
    case _:
      False{}

def pfcp_type(r: B.Read(Pf.Msg), +kind: U32, with_seid: Bool) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{(+m, rest)}:
      Bool.and(U32.is_eq(Pf.Msg.kind(m), kind), Bool.and(bool_eq(Tb.Table.present(B.Bytes(), Pf.Msg.seid(m)), with_seid), B.bytes_eq(rest, [])))

def configured(st: S.State) -> Bool:
  Tb.Table.present(S.Cfg, S.State.config(st))

def Tb_keys(t: List<&2, Sigma<&2, &2, U32, _ => S.Ue>>) -> List<&2, U32>:
  match t:
    case Nil{}:
      []
    case (k, u) <> more:
      k <> Tb_keys(more)

def ue_keys(st: S.State) -> List<&2, U32>:
  Tb_keys(S.State.ues(st))

def ue_of(assoc: U32, ran: B.Bytes()) -> S.Ue:
  S.Ue{assoc, ran, 1, None{}, None{}, [], 0, S.Releasing{S.Guard{0}}, []}

def with_ues(st: S.State, ues: List<&2, Sigma<&2, &2, U32, _ => S.Ue>>, sessions: List<&2, Sigma<&2, &2, U32, _ => S.Session>>) -> S.State:
  match st:
    case S.State{config, subs, assocs, old_ues, old_sessions, pfcp_seq, next_ue, recovery}:
      S.State{config, subs, assocs, ues, sessions, pfcp_seq, next_ue, recovery}

def main() -> IO(Unit):
  do IO<Unit>:
    +msgs : List<&2, V.Vec> = V.Vec.items(V.Vec.field(Capture.data(), "messages"))
    +request : B.Bytes() = bytes_or(first_of("NGSetupRequest", msgs))
    +response : B.Bytes() = bytes_or(first_of("NGSetupResponse", msgs))
    +o1 : N.Step() = K.Kernel.step(S.State.initial(), config_event([0, 0, 1]), A.entropy())
    +st1 : S.State = K.Kernel.state(o1)
    +a1 : List<&2, F.Action> = K.Kernel.frames(o1)
    +st2 : S.State = K.Kernel.state(K.Kernel.step(st1, F.NgapAssocUp{1}, A.entropy()))
    +o3 : N.Step() = K.Kernel.step(st2, data_event(1, request), A.entropy())
    +a3 : List<&2, F.Action> = K.Kernel.frames(o3)
    +reply : B.Bytes() = send_bytes(one_send(a3))
    C.Check.report("Config: the configuration is kept", configured(st1))
    C.Check.report("Config: a PFCP Association Setup Request goes to the UPF", pfcp_type(Pf.Msg.read(P.first_pfcp(a1)), 5, False{}))
    C.Check.report("NgapAssocUp: the association is not set up yet", Bool.not(S.Assocs.has(1, S.State.assocs(st2))))
    +o_early : N.Step() = K.Kernel.step(st2, data_event(1, bytes_or(first_of("InitialUEMessage", msgs))), A.entropy())
    C.Check.report("InitialUEMessage before NG Setup: Error Indication and one log line, no context", Bool.and(A.pdu_is(Fr.Pdu.read(send_bytes(one_send(K.Kernel.frames(o_early)))), Fr.Pdu.initiating(), 9), Bool.and(Nat.is_eq(count_logs(K.Kernel.frames(o_early)), 1n), Nat.is_eq(List.length(&2, U32, ue_keys(K.Kernel.state(o_early))), 0n))))
    C.Check.report("NG Setup Request: exactly one NGAP message answers, on stream 0", send_on(one_send(a3), 1, 0))
    C.Check.report("NG Setup Request: the answer is an NG Setup Response", A.pdu_is(Fr.Pdu.read(reply), Fr.Pdu.successful(), 21))
    C.Check.report("NG Setup Request: the response carries the configured GUAMI and AMF name", guami_ok(W.NGSetupResponse.view(A.ies_of(Fr.Pdu.read(reply)))))
    C.Check.report("NG Setup Request: the response is the captured one, byte for byte", B.bytes_eq(reply, response))
    C.Check.report("NG Setup Response: the association is set up, no UE context", Bool.and(S.Assocs.has(1, S.State.assocs(K.Kernel.state(o3))), Nat.is_eq(List.length(&2, U32, ue_keys(K.Kernel.state(o3))), 0n)))
    +st_tac : S.State = K.Kernel.state(K.Kernel.step(K.Kernel.state(K.Kernel.step(S.State.initial(), config_event([0, 0, 2]), A.entropy())), F.NgapAssocUp{1}, A.entropy()))
    +o_tac : N.Step() = K.Kernel.step(st_tac, data_event(1, request), A.entropy())
    +reply_tac : B.Bytes() = send_bytes(one_send(K.Kernel.frames(o_tac)))
    C.Check.report("NG Setup Request for another TAC: NG Setup Failure, the association not set up", Bool.and(A.pdu_is(Fr.Pdu.read(reply_tac), Fr.Pdu.unsuccessful(), 21), Bool.not(S.Assocs.has(1, S.State.assocs(K.Kernel.state(o_tac))))))
    +reply_none : B.Bytes() = send_bytes(one_send(K.Kernel.frames(K.Kernel.step(S.State.initial(), data_event(1, request), A.entropy()))))
    C.Check.report("NG Setup Request before Config: NG Setup Failure", A.pdu_is(Fr.Pdu.read(reply_none), Fr.Pdu.unsuccessful(), 21))
    +o_bad : N.Step() = K.Kernel.step(K.Kernel.state(o3), data_event(1, [1, 2, 3]), A.entropy())
    +a_bad : List<&2, F.Action> = K.Kernel.frames(o_bad)
    C.Check.report("an undecodable PDU: Error Indication on stream 0 and one log line", Bool.and(A.pdu_is(Fr.Pdu.read(send_bytes(one_send(a_bad))), Fr.Pdu.initiating(), 9), Bool.and(send_on(one_send(a_bad), 1, 0), Bool.and(Nat.is_eq(count_logs(a_bad), 1n), Nat.is_eq(List.length(&2, F.Action, a_bad), 2n)))))
    C.Check.report("an undecodable PDU: the association stays set up", S.Assocs.has(1, S.State.assocs(K.Kernel.state(o_bad))))
    +o_inc : N.Step() = K.Kernel.step(S.State.initial(), F.Evt.config_make([T.Tlv.make(1, [0, 241, 16])]), A.entropy())
    C.Check.report("an incomplete Config: not kept, one log line", Bool.and(Bool.not(configured(K.Kernel.state(o_inc))), Nat.is_eq(count_logs(K.Kernel.frames(o_inc)), 1n)))
    +o_plmn : N.Step() = K.Kernel.step(S.State.initial(), F.Evt.config_make(List.append(&2, T.Tlv, config([0, 0, 1]), [T.Tlv.make(1, [170, 241, 16])])), A.entropy())
    C.Check.report("a Config whose PLMN holds a digit above 9: not kept, one log line", Bool.and(Bool.not(configured(K.Kernel.state(o_plmn))), Nat.is_eq(count_logs(K.Kernel.frames(o_plmn)), 1n)))
    +o_dns : N.Step() = K.Kernel.step(S.State.initial(), F.Evt.config_make(List.append(&2, T.Tlv, config([0, 0, 1]), [T.Tlv.make(11, [8, 8, 8])])), A.entropy())
    C.Check.report("a Config whose DNS server is not four octets: not kept, one log line", Bool.and(Bool.not(configured(K.Kernel.state(o_dns))), Nat.is_eq(count_logs(K.Kernel.frames(o_dns)), 1n)))
    +o_set : N.Step() = K.Kernel.step(S.State.initial(), F.Evt.config_make(List.append(&2, T.Tlv, config([0, 0, 1]), [T.Tlv.make(3, [4, 0])])), A.entropy())
    C.Check.report("a Config whose AMF Set ID needs more than 10 bits: not kept, one log line", Bool.and(Bool.not(configured(K.Kernel.state(o_set))), Nat.is_eq(count_logs(K.Kernel.frames(o_set)), 1n)))
    +o_ptr : N.Step() = K.Kernel.step(S.State.initial(), F.Evt.config_make(List.append(&2, T.Tlv, config([0, 0, 1]), [T.Tlv.make(4, [64])])), A.entropy())
    C.Check.report("a Config whose AMF Pointer needs more than 6 bits: not kept, one log line", Bool.and(Bool.not(configured(K.Kernel.state(o_ptr))), Nat.is_eq(count_logs(K.Kernel.frames(o_ptr)), 1n)))
    +o_max : N.Step() = K.Kernel.step(S.State.initial(), F.Evt.config_make(List.append(&2, T.Tlv, config([0, 0, 1]), [T.Tlv.make(3, [3, 255]), T.Tlv.make(4, [63])])), A.entropy())
    C.Check.report("a Config with the largest AMF Set ID and Pointer: kept", configured(K.Kernel.state(o_max)))
    +st_ues : S.State = with_ues(K.Kernel.state(o3), [(7, ue_of(1, [1])), (8, ue_of(2, [1])), (9, ue_of(1, [2]))], [(1, S.Session{S.SId{7, 1, 1, 1}, S.SVar{[0, 0, 0, 0, 0, 0, 0, 1], 0, S.Active{}}}), (2, S.Session{S.SId{8, 1, 2, 2}, S.SVar{[0, 0, 0, 0, 0, 0, 0, 2], 0, S.Active{}}})])
    +o_down : N.Step() = K.Kernel.step(st_ues, F.NgapAssocDown{1}, A.entropy())
    C.Check.report("NgapAssocDown: only the other association's UE remains", B.bytes_eq(ue_keys(K.Kernel.state(o_down)), [8]))
    C.Check.report("NgapAssocDown: the released UE's session is deleted at the UPF", Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), P.pfcp_sends(K.Kernel.frames(o_down))), 1n), pfcp_type(Pf.Msg.read(P.first_pfcp(K.Kernel.frames(o_down))), 54, True{})))
    C.Check.report("NgapAssocDown: the association is forgotten", Bool.not(S.Assocs.has(1, S.State.assocs(K.Kernel.state(o_down)))))
    +o_again : N.Step() = K.Kernel.step(st_ues, data_event(1, request), A.entropy())
    C.Check.report("NG Setup again: the association's UEs are released, the other association's stays", B.bytes_eq(ue_keys(K.Kernel.state(o_again)), [8]))
    C.Check.report("NG Setup again: the released UE's session is deleted at the UPF", Bool.and(Nat.is_eq(List.length(&2, B.Bytes(), P.pfcp_sends(K.Kernel.frames(o_again))), 1n), pfcp_type(Pf.Msg.read(P.first_pfcp(K.Kernel.frames(o_again))), 54, True{})))
    C.Check.report("NG Setup again: answered with the NG Setup Response, the association set up", Bool.and(A.pdu_is(Fr.Pdu.read(send_bytes(one_send(K.Kernel.frames(o_again)))), Fr.Pdu.successful(), 21), S.Assocs.has(1, S.State.assocs(K.Kernel.state(o_again)))))
    +st_rep : S.State = with_ues(K.Kernel.state(K.Kernel.step(K.Kernel.state(o3), config_event([0, 0, 2]), A.entropy())), [(7, ue_of(1, [1])), (8, ue_of(2, [1]))], [(1, S.Session{S.SId{7, 1, 1, 1}, S.SVar{[0, 0, 0, 0, 0, 0, 0, 1], 0, S.Active{}}})])
    +o_fail : N.Step() = K.Kernel.step(st_rep, data_event(1, request), A.entropy())
    C.Check.report("NG Setup failing again: the association's UEs are released with their sessions", Bool.and(B.bytes_eq(ue_keys(K.Kernel.state(o_fail)), [8]), Bool.and(Nat.is_eq(List.length(&2, Sigma<&2, &2, U32, _ => S.Session>, S.State.sessions(K.Kernel.state(o_fail))), 0n), pfcp_type(Pf.Msg.read(P.first_pfcp(K.Kernel.frames(o_fail))), 54, True{}))))
    C.Check.report("NG Setup failing again: NG Setup Failure, the association no longer set up", Bool.and(A.pdu_is(Fr.Pdu.read(send_bytes(one_send(K.Kernel.frames(o_fail)))), Fr.Pdu.unsuccessful(), 21), Bool.not(S.Assocs.has(1, S.State.assocs(K.Kernel.state(o_fail))))))
