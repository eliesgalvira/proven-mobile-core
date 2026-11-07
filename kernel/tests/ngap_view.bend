import Base
import ../bytes.bend as B
import ../aper.bend as A
import ../ngap/frame.bend as F
import ../ngap/gen/types.bend as G
import ../ngap/gen/views.bend as W
import ./lib/check.bend as C
import ./lib/vec.bend as V
import ./lib/ngap_vectors.bend as N

# Every NGAP message of the vectors passes its view; the InitialUEMessage
# view yields the captured identities; and the views reject a missing
# mandatory IE, a duplicated IE, and an unknown IE with criticality reject,
# while they skip an unknown IE with criticality ignore.

def ies_of(p: F.Pdu) -> A.Rd(List<&2, F.Ie>):
  F.Ies.read(A.Cur{7n, List.drop(&2, Bool, A.unpack(F.Pdu.value(p)), 1n)})

def accepted(+name: String, r: Maybe<&2, Bool>) -> IO(Unit):
  match r:
    case None{}:
      C.Check.report(name ++ ": has a view", False{})
    case Some{ok}:
      C.Check.report(name ++ ": passes its view", ok)

def container(+name: String, kind: Nat, code: Nat, r: A.Rd(List<&2, F.Ie>)) -> IO(Unit):
  match r:
    case Fail{e}:
      C.Check.report(name ++ ": IE container decodes", False{})
    case Done{(ies, c)}:
      accepted(name, W.View.check(kind, code, ies))

def pdu(+name: String, r: Result<&2, &2, B.Err, F.Pdu>) -> IO(Unit):
  match r:
    case Fail{e}:
      C.Check.report(name ++ ": PDU decodes", False{})
    case Done{+p}:
      container(name, U32.to_nat(F.Pdu.kind(p)), U32.to_nat(F.Pdu.code(p)), ies_of(p))

def one(+m: V.Vec, protocol: String) -> IO(Unit):
  match protocol:
    case "NGAP":
      pdu(V.Vec.text(V.Vec.field(m, "message")), F.Pdu.read(V.Vec.bytes(V.Vec.field(m, "hex"))))
    case _:
      IO.pure(Unit, Unit{})

def run(msgs: List<&2, V.Vec>) -> IO(Unit):
  match msgs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +m <> rest:
      do IO<Unit>:
        one(m, V.Vec.text(V.Vec.field(m, "protocol")))
        run(rest)

def from_rd(r: A.Rd(List<&2, F.Ie>)) -> List<&2, F.Ie>:
  match r:
    case Fail{e}:
      []
    case Done{(ies, c)}:
      ies

def from_pdu(r: Result<&2, &2, B.Err, F.Pdu>) -> List<&2, F.Ie>:
  match r:
    case Fail{e}:
      []
    case Done{p}:
      from_rd(ies_of(p))

def pick(+m: V.Vec, rest: List<&2, F.Ie>, hit: Bool) -> List<&2, F.Ie>:
  match hit:
    case True{}:
      from_pdu(F.Pdu.read(V.Vec.bytes(V.Vec.field(m, "hex"))))
    case False{}:
      rest

# The IEs of the first message of the vectors with this name.
def first_ies(+name: String, msgs: List<&2, V.Vec>) -> List<&2, F.Ie>:
  match msgs:
    case Nil{}:
      []
    case +m <> rest:
      pick(m, first_ies(name, rest), String.eq(V.Vec.text(V.Vec.field(m, "message")), name))

def keep(ie: F.Ie, rest: List<&2, F.Ie>, drop: Bool) -> List<&2, F.Ie>:
  match drop:
    case True{}:
      rest
    case False{}:
      ie <> rest

def without(+id: U32, ies: List<&2, F.Ie>) -> List<&2, F.Ie>:
  match ies:
    case Nil{}:
      []
    case +ie <> more:
      keep(ie, without(id, more), U32.is_eq(F.Ie.id(ie), id))

def ran_ue_id(r: Result<&2, &2, B.Err, W.InitialUEMessage.View>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{v}:
      match v:
        case W.InitialUEMessage.View{ran_ue_ngap_id, nas_pdu, userlocationinformation, rrcestablishmentcause, fiveg_s_tmsi, amfsetid, allowednssai, selectedplmnidentity, iabnodeindication, cemodebsupport_indicator, npn_accessinformation}:
          Bool.and(B.bytes_eq(ran_ue_ngap_id, [1]), U32.is_eq(A.Enum.index(rrcestablishmentcause), G.RRCEstablishmentCause.mo_Signalling()))

def passes(r: Maybe<&2, Bool>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{ok}:
      ok

# Whether the view of the message with this PDU kind and procedure code accepts the IEs.
def accepts(kind: Nat, code: Nat, ies: List<&2, F.Ie>) -> Bool:
  passes(W.View.check(kind, code, ies))

def main() -> IO(Unit):
  do IO<Unit>:
    run(N.Ngap.vectors())
    +ies : List<&2, F.Ie> = first_ies("InitialUEMessage", N.Ngap.vectors())
    C.Check.report("the InitialUEMessage view carries RAN-UE-NGAP-ID 1 and cause mo-Signalling", ran_ue_id(W.InitialUEMessage.view(ies)))
    C.Check.report("an InitialUEMessage without UserLocationInformation is rejected", Bool.not(accepts(0n, 15n, without(121, ies))))
    C.Check.report("an InitialUEMessage without its NAS-PDU is rejected", Bool.not(accepts(0n, 15n, without(38, ies))))
    C.Check.report("a duplicated RAN-UE-NGAP-ID is rejected", Bool.not(accepts(0n, 15n, F.Ie{85, 0, [0, 1]} <> ies)))
    C.Check.report("an unknown IE with criticality reject is rejected", Bool.not(accepts(0n, 15n, F.Ie{60000, 0, [0]} <> ies)))
    C.Check.report("an unknown IE with criticality ignore is skipped", accepts(0n, 15n, F.Ie{60000, 1, [0]} <> ies))
    C.Check.report("a known IE with a malformed value is rejected", Bool.not(accepts(0n, 15n, F.Ie{85, 0, [64, 0, 1]} <> without(85, ies))))
    +psr : List<&2, F.Ie> = first_ies("PathSwitchRequest", N.Ngap.vectors())
    C.Check.report("a PathSwitchRequest without UESecurityCapabilities is rejected", Bool.not(accepts(0n, 25n, without(119, psr))))
    C.Check.report("a PathSwitchRequest without its PDU session list is rejected", Bool.not(accepts(0n, 25n, without(76, psr))))
    C.Check.report("a PathSwitchRequest with a duplicated Source AMF-UE-NGAP-ID is rejected", Bool.not(accepts(0n, 25n, F.Ie{100, 0, [0, 1]} <> psr)))
    +hr : List<&2, F.Ie> = first_ies("HandoverRequired", N.Ngap.vectors())
    C.Check.report("a HandoverRequired without TargetID is rejected", Bool.not(accepts(0n, 12n, without(105, hr))))
    C.Check.report("a HandoverRequired with an unknown IE with criticality reject is rejected", Bool.not(accepts(0n, 12n, F.Ie{60000, 0, [0]} <> hr)))
    +hra : List<&2, F.Ie> = first_ies("HandoverRequestAcknowledge", N.Ngap.vectors())
    C.Check.report("a HandoverRequestAcknowledge without its Target to Source container is rejected", Bool.not(accepts(1n, 13n, without(106, hra))))
    C.Check.report("a HandoverRequestAcknowledge with an unknown IE with criticality ignore passes", accepts(1n, 13n, F.Ie{60000, 1, [0]} <> hra))
