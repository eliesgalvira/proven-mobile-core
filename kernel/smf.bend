import Base
import ./bytes.bend as B
import ./tlv.bend as T
import ./pfcp.bend as Pf
import ./state.bend as S

# The SMF's PFCP messages to eUPF (TS 29.244, the subset of
# docs/research/eupf-pfcp.md). Ticket 19 completes the procedures; here are the
# messages the state machine already needs.

def Assoc.setup_request(cfg: S.Cfg, recovery: B.Bytes(), seq: U32) -> B.Bytes():
  Pf.Msg.write(Pf.Msg.make(5, None{}, seq, [T.Tlv.make(60, Pf.NodeId.write(Pf.NodeV4{S.Cfg.smf_n4(cfg)})), T.Tlv.make(96, recovery)]), [])

def Session.deletion_request(up_seid: B.Bytes(), seq: U32) -> B.Bytes():
  Pf.Msg.write(Pf.Msg.make(54, Some{up_seid}, seq, []), [])
