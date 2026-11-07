import Base
import ./bytes.bend as B
import ./frame.bend as F
import ./state.bend as S
import ./step.bend as K

# The kernel process (docs/spec/milestone-1.md § The frame protocol), the one
# module that performs IO. It listens on 127.0.0.1 at the port given, takes
# one edge, and for every frame decodes the event, steps, answers one Actions
# frame and echoes the Log actions to stderr. An undecodable or oversized
# frame is a protocol error: the connection closes and the process exits 1.

def Main.port(args: List<String>) -> Maybe<&2, U32>:
  match args:
    case prog <> p <> rest:
      U32.read(p)
    case _:
      None{}

def Main.chars(bs: B.Bytes()) -> List<&2, Char>:
  match bs:
    case Nil{}:
      []
    case b <> rest:
      Chr{b} <> Main.chars(rest)

def Main.level(l: F.Level) -> String:
  match l:
    case F.Debug{}:
      "debug"
    case F.Info{}:
      "info"
    case F.Warn{}:
      "warn"
    case F.Error{}:
      "error"

def Main.echo(actions: List<&2, F.Action>) -> IO(Unit):
  match actions:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case F.Log{level, len, text} <> more:
      do IO<Unit>:
        IO.print_err(Main.level(level) ++ ": " ++ String.from_list(Main.chars(text)))
        Main.echo(more)
    case a <> more:
      Main.echo(more)

def Main.fail(sock: Socket, why: String) -> IO(Unit):
  do IO<Unit>:
    Socket.close(sock)
    IO.die(Unit, 1, "kernel: " ++ why)

# One event: step, answer, echo, go on with what followed the frame.
@unsafe def Main.event(sock: Socket, st: S.State, rest: B.Bytes(), r: B.Read(F.Input)) -> IO(Unit):
  match r:
    case Fail{e}:
      Main.fail(sock, "event not decodable")
    case Done{(F.Input{entropy, event}, Nil{})}:
      +o = K.Kernel.step(st, event, entropy)
      +actions : List<&2, F.Action> = K.Kernel.frames(o)
      do IO<Unit>:
        sent : Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit> <- TCP.send_bytes(sock, F.Frame.write(F.Actions.write(F.Actions.make(actions), []), []))
        Main.echo(actions)
        Main.sent(K.Kernel.state(o), rest, sent)
    case Done{(input, b <> trailing)}:
      Main.fail(sock, "bytes after the event in its frame")

@unsafe def Main.sent(st: S.State, rest: B.Bytes(), sent: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> IO(Unit):
  match sent:
    case (sock, Done{u}):
      Main.frames(sock, st, rest)
    case (sock, Fail{((code, msg), left)}):
      Main.fail(sock, "send: " ++ msg)

# Every complete frame in the buffer, then more bytes.
@unsafe def Main.frames(sock: Socket, st: S.State, +buf: B.Bytes()) -> IO(Unit):
  Main.framed(sock, st, buf, F.Frame.read(buf))

@unsafe def Main.framed(sock: Socket, st: S.State, +buf: B.Bytes(), r: B.Read(B.Bytes())) -> IO(Unit):
  match r:
    case Done{(body, rest)}:
      Main.event(sock, st, rest, F.Input.read(body))
    case Fail{B.Short{}}:
      Main.wait(sock, st, [buf], List.length(&2, U32, buf), Main.need(B.u32(buf)))
    case Fail{e}:
      Main.fail(sock, "frame too long or malformed")

# The bytes a frame needs: its length field, then the body it declares.
def Main.need(r: B.Read(U32)) -> Nat:
  match r:
    case Done{(len, rest)}:
      Nat.add(4n, U32.to_nat(len))
    case Fail{e}:
      4n

# The chunks received, newest first, are joined once the frame is complete,
# so a frame arriving in pieces costs its length, not its length squared.
@unsafe def Main.wait(sock: Socket, st: S.State, chunks: List<&2, B.Bytes()>, have: Nat, need: Nat) -> IO(Unit):
  do IO<Unit>:
    got : Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>> <- TCP.recv_bytes(sock, 65536)
    Main.received(st, chunks, have, need, got)

@unsafe def Main.received(st: S.State, chunks: List<&2, B.Bytes()>, have: Nat, +need: Nat, got: Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>) -> IO(Unit):
  match got:
    case (sock, Done{Some{+bytes}}):
      +total = Nat.add(have, List.length(&2, U32, bytes))
      Main.gathered(sock, st, bytes <> chunks, total, need, Nat.is_le(need, total))
    case (sock, Done{None{}}):
      do IO<Unit>:
        Socket.close(sock)
        IO.print_err("kernel: edge closed the connection")
    case (sock, Fail{(code, msg)}):
      Main.fail(sock, "recv: " ++ msg)

@unsafe def Main.gathered(sock: Socket, st: S.State, chunks: List<&2, B.Bytes()>, have: Nat, need: Nat, complete: Bool) -> IO(Unit):
  match complete:
    case True{}:
      Main.frames(sock, st, List.concat(&2, U32, List.reverse(&2, B.Bytes(), chunks)))
    case False{}:
      Main.wait(sock, st, chunks, have, need)

def Main.serve(accepted: Listener & Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  match accepted:
    case (listener, Done{sock}):
      do IO<Unit>:
        Listener.close(listener)
        Main.frames(sock, S.State.initial(), [])
    case (listener, Fail{(code, msg)}):
      do IO<Unit>:
        Listener.close(listener)
        IO.die(Unit, 1, "kernel: accept: " ++ msg)

def Main.listen(port: Maybe<&2, U32>) -> IO(Unit):
  match port:
    case None{}:
      IO.die(Unit, 2, "usage: kernel <port>")
    case Some{p}:
      do IO<Unit>:
        listener : Listener <- IO.try(Listener, TCP.listen("127.0.0.1", p))
        accepted : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(listener)
        Main.serve(accepted)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    Main.listen(Main.port(args))
