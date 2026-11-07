//! The loop: one event at a time to the kernel, its actions applied to the
//! sockets and the timers. Socket threads feed the loop through a channel;
//! every timer due fires after each message and when the receive times out.

use std::collections::HashMap;
use std::fmt;
use std::net::{SocketAddr, SocketAddrV4, UdpSocket};
use std::sync::mpsc::{Receiver, RecvTimeoutError, Sender};
use std::sync::Arc;
use std::thread;
use std::time::Instant;

use crate::config::{Config, N2_PORT, N4_PORT};
use crate::frame::{Action, Entropy, Event, MAX_NGAP};
use crate::kernel::{self, Link};
use crate::sctp;
use crate::timers::Timers;

pub enum Msg {
    Up(u32, Arc<sctp::Assoc>),
    Data(u32, u16, Vec<u8>),
    Down(u32),
    Pfcp(Vec<u8>, SocketAddr),
    Fatal(String),
}

#[derive(Debug)]
pub enum Error {
    Kernel(kernel::Error),
    Entropy(getrandom::Error),
    Socket(std::io::Error),
    Fatal(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Kernel(e) => write!(f, "{e}"),
            Error::Entropy(e) => write!(f, "entropy: {e}"),
            Error::Socket(e) => write!(f, "socket: {e}"),
            Error::Fatal(why) => write!(f, "{why}"),
        }
    }
}

impl std::error::Error for Error {}

fn entropy() -> Result<Entropy, Error> {
    let mut bytes = [0u8; 32];
    getrandom::fill(&mut bytes).map_err(Error::Entropy)?;
    Ok(bytes)
}

pub struct Edge {
    link: Link,
    udp: UdpSocket,
    upf: SocketAddrV4,
    assocs: HashMap<u32, Arc<sctp::Assoc>>,
    timers: Timers,
}

impl Edge {
    pub fn new(link: Link, udp: UdpSocket, upf: SocketAddrV4) -> Edge {
        Edge { link, udp, upf, assocs: HashMap::new(), timers: Timers::default() }
    }

    pub fn step(&mut self, event: &Event) -> Result<(), Error> {
        self.step_to(event, SocketAddr::V4(self.upf))
    }

    /// Steps the kernel and sends its PFCP to `n4`: the UPF's N4 port, or the
    /// source of the UPF datagram being answered (TS 29.244 §7.2).
    fn step_to(&mut self, event: &Event, n4: SocketAddr) -> Result<(), Error> {
        let actions = self.link.step(&entropy()?, event).map_err(Error::Kernel)?;
        let now = Instant::now();
        for action in actions {
            match action {
                Action::NgapSend { assoc, stream, bytes } => match self.assocs.get(&assoc) {
                    Some(a) => {
                        if let Err(e) = a.send(stream, &bytes) {
                            eprintln!("edge: association {assoc}: send: {e}");
                        }
                    }
                    None => eprintln!("edge: NgapSend to unknown association {assoc}"),
                },
                Action::NgapClose(assoc) => {
                    if let Some(a) = self.assocs.remove(&assoc) {
                        a.shutdown();
                    }
                }
                Action::PfcpSend(bytes) => {
                    if let Err(e) = self.udp.send_to(&bytes, n4) {
                        eprintln!("edge: N4 send: {e}");
                    }
                }
                Action::TimerStart { timer, ms } => self.timers.start(timer, ms, now),
                Action::TimerCancel(timer) => self.timers.cancel(timer),
                Action::Log { .. } => {}
            }
        }
        Ok(())
    }

    /// Runs until a socket thread reports a fatal error or the kernel fails,
    /// then closes every association and returns why.
    pub fn serve(&mut self, rx: &Receiver<Msg>) -> Error {
        let why = loop {
            if let Err(e) = self.turn(rx) {
                break e;
            }
        };
        for a in self.assocs.values() {
            a.shutdown();
        }
        why
    }

    fn turn(&mut self, rx: &Receiver<Msg>) -> Result<(), Error> {
        let msg = match self.timers.deadline() {
            Some(at) => rx.recv_timeout(at.saturating_duration_since(Instant::now())),
            None => rx.recv().map_err(|_| RecvTimeoutError::Disconnected),
        };
        self.receive(msg)?;
        let now = Instant::now();
        while let Some(id) = self.timers.pop_due(now) {
            self.step(&Event::TimerFired(id))?;
        }
        Ok(())
    }

    fn receive(&mut self, msg: Result<Msg, RecvTimeoutError>) -> Result<(), Error> {
        match msg {
            Ok(Msg::Up(id, assoc)) => {
                self.assocs.insert(id, assoc);
                self.step(&Event::NgapAssocUp(id))
            }
            Ok(Msg::Data(id, stream, bytes)) if self.assocs.contains_key(&id) => self.step(&Event::NgapData { assoc: id, stream, bytes }),
            Ok(Msg::Down(id)) if self.assocs.remove(&id).is_some() => self.step(&Event::NgapAssocDown(id)),
            Ok(Msg::Data(..)) | Ok(Msg::Down(_)) => Ok(()),
            Ok(Msg::Pfcp(bytes, from)) if from.ip() == *self.upf.ip() => self.step_to(&Event::PfcpData(bytes), from),
            Ok(Msg::Pfcp(_, from)) => {
                eprintln!("edge: N4 datagram from {from} dropped: not the UPF");
                Ok(())
            }
            Ok(Msg::Fatal(why)) => Err(Error::Fatal(why)),
            Err(RecvTimeoutError::Timeout) => Ok(()),
            Err(RecvTimeoutError::Disconnected) => Err(Error::Fatal("every socket thread has stopped".to_string())),
        }
    }
}

pub fn spawn_n2(listener: sctp::Listener, tx: Sender<Msg>) {
    thread::spawn(move || {
        let mut next = 1u32;
        loop {
            match listener.accept() {
                Ok(assoc) => {
                    let id = next;
                    next += 1;
                    let assoc = Arc::new(assoc);
                    if tx.send(Msg::Up(id, assoc.clone())).is_err() {
                        return;
                    }
                    let tx = tx.clone();
                    thread::spawn(move || read_assoc(id, assoc, tx));
                }
                Err(e) => {
                    let _ = tx.send(Msg::Fatal(format!("N2 accept: {e}")));
                    return;
                }
            }
        }
    });
}

fn read_assoc(id: u32, assoc: Arc<sctp::Assoc>, tx: Sender<Msg>) {
    loop {
        match assoc.recv(MAX_NGAP) {
            Ok(Some((stream, bytes))) => {
                if tx.send(Msg::Data(id, stream, bytes)).is_err() {
                    return;
                }
            }
            Ok(None) => break,
            Err(e) => {
                eprintln!("edge: association {id}: recv: {e}");
                break;
            }
        }
    }
    let _ = tx.send(Msg::Down(id));
}

pub fn spawn_n4(udp: UdpSocket, tx: Sender<Msg>) {
    thread::spawn(move || {
        let mut buf = vec![0u8; 65_536];
        loop {
            match udp.recv_from(&mut buf) {
                Ok((n, from)) => {
                    if tx.send(Msg::Pfcp(buf[..n].to_vec(), from)).is_err() {
                        return;
                    }
                }
                Err(e) => {
                    let _ = tx.send(Msg::Fatal(format!("N4 recv: {e}")));
                    return;
                }
            }
        }
    });
}

/// The whole edge for one configuration: kernel, Config, N2, N4, then the loop.
pub fn run(config: &Config) -> Result<(), Error> {
    let tlvs = config.tlvs().map_err(|e| Error::Fatal(e.to_string()))?;
    let (_process, link) = kernel::Process::spawn(&config.kernel.path, config.kernel.port).map_err(Error::Socket)?;
    let upf = SocketAddrV4::new(config.n4.upf, N4_PORT);
    let udp = UdpSocket::bind(SocketAddrV4::new(config.n4.smf, N4_PORT)).map_err(Error::Socket)?;
    let listener = sctp::Listener::bind(config.n2.address, N2_PORT).map_err(Error::Socket)?;
    let mut edge = Edge::new(link, udp.try_clone().map_err(Error::Socket)?, upf);
    edge.step(&Event::Config(tlvs))?;
    let (tx, rx) = std::sync::mpsc::channel();
    spawn_n2(listener, tx.clone());
    spawn_n4(udp, tx);
    eprintln!("edge: N2 on {}:{N2_PORT}, N4 on {}:{N4_PORT} to {upf}", config.n2.address, config.n4.smf);
    Err(edge.serve(&rx))
}
