//! The kernel process and the TCP link to it: one event in, one Actions
//! frame out.

use std::fmt;
use std::io;
use std::net::{Ipv4Addr, TcpStream};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use crate::frame::{self, Action, Entropy, Event};

#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    Frame(frame::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Io(e) => write!(f, "kernel link: {e}"),
            Error::Frame(e) => write!(f, "kernel sent an invalid frame: {e}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Error::Io(e)
    }
}

pub struct Link {
    stream: TcpStream,
}

impl Link {
    /// Connects to a kernel listening on 127.0.0.1, retrying while it starts.
    pub fn connect(port: u16, patience: Duration) -> io::Result<Link> {
        let deadline = Instant::now() + patience;
        loop {
            match TcpStream::connect((Ipv4Addr::LOCALHOST, port)) {
                Ok(stream) => {
                    stream.set_nodelay(true)?;
                    return Ok(Link { stream });
                }
                Err(_) if Instant::now() < deadline => std::thread::sleep(Duration::from_millis(50)),
                Err(e) => return Err(e),
            }
        }
    }

    pub fn step(&mut self, entropy: &Entropy, event: &Event) -> Result<Vec<Action>, Error> {
        frame::write_frame(&mut self.stream, &frame::event_body(entropy, event))?;
        let body = frame::read_frame(&mut self.stream)?;
        frame::parse_actions(&body).map_err(Error::Frame)
    }
}

/// The kernel process, killed when dropped.
pub struct Process {
    child: Child,
}

impl Process {
    pub fn spawn(path: &str, port: u16) -> io::Result<(Process, Link)> {
        let child = Command::new(path).arg(port.to_string()).stdin(Stdio::null()).spawn()?;
        let link = Link::connect(port, Duration::from_secs(10))?;
        Ok((Process { child }, link))
    }
}

impl Drop for Process {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
