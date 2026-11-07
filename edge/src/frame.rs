//! The frame protocol (docs/spec/milestone-1.md § The frame protocol), both
//! ways: the edge sends events and reads actions, the tests' fake kernel does
//! the reverse.

use std::fmt;
use std::io::{self, Read, Write};

pub const MAX_BODY: usize = 262_144;
/// The largest NGAP message that fits an NgapData event: the body less its kind, entropy, assoc, stream and length.
pub const MAX_NGAP: usize = MAX_BODY - 1 - 32 - 4 - 2 - 4;
/// The most TLV bytes a Config event carries: the body less its kind, entropy and length.
pub const MAX_CONFIG: usize = MAX_BODY - 1 - 32 - 4;
pub type Entropy = [u8; 32];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tlv {
    pub tag: u16,
    pub value: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    Config(Vec<Tlv>),
    NgapAssocUp(u32),
    NgapAssocDown(u32),
    NgapData { assoc: u32, stream: u16, bytes: Vec<u8> },
    PfcpData(Vec<u8>),
    TimerFired(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Action {
    NgapSend { assoc: u32, stream: u16, bytes: Vec<u8> },
    NgapClose(u32),
    PfcpSend(Vec<u8>),
    TimerStart { timer: u32, ms: u32 },
    TimerCancel(u32),
    Log { level: u8, text: Vec<u8> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    Short,
    Trailing,
    UnknownKind(u8),
    Invalid(&'static str),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Short => write!(f, "body shorter than its fields declare"),
            Error::Trailing => write!(f, "bytes after the last field"),
            Error::UnknownKind(k) => write!(f, "unknown kind byte {k:#04x}"),
            Error::Invalid(why) => write!(f, "{why}"),
        }
    }
}

impl std::error::Error for Error {}

struct Cursor<'a> {
    bytes: &'a [u8],
}

impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], Error> {
        if self.bytes.len() < n {
            return Err(Error::Short);
        }
        let (head, tail) = self.bytes.split_at(n);
        self.bytes = tail;
        Ok(head)
    }

    fn u8(&mut self) -> Result<u8, Error> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, Error> {
        Ok(u16::from_be_bytes(self.take(2)?.try_into().unwrap()))
    }

    fn u32(&mut self) -> Result<u32, Error> {
        Ok(u32::from_be_bytes(self.take(4)?.try_into().unwrap()))
    }

    fn sized(&mut self) -> Result<Vec<u8>, Error> {
        let n = self.u32()? as usize;
        Ok(self.take(n)?.to_vec())
    }

    fn done(&self) -> Result<(), Error> {
        if self.bytes.is_empty() {
            Ok(())
        } else {
            Err(Error::Trailing)
        }
    }
}

fn put_sized(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
    out.extend_from_slice(bytes);
}

pub fn tlvs_bytes(tlvs: &[Tlv]) -> Vec<u8> {
    let mut out = Vec::new();
    for t in tlvs {
        out.extend_from_slice(&t.tag.to_be_bytes());
        out.extend_from_slice(&(t.value.len() as u16).to_be_bytes());
        out.extend_from_slice(&t.value);
    }
    out
}

fn parse_tlvs(bytes: &[u8]) -> Result<Vec<Tlv>, Error> {
    let mut c = Cursor { bytes };
    let mut tlvs = Vec::new();
    while !c.bytes.is_empty() {
        let tag = c.u16()?;
        let len = c.u16()? as usize;
        tlvs.push(Tlv { tag, value: c.take(len)?.to_vec() });
    }
    Ok(tlvs)
}

pub fn event_body(entropy: &Entropy, event: &Event) -> Vec<u8> {
    let mut out = Vec::new();
    let kind = match event {
        Event::Config(_) => 0x01,
        Event::NgapAssocUp(_) => 0x02,
        Event::NgapAssocDown(_) => 0x03,
        Event::NgapData { .. } => 0x04,
        Event::PfcpData(_) => 0x05,
        Event::TimerFired(_) => 0x06,
    };
    out.push(kind);
    out.extend_from_slice(entropy);
    match event {
        Event::Config(tlvs) => put_sized(&mut out, &tlvs_bytes(tlvs)),
        Event::NgapAssocUp(a) | Event::NgapAssocDown(a) | Event::TimerFired(a) => out.extend_from_slice(&a.to_be_bytes()),
        Event::NgapData { assoc, stream, bytes } => {
            out.extend_from_slice(&assoc.to_be_bytes());
            out.extend_from_slice(&stream.to_be_bytes());
            put_sized(&mut out, bytes);
        }
        Event::PfcpData(bytes) => put_sized(&mut out, bytes),
    }
    out
}

pub fn parse_event(body: &[u8]) -> Result<(Entropy, Event), Error> {
    let mut c = Cursor { bytes: body };
    let kind = c.u8()?;
    let entropy: Entropy = c.take(32)?.try_into().unwrap();
    let event = match kind {
        0x01 => Event::Config(parse_tlvs(&c.sized()?)?),
        0x02 => Event::NgapAssocUp(c.u32()?),
        0x03 => Event::NgapAssocDown(c.u32()?),
        0x04 => Event::NgapData { assoc: c.u32()?, stream: c.u16()?, bytes: c.sized()? },
        0x05 => Event::PfcpData(c.sized()?),
        0x06 => Event::TimerFired(c.u32()?),
        k => return Err(Error::UnknownKind(k)),
    };
    c.done()?;
    Ok((entropy, event))
}

pub fn actions_body(actions: &[Action]) -> Vec<u8> {
    let mut out = vec![0x80];
    out.extend_from_slice(&(actions.len() as u16).to_be_bytes());
    for a in actions {
        match a {
            Action::NgapSend { assoc, stream, bytes } => {
                out.push(0x81);
                out.extend_from_slice(&assoc.to_be_bytes());
                out.extend_from_slice(&stream.to_be_bytes());
                put_sized(&mut out, bytes);
            }
            Action::NgapClose(assoc) => {
                out.push(0x82);
                out.extend_from_slice(&assoc.to_be_bytes());
            }
            Action::PfcpSend(bytes) => {
                out.push(0x83);
                put_sized(&mut out, bytes);
            }
            Action::TimerStart { timer, ms } => {
                out.push(0x84);
                out.extend_from_slice(&timer.to_be_bytes());
                out.extend_from_slice(&ms.to_be_bytes());
            }
            Action::TimerCancel(timer) => {
                out.push(0x85);
                out.extend_from_slice(&timer.to_be_bytes());
            }
            Action::Log { level, text } => {
                out.push(0x86);
                out.push(*level);
                put_sized(&mut out, text);
            }
        }
    }
    out
}

pub fn parse_actions(body: &[u8]) -> Result<Vec<Action>, Error> {
    let mut c = Cursor { bytes: body };
    if c.u8()? != 0x80 {
        return Err(Error::Invalid("not an Actions body"));
    }
    let count = c.u16()?;
    let mut actions = Vec::with_capacity(count as usize);
    for _ in 0..count {
        actions.push(match c.u8()? {
            0x81 => Action::NgapSend { assoc: c.u32()?, stream: c.u16()?, bytes: c.sized()? },
            0x82 => Action::NgapClose(c.u32()?),
            0x83 => Action::PfcpSend(c.sized()?),
            0x84 => Action::TimerStart { timer: c.u32()?, ms: c.u32()? },
            0x85 => Action::TimerCancel(c.u32()?),
            0x86 => {
                let level = c.u8()?;
                if level > 3 {
                    return Err(Error::Invalid("log level above 3"));
                }
                Action::Log { level, text: c.sized()? }
            }
            k => return Err(Error::UnknownKind(k)),
        });
    }
    c.done()?;
    Ok(actions)
}

pub fn frame(body: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(body.len() + 4);
    put_sized(&mut out, body);
    out
}

pub fn write_frame<W: Write>(w: &mut W, body: &[u8]) -> io::Result<()> {
    w.write_all(&frame(body))
}

/// One frame's body; `UnexpectedEof` when the peer closed between frames,
/// `InvalidData` when the length word exceeds the limit.
pub fn read_frame<R: Read>(r: &mut R) -> io::Result<Vec<u8>> {
    let mut len = [0u8; 4];
    r.read_exact(&mut len)?;
    let len = u32::from_be_bytes(len) as usize;
    if len > MAX_BODY {
        return Err(io::Error::new(io::ErrorKind::InvalidData, format!("frame body of {len} bytes exceeds {MAX_BODY}")));
    }
    let mut body = vec![0u8; len];
    r.read_exact(&mut body)?;
    Ok(body)
}
