//! N2 transport: one-to-one SCTP sockets through libc, the only `unsafe` in
//! the crate. Each accepted socket is one association; messages carry their
//! stream id both ways and the NGAP payload protocol identifier.

use std::io;
use std::mem;
use std::net::Ipv4Addr;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};

pub const NGAP_PPID: u32 = 60;
const CHUNK: usize = 65_536;

fn check(r: libc::c_int) -> io::Result<libc::c_int> {
    if r < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(r)
    }
}

fn check_len(r: libc::ssize_t) -> io::Result<usize> {
    if r < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(r as usize)
    }
}

fn sockaddr(addr: Ipv4Addr, port: u16) -> libc::sockaddr_in {
    let mut sa: libc::sockaddr_in = unsafe { mem::zeroed() };
    sa.sin_family = libc::AF_INET as libc::sa_family_t;
    sa.sin_port = port.to_be();
    sa.sin_addr = libc::in_addr { s_addr: u32::from_ne_bytes(addr.octets()) };
    sa
}

fn socket() -> io::Result<OwnedFd> {
    let fd = check(unsafe { libc::socket(libc::AF_INET, libc::SOCK_STREAM | libc::SOCK_CLOEXEC, libc::IPPROTO_SCTP) })?;
    Ok(unsafe { OwnedFd::from_raw_fd(fd) })
}

fn set_int(fd: RawFd, level: libc::c_int, name: libc::c_int, value: libc::c_int) -> io::Result<()> {
    check(unsafe {
        libc::setsockopt(fd, level, name, &value as *const libc::c_int as *const libc::c_void, mem::size_of::<libc::c_int>() as libc::socklen_t)
    })?;
    Ok(())
}

/// Whether this kernel offers SCTP sockets at all.
pub fn available() -> io::Result<()> {
    socket().map(drop)
}

pub struct Listener {
    fd: OwnedFd,
}

impl Listener {
    pub fn bind(addr: Ipv4Addr, port: u16) -> io::Result<Listener> {
        let fd = socket()?;
        set_int(fd.as_raw_fd(), libc::SOL_SOCKET, libc::SO_REUSEADDR, 1)?;
        let sa = sockaddr(addr, port);
        check(unsafe {
            libc::bind(fd.as_raw_fd(), &sa as *const libc::sockaddr_in as *const libc::sockaddr, mem::size_of::<libc::sockaddr_in>() as libc::socklen_t)
        })?;
        check(unsafe { libc::listen(fd.as_raw_fd(), 16) })?;
        Ok(Listener { fd })
    }

    pub fn local_port(&self) -> io::Result<u16> {
        let mut sa: libc::sockaddr_in = unsafe { mem::zeroed() };
        let mut len = mem::size_of::<libc::sockaddr_in>() as libc::socklen_t;
        check(unsafe { libc::getsockname(self.fd.as_raw_fd(), &mut sa as *mut libc::sockaddr_in as *mut libc::sockaddr, &mut len) })?;
        Ok(u16::from_be(sa.sin_port))
    }

    pub fn accept(&self) -> io::Result<Assoc> {
        let fd = check(unsafe { libc::accept4(self.fd.as_raw_fd(), std::ptr::null_mut(), std::ptr::null_mut(), libc::SOCK_CLOEXEC) })?;
        Assoc::adopt(unsafe { OwnedFd::from_raw_fd(fd) })
    }
}

pub struct Assoc {
    fd: OwnedFd,
}

impl Assoc {
    fn adopt(fd: OwnedFd) -> io::Result<Assoc> {
        set_int(fd.as_raw_fd(), libc::IPPROTO_SCTP, libc::SCTP_RECVRCVINFO, 1)?;
        Ok(Assoc { fd })
    }

    pub fn connect(addr: Ipv4Addr, port: u16) -> io::Result<Assoc> {
        let fd = socket()?;
        let sa = sockaddr(addr, port);
        check(unsafe {
            libc::connect(fd.as_raw_fd(), &sa as *const libc::sockaddr_in as *const libc::sockaddr, mem::size_of::<libc::sockaddr_in>() as libc::socklen_t)
        })?;
        Assoc::adopt(fd)
    }

    /// One whole message with its stream id; `None` once the peer has closed.
    /// A message longer than `max` bytes is an error, so the caller drops the association.
    pub fn recv(&self, max: usize) -> io::Result<Option<(u16, Vec<u8>)>> {
        let mut message = Vec::new();
        let mut stream = 0u16;
        let mut buf = vec![0u8; CHUNK];
        let mut control = [0u8; 128];
        loop {
            let mut iov = libc::iovec { iov_base: buf.as_mut_ptr() as *mut libc::c_void, iov_len: buf.len() };
            let mut hdr: libc::msghdr = unsafe { mem::zeroed() };
            hdr.msg_iov = &mut iov;
            hdr.msg_iovlen = 1;
            hdr.msg_control = control.as_mut_ptr() as *mut libc::c_void;
            hdr.msg_controllen = control.len() as _;
            let n = check_len(unsafe { libc::recvmsg(self.fd.as_raw_fd(), &mut hdr, 0) })?;
            if n == 0 {
                return Ok(None);
            }
            if hdr.msg_flags & libc::MSG_NOTIFICATION != 0 {
                continue;
            }
            if let Some(sid) = stream_of(&hdr) {
                stream = sid;
            }
            message.extend_from_slice(&buf[..n]);
            if message.len() > max {
                return Err(io::Error::new(io::ErrorKind::InvalidData, format!("SCTP message over {max} bytes")));
            }
            if hdr.msg_flags & libc::MSG_EOR != 0 {
                return Ok(Some((stream, message)));
            }
        }
    }

    pub fn send(&self, stream: u16, bytes: &[u8]) -> io::Result<()> {
        let info = libc::sctp_sndinfo { snd_sid: stream, snd_flags: 0, snd_ppid: NGAP_PPID.to_be(), snd_context: 0, snd_assoc_id: 0 };
        let info_len = mem::size_of::<libc::sctp_sndinfo>() as libc::c_uint;
        let mut control = vec![0u8; unsafe { libc::CMSG_SPACE(info_len) } as usize];
        let mut iov = libc::iovec { iov_base: bytes.as_ptr() as *mut libc::c_void, iov_len: bytes.len() };
        let mut hdr: libc::msghdr = unsafe { mem::zeroed() };
        hdr.msg_iov = &mut iov;
        hdr.msg_iovlen = 1;
        hdr.msg_control = control.as_mut_ptr() as *mut libc::c_void;
        hdr.msg_controllen = control.len() as _;
        unsafe {
            let cmsg = libc::CMSG_FIRSTHDR(&hdr);
            (*cmsg).cmsg_level = libc::IPPROTO_SCTP;
            (*cmsg).cmsg_type = libc::SCTP_SNDINFO;
            (*cmsg).cmsg_len = libc::CMSG_LEN(info_len) as _;
            std::ptr::copy_nonoverlapping(&info as *const libc::sctp_sndinfo as *const u8, libc::CMSG_DATA(cmsg), info_len as usize);
        }
        let sent = check_len(unsafe { libc::sendmsg(self.fd.as_raw_fd(), &hdr, libc::MSG_NOSIGNAL) })?;
        if sent != bytes.len() {
            return Err(io::Error::new(io::ErrorKind::WriteZero, "SCTP message sent in part"));
        }
        Ok(())
    }

    /// Closes both directions; a blocked `recv` then returns `None`.
    pub fn shutdown(&self) {
        unsafe { libc::shutdown(self.fd.as_raw_fd(), libc::SHUT_RDWR) };
    }
}

fn stream_of(hdr: &libc::msghdr) -> Option<u16> {
    let mut cmsg = unsafe { libc::CMSG_FIRSTHDR(hdr) };
    while !cmsg.is_null() {
        let (level, kind) = unsafe { ((*cmsg).cmsg_level, (*cmsg).cmsg_type) };
        if level == libc::IPPROTO_SCTP && kind == libc::SCTP_RCVINFO {
            let mut info: libc::sctp_rcvinfo = unsafe { mem::zeroed() };
            unsafe { std::ptr::copy_nonoverlapping(libc::CMSG_DATA(cmsg), &mut info as *mut libc::sctp_rcvinfo as *mut u8, mem::size_of::<libc::sctp_rcvinfo>()) };
            return Some(info.rcv_sid);
        }
        cmsg = unsafe { libc::CMSG_NXTHDR(hdr, cmsg) };
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn loopback_carries_streams_both_ways() {
        match available() {
            Ok(()) => {}
            Err(e) if e.raw_os_error() == Some(libc::EPROTONOSUPPORT) || e.raw_os_error() == Some(libc::ESOCKTNOSUPPORT) => {
                assert!(std::env::var("REQUIRE_SCTP").as_deref() != Ok("1"), "no SCTP, and REQUIRE_SCTP=1");
                println!("SKIP: no SCTP");
                return;
            }
            Err(e) => panic!("SCTP socket: {e}"),
        }
        let listener = Listener::bind(Ipv4Addr::LOCALHOST, 0).unwrap();
        let port = listener.local_port().unwrap();
        let client = Assoc::connect(Ipv4Addr::LOCALHOST, port).unwrap();
        let server = listener.accept().unwrap();
        client.send(1, &[0, 21, 0, 61]).unwrap();
        assert_eq!(server.recv(4).unwrap(), Some((1, vec![0, 21, 0, 61])));
        server.send(0, &[32, 21]).unwrap();
        assert_eq!(client.recv(4).unwrap(), Some((0, vec![32, 21])));
        client.send(0, &[1, 2, 3, 4, 5]).unwrap();
        assert_eq!(server.recv(4).unwrap_err().kind(), io::ErrorKind::InvalidData);
        server.shutdown();
        assert_eq!(client.recv(4).unwrap(), None);
    }
}
