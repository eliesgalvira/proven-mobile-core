//! The edge against a fake kernel: a TCP listener that records every event
//! and answers with scripted actions.

use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4, TcpListener, UdpSocket};
use std::sync::mpsc;
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use edge::edge::{Edge, Msg};
use edge::frame::{self, Action, Event, Tlv};
use edge::kernel::{self, Link};

type Script = Box<dyn Fn(&Event) -> Option<Vec<Action>> + Send>;

/// Answers each event with what the script says; `None` sends a broken frame.
fn fake_kernel(script: Script) -> (u16, JoinHandle<Vec<Event>>) {
    let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).unwrap();
    let port = listener.local_addr().unwrap().port();
    let handle = thread::spawn(move || {
        let (mut stream, _) = listener.accept().unwrap();
        stream.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        let mut seen = Vec::new();
        while let Ok(body) = frame::read_frame(&mut stream) {
            let (_, event) = frame::parse_event(&body).unwrap();
            let answer = match script(&event) {
                Some(actions) => frame::actions_body(&actions),
                None => vec![0x80, 0, 1, 0x86, 9],
            };
            seen.push(event);
            frame::write_frame(&mut stream, &answer).unwrap();
        }
        seen
    });
    (port, handle)
}

fn connect(port: u16) -> Link {
    Link::connect(port, Duration::from_secs(5)).unwrap()
}

#[test]
fn link_carries_events_and_actions_byte_for_byte() {
    let (port, kernel) = fake_kernel(Box::new(|e| match e {
        Event::Config(tlvs) => Some(vec![Action::PfcpSend(vec![0x20, 0x05]), Action::Log { level: 1, text: tlvs[0].value.clone() }]),
        Event::NgapData { assoc, stream, bytes } => Some(vec![Action::NgapSend { assoc: *assoc, stream: *stream, bytes: bytes.clone() }]),
        _ => Some(vec![]),
    }));
    let mut link = connect(port);
    let entropy = [7u8; 32];
    let config = Event::Config(vec![Tlv { tag: 1, value: vec![0x00, 0xF1, 0x10] }]);
    assert_eq!(
        link.step(&entropy, &config).unwrap(),
        vec![Action::PfcpSend(vec![0x20, 0x05]), Action::Log { level: 1, text: vec![0x00, 0xF1, 0x10] }]
    );
    let data = Event::NgapData { assoc: 4, stream: 1, bytes: vec![0, 21, 0, 61] };
    assert_eq!(link.step(&entropy, &data).unwrap(), vec![Action::NgapSend { assoc: 4, stream: 1, bytes: vec![0, 21, 0, 61] }]);
    assert_eq!(link.step(&entropy, &Event::TimerFired(3)).unwrap(), vec![]);
    drop(link);
    assert_eq!(kernel.join().unwrap(), vec![config, data, Event::TimerFired(3)]);
}

#[test]
fn an_invalid_frame_from_the_kernel_is_an_error() {
    let (port, kernel) = fake_kernel(Box::new(|_| None));
    let mut link = connect(port);
    match link.step(&[0u8; 32], &Event::TimerFired(1)) {
        Err(kernel::Error::Frame(frame::Error::Invalid(_))) => {}
        other => panic!("expected a frame error, got {other:?}"),
    }
    drop(link);
    kernel.join().unwrap();
}

#[test]
fn the_loop_runs_timers_and_keeps_n4_to_the_upf() {
    let upf = UdpSocket::bind((Ipv4Addr::LOCALHOST, 0)).unwrap();
    upf.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    let upf_addr = match upf.local_addr().unwrap() {
        SocketAddr::V4(a) => a,
        _ => unreachable!(),
    };
    let (port, kernel) = fake_kernel(Box::new(|e| match e {
        Event::Config(_) => Some(vec![Action::TimerStart { timer: 1, ms: 500 }, Action::TimerStart { timer: 2, ms: 20 }, Action::TimerCancel(1)]),
        Event::TimerFired(2) => Some(vec![Action::PfcpSend(vec![0x20, 0x01]), Action::NgapClose(9)]),
        Event::PfcpData(bytes) => Some(vec![Action::PfcpSend(bytes.clone())]),
        _ => Some(vec![]),
    }));
    let mut edge = Edge::new(connect(port), UdpSocket::bind((Ipv4Addr::LOCALHOST, 0)).unwrap(), upf_addr);
    edge.step(&Event::Config(vec![])).unwrap();
    let (tx, rx) = mpsc::channel();
    let stranger = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(10, 0, 0, 9), 8805));
    tx.send(Msg::Pfcp(vec![0x20, 0x02], stranger)).unwrap();
    tx.send(Msg::Pfcp(vec![0x20, 0x03], SocketAddr::V4(upf_addr))).unwrap();
    let started = Instant::now();
    let stop = thread::spawn(move || {
        thread::sleep(Duration::from_millis(200));
        drop(tx);
    });
    let why = edge.serve(&rx);
    assert!(matches!(why, edge::edge::Error::Fatal(_)), "{why}");
    assert!(started.elapsed() < Duration::from_millis(450), "timer 1 was cancelled, so nothing waits 500 ms");
    stop.join().unwrap();
    let mut buf = [0u8; 16];
    let (n, _) = upf.recv_from(&mut buf).unwrap();
    assert_eq!(&buf[..n], &[0x20, 0x03], "the datagram from the UPF is answered first");
    let (n, _) = upf.recv_from(&mut buf).unwrap();
    assert_eq!(&buf[..n], &[0x20, 0x01], "then timer 2 fires");
    drop(edge);
    assert_eq!(kernel.join().unwrap(), vec![Event::Config(vec![]), Event::PfcpData(vec![0x20, 0x03]), Event::TimerFired(2)]);
}

#[test]
fn expired_timers_fire_between_queued_events() {
    let upf = UdpSocket::bind((Ipv4Addr::LOCALHOST, 0)).unwrap();
    let upf_addr = match upf.local_addr().unwrap() {
        SocketAddr::V4(a) => a,
        _ => unreachable!(),
    };
    let (port, kernel) = fake_kernel(Box::new(|e| match e {
        Event::Config(_) => Some(vec![Action::TimerStart { timer: 1, ms: 0 }]),
        _ => Some(vec![]),
    }));
    let mut edge = Edge::new(connect(port), UdpSocket::bind((Ipv4Addr::LOCALHOST, 0)).unwrap(), upf_addr);
    edge.step(&Event::Config(vec![])).unwrap();
    let (tx, rx) = mpsc::channel();
    for b in [1, 2, 3] {
        tx.send(Msg::Pfcp(vec![b], SocketAddr::V4(upf_addr))).unwrap();
    }
    drop(tx);
    edge.serve(&rx);
    drop(edge);
    let pfcp = |b| Event::PfcpData(vec![b]);
    assert_eq!(kernel.join().unwrap(), vec![Event::Config(vec![]), pfcp(1), Event::TimerFired(1), pfcp(2), pfcp(3)]);
}
