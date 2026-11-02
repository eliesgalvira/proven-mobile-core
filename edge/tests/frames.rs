//! The frame codec against test-vectors/frames.json, the bytes the kernel's
//! tests read too.

use edge::frame::{self, Action, Event, Tlv};
use serde_json::Value;

fn hex(v: &Value) -> Vec<u8> {
    let s = v.as_str().unwrap();
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn u32_of(v: &Value) -> u32 {
    v.as_u64().unwrap() as u32
}

fn event_of(v: &Value) -> Event {
    match v["kind"].as_str().unwrap() {
        "Config" => Event::Config(
            v["tlvs"].as_array().unwrap().iter().map(|t| Tlv { tag: u32_of(&t["tag"]) as u16, value: hex(&t["hex"]) }).collect(),
        ),
        "NgapAssocUp" => Event::NgapAssocUp(u32_of(&v["assoc"])),
        "NgapAssocDown" => Event::NgapAssocDown(u32_of(&v["assoc"])),
        "NgapData" => Event::NgapData { assoc: u32_of(&v["assoc"]), stream: u32_of(&v["stream"]) as u16, bytes: hex(&v["hex"]) },
        "PfcpData" => Event::PfcpData(hex(&v["hex"])),
        "TimerFired" => Event::TimerFired(u32_of(&v["timer"])),
        k => panic!("unknown event kind {k}"),
    }
}

fn action_of(v: &Value) -> Action {
    match v["kind"].as_str().unwrap() {
        "NgapSend" => Action::NgapSend { assoc: u32_of(&v["assoc"]), stream: u32_of(&v["stream"]) as u16, bytes: hex(&v["hex"]) },
        "NgapClose" => Action::NgapClose(u32_of(&v["assoc"])),
        "PfcpSend" => Action::PfcpSend(hex(&v["hex"])),
        "TimerStart" => Action::TimerStart { timer: u32_of(&v["timer"]), ms: u32_of(&v["ms"]) },
        "TimerCancel" => Action::TimerCancel(u32_of(&v["timer"])),
        "Log" => Action::Log { level: u32_of(&v["level"]) as u8, text: v["text"].as_str().unwrap().as_bytes().to_vec() },
        k => panic!("unknown action kind {k}"),
    }
}

fn vectors() -> Value {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../test-vectors/frames.json");
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

#[test]
fn every_event_vector_encodes_and_parses() {
    let doc = vectors();
    let entropy: [u8; 32] = hex(&doc["entropy"]).try_into().unwrap();
    for case in doc["events"].as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let event = event_of(&case["event"]);
        let body = frame::event_body(&entropy, &event);
        assert_eq!(frame::frame(&body), hex(&case["frame"]), "{name}: encoding");
        assert_eq!(frame::parse_event(&body), Ok((entropy, event)), "{name}: parsing");
        assert_eq!(frame::parse_event(&body[..body.len() - 1]), Err(frame::Error::Short), "{name}: one byte short");
    }
}

#[test]
fn every_actions_vector_encodes_and_parses() {
    let doc = vectors();
    for case in doc["actions"].as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let actions: Vec<Action> = case["actions"].as_array().unwrap().iter().map(action_of).collect();
        let body = frame::actions_body(&actions);
        assert_eq!(frame::frame(&body), hex(&case["frame"]), "{name}: encoding");
        assert_eq!(frame::parse_actions(&body), Ok(actions), "{name}: parsing");
    }
}

#[test]
fn malformed_frames_are_refused() {
    assert_eq!(frame::parse_actions(&[0x01, 0, 0]), Err(frame::Error::Invalid("not an Actions body")));
    assert_eq!(frame::parse_actions(&[0x80, 0, 1, 0x86, 4, 0, 0, 0, 0]), Err(frame::Error::Invalid("log level above 3")));
    assert_eq!(frame::parse_actions(&[0x80, 0, 2, 0x82, 0, 0, 0, 3]), Err(frame::Error::Short));
    assert_eq!(frame::parse_actions(&[0x80, 0, 0, 9]), Err(frame::Error::Trailing));
    assert_eq!(frame::parse_actions(&[0x80, 0, 1, 0x90]), Err(frame::Error::UnknownKind(0x90)));
    let mut over = (frame::MAX_BODY as u32 + 1).to_be_bytes().to_vec();
    over.extend([0u8; 8]);
    assert_eq!(frame::read_frame(&mut over.as_slice()).unwrap_err().kind(), std::io::ErrorKind::InvalidData);
    assert_eq!(frame::read_frame(&mut [0u8, 0, 0, 3, 1, 2].as_slice()).unwrap_err().kind(), std::io::ErrorKind::UnexpectedEof);
    assert_eq!(frame::read_frame(&mut [0u8, 0, 0, 3, 1, 2, 3, 4].as_slice()).unwrap(), vec![1, 2, 3]);
}
