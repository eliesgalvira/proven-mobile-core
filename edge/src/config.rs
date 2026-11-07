//! The operator's TOML (edge/config.example.toml) and its Config TLVs
//! (docs/spec/milestone-1.md § The frame protocol).

use std::fmt;
use std::fs;
use std::net::Ipv4Addr;
use std::path::Path;

use serde::Deserialize;

use crate::frame::{Tlv, MAX_CONFIG};

#[derive(Debug)]
pub enum Error {
    Read(std::io::Error),
    Toml(toml::de::Error),
    Field(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Read(e) => write!(f, "config: {e}"),
            Error::Toml(e) => write!(f, "config: {e}"),
            Error::Field(why) => write!(f, "config: {why}"),
        }
    }
}

impl std::error::Error for Error {}

#[derive(Debug, Deserialize)]
pub struct Config {
    pub kernel: Kernel,
    pub n2: N2,
    pub n4: N4,
    pub network: Network,
    pub slice: Slice,
    pub suci: Suci,
    pub nas: Nas,
    #[serde(default)]
    pub subscriber: Vec<Subscriber>,
}

#[derive(Debug, Deserialize)]
pub struct Kernel {
    pub path: String,
    pub port: u16,
}

#[derive(Debug, Deserialize)]
pub struct N2 {
    pub address: Ipv4Addr,
}

#[derive(Debug, Deserialize)]
pub struct N4 {
    pub smf: Ipv4Addr,
    pub upf: Ipv4Addr,
}

#[derive(Debug, Deserialize)]
pub struct Network {
    pub mcc: String,
    pub mnc: String,
    pub amf_region_id: u8,
    pub amf_set_id: u16,
    pub amf_pointer: u8,
    pub tac: u32,
    pub amf_name: String,
}

#[derive(Debug, Deserialize)]
pub struct Slice {
    pub sst: u8,
    pub dnn: String,
    pub ue_pool: String,
    pub dns: Ipv4Addr,
    pub upf_n3: Ipv4Addr,
}

#[derive(Debug, Deserialize)]
pub struct Suci {
    pub private_key: String,
    pub key_id: u8,
}

#[derive(Debug, Deserialize)]
pub struct Nas {
    pub ciphering: Vec<u8>,
    pub integrity: Vec<u8>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Subscriber {
    pub supi: String,
    pub k: String,
    pub opc: String,
    pub amf: String,
    pub sqn: String,
}

pub const N2_PORT: u16 = 38412;
pub const N4_PORT: u16 = 8805;

fn hex(name: &str, text: &str, len: usize) -> Result<Vec<u8>, Error> {
    let digits: Vec<u8> = text.bytes().filter(|b| !b.is_ascii_whitespace()).collect();
    let bad = || Error::Field(format!("{name} must be {len} bytes of hex"));
    if digits.len() != 2 * len {
        return Err(bad());
    }
    digits.chunks(2).map(|pair| u8::from_str_radix(std::str::from_utf8(pair).map_err(|_| bad())?, 16).map_err(|_| bad())).collect()
}

fn digits(name: &str, text: &str, min: usize, max: usize) -> Result<Vec<u8>, Error> {
    if text.len() < min || text.len() > max || !text.bytes().all(|b| b.is_ascii_digit()) {
        return Err(Error::Field(format!("{name} must be {min} to {max} decimal digits")));
    }
    Ok(text.bytes().map(|b| b - b'0').collect())
}

/// A variable-length value, which a TLV's 16-bit length must be able to carry.
fn value(name: &str, bytes: &[u8]) -> Result<Vec<u8>, Error> {
    if bytes.len() > u16::MAX as usize {
        return Err(Error::Field(format!("{name} takes at most {} bytes", u16::MAX)));
    }
    Ok(bytes.to_vec())
}

/// TS 24.501 PLMN: MCC digit 2 | digit 1, MNC digit 3 (or 0xF) | MCC digit 3, MNC digit 2 | digit 1.
fn plmn(mcc: &str, mnc: &str) -> Result<Vec<u8>, Error> {
    let mcc = digits("mcc", mcc, 3, 3)?;
    let mnc = digits("mnc", mnc, 2, 3)?;
    let mnc3 = if mnc.len() == 3 { mnc[2] } else { 0xF };
    Ok(vec![mcc[1] << 4 | mcc[0], mnc3 << 4 | mcc[2], mnc[1] << 4 | mnc[0]])
}

fn pool(text: &str) -> Result<(Ipv4Addr, u8), Error> {
    let bad = || Error::Field("ue_pool must be an IPv4 network such as 10.45.0.0/16".to_string());
    let (addr, prefix) = text.split_once('/').ok_or_else(bad)?;
    let addr: Ipv4Addr = addr.parse().map_err(|_| bad())?;
    let prefix: u8 = prefix.parse().map_err(|_| bad())?;
    if prefix > 30 {
        return Err(bad());
    }
    Ok((addr, prefix))
}

impl Config {
    pub fn load(path: &Path) -> Result<Config, Error> {
        let text = fs::read_to_string(path).map_err(Error::Read)?;
        toml::from_str(&text).map_err(Error::Toml)
    }

    pub fn tlvs(&self) -> Result<Vec<Tlv>, Error> {
        let (pool_base, prefix) = pool(&self.slice.ue_pool)?;
        if self.network.amf_set_id >= 1024 || self.network.amf_pointer >= 64 || self.network.tac >= 1 << 24 {
            return Err(Error::Field("amf_set_id takes 10 bits, amf_pointer 6, tac 24".to_string()));
        }
        let mut tlvs = vec![
            Tlv { tag: 0x0001, value: plmn(&self.network.mcc, &self.network.mnc)? },
            Tlv { tag: 0x0002, value: vec![self.network.amf_region_id] },
            Tlv { tag: 0x0003, value: self.network.amf_set_id.to_be_bytes().to_vec() },
            Tlv { tag: 0x0004, value: vec![self.network.amf_pointer] },
            Tlv { tag: 0x0005, value: self.network.tac.to_be_bytes()[1..].to_vec() },
            Tlv { tag: 0x0006, value: value("amf_name", self.network.amf_name.as_bytes())? },
            Tlv { tag: 0x0007, value: vec![self.slice.sst] },
            Tlv { tag: 0x0008, value: value("dnn", self.slice.dnn.as_bytes())? },
            Tlv { tag: 0x0009, value: pool_base.octets().to_vec() },
            Tlv { tag: 0x000A, value: vec![prefix] },
            Tlv { tag: 0x000B, value: self.slice.dns.octets().to_vec() },
            Tlv { tag: 0x000C, value: self.n4.smf.octets().to_vec() },
            Tlv { tag: 0x000D, value: self.slice.upf_n3.octets().to_vec() },
            Tlv { tag: 0x000E, value: self.n4.upf.octets().to_vec() },
            Tlv { tag: 0x000F, value: hex("suci.private_key", &self.suci.private_key, 32)? },
            Tlv { tag: 0x0010, value: vec![self.suci.key_id] },
            Tlv { tag: 0x0011, value: value("nas.ciphering", &self.nas.ciphering)? },
            Tlv { tag: 0x0012, value: value("nas.integrity", &self.nas.integrity)? },
        ];
        for s in &self.subscriber {
            let supi = digits("supi", &s.supi, 5, 15)?;
            let mut value = vec![supi.len() as u8];
            value.extend(supi.iter().map(|d| d + b'0'));
            value.extend(hex("k", &s.k, 16)?);
            value.extend(hex("opc", &s.opc, 16)?);
            value.extend(hex("amf", &s.amf, 2)?);
            value.extend(hex("sqn", &s.sqn, 6)?);
            tlvs.push(Tlv { tag: 0x0020, value });
        }
        let len: usize = tlvs.iter().map(|t| 4 + t.value.len()).sum();
        if len > MAX_CONFIG {
            return Err(Error::Field(format!("the config takes {len} bytes of TLVs, more than the {MAX_CONFIG} a frame carries")));
        }
        Ok(tlvs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn example() -> Config {
        Config::load(Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/config.example.toml"))).unwrap()
    }

    #[test]
    fn example_config_encodes_the_capture_bench() {
        let tlvs = example().tlvs().unwrap();
        let get = |tag: u16| tlvs.iter().filter(|t| t.tag == tag).map(|t| t.value.clone()).collect::<Vec<_>>();
        assert_eq!(get(0x0001), [vec![0x00, 0xF1, 0x10]]);
        assert_eq!(get(0x0003), [vec![0, 1]]);
        assert_eq!(get(0x0005), [vec![0, 0, 1]]);
        assert_eq!(get(0x0006), [b"speck-amf0".to_vec()]);
        assert_eq!(get(0x0009), [vec![10, 45, 0, 0]]);
        assert_eq!(get(0x000A), [vec![16]]);
        assert_eq!(get(0x0011), [vec![2]]);
        assert_eq!(get(0x000F)[0].len(), 32);
        let sub = &get(0x0020)[0];
        assert_eq!(sub.len(), 1 + 15 + 16 + 16 + 2 + 6);
        assert_eq!(&sub[..16], b"\x0f001010000000001");
        assert_eq!(&sub[48..], &[0x80, 0x00, 0, 0, 0, 0, 0, 0x40]);
        assert_eq!(tlvs.len(), 19);
    }

    #[test]
    fn values_a_tlv_or_a_frame_cannot_carry_are_refused() {
        let mut c = example();
        c.network.amf_name = "a".repeat(65_535);
        assert!(c.tlvs().is_ok());
        c.network.amf_name.push('a');
        assert!(c.tlvs().is_err());
        let mut c = example();
        c.nas.integrity = vec![2; 65_536];
        assert!(c.tlvs().is_err());
        let mut c = example();
        let one = c.subscriber.pop().unwrap();
        c.subscriber = vec![one.clone(); 4_365];
        assert!(c.tlvs().is_ok(), "4365 subscribers fit a frame body");
        c.subscriber.push(one);
        assert!(c.tlvs().is_err(), "4366 do not");
    }

    #[test]
    fn three_digit_mnc_and_bad_values_are_told_apart() {
        assert_eq!(plmn("310", "260").unwrap(), vec![0x13, 0x00, 0x62]);
        assert!(plmn("31", "260").is_err());
        assert!(hex("k", "00", 16).is_err());
        assert!(hex("k", "zz", 1).is_err());
        assert!(pool("10.45.0.0/33").is_err());
        assert_eq!(pool("10.45.0.0/16").unwrap(), (Ipv4Addr::new(10, 45, 0, 0), 16));
    }
}
