use crate::prelude::*;
use std::io::Read;

pub(super) fn object(fields: Vec<(&str, JsonValue)>) -> JsonValue {
    JsonValue::object_from(
        fields
            .into_iter()
            .map(|(key, value)| (key.into(), value))
            .collect(),
    )
}

pub(super) fn node(type_name: &str, variant: &str, fields: Vec<(&str, JsonValue)>) -> JsonValue {
    object(vec![
        ("type", JsonValue::String(type_name.into())),
        ("variant", JsonValue::String(variant.into())),
        ("fields", object(fields)),
    ])
}

pub(super) fn text(value: &str) -> JsonValue {
    JsonValue::String(value.into())
}

pub(super) fn strings(values: &[String]) -> JsonValue {
    JsonValue::Array(values.iter().map(|value| text(value)).collect())
}

/// Content fingerprint for cache identity, not a cryptographic signature.
pub(super) fn digest(source: &str) -> String {
    let mut hash = 0xcbf29ce484222325u64;
    for byte in source.bytes() {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{hash:016x}")
}

/// Identify the actual executable hosting this engine (including library
/// embedders). This is a reproducibility fingerprint, not a security signature.
pub(super) fn executable_digest() -> Option<String> {
    let path = std::env::current_exe().ok()?;
    let mut file = std::fs::File::open(path).ok()?;
    let mut hash = 0xcbf29ce484222325u64;
    let mut buffer = [0u8; 65536];
    loop {
        let count = file.read(&mut buffer).ok()?;
        if count == 0 {
            break;
        }
        for byte in &buffer[..count] {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
    }
    Some(format!("fnv1a64:{hash:016x}"))
}
