//! Minimal JSON Value + parse/stringify (no external crates).
//! Enough for knowledge_base wire formats: object / array / string / number / bool / null.
//! Object fields keep insertion order (human-facing Normal JSON care about key order).

use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<JsonValue>),
    Object(JsonObject),
}

/// Ordered JSON object. Iteration / stringify follow insertion order.
/// Equality ignores key order (same keys and values).
#[derive(Clone, Debug, Default)]
pub struct JsonObject {
    entries: Vec<(String, JsonValue)>,
}

impl PartialEq for JsonObject {
    fn eq(&self, other: &Self) -> bool {
        if self.entries.len() != other.entries.len() {
            return false;
        }
        for (key, value) in &self.entries {
            match other.get(key) {
                Some(other_value) if other_value == value => {}
                _ => return false,
            }
        }
        true
    }
}

impl JsonObject {
    pub fn new() -> Self {
        JsonObject {
            entries: Vec::new(),
        }
    }

    pub fn from_entries(entries: Vec<(String, JsonValue)>) -> Self {
        let mut object = JsonObject::new();
        for (key, value) in entries {
            object.insert(key, value);
        }
        object
    }

    pub fn insert(&mut self, key: String, value: JsonValue) {
        if let Some((_, existing)) = self.entries.iter_mut().find(|(k, _)| *k == key) {
            *existing = value;
            return;
        }
        self.entries.push((key, value));
    }

    pub fn get(&self, key: &str) -> Option<&JsonValue> {
        self.entries
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, value)| value)
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&String, &JsonValue)> {
        self.entries.iter().map(|(k, v)| (k, v))
    }

    pub fn keys_in_order(&self) -> Vec<&str> {
        self.entries.iter().map(|(k, _)| k.as_str()).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonError(pub String);

impl fmt::Display for JsonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl JsonValue {
    pub fn object_from(entries: Vec<(String, JsonValue)>) -> Self {
        JsonValue::Object(JsonObject::from_entries(entries))
    }

    pub fn as_object(&self) -> Result<&JsonObject, JsonError> {
        match self {
            JsonValue::Object(map) => Ok(map),
            _ => Err(JsonError("expected JSON object".to_string())),
        }
    }

    pub fn as_array(&self) -> Result<&[JsonValue], JsonError> {
        match self {
            JsonValue::Array(items) => Ok(items),
            _ => Err(JsonError("expected JSON array".to_string())),
        }
    }

    pub fn as_str(&self) -> Result<&str, JsonError> {
        match self {
            JsonValue::String(s) => Ok(s),
            _ => Err(JsonError("expected JSON string".to_string())),
        }
    }

    pub fn as_u64(&self) -> Result<u64, JsonError> {
        // u64::MAX rounds up to 2^64 in f64, so this bound is exclusive.
        match self {
            JsonValue::Number(n)
                if n.is_finite() && *n >= 0.0 && *n < (u64::MAX as f64) && n.fract() == 0.0 => {
                Ok(*n as u64)
            }
            _ => Err(JsonError(
                "expected non-negative integer JSON number within u64 range".to_string(),
            )),
        }
    }

    pub fn get<'a>(map: &'a JsonObject, key: &str) -> Result<&'a JsonValue, JsonError> {
        map.get(key)
            .ok_or_else(|| JsonError(format!("missing JSON field `{key}`")))
    }

    pub fn stringify(&self) -> String {
        let mut out = String::new();
        write_value_compact(&mut out, self);
        out
    }

    /// Pretty JSON with 2-space indent (human-facing goldens / examples).
    pub fn stringify_pretty(&self) -> String {
        let mut out = String::new();
        write_value_pretty(&mut out, self, 0);
        out
    }

    pub fn parse(input: &str) -> Result<JsonValue, JsonError> {
        let mut parser = Parser {
            bytes: input.as_bytes(),
            index: 0,
        };
        parser.skip_ws();
        let value = parser.parse_value()?;
        parser.skip_ws();
        if parser.index != parser.bytes.len() {
            return Err(JsonError("trailing input after JSON value".to_string()));
        }
        Ok(value)
    }
}

fn write_value_compact(out: &mut String, value: &JsonValue) {
    match value {
        JsonValue::Null => out.push_str("null"),
        JsonValue::Bool(true) => out.push_str("true"),
        JsonValue::Bool(false) => out.push_str("false"),
        JsonValue::Number(n) => write_number(out, *n),
        JsonValue::String(s) => write_string(out, s),
        JsonValue::Array(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_value_compact(out, item);
            }
            out.push(']');
        }
        JsonValue::Object(map) => {
            out.push('{');
            for (i, (key, value)) in map.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_string(out, key);
                out.push(':');
                write_value_compact(out, value);
            }
            out.push('}');
        }
    }
}

fn write_value_pretty(out: &mut String, value: &JsonValue, depth: usize) {
    match value {
        JsonValue::Null => out.push_str("null"),
        JsonValue::Bool(true) => out.push_str("true"),
        JsonValue::Bool(false) => out.push_str("false"),
        JsonValue::Number(n) => write_number(out, *n),
        JsonValue::String(s) => write_string(out, s),
        JsonValue::Array(items) if items.is_empty() => out.push_str("[]"),
        JsonValue::Array(items) => {
            out.push('[');
            out.push('\n');
            for (i, item) in items.iter().enumerate() {
                write_indent(out, depth + 1);
                write_value_pretty(out, item, depth + 1);
                if i + 1 < items.len() {
                    out.push(',');
                }
                out.push('\n');
            }
            write_indent(out, depth);
            out.push(']');
        }
        JsonValue::Object(map) if map.is_empty() => out.push_str("{}"),
        JsonValue::Object(map) => {
            out.push('{');
            out.push('\n');
            let len = map.len();
            for (i, (key, value)) in map.iter().enumerate() {
                write_indent(out, depth + 1);
                write_string(out, key);
                out.push_str(": ");
                write_value_pretty(out, value, depth + 1);
                if i + 1 < len {
                    out.push(',');
                }
                out.push('\n');
            }
            write_indent(out, depth);
            out.push('}');
        }
    }
}

fn write_indent(out: &mut String, depth: usize) {
    for _ in 0..depth {
        out.push_str("  ");
    }
}

fn write_number(out: &mut String, n: f64) {
    if n.is_finite() && n.fract() == 0.0 && n >= 0.0 && n < (u64::MAX as f64) {
        out.push_str(&(n as u64).to_string());
    } else {
        out.push_str(&n.to_string());
    }
}

fn write_string(out: &mut String, s: &str) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

struct Parser<'a> {
    bytes: &'a [u8],
    index: usize,
}

impl<'a> Parser<'a> {
    fn skip_ws(&mut self) {
        while let Some(b) = self.peek() {
            if matches!(b, b' ' | b'\n' | b'\r' | b'\t') {
                self.index += 1;
            } else {
                break;
            }
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.index).copied()
    }

    fn bump(&mut self) -> Result<u8, JsonError> {
        let b = self
            .peek()
            .ok_or_else(|| JsonError("unexpected end of JSON".to_string()))?;
        self.index += 1;
        Ok(b)
    }

    fn parse_value(&mut self) -> Result<JsonValue, JsonError> {
        self.skip_ws();
        match self.peek() {
            Some(b'n') => self.parse_null(),
            Some(b't') => self.parse_true(),
            Some(b'f') => self.parse_false(),
            Some(b'"') => Ok(JsonValue::String(self.parse_string()?)),
            Some(b'[') => self.parse_array(),
            Some(b'{') => self.parse_object(),
            Some(b'-') | Some(b'0'..=b'9') => self.parse_number(),
            Some(b) => Err(JsonError(format!(
                "unexpected JSON byte `{}`",
                b as char
            ))),
            None => Err(JsonError("unexpected end of JSON".to_string())),
        }
    }

    fn parse_null(&mut self) -> Result<JsonValue, JsonError> {
        self.expect_literal(b"null")?;
        Ok(JsonValue::Null)
    }

    fn parse_true(&mut self) -> Result<JsonValue, JsonError> {
        self.expect_literal(b"true")?;
        Ok(JsonValue::Bool(true))
    }

    fn parse_false(&mut self) -> Result<JsonValue, JsonError> {
        self.expect_literal(b"false")?;
        Ok(JsonValue::Bool(false))
    }

    fn expect_literal(&mut self, lit: &[u8]) -> Result<(), JsonError> {
        for expected in lit {
            let got = self.bump()?;
            if got != *expected {
                return Err(JsonError(format!(
                    "expected `{}`, got `{}`",
                    *expected as char, got as char
                )));
            }
        }
        Ok(())
    }

    fn parse_array(&mut self) -> Result<JsonValue, JsonError> {
        self.bump()?; // '['
        self.skip_ws();
        let mut items = Vec::new();
        if self.peek() == Some(b']') {
            self.bump()?;
            return Ok(JsonValue::Array(items));
        }
        loop {
            items.push(self.parse_value()?);
            self.skip_ws();
            match self.bump()? {
                b',' => {
                    self.skip_ws();
                    continue;
                }
                b']' => break,
                b => {
                    return Err(JsonError(format!(
                        "expected `,` or `]` in array, got `{}`",
                        b as char
                    )))
                }
            }
        }
        Ok(JsonValue::Array(items))
    }

    fn parse_object(&mut self) -> Result<JsonValue, JsonError> {
        self.bump()?; // '{'
        self.skip_ws();
        let mut object = JsonObject::new();
        if self.peek() == Some(b'}') {
            self.bump()?;
            return Ok(JsonValue::Object(object));
        }
        loop {
            self.skip_ws();
            let key = self.parse_string()?;
            self.skip_ws();
            let colon = self.bump()?;
            if colon != b':' {
                return Err(JsonError("expected `:` after object key".to_string()));
            }
            let value = self.parse_value()?;
            object.insert(key, value);
            self.skip_ws();
            match self.bump()? {
                b',' => continue,
                b'}' => break,
                b => {
                    return Err(JsonError(format!(
                        "expected `,` or `}}` in object, got `{}`",
                        b as char
                    )))
                }
            }
        }
        Ok(JsonValue::Object(object))
    }

    fn parse_string(&mut self) -> Result<String, JsonError> {
        if self.bump()? != b'"' {
            return Err(JsonError("expected string opening quote".to_string()));
        }
        let mut out = Vec::new();
        loop {
            match self.bump()? {
                b'"' => break,
                b'\\' => match self.bump()? {
                    b'"' => out.push(b'"'),
                    b'\\' => out.push(b'\\'),
                    b'/' => out.push(b'/'),
                    b'b' => out.push(0x08),
                    b'f' => out.push(0x0c),
                    b'n' => out.push(b'\n'),
                    b'r' => out.push(b'\r'),
                    b't' => out.push(b'\t'),
                    b'u' => {
                        let mut code = self.parse_hex_quad()?;
                        if (0xd800..=0xdbff).contains(&code) {
                            if self.bump()? != b'\\' || self.bump()? != b'u' {
                                return Err(JsonError("expected low Unicode surrogate".to_string()));
                            }
                            let low = self.parse_hex_quad()?;
                            if !(0xdc00..=0xdfff).contains(&low) {
                                return Err(JsonError("invalid low Unicode surrogate".to_string()));
                            }
                            code = 0x10000 + ((code - 0xd800) << 10) + low - 0xdc00;
                        }
                        let ch = char::from_u32(code)
                            .ok_or_else(|| JsonError("invalid unicode escape".to_string()))?;
                        let mut encoded = [0; 4];
                        out.extend_from_slice(ch.encode_utf8(&mut encoded).as_bytes());
                    }
                    b => {
                        return Err(JsonError(format!(
                            "invalid JSON string escape `\\{}`",
                            b as char
                        )))
                    }
                },
                0x00..=0x1f => {
                    return Err(JsonError("unescaped control character in JSON string".to_string()));
                }
                b => out.push(b),
            }
        }
        String::from_utf8(out)
            .map_err(|_| JsonError("invalid UTF-8 in JSON string".to_string()))
    }

    fn parse_hex_quad(&mut self) -> Result<u32, JsonError> {
        let mut code = 0;
        for _ in 0..4 {
            code = code * 16
                + hex_digit(self.bump()?).ok_or_else(|| {
                    JsonError("invalid \\u escape in JSON string".to_string())
                })?;
        }
        Ok(code)
    }

    fn parse_number(&mut self) -> Result<JsonValue, JsonError> {
        let mut s = String::new();
        if self.peek() == Some(b'-') {
            s.push('-');
            self.index += 1;
        }
        if self.peek() == Some(b'0') {
            s.push('0');
            self.index += 1;
        } else {
            let mut any = false;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                s.push(self.bump()? as char);
                any = true;
            }
            if !any {
                return Err(JsonError("invalid JSON number".to_string()));
            }
        }
        if self.peek() == Some(b'.') {
            s.push('.');
            self.index += 1;
            let mut any = false;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                s.push(self.bump()? as char);
                any = true;
            }
            if !any {
                return Err(JsonError("invalid JSON number fraction".to_string()));
            }
        }
        if matches!(self.peek(), Some(b'e') | Some(b'E')) {
            s.push(self.bump()? as char);
            if matches!(self.peek(), Some(b'+') | Some(b'-')) {
                s.push(self.bump()? as char);
            }
            let mut any = false;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                s.push(self.bump()? as char);
                any = true;
            }
            if !any {
                return Err(JsonError("invalid JSON number exponent".to_string()));
            }
        }
        let n: f64 = s
            .parse()
            .map_err(|_| JsonError(format!("invalid JSON number `{s}`")))?;
        if !n.is_finite() {
            return Err(JsonError(format!("JSON number `{s}` exceeds the finite numeric range")));
        }
        Ok(JsonValue::Number(n))
    }
}

fn hex_digit(b: u8) -> Option<u32> {
    match b {
        b'0'..=b'9' => Some((b - b'0') as u32),
        b'a'..=b'f' => Some((b - b'a') as u32 + 10),
        b'A'..=b'F' => Some((b - b'A') as u32 + 10),
        _ => None,
    }
}
