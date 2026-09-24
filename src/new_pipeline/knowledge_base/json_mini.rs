//! Minimal JSON Value + parse/stringify (no external crates).
//! Enough for knowledge_base wire formats: object / array / string / number / bool / null.

use std::collections::BTreeMap;
use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<JsonValue>),
    Object(BTreeMap<String, JsonValue>),
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
        let mut map = BTreeMap::new();
        for (key, value) in entries {
            map.insert(key, value);
        }
        JsonValue::Object(map)
    }

    pub fn as_object(&self) -> Result<&BTreeMap<String, JsonValue>, JsonError> {
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
        match self {
            JsonValue::Number(n) if n.is_finite() && *n >= 0.0 && n.fract() == 0.0 => {
                Ok(*n as u64)
            }
            _ => Err(JsonError("expected non-negative integer JSON number".to_string())),
        }
    }

    pub fn get<'a>(
        map: &'a BTreeMap<String, JsonValue>,
        key: &str,
    ) -> Result<&'a JsonValue, JsonError> {
        map.get(key)
            .ok_or_else(|| JsonError(format!("missing JSON field `{key}`")))
    }

    pub fn stringify(&self) -> String {
        let mut out = String::new();
        write_value(&mut out, self);
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

fn write_value(out: &mut String, value: &JsonValue) {
    match value {
        JsonValue::Null => out.push_str("null"),
        JsonValue::Bool(true) => out.push_str("true"),
        JsonValue::Bool(false) => out.push_str("false"),
        JsonValue::Number(n) => {
            if n.is_finite() && n.fract() == 0.0 && *n >= 0.0 && *n <= (u64::MAX as f64) {
                out.push_str(&(*n as u64).to_string());
            } else {
                out.push_str(&n.to_string());
            }
        }
        JsonValue::String(s) => write_string(out, s),
        JsonValue::Array(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_value(out, item);
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
                write_value(out, value);
            }
            out.push('}');
        }
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
            if b.is_ascii_whitespace() {
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
        let mut map = BTreeMap::new();
        if self.peek() == Some(b'}') {
            self.bump()?;
            return Ok(JsonValue::Object(map));
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
            map.insert(key, value);
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
        Ok(JsonValue::Object(map))
    }

    fn parse_string(&mut self) -> Result<String, JsonError> {
        if self.bump()? != b'"' {
            return Err(JsonError("expected string opening quote".to_string()));
        }
        let mut out = String::new();
        loop {
            match self.bump()? {
                b'"' => break,
                b'\\' => match self.bump()? {
                    b'"' => out.push('"'),
                    b'\\' => out.push('\\'),
                    b'/' => out.push('/'),
                    b'n' => out.push('\n'),
                    b'r' => out.push('\r'),
                    b't' => out.push('\t'),
                    b'u' => {
                        let mut code = 0u32;
                        for _ in 0..4 {
                            let h = self.bump()?;
                            code = code * 16
                                + hex_digit(h).ok_or_else(|| {
                                    JsonError("invalid \\u escape in JSON string".to_string())
                                })?;
                        }
                        out.push(
                            char::from_u32(code)
                                .ok_or_else(|| JsonError("invalid unicode escape".to_string()))?,
                        );
                    }
                    b => {
                        return Err(JsonError(format!(
                            "invalid JSON string escape `\\{}`",
                            b as char
                        )))
                    }
                },
                b => out.push(b as char),
            }
        }
        Ok(out)
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
