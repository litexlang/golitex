//! Compact a child process's JSON transport without changing any string bytes.
//! Parsing and mathematical evidence remain owned by the existing producer.

use std::io::{self, BufWriter, Read, Write};

pub(super) fn compact_json_output(mut input: impl Read, output: impl Write) -> io::Result<u64> {
    let mut output = BufWriter::new(output);
    let mut buffer = [0; 32 * 1024];
    let mut compact = Vec::with_capacity(buffer.len());
    let mut in_string = false;
    let mut escaped = false;
    let mut written = 0;
    loop {
        let count = match input.read(&mut buffer) {
            Ok(0) => break,
            Ok(count) => count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        };
        compact.clear();
        for &byte in &buffer[..count] {
            if in_string {
                compact.push(byte);
                if escaped {
                    escaped = false;
                } else if byte == b'\\' {
                    escaped = true;
                } else if byte == b'"' {
                    in_string = false;
                }
            } else if !matches!(byte, b' ' | b'\t' | b'\r' | b'\n') {
                compact.push(byte);
                in_string = byte == b'"';
            }
        }
        output.write_all(&compact)?;
        written += compact.len() as u64;
    }
    output.flush()?;
    Ok(written)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::knowledge_base::JsonValue;

    struct Chunks<'a> {
        bytes: &'a [u8],
        width: usize,
    }

    impl Read for Chunks<'_> {
        fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
            let count = output.len().min(self.width).min(self.bytes.len());
            output[..count].copy_from_slice(&self.bytes[..count]);
            self.bytes = &self.bytes[count..];
            Ok(count)
        }
    }

    #[test]
    fn preserves_json_values_and_string_bytes_at_every_chunk_boundary() {
        let input = r##" {
            "source": "# 中文 \\\\ path \"quote\"\n  x = x\t",
            "escape": "\\\" \\u2200 ",
            "facts": [1, -2.5, true, null, {"name": "a b"}]
        } "##;
        let expected = JsonValue::parse(input).unwrap();
        for width in 1..=37 {
            let mut output = Vec::new();
            let count = compact_json_output(
                Chunks {
                    bytes: input.as_bytes(),
                    width,
                },
                &mut output,
            )
            .unwrap();
            assert_eq!(count as usize, output.len());
            let output = String::from_utf8(output).unwrap();
            assert_eq!(JsonValue::parse(&output).unwrap(), expected);
            assert_eq!(output, expected.stringify());
            assert!(output.contains(r#"# 中文 \\\\ path \"quote\"\n  x = x\t"#));
        }
    }

    #[test]
    fn preserves_large_string_content_across_internal_buffers() {
        let source = "  数学 \" \\ \n\t".repeat(10000);
        let value = JsonValue::object_from(vec![("content".into(), JsonValue::String(source))]);
        let mut output = Vec::new();
        compact_json_output(value.stringify_pretty().as_bytes(), &mut output).unwrap();
        assert_eq!(String::from_utf8(output).unwrap(), value.stringify());
    }
}
