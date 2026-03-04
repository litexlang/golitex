use crate::errors::ParseBlockError;
use crate::tokenizer::tokenize_line;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenBlock {
    pub header: Vec<String>,
    pub body: Vec<BlockItem>,
    pub parse_index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockItem {
    Line(String),
    Block(TokenBlock),
}

fn indent_level(line: &str) -> usize {
    let mut n = 0;
    for c in line.chars() {
        match c {
            ' ' => n += 1,
            '\t' => n += 4,
            _ => break,
        }
    }
    n
}

fn ends_with_colon(s: &str) -> bool {
    s.trim_end().ends_with(':')
}

pub fn parse_blocks(s: &str) -> Result<Vec<BlockItem>, ParseBlockError> {
    let lines: Vec<_> = s.lines().collect();
    let mut i = 0;
    parse_level(&lines, &mut i, 0)
}

fn parse_level(
    lines: &[&str],
    i: &mut usize,
    base_indent: usize,
) -> Result<Vec<BlockItem>, ParseBlockError> {
    let mut items = Vec::new();
    let mut body_indent = None;

    while *i < lines.len() {
        let raw = lines[*i];
        let line_no = *i + 1;
        let indent = indent_level(raw);
        let content = raw.trim();

        if content.is_empty() {
            *i += 1;
            continue;
        }

        if indent < base_indent {
            break;
        }

        if indent > base_indent {
            return Err(ParseBlockError::UnexpectedIndent { line: line_no });
        }

        *i += 1;

        if ends_with_colon(content) {
            // 必须有 body
            if *i >= lines.len() {
                return Err(ParseBlockError::MissingBody { line: line_no });
            }

            let next_indent = indent_level(lines[*i]);
            if next_indent <= indent {
                return Err(ParseBlockError::ExpectedIndent { line: *i + 1 });
            }

            let body = parse_level(lines, i, next_indent)?;

            let header_tokens = tokenize_line(content);
            
            items.push(BlockItem::Block(TokenBlock {
                header: header_tokens,
                body,
                parse_index: 0,
            }));
        } else {
            items.push(BlockItem::Line(content.to_string()));
        }

        if let Some(expected) = body_indent {
            if indent != expected {
                return Err(ParseBlockError::InconsistentIndent { line: line_no });
            }
        } else {
            body_indent = Some(indent);
        }
    }

    Ok(items)
}

impl TokenBlock {
    pub fn current_token(&self) -> Option<&str> {
        self.header.get(self.parse_index).map(|s| s.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let r = parse_blocks("").unwrap();
        assert!(r.is_empty());
        let r = parse_blocks("\n\n  \n").unwrap();
        assert!(r.is_empty());
    }

    #[test]
    fn test_flat_lines() {
        let r = parse_blocks("a\nb\nc").unwrap();
        assert_eq!(r.len(), 3);
        assert!(matches!(&r[0], BlockItem::Line(s) if s == "a"));
        assert!(matches!(&r[1], BlockItem::Line(s) if s == "b"));
        assert!(matches!(&r[2], BlockItem::Line(s) if s == "c"));
    }

    #[test]
    fn test_one_block_with_body() {
        let r = parse_blocks("x:\n  y").unwrap();
        assert_eq!(r.len(), 1);
        let BlockItem::Block(b) = &r[0] else { panic!("expected Block") };
        assert_eq!(b.header, vec!["x", ":"]);
        assert_eq!(b.body.len(), 1);
        assert!(matches!(&b.body[0], BlockItem::Line(s) if s == "y"));
    }

    #[test]
    fn test_two_top_blocks() {
        let r = parse_blocks("def f():\n  pass\ndef g():\n  pass").unwrap();
        assert_eq!(r.len(), 2);
        let BlockItem::Block(b1) = &r[0] else { panic!() };
        assert!(b1.header.iter().any(|s| s == "def"));
        assert_eq!(b1.body.len(), 1);
        assert!(matches!(&b1.body[0], BlockItem::Line(s) if s == "pass"));
        let BlockItem::Block(b2) = &r[1] else { panic!() };
        assert_eq!(b2.body.len(), 1);
        assert!(matches!(&b2.body[0], BlockItem::Line(s) if s == "pass"));
    }

    #[test]
    fn test_nested_block() {
        let r = parse_blocks("a:\n  b:\n    c").unwrap();
        assert_eq!(r.len(), 1);
        let BlockItem::Block(outer) = &r[0] else { panic!() };
        assert_eq!(outer.body.len(), 1);
        let BlockItem::Block(inner) = &outer.body[0] else { panic!() };
        assert_eq!(inner.body.len(), 1);
        assert!(matches!(&inner.body[0], BlockItem::Line(s) if s == "c"));
    }

    #[test]
    fn test_missing_body() {
        let e = parse_blocks("a:").unwrap_err();
        assert!(matches!(e, ParseBlockError::MissingBody { .. }));
    }

    #[test]
    fn test_expected_indent() {
        let e = parse_blocks("a:\nnext").unwrap_err();
        assert!(matches!(e, ParseBlockError::ExpectedIndent { .. }));
    }

    #[test]
    fn test_unexpected_indent() {
        let e = parse_blocks("  oops").unwrap_err();
        assert!(matches!(e, ParseBlockError::UnexpectedIndent { .. }));
    }
}