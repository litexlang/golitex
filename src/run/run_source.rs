//! Source snapshot for output diagnostics. Line numbers belong to this submission.
use crate::runtime::CodeSource;
use crate::tokenize::TokenBlock;
use std::collections::BTreeMap;
use std::sync::Arc;

pub struct RunSource {
    pub origin: CodeSource,
    pub statements: Vec<usize>,
    code: Arc<str>,
    line_offsets: Vec<usize>,
    blocks: BTreeMap<usize, SourceBlock>,
}

struct SourceBlock {
    end_line: usize,
    children: Vec<usize>,
}

impl RunSource {
    pub(super) fn new(code: &str, origin: CodeSource, blocks: &[TokenBlock]) -> Self {
        let mut line_offsets = vec![0];
        line_offsets.extend(code.match_indices('\n').map(|(index, _)| index + 1));
        let mut source = Self {
            origin,
            statements: blocks.iter().map(|block| block.line).collect(),
            code: blocks
                .first()
                .and_then(|block| block.source.clone())
                .unwrap_or_else(|| Arc::from(code)),
            line_offsets,
            blocks: BTreeMap::new(),
        };
        for block in blocks {
            source.insert_block(block);
        }
        source
    }

    pub fn line(&self, line: usize) -> Option<&str> {
        self.lines(line, line)
    }

    pub fn block(&self, line: usize) -> Option<&str> {
        let end = self.blocks.get(&line).map_or(line, |block| block.end_line);
        self.lines(line, end)
    }

    pub fn children(&self, line: usize) -> &[usize] {
        self.blocks.get(&line).map_or(&[], |block| &block.children)
    }

    fn insert_block(&mut self, block: &TokenBlock) -> usize {
        let mut end_line = block.line;
        if let Some(span) = block.token_spans.last() {
            end_line = end_line.max(
                self.line_offsets
                    .partition_point(|offset| *offset < span.end),
            );
        }
        for child in &block.body {
            end_line = end_line.max(self.insert_block(child));
        }
        self.blocks.insert(
            block.line,
            SourceBlock {
                end_line,
                children: block.body.iter().map(|child| child.line).collect(),
            },
        );
        end_line
    }

    fn lines(&self, first: usize, last: usize) -> Option<&str> {
        let start = *self.line_offsets.get(first.checked_sub(1)?)?;
        let end = self
            .line_offsets
            .get(last)
            .copied()
            .unwrap_or(self.code.len());
        self.code.get(start..end).map(|text| {
            text.strip_suffix("\r\n")
                .or_else(|| text.strip_suffix('\n'))
                .unwrap_or(text)
        })
    }
}
