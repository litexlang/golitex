use super::keywords::{
    ABSTRACT_PROP, ALGO, AXIOM, BY, CART, CLAIM, EVAL, EXAMPLE, FINITE_SEQ, FN, FOR, HAVE, IMPORT,
    LET, MATRIX, OBTAIN, PREIMAGE, PROP, QUESTION_GOAL, RELEASE, SEQ, SETTING, SKETCH, STRATEGY,
    STRONG_INDUC, STRUCT, TEMPLATE, THM, TRUST, TRY, TUPLE, WITNESS,
};
use crate::new_pipeline::ast::stmt::Stmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    /// Parse token blocks into new-pipeline statements.
    pub fn parse(&mut self, token_blocks: &[TokenBlock]) -> RuntimeResult<Vec<Stmt>> {
        let mut stmts = Vec::new();
        for block in token_blocks {
            stmts.push(self.parse_token_block(block)?);
        }
        Ok(stmts)
    }

    // Match the leading token, then hand off to the statement family parser.
    fn parse_token_block(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let Some(first) = block.header.first().map(String::as_str) else {
            return Err(RuntimeParseError::new(
                "empty statement",
                block.line,
                block.source_path.clone(),
            )
            .into());
        };

        match first {
            PROP => self.unsupported_stmt(block, "prop"),
            ABSTRACT_PROP => self.unsupported_stmt(block, "abstract_prop"),
            LET => self.parse_let_stmt(block),
            HAVE => self.parse_have_dispatch(block),
            OBTAIN => self.unsupported_stmt(block, "obtain"),
            CLAIM => self.unsupported_stmt(block, "claim"),
            EXAMPLE => self.unsupported_stmt(block, "example"),
            THM => self.unsupported_stmt(block, "thm"),
            AXIOM => self.unsupported_stmt(block, "axiom"),
            STRATEGY => self.unsupported_stmt(block, "strategy"),
            SKETCH => self.unsupported_stmt(block, "sketch"),
            TRY => self.unsupported_stmt(block, "try"),
            QUESTION_GOAL => Err(RuntimeParseError::new(
                "top-level `?` is not supported; use it as a goal inside claim/example/thm/by/strategy",
                block.line,
                block.source_path.clone(),
            )
            .into()),
            TRUST => self.unsupported_stmt(block, "trust"),
            IMPORT => Err(RuntimeParseError::new(
                "`import` is not a Litex statement; declare dependencies in litex.config",
                block.line,
                block.source_path.clone(),
            )
            .into()),
            EVAL => self.unsupported_stmt(block, "eval"),
            WITNESS => self.unsupported_stmt(block, "witness"),
            STRUCT => self.unsupported_stmt(block, "struct"),
            TEMPLATE => self.unsupported_stmt(block, "template"),
            SETTING => self.unsupported_stmt(block, "setting"),
            STRONG_INDUC => Err(RuntimeParseError::new(
                "`strong_induc` is only valid after `by`",
                block.line,
                block.source_path.clone(),
            )
            .into()),
            RELEASE => match block.header.get(1).map(String::as_str) {
                Some(THM) => self.unsupported_stmt(block, "release thm"),
                _ => Err(RuntimeParseError::new(
                    "release: expected `thm …`",
                    block.line,
                    block.source_path.clone(),
                )
                .into()),
            },
            BY => self.unsupported_stmt(block, "by"),
            _ => self.parse_fact_stmt(block),
        }
    }

    fn parse_have_dispatch(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        match block.header.get(1).map(String::as_str) {
            Some(ALGO) => match block.header.get(2).map(String::as_str) {
                Some(FOR) => self.unsupported_stmt(block, "have algo for"),
                _ => Err(RuntimeParseError::new(
                    "have algo: expected `for …`",
                    block.line,
                    block.source_path.clone(),
                )
                .into()),
            },
            Some(TUPLE) => self.unsupported_stmt(block, "have tuple"),
            Some(CART) => self.unsupported_stmt(block, "have cart"),
            Some(SEQ) => self.unsupported_stmt(block, "have seq"),
            Some(FINITE_SEQ) => self.unsupported_stmt(block, "have finite_seq"),
            Some(MATRIX) => self.unsupported_stmt(block, "have matrix"),
            Some(FN) => self.unsupported_stmt(block, "have fn"),
            Some(BY) => match block.header.get(2).map(String::as_str) {
                Some(PREIMAGE) => self.unsupported_stmt(block, "have by preimage"),
                _ => Err(RuntimeParseError::new(
                    "have by: expected `preimage`",
                    block.line,
                    block.source_path.clone(),
                )
                .into()),
            },
            None => Err(RuntimeParseError::new(
                "have: expected object definition, `fn`, or `by preimage`",
                block.line,
                block.source_path.clone(),
            )
            .into()),
            Some(_) => self.unsupported_stmt(block, "have"),
        }
    }

    fn unsupported_stmt(&self, block: &TokenBlock, kind: &str) -> RuntimeResult<Stmt> {
        Err(RuntimeError::Unsupported(format!(
            "parse: `{kind}` statements are not wired yet (line {} in {})",
            block.line, block.source_path
        )))
    }
}
