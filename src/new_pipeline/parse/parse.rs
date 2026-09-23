use super::keywords::{
    ABSTRACT_PROP, ALGO, AXIOM, BY, CART, CLAIM, EVAL, EXAMPLE, FINITE_SEQ, FN, FOR, HAVE, IMPORT,
    LET, MATRIX, OBJ, OBTAIN, PREIMAGE, PROP, QUESTION_GOAL, RELEASE, SEQ, SETTING, SKETCH, STRATEGY,
    STRONG_INDUC, STRUCT, TEMPLATE, THM, TRUST, TRY, TUPLE, WITNESS,
};
use crate::new_pipeline::ast::stmt::Stmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeParseError, RuntimeResult};
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
    pub(super) fn parse_token_block(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        // Tokenizer never emits empty headers.
        let first = block.header[0].as_str();
        match first {
            PROP => self.parse_def_prop_stmt(block),
            ABSTRACT_PROP => self.parse_def_abstract_prop_stmt(block),
            LET => self.parse_let_stmt(block),
            HAVE => self.parse_have_dispatch(block),
            OBTAIN => self.parse_obtain_stmt(block),
            CLAIM => self.parse_claim_stmt(block),
            EXAMPLE => self.parse_example_stmt(block),
            THM => self.parse_def_thm_stmt(block),
            AXIOM => self.parse_axiom_stmt(block),
            STRATEGY => self.parse_def_strategy_stmt(block),
            SKETCH => self.parse_sketch_stmt(block),
            TRY => self.parse_try_stmt(block),
            QUESTION_GOAL => Err(RuntimeParseError::new(
                "top-level `?` is not supported; use it as a goal inside claim/example/thm/by/strategy",
                block.line,
                block.source_path.clone(),
            )
            .into()),
            TRUST => self.parse_trust_stmt(block),
            IMPORT => Err(RuntimeParseError::new(
                format!(
                    "`import` is not a {} statement; declare dependencies in litex.config",
                    crate::new_pipeline::LITEX
                ),
                block.line,
                block.source_path.clone(),
            )
            .into()),
            EVAL => self.parse_eval_stmt(block),
            WITNESS => self.parse_witness_stmt(block),
            STRUCT => self.parse_def_struct_stmt(block),
            TEMPLATE => self.parse_def_template_stmt(block),
            SETTING => self.parse_def_setting_stmt(block),
            STRONG_INDUC => Err(RuntimeParseError::new(
                "`strong_induc` is only valid after `by`",
                block.line,
                block.source_path.clone(),
            )
            .into()),
            RELEASE => match block.header.get(1).map(String::as_str) {
                Some(THM) => self.parse_release_thm_stmt(block),
                Some(STRUCT) => self.parse_release_struct_def_stmt(block),
                Some(OBJ) => self.parse_release_obj_def_stmt(block),
                _ => Err(RuntimeParseError::new(
                    "release: expected `thm …`, `struct def …`, or `obj def …`",
                    block.line,
                    block.source_path.clone(),
                )
                .into()),
            },
            BY => self.parse_by_stmt(block),
            _ => self.parse_fact_stmt(block),
        }
    }

    fn parse_have_dispatch(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        match block.header.get(1).map(String::as_str) {
            Some(ALGO) => match block.header.get(2).map(String::as_str) {
                Some(FOR) => Err(RuntimeParseError::new(
                    "have algo for: not wired yet in new_pipeline",
                    block.line,
                    block.source_path.clone(),
                )
                .into()),
                _ => Err(RuntimeParseError::new(
                    "have algo: expected `for …`",
                    block.line,
                    block.source_path.clone(),
                )
                .into()),
            },
            Some(TUPLE) | Some(CART) | Some(SEQ) | Some(FINITE_SEQ) | Some(MATRIX) => {
                Err(RuntimeParseError::new(
                    "removed; use have fn for indexed data",
                    block.line,
                    block.source_path.clone(),
                )
                .into())
            }
            Some(FN) => self.parse_have_fn_stmt(block),
            Some(BY) => match block.header.get(2).map(String::as_str) {
                // AST exists; exec not wired. Needed for multi-arg fn_range /
                // preimage naming (see HaveByPreimageStmt).
                Some(PREIMAGE) => Err(RuntimeParseError::new(
                    "have by preimage: not wired yet in new_pipeline",
                    block.line,
                    block.source_path.clone(),
                )
                .into()),
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
            Some(_) => self.parse_have_obj_stmt(block),
        }
    }
}
