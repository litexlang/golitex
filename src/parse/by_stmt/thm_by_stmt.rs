use crate::prelude::*;

impl Runtime {
    pub fn parse_by_thm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(THM)?;
        let (name, args) = self.parse_theorem_call(tb)?;
        let selected_facts = if tb.current_token_is_equal_to(RIGHT_ARROW) {
            if !tb.body.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by thm: `=>` does not accept an indented body".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            tb.skip_token(RIGHT_ARROW)?;
            if tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by thm: `=>` expects one atomic fact".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let fact = self.parse_atomic_fact(tb, true)?;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by thm: `=>` expects exactly one atomic fact".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            Some(vec![fact.into()])
        } else if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            if !tb.exceed_end_of_head() || tb.body.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by thm: expects exactly one `? <atomic fact>` goal block and no proof body"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            Some(vec![self
                .parse_goal_atomic_fact_block(&mut tb.body[0], "by thm")?
                .into()])
        } else {
            if !tb.body.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by thm does not accept an indented body".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            None
        };
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by thm: unexpected token after theorem call".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByThmStmt::new(name, args, selected_facts, tb.line_file.clone()).into())
    }

    /// Parse the shared `name(args)` portion of an explicit theorem call.
    pub(crate) fn parse_theorem_call(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(AtomicName, Vec<Obj>), RuntimeError> {
        let name = if is_builtin_theorem_name(tb.current()?) && tb.token_at_add_index(1) != MOD_SIGN
        {
            AtomicName::WithoutMod(tb.advance()?)
        } else {
            self.parse_module_qualified_reference_name(tb)?
        };
        let args = self.parse_braced_objs(tb)?;
        Ok((name, args))
    }
}

#[cfg(test)]
mod tests {
    use crate::parse::Tokenizer;
    use crate::prelude::*;
    use std::rc::Rc;

    fn parse_one(source: &str) -> Result<Stmt, RuntimeError> {
        let mut runtime = Runtime::new();
        let mut blocks = Tokenizer::new()
            .parse_blocks(source, Rc::from("by_thm_selected_fact_test.lit"))
            .expect("tokenize by thm statement");
        assert_eq!(blocks.len(), 1);
        runtime.parse_stmt(&mut blocks[0])
    }

    #[test]
    fn by_thm_parses_optional_selected_atomic_fact() {
        let legacy = parse_one("by thm T(a)").expect("parse legacy by thm");
        let Stmt::By(ByStmt::ByThmStmt(legacy)) = legacy else {
            panic!("expected by thm statement")
        };
        assert!(legacy.selected_facts.is_none());

        let selected =
            parse_one("by thm T(a) => not $P(a)").expect("parse by thm with selected atomic fact");
        let Stmt::By(ByStmt::ByThmStmt(selected)) = selected else {
            panic!("expected by thm statement")
        };
        assert!(selected.selected_facts.as_ref().is_some_and(
            |facts| matches!(facts.as_slice(), [Fact::AtomicFact(fact)] if !fact.is_true())
        ));
        assert_eq!(selected.to_string(), "by thm T(a) => not $P(a)");

        let goal_block =
            parse_one("by thm T(a):\n    ? not $P(a)").expect("parse bodyless by thm goal");
        let Stmt::By(ByStmt::ByThmStmt(goal_block)) = goal_block else {
            panic!("expected by thm statement")
        };
        assert!(goal_block.selected_facts.as_ref().is_some_and(
            |facts| matches!(facts.as_slice(), [Fact::AtomicFact(fact)] if !fact.is_true())
        ));
        assert_eq!(goal_block.to_string(), "by thm T(a) => not $P(a)");
    }

    #[test]
    fn by_thm_selected_fact_rejects_missing_compound_and_indented_targets() {
        let cases = [
            ("by thm T(a) =>", "by thm: `=>` expects one atomic fact"),
            (
                "by thm T(a) => $P(a) and $Q(a)",
                "by thm: `=>` expects exactly one atomic fact",
            ),
            (
                "by thm T(a):\n    do_nothing",
                "by thm: expects a `? <fact>` goal block",
            ),
            (
                "by thm T(a):\n    ? $P(a)\n    do_nothing",
                "by thm: expects exactly one `? <atomic fact>` goal block and no proof body",
            ),
        ];
        for (source, expected) in cases {
            let error = parse_one(source).expect_err("invalid by thm target should fail");
            let RuntimeError::ParseError(error) = error else {
                panic!("{source}: expected parse error")
            };
            assert!(error.msg.contains(expected), "{source}: {}", error.msg);
        }
    }
}
