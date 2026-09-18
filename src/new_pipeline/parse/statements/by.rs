use super::super::keywords::{
    BY, CASE, CASES, COLON, COMMA, CONTRA, DEF, FINITE_SET_INDUC, IMPOSSIBLE, INDUC, LEFT_PAREN,
    QUESTION_GOAL, REFLEXIVE_PROP, RELEASE, RIGHT_ARROW, RIGHT_PAREN, STRONG_INDUC, SYMMETRIC_PROP,
    THM,
};
use super::super::object::{is_simple_name, parse_obj};
use crate::new_pipeline::ast::fact::{AndChainAtomicFact, AtomicFact};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::stmt::{
    ByCasesStmt, ByContraStmt, ByDefStmt, ByReflexivePropStmt, ByStmt, BySymmetricPropStmt,
    ByThmStmt, ReleaseThmStmt, Stmt, TheoremCall, TheoremCallArguments,
};
use crate::new_pipeline::parse::prop_registration_shape::{
    reflexive_prop_name_from_forall, symmetric_prop_registration_from_forall,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    pub(in super::super) fn parse_by_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(BY)?;
        match tb.peek() {
            Some(CASES) => self.parse_by_cases_stmt(&mut tb, block),
            Some(CONTRA) => self.parse_by_contra_stmt(&mut tb, block),
            Some(DEF) => self.parse_by_def_stmt(&mut tb, block),
            Some(INDUC) | Some(STRONG_INDUC) | Some(FINITE_SET_INDUC) => Err(tb.parse_error(
                "by induc / strong_induc / finite_set_induc: not wired (binder reuse)",
            )),
            Some(THM) => self.parse_by_thm_or_release(&mut tb, block),
            Some(REFLEXIVE_PROP) => self.parse_by_reflexive_prop_stmt(&mut tb, block),
            Some(SYMMETRIC_PROP) => self.parse_by_symmetric_prop_stmt(&mut tb, block),
            Some(other) => Err(tb.parse_error(format!(
                "by: `{other}` is not wired yet (supported: cases, contra, def, thm, reflexive_prop, symmetric_prop; induc deferred)"
            ))),
            None => Err(tb.parse_error("by: expected a proof directive after `by`")),
        }
    }

    fn parse_by_reflexive_prop_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(REFLEXIVE_PROP)?;
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(tb.parse_error("by reflexive_prop: expects a body"));
        }
        let mut goal = tb.body[0].clone();
        let forall_fact = self.parse_goal_forall_fact(&mut goal, "by reflexive_prop")?;
        if let Err(msg) = reflexive_prop_name_from_forall(&forall_fact) {
            return Err(tb.parse_error(msg));
        }
        let proof_blocks = &tb.body[1..];
        let proof = self.with_forall_params_occupied(&forall_fact.typed_parameters, tb, |this| {
            this.parse_body_stmts(proof_blocks)
        })?;
        Ok(Stmt::By(ByStmt::ByReflexivePropStmt(ByReflexivePropStmt {
            forall_fact,
            proof,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }

    fn parse_by_symmetric_prop_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(SYMMETRIC_PROP)?;
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(tb.parse_error("by symmetric_prop: expects a body"));
        }
        let mut goal = tb.body[0].clone();
        let forall_fact = self.parse_goal_forall_fact(&mut goal, "by symmetric_prop")?;
        if let Err(msg) = symmetric_prop_registration_from_forall(&forall_fact) {
            return Err(tb.parse_error(msg));
        }
        let proof_blocks = &tb.body[1..];
        let proof = self.with_forall_params_occupied(&forall_fact.typed_parameters, tb, |this| {
            this.parse_body_stmts(proof_blocks)
        })?;
        Ok(Stmt::By(ByStmt::BySymmetricPropStmt(BySymmetricPropStmt {
            forall_fact,
            proof,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }

    fn parse_by_cases_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(CASES)?;
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(
                tb.parse_error("by cases: expects at least one `? <fact>` goal and one `case` arm")
            );
        }

        let mut then_facts = Vec::new();
        let mut case_start = 0;
        for (i, child) in tb.body.iter().enumerate() {
            if child.header.first().map(String::as_str) != Some(QUESTION_GOAL) {
                case_start = i;
                break;
            }
            let mut goal = child.clone();
            then_facts.push(self.parse_goal_fact(&mut goal, "by cases")?);
            case_start = i + 1;
        }
        if then_facts.is_empty() {
            return Err(tb.parse_error("by cases: expects at least one `? <fact>` goal"));
        }
        if case_start >= tb.body.len() {
            return Err(tb.parse_error("by cases: expects at least one `case` arm"));
        }

        let mut cases: Vec<AndChainAtomicFact> = Vec::new();
        let mut proofs = Vec::new();
        let mut impossible_facts: Vec<Option<AtomicFact>> = Vec::new();

        for child in tb.body.iter().skip(case_start) {
            let mut arm = child.clone();
            arm.expect(CASE)?;
            let case = self.parse_and_chain_atomic_fact_allow_not(&mut arm)?;
            let bodyless = arm.body.is_empty();
            if bodyless {
                if arm.peek() == Some(COLON) {
                    arm.expect(COLON)?;
                }
            } else {
                arm.expect(COLON)?;
            }
            if !arm.exceed_end_of_head() {
                return Err(arm.parse_error("case: expected end of head after condition"));
            }

            self.push_parse_scope();
            let arm_result = (|| {
                if bodyless {
                    return Ok((Vec::new(), None));
                }
                let n = arm.body.len();
                let last_is_impossible =
                    arm.body[n - 1].header.first().map(String::as_str) == Some(IMPOSSIBLE);
                if last_is_impossible {
                    let proof = self.parse_body_stmts(&arm.body[..n - 1])?;
                    let mut last = arm.body[n - 1].clone();
                    last.expect(IMPOSSIBLE)?;
                    let imp = self.parse_atomic_fact(&mut last, true)?;
                    if !last.exceed_end_of_head() || !last.body.is_empty() {
                        return Err(last.parse_error("impossible: expected a single atomic fact"));
                    }
                    Ok((proof, Some(imp)))
                } else {
                    Ok((self.parse_body_stmts(&arm.body)?, None))
                }
            })();
            self.pop_parse_scope();
            let (proof, impossible) = arm_result?;
            cases.push(case);
            proofs.push(proof);
            impossible_facts.push(impossible);
        }

        Ok(Stmt::By(ByStmt::ByCasesStmt(ByCasesStmt {
            cases,
            then_facts,
            proofs,
            impossible_facts,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }

    fn parse_by_contra_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(CONTRA)?;
        tb.expect_colon_end_of_header()?;
        if tb.body.len() < 2 {
            return Err(tb.parse_error(
                "by contra: expects a `? <fact>` goal block and `impossible ...` tail",
            ));
        }
        let mut goal = tb.body[0].clone();
        let to_prove = self.parse_goal_fact(&mut goal, "by contra")?;
        let n = tb.body.len();
        let proof_blocks = &tb.body[1..n - 1];
        let mut last = tb.body[n - 1].clone();

        let (proof, impossible_fact) = if let Some(params) = Self::forall_params_of_fact(&to_prove)
        {
            self.with_forall_params_occupied(params, tb, |this| {
                let proof = this.parse_body_stmts(proof_blocks)?;
                last.expect(IMPOSSIBLE)?;
                let impossible_fact = this.parse_atomic_fact(&mut last, true)?;
                if !last.exceed_end_of_head() || !last.body.is_empty() {
                    return Err(last.parse_error("impossible: expected a single atomic fact"));
                }
                Ok((proof, impossible_fact))
            })?
        } else {
            self.push_parse_scope();
            let result = (|| {
                let proof = self.parse_body_stmts(proof_blocks)?;
                last.expect(IMPOSSIBLE)?;
                let impossible_fact = self.parse_atomic_fact(&mut last, true)?;
                if !last.exceed_end_of_head() || !last.body.is_empty() {
                    return Err(last.parse_error("impossible: expected a single atomic fact"));
                }
                Ok((proof, impossible_fact))
            })();
            self.pop_parse_scope();
            result?
        };

        Ok(Stmt::By(ByStmt::ByContraStmt(ByContraStmt {
            to_prove,
            proof,
            impossible_fact,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }

    fn parse_by_def_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(DEF)?;
        let fact = if tb.peek() == Some(COLON) {
            tb.expect_colon_end_of_header()?;
            if tb.body.len() != 1 {
                return Err(
                    tb.parse_error("by def: expects exactly one `? <atomic fact>` goal block")
                );
            }
            let mut goal = tb.body[0].clone();
            if goal.peek() != Some(QUESTION_GOAL) {
                return Err(goal.parse_error("by def: expected `? <atomic fact>`"));
            }
            goal.expect(QUESTION_GOAL)?;
            let atomic = self.parse_atomic_fact(&mut goal, true)?;
            if !goal.exceed_end_of_head() || !goal.body.is_empty() {
                return Err(goal.parse_error("by def: unfinished tokens in `?` atomic goal"));
            }
            atomic
        } else {
            if !tb.body.is_empty() {
                return Err(tb.parse_error("inline by def does not accept an indented body"));
            }
            let atomic = self.parse_atomic_fact(tb, true)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error("inline by def expects exactly one atomic fact"));
            }
            atomic
        };
        if is_negative_atomic(&fact) {
            return Err(tb.parse_error("by def expects one positive atomic fact"));
        }
        Ok(Stmt::By(ByStmt::ByDefStmt(ByDefStmt {
            fact,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }

    fn parse_by_thm_or_release(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(THM)?;
        let call = self.parse_theorem_call(tb)?;
        if tb.peek() == Some(RIGHT_ARROW) {
            tb.expect(RIGHT_ARROW)?;
            if !tb.body.is_empty() {
                return Err(tb.parse_error("by thm: `=>` does not accept an indented body"));
            }
            let selected_fact = self.parse_atomic_fact(tb, true)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error("by thm: `=>` expects exactly one atomic fact"));
            }
            return Ok(Stmt::By(ByStmt::ByThmStmt(ByThmStmt {
                call,
                selected_fact,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            })));
        }
        if !tb.exceed_end_of_head() || !tb.body.is_empty() {
            return Err(tb.parse_error("by thm: expected bare call or `=> <atomic fact>`"));
        }
        Ok(Stmt::ReleaseThmStmt(ReleaseThmStmt {
            call,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        }))
    }

    pub(in super::super) fn parse_release_thm_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(RELEASE)?;
        tb.expect(THM)?;
        let call = self.parse_theorem_call(&mut tb)?;
        if !tb.exceed_end_of_head() || !tb.body.is_empty() {
            return Err(tb.parse_error("release thm accepts only a bare theorem call"));
        }
        Ok(Stmt::ReleaseThmStmt(ReleaseThmStmt {
            call,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        }))
    }

    pub(in super::super) fn parse_theorem_call(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TheoremCall> {
        let name_tok = tb
            .advance()
            .map_err(|_| tb.parse_error("theorem call expects a name"))?;
        if !is_simple_name(&name_tok) {
            return Err(tb.parse_error(format!("invalid theorem name `{name_tok}`")));
        }
        let name = AtomicName::Plain { name: name_tok };
        let arguments = if tb.peek() == Some(LEFT_PAREN) {
            tb.expect(LEFT_PAREN)?;
            let mut args = Vec::new();
            if tb.peek() != Some(RIGHT_PAREN) {
                loop {
                    args.push(parse_obj(self, tb)?);
                    if tb.peek() == Some(COMMA) {
                        tb.advance()?;
                        continue;
                    }
                    break;
                }
            }
            tb.expect(RIGHT_PAREN)?;
            TheoremCallArguments::Parenthesized(args)
        } else {
            TheoremCallArguments::Bare
        };
        Ok(TheoremCall { name, arguments })
    }
}

fn is_negative_atomic(fact: &AtomicFact) -> bool {
    matches!(
        fact,
        AtomicFact::NotNormalAtomicFact(_)
            | AtomicFact::NotEqualFact(_)
            | AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::NotIsSetFact(_)
            | AtomicFact::NotIsNonemptySetFact(_)
            | AtomicFact::NotIsFiniteSetFact(_)
            | AtomicFact::NotInFact(_)
            | AtomicFact::NotIsCartFact(_)
            | AtomicFact::NotIsTupleFact(_)
            | AtomicFact::NotSubsetFact(_)
            | AtomicFact::NotSupersetFact(_)
    )
}
