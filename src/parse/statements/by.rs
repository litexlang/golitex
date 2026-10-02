use super::super::keywords::{
    AXIOM_OF_CHOICE, BY, CASE, CASES, COLON, COMMA, CONTRA, DEF, EQUAL, FROM, IMPOSSIBLE, IN, INDUC,
    LEFT_PAREN, MOD_FLAT_SIGN, MOD_SIGN, QUESTION_GOAL, REGULARITY_AXIOM, RIGHT_ARROW, RIGHT_PAREN,
    STRONG_INDUC, EXTENSION, FN_EXTENSION, THM, ENUMERATE, FOR, CLOSED_RANGE, FINITE_SET, RANGE,
    ZORN_LEMMA,
};
use super::super::object::{is_simple_name, parse_obj};
use crate::ast::obj::Obj;
use crate::ast::fact::{
    AndChainAtomicFact, AtomicFact, ExistOrAndChainAtomicFact, Fact,
};
use crate::ast::line_file::SourceLine;
use crate::ast::names::AtomicName;
use crate::ast::stmt::{
    ByCasesStmt, ByContraStmt, ByDefStmt, ByInducStmt, ByStmt, ByStrongInducStmt, ByExtensionStmt,
    ByFnExtensionStmt, ByForStmt, ByEnumerateFiniteSetStmt, ByThmStmt, ReleaseAndExpandStmt,
    ReleaseThmStmt, Stmt, TheoremCall, TheoremCallArguments,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

impl Runtime {
    pub(in super::super) fn parse_by_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(BY)?;
        match tb.peek() {
            Some(CASES) => self.parse_by_cases_stmt(&mut tb, block),
            Some(CONTRA) => self.parse_by_contra_stmt(&mut tb, block),
            Some(DEF) => self.parse_by_def_stmt(&mut tb, block),
            Some(INDUC) | Some(STRONG_INDUC) => self.parse_by_induc_or_strong_induc_stmt(&mut tb, block),
            Some(THM) => self.parse_by_thm_or_release(&mut tb, block),
            Some(EXTENSION) => self.parse_by_extension_stmt(&mut tb, block),
            Some(FN_EXTENSION) => self.parse_by_fn_extension_stmt(&mut tb, block),
            Some(ENUMERATE) => self.parse_by_enumerate_stmt(&mut tb, block),
            Some(FOR) => self.parse_by_for_stmt(&mut tb, block),
            Some(CLOSED_RANGE) => Err(tb.parse_error(
                "removed: use `expand: e $in closed_range(…)` or `expand: e $in a...b`",
            )),
            Some(REGULARITY_AXIOM) => Err(tb.parse_error(
                "removed: use `release regularity_axiom(S)`",
            )),
            Some(AXIOM_OF_CHOICE) => Err(tb.parse_error(
                "removed: use `release axiom_of_choice: set F:`",
            )),
            Some(ZORN_LEMMA) => Err(tb.parse_error(
                "removed: use `release zorn_lemma: set S, prop P, prop U, prop M:`",
            )),
            Some(other) => Err(tb.parse_error(format!(
                "by: `{other}` is not wired yet (supported: cases, contra, def, thm, extension, fn_extension, induc, strong_induc, enumerate finite_set, for)"
            ))),
            None => Err(tb.parse_error("by: expected a proof directive after `by`")),
        }
    }


    fn parse_by_extension_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(EXTENSION)?;
        let (left, right, proof) = if tb.peek() == Some(COLON) {
            tb.expect_colon_end_of_header()?;
            if tb.body.is_empty() {
                return Err(tb.parse_error("by extension: expects a `? <equality>` goal block"));
            }
            let mut goal = tb.body[0].clone();
            let fact = self.parse_goal_fact(&mut goal, "by extension")?;
            let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = fact else {
                return Err(tb.parse_error("by extension: goal expects an equality fact"));
            };
            self.push_parse_scope();
            let proof = self.parse_body_stmts(&tb.body[1..]);
            self.pop_parse_scope();
            let proof = proof?;
            (eq.left, eq.right, proof)
        } else {
            if !tb.body.is_empty() {
                return Err(tb.parse_error(
                    "inline by extension does not accept an indented body; use `by extension:`",
                ));
            }
            let atomic = self.parse_atomic_fact(tb, true)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error("inline by extension expects exactly one equality"));
            }
            let AtomicFact::EqualFact(eq) = atomic else {
                return Err(tb.parse_error("by extension: expects an equality fact"));
            };
            (eq.left, eq.right, Vec::new())
        };
        Ok(Stmt::By(ByStmt::ByExtensionStmt(ByExtensionStmt {
            left,
            right,
            proof,
            line_file: SourceLine::new(block.line, self.code_source.clone()),
        })))
    }

    fn parse_by_fn_extension_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(FN_EXTENSION)?;
        let (left, right, proof) = if tb.peek() == Some(COLON) {
            tb.expect_colon_end_of_header()?;
            if tb.body.is_empty() {
                return Err(tb.parse_error(
                    "by fn_extension: expects a `? <equality>` goal block",
                ));
            }
            let mut goal = tb.body[0].clone();
            let fact = self.parse_goal_fact(&mut goal, "by fn_extension")?;
            let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = fact else {
                return Err(tb.parse_error("by fn_extension: goal expects an equality fact"));
            };
            self.push_parse_scope();
            let proof = self.parse_body_stmts(&tb.body[1..]);
            self.pop_parse_scope();
            let proof = proof?;
            (eq.left, eq.right, proof)
        } else {
            if !tb.body.is_empty() {
                return Err(tb.parse_error(
                    "inline by fn_extension does not accept an indented body; use `by fn_extension:`",
                ));
            }
            let atomic = self.parse_atomic_fact(tb, true)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error(
                    "inline by fn_extension expects exactly one equality",
                ));
            }
            let AtomicFact::EqualFact(eq) = atomic else {
                return Err(tb.parse_error("by fn_extension: expects an equality fact"));
            };
            (eq.left, eq.right, Vec::new())
        };
        Ok(Stmt::By(ByStmt::ByFnExtensionStmt(ByFnExtensionStmt {
            left,
            right,
            proof,
            line_file: SourceLine::new(block.line, self.code_source.clone()),
        })))
    }

    fn parse_by_enumerate_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(ENUMERATE)?;
        match tb.peek() {
            Some(FINITE_SET) => self.parse_by_enumerate_finite_set_stmt(tb, block),
            Some(RANGE) | Some(CLOSED_RANGE) => Err(tb.parse_error(
                "removed: use `expand: e $in range(…)` / `expand: e $in closed_range(…)` / `expand: e $in a...b`",
            )),
            other => Err(tb.parse_error(format!(
                "by enumerate: expected `finite_set`, got {other:?}"
            ))),
        }
    }

    fn parse_by_enumerate_finite_set_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(FINITE_SET)?;
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(tb.parse_error("by enumerate finite_set: expects a body"));
        }
        let mut goal = tb.body[0].clone();
        let forall_fact = self.parse_goal_forall_fact(&mut goal, "by enumerate finite_set")?;
        let proof = self.with_forall_params_occupied(&forall_fact.typed_parameters, tb, |this| {
            this.parse_body_stmts(&tb.body[1..])
        })?;
        Ok(Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(
            ByEnumerateFiniteSetStmt {
                forall_fact,
                proof,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
        )))
    }

    fn parse_by_for_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(FOR)?;
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(tb.parse_error("by for: expects a body"));
        }
        let mut goal = tb.body[0].clone();
        let forall_fact = self.parse_goal_forall_fact(&mut goal, "by for")?;
        let proof = self.with_forall_params_occupied(&forall_fact.typed_parameters, tb, |this| {
            this.parse_body_stmts(&tb.body[1..])
        })?;
        Ok(Stmt::By(ByStmt::ByForStmt(ByForStmt {
            forall_fact,
            proof,
            line_file: SourceLine::new(block.line, self.code_source.clone()),
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
                    let imp = self.parse_impossible_atomic_fact(&mut last)?;
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
            line_file: SourceLine::new(block.line, self.code_source.clone()),
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
                let impossible_fact = this.parse_impossible_atomic_fact(&mut last)?;
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
                let impossible_fact = self.parse_impossible_atomic_fact(&mut last)?;
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
            line_file: SourceLine::new(block.line, self.code_source.clone()),
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
            line_file: SourceLine::new(block.line, self.code_source.clone()),
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
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            })));
        }
        if !tb.exceed_end_of_head() || !tb.body.is_empty() {
            return Err(tb.parse_error("by thm: expected bare call or `=> <atomic fact>`"));
        }
        Ok(Stmt::ReleaseAndExpand(
            ReleaseAndExpandStmt::ReleaseThmStmt(ReleaseThmStmt {
                call,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            }),
        ))
    }

    pub(in super::super) fn parse_theorem_call(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TheoremCall> {
        let name = self.parse_theorem_call_name(tb)?;
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

    // `name`, `export::name`, `Mod::export::name`, or `Mod:::name`.
    fn parse_theorem_call_name(&mut self, tb: &mut TokenBlock) -> RuntimeResult<AtomicName> {
        let first = tb
            .advance()
            .map_err(|_| tb.parse_error("theorem call expects a name"))?;
        if !is_simple_name(&first) {
            return Err(tb.parse_error(format!("invalid theorem name `{first}`")));
        }
        if tb.peek() == Some(MOD_FLAT_SIGN) {
            tb.advance()?;
            let next = tb.advance().map_err(|_| {
                tb.parse_error("theorem call: expected identifier after `:::`")
            })?;
            if !is_simple_name(&next) {
                return Err(tb.parse_error(format!(
                    "theorem call: expected identifier after `:::`, got `{next}`"
                )));
            }
            return self.elaborate_flat_import(&first, next).map_err(|err| match err {
                crate::runtime::RuntimeError::InternalBug(message) => {
                    tb.parse_error(message)
                }
                other => other,
            });
        }
        if tb.peek() != Some(MOD_SIGN) {
            return Ok(AtomicName::Plain { name: first });
        }
        let mut parts = vec![first];
        while tb.peek() == Some(MOD_SIGN) {
            tb.advance()?;
            let next = tb.advance().map_err(|_| {
                tb.parse_error("theorem call: expected identifier after `::`")
            })?;
            if !is_simple_name(&next) {
                return Err(tb.parse_error(format!(
                    "theorem call: expected identifier after `::`, got `{next}`"
                )));
            }
            parts.push(next);
        }
        if parts.len() != 2 && parts.len() != 3 {
            return Err(tb.parse_error(
                "qualified theorem name must be `a::b`, `a:::b`, or `a::b::c`",
            ));
        }
        self.elaborate_name_parts(&parts).map_err(|err| match err {
            crate::runtime::RuntimeError::InternalBug(message) => {
                tb.parse_error(message)
            }
            other => other,
        })
    }
}

impl Runtime {
    fn parse_by_induc_or_strong_induc_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let strong = tb.peek() == Some(STRONG_INDUC);
        if strong {
            tb.expect(STRONG_INDUC)?;
        } else {
            tb.expect(INDUC)?;
        }
        let syntax = if strong { "by strong_induc" } else { "by induc" };
        let Some(param) = tb.peek().map(str::to_string) else {
            return Err(tb.parse_error(format!("{syntax}: expected induction parameter")));
        };
        if !is_simple_name(&param) {
            return Err(tb.parse_error(format!(
                "{syntax}: induction parameter must be a simple name, got `{param}`"
            )));
        }
        tb.advance()?;
        // Finite-set induction (`by induc S:` / `by induc S in A:`) is removed.
        if tb.peek() == Some(COLON) || tb.peek() == Some(IN) {
            return Err(tb.parse_error(format!(
                "{syntax}: finite-set induction was removed; use `{syntax} <param> from <base>:`"
            )));
        }
        tb.expect(FROM)?;
        let induc_from = parse_obj(self, tb)?;
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(tb.parse_error(format!("{syntax}: expects at least one `?` goal")));
        }

        self.push_parse_scope();
        let parsed = (|| {
            // `by induc n` selects an existing goal binder when it is visible;
            // it introduces a binder only for a standalone induction statement.
            if !self.plain_atom_is_visible(&param) {
                self.define_plain_atom_as_parse(tb, param.clone())?;
            }
            let mut goal_count = 0usize;
            for child in &tb.body {
                if !is_induc_goal_block(child) {
                    break;
                }
                if is_induc_structured_header_block(child) {
                    break;
                }
                goal_count += 1;
            }
            if goal_count == 0 {
                return Err(tb.parse_error(format!(
                    "{syntax}: expects one or more `? <fact>` goals before the proof"
                )));
            }

            let mut to_prove = Vec::with_capacity(goal_count);
            for child in tb.body.iter().take(goal_count) {
                let mut goal = child.clone();
                let fact = self.parse_goal_fact(&mut goal, syntax)?;
                to_prove.push(fact_as_induc_goal(fact, &goal, syntax)?);
            }

            let rest = &tb.body[goal_count..];
            let (proof, base_proof, step_proof) =
                self.parse_induc_proof_sections(rest, &param, &induc_from, strong, syntax)?;
            Ok((to_prove, proof, base_proof, step_proof))
        })();
        self.pop_parse_scope();
        let (to_prove, proof, base_proof, step_proof) = parsed?;

        let line_file = SourceLine::new(block.line, self.code_source.clone());
        if strong {
            Ok(Stmt::By(ByStmt::ByStrongInducStmt(ByStrongInducStmt {
                to_prove,
                proof,
                base_proof,
                step_proof,
                param_binding: param,
                induc_from,
                line_file,
            })))
        } else {
            Ok(Stmt::By(ByStmt::ByInducStmt(ByInducStmt {
                to_prove,
                proof,
                base_proof,
                step_proof,
                param_binding: param,
                induc_from,
                line_file,
            })))
        }
    }

    fn parse_induc_proof_sections(
        &mut self,
        rest: &[TokenBlock],
        param: &str,
        induc_from: &Obj,
        strong: bool,
        syntax: &str,
    ) -> RuntimeResult<(Vec<Stmt>, Option<Vec<Stmt>>, Option<Vec<Stmt>>)> {
        if rest.is_empty() {
            return Ok((Vec::new(), None, None));
        }
        if rest.iter().any(is_induc_structured_header_block) {
            let mut base_proof = None;
            let mut step_proof = None;
            for child in rest {
                if is_induc_base_header_block(child) {
                    if base_proof.is_some() {
                        return Err(child.parse_error(format!("{syntax}: duplicated `? from` block")));
                    }
                    let mut header = child.clone();
                    self.expect_induc_base_header(&mut header, param, induc_from, syntax)?;
                    base_proof = Some(self.parse_body_stmts(&header.body)?);
                } else if is_induc_step_header_block(child, strong) {
                    if step_proof.is_some() {
                        return Err(child.parse_error(format!(
                            "{syntax}: duplicated `? {}` block",
                            if strong { STRONG_INDUC } else { INDUC }
                        )));
                    }
                    let mut header = child.clone();
                    header.expect(QUESTION_GOAL)?;
                    if strong {
                        header.expect(STRONG_INDUC)?;
                    } else {
                        header.expect(INDUC)?;
                    }
                    header.expect_colon_end_of_header()?;
                    step_proof = Some(self.parse_body_stmts(&header.body)?);
                } else if is_induc_step_header_block(child, !strong) {
                    return Err(child.parse_error(format!(
                        "{syntax}: expected `? {}:` for this induction method",
                        if strong { STRONG_INDUC } else { INDUC }
                    )));
                } else {
                    return Err(child.parse_error(format!(
                        "{syntax}: unstructured proof cannot mix with `? from` / `? induc` blocks"
                    )));
                }
            }
            if base_proof.is_none() || step_proof.is_none() {
                return Err(rest[0].parse_error(format!(
                    "{syntax}: structured proof needs both `? from` and `? {}`",
                    if strong { STRONG_INDUC } else { INDUC }
                )));
            }
            Ok((Vec::new(), base_proof, step_proof))
        } else {
            Ok((self.parse_body_stmts(rest)?, None, None))
        }
    }

    fn expect_induc_base_header(
        &mut self,
        tb: &mut TokenBlock,
        param: &str,
        induc_from: &Obj,
        syntax: &str,
    ) -> RuntimeResult<()> {
        tb.expect(QUESTION_GOAL)?;
        tb.expect(FROM)?;
        let left = parse_obj(self, tb)?;
        tb.expect(EQUAL)?;
        let right = parse_obj(self, tb)?;
        tb.expect_colon_end_of_header()?;
        let Obj::Identifier(id) = &left else {
            return Err(tb.parse_error(format!(
                "{syntax}: `? from` left side must be the induction parameter `{param}`"
            )));
        };
        if id.display_string() != param {
            return Err(tb.parse_error(format!(
                "{syntax}: `? from` must start with `{param} = ...`"
            )));
        }
        if &right != induc_from {
            return Err(tb.parse_error(format!(
                "{syntax}: `? from` right side must equal the induction base"
            )));
        }
        Ok(())
    }
}

fn is_induc_goal_block(block: &TokenBlock) -> bool {
    block.peek() == Some(QUESTION_GOAL)
}

fn is_induc_base_header_block(block: &TokenBlock) -> bool {
    block.peek() == Some(QUESTION_GOAL) && block.peek_at(1) == Some(FROM)
}

fn is_induc_step_header_block(block: &TokenBlock, strong: bool) -> bool {
    let step = if strong { STRONG_INDUC } else { INDUC };
    block.peek() == Some(QUESTION_GOAL) && block.peek_at(1) == Some(step)
}

fn is_induc_structured_header_block(block: &TokenBlock) -> bool {
    is_induc_base_header_block(block)
        || is_induc_step_header_block(block, false)
        || is_induc_step_header_block(block, true)
}

fn fact_as_induc_goal(
    fact: Fact,
    tb: &TokenBlock,
    syntax: &str,
) -> RuntimeResult<ExistOrAndChainAtomicFact> {
    match fact {
        Fact::AtomicFact(a) => Ok(ExistOrAndChainAtomicFact::AtomicFact(a)),
        Fact::AndFact(a) => Ok(ExistOrAndChainAtomicFact::AndFact(a)),
        Fact::ChainFact(c) => Ok(ExistOrAndChainAtomicFact::ChainFact(c)),
        Fact::OrFact(o) => Ok(ExistOrAndChainAtomicFact::OrFact(o)),
        Fact::ExistFact(e) => Ok(ExistOrAndChainAtomicFact::ExistFact(e)),
        Fact::ExistUniqueFact(e) => Ok(ExistOrAndChainAtomicFact::ExistUniqueFact(e)),
        Fact::NotExistFact(e) => Ok(ExistOrAndChainAtomicFact::NotExistFact(e)),
        _ => Err(tb.parse_error(format!(
            "{syntax}: goal must be quantifier-free (forall goals are not allowed here)"
        ))),
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

