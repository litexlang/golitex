//! `have fn name(...) ret by cases:` / `have fn name(...) ret = expr` /
//! `have fn name by exist!:`.

use super::super::keywords::{BY, CASE, CASES, COLON, EQUAL, EXIST, EXIST_BANG, FN, FROM, INDUC};
use super::super::object::{is_simple_name, parse_obj};
use crate::new_pipeline::ast::fact::{
    AndChainAtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact,
};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::obj::{AnonymousFn, FnSet, Obj};
use crate::new_pipeline::ast::param::ParamType;
use crate::new_pipeline::ast::stmt::{
    DefinitionStmt, FnSetClause, HaveFnByForallExistUniqueStmt, HaveFnByInducCase,
    HaveFnByInducCaseBody, HaveFnByInducStmt, HaveFnEqualCaseByCaseStmt, HaveFnEqualStmt, Stmt,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // `have fn f(x R) R = x` | `have fn f(x R) Z by cases:` …
    pub(in crate::new_pipeline::parse) fn parse_have_fn_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.advance()?; // `have`
        tb.expect(FN)?;

        let name = tb.advance().map_err(|_| {
            RuntimeParseError::new(
                "`have fn` expects a function name",
                block.line,
                block.source_path.clone(),
            )
        })?;
        if !is_simple_name(&name) {
            return Err(RuntimeParseError::new(
                format!("invalid have fn name `{name}`"),
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        // Occupy at enclosing scope before param binders.
        let _bound = self.define_plain_atom_as_parse(&tb, name.clone())?;

        // `have fn name by exist!:` has no signature paren list.
        if tb.peek() == Some(BY) {
            return self.parse_have_fn_by_exist_or_error(block, &mut tb, name);
        }

        self.push_parse_scope();
        let result = (|| {
            let (params, dom_facts) = self.parse_fn_set_header(&mut tb)?;
            let ret_set = parse_obj(self, &mut tb)?;
            let fn_set_clause = FnSetClause {
                set_bound_parameters: params,
                dom_facts,
                ret_set,
            };

            if tb.peek() == Some(BY) {
                tb.expect(BY)?;
                if tb.peek() == Some(CASES) {
                    return self.parse_have_fn_by_cases_tail(block, &mut tb, name, fn_set_clause);
                }
                if tb.peek() == Some(INDUC) {
                    return self.parse_have_fn_by_induc_tail(block, &mut tb, name, fn_set_clause);
                }
                return Err(tb.parse_error(
                    "have fn: expected `by cases` or `by induc` after signature",
                ));
            }

            if tb.peek() == Some(COLON) {
                return Err(RuntimeParseError::new(
                    "have fn colon case body: not wired yet in new_pipeline (use `by cases`)",
                    block.line,
                    block.source_path.clone(),
                )
                .into());
            }

            tb.expect(EQUAL)?;
            let equal_to = parse_obj(self, &mut tb)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error("trailing tokens after have fn equal body"));
            }
            if !block.body.is_empty() {
                return Err(RuntimeParseError::new(
                    "`have fn ... =` cannot have an indented body",
                    block.line,
                    block.source_path.clone(),
                )
                .into());
            }

            let equal_to_anonymous_fn = AnonymousFn {
                body: FnSet {
                    set_bound_parameters: fn_set_clause.set_bound_parameters,
                    dom_facts: fn_set_clause.dom_facts,
                    ret_set: Box::new(fn_set_clause.ret_set),
                },
                equal_to: Box::new(equal_to),
            };
            Ok(Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(
                HaveFnEqualStmt {
                    name,
                    equal_to_anonymous_fn,
                    line_file: LineFile::new(block.line, block.source_path.clone()),
                },
            )))
        })();
        self.pop_parse_scope();
        result
    }

    fn parse_have_fn_by_cases_tail(
        &mut self,
        block: &TokenBlock,
        tb: &mut TokenBlock,
        name: String,
        fn_set_clause: FnSetClause,
    ) -> RuntimeResult<Stmt> {
        tb.expect(CASES)?;
        tb.expect(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("unexpected token after `have fn ... by cases:`"));
        }
        if block.body.is_empty() {
            return Err(RuntimeParseError::new(
                "have fn by cases: expects at least one `case` arm",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        let mut cases: Vec<AndChainAtomicFact> = Vec::new();
        let mut equal_tos: Vec<Obj> = Vec::new();
        for child in &block.body {
            let mut arm = child.clone();
            arm.expect(CASE)?;
            let case = self.parse_and_chain_atomic_fact_allow_not(&mut arm)?;
            arm.expect(COLON)?;
            let equal_to = parse_obj(self, &mut arm)?;
            if !arm.exceed_end_of_head() {
                return Err(arm.parse_error("case: trailing tokens after value"));
            }
            if !arm.body.is_empty() {
                return Err(arm.parse_error("case: value must be on the case header line"));
            }
            cases.push(case);
            equal_tos.push(equal_to);
        }

        Ok(Stmt::Definition(DefinitionStmt::HaveFnEqualCaseByCaseStmt(
            HaveFnEqualCaseByCaseStmt {
                name,
                fn_set_clause,
                cases,
                equal_tos,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }

    fn parse_have_fn_by_induc_tail(
        &mut self,
        block: &TokenBlock,
        tb: &mut TokenBlock,
        name: String,
        fn_set_clause: FnSetClause,
    ) -> RuntimeResult<Stmt> {
        tb.expect(INDUC)?;
        let measure = parse_obj(self, tb)?;
        tb.expect(FROM)?;
        let lower_bound = parse_obj(self, tb)?;
        tb.expect(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("unexpected token after `by induc <measure> from <lower>:`"));
        }
        if block.body.is_empty() {
            return Err(RuntimeParseError::new(
                "have fn by induc: expects at least one `case` arm",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }
        let cases = self.parse_have_fn_by_induc_cases(&block.body)?;
        Ok(Stmt::Definition(DefinitionStmt::HaveFnByInducStmt(
            HaveFnByInducStmt {
                name,
                fn_set_clause,
                measure,
                lower_bound,
                cases,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }

    fn parse_have_fn_by_induc_cases(
        &mut self,
        blocks: &[TokenBlock],
    ) -> RuntimeResult<Vec<HaveFnByInducCase>> {
        let mut cases = Vec::with_capacity(blocks.len());
        for child in blocks {
            cases.push(self.parse_have_fn_by_induc_case(child)?);
        }
        Ok(cases)
    }

    fn parse_have_fn_by_induc_case(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<HaveFnByInducCase> {
        let mut arm = block.clone();
        arm.expect(CASE)?;
        let case_fact = self.parse_and_chain_atomic_fact_allow_not(&mut arm)?;
        arm.expect(COLON)?;
        if !arm.exceed_end_of_head() {
            let equal_to = parse_obj(self, &mut arm)?;
            if !arm.exceed_end_of_head() {
                return Err(arm.parse_error("unexpected token after case right-hand side"));
            }
            if !arm.body.is_empty() {
                return Err(arm.parse_error(
                    "a case with an inline right-hand side cannot also have nested cases",
                ));
            }
            return Ok(HaveFnByInducCase {
                case_fact,
                body: HaveFnByInducCaseBody::EqualTo(equal_to),
            });
        }
        if arm.body.is_empty() {
            return Err(arm.parse_error(
                "case must end with a right-hand side or nested case blocks",
            ));
        }
        let nested = self.parse_have_fn_by_induc_cases(&arm.body)?;
        Ok(HaveFnByInducCase {
            case_fact,
            body: HaveFnByInducCaseBody::NestedCases(nested),
        })
    }

    // `have fn name by exist!:` then only `? forall …` (no proof body).
    fn parse_have_fn_by_exist_or_error(
        &mut self,
        block: &TokenBlock,
        tb: &mut TokenBlock,
        name: String,
    ) -> RuntimeResult<Stmt> {
        tb.expect(BY)?;
        let is_exist_bang = match tb.peek() {
            Some(EXIST_BANG) => {
                tb.advance()?;
                true
            }
            Some(EXIST) => {
                tb.advance()?;
                if tb.peek() == Some(super::super::keywords::BANG) {
                    tb.advance()?;
                    true
                } else {
                    false
                }
            }
            _ => false,
        };
        if !is_exist_bang {
            let _ = FROM;
            return Err(RuntimeParseError::new(
                "have fn: expected signature `(…)` or `by exist!`",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }
        tb.expect(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("unexpected token after `have fn … by exist!:`"));
        }
        if block.body.is_empty() {
            return Err(RuntimeParseError::new(
                "`have fn … by exist!:` expects a `? forall ...` goal block",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }
        if block.body.len() != 1 {
            return Err(RuntimeParseError::new(
                "`have fn … by exist!:` takes only a `? forall ...` goal; prove it outside with claim/thm/trust",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        let mut goal = block.body[0].clone();
        let forall = self.parse_goal_forall_fact(&mut goal, "have fn by exist!")?;
        check_have_fn_by_exist_forall_shape(block, &forall)?;

        Ok(Stmt::Definition(DefinitionStmt::HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt {
                name,
                forall,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            }),
        ))
    }
}

// Shape required so the forall can become an AnonymousFn / FnSet later:
// - every forall param type is Obj (set-bound), at least one param
// - every dom fact is quantifier-free (atomic / and / chain / or)
// - exactly one then, and it is exist!
// - that exist! binds exactly one Obj-typed witness (the return set)
//
// Example (ok):
//   have fn f by exist!:
//       ? forall x A:
//           exist! y B st {$F(x, y)}
fn check_have_fn_by_exist_forall_shape(
    block: &TokenBlock,
    forall: &ForallFact,
) -> RuntimeResult<()> {
    let mut forall_param_count = 0usize;
    for group in &forall.typed_parameters.groups {
        forall_param_count += group.params.len();
        match &group.param_type {
            ParamType::Obj(_) => {}
            _ => {
                return Err(RuntimeParseError::new(
                    "`have fn … by exist!`: forall parameters must all be Obj-typed (e.g. `x A`), not `set` / `nonempty_set` / `finite_set`",
                    block.line,
                    block.source_path.clone(),
                )
                .into());
            }
        }
    }
    if forall_param_count == 0 {
        return Err(RuntimeParseError::new(
            "`have fn … by exist!`: forall must bind at least one Obj parameter",
            block.line,
            block.source_path.clone(),
        )
        .into());
    }

    for dom in &forall.dom_facts {
        if !fact_is_fn_set_dom_shape(dom) {
            return Err(RuntimeParseError::new(
                "`have fn … by exist!`: forall domain facts must be usable as anonymous-fn / fn-set domain facts (atomic / and / chain / or)",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }
    }

    if forall.then_facts.len() != 1 {
        return Err(RuntimeParseError::new(
            "`have fn … by exist!`: forall must have exactly one then fact, and it must be `exist!`",
            block.line,
            block.source_path.clone(),
        )
        .into());
    }

    let ExistOrAndChainAtomicFact::ExistUniqueFact(exist_body) = &forall.then_facts[0] else {
        return Err(RuntimeParseError::new(
            "`have fn … by exist!`: the only forall then fact must be `exist!`",
            block.line,
            block.source_path.clone(),
        )
        .into());
    };

    let mut witness_count = 0usize;
    for group in &exist_body.typed_parameters.groups {
        witness_count += group.params.len();
        match &group.param_type {
            ParamType::Obj(_) => {}
            _ => {
                return Err(RuntimeParseError::new(
                    "`have fn … by exist!`: `exist!` witness type must be Obj (e.g. `y B`), not `set` / `nonempty_set` / `finite_set`",
                    block.line,
                    block.source_path.clone(),
                )
                .into());
            }
        }
    }
    if witness_count != 1 {
        return Err(RuntimeParseError::new(
            "`have fn … by exist!`: `exist!` must bind exactly one Obj-typed witness",
            block.line,
            block.source_path.clone(),
        )
        .into());
    }

    Ok(())
}

fn fact_is_fn_set_dom_shape(fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(_) | Fact::AndFact(_) | Fact::ChainFact(_) | Fact::OrFact(_)
    )
}
