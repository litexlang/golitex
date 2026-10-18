use super::compile_by_contra_stmt_result::validate_atomic_negation;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{
    ByCasesBranchClosingSuccess, ByCasesBranchSuccess, ExecByCasesStmtResult,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_by_cases_result(
        &self,
        result: &ExecByCasesStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecByCasesStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Cases/Failed"));
        };
        let count = proof.stored.len();
        if count == 0
            || proof.branches.is_empty()
            || proof.then_facts_wd.len() != count
            || proof.stored_wd.len() != count
        {
            return Err(LeanCompileError::new(
                "Cases/Stages",
                "Case formation, branches and ordered output stores have inconsistent arities.",
            ));
        }
        let head = count + 2;
        let mut goals = Vec::new();
        let mut propositions = Vec::new();
        for (i, store) in proof.stored.iter().enumerate() {
            let complete = SourcePosition {
                before: head + 2 * i + 2,
                ..*position
            };
            let goal = self.resolve_fact(store.primary_fact_id(), &complete)?;
            self.validate_store(&store.store, &goal)?;
            let VerifyFactWellDefinedResult::Success(wd) = &proof.then_facts_wd[i] else {
                return Err(LeanCompileError::unsupported("Cases/GoalWD"));
            };
            let prior = SourcePosition {
                before: i,
                ..*position
            };
            self.compile_fact_wd(wd, &goal, &prior)?;
            let formed = SourcePosition::new(Some(&prior), SourceOwner::FactWD(wd), usize::MAX);
            propositions.push(self.fact_proposition(&goal, &formed)?);
            goals.push(goal);
        }
        let coverage_source = source_subject(&proof.coverage)?;
        let Fact::OrFact(coverage_fact) = &coverage_source else {
            return Err(LeanCompileError::unsupported("Cases/CoverageShape"));
        };
        if coverage_fact.facts.len() != proof.branches.len()
            || coverage_fact
                .facts
                .iter()
                .zip(&proof.branches)
                .any(|(case, branch)| case != &branch.assumption)
        {
            return Err(LeanCompileError::new(
                "Cases/CoverageBranches",
                "The coverage disjunction differs from the ordered branch assumptions.",
            ));
        }
        let coverage_scope = SourcePosition {
            before: count,
            ..*position
        };
        let coverage = self.compile_cases_coverage(&proof.coverage, &coverage_scope)?;
        let caller = SourcePosition {
            before: count + 1,
            ..*position
        };
        let mut branches = Vec::new();
        for branch in &proof.branches {
            branches.push(self.compile_case_branch(branch, &goals, &caller)?);
        }
        let mut eliminator = branches.pop().expect("nonempty branches");
        while let Some(branch) = branches.pop() {
            eliminator = format!(
                "(fun _litex_cases_tail => Or.elim _litex_cases_tail {branch} {eliminator})"
            );
        }
        let name = format!("_cases_result_{}", coverage_fact.fact_id.value());
        let kind = if local { "have" } else { "theorem" };
        let header = if local {
            String::new()
        } else {
            self.context_header(position)?
        };
        let mut declarations = vec![format!(
            "{kind} {name}{header} : {} :=\n  ({eliminator} {})",
            conjunction_proposition(propositions.clone())?,
            coverage.1,
        )];
        let reference = if local {
            name
        } else {
            self.context_application(&name, position)
        };
        for (i, ((goal, proposition), store)) in goals
            .iter()
            .zip(propositions)
            .zip(&proof.stored)
            .enumerate()
        {
            let output = SourcePosition {
                before: head + 2 * i,
                ..*position
            };
            self.compile_fact_wd(&proof.stored_wd[i], goal, &output)?;
            let mut selected = reference.clone();
            for _ in 0..i {
                selected = format!("(And.right {selected})");
            }
            if i + 1 != count {
                selected = format!("(And.left {selected})");
            }
            declarations.push(self.emit_by_completed_fact(
                goal,
                (proposition, selected),
                store,
                &output,
                head + 2 * i + 2,
                index,
                local,
            )?);
        }
        Ok(declarations.join("\n\n"))
    }

    fn compile_case_branch(
        &self,
        branch: &ByCasesBranchSuccess,
        goals: &[Fact],
        caller: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let assumption = crate::ast::fact::and_chain_as_fact(&branch.assumption);
        let scope = SourcePosition::new(Some(caller), SourceOwner::CasesBranch(branch), 0);
        let (proposition, mut body) = self.compile_by_local_assumption(
            &assumption,
            branch.assumption_fact_id,
            &branch.assumption_components,
            &branch.assumption_wd,
            &branch.assumptions_stored,
            &scope,
        )?;
        for (i, step) in branch.proof_steps.iter().enumerate() {
            body.push(self.compile_statement_in_scope(
                step,
                &SourcePosition {
                    before: 2 + i,
                    ..scope
                },
                i + 1,
                true,
            )?);
        }
        let head = 2 + branch.proof_steps.len();
        match &branch.closing {
            ByCasesBranchClosingSuccess::Impossible(closing) => {
                let prior = SourcePosition {
                    before: head,
                    ..scope
                };
                body.push(format!(
                    "exact False.elim {}",
                    self.compile_by_contradiction_closing(closing, &prior)?
                ));
            }
            ByCasesBranchClosingSuccess::ThenFacts { proved_then_facts } => {
                if proved_then_facts.len() != goals.len() {
                    return Err(LeanCompileError::new(
                        "Cases/ClosingArity",
                        "A branch closes a different number of source goals.",
                    ));
                }
                let mut terms = Vec::new();
                for (i, (checked, goal)) in proved_then_facts.iter().zip(goals).enumerate() {
                    let source = source_subject(&checked.verify_result)?;
                    if source != *goal || source.fact_id() != goal.fact_id() {
                        return Err(LeanCompileError::new(
                            "Cases/ClosingSubject",
                            "A branch closes another original goal.",
                        ));
                    }
                    let prior = SourcePosition {
                        before: head + 2 * i,
                        ..scope
                    };
                    let compiled = self.compile_verify(&checked.verify_result, &prior)?;
                    body.push(self.emit_by_completed_fact(
                        goal,
                        compiled,
                        &checked.store_and_infer,
                        &prior,
                        head + 2 * i + 2,
                        i + 1,
                        true,
                    )?);
                    terms.push(format!("h_{}", goal.fact_id().value()));
                }
                let mut term = terms.pop().expect("nonempty goals");
                while let Some(left) = terms.pop() {
                    term = format!("(And.intro {left} {term})");
                }
                body.push(format!("exact {term}"));
            }
        }
        Ok(format!(
            "(fun (h_{} : {proposition}) => by\n  {}\n)",
            branch.assumption_fact_id.value(),
            body.join("\n").replace('\n', "\n  ")
        ))
    }

    // Geometry selects the exact complementary-atomic builtin for its two
    // cases. Other recorded routes still use the ordinary verification dispatcher.
    fn compile_cases_coverage(
        &self,
        result: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        if let VerifyFactResult::OrFact(result_or) = result {
            if let VerifyOrFactResult::Success(proof) = result_or.as_ref() {
                if let OrFactSearchedProof::ByBuiltinRule(
                    OrFactSearchProofByBuiltinRule::ComplementaryAtomic(selected),
                ) = &proof.searched_proof
                {
                    let [AndChainAtomicFact::AtomicFact(left), AndChainAtomicFact::AtomicFact(right)] =
                        proof.fact.facts.as_slice()
                    else {
                        return Err(LeanCompileError::unsupported(
                            "Cases/ComplementaryCoverageShape",
                        ));
                    };
                    if left != &selected.left
                        || right != &selected.right
                        || left.fact_id() != selected.left.fact_id()
                        || right.fact_id() != selected.right.fact_id()
                    {
                        return Err(LeanCompileError::new(
                            "Cases/ComplementaryCoverageSubject",
                            "The selected complementary atoms differ from the coverage branches.",
                        ));
                    }
                    let left_negative =
                        validate_atomic_negation(&left.clone().into(), &right.clone().into())?;
                    let verify_scope =
                        SourcePosition::new(Some(position), SourceOwner::Verify(result), 0);
                    self.compile_or_wd(&proof.fact, &proof.well_defined_proof, &verify_scope)?;
                    let formed = SourcePosition {
                        before: proof.fact.facts.len(),
                        ..verify_scope
                    };
                    let positive =
                        self.atomic_proposition(if left_negative { right } else { left }, &formed)?;
                    let term = if left_negative {
                        format!("(Or.symm (Classical.em ({positive})))")
                    } else {
                        format!("(Classical.em ({positive}))")
                    };
                    return Ok((
                        self.fact_proposition(&Fact::OrFact(proof.fact.clone()), &formed)?,
                        term,
                    ));
                }
            }
        }
        self.compile_verify(result, position)
    }
}
