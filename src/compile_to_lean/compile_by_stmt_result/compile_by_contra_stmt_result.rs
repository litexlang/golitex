use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{ByContradictionClosingSuccess, ExecByContraStmtResult};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_by_contra_result(
        &self,
        result: &ExecByContraStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecByContraStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Contra/Failed"));
        };
        let VerifyFactWellDefinedResult::Success(goal_wd) = &proof.goal_wd else {
            return Err(LeanCompileError::unsupported("Contra/GoalWD"));
        };
        let negative_goal = validate_atomic_negation(&proof.goal, &proof.reverse_assumption)?;
        self.compile_fact_wd(goal_wd, &proof.goal, position)?;
        let goal_formed =
            SourcePosition::new(Some(position), SourceOwner::FactWD(goal_wd), usize::MAX);
        let proposition = self.fact_proposition(&proof.goal, &goal_formed)?;
        let caller = SourcePosition {
            before: 1,
            ..*position
        };
        let scope = SourcePosition::new(Some(&caller), SourceOwner::Contra(proof), 0);
        let (assumption, mut body) = self.compile_by_local_assumption(
            &proof.reverse_assumption,
            proof.reverse_assumption_fact_id,
            &proof.assumption_components,
            &proof.reverse_assumption_wd,
            &proof.negation_assumed,
            &scope,
        )?;
        let name = format!("h_{}", proof.reverse_assumption_fact_id.value());
        let mut steps = if negative_goal {
            vec![
                "classical".to_string(),
                "apply Classical.byContradiction".to_string(),
                "intro _litex_negated_goal".to_string(),
                format!(
                    "have {name} : {assumption} := Classical.byContradiction _litex_negated_goal"
                ),
            ]
        } else {
            vec![
                "classical".into(),
                "apply Classical.byContradiction".into(),
                format!("intro {name}"),
            ]
        };
        steps.append(&mut body);
        for (step_index, step) in proof.proof_steps.iter().enumerate() {
            steps.push(self.compile_statement_in_scope(
                step,
                &SourcePosition {
                    before: 2 + step_index,
                    ..scope
                },
                step_index + 1,
                true,
            )?);
        }
        let closing = SourcePosition {
            before: 2 + proof.proof_steps.len(),
            ..scope
        };
        steps.push(format!(
            "exact {}",
            self.compile_by_contradiction_closing(&proof.closing, &closing)?
        ));
        let term = format!("(by\n  {}\n)", steps.join("\n").replace('\n', "\n  "));

        let output = SourcePosition {
            before: 2,
            ..*position
        };
        self.compile_fact_wd(&proof.stored_wd, &proof.goal, &output)?;
        self.emit_by_completed_fact(
            &proof.goal,
            (proposition, term),
            &proof.stored,
            position,
            4,
            index,
            local,
        )
    }

    // Both local flows own exactly the same WD → assumption-store prefix.
    pub(in crate::compile_to_lean) fn compile_by_local_assumption(
        &self,
        fact: &Fact,
        id: FactId,
        components: &[(FactId, AtomicFact)],
        wd: &FactWellDefinedProof,
        store: &StoreFactAndInferResult,
        scope: &SourcePosition<'_>,
    ) -> Result<(String, Vec<String>), LeanCompileError> {
        if fact.fact_id() != id
            || store.primary_fact_id() != id
            || components != store.atomic_components().as_slice()
        {
            return Err(LeanCompileError::new(
                "By/AssumptionCapture",
                "The local assumption ID or ordered components differ from its original store.",
            ));
        }
        self.compile_fact_wd(wd, fact, scope)?;
        self.validate_store(&store.store, fact)?;
        let formed = SourcePosition {
            before: 1,
            ..*scope
        };
        let proposition = self.fact_proposition(fact, &formed)?;
        let complete = SourcePosition {
            before: 2,
            ..*scope
        };
        let inferences = self.compile_stored_inferences(
            store,
            fact,
            &(proposition.clone(), format!("h_{}", id.value())),
            &complete,
        )?;
        Ok((proposition, inferences))
    }

    pub(in crate::compile_to_lean) fn compile_by_contradiction_closing(
        &self,
        closing: &ByContradictionClosingSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let impossible = source_subject(&closing.impossible)?;
        if impossible != closing.impossible_fact
            || impossible.fact_id() != closing.impossible_fact.fact_id()
        {
            return Err(LeanCompileError::new(
                "By/ImpossibleSubject",
                "The original impossible fact differs from its verification.",
            ));
        }
        let negated = source_subject(&closing.negated_impossible)?;
        let impossible_is_negative = validate_atomic_negation(&impossible, &negated)?;
        let positive = self.compile_verify(&closing.impossible, position)?;
        let next = SourcePosition {
            before: position.before + 1,
            ..*position
        };
        let negative = self.compile_verify(&closing.negated_impossible, &next)?;
        let complete = SourcePosition {
            before: position.before + 2,
            ..*position
        };
        // Optional IDs describe earlier exact citations; they are never a replacement
        // for either retained verification tree. Runtime records this view only
        // after both checks have completed, so audit it at that same prefix.
        for (id, expected) in [
            (closing.impossible_fact_id, &impossible),
            (closing.negated_impossible_fact_id, &negated),
        ] {
            if let Some(id) = id {
                let (actual, _) = self.cited_fact_reference(id, &complete)?;
                if actual.ir() != expected.ir() {
                    return Err(LeanCompileError::new(
                        "By/ClosingCitation",
                        "An original closing citation has another subject.",
                    ));
                }
            }
        }
        let (asserted, denied) = if impossible_is_negative {
            (negative, positive)
        } else {
            (positive, negative)
        };
        Ok(format!(
            "(by\n  have _asserted : {} := {}\n  have _denied : ¬ ({}) := {}\n  exact _denied _asserted)",
            asserted.0, asserted.1, asserted.0, denied.1
        ))
    }

    // Output stores have flow-specific stage numbers; the ordinary one-stage
    // fact emitter cannot supply their completed source cursor.
    pub(in crate::compile_to_lean) fn emit_by_completed_fact(
        &self,
        source: &Fact,
        compiled: (String, String),
        store: &StoreFactAndInferResult,
        position: &SourcePosition<'_>,
        completed_before: usize,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        self.validate_store(&store.store, source)?;
        let mut declarations =
            vec![self.emit_fact(source, compiled.clone(), index, local, position)?];
        let name = format!("h_{}", source.fact_id().value());
        let reference = if local {
            name
        } else {
            self.context_application(&name, position)
        };
        let complete = SourcePosition {
            before: completed_before,
            ..*position
        };
        declarations.extend(self.compile_stored_inferences(
            store,
            source,
            &(compiled.0, reference),
            &complete,
        )?);
        Ok(declarations.join("\n\n"))
    }
}

// Reconstruct only the classified negation shape, reusing the recorded target
// ID. This does not allocate an ID, mutate Runtime, or search for a proof.
pub(super) fn validate_atomic_negation(
    left: &Fact,
    right: &Fact,
) -> Result<bool, LeanCompileError> {
    let (Fact::AtomicFact(left), Fact::AtomicFact(right)) = (left, right) else {
        return Err(LeanCompileError::unsupported("By/AtomicNegation"));
    };
    let negative = match left {
        AtomicFact::NormalAtomicFact(_)
        | AtomicFact::EqualFact(_)
        | AtomicFact::LessFact(_)
        | AtomicFact::GreaterFact(_)
        | AtomicFact::LessEqualFact(_)
        | AtomicFact::GreaterEqualFact(_) => false,
        AtomicFact::NotNormalAtomicFact(_)
        | AtomicFact::NotEqualFact(_)
        | AtomicFact::NotLessFact(_)
        | AtomicFact::NotGreaterFact(_)
        | AtomicFact::NotLessEqualFact(_)
        | AtomicFact::NotGreaterEqualFact(_) => true,
        _ => return Err(LeanCompileError::unsupported("By/AtomicNegationFamily")),
    };
    let expected = crate::ast::fact::negate_atomic_fact(left, right.fact_id())
        .ok_or_else(|| LeanCompileError::unsupported("By/AtomicNegationFamily"))?;
    if expected.ir() != right.ir() {
        return Err(LeanCompileError::new(
            "By/NegationSubject",
            "The recorded pair is not the original classified atomic negation.",
        ));
    }
    Ok(negative)
}
