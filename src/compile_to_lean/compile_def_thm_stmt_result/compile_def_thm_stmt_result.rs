use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_named_theorem(
        &self,
        proof: &ExecDefThmStmtSuccess,
        position: &SourcePosition<'_>,
        _index: usize,
    ) -> Result<String, LeanCompileError> {
        let goal_wd = match &proof.goal_wd {
            VerifyFactWellDefinedResult::Success(wd) => wd,
            VerifyFactWellDefinedResult::Failed(_) => {
                return Err(LeanCompileError::new(
                    "Theorem/GoalWD",
                    "A successful theorem has failed goal-formation evidence.",
                ))
            }
        };
        self.compile_fact_wd(goal_wd, &proof.statement.fact, position)?;
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::Named(proof),
            before: 0,
        };
        let compiled = self.compile_named_theorem_body(proof, &source_position);
        let compiled = compiled?;
        self.validate_store(&proof.stored, &proof.statement.fact)?;
        let name = format!("h_{}", proof.statement.fact.fact_id().value());
        let declaration = format!(
            "theorem {name}{} : {} :=\n  {}",
            self.context_header(position),
            compiled.0,
            compiled.1.replace('\n', "\n  ")
        );
        Ok(declaration)
    }

    pub(in crate::compile_to_lean) fn compile_named_theorem_body(
        &self,
        proof: &ExecDefThmStmtSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let (binders, introductions, definitions, steps, results, expected) =
            match (&proof.statement.fact, &proof.body) {
                (Fact::ForallFact(fact), ExecDefThmBodyProof::Forall(body)) => {
                    let (binders, introductions, definitions) = self.compile_forall_head(
                        fact,
                        &body.introduced_params,
                        &body.assumed_dom_facts,
                        position,
                    )?;
                    let expected = fact
                        .then_facts
                        .iter()
                        .map(|fact| match fact {
                            ExistOrAndChainAtomicFact::AtomicFact(atomic) => {
                                Ok(Fact::AtomicFact(atomic.clone()))
                            }
                            _ => Err(LeanCompileError::unsupported("Theorem/CompoundThen")),
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    (
                        binders,
                        introductions,
                        definitions,
                        &body.proof_steps,
                        body.conclusion_proofs.iter().collect::<Vec<_>>(),
                        expected,
                    )
                }
                (Fact::AtomicFact(_), ExecDefThmBodyProof::NonForall(body)) => (
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    &body.proof_steps,
                    vec![&body.conclusion_proof],
                    vec![proof.statement.fact.clone()],
                ),
                _ => return Err(LeanCompileError::unsupported("Theorem/GoalBodyShape")),
            };
        if steps.len() != proof.statement.prove_process.len()
            || results.len() != expected.len()
            || results.is_empty()
        {
            return Err(LeanCompileError::new(
                "Theorem/Stages",
                "The theorem body has different source steps or conclusion arity.",
            ));
        }
        let head_count = match &proof.statement.fact {
            Fact::ForallFact(f) => {
                f.typed_parameters
                    .groups
                    .iter()
                    .map(|g| g.params.len())
                    .sum::<usize>()
                    + f.dom_facts.len()
            }
            _ => 0,
        };
        let mut body_text = definitions;
        for (index, (source, step)) in proof.statement.prove_process.iter().zip(steps).enumerate() {
            validate_statement_capture(source, step)?;
            body_text.push(self.compile_statement_in_scope(
                step,
                &SourcePosition {
                    before: head_count + index,
                    ..*position
                },
                index + 1,
                true,
            )?);
        }
        let mut conclusions = Vec::new();
        for (expected, result) in expected.iter().zip(results) {
            let compiled = self.compile_verify(
                result,
                &SourcePosition {
                    before: head_count + steps.len(),
                    ..*position
                },
            )?;
            if &source_subject(result)? != expected {
                return Err(LeanCompileError::new(
                    "Theorem/Conclusion",
                    "The proof has another source conclusion.",
                ));
            }
            conclusions.push(compiled);
        }
        let mut conclusion = conclusions.pop().expect("nonempty conclusions");
        while let Some(left) = conclusions.pop() {
            conclusion.0 = format!("({} ∧ {})", left.0, conclusion.0);
            conclusion.1 = format!("(And.intro {} {})", left.1, conclusion.1);
        }
        let closed_proposition = self.scope_proposition(conclusion.0, &body_text);
        let proposition = if binders.is_empty() {
            closed_proposition
        } else {
            format!("∀ {}, {}", binders.join(" "), closed_proposition)
        };
        let mut statements = Vec::new();
        if !introductions.is_empty() {
            statements.push(format!("intro {}", introductions.join(" ")));
        }
        statements.extend(body_text);
        statements.push(format!("exact {}", conclusion.1));
        Ok((
            proposition,
            format!("(by\n  {}\n)", statements.join("\n").replace('\n', "\n  ")),
        ))
    }
}
