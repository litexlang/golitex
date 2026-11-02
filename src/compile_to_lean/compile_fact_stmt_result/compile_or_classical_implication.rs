use crate::compile_to_lean::compile_by_stmt_result::compile_by_contra_stmt_result::validate_atomic_negation;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinClassicalImplication;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_or_classical_implication(
        &self,
        fact: &OrFact,
        selected: &OrBuiltinClassicalImplication,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let assumption = selected.assumed_from_branch_index;
        let conclusion = selected.conclusion_branch_index;
        if fact.facts.len() != 2 || assumption > 1 || conclusion != 1 - assumption {
            return Err(invalid("BranchIndices"));
        }
        let original_negative = crate::ast::fact::and_chain_as_fact(&fact.facts[assumption]);
        if !validate_atomic_negation(&original_negative, &selected.assumed_premise)? {
            return Err(invalid("OriginalNegativeBranch"));
        }
        let original_conclusion = crate::ast::fact::and_chain_as_fact(&fact.facts[conclusion]);
        if source_subject(&selected.conclusion_proof)? != original_conclusion {
            return Err(invalid("OriginalConclusion"));
        }
        let scope = SourcePosition::new(
            Some(position),
            SourceOwner::OrClassicalImplication(selected),
            0,
        );
        self.compile_fact_wd(
            &selected.assumed_well_defined,
            &selected.assumed_premise,
            &scope,
        )?;
        self.validate_store(
            &selected.assumed_store_and_infer.store,
            &selected.assumed_premise,
        )?;
        let formed = SourcePosition::new(
            Some(&scope),
            SourceOwner::FactWD(&selected.assumed_well_defined),
            usize::MAX,
        );
        let assumption_statement = self.fact_proposition(&selected.assumed_premise, &formed)?;
        // The outer Or already established conclusion WD before assuming A.
        // Keep this outer proposition outside the compiled implication; any
        // constructor WD derived inside A stays private to its proof body.
        let conclusion_statement = self.fact_proposition(&original_conclusion, position)?;
        let complete = SourcePosition { before: 2, ..scope };
        let mut body = vec![
            "intro _original_premise".into(),
            self.emit_internal_fact(
                &selected.assumed_premise,
                &(assumption_statement.clone(), "_original_premise".into()),
                &formed,
            )?,
        ];
        body.extend(self.compile_stored_inferences(
            &selected.assumed_store_and_infer,
            &selected.assumed_premise,
            &(
                assumption_statement.clone(),
                format!("h_{}", selected.assumed_premise.fact_id().value()),
            ),
            &complete,
        )?);
        let checked = self.compile_verify(&selected.conclusion_proof, &complete)?;
        body.push(format!("exact {}", checked.1));
        let implication = format!("(by\n  {}\n)", body.join("\n").replace('\n', "\n  "));
        let proof=format!("(Litex.classicalImplicationDisjunction ({assumption_statement}) ({conclusion_statement}) {implication})");
        Ok(if assumption == 0 {
            proof
        } else {
            format!("(Or.symm {proof})")
        })
    }
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("OrImplication/{part}"))
}
