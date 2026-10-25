use super::compile_assumption_stmt_result::{assumption_stages, assumption_start, trust_have};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult, ExecSketchStmtResult,
};
use crate::prelude::*;

/// Borrow the original lexical block and its actual parameter introductions.
fn block(
    statement: &ExecStmtResult,
) -> Option<(
    SourceOwner<'_>,
    Option<(
        &ForallFact,
        &IntroduceTypedParametersResult,
        &[AssumeDomFactResult],
    )>,
    &[ExecStmtResult],
)> {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) => {
            let head = match (&p.statement.fact, &p.body) {
                (Fact::ForallFact(f), ExecDefThmBodyProof::Forall(b)) => {
                    Some((f, &b.introduced_params, b.assumed_dom_facts.as_slice()))
                }
                _ => None,
            };
            let steps = match &p.body {
                ExecDefThmBodyProof::Forall(b) => &b.proof_steps,
                ExecDefThmBodyProof::NonForall(b) => &b.proof_steps,
            };
            Some((SourceOwner::Named(p), head, steps))
        }
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Success(p),
        )) => {
            let head = match (&p.statement.fact, &p.body) {
                (Fact::ForallFact(f), ExecClaimBodyProof::Forall(b)) => {
                    Some((f, &b.introduced_params, b.assumed_dom_facts.as_slice()))
                }
                _ => None,
            };
            Some((SourceOwner::Claim(p), head, p.body.proof_steps()))
        }
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(
            ExecSketchStmtResult::Success(p),
        )) => Some((SourceOwner::Sketch(p), None, &p.proof_steps)),
        _ => None,
    }
}

pub(super) fn local_assumption_ids(statement: &ExecStmtResult) -> Vec<FactId> {
    let Some((_, _, steps)) = block(statement) else {
        return Vec::new();
    };
    steps
        .iter()
        .flat_map(|step| {
            let mut ids = assumption_stages(step)
                .iter()
                .map(|(f, _, _)| f.fact_id())
                .collect::<Vec<_>>();
            ids.extend(local_assumption_ids(step));
            ids
        })
        .collect()
}

impl LitexToLeanCompiler {
    pub(super) fn closed_assumption_binders(
        &self,
        statement: &ExecStmtResult,
        parent: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        if local_assumption_ids(statement).is_empty() {
            return Ok(Vec::new());
        }
        Ok(self
            .close_statement_assumptions(statement, parent)?
            .into_iter()
            .map(|(id, proposition)| format!("(h_{} : {proposition})", id.value()))
            .collect())
    }

    fn close_statement_assumptions(
        &self,
        statement: &ExecStmtResult,
        parent: &SourcePosition<'_>,
    ) -> Result<Vec<(FactId, String)>, LeanCompileError> {
        let statement_scope =
            SourcePosition::new(Some(parent), SourceOwner::Statement(statement), 0);
        if matches!(statement, ExecStmtResult::Trust(_)) {
            if trust_have(statement).is_some() {
                return Err(LeanCompileError::unsupported(
                    "Assumption/LocalWitnessClosure",
                ));
            }
            return assumption_stages(statement)
                .iter()
                .enumerate()
                .map(|(i, (fact, wd, store))| {
                    self.validate_store(&store.store, fact)?;
                    let site = SourcePosition {
                        before: assumption_start(statement) + i,
                        ..statement_scope
                    };
                    Ok((
                        fact.fact_id(),
                        self.compile_assumption_proposition(wd, fact, &site)?,
                    ))
                })
                .collect();
        }
        if local_assumption_ids(statement).is_empty() {
            return Ok(Vec::new());
        }
        let Some((owner, header, steps)) = block(statement) else {
            return Ok(Vec::new());
        };
        let scope = SourcePosition::new(Some(&statement_scope), owner, 0);
        let (mut binders, _, mut definitions) = match header {
            Some((fact, introduced, assumed)) => {
                self.compile_forall_head(fact, introduced, assumed, &scope)?
            }
            None => (Vec::new(), Vec::new(), Vec::new()),
        };
        // A context hypothesis cannot quantify over universe levels. Close on
        // semantic objects; use sites retain their own host representation.
        if let Some((fact, _, _)) = header {
            for (index, id) in fact.typed_parameters.ordered_param_ids().iter().enumerate() {
                binders[2 * index] =
                    format!("(_value_i{} : Litex.Obj (M := M) M.Value)", id.value());
            }
        }
        let head_count = header.map_or(0, |(f, _, _)| {
            f.typed_parameters.ordered_param_ids().len() + f.dom_facts.len()
        });
        let mut closed = Vec::new();
        let last = steps
            .iter()
            .rposition(|s| !assumption_stages(s).is_empty() || !local_assumption_ids(s).is_empty())
            .expect("contains assumptions");
        for (index, step) in steps.iter().take(last + 1).enumerate() {
            let prior = SourcePosition {
                before: head_count + index,
                ..scope
            };
            for (id, proposition) in self.close_statement_assumptions(step, &prior)? {
                let proposition = self.scope_proposition(proposition, &definitions);
                closed.push((
                    id,
                    if binders.is_empty() {
                        proposition
                    } else {
                        format!("(∀ {}, {proposition})", binders.join(" "))
                    },
                ));
            }
            if index < last {
                let compiled = self.compile_statement_in_scope(step, &prior, index + 1, true)?;
                if compiled.lines().any(|line| line.starts_with("obtain ")) {
                    return Err(LeanCompileError::unsupported(
                        "Assumption/LocalWitnessClosure",
                    ));
                }
                definitions.push(compiled);
            }
        }
        Ok(closed)
    }

    /// Apply the already-declared closure at the original enclosing binders.
    pub(super) fn local_assumption_reference(
        &self,
        id: FactId,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let mut cursor = position.parent;
        let mut scopes = Vec::new();
        let mut top_statement = None;
        while let Some(p) = cursor {
            if let SourceOwner::Statement(statement) = p.owner {
                if p.parent
                    .is_some_and(|q| matches!(q.owner, SourceOwner::Run(_)))
                {
                    top_statement = Some(statement);
                }
            }
            let header = match p.owner {
                SourceOwner::Named(proof) => match (&proof.statement.fact, &proof.body) {
                    (Fact::ForallFact(f), ExecDefThmBodyProof::Forall(b)) => {
                        Some((f, &b.introduced_params))
                    }
                    _ => None,
                },
                SourceOwner::Claim(proof) => match (&proof.statement.fact, &proof.body) {
                    (Fact::ForallFact(f), ExecClaimBodyProof::Forall(b)) => {
                        Some((f, &b.introduced_params))
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some((fact, introduced)) = header {
                let mut args = Vec::new();
                for (parameter, store) in fact
                    .typed_parameters
                    .groups
                    .iter()
                    .flat_map(|g| &g.params)
                    .zip(&introduced.defined_params.store_and_infer_results)
                {
                    let n = parameter.id.value();
                    args.extend([format!("(Litex.semanticObject (Litex.denote _value_i{n}) (Litex.isSet _value_i{n}))"), format!("h_{}", store.primary_fact_id().value())]);
                }
                args.extend(
                    fact.dom_facts
                        .iter()
                        .map(|f| format!("h_{}", f.fact_id().value())),
                );
                scopes.push(args);
            }
            cursor = p.parent;
        }
        if !top_statement.is_some_and(|s| local_assumption_ids(s).contains(&id)) {
            return Err(LeanCompileError::unsupported("Assumption/LocalClosure"));
        }
        scopes.reverse();
        let args = scopes.into_iter().flatten().collect::<Vec<_>>();
        Ok(if args.is_empty() {
            format!("h_{}", id.value())
        } else {
            format!("(@h_{} {})", id.value(), args.join(" "))
        })
    }
}
