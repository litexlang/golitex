use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::ExecByContraStmtSuccess;
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Lift the canonical denotation-level universal to arbitrary source host
    /// representations. Membership and domain premises keep their actual IDs.
    pub(super) fn compile_quantified_contra_bridge(
        &self,
        proof: &ExecByContraStmtSuccess,
        denied_goal: &str,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        if matches!(proof.goal, Fact::ExistUniqueFact(_)) {
            return self
                .compile_unique_contra_bridge(proof, denied_goal, position)
                .map(Some);
        }
        let (positive, formation, goal_is_negative) = match (
            &proof.goal,
            &proof.goal_wd,
            &proof.reverse_assumption,
            &proof.reverse_assumption_wd,
        ) {
            (
                Fact::ForallFact(positive),
                VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(wd)),
                Fact::NotForall(_),
                _,
            ) => (positive, wd, false),
            (
                Fact::NotForall(_),
                _,
                Fact::ForallFact(positive),
                FactWellDefinedProof::ForallFact(wd),
            ) => (positive, wd, true),
            _ => return Ok(None),
        };
        // A local hypothesis cannot quantify over Lean universe levels. Store
        // its universal over semantic values; each citation lifts it separately.
        if goal_is_negative {
            return Ok(Some(format!("(Classical.byContradiction {denied_goal})")));
        }
        let scope = SourcePosition::new(
            Some(position),
            SourceOwner::ForallWD(positive, formation),
            0,
        );
        let (_, introductions, definitions) = self.compile_forall_head(
            positive,
            &formation.introduced_params,
            &formation.assumed_dom_facts,
            &scope,
        )?;
        let mut arguments = Vec::new();
        for (parameter, store) in positive
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .zip(
                &formation
                    .introduced_params
                    .defined_params
                    .store_and_infer_results,
            )
        {
            let name = format!("_value_i{}", parameter.id.value());
            arguments.push(format!(
                "(Litex.semanticObject (Litex.denote {name}) (Litex.isSet {name}))"
            ));
            arguments.push(format!("h_{}", store.primary_fact_id().value()));
        }
        arguments.extend(
            positive
                .dom_facts
                .iter()
                .map(|f| format!("h_{}", f.fact_id().value())),
        );
        let mut steps = vec!["classical".to_string()];
        steps.push("intro _canonical".into());
        steps.push(format!("apply {denied_goal}"));
        steps.push(format!("intro {}", introductions.join(" ")));
        steps.extend(definitions);
        steps.push(format!("exact _canonical {}", arguments.join(" ")));
        Ok(Some(format!(
            "(by\n  {})",
            steps.join("\n").replace('\n', "\n  ")
        )))
    }

    /// Reuse the checked head, specializing only host binders. Membership,
    /// domain facts and their WD producers keep their original source IDs.
    pub(in crate::compile_to_lean) fn compile_canonical_forall_head(
        &self,
        fact: &ForallFact,
        proof: &ForallFactWellDefinedProof,
        scope: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>, Vec<String>), LeanCompileError> {
        let (mut binders, _, definitions) = self.compile_forall_head(
            fact,
            &proof.introduced_params,
            &proof.assumed_dom_facts,
            scope,
        )?;
        let mut introductions = Vec::new();
        for (index, (id, store)) in fact
            .typed_parameters
            .ordered_param_ids()
            .iter()
            .zip(
                &proof
                    .introduced_params
                    .defined_params
                    .store_and_infer_results,
            )
            .enumerate()
        {
            let value = format!("_value_i{}", id.value());
            binders[2 * index] = format!("({value} : Litex.Obj (M := M) M.Value)");
            introductions.extend([value, format!("h_{}", store.primary_fact_id().value())]);
        }
        introductions.extend(
            fact.dom_facts
                .iter()
                .map(|f| format!("h_{}", f.fact_id().value())),
        );
        Ok((binders, introductions, definitions))
    }

    pub(in crate::compile_to_lean) fn compile_local_forall_citation(
        &self,
        id: FactId,
        reference: String,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (run, index, statement, before) in position.context_statements() {
            let stages = crate::compile_to_lean::compile_assumption_stmt_result::assumption_stages(
                statement,
            );
            for (offset, (fact, wd, _)) in stages
                .iter()
                .take(before.saturating_sub(stages.len()))
                .enumerate()
            {
                if fact.fact_id() != id {
                    continue;
                }
                if let (Fact::ForallFact(fact), FactWellDefinedProof::ForallFact(wd)) = (fact, wd) {
                    let prior = SourcePosition::new(None, SourceOwner::Run(run), index);
                    let before = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::Statement(statement),
                        offset,
                    );
                    return self.compile_canonical_forall_citation(fact, wd, reference, &before);
                }
            }
        }
        let mut cursor = Some(position);
        while let Some(owner) = cursor {
            if let SourceOwner::Contra(proof) = owner.owner {
                if proof.reverse_assumption_fact_id == id {
                    if let (Fact::ForallFact(fact), FactWellDefinedProof::ForallFact(wd)) =
                        (&proof.reverse_assumption, &proof.reverse_assumption_wd)
                    {
                        // Reconstruct only the original formation prefix. The
                        // assumption itself and later proof steps are not visible.
                        let before_assumption = SourcePosition {
                            before: 0,
                            ..*owner
                        };
                        return self.compile_canonical_forall_citation(
                            fact,
                            wd,
                            reference,
                            &before_assumption,
                        );
                    }
                }
            }
            cursor = owner.parent;
        }
        Ok(reference)
    }
    fn compile_canonical_forall_citation(
        &self,
        fact: &ForallFact,
        wd: &ForallFactWellDefinedProof,
        reference: String,
        before: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let term = SourcePosition::new(Some(before), SourceOwner::Term, 0);
        let scope = SourcePosition::new(Some(&term), SourceOwner::ForallWD(fact, wd), 0);
        let (binders, _, mut definitions) =
            self.compile_forall_head(fact, &wd.introduced_params, &wd.assumed_dom_facts, &scope)?;
        let mut arguments = Vec::new();
        for (parameter, store) in fact
            .typed_parameters
            .ordered_param_ids()
            .iter()
            .zip(&wd.introduced_params.defined_params.store_and_infer_results)
        {
            let value = format!("_value_i{}", parameter.value());
            arguments.push(format!(
                "(Litex.semanticObject (Litex.denote {value}) (Litex.isSet {value}))"
            ));
            arguments.push(format!("h_{}", store.primary_fact_id().value()));
        }
        arguments.extend(
            fact.dom_facts
                .iter()
                .map(|f| format!("h_{}", f.fact_id().value())),
        );
        definitions.push(format!("exact {reference} {}", arguments.join(" ")));
        let proposition = self.compile_forall_formation(fact, wd, &term)?;
        Ok(format!(
            "(show {proposition} from (fun {} => by\n  {}))",
            binders.join(" "),
            definitions.join("\n").replace('\n', "\n  ")
        ))
    }
}
