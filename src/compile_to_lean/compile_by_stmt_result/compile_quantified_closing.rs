use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Both children have already been replayed at their original closing
    /// stages and their classified negation checked. These are fixed logical
    /// eliminations, independent of the source verifier's search route.
    pub(super) fn compile_quantified_closing(
        &self,
        source: &Fact,
        negated: &Fact,
        positive: &(String, String),
        negative: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let (forall, asserted, denied) = match (source, negated) {
            (Fact::ForallFact(fact), Fact::NotForall(_)) => (fact, positive, negative),
            (Fact::NotForall(_), Fact::ForallFact(fact)) => (fact, negative, positive),
            (Fact::ExistUniqueFact(fact), Fact::ForallFact(_)) => {
                return self
                    .compile_unique_closing(fact, positive, negative, position)
                    .map(Some);
            }
            _ => return Ok(None),
        };
        let mut arguments = Vec::new();
        for parameter in forall
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
        {
            arguments.push(format!("_closing_i{}", parameter.id.value()));
            arguments.push(format!("_closing_member_i{}", parameter.id.value()));
        }
        arguments.extend(
            forall
                .dom_facts
                .iter()
                .map(|f| format!("h_{}", f.fact_id().value())),
        );
        Ok(Some(format!("(by\n  have _universal : {} := {}\n  have _not_universal : {} := {}\n  apply _not_universal\n  intro {}\n  exact _universal {})", asserted.0, asserted.1, denied.0, denied.1,
            arguments.join(" "), arguments.join(" "))))
    }

    fn compile_unique_closing(
        &self,
        source: &PlainExistFact,
        asserted: &(String, String),
        denied: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let parameters = source.typed_parameters.ordered_param_ids();
        let (_, unique_arguments) = self.unique_signature(source, position)?;
        let candidates: Vec<Vec<String>> = ["left", "right"]
            .iter()
            .map(|side| {
                let mut arguments = Vec::new();
                for id in &parameters {
                    arguments.push(format!("_unique_{side}_i{}", id.value()));
                    arguments.push(format!("_member_{side}_i{}", id.value()));
                }
                arguments.extend((0..source.facts.len()).map(|i| format!("_body_{side}_{i}")));
                arguments
            })
            .collect();
        let mut left_pattern = candidates[0].clone();
        if source.facts.is_empty() {
            left_pattern.push("_".into());
        }
        let mut right_pattern = candidates[1].clone();
        right_pattern.push("_different".into());
        let mut steps = vec![
            format!("have _unique_exists : {} := {}", asserted.0, asserted.1),
            format!("have _alternative : {} := {}", denied.0, denied.1),
            "rcases _unique_exists with ⟨_exists, _unique⟩".into(),
            format!("rcases _exists with ⟨{}⟩", left_pattern.join(", ")),
            format!(
                "obtain ⟨{}⟩ := _alternative {}",
                right_pattern.join(", "),
                candidates[0].join(" ")
            ),
            format!("have _same := _unique {}", unique_arguments.join(" ")),
        ];
        if parameters.len() == 1 {
            steps.push("exact _different _same.symm".into());
        } else {
            steps.push(format!(
                "rcases _different with {}",
                vec!["_different"; parameters.len()].join(" | ")
            ));
            for i in 0..parameters.len() {
                let mut index = format!("(0 : Fin {})", parameters.len() - i);
                for _ in 0..i {
                    index = format!("(Fin.succ {index})");
                }
                steps.push(format!("· apply _different\n  simpa only [Litex.Same, Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using (congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index {index})) _same).symm"));
            }
        }
        Ok(format!(
            "(by\n  {})",
            steps.join("\n").replace('\n', "\n  ")
        ))
    }
}
