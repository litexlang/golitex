use crate::prelude::{StmtResult, SuccessFactProofResult, SuccessInferResult, SUCCESS_COLON};

const VERIFIED_BY: &str = "verified by";
const STORE_FACTS_COLON: &str = "store facts:";

pub fn stmt_result_body_string(result: &StmtResult) -> String {
    if let Some(x) = result.non_factual_success() {
        let infer_block = x
            .common()
            .map(|common| infer_block_string(&common.infers))
            .unwrap_or_default();
        format!("{}\n{}{}", SUCCESS_COLON, x.statement(), infer_block)
    } else if let Some(x) = result.factual_success() {
        format!(
            "{}\n{}\n{}\n{}{}",
            SUCCESS_COLON,
            x.fact(),
            VERIFIED_BY,
            verified_by_display_line(x.proof()),
            infer_block_string(&x.infers)
        )
    } else if let Some(x) = result.as_unknown() {
        x.to_string()
    } else if let Some(x) = result.as_fact_unknown() {
        x.to_string()
    } else {
        unreachable!()
    }
}

fn infer_block_string(infer_result: &SuccessInferResult) -> String {
    if infer_result.is_empty() {
        return String::new();
    }
    format!(
        "\n\n{}\n{}",
        STORE_FACTS_COLON,
        infer_result.join_infer_lines("\n")
    )
}

fn verified_by_display_line(verified_by: &SuccessFactProofResult) -> String {
    match verified_by {
        SuccessFactProofResult::BuiltinRule(r) => r.msg.clone(),
        SuccessFactProofResult::BuiltinStrategy(r) => r.msg.clone(),
        SuccessFactProofResult::StoredFactCitation(r) => {
            if let Some(d) = &r.detail {
                if !d.is_empty() {
                    return d.clone();
                }
            }
            r.source_fact.to_string()
        }
        SuccessFactProofResult::KnownForallInstantiation(r) => r.source_fact.to_string(),
        SuccessFactProofResult::DefinitionReduction(r) => {
            r.detail.clone().unwrap_or_else(|| r.definition.to_string())
        }
        SuccessFactProofResult::CheckedFunctionDefinitionReduction(r) => r
            .detail
            .clone()
            .unwrap_or_else(|| "checked function definition reduction".to_string()),
        SuccessFactProofResult::DiagnosticOnly(r) => r.detail.clone(),
        SuccessFactProofResult::CombinedProofs(w) => {
            let mut parts = Vec::new();
            if let Some(primary) = w.primary.as_ref() {
                parts.push(verified_by_display_line(primary.proof()));
            }
            for step in w.steps.iter() {
                if let Some(factual) = step.factual_success() {
                    parts.push(verified_by_display_line(factual.proof()));
                } else {
                    parts.push("statement result".to_string());
                }
            }
            parts.join("; ")
        }
        SuccessFactProofResult::ForallProof(_) => "forall proof".to_string(),
        SuccessFactProofResult::Transform(result) => {
            format!(
                "fact transform after {}",
                verified_by_display_line(result.source.proof())
            )
        }
        SuccessFactProofResult::Reuse(result) => verified_by_display_line(result.source.proof()),
    }
}
