use crate::prelude::{SuccessInferResult, StmtResult, SuccessFactProofResult, SuccessCombinedFactProofItemResult, SUCCESS_COLON};

const VERIFIED_BY: &str = "verified by";
const STORE_FACTS_COLON: &str = "store facts:";

pub(crate) fn stmt_result_body_string(result: &StmtResult) -> String {
    if let Some(x) = result.non_factual_success() {
        let infer_block = x
            .common()
            .map(|common| infer_block_string(&common.infers))
            .unwrap_or_default();
        format!(
            "{}\n{}{}",
            SUCCESS_COLON,
            x.statement(),
            infer_block
        )
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

fn verified_bys_display_line(item: &SuccessCombinedFactProofItemResult) -> String {
    match item {
        SuccessCombinedFactProofItemResult::ByBuiltinRule(r) | SuccessCombinedFactProofItemResult::ByBuiltinStrategy(r) => {
            r.msg.clone()
        }
        SuccessCombinedFactProofItemResult::ByFact(r) => {
            if let Some(d) = &r.detail {
                if !d.is_empty() {
                    return d.clone();
                }
            }
            r.cite_what.to_string()
        }
    }
}

fn verified_by_display_line(verified_by: &SuccessFactProofResult) -> String {
    match verified_by {
        SuccessFactProofResult::BuiltinRule(r) => r.msg.clone(),
        SuccessFactProofResult::BuiltinStrategy(r) => r.msg.clone(),
        SuccessFactProofResult::Fact(r) => {
            if let Some(d) = &r.detail {
                if !d.is_empty() {
                    return d.clone();
                }
            }
            r.cite_what.to_string()
        }
        SuccessFactProofResult::CombinedProofs(w) => {
            if w.cite_what.is_empty() {
                return String::new();
            }
            w.cite_what
                .iter()
                .map(verified_bys_display_line)
                .collect::<Vec<_>>()
                .join("; ")
        }
        SuccessFactProofResult::ForallProof(_) => "forall proof".to_string(),
    }
}
