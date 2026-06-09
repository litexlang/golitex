use crate::prelude::{InferResult, StmtResult, VerifiedByResult, VerifiedBysEnum, SUCCESS_COLON};

const VERIFIED_BY: &str = "verified by";
const EFFECTS_COLON: &str = "effects:";

pub(crate) fn stmt_result_body_string(result: &StmtResult) -> String {
    if let Some(x) = result.non_factual_success() {
        format!(
            "{}\n{}{}",
            SUCCESS_COLON,
            x.stmt,
            infer_block_string(&x.infers)
        )
    } else if let Some(x) = result.factual_success() {
        format!(
            "{}\n{}\n{}\n{}{}",
            SUCCESS_COLON,
            x.stmt,
            VERIFIED_BY,
            verified_by_display_line(&x.verified_by),
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

fn infer_block_string(infer_result: &InferResult) -> String {
    if infer_result.is_empty() {
        return String::new();
    }
    format!(
        "\n\n{}\n{}",
        EFFECTS_COLON,
        infer_result.join_infer_lines("\n")
    )
}

fn verified_bys_display_line(item: &VerifiedBysEnum) -> String {
    match item {
        VerifiedBysEnum::ByBuiltinRule(r) => r.msg.clone(),
        VerifiedBysEnum::ByFact(r) => {
            if let Some(d) = &r.detail {
                if !d.is_empty() {
                    return d.clone();
                }
            }
            r.cite_what.to_string()
        }
    }
}

fn verified_by_display_line(verified_by: &VerifiedByResult) -> String {
    match verified_by {
        VerifiedByResult::BuiltinRule(r) => r.msg.clone(),
        VerifiedByResult::Fact(r) => {
            if let Some(d) = &r.detail {
                if !d.is_empty() {
                    return d.clone();
                }
            }
            r.cite_what.to_string()
        }
        VerifiedByResult::VerifiedBys(w) => {
            if w.cite_what.is_empty() {
                return String::new();
            }
            w.cite_what
                .iter()
                .map(verified_bys_display_line)
                .collect::<Vec<_>>()
                .join("; ")
        }
        VerifiedByResult::ForallProof(_) => "forall proof".to_string(),
    }
}
