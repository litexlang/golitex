//! Localized explanations for JSON output.
//!
//! Keep all localized copy here. Verify/exec IR types stay language-free;
//! projection calls into this module with `OutputLanguage` from LaunchCommand.
//!
//! Policy: every Normal surface has localized `rule_name` / `message`,
//! including every atomic builtin leaf (no family-level stubs).

pub mod atomic_builtin_rule;
pub mod equality_builtin_rule;
pub mod searched_proof_why;
pub mod stmt_why;
mod text;

pub use searched_proof_why::explain_searched_proof_why;
pub use stmt_why::{explain_compound_fact_why, explain_define_obj_why, explain_stmt_kind};
pub use text::BuiltinRuleText;

pub(super) fn well_defined_not_proven_message(
    language: crate::launch_command::OutputLanguage,
) -> &'static str {
    use crate::launch_command::OutputLanguage;
    match language {
        OutputLanguage::English => "Could not prove that the statement is well-defined.",
        OutputLanguage::Chinese => "未能证明该语句中的表达式有定义。",
        OutputLanguage::ChineseTraditional => "未能證明該語句中的表達式有定義。",
        OutputLanguage::French => "Impossible de prouver que l'énoncé est bien défini.",
        OutputLanguage::Russian => {
            "Не удалось доказать корректность определения выражений в утверждении."
        }
        OutputLanguage::Spanish => "No se pudo demostrar que el enunciado está bien definido.",
        OutputLanguage::Arabic => "تعذر إثبات أن العبارة معرفة تعريفا سليما.",
        OutputLanguage::Japanese => "文中の式が適切に定義されていることを証明できませんでした。",
        OutputLanguage::Korean => "명제의 표현식이 잘 정의되어 있음을 증명하지 못했습니다.",
        OutputLanguage::Vietnamese => "Không thể chứng minh rằng mệnh đề được xác định tốt.",
    }
}
