use crate::json_output::explain::{text::text, BuiltinRuleText};
use crate::launch_command::OutputLanguage;
use crate::prelude::*;

pub(super) fn sign_text(proof: &StructuralRealSignProof, lang: OutputLanguage) -> BuiltinRuleText {
    let relation = match proof.sign {
        RealSign::Positive => "> 0",
        RealSign::Negative => "< 0",
        RealSign::Nonnegative => ">= 0",
        RealSign::Nonpositive => "<= 0",
        RealSign::Nonzero => "!= 0",
        RealSign::Zero => "= 0",
    };
    text(
        label(lang),
        &format!("{} {relation}", proof.element.readable_string()),
    )
}

pub(super) fn membership_text(
    proof: &SignedNumericMembershipProof,
    lang: OutputLanguage,
) -> BuiltinRuleText {
    text(
        label(lang),
        &format!(
            "{} $in {}; {}",
            proof.base_membership.element.readable_string(),
            Obj::StandardSet(proof.base_membership.set.clone()).readable_string(),
            sign_text(&proof.sign, lang).message
        ),
    )
}

fn label(lang: OutputLanguage) -> &'static str {
    match lang {
        OutputLanguage::English => "Compose real sign certificates",
        OutputLanguage::Chinese => "组合实数符号证明",
        OutputLanguage::ChineseTraditional => "組合實數符號證明",
        OutputLanguage::French => "Composer les preuves de signe réel",
        OutputLanguage::Russian => "Композиция доказательств знака вещественных чисел",
        OutputLanguage::Spanish => "Componer pruebas de signo real",
        OutputLanguage::Arabic => "تركيب براهين إشارة الأعداد الحقيقية",
        OutputLanguage::Japanese => "実数の符号の証明を合成",
        OutputLanguage::Korean => "실수 부호 증명의 합성",
        OutputLanguage::Vietnamese => "Kết hợp chứng minh dấu số thực",
    }
}
