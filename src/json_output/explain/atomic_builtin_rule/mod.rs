//! Atomic-except-equality builtin rules → Normal JSON text.
//!
//! Call site: `rule.rule_id_and_message(lang)` on
//! `AtomicExceptEqualityFactSearchProofByBuiltinRule`. Each family enum and
//! leaf proof owns its copy here (not in `project_normal`).

mod cite;
mod families;
mod greater_equal;
mod less;
mod less_equal;
mod not_equal;
mod text;

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::AtomicExceptEqualityFactSearchProofByBuiltinRule;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;

use self::cite::cite_from_atomic_builtin_rule;
use self::families::family_text;

impl AtomicExceptEqualityFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::GreaterEqualFact(g) => g.rule_id_and_message(lang),
            Self::LessEqualFact(l) => l.rule_id_and_message(lang),
            Self::LessFact(l) => l.rule_id_and_message(lang),
            Self::NotEqualFact(n) => n.rule_id_and_message(lang),
            Self::GreaterFact(_) => family_text("GreaterFactBuiltin", lang),
            Self::IsSetFact(_) => family_text("IsSetFactBuiltin", lang),
            Self::IsNonemptySetFact(_) => family_text("IsNonemptySetFactBuiltin", lang),
            Self::IsFiniteSetFact(_) => family_text("IsFiniteSetFactBuiltin", lang),
            Self::InFact(_) => family_text("InFactBuiltin", lang),
            Self::IsCartFact(_) => family_text("IsCartFactBuiltin", lang),
            Self::IsTupleFact(_) => family_text("IsTupleFactBuiltin", lang),
            Self::SubsetFact(_) => family_text("SubsetFactBuiltin", lang),
            Self::SupersetFact(_) => family_text("SupersetFactBuiltin", lang),
            Self::ProperSubsetFact(_) => family_text("ProperSubsetFactBuiltin", lang),
            Self::ProperSupersetFact(_) => family_text("ProperSupersetFactBuiltin", lang),
            Self::PrimeFact(_) => family_text("PrimeFactBuiltin", lang),
            Self::CoprimeFact(_) => family_text("CoprimeFactBuiltin", lang),
            Self::DvdFact(_) => family_text("DvdFactBuiltin", lang),
            Self::InjectiveFact(_) => family_text("InjectiveFactBuiltin", lang),
            Self::SurjectiveFact(_) => family_text("SurjectiveFactBuiltin", lang),
            Self::BijectiveFact(_) => family_text("BijectiveFactBuiltin", lang),
            Self::IsChoiceFunctionForFact(_) => {
                family_text("IsChoiceFunctionForFactBuiltin", lang)
            }
            Self::NormalAtomicFact(_) => family_text("NormalAtomicFactBuiltin", lang),
            Self::NotNormalAtomicFact(_) => family_text("NotNormalAtomicFactBuiltin", lang),
            Self::NotLessFact(_) => family_text("NotLessFactBuiltin", lang),
            Self::NotGreaterFact(_) => family_text("NotGreaterFactBuiltin", lang),
            Self::NotLessEqualFact(_) => family_text("NotLessEqualFactBuiltin", lang),
            Self::NotGreaterEqualFact(_) => family_text("NotGreaterEqualFactBuiltin", lang),
            Self::NotIsSetFact(_) => family_text("NotIsSetFactBuiltin", lang),
            Self::NotIsNonemptySetFact(_) => family_text("NotIsNonemptySetFactBuiltin", lang),
            Self::NotIsFiniteSetFact(_) => family_text("NotIsFiniteSetFactBuiltin", lang),
            Self::NotInFact(_) => family_text("NotInFactBuiltin", lang),
            Self::NotIsCartFact(_) => family_text("NotIsCartFactBuiltin", lang),
            Self::NotIsTupleFact(_) => family_text("NotIsTupleFactBuiltin", lang),
            Self::NotSubsetFact(_) => family_text("NotSubsetFactBuiltin", lang),
            Self::NotSupersetFact(_) => family_text("NotSupersetFactBuiltin", lang),
            Self::NotProperSubsetFact(_) => family_text("NotProperSubsetFactBuiltin", lang),
            Self::NotProperSupersetFact(_) => family_text("NotProperSupersetFactBuiltin", lang),
            Self::NotPrimeFact(_) => family_text("NotPrimeFactBuiltin", lang),
            Self::NotCoprimeFact(_) => family_text("NotCoprimeFactBuiltin", lang),
            Self::NotDvdFact(_) => family_text("NotDvdFactBuiltin", lang),
            Self::NotInjectiveFact(_) => family_text("NotInjectiveFactBuiltin", lang),
            Self::NotSurjectiveFact(_) => family_text("NotSurjectiveFactBuiltin", lang),
            Self::NotBijectiveFact(_) => family_text("NotBijectiveFactBuiltin", lang),
            Self::NotIsChoiceFunctionForFact(_) => {
                family_text("NotIsChoiceFunctionForFactBuiltin", lang)
            }
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        cite_from_atomic_builtin_rule(self)
    }
}
