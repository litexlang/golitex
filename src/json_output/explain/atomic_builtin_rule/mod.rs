//! Atomic-except-equality builtin rules → Normal JSON text.
//!
//! Call site: `rule.rule_id_and_message(lang)` on
//! `AtomicExceptEqualityFactSearchProofByBuiltinRule`. Each family enum and
//! leaf proof owns its copy here (not in `project_normal`).

mod cite;
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
use self::text::family_fallback;

impl AtomicExceptEqualityFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::GreaterEqualFact(g) => g.rule_id_and_message(lang),
            Self::LessEqualFact(l) => l.rule_id_and_message(lang),
            Self::LessFact(l) => l.rule_id_and_message(lang),
            Self::NotEqualFact(n) => n.rule_id_and_message(lang),
            Self::GreaterFact(_) => family_fallback("GreaterFactBuiltin", lang),
            Self::IsSetFact(_) => family_fallback("IsSetFactBuiltin", lang),
            Self::IsNonemptySetFact(_) => family_fallback("IsNonemptySetFactBuiltin", lang),
            Self::IsFiniteSetFact(_) => family_fallback("IsFiniteSetFactBuiltin", lang),
            Self::InFact(_) => family_fallback("InFactBuiltin", lang),
            Self::IsCartFact(_) => family_fallback("IsCartFactBuiltin", lang),
            Self::IsTupleFact(_) => family_fallback("IsTupleFactBuiltin", lang),
            Self::SubsetFact(_) => family_fallback("SubsetFactBuiltin", lang),
            Self::SupersetFact(_) => family_fallback("SupersetFactBuiltin", lang),
            Self::ProperSubsetFact(_) => family_fallback("ProperSubsetFactBuiltin", lang),
            Self::ProperSupersetFact(_) => family_fallback("ProperSupersetFactBuiltin", lang),
            Self::PrimeFact(_) => family_fallback("PrimeFactBuiltin", lang),
            Self::CoprimeFact(_) => family_fallback("CoprimeFactBuiltin", lang),
            Self::DvdFact(_) => family_fallback("DvdFactBuiltin", lang),
            Self::InjectiveFact(_) => family_fallback("InjectiveFactBuiltin", lang),
            Self::SurjectiveFact(_) => family_fallback("SurjectiveFactBuiltin", lang),
            Self::BijectiveFact(_) => family_fallback("BijectiveFactBuiltin", lang),
            Self::IsChoiceFunctionForFact(_) => {
                family_fallback("IsChoiceFunctionForFactBuiltin", lang)
            }
            Self::NormalAtomicFact(_) => family_fallback("NormalAtomicFactBuiltin", lang),
            Self::NotNormalAtomicFact(_) => family_fallback("NotNormalAtomicFactBuiltin", lang),
            Self::NotLessFact(_) => family_fallback("NotLessFactBuiltin", lang),
            Self::NotGreaterFact(_) => family_fallback("NotGreaterFactBuiltin", lang),
            Self::NotLessEqualFact(_) => family_fallback("NotLessEqualFactBuiltin", lang),
            Self::NotGreaterEqualFact(_) => family_fallback("NotGreaterEqualFactBuiltin", lang),
            Self::NotIsSetFact(_) => family_fallback("NotIsSetFactBuiltin", lang),
            Self::NotIsNonemptySetFact(_) => family_fallback("NotIsNonemptySetFactBuiltin", lang),
            Self::NotIsFiniteSetFact(_) => family_fallback("NotIsFiniteSetFactBuiltin", lang),
            Self::NotInFact(_) => family_fallback("NotInFactBuiltin", lang),
            Self::NotIsCartFact(_) => family_fallback("NotIsCartFactBuiltin", lang),
            Self::NotIsTupleFact(_) => family_fallback("NotIsTupleFactBuiltin", lang),
            Self::NotSubsetFact(_) => family_fallback("NotSubsetFactBuiltin", lang),
            Self::NotSupersetFact(_) => family_fallback("NotSupersetFactBuiltin", lang),
            Self::NotProperSubsetFact(_) => family_fallback("NotProperSubsetFactBuiltin", lang),
            Self::NotProperSupersetFact(_) => family_fallback("NotProperSupersetFactBuiltin", lang),
            Self::NotPrimeFact(_) => family_fallback("NotPrimeFactBuiltin", lang),
            Self::NotCoprimeFact(_) => family_fallback("NotCoprimeFactBuiltin", lang),
            Self::NotDvdFact(_) => family_fallback("NotDvdFactBuiltin", lang),
            Self::NotInjectiveFact(_) => family_fallback("NotInjectiveFactBuiltin", lang),
            Self::NotSurjectiveFact(_) => family_fallback("NotSurjectiveFactBuiltin", lang),
            Self::NotBijectiveFact(_) => family_fallback("NotBijectiveFactBuiltin", lang),
            Self::NotIsChoiceFunctionForFact(_) => {
                family_fallback("NotIsChoiceFunctionForFactBuiltin", lang)
            }
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        cite_from_atomic_builtin_rule(self)
    }
}
