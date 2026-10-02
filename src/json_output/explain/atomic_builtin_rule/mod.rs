//! Atomic-except-equality builtin rules → Normal JSON text.
//!
//! Call site: `rule.rule_id_and_message(lang)` on
//! `AtomicExceptEqualityFactSearchProofByBuiltinRule`. Each family enum and
//! leaf proof owns its copy here (not in `project_normal`).

mod cite;
mod greater;
mod greater_equal;
mod in_fact;
mod is_cart;
mod is_finite_set;
mod is_nonempty_set;
mod is_set;
mod is_tuple;
mod less;
mod less_equal;
mod not_equal;
mod not_greater;
mod not_greater_equal;
mod not_in_fact;
mod not_is_finite_set;
mod not_is_nonempty_set;
mod not_less;
mod not_less_equal;
mod not_subset;
mod not_superset;
mod misc_result;
mod subset;
mod superset;
mod text;

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::AtomicExceptEqualityFactSearchProofByBuiltinRule;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;

use self::cite::cite_from_atomic_builtin_rule;

impl AtomicExceptEqualityFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::BijectiveFact(bf) => bf.rule_id_and_message(lang),
            Self::CoprimeFact(cf) => cf.rule_id_and_message(lang),
            Self::DvdFact(df) => df.rule_id_and_message(lang),
            Self::GreaterEqualFact(gef) => gef.rule_id_and_message(lang),
            Self::GreaterFact(gf) => gf.rule_id_and_message(lang),
            Self::InFact(if_) => if_.rule_id_and_message(lang),
            Self::InjectiveFact(if_) => if_.rule_id_and_message(lang),
            Self::IsCartFact(icf) => icf.rule_id_and_message(lang),
            Self::IsChoiceFunctionForFact(icfff) => icfff.rule_id_and_message(lang),
            Self::IsFiniteSetFact(ifsf) => ifsf.rule_id_and_message(lang),
            Self::IsNonemptySetFact(insf) => insf.rule_id_and_message(lang),
            Self::IsSetFact(isf) => isf.rule_id_and_message(lang),
            Self::IsTupleFact(itf) => itf.rule_id_and_message(lang),
            Self::LessEqualFact(lef) => lef.rule_id_and_message(lang),
            Self::LessFact(lf) => lf.rule_id_and_message(lang),
            Self::NormalAtomicFact(naf) => naf.rule_id_and_message(lang),
            Self::NotBijectiveFact(nbf) => nbf.rule_id_and_message(lang),
            Self::NotCoprimeFact(ncf) => ncf.rule_id_and_message(lang),
            Self::NotDvdFact(ndf) => ndf.rule_id_and_message(lang),
            Self::NotEqualFact(nef) => nef.rule_id_and_message(lang),
            Self::NotGreaterEqualFact(ngef) => ngef.rule_id_and_message(lang),
            Self::NotGreaterFact(ngf) => ngf.rule_id_and_message(lang),
            Self::NotInFact(nif) => nif.rule_id_and_message(lang),
            Self::NotInjectiveFact(nif) => nif.rule_id_and_message(lang),
            Self::NotIsCartFact(nicf) => nicf.rule_id_and_message(lang),
            Self::NotIsChoiceFunctionForFact(nicfff) => nicfff.rule_id_and_message(lang),
            Self::NotIsFiniteSetFact(nifsf) => nifsf.rule_id_and_message(lang),
            Self::NotIsNonemptySetFact(ninsf) => ninsf.rule_id_and_message(lang),
            Self::NotIsSetFact(nisf) => nisf.rule_id_and_message(lang),
            Self::NotIsTupleFact(nitf) => nitf.rule_id_and_message(lang),
            Self::NotLessEqualFact(nlef) => nlef.rule_id_and_message(lang),
            Self::NotLessFact(nlf) => nlf.rule_id_and_message(lang),
            Self::NotNormalAtomicFact(nnaf) => nnaf.rule_id_and_message(lang),
            Self::NotPrimeFact(npf) => npf.rule_id_and_message(lang),
            Self::NotProperSubsetFact(npsf) => npsf.rule_id_and_message(lang),
            Self::NotProperSupersetFact(npsf) => npsf.rule_id_and_message(lang),
            Self::NotSubsetFact(nsf) => nsf.rule_id_and_message(lang),
            Self::NotSupersetFact(nsf) => nsf.rule_id_and_message(lang),
            Self::NotSurjectiveFact(nsf) => nsf.rule_id_and_message(lang),
            Self::PrimeFact(pf) => pf.rule_id_and_message(lang),
            Self::ProperSubsetFact(psf) => psf.rule_id_and_message(lang),
            Self::ProperSupersetFact(psf) => psf.rule_id_and_message(lang),
            Self::SubsetFact(sf) => sf.rule_id_and_message(lang),
            Self::SupersetFact(sf) => sf.rule_id_and_message(lang),
            Self::SurjectiveFact(sf) => sf.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        cite_from_atomic_builtin_rule(self)
    }
}


mod order_complement;
