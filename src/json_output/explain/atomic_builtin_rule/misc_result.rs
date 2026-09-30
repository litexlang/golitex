//! Leaf explain for atomic family group `search_atomic_except_equality_fact_proof_by_builtin_rule_result`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::search_atomic_except_equality_fact_proof_by_builtin_rule_result::{
    BijectiveFactSearchProofByBuiltinRule,
    CoprimeByComputation,
    CoprimeFactSearchProofByBuiltinRule,
    DvdFactSearchProofByBuiltinRule,
    InjectiveFactSearchProofByBuiltinRule,
    IsChoiceFunctionForFactSearchProofByBuiltinRule,
    NormalAtomicFactSearchProofByBuiltinRule,
    NotBijectiveFactSearchProofByBuiltinRule,
    NotCoprimeByComputation,
    NotCoprimeFactSearchProofByBuiltinRule,
    NotDvdFactSearchProofByBuiltinRule,
    NotInjectiveFactSearchProofByBuiltinRule,
    NotIsCartFactSearchProofByBuiltinRule,
    NotIsChoiceFunctionForFactSearchProofByBuiltinRule,
    NotIsSetFactSearchProofByBuiltinRule,
    NotIsTupleFactSearchProofByBuiltinRule,
    NotNormalAtomicFactSearchProofByBuiltinRule,
    NotPrimeByComputation,
    NotPrimeFactSearchProofByBuiltinRule,
    NotProperSubsetFactSearchProofByBuiltinRule,
    NotProperSupersetFactSearchProofByBuiltinRule,
    NotSurjectiveFactSearchProofByBuiltinRule,
    PrimeByComputation,
    PrimeFactSearchProofByBuiltinRule,
    ProperSubsetFactSearchProofByBuiltinRule,
    ProperSupersetFactSearchProofByBuiltinRule,
    SurjectiveFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl ProperSubsetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl ProperSupersetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl PrimeFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::PrimeByComputation(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::PrimeByComputation(_) => None,
        }
    }
}

impl PrimeByComputation {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PrimeByComputation",
            "Prime By Computation",
            "`$prime(n)` for a resolved nonnegative integer prime",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PrimeByComputation",
            "计算素性",
            "由封闭非负整数计算判定素数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl CoprimeFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::CoprimeByComputation(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::CoprimeByComputation(_) => None,
        }
    }
}

impl CoprimeByComputation {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CoprimeByComputation",
            "Coprime By Computation",
            "`$coprime(a, b)` when resolved nonnegative integers",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "CoprimeByComputation",
            "计算互素",
            "由 gcd 为 1 判定互素",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl DvdFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl InjectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl SurjectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl BijectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl IsChoiceFunctionForFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NormalAtomicFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotNormalAtomicFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotIsSetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotIsCartFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotIsTupleFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotProperSubsetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotProperSupersetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotPrimeFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::NotPrimeByComputation(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::NotPrimeByComputation(_) => None,
        }
    }
}

impl NotPrimeByComputation {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NotPrimeByComputation",
            "Not Prime By Computation",
            "`not $prime(n)` for a resolved nonnegative non-prime",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NotPrimeByComputation",
            "计算非素性",
            "由封闭非负整数计算判定非素数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NotCoprimeFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::NotCoprimeByComputation(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::NotCoprimeByComputation(_) => None,
        }
    }
}

impl NotCoprimeByComputation {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NotCoprimeByComputation",
            "Not Coprime By Computation",
            "`not $coprime(a, b)` when resolved nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NotCoprimeByComputation",
            "计算非互素",
            "由 gcd 判定非互素",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NotDvdFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotInjectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotSurjectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotBijectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotIsChoiceFunctionForFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

