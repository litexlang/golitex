//! Explain + cite for `NotEqualFactSearchProofByBuiltinRule`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::{NotEqualFactSearchProofByBuiltinRule,
    AbsNonzeroFromArgBuiltinRuleProof,
    AddNonzeroFromNotEqualNegationBuiltinRuleProof,
    ClosedDecimalNotEqualBuiltinRuleProof,
    CosNonzeroAtZeroBuiltinRuleProof,
    CosNonzeroOnOpenHalfPiBuiltinRuleProof,
    DiffNonzeroFromInequalityBuiltinRuleProof,
    DivNonzeroFromFactorsBuiltinRuleProof,
    EmptySetFromNonemptyBuiltinRuleProof,
    FromKnownStrictOrderBuiltinRuleProof,
    ListSetDifferentLengthBuiltinRuleProof,
    MembershipContradictionBuiltinRuleProof,
    NotEqualSymmetryBuiltinRuleProof,
    PowNonzeroFromBaseBuiltinRuleProof,
    ProductComponentNonzeroBuiltinRuleProof,
    SinNonzeroAtHalfPiBuiltinRuleProof,
    SinNonzeroOnOpenPiBuiltinRuleProof,
    SqrtNonzeroFromPositiveArgBuiltinRuleProof,
    SquareSumNonzeroFromComponentBuiltinRuleProof,
    ZeroFromNatAndOneLeBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::from_known_in_signed_standard_set::FromKnownInNonzeroStandardSetBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::{family_fallback, text};

impl NotEqualFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ClosedDecimal(p) => p.rule_id_and_message(lang),
            Self::NotEqualSymmetry(p) => p.rule_id_and_message(lang),
            Self::ListSetDifferentLength(p) => p.rule_id_and_message(lang),
            Self::FromKnownStrictOrder(p) => p.rule_id_and_message(lang),
            Self::FromKnownInNonzeroStandardSet(_) => family_fallback(
                "FromKnownInNonzeroStandardSet",
                lang,
            ),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_id_and_message(lang),
            Self::CosNonzeroAtZero(p) => p.rule_id_and_message(lang),
            Self::SinNonzeroOnOpenPi(p) => p.rule_id_and_message(lang),
            Self::SinNonzeroAtHalfPi(p) => p.rule_id_and_message(lang),
            Self::AbsNonzeroFromArg(p) => p.rule_id_and_message(lang),
            Self::DiffNonzeroFromInequality(p) => p.rule_id_and_message(lang),
            Self::EmptySetFromNonempty(p) => p.rule_id_and_message(lang),
            Self::ZeroFromNatAndOneLe(p) => p.rule_id_and_message(lang),
            Self::PowNonzeroFromBase(p) => p.rule_id_and_message(lang),
            Self::DivNonzeroFromFactors(p) => p.rule_id_and_message(lang),
            Self::ProductComponentNonzero(p) => p.rule_id_and_message(lang),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_id_and_message(lang),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_id_and_message(lang),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_id_and_message(lang),
            Self::MembershipContradiction(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FromKnownStrictOrder(p) => Some(p.cite_fact_id),
            Self::FromKnownInNonzeroStandardSet(p) => Some(p.cite_fact_id),
            _ => None,
        }
    }
}

impl ClosedDecimalNotEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedDecimalNotEqual",
            "Closed decimal inequality",
            "Both sides evaluate to different closed numbers",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedDecimalNotEqual",
            "封闭数值不等",
            "两边算出不同的封闭数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NotEqualSymmetryBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NotEqualSymmetry",
            "Inequality symmetry",
            "Inequality is symmetric in its two sides",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NotEqualSymmetry",
            "不等号对称性",
            "不等关系对两边对称",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ListSetDifferentLengthBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ListSetDifferentLength", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FromKnownStrictOrderBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("FromKnownStrictOrder", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FromKnownInNonzeroStandardSetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownInNonzeroStandardSet",
            "From known nonzero",
            "Inequality follows from known nonzero / nonzero-set membership",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownInNonzeroStandardSet",
            "已知非零",
            "不等关系由已知非零（或非零集成员）推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl CosNonzeroOnOpenHalfPiBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("CosNonzeroOnOpenHalfPi", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl CosNonzeroAtZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("CosNonzeroAtZero", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SinNonzeroOnOpenPiBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SinNonzeroOnOpenPi", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SinNonzeroAtHalfPiBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SinNonzeroAtHalfPi", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AbsNonzeroFromArgBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AbsNonzeroFromArg", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl DiffNonzeroFromInequalityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("DiffNonzeroFromInequality", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl EmptySetFromNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("EmptySetFromNonempty", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ZeroFromNatAndOneLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ZeroFromNatAndOneLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl PowNonzeroFromBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("PowNonzeroFromBase", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl DivNonzeroFromFactorsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("DivNonzeroFromFactors", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ProductComponentNonzeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ProductComponentNonzero", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SqrtNonzeroFromPositiveArgBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SqrtNonzeroFromPositiveArg", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SquareSumNonzeroFromComponentBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SquareSumNonzeroFromComponent", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AddNonzeroFromNotEqualNegationBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AddNonzeroFromNotEqualNegation", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl MembershipContradictionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("MembershipContradiction", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

