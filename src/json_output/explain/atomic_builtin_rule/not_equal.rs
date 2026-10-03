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
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotEqualFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::PeriodicTrigNonzero(_) => match lang {
                OutputLanguage::English => text("PeriodicTrigNonzero", "Nonzero periodic trigonometric value", "The exact pi coefficient and checked integer terms exclude sine/cosine zeros"),
                OutputLanguage::Chinese => text("PeriodicTrigNonzero", "周期三角值非零", "精确 pi 系数和已验证的整数项排除了正弦或余弦的零点"),
            },
            Self::NonzeroFromSignedBound(_) => text("NonzeroFromSignedBound", "Nonzero from signed bound", "A checked bound strictly separates the value from zero"),
            Self::ImaginaryUnitNonzero(_) => match lang {
                OutputLanguage::English => text("ImaginaryUnitNonzero", "i ≠ 0", "The reserved imaginary unit satisfies i² = -1 and is nonzero"),
                OutputLanguage::Chinese => text("ImaginaryUnitNonzero", "虚数单位非零", "内建虚数单位满足 i² = -1，因而不等于零"),
            },
            Self::InequalityFromDifferenceNonzero(_) => text("InequalityFromDifferenceNonzero", "Nonzero difference", "A checked nonzero difference implies unequal operands"),
            Self::InequalityFromSumNonzero(_) => text("InequalityFromSumNonzero", "Nonzero sum", "A checked nonzero sum excludes opposite operands"),
            Self::ComplexModulusNonzero(_) => text("ComplexModulusNonzero", "Nonzero complex modulus", "A nonzero complex number has nonzero modulus"),
            Self::PiNonzero(_) => text("PiNonzero", "π ≠ 0", "The real constant π is strictly positive, hence nonzero"),
            Self::ClosedDecimal(p) => p.rule_id_and_message(lang),
            Self::ClosedRational(_) => match lang {
                OutputLanguage::English => text("ClosedRationalNotEqual", "Exact rational inequality", "Exact closed fractions have different normalized values"),
                OutputLanguage::Chinese => text("ClosedRationalNotEqual", "精确分数不等", "两边的精确分数规范化后不同"),
            },
            Self::ClosedComplex(_) => match lang {
                OutputLanguage::English => text("ClosedComplexNotEqual", "Exact complex inequality", "The exact real or imaginary coordinates differ"),
                OutputLanguage::Chinese => text("ClosedComplexNotEqual", "精确复数不等", "精确实部或虚部不同"),
            },
            Self::NotEqualSymmetry(p) => p.rule_id_and_message(lang),
            Self::ListSetDifferentLength(p) => p.rule_id_and_message(lang),
            Self::FromKnownStrictOrder(p) => p.rule_id_and_message(lang),
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
            Self::NonzeroFromSignedBound(p) => Some(p.cite_fact_id),
            Self::FromKnownStrictOrder(p) => p.premise_proof.cite_fact_id(),
            Self::InequalityFromDifferenceNonzero(p) => p.premise_proof.cite_fact_id(),
            Self::InequalityFromSumNonzero(p) => p.premise_proof.cite_fact_id(),
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
        text(
            "ListSetDifferentLength",
            "List sets ≠ by length",
            "List sets of different lengths are unequal",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ListSetDifferentLength",
            "列表集因长度不等",
            "不同长度的列表集不等",
        )
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
        text(
            "FromKnownStrictOrder",
            "From known strict order",
            "Inequality follows from a known strict order fact",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownStrictOrder",
            "由已知严格序",
            "不等关系由已知严格序事实推出",
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
        text(
            "CosNonzeroOnOpenHalfPi",
            "cos ≠ 0 on (-π/2,π/2)",
            "cosine is nonzero on the open half-pi interval",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "CosNonzeroOnOpenHalfPi",
            "cos 在 (-π/2,π/2) 非零",
            "余弦在开半 π 区间上非零",
        )
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
        text(
            "CosNonzeroAtZero",
            "cos(0) ≠ 0",
            "cosine is nonzero at zero",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "CosNonzeroAtZero",
            "cos(0) ≠ 0",
            "余弦在 0 处非零",
        )
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
        text(
            "SinNonzeroOnOpenPi",
            "sin ≠ 0 on (0,π)",
            "sine is nonzero on the open pi interval",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SinNonzeroOnOpenPi",
            "sin 在 (0,π) 非零",
            "正弦在开 π 区间上非零",
        )
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
        text(
            "SinNonzeroAtHalfPi",
            "sin(π/2) ≠ 0",
            "sine is nonzero at half pi",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SinNonzeroAtHalfPi",
            "sin(π/2) ≠ 0",
            "正弦在 π/2 处非零",
        )
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
        text(
            "AbsNonzeroFromArg",
            "|x| ≠ 0 from x ≠ 0",
            "Absolute value is nonzero when the argument is nonzero",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsNonzeroFromArg",
            "由 x ≠ 0 得 |x| ≠ 0",
            "当参数非零时绝对值非零",
        )
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
        text(
            "DiffNonzeroFromInequality",
            "a-b ≠ 0 from a ≠ b",
            "A difference is nonzero when the operands are unequal",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DiffNonzeroFromInequality",
            "由 a ≠ b 得 a-b ≠ 0",
            "两边不等则差非零",
        )
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
        text(
            "EmptySetFromNonempty",
            "∅ ≠ nonempty",
            "The empty set is unequal to a nonempty set",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "EmptySetFromNonempty",
            "∅ ≠ 非空",
            "空集不等于非空集",
        )
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
        text(
            "ZeroFromNatAndOneLe",
            "0 from n∈N and 1≤n false path",
            "Zero follows from natural membership with a one-lower-bound contradiction path",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ZeroFromNatAndOneLe",
            "由 n∈N 与 1≤n 矛盾得 0",
            "由自然数成员与 1 下界矛盾路径得到零",
        )
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
        text(
            "PowNonzeroFromBase",
            "pow ≠ 0 from base",
            "A power is nonzero when the base is nonzero",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PowNonzeroFromBase",
            "由底非零得幂非零",
            "底非零则幂非零",
        )
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
        text(
            "DivNonzeroFromFactors",
            "a/b ≠ 0 from factors",
            "A quotient is nonzero when numerator and denominator are nonzero",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivNonzeroFromFactors",
            "由因子得 a/b ≠ 0",
            "分子分母都非零则商非零",
        )
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
        text(
            "ProductComponentNonzero",
            "Product ≠ 0 from component",
            "A product is nonzero when a component is nonzero under nonzero companions",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ProductComponentNonzero",
            "由分量得积 ≠ 0",
            "在同伴非零时，分量非零则积非零",
        )
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
        text(
            "SqrtNonzeroFromPositiveArg",
            "√ ≠ 0 from positive arg",
            "Square root is nonzero when the argument is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SqrtNonzeroFromPositiveArg",
            "由正参数得 √ ≠ 0",
            "当参数为正时平方根非零",
        )
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
        text(
            "SquareSumNonzeroFromComponent",
            "a²+b² ≠ 0",
            "A sum of squares is nonzero when a component is nonzero",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SquareSumNonzeroFromComponent",
            "a²+b² ≠ 0",
            "分量非零则平方和非零",
        )
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
        text(
            "AddNonzeroFromNotEqualNegation",
            "a+b ≠ 0 from a ≠ -b",
            "A sum is nonzero when the summands are not negatives",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddNonzeroFromNotEqualNegation",
            "由 a ≠ -b 得 a+b ≠ 0",
            "加数互不为相反数则和非零",
        )
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
        text(
            "MembershipContradiction",
            "Membership contradiction",
            "Conflicting membership facts yield inequality",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MembershipContradiction",
            "成员关系矛盾",
            "冲突的成员关系推出不等",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}
