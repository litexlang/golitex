//! Leaf explain for atomic family group `in_fact`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::{
    AddInNaturalBuiltinRuleProof,
    CartMembershipBuiltinRuleProof,
    ClosedNumericMembershipBuiltinRuleProof,
    ComplexArithmeticClosureBuiltinRuleProof,
    ComplexCoordinateInComplexBuiltinRuleProof,
    ComplexCoordinateInRealBuiltinRuleProof,
    FamilyUnionMembershipFromMemberBuiltinRuleProof,
    FiniteSetSubsetMembershipBuiltinRuleProof,
    AnonymousFnApplicationInFnRangeBuiltinRuleProof,
    InFactSearchProofByBuiltinRule,
    IndexUnionMembershipFromIndexBuiltinRuleProof,
    IntersectMembershipBuiltinRuleProof,
    IntervalMembershipBuiltinRuleProof,
    ListSetElementMembershipBuiltinRuleProof,
    MulInNaturalBuiltinRuleProof,
    NativeConstantMembershipBuiltinRuleProof,
    NativeScalarCodomainBuiltinRuleProof,
    PositiveIntegerInNPosBuiltinRuleProof,
    CartDimInNaturalBuiltinRuleProof,
    TupleDimInNaturalBuiltinRuleProof,
    AnonymousFnInDeclaredFnSetBuiltinRuleProof,
    OneSideInfinityIntervalMembershipBuiltinRuleProof,
    PowerSetMembershipBuiltinRuleProof,
    PredecessorInNaturalBuiltinRuleProof,
    PredecessorFromPositiveNaturalBuiltinRuleProof,
    PredecessorFromNaturalAboveZeroBuiltinRuleProof,
    RealArithmeticClosureBuiltinRuleProof,
    RealTrigClosureBuiltinRuleProof,
    RealTrigInComplexBuiltinRuleProof,
    SetBuilderMembershipBuiltinRuleProof,
    SetMinusMembershipBuiltinRuleProof,
    StandardSetSubsetMembershipBuiltinRuleProof,
    StructObjMembershipBuiltinRuleProof,
    UnionMembershipFromLeftBuiltinRuleProof,
    UnionMembershipFromRightBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl InFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericMembership(p) => p.rule_id_and_message(lang),
            Self::ComplexArithmeticClosure(p) => p.rule_id_and_message(lang),
            Self::RealTrigClosure(p) => p.rule_id_and_message(lang),
            Self::RealTrigInComplex(p) => p.rule_id_and_message(lang),
            Self::ComplexCoordinateInReal(p) => p.rule_id_and_message(lang),
            Self::ComplexCoordinateInComplex(p) => p.rule_id_and_message(lang),
            Self::RealArithmeticClosure(p) => p.rule_id_and_message(lang),
            Self::RealOperandArithmeticClosure(_) => match lang {
                OutputLanguage::English => text("RealOperandArithmeticClosure", "Real arithmetic from checked operands", "Checked real operands remain real under field arithmetic; division also has its checked WD domain"),
                OutputLanguage::Chinese => text("RealOperandArithmeticClosure", "由实数操作数得实数运算结果", "已验证的实数操作数经四则运算仍为实数；除法另有已验证的定义域条件"),
            },
            Self::RealIntegerPower(_) => match lang {
                OutputLanguage::English => text("RealIntegerPower", "Real integer power", "The base is checked real and the enclosing power WD certificate establishes an integer exponent and required nonzero domain"),
                OutputLanguage::Chinese => text("RealIntegerPower", "实数的整数幂", "底数已验证为实数；幂的定义良好证据验证整数指数及所需非零条件"),
            },
            Self::ClosedExactScalarMembership(_) => match lang {
                OutputLanguage::English => text("ClosedExactScalarMembership", "Exact scalar membership", "Exact real and imaginary coordinates satisfy the target scalar carrier"),
                OutputLanguage::Chinese => text("ClosedExactScalarMembership", "精确数值载体", "精确的实部和虚部满足目标数值集合的条件"),
            },
            Self::IntegerArithmeticClosure(_) => match lang {
                OutputLanguage::English => text("IntegerArithmeticClosure", "Integer arithmetic closure", "Checked integer operands remain integers under negation, absolute value, addition, subtraction, multiplication and natural powers"),
                OutputLanguage::Chinese => text("IntegerArithmeticClosure", "整数运算封闭", "已验证的整数操作数经取负、绝对值、加减乘及自然数幂仍为整数"),
            },
            Self::NativeScalarCodomain(p) => p.rule_id_and_message(lang),
            Self::PositiveIntegerInNPos(p) => p.rule_id_and_message(lang),
            Self::FoldScalarCodomain(_) => match lang {
                OutputLanguage::English => text("FoldScalarCodomain", "Fold carrier", "The checked homogeneous operation and seed preserve the fold carrier"),
                OutputLanguage::Chinese => text("FoldScalarCodomain", "Fold 的载体", "已验证的齐次运算与初值保持 fold 的载体"),
            },
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = match lang {
                    OutputLanguage::English => ("Finite aggregate scalar carrier", "Checked summands or factors close the declared scalar carrier; empty sums include zero"),
                    OutputLanguage::Chinese => ("有限聚合的数值载体", "合法求和项或因子在声明的数值载体内封闭；空求和须包含零"),
                };
                BuiltinRuleText { rule_id: "AggregateScalarCodomain", rule_name:name.into(), message:message.into() }
            },
            Self::CartDimInNatural(p) => p.rule_id_and_message(lang),
            Self::TupleDimInNatural(p) => p.rule_id_and_message(lang),
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_id_and_message(lang),
            Self::AnonymousFnApplicationScalarCodomain(_) => match lang {
                OutputLanguage::English => text("AnonymousFnApplicationScalarCodomain", "Anonymous function return carrier", "A checked direct application inhabits its declared static scalar codomain"),
                OutputLanguage::Chinese => text("AnonymousFnApplicationScalarCodomain", "匿名函数的返回载体", "已验证的直接调用属于其声明的静态数值返回载体"),
            },
            Self::StandardSetSubsetMembership(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSubsetMembership(p) => p.rule_id_and_message(lang),
            Self::SetBuilderMembership(p) => p.rule_id_and_message(lang),
            Self::NativeConstantMembership(p) => p.rule_id_and_message(lang),
            Self::ListSetElementMembership(p) => p.rule_id_and_message(lang),
            Self::CartMembership(p) => p.rule_id_and_message(lang),
            Self::PowerSetMembership(p) => p.rule_id_and_message(lang),
            Self::StructObjMembership(p) => p.rule_id_and_message(lang),
            Self::PredecessorInNatural(p) => p.rule_id_and_message(lang),
            Self::PredecessorFromPositiveNatural(p) => p.rule_id_and_message(lang),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_id_and_message(lang),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_id_and_message(lang),
            Self::UnionMembershipFromLeft(p) => p.rule_id_and_message(lang),
            Self::UnionMembershipFromRight(p) => p.rule_id_and_message(lang),
            Self::IntersectMembership(p) => p.rule_id_and_message(lang),
            Self::SetMinusMembership(p) => p.rule_id_and_message(lang),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_id_and_message(lang),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_id_and_message(lang),
            Self::IntervalMembership(p) => p.rule_id_and_message(lang),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_id_and_message(lang),
            Self::AddInNatural(p) => p.rule_id_and_message(lang),
            Self::MulInNatural(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::ClosedNumericMembership(_) => None,
            Self::ComplexArithmeticClosure(_) => None,
            Self::RealTrigClosure(_) => None,
            Self::RealTrigInComplex(_) => None,
            Self::ComplexCoordinateInReal(_) => None,
            Self::ComplexCoordinateInComplex(_) => None,
            Self::RealArithmeticClosure(_) => None,
            Self::RealOperandArithmeticClosure(_) => None,
            Self::RealIntegerPower(_) => None,
            Self::ClosedExactScalarMembership(_) => None,
            Self::IntegerArithmeticClosure(_) => None,
            Self::NativeScalarCodomain(_) => None,
            Self::PositiveIntegerInNPos(_) => None,
            Self::AggregateScalarCodomain(_) => None,
            Self::FoldScalarCodomain(_) => None,
            Self::CartDimInNatural(_) => None,
            Self::TupleDimInNatural(_) => None,
            Self::AnonymousFnInDeclaredFnSet(_) => None,
            Self::AnonymousFnApplicationScalarCodomain(_) => None,
            Self::StandardSetSubsetMembership(_) => None,
            Self::FiniteSetSubsetMembership(_) => None,
            Self::SetBuilderMembership(_) => None,
            Self::NativeConstantMembership(_) => None,
            Self::ListSetElementMembership(_) => None,
            Self::CartMembership(_) => None,
            Self::PowerSetMembership(_) => None,
            Self::StructObjMembership(_) => None,
            Self::PredecessorInNatural(p) => p.in_natural_proof.cite_fact_id(),
            Self::PredecessorFromPositiveNatural(p) => p.in_natural_proof.cite_fact_id(),
            Self::PredecessorFromNaturalAboveZero(p) => p.in_natural_proof.cite_fact_id(),
            Self::AnonymousFnApplicationInFnRange(_) => None,
            Self::UnionMembershipFromLeft(_) => None,
            Self::UnionMembershipFromRight(_) => None,
            Self::IntersectMembership(_) => None,
            Self::SetMinusMembership(_) => None,
            Self::FamilyUnionMembershipFromMember(p) => Some(p.cite_member_set_in_family_fact_id),
            Self::IndexUnionMembershipFromIndex(p) => Some(p.cite_index_in_index_set_fact_id),
            Self::IntervalMembership(_) => None,
            Self::OneSideInfinityIntervalMembership(_) => None,
            Self::AddInNatural(_) => None,
            Self::MulInNatural(_) => None,
        }
    }
}

impl ClosedNumericMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericMembership",
            "Closed Numeric Membership",
            "a closed expression that evaluates to a normalized",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericMembership",
            "封闭数值成员",
            "封闭表达式算出的值属于目标集合",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ComplexArithmeticClosureBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ComplexArithmeticClosure",
            "Complex Arithmetic Closure",
            "after child WD, `+ - * / …` over C-carriers stay in C",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ComplexArithmeticClosure",
            "复数运算封闭",
            "良定的复数运算结果属于复数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl RealTrigClosureBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "RealTrigClosure",
            "Real Trig Closure",
            "after child WD, `sin`/`cos`/`tan`/`cot` and their",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "RealTrigClosure",
            "实三角运算封闭",
            "良定的实三角运算结果属于实数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl RealTrigInComplexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "RealTrigInComplex",
            "Real Trig In Complex",
            "sin/cos/... : R → R ⊂ C",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "RealTrigInComplex",
            "实三角值属于复数",
            "实三角值经 R⊂C 属于复数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ComplexCoordinateInRealBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ComplexCoordinateInReal",
            "Complex Coordinate In Real",
            "`C_abs(z)`, `re(z)`, `img(z)` are real after WD",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ComplexCoordinateInReal",
            "复坐标属于实数",
            "模与实部虚部属于实数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ComplexCoordinateInComplexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ComplexCoordinateInComplex",
            "Complex Coordinate In Complex",
            "Complex modulus / coordinates also inhabit C via R ⊂ C",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ComplexCoordinateInComplex",
            "复坐标属于复数",
            "模与实部虚部属于复数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl RealArithmeticClosureBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "RealArithmeticClosure",
            "Real Arithmetic Closure",
            "after domain WD, abs, sqrt, log and ln have real-valued results",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "RealArithmeticClosure",
            "实数运算封闭",
            "良定的实数运算结果属于实数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl StandardSetSubsetMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StandardSetSubsetMembership",
            "Standard Set Subset Membership",
            "if `x $in S` and `S $subset T` among standard sets,",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "StandardSetSubsetMembership",
            "标准集链上传成员",
            "沿标准集包含链提升成员关系",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSetSubsetMembershipBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FiniteSetSubsetMembership",
                "Finite Set Subset Membership",
                "the element belongs to a finite set whose every member belongs to the target carrier",
            ),
            OutputLanguage::Chinese => text(
                "FiniteSetSubsetMembership",
                "有限集成员类型提升",
                "元素属于有限集，且每个列出的成员都属于目标集合",
            ),
        }
    }
}

impl SetBuilderMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetBuilderMembership",
            "Set Builder Membership",
            "Set-builder membership from base membership plus defining facts",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetBuilderMembership",
            "集合构造成员",
            "由底集成员与定义事实得集合构造成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NativeConstantMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NativeConstantMembership",
            "Native Constant Membership",
            "Native mathematical constants inhabit fixed carriers",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NativeConstantMembership",
            "内置常数成员",
            "内置数学常数属于固定载体",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ListSetElementMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ListSetElementMembership",
            "List Set Element Membership",
            "if `x = a_i` for some `a_i` in `{a_1, …, a_n}`,",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ListSetElementMembership",
            "列表集元素成员",
            "等于某一列出元素则属于列表集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl CartMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CartMembership",
            "Cart Membership",
            "`e $in cart(A1,…,An)` (n≥2) from coordinate",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "CartMembership",
            "笛卡尔积成员",
            "各分量成员推出笛卡尔积成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl PowerSetMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PowerSetMembership",
            "Power Set Membership",
            "if `A $subset B`, then `A $in power_set(B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PowerSetMembership",
            "幂集成员",
            "子集关系推出幂集成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl StructObjMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StructObjMembership",
            "Struct Obj Membership",
            "`e` inhabits `&Struct` when it meets the field",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "StructObjMembership",
            "结构对象成员",
            "结构载体与等价律推出结构集成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl PredecessorFromNaturalAboveZeroBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("PredecessorFromNaturalAboveZero", "Natural above zero has a predecessor", "`x $in N` and `0 < x` imply `x - 1 $in N`"),
            OutputLanguage::Chinese => text("PredecessorFromNaturalAboveZero", "零小于自然数时的前驱", "已知自然数 x 且 0 < x，其前驱仍属于自然数"),
        }
    }
}

impl PredecessorFromPositiveNaturalBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "PredecessorFromPositiveNatural",
                "Predecessor of a positive natural",
                "`x $in N` and `x > 0` imply `x - 1 $in N`",
            ),
            OutputLanguage::Chinese => text(
                "PredecessorFromPositiveNatural",
                "正自然数的前驱",
                "已知自然数严格大于零，其前驱仍属于自然数",
            ),
        }
    }
}

impl PredecessorInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PredecessorInNatural",
            "Predecessor In Natural",
            "`x $in N` and `x >= 1` ⇒ `x - 1 $in N`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PredecessorInNatural",
            "前驱属于自然数",
            "自然数且至少为 1 则前驱仍是自然数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AnonymousFnApplicationInFnRangeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AnonymousFnApplicationInFnRange",
            "Anonymous function application in range",
            "A well-defined application of an anonymous function belongs to its range",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AnonymousFnApplicationInFnRange",
            "匿名函数应用落在值域",
            "良定的匿名函数应用落在该函数值域",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl UnionMembershipFromLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnionMembershipFromLeft",
            "Union Membership From Left",
            "`x $in A` ⇒ `x $in union(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnionMembershipFromLeft",
            "由左因子得并成员",
            "属于左因子则属于并",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl UnionMembershipFromRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnionMembershipFromRight",
            "Union Membership From Right",
            "`x $in B` ⇒ `x $in union(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnionMembershipFromRight",
            "由右因子得并成员",
            "属于右因子则属于并",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl IntersectMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectMembership",
            "Intersect Membership",
            "`x $in A` and `x $in B` ⇒ `x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntersectMembership",
            "交成员",
            "同时属于两边则属于交",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SetMinusMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetMinusMembership",
            "Set Minus Membership",
            "`x $in A` and `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetMinusMembership",
            "差集成员",
            "属于左且不属于右则属于差集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FamilyUnionMembershipFromMemberBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FamilyUnionMembershipFromMember",
            "Family Union Membership From Member",
            "`A $in F` and `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FamilyUnionMembershipFromMember",
            "由成员集得族并成员",
            "属于族中某集则属于族并",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl IndexUnionMembershipFromIndexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IndexUnionMembershipFromIndex",
            "Index Union Membership From Index",
            "`i $in I` and `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IndexUnionMembershipFromIndex",
            "由指标得指标并成员",
            "属于某指标纤维则属于指标并",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl IntervalMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntervalMembership",
            "Interval Membership",
            "`x $in R` plus the matching open/closed endpoint inequalities",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntervalMembership",
            "区间成员",
            "由载体与端点界推出区间成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl OneSideInfinityIntervalMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OneSideInfinityIntervalMembership",
            "One Side Infinity Interval Membership",
            "One-sided real ray membership from carrier and the finite endpoint bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OneSideInfinityIntervalMembership",
            "单侧无穷区间成员",
            "由载体与有限端点界推出射线成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AddInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddInNatural",
            "Add In Natural",
            "Natural addition closure: `a $in N` and `b $in N` ⇒ `a + b $in N`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddInNatural",
            "自然数加法封闭",
            "自然数加法封闭",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl MulInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulInNatural",
            "Mul In Natural",
            "Natural multiplication closure: `a $in N` and `b $in N` ⇒ `a * b $in N`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulInNatural",
            "自然数乘法封闭",
            "自然数乘法封闭",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NativeScalarCodomainBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "Native Scalar Codomain".to_string(),
            message: format!(
                "after input-domain WD, the native result belongs to {} and its standard-set supertypes",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "原生标量返回类型".to_string(),
            message: format!(
                "参数定义域已通过良定检查，原生运算结果属于 {} 及其标准集合超集",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl CartDimInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("CartDimInNatural", "Cartesian Dimension in N", "a well-defined Cartesian dimension belongs to N and its numeric supertypes"),
            OutputLanguage::Chinese => text("CartDimInNatural", "笛卡尔维数属于自然数", "已通过良定检查的笛卡尔维数属于 N 及其数值超集"),
        }
    }
}

impl TupleDimInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("TupleDimInNatural", "Tuple Dimension in N", "a well-defined tuple dimension belongs to N and its numeric supertypes"),
            OutputLanguage::Chinese => text("TupleDimInNatural", "元组维数属于自然数", "已通过良定检查的元组维数属于 N 及其数值超集"),
        }
    }
}

impl AnonymousFnInDeclaredFnSetBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("AnonymousFnInDeclaredFnSet", "Anonymous function in declared function set", "the checked function's signature matches the target modulo bound-name renaming"),
            OutputLanguage::Chinese => text("AnonymousFnInDeclaredFnSet", "匿名函数属于声明的函数集", "函数已通过良定检查，目标签名仅在绑定参数名称上不同"),
        }
    }
}

impl PositiveIntegerInNPosBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let (name, message) = match lang {
            OutputLanguage::English => ("Positive integer membership", "An integer strictly greater than zero belongs to N+"),
            OutputLanguage::Chinese => ("正整数成员", "整数且严格大于零的对象属于 N+"),
        };
        BuiltinRuleText { rule_id: "PositiveIntegerInNPos", rule_name: name.into(), message: message.into() }
    }
}
