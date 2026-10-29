//! The evidence enum also supplies per-variant reading rule identities.
use crate::json_output::explain::BuiltinRuleText;
use crate::prelude::*;

impl ElementaryIdentitySearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        let (name, meaning) = match self {
            Self::MinAssociative(_) => ("Associativity of minimum", "For real x,y,z, regrouping a minimum does not change its value"),
            Self::MaxAssociative(_) => ("Associativity of maximum", "For real x,y,z, regrouping a maximum does not change its value"),
            Self::MinMaxSum(_) => ("Sum of minimum and maximum", "Sorting two real numbers preserves their sum"),
            Self::MinMaxProduct(_) => ("Product of minimum and maximum", "Sorting two real numbers preserves their product"),
            Self::MinTranslation(_) => ("Translation of minimum", "Adding the same real number to both operands adds it to their minimum"),
            Self::MaxNegation(_) => ("Negation exchanges minimum and maximum", "Negation reverses real order, exchanging minimum and maximum"),
            Self::FloorCharacterization(_) => ("Characterization of floor", "The integer n with n≤x<n+1 is exactly the floor of real x"),
            Self::CeilCharacterization(_) => ("Characterization of ceiling", "The integer n with n−1<x≤n is exactly the ceiling of real x"),
            Self::GcdAddArgument(_) => ("Euclidean invariance of gcd", "For integers a,b, replacing a by a+b leaves their common divisors unchanged"),
            Self::GcdNegation(_) => ("Sign invariance of gcd", "Changing the sign of an integer does not change its common divisors with another integer"),
            Self::GcdPositiveScale(_) => ("Positive scaling of gcd", "Scaling two positive integers by a positive integer k scales their gcd by k"),
            Self::RemainderIntegerShift(_) => ("Remainder is invariant under integer multiples", "For integers a,k and nonzero integer m, adding k·m to a leaves its remainder modulo m unchanged"),
            Self::CartesianUnion(_) => ("Cartesian product distributes over union", "For sets S,T,U, membership in S×(T∪U) is equivalent to membership in (S×T)∪(S×U)"),
            Self::PowerSetIntersection(_) => ("Power set of an intersection", "A set is a subset of S∩T exactly when it is a subset of both S and T"),
        };
        BuiltinRuleText {
            rule_name: name.into(),
            message: format!("{meaning}: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        let (name, meaning) = match self {
            Self::MinAssociative(_) => (
                "最小值的结合律",
                "对实数 x、y、z，改变最小值的分组不改变结果",
            ),
            Self::MaxAssociative(_) => (
                "最大值的结合律",
                "对实数 x、y、z，改变最大值的分组不改变结果",
            ),
            Self::MinMaxSum(_) => ("最小值与最大值之和", "对两个实数排序不改变它们的和"),
            Self::MinMaxProduct(_) => ("最小值与最大值之积", "对两个实数排序不改变它们的积"),
            Self::MinTranslation(_) => (
                "最小值的平移",
                "给两个实数同时加上同一个数，最小值增加相同的量",
            ),
            Self::MaxNegation(_) => (
                "取相反数交换最小值与最大值",
                "取相反数反转实数的顺序，从而交换最小值与最大值",
            ),
            Self::FloorCharacterization(_) => (
                "向下取整的刻画",
                "实数 x 满足 n≤x<n+1 时，整数 n 恰为 x 的向下取整",
            ),
            Self::CeilCharacterization(_) => (
                "向上取整的刻画",
                "实数 x 满足 n−1<x≤n 时，整数 n 恰为 x 的向上取整",
            ),
            Self::GcdAddArgument(_) => (
                "最大公约数的加法不变性",
                "对整数 a、b，将 a 替换为 a+b 不改变它们的公约数",
            ),
            Self::GcdNegation(_) => (
                "最大公约数的符号不变性",
                "将一个整数变为相反数，不改变它与另一个整数的公约数",
            ),
            Self::GcdPositiveScale(_) => (
                "最大公约数的正整数缩放",
                "将两个正整数同时乘以正整数 k，最大公约数也乘以 k",
            ),
            Self::RemainderIntegerShift(_) => (
                "加上模数的整数倍不改变余数",
                "对整数 a、k 与非零整数 m，给 a 加上 k·m 不改变其模 m 的余数",
            ),
            Self::CartesianUnion(_) => (
                "笛卡尔积对并集的分配律",
                "对集合 S、T、U，S×(T∪U) 与 (S×T)∪(S×U) 具有相同元素",
            ),
            Self::PowerSetIntersection(_) => (
                "交集的幂集",
                "一个集合是 S∩T 的子集，当且仅当它同时为 S 与 T 的子集",
            ),
        };
        BuiltinRuleText {
            rule_name: name.into(),
            message: format!("{meaning}: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!("兩邊及定義域條件均已檢查: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!(
                "Les deux membres et leurs domaines sont vérifiés: {}",
                self.law()
            ),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!(
                "Обе части и условия области определения проверены: {}",
                self.law()
            ),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!(
                "Ambos miembros y sus dominios están verificados: {}",
                self.law()
            ),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!("تم التحقق من الطرفين وشروط المجال: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!("両辺と定義域の条件を確認済み: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!("양변과 정의역 조건을 확인했습니다: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!(
                "Hai vế và điều kiện miền xác định đã được kiểm tra: {}",
                self.law()
            ),
        }
    }

    pub fn rule_name_and_message(&self, language: OutputLanguage) -> BuiltinRuleText {
        match language {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}
