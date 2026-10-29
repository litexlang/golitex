//! Mathematical comments owned by the typed disjunction/existence rules.
use super::text::text;
use super::BuiltinRuleText;
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinClosedIntegerRangeEqualityCover;
use crate::execute::execute_fact_stmt::verify_or_fact::OrFactSearchProofByBuiltinRule;
use crate::launch_command::OutputLanguage;
impl OrBuiltinClosedIntegerRangeEqualityCover {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Exhaust a closed integer interval", "A member of a finite closed integer interval equals one of its integers: x ∈ {m,…,n} ⇒ x=m ∨ … ∨ x=n.")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "整数闭区间的穷尽分类",
            "有限整数闭区间中的元素必等于其中某个整数：x ∈ {m,…,n} ⇒ x=m ∨ … ∨ x=n。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinHalfOpenIntegerRangeEqualityCover;
impl OrBuiltinHalfOpenIntegerRangeEqualityCover {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Exhaust a half-open integer interval", "A member of {m,…,n−1} equals one of the listed integers; the upper endpoint n is excluded.")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "整数半开区间的穷尽分类",
            "{m,…,n−1} 中的元素必等于所列的某个整数；上端点 n 不属于该区间。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinRealLineTrichotomyEqLessGreater;
impl OrBuiltinRealLineTrichotomyEqLessGreater {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Real trichotomy",
            "For real a and b, exactly one of a = b, a < b and a > b holds.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "实数的三歧性",
            "对任意实数 a、b，a = b、a < b、a > b 中恰有一个成立。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinRealLineTrichotomyLessEqGreater;
impl OrBuiltinRealLineTrichotomyLessEqGreater {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Real trichotomy",
            "For real a and b, exactly one of a < b, a = b and a > b holds.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "实数的三歧性",
            "对任意实数 a、b，a < b、a = b、a > b 中恰有一个成立。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinRealLineTrichotomyGreaterEqLess;
impl OrBuiltinRealLineTrichotomyGreaterEqLess {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Real trichotomy",
            "For real a and b, exactly one of a > b, a = b and a < b holds.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "实数的三歧性",
            "对任意实数 a、b，a > b、a = b、a < b 中恰有一个成立。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinNaturalZeroOrAtLeastOne;
impl OrBuiltinNaturalZeroOrAtLeastOne {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Natural number dichotomy",
            "A natural number is either zero or at least one: n ∈ ℕ ⇒ n = 0 ∨ n ≥ 1.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "自然数的零与正数分类",
            "自然数不是零就是至少为一：n ∈ ℕ ⇒ n = 0 ∨ n ≥ 1。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinComplementaryAtomic;
impl OrBuiltinComplementaryAtomic {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Excluded middle", "For an atomic proposition P, P ∨ ¬P holds; this does not select which alternative holds.")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "排中律",
            "对原子命题 P，P ∨ ¬P 成立；该结论不指定哪一个分支成立。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinAbsSignSplit;
impl OrBuiltinAbsSignSplit {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Absolute value by sign",
            "For real x, |x| = x or |x| = −x, according to its sign.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "绝对值的符号分类",
            "对实数 x，|x| = x 或 |x| = −x，具体取决于 x 的符号。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinZeroProductSplit;
impl OrBuiltinZeroProductSplit {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Zero product", "For real a and b, a·b = 0 ⇒ a = 0 ∨ b = 0.")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("零乘积性质", "对实数 a、b，a·b = 0 ⇒ a = 0 ∨ b = 0。")
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinLessOrGreaterEqual;
impl OrBuiltinLessOrGreaterEqual {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Complementary real orders",
            "For real a and b, a < b ∨ a ≥ b.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实数序的互补关系", "对实数 a、b，a < b ∨ a ≥ b。")
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinGreaterOrLessEqual;
impl OrBuiltinGreaterOrLessEqual {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Complementary real orders",
            "For real a and b, a > b ∨ a ≤ b.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实数序的互补关系", "对实数 a、b，a > b ∨ a ≤ b。")
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinWeakOrderLeOrGe;
impl OrBuiltinWeakOrderLeOrGe {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Total real order",
            "Any two real numbers are comparable: a ≤ b ∨ a ≥ b.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实数序的完全性", "任意两个实数都可比较：a ≤ b ∨ a ≥ b。")
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinEqualityPlusStrictCoversWeak;
impl OrBuiltinEqualityPlusStrictCoversWeak {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Split a weak inequality",
            "For reals, a ≤ b ⇒ a = b ∨ a < b; dually, a ≥ b ⇒ a = b ∨ a > b.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "非严格不等式的分类",
            "对实数，a ≤ b ⇒ a = b ∨ a < b；对偶地，a ≥ b ⇒ a = b ∨ a > b。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinCompleteResidues;
impl OrBuiltinCompleteResidues {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Complete residue classes", "For integer n and positive integer m, the Euclidean remainder n mod m is one of 0, …, m−1. For example, n mod 2 = 0 ∨ n mod 2 = 1.")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("完整余数分类", "对整数 n 和正整数 m，欧几里得余数 n mod m 取 0,…,m−1 中的一个值。例如 n mod 2 = 0 ∨ n mod 2 = 1。")
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinIntegerSuccessorTail;
impl OrBuiltinIntegerSuccessorTail {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Integer interval and tail", "An integer with a known lower bound is either one of the listed consecutive integers or greater than the last one. For example, x ≥ 1 ⇒ x = 1 ∨ x = 2 ∨ x > 2.")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("整数的有限分类与尾部", "具有已知下界的整数，或等于依次列出的某个整数，或大于最后一个。例如 x ≥ 1 ⇒ x = 1 ∨ x = 2 ∨ x > 2。")
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinSquareSumComponentNonzero;
impl OrBuiltinSquareSumComponentNonzero {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "A nonzero component",
            "For real a and b, a²+b² ≠ 0 ⇒ a ≠ 0 ∨ b ≠ 0.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "平方和的非零分量",
            "对实数 a、b，a²+b² ≠ 0 ⇒ a ≠ 0 ∨ b ≠ 0。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinClassicalImplication;
impl OrBuiltinClassicalImplication {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Implication as a disjunction", "To establish ¬A ∨ B, assume A and derive B. This uses the classical equivalence (A ⇒ B) ⇔ (¬A ∨ B).")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "蕴含的析取形式",
            "证明 ¬A ∨ B 时，在假设 A 下推出 B；这里使用经典逻辑等价式 (A ⇒ B) ⇔ (¬A ∨ B)。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinIntegerDiscreteSplit;
impl OrBuiltinIntegerDiscreteSplit {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Discreteness of integers",
            "There is no integer strictly between consecutive integers: x,n ∈ ℤ ⇒ x ≤ n ∨ x ≥ n+1.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "整数序的离散性",
            "相邻整数之间没有整数：x,n ∈ ℤ ⇒ x ≤ n ∨ x ≥ n+1。",
        )
    }
}
impl OrFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedIntegerRangeEqualityCover(proof) => proof.rule_name_and_message_en(),
            Self::HalfOpenIntegerRangeEqualityCover(proof) => proof.rule_name_and_message_en(),
            Self::RealLineTrichotomyEqLessGreater(proof) => proof.rule_name_and_message_en(),
            Self::RealLineTrichotomyLessEqGreater(proof) => proof.rule_name_and_message_en(),
            Self::RealLineTrichotomyGreaterEqLess(proof) => proof.rule_name_and_message_en(),
            Self::NaturalZeroOrAtLeastOne(proof) => proof.rule_name_and_message_en(),
            Self::ComplementaryAtomic(proof) => proof.rule_name_and_message_en(),
            Self::AbsSignSplit(proof) => proof.rule_name_and_message_en(),
            Self::ZeroProductSplit(proof) => proof.rule_name_and_message_en(),
            Self::LessOrGreaterEqual(proof) => proof.rule_name_and_message_en(),
            Self::GreaterOrLessEqual(proof) => proof.rule_name_and_message_en(),
            Self::WeakOrderLeOrGe(proof) => proof.rule_name_and_message_en(),
            Self::EqualityPlusStrictCoversWeak(proof) => proof.rule_name_and_message_en(),
            Self::CompleteResidues(proof) => proof.rule_name_and_message_en(),
            Self::IntegerSuccessorTail(proof) => proof.rule_name_and_message_en(),
            Self::SquareSumComponentNonzero(proof) => proof.rule_name_and_message_en(),
            Self::ClassicalImplication(proof) => proof.rule_name_and_message_en(),
            Self::IntegerDiscreteSplit(proof) => proof.rule_name_and_message_en(),
        }
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedIntegerRangeEqualityCover(proof) => proof.rule_name_and_message_zh(),
            Self::HalfOpenIntegerRangeEqualityCover(proof) => proof.rule_name_and_message_zh(),
            Self::RealLineTrichotomyEqLessGreater(proof) => proof.rule_name_and_message_zh(),
            Self::RealLineTrichotomyLessEqGreater(proof) => proof.rule_name_and_message_zh(),
            Self::RealLineTrichotomyGreaterEqLess(proof) => proof.rule_name_and_message_zh(),
            Self::NaturalZeroOrAtLeastOne(proof) => proof.rule_name_and_message_zh(),
            Self::ComplementaryAtomic(proof) => proof.rule_name_and_message_zh(),
            Self::AbsSignSplit(proof) => proof.rule_name_and_message_zh(),
            Self::ZeroProductSplit(proof) => proof.rule_name_and_message_zh(),
            Self::LessOrGreaterEqual(proof) => proof.rule_name_and_message_zh(),
            Self::GreaterOrLessEqual(proof) => proof.rule_name_and_message_zh(),
            Self::WeakOrderLeOrGe(proof) => proof.rule_name_and_message_zh(),
            Self::EqualityPlusStrictCoversWeak(proof) => proof.rule_name_and_message_zh(),
            Self::CompleteResidues(proof) => proof.rule_name_and_message_zh(),
            Self::IntegerSuccessorTail(proof) => proof.rule_name_and_message_zh(),
            Self::SquareSumComponentNonzero(proof) => proof.rule_name_and_message_zh(),
            Self::ClassicalImplication(proof) => proof.rule_name_and_message_zh(),
            Self::IntegerDiscreteSplit(proof) => proof.rule_name_and_message_zh(),
        }
    }
    pub fn rule_name_and_message(&self, language: OutputLanguage) -> BuiltinRuleText {
        match language {
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            _ => self.rule_name_and_message_en(),
        }
    }
}
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedBuiltinBijectivePreimage;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchProofByBuiltinRule;
impl ExistShapedBuiltinBijectivePreimage {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Unique preimage under a bijection",
            "If f: A → B is bijective, each y ∈ B has exactly one x ∈ A with f(x)=y.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "双射的唯一原像",
            "若 f: A → B 为双射，则每个 y ∈ B 都有唯一的 x ∈ A 满足 f(x)=y。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedBuiltinRealLineComparisonWitness;
impl ExistShapedBuiltinRealLineComparisonWitness {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Witnesses on the real line", "For a given real c, real numbers equal to, distinct from, above or below c exist. For example, c+1 is a witness for ∃x ∈ ℝ: x>c.")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实数序中的见证", "对给定实数 c，存在与 c 相等、不等、大于或小于 c 的实数。例如 c+1 是 ∃x ∈ ℝ: x>c 的见证。")
    }
}
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedBuiltinEqualityWitnessFromMembership;
impl ExistShapedBuiltinEqualityWitnessFromMembership {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Use a known member as witness",
            "If a ∈ S, choosing x=a proves ∃x ∈ S: x=a.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("用已知元素作见证", "若 a ∈ S，取 x=a 即证明 ∃x ∈ S: x=a。")
    }
}
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedBuiltinNonemptySetMemberWitness;
impl ExistShapedBuiltinNonemptySetMemberWitness {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "An element of a nonempty set",
            "A nonempty set S has an element: ∃x ∈ S.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("非空集合中的元素", "非空集合 S 中存在元素：∃x ∈ S。")
    }
}
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedBuiltinRationalPositiveDenominator;
impl ExistShapedBuiltinRationalPositiveDenominator {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Rational representation with positive denominator", "Every rational q has a representation q=a/b with a,b ∈ ℤ and b>0. This rule does not assert that the fraction is reduced.")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有理数的正分母表示",
            "任意有理数 q 可写为 q=a/b，其中 a,b ∈ ℤ 且 b>0；此规则不要求该分数既约。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedBuiltinRationalIntegerRatio;
impl ExistShapedBuiltinRationalIntegerRatio {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Rational representation as an integer ratio",
            "Every rational q has a representation q=a/b with a ∈ ℤ and b ∈ ℤ∖{0}.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有理数的整数比表示",
            "任意有理数 q 可写为 q=a/b，其中 a ∈ ℤ，b ∈ ℤ∖{0}。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedBuiltinIntegerMultipleFromZeroRemainder;
impl ExistShapedBuiltinIntegerMultipleFromZeroRemainder {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "A zero remainder gives an integer multiple",
            "For a,b ∈ ℤ with b≠0, a mod b=0 implies ∃k ∈ ℤ: a=b·k. For example, 6=3·2.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "零余数给出整数倍",
            "对 a,b ∈ ℤ 且 b≠0，a mod b=0 推出 ∃k ∈ ℤ: a=b·k。例如 6=3·2。",
        )
    }
}
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedBuiltinArchimedeanReciprocal;
impl ExistShapedBuiltinArchimedeanReciprocal {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Archimedean reciprocal bound",
            "For each ε>0 there exists n ∈ ℕ+ such that 1/n<ε.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("阿基米德倒数界", "对每个 ε>0，存在 n ∈ ℕ+ 使得 1/n<ε。")
    }
}
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedBuiltinRealDensityMidpoint;
impl ExistShapedBuiltinRealDensityMidpoint {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Density by a midpoint",
            "For real a<b, the midpoint r=(a+b)/2 satisfies a<r<b.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "中点给出的稠密性",
            "对实数 a<b，中点 r=(a+b)/2 满足 a<r<b。",
        )
    }
}
impl ExistShapedFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::BijectivePreimage(proof) => proof.rule_name_and_message_en(),
            Self::RealLineComparisonWitness(proof) => proof.rule_name_and_message_en(),
            Self::EqualityWitnessFromMembership(proof) => proof.rule_name_and_message_en(),
            Self::NonemptySetMemberWitness(proof) => proof.rule_name_and_message_en(),
            Self::RationalPositiveDenominator(proof) => proof.rule_name_and_message_en(),
            Self::RationalIntegerRatio(proof) => proof.rule_name_and_message_en(),
            Self::IntegerMultipleFromZeroRemainder(proof) => proof.rule_name_and_message_en(),
            Self::ArchimedeanReciprocal(proof) => proof.rule_name_and_message_en(),
            Self::RealDensityMidpoint(proof) => proof.rule_name_and_message_en(),
        }
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::BijectivePreimage(proof) => proof.rule_name_and_message_zh(),
            Self::RealLineComparisonWitness(proof) => proof.rule_name_and_message_zh(),
            Self::EqualityWitnessFromMembership(proof) => proof.rule_name_and_message_zh(),
            Self::NonemptySetMemberWitness(proof) => proof.rule_name_and_message_zh(),
            Self::RationalPositiveDenominator(proof) => proof.rule_name_and_message_zh(),
            Self::RationalIntegerRatio(proof) => proof.rule_name_and_message_zh(),
            Self::IntegerMultipleFromZeroRemainder(proof) => proof.rule_name_and_message_zh(),
            Self::ArchimedeanReciprocal(proof) => proof.rule_name_and_message_zh(),
            Self::RealDensityMidpoint(proof) => proof.rule_name_and_message_zh(),
        }
    }
    pub fn rule_name_and_message(&self, language: OutputLanguage) -> BuiltinRuleText {
        match language {
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            _ => self.rule_name_and_message_en(),
        }
    }
}
