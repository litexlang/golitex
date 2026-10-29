//! Mathematical closure comments for the shared membership certificates.
use super::text::text;
use super::BuiltinRuleText;
use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::StructuralMembershipReason;
impl StructuralMembershipReason {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
        Self::Known(_) => text("Known membership", "Reuse the recorded membership fact."),
        Self::Closed(_) => text("Membership by exact calculation", "The evaluated numeric value belongs to the stated number set."),
        Self::KnownSubset(_) => text("Membership through a subset", "From x ∈ A and A ⊆ B, infer x ∈ B."),
        Self::StandardSuperset(_) => text("Inclusion of number sets", "Use the inclusions ℕ ⊆ ℤ ⊆ ℚ ⊆ ℝ ⊆ ℂ to regard an element as belonging to a larger number set."),
        Self::Add{ .. } => text("Closure under addition", "Each of ℕ, ℤ, ℚ, ℝ and ℂ is closed under addition: two operands in the same number set have their sum in that set."),
        Self::Sub{ .. } => text("Closure under subtraction", "Each of ℤ, ℚ, ℝ and ℂ is closed under subtraction. Natural numbers are not generally closed under subtraction."),
        Self::Mul{ .. } => text("Closure under multiplication", "Each of ℕ, ℤ, ℚ, ℝ and ℂ is closed under multiplication."),
        Self::Div{ .. } => text("Closure under division", "For S equal to ℚ, ℝ or ℂ, a,b ∈ S and b≠0 imply a/b ∈ S."),
        Self::ExactIntegerDiv{ .. } => text("Integer quotient by divisibility", "If integers a,b satisfy b≠0 and b divides a, then a/b is an integer. For example, 6/2 ∈ ℤ."),
        Self::Neg{ .. } => text("Closure under negation", "Each of ℤ, ℚ, ℝ and ℂ contains the additive inverse of each of its elements."),
        Self::Abs{ .. } => text("Carrier of an absolute value", "Absolute value preserves integer, rational and real membership; the absolute value of an integer is also a natural number."),
        Self::Pow{ .. } => text("Closure under powers", "Natural and integer bases remain in their respective number sets under natural powers. Rational, real and complex bases remain in their respective number sets under defined integer powers."),
        Self::Min{ .. } => text("Carrier of a minimum", "For a,b in the same ordered number set, min(a,b) is one of a,b and belongs to that set."),
        Self::Max{ .. } => text("Carrier of a maximum", "For a,b in the same ordered number set, max(a,b) is one of a,b and belongs to that set."),
        Self::NaturalMaxDifference{ .. } => text("Natural difference from a maximum", "For natural a,b, max(a,b)−a and max(a,b)−b are nonnegative integers, hence natural numbers."),
        Self::FunctionReturn{ .. } => text("Declared return domain", "A function applied to arguments satisfying its declared domain has a value in its declared return domain."),
        Self::Intrinsic(_) => text("Return domain of a mathematical operation", "The operation has the recorded fixed return domain whenever its defining conditions hold. This establishes its domain membership, without asserting a particular value."),
    }
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
        Self::Known(_) => text("已知的成员关系", "引用记录中的已知成员事实。"),
        Self::Closed(_) => text("数值计算的成员关系", "计算所得数值属于指定数集。"),
        Self::KnownSubset(_) => text("沿子集关系传递成员关系", "由 x ∈ A 与 A ⊆ B 推出 x ∈ B。"),
        Self::StandardSuperset(_) => text("数域的包含关系", "沿 ℕ ⊆ ℤ ⊆ ℚ ⊆ ℝ ⊆ ℂ 的包含关系，得到元素属于更大的数集。"),
        Self::Add{ .. } => text("加法封闭性", "ℕ、ℤ、ℚ、ℝ、ℂ 分别对加法封闭：两个操作数属于同一数域，其和仍属于该数域。"),
        Self::Sub{ .. } => text("减法封闭性", "ℤ、ℚ、ℝ、ℂ 分别对减法封闭；自然数一般不对减法封闭。"),
        Self::Mul{ .. } => text("乘法封闭性", "ℕ、ℤ、ℚ、ℝ、ℂ 分别对乘法封闭。"),
        Self::Div{ .. } => text("除法封闭性", "当 S 为 ℚ、ℝ 或 ℂ 时，a,b ∈ S 且 b≠0 推出 a/b ∈ S。"),
        Self::ExactIntegerDiv{ .. } => text("整除给出的整数商", "若整数 a、b 满足 b≠0 且 b 整除 a，则 a/b 为整数。例如 6/2 ∈ ℤ。"),
        Self::Neg{ .. } => text("取相反数的封闭性", "ℤ、ℚ、ℝ、ℂ 分别包含其中每个元素的相反数。"),
        Self::Abs{ .. } => text("绝对值的数域归属", "整数、有理数和实数的绝对值分别仍是整数、有理数和实数；整数的绝对值还属于自然数。"),
        Self::Pow{ .. } => text("幂的封闭性", "自然数与整数的自然数次幂分别仍属于原数集；有理数、实数与复数的有定义整数次幂分别仍属于原数域。"),
        Self::Min{ .. } => text("最小值的数域归属", "同一有序数集中的 a、b，其 min(a,b) 等于其中之一，因此仍属于该数集。"),
        Self::Max{ .. } => text("最大值的数域归属", "同一有序数集中的 a、b，其 max(a,b) 等于其中之一，因此仍属于该数集。"),
        Self::NaturalMaxDifference{ .. } => text("自然数最大值的差", "对自然数 a、b，max(a,b)−a 与 max(a,b)−b 都是非负整数，因而属于自然数。"),
        Self::FunctionReturn{ .. } => text("函数声明的返回域", "函数的实参满足其声明的定义域条件时，函数值属于声明的返回域。"),
        Self::Intrinsic(_) => text("数学运算的返回域", "运算满足其定义条件时，结果属于记录中的固定返回域；这里只确定数域归属，不确定具体取值。"),
    }
    }
}
