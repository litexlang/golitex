//! English catalog for equality builtin rules.
//! Chinese slots reuse English until dedicated zh copy is filled.

use super::equality_calculation::explain_calculation;
use super::fallback::BuiltinRuleText;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;
use crate::launch_command::OutputLanguage;

pub fn explain_equality_builtin_rule(
    rule: &EqualitySearchProofByBuiltinRule,
    lang: OutputLanguage,
) -> BuiltinRuleText {
    match rule {
        EqualitySearchProofByBuiltinRule::Calculation(proof) => explain_calculation(proof, lang),
        EqualitySearchProofByBuiltinRule::ByEqualIr(_) => BuiltinRuleText {
            rule_id: "ByEqualIr",
            rule_name: "Equal by IR".to_string(),
            message: "Both sides share the same internal representation".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ByEqualToObjWithFreeParamsLookup(_) => BuiltinRuleText {
            rule_id: "ByEqualToObjWithFreeParamsLookup",
            rule_name: "Equal via free-param object".to_string(),
            message: "Equality follows from a looked-up object with free parameters".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ByFnSetAlphaEqual(_) => BuiltinRuleText {
            rule_id: "ByFnSetAlphaEqual",
            rule_name: "FnSet α-equal".to_string(),
            message: "Function sets are equal up to renaming bound variables".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ByAnonymousFnAlphaEqual(_) => BuiltinRuleText {
            rule_id: "ByAnonymousFnAlphaEqual",
            rule_name: "Anonymous fn α-equal".to_string(),
            message: "Anonymous functions are equal up to renaming bound variables".to_string(),
        },
        EqualitySearchProofByBuiltinRule::BySetBuilderAlphaEqual(_) => BuiltinRuleText {
            rule_id: "BySetBuilderAlphaEqual",
            rule_name: "Set-builder α-equal".to_string(),
            message: "Set builders are equal up to renaming bound variables".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SinArcsinLeftInverse(_) => BuiltinRuleText {
            rule_id: "SinArcsinLeftInverse",
            rule_name: "sin ∘ arcsin".to_string(),
            message: "sin(arcsin(x)) = x on the arcsin range".to_string(),
        },
        EqualitySearchProofByBuiltinRule::CosArccosLeftInverse(_) => BuiltinRuleText {
            rule_id: "CosArccosLeftInverse",
            rule_name: "cos ∘ arccos".to_string(),
            message: "cos(arccos(x)) = x on the arccos range".to_string(),
        },
        EqualitySearchProofByBuiltinRule::TanArctanLeftInverse(_) => BuiltinRuleText {
            rule_id: "TanArctanLeftInverse",
            rule_name: "tan ∘ arctan".to_string(),
            message: "tan(arctan(x)) = x".to_string(),
        },
        EqualitySearchProofByBuiltinRule::CotArccotLeftInverse(_) => BuiltinRuleText {
            rule_id: "CotArccotLeftInverse",
            rule_name: "cot ∘ arccot".to_string(),
            message: "cot(arccot(x)) = x".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArcsinSinRightInverse(_) => BuiltinRuleText {
            rule_id: "ArcsinSinRightInverse",
            rule_name: "arcsin ∘ sin".to_string(),
            message: "arcsin(sin(x)) = x on the principal interval".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArccosCosRightInverse(_) => BuiltinRuleText {
            rule_id: "ArccosCosRightInverse",
            rule_name: "arccos ∘ cos".to_string(),
            message: "arccos(cos(x)) = x on the principal interval".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArctanTanRightInverse(_) => BuiltinRuleText {
            rule_id: "ArctanTanRightInverse",
            rule_name: "arctan ∘ tan".to_string(),
            message: "arctan(tan(x)) = x on the principal interval".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArccotCotRightInverse(_) => BuiltinRuleText {
            rule_id: "ArccotCotRightInverse",
            rule_name: "arccot ∘ cot".to_string(),
            message: "arccot(cot(x)) = x on the principal interval".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArcsinExactZero(_) => BuiltinRuleText {
            rule_id: "ArcsinExactZero",
            rule_name: "arcsin 0".to_string(),
            message: "arcsin(0) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArcsinExactOne(_) => BuiltinRuleText {
            rule_id: "ArcsinExactOne",
            rule_name: "arcsin 1".to_string(),
            message: "arcsin(1) = π/2".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArcsinExactNegOne(_) => BuiltinRuleText {
            rule_id: "ArcsinExactNegOne",
            rule_name: "arcsin(-1)".to_string(),
            message: "arcsin(-1) = -π/2".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArccosExactOne(_) => BuiltinRuleText {
            rule_id: "ArccosExactOne",
            rule_name: "arccos 1".to_string(),
            message: "arccos(1) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArccosExactZero(_) => BuiltinRuleText {
            rule_id: "ArccosExactZero",
            rule_name: "arccos 0".to_string(),
            message: "arccos(0) = π/2".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArccosExactNegOne(_) => BuiltinRuleText {
            rule_id: "ArccosExactNegOne",
            rule_name: "arccos(-1)".to_string(),
            message: "arccos(-1) = π".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArctanExactZero(_) => BuiltinRuleText {
            rule_id: "ArctanExactZero",
            rule_name: "arctan 0".to_string(),
            message: "arctan(0) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ArccotExactZero(_) => BuiltinRuleText {
            rule_id: "ArccotExactZero",
            rule_name: "arccot 0".to_string(),
            message: "arccot(0) = π/2".to_string(),
        },
        EqualitySearchProofByBuiltinRule::PowerProductSameBase(_) => BuiltinRuleText {
            rule_id: "PowerProductSameBase",
            rule_name: "a^m · a^n".to_string(),
            message: "a^m · a^n = a^(m+n)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::PowerOfPower(_) => BuiltinRuleText {
            rule_id: "PowerOfPower",
            rule_name: "(a^m)^n".to_string(),
            message: "(a^m)^n = a^(m·n)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::PowerOfProduct(_) => BuiltinRuleText {
            rule_id: "PowerOfProduct",
            rule_name: "(a·b)^n".to_string(),
            message: "(a·b)^n = a^n · b^n".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ReciprocalAsNegOnePower(_) => BuiltinRuleText {
            rule_id: "ReciprocalAsNegOnePower",
            rule_name: "1/a as a^(-1)".to_string(),
            message: "1/a = a^(-1)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::QuotientAsMulNegOnePower(_) => BuiltinRuleText {
            rule_id: "QuotientAsMulNegOnePower",
            rule_name: "a/b as a·b^(-1)".to_string(),
            message: "a/b = a · b^(-1)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::OneToAnyPower(_) => BuiltinRuleText {
            rule_id: "OneToAnyPower",
            rule_name: "1^n".to_string(),
            message: "1^n = 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ZeroToPosNatPower(_) => BuiltinRuleText {
            rule_id: "ZeroToPosNatPower",
            rule_name: "0^n (n>0)".to_string(),
            message: "0^n = 0 for positive natural n".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SqrtSquare(_) => BuiltinRuleText {
            rule_id: "SqrtSquare",
            rule_name: "√(a²)".to_string(),
            message: "√(a²) relates to |a| / square-root of a square".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SqrtZero(_) => BuiltinRuleText {
            rule_id: "SqrtZero",
            rule_name: "√0".to_string(),
            message: "√0 = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SqrtOne(_) => BuiltinRuleText {
            rule_id: "SqrtOne",
            rule_name: "√1".to_string(),
            message: "√1 = 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SqrtOfSquare(_) => BuiltinRuleText {
            rule_id: "SqrtOfSquare",
            rule_name: "√(a·a)".to_string(),
            message: "√(a·a) = |a|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SqrtProduct(_) => BuiltinRuleText {
            rule_id: "SqrtProduct",
            rule_name: "√(a·b)".to_string(),
            message: "√(a·b) = √a · √b (when defined)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SqrtQuotient(_) => BuiltinRuleText {
            rule_id: "SqrtQuotient",
            rule_name: "√(a/b)".to_string(),
            message: "√(a/b) = √a / √b (when defined)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::AbsOfNegation(_) => BuiltinRuleText {
            rule_id: "AbsOfNegation",
            rule_name: "|-a|".to_string(),
            message: "|-a| = |a|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::AbsProduct(_) => BuiltinRuleText {
            rule_id: "AbsProduct",
            rule_name: "|a·b|".to_string(),
            message: "|a·b| = |a|·|b|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::AbsSquare(_) => BuiltinRuleText {
            rule_id: "AbsSquare",
            rule_name: "|a|²".to_string(),
            message: "|a|² = a²".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LogBaseSelf(_) => BuiltinRuleText {
            rule_id: "LogBaseSelf",
            rule_name: "log_a(a)".to_string(),
            message: "log_a(a) = 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LogOfOne(_) => BuiltinRuleText {
            rule_id: "LogOfOne",
            rule_name: "log_a(1)".to_string(),
            message: "log_a(1) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LogOfPowerSameBase(_) => BuiltinRuleText {
            rule_id: "LogOfPowerSameBase",
            rule_name: "log_a(a^n)".to_string(),
            message: "log_a(a^n) = n".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LogArgPower(_) => BuiltinRuleText {
            rule_id: "LogArgPower",
            rule_name: "log_a(b^n)".to_string(),
            message: "log_a(b^n) = n · log_a(b)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LogProduct(_) => BuiltinRuleText {
            rule_id: "LogProduct",
            rule_name: "log_a(b·c)".to_string(),
            message: "log_a(b·c) = log_a(b) + log_a(c)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LogQuotient(_) => BuiltinRuleText {
            rule_id: "LogQuotient",
            rule_name: "log_a(b/c)".to_string(),
            message: "log_a(b/c) = log_a(b) - log_a(c)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LogReciprocal(_) => BuiltinRuleText {
            rule_id: "LogReciprocal",
            rule_name: "log_a(1/b)".to_string(),
            message: "log_a(1/b) = -log_a(b)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LogChangeOfBase(_) => BuiltinRuleText {
            rule_id: "LogChangeOfBase",
            rule_name: "change of base".to_string(),
            message: "log_a(b) = log_c(b) / log_c(a)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ZeroMod(_) => BuiltinRuleText {
            rule_id: "ZeroMod",
            rule_name: "0 mod n".to_string(),
            message: "0 mod n = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ModOne(_) => BuiltinRuleText {
            rule_id: "ModOne",
            rule_name: "a mod 1".to_string(),
            message: "a mod 1 = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::OneModAtLeastTwo(_) => BuiltinRuleText {
            rule_id: "OneModAtLeastTwo",
            rule_name: "1 mod n (n≥2)".to_string(),
            message: "1 mod n = 1 when n ≥ 2".to_string(),
        },
        EqualitySearchProofByBuiltinRule::NestedSameModAbsorption(_) => BuiltinRuleText {
            rule_id: "NestedSameModAbsorption",
            rule_name: "nested same mod".to_string(),
            message: "(a mod n) mod n = a mod n".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ModCompatibleSmallerModulus(_) => BuiltinRuleText {
            rule_id: "ModCompatibleSmallerModulus",
            rule_name: "compatible smaller modulus".to_string(),
            message: "a mod d = (a mod m) mod d when m mod d = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::MinIdempotent(_) => BuiltinRuleText {
            rule_id: "MinIdempotent",
            rule_name: "min(a,a)".to_string(),
            message: "min(a,a) = a".to_string(),
        },
        EqualitySearchProofByBuiltinRule::MaxIdempotent(_) => BuiltinRuleText {
            rule_id: "MaxIdempotent",
            rule_name: "max(a,a)".to_string(),
            message: "max(a,a) = a".to_string(),
        },
        EqualitySearchProofByBuiltinRule::MinCommutative(_) => BuiltinRuleText {
            rule_id: "MinCommutative",
            rule_name: "min commutative".to_string(),
            message: "min(a,b) = min(b,a)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::MaxCommutative(_) => BuiltinRuleText {
            rule_id: "MaxCommutative",
            rule_name: "max commutative".to_string(),
            message: "max(a,b) = max(b,a)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::AbsAbsAbsorption(_) => BuiltinRuleText {
            rule_id: "AbsAbsAbsorption",
            rule_name: "||a||".to_string(),
            message: "||a|| = |a|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ExpOfLn(_) => BuiltinRuleText {
            rule_id: "ExpOfLn",
            rule_name: "exp(ln(x))".to_string(),
            message: "exp(ln(x)) = x".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LnOfExp(_) => BuiltinRuleText {
            rule_id: "LnOfExp",
            rule_name: "ln(exp(x))".to_string(),
            message: "ln(exp(x)) = x".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FloorOfInteger(_) => BuiltinRuleText {
            rule_id: "FloorOfInteger",
            rule_name: "⌊n⌋ for integer n".to_string(),
            message: "⌊n⌋ = n when n is an integer".to_string(),
        },
        EqualitySearchProofByBuiltinRule::CeilOfInteger(_) => BuiltinRuleText {
            rule_id: "CeilOfInteger",
            rule_name: "⌈n⌉ for integer n".to_string(),
            message: "⌈n⌉ = n when n is an integer".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ModSelfZero(_) => BuiltinRuleText {
            rule_id: "ModSelfZero",
            rule_name: "a mod a".to_string(),
            message: "a mod a = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FloorOfCeilOfInteger(_) => BuiltinRuleText {
            rule_id: "FloorOfCeilOfInteger",
            rule_name: "⌊⌈n⌉⌋".to_string(),
            message: "⌊⌈n⌉⌋ = n for integer n".to_string(),
        },
        EqualitySearchProofByBuiltinRule::CeilOfFloorOfInteger(_) => BuiltinRuleText {
            rule_id: "CeilOfFloorOfInteger",
            rule_name: "⌈⌊n⌋⌉".to_string(),
            message: "⌈⌊n⌋⌉ = n for integer n".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SqrtOfSquareEqualsAbs(_) => BuiltinRuleText {
            rule_id: "SqrtOfSquareEqualsAbs",
            rule_name: "√(a²)=|a|".to_string(),
            message: "√(a²) = |a|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::QuotByOne(_) => BuiltinRuleText {
            rule_id: "QuotByOne",
            rule_name: "a ÷ 1".to_string(),
            message: "a quot 1 = a".to_string(),
        },
        EqualitySearchProofByBuiltinRule::QuotSelfOne(_) => BuiltinRuleText {
            rule_id: "QuotSelfOne",
            rule_name: "a ÷ a".to_string(),
            message: "a quot a = 1 (a ≠ 0)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LcmCommutative(_) => BuiltinRuleText {
            rule_id: "LcmCommutative",
            rule_name: "lcm commutative".to_string(),
            message: "lcm(a,b) = lcm(b,a)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LcmIdempotentAbs(_) => BuiltinRuleText {
            rule_id: "LcmIdempotentAbs",
            rule_name: "lcm(a,a)".to_string(),
            message: "lcm(a,a) = |a|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::GcdCommutative(_) => BuiltinRuleText {
            rule_id: "GcdCommutative",
            rule_name: "gcd commutative".to_string(),
            message: "gcd(a,b) = gcd(b,a)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::GcdIdempotentAbs(_) => BuiltinRuleText {
            rule_id: "GcdIdempotentAbs",
            rule_name: "gcd(a,a)".to_string(),
            message: "gcd(a,a) = |a|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::GcdRightZeroAbs(_) => BuiltinRuleText {
            rule_id: "GcdRightZeroAbs",
            rule_name: "gcd(a,0)".to_string(),
            message: "gcd(a,0) = |a|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::GcdLeftZeroAbs(_) => BuiltinRuleText {
            rule_id: "GcdLeftZeroAbs",
            rule_name: "gcd(0,a)".to_string(),
            message: "gcd(0,a) = |a|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FactorialSuccessor(_) => BuiltinRuleText {
            rule_id: "FactorialSuccessor",
            rule_name: "(n+1)!".to_string(),
            message: "(n+1)! = (n+1)·n!".to_string(),
        },
        EqualitySearchProofByBuiltinRule::AbsNonnegEqualsSelf(_) => BuiltinRuleText {
            rule_id: "AbsNonnegEqualsSelf",
            rule_name: "|a| for a≥0".to_string(),
            message: "|a| = a when a ≥ 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::AbsNonposEqualsNegation(_) => BuiltinRuleText {
            rule_id: "AbsNonposEqualsNegation",
            rule_name: "|a| for a≤0".to_string(),
            message: "|a| = -a when a ≤ 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SignOfPositive(_) => BuiltinRuleText {
            rule_id: "SignOfPositive",
            rule_name: "sign of positive".to_string(),
            message: "sign(a) = 1 when a > 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SignOfNegative(_) => BuiltinRuleText {
            rule_id: "SignOfNegative",
            rule_name: "sign of negative".to_string(),
            message: "sign(a) = -1 when a < 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::MaxRightWhenLessEqual(_) => BuiltinRuleText {
            rule_id: "MaxRightWhenLessEqual",
            rule_name: "max when a≤b".to_string(),
            message: "max(a,b) = b when a ≤ b".to_string(),
        },
        EqualitySearchProofByBuiltinRule::MaxLeftWhenLessEqual(_) => BuiltinRuleText {
            rule_id: "MaxLeftWhenLessEqual",
            rule_name: "max when b≤a".to_string(),
            message: "max(a,b) = a when b ≤ a".to_string(),
        },
        EqualitySearchProofByBuiltinRule::MinLeftWhenLessEqual(_) => BuiltinRuleText {
            rule_id: "MinLeftWhenLessEqual",
            rule_name: "min when a≤b".to_string(),
            message: "min(a,b) = a when a ≤ b".to_string(),
        },
        EqualitySearchProofByBuiltinRule::MinRightWhenLessEqual(_) => BuiltinRuleText {
            rule_id: "MinRightWhenLessEqual",
            rule_name: "min when b≤a".to_string(),
            message: "min(a,b) = b when b ≤ a".to_string(),
        },
        EqualitySearchProofByBuiltinRule::GcdDividesArgument(_) => BuiltinRuleText {
            rule_id: "GcdDividesArgument",
            rule_name: "gcd divides".to_string(),
            message: "gcd(a,b) divides a (and b)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ProductModFactorZero(_) => BuiltinRuleText {
            rule_id: "ProductModFactorZero",
            rule_name: "product mod factor".to_string(),
            message: "(k·n) mod n = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::EqualityFromTwoSidedWeakOrder(_) => BuiltinRuleText {
            rule_id: "EqualityFromTwoSidedWeakOrder",
            rule_name: "a≤b and b≤a".to_string(),
            message: "a = b follows from a ≤ b and b ≤ a".to_string(),
        },
        EqualitySearchProofByBuiltinRule::DiffZeroFromEqualOperands(_) => BuiltinRuleText {
            rule_id: "DiffZeroFromEqualOperands",
            rule_name: "a−b=0 from a=b".to_string(),
            message: "a − b = 0 follows from a = b".to_string(),
        },
        EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(_) => BuiltinRuleText {
            rule_id: "EqualFromKnownDifferenceZero",
            rule_name: "a=b from a−b=0".to_string(),
            message: "a = b follows from a known a − b = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ZeroProductCancel(_) => BuiltinRuleText {
            rule_id: "ZeroProductCancel",
            rule_name: "zero product".to_string(),
            message: "a·b = 0 with a≠0 gives b = 0 (and symmetrically)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SignOfNegation(_) => BuiltinRuleText {
            rule_id: "SignOfNegation",
            rule_name: "sign(-a)".to_string(),
            message: "sign(-a) = -sign(a)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SignTimesAbsEqualsArg(_) => BuiltinRuleText {
            rule_id: "SignTimesAbsEqualsArg",
            rule_name: "sign(a)·|a|".to_string(),
            message: "sign(a)·|a| = a".to_string(),
        },
        EqualitySearchProofByBuiltinRule::AbsEqualsSignTimesArg(_) => BuiltinRuleText {
            rule_id: "AbsEqualsSignTimesArg",
            rule_name: "|a| = sign(a)·a".to_string(),
            message: "|a| = sign(a)·a when sign is defined".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SignOfProduct(_) => BuiltinRuleText {
            rule_id: "SignOfProduct",
            rule_name: "sign(a·b)".to_string(),
            message: "sign(a·b) = sign(a)·sign(b)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SubtractionFromKnownAddition(_) => BuiltinRuleText {
            rule_id: "SubtractionFromKnownAddition",
            rule_name: "subtraction from addition".to_string(),
            message: "c = a − b follows from a known a = b + c".to_string(),
        },
        EqualitySearchProofByBuiltinRule::QuotEuclideanDecomposition(_) => BuiltinRuleText {
            rule_id: "QuotEuclideanDecomposition",
            rule_name: "Euclidean quot".to_string(),
            message: "a = (a quot n)·n + (a mod n)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ModDividendMinusRemainderZero(_) => BuiltinRuleText {
            rule_id: "ModDividendMinusRemainderZero",
            rule_name: "mod remainder".to_string(),
            message: "a − (a mod n) is divisible by n".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SquareSumComponentZero(_) => BuiltinRuleText {
            rule_id: "SquareSumComponentZero",
            rule_name: "square-sum zero".to_string(),
            message: "a² + b² = 0 forces a = 0 and b = 0 (over reals)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::MinusOneOddNaturalPower(_) => BuiltinRuleText {
            rule_id: "MinusOneOddNaturalPower",
            rule_name: "(-1)^(odd)".to_string(),
            message: "(-1)^n = -1 for odd natural n".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LcmGcdProductAbs(_) => BuiltinRuleText {
            rule_id: "LcmGcdProductAbs",
            rule_name: "lcm·gcd".to_string(),
            message: "lcm(a,b)·gcd(a,b) = |a·b|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::UnionEmptyRight(_) => BuiltinRuleText {
            rule_id: "UnionEmptyRight",
            rule_name: "A ∪ ∅".to_string(),
            message: "A ∪ ∅ = A".to_string(),
        },
        EqualitySearchProofByBuiltinRule::UnionEmptyLeft(_) => BuiltinRuleText {
            rule_id: "UnionEmptyLeft",
            rule_name: "∅ ∪ A".to_string(),
            message: "∅ ∪ A = A".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IntersectEmptyRight(_) => BuiltinRuleText {
            rule_id: "IntersectEmptyRight",
            rule_name: "A ∩ ∅".to_string(),
            message: "A ∩ ∅ = ∅".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IntersectEmptyLeft(_) => BuiltinRuleText {
            rule_id: "IntersectEmptyLeft",
            rule_name: "∅ ∩ A".to_string(),
            message: "∅ ∩ A = ∅".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SetMinusSelfEmpty(_) => BuiltinRuleText {
            rule_id: "SetMinusSelfEmpty",
            rule_name: "A \\ A".to_string(),
            message: "A \\ A = ∅".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SetMinusEmptyRight(_) => BuiltinRuleText {
            rule_id: "SetMinusEmptyRight",
            rule_name: "A \\ ∅".to_string(),
            message: "A \\ ∅ = A".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SetMinusEmptyLeft(_) => BuiltinRuleText {
            rule_id: "SetMinusEmptyLeft",
            rule_name: "∅ \\ A".to_string(),
            message: "∅ \\ A = ∅".to_string(),
        },
        EqualitySearchProofByBuiltinRule::UnionCommutative(_) => BuiltinRuleText {
            rule_id: "UnionCommutative",
            rule_name: "union commutative".to_string(),
            message: "A ∪ B = B ∪ A".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IntersectCommutative(_) => BuiltinRuleText {
            rule_id: "IntersectCommutative",
            rule_name: "intersect commutative".to_string(),
            message: "A ∩ B = B ∩ A".to_string(),
        },
        EqualitySearchProofByBuiltinRule::UnionIdempotent(_) => BuiltinRuleText {
            rule_id: "UnionIdempotent",
            rule_name: "A ∪ A".to_string(),
            message: "A ∪ A = A".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IntersectIdempotent(_) => BuiltinRuleText {
            rule_id: "IntersectIdempotent",
            rule_name: "A ∩ A".to_string(),
            message: "A ∩ A = A".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IntersectFromSubset(_) => BuiltinRuleText {
            rule_id: "IntersectFromSubset",
            rule_name: "intersect from subset".to_string(),
            message: "A ⊆ B gives A ∩ B = A".to_string(),
        },
        EqualitySearchProofByBuiltinRule::EmptySetFromNotNonempty(_) => BuiltinRuleText {
            rule_id: "EmptySetFromNotNonempty",
            rule_name: "empty from not nonempty".to_string(),
            message: "¬$is_nonempty_set(A) gives A = ∅".to_string(),
        },
        EqualitySearchProofByBuiltinRule::PowerSetFiniteSetSize(_) => BuiltinRuleText {
            rule_id: "PowerSetFiniteSetSize",
            rule_name: "|pow(A)|".to_string(),
            message: "|pow(A)| = 2^|A| for finite A".to_string(),
        },
        EqualitySearchProofByBuiltinRule::UnionAssociative(_) => BuiltinRuleText {
            rule_id: "UnionAssociative",
            rule_name: "union associative".to_string(),
            message: "(A ∪ B) ∪ C = A ∪ (B ∪ C)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IntersectAssociative(_) => BuiltinRuleText {
            rule_id: "IntersectAssociative",
            rule_name: "intersect associative".to_string(),
            message: "(A ∩ B) ∩ C = A ∩ (B ∩ C)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IntersectUnionDistributive(_) => BuiltinRuleText {
            rule_id: "IntersectUnionDistributive",
            rule_name: "∩ distributes over ∪".to_string(),
            message: "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SetMinusUnionDeMorgan(_) => BuiltinRuleText {
            rule_id: "SetMinusUnionDeMorgan",
            rule_name: "\\ over ∪".to_string(),
            message: "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SetMinusIntersectDeMorgan(_) => BuiltinRuleText {
            rule_id: "SetMinusIntersectDeMorgan",
            rule_name: "\\ over ∩".to_string(),
            message: "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IntersectSetMinusSelfEmpty(_) => BuiltinRuleText {
            rule_id: "IntersectSetMinusSelfEmpty",
            rule_name: "A ∩ (A\\B)".to_string(),
            message: "A ∩ (A \\ B) relates to emptiness / difference".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumEmpty(_) => BuiltinRuleText {
            rule_id: "FiniteSetSumEmpty",
            rule_name: "sum over ∅".to_string(),
            message: "∑_{x∈∅} f(x) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSetProductEmpty(_) => BuiltinRuleText {
            rule_id: "FiniteSetProductEmpty",
            rule_name: "product over ∅".to_string(),
            message: "∏_{x∈∅} f(x) = 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSetReduceEmpty(_) => BuiltinRuleText {
            rule_id: "FiniteSetReduceEmpty",
            rule_name: "reduce over ∅".to_string(),
            message: "reduce over the empty set is the unit".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ReduceEmpty(_) => BuiltinRuleText {
            rule_id: "ReduceEmpty",
            rule_name: "reduce empty".to_string(),
            message: "reduce on an empty range is the unit".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SumEmptyRange(_) => BuiltinRuleText {
            rule_id: "SumEmptyRange",
            rule_name: "sum empty range".to_string(),
            message: "∑ over an empty range is 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ProductEmptyRange(_) => BuiltinRuleText {
            rule_id: "ProductEmptyRange",
            rule_name: "product empty range".to_string(),
            message: "∏ over an empty range is 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::UnionAbsorptionFromSubset(_) => BuiltinRuleText {
            rule_id: "UnionAbsorptionFromSubset",
            rule_name: "union absorption".to_string(),
            message: "A ⊆ B gives A ∪ B = B".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SetMinusRecoversSubset(_) => BuiltinRuleText {
            rule_id: "SetMinusRecoversSubset",
            rule_name: "difference recovers subset".to_string(),
            message: "A ⊆ B gives B \\ (B \\ A) = A".to_string(),
        },
        EqualitySearchProofByBuiltinRule::EmptySetFromSizeZero(_) => BuiltinRuleText {
            rule_id: "EmptySetFromSizeZero",
            rule_name: "empty from size 0".to_string(),
            message: "|A| = 0 gives A = ∅".to_string(),
        },
        EqualitySearchProofByBuiltinRule::CartProjFactor(_) => BuiltinRuleText {
            rule_id: "CartProjFactor",
            rule_name: "cart projection factor".to_string(),
            message: "Projection recovers a Cartesian factor".to_string(),
        },
        EqualitySearchProofByBuiltinRule::TupleComponentAtIndex(_) => BuiltinRuleText {
            rule_id: "TupleComponentAtIndex",
            rule_name: "tuple component".to_string(),
            message: "The i-th component of a tuple equals the stated entry".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSizeSetMinus(_) => BuiltinRuleText {
            rule_id: "FiniteSetSizeSetMinus",
            rule_name: "|A\\B|".to_string(),
            message: "|A \\ B| = |A| − |A ∩ B| for finite sets".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSizeUnion(_) => BuiltinRuleText {
            rule_id: "FiniteSetSizeUnion",
            rule_name: "|A∪B|".to_string(),
            message: "|A ∪ B| = |A| + |B| − |A ∩ B|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ClosedRangeSingletonListSet(_) => BuiltinRuleText {
            rule_id: "ClosedRangeSingletonListSet",
            rule_name: "closed range singleton".to_string(),
            message: "{n..n} = {n}".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SumSingleTerm(_) => BuiltinRuleText {
            rule_id: "SumSingleTerm",
            rule_name: "sum one term".to_string(),
            message: "∑ with a single term equals that term".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ProductSingleTerm(_) => BuiltinRuleText {
            rule_id: "ProductSingleTerm",
            rule_name: "product one term".to_string(),
            message: "∏ with a single term equals that term".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ReduceAddZeroEqualsSum(_) => BuiltinRuleText {
            rule_id: "ReduceAddZeroEqualsSum",
            rule_name: "reduce +0 as sum".to_string(),
            message: "reduce with add and 0 equals a sum".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSetReduceAddZeroEqualsSum(_) => BuiltinRuleText {
            rule_id: "FiniteSetReduceAddZeroEqualsSum",
            rule_name: "finite-set reduce as sum".to_string(),
            message: "finite-set reduce with + and 0 equals a sum".to_string(),
        },
        EqualitySearchProofByBuiltinRule::PowOfLogInverse(_) => BuiltinRuleText {
            rule_id: "PowOfLogInverse",
            rule_name: "a^(log_a b)".to_string(),
            message: "a^(log_a(b)) = b".to_string(),
        },
        EqualitySearchProofByBuiltinRule::UnionSetMinusDecomposition(_) => BuiltinRuleText {
            rule_id: "UnionSetMinusDecomposition",
            rule_name: "union\\difference".to_string(),
            message: "A ∪ B = A ∪ (B \\ A)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SetMinusIntersectSelf(_) => BuiltinRuleText {
            rule_id: "SetMinusIntersectSelf",
            rule_name: "A \\ (A∩B)".to_string(),
            message: "A \\ (A ∩ B) = A \\ B".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ReOfImaginaryUnit(_) => BuiltinRuleText {
            rule_id: "ReOfImaginaryUnit",
            rule_name: "Re(i)".to_string(),
            message: "Re(i) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ImgOfImaginaryUnit(_) => BuiltinRuleText {
            rule_id: "ImgOfImaginaryUnit",
            rule_name: "Im(i)".to_string(),
            message: "Im(i) = 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ReOfRealEmbedding(_) => BuiltinRuleText {
            rule_id: "ReOfRealEmbedding",
            rule_name: "Re of real".to_string(),
            message: "Re(embed(x)) = x".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ImgOfRealEmbedding(_) => BuiltinRuleText {
            rule_id: "ImgOfRealEmbedding",
            rule_name: "Im of real".to_string(),
            message: "Im(embed(x)) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ReOfRealPlusI(_) => BuiltinRuleText {
            rule_id: "ReOfRealPlusI",
            rule_name: "Re(x+i)".to_string(),
            message: "Re(x + i) = x".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusI(_) => BuiltinRuleText {
            rule_id: "ImgOfRealPlusI",
            rule_name: "Im(x+i)".to_string(),
            message: "Im(x + i) = 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsOfImaginaryUnit(_) => BuiltinRuleText {
            rule_id: "ComplexAbsOfImaginaryUnit",
            rule_name: "|i|".to_string(),
            message: "|i| = 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ModNestedDivisibleAbsorption(_) => BuiltinRuleText {
            rule_id: "ModNestedDivisibleAbsorption",
            rule_name: "nested mod absorption".to_string(),
            message: "If n | m then (a mod m) mod n = a mod n".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SumSplitLastTerm(_) => BuiltinRuleText {
            rule_id: "SumSplitLastTerm",
            rule_name: "sum split last".to_string(),
            message: "Sum splits off its last term".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ProductSplitLastTerm(_) => BuiltinRuleText {
            rule_id: "ProductSplitLastTerm",
            rule_name: "product split last".to_string(),
            message: "Product splits off its last term".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumListExpansion(_) => BuiltinRuleText {
            rule_id: "FiniteSetSumListExpansion",
            rule_name: "finite-set sum expand".to_string(),
            message: "Sum over a list-set expands to an explicit sum".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSetProductListExpansion(_) => BuiltinRuleText {
            rule_id: "FiniteSetProductListExpansion",
            rule_name: "finite-set product expand".to_string(),
            message: "Product over a list-set expands to an explicit product".to_string(),
        },
        EqualitySearchProofByBuiltinRule::EulerEqualsExpOne(_) => BuiltinRuleText {
            rule_id: "EulerEqualsExpOne",
            rule_name: "e = exp(1)".to_string(),
            message: "e = exp(1)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LnOfEuler(_) => BuiltinRuleText {
            rule_id: "LnOfEuler",
            rule_name: "ln(e)".to_string(),
            message: "ln(e) = 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ReOfReal(_) => BuiltinRuleText {
            rule_id: "ReOfReal",
            rule_name: "Re(x) for real x".to_string(),
            message: "Re(x) = x for real x".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ImgOfReal(_) => BuiltinRuleText {
            rule_id: "ImgOfReal",
            rule_name: "Im(x) for real x".to_string(),
            message: "Im(x) = 0 for real x".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ReOfRealPlusImagScaled(_) => BuiltinRuleText {
            rule_id: "ReOfRealPlusImagScaled",
            rule_name: "Re(x+y·i)".to_string(),
            message: "Re(x + y·i) = x".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusImagScaled(_) => BuiltinRuleText {
            rule_id: "ImgOfRealPlusImagScaled",
            rule_name: "Im(x+y·i)".to_string(),
            message: "Im(x + y·i) = y".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsOfNonnegReal(_) => BuiltinRuleText {
            rule_id: "ComplexAbsOfNonnegReal",
            rule_name: "|x| for x≥0 real".to_string(),
            message: "|embed(x)| = x for x ≥ 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsOfImagScaled(_) => BuiltinRuleText {
            rule_id: "ComplexAbsOfImagScaled",
            rule_name: "|y·i|".to_string(),
            message: "|y·i| = |y|".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ClosedRangeLiteralExpansion(_) => BuiltinRuleText {
            rule_id: "ClosedRangeLiteralExpansion",
            rule_name: "closed range expand".to_string(),
            message: "A numeric closed range expands to an explicit list set".to_string(),
        },
        EqualitySearchProofByBuiltinRule::RangeLiteralExpansion(_) => BuiltinRuleText {
            rule_id: "RangeLiteralExpansion",
            rule_name: "range expand".to_string(),
            message: "A numeric range expands to an explicit list set".to_string(),
        },
        EqualitySearchProofByBuiltinRule::PowerSetOfEmpty(_) => BuiltinRuleText {
            rule_id: "PowerSetOfEmpty",
            rule_name: "pow(∅)".to_string(),
            message: "pow(∅) = {∅}".to_string(),
        },
        EqualitySearchProofByBuiltinRule::PowerSetOfSingleton(_) => BuiltinRuleText {
            rule_id: "PowerSetOfSingleton",
            rule_name: "pow({a})".to_string(),
            message: "pow({a}) = {∅, {a}}".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FamilyUnionOfEmpty(_) => BuiltinRuleText {
            rule_id: "FamilyUnionOfEmpty",
            rule_name: "⋃∅".to_string(),
            message: "⋃∅ = ∅".to_string(),
        },
        EqualitySearchProofByBuiltinRule::CartWithEmptyFactor(_) => BuiltinRuleText {
            rule_id: "CartWithEmptyFactor",
            rule_name: "A × ∅".to_string(),
            message: "A × ∅ = ∅".to_string(),
        },
        EqualitySearchProofByBuiltinRule::UnionOverIntersectDistributive(_) => BuiltinRuleText {
            rule_id: "UnionOverIntersectDistributive",
            rule_name: "∪ over ∩".to_string(),
            message: "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SetMinusChainToUnion(_) => BuiltinRuleText {
            rule_id: "SetMinusChainToUnion",
            rule_name: "chained difference".to_string(),
            message: "A \\ B \\ C expands via union of removed sets".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FnRangeOfConstantAnonymousFn(_) => BuiltinRuleText {
            rule_id: "FnRangeOfConstantAnonymousFn",
            rule_name: "range of constant fn".to_string(),
            message: "Range of a constant anonymous function is a singleton".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SeqEqualsFnOnN(_) => BuiltinRuleText {
            rule_id: "SeqEqualsFnOnN",
            rule_name: "seq as fn on N".to_string(),
            message: "A sequence equals its function on N".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSeqEqualsFnOnClosedRange(_) => BuiltinRuleText {
            rule_id: "FiniteSeqEqualsFnOnClosedRange",
            rule_name: "finite seq as fn".to_string(),
            message: "A finite sequence equals its function on a closed range".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IndexUnionEmptyIndex(_) => BuiltinRuleText {
            rule_id: "IndexUnionEmptyIndex",
            rule_name: "⋃_{i∈∅}".to_string(),
            message: "Indexed union over an empty index is ∅".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IndexIntersectEmptyIndex(_) => BuiltinRuleText {
            rule_id: "IndexIntersectEmptyIndex",
            rule_name: "⋂_{i∈∅}".to_string(),
            message: "Indexed intersect over an empty index is the ambient universe convention used by Litex".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IndexCartEmptyIndex(_) => BuiltinRuleText {
            rule_id: "IndexCartEmptyIndex",
            rule_name: "indexed cart empty".to_string(),
            message: "Indexed Cartesian product over an empty index is a unit".to_string(),
        },
        EqualitySearchProofByBuiltinRule::IndexUnionSingleton(_) => BuiltinRuleText {
            rule_id: "IndexUnionSingleton",
            rule_name: "⋃_{i∈{a}}".to_string(),
            message: "Indexed union over a singleton index is the single set".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSeqZeroEqualsFnOnEmpty(_) => BuiltinRuleText {
            rule_id: "FiniteSeqZeroEqualsFnOnEmpty",
            rule_name: "empty finite seq".to_string(),
            message: "The length-0 finite sequence equals the function on the empty range".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SetBuilderObviouslyEmpty(_) => BuiltinRuleText {
            rule_id: "SetBuilderObviouslyEmpty",
            rule_name: "empty set-builder".to_string(),
            message: "A contradictory set-builder equals ∅".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsSquaredOfRectForm(_) => BuiltinRuleText {
            rule_id: "ComplexAbsSquaredOfRectForm",
            rule_name: "|x+y i|²".to_string(),
            message: "|x + y·i|² = x² + y²".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ExpOfSum(_) => BuiltinRuleText {
            rule_id: "ExpOfSum",
            rule_name: "exp(x+y)".to_string(),
            message: "exp(x+y) = exp(x)·exp(y)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::LogBasePower(_) => BuiltinRuleText {
            rule_id: "LogBasePower",
            rule_name: "log_(a^n)(b)".to_string(),
            message: "log_(a^n)(b) = (1/n)·log_a(b)".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ReOfProduct(_) => BuiltinRuleText {
            rule_id: "ReOfProduct",
            rule_name: "Re(z·w)".to_string(),
            message: "Re(z·w) expands from rectangular forms".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ImgOfProduct(_) => BuiltinRuleText {
            rule_id: "ImgOfProduct",
            rule_name: "Im(z·w)".to_string(),
            message: "Im(z·w) expands from rectangular forms".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SinOfSum(_) => BuiltinRuleText {
            rule_id: "SinOfSum",
            rule_name: "sin(x+y)".to_string(),
            message: "sin(x+y) = sin x cos y + cos x sin y".to_string(),
        },
        EqualitySearchProofByBuiltinRule::CosOfSum(_) => BuiltinRuleText {
            rule_id: "CosOfSum",
            rule_name: "cos(x+y)".to_string(),
            message: "cos(x+y) = cos x cos y − sin x sin y".to_string(),
        },
        EqualitySearchProofByBuiltinRule::ReduceSingleTermWithAddZero(_) => BuiltinRuleText {
            rule_id: "ReduceSingleTermWithAddZero",
            rule_name: "reduce one term".to_string(),
            message: "Reduce with a single term and +0 equals that term".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumFubiniSwap(_) => BuiltinRuleText {
            rule_id: "FiniteSetSumFubiniSwap",
            rule_name: "Fubini swap for sums".to_string(),
            message: "Finite double sums may swap summation order".to_string(),
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumOverCartesianProduct(_) => BuiltinRuleText {
            rule_id: "FiniteSetSumOverCartesianProduct",
            rule_name: "sum over A×B".to_string(),
            message: "Sum over a Cartesian product expands as an iterated sum".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SinOfZero(_) => BuiltinRuleText {
            rule_id: "SinOfZero",
            rule_name: "sin 0".to_string(),
            message: "sin(0) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::CosOfZero(_) => BuiltinRuleText {
            rule_id: "CosOfZero",
            rule_name: "cos 0".to_string(),
            message: "cos(0) = 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::TanOfZero(_) => BuiltinRuleText {
            rule_id: "TanOfZero",
            rule_name: "tan 0".to_string(),
            message: "tan(0) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SinOfHalfPi(_) => BuiltinRuleText {
            rule_id: "SinOfHalfPi",
            rule_name: "sin(π/2)".to_string(),
            message: "sin(π/2) = 1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::CosOfPi(_) => BuiltinRuleText {
            rule_id: "CosOfPi",
            rule_name: "cos(π)".to_string(),
            message: "cos(π) = -1".to_string(),
        },
        EqualitySearchProofByBuiltinRule::SinOfPi(_) => BuiltinRuleText {
            rule_id: "SinOfPi",
            rule_name: "sin(π)".to_string(),
            message: "sin(π) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::CotOfHalfPi(_) => BuiltinRuleText {
            rule_id: "CotOfHalfPi",
            rule_name: "cot(π/2)".to_string(),
            message: "cot(π/2) = 0".to_string(),
        },
        EqualitySearchProofByBuiltinRule::PythagoreanIdentity(_) => BuiltinRuleText {
            rule_id: "PythagoreanIdentity",
            rule_name: "sin²+cos²".to_string(),
            message: "sin²(x) + cos²(x) = 1".to_string(),
        },
    }
}


impl EqualitySearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        explain_equality_builtin_rule(self, lang)
    }
}
