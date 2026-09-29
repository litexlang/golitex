//! English catalog for equality builtin rules.
//! Chinese slots are `None` for now (`bilingual_builtin` falls back to English).

use super::bilingual::bilingual_builtin;
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
        EqualitySearchProofByBuiltinRule::ByEqualIr(_) => bilingual_builtin(
            "ByEqualIr",
            "Equal by IR",
            "Both sides share the same internal representation",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ByEqualToObjWithFreeParamsLookup(_) => bilingual_builtin(
            "ByEqualToObjWithFreeParamsLookup",
            "Equal via free-param object",
            "Equality follows from a looked-up object with free parameters",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ByFnSetAlphaEqual(_) => bilingual_builtin(
            "ByFnSetAlphaEqual",
            "FnSet α-equal",
            "Function sets are equal up to renaming bound variables",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ByAnonymousFnAlphaEqual(_) => bilingual_builtin(
            "ByAnonymousFnAlphaEqual",
            "Anonymous fn α-equal",
            "Anonymous functions are equal up to renaming bound variables",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::BySetBuilderAlphaEqual(_) => bilingual_builtin(
            "BySetBuilderAlphaEqual",
            "Set-builder α-equal",
            "Set builders are equal up to renaming bound variables",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SinArcsinLeftInverse(_) => bilingual_builtin(
            "SinArcsinLeftInverse",
            "sin ∘ arcsin",
            "sin(arcsin(x)) = x on the arcsin range",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::CosArccosLeftInverse(_) => bilingual_builtin(
            "CosArccosLeftInverse",
            "cos ∘ arccos",
            "cos(arccos(x)) = x on the arccos range",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::TanArctanLeftInverse(_) => bilingual_builtin(
            "TanArctanLeftInverse",
            "tan ∘ arctan",
            "tan(arctan(x)) = x",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::CotArccotLeftInverse(_) => bilingual_builtin(
            "CotArccotLeftInverse",
            "cot ∘ arccot",
            "cot(arccot(x)) = x",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArcsinSinRightInverse(_) => bilingual_builtin(
            "ArcsinSinRightInverse",
            "arcsin ∘ sin",
            "arcsin(sin(x)) = x on the principal interval",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArccosCosRightInverse(_) => bilingual_builtin(
            "ArccosCosRightInverse",
            "arccos ∘ cos",
            "arccos(cos(x)) = x on the principal interval",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArctanTanRightInverse(_) => bilingual_builtin(
            "ArctanTanRightInverse",
            "arctan ∘ tan",
            "arctan(tan(x)) = x on the principal interval",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArccotCotRightInverse(_) => bilingual_builtin(
            "ArccotCotRightInverse",
            "arccot ∘ cot",
            "arccot(cot(x)) = x on the principal interval",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArcsinExactZero(_) => bilingual_builtin(
            "ArcsinExactZero",
            "arcsin 0",
            "arcsin(0) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArcsinExactOne(_) => bilingual_builtin(
            "ArcsinExactOne",
            "arcsin 1",
            "arcsin(1) = π/2",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArcsinExactNegOne(_) => bilingual_builtin(
            "ArcsinExactNegOne",
            "arcsin(-1)",
            "arcsin(-1) = -π/2",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArccosExactOne(_) => bilingual_builtin(
            "ArccosExactOne",
            "arccos 1",
            "arccos(1) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArccosExactZero(_) => bilingual_builtin(
            "ArccosExactZero",
            "arccos 0",
            "arccos(0) = π/2",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArccosExactNegOne(_) => bilingual_builtin(
            "ArccosExactNegOne",
            "arccos(-1)",
            "arccos(-1) = π",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArctanExactZero(_) => bilingual_builtin(
            "ArctanExactZero",
            "arctan 0",
            "arctan(0) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ArccotExactZero(_) => bilingual_builtin(
            "ArccotExactZero",
            "arccot 0",
            "arccot(0) = π/2",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::PowerProductSameBase(_) => bilingual_builtin(
            "PowerProductSameBase",
            "a^m · a^n",
            "a^m · a^n = a^(m+n)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::PowerOfPower(_) => bilingual_builtin(
            "PowerOfPower",
            "(a^m)^n",
            "(a^m)^n = a^(m·n)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::PowerOfProduct(_) => bilingual_builtin(
            "PowerOfProduct",
            "(a·b)^n",
            "(a·b)^n = a^n · b^n",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ReciprocalAsNegOnePower(_) => bilingual_builtin(
            "ReciprocalAsNegOnePower",
            "1/a as a^(-1)",
            "1/a = a^(-1)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::QuotientAsMulNegOnePower(_) => bilingual_builtin(
            "QuotientAsMulNegOnePower",
            "a/b as a·b^(-1)",
            "a/b = a · b^(-1)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::OneToAnyPower(_) => bilingual_builtin(
            "OneToAnyPower",
            "1^n",
            "1^n = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ZeroToPosNatPower(_) => bilingual_builtin(
            "ZeroToPosNatPower",
            "0^n (n>0)",
            "0^n = 0 for positive natural n",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SqrtSquare(_) => bilingual_builtin(
            "SqrtSquare",
            "√(a²)",
            "√(a²) relates to |a| / square-root of a square",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SqrtZero(_) => bilingual_builtin(
            "SqrtZero",
            "√0",
            "√0 = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SqrtOne(_) => bilingual_builtin(
            "SqrtOne",
            "√1",
            "√1 = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SqrtOfSquare(_) => bilingual_builtin(
            "SqrtOfSquare",
            "√(a·a)",
            "√(a·a) = |a|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SqrtProduct(_) => bilingual_builtin(
            "SqrtProduct",
            "√(a·b)",
            "√(a·b) = √a · √b (when defined)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SqrtQuotient(_) => bilingual_builtin(
            "SqrtQuotient",
            "√(a/b)",
            "√(a/b) = √a / √b (when defined)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::AbsOfNegation(_) => bilingual_builtin(
            "AbsOfNegation",
            "|-a|",
            "|-a| = |a|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::AbsProduct(_) => bilingual_builtin(
            "AbsProduct",
            "|a·b|",
            "|a·b| = |a|·|b|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::AbsSquare(_) => bilingual_builtin(
            "AbsSquare",
            "|a|²",
            "|a|² = a²",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LogBaseSelf(_) => bilingual_builtin(
            "LogBaseSelf",
            "log_a(a)",
            "log_a(a) = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LogOfOne(_) => bilingual_builtin(
            "LogOfOne",
            "log_a(1)",
            "log_a(1) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LogOfPowerSameBase(_) => bilingual_builtin(
            "LogOfPowerSameBase",
            "log_a(a^n)",
            "log_a(a^n) = n",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LogArgPower(_) => bilingual_builtin(
            "LogArgPower",
            "log_a(b^n)",
            "log_a(b^n) = n · log_a(b)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LogProduct(_) => bilingual_builtin(
            "LogProduct",
            "log_a(b·c)",
            "log_a(b·c) = log_a(b) + log_a(c)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LogQuotient(_) => bilingual_builtin(
            "LogQuotient",
            "log_a(b/c)",
            "log_a(b/c) = log_a(b) - log_a(c)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LogReciprocal(_) => bilingual_builtin(
            "LogReciprocal",
            "log_a(1/b)",
            "log_a(1/b) = -log_a(b)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LogChangeOfBase(_) => bilingual_builtin(
            "LogChangeOfBase",
            "change of base",
            "log_a(b) = log_c(b) / log_c(a)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ZeroMod(_) => bilingual_builtin(
            "ZeroMod",
            "0 mod n",
            "0 mod n = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ModOne(_) => bilingual_builtin(
            "ModOne",
            "a mod 1",
            "a mod 1 = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::OneModAtLeastTwo(_) => bilingual_builtin(
            "OneModAtLeastTwo",
            "1 mod n (n≥2)",
            "1 mod n = 1 when n ≥ 2",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::NestedSameModAbsorption(_) => bilingual_builtin(
            "NestedSameModAbsorption",
            "nested same mod",
            "(a mod n) mod n = a mod n",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::MinIdempotent(_) => bilingual_builtin(
            "MinIdempotent",
            "min(a,a)",
            "min(a,a) = a",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::MaxIdempotent(_) => bilingual_builtin(
            "MaxIdempotent",
            "max(a,a)",
            "max(a,a) = a",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::MinCommutative(_) => bilingual_builtin(
            "MinCommutative",
            "min commutative",
            "min(a,b) = min(b,a)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::MaxCommutative(_) => bilingual_builtin(
            "MaxCommutative",
            "max commutative",
            "max(a,b) = max(b,a)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::AbsAbsAbsorption(_) => bilingual_builtin(
            "AbsAbsAbsorption",
            "||a||",
            "||a|| = |a|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ExpOfLn(_) => bilingual_builtin(
            "ExpOfLn",
            "exp(ln(x))",
            "exp(ln(x)) = x",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LnOfExp(_) => bilingual_builtin(
            "LnOfExp",
            "ln(exp(x))",
            "ln(exp(x)) = x",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FloorOfInteger(_) => bilingual_builtin(
            "FloorOfInteger",
            "⌊n⌋ for integer n",
            "⌊n⌋ = n when n is an integer",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::CeilOfInteger(_) => bilingual_builtin(
            "CeilOfInteger",
            "⌈n⌉ for integer n",
            "⌈n⌉ = n when n is an integer",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ModSelfZero(_) => bilingual_builtin(
            "ModSelfZero",
            "a mod a",
            "a mod a = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FloorOfCeilOfInteger(_) => bilingual_builtin(
            "FloorOfCeilOfInteger",
            "⌊⌈n⌉⌋",
            "⌊⌈n⌉⌋ = n for integer n",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::CeilOfFloorOfInteger(_) => bilingual_builtin(
            "CeilOfFloorOfInteger",
            "⌈⌊n⌋⌉",
            "⌈⌊n⌋⌉ = n for integer n",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SqrtOfSquareEqualsAbs(_) => bilingual_builtin(
            "SqrtOfSquareEqualsAbs",
            "√(a²)=|a|",
            "√(a²) = |a|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::QuotByOne(_) => bilingual_builtin(
            "QuotByOne",
            "a ÷ 1",
            "a quot 1 = a",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::QuotSelfOne(_) => bilingual_builtin(
            "QuotSelfOne",
            "a ÷ a",
            "a quot a = 1 (a ≠ 0)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LcmCommutative(_) => bilingual_builtin(
            "LcmCommutative",
            "lcm commutative",
            "lcm(a,b) = lcm(b,a)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LcmIdempotentAbs(_) => bilingual_builtin(
            "LcmIdempotentAbs",
            "lcm(a,a)",
            "lcm(a,a) = |a|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::GcdCommutative(_) => bilingual_builtin(
            "GcdCommutative",
            "gcd commutative",
            "gcd(a,b) = gcd(b,a)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::GcdIdempotentAbs(_) => bilingual_builtin(
            "GcdIdempotentAbs",
            "gcd(a,a)",
            "gcd(a,a) = |a|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::GcdRightZeroAbs(_) => bilingual_builtin(
            "GcdRightZeroAbs",
            "gcd(a,0)",
            "gcd(a,0) = |a|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::GcdLeftZeroAbs(_) => bilingual_builtin(
            "GcdLeftZeroAbs",
            "gcd(0,a)",
            "gcd(0,a) = |a|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FactorialSuccessor(_) => bilingual_builtin(
            "FactorialSuccessor",
            "(n+1)!",
            "(n+1)! = (n+1)·n!",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::AbsNonnegEqualsSelf(_) => bilingual_builtin(
            "AbsNonnegEqualsSelf",
            "|a| for a≥0",
            "|a| = a when a ≥ 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::AbsNonposEqualsNegation(_) => bilingual_builtin(
            "AbsNonposEqualsNegation",
            "|a| for a≤0",
            "|a| = -a when a ≤ 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SignOfPositive(_) => bilingual_builtin(
            "SignOfPositive",
            "sign of positive",
            "sign(a) = 1 when a > 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SignOfNegative(_) => bilingual_builtin(
            "SignOfNegative",
            "sign of negative",
            "sign(a) = -1 when a < 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::MaxRightWhenLessEqual(_) => bilingual_builtin(
            "MaxRightWhenLessEqual",
            "max when a≤b",
            "max(a,b) = b when a ≤ b",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::MaxLeftWhenLessEqual(_) => bilingual_builtin(
            "MaxLeftWhenLessEqual",
            "max when b≤a",
            "max(a,b) = a when b ≤ a",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::MinLeftWhenLessEqual(_) => bilingual_builtin(
            "MinLeftWhenLessEqual",
            "min when a≤b",
            "min(a,b) = a when a ≤ b",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::MinRightWhenLessEqual(_) => bilingual_builtin(
            "MinRightWhenLessEqual",
            "min when b≤a",
            "min(a,b) = b when b ≤ a",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::GcdDividesArgument(_) => bilingual_builtin(
            "GcdDividesArgument",
            "gcd divides",
            "gcd(a,b) divides a (and b)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ProductModFactorZero(_) => bilingual_builtin(
            "ProductModFactorZero",
            "product mod factor",
            "(k·n) mod n = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::EqualityFromTwoSidedWeakOrder(_) => bilingual_builtin(
            "EqualityFromTwoSidedWeakOrder",
            "a≤b and b≤a",
            "a = b follows from a ≤ b and b ≤ a",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::DiffZeroFromEqualOperands(_) => bilingual_builtin(
            "DiffZeroFromEqualOperands",
            "a−b=0 from a=b",
            "a − b = 0 follows from a = b",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(_) => bilingual_builtin(
            "EqualFromKnownDifferenceZero",
            "a=b from a−b=0",
            "a = b follows from a known a − b = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ZeroProductCancel(_) => bilingual_builtin(
            "ZeroProductCancel",
            "zero product",
            "a·b = 0 with a≠0 gives b = 0 (and symmetrically)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SignOfNegation(_) => bilingual_builtin(
            "SignOfNegation",
            "sign(-a)",
            "sign(-a) = -sign(a)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SignTimesAbsEqualsArg(_) => bilingual_builtin(
            "SignTimesAbsEqualsArg",
            "sign(a)·|a|",
            "sign(a)·|a| = a",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::AbsEqualsSignTimesArg(_) => bilingual_builtin(
            "AbsEqualsSignTimesArg",
            "|a| = sign(a)·a",
            "|a| = sign(a)·a when sign is defined",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SignOfProduct(_) => bilingual_builtin(
            "SignOfProduct",
            "sign(a·b)",
            "sign(a·b) = sign(a)·sign(b)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SubtractionFromKnownAddition(_) => bilingual_builtin(
            "SubtractionFromKnownAddition",
            "subtraction from addition",
            "c = a − b follows from a known a = b + c",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::QuotEuclideanDecomposition(_) => bilingual_builtin(
            "QuotEuclideanDecomposition",
            "Euclidean quot",
            "a = (a quot n)·n + (a mod n)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ModDividendMinusRemainderZero(_) => bilingual_builtin(
            "ModDividendMinusRemainderZero",
            "mod remainder",
            "a − (a mod n) is divisible by n",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SquareSumComponentZero(_) => bilingual_builtin(
            "SquareSumComponentZero",
            "square-sum zero",
            "a² + b² = 0 forces a = 0 and b = 0 (over reals)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::MinusOneOddNaturalPower(_) => bilingual_builtin(
            "MinusOneOddNaturalPower",
            "(-1)^(odd)",
            "(-1)^n = -1 for odd natural n",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LcmGcdProductAbs(_) => bilingual_builtin(
            "LcmGcdProductAbs",
            "lcm·gcd",
            "lcm(a,b)·gcd(a,b) = |a·b|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::UnionEmptyRight(_) => bilingual_builtin(
            "UnionEmptyRight",
            "A ∪ ∅",
            "A ∪ ∅ = A",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::UnionEmptyLeft(_) => bilingual_builtin(
            "UnionEmptyLeft",
            "∅ ∪ A",
            "∅ ∪ A = A",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IntersectEmptyRight(_) => bilingual_builtin(
            "IntersectEmptyRight",
            "A ∩ ∅",
            "A ∩ ∅ = ∅",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IntersectEmptyLeft(_) => bilingual_builtin(
            "IntersectEmptyLeft",
            "∅ ∩ A",
            "∅ ∩ A = ∅",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SetMinusSelfEmpty(_) => bilingual_builtin(
            "SetMinusSelfEmpty",
            "A \\ A",
            "A \\ A = ∅",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SetMinusEmptyRight(_) => bilingual_builtin(
            "SetMinusEmptyRight",
            "A \\ ∅",
            "A \\ ∅ = A",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SetMinusEmptyLeft(_) => bilingual_builtin(
            "SetMinusEmptyLeft",
            "∅ \\ A",
            "∅ \\ A = ∅",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::UnionCommutative(_) => bilingual_builtin(
            "UnionCommutative",
            "union commutative",
            "A ∪ B = B ∪ A",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IntersectCommutative(_) => bilingual_builtin(
            "IntersectCommutative",
            "intersect commutative",
            "A ∩ B = B ∩ A",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::UnionIdempotent(_) => bilingual_builtin(
            "UnionIdempotent",
            "A ∪ A",
            "A ∪ A = A",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IntersectIdempotent(_) => bilingual_builtin(
            "IntersectIdempotent",
            "A ∩ A",
            "A ∩ A = A",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IntersectFromSubset(_) => bilingual_builtin(
            "IntersectFromSubset",
            "intersect from subset",
            "A ⊆ B gives A ∩ B = A",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::EmptySetFromNotNonempty(_) => bilingual_builtin(
            "EmptySetFromNotNonempty",
            "empty from not nonempty",
            "¬$is_nonempty_set(A) gives A = ∅",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::PowerSetFiniteSetSize(_) => bilingual_builtin(
            "PowerSetFiniteSetSize",
            "|pow(A)|",
            "|pow(A)| = 2^|A| for finite A",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::UnionAssociative(_) => bilingual_builtin(
            "UnionAssociative",
            "union associative",
            "(A ∪ B) ∪ C = A ∪ (B ∪ C)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IntersectAssociative(_) => bilingual_builtin(
            "IntersectAssociative",
            "intersect associative",
            "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IntersectUnionDistributive(_) => bilingual_builtin(
            "IntersectUnionDistributive",
            "∩ distributes over ∪",
            "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SetMinusUnionDeMorgan(_) => bilingual_builtin(
            "SetMinusUnionDeMorgan",
            "\\ over ∪",
            "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SetMinusIntersectDeMorgan(_) => bilingual_builtin(
            "SetMinusIntersectDeMorgan",
            "\\ over ∩",
            "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IntersectSetMinusSelfEmpty(_) => bilingual_builtin(
            "IntersectSetMinusSelfEmpty",
            "A ∩ (A\\B)",
            "A ∩ (A \\ B) relates to emptiness / difference",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSumEmpty(_) => bilingual_builtin(
            "FiniteSetSumEmpty",
            "sum over ∅",
            "∑_{x∈∅} f(x) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetProductEmpty(_) => bilingual_builtin(
            "FiniteSetProductEmpty",
            "product over ∅",
            "∏_{x∈∅} f(x) = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetReduceEmpty(_) => bilingual_builtin(
            "FiniteSetReduceEmpty",
            "reduce over ∅",
            "reduce over the empty set is the unit",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ReduceEmpty(_) => bilingual_builtin(
            "ReduceEmpty",
            "reduce empty",
            "reduce on an empty range is the unit",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SumEmptyRange(_) => bilingual_builtin(
            "SumEmptyRange",
            "sum empty range",
            "∑ over an empty range is 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ProductEmptyRange(_) => bilingual_builtin(
            "ProductEmptyRange",
            "product empty range",
            "∏ over an empty range is 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::UnionAbsorptionFromSubset(_) => bilingual_builtin(
            "UnionAbsorptionFromSubset",
            "union absorption",
            "A ⊆ B gives A ∪ B = B",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SetMinusRecoversSubset(_) => bilingual_builtin(
            "SetMinusRecoversSubset",
            "difference recovers subset",
            "A ⊆ B gives B \\ (B \\ A) = A",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::EmptySetFromSizeZero(_) => bilingual_builtin(
            "EmptySetFromSizeZero",
            "empty from size 0",
            "|A| = 0 gives A = ∅",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::CartProjFactor(_) => bilingual_builtin(
            "CartProjFactor",
            "cart projection factor",
            "Projection recovers a Cartesian factor",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::TupleComponentAtIndex(_) => bilingual_builtin(
            "TupleComponentAtIndex",
            "tuple component",
            "The i-th component of a tuple equals the stated entry",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSizeSetMinus(_) => bilingual_builtin(
            "FiniteSetSizeSetMinus",
            "|A\\B|",
            "|A \\ B| = |A| − |A ∩ B| for finite sets",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSizeUnion(_) => bilingual_builtin(
            "FiniteSetSizeUnion",
            "|A∪B|",
            "|A ∪ B| = |A| + |B| − |A ∩ B|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ClosedRangeSingletonListSet(_) => bilingual_builtin(
            "ClosedRangeSingletonListSet",
            "closed range singleton",
            "{n..n} = {n}",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SumSingleTerm(_) => bilingual_builtin(
            "SumSingleTerm",
            "sum one term",
            "∑ with a single term equals that term",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ProductSingleTerm(_) => bilingual_builtin(
            "ProductSingleTerm",
            "product one term",
            "∏ with a single term equals that term",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ReduceAddZeroEqualsSum(_) => bilingual_builtin(
            "ReduceAddZeroEqualsSum",
            "reduce +0 as sum",
            "reduce with add and 0 equals a sum",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetReduceAddZeroEqualsSum(_) => bilingual_builtin(
            "FiniteSetReduceAddZeroEqualsSum",
            "finite-set reduce as sum",
            "finite-set reduce with + and 0 equals a sum",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::PowOfLogInverse(_) => bilingual_builtin(
            "PowOfLogInverse",
            "a^(log_a b)",
            "a^(log_a(b)) = b",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::UnionSetMinusDecomposition(_) => bilingual_builtin(
            "UnionSetMinusDecomposition",
            "union\\difference",
            "A ∪ B = A ∪ (B \\ A)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SetMinusIntersectSelf(_) => bilingual_builtin(
            "SetMinusIntersectSelf",
            "A \\ (A∩B)",
            "A \\ (A ∩ B) = A \\ B",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ReOfImaginaryUnit(_) => bilingual_builtin(
            "ReOfImaginaryUnit",
            "Re(i)",
            "Re(i) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ImgOfImaginaryUnit(_) => bilingual_builtin(
            "ImgOfImaginaryUnit",
            "Im(i)",
            "Im(i) = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ReOfRealEmbedding(_) => bilingual_builtin(
            "ReOfRealEmbedding",
            "Re of real",
            "Re(embed(x)) = x",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ImgOfRealEmbedding(_) => bilingual_builtin(
            "ImgOfRealEmbedding",
            "Im of real",
            "Im(embed(x)) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ReOfRealPlusI(_) => bilingual_builtin(
            "ReOfRealPlusI",
            "Re(x+i)",
            "Re(x + i) = x",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusI(_) => bilingual_builtin(
            "ImgOfRealPlusI",
            "Im(x+i)",
            "Im(x + i) = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ComplexAbsOfImaginaryUnit(_) => bilingual_builtin(
            "ComplexAbsOfImaginaryUnit",
            "|i|",
            "|i| = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ModNestedDivisibleAbsorption(_) => bilingual_builtin(
            "ModNestedDivisibleAbsorption",
            "nested mod absorption",
            "If n | m then (a mod m) mod n = a mod n",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SumSplitLastTerm(_) => bilingual_builtin(
            "SumSplitLastTerm",
            "sum split last",
            "Sum splits off its last term",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ProductSplitLastTerm(_) => bilingual_builtin(
            "ProductSplitLastTerm",
            "product split last",
            "Product splits off its last term",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSumListExpansion(_) => bilingual_builtin(
            "FiniteSetSumListExpansion",
            "finite-set sum expand",
            "Sum over a list-set expands to an explicit sum",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetProductListExpansion(_) => bilingual_builtin(
            "FiniteSetProductListExpansion",
            "finite-set product expand",
            "Product over a list-set expands to an explicit product",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::EulerEqualsExpOne(_) => bilingual_builtin(
            "EulerEqualsExpOne",
            "e = exp(1)",
            "e = exp(1)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LnOfEuler(_) => bilingual_builtin(
            "LnOfEuler",
            "ln(e)",
            "ln(e) = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ReOfReal(_) => bilingual_builtin(
            "ReOfReal",
            "Re(x) for real x",
            "Re(x) = x for real x",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ImgOfReal(_) => bilingual_builtin(
            "ImgOfReal",
            "Im(x) for real x",
            "Im(x) = 0 for real x",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ReOfRealPlusImagScaled(_) => bilingual_builtin(
            "ReOfRealPlusImagScaled",
            "Re(x+y·i)",
            "Re(x + y·i) = x",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusImagScaled(_) => bilingual_builtin(
            "ImgOfRealPlusImagScaled",
            "Im(x+y·i)",
            "Im(x + y·i) = y",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ComplexAbsOfNonnegReal(_) => bilingual_builtin(
            "ComplexAbsOfNonnegReal",
            "|x| for x≥0 real",
            "|embed(x)| = x for x ≥ 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ComplexAbsOfImagScaled(_) => bilingual_builtin(
            "ComplexAbsOfImagScaled",
            "|y·i|",
            "|y·i| = |y|",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ClosedRangeLiteralExpansion(_) => bilingual_builtin(
            "ClosedRangeLiteralExpansion",
            "closed range expand",
            "A numeric closed range expands to an explicit list set",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::RangeLiteralExpansion(_) => bilingual_builtin(
            "RangeLiteralExpansion",
            "range expand",
            "A numeric range expands to an explicit list set",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::PowerSetOfEmpty(_) => bilingual_builtin(
            "PowerSetOfEmpty",
            "pow(∅)",
            "pow(∅) = {∅}",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::PowerSetOfSingleton(_) => bilingual_builtin(
            "PowerSetOfSingleton",
            "pow({a})",
            "pow({a}) = {∅, {a}}",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FamilyUnionOfEmpty(_) => bilingual_builtin(
            "FamilyUnionOfEmpty",
            "⋃∅",
            "⋃∅ = ∅",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::CartWithEmptyFactor(_) => bilingual_builtin(
            "CartWithEmptyFactor",
            "A × ∅",
            "A × ∅ = ∅",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::UnionOverIntersectDistributive(_) => bilingual_builtin(
            "UnionOverIntersectDistributive",
            "∪ over ∩",
            "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SetMinusChainToUnion(_) => bilingual_builtin(
            "SetMinusChainToUnion",
            "chained difference",
            "A \\ B \\ C expands via union of removed sets",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FnRangeOfConstantAnonymousFn(_) => bilingual_builtin(
            "FnRangeOfConstantAnonymousFn",
            "range of constant fn",
            "Range of a constant anonymous function is a singleton",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SeqEqualsFnOnN(_) => bilingual_builtin(
            "SeqEqualsFnOnN",
            "seq as fn on N",
            "A sequence equals its function on N",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSeqEqualsFnOnClosedRange(_) => bilingual_builtin(
            "FiniteSeqEqualsFnOnClosedRange",
            "finite seq as fn",
            "A finite sequence equals its function on a closed range",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IndexUnionEmptyIndex(_) => bilingual_builtin(
            "IndexUnionEmptyIndex",
            "⋃_{i∈∅}",
            "Indexed union over an empty index is ∅",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IndexIntersectEmptyIndex(_) => bilingual_builtin(
            "IndexIntersectEmptyIndex",
            "⋂_{i∈∅}",
            "Indexed intersect over an empty index is the ambient universe convention used by Litex",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IndexCartEmptyIndex(_) => bilingual_builtin(
            "IndexCartEmptyIndex",
            "indexed cart empty",
            "Indexed Cartesian product over an empty index is a unit",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::IndexUnionSingleton(_) => bilingual_builtin(
            "IndexUnionSingleton",
            "⋃_{i∈{a}}",
            "Indexed union over a singleton index is the single set",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSeqZeroEqualsFnOnEmpty(_) => bilingual_builtin(
            "FiniteSeqZeroEqualsFnOnEmpty",
            "empty finite seq",
            "The length-0 finite sequence equals the function on the empty range",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SetBuilderObviouslyEmpty(_) => bilingual_builtin(
            "SetBuilderObviouslyEmpty",
            "empty set-builder",
            "A contradictory set-builder equals ∅",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ComplexAbsSquaredOfRectForm(_) => bilingual_builtin(
            "ComplexAbsSquaredOfRectForm",
            "|x+y i|²",
            "|x + y·i|² = x² + y²",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ExpOfSum(_) => bilingual_builtin(
            "ExpOfSum",
            "exp(x+y)",
            "exp(x+y) = exp(x)·exp(y)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::LogBasePower(_) => bilingual_builtin(
            "LogBasePower",
            "log_(a^n)(b)",
            "log_(a^n)(b) = (1/n)·log_a(b)",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ReOfProduct(_) => bilingual_builtin(
            "ReOfProduct",
            "Re(z·w)",
            "Re(z·w) expands from rectangular forms",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ImgOfProduct(_) => bilingual_builtin(
            "ImgOfProduct",
            "Im(z·w)",
            "Im(z·w) expands from rectangular forms",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SinOfSum(_) => bilingual_builtin(
            "SinOfSum",
            "sin(x+y)",
            "sin(x+y) = sin x cos y + cos x sin y",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::CosOfSum(_) => bilingual_builtin(
            "CosOfSum",
            "cos(x+y)",
            "cos(x+y) = cos x cos y − sin x sin y",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::ReduceSingleTermWithAddZero(_) => bilingual_builtin(
            "ReduceSingleTermWithAddZero",
            "reduce one term",
            "Reduce with a single term and +0 equals that term",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSumFubiniSwap(_) => bilingual_builtin(
            "FiniteSetSumFubiniSwap",
            "Fubini swap for sums",
            "Finite double sums may swap summation order",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSumOverCartesianProduct(_) => bilingual_builtin(
            "FiniteSetSumOverCartesianProduct",
            "sum over A×B",
            "Sum over a Cartesian product expands as an iterated sum",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SinOfZero(_) => bilingual_builtin(
            "SinOfZero",
            "sin 0",
            "sin(0) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::CosOfZero(_) => bilingual_builtin(
            "CosOfZero",
            "cos 0",
            "cos(0) = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::TanOfZero(_) => bilingual_builtin(
            "TanOfZero",
            "tan 0",
            "tan(0) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SinOfHalfPi(_) => bilingual_builtin(
            "SinOfHalfPi",
            "sin(π/2)",
            "sin(π/2) = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::CosOfPi(_) => bilingual_builtin(
            "CosOfPi",
            "cos(π)",
            "cos(π) = -1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::SinOfPi(_) => bilingual_builtin(
            "SinOfPi",
            "sin(π)",
            "sin(π) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::CotOfHalfPi(_) => bilingual_builtin(
            "CotOfHalfPi",
            "cot(π/2)",
            "cot(π/2) = 0",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
        EqualitySearchProofByBuiltinRule::PythagoreanIdentity(_) => bilingual_builtin(
            "PythagoreanIdentity",
            "sin²+cos²",
            "sin²(x) + cos²(x) = 1",
            None, // zh rule_name
            None, // zh message
            lang,
        ),
    }
}
