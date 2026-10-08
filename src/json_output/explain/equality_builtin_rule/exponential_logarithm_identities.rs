use crate::json_output::explain::BuiltinRuleText;
use crate::json_output::explain::text::text;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_exponential_logarithm_identities::ExponentialLogarithmIdentityProof;

impl ExponentialLogarithmIdentityProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::ExpDifference(_) => text(
                "Exponential difference",
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
            ),
            Self::LnProduct(_) => text("Logarithm of a product", "a,b $in R+: ln(a*b)=ln(a)+ln(b)"),
            Self::LnQuotient(_) => {
                text("Logarithm of a quotient", "a,b $in R+: ln(a/b)=ln(a)-ln(b)")
            }
            Self::ExpInjective(_) => text(
                "Injectivity of real exponential",
                "x,y $in R: exp(x)=exp(y) => x=y",
            ),
            Self::LnInjective(_) => text(
                "Injectivity of positive logarithm",
                "x,y $in R+: ln(x)=ln(y) => x=y",
            ),
            Self::LogFromKnownPower(_) => text(
                "Logarithm from a known integer power",
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
            ),
            Self::PowerFromKnownLog(_) => text(
                "Integer power from a known logarithm",
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
            ),
        }
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::ExpDifference(_) => text("指数差公式", "a,b $in R: exp(a-b)=exp(a)/exp(b)"),
            Self::LnProduct(_) => text("自然对数乘积公式", "a,b $in R+: ln(a*b)=ln(a)+ln(b)"),
            Self::LnQuotient(_) => text("自然对数商公式", "a,b $in R+: ln(a/b)=ln(a)-ln(b)"),
            Self::ExpInjective(_) => text("实指数函数单射", "x,y $in R: exp(x)=exp(y) => x=y"),
            Self::LnInjective(_) => text("正实数自然对数单射", "x,y $in R+: ln(x)=ln(y) => x=y"),
            Self::LogFromKnownPower(_) => text(
                "由已知整数幂得到对数",
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
            ),
            Self::PowerFromKnownLog(_) => text(
                "由已知对数得到整数幂",
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
            ),
        }
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::ExpDifference(_) => text("指数差公式", "a,b $in R: exp(a-b)=exp(a)/exp(b)"),
            Self::LnProduct(_) => text("自然对数乘积公式", "a,b $in R+: ln(a*b)=ln(a)+ln(b)"),
            Self::LnQuotient(_) => text("自然对数商公式", "a,b $in R+: ln(a/b)=ln(a)-ln(b)"),
            Self::ExpInjective(_) => text("实指数函数单射", "x,y $in R: exp(x)=exp(y) => x=y"),
            Self::LnInjective(_) => text("正实数自然对数单射", "x,y $in R+: ln(x)=ln(y) => x=y"),
            Self::LogFromKnownPower(_) => text(
                "由已知整数幂得到对数",
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
            ),
            Self::PowerFromKnownLog(_) => text(
                "由已知对数得到整数幂",
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
            ),
        }
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::ExpDifference(_) => text(
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
            ),
            Self::LnProduct(_) => text(
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
            ),
            Self::LnQuotient(_) => text(
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
            ),
            Self::ExpInjective(_) => text(
                "x,y $in R: exp(x)=exp(y) => x=y",
                "x,y $in R: exp(x)=exp(y) => x=y",
            ),
            Self::LnInjective(_) => text(
                "x,y $in R+: ln(x)=ln(y) => x=y",
                "x,y $in R+: ln(x)=ln(y) => x=y",
            ),
            Self::LogFromKnownPower(_) => text(
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
            ),
            Self::PowerFromKnownLog(_) => text(
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
            ),
        }
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::ExpDifference(_) => text(
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
            ),
            Self::LnProduct(_) => text(
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
            ),
            Self::LnQuotient(_) => text(
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
            ),
            Self::ExpInjective(_) => text(
                "x,y $in R: exp(x)=exp(y) => x=y",
                "x,y $in R: exp(x)=exp(y) => x=y",
            ),
            Self::LnInjective(_) => text(
                "x,y $in R+: ln(x)=ln(y) => x=y",
                "x,y $in R+: ln(x)=ln(y) => x=y",
            ),
            Self::LogFromKnownPower(_) => text(
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
            ),
            Self::PowerFromKnownLog(_) => text(
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
            ),
        }
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::ExpDifference(_) => text(
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
            ),
            Self::LnProduct(_) => text(
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
            ),
            Self::LnQuotient(_) => text(
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
            ),
            Self::ExpInjective(_) => text(
                "x,y $in R: exp(x)=exp(y) => x=y",
                "x,y $in R: exp(x)=exp(y) => x=y",
            ),
            Self::LnInjective(_) => text(
                "x,y $in R+: ln(x)=ln(y) => x=y",
                "x,y $in R+: ln(x)=ln(y) => x=y",
            ),
            Self::LogFromKnownPower(_) => text(
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
            ),
            Self::PowerFromKnownLog(_) => text(
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
            ),
        }
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::ExpDifference(_) => text(
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
            ),
            Self::LnProduct(_) => text(
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
            ),
            Self::LnQuotient(_) => text(
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
            ),
            Self::ExpInjective(_) => text(
                "x,y $in R: exp(x)=exp(y) => x=y",
                "x,y $in R: exp(x)=exp(y) => x=y",
            ),
            Self::LnInjective(_) => text(
                "x,y $in R+: ln(x)=ln(y) => x=y",
                "x,y $in R+: ln(x)=ln(y) => x=y",
            ),
            Self::LogFromKnownPower(_) => text(
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
            ),
            Self::PowerFromKnownLog(_) => text(
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
            ),
        }
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::ExpDifference(_) => text(
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
            ),
            Self::LnProduct(_) => text(
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
            ),
            Self::LnQuotient(_) => text(
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
            ),
            Self::ExpInjective(_) => text(
                "x,y $in R: exp(x)=exp(y) => x=y",
                "x,y $in R: exp(x)=exp(y) => x=y",
            ),
            Self::LnInjective(_) => text(
                "x,y $in R+: ln(x)=ln(y) => x=y",
                "x,y $in R+: ln(x)=ln(y) => x=y",
            ),
            Self::LogFromKnownPower(_) => text(
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
            ),
            Self::PowerFromKnownLog(_) => text(
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
            ),
        }
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::ExpDifference(_) => text(
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
            ),
            Self::LnProduct(_) => text(
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
            ),
            Self::LnQuotient(_) => text(
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
            ),
            Self::ExpInjective(_) => text(
                "x,y $in R: exp(x)=exp(y) => x=y",
                "x,y $in R: exp(x)=exp(y) => x=y",
            ),
            Self::LnInjective(_) => text(
                "x,y $in R+: ln(x)=ln(y) => x=y",
                "x,y $in R+: ln(x)=ln(y) => x=y",
            ),
            Self::LogFromKnownPower(_) => text(
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
            ),
            Self::PowerFromKnownLog(_) => text(
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
            ),
        }
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::ExpDifference(_) => text(
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
                "a,b $in R: exp(a-b)=exp(a)/exp(b)",
            ),
            Self::LnProduct(_) => text(
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
                "a,b $in R+: ln(a*b)=ln(a)+ln(b)",
            ),
            Self::LnQuotient(_) => text(
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
                "a,b $in R+: ln(a/b)=ln(a)-ln(b)",
            ),
            Self::ExpInjective(_) => text(
                "x,y $in R: exp(x)=exp(y) => x=y",
                "x,y $in R: exp(x)=exp(y) => x=y",
            ),
            Self::LnInjective(_) => text(
                "x,y $in R+: ln(x)=ln(y) => x=y",
                "x,y $in R+: ln(x)=ln(y) => x=y",
            ),
            Self::LogFromKnownPower(_) => text(
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
                "a,x $in R+, a!=1, n $in Z, a^n=x => log(a,x)=n",
            ),
            Self::PowerFromKnownLog(_) => text(
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
                "a,x $in R+, a!=1, n $in Z, log(a,x)=n => a^n=x",
            ),
        }
    }
}
