//! Fact and AtomicFact IR + display_string.

use super::types::FactIR;
use crate::new_pipeline::ast::fact::*;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::parse::keywords::*;

macro_rules! impl_display_pair {
    () => {
        pub fn display_string(&self) -> String {
            self.ir().display_string()
        }
    };
}

impl Fact {
    pub fn ir(&self) -> FactIR {
        match self {
            Fact::AtomicFact(x) => x.ir(),
            Fact::ExistFact(x) => x.ir(),
            Fact::OrFact(x) => x.ir(),
            Fact::AndFact(x) => x.ir(),
            Fact::ChainFact(x) => x.ir(),
            Fact::ForallFact(x) => x.ir(),
            Fact::ForallFactWithIff(x) => x.ir(),
            Fact::NotForall(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl AtomicFact {
    pub fn ir(&self) -> FactIR {
        match self {
            AtomicFact::NormalAtomicFact(x) => x.ir(),
            AtomicFact::EqualFact(x) => x.ir(),
            AtomicFact::LessFact(x) => x.ir(),
            AtomicFact::GreaterFact(x) => x.ir(),
            AtomicFact::LessEqualFact(x) => x.ir(),
            AtomicFact::GreaterEqualFact(x) => x.ir(),
            AtomicFact::IsSetFact(x) => x.ir(),
            AtomicFact::IsNonemptySetFact(x) => x.ir(),
            AtomicFact::IsFiniteSetFact(x) => x.ir(),
            AtomicFact::InFact(x) => x.ir(),
            AtomicFact::IsCartFact(x) => x.ir(),
            AtomicFact::IsTupleFact(x) => x.ir(),
            AtomicFact::SubsetFact(x) => x.ir(),
            AtomicFact::SupersetFact(x) => x.ir(),
            AtomicFact::NotNormalAtomicFact(x) => x.ir(),
            AtomicFact::NotEqualFact(x) => x.ir(),
            AtomicFact::NotLessFact(x) => x.ir(),
            AtomicFact::NotGreaterFact(x) => x.ir(),
            AtomicFact::NotLessEqualFact(x) => x.ir(),
            AtomicFact::NotGreaterEqualFact(x) => x.ir(),
            AtomicFact::NotIsSetFact(x) => x.ir(),
            AtomicFact::NotIsNonemptySetFact(x) => x.ir(),
            AtomicFact::NotIsFiniteSetFact(x) => x.ir(),
            AtomicFact::NotInFact(x) => x.ir(),
            AtomicFact::NotIsCartFact(x) => x.ir(),
            AtomicFact::NotIsTupleFact(x) => x.ir(),
            AtomicFact::NotSubsetFact(x) => x.ir(),
            AtomicFact::NotSupersetFact(x) => x.ir(),
            AtomicFact::FnEqualInFact(x) => x.ir(),
            AtomicFact::FnEqualFact(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl EqualFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {} {}",
            self.left.ir(),
            EQUAL,
            self.right.ir()
        ))
    }
    impl_display_pair!();
}

impl NotEqualFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {} {}",
            self.left.ir(),
            NOT_EQUAL,
            self.right.ir()
        ))
    }
    impl_display_pair!();
}

macro_rules! impl_bin_rel {
    ($ty:ty, $op:expr) => {
        impl $ty {
            pub fn ir(&self) -> FactIR {
                FactIR(format!(
                    "{} {} {}",
                    self.left.ir(),
                    $op,
                    self.right.ir()
                ))
            }
            impl_display_pair!();
        }
    };
}

macro_rules! impl_not_bin_rel {
    ($ty:ty, $op:expr) => {
        impl $ty {
            pub fn ir(&self) -> FactIR {
                FactIR(format!(
                    "{} {} {} {}",
                    NOT,
                    self.left.ir(),
                    $op,
                    self.right.ir()
                ))
            }
            impl_display_pair!();
        }
    };
}

impl_bin_rel!(LessFact, LESS);
impl_bin_rel!(GreaterFact, GREATER);
impl_bin_rel!(LessEqualFact, LESS_EQUAL);
impl_bin_rel!(GreaterEqualFact, GREATER_EQUAL);
impl_not_bin_rel!(NotLessFact, LESS);
impl_not_bin_rel!(NotGreaterFact, GREATER);
impl_not_bin_rel!(NotLessEqualFact, LESS_EQUAL);
impl_not_bin_rel!(NotGreaterEqualFact, GREATER_EQUAL);

impl InFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {}{} {}",
            self.element.ir(),
            FACT_PREFIX,
            IN,
            self.set.ir()
        ))
    }
    impl_display_pair!();
}

impl NotInFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {} {}{} {}",
            NOT,
            self.element.ir(),
            FACT_PREFIX,
            IN,
            self.set.ir()
        ))
    }
    impl_display_pair!();
}

macro_rules! impl_dollar_set_prop {
    ($ty:ty, $kw:expr) => {
        impl $ty {
            pub fn ir(&self) -> FactIR {
                FactIR(format!(
                    "{}{}{}{}{}",
                    FACT_PREFIX,
                    $kw,
                    LEFT_PAREN,
                    self.set.ir(),
                    RIGHT_PAREN
                ))
            }
            impl_display_pair!();
        }
    };
}

macro_rules! impl_not_dollar_set_prop {
    ($ty:ty, $kw:expr) => {
        impl $ty {
            pub fn ir(&self) -> FactIR {
                FactIR(format!(
                    "{} {}{}{}{}{}",
                    NOT,
                    FACT_PREFIX,
                    $kw,
                    LEFT_PAREN,
                    self.set.ir(),
                    RIGHT_PAREN
                ))
            }
            impl_display_pair!();
        }
    };
}

impl_dollar_set_prop!(IsSetFact, IS_SET);
impl_not_dollar_set_prop!(NotIsSetFact, IS_SET);
impl_dollar_set_prop!(IsNonemptySetFact, IS_NONEMPTY_SET);
impl_not_dollar_set_prop!(NotIsNonemptySetFact, IS_NONEMPTY_SET);
impl_dollar_set_prop!(IsFiniteSetFact, IS_FINITE_SET);
impl_not_dollar_set_prop!(NotIsFiniteSetFact, IS_FINITE_SET);
impl_dollar_set_prop!(IsCartFact, IS_CART);
impl_not_dollar_set_prop!(NotIsCartFact, IS_CART);
impl_dollar_set_prop!(IsTupleFact, IS_TUPLE);
impl_not_dollar_set_prop!(NotIsTupleFact, IS_TUPLE);

impl SubsetFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {}{} {}",
            self.left.ir(),
            FACT_PREFIX,
            SUBSET,
            self.right.ir()
        ))
    }
    impl_display_pair!();
}

impl NotSubsetFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {} {}{} {}",
            NOT,
            self.left.ir(),
            FACT_PREFIX,
            SUBSET,
            self.right.ir()
        ))
    }
    impl_display_pair!();
}

impl SupersetFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {}{} {}",
            self.left.ir(),
            FACT_PREFIX,
            SUPERSET,
            self.right.ir()
        ))
    }
    impl_display_pair!();
}

impl NotSupersetFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {} {}{} {}",
            NOT,
            self.left.ir(),
            FACT_PREFIX,
            SUPERSET,
            self.right.ir()
        ))
    }
    impl_display_pair!();
}

macro_rules! impl_normal_atomic {
    ($ty:ty, $negated:expr) => {
        impl $ty {
            pub fn ir(&self) -> FactIR {
                if let AtomicName::WithoutMod(name) = &self.predicate {
                    if self.body.len() == 2
                        && (name.as_str() == PROPER_SUBSET || name.as_str() == PROPER_SUPERSET)
                    {
                        let mut s = String::new();
                        if $negated {
                            s.push_str(NOT);
                            s.push(' ');
                        }
                        s.push_str(&self.body[0].ir());
                        s.push(' ');
                        s.push_str(FACT_PREFIX);
                        s.push_str(name);
                        s.push(' ');
                        s.push_str(&self.body[1].ir());
                        return FactIR(s);
                    }
                }
                let mut s = String::new();
                if $negated {
                    s.push_str(NOT);
                    s.push(' ');
                }
                s.push_str(FACT_PREFIX);
                s.push_str(&self.predicate.ir());
                let parts: Vec<_> = self
                    .body
                    .iter()
                    .map(|o| o.ir())
                    .collect();
                s.push_str(LEFT_PAREN);
                s.push_str(&parts.join(&format!("{} ", COMMA)));
                s.push_str(RIGHT_PAREN);
                FactIR(s)
            }
            impl_display_pair!();
        }
    };
}

impl_normal_atomic!(NormalAtomicFact, false);
impl_normal_atomic!(NotNormalAtomicFact, true);

impl FnEqualInFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{}{}{}{}{} {}{} {}{}",
            FACT_PREFIX,
            FN_EQ_IN,
            LEFT_PAREN,
            self.left.ir(),
            COMMA,
            self.right.ir(),
            COMMA,
            self.set.ir(),
            RIGHT_PAREN
        ))
    }
    impl_display_pair!();
}

impl FnEqualFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{}{}{}{}{} {}{}",
            FACT_PREFIX,
            FN_EQ,
            LEFT_PAREN,
            self.left.ir(),
            COMMA,
            self.right.ir(),
            RIGHT_PAREN
        ))
    }
    impl_display_pair!();
}

impl AndFact {
    pub fn ir(&self) -> FactIR {
        FactIR(
            self.facts
                .iter()
                .map(|f| f.ir())
                .collect::<Vec<_>>()
                .join(&format!(" {} ", AND)),
        )
    }
    impl_display_pair!();
}

impl OrFact {
    pub fn ir(&self) -> FactIR {
        FactIR(
            self.facts
                .iter()
                .map(|f| f.ir())
                .collect::<Vec<_>>()
                .join(&format!(" {} ", OR)),
        )
    }
    impl_display_pair!();
}

impl ChainFact {
    pub fn ir(&self) -> FactIR {
        let mut s = format!("{}", self.objs[0].ir());
        for (i, obj) in self.objs[1..].iter().enumerate() {
            let prop_s = self.prop_names[i].ir();
            if is_comparison_str(&prop_s) {
                s.push_str(&format!(" {} ", prop_s));
            } else {
                s.push_str(&format!(" {}{} ", FACT_PREFIX, prop_s));
            }
            s.push_str(&obj.ir());
        }
        FactIR(s)
    }
    impl_display_pair!();
}

impl ChainAtomicFact {
    pub fn ir(&self) -> FactIR {
        match self {
            ChainAtomicFact::AtomicFact(a) => a.ir(),
            ChainAtomicFact::ChainFact(c) => c.ir(),
        }
    }
    impl_display_pair!();
}

impl AndChainAtomicFact {
    pub fn ir(&self) -> FactIR {
        match self {
            AndChainAtomicFact::AtomicFact(a) => a.ir(),
            AndChainAtomicFact::AndFact(a) => a.ir(),
            AndChainAtomicFact::ChainFact(c) => c.ir(),
        }
    }
    impl_display_pair!();
}

impl QuantifierFreeFact {
    pub fn ir(&self) -> FactIR {
        match self {
            QuantifierFreeFact::AtomicFact(a) => a.ir(),
            QuantifierFreeFact::AndFact(a) => a.ir(),
            QuantifierFreeFact::ChainFact(c) => c.ir(),
            QuantifierFreeFact::OrFact(o) => o.ir(),
        }
    }
    impl_display_pair!();
}

impl ExistOrAndChainAtomicFact {
    pub fn ir(&self) -> FactIR {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(a) => a.ir(),
            ExistOrAndChainAtomicFact::AndFact(a) => a.ir(),
            ExistOrAndChainAtomicFact::ChainFact(c) => c.ir(),
            ExistOrAndChainAtomicFact::OrFact(o) => o.ir(),
            ExistOrAndChainAtomicFact::ExistFact(e) => e.ir(),
        }
    }
    impl_display_pair!();
}

impl PlainExistFact {
    pub fn ir(&self) -> FactIR {
        let parts: Vec<_> = self
            .facts
            .iter()
            .map(|fact| fact.ir())
            .collect();
        FactIR(format!(
            "{} {} {} {}{}{}",
            EXIST,
            self.typed_parameters.ir(),
            ST,
            LEFT_CURLY,
            parts.join(", "),
            RIGHT_CURLY
        ))
    }
    impl_display_pair!();
}

impl ExistFact {
    pub fn ir(&self) -> FactIR {
        let keyword = if matches!(self, ExistFact::NotExistFact(_)) {
            format!("{} {}", NOT, EXIST)
        } else if matches!(self, ExistFact::ExistUniqueFact(_)) {
            EXIST_BANG.to_string()
        } else {
            EXIST.to_string()
        };
        let body = match self {
            ExistFact::PlainExistFact(b)
            | ExistFact::ExistUniqueFact(b)
            | ExistFact::NotExistFact(b) => b,
        };
        let parts: Vec<_> = body
            .facts
            .iter()
            .map(|fact| fact.ir())
            .collect();
        FactIR(format!(
            "{} {} {} {}{}{}",
            keyword,
            body.typed_parameters.ir(),
            ST,
            LEFT_CURLY,
            parts.join(", "),
            RIGHT_CURLY
        ))
    }
    impl_display_pair!();
}

impl ForallFact {
    pub fn ir(&self) -> FactIR {
        let indent = |text: &str, n: usize| -> String {
            let prefix = "    ".repeat(n);
            text.split('\n')
                .map(|line| format!("{}{}", prefix, line))
                .collect::<Vec<_>>()
                .join("\n")
        };
        let mut s = format!(
            "{} {}{}",
            FORALL,
            self.typed_parameters.ir(),
            COLON
        );
        if self.dom_facts.is_empty() {
            s.push('\n');
            let then_parts: Vec<_> = self
                .then_facts
                .iter()
                .map(|t| t.ir())
                .collect();
            s.push_str(&indent(&then_parts.join("\n"), 1));
        } else {
            s.push('\n');
            let dom_parts: Vec<_> = self
                .dom_facts
                .iter()
                .map(|d| d.ir())
                .collect();
            s.push_str(&indent(&dom_parts.join("\n"), 1));
            s.push('\n');
            s.push_str(&indent(RIGHT_ARROW, 1));
            s.push_str(COLON);
            s.push('\n');
            let then_parts: Vec<_> = self
                .then_facts
                .iter()
                .map(|t| t.ir())
                .collect();
            s.push_str(&indent(&then_parts.join("\n"), 2));
        }
        FactIR(s)
    }
    impl_display_pair!();
}

impl ForallFactWithIff {
    pub fn ir(&self) -> FactIR {
        let indent = |text: &str, n: usize| -> String {
            let prefix = "    ".repeat(n);
            text.split('\n')
                .map(|line| format!("{}{}", prefix, line))
                .collect::<Vec<_>>()
                .join("\n")
        };
        let mut s = format!("{}", self.forall_fact.ir());
        s.push('\n');
        s.push_str(&indent(EQUIVALENT_SIGN, 1));
        s.push_str(COLON);
        s.push('\n');
        let iff_parts: Vec<_> = self
            .iff_facts
            .iter()
            .map(|t| t.ir())
            .collect();
        s.push_str(&indent(&iff_parts.join("\n"), 2));
        FactIR(s)
    }
    impl_display_pair!();
}

impl NotForallFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!("{} {}", NOT, self.forall_fact.ir()))
    }
    impl_display_pair!();
}
