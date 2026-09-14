//! Fact and AtomicFact internal representation + display_string.

use super::helper::strip_identifier_id_tags;
use crate::new_pipeline::ast::fact::*;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::parse::keywords::*;

macro_rules! impl_display_pair {
    () => {
        pub fn display_string(&self) -> String {
            strip_identifier_id_tags(&self.internal_representation())
        }
    };
}

impl Fact {
    pub fn internal_representation(&self) -> String {
        match self {
            Fact::AtomicFact(x) => x.internal_representation(),
            Fact::ExistFact(x) => x.internal_representation(),
            Fact::OrFact(x) => x.internal_representation(),
            Fact::AndFact(x) => x.internal_representation(),
            Fact::ChainFact(x) => x.internal_representation(),
            Fact::ForallFact(x) => x.internal_representation(),
            Fact::ForallFactWithIff(x) => x.internal_representation(),
            Fact::NotForall(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl AtomicFact {
    pub fn internal_representation(&self) -> String {
        match self {
            AtomicFact::NormalAtomicFact(x) => x.internal_representation(),
            AtomicFact::EqualFact(x) => x.internal_representation(),
            AtomicFact::LessFact(x) => x.internal_representation(),
            AtomicFact::GreaterFact(x) => x.internal_representation(),
            AtomicFact::LessEqualFact(x) => x.internal_representation(),
            AtomicFact::GreaterEqualFact(x) => x.internal_representation(),
            AtomicFact::IsSetFact(x) => x.internal_representation(),
            AtomicFact::IsNonemptySetFact(x) => x.internal_representation(),
            AtomicFact::IsFiniteSetFact(x) => x.internal_representation(),
            AtomicFact::InFact(x) => x.internal_representation(),
            AtomicFact::IsCartFact(x) => x.internal_representation(),
            AtomicFact::IsTupleFact(x) => x.internal_representation(),
            AtomicFact::SubsetFact(x) => x.internal_representation(),
            AtomicFact::SupersetFact(x) => x.internal_representation(),
            AtomicFact::NotNormalAtomicFact(x) => x.internal_representation(),
            AtomicFact::NotEqualFact(x) => x.internal_representation(),
            AtomicFact::NotLessFact(x) => x.internal_representation(),
            AtomicFact::NotGreaterFact(x) => x.internal_representation(),
            AtomicFact::NotLessEqualFact(x) => x.internal_representation(),
            AtomicFact::NotGreaterEqualFact(x) => x.internal_representation(),
            AtomicFact::NotIsSetFact(x) => x.internal_representation(),
            AtomicFact::NotIsNonemptySetFact(x) => x.internal_representation(),
            AtomicFact::NotIsFiniteSetFact(x) => x.internal_representation(),
            AtomicFact::NotInFact(x) => x.internal_representation(),
            AtomicFact::NotIsCartFact(x) => x.internal_representation(),
            AtomicFact::NotIsTupleFact(x) => x.internal_representation(),
            AtomicFact::NotSubsetFact(x) => x.internal_representation(),
            AtomicFact::NotSupersetFact(x) => x.internal_representation(),
            AtomicFact::FnEqualInFact(x) => x.internal_representation(),
            AtomicFact::FnEqualFact(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl EqualFact {
    pub fn internal_representation(&self) -> String {
        format!(
            "{} {} {}",
            self.left.internal_representation(),
            EQUAL,
            self.right.internal_representation()
        )
    }
    impl_display_pair!();
}

impl NotEqualFact {
    pub fn internal_representation(&self) -> String {
        format!(
            "{} {} {}",
            self.left.internal_representation(),
            NOT_EQUAL,
            self.right.internal_representation()
        )
    }
    impl_display_pair!();
}

macro_rules! impl_bin_rel {
    ($ty:ty, $op:expr) => {
        impl $ty {
            pub fn internal_representation(&self) -> String {
                format!(
                    "{} {} {}",
                    self.left.internal_representation(),
                    $op,
                    self.right.internal_representation()
                )
            }
            impl_display_pair!();
        }
    };
}

macro_rules! impl_not_bin_rel {
    ($ty:ty, $op:expr) => {
        impl $ty {
            pub fn internal_representation(&self) -> String {
                format!(
                    "{} {} {} {}",
                    NOT,
                    self.left.internal_representation(),
                    $op,
                    self.right.internal_representation()
                )
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
    pub fn internal_representation(&self) -> String {
        format!(
            "{} {}{} {}",
            self.element.internal_representation(),
            FACT_PREFIX,
            IN,
            self.set.internal_representation()
        )
    }
    impl_display_pair!();
}

impl NotInFact {
    pub fn internal_representation(&self) -> String {
        format!(
            "{} {} {}{} {}",
            NOT,
            self.element.internal_representation(),
            FACT_PREFIX,
            IN,
            self.set.internal_representation()
        )
    }
    impl_display_pair!();
}

macro_rules! impl_dollar_set_prop {
    ($ty:ty, $kw:expr) => {
        impl $ty {
            pub fn internal_representation(&self) -> String {
                format!(
                    "{}{}{}{}{}",
                    FACT_PREFIX,
                    $kw,
                    LEFT_PAREN,
                    self.set.internal_representation(),
                    RIGHT_PAREN
                )
            }
            impl_display_pair!();
        }
    };
}

macro_rules! impl_not_dollar_set_prop {
    ($ty:ty, $kw:expr) => {
        impl $ty {
            pub fn internal_representation(&self) -> String {
                format!(
                    "{} {}{}{}{}{}",
                    NOT,
                    FACT_PREFIX,
                    $kw,
                    LEFT_PAREN,
                    self.set.internal_representation(),
                    RIGHT_PAREN
                )
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
    pub fn internal_representation(&self) -> String {
        format!(
            "{} {}{} {}",
            self.left.internal_representation(),
            FACT_PREFIX,
            SUBSET,
            self.right.internal_representation()
        )
    }
    impl_display_pair!();
}

impl NotSubsetFact {
    pub fn internal_representation(&self) -> String {
        format!(
            "{} {} {}{} {}",
            NOT,
            self.left.internal_representation(),
            FACT_PREFIX,
            SUBSET,
            self.right.internal_representation()
        )
    }
    impl_display_pair!();
}

impl SupersetFact {
    pub fn internal_representation(&self) -> String {
        format!(
            "{} {}{} {}",
            self.left.internal_representation(),
            FACT_PREFIX,
            SUPERSET,
            self.right.internal_representation()
        )
    }
    impl_display_pair!();
}

impl NotSupersetFact {
    pub fn internal_representation(&self) -> String {
        format!(
            "{} {} {}{} {}",
            NOT,
            self.left.internal_representation(),
            FACT_PREFIX,
            SUPERSET,
            self.right.internal_representation()
        )
    }
    impl_display_pair!();
}

macro_rules! impl_normal_atomic {
    ($ty:ty, $negated:expr) => {
        impl $ty {
            pub fn internal_representation(&self) -> String {
                if let AtomicName::WithoutMod(name) = &self.predicate {
                    if self.body.len() == 2
                        && (name.as_str() == PROPER_SUBSET || name.as_str() == PROPER_SUPERSET)
                    {
                        let mut s = String::new();
                        if $negated {
                            s.push_str(NOT);
                            s.push(' ');
                        }
                        s.push_str(&self.body[0].internal_representation());
                        s.push(' ');
                        s.push_str(FACT_PREFIX);
                        s.push_str(name);
                        s.push(' ');
                        s.push_str(&self.body[1].internal_representation());
                        return s;
                    }
                }
                let mut s = String::new();
                if $negated {
                    s.push_str(NOT);
                    s.push(' ');
                }
                s.push_str(FACT_PREFIX);
                s.push_str(&self.predicate.internal_representation());
                let parts: Vec<String> = self
                    .body
                    .iter()
                    .map(|o| o.internal_representation())
                    .collect();
                s.push_str(LEFT_PAREN);
                s.push_str(&parts.join(&format!("{} ", COMMA)));
                s.push_str(RIGHT_PAREN);
                s
            }
            impl_display_pair!();
        }
    };
}

impl_normal_atomic!(NormalAtomicFact, false);
impl_normal_atomic!(NotNormalAtomicFact, true);

impl FnEqualInFact {
    pub fn internal_representation(&self) -> String {
        format!(
            "{}{}{}{}{} {}{} {}{}",
            FACT_PREFIX,
            FN_EQ_IN,
            LEFT_PAREN,
            self.left.internal_representation(),
            COMMA,
            self.right.internal_representation(),
            COMMA,
            self.set.internal_representation(),
            RIGHT_PAREN
        )
    }
    impl_display_pair!();
}

impl FnEqualFact {
    pub fn internal_representation(&self) -> String {
        format!(
            "{}{}{}{}{} {}{}",
            FACT_PREFIX,
            FN_EQ,
            LEFT_PAREN,
            self.left.internal_representation(),
            COMMA,
            self.right.internal_representation(),
            RIGHT_PAREN
        )
    }
    impl_display_pair!();
}

impl AndFact {
    pub fn internal_representation(&self) -> String {
        self.facts
            .iter()
            .map(|f| f.internal_representation())
            .collect::<Vec<_>>()
            .join(&format!(" {} ", AND))
    }
    impl_display_pair!();
}

impl OrFact {
    pub fn internal_representation(&self) -> String {
        self.facts
            .iter()
            .map(|f| f.internal_representation())
            .collect::<Vec<_>>()
            .join(&format!(" {} ", OR))
    }
    impl_display_pair!();
}

impl ChainFact {
    pub fn internal_representation(&self) -> String {
        let mut s = self.objs[0].internal_representation();
        for (i, obj) in self.objs[1..].iter().enumerate() {
            let prop_s = self.prop_names[i].internal_representation();
            if is_comparison_str(&prop_s) {
                s.push_str(&format!(" {} ", prop_s));
            } else {
                s.push_str(&format!(" {}{} ", FACT_PREFIX, prop_s));
            }
            s.push_str(&obj.internal_representation());
        }
        s
    }
    impl_display_pair!();
}

impl ChainAtomicFact {
    pub fn internal_representation(&self) -> String {
        match self {
            ChainAtomicFact::AtomicFact(a) => a.internal_representation(),
            ChainAtomicFact::ChainFact(c) => c.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl AndChainAtomicFact {
    pub fn internal_representation(&self) -> String {
        match self {
            AndChainAtomicFact::AtomicFact(a) => a.internal_representation(),
            AndChainAtomicFact::AndFact(a) => a.internal_representation(),
            AndChainAtomicFact::ChainFact(c) => c.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl QuantifierFreeFact {
    pub fn internal_representation(&self) -> String {
        match self {
            QuantifierFreeFact::AtomicFact(a) => a.internal_representation(),
            QuantifierFreeFact::AndFact(a) => a.internal_representation(),
            QuantifierFreeFact::ChainFact(c) => c.internal_representation(),
            QuantifierFreeFact::OrFact(o) => o.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl ExistOrAndChainAtomicFact {
    pub fn internal_representation(&self) -> String {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(a) => a.internal_representation(),
            ExistOrAndChainAtomicFact::AndFact(a) => a.internal_representation(),
            ExistOrAndChainAtomicFact::ChainFact(c) => c.internal_representation(),
            ExistOrAndChainAtomicFact::OrFact(o) => o.internal_representation(),
            ExistOrAndChainAtomicFact::ExistFact(e) => e.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl PlainExistFact {
    pub fn internal_representation(&self) -> String {
        let parts: Vec<String> = self
            .facts
            .iter()
            .map(|fact| fact.internal_representation())
            .collect();
        format!(
            "{} {} {} {}{}{}",
            EXIST,
            self.typed_parameters.internal_representation(),
            ST,
            LEFT_CURLY,
            parts.join(", "),
            RIGHT_CURLY
        )
    }
    impl_display_pair!();
}

impl ExistFact {
    pub fn internal_representation(&self) -> String {
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
        let parts: Vec<String> = body
            .facts
            .iter()
            .map(|fact| fact.internal_representation())
            .collect();
        format!(
            "{} {} {} {}{}{}",
            keyword,
            body.typed_parameters.internal_representation(),
            ST,
            LEFT_CURLY,
            parts.join(", "),
            RIGHT_CURLY
        )
    }
    impl_display_pair!();
}

impl ForallFact {
    pub fn internal_representation(&self) -> String {
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
            self.typed_parameters.internal_representation(),
            COLON
        );
        if self.dom_facts.is_empty() {
            s.push('\n');
            let then_parts: Vec<String> = self
                .then_facts
                .iter()
                .map(|t| t.internal_representation())
                .collect();
            s.push_str(&indent(&then_parts.join("\n"), 1));
        } else {
            s.push('\n');
            let dom_parts: Vec<String> = self
                .dom_facts
                .iter()
                .map(|d| d.internal_representation())
                .collect();
            s.push_str(&indent(&dom_parts.join("\n"), 1));
            s.push('\n');
            s.push_str(&indent(RIGHT_ARROW, 1));
            s.push_str(COLON);
            s.push('\n');
            let then_parts: Vec<String> = self
                .then_facts
                .iter()
                .map(|t| t.internal_representation())
                .collect();
            s.push_str(&indent(&then_parts.join("\n"), 2));
        }
        s
    }
    impl_display_pair!();
}

impl ForallFactWithIff {
    pub fn internal_representation(&self) -> String {
        let indent = |text: &str, n: usize| -> String {
            let prefix = "    ".repeat(n);
            text.split('\n')
                .map(|line| format!("{}{}", prefix, line))
                .collect::<Vec<_>>()
                .join("\n")
        };
        let mut s = self.forall_fact.internal_representation();
        s.push('\n');
        s.push_str(&indent(EQUIVALENT_SIGN, 1));
        s.push_str(COLON);
        s.push('\n');
        let iff_parts: Vec<String> = self
            .iff_facts
            .iter()
            .map(|t| t.internal_representation())
            .collect();
        s.push_str(&indent(&iff_parts.join("\n"), 2));
        s
    }
    impl_display_pair!();
}

impl NotForallFact {
    pub fn internal_representation(&self) -> String {
        format!("{} {}", NOT, self.forall_fact.internal_representation())
    }
    impl_display_pair!();
}
