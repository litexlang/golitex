//! Fact and AtomicFact IR + display_string.

use super::types::FactIR;
use crate::ast::fact::*;
use crate::ast::names::AtomicName;
use crate::parse::keywords::*;

macro_rules! impl_display_pair {
    () => {
        pub fn display_string(&self) -> String {
            self.ir().display_string()
        }

        // Human-facing: IR text with `#id#` wrappers stripped.
        pub fn readable_string(&self) -> String {
            crate::display_and_ir::readable_string_from_ir_text(
                self.ir().as_str(),
            )
        }
    };
}

impl Fact {
    pub fn ir(&self) -> FactIR {
        match self {
            Fact::AtomicFact(x) => x.ir(),
            Fact::ExistFact(x) => ExistShapedFact::Exist(x.clone()).ir(),
            Fact::ExistUniqueFact(x) => ExistShapedFact::ExistUnique(x.clone()).ir(),
            Fact::NotExistFact(x) => ExistShapedFact::NotExist(x.clone()).ir(),
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
            AtomicFact::SubsetFact(x) => x.ir(),
            AtomicFact::SupersetFact(x) => x.ir(),
            AtomicFact::ProperSubsetFact(x) => x.ir(),
            AtomicFact::ProperSupersetFact(x) => x.ir(),
            AtomicFact::PrimeFact(x) => x.ir(),
            AtomicFact::CoprimeFact(x) => x.ir(),
            AtomicFact::DvdFact(x) => x.ir(),
            AtomicFact::InjectiveFact(x) => x.ir(),
            AtomicFact::SurjectiveFact(x) => x.ir(),
            AtomicFact::BijectiveFact(x) => x.ir(),
            AtomicFact::IsChoiceFunctionForFact(x) => x.ir(),
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
            AtomicFact::NotSubsetFact(x) => x.ir(),
            AtomicFact::NotSupersetFact(x) => x.ir(),
            AtomicFact::NotProperSubsetFact(x) => x.ir(),
            AtomicFact::NotProperSupersetFact(x) => x.ir(),
            AtomicFact::NotPrimeFact(x) => x.ir(),
            AtomicFact::NotCoprimeFact(x) => x.ir(),
            AtomicFact::NotDvdFact(x) => x.ir(),
            AtomicFact::NotInjectiveFact(x) => x.ir(),
            AtomicFact::NotSurjectiveFact(x) => x.ir(),
            AtomicFact::NotBijectiveFact(x) => x.ir(),
            AtomicFact::NotIsChoiceFunctionForFact(x) => x.ir(),
        }
    }

    pub fn display_string(&self) -> String {
        match self {
            AtomicFact::NormalAtomicFact(x) => x.display_string(),
            AtomicFact::EqualFact(x) => x.display_string(),
            AtomicFact::LessFact(x) => x.display_string(),
            AtomicFact::GreaterFact(x) => x.display_string(),
            AtomicFact::LessEqualFact(x) => x.display_string(),
            AtomicFact::GreaterEqualFact(x) => x.display_string(),
            AtomicFact::IsSetFact(x) => x.display_string(),
            AtomicFact::IsNonemptySetFact(x) => x.display_string(),
            AtomicFact::IsFiniteSetFact(x) => x.display_string(),
            AtomicFact::InFact(x) => x.display_string(),
            AtomicFact::SubsetFact(x) => x.display_string(),
            AtomicFact::SupersetFact(x) => x.display_string(),
            AtomicFact::ProperSubsetFact(x) => x.display_string(),
            AtomicFact::ProperSupersetFact(x) => x.display_string(),
            AtomicFact::PrimeFact(x) => x.display_string(),
            AtomicFact::CoprimeFact(x) => x.display_string(),
            AtomicFact::DvdFact(x) => x.display_string(),
            AtomicFact::InjectiveFact(x) => x.display_string(),
            AtomicFact::SurjectiveFact(x) => x.display_string(),
            AtomicFact::BijectiveFact(x) => x.display_string(),
            AtomicFact::IsChoiceFunctionForFact(x) => x.display_string(),
            AtomicFact::NotNormalAtomicFact(x) => x.display_string(),
            AtomicFact::NotEqualFact(x) => x.display_string(),
            AtomicFact::NotLessFact(x) => x.display_string(),
            AtomicFact::NotGreaterFact(x) => x.display_string(),
            AtomicFact::NotLessEqualFact(x) => x.display_string(),
            AtomicFact::NotGreaterEqualFact(x) => x.display_string(),
            AtomicFact::NotIsSetFact(x) => x.display_string(),
            AtomicFact::NotIsNonemptySetFact(x) => x.display_string(),
            AtomicFact::NotIsFiniteSetFact(x) => x.display_string(),
            AtomicFact::NotInFact(x) => x.display_string(),
            AtomicFact::NotSubsetFact(x) => x.display_string(),
            AtomicFact::NotSupersetFact(x) => x.display_string(),
            AtomicFact::NotProperSubsetFact(x) => x.display_string(),
            AtomicFact::NotProperSupersetFact(x) => x.display_string(),
            AtomicFact::NotPrimeFact(x) => x.display_string(),
            AtomicFact::NotCoprimeFact(x) => x.display_string(),
            AtomicFact::NotDvdFact(x) => x.display_string(),
            AtomicFact::NotInjectiveFact(x) => x.display_string(),
            AtomicFact::NotSurjectiveFact(x) => x.display_string(),
            AtomicFact::NotBijectiveFact(x) => x.display_string(),
            AtomicFact::NotIsChoiceFunctionForFact(x) => x.display_string(),
        }
    }

    // Human-facing: IR text with `#id#` wrappers stripped.
    pub fn readable_string(&self) -> String {
        crate::display_and_ir::readable_string_from_ir_text(self.ir().as_str())
    }
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
    pub fn display_string(&self) -> String {
        format!(
            "{} {} {}",
            self.left.display_string(),
            EQUAL,
            self.right.display_string()
        )
    }
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
    pub fn display_string(&self) -> String {
        format!(
            "{} {} {}",
            self.left.display_string(),
            NOT_EQUAL,
            self.right.display_string()
        )
    }
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
            pub fn display_string(&self) -> String {
                format!(
                    "{} {} {}",
                    self.left.display_string(),
                    $op,
                    self.right.display_string()
                )
            }
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
            pub fn display_string(&self) -> String {
                format!(
                    "{} {} {} {}",
                    NOT,
                    self.left.display_string(),
                    $op,
                    self.right.display_string()
                )
            }
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
    pub fn display_string(&self) -> String {
        format!(
            "{} {}{} {}",
            self.element.display_string(),
            FACT_PREFIX,
            IN,
            self.set.display_string()
        )
    }
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
    pub fn display_string(&self) -> String {
        format!(
            "{} {} {}{} {}",
            NOT,
            self.element.display_string(),
            FACT_PREFIX,
            IN,
            self.set.display_string()
        )
    }
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
            pub fn display_string(&self) -> String {
                format!(
                    "{}{}{}{}{}",
                    FACT_PREFIX,
                    $kw,
                    LEFT_PAREN,
                    self.set.display_string(),
                    RIGHT_PAREN
                )
            }
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
            pub fn display_string(&self) -> String {
                format!(
                    "{} {}{}{}{}{}",
                    NOT,
                    FACT_PREFIX,
                    $kw,
                    LEFT_PAREN,
                    self.set.display_string(),
                    RIGHT_PAREN
                )
            }
        }
    };
}

impl_dollar_set_prop!(IsSetFact, IS_SET);
impl_not_dollar_set_prop!(NotIsSetFact, IS_SET);
impl_dollar_set_prop!(IsNonemptySetFact, IS_NONEMPTY_SET);
impl_not_dollar_set_prop!(NotIsNonemptySetFact, IS_NONEMPTY_SET);
impl_dollar_set_prop!(IsFiniteSetFact, IS_FINITE_SET);
impl_not_dollar_set_prop!(NotIsFiniteSetFact, IS_FINITE_SET);

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
    pub fn display_string(&self) -> String {
        format!(
            "{} {}{} {}",
            self.left.display_string(),
            FACT_PREFIX,
            SUBSET,
            self.right.display_string()
        )
    }
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
    pub fn display_string(&self) -> String {
        format!(
            "{} {} {}{} {}",
            NOT,
            self.left.display_string(),
            FACT_PREFIX,
            SUBSET,
            self.right.display_string()
        )
    }
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
    pub fn display_string(&self) -> String {
        format!(
            "{} {}{} {}",
            self.left.display_string(),
            FACT_PREFIX,
            SUPERSET,
            self.right.display_string()
        )
    }
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
    pub fn display_string(&self) -> String {
        format!(
            "{} {} {}{} {}",
            NOT,
            self.left.display_string(),
            FACT_PREFIX,
            SUPERSET,
            self.right.display_string()
        )
    }
}

impl ProperSubsetFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {}{} {}",
            self.left.ir(),
            FACT_PREFIX,
            PROPER_SUBSET,
            self.right.ir()
        ))
    }
    pub fn display_string(&self) -> String {
        format!(
            "{} {}{} {}",
            self.left.display_string(),
            FACT_PREFIX,
            PROPER_SUBSET,
            self.right.display_string()
        )
    }
}

impl NotProperSubsetFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {} {}{} {}",
            NOT,
            self.left.ir(),
            FACT_PREFIX,
            PROPER_SUBSET,
            self.right.ir()
        ))
    }
    pub fn display_string(&self) -> String {
        format!(
            "{} {} {}{} {}",
            NOT,
            self.left.display_string(),
            FACT_PREFIX,
            PROPER_SUBSET,
            self.right.display_string()
        )
    }
}

impl ProperSupersetFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {}{} {}",
            self.left.ir(),
            FACT_PREFIX,
            PROPER_SUPERSET,
            self.right.ir()
        ))
    }
    pub fn display_string(&self) -> String {
        format!(
            "{} {}{} {}",
            self.left.display_string(),
            FACT_PREFIX,
            PROPER_SUPERSET,
            self.right.display_string()
        )
    }
}

impl NotProperSupersetFact {
    pub fn ir(&self) -> FactIR {
        FactIR(format!(
            "{} {} {}{} {}",
            NOT,
            self.left.ir(),
            FACT_PREFIX,
            PROPER_SUPERSET,
            self.right.ir()
        ))
    }
    pub fn display_string(&self) -> String {
        format!(
            "{} {} {}{} {}",
            NOT,
            self.left.display_string(),
            FACT_PREFIX,
            PROPER_SUPERSET,
            self.right.display_string()
        )
    }
}

macro_rules! impl_dollar_prefix_args {
    ($ty:ty, $kw:expr, $($field:ident),+) => {
        impl $ty {
            pub fn ir(&self) -> FactIR {
                let parts = vec![$(self.$field.ir()),+];
                FactIR(format!(
                    "{}{}{}{}{}",
                    FACT_PREFIX,
                    $kw,
                    LEFT_PAREN,
                    parts.join(&format!("{} ", COMMA)),
                    RIGHT_PAREN
                ))
            }
            pub fn display_string(&self) -> String {
                let parts = vec![$(self.$field.display_string()),+];
                format!(
                    "{}{}{}{}{}",
                    FACT_PREFIX,
                    $kw,
                    LEFT_PAREN,
                    parts.join(&format!("{} ", COMMA)),
                    RIGHT_PAREN
                )
            }
        }
    };
}

macro_rules! impl_not_dollar_prefix_args {
    ($ty:ty, $kw:expr, $($field:ident),+) => {
        impl $ty {
            pub fn ir(&self) -> FactIR {
                let parts = vec![$(self.$field.ir()),+];
                FactIR(format!(
                    "{} {}{}{}{}{}",
                    NOT,
                    FACT_PREFIX,
                    $kw,
                    LEFT_PAREN,
                    parts.join(&format!("{} ", COMMA)),
                    RIGHT_PAREN
                ))
            }
            pub fn display_string(&self) -> String {
                let parts = vec![$(self.$field.display_string()),+];
                format!(
                    "{} {}{}{}{}{}",
                    NOT,
                    FACT_PREFIX,
                    $kw,
                    LEFT_PAREN,
                    parts.join(&format!("{} ", COMMA)),
                    RIGHT_PAREN
                )
            }
        }
    };
}

impl_dollar_prefix_args!(PrimeFact, PRIME, value);
impl_not_dollar_prefix_args!(NotPrimeFact, PRIME, value);
impl_dollar_prefix_args!(CoprimeFact, COPRIME, left, right);
impl_not_dollar_prefix_args!(NotCoprimeFact, COPRIME, left, right);
impl_dollar_prefix_args!(DvdFact, DVD, left, right);
impl_not_dollar_prefix_args!(NotDvdFact, DVD, left, right);
impl_dollar_prefix_args!(InjectiveFact, INJECTIVE, domain, codomain, function);
impl_not_dollar_prefix_args!(NotInjectiveFact, INJECTIVE, domain, codomain, function);
impl_dollar_prefix_args!(SurjectiveFact, SURJECTIVE, domain, codomain, function);
impl_not_dollar_prefix_args!(NotSurjectiveFact, SURJECTIVE, domain, codomain, function);
impl_dollar_prefix_args!(BijectiveFact, BIJECTIVE, domain, codomain, function);
impl_not_dollar_prefix_args!(NotBijectiveFact, BIJECTIVE, domain, codomain, function);
impl_dollar_prefix_args!(
    IsChoiceFunctionForFact,
    IS_CHOICE_FUNCTION_FOR,
    index,
    set,
    family,
    choice
);
impl_not_dollar_prefix_args!(
    NotIsChoiceFunctionForFact,
    IS_CHOICE_FUNCTION_FOR,
    index,
    set,
    family,
    choice
);

macro_rules! impl_normal_atomic {
    ($ty:ty, $negated:expr) => {
        impl $ty {
            pub fn ir(&self) -> FactIR {
                if let AtomicName::Plain { name } = &self.predicate {
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
                        s.push_str(name.as_str());
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
            pub fn display_string(&self) -> String {
                if let AtomicName::Plain { name } = &self.predicate {
                    if self.body.len() == 2
                        && (name.as_str() == PROPER_SUBSET || name.as_str() == PROPER_SUPERSET)
                    {
                        let mut s = String::new();
                        if $negated {
                            s.push_str(NOT);
                            s.push(' ');
                        }
                        s.push_str(&self.body[0].display_string());
                        s.push(' ');
                        s.push_str(FACT_PREFIX);
                        s.push_str(name.as_str());
                        s.push(' ');
                        s.push_str(&self.body[1].display_string());
                        return s;
                    }
                }
                let mut s = String::new();
                if $negated {
                    s.push_str(NOT);
                    s.push(' ');
                }
                s.push_str(FACT_PREFIX);
                s.push_str(&self.predicate.display_string());
                let parts: Vec<_> = self
                    .body
                    .iter()
                    .map(|o| o.display_string())
                    .collect();
                s.push_str(LEFT_PAREN);
                s.push_str(&parts.join(&format!("{} ", COMMA)));
                s.push_str(RIGHT_PAREN);
                s
            }
        }
    };
}

impl_normal_atomic!(NormalAtomicFact, false);
impl_normal_atomic!(NotNormalAtomicFact, true);



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
    pub fn display_string(&self) -> String {
        self.facts
            .iter()
            .map(|f| f.display_string())
            .collect::<Vec<_>>()
            .join(&format!(" {} ", AND))
    }
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
    pub fn display_string(&self) -> String {
        self.facts
            .iter()
            .map(|f| f.display_string())
            .collect::<Vec<_>>()
            .join(&format!(" {} ", OR))
    }
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
    pub fn display_string(&self) -> String {
        let mut s = format!("{}", self.objs[0].display_string());
        for (i, obj) in self.objs[1..].iter().enumerate() {
            let prop_s = self.prop_names[i].display_string();
            if is_comparison_str(&prop_s) {
                s.push_str(&format!(" {} ", prop_s));
            } else {
                s.push_str(&format!(" {}{} ", FACT_PREFIX, prop_s));
            }
            s.push_str(&obj.display_string());
        }
        s
    }
}

impl ChainAtomicFact {
    pub fn ir(&self) -> FactIR {
        match self {
            ChainAtomicFact::AtomicFact(a) => a.ir(),
            ChainAtomicFact::ChainFact(c) => c.ir(),
        }
    }
    pub fn display_string(&self) -> String {
        match self {
            ChainAtomicFact::AtomicFact(a) => a.display_string(),
            ChainAtomicFact::ChainFact(c) => c.display_string(),
        }
    }
}

impl AndChainAtomicFact {
    pub fn ir(&self) -> FactIR {
        match self {
            AndChainAtomicFact::AtomicFact(a) => a.ir(),
            AndChainAtomicFact::AndFact(a) => a.ir(),
            AndChainAtomicFact::ChainFact(c) => c.ir(),
        }
    }
    pub fn display_string(&self) -> String {
        match self {
            AndChainAtomicFact::AtomicFact(a) => a.display_string(),
            AndChainAtomicFact::AndFact(a) => a.display_string(),
            AndChainAtomicFact::ChainFact(c) => c.display_string(),
        }
    }
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
    pub fn display_string(&self) -> String {
        match self {
            QuantifierFreeFact::AtomicFact(a) => a.display_string(),
            QuantifierFreeFact::AndFact(a) => a.display_string(),
            QuantifierFreeFact::ChainFact(c) => c.display_string(),
            QuantifierFreeFact::OrFact(o) => o.display_string(),
        }
    }
}

impl ExistOrAndChainAtomicFact {
    pub fn ir(&self) -> FactIR {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(a) => a.ir(),
            ExistOrAndChainAtomicFact::AndFact(a) => a.ir(),
            ExistOrAndChainAtomicFact::ChainFact(c) => c.ir(),
            ExistOrAndChainAtomicFact::OrFact(o) => o.ir(),
            ExistOrAndChainAtomicFact::ExistFact(e) => ExistShapedFact::Exist(e.clone()).ir(),
            ExistOrAndChainAtomicFact::ExistUniqueFact(e) => {
                ExistShapedFact::ExistUnique(e.clone()).ir()
            }
            ExistOrAndChainAtomicFact::NotExistFact(e) => ExistShapedFact::NotExist(e.clone()).ir(),
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
    pub fn display_string(&self) -> String {
        let parts: Vec<_> = self
            .facts
            .iter()
            .map(|fact| fact.display_string())
            .collect();
        format!(
            "{} {} {} {}{}{}",
            EXIST,
            self.typed_parameters.display_string(),
            ST,
            LEFT_CURLY,
            parts.join(", "),
            RIGHT_CURLY
        )
    }
}

impl ExistShapedFact {
    pub fn ir(&self) -> FactIR {
        let keyword = if matches!(self, ExistShapedFact::NotExist(_)) {
            format!("{} {}", NOT, EXIST)
        } else if matches!(self, ExistShapedFact::ExistUnique(_)) {
            EXIST_BANG.to_string()
        } else {
            EXIST.to_string()
        };
        let body = match self {
            ExistShapedFact::Exist(b)
            | ExistShapedFact::ExistUnique(b)
            | ExistShapedFact::NotExist(b) => b,
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
    pub fn display_string(&self) -> String {
        let keyword = if matches!(self, ExistShapedFact::NotExist(_)) {
            format!("{} {}", NOT, EXIST)
        } else if matches!(self, ExistShapedFact::ExistUnique(_)) {
            EXIST_BANG.to_string()
        } else {
            EXIST.to_string()
        };
        let body = match self {
            ExistShapedFact::Exist(b)
            | ExistShapedFact::ExistUnique(b)
            | ExistShapedFact::NotExist(b) => b,
        };
        let parts: Vec<_> = body
            .facts
            .iter()
            .map(|fact| fact.display_string())
            .collect();
        format!(
            "{} {} {} {}{}{}",
            keyword,
            body.typed_parameters.display_string(),
            ST,
            LEFT_CURLY,
            parts.join(", "),
            RIGHT_CURLY
        )
    }
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
    pub fn display_string(&self) -> String {
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
            self.typed_parameters.display_string(),
            COLON
        );
        if self.dom_facts.is_empty() {
            s.push('\n');
            let then_parts: Vec<_> = self
                .then_facts
                .iter()
                .map(|t| t.display_string())
                .collect();
            s.push_str(&indent(&then_parts.join("\n"), 1));
        } else {
            s.push('\n');
            let dom_parts: Vec<_> = self
                .dom_facts
                .iter()
                .map(|d| d.display_string())
                .collect();
            s.push_str(&indent(&dom_parts.join("\n"), 1));
            s.push('\n');
            s.push_str(&indent(RIGHT_ARROW, 1));
            s.push_str(COLON);
            s.push('\n');
            let then_parts: Vec<_> = self
                .then_facts
                .iter()
                .map(|t| t.display_string())
                .collect();
            s.push_str(&indent(&then_parts.join("\n"), 2));
        }
        s
    }
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
        let mut s = if self.forall_fact.dom_facts.is_empty() {
            let then_parts: Vec<_> = self.forall_fact.then_facts.iter().map(|t| t.ir()).collect();
            format!(
                "{} {}{}\n{}{}\n{}",
                FORALL, self.forall_fact.typed_parameters.ir(), COLON,
                indent(RIGHT_ARROW, 1), COLON, indent(&then_parts.join("\n"), 2)
            )
        } else {
            format!("{}", self.forall_fact.ir())
        };
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
    pub fn display_string(&self) -> String {
        let indent = |text: &str, n: usize| -> String {
            let prefix = "    ".repeat(n);
            text.split('\n')
                .map(|line| format!("{}{}", prefix, line))
                .collect::<Vec<_>>()
                .join("\n")
        };
        let mut s = if self.forall_fact.dom_facts.is_empty() {
            let then_parts: Vec<_> = self.forall_fact.then_facts.iter().map(|t| t.display_string()).collect();
            format!(
                "{} {}{}\n{}{}\n{}",
                FORALL, self.forall_fact.typed_parameters.display_string(), COLON,
                indent(RIGHT_ARROW, 1), COLON, indent(&then_parts.join("\n"), 2)
            )
        } else {
            format!("{}", self.forall_fact.display_string())
        };
        s.push('\n');
        s.push_str(&indent(EQUIVALENT_SIGN, 1));
        s.push_str(COLON);
        s.push('\n');
        let iff_parts: Vec<_> = self
            .iff_facts
            .iter()
            .map(|t| t.display_string())
            .collect();
        s.push_str(&indent(&iff_parts.join("\n"), 2));
        s
    }
}

impl NotForallFact {
    pub fn ir(&self) -> FactIR {
        let indent = |text: &str, n: usize| -> String {
            let prefix = "    ".repeat(n);
            text.split('\n')
                .map(|line| format!("{}{}", prefix, line))
                .collect::<Vec<_>>()
                .join("\n")
        };
        let mut s = format!(
            "{} {} {}{}",
            NOT,
            FORALL,
            self.typed_parameters.ir(),
            COLON
        );
        if self.dom_facts.is_empty() {
            s.push('\n');
            let then_parts: Vec<_> = self.then_facts.iter().map(|t| t.ir()).collect();
            s.push_str(&indent(&then_parts.join("\n"), 1));
        } else {
            s.push('\n');
            let dom_parts: Vec<_> = self.dom_facts.iter().map(|d| d.ir()).collect();
            s.push_str(&indent(&dom_parts.join("\n"), 1));
            s.push('\n');
            s.push_str(&indent(RIGHT_ARROW, 1));
            s.push_str(COLON);
            s.push('\n');
            let then_parts: Vec<_> = self.then_facts.iter().map(|t| t.ir()).collect();
            s.push_str(&indent(&then_parts.join("\n"), 2));
        }
        FactIR(s)
    }
    pub fn display_string(&self) -> String {
        let indent = |text: &str, n: usize| -> String {
            let prefix = "    ".repeat(n);
            text.split('\n')
                .map(|line| format!("{}{}", prefix, line))
                .collect::<Vec<_>>()
                .join("\n")
        };
        let mut s = format!(
            "{} {} {}{}",
            NOT,
            FORALL,
            self.typed_parameters.display_string(),
            COLON
        );
        if self.dom_facts.is_empty() {
            s.push('\n');
            let then_parts: Vec<_> = self
                .then_facts
                .iter()
                .map(|t| t.display_string())
                .collect();
            s.push_str(&indent(&then_parts.join("\n"), 1));
        } else {
            s.push('\n');
            let dom_parts: Vec<_> = self
                .dom_facts
                .iter()
                .map(|d| d.display_string())
                .collect();
            s.push_str(&indent(&dom_parts.join("\n"), 1));
            s.push('\n');
            s.push_str(&indent(RIGHT_ARROW, 1));
            s.push_str(COLON);
            s.push('\n');
            let then_parts: Vec<_> = self
                .then_facts
                .iter()
                .map(|t| t.display_string())
                .collect();
            s.push_str(&indent(&then_parts.join("\n"), 2));
        }
        s
    }
}
