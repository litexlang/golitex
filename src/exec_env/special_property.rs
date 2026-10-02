use crate::ast::fact::{AtomicFact, EqualFact, InFact};
use crate::ast::obj::{FnSet, FunctionSpace, Obj};
use crate::exec_env::{ExecEnv, ObjIR};
use crate::runtime::FactId;

/// An index of stored facts, independent of the statement that introduced them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecialProperty {
    Membership(InFact),
    Equality(EqualFact),
    /// Field names need a selected view, in addition to mathematical membership.
    DefaultStructView(InFact),
}

impl SpecialProperty {
    pub fn fact_id(&self) -> FactId {
        match self {
            Self::Membership(fact) | Self::DefaultStructView(fact) => fact.fact_id,
            Self::Equality(fact) => fact.fact_id,
        }
    }

    pub fn function_signature(&self) -> Option<FnSet> {
        match self {
            Self::Membership(fact) => match &fact.set {
                Obj::FunctionSpace(FunctionSpace::FnSet(signature)) => Some(signature.clone()),
                _ => None,
            },
            Self::Equality(fact) => {
                for side in [&fact.left, &fact.right] {
                    match side {
                        Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => {
                            return Some(function.body.clone());
                        }
                        // Preserve the existing signature-alias callable contract.
                        Obj::FunctionSpace(FunctionSpace::FnSet(signature)) => {
                            return Some(signature.clone());
                        }
                        _ => {}
                    }
                }
                None
            }
            Self::DefaultStructView(_) => None,
        }
    }

    pub fn function_subject(&self) -> Option<&Obj> {
        match self {
            Self::Membership(fact)
                if matches!(&fact.set, Obj::FunctionSpace(FunctionSpace::FnSet(_))) =>
            {
                Some(&fact.element)
            }
            Self::Equality(fact) => {
                if matches!(
                    &fact.left,
                    Obj::FunctionSpace(FunctionSpace::FnSet(_) | FunctionSpace::AnonymousFn(_))
                ) {
                    Some(&fact.right)
                } else if matches!(
                    &fact.right,
                    Obj::FunctionSpace(FunctionSpace::FnSet(_) | FunctionSpace::AnonymousFn(_))
                ) {
                    Some(&fact.left)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl ExecEnv {
    pub(crate) fn index_special_property(&mut self, fact: &AtomicFact) {
        match fact {
            AtomicFact::InFact(fact) => {
                self.record_special_property(
                    fact.element.ir(),
                    SpecialProperty::Membership(fact.clone()),
                );
            }
            AtomicFact::EqualFact(fact) => {
                self.record_special_property(
                    fact.left.ir(),
                    SpecialProperty::Equality(fact.clone()),
                );
                self.record_special_property(
                    fact.right.ir(),
                    SpecialProperty::Equality(fact.clone()),
                );
            }
            _ => {}
        }
    }

    pub(crate) fn record_special_property(&mut self, key: ObjIR, property: SpecialProperty) {
        let properties = self.special_properties.entry(key).or_default();
        if !properties.contains(&property) {
            properties.push(property);
        }
    }
}
