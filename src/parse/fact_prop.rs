//! Map `$prop(...)` / infix `$prop` names onto AtomicFact variants.

use crate::ast::fact::{
    AtomicFact, BijectiveFact, CoprimeFact, DvdFact, EqualFact, GreaterEqualFact, GreaterFact,
    InFact, InjectiveFact, IsCartFact, IsChoiceFunctionForFact, IsFiniteSetFact, IsNonemptySetFact,
    IsSetFact, IsTupleFact, LessEqualFact, LessFact, NormalAtomicFact, NotBijectiveFact,
    NotCoprimeFact, NotDvdFact, NotEqualFact, NotGreaterEqualFact, NotGreaterFact, NotInFact,
    NotInjectiveFact, NotIsCartFact, NotIsChoiceFunctionForFact, NotIsFiniteSetFact,
    NotIsNonemptySetFact, NotIsSetFact, NotIsTupleFact, NotLessEqualFact, NotLessFact,
    NotNormalAtomicFact, NotPrimeFact, NotProperSubsetFact, NotProperSupersetFact, NotSubsetFact,
    NotSupersetFact, NotSurjectiveFact, PrimeFact, ProperSubsetFact, ProperSupersetFact,
    SubsetFact, SupersetFact, SurjectiveFact,
};
use crate::ast::line_file::SourceLine;
use crate::ast::names::AtomicName;
use crate::ast::obj::Obj;
use crate::parse::keywords::{
    BIJECTIVE, COPRIME, DVD, EQUAL, GREATER, GREATER_EQUAL, IN, INJECTIVE, IS_CHOICE_FUNCTION_FOR,
    LESS, LESS_EQUAL, NOT_EQUAL, PRIME, SURJECTIVE,
};
use crate::runtime::{FactId, Runtime, RuntimeParseError, RuntimeResult};

pub const IS_SET: &str = "is_set";
pub const IS_NONEMPTY_SET: &str = "is_nonempty_set";
pub const IS_FINITE_SET: &str = "is_finite_set";
pub const IS_CART: &str = "is_cart";
pub const IS_TUPLE: &str = "is_tuple";
pub const SUBSET: &str = "subset";
pub const SUPERSET: &str = "superset";
pub const PROPER_SUBSET: &str = "proper_subset";
pub const PROPER_SUPERSET: &str = "proper_superset";
pub const FN_EQ: &str = "fn_eq";
pub const FN_EQ_IN: &str = "fn_eq_in";

pub fn is_infix_prop_name(name: &str) -> bool {
    matches!(
        name,
        IN | SUBSET
            | SUPERSET
            | PROPER_SUBSET
            | PROPER_SUPERSET
            | EQUAL
            | NOT_EQUAL
            | LESS
            | GREATER
            | LESS_EQUAL
            | GREATER_EQUAL
    )
}

impl Runtime {
    pub(crate) fn atomic_from_prop(
        &mut self,
        prop: AtomicName,
        args: Vec<Obj>,
        positive: bool,
        line_file: SourceLine,
    ) -> RuntimeResult<AtomicFact> {
        let name = match &prop {
            AtomicName::Plain { name } => name.as_str(),
            AtomicName::WithExportFileId { .. } | AtomicName::WithModAndExportFileId { .. } => {
                return Ok(normal_or_not(
                    self.global_ids.allocate_fact_id(),
                    prop,
                    args,
                    positive,
                    line_file,
                ));
            }
        };

        match name {
            EQUAL | NOT_EQUAL | LESS | GREATER | LESS_EQUAL | GREATER_EQUAL => {
                two_args(self, name, &args, line_file.line)?;
                build_binary_compare(
                    self,
                    name,
                    args[0].clone(),
                    args[1].clone(),
                    positive,
                    line_file,
                )
            }
            IN => {
                two_args(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::InFact(InFact {
                        fact_id,
                        element: args[0].clone(),
                        set: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotInFact(NotInFact {
                        fact_id,
                        element: args[0].clone(),
                        set: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            SUBSET => {
                two_args(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::SubsetFact(SubsetFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotSubsetFact(NotSubsetFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            SUPERSET => {
                two_args(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::SupersetFact(SupersetFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotSupersetFact(NotSupersetFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            IS_SET => {
                one_arg(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::IsSetFact(IsSetFact {
                        fact_id,
                        set: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotIsSetFact(NotIsSetFact {
                        fact_id,
                        set: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            IS_NONEMPTY_SET => {
                one_arg(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                        fact_id,
                        set: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact {
                        fact_id,
                        set: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            IS_FINITE_SET => {
                one_arg(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
                        fact_id,
                        set: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact {
                        fact_id,
                        set: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            IS_CART => {
                one_arg(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::IsCartFact(IsCartFact {
                        fact_id,
                        set: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotIsCartFact(NotIsCartFact {
                        fact_id,
                        set: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            IS_TUPLE => {
                one_arg(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::IsTupleFact(IsTupleFact {
                        fact_id,
                        set: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotIsTupleFact(NotIsTupleFact {
                        fact_id,
                        set: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            FN_EQ | FN_EQ_IN => {
                return Err(RuntimeParseError::new(
                    format!(
                        "`${name}` is removed; use ordinary equality `f = g` or `by fn_extension` / `forall` for pointwise agreement"
                    ),
                    line_file.line,
                    self.current_file.clone(),
                )
                .into());
            }
            PROPER_SUBSET => {
                two_args(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::ProperSubsetFact(ProperSubsetFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotProperSubsetFact(NotProperSubsetFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            PROPER_SUPERSET => {
                two_args(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::ProperSupersetFact(ProperSupersetFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotProperSupersetFact(NotProperSupersetFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            PRIME => {
                one_arg(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::PrimeFact(PrimeFact {
                        fact_id,
                        value: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotPrimeFact(NotPrimeFact {
                        fact_id,
                        value: args[0].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            COPRIME => {
                two_args(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::CoprimeFact(CoprimeFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotCoprimeFact(NotCoprimeFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            DVD => {
                two_args(self, name, &args, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::DvdFact(DvdFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotDvdFact(NotDvdFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            INJECTIVE => {
                n_args(self, name, &args, 3, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::InjectiveFact(InjectiveFact {
                        fact_id,
                        domain: args[0].clone(),
                        codomain: args[1].clone(),
                        function: args[2].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotInjectiveFact(NotInjectiveFact {
                        fact_id,
                        domain: args[0].clone(),
                        codomain: args[1].clone(),
                        function: args[2].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            SURJECTIVE => {
                n_args(self, name, &args, 3, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::SurjectiveFact(SurjectiveFact {
                        fact_id,
                        domain: args[0].clone(),
                        codomain: args[1].clone(),
                        function: args[2].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotSurjectiveFact(NotSurjectiveFact {
                        fact_id,
                        domain: args[0].clone(),
                        codomain: args[1].clone(),
                        function: args[2].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            BIJECTIVE => {
                n_args(self, name, &args, 3, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::BijectiveFact(BijectiveFact {
                        fact_id,
                        domain: args[0].clone(),
                        codomain: args[1].clone(),
                        function: args[2].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotBijectiveFact(NotBijectiveFact {
                        fact_id,
                        domain: args[0].clone(),
                        codomain: args[1].clone(),
                        function: args[2].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            IS_CHOICE_FUNCTION_FOR => {
                n_args(self, name, &args, 4, line_file.line)?;
                let fact_id = self.global_ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::IsChoiceFunctionForFact(IsChoiceFunctionForFact {
                        fact_id,
                        index: args[0].clone(),
                        set: args[1].clone(),
                        family: args[2].clone(),
                        choice: args[3].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotIsChoiceFunctionForFact(
                        NotIsChoiceFunctionForFact {
                            fact_id,
                            index: args[0].clone(),
                            set: args[1].clone(),
                            family: args[2].clone(),
                            choice: args[3].clone(),
                            line_file: Some(line_file),
                        },
                    ))
                }
            }
            _ => Ok(normal_or_not(
                self.global_ids.allocate_fact_id(),
                prop,
                args,
                positive,
                line_file,
            )),
        }
    }
}

fn n_args(rt: &Runtime, name: &str, args: &[Obj], expected: usize, line: usize) -> RuntimeResult<()> {
    if args.len() != expected {
        return Err(RuntimeParseError::new(
            format!("`{name}` requires {expected} arguments, got {}", args.len()),
            line,
            rt.current_file.clone(),
        )
        .into());
    }
    Ok(())
}

fn normal_or_not(
    fact_id: FactId,
    predicate: AtomicName,
    body: Vec<Obj>,
    positive: bool,
    line_file: SourceLine,
) -> AtomicFact {
    if positive {
        AtomicFact::NormalAtomicFact(NormalAtomicFact {
            fact_id,
            predicate,
            body,
            line_file: Some(line_file),
        })
    } else {
        AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact {
            fact_id,
            predicate,
            body,
            line_file: Some(line_file),
        })
    }
}

fn one_arg(rt: &Runtime, name: &str, args: &[Obj], line: usize) -> RuntimeResult<()> {
    if args.len() != 1 {
        return Err(RuntimeParseError::new(
            format!("`{name}` requires 1 argument, got {}", args.len()),
            line,
            rt.current_file.clone(),
        )
        .into());
    }
    Ok(())
}

fn two_args(rt: &Runtime, name: &str, args: &[Obj], line: usize) -> RuntimeResult<()> {
    if args.len() != 2 {
        return Err(RuntimeParseError::new(
            format!("`{name}` requires 2 arguments, got {}", args.len()),
            line,
            rt.current_file.clone(),
        )
        .into());
    }
    Ok(())
}

fn build_binary_compare(
    rt: &mut Runtime,
    op: &str,
    left: Obj,
    right: Obj,
    positive: bool,
    line_file: SourceLine,
) -> RuntimeResult<AtomicFact> {
    let fact_id = rt.global_ids.allocate_fact_id();
    Ok(match (op, positive) {
        (EQUAL, true) => AtomicFact::EqualFact(EqualFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (EQUAL, false) => AtomicFact::NotEqualFact(NotEqualFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (NOT_EQUAL, true) => AtomicFact::NotEqualFact(NotEqualFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (NOT_EQUAL, false) => AtomicFact::EqualFact(EqualFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (LESS, true) => AtomicFact::LessFact(LessFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (LESS, false) => AtomicFact::NotLessFact(NotLessFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (GREATER, true) => AtomicFact::GreaterFact(GreaterFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (GREATER, false) => AtomicFact::NotGreaterFact(NotGreaterFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (LESS_EQUAL, true) => AtomicFact::LessEqualFact(LessEqualFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (LESS_EQUAL, false) => AtomicFact::NotLessEqualFact(NotLessEqualFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (GREATER_EQUAL, true) => AtomicFact::GreaterEqualFact(GreaterEqualFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        (GREATER_EQUAL, false) => AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact {
            fact_id,
            left,
            right,
            line_file: Some(line_file),
        }),
        _ => {
            return Err(RuntimeParseError::new(
                format!("unknown comparison `{op}`"),
                line_file.line,
                rt.current_file.clone(),
            )
            .into());
        }
    })
}
