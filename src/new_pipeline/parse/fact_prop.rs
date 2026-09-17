//! Map `$prop(...)` / infix `$prop` names onto AtomicFact variants.

use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, FnEqualInFact, GreaterEqualFact, GreaterFact, InFact, IsCartFact,
    IsFiniteSetFact, IsNonemptySetFact, IsSetFact, IsTupleFact, LessEqualFact, LessFact,
    NormalAtomicFact, NotEqualFact, NotFnEqualInFact, NotGreaterEqualFact, NotGreaterFact,
    NotInFact, NotIsCartFact, NotIsFiniteSetFact, NotIsNonemptySetFact, NotIsSetFact,
    NotIsTupleFact, NotLessEqualFact, NotLessFact, NotNormalAtomicFact, NotSubsetFact,
    NotSupersetFact, SubsetFact, SupersetFact,
};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::parse::keywords::{
    EQUAL, GREATER, GREATER_EQUAL, IN, LESS, LESS_EQUAL, NOT_EQUAL,
};
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeParseError, RuntimeResult};

pub const IS_SET: &str = "is_set";
pub const IS_NONEMPTY_SET: &str = "is_nonempty_set";
pub const IS_FINITE_SET: &str = "is_finite_set";
pub const IS_CART: &str = "is_cart";
pub const IS_TUPLE: &str = "is_tuple";
pub const SUBSET: &str = "subset";
pub const SUPERSET: &str = "superset";
pub const FN_EQ: &str = "fn_eq";
pub const FN_EQ_IN: &str = "fn_eq_in";

pub fn is_infix_prop_name(name: &str) -> bool {
    matches!(
        name,
        IN | SUBSET
            | SUPERSET
            | EQUAL
            | NOT_EQUAL
            | LESS
            | GREATER
            | LESS_EQUAL
            | GREATER_EQUAL
            | FN_EQ_IN
    )
}

impl Runtime {
    pub(crate) fn atomic_from_prop(
        &mut self,
        prop: AtomicName,
        args: Vec<Obj>,
        positive: bool,
        line_file: LineFile,
    ) -> RuntimeResult<AtomicFact> {
        let name = match &prop {
            AtomicName::Plain { name } => name.as_str(),
            AtomicName::WithExportFileId { .. } | AtomicName::WithModAndExportFileId { .. } => {
                return Ok(normal_or_not(
                    self.ids.allocate_fact_id(),
                    prop,
                    args,
                    positive,
                    line_file,
                ));
            }
        };

        match name {
            EQUAL | NOT_EQUAL | LESS | GREATER | LESS_EQUAL | GREATER_EQUAL => {
                two_args(name, &args, &line_file)?;
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
                two_args(name, &args, &line_file)?;
                let fact_id = self.ids.allocate_fact_id();
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
                two_args(name, &args, &line_file)?;
                let fact_id = self.ids.allocate_fact_id();
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
                two_args(name, &args, &line_file)?;
                let fact_id = self.ids.allocate_fact_id();
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
                one_arg(name, &args, &line_file)?;
                let fact_id = self.ids.allocate_fact_id();
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
                one_arg(name, &args, &line_file)?;
                let fact_id = self.ids.allocate_fact_id();
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
                one_arg(name, &args, &line_file)?;
                let fact_id = self.ids.allocate_fact_id();
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
                one_arg(name, &args, &line_file)?;
                let fact_id = self.ids.allocate_fact_id();
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
                one_arg(name, &args, &line_file)?;
                let fact_id = self.ids.allocate_fact_id();
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
            FN_EQ => {
                return Err(RuntimeParseError::new(
                    "`$fn_eq` is removed; use ordinary equality `f = g` or `$fn_eq_in`",
                    line_file.line,
                    line_file.path.clone(),
                )
                .into());
            }
            FN_EQ_IN => {
                if args.len() != 3 {
                    return Err(RuntimeParseError::new(
                        format!("`{name}` requires 3 arguments, got {}", args.len()),
                        line_file.line,
                        line_file.path.clone(),
                    )
                    .into());
                }
                let fact_id = self.ids.allocate_fact_id();
                if positive {
                    Ok(AtomicFact::FnEqualInFact(FnEqualInFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        set: args[2].clone(),
                        line_file: Some(line_file),
                    }))
                } else {
                    Ok(AtomicFact::NotFnEqualInFact(NotFnEqualInFact {
                        fact_id,
                        left: args[0].clone(),
                        right: args[1].clone(),
                        set: args[2].clone(),
                        line_file: Some(line_file),
                    }))
                }
            }
            _ => Ok(normal_or_not(
                self.ids.allocate_fact_id(),
                prop,
                args,
                positive,
                line_file,
            )),
        }
    }
}

fn normal_or_not(
    fact_id: FactId,
    predicate: AtomicName,
    body: Vec<Obj>,
    positive: bool,
    line_file: LineFile,
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

fn one_arg(name: &str, args: &[Obj], line_file: &LineFile) -> RuntimeResult<()> {
    if args.len() != 1 {
        return Err(RuntimeParseError::new(
            format!("`{name}` requires 1 argument, got {}", args.len()),
            line_file.line,
            line_file.path.clone(),
        )
        .into());
    }
    Ok(())
}

fn two_args(name: &str, args: &[Obj], line_file: &LineFile) -> RuntimeResult<()> {
    if args.len() != 2 {
        return Err(RuntimeParseError::new(
            format!("`{name}` requires 2 arguments, got {}", args.len()),
            line_file.line,
            line_file.path.clone(),
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
    line_file: LineFile,
) -> RuntimeResult<AtomicFact> {
    let fact_id = rt.ids.allocate_fact_id();
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
                line_file.path.clone(),
            )
            .into());
        }
    })
}
