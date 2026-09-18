use crate::new_pipeline::ast::fact::{
    AtomicFact, FnEqualInFact, GreaterEqualFact, GreaterFact, InFact, IsCartFact,
    IsFiniteSetFact, IsNonemptySetFact, IsSetFact, IsTupleFact, LessEqualFact, LessFact,
    NormalAtomicFact, NotEqualFact, NotFnEqualInFact, NotGreaterEqualFact, NotGreaterFact,
    NotInFact, NotIsCartFact, NotIsFiniteSetFact, NotIsNonemptySetFact, NotIsSetFact,
    NotIsTupleFact, NotLessEqualFact, NotLessFact, NotNormalAtomicFact, NotSubsetFact,
    NotSupersetFact, SubsetFact, SupersetFact,
};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::fact::atomic_fact_args_ref;
use crate::new_pipeline::runtime::runtime_ids::FactId;

// Rebuild an atomic fact with the same shape and new argument list (same arity).
// EqualFact is rejected (equality uses its own rewrite path).
pub(super) fn atomic_fact_with_args(
    fact: &AtomicFact,
    args: Vec<Obj>,
    fact_id: FactId,
) -> Option<AtomicFact> {
    if args.len() != atomic_fact_args_ref(fact).len() {
        return None;
    }
    macro_rules! take2 {
        ($args:expr) => {{
            let mut it = $args.into_iter();
            (it.next().unwrap(), it.next().unwrap())
        }};
    }
    macro_rules! take3 {
        ($args:expr) => {{
            let mut it = $args.into_iter();
            (it.next().unwrap(), it.next().unwrap(), it.next().unwrap())
        }};
    }
    Some(match fact {
        AtomicFact::EqualFact(_) => return None,
        AtomicFact::NormalAtomicFact(f) => AtomicFact::NormalAtomicFact(NormalAtomicFact {
            fact_id,
            predicate: f.predicate.clone(),
            body: args,
            line_file: f.line_file.clone(),
        }),
        AtomicFact::NotNormalAtomicFact(f) => {
            AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact {
                fact_id,
                predicate: f.predicate.clone(),
                body: args,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotEqualFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotEqualFact(NotEqualFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::LessFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::LessFact(LessFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotLessFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotLessFact(NotLessFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::GreaterFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::GreaterFact(GreaterFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotGreaterFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotGreaterFact(NotGreaterFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::LessEqualFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::LessEqualFact(LessEqualFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotLessEqualFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotLessEqualFact(NotLessEqualFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::GreaterEqualFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::GreaterEqualFact(GreaterEqualFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotGreaterEqualFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::IsSetFact(f) => AtomicFact::IsSetFact(IsSetFact {
            fact_id,
            set: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::NotIsSetFact(f) => AtomicFact::NotIsSetFact(NotIsSetFact {
            fact_id,
            set: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::IsNonemptySetFact(f) => AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
            fact_id,
            set: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::NotIsNonemptySetFact(f) => {
            AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact {
                fact_id,
                set: args.into_iter().next().unwrap(),
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::IsFiniteSetFact(f) => AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id,
            set: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::NotIsFiniteSetFact(f) => AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact {
            fact_id,
            set: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::InFact(f) => {
            let (element, set) = take2!(args);
            AtomicFact::InFact(InFact {
                fact_id,
                element,
                set,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotInFact(f) => {
            let (element, set) = take2!(args);
            AtomicFact::NotInFact(NotInFact {
                fact_id,
                element,
                set,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::IsCartFact(f) => AtomicFact::IsCartFact(IsCartFact {
            fact_id,
            set: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::NotIsCartFact(f) => AtomicFact::NotIsCartFact(NotIsCartFact {
            fact_id,
            set: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::IsTupleFact(f) => AtomicFact::IsTupleFact(IsTupleFact {
            fact_id,
            set: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::NotIsTupleFact(f) => AtomicFact::NotIsTupleFact(NotIsTupleFact {
            fact_id,
            set: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::SubsetFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::SubsetFact(SubsetFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotSubsetFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotSubsetFact(NotSubsetFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::SupersetFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::SupersetFact(SupersetFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotSupersetFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotSupersetFact(NotSupersetFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::FnEqualInFact(f) => {
            let (left, right, set) = take3!(args);
            AtomicFact::FnEqualInFact(FnEqualInFact {
                fact_id,
                left,
                right,
                set,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotFnEqualInFact(f) => {
            let (left, right, set) = take3!(args);
            AtomicFact::NotFnEqualInFact(NotFnEqualInFact {
                fact_id,
                left,
                right,
                set,
                line_file: f.line_file.clone(),
            })
        }
    })
}
