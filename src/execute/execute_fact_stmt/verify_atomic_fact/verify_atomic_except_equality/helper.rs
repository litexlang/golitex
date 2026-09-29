use crate::ast::fact::{
    AtomicFact, BijectiveFact, CoprimeFact, DvdFact, GreaterEqualFact, GreaterFact, InFact,
    InjectiveFact, IsCartFact, IsChoiceFunctionForFact, IsFiniteSetFact, IsNonemptySetFact,
    IsSetFact, IsTupleFact, LessEqualFact, LessFact, NormalAtomicFact, NotBijectiveFact,
    NotCoprimeFact, NotDvdFact, NotEqualFact, NotGreaterEqualFact, NotGreaterFact, NotInFact,
    NotInjectiveFact, NotIsCartFact, NotIsChoiceFunctionForFact, NotIsFiniteSetFact,
    NotIsNonemptySetFact, NotIsSetFact, NotIsTupleFact, NotLessEqualFact, NotLessFact,
    NotNormalAtomicFact, NotPrimeFact, NotProperSubsetFact, NotProperSupersetFact, NotSubsetFact,
    NotSupersetFact, NotSurjectiveFact, PrimeFact, ProperSubsetFact, ProperSupersetFact,
    SubsetFact, SupersetFact, SurjectiveFact,
};
use crate::ast::obj::Obj;
use crate::ast::fact::atomic_fact_args_ref;
use crate::runtime::runtime_ids::FactId;

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
        AtomicFact::ProperSubsetFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::ProperSubsetFact(ProperSubsetFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotProperSubsetFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotProperSubsetFact(NotProperSubsetFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::ProperSupersetFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::ProperSupersetFact(ProperSupersetFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotProperSupersetFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotProperSupersetFact(NotProperSupersetFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::PrimeFact(f) => AtomicFact::PrimeFact(PrimeFact {
            fact_id,
            value: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::NotPrimeFact(f) => AtomicFact::NotPrimeFact(NotPrimeFact {
            fact_id,
            value: args.into_iter().next().unwrap(),
            line_file: f.line_file.clone(),
        }),
        AtomicFact::CoprimeFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::CoprimeFact(CoprimeFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotCoprimeFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotCoprimeFact(NotCoprimeFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::DvdFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::DvdFact(DvdFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotDvdFact(f) => {
            let (left, right) = take2!(args);
            AtomicFact::NotDvdFact(NotDvdFact {
                fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::InjectiveFact(f) => {
            let (domain, codomain, function) = take3!(args);
            AtomicFact::InjectiveFact(InjectiveFact {
                fact_id,
                domain,
                codomain,
                function,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotInjectiveFact(f) => {
            let (domain, codomain, function) = take3!(args);
            AtomicFact::NotInjectiveFact(NotInjectiveFact {
                fact_id,
                domain,
                codomain,
                function,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::SurjectiveFact(f) => {
            let (domain, codomain, function) = take3!(args);
            AtomicFact::SurjectiveFact(SurjectiveFact {
                fact_id,
                domain,
                codomain,
                function,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotSurjectiveFact(f) => {
            let (domain, codomain, function) = take3!(args);
            AtomicFact::NotSurjectiveFact(NotSurjectiveFact {
                fact_id,
                domain,
                codomain,
                function,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::BijectiveFact(f) => {
            let (domain, codomain, function) = take3!(args);
            AtomicFact::BijectiveFact(BijectiveFact {
                fact_id,
                domain,
                codomain,
                function,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotBijectiveFact(f) => {
            let (domain, codomain, function) = take3!(args);
            AtomicFact::NotBijectiveFact(NotBijectiveFact {
                fact_id,
                domain,
                codomain,
                function,
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::IsChoiceFunctionForFact(f) => {
            let mut it = args.into_iter();
            AtomicFact::IsChoiceFunctionForFact(IsChoiceFunctionForFact {
                fact_id,
                index: it.next().unwrap(),
                set: it.next().unwrap(),
                family: it.next().unwrap(),
                choice: it.next().unwrap(),
                line_file: f.line_file.clone(),
            })
        }
        AtomicFact::NotIsChoiceFunctionForFact(f) => {
            let mut it = args.into_iter();
            AtomicFact::NotIsChoiceFunctionForFact(NotIsChoiceFunctionForFact {
                fact_id,
                index: it.next().unwrap(),
                set: it.next().unwrap(),
                family: it.next().unwrap(),
                choice: it.next().unwrap(),
                line_file: f.line_file.clone(),
            })
        }
    })
}
