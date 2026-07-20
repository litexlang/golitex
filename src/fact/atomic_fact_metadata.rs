use crate::prelude::*;

impl AtomicFact {
    pub fn is_builtin_predicate_and_return_expected_args_len(&self) -> usize {
        match self {
            AtomicFact::EqualFact(_) => 2,
            AtomicFact::LessFact(_) => 2,
            AtomicFact::GreaterFact(_) => 2,
            AtomicFact::LessEqualFact(_) => 2,
            AtomicFact::GreaterEqualFact(_) => 2,
            AtomicFact::IsSetFact(_) => 1,
            AtomicFact::IsNonemptySetFact(_) => 1,
            AtomicFact::IsFiniteSetFact(_) => 1,
            AtomicFact::InFact(_) => 2,
            AtomicFact::IsCartFact(_) => 1,
            AtomicFact::IsTupleFact(_) => 1,
            AtomicFact::SubsetFact(_) => 2,
            AtomicFact::SupersetFact(_) => 2,
            AtomicFact::NotEqualFact(_) => 2,
            AtomicFact::NotLessFact(_) => 2,
            AtomicFact::NotGreaterFact(_) => 2,
            AtomicFact::NotLessEqualFact(_) => 2,
            AtomicFact::NotGreaterEqualFact(_) => 2,
            AtomicFact::NotIsSetFact(_) => 1,
            AtomicFact::NotIsNonemptySetFact(_) => 1,
            AtomicFact::NotIsFiniteSetFact(_) => 1,
            AtomicFact::NotInFact(_) => 2,
            AtomicFact::NotIsCartFact(_) => 1,
            AtomicFact::NotIsTupleFact(_) => 1,
            AtomicFact::NotSubsetFact(_) => 2,
            AtomicFact::NotSupersetFact(_) => 2,
            AtomicFact::FnEqualInFact(_) => 3,
            AtomicFact::FnEqualFact(_) => 2,
            AtomicFact::NormalAtomicFact(a)
                if matches!(
                    a.predicate.to_string().as_str(),
                    INJECTIVE | SURJECTIVE | BIJECTIVE
                ) =>
            {
                3
            }
            AtomicFact::NotNormalAtomicFact(a)
                if matches!(
                    a.predicate.to_string().as_str(),
                    INJECTIVE | SURJECTIVE | BIJECTIVE
                ) =>
            {
                3
            }
            AtomicFact::NormalAtomicFact(a)
                if matches!(
                    a.predicate.to_string().as_str(),
                    PROPER_SUBSET | PROPER_SUPERSET
                ) =>
            {
                2
            }
            AtomicFact::NotNormalAtomicFact(a)
                if matches!(
                    a.predicate.to_string().as_str(),
                    PROPER_SUBSET | PROPER_SUPERSET
                ) =>
            {
                2
            }
            _ => unreachable!("other cases are not builtin predicates"),
        }
    }

    pub fn number_of_args(&self) -> usize {
        match self {
            AtomicFact::EqualFact(_) => 2,
            AtomicFact::LessFact(_) => 2,
            AtomicFact::GreaterFact(_) => 2,
            AtomicFact::LessEqualFact(_) => 2,
            AtomicFact::GreaterEqualFact(_) => 2,
            AtomicFact::IsSetFact(_) => 1,
            AtomicFact::IsNonemptySetFact(_) => 1,
            AtomicFact::IsFiniteSetFact(_) => 1,
            AtomicFact::InFact(_) => 2,
            AtomicFact::IsCartFact(_) => 1,
            AtomicFact::IsTupleFact(_) => 1,
            AtomicFact::SubsetFact(_) => 2,
            AtomicFact::SupersetFact(_) => 2,
            AtomicFact::NotEqualFact(_) => 2,
            AtomicFact::NotLessFact(_) => 2,
            AtomicFact::NotGreaterFact(_) => 2,
            AtomicFact::NotLessEqualFact(_) => 2,
            AtomicFact::NotGreaterEqualFact(_) => 2,
            AtomicFact::NotIsSetFact(_) => 1,
            AtomicFact::NotIsNonemptySetFact(_) => 1,
            AtomicFact::NotIsFiniteSetFact(_) => 1,
            AtomicFact::NotInFact(_) => 2,
            AtomicFact::NotIsCartFact(_) => 1,
            AtomicFact::NotIsTupleFact(_) => 1,
            AtomicFact::NotSubsetFact(_) => 2,
            AtomicFact::NotSupersetFact(_) => 2,
            AtomicFact::NormalAtomicFact(a) => a.body.len(),
            AtomicFact::NotNormalAtomicFact(a) => a.body.len(),
            AtomicFact::FnEqualInFact(_) => 3,
            AtomicFact::FnEqualFact(_) => 2,
        }
    }

    pub fn line_file(&self) -> LineFile {
        match self {
            AtomicFact::EqualFact(a) => a.line_file.clone(),
            AtomicFact::LessFact(a) => a.line_file.clone(),
            AtomicFact::GreaterFact(a) => a.line_file.clone(),
            AtomicFact::LessEqualFact(a) => a.line_file.clone(),
            AtomicFact::GreaterEqualFact(a) => a.line_file.clone(),
            AtomicFact::IsSetFact(a) => a.line_file.clone(),
            AtomicFact::IsNonemptySetFact(a) => a.line_file.clone(),
            AtomicFact::IsFiniteSetFact(a) => a.line_file.clone(),
            AtomicFact::InFact(a) => a.line_file.clone(),
            AtomicFact::IsCartFact(a) => a.line_file.clone(),
            AtomicFact::IsTupleFact(a) => a.line_file.clone(),
            AtomicFact::SubsetFact(a) => a.line_file.clone(),
            AtomicFact::SupersetFact(a) => a.line_file.clone(),
            AtomicFact::NormalAtomicFact(a) => a.line_file.clone(),
            AtomicFact::NotNormalAtomicFact(a) => a.line_file.clone(),
            AtomicFact::NotEqualFact(a) => a.line_file.clone(),
            AtomicFact::NotLessFact(a) => a.line_file.clone(),
            AtomicFact::NotGreaterFact(a) => a.line_file.clone(),
            AtomicFact::NotLessEqualFact(a) => a.line_file.clone(),
            AtomicFact::NotGreaterEqualFact(a) => a.line_file.clone(),
            AtomicFact::NotIsSetFact(a) => a.line_file.clone(),
            AtomicFact::NotIsNonemptySetFact(a) => a.line_file.clone(),
            AtomicFact::NotIsFiniteSetFact(a) => a.line_file.clone(),
            AtomicFact::NotInFact(a) => a.line_file.clone(),
            AtomicFact::NotIsCartFact(a) => a.line_file.clone(),
            AtomicFact::NotIsTupleFact(a) => a.line_file.clone(),
            AtomicFact::NotSubsetFact(a) => a.line_file.clone(),
            AtomicFact::NotSupersetFact(a) => a.line_file.clone(),
            AtomicFact::FnEqualInFact(a) => a.line_file.clone(),
            AtomicFact::FnEqualFact(a) => a.line_file.clone(),
        }
    }

    pub fn with_line_file(mut self, line_file: LineFile) -> Self {
        match &mut self {
            AtomicFact::EqualFact(a) => a.line_file = line_file,
            AtomicFact::LessFact(a) => a.line_file = line_file,
            AtomicFact::GreaterFact(a) => a.line_file = line_file,
            AtomicFact::LessEqualFact(a) => a.line_file = line_file,
            AtomicFact::GreaterEqualFact(a) => a.line_file = line_file,
            AtomicFact::IsSetFact(a) => a.line_file = line_file,
            AtomicFact::IsNonemptySetFact(a) => a.line_file = line_file,
            AtomicFact::IsFiniteSetFact(a) => a.line_file = line_file,
            AtomicFact::InFact(a) => a.line_file = line_file,
            AtomicFact::IsCartFact(a) => a.line_file = line_file,
            AtomicFact::IsTupleFact(a) => a.line_file = line_file,
            AtomicFact::SubsetFact(a) => a.line_file = line_file,
            AtomicFact::SupersetFact(a) => a.line_file = line_file,
            AtomicFact::NormalAtomicFact(a) => a.line_file = line_file,
            AtomicFact::NotNormalAtomicFact(a) => a.line_file = line_file,
            AtomicFact::NotEqualFact(a) => a.line_file = line_file,
            AtomicFact::NotLessFact(a) => a.line_file = line_file,
            AtomicFact::NotGreaterFact(a) => a.line_file = line_file,
            AtomicFact::NotLessEqualFact(a) => a.line_file = line_file,
            AtomicFact::NotGreaterEqualFact(a) => a.line_file = line_file,
            AtomicFact::NotIsSetFact(a) => a.line_file = line_file,
            AtomicFact::NotIsNonemptySetFact(a) => a.line_file = line_file,
            AtomicFact::NotIsFiniteSetFact(a) => a.line_file = line_file,
            AtomicFact::NotInFact(a) => a.line_file = line_file,
            AtomicFact::NotIsCartFact(a) => a.line_file = line_file,
            AtomicFact::NotIsTupleFact(a) => a.line_file = line_file,
            AtomicFact::NotSubsetFact(a) => a.line_file = line_file,
            AtomicFact::NotSupersetFact(a) => a.line_file = line_file,
            AtomicFact::FnEqualInFact(a) => a.line_file = line_file,
            AtomicFact::FnEqualFact(a) => a.line_file = line_file,
        }
        self
    }
}
