use super::InferExistUniqueUniquenessForallResult;

pub enum InferExistUniqueFactResult {
    // Rule: `exist!` exposes componentwise uniqueness forall (Manual Builtin Inference).
    UniquenessForall(InferExistUniqueUniquenessForallResult),
    NoInfer,
}
