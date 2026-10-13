pub enum InferOrFactResult {
    // Or is not split on store; do not eager-infer a branch.
    NoInfer,
}
