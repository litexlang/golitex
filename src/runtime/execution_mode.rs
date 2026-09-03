#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecutionMode {
    RequireVerification,
    Trusted,
}
