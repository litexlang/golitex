#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustedOrRequireVerify {
    RequireVerification,
    Trusted,
}
