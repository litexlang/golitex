#[derive(Clone)]
pub struct VerifyState {
    pub can_use_forall_fact: bool,
    pub can_use_known_algebraic_rewrite: bool,
}
