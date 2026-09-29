use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::AtomicExceptEqualityFactSearchProofByBuiltinRule;
use crate::runtime::FactId;

pub(super) fn cite_from_atomic_builtin_rule(
    rule: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
) -> Option<FactId> {
    match rule {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(g) => g.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(l) => l.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(l) => l.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(n) => n.cite_fact_id(),
        _ => None,
    }
}
