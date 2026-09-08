use crate::prelude::*;

pub struct VerifyNonEquationalAtomicFactResult {
    pub fact: AtomicFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: NonEquationalAtomicFactSearchedProof,
}

pub enum NonEquationalAtomicFactSearchedProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(NonEquationalAtomicFactSearchProofByBuiltinRule),
    ByKnownAtomicFact(NonEquationalAtomicFactSearchedProofByKnownAtomicFact),
    ByDefinition(NonEquationalAtomicFactSearchedProofByDefinition),
    ByBuiltinStrategy(NonEquationalAtomicFactSearchProofByBuiltinStrategy),
    ByKnownForallFact(NonEquationalAtomicFactSearchedProofByKnownForallFact),
    ByBuiltinAlgebraicRewrite(NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite),
    ByKnownAlgebraicRewrite(NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite),
}

pub struct NonEquationalAtomicFactSearchedProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult>,
}

pub struct NonEquationalAtomicFactSearchedProofByDefinition {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// 需要记录一下 forall 事实里的参数a, b, c 是如何对应到传入的事实里的参数的。比如 forall a R: a > 0 => $p(a) 对应上 $p(1)，就是a对应了1。
pub struct NonEquationalAtomicFactSearchedProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub forall_parameters_match_what_args: Vec<Obj>,
    // 包括为啥这些对应上的arg满足forall的参数要求，以及为什么forall的domain事实被满足了。比如 forall a R: a > 0 => $p(a) 对应上 $p(1)，就是a对应了1。这里就要保存 1 $in R, 1 > 0 的证明
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
