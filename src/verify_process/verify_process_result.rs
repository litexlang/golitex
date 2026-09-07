pub struct VerifyState {
    pub can_use_forall_fact: bool,
    pub can_use_prop_algebraic_rewrite: bool,
}

// is one of the fields of enum StmtResult, which is the result of executing a statement
pub struct ExecFactStmtResult {
    pub verify_result: VerifyFactResult,
    pub store_and_infer_result: StoreAndInferResult,
}

pub struct FactId {
    pub scope_depth: u64,
    pub index: u64,
}

pub struct VerifyFactByCacheResult {
    pub cite_fact_id: FactId,
}

pub enum VerifyFactResult {
    AtomicFact(VerifyAtomicFactResult),
    ForallFact(VerifyForallFactResult),
    ExistFact(VerifyExistFactResult)
    /// ...
}

pub enum VerifyAtomicFactResult {
    Equality(VerifyEqualityFactResult),
    NonEquationalAtomicFact(VerifyNonEquationalAtomicFactResult)
}

pub struct VerifyNonEquationalAtomicFactResult {
    pub well_definedness_result: VerifyNonEquationalAtomicFactWellDefinednessResult,
    pub proof: VerifyNonEquationalAtomicFactResultProof,
}

pub struct VerifyNonEquationalAtomicFactWellDefinednessResult {
    pub well_definedness_proof_of_each_parameter: Vec<WellDefinednessProofOfObj>,
}

pub enum WellDefinednessProofOfObj {
    // 这里应该要对应上每个 obj 的 enum 的 field
    // 举例
    Add(WellDefinednessProofOfAddObj),
    // ...
}

pub struct WellDefinednessProofOfAddObj {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum VerifyNonEquationalAtomicFactResult {
    VerifyByCache(VerifyFactByCacheResult),
    VerifyByBuiltinRule(VerifyNonEquationalAtomicFactProofSearchByBuiltinRuleResult),
    VerifyByKnownAtomicFact(VerifyNonEquationalAtomicFactProofSearchByKnownAtomicFactResult),
    VerifyByDefinition(VerifyNonEquationalAtomicFactProofSearchByDefinitionResult),
    VerifyByBuiltinStrategy(VerifyNonEquationalAtomicFactProofSearchByBuiltinStrategyResult),
    VerifyByKnownForallFact(VerifyNonEquationalAtomicFactProofSearchByKnown),
    VerifyByAlgebraicRewrite(VerifyNonEquationalAtomicFactProofSearchByAlgebraicRewriteResult),
}

pub enum VerifyNonEquationalAtomicFactProofSearchByBuiltinRuleResult {
    // 每个 NonEquationalAtomicFact builtin rule 对应一个
    // 举例
    PosAddPosIsPos(PosAddPosIsPosBuiltinRule),
    // ...
}

pub struct PosAddPosIsPosBuiltinRule {
    pub requirement_facts: Vec<FactStmt>, // a $in R, a > 0, b $in R, b > 0 才能对应上 a + b > 0
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct VerifyNonEquationalAtomicFactProofSearchByKnownAtomicFactResult {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult>,
}

pub struct VerifyNonEquationalAtomicFactProofSearchByDefinitionResult {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum VerifyNonEquationalAtomicFactProofSearchByBuiltinStrategyResult {
    // 所有的 builtin strategy 对应的 single step 都要有一个对应的 enum field
    // 举例 a + b > 0 在  a > 0, b > 0 时 OK
    PosAddPosIsPos(PosAddPosIsPosStrategySingleStep)
}

pub struct PosAddPosIsPosStrategySingleStep {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyNonEquationalAtomicFactProofSearchByBuiltinStrategyResult>
}

pub struct VerifyNonEquationalAtomicFactProofSearchByKnownForallFactResult {
    pub cite_fact_id: FactId,
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum VerifyNonEquationalAtomicFactProofSearchByPropAlgebraicRewriteResult {
    Transitivity(VerifyNonEquationalAtomicFactByTransitivity),
    Symmetry(VerifyNonEquationalAtomicFactBySymmetry),
    // ...
}

pub struct VerifyNonEquationalAtomicFactByTransitivity {
    pub searched_fact_id_for_transitivity: (FactId, FactId)
}

