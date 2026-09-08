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
