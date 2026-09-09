pub enum WellDefinednessProofOfObj {
    // Variants should match the fields of the Obj enum.
    // Example:
    Add(WellDefinednessProofOfAddObj),
    // ...
}

pub struct WellDefinednessProofOfAddObj {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
