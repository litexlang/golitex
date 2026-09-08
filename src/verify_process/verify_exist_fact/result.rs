use crate::prelude::*;

pub enum VerifyExistFactResult {
    Exist(VerifyPlainExistFactResult),
    ExistUnique(VerifyExistUniqueFactResult),
    NotExist(VerifyNotExistFactResult),
}

pub struct VerifyPlainExistFactResult {
    pub witnesses: Vec<Obj>,
    pub proof_of_body_facts: Vec<VerifyFactResult>,
}

pub struct VerifyExistUniqueFactResult {
    pub existence: VerifyPlainExistFactResult,
    pub uniqueness: VerifyForallFactResult,
}

pub struct VerifyNotExistFactResult {
    pub demorgan_forall: VerifyForallFactResult,
}
