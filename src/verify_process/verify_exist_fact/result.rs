use crate::prelude::*;

pub enum VerifyExistFactResult {
    Exist(VerifyPlainExistFactResult),
    ExistUnique(VerifyExistUniqueFactResult),
    NotExist(VerifyNotExistFactResult),
}
