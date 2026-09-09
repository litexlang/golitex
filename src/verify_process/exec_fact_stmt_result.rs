// This is one of the fields of enum StmtResult, which is the result of executing a statement
// Executing a fact statement does two things: prove the fact, then store it.
pub struct ExecFactStmtResult {
    pub verify_result: VerifyFactResult,
    pub store_and_infer_result: StoreAndInferResult,
}
