// This is one of the fields of enum StmtResult, which is the result of executing a statement
// execute fact statement的时候，有两个事情，一个是证明这个事实，一个是把这个事实存下来
pub struct ExecFactStmtResult {
    pub verify_result: VerifyFactResult,
    pub store_and_infer_result: StoreAndInferResult,
}
