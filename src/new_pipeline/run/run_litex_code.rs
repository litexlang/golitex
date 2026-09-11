impl Runtime {
    pub fn run_code(&mut self, code: &str) -> Runtime<Vec<ExecStmtResult>, RuntimeError> {
        // 先 tokenize

        // 再 Parse

        // 在执行
        self.exec_stmt()
    }
}
