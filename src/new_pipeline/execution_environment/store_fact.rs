impl Runtime {
    pub fn store_fact_and_well_definedness_then_infer(
        verify_result: VerifyFactResult2,
    ) -> Result<ExecFactStmtResult2, RuntimeError> {
        self.store_fact(VerifyFactResult2);
        self.store_well_definedness_of_objects_inside_fact(VerifyFactResult2);
        self.infer_facts(VerifyFactResult2);
    }
}
