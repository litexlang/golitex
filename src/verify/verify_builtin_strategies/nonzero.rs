use crate::prelude::*;

impl Runtime {
    // Product nonzero is a bounded, constructor-decreasing strategy:
    //
    //     left != 0    right != 0
    //     ------------------------
    //          left * right != 0
    //
    // Each premise is an immediate, strictly smaller subexpression. A premise first gets the
    // normal direct routes (known fact, direct evaluation, or one premise-producing builtin
    // rule); only a nested product repeats this structural split. For example, `2 * cot(x) != 0`
    // reduces to `2 != 0` and `cot(x) != 0`, so the latter may use the direct trigonometry rule,
    // while the strategy itself never re-enters the unrestricted verifier search.
    pub(crate) fn verify_nonzero_product_with_builtin_strategy(
        &mut self,
        fact: &NotEqualFact,
    ) -> Result<StmtResult, RuntimeError> {
        let expression = if self.obj_represents_zero_for_not_equal_builtin_rules(&fact.right) {
            &fact.left
        } else if self.obj_represents_zero_for_not_equal_builtin_rules(&fact.left) {
            &fact.right
        } else {
            return Ok(StmtUnknown::new().into());
        };
        let Obj::Mul(product) = expression else {
            return Ok(StmtUnknown::new().into());
        };

        let zero: Obj = Number::new("0".to_string()).into();
        let required: [AtomicFact; 2] = [
            NotEqualFact::new(
                product.left.as_ref().clone(),
                zero.clone(),
                fact.line_file.clone(),
            )
            .into(),
            NotEqualFact::new(product.right.as_ref().clone(), zero, fact.line_file.clone()).into(),
        ];
        let mut children = Vec::with_capacity(required.len());
        for child in &required {
            let result = self.verify_builtin_strategy_child(child)?;
            if !result.is_true() {
                return Ok(StmtUnknown::new().into());
            }
            children.push(result);
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                fact.clone().into(),
                "nonzero-product strategy: all immediate factors are nonzero".to_string(),
                children,
            )
            .into(),
        )
    }
}
