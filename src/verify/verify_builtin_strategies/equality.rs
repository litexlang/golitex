use crate::prelude::*;

impl Runtime {
    pub fn verify_equality_with_builtin_strategy(
        &mut self,
        fact: &EqualFact,
    ) -> Result<StmtResult, RuntimeError> {
        let extrema = self.verify_extremum_equality_with_builtin_strategy(fact)?;
        if extrema.is_success() {
            return Ok(extrema);
        }
        let finite_product =
            self.verify_finite_set_product_pointwise_equality_with_builtin_strategy(fact)?;
        if finite_product.is_success() {
            return Ok(finite_product);
        }
        self.verify_mod_congruence_with_builtin_strategy(fact)
    }

    // Pointwise finite-product congruence is structural: reduce the product equality to one
    // factor equality under a fresh member of the common finite set. Example:
    // `forall x X: f(x) = g(x)` proves `finite_set_product(X, f) = finite_set_product(X, g)`.
    fn verify_finite_set_product_pointwise_equality_with_builtin_strategy(
        &mut self,
        fact: &EqualFact,
    ) -> Result<StmtResult, RuntimeError> {
        let (Obj::ProductOfFiniteSet(left), Obj::ProductOfFiniteSet(right)) =
            (&fact.left, &fact.right)
        else {
            return Ok(UnknownGenericStmtResult::new().into());
        };
        let set_goal: AtomicFact = EqualFact::new(
            left.set.as_ref().clone(),
            right.set.as_ref().clone(),
            fact.line_file.clone(),
        )
        .into();
        let set_result = self.verify_builtin_strategy_child(&set_goal)?;
        if !set_result.is_success() {
            return Ok(UnknownGenericStmtResult::new().into());
        }

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name)?;
        let Some(left_at_x) = self.instantiate_unary_function_at(left.func.as_ref(), &x_obj)?
        else {
            return Ok(UnknownGenericStmtResult::new().into());
        };
        let Some(right_at_x) = self.instantiate_unary_function_at(right.func.as_ref(), &x_obj)?
        else {
            return Ok(UnknownGenericStmtResult::new().into());
        };
        let pointwise_goal: AtomicFact =
            EqualFact::new(left_at_x, right_at_x, fact.line_file.clone()).into();
        let pointwise_result = self.run_in_local_env(|rt| {
            let params_def = TypedParameterList::new(vec![TypedParameterGroup::new(
                vec![x_binding],
                ParamType::Obj(left.set.as_ref().clone()),
            )]);
            rt.define_params_with_type(&params_def, false, BindingScope::LocalBinder)?;
            rt.verify_builtin_strategy_child(&pointwise_goal)
        })?;
        if !pointwise_result.is_success() {
            return Ok(UnknownGenericStmtResult::new().into());
        }

        Ok(
            SuccessFactStmtResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                fact.clone().into(),
                "finite-set product congruence strategy: prove pointwise factor equality"
                    .to_string(),
                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyFiniteSetProductPointwiseEqualityWithBuiltinStrategy),
                vec![set_result, pointwise_result],
            )
            .into(),
        )
    }

    // Choosing a concrete finite-set extremum is an antisymmetry strategy: prove
    // the two immediate weak-order goals independently, each with a fresh direct
    // builtin-rule boundary.  Restricting the shape avoids turning every unknown
    // equality into an open-ended order search.
    fn verify_extremum_equality_with_builtin_strategy(
        &mut self,
        fact: &EqualFact,
    ) -> Result<StmtResult, RuntimeError> {
        let has_extremum = matches!(
            (&fact.left, &fact.right),
            (Obj::FiniteSetMax(_) | Obj::FiniteSetMin(_), _)
                | (_, Obj::FiniteSetMax(_) | Obj::FiniteSetMin(_))
        );
        if !has_extremum {
            return Ok(UnknownGenericStmtResult::new().into());
        }

        let required: [AtomicFact; 2] = [
            LessEqualFact::new(
                fact.left.clone(),
                fact.right.clone(),
                fact.line_file.clone(),
            )
            .into(),
            LessEqualFact::new(
                fact.right.clone(),
                fact.left.clone(),
                fact.line_file.clone(),
            )
            .into(),
        ];
        let mut steps = Vec::with_capacity(required.len());
        for child in &required {
            let result = self.verify_builtin_strategy_child(child)?;
            if !result.is_success() {
                return Ok(UnknownGenericStmtResult::new().into());
            }
            steps.push(result);
        }

        Ok(
            SuccessFactStmtResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                fact.clone().into(),
                "finite-extremum equality strategy: prove both weak-order directions".to_string(),
                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyExtremumEqualityWithBuiltinStrategy),
                steps,
            )
            .into(),
        )
    }

    // Congruence is structural: a binary expression modulo `m` is reduced by
    // reducing its two immediate operands modulo `m`.  Repeating this strategy
    // follows the expression tree; every immediate child still gets only a
    // fresh known-fact lookup and one direct builtin rule.
    fn verify_mod_congruence_with_builtin_strategy(
        &mut self,
        fact: &EqualFact,
    ) -> Result<StmtResult, RuntimeError> {
        let (Obj::Mod(left_mod), Obj::Mod(right_mod)) = (&fact.left, &fact.right) else {
            return Ok(UnknownGenericStmtResult::new().into());
        };

        let modulus_goal = EqualFact::new(
            left_mod.right.as_ref().clone(),
            right_mod.right.as_ref().clone(),
            fact.line_file.clone(),
        );
        let modulus_result = self.verify_equal_fact_with_bounded_builtin_routes(&modulus_goal)?;
        if !modulus_result.is_success() {
            return Ok(UnknownGenericStmtResult::new().into());
        }

        let pairs = match (left_mod.left.as_ref(), right_mod.left.as_ref()) {
            (Obj::Add(left), Obj::Add(right)) => [
                (left.left.as_ref(), right.left.as_ref()),
                (left.right.as_ref(), right.right.as_ref()),
            ],
            (Obj::Sub(left), Obj::Sub(right)) => [
                (left.left.as_ref(), right.left.as_ref()),
                (left.right.as_ref(), right.right.as_ref()),
            ],
            (Obj::Mul(left), Obj::Mul(right)) => [
                (left.left.as_ref(), right.left.as_ref()),
                (left.right.as_ref(), right.right.as_ref()),
            ],
            _ => return Ok(UnknownGenericStmtResult::new().into()),
        };

        let mut subgoals = vec![modulus_result];
        let residue = |obj: &Obj, modulus: &Obj| {
            if let Obj::Mod(remainder) = obj {
                if remainder.right.to_string() == modulus.to_string() {
                    return obj.clone();
                }
            }
            Mod::new(obj.clone(), modulus.clone()).into()
        };
        for (left, right) in pairs {
            let child = EqualFact::new(
                residue(left, left_mod.right.as_ref()),
                residue(right, right_mod.right.as_ref()),
                fact.line_file.clone(),
            );
            let direct = self.verify_equal_fact_with_bounded_builtin_routes(&child)?;
            let result = if direct.is_success() {
                direct
            } else {
                self.verify_mod_congruence_with_builtin_strategy(&child)?
            };
            if !result.is_success() {
                return Ok(UnknownGenericStmtResult::new().into());
            }
            subgoals.push(result);
        }

        Ok(
            SuccessFactStmtResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                fact.clone().into(),
                "mod-congruence strategy: reduce immediate binary operands modulo m".to_string(),
                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyModCongruenceWithBuiltinStrategy),
                subgoals,
            )
            .into(),
        )
    }
}
