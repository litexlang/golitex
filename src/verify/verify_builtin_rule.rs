use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_objects_are_known_reals_in_builtin(
        &mut self,
        objs: &[&Obj],
        line_file: &LineFile,
        builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let mut seen = Vec::new();
        let mut steps = Vec::new();
        for obj in objs {
            let key = obj.to_string();
            if seen.contains(&key) {
                continue;
            }
            seen.push(key);
            let Some(mut object_steps) =
                self.verify_one_object_is_known_real_in_builtin(obj, line_file, builtin_state)?
            else {
                return Ok(None);
            };
            steps.append(&mut object_steps);
        }
        Ok(Some(steps))
    }

    pub(crate) fn verify_atomic_fact_with_builtin_rules(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let known_result = self.verify_known_non_forall_atomic_fact(goal)?;
        if known_result.is_true() {
            return Ok(known_result);
        }

        let mut builtin_state = BuiltinRuleVerifyState::new();
        self.verify_atomic_fact_with_builtin_rules_inner(goal, &mut builtin_state)
    }

    pub(crate) fn verify_known_non_forall_atomic_fact(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        match goal {
            AtomicFact::EqualFact(fact) => Ok(self.verify_objs_are_equal_known_only(
                &fact.left,
                &fact.right,
                fact.line_file.clone(),
            )),
            _ => self.verify_non_equational_atomic_fact_with_known_atomic_facts(goal),
        }
    }

    pub(crate) fn verify_same_family_builtin_child(
        &mut self,
        child: &AtomicFact,
        builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let known_result = self.verify_known_non_forall_atomic_fact(child)?;
        if known_result.is_true() {
            return Ok(known_result);
        }
        if !builtin_state.try_enter_recursive_goal() {
            return Ok(StmtUnknown::new().into());
        }
        self.verify_atomic_fact_with_builtin_rules_inner(child, builtin_state)
    }

    pub(crate) fn verify_cross_family_builtin_child(
        &mut self,
        child: &AtomicFact,
        _builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_known_non_forall_atomic_fact(child)
    }

    pub(crate) fn verify_cross_family_known_or_number_calculation(
        &mut self,
        child: &AtomicFact,
        builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let known_result = self.verify_cross_family_builtin_child(child, builtin_state)?;
        if known_result.is_true() {
            return Ok(known_result);
        }
        if self.verify_number_comparison_builtin_rule(child) == Some(true) {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    child.clone().into(),
                    "number comparison".to_string(),
                    Vec::new(),
                )
                .into(),
            );
        }
        Ok(StmtUnknown::new().into())
    }

    pub(crate) fn verify_same_family_builtin_children(
        &mut self,
        children: &[AtomicFact],
        builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let mut results = Vec::with_capacity(children.len());
        for child in children {
            let result = self.verify_same_family_builtin_child(child, builtin_state)?;
            if !result.is_true() {
                return Ok(None);
            }
            results.push(result);
        }
        Ok(Some(results))
    }

    fn verify_atomic_fact_with_builtin_rules_inner(
        &mut self,
        goal: &AtomicFact,
        builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match goal {
            AtomicFact::EqualFact(fact) => self.verify_equality_by_builtin_rules(
                &fact.left,
                &fact.right,
                fact.line_file.clone(),
                builtin_state,
            ),
            _ => {
                self.verify_non_equational_atomic_fact_with_builtin_rules_inner(goal, builtin_state)
            }
        }
    }

    fn verify_one_object_is_known_real_in_builtin(
        &mut self,
        obj: &Obj,
        line_file: &LineFile,
        builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let in_r: AtomicFact =
            InFact::new(obj.clone(), StandardSet::R.into(), line_file.clone()).into();
        let direct_result = self.verify_cross_family_builtin_child(&in_r, builtin_state)?;
        if direct_result.is_true() {
            return Ok(Some(vec![direct_result]));
        }

        // Equality-class resolution and literal evaluation are pure normalization, not a
        // recursive proof in another fact family.  This keeps finite enumeration cases such as
        // `a = 1` usable by numeric builtin rules without opening cross-family recursion.
        if self.resolve_obj_to_number_resolved(obj).is_some() {
            return Ok(Some(Vec::new()));
        }

        for source_set in self.known_sets_containing_obj(obj) {
            let source_membership: AtomicFact =
                InFact::new(obj.clone(), source_set.clone(), line_file.clone()).into();
            let source_result = self.verify_known_non_forall_atomic_fact(&source_membership)?;
            if !source_result.is_true() {
                continue;
            }
            for carrier in [
                StandardSet::R,
                StandardSet::NPos,
                StandardSet::N,
                StandardSet::ZNeg,
                StandardSet::ZNz,
                StandardSet::Z,
                StandardSet::Q,
                StandardSet::QPos,
                StandardSet::QNeg,
                StandardSet::QNz,
                StandardSet::RPos,
                StandardSet::RNeg,
                StandardSet::RNz,
            ] {
                let subset: AtomicFact = SubsetFact::new(
                    source_set.clone(),
                    carrier.clone().into(),
                    line_file.clone(),
                )
                .into();
                if let (Obj::StandardSet(source), AtomicFact::SubsetFact(subset_fact)) =
                    (&source_set, &subset)
                {
                    if Self::standard_set_is_subset_eq(source, &carrier) {
                        let subset_result =
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                subset_fact.clone().into(),
                                "standard_set_subset".to_string(),
                                Vec::new(),
                            )
                            .into();
                        return Ok(Some(vec![source_result, subset_result]));
                    }
                }
                let subset_result = self.verify_known_non_forall_atomic_fact(&subset)?;
                if subset_result.is_true() {
                    return Ok(Some(vec![source_result, subset_result]));
                }
            }
        }

        if matches!(obj, Obj::Number(_) | Obj::EulerNumber(_) | Obj::Pi(_)) {
            return Ok(Some(Vec::new()));
        }

        let iterated_func = match obj {
            Obj::Sum(sum) => Some(sum.func.as_ref()),
            Obj::SumOfFiniteSet(sum) => Some(sum.func.as_ref()),
            Obj::Product(product) => Some(product.func.as_ref()),
            Obj::ProductOfFiniteSet(product) => Some(product.func.as_ref()),
            _ => None,
        };
        if let Some(func) = iterated_func {
            let Some(Obj::StandardSet(ret_set)) = self.iterated_op_func_ret_set(func) else {
                return Ok(None);
            };
            return if Self::standard_set_is_subset_eq(&ret_set, &StandardSet::R) {
                Ok(Some(Vec::new()))
            } else {
                Ok(None)
            };
        }

        let child_objects: Vec<&Obj> = match obj {
            Obj::Add(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Sub(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Mul(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Div(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Mod(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Gcd(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Lcm(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Min(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Max(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Pow(x) => vec![x.base.as_ref(), x.exponent.as_ref()],
            Obj::Log(x) => vec![x.base.as_ref(), x.arg.as_ref()],
            Obj::Floor(x) => vec![x.arg.as_ref()],
            Obj::Ceil(x) => vec![x.arg.as_ref()],
            Obj::Exp(x) => vec![x.arg.as_ref()],
            Obj::Ln(x) => vec![x.arg.as_ref()],
            Obj::Sign(x) => vec![x.arg.as_ref()],
            Obj::Factorial(x) => vec![x.arg.as_ref()],
            Obj::Abs(x) => vec![x.arg.as_ref()],
            Obj::Sin(x) => vec![x.arg.as_ref()],
            Obj::Cos(x) => vec![x.arg.as_ref()],
            Obj::Tan(x) => vec![x.arg.as_ref()],
            Obj::Cot(x) => vec![x.arg.as_ref()],
            // These operators have real codomain. Their complex-domain obligation
            // belongs to the enclosing fact's well-definedness phase, not to a
            // cross-family builtin premise.
            Obj::RealPart(_) | Obj::ImaginaryPart(_) | Obj::ComplexAbs(_) => {
                return Ok(Some(Vec::new()));
            }
            Obj::Sqrt(x) => vec![x.arg.as_ref()],
            Obj::FiniteSetSize(_) | Obj::FiniteSetMax(_) | Obj::FiniteSetMin(_) => {
                return Ok(Some(Vec::new()));
            }
            _ => return Ok(None),
        };

        let mut steps = Vec::new();
        for child in child_objects {
            let Some(mut child_steps) =
                self.verify_one_object_is_known_real_in_builtin(child, line_file, builtin_state)?
            else {
                return Ok(None);
            };
            steps.append(&mut child_steps);
        }
        Ok(Some(steps))
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    #[test]
    fn raw_builtin_dispatch_has_only_the_root_and_limited_child_entry_points() {
        let source = include_str!("verify_builtin_rule.rs");
        let full_verify_state_constructor = ["VerifyState", "::new("].concat();
        let raw_dispatch = ["verify_atomic_fact_with_builtin_rules_", "inner("].concat();
        let creates_full_verify_state =
            source
                .match_indices(&full_verify_state_constructor)
                .any(|(index, _)| {
                    source[..index]
                        .chars()
                        .next_back()
                        .is_none_or(|ch| !(ch.is_ascii_alphanumeric() || ch == '_'))
                });
        assert!(!creates_full_verify_state);
        assert_eq!(
            source.matches(&raw_dispatch).count(),
            3,
            "the raw dispatcher must only be defined once and called by the root and limited-child entry points"
        );
    }

    #[test]
    fn automatic_builtin_rule_files_do_not_create_fresh_roots_or_bypass_the_limited_entry() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/verify/verify_builtin_rules");
        visit_rust_files(&dir, &mut |path, source| {
            assert!(
                !source.contains("BuiltinRuleVerifyState::new"),
                "{} creates a fresh recursive builtin root",
                path.display()
            );
            assert!(
                !source.contains("verify_atomic_fact_with_builtin_rules("),
                "{} bypasses the same-family/cross-family premise entry points",
                path.display()
            );
        });
    }

    fn visit_rust_files(dir: &Path, f: &mut impl FnMut(&Path, &str)) {
        for entry in fs::read_dir(dir).expect("read builtin rule source directory") {
            let path = entry.expect("read builtin rule directory entry").path();
            if path.is_dir() {
                visit_rust_files(&path, f);
            } else if path.extension().and_then(|value| value.to_str()) == Some("rs") {
                let source = fs::read_to_string(&path).expect("read builtin rule source file");
                f(&path, &source);
            }
        }
    }
}
