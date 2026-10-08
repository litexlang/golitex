//! Iterated / range / sequence object WD.
//! Sum/Product: Z endpoints, start<=end, iterand return ⊆ C, light domain coverage.
//! Reduce: Z endpoints, homogeneous binary op, seed ∈ carrier, iterand ret = carrier.
//! Range/ClosedRange and accurate FiniteSeqSet/SeqSet contracts.

use super::helper::set_bound_parameter_count;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::ast::fact::{
    AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, LessEqualFact, SubsetFact,
};
use crate::ast::obj::{
    ClosedRange, FiniteSeqSet, FiniteSetReduce, FnSet, FunctionSpace, Obj, Product,
    ProductOfFiniteSet, ProductShape, Range, Reduce, SeqSet, SetFormer, StandardSet, Sum,
    SumOfFiniteSet,
};
use crate::ast::param::{
    ParamType, SetBoundParameterGroup, SetBoundParameterList, TypedParameterGroup,
    TypedParameterList,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // sum(start, end, f): children, start/end ∈ Z, start <= end, f unary with ret ⊆ C,
    // and the closed index range covered by f's domain.
    // Example: `sum(1, 3, fn(x Z) Z {x})`.
    pub(super) fn verify_sum_obj_well_definedness_by_def(
        &mut self,
        value: &Sum,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_range_iteration_obj_well_definedness_by_def(
            value.start.as_ref(),
            value.end.as_ref(),
            value.func.as_ref(),
            "sum",
            verify_state,
        )
    }

    pub(super) fn verify_sum_of_finite_set_obj_well_definedness_by_def(
        &mut self,
        value: &SumOfFiniteSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_finite_aggregate_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.func.as_ref(),
            "finite_set_sum",
            verify_state,
        )
    }

    // product(start, end, f): same obligations as sum.
    // Example: `product(1, 3, fn(x Z) Z {x})`.
    pub(super) fn verify_product_obj_well_definedness_by_def(
        &mut self,
        value: &Product,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_range_iteration_obj_well_definedness_by_def(
            value.start.as_ref(),
            value.end.as_ref(),
            value.func.as_ref(),
            "product",
            verify_state,
        )
    }

    pub(super) fn verify_product_of_finite_set_obj_well_definedness_by_def(
        &mut self,
        value: &ProductOfFiniteSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_finite_aggregate_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.func.as_ref(),
            "finite_set_product",
            verify_state,
        )
    }

    // reduce(start, end, f, op, seed): children, start/end ∈ Z, op = fn(x, y T) T,
    // f unary with ret = T, seed ∈ T. Empty range (end < start) is allowed; no start<=end.
    // Example: `reduce(1, 3, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0)`.
    pub(super) fn verify_reduce_obj_well_definedness_by_def(
        &mut self,
        value: &Reduce,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_objs_as_children(
            &[
                value.start.as_ref(),
                value.end.as_ref(),
                value.func.as_ref(),
                value.op.as_ref(),
                value.seed.as_ref(),
            ],
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.start.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            format!("reduce start {} is not in Z", value.start.ir()),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.end.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            format!("reduce end {} is not in Z", value.end.ir()),
        )?);
        self.append_reduce_signature_requirements(
            value.func.as_ref(),
            value.op.as_ref(),
            value.seed.as_ref(),
            "reduce",
            verify_state,
            &mut reqs,
        )?;
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_finite_set_reduce_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetReduce,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_objs_as_children(
            &[
                value.set.as_ref(),
                value.func.as_ref(),
                value.op.as_ref(),
                value.seed.as_ref(),
            ],
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_is_finite_set(
            value.set.as_ref(),
            verify_state.clone(),
            format!(
                "finite_set_reduce: set {} is not verified to be finite",
                value.set.ir()
            ),
        )?);
        self.append_reduce_signature_requirements(
            value.func.as_ref(),
            value.op.as_ref(),
            value.seed.as_ref(),
            "finite_set_reduce",
            verify_state.clone(),
            &mut reqs,
        )?;
        // Enumeration-independent reduction requires both operation laws.
        if let Some(signature) = self.resolve_callable_fn_set(value.op.as_ref()) {
            if let Some(carrier) = homogeneous_binary_carrier(&signature) {
                reqs.extend(self.unordered_fold_laws(
                    value.op.as_ref(),
                    &carrier,
                    verify_state.clone(),
                )?);
            }
        }
        // A finite fold applies f at every set element, so its declared domain
        // and predicates must cover the set (e.g. {1} is not covered by {2}).
        if let Some(signature) = self.resolve_callable_fn_set(value.func.as_ref()) {
            if set_bound_parameter_count(&signature.set_bound_parameters) == 1 {
                for group in &signature.set_bound_parameters.groups {
                    if group.params.is_empty() {
                        continue;
                    }
                    let coverage = AtomicFact::SubsetFact(SubsetFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: value.set.as_ref().clone(),
                        right: group.param_type.as_ref().clone(),
                        line_file: None,
                    });
                    reqs.push(self.verify_required_atomic_fact(
                        coverage,
                        verify_state.clone(),
                        "finite_set_reduce: iterand must cover the finite set".to_string(),
                    )?);
                }
                self.append_aggregate_predicate_requirements(
                    &signature,
                    AggregateIndexDomain::FiniteSet(value.set.as_ref()),
                    verify_state.clone(),
                    &mut reqs,
                )?;
            }
        }
        Ok(self.with_requirements(proof, reqs))
    }

    // range(start, end): children, then both endpoints $in Z.
    // Example: `range(1, 3)`.
    pub(super) fn verify_range_obj_well_definedness_by_def(
        &mut self,
        value: &Range,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.start.as_ref(),
            value.end.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.start.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            format!("range start {} is not in Z", value.start.ir()),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.end.as_ref(),
            StandardSet::Z,
            verify_state,
            format!("range end {} is not in Z", value.end.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // closed_range(start, end): same Z carrier obligations as range.
    pub(super) fn verify_closed_range_obj_well_definedness_by_def(
        &mut self,
        value: &ClosedRange,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.start.as_ref(),
            value.end.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.start.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            format!("closed_range start {} is not in Z", value.start.ir()),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.end.as_ref(),
            StandardSet::Z,
            verify_state,
            format!("closed_range end {} is not in Z", value.end.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // finite_seq_set(S, n): children, `$is_set(S)`, `n $in N`.
    pub(super) fn verify_finite_seq_set_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSeqSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.n.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_is_set(
            value.set.as_ref(),
            verify_state.clone(),
            format!(
                "finite_seq_set: first argument {} is not a set",
                value.set.ir()
            ),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.n.as_ref(),
            StandardSet::N,
            verify_state,
            format!(
                "finite_seq_set: length {} is not verified in N",
                value.n.ir()
            ),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // seq_set(S): children, `$is_set(S)`.
    pub(super) fn verify_seq_set_obj_well_definedness_by_def(
        &mut self,
        value: &SeqSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state.clone())?;
        let req = self.require_is_set(
            value.set.as_ref(),
            verify_state,
            format!("seq_set: argument {} is not a set", value.set.ir()),
        )?;
        Ok(self.with_requirements(proof, vec![req]))
    }

    fn verify_range_iteration_obj_well_definedness_by_def(
        &mut self,
        start: &Obj,
        end: &Obj,
        function: &Obj,
        operation: &str,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_objs_as_children(&[start, end, function], verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            start,
            StandardSet::Z,
            verify_state.clone(),
            format!("{operation} start {} is not in Z", start.ir()),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            end,
            StandardSet::Z,
            verify_state.clone(),
            format!("{operation} end {} is not in Z", end.ir()),
        )?);
        let ordered = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: start.clone(),
            right: end.clone(),
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            ordered,
            verify_state.clone(),
            format!("{operation}: cannot verify start <= end for the iteration range"),
        )?);
        self.append_unary_scalar_iterand_requirements(
            function,
            start,
            end,
            operation,
            verify_state,
            &mut reqs,
        )?;
        Ok(self.with_requirements(proof, reqs))
    }

    fn verify_finite_aggregate_obj_well_definedness_by_def(
        &mut self,
        set: &Obj,
        function: &Obj,
        operation: &str,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof =
            self.verify_binary_obj_well_definedness_by_def(set, function, verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_is_finite_set(
            set,
            verify_state.clone(),
            format!("{operation}: set {} is not a finite set", set.ir()),
        )?);
        match self.resolve_callable_fn_set(function) {
            Some(fn_set) => {
                if set_bound_parameter_count(&fn_set.set_bound_parameters) != 1 {
                    reqs.push(self.require_callable_as_expected_unary(
                        function,
                        set,
                        operation,
                        verify_state,
                    )?);
                } else {
                    let parameter_set = fn_set
                        .set_bound_parameters
                        .groups
                        .iter()
                        .find(|g| !g.params.is_empty())
                        .expect("one parameter")
                        .param_type
                        .as_ref();
                    let subset = AtomicFact::SubsetFact(SubsetFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: set.clone(),
                        right: parameter_set.clone(),
                        line_file: None,
                    });
                    reqs.push(self.verify_required_atomic_fact(
                        subset,
                        verify_state.clone(),
                        format!(
                            "{operation}: set {} is not covered by iterand domain {}",
                            set.ir(),
                            parameter_set.ir()
                        ),
                    )?);
                    reqs.push(self.require_obj_subset_of_standard_set(
                        fn_set.ret_set.as_ref(),
                        StandardSet::C,
                        verify_state.clone(),
                        format!(
                            "{operation}: iterand return set {} is not verified ⊆ C",
                            fn_set.ret_set.ir()
                        ),
                    )?);
                    self.append_aggregate_predicate_requirements(
                        &fn_set,
                        AggregateIndexDomain::FiniteSet(set),
                        verify_state,
                        &mut reqs,
                    )?;
                }
            }
            None => {
                reqs.push(self.require_callable_as_expected_unary(
                    function,
                    set,
                    operation,
                    verify_state,
                )?);
            }
        }
        Ok(self.with_requirements(proof, reqs))
    }

    fn append_unary_scalar_iterand_requirements(
        &mut self,
        function: &Obj,
        start: &Obj,
        end: &Obj,
        operation: &str,
        verify_state: VerifyState,
        reqs: &mut Vec<VerifyFactResult>,
    ) -> RuntimeResult<()> {
        let Some(fn_set) = self.resolve_callable_fn_set(function) else {
            reqs.push(self.require_callable_as_expected_unary(
                function,
                &Obj::StandardSet(StandardSet::Z),
                operation,
                verify_state,
            )?);
            return Ok(());
        };
        if set_bound_parameter_count(&fn_set.set_bound_parameters) != 1 {
            reqs.push(self.require_callable_as_expected_unary(
                function,
                &Obj::StandardSet(StandardSet::Z),
                operation,
                verify_state,
            )?);
            return Ok(());
        }
        reqs.push(self.require_obj_subset_of_standard_set(
            fn_set.ret_set.as_ref(),
            StandardSet::C,
            verify_state.clone(),
            format!(
                "{operation}: iterand return set {} is not verified ⊆ C",
                fn_set.ret_set.ir()
            ),
        )?);
        let param_set = fn_set
            .set_bound_parameters
            .groups
            .first()
            .map(|g| g.param_type.as_ref().clone())
            .unwrap_or_else(|| Obj::StandardSet(StandardSet::Z));
        self.append_iteration_coverage_requirements(
            start,
            end,
            &param_set,
            operation,
            verify_state.clone(),
            reqs,
        )?;
        self.append_aggregate_predicate_requirements(
            &fn_set,
            AggregateIndexDomain::Range(start, end),
            verify_state,
            reqs,
        )?;
        Ok(())
    }

    // A callable's predicate domain must hold at every aggregate argument,
    // before either symbolic identities or numeric consumers may use it.
    fn append_aggregate_predicate_requirements(
        &mut self,
        signature: &FnSet,
        domain: AggregateIndexDomain,
        state: VerifyState,
        requirements: &mut Vec<VerifyFactResult>,
    ) -> RuntimeResult<()> {
        if signature.dom_facts.is_empty() {
            return Ok(());
        }
        if matches!(domain, AggregateIndexDomain::FiniteSet(Obj::SetFormer(SetFormer::ListSet(s))) if s.list.is_empty())
        {
            return Ok(());
        }
        if let Some((arguments, endpoint_equalities)) =
            self.explicit_aggregate_predicate_arguments(domain)
        {
            for equality in endpoint_equalities {
                requirements.push(self.verify_fact(&equality, state)?);
            }
            let original = signature
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|g| &g.params)
                .next()
                .expect("unary");
            for argument in arguments {
                let substitution = std::collections::HashMap::from([(original.id, argument)]);
                for condition in &signature.dom_facts {
                    let instantiated = self
                        .inst_fact(
                            &crate::instantiate::quantifier_free_fact_to_fact(condition.clone()),
                            &substitution,
                        )
                        .map_err(|e| {
                            crate::runtime::RuntimeError::InternalBug(format!(
                                "aggregate argument substitution: {e}"
                            ))
                        })?;
                    requirements.push(self.verify_fact(&instantiated, state)?);
                }
            }
            return Ok(());
        }
        let parameter = self.fresh_internal_param();
        let index = Obj::Identifier(crate::ast::obj::IdentifierObj::from_bound_name(&parameter));
        let original = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .next()
            .expect("unary");
        let substitution = std::collections::HashMap::from([(original.id, index.clone())]);
        let (parameter_set, dom_facts) = match domain {
            AggregateIndexDomain::FiniteSet(set) => (set.clone(), vec![]),
            AggregateIndexDomain::Range(start, end) => {
                let lower: Fact = LessEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: start.clone(),
                    right: index.clone(),
                    line_file: None,
                }
                .into();
                let upper: Fact = LessEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: index,
                    right: end.clone(),
                    line_file: None,
                }
                .into();
                (Obj::StandardSet(StandardSet::Z), vec![lower, upper])
            }
        };
        let mut then_facts = Vec::new();
        for condition in &signature.dom_facts {
            let instantiated = self
                .inst_fact(
                    &crate::instantiate::quantifier_free_fact_to_fact(condition.clone()),
                    &substitution,
                )
                .map_err(|error| {
                    crate::runtime::RuntimeError::InternalBug(format!(
                        "aggregate predicate binder substitution: {error}"
                    ))
                })?;
            then_facts.push(match instantiated {
                Fact::AtomicFact(p) => ExistOrAndChainAtomicFact::AtomicFact(p),
                Fact::AndFact(p) => ExistOrAndChainAtomicFact::AndFact(p),
                Fact::ChainFact(p) => ExistOrAndChainAtomicFact::ChainFact(p),
                Fact::OrFact(p) => ExistOrAndChainAtomicFact::OrFact(p),
                _ => unreachable!("quantifier-free callable domain"),
            });
        }
        let coverage = ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![parameter],
                    param_type: ParamType::Obj(parameter_set),
                }],
            },
            dom_facts,
            then_facts,
            line_file: None,
        };
        requirements.push(self.verify_forall_fact(&coverage, state)?);
        Ok(())
    }

    // Literal finite enumeration supplies exactly the predicate obligations for
    // the source interval/list. Endpoint calculation is retained as equality
    // evidence; symbolic domains continue through the universal coverage path.
    fn explicit_aggregate_predicate_arguments(
        &mut self,
        domain: AggregateIndexDomain,
    ) -> Option<(Vec<Obj>, Vec<Fact>)> {
        use crate::rational_expression::exact_rational::EvalRational;
        let (start, end, half_open) = match domain {
            AggregateIndexDomain::Range(a, b) => (a, b, false),
            AggregateIndexDomain::FiniteSet(Obj::SetFormer(SetFormer::ListSet(s))) => {
                return (s.list.len()
                    <= crate::execute::execute_eval_stmt::helper::MAX_AGGREGATE_TERMS)
                    .then(|| (s.list.iter().map(|v| v.as_ref().clone()).collect(), vec![]));
            }
            AggregateIndexDomain::FiniteSet(Obj::SetFormer(SetFormer::ClosedRange(s))) => {
                (s.start.as_ref(), s.end.as_ref(), false)
            }
            AggregateIndexDomain::FiniteSet(Obj::SetFormer(SetFormer::Range(s))) => {
                (s.start.as_ref(), s.end.as_ref(), true)
            }
            AggregateIndexDomain::FiniteSet(_) => return None,
        };
        let (start_rewritten, _) = self.rewrite_obj_by_known_closed_numeric_equal(start);
        let (end_rewritten, _) = self.rewrite_obj_by_known_closed_numeric_equal(end);
        let first = EvalRational::from_obj(&start_rewritten)?.to_i128_if_integer()?;
        let last = EvalRational::from_obj(&end_rewritten)?.to_i128_if_integer()?;
        let count = if last < first || (half_open && last == first) {
            0
        } else {
            let difference = last.checked_sub(first)?;
            usize::try_from(if half_open {
                difference
            } else {
                difference.checked_add(1)?
            })
            .ok()?
        };
        if count > crate::execute::execute_eval_stmt::helper::MAX_AGGREGATE_TERMS {
            return None;
        }
        let number = |value: i128| {
            Obj::Literal(crate::ast::obj::Literal::Number(
                crate::ast::obj::Number::new(value.to_string()),
            ))
        };
        let endpoints = vec![
            crate::ast::fact::EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: start.clone(),
                right: number(first),
                line_file: None,
            }
            .into(),
            crate::ast::fact::EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: end.clone(),
                right: number(last),
                line_file: None,
            }
            .into(),
        ];
        let arguments = (0..count)
            .map(|offset| {
                number(
                    first
                        .checked_add(offset as i128)
                        .expect("checked interval count"),
                )
            })
            .collect();
        Some((arguments, endpoints))
    }

    // Light coverage: universal numeric carriers auto-pass; N / NPos check start;
    // otherwise require closed_range(start, end) ⊆ param_set.
    fn append_iteration_coverage_requirements(
        &mut self,
        start: &Obj,
        end: &Obj,
        parameter_set: &Obj,
        operation: &str,
        verify_state: VerifyState,
        reqs: &mut Vec<VerifyFactResult>,
    ) -> RuntimeResult<()> {
        match parameter_set {
            Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::Q)
            | Obj::StandardSet(StandardSet::R)
            | Obj::StandardSet(StandardSet::C) => Ok(()),
            Obj::StandardSet(StandardSet::N) => {
                reqs.push(self.require_obj_in_standard_set(
                    start,
                    StandardSet::N,
                    verify_state,
                    format!(
                        "{operation}: start {} must be in N when the iterand domain is N",
                        start.ir()
                    ),
                )?);
                Ok(())
            }
            Obj::StandardSet(StandardSet::NPos)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::RPos) => {
                reqs.push(self.require_obj_in_standard_set(
                    start,
                    StandardSet::NPos,
                    verify_state,
                    format!(
                        "{operation}: start {} must be in N+ for positive iterand domain",
                        start.ir()
                    ),
                )?);
                Ok(())
            }
            _ => {
                let interval = Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
                    start: Box::new(start.clone()),
                    end: Box::new(end.clone()),
                }));
                let subset = AtomicFact::SubsetFact(SubsetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: interval,
                    right: parameter_set.clone(),
                    line_file: None,
                });
                reqs.push(self.verify_required_atomic_fact(
                    subset,
                    verify_state,
                    format!(
                        "{operation}: cannot verify closed_range({}, {}) ⊆ {}",
                        start.ir(),
                        end.ir(),
                        parameter_set.ir()
                    ),
                )?);
                Ok(())
            }
        }
    }

    fn append_reduce_signature_requirements(
        &mut self,
        function: &Obj,
        operation: &Obj,
        seed: &Obj,
        operation_name: &str,
        verify_state: VerifyState,
        reqs: &mut Vec<VerifyFactResult>,
    ) -> RuntimeResult<()> {
        let Some(op_set) = self.resolve_callable_fn_set(operation) else {
            reqs.push(self.require_callable_as_expected_binary_homogeneous(
                operation,
                operation_name,
                verify_state,
            )?);
            return Ok(());
        };
        let Some(carrier) = homogeneous_binary_carrier(&op_set) else {
            reqs.push(self.require_callable_as_expected_binary_homogeneous(
                operation,
                operation_name,
                verify_state,
            )?);
            return Ok(());
        };
        let Some(iterand_set) = self.resolve_callable_fn_set(function) else {
            reqs.push(self.require_callable_as_expected_unary(
                function,
                &carrier,
                operation_name,
                verify_state,
            )?);
            return Ok(());
        };
        if set_bound_parameter_count(&iterand_set.set_bound_parameters) != 1
            || iterand_set.ret_set.ir() != carrier.ir()
        {
            reqs.push(self.require_callable_as_expected_unary(
                function,
                &carrier,
                operation_name,
                verify_state.clone(),
            )?);
            return Ok(());
        }
        let seed_in = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: seed.clone(),
            set: carrier,
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            seed_in,
            verify_state,
            format!(
                "{operation_name}: seed {} is not verified to belong to the operation carrier",
                seed.ir()
            ),
        )?);
        Ok(())
    }

    // Soft shape miss: require `function $in fn(__p Dom) C` (fails when not that signature).
    fn require_callable_as_expected_unary(
        &mut self,
        function: &Obj,
        domain: &Obj,
        operation: &str,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let expected = self.fresh_unary_fn_set(domain.clone(), Obj::StandardSet(StandardSet::C));
        let membership = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: function.clone(),
            set: Obj::FunctionSpace(FunctionSpace::FnSet(expected)),
            line_file: None,
        });
        self.verify_required_atomic_fact(
            membership,
            verify_state,
            format!(
                "{operation}: expected a unary scalar-valued function; got {}",
                function.ir()
            ),
        )
    }

    fn require_callable_as_expected_binary_homogeneous(
        &mut self,
        operation: &Obj,
        operation_name: &str,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let carrier = Obj::StandardSet(StandardSet::C);
        let expected = self.fresh_binary_homogeneous_fn_set(carrier);
        let membership = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: operation.clone(),
            set: Obj::FunctionSpace(FunctionSpace::FnSet(expected)),
            line_file: None,
        });
        self.verify_required_atomic_fact(
            membership,
            verify_state,
            format!(
                "{operation_name}: operation {} must have signature fn(x, y T) T",
                operation.ir()
            ),
        )
    }

    pub(super) fn require_obj_subset_of_standard_set(
        &mut self,
        obj: &Obj,
        set: StandardSet,
        verify_state: VerifyState,
        failure_message: String,
    ) -> RuntimeResult<VerifyFactResult> {
        let fact = AtomicFact::SubsetFact(SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: obj.clone(),
            right: Obj::StandardSet(set),
            line_file: None,
        });
        self.verify_required_atomic_fact(fact, verify_state, failure_message)
    }

    fn fresh_unary_fn_set(&mut self, domain: Obj, ret: Obj) -> FnSet {
        let param = self.fresh_internal_param();
        FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![param],
                    param_type: Box::new(domain),
                }],
            },
            dom_facts: vec![],
            ret_set: Box::new(ret),
        }
    }

    fn fresh_binary_homogeneous_fn_set(&mut self, carrier: Obj) -> FnSet {
        let left = self.fresh_internal_param();
        let right = self.fresh_internal_param();
        FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![left, right],
                    param_type: Box::new(carrier.clone()),
                }],
            },
            dom_facts: vec![],
            ret_set: Box::new(carrier),
        }
    }
}

#[derive(Clone, Copy)]
enum AggregateIndexDomain<'a> {
    Range(&'a Obj, &'a Obj),
    FiniteSet(&'a Obj),
}

fn homogeneous_binary_carrier(fn_set: &FnSet) -> Option<Obj> {
    if set_bound_parameter_count(&fn_set.set_bound_parameters) != 2 || !fn_set.dom_facts.is_empty()
    {
        return None;
    }
    let mut carriers = Vec::new();
    for group in &fn_set.set_bound_parameters.groups {
        for _ in &group.params {
            carriers.push(group.param_type.as_ref().clone());
        }
    }
    let [left, right] = carriers.as_slice() else {
        return None;
    };
    if left.ir() != right.ir() || left.ir() != fn_set.ret_set.ir() {
        return None;
    }
    Some(left.clone())
}
