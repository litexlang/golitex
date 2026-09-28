//! Iterated / range / sequence object WD.
//! Sum/Product: Z endpoints, start<=end, iterand return ⊆ C, light domain coverage.
//! Reduce: Z endpoints, homogeneous binary op, seed ∈ carrier, iterand ret = carrier.
//! ObjAtIndex + Range/ClosedRange + FiniteSeqSet/SeqSet as before.

use super::helper::set_bound_parameter_count;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::ast::fact::{
    AtomicFact, InFact, IsTupleFact, LessEqualFact, SubsetFact,
};
use crate::ast::obj::{
    ClosedRange, FiniteSeqSet, FiniteSetReduce, FnSet, FunctionSpace, Obj, ObjAtIndex, Product,
    ProductOfFiniteSet, ProductShape, Range, Reduce, SeqSet, SetFormer, StandardSet, Sum,
    SumOfFiniteSet, TupleDim,
};
use crate::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
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
            verify_state,
            &mut reqs,
        )?;
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

    // t[i]: children, then `i $in N+`, `$is_tuple(t)`, `i <= tuple_dim(t)`.
    // Example: `(1, 2)[1]` is WD; `(1, 2)[0]` fails `0 $in N+`; `(1, 2)[3]` fails bound.
    pub(super) fn verify_obj_at_index_obj_well_definedness_by_def(
        &mut self,
        value: &ObjAtIndex,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.obj.as_ref(),
            value.index.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.index.as_ref(),
            StandardSet::NPos,
            verify_state.clone(),
            format!("index {} is not a positive integer", value.index.ir()),
        )?);
        let is_tuple = AtomicFact::IsTupleFact(IsTupleFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: value.obj.as_ref().clone(),
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            is_tuple,
            verify_state.clone(),
            format!("index target {} is not a tuple", value.obj.ir()),
        )?);
        let tuple_dim: Obj = Obj::ProductShape(ProductShape::TupleDim(TupleDim {
            arg: value.obj.clone(),
        }));
        let bounded = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.index.as_ref().clone(),
            right: tuple_dim.clone(),
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            bounded,
            verify_state,
            format!("{} <= {} is unknown", value.index.ir(), tuple_dim.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
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
                    reqs.push(self.require_obj_subset_of_standard_set(
                        fn_set.ret_set.as_ref(),
                        StandardSet::C,
                        verify_state,
                        format!(
                            "{operation}: iterand return set {} is not verified ⊆ C",
                            fn_set.ret_set.ir()
                        ),
                    )?);
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
            verify_state,
            reqs,
        )?;
        Ok(())
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

    fn require_obj_subset_of_standard_set(
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
