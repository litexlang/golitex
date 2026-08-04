use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::{
    factual_equal_success_by_builtin_reason, verify_equality_by_they_are_the_same,
};

impl Runtime {
    pub fn objs_have_same_known_equality_rc_in_some_env(&self, left: &Obj, right: &Obj) -> bool {
        let left_key = obj_equality_key(left);
        let right_key = obj_equality_key(right);
        self.get_all_objs_equal_to_given(&left_key)
            .contains(&right_key)
    }

    pub fn verify_objs_are_equal_by_known_equality(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> StmtResult {
        let goal: AtomicFact =
            EqualFact::new(left.clone(), right.clone(), line_file.clone()).into();
        if let Some(memoized_result) = self.verify_atomic_fact_from_statement_memo(&goal) {
            return memoized_result;
        }

        let direct_result =
            self.verify_objs_are_equal_directly_known_only(left, right, line_file.clone());
        if direct_result.is_true() {
            return direct_result;
        }

        StmtResult::Unknown(StmtUnknown::new())
    }

    fn verify_objs_are_equal_directly_known_only(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> StmtResult {
        if verify_equality_by_they_are_the_same(left, right) {
            return factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "known-only equality: they are the same",
            );
        }

        if self.objs_have_same_known_equality_rc_in_some_env(left, right) {
            return factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "known-only equality: same known equality class",
            );
        }

        let left_resolved = self.resolve_obj(left);
        let right_resolved = self.resolve_obj(right);
        if left_resolved.to_string() != left.to_string()
            || right_resolved.to_string() != right.to_string()
        {
            if left_resolved.two_objs_can_be_calculated_and_equal_by_calculation(&right_resolved) {
                return factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "calculation",
                );
            }
            if verify_equality_by_they_are_the_same(&left_resolved, &right_resolved)
                || self
                    .objs_have_same_known_equality_rc_in_some_env(&left_resolved, &right_resolved)
            {
                return factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "known-only equality: resolved objects match",
                );
            }
        }

        StmtResult::Unknown(StmtUnknown::new())
    }

    pub(crate) fn objs_are_congruent_by_known_equalities(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> bool {
        if self
            .verify_objs_are_equal_directly_known_only(left, right, line_file.clone())
            .is_true()
        {
            return true;
        }

        let result: Result<bool, ()> = Self::same_shape_and_corresponding_args_match(
            left,
            right,
            &mut |left_arg, right_arg| {
                Ok(self.objs_are_congruent_by_known_equalities(
                    left_arg,
                    right_arg,
                    line_file.clone(),
                ))
            },
        );
        result.expect("known-equality comparison is infallible")
    }

    pub(crate) fn objs_are_congruent_by_replay_safe_equality_routes(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let candidate_fact: AtomicFact =
            EqualFact::new(left.clone(), right.clone(), line_file.clone()).into();
        let leaf_result = self
            .verify_atomic_fact_with_non_forall_facts_then_with_builtin_computation(
                &candidate_fact,
            )?;
        if leaf_result.is_true() {
            return Ok(true);
        }

        Self::same_shape_and_corresponding_args_match(left, right, &mut |left_arg, right_arg| {
            self.objs_are_congruent_by_replay_safe_equality_routes(
                left_arg,
                right_arg,
                line_file.clone(),
            )
        })
    }

    pub(crate) fn same_shape_and_corresponding_args_match<E>(
        left: &Obj,
        right: &Obj,
        compare: &mut impl FnMut(&Obj, &Obj) -> Result<bool, E>,
    ) -> Result<bool, E> {
        macro_rules! compare_pairs {
            ($(($left_arg:expr, $right_arg:expr)),+ $(,)?) => {{
                $(
                    if !compare($left_arg, $right_arg)? {
                        return Ok(false);
                    }
                )+
                Ok(true)
            }};
        }

        macro_rules! compare_slices {
            ($left_values:expr, $right_values:expr) => {{
                if $left_values.len() != $right_values.len() {
                    return Ok(false);
                }
                for (left_value, right_value) in $left_values.iter().zip($right_values.iter()) {
                    if !compare(left_value, right_value)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }};
        }

        match (left, right) {
            (Obj::StructObj(left), Obj::StructObj(right)) => {
                if left.name != right.name {
                    return Ok(false);
                }
                compare_slices!(left.params, right.params)
            }
            (
                Obj::ObjAsStructInstanceWithFieldAccess(left),
                Obj::ObjAsStructInstanceWithFieldAccess(right),
            ) => {
                if left.field_name != right.field_name
                    || left.struct_obj.name != right.struct_obj.name
                    || left.struct_obj.params.len() != right.struct_obj.params.len()
                {
                    return Ok(false);
                }
                if !compare(left.obj.as_ref(), right.obj.as_ref())? {
                    return Ok(false);
                }
                compare_slices!(left.struct_obj.params, right.struct_obj.params)
            }
            (Obj::FnObj(left), Obj::FnObj(right)) => {
                let mut left_group_count = left.body.len();
                let mut right_group_count = right.body.len();
                while left_group_count > 0 && right_group_count > 0 {
                    let left_group = &left.body[left_group_count - 1];
                    let right_group = &right.body[right_group_count - 1];
                    if left_group.len() != right_group.len() {
                        return Ok(false);
                    }
                    for (left_arg, right_arg) in left_group.iter().zip(right_group.iter()) {
                        if !compare(left_arg, right_arg)? {
                            return Ok(false);
                        }
                    }
                    left_group_count -= 1;
                    right_group_count -= 1;
                }
                let left_prefix = left.prefix_obj(left_group_count);
                let right_prefix = right.prefix_obj(right_group_count);
                compare(&left_prefix, &right_prefix)
            }
            (Obj::Add(left), Obj::Add(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::Sub(left), Obj::Sub(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::Mul(left), Obj::Mul(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::Div(left), Obj::Div(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::Mod(left), Obj::Mod(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::Gcd(left), Obj::Gcd(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::Lcm(left), Obj::Lcm(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::Min(left), Obj::Min(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::Max(left), Obj::Max(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::Pow(left), Obj::Pow(right)) => {
                compare_pairs!((&left.base, &right.base), (&left.exponent, &right.exponent),)
            }
            (Obj::Log(left), Obj::Log(right)) => {
                compare_pairs!((&left.base, &right.base), (&left.arg, &right.arg),)
            }
            (Obj::Abs(left), Obj::Abs(right)) => compare(&left.arg, &right.arg),
            (Obj::Floor(left), Obj::Floor(right)) => compare(&left.arg, &right.arg),
            (Obj::Ceil(left), Obj::Ceil(right)) => compare(&left.arg, &right.arg),
            (Obj::Exp(left), Obj::Exp(right)) => compare(&left.arg, &right.arg),
            (Obj::Ln(left), Obj::Ln(right)) => compare(&left.arg, &right.arg),
            (Obj::Sign(left), Obj::Sign(right)) => compare(&left.arg, &right.arg),
            (Obj::Factorial(left), Obj::Factorial(right)) => compare(&left.arg, &right.arg),
            (Obj::Sin(left), Obj::Sin(right)) => compare(&left.arg, &right.arg),
            (Obj::Cos(left), Obj::Cos(right)) => compare(&left.arg, &right.arg),
            (Obj::Tan(left), Obj::Tan(right)) => compare(&left.arg, &right.arg),
            (Obj::Cot(left), Obj::Cot(right)) => compare(&left.arg, &right.arg),
            (Obj::Sqrt(left), Obj::Sqrt(right)) => compare(&left.arg, &right.arg),
            (Obj::MatrixAdd(left), Obj::MatrixAdd(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::MatrixSub(left), Obj::MatrixSub(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::MatrixMul(left), Obj::MatrixMul(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::MatrixScalarMul(left), Obj::MatrixScalarMul(right)) => {
                compare_pairs!((&left.scalar, &right.scalar), (&left.matrix, &right.matrix),)
            }
            (Obj::MatrixPow(left), Obj::MatrixPow(right)) => {
                compare_pairs!((&left.base, &right.base), (&left.exponent, &right.exponent),)
            }
            (Obj::Union(left), Obj::Union(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::Intersect(left), Obj::Intersect(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::SetMinus(left), Obj::SetMinus(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::SetDiff(left), Obj::SetDiff(right)) => {
                compare_pairs!((&left.left, &right.left), (&left.right, &right.right),)
            }
            (Obj::BigUnion(left), Obj::BigUnion(right)) => compare(&left.left, &right.left),
            (Obj::BigIntersect(left), Obj::BigIntersect(right)) => compare(&left.left, &right.left),
            (Obj::PowerSet(left), Obj::PowerSet(right)) => compare(&left.set, &right.set),
            (Obj::CartDim(left), Obj::CartDim(right)) => compare(&left.set, &right.set),
            (Obj::TupleDim(left), Obj::TupleDim(right)) => compare(&left.arg, &right.arg),
            (Obj::FiniteSetSize(left), Obj::FiniteSetSize(right)) => compare(&left.set, &right.set),
            (Obj::FiniteSetMax(left), Obj::FiniteSetMax(right)) => compare(&left.set, &right.set),
            (Obj::FiniteSetMin(left), Obj::FiniteSetMin(right)) => compare(&left.set, &right.set),
            (Obj::FnRange(left), Obj::FnRange(right)) => compare(&left.function, &right.function),
            (Obj::Replacement(left), Obj::Replacement(right)) => {
                if left.prop_name.to_string() != right.prop_name.to_string() {
                    return Ok(false);
                }
                compare(&left.source_set, &right.source_set)
            }
            (Obj::Range(left), Obj::Range(right)) => {
                compare_pairs!((&left.start, &right.start), (&left.end, &right.end),)
            }
            (Obj::Sum(left), Obj::Sum(right)) => compare_pairs!(
                (&left.start, &right.start),
                (&left.end, &right.end),
                (left.func.as_ref(), right.func.as_ref()),
            ),
            (Obj::SumOfFiniteSet(left), Obj::SumOfFiniteSet(right)) => compare_pairs!(
                (left.set.as_ref(), right.set.as_ref()),
                (left.func.as_ref(), right.func.as_ref()),
            ),
            (Obj::ProductOfFiniteSet(left), Obj::ProductOfFiniteSet(right)) => compare_pairs!(
                (left.set.as_ref(), right.set.as_ref()),
                (left.func.as_ref(), right.func.as_ref()),
            ),
            (Obj::Product(left), Obj::Product(right)) => compare_pairs!(
                (&left.start, &right.start),
                (&left.end, &right.end),
                (left.func.as_ref(), right.func.as_ref()),
            ),
            (Obj::ClosedRange(left), Obj::ClosedRange(right)) => {
                compare_pairs!((&left.start, &right.start), (&left.end, &right.end),)
            }
            (Obj::IntervalObj(left), Obj::IntervalObj(right)) => {
                if left.left_closed() != right.left_closed()
                    || left.right_closed() != right.right_closed()
                {
                    return Ok(false);
                }
                compare_pairs!((left.start(), right.start()), (left.end(), right.end()),)
            }
            (Obj::OneSideInfinityIntervalObj(left), Obj::OneSideInfinityIntervalObj(right)) => {
                if !left.same_kind_as(right) {
                    return Ok(false);
                }
                compare(left.start(), right.start())
            }
            (Obj::FiniteSeqSet(left), Obj::FiniteSeqSet(right)) => {
                compare_pairs!((&left.set, &right.set), (&left.n, &right.n),)
            }
            (Obj::SeqSet(left), Obj::SeqSet(right)) => {
                compare(left.set.as_ref(), right.set.as_ref())
            }
            (Obj::FiniteSeqListObj(left), Obj::FiniteSeqListObj(right)) => {
                compare_slices!(left.objs, right.objs)
            }
            (Obj::MatrixSet(left), Obj::MatrixSet(right)) => compare_pairs!(
                (&left.set, &right.set),
                (&left.row_len, &right.row_len),
                (&left.col_len, &right.col_len),
            ),
            (Obj::MatrixListObj(left), Obj::MatrixListObj(right)) => {
                if left.rows.len() != right.rows.len() {
                    return Ok(false);
                }
                for (left_row, right_row) in left.rows.iter().zip(right.rows.iter()) {
                    if left_row.len() != right_row.len() {
                        return Ok(false);
                    }
                    for (left_cell, right_cell) in left_row.iter().zip(right_row.iter()) {
                        if !compare(left_cell, right_cell)? {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            (Obj::Proj(left), Obj::Proj(right)) => {
                compare_pairs!((&left.set, &right.set), (&left.dim, &right.dim),)
            }
            (Obj::ObjAtIndex(left), Obj::ObjAtIndex(right)) => {
                compare_pairs!((&left.obj, &right.obj), (&left.index, &right.index),)
            }
            (Obj::Tuple(left), Obj::Tuple(right)) => compare_slices!(left.args, right.args),
            (Obj::ListSet(left), Obj::ListSet(right)) => compare_slices!(left.list, right.list),
            (Obj::Cart(left), Obj::Cart(right)) => compare_slices!(left.args, right.args),
            _ => Ok(false),
        }
    }

    pub fn verify_objs_are_equal_in_equality_builtin(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let fact: AtomicFact = EqualFact::new(left.clone(), right.clone(), line_file).into();
        self.verify_builtin_rule_premise(&fact, builtin_state)
    }

    pub fn verify_equality_by_they_are_the_same_and_calculation(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        _builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<(StmtResult, Obj, Obj), RuntimeError> {
        if verify_equality_by_they_are_the_same(left, right) {
            return Ok((
                factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "they are the same",
                ),
                left.clone(),
                right.clone(),
            ));
        }

        let left_resolved = self.resolve_obj(left);
        let right_resolved = self.resolve_obj(right);

        if left_resolved.two_objs_can_be_calculated_and_equal_by_calculation(&right_resolved) {
            return Ok((
                factual_equal_success_by_builtin_reason(left, right, line_file, "calculation"),
                left_resolved,
                right_resolved,
            ));
        }

        Ok((
            StmtResult::Unknown(StmtUnknown::new()),
            left_resolved,
            right_resolved,
        ))
    }
}
