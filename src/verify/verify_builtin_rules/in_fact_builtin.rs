use crate::prelude::*;
use crate::verify::{
    number_is_in_n, number_is_in_n_pos, number_is_in_q_neg, number_is_in_q_nz, number_is_in_q_pos,
    number_is_in_r_neg, number_is_in_r_nz, number_is_in_r_pos, number_is_in_z, number_is_in_z_neg,
    number_is_in_z_nz, VerifyState,
};
use std::collections::{HashMap, HashSet};

// Rename param groups to mangled storage names using `flat_original` and `mangled_by_index`
// (same flatten order as `FnSet::get_params`).
fn param_def_with_set_rename_to_mangled(
    groups: &[ParamGroupWithSet],
    flat_original: &[String],
    mangled_by_index: &[String],
) -> Vec<ParamGroupWithSet> {
    let mut name_to_i: HashMap<String, usize> = HashMap::new();
    for (i, n) in flat_original.iter().enumerate() {
        name_to_i.insert(n.clone(), i);
    }
    let mut out = Vec::with_capacity(groups.len());
    for g in groups {
        let new_names: Vec<String> = g
            .params
            .iter()
            .map(|n| {
                let i = name_to_i[n];
                mangled_by_index[i].clone()
            })
            .collect();
        out.push(ParamGroupWithSet::new(new_names, g.set.clone()));
    }
    out
}

fn number_in_set_verified_by_builtin_rules_result(
    in_fact: &InFact,
    reason: &str,
) -> StmtResult {
    StmtResult::FactualStmtSuccess(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

fn not_in_fact_verified_by_builtin_rules_result(
    not_in_fact: &NotInFact,
    reason: &str,
) -> StmtResult {
    StmtResult::FactualStmtSuccess(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            not_in_fact.clone().into(),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

fn arithmetic_obj_in_r_verified_by_builtin_rules_result(in_fact: &InFact) -> StmtResult {
    StmtResult::FactualStmtSuccess(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            "arithmetic expression is in R".to_string(),
            Vec::new(),
        ),
    )
}

fn builtin_in_fact_result_for_evaluated_number_in_standard_set(
    in_fact: &InFact,
    evaluated_number: &Number,
    standard_set: &StandardSet,
) -> StmtResult {
    match standard_set {
        StandardSet::R => number_in_set_verified_by_builtin_rules_result(in_fact, "number in R"),
        StandardSet::RPos => {
            if number_is_in_r_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_pos")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::RNeg => {
            if number_is_in_r_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_neg")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::RNz => {
            if number_is_in_r_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_nz")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::Q => number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q"),
        StandardSet::QPos => {
            if number_is_in_q_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_pos")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QNeg => {
            if number_is_in_q_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_neg")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QNz => {
            if number_is_in_q_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_nz")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::Z => {
            if number_is_in_z(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNeg => {
            if number_is_in_z_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z_neg")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNz => {
            if number_is_in_z_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z_nz")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::N => {
            if number_is_in_n(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::NPos => {
            if number_is_in_n_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N_pos")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
    }
}

fn builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
    not_in_fact: &NotInFact,
    evaluated_number: &Number,
    standard_set: &StandardSet,
) -> StmtResult {
    match standard_set {
        StandardSet::R | StandardSet::Q => StmtResult::StmtUnknown(StmtUnknown::new()),
        StandardSet::RPos => {
            if !number_is_in_r_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R_pos")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::RNeg => {
            if !number_is_in_r_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R_neg")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::RNz => {
            if !number_is_in_r_nz(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R_nz")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QPos => {
            if !number_is_in_q_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q_pos")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QNeg => {
            if !number_is_in_q_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q_neg")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QNz => {
            if !number_is_in_q_nz(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q_nz")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::Z => {
            if !number_is_in_z(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNeg => {
            if !number_is_in_z_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z_neg")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNz => {
            if !number_is_in_z_nz(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z_nz")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::N => {
            if !number_is_in_n(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in N")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::NPos => {
            if !number_is_in_n_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in N_pos")
            } else {
                StmtResult::StmtUnknown(StmtUnknown::new())
            }
        }
    }
}

impl Runtime {
    pub fn verify_not_in_fact_with_builtin_rules(
        &mut self,
        not_in_fact: &NotInFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Obj::StandardSet(standard_set) = &not_in_fact.set {
            if !matches!(&not_in_fact.element, Obj::Number(_)) {
                if let Some(evaluated_number) =
                    not_in_fact.element.evaluate_to_normalized_decimal_number()
                {
                    return Ok(
                        builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
                            not_in_fact,
                            &evaluated_number,
                            standard_set,
                        ),
                    );
                }
            }
        }
        match (&not_in_fact.element, &not_in_fact.set) {
            (Obj::Number(num), Obj::StandardSet(standard_set)) => Ok(
                builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
                    not_in_fact,
                    num,
                    standard_set,
                ),
            ),
            _ => Ok((StmtUnknown::new()).into()),
        }
    }

    pub fn verify_in_fact_with_builtin_rules(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Obj::StandardSet(standard_set) = &in_fact.set {
            if !matches!(&in_fact.element, Obj::Number(_)) {
                if let Some(evaluated_number) =
                    in_fact.element.evaluate_to_normalized_decimal_number()
                {
                    let evaluation_membership_result =
                        builtin_in_fact_result_for_evaluated_number_in_standard_set(
                            in_fact,
                            &evaluated_number,
                            standard_set,
                        );
                    return Ok(evaluation_membership_result);
                }
            }
        }
        match (&in_fact.element, &in_fact.set) {
            (Obj::Tuple(tuple), Obj::Cart(cart)) => {
                return self.verify_in_fact_by_left_is_tuple_right_is_cart(
                    in_fact,
                    tuple,
                    cart,
                    verify_state,
                );
            }
            (Obj::Number(num), Obj::StandardSet(standard_set)) => {
                Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                    in_fact,
                    num,
                    standard_set,
                ))
            }
            (_, Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_n_pos_by_zero_less_and_in_z_or_n(in_fact, verify_state),
            (_, Obj::ClosedRange(closed_range)) => {
                self.verify_in_fact_closed_range_by_order_bounds(in_fact, closed_range, verify_state)
            }
            (_, Obj::Range(range)) => {
                self.verify_in_fact_open_range_by_order_bounds(in_fact, range, verify_state)
            }
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Mod(_) | Obj::Pow(_) | Obj::Max(_)
                | Obj::Min(_),
                Obj::StandardSet(StandardSet::Z),
            ) => self.verify_in_fact_arithmetic_expression_in_z(in_fact, verify_state),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Pow(_) | Obj::Max(_)
                | Obj::Min(_),
                Obj::StandardSet(StandardSet::Q),
            ) => self.verify_in_fact_arithmetic_expression_in_q(in_fact, verify_state),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_)
                | Obj::Max(_) | Obj::Min(_),
                Obj::StandardSet(StandardSet::RNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::RNeg,
            ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_)
                | Obj::Max(_) | Obj::Min(_),
                Obj::StandardSet(StandardSet::QNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::QNeg,
            ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_)
                | Obj::Max(_) | Obj::Min(_),
                Obj::StandardSet(StandardSet::ZNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::ZNeg,
            ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_)
                | Obj::Max(_) | Obj::Min(_),
                Obj::StandardSet(StandardSet::R),
            ) => Ok(arithmetic_obj_in_r_verified_by_builtin_rules_result(
                in_fact,
            )),
            (Obj::ListSet(list_set), Obj::PowerSet(power_set)) => self
                .verify_in_fact_list_set_in_power_set_defines_membership(
                    in_fact,
                    list_set,
                    power_set,
                    verify_state,
                ),
            (Obj::Choose(choose), where_is_obj) => {
                let choose_from = choose.set.clone();
                let equal_fact = EqualFact::new(
                    *choose_from,
                    where_is_obj.clone(),
                    in_fact.line_file.clone(),
                ).into();
                let equal_fact_verify_result =
                    self.verify_atomic_fact(&equal_fact, verify_state)?;
                if equal_fact_verify_result.is_true() {
                    return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            in_fact.clone().into(),
                            "By ZFC, we can choose an element from a nonempty set whose elements are all nonempty.".to_string(),
                            Vec::new(),
                        )).into());
                } else {
                    return Ok((StmtUnknown::new()).into());
                }
            }
            (_, Obj::ListSet(list_set)) => self.verify_in_fact_by_equal_to_one_element_in_list_set(
                in_fact,
                list_set,
                verify_state,
            ),
            (Obj::Identifier(identifier), Obj::FnSet(expected_fn_set)) => self
                .verify_in_fact_identifier_in_fn_set_by_stored_definition(
                    identifier,
                    expected_fn_set,
                    in_fact,
                ),
            (_, Obj::FamilyObj(family_ty)) => {
                self.verify_obj_satisfies_family(in_fact.element.clone(), family_ty, verify_state)
            }
            (_, Obj::StructObj(struct_ty)) => self.verify_obj_satisfies_struct_param_type(
                in_fact.element.clone(),
                struct_ty,
                verify_state,
            ),
            (_, target_set_obj) => {
                self.verify_in_fact_by_known_standard_subset_membership(in_fact, target_set_obj)
            }
        }
    }

    // `N_pos` = positive integers: from `0 < x` and (`x $in Z` or `x $in N`).
    fn verify_in_fact_n_pos_by_zero_less_and_in_z_or_n(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let zero: Obj = Number::new("0".to_string()).into();
        let zero_lt_elem = LessFact::new(
            zero,
            elem.clone(),
            lf.clone(),
        ).into();
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &zero_lt_elem,
            verify_state,
        )? {
            return Ok((StmtUnknown::new()).into());
        }

        let in_z = InFact::new(
            elem.clone(),
            StandardSet::Z.into(),
            lf.clone(),
        ).into();
        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(&in_z, verify_state)? {
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "N_pos: 0 < x and x in Z",
            ));
        }

        let in_n = InFact::new(
            elem.clone(),
            StandardSet::N.into(),
            lf.clone(),
        ).into();
        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(&in_n, verify_state)? {
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "N_pos: 0 < x and x in N",
            ));
        }

        Ok((StmtUnknown::new()).into())
    }

    fn verify_in_fact_closed_range_by_order_bounds(
        &mut self,
        in_fact: &InFact,
        closed_range: &ClosedRange,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let a_le_i = LessEqualFact::new(
            (*closed_range.start).clone(),
            elem.clone(),
            lf.clone(),
        ).into();
        let i_le_b = LessEqualFact::new(
            elem.clone(),
            (*closed_range.end).clone(),
            lf.clone(),
        ).into();
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(&a_le_i, verify_state)? {
            return Ok((StmtUnknown::new()).into());
        }
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(&i_le_b, verify_state)? {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            "in closed_range: a <= i and i <= b",
        ))
    }

    fn verify_in_fact_open_range_by_order_bounds(
        &mut self,
        in_fact: &InFact,
        range: &Range,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let a_le_i = LessEqualFact::new(
            (*range.start).clone(),
            elem.clone(),
            lf.clone(),
        ).into();
        let i_lt_b = LessFact::new(
            elem.clone(),
            (*range.end).clone(),
            lf.clone(),
        ).into();
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(&a_le_i, verify_state)? {
            return Ok((StmtUnknown::new()).into());
        }
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(&i_lt_b, verify_state)? {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            "in range: a <= i and i < b",
        ))
    }

    // Builtin closure of `Z` under `+`, `-`, `*`, `mod`, and `^` when direct operands are in `Z`
    // (`Pow` checks `base` and `exponent`; if the power normalizes to a decimal, the numeric branch above applies).
    fn verify_in_fact_arithmetic_expression_in_z(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::Z,
            ));
        }
        let z_obj: Obj = StandardSet::Z.into();
        let lf = in_fact.line_file.clone();

        let mut require_in_z = |o: &Obj| -> Result<bool, RuntimeError> {
            let f = InFact::new(o.clone(), z_obj.clone(), lf.clone()).into();
            self.non_equational_atomic_fact_holds_by_full_verify_pipeline(&f, verify_state)
        };

        let ok = match &in_fact.element {
            Obj::Add(a) => require_in_z(&a.left)? && require_in_z(&a.right)?,
            Obj::Sub(s) => require_in_z(&s.left)? && require_in_z(&s.right)?,
            Obj::Mul(m) => require_in_z(&m.left)? && require_in_z(&m.right)?,
            Obj::Mod(m) => require_in_z(&m.left)? && require_in_z(&m.right)?,
            Obj::Pow(p) => require_in_z(&p.base)? && require_in_z(&p.exponent)?,
            Obj::Max(m) => require_in_z(&m.left)? && require_in_z(&m.right)?,
            Obj::Min(m) => require_in_z(&m.left)? && require_in_z(&m.right)?,
            _ => false,
        };

        if !ok {
            return Ok((StmtUnknown::new()).into());
        }

        Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "Z closure: operands in Z".to_string(),
                Vec::new(),
            )).into())
    }

    // Builtin closure of `Q` under `+`, `-`, `*`, `/` when both operands are in `Q`. For `^`, require
    // `base` in `Q` and `exponent` in `Z` (rational base with integer exponent stays in `Q`).
    fn verify_in_fact_arithmetic_expression_in_q(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::Q,
            ));
        }
        let q_obj: Obj = StandardSet::Q.into();
        let z_obj: Obj = StandardSet::Z.into();
        let lf = in_fact.line_file.clone();

        let in_q =
            |slf: &mut Self, o: &Obj| -> Result<bool, RuntimeError> {
                let f = InFact::new(o.clone(), q_obj.clone(), lf.clone()).into();
                slf.non_equational_atomic_fact_holds_by_full_verify_pipeline(&f, verify_state)
            };
        let in_z =
            |slf: &mut Self, o: &Obj| -> Result<bool, RuntimeError> {
                let f = InFact::new(o.clone(), z_obj.clone(), lf.clone()).into();
                slf.non_equational_atomic_fact_holds_by_full_verify_pipeline(&f, verify_state)
            };

        let ok = match &in_fact.element {
            Obj::Add(a) => in_q(self, &a.left)? && in_q(self, &a.right)?,
            Obj::Sub(s) => in_q(self, &s.left)? && in_q(self, &s.right)?,
            Obj::Mul(m) => in_q(self, &m.left)? && in_q(self, &m.right)?,
            Obj::Div(d) => in_q(self, &d.left)? && in_q(self, &d.right)?,
            Obj::Pow(p) => in_q(self, &p.base)? && in_z(self, &p.exponent)?,
            Obj::Max(m) => in_q(self, &m.left)? && in_q(self, &m.right)?,
            Obj::Min(m) => in_q(self, &m.left)? && in_q(self, &m.right)?,
            _ => false,
        };

        if !ok {
            return Ok((StmtUnknown::new()).into());
        }

        Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "Q closure: +-*/ operands in Q; pow base in Q and exponent in Z".to_string(),
                Vec::new(),
            )).into())
    }

    fn verify_in_fact_arithmetic_expression_in_standard_negative_set(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
        target_negative_standard_set: StandardSet,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &target_negative_standard_set,
            ));
        }
        let mul = match &in_fact.element {
            Obj::Mul(mul) => mul,
            _ => return Ok((StmtUnknown::new()).into()),
        };
        let product_in_r_fact = InFact::new(
            in_fact.element.clone(),
            StandardSet::R.into(),
            in_fact.line_file.clone(),
        ).into();
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &product_in_r_fact,
            verify_state,
        )? {
            return Ok((StmtUnknown::new()).into());
        }
        if !self
            .mul_product_negative_when_factors_have_strict_opposite_sign_by_non_equational_verify(
                &mul.left,
                &mul.right,
                in_fact.line_file.clone(),
                verify_state,
            )?
        {
            return Ok((StmtUnknown::new()).into());
        }
        match target_negative_standard_set {
            StandardSet::RNeg => Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "mul_opposite_signs_product_in_R_neg".to_string(),
                    Vec::new(),
                )).into()),
            StandardSet::QNeg => {
                let product_in_q_fact = InFact::new(
                    in_fact.element.clone(),
                    StandardSet::Q.into(),
                    in_fact.line_file.clone(),
                ).into();
                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &product_in_q_fact,
                    verify_state,
                )? {
                    Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            in_fact.clone().into(),
                            "mul_opposite_signs_product_in_Q_neg".to_string(),
                            Vec::new(),
                        )).into())
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            StandardSet::ZNeg => {
                let product_in_z_fact = InFact::new(
                    in_fact.element.clone(),
                    StandardSet::Z.into(),
                    in_fact.line_file.clone(),
                ).into();
                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &product_in_z_fact,
                    verify_state,
                )? {
                    Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            in_fact.clone().into(),
                            "mul_opposite_signs_product_in_Z_neg".to_string(),
                            Vec::new(),
                        )).into())
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            _ => Ok((StmtUnknown::new()).into()),
        }
    }

    fn verify_in_fact_list_set_in_power_set_defines_membership(
        &mut self,
        in_fact: &InFact,
        list_set: &ListSet,
        power_set: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let base_set = power_set.set.as_ref();
        let mut infer_result = InferResult::new();
        for element_box in list_set.list.iter() {
            let element_obj = *element_box.clone();
            let element_in_base_fact = InFact::new(
                element_obj,
                base_set.clone(),
                in_fact.line_file.clone(),
            ).into();
            let verify_one_element_result =
                self.verify_atomic_fact(&element_in_base_fact, verify_state)?;
            if !verify_one_element_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            match verify_one_element_result {
                StmtResult::FactualStmtSuccess(factual_success) => {
                    infer_result.new_infer_result_inside(factual_success.infers.clone());
                }
                StmtResult::NonFactualStmtSuccess(non_factual_success) => {
                    infer_result.new_infer_result_inside(non_factual_success.infers.clone());
                }
                StmtResult::StmtUnknown(_) => {
                    return Ok((StmtUnknown::new()).into());
                }
            }
        }
        let stmt = in_fact.clone().into();
        infer_result.new_fact(&stmt);
        Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules(
                stmt,
                infer_result,
                "list_set in power_set: each element is in the base set".to_string(),
                Vec::new(),
            )).into())
    }

    fn verify_in_fact_by_equal_to_one_element_in_list_set(
        &mut self,
        in_fact: &InFact,
        list_set: &ListSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        for current_element_in_list_set in list_set.list.iter() {
            let equal_fact = EqualFact::new(
                in_fact.element.clone(),
                *current_element_in_list_set.clone(),
                in_fact.line_file.clone(),
            ).into();
            let equal_fact_verify_result = self.verify_atomic_fact(&equal_fact, verify_state)?;
            if equal_fact_verify_result.is_true() {
                return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        format!(
                            "{} equals one element in list_set {}",
                            in_fact.element, in_fact.set
                        ),
                        Vec::new(),
                    )).into());
            }
        }
        Ok((StmtUnknown::new()).into())
    }

    fn standard_subset_set_objs_for_target_set(target_set_obj: &Obj) -> Option<Vec<Obj>> {
        match target_set_obj {
            Obj::StandardSet(StandardSet::NPos) => Some(vec![]),
            Obj::StandardSet(StandardSet::N) => Some(vec![StandardSet::NPos.into()]),
            Obj::StandardSet(StandardSet::ZNeg) => Some(vec![]),
            Obj::StandardSet(StandardSet::ZNz) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::ZNeg.into(),
            ]),
            Obj::StandardSet(StandardSet::Z) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::N.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
            ]),
            Obj::StandardSet(StandardSet::QPos) => Some(vec![StandardSet::NPos.into()]),
            Obj::StandardSet(StandardSet::QNeg) => Some(vec![StandardSet::ZNeg.into()]),
            Obj::StandardSet(StandardSet::QNz) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
            ]),
            Obj::StandardSet(StandardSet::Q) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::N.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::Z.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
                StandardSet::QNz.into(),
            ]),
            Obj::StandardSet(StandardSet::RPos) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::QPos.into(),
            ]),
            Obj::StandardSet(StandardSet::RNeg) => Some(vec![
                StandardSet::ZNeg.into(),
                StandardSet::QNeg.into(),
            ]),
            Obj::StandardSet(StandardSet::RNz) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
                StandardSet::QNz.into(),
                StandardSet::RPos.into(),
                StandardSet::RNeg.into(),
            ]),
            Obj::StandardSet(StandardSet::R) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::N.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::Z.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
                StandardSet::QNz.into(),
                StandardSet::Q.into(),
                StandardSet::RPos.into(),
                StandardSet::RNeg.into(),
                StandardSet::RNz.into(),
            ]),
            _ => None,
        }
    }

    // `fn(x N_pos) R` vs `fn(y N_pos) R`: pick fresh base names per dimension with `__` prefix, substitute
    // the same storage names on both sides, then compare `Display` of params / dom / ret.
    fn fn_set_with_params_equal_modulo_param_rename(
        &self,
        a: &FnSet,
        b: &FnSet,
    ) -> Result<bool, RuntimeError> {
        let pa = a.get_params();
        let pb = b.get_params();
        if pa.len() != pb.len() {
            return Ok(false);
        }
        let n = pa.len();

        let mut reserved: HashSet<String> = HashSet::new();
        for s in pa.iter().chain(pb.iter()) {
            reserved.insert(s.clone());
        }

        let mut mangled_placeholders: Vec<String> = Vec::with_capacity(n);
        for _ in 0..n {
            let base = self.generate_one_unused_name_with_reserved(&reserved);
            reserved.insert(base.clone());
            mangled_placeholders.push(format!("{}{}", DEFAULT_MANGLED_FN_PARAM_PREFIX, base));
        }

        let mut pa_map = HashMap::new();
        let mut pb_map = HashMap::new();
        for i in 0..n {
            let ph = mangled_placeholders[i].clone();
            pa_map.insert(pa[i].clone(), ph.clone().into());
            pb_map.insert(pb[i].clone(), ph.into());
        }

        let a_params = param_def_with_set_rename_to_mangled(
            &a.params_def_with_set,
            &pa,
            &mangled_placeholders,
        );
        let b_params = param_def_with_set_rename_to_mangled(
            &b.params_def_with_set,
            &pb,
            &mangled_placeholders,
        );

        let a_dom: Vec<OrAndChainAtomicFact> = a
            .dom_facts
            .iter()
            .map(|dom_fact| self.inst_or_and_chain_atomic_fact(dom_fact, &pa_map))
            .collect::<Result<Vec<_>, _>>()?;
        let b_dom: Vec<OrAndChainAtomicFact> = b
            .dom_facts
            .iter()
            .map(|dom_fact| self.inst_or_and_chain_atomic_fact(dom_fact, &pb_map))
            .collect::<Result<Vec<_>, _>>()?;

        let a_ret = a.ret_set.as_ref().clone();
        let b_ret = b.ret_set.as_ref().clone();

        let a_instantiated = self.new_fn_set_and_add_mangled_prefix(a_params, a_dom, a_ret)?;
        let b_instantiated = self.new_fn_set_and_add_mangled_prefix(b_params, b_dom, b_ret)?;

        Ok(a_instantiated.to_string() == b_instantiated.to_string())
    }

    // If the env already has `identifier $in fn_def` (from `known_obj_in_fn_set`), α-compare to the RHS `fn ...`.
    fn verify_in_fact_identifier_in_fn_set_by_stored_definition(
        &mut self,
        identifier: &Identifier,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
        let element_obj = identifier.name.clone().into();
        let Some(stored_fn_set) = self.get_cloned_object_in_fn_set(&element_obj) else {
            return Ok((StmtUnknown::new()).into());
        };
        if self
            .fn_set_with_params_equal_modulo_param_rename(&stored_fn_set, expected_fn_set)
            .map_err(|e| {
                RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                    in_fact.clone().into(),
                    String::new(),
                    in_fact.line_file.clone(),
                    Some(e),
                )
            })?
        {
            return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "fn membership: stored fn signature matches RHS (α-renamed compare)"
                        .to_string(),
                    Vec::new(),
                )).into());
        }
        Ok((StmtUnknown::new()).into())
    }

    fn verify_in_fact_by_known_standard_subset_membership(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
    ) -> Result<StmtResult, RuntimeError> {
        let standard_subset_set_objs =
            match Self::standard_subset_set_objs_for_target_set(target_set_obj) {
                Some(standard_subset_set_objs) => standard_subset_set_objs,
                None => return Ok((StmtUnknown::new()).into()),
            };
        for standard_subset_set_obj in standard_subset_set_objs.iter() {
            let in_fact_into_standard_subset = InFact::new(
                in_fact.element.clone(),
                standard_subset_set_obj.clone(),
                in_fact.line_file.clone(),
            ).into();
            let verify_result = self
                .verify_non_equational_atomic_fact_with_known_atomic_facts(
                    &in_fact_into_standard_subset,
                )?;
            if verify_result.is_true() {
                return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        format!(
                            "{} in {} implies in {} (standard subset relation)",
                            in_fact.element, standard_subset_set_obj, target_set_obj
                        ),
                        Vec::new(),
                    )).into());
            }
        }
        Ok((StmtUnknown::new()).into())
    }

    fn verify_in_fact_by_left_is_tuple_right_is_cart(
        &mut self,
        in_fact: &InFact,
        tuple: &Tuple,
        cart: &Cart,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if tuple.args.len() < 2 {
            return Ok((StmtUnknown::new()).into());
        }
        if tuple.args.len() != cart.args.len() {
            return Ok((StmtUnknown::new()).into());
        }

        for component_index in 0..tuple.args.len() {
            let tuple_component_obj = (*tuple.args[component_index]).clone();
            let cart_component_obj = (*cart.args[component_index]).clone();
            let component_in_fact = InFact::new(
                tuple_component_obj,
                cart_component_obj,
                in_fact.line_file.clone(),
            ).into();
            let component_verify_result =
                self.verify_atomic_fact(&component_in_fact, verify_state)?;
            if !component_verify_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
        }

        Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "tuple in cart: each component is in the corresponding cart factor".to_string(),
                Vec::new(),
            )).into())
    }
}
