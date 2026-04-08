use crate::prelude::*;
use crate::verify::*;
use std::collections::{HashMap, HashSet};

/// 按 `flat_original` 与 `mangled_by_index` 把各组形参换成同一套存储名（与 [`FnSet::get_params`] 展平顺序一致）。
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
) -> NonErrStmtExecResult {
    NonErrStmtExecResult::FactualStmtSuccess(
        FactualStmtSuccess::new_with_verified_by_builtin_rules(
            Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
            InferResult::new(),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

fn not_in_fact_verified_by_builtin_rules_result(
    not_in_fact: &NotInFact,
    reason: &str,
) -> NonErrStmtExecResult {
    NonErrStmtExecResult::FactualStmtSuccess(
        FactualStmtSuccess::new_with_verified_by_builtin_rules(
            Fact::AtomicFact(AtomicFact::NotInFact(not_in_fact.clone())),
            InferResult::new(),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

fn arithmetic_obj_in_r_verified_by_builtin_rules_result(in_fact: &InFact) -> NonErrStmtExecResult {
    NonErrStmtExecResult::FactualStmtSuccess(
        FactualStmtSuccess::new_with_verified_by_builtin_rules(
            Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
            InferResult::new(),
            "arithmetic expression is in R".to_string(),
            Vec::new(),
        ),
    )
}

fn builtin_in_fact_result_for_evaluated_number_in_standard_set(
    in_fact: &InFact,
    evaluated_number: &Number,
    standard_set: &StandardSet,
) -> NonErrStmtExecResult {
    match standard_set {
        StandardSet::R => number_in_set_verified_by_builtin_rules_result(in_fact, "number in R"),
        StandardSet::RPos => {
            if number_is_in_r_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_pos")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::RNeg => {
            if number_is_in_r_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_neg")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::RNz => {
            if number_is_in_r_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_nz")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::Q => number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q"),
        StandardSet::QPos => {
            if number_is_in_q_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_pos")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QNeg => {
            if number_is_in_q_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_neg")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QNz => {
            if number_is_in_q_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_nz")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::Z => {
            if number_is_in_z(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNeg => {
            if number_is_in_z_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z_neg")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNz => {
            if number_is_in_z_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z_nz")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::N => {
            if number_is_in_n(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::NPos => {
            if number_is_in_n_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N_pos")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
    }
}

fn builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
    not_in_fact: &NotInFact,
    evaluated_number: &Number,
    standard_set: &StandardSet,
) -> NonErrStmtExecResult {
    match standard_set {
        StandardSet::R | StandardSet::Q => NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()),
        StandardSet::RPos => {
            if !number_is_in_r_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R_pos")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::RNeg => {
            if !number_is_in_r_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R_neg")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::RNz => {
            if !number_is_in_r_nz(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R_nz")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QPos => {
            if !number_is_in_q_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q_pos")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QNeg => {
            if !number_is_in_q_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q_neg")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QNz => {
            if !number_is_in_q_nz(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q_nz")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::Z => {
            if !number_is_in_z(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNeg => {
            if !number_is_in_z_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z_neg")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNz => {
            if !number_is_in_z_nz(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z_nz")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::N => {
            if !number_is_in_n(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in N")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::NPos => {
            if !number_is_in_n_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in N_pos")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
    }
}

impl Runtime {
    pub fn verify_not_in_fact_with_builtin_rules(
        &mut self,
        not_in_fact: &NotInFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
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
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    pub fn verify_in_fact_with_builtin_rules(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
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
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet(StandardSet::RNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::RNeg,
            ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet(StandardSet::QNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::QNeg,
            ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet(StandardSet::ZNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::ZNeg,
            ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
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

    fn verify_in_fact_arithmetic_expression_in_standard_negative_set(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
        target_negative_standard_set: StandardSet,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &target_negative_standard_set,
            ));
        }
        let mul = match &in_fact.element {
            Obj::Mul(mul) => mul,
            _ => return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        };
        let product_in_r_fact = AtomicFact::InFact(InFact::new(
            in_fact.element.clone(),
            Obj::StandardSet(StandardSet::R),
            in_fact.line_file.clone(),
        ));
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &product_in_r_fact,
            verify_state,
        )? {
            return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
        }
        if !self
            .mul_product_negative_when_factors_have_strict_opposite_sign_by_non_equational_verify(
                &mul.left,
                &mul.right,
                in_fact.line_file.clone(),
                verify_state,
            )?
        {
            return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
        }
        match target_negative_standard_set {
            StandardSet::RNeg => Ok(NonErrStmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules(
                    Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                    InferResult::new(),
                    "mul_opposite_signs_product_in_R_neg".to_string(),
                    Vec::new(),
                ),
            )),
            StandardSet::QNeg => {
                let product_in_q_fact = AtomicFact::InFact(InFact::new(
                    in_fact.element.clone(),
                    Obj::StandardSet(StandardSet::Q),
                    in_fact.line_file.clone(),
                ));
                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &product_in_q_fact,
                    verify_state,
                )? {
                    Ok(NonErrStmtExecResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules(
                            Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                            InferResult::new(),
                            "mul_opposite_signs_product_in_Q_neg".to_string(),
                            Vec::new(),
                        ),
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            StandardSet::ZNeg => {
                let product_in_z_fact = AtomicFact::InFact(InFact::new(
                    in_fact.element.clone(),
                    Obj::StandardSet(StandardSet::Z),
                    in_fact.line_file.clone(),
                ));
                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &product_in_z_fact,
                    verify_state,
                )? {
                    Ok(NonErrStmtExecResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules(
                            Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                            InferResult::new(),
                            "mul_opposite_signs_product_in_Z_neg".to_string(),
                            Vec::new(),
                        ),
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    fn verify_in_fact_list_set_in_power_set_defines_membership(
        &mut self,
        in_fact: &InFact,
        list_set: &crate::obj::ListSet,
        power_set: &crate::obj::PowerSet,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let base_set = power_set.set.as_ref();
        let mut infer_result = InferResult::new();
        for element_box in list_set.list.iter() {
            let element_obj = *element_box.clone();
            let element_in_base_fact = AtomicFact::InFact(InFact::new(
                element_obj,
                base_set.clone(),
                in_fact.line_file.clone(),
            ));
            let verify_one_element_result =
                self.verify_atomic_fact(&element_in_base_fact, verify_state)?;
            if !verify_one_element_result.is_true() {
                return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
            }
            match verify_one_element_result {
                NonErrStmtExecResult::FactualStmtSuccess(factual_success) => {
                    infer_result.new_infer_result_inside(factual_success.infers.clone());
                }
                NonErrStmtExecResult::NonFactualStmtSuccess(non_factual_success) => {
                    infer_result.new_infer_result_inside(non_factual_success.infers.clone());
                }
                NonErrStmtExecResult::StmtUnknown(_) => {
                    return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
                }
            }
        }
        Ok(NonErrStmtExecResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules(
                Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                infer_result,
                "list_set in power_set: each element is in the base set".to_string(),
                Vec::new(),
            ),
        ))
    }

    fn verify_in_fact_by_equal_to_one_element_in_list_set(
        &mut self,
        in_fact: &InFact,
        list_set: &crate::obj::ListSet,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        for current_element_in_list_set in list_set.list.iter() {
            let equal_fact = AtomicFact::EqualFact(EqualFact::new(
                in_fact.element.clone(),
                *current_element_in_list_set.clone(),
                in_fact.line_file.clone(),
            ));
            let equal_fact_verify_result = self.verify_atomic_fact(&equal_fact, verify_state)?;
            if equal_fact_verify_result.is_true() {
                return Ok(NonErrStmtExecResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules(
                        Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                        InferResult::new(),
                        format!(
                            "{} equals one element in list_set {}",
                            in_fact.element, in_fact.set
                        ),
                        Vec::new(),
                    ),
                ));
            }
        }
        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn standard_subset_set_objs_for_target_set(target_set_obj: &Obj) -> Option<Vec<Obj>> {
        match target_set_obj {
            Obj::StandardSet(StandardSet::NPos) => Some(vec![]),
            Obj::StandardSet(StandardSet::N) => Some(vec![Obj::StandardSet(StandardSet::NPos)]),
            Obj::StandardSet(StandardSet::ZNeg) => Some(vec![]),
            Obj::StandardSet(StandardSet::ZNz) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::ZNeg),
            ]),
            Obj::StandardSet(StandardSet::Z) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::N),
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::ZNz),
            ]),
            Obj::StandardSet(StandardSet::QPos) => Some(vec![Obj::StandardSet(StandardSet::NPos)]),
            Obj::StandardSet(StandardSet::QNeg) => Some(vec![Obj::StandardSet(StandardSet::ZNeg)]),
            Obj::StandardSet(StandardSet::QNz) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::ZNz),
                Obj::StandardSet(StandardSet::QPos),
                Obj::StandardSet(StandardSet::QNeg),
            ]),
            Obj::StandardSet(StandardSet::Q) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::N),
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::ZNz),
                Obj::StandardSet(StandardSet::Z),
                Obj::StandardSet(StandardSet::QPos),
                Obj::StandardSet(StandardSet::QNeg),
                Obj::StandardSet(StandardSet::QNz),
            ]),
            Obj::StandardSet(StandardSet::RPos) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::QPos),
            ]),
            Obj::StandardSet(StandardSet::RNeg) => Some(vec![
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::QNeg),
            ]),
            Obj::StandardSet(StandardSet::RNz) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::ZNz),
                Obj::StandardSet(StandardSet::QPos),
                Obj::StandardSet(StandardSet::QNeg),
                Obj::StandardSet(StandardSet::QNz),
                Obj::StandardSet(StandardSet::RPos),
                Obj::StandardSet(StandardSet::RNeg),
            ]),
            Obj::StandardSet(StandardSet::R) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::N),
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::ZNz),
                Obj::StandardSet(StandardSet::Z),
                Obj::StandardSet(StandardSet::QPos),
                Obj::StandardSet(StandardSet::QNeg),
                Obj::StandardSet(StandardSet::QNz),
                Obj::StandardSet(StandardSet::Q),
                Obj::StandardSet(StandardSet::RPos),
                Obj::StandardSet(StandardSet::RNeg),
                Obj::StandardSet(StandardSet::RNz),
            ]),
            _ => None,
        }
    }

    /// `fn(x N_pos) R` 与 `fn(y N_pos) R`：为每维生成随机基名并加 `__` 前缀，两侧代入同一套存储名后对 `params` / `dom` / `ret` 比较 `Display`。
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
            mangled_placeholders.push(format!(
                "{}{}",
                DEFAULT_MANGLED_FN_PARAM_PREFIX,
                base
            ));
        }

        let mut pa_map = HashMap::new();
        let mut pb_map = HashMap::new();
        for i in 0..n {
            let ph = mangled_placeholders[i].clone();
            pa_map.insert(pa[i].clone(), Obj::Identifier(Identifier::new(ph.clone())));
            pb_map.insert(pb[i].clone(), Obj::Identifier(Identifier::new(ph)));
        }

        let a_params = param_def_with_set_rename_to_mangled(&a.params_def_with_set, &pa, &mangled_placeholders);
        let b_params = param_def_with_set_rename_to_mangled(&b.params_def_with_set, &pb, &mangled_placeholders);

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

        let a_instantiated = FnSet::new(a_params, a_dom, a_ret);
        let b_instantiated = FnSet::new(b_params, b_dom, b_ret);

        Ok(a_instantiated.to_string() == b_instantiated.to_string())
    }

    /// 若环境中已有 `identifier $in fn_定义`（由先前推断写入 `known_obj_in_fn_set`），则与当前 `fn ...` 右侧做 α-等价比较。
    fn verify_in_fact_identifier_in_fn_set_by_stored_definition(
        &mut self,
        identifier: &Identifier,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let element_obj = Obj::Identifier(Identifier::new(identifier.name.clone()));
        let Some(stored_fn_set) = self.get_cloned_object_in_fn_set(&element_obj) else {
            return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
        };
        if self.fn_set_with_params_equal_modulo_param_rename(&stored_fn_set, expected_fn_set)
            .map_err(|e| {
                RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                    Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                    String::new(),
                    in_fact.line_file.clone(),
                    Some(e),
                )
            })?
        {
            return Ok(NonErrStmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules(
                    Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                    InferResult::new(),
                    "fn membership: stored fn signature matches RHS (α-renamed compare)"
                        .to_string(),
                    Vec::new(),
                ),
            ));
        }
        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_in_fact_by_known_standard_subset_membership(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let standard_subset_set_objs =
            match Self::standard_subset_set_objs_for_target_set(target_set_obj) {
                Some(standard_subset_set_objs) => standard_subset_set_objs,
                None => return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
            };
        for standard_subset_set_obj in standard_subset_set_objs.iter() {
            let in_fact_into_standard_subset = AtomicFact::InFact(InFact::new(
                in_fact.element.clone(),
                standard_subset_set_obj.clone(),
                in_fact.line_file.clone(),
            ));
            let verify_result = self
                .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                    &in_fact_into_standard_subset,
                )?;
            if verify_result.is_true() {
                return Ok(NonErrStmtExecResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules(
                        Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                        InferResult::new(),
                        format!(
                            "{} in {} implies in {} (standard subset relation)",
                            in_fact.element, standard_subset_set_obj, target_set_obj
                        ),
                        Vec::new(),
                    ),
                ));
            }
        }
        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_in_fact_by_left_is_tuple_right_is_cart(
        &mut self,
        in_fact: &InFact,
        tuple: &Tuple,
        cart: &Cart,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        if tuple.args.len() != cart.args.len() {
            return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
        }

        for component_index in 0..tuple.args.len() {
            let tuple_component_obj = (*tuple.args[component_index]).clone();
            let cart_component_obj = (*cart.args[component_index]).clone();
            let component_in_fact = AtomicFact::InFact(InFact::new(
                tuple_component_obj,
                cart_component_obj,
                in_fact.line_file.clone(),
            ));
            let component_verify_result =
                self.verify_atomic_fact(&component_in_fact, verify_state)?;
            if !component_verify_result.is_true() {
                return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
            }
        }

        Ok(NonErrStmtExecResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules(
                Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                InferResult::new(),
                "tuple in cart: each component is in the corresponding cart factor".to_string(),
                Vec::new(),
            ),
        ))
    }
}
