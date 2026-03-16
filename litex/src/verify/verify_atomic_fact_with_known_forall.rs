use std::collections::HashMap;
use crate::fact::ExistOrAndChainAtomicFact;
use crate::environment::KnownForallFactParamsAndDom;
use std::rc::Rc;
use crate::error::VerifyError;
use crate::fact::{AtomicFact, ForallFact};
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult, StmtUnknown};
use crate::verify::VerifyState;
use crate::execute::Executor;
use crate::obj::{Identifier, Obj, FnObj};
use crate::stmt::parameter_type_and_property::ParamDefWithParamType;
use std::result::Result;

impl<'a> Executor<'a> {
    pub fn verify_atomic_fact_with_known_forall(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<NonErrStmtExecResult, VerifyError> {
        let key = atomic_fact.key();
        let is_true = atomic_fact.is_true();

        let mut known_facts = Vec::new();
        for current_env in self.runtime_context.environments.iter().rev() {
            if let Some(atomic_fact_in_known_forall_facts) = current_env.known_atomic_facts_in_forall_facts.get(&(key.clone(), is_true)) {
                known_facts.extend(atomic_fact_in_known_forall_facts.iter().rev().cloned());
            }
        }

        let result_in_env = self.match_and_verify_atomic_fact_with_known_forall_facts(
            known_facts,
            atomic_fact,
            verify_state)?;
        if let Some(fact_verified) = result_in_env {
            return Ok(NonErrStmtExecResult::FactVerifiedByFact(fact_verified));
        }

        return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
    }

    fn match_and_verify_atomic_fact_with_known_forall_facts(
        &mut self,
        forall_entries: Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactVerifiedByFact>, VerifyError> {
        for (atomic_fact_in_known_forall_fact, forall_rc) in forall_entries.iter().rev() {
            let match_result =
                Self::match_atomic_fact_in_known_forall_fact_with_given_atomic_fact(
                    atomic_fact_in_known_forall_fact,
                    atomic_fact,
                    verify_state,
                )?;
            if let Some(arg_map) = match_result {
                if let Some(fact_verified) = self.verify_matched_args_satisfy_forall_requirements(
                    atomic_fact_in_known_forall_fact,
                    forall_rc,
                    arg_map,
                    atomic_fact,
                    verify_state,
                )? {
                    return Ok(Some(fact_verified));
                }
            }
        }

        Ok(None)
    }

    fn verify_matched_args_satisfy_forall_requirements(
        &mut self,
        atomic_fact_in_known_forall_fact: &AtomicFact,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        arg_map: HashMap<String, Vec<Obj>>,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactVerifiedByFact>, VerifyError> {
        let param_names = ParamDefWithParamType::collect_param_names(&known_forall.params);

        if !param_names.iter().all(|param_name| arg_map.contains_key(param_name)) {
            return Ok(None);
        }

        for param_name in param_names.iter() {
            let objs = match arg_map.get(param_name) {
                Some(v) => v,
                None => return Ok(None),
            };
            if !self.verify_atom_in_atomic_fact_in_known_forall_fact_matches_equal_objects(
                objs,
                verify_state,
            )? {
                return Ok(None);
            }
        }

        let args_satisfy_param_types = ParamDefWithParamType::facts_for_args_satisfy_param_def_with_type_vec(&known_forall.params, &atomic_fact.args())
            .map_err(|e| VerifyError::new(e.error_body(), vec![e], None))?;

        for fact in args_satisfy_param_types.iter() {
            let result = self.verify_fact(fact, verify_state)?;
            if !result.is_true() {
                return Ok(None);
            }
        }

        
        let param_to_arg_map = match ParamDefWithParamType::param_def_params_to_arg_map(
            &known_forall.params,
            &arg_map,
        ) {
            Some(m) => m,
            None => return Ok(None),
        };

        for dom_fact in known_forall.dom.iter() {
            let instantiated_dom_fact = dom_fact.instantiate(&param_to_arg_map);
            let fact = instantiated_dom_fact.to_fact();
            let result = self.verify_fact(&fact, verify_state)?;
            if !result.is_true() {
                return Ok(None);
            }
        }

        let fact_string = atomic_fact.to_string();
        let verified_by_known_forall_fact = ForallFact::new(
            known_forall.params.clone(),
            known_forall.dom.clone(),
            vec![ExistOrAndChainAtomicFact::AtomicFact(atomic_fact_in_known_forall_fact.clone())],
            known_forall.line_file.clone(),
        );
        let fact_verified = FactVerifiedByFact::new(
            fact_string,
            verified_by_known_forall_fact.to_string(),
            verified_by_known_forall_fact.line_file_index,
        );
        Ok(Some(fact_verified))
    }

    fn verify_atom_in_atomic_fact_in_known_forall_fact_matches_equal_objects(
        &self,
        objs: &Vec<Obj>,
        _verify_state: &VerifyState,
    ) -> Result<bool, VerifyError> {
        let len = objs.len();
        if len <= 1 {
            return Ok(true);
        }

        let mut i = 0;
        while i < len {
            let mut j = i + 1;
            while j < len {
                if !Self::verify_equality_by_they_are_the_same(&objs[i], &objs[j]) {
                    return Ok(false);
                }
                j += 1;
            }
            i += 1;
        }

        Ok(true)
    }

    fn match_atomic_fact_in_known_forall_fact_with_given_atomic_fact(atomic_fact_in_known_forall: &AtomicFact, given_atomic_fact: &AtomicFact, _verify_state: &VerifyState) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        let mut atom_in_known_atomic_fact_to_matched_objs_in_given_fact_map: HashMap<String, Vec<Obj>> = HashMap::new();

        for (arg_in_atomic_fact_in_known_forall, arg_in_given) in atomic_fact_in_known_forall.args().iter().zip(given_atomic_fact.args().iter()) {
            let sub_map_option = Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(arg_in_atomic_fact_in_known_forall, arg_in_given)?;
            let sub_map = match sub_map_option {
                Some(m) => m,
                None => return Ok(None),
            };
            for (k, v) in sub_map {
                atom_in_known_atomic_fact_to_matched_objs_in_given_fact_map.entry(k).or_default().extend(v);
            }
        }

        Ok(Some(atom_in_known_atomic_fact_to_matched_objs_in_given_fact_map))
    }

    fn match_arg_in_atomic_fact_in_known_forall_with_given_arg(arg_in_atomic_fact_in_known_forall: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match arg_in_atomic_fact_in_known_forall {
            Obj::Identifier(ref id_known) => Self::match_arg_when_left_is_identifier(id_known, given_arg),
            Obj::IdentifierWithMod(_) => Self::match_arg_when_left_is_identifier_with_mod(given_arg),
            Obj::FieldAccess(_) => Self::match_arg_when_left_is_field_access(given_arg),
            Obj::FieldAccessWithMod(_) => Self::match_arg_when_left_is_field_access_with_mod(given_arg),
            Obj::FnObj(ref f) => Self::match_arg_when_left_is_fn_obj(f, given_arg),
            Obj::Number(_) => Self::match_arg_when_left_is_number(given_arg),
            Obj::Add(ref a) => Self::match_arg_when_left_is_add(&a.left, &a.right, given_arg),
            Obj::Sub(ref a) => Self::match_arg_when_left_is_sub(&a.left, &a.right, given_arg),
            Obj::Mul(ref a) => Self::match_arg_when_left_is_mul(&a.left, &a.right, given_arg),
            Obj::Div(ref a) => Self::match_arg_when_left_is_div(&a.left, &a.right, given_arg),
            Obj::Mod(ref a) => Self::match_arg_when_left_is_mod(&a.left, &a.right, given_arg),
            Obj::Pow(ref a) => Self::match_arg_when_left_is_pow(&a.base, &a.exponent, given_arg),
            Obj::Union(ref a) => Self::match_arg_when_left_is_union(&a.left, &a.right, given_arg),
            Obj::Intersect(ref a) => Self::match_arg_when_left_is_intersect(&a.left, &a.right, given_arg),
            Obj::SetMinus(ref a) => Self::match_arg_when_left_is_set_minus(&a.left, &a.right, given_arg),
            Obj::SetDiff(ref a) => Self::match_arg_when_left_is_set_diff(&a.left, &a.right, given_arg),
            Obj::Cup(ref a) => Self::match_arg_when_left_is_cup(&a.left, given_arg),
            Obj::Cap(ref a) => Self::match_arg_when_left_is_cap(&a.left, given_arg),
            Obj::ListSet(_) => Self::match_arg_when_left_is_list_set(given_arg),
            Obj::SetBuilder(_) => Self::match_arg_when_left_is_set_builder(given_arg),
            Obj::FnSetWithoutDom(_) => Self::match_arg_when_left_is_fn_set_without_dom(given_arg),
            Obj::FnSetWithDom(_) => Self::match_arg_when_left_is_fn_set_with_dom(given_arg),
            Obj::NPosObj(_) => Self::match_arg_when_left_is_n_pos_obj(given_arg),
            Obj::NObj(_) => Self::match_arg_when_left_is_n_obj(given_arg),
            Obj::QObj(_) => Self::match_arg_when_left_is_q_obj(given_arg),
            Obj::ZObj(_) => Self::match_arg_when_left_is_z_obj(given_arg),
            Obj::RObj(_) => Self::match_arg_when_left_is_r_obj(given_arg),
            Obj::InstSetStructObj(_) => Self::match_arg_when_left_is_inst_set_struct_obj(given_arg),
            Obj::Cart(_) => Self::match_arg_when_left_is_cart(given_arg),
            Obj::CartDim(_) => Self::match_arg_when_left_is_cart_dim(given_arg),
            Obj::Proj(_) => Self::match_arg_when_left_is_proj(given_arg),
            Obj::Dim(_) => Self::match_arg_when_left_is_dim(given_arg),
            Obj::Tuple(_) => Self::match_arg_when_left_is_tuple(given_arg),
            Obj::Count(_) => Self::match_arg_when_left_is_count(given_arg),
            Obj::Range(_) => Self::match_arg_when_left_is_range(given_arg),
            Obj::ClosedRange(_) => Self::match_arg_when_left_is_closed_range(given_arg),
            Obj::Val(_) => Self::match_arg_when_left_is_val(given_arg),
            Obj::PowerSet(_) => Self::match_arg_when_left_is_power_set(given_arg),
            Obj::Choose(_) => Self::match_arg_when_left_is_choose(given_arg),
            Obj::ObjAtIndex(_) => Self::match_arg_when_left_is_obj_at_index(given_arg),
            Obj::QPos(_) => Self::match_arg_when_left_is_q_pos(given_arg),
            Obj::ZPos(_) => Self::match_arg_when_left_is_z_pos(given_arg),
            Obj::RPos(_) => Self::match_arg_when_left_is_r_pos(given_arg),
            Obj::QNeg(_) => Self::match_arg_when_left_is_q_neg(given_arg),
            Obj::ZNeg(_) => Self::match_arg_when_left_is_z_neg(given_arg),
            Obj::RNeg(_) => Self::match_arg_when_left_is_r_neg(given_arg),
            Obj::QNz(_) => Self::match_arg_when_left_is_q_nz(given_arg),
            Obj::ZNz(_) => Self::match_arg_when_left_is_z_nz(given_arg),
            Obj::RNz(_) => Self::match_arg_when_left_is_r_nz(given_arg),
        }
    }

    fn match_arg_when_left_is_identifier(id_known: &Identifier, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        let mut map = HashMap::new();
        map.insert(id_known.name.clone(), vec![given_arg.clone()]);
        Ok(Some(map))
    }

    fn match_arg_when_left_is_identifier_with_mod(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::IdentifierWithMod(_) => Self::match_arg_type_not_implemented("IdentifierWithMod"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_field_access(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::FieldAccess(_) => Self::match_arg_type_not_implemented("FieldAccess"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_field_access_with_mod(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::FieldAccessWithMod(_) => Self::match_arg_type_not_implemented("FieldAccessWithMod"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_fn_obj(left: &FnObj, right: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match right {
            Obj::FnObj(ref right_fn) => {
                // body lengths must match
                if left.body.len() != right_fn.body.len() {
                    return Ok(None);
                }
                
                // heads must match
                let head_match = Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    &Obj::from(left.head.as_ref().clone()),
                    &Obj::from(right_fn.head.as_ref().clone()),
                )?;
                let mut head_map = match head_match {
                    Some(m) => m,
                    None => return Ok(None),
                };

                for (left_row, right_row) in left.body.iter().zip(right_fn.body.iter()) {
                    if left_row.len() != right_row.len() {
                        return Ok(None);
                    }
                    for (left_arg, right_arg) in left_row.iter().zip(right_row.iter()) {
                        let sub = Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                            left_arg.as_ref(),
                            right_arg.as_ref(),
                        )?;
                        let sub_map = match sub {
                            Some(m) => m,
                            None => return Ok(None),
                        };
                        for (k, v) in sub_map {
                            head_map.entry(k).or_default().extend(v);
                        }
                    }
                }

                Ok(Some(head_map))
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_number(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        let mut map = HashMap::new();
        map.insert(given_arg.to_string(), vec![given_arg.clone()]);
        Ok(Some(map))
    }

    fn match_arg_when_left_is_add(left_left: &Obj, left_right: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Add(ref g) => Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_sub(left_left: &Obj, left_right: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Sub(ref g) => Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_mul(left_left: &Obj, left_right: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Mul(ref g) => Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_div(left_left: &Obj, left_right: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Div(ref g) => Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_mod(left_left: &Obj, left_right: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Mod(ref g) => Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_pow(left_left: &Obj, left_right: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Pow(ref g) => Self::match_arg_binary_then_merge(left_left, left_right, &g.base, &g.exponent),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_union(left_left: &Obj, left_right: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Union(ref g) => Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_intersect(left_left: &Obj, left_right: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Intersect(ref g) => Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_set_minus(left_left: &Obj, left_right: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::SetMinus(ref g) => Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_set_diff(left_left: &Obj, left_right: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::SetDiff(ref g) => Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cup(left_left: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Cup(ref g) => Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, &g.left),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cap(left_left: &Obj, given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Cap(ref g) => Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, &g.left),
            _ => Ok(None),
        }
    }

    /// Match two pairs (left_left, given_left) and (left_right, given_right); if either returns None, return None; else merge maps and return Some(merged).
    fn match_arg_binary_then_merge(
        left_left: &Obj,
        left_right: &Obj,
        given_left: &Obj,
        given_right: &Obj,
    ) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        let left_res = Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, given_left)?;
        let map1 = match left_res {
            Some(m) => m,
            None => return Ok(None),
        };
        let right_res = Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_right, given_right)?;
        let map2 = match right_res {
            Some(m) => m,
            None => return Ok(None),
        };
        let merged = Self::merge_arg_match_maps(map1, map2);
        Ok(Some(merged))
    }

    fn merge_arg_match_maps(
        mut map1: HashMap<String, Vec<Obj>>,
        map2: HashMap<String, Vec<Obj>>,
    ) -> HashMap<String, Vec<Obj>> {
        for (k, v) in map2 {
            map1.entry(k).or_default().extend(v);
        }
        map1
    }

    fn match_arg_when_left_is_list_set(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::ListSet(_) => Self::match_arg_type_not_implemented("ListSet"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_set_builder(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::SetBuilder(_) => Self::match_arg_type_not_implemented("SetBuilder"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_fn_set_without_dom(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::FnSetWithoutDom(_) => Self::match_arg_type_not_implemented("FnSetWithoutDom"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_fn_set_with_dom(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::FnSetWithDom(_) => Self::match_arg_type_not_implemented("FnSetWithDom"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_n_pos_obj(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::NPosObj(_) => Self::match_arg_type_not_implemented("NPosObj"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_n_obj(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::NObj(_) => Self::match_arg_type_not_implemented("NObj"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_obj(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::QObj(_) => Self::match_arg_type_not_implemented("QObj"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_obj(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::ZObj(_) => Self::match_arg_type_not_implemented("ZObj"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_obj(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::RObj(_) => Self::match_arg_type_not_implemented("RObj"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_inst_set_struct_obj(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::InstSetStructObj(_) => Self::match_arg_type_not_implemented("InstSetStructObj"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cart(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Cart(_) => Self::match_arg_type_not_implemented("Cart"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cart_dim(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::CartDim(_) => Self::match_arg_type_not_implemented("CartDim"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_proj(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Proj(_) => Self::match_arg_type_not_implemented("Proj"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_dim(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Dim(_) => Self::match_arg_type_not_implemented("Dim"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_tuple(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Tuple(_) => Self::match_arg_type_not_implemented("Tuple"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_count(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Count(_) => Self::match_arg_type_not_implemented("Count"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_range(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Range(_) => Self::match_arg_type_not_implemented("Range"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_closed_range(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::ClosedRange(_) => Self::match_arg_type_not_implemented("ClosedRange"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_val(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Val(_) => Self::match_arg_type_not_implemented("Val"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_power_set(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::PowerSet(_) => Self::match_arg_type_not_implemented("PowerSet"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_choose(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::Choose(_) => Self::match_arg_type_not_implemented("Choose"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_obj_at_index(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::ObjAtIndex(_) => Self::match_arg_type_not_implemented("ObjAtIndex"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_pos(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::QPos(_) => Self::match_arg_type_not_implemented("QPos"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_pos(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::ZPos(_) => Self::match_arg_type_not_implemented("ZPos"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_pos(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::RPos(_) => Self::match_arg_type_not_implemented("RPos"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_neg(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::QNeg(_) => Self::match_arg_type_not_implemented("QNeg"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_neg(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::ZNeg(_) => Self::match_arg_type_not_implemented("ZNeg"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_neg(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::RNeg(_) => Self::match_arg_type_not_implemented("RNeg"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_nz(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::QNz(_) => Self::match_arg_type_not_implemented("QNz"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_nz(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::ZNz(_) => Self::match_arg_type_not_implemented("ZNz"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_nz(given_arg: &Obj) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        match given_arg {
            Obj::RNz(_) => Self::match_arg_type_not_implemented("RNz"),
            _ => Ok(None),
        }
    }

    fn match_arg_type_not_implemented(obj_type_name: &str) -> Result<Option<HashMap<String, Vec<Obj>>>, VerifyError> {
        Err(VerifyError::new(
            format!("match_arg for {} not implemented", obj_type_name),
            vec![],
            None,
        ))
    }
}

impl<'a> Executor<'a> {
    // 证明 把 args 代入到 forall 的 param 里，得到的 facts_for_args_satisfy_param_def_with_type_vec 是正确的，而且dom里面的东西也是正确的

}