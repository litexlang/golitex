use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

impl Runtime {
    pub fn verify_atomic_fact_with_known_forall(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(fact_verified) =
            self.try_verify_with_known_forall_facts_in_envs(atomic_fact, verify_state)?
        {
            return Ok(NonErrStmtExecResult::FactVerifiedByFact(fact_verified));
        }
        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn get_matched_atomic_fact_in_known_forall_fact_in_envs(
        &self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_fact: &AtomicFact,
    ) -> Result<
        (
            (usize, usize),
            Option<HashMap<String, Obj>>,
            Option<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>,
        ),
        VerifyError,
    > {
        let key = given_fact.key();
        let is_true = given_fact.is_true();

        let envs_count = self.environment_stack.len();
        for i in iterate_from_env_index..envs_count {
            let env = &self.environment_stack[envs_count - 1 - i];
            if let Some(known_forall_facts_in_env) = env
                .known_atomic_facts_in_forall_facts
                .get(&(key.clone(), is_true))
            {
                let known_forall_facts_count = known_forall_facts_in_env.len();
                for j in iterate_from_known_forall_fact_index..known_forall_facts_count {
                    let current_known_forall =
                        &known_forall_facts_in_env[known_forall_facts_count - 1 - j];
                    let atomic_fact_args_in_known_forall = current_known_forall.0.args();
                    let given_atomic_fact_args = given_fact.args();
                    let match_result =
                        Self::match_args_in_fact_in_known_forall_fact_with_given_args(
                            &atomic_fact_args_in_known_forall,
                            &given_atomic_fact_args,
                        )?;
                    if let Some(arg_map) = match_result {
                        return Ok(((i, j), Some(arg_map), Some(current_known_forall.clone())));
                    }
                }
            }
        }

        Ok((DEFAULT_LINE_FILE, None, None))
    }

    fn try_verify_with_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactVerifiedByFact>, VerifyError> {
        let mut iterate_from_env_index = 0;
        let mut iterate_from_known_forall_fact_index = 0;

        loop {
            let result = self.get_matched_atomic_fact_in_known_forall_fact_in_envs(
                iterate_from_env_index,
                iterate_from_known_forall_fact_index,
                atomic_fact,
            )?;
            let ((i, j), arg_map_opt, known_forall_opt) = result;
            match (arg_map_opt, known_forall_opt) {
                (Some(arg_map), Some((atomic_fact_in_known_forall_fact, forall_rc))) => {
                    if let Some(fact_verified) = self.verify_args_satisfy_forall_requirements(
                        &atomic_fact_in_known_forall_fact,
                        &forall_rc,
                        arg_map,
                        atomic_fact,
                        verify_state,
                    )? {
                        return Ok(Some(fact_verified));
                    }
                    iterate_from_env_index = i;
                    iterate_from_known_forall_fact_index = j + 1;
                }
                _ => return Ok(None),
            }
        }
    }

    fn verify_args_satisfy_forall_requirements(
        &mut self,
        atomic_fact_in_known_forall_fact: &AtomicFact,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        arg_map: HashMap<String, Obj>,
        given_atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactVerifiedByFact>, VerifyError> {
        let param_names = ParamDefWithParamType::collect_param_names(&known_forall.params_def);

        if !param_names
            .iter()
            .all(|param_name| arg_map.contains_key(param_name))
        {
            return Ok(None);
        }

        // Collect the arg for each param.
        let mut args_for_params: Vec<Obj> = Vec::new();

        for param_name in param_names.iter() {
            let obj = match arg_map.get(param_name) {
                Some(v) => v,
                None => return Ok(None),
            };

            args_for_params.push(obj.clone());
        }

        // the same atom in atomic fact in known forall fact which is not a parameter matches the same atom in given atomic fact
        for (key, obj) in arg_map.iter() {
            if param_names.contains(key) {
                continue;
            } else {
                if key != &obj.to_string() {
                    return Ok(None);
                }
            }
        }

        let args_satisfy_param_types =
            ParamDefWithParamType::facts_for_args_satisfy_param_def_with_type_vec(
                &known_forall.params_def,
                &args_for_params,
            )
            .map_err(|e| VerifyError::new(Fact::AtomicFact(given_atomic_fact.clone()), Some(e)))?;

        for fact in args_satisfy_param_types.iter() {
            let result = self.verify_atomic_fact(fact, verify_state)?;
            if result.is_unknown() {
                return Ok(None);
            }
        }

        let param_to_arg_map = match ParamDefWithParamType::param_def_params_to_arg_map(
            &known_forall.params_def,
            &arg_map,
        ) {
            Some(m) => m,
            None => return Ok(None),
        };

        for dom_fact in known_forall.dom.iter() {
            let instantiated_dom_fact = dom_fact.instantiate(&param_to_arg_map);
            let result =
                self.verify_exist_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)?;
            if result.is_unknown() {
                return Ok(None);
            }
        }

        let verified_by_known_forall_fact = ForallFact::new(
            known_forall.params_def.clone(),
            known_forall.dom.clone(),
            vec![ExistOrAndChainAtomicFact::AtomicFact(
                atomic_fact_in_known_forall_fact.clone(),
            )],
            known_forall.line_file.clone(),
        );
        let fact_verified = FactVerifiedByFact::new(
            Fact::AtomicFact(given_atomic_fact.clone()),
            verified_by_known_forall_fact.to_string(),
            InferResult::new(),
            verified_by_known_forall_fact.line_file,
        );
        Ok(Some(fact_verified))
    }

    pub fn match_args_in_fact_in_known_forall_fact_with_given_args(
        fact_args_in_known_forall: &Vec<Obj>,
        given_fact_args: &Vec<Obj>,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        if fact_args_in_known_forall.len() != given_fact_args.len() {
            return Ok(None);
        }

        let mut atom_in_known_atomic_fact_to_matched_objs_in_given_fact_map: HashMap<String, Obj> =
            HashMap::new();

        for (arg_in_atomic_fact_in_known_forall, arg_in_given) in
            fact_args_in_known_forall.iter().zip(given_fact_args.iter())
        {
            let sub_map_option = Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                arg_in_atomic_fact_in_known_forall,
                arg_in_given,
            )?;
            let sub_map = match sub_map_option {
                Some(m) => m,
                None => return Ok(None),
            };
            for (k, v) in sub_map {
                if let Some(existing_obj) =
                    atom_in_known_atomic_fact_to_matched_objs_in_given_fact_map.get(&k)
                {
                    if existing_obj.to_string() != v.to_string() {
                        return Ok(None);
                    }
                }

                atom_in_known_atomic_fact_to_matched_objs_in_given_fact_map.insert(k, v);
            }
        }

        Ok(Some(
            atom_in_known_atomic_fact_to_matched_objs_in_given_fact_map,
        ))
    }

    fn match_arg_in_atomic_fact_in_known_forall_with_given_arg(
        arg_in_atomic_fact_in_known_forall: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match arg_in_atomic_fact_in_known_forall {
            Obj::Identifier(ref id_known) => {
                Self::match_arg_when_left_is_identifier(id_known, given_arg)
            }
            Obj::IdentifierWithMod(_) => {
                Self::match_arg_when_left_is_identifier_with_mod(given_arg)
            }
            Obj::FieldAccess(_) => Self::match_arg_when_left_is_field_access(given_arg),
            Obj::FieldAccessWithMod(_) => {
                Self::match_arg_when_left_is_field_access_with_mod(given_arg)
            }
            Obj::FnObj(ref f) => Self::match_arg_when_left_is_fn_obj(f, given_arg),
            Obj::Number(ref left) => Self::match_arg_when_left_is_number(left, given_arg),
            Obj::Add(ref a) => Self::match_arg_when_left_is_add(&a.left, &a.right, given_arg),
            Obj::Sub(ref a) => Self::match_arg_when_left_is_sub(&a.left, &a.right, given_arg),
            Obj::Mul(ref a) => Self::match_arg_when_left_is_mul(&a.left, &a.right, given_arg),
            Obj::Div(ref a) => Self::match_arg_when_left_is_div(&a.left, &a.right, given_arg),
            Obj::Mod(ref a) => Self::match_arg_when_left_is_mod(&a.left, &a.right, given_arg),
            Obj::Pow(ref a) => Self::match_arg_when_left_is_pow(&a.base, &a.exponent, given_arg),
            Obj::Union(ref a) => Self::match_arg_when_left_is_union(&a.left, &a.right, given_arg),
            Obj::Intersect(ref a) => {
                Self::match_arg_when_left_is_intersect(&a.left, &a.right, given_arg)
            }
            Obj::SetMinus(ref a) => {
                Self::match_arg_when_left_is_set_minus(&a.left, &a.right, given_arg)
            }
            Obj::SetDiff(ref a) => {
                Self::match_arg_when_left_is_set_diff(&a.left, &a.right, given_arg)
            }
            Obj::Cup(ref a) => Self::match_arg_when_left_is_cup(&a.left, given_arg),
            Obj::Cap(ref a) => Self::match_arg_when_left_is_cap(&a.left, given_arg),
            Obj::ListSet(ref left) => Self::match_arg_when_left_is_list_set(&left.list, given_arg),
            Obj::SetBuilder(_) => Self::match_arg_when_left_is_set_builder(given_arg),
            Obj::FnSetWithoutParams(ref left) => Self::match_arg_when_left_is_fn_set_without_dom(
                &left.param_sets,
                left.ret_set.as_ref(),
                given_arg,
            ),
            Obj::FnSetWithParams(_) => Self::match_arg_when_left_is_fn_set_with_dom(given_arg),
            Obj::NPosObj(_) => Self::match_arg_when_left_is_n_pos_obj(given_arg),
            Obj::NObj(_) => Self::match_arg_when_left_is_n_obj(given_arg),
            Obj::QObj(_) => Self::match_arg_when_left_is_q_obj(given_arg),
            Obj::ZObj(_) => Self::match_arg_when_left_is_z_obj(given_arg),
            Obj::RObj(_) => Self::match_arg_when_left_is_r_obj(given_arg),
            Obj::InstSetStructObj(ref left) => Self::match_arg_when_left_is_inst_set_struct_obj(
                &left.struct_name,
                &left.args,
                given_arg,
            ),
            Obj::Cart(ref left) => Self::match_arg_when_left_is_cart(&left.args, given_arg),
            Obj::CartDim(ref left) => {
                Self::match_arg_when_left_is_cart_dim(left.set.as_ref(), given_arg)
            }
            Obj::Proj(ref left) => {
                Self::match_arg_when_left_is_proj(left.set.as_ref(), left.dim.as_ref(), given_arg)
            }
            Obj::TupleDim(ref left) => {
                Self::match_arg_when_left_is_dim(left.arg.as_ref(), given_arg)
            }
            Obj::Tuple(ref left) => Self::match_arg_when_left_is_tuple(&left.args, given_arg),
            Obj::Count(ref left) => {
                Self::match_arg_when_left_is_count(left.set.as_ref(), given_arg)
            }
            Obj::Range(ref left) => Self::match_arg_when_left_is_range(
                left.start.as_ref(),
                left.end.as_ref(),
                given_arg,
            ),
            Obj::ClosedRange(ref left) => Self::match_arg_when_left_is_closed_range(
                left.start.as_ref(),
                left.end.as_ref(),
                given_arg,
            ),
            Obj::Val(ref left) => Self::match_arg_when_left_is_val(left.value.as_ref(), given_arg),
            Obj::PowerSet(ref left) => {
                Self::match_arg_when_left_is_power_set(left.set.as_ref(), given_arg)
            }
            Obj::Choose(ref left) => {
                Self::match_arg_when_left_is_choose(left.set.as_ref(), given_arg)
            }
            Obj::ObjAtIndex(ref left) => Self::match_arg_when_left_is_obj_at_index(
                left.obj.as_ref(),
                left.index.as_ref(),
                given_arg,
            ),
            Obj::QPos(_) => Self::match_arg_when_left_is_q_pos(given_arg),
            Obj::RPos(_) => Self::match_arg_when_left_is_r_pos(given_arg),
            Obj::QNeg(_) => Self::match_arg_when_left_is_q_neg(given_arg),
            Obj::ZNeg(_) => Self::match_arg_when_left_is_z_neg(given_arg),
            Obj::RNeg(_) => Self::match_arg_when_left_is_r_neg(given_arg),
            Obj::QNz(_) => Self::match_arg_when_left_is_q_nz(given_arg),
            Obj::ZNz(_) => Self::match_arg_when_left_is_z_nz(given_arg),
            Obj::RNz(_) => Self::match_arg_when_left_is_r_nz(given_arg),
        }
    }

    fn match_arg_when_left_is_identifier(
        id_known: &Identifier,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        let mut map = HashMap::new();
        map.insert(id_known.name.clone(), given_arg.clone());
        Ok(Some(map))
    }

    fn match_arg_when_left_is_identifier_with_mod(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::IdentifierWithMod(_) => Self::match_arg_type_not_implemented("IdentifierWithMod"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_field_access(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::FieldAccess(_) => Self::match_arg_type_not_implemented("FieldAccess"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_field_access_with_mod(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::FieldAccessWithMod(_) => {
                Self::match_arg_type_not_implemented("FieldAccessWithMod")
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_fn_obj(
        left: &FnObj,
        right: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
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
                            if let Some(existing_obj) = head_map.get(&k) {
                                if existing_obj.to_string() != v.to_string() {
                                    return Ok(None);
                                }
                            }
                            head_map.insert(k, v);
                        }
                    }
                }

                Ok(Some(head_map))
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_number(
        left: &Number,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        if !given_arg
            .calculate_arithmetic_value_and_normalize()
            .is_some()
        {
            return Ok(None);
        }
        let left_obj = Obj::Number(left.clone());
        if left_obj.two_objs_can_be_calculated_and_equal_by_calculation(given_arg) {
            Ok(Some(HashMap::new()))
        } else {
            Ok(None)
        }
    }

    fn match_arg_when_left_is_add(
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Add(ref g) => {
                Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_sub(
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Sub(ref g) => {
                Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_mul(
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Mul(ref g) => {
                Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_div(
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Div(ref g) => {
                Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_mod(
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Mod(ref g) => {
                Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_pow(
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Pow(ref g) => {
                Self::match_arg_binary_then_merge(left_left, left_right, &g.base, &g.exponent)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_union(
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Union(ref g) => {
                Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_intersect(
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Intersect(ref g) => {
                Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_set_minus(
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::SetMinus(ref g) => {
                Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_set_diff(
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::SetDiff(ref g) => {
                Self::match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cup(
        left_left: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Cup(ref g) => {
                Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, &g.left)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cap(
        left_left: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Cap(ref g) => {
                Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, &g.left)
            }
            _ => Ok(None),
        }
    }

    /// Match two pairs (left_left, given_left) and (left_right, given_right); if either returns None, return None; else merge maps and return Some(merged).
    fn match_arg_binary_then_merge(
        left_left: &Obj,
        left_right: &Obj,
        given_left: &Obj,
        given_right: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        let left_res =
            Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, given_left)?;
        let map1 = match left_res {
            Some(m) => m,
            None => return Ok(None),
        };
        let right_res =
            Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_right, given_right)?;
        let map2 = match right_res {
            Some(m) => m,
            None => return Ok(None),
        };
        let merged = Self::merge_arg_match_maps(map1, map2);
        Ok(merged)
    }

    fn merge_arg_match_maps(
        map1: HashMap<String, Obj>,
        map2: HashMap<String, Obj>,
    ) -> Option<HashMap<String, Obj>> {
        let mut merged = HashMap::new();
        for (k, v) in map2 {
            if let Some(existing_obj) = map1.get(&k) {
                if existing_obj.to_string() != v.to_string() {
                    return None;
                }
            }
            merged.insert(k, v);
        }
        Some(merged)
    }

    fn match_arg_vec_then_merge(
        left_elements: &[Box<Obj>],
        given_elements: &[Box<Obj>],
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        if left_elements.len() != given_elements.len() {
            return Ok(None);
        }
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (left_elem, given_elem) in left_elements.iter().zip(given_elements.iter()) {
            let sub_map = match Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                left_elem.as_ref(),
                given_elem.as_ref(),
            )? {
                Some(m) => m,
                None => return Ok(None),
            };
            for (k, v) in sub_map {
                if let Some(existing_obj) = merged.get(&k) {
                    if existing_obj.to_string() != v.to_string() {
                        return Ok(None);
                    }
                }
                merged.insert(k, v);
            }
        }
        Ok(Some(merged))
    }

    fn match_arg_when_left_is_list_set(
        left_list: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::ListSet(ref given) => Self::match_arg_vec_then_merge(left_list, &given.list),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_set_builder(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::SetBuilder(_) => Self::match_arg_type_not_implemented("SetBuilder"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_fn_set_without_dom(
        left_param_sets: &[Box<Obj>],
        left_ret_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::FnSetWithoutParams(ref given) => {
                let param_maps =
                    Self::match_arg_vec_then_merge(left_param_sets, &given.param_sets)?;
                let param_map = match param_maps {
                    Some(m) => m,
                    None => return Ok(None),
                };
                let ret_map = Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_ret_set,
                    given.ret_set.as_ref(),
                )?;
                let ret_map = match ret_map {
                    Some(m) => m,
                    None => return Ok(None),
                };
                let merged = Self::merge_arg_match_maps(param_map, ret_map);
                Ok(merged)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_fn_set_with_dom(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::FnSetWithParams(_) => Self::match_arg_type_not_implemented("FnSetWithDom"),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_n_pos_obj(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::NPosObj(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_n_obj(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::NObj(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_obj(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::QObj(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_obj(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::ZObj(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_obj(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::RObj(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_inst_set_struct_obj(
        left_struct_name: &IdentifierOrIdentifierWithMod,
        left_args: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::InstSetStructObj(ref given) => {
                if !left_struct_name.literally_the_same_as(&given.struct_name) {
                    return Ok(None);
                }
                Self::match_arg_vec_then_merge(left_args, &given.args)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cart(
        left_args: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Cart(ref given) => Self::match_arg_vec_then_merge(left_args, &given.args),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cart_dim(
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::CartDim(ref given) => {
                Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                )
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_proj(
        left_set: &Obj,
        left_dim: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Proj(ref given) => Self::match_arg_binary_then_merge(
                left_set,
                left_dim,
                given.set.as_ref(),
                given.dim.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_dim(
        left_dim: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::TupleDim(ref given) => {
                Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_dim,
                    given.arg.as_ref(),
                )
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_tuple(
        left_elements: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Tuple(ref given) => Self::match_arg_vec_then_merge(left_elements, &given.args),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_count(
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Count(ref given) => Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                left_set,
                given.set.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_range(
        left_start: &Obj,
        left_end: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Range(ref given) => Self::match_arg_binary_then_merge(
                left_start,
                left_end,
                given.start.as_ref(),
                given.end.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_closed_range(
        left_start: &Obj,
        left_end: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::ClosedRange(ref given) => Self::match_arg_binary_then_merge(
                left_start,
                left_end,
                given.start.as_ref(),
                given.end.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_val(
        left_value: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Val(ref given) => Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                left_value,
                given.value.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_power_set(
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::PowerSet(ref given) => {
                Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                )
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_choose(
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::Choose(ref given) => {
                Self::match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                )
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_obj_at_index(
        left_obj: &Obj,
        left_index: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::ObjAtIndex(ref given) => Self::match_arg_binary_then_merge(
                left_obj,
                left_index,
                given.obj.as_ref(),
                given.index.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_pos(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::QPos(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_pos(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::RPos(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_neg(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::QNeg(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_neg(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::ZNeg(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_neg(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::RNeg(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_nz(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::QNz(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_nz(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::ZNz(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_nz(
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        match given_arg {
            Obj::RNz(_) => Self::match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_same_type(given_arg: &Obj) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        let mut map = HashMap::new();
        map.insert(given_arg.to_string(), given_arg.clone());
        Ok(Some(map))
    }

    fn match_arg_type_not_implemented(
        obj_type_name: &str,
    ) -> Result<Option<HashMap<String, Obj>>, VerifyError> {
        let _ = obj_type_name;
        Ok(None)
    }
}
