use crate::prelude::*;
use std::collections::HashMap;

fn remove_param_names_from_param_to_arg_map(
    param_to_arg_map: &HashMap<String, Obj>,
    param_names: &Vec<String>,
) -> HashMap<String, Obj> {
    let mut filtered_param_to_arg_map = HashMap::new();
    for (param_name, arg) in param_to_arg_map.iter() {
        if !param_names.contains(param_name) {
            filtered_param_to_arg_map.insert(param_name.clone(), arg.clone());
        }
    }
    filtered_param_to_arg_map
}


impl Runtime {
    pub fn inst_obj(
        &self,
        obj: &Obj,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        match obj {
            Obj::Identifier(inner) => self.inst_identifier(inner, param_to_arg_map),
            Obj::IdentifierWithMod(inner) => self.inst_identifier_with_mod(inner, param_to_arg_map),
            Obj::FieldAccess(inner) => self.inst_field_access(inner, param_to_arg_map),
            Obj::FieldAccessWithMod(inner) => {
                self.inst_field_access_with_mod(inner, param_to_arg_map)
            }
            Obj::FnObj(inner) => self.inst_fn_obj(inner, param_to_arg_map, ctx),
            Obj::Number(inner) => self.inst_number(inner, param_to_arg_map, ctx),
            Obj::Add(inner) => self.inst_add(inner, param_to_arg_map, ctx),
            Obj::Sub(inner) => self.inst_sub(inner, param_to_arg_map, ctx),
            Obj::Mul(inner) => self.inst_mul(inner, param_to_arg_map, ctx),
            Obj::Div(inner) => self.inst_div(inner, param_to_arg_map, ctx),
            Obj::Mod(inner) => self.inst_mod(inner, param_to_arg_map, ctx),
            Obj::Pow(inner) => self.inst_pow(inner, param_to_arg_map, ctx),
            Obj::MatrixAdd(inner) => self.inst_matrix_add(inner, param_to_arg_map, ctx),
            Obj::MatrixSub(inner) => self.inst_matrix_sub(inner, param_to_arg_map, ctx),
            Obj::MatrixMul(inner) => self.inst_matrix_mul(inner, param_to_arg_map, ctx),
            Obj::MatrixScalarMul(inner) => self.inst_matrix_scalar_mul(inner, param_to_arg_map, ctx),
            Obj::MatrixPow(inner) => self.inst_matrix_pow(inner, param_to_arg_map, ctx),
            Obj::Abs(inner) => self.inst_abs(inner, param_to_arg_map, ctx),
            Obj::Log(inner) => self.inst_log(inner, param_to_arg_map, ctx),
            Obj::Max(inner) => self.inst_max(inner, param_to_arg_map, ctx),
            Obj::Min(inner) => self.inst_min(inner, param_to_arg_map, ctx),
            Obj::Union(inner) => self.inst_union(inner, param_to_arg_map, ctx),
            Obj::Intersect(inner) => self.inst_intersect(inner, param_to_arg_map, ctx),
            Obj::SetMinus(inner) => self.inst_set_minus(inner, param_to_arg_map, ctx),
            Obj::SetDiff(inner) => self.inst_set_diff(inner, param_to_arg_map, ctx),
            Obj::Cup(inner) => self.inst_cup(inner, param_to_arg_map, ctx),
            Obj::Cap(inner) => self.inst_cap(inner, param_to_arg_map, ctx),
            Obj::ListSet(inner) => self.inst_list_set(inner, param_to_arg_map, ctx),
            Obj::SetBuilder(inner) => self.inst_set_builder(inner, param_to_arg_map, ctx),
            Obj::FnSet(inner) => self.inst_fn_set_with_params(inner, param_to_arg_map, ctx),
            Obj::StandardSet(standard_set) => self.inst_standard_set(standard_set),
            Obj::Cart(inner) => self.inst_cart(inner, param_to_arg_map, ctx),
            Obj::CartDim(inner) => self.inst_cart_dim(inner, param_to_arg_map, ctx),
            Obj::Proj(inner) => self.inst_proj(inner, param_to_arg_map, ctx),
            Obj::TupleDim(inner) => self.inst_tuple_dim(inner, param_to_arg_map, ctx),
            Obj::Tuple(inner) => self.inst_tuple(inner, param_to_arg_map, ctx),
            Obj::Count(inner) => self.inst_count(inner, param_to_arg_map, ctx),
            Obj::Range(inner) => self.inst_range(inner, param_to_arg_map, ctx),
            Obj::ClosedRange(inner) => self.inst_closed_range(inner, param_to_arg_map, ctx),
            Obj::FiniteSeqSet(inner) => self.inst_finite_seq_set(inner, param_to_arg_map, ctx),
            Obj::SeqSet(inner) => self.inst_seq_set(inner, param_to_arg_map, ctx),
            Obj::FiniteSeqListObj(inner) => self.inst_finite_seq_list_obj(inner, param_to_arg_map, ctx),
            Obj::MatrixSet(inner) => self.inst_matrix_set(inner, param_to_arg_map, ctx),
            Obj::MatrixListObj(inner) => self.inst_matrix_list_obj(inner, param_to_arg_map, ctx),
            Obj::PowerSet(inner) => self.inst_power_set(inner, param_to_arg_map, ctx),
            Obj::Choose(inner) => self.inst_choose(inner, param_to_arg_map, ctx),
            Obj::ObjAtIndex(inner) => self.inst_obj_at_index(inner, param_to_arg_map, ctx),
            Obj::FamilyObj(family) => {
                let mut params = Vec::with_capacity(family.params.len());
                for p in family.params.iter() {
                    params.push(self.inst_obj(p, param_to_arg_map, ctx)?);
                }
                Ok(FamilyObj {
                    name: family.name.clone(),
                    params,
                }
                .into())
            }
            Obj::StructObj(s) => {
                let mut args = Vec::with_capacity(s.args.len());
                for a in s.args.iter() {
                    args.push(self.inst_obj(a, param_to_arg_map, ctx)?);
                }
                Ok(StructObj::new(s.name.clone(), args).into())
            }
            Obj::ForallFreeParamObj(p) => {
                if ctx == ParamObjType::Forall {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::ForallFieldAccessObj(p) => {
                if ctx != ParamObjType::Forall {
                    return Ok(ForallFieldAccessObj::new(p.name.clone(), p.field.clone()).into());
                }
                let fa = FieldAccess::new(p.name.clone(), p.field.clone());
                let dotted = field_access_to_string(&fa.name, &fa.field);
                if let Some(obj) = param_to_arg_map.get(&dotted) {
                    return Ok(obj.clone());
                }
                match self.inst_field_access(&fa, param_to_arg_map)? {
                    Obj::FieldAccess(f) if f.name == p.name && f.field == p.field => {
                        Ok(ForallFieldAccessObj::new(p.name.clone(), p.field.clone()).into())
                    }
                    other => Ok(other),
                }
            }
            Obj::DefFreeParamObj(p) => {
                if ctx == ParamObjType::DefProp {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::ExistFreeParamObj(p) => {
                if ctx == ParamObjType::Exist {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::SetBuilderFreeParamObj(p) => {
                if ctx == ParamObjType::SetBuilder {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::FnSetFreeParamObj(p) => {
                if ctx == ParamObjType::FnSet {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::ByInducFreeParamObj(p) => {
                if ctx == ParamObjType::Induc {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::DefAlgoFreeParamObj(p) => {
                if ctx == ParamObjType::DefAlgo {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::StructSelfFieldFreeParamObj(p) => {
                if ctx != ParamObjType::StructSelf {
                    return Ok(p.clone().into());
                }
                let fa = FieldAccess::new(SELF.to_string(), p.field.clone());
                self.inst_field_access(&fa, param_to_arg_map)
            }
        }
    }

    pub fn inst_identifier(
        &self,
        identifier: &Identifier,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        Ok(match param_to_arg_map.get(&identifier.name) {
            Some(obj) => obj.clone(),
            None => identifier.clone().into(),
        })
    }

    pub fn inst_identifier_with_mod(
        &self,
        identifier_with_mod: &IdentifierWithMod,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        _ = param_to_arg_map;
        Ok(identifier_with_mod.clone().into())
    }

    pub fn inst_field_access(
        &self,
        field_access: &FieldAccess,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        let dotted = field_access_to_string(&field_access.name, &field_access.field);
        if let Some(obj) = param_to_arg_map.get(&dotted) {
            return Ok(obj.clone());
        }
        match param_to_arg_map.get(&field_access.name) {
            Some(Obj::Identifier(identifier)) => {
                Ok(FieldAccess::new(identifier.name.clone(), field_access.field.clone()).into())
            }
            Some(Obj::IdentifierWithMod(identifier_with_mod)) => Ok(FieldAccessWithMod::new(
                identifier_with_mod.mod_name.clone(),
                identifier_with_mod.name.clone(),
                field_access.field.clone(),
            )
            .into()),
            Some(obj) => {
                let tuple_opt = match obj {
                    Obj::Tuple(t) => Some(t.clone()),
                    _ => self.get_obj_equal_to_tuple(&obj.to_string()),
                };
                match tuple_opt {
                    Some(t) => self.inst_field_access_on_struct_tuple(field_access, &t),
                    None => {
                        return Err(InstantiateRuntimeError(RuntimeErrorStruct::new(
                            None,
                            format!(
                                "field `{}` of struct `{}` is not a tuple",
                                field_access.field, field_access.name
                            ),
                            default_line_file(),
                            None,
                            vec![],
                        ))
                        .into())
                    }
                }
            }
            None => Ok(field_access.clone().into()),
        }
    }

    fn inst_field_access_on_struct_tuple(
        &self,
        field_access: &FieldAccess,
        tuple: &Tuple,
    ) -> Result<Obj, RuntimeError> {
        let Some(def) = self.get_definition_of_struct_where_object_satisfies(
            &IdentifierOrIdentifierWithMod::Identifier(Identifier::new(field_access.name.clone())),
        ) else {
            return Err(InstantiateRuntimeError(RuntimeErrorStruct::new(
                None,
                format!("struct `{}` is not defined", field_access.name),
                default_line_file(),
                None,
                vec![],
            ))
            .into());
        };

        let Some(field_index) = def
            .fields
            .iter()
            .position(|(fname, _)| fname == &field_access.field)
        else {
            return Err(InstantiateRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "field `{}` of struct `{}` is not defined",
                    field_access.field, field_access.name
                ),
                default_line_file(),
                None,
                vec![],
            ))
            .into());
        };

        let tuple_index = field_index + def.number_of_params();
        let Some(component) = tuple.args.get(tuple_index) else {
            return Err(
                InstantiateRuntimeError(RuntimeErrorStruct::new(
                    None,
                    format!("field `{}` of struct `{}` is at index {}, but tuple for `{}` has only {} component(s)", field_access.field, field_access.name, tuple_index, field_access.name, tuple.args.len()),
                    default_line_file(),
                    None,
                    vec![],
                ))
                .into(),
            );
        };

        Ok((**component).clone())
    }

    pub fn inst_field_access_with_mod(
        &self,
        field_access_with_mod: &FieldAccessWithMod,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        _ = param_to_arg_map;
        Ok(field_access_with_mod.clone().into())
    }

    pub fn inst_fn_obj(
        &self,
        fn_obj: &FnObj,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let mut merged_body = Vec::with_capacity(fn_obj.body.len());
        for obj_vec in fn_obj.body.iter() {
            let mut new_obj_vec = Vec::with_capacity(obj_vec.len());
            for obj in obj_vec.iter() {
                new_obj_vec.push(Box::new(self.inst_obj(obj, param_to_arg_map, ctx)?));
            }
            merged_body.push(new_obj_vec);
        }

        let inst_head = self.inst_obj(&(*fn_obj.head.clone()).into(), param_to_arg_map, ctx)?;

        let final_head: Atom = match inst_head {
            Obj::Identifier(x) => x.clone().into(),
            Obj::IdentifierWithMod(x) => x.clone().into(),
            Obj::FieldAccess(x) => x.clone().into(),
            Obj::FieldAccessWithMod(x) => x.clone().into(),
            Obj::StructSelfFieldFreeParamObj(p) => p.clone().into(),
            Obj::FnObj(x) => {
                let merged_body_original = merged_body.clone();
                merged_body = vec![];
                merged_body.extend(x.body);
                merged_body.extend(merged_body_original);
                (*x.head.clone()).into()
            }
            _ => return Err(InstantiateRuntimeError(RuntimeErrorStruct::new(
                None,
                format!("instantiate fn object: after substitution, head must be an atom or curried fn, got {}", inst_head),
                default_line_file(),
                None,
                vec![],
            ))
            .into()),
        };

        Ok(FnObj::new(final_head, merged_body).into())
    }

    pub fn inst_number(
        &self,
        number: &Number,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        _ = param_to_arg_map;
        _ = ctx;
        Ok(number.clone().into())
    }

    pub fn inst_add(
        &self,
        add: &Add,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&add.left, param_to_arg_map, ctx)?;
        let instantiated_right_obj = self.inst_obj(&add.right, param_to_arg_map, ctx)?;
        Ok(Add::new(instantiated_left_obj, instantiated_right_obj).into())
    }

    pub fn inst_matrix_add(
        &self,
        ma: &MatrixAdd,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&ma.left, param_to_arg_map, ctx)?;
        let instantiated_right_obj = self.inst_obj(&ma.right, param_to_arg_map, ctx)?;
        Ok(MatrixAdd::new(instantiated_left_obj, instantiated_right_obj).into())
    }

    pub fn inst_matrix_sub(
        &self,
        ms: &MatrixSub,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let l = self.inst_obj(&ms.left, param_to_arg_map, ctx)?;
        let r = self.inst_obj(&ms.right, param_to_arg_map, ctx)?;
        Ok(MatrixSub::new(l, r).into())
    }

    pub fn inst_matrix_mul(
        &self,
        mm: &MatrixMul,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let l = self.inst_obj(&mm.left, param_to_arg_map, ctx)?;
        let r = self.inst_obj(&mm.right, param_to_arg_map, ctx)?;
        Ok(MatrixMul::new(l, r).into())
    }

    pub fn inst_matrix_scalar_mul(
        &self,
        m: &MatrixScalarMul,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let s = self.inst_obj(&m.scalar, param_to_arg_map, ctx)?;
        let mat = self.inst_obj(&m.matrix, param_to_arg_map, ctx)?;
        Ok(MatrixScalarMul::new(s, mat).into())
    }

    pub fn inst_matrix_pow(
        &self,
        m: &MatrixPow,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let b = self.inst_obj(&m.base, param_to_arg_map, ctx)?;
        let e = self.inst_obj(&m.exponent, param_to_arg_map, ctx)?;
        Ok(MatrixPow::new(b, e).into())
    }

    pub fn inst_sub(
        &self,
        sub: &Sub,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&sub.left, param_to_arg_map, ctx)?;
        let instantiated_right_obj = self.inst_obj(&sub.right, param_to_arg_map, ctx)?;
        Ok(Sub::new(instantiated_left_obj, instantiated_right_obj).into())
    }

    pub fn inst_mul(
        &self,
        mul: &Mul,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&mul.left, param_to_arg_map, ctx)?;
        let instantiated_right_obj = self.inst_obj(&mul.right, param_to_arg_map, ctx)?;
        Ok(Mul::new(instantiated_left_obj, instantiated_right_obj).into())
    }

    pub fn inst_div(
        &self,
        div: &Div,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Div::new(
            self.inst_obj(&div.left, param_to_arg_map, ctx)?,
            self.inst_obj(&div.right, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_mod(
        &self,
        mod_obj: &Mod,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&mod_obj.left, param_to_arg_map, ctx)?;
        let instantiated_right_obj = self.inst_obj(&mod_obj.right, param_to_arg_map, ctx)?;
        Ok(Mod::new(instantiated_left_obj, instantiated_right_obj).into())
    }

    pub fn inst_pow(
        &self,
        pow: &Pow,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_base_obj = self.inst_obj(&pow.base, param_to_arg_map, ctx)?;
        let instantiated_exponent_obj = self.inst_obj(&pow.exponent, param_to_arg_map, ctx)?;
        Ok(Pow::new(instantiated_base_obj, instantiated_exponent_obj).into())
    }

    pub fn inst_abs(
        &self,
        abs: &Abs,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Abs::new(self.inst_obj(&abs.arg, param_to_arg_map, ctx)?).into())
    }

    pub fn inst_log(
        &self,
        log: &Log,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Log::new(
            self.inst_obj(&log.base, param_to_arg_map, ctx)?,
            self.inst_obj(&log.arg, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_max(
        &self,
        max: &Max,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Max::new(
            self.inst_obj(&max.left, param_to_arg_map, ctx)?,
            self.inst_obj(&max.right, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_min(
        &self,
        min: &Min,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Min::new(
            self.inst_obj(&min.left, param_to_arg_map, ctx)?,
            self.inst_obj(&min.right, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_union(
        &self,
        union: &Union,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Union::new(
            self.inst_obj(&union.left, param_to_arg_map, ctx)?,
            self.inst_obj(&union.right, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_intersect(
        &self,
        intersect: &Intersect,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Intersect::new(
            self.inst_obj(&intersect.left, param_to_arg_map, ctx)?,
            self.inst_obj(&intersect.right, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_set_minus(
        &self,
        set_minus: &SetMinus,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(SetMinus::new(
            self.inst_obj(&set_minus.left, param_to_arg_map, ctx)?,
            self.inst_obj(&set_minus.right, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_set_diff(
        &self,
        set_diff: &SetDiff,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(SetDiff::new(
            self.inst_obj(&set_diff.left, param_to_arg_map, ctx)?,
            self.inst_obj(&set_diff.right, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_cup(
        &self,
        cup: &Cup,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Cup::new(self.inst_obj(&cup.left, param_to_arg_map, ctx)?).into())
    }

    pub fn inst_cap(
        &self,
        cap: &Cap,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Cap::new(self.inst_obj(&cap.left, param_to_arg_map, ctx)?).into())
    }

    pub fn inst_power_set(
        &self,
        power_set: &PowerSet,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(PowerSet::new(self.inst_obj(&power_set.set, param_to_arg_map, ctx)?).into())
    }

    pub fn inst_list_set(
        &self,
        list_set: &ListSet,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let mut list = Vec::with_capacity(list_set.list.len());
        for obj in list_set.list.iter() {
            list.push(self.inst_obj(obj, param_to_arg_map, ctx)?);
        }
        Ok(ListSet::new(list).into())
    }

    pub fn inst_set_builder(
        &self,
        set_builder: &SetBuilder,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let param_names = vec![set_builder.param.clone()];
        let filtered_param_to_arg_map =
            remove_param_names_from_param_to_arg_map(param_to_arg_map, &param_names);
        let mut facts = Vec::with_capacity(set_builder.facts.len());
        for fact in set_builder.facts.iter() {
            facts.push(self.inst_or_and_chain_atomic_fact(fact, &filtered_param_to_arg_map, ctx)?);
        }
        Ok(SetBuilder::new(
            set_builder.param.clone(),
            self.inst_obj(&set_builder.param_set, &filtered_param_to_arg_map, ctx)?,
            facts,
        )
        .into())
    }

    pub fn inst_fn_set_with_params(
        &self,
        fn_set_with_params: &FnSet,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let param_names =
            ParamGroupWithSet::collect_param_names(&fn_set_with_params.params_def_with_set);
        let filtered_param_to_arg_map =
            remove_param_names_from_param_to_arg_map(param_to_arg_map, &param_names);
        let mut params_def_with_set =
            Vec::with_capacity(fn_set_with_params.params_def_with_set.len());
        for param_def_with_set in fn_set_with_params.params_def_with_set.iter() {
            params_def_with_set.push(ParamGroupWithSet::new(
                param_def_with_set.params.clone(),
                self.inst_obj(&param_def_with_set.set, &filtered_param_to_arg_map, ctx)?,
            ));
        }
        let mut dom_facts = Vec::with_capacity(fn_set_with_params.dom_facts.len());
        for dom_fact in fn_set_with_params.dom_facts.iter() {
            dom_facts
                .push(self.inst_or_and_chain_atomic_fact(dom_fact, &filtered_param_to_arg_map, ctx)?);
        }
        Ok(FnSet::new(
            params_def_with_set,
            dom_facts,
            self.inst_obj(&fn_set_with_params.ret_set, &filtered_param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_cart(
        &self,
        cart: &Cart,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let mut args = Vec::with_capacity(cart.args.len());
        for arg in cart.args.iter() {
            args.push(self.inst_obj(arg, param_to_arg_map, ctx)?);
        }
        Ok(Cart::new(args).into())
    }

    pub fn inst_cart_dim(
        &self,
        cart_dim: &CartDim,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(CartDim::new(self.inst_obj(&cart_dim.set, param_to_arg_map, ctx)?).into())
    }

    pub fn inst_proj(
        &self,
        proj: &Proj,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Proj::new(
            self.inst_obj(&proj.set, param_to_arg_map, ctx)?,
            self.inst_obj(&proj.dim, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_tuple_dim(
        &self,
        tuple_dim: &TupleDim,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(TupleDim::new(self.inst_obj(&tuple_dim.arg, param_to_arg_map, ctx)?).into())
    }

    pub fn inst_tuple(
        &self,
        tuple: &Tuple,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let mut elements = Vec::with_capacity(tuple.args.len());
        for element in tuple.args.iter() {
            elements.push(self.inst_obj(element, param_to_arg_map, ctx)?);
        }
        Ok(Tuple::new(elements).into())
    }

    pub fn inst_count(
        &self,
        count: &Count,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Count::new(self.inst_obj(&count.set, param_to_arg_map, ctx)?).into())
    }

    pub fn inst_range(
        &self,
        range: &Range,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Range::new(
            self.inst_obj(&range.start, param_to_arg_map, ctx)?,
            self.inst_obj(&range.end, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_closed_range(
        &self,
        closed_range: &ClosedRange,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(ClosedRange::new(
            self.inst_obj(&closed_range.start, param_to_arg_map, ctx)?,
            self.inst_obj(&closed_range.end, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_finite_seq_set(
        &self,
        fs: &FiniteSeqSet,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(FiniteSeqSet::new(
            self.inst_obj(&fs.set, param_to_arg_map, ctx)?,
            self.inst_obj(&fs.n, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_seq_set(
        &self,
        ss: &SeqSet,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(SeqSet::new(self.inst_obj(&ss.set, param_to_arg_map, ctx)?).into())
    }

    pub fn inst_finite_seq_list_obj(
        &self,
        v: &FiniteSeqListObj,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let mut objs = Vec::with_capacity(v.objs.len());
        for o in v.objs.iter() {
            objs.push(self.inst_obj(o, param_to_arg_map, ctx)?);
        }
        Ok(FiniteSeqListObj::new(objs).into())
    }

    pub fn inst_matrix_set(
        &self,
        ms: &MatrixSet,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(MatrixSet::new(
            self.inst_obj(&ms.set, param_to_arg_map, ctx)?,
            self.inst_obj(&ms.row_len, param_to_arg_map, ctx)?,
            self.inst_obj(&ms.col_len, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_matrix_list_obj(
        &self,
        m: &MatrixListObj,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        let mut rows: Vec<Vec<Obj>> = Vec::with_capacity(m.rows.len());
        for row in m.rows.iter() {
            let mut inst_row = Vec::with_capacity(row.len());
            for o in row.iter() {
                inst_row.push(self.inst_obj(o, param_to_arg_map, ctx)?);
            }
            rows.push(inst_row);
        }
        Ok(MatrixListObj::new(rows).into())
    }

    pub fn inst_choose(
        &self,
        choose: &Choose,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(Choose::new(self.inst_obj(&choose.set, param_to_arg_map, ctx)?).into())
    }

    pub fn inst_obj_at_index(
        &self,
        obj_at_index: &ObjAtIndex,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<Obj, RuntimeError> {
        Ok(ObjAtIndex::new(
            self.inst_obj(&obj_at_index.obj, param_to_arg_map, ctx)?,
            self.inst_obj(&obj_at_index.index, param_to_arg_map, ctx)?,
        )
        .into())
    }

    pub fn inst_standard_set(&self, standard_set: &StandardSet) -> Result<Obj, RuntimeError> {
        Ok(standard_set.clone().into())
    }

    pub fn inst_param_type(
        &self,
        param_type: &ParamType,
        param_to_arg_map: &HashMap<String, Obj>,
        ctx: InstObjState,
    ) -> Result<ParamType, RuntimeError> {
        match param_type {
            ParamType::Set(_) => Ok(param_type.clone()),
            ParamType::FiniteSet(_) => Ok(param_type.clone()),
            ParamType::NonemptySet(_) => Ok(param_type.clone()),
            ParamType::Obj(obj) => Ok(ParamType::Obj(self.inst_obj(obj, param_to_arg_map, ctx)?)),
            ParamType::Struct(struct_ty) => {
                let mut params = Vec::with_capacity(struct_ty.args.len());
                for param in struct_ty.args.iter() {
                    params.push(self.inst_obj(param, param_to_arg_map, ctx)?);
                }
                Ok(ParamType::Struct(StructObj::new(
                    struct_ty.name.clone(),
                    params,
                )))
            }
        }
    }

    pub fn inst_param_def_with_set_one_by_one(
        &self,
        param_defs: &Vec<ParamGroupWithSet>,
        args: &Vec<Obj>,
        inst_state: InstObjState,
    ) -> Result<Vec<Obj>, RuntimeError> {
        let total_param_count = ParamGroupWithSet::number_of_params(param_defs);
        if total_param_count != args.len() {
            return Err(InstantiateRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "argument count mismatch: expected {} parameter(s), got {} argument(s)",
                    total_param_count,
                    args.len()
                ),
                default_line_file(),
                None,
                vec![],
            ))
            .into());
        }

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::with_capacity(total_param_count);
        let mut arg_index: usize = 0;
        let mut instantiated_param_sets: Vec<Obj> = Vec::with_capacity(param_defs.len());
        for param_def in param_defs.iter() {
            let instantiated_param_set = if arg_index != 0 {
                self.inst_obj(&param_def.set, &param_to_arg_map, inst_state)?
            } else {
                param_def.set.clone()
            };
            instantiated_param_sets.push(instantiated_param_set);

            for param_name in param_def.params.iter() {
                param_to_arg_map.insert(param_name.clone(), args[arg_index].clone());
                arg_index += 1;
            }
        }

        Ok(instantiated_param_sets)
    }

    pub fn inst_param_def_with_type_one_by_one(
        &self,
        param_defs: &ParamDefWithType,
        args: &Vec<Obj>,
        inst_state: InstObjState,
    ) -> Result<Vec<ParamType>, RuntimeError> {
        let total_param_count = param_defs.number_of_params();
        if total_param_count != args.len() {
            return Err(InstantiateRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "argument count mismatch: expected {} parameter(s), got {} argument(s)",
                    total_param_count,
                    args.len()
                ),
                default_line_file(),
                None,
                vec![],
            ))
            .into());
        }

        let mut param_arg_map: HashMap<String, Obj> = HashMap::with_capacity(total_param_count);
        let mut arg_index: usize = 0;
        let mut new_types: Vec<ParamType> = Vec::with_capacity(param_defs.groups.len());
        for param_def in param_defs.groups.iter() {
            let new_type = if arg_index != 0 {
                self.inst_param_type(&param_def.param_type, &param_arg_map, inst_state)?
            } else {
                param_def.param_type.clone()
            };
            new_types.push(new_type);

            for param_name in param_def.params.iter() {
                param_arg_map.insert(param_name.clone(), args[arg_index].clone());
                arg_index += 1;
            }
        }

        Ok(new_types)
    }
}
