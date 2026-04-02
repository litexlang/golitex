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
    ) -> Result<Obj, RuntimeError> {
        match obj {
            Obj::Identifier(inner) => self.inst_identifier(inner, param_to_arg_map),
            Obj::IdentifierWithMod(inner) => self.inst_identifier_with_mod(inner, param_to_arg_map),
            Obj::FieldAccess(inner) => self.inst_field_access(inner, param_to_arg_map),
            Obj::FieldAccessWithMod(inner) => {
                self.inst_field_access_with_mod(inner, param_to_arg_map)
            }
            Obj::FnObj(inner) => self.inst_fn_obj(inner, param_to_arg_map),
            Obj::Number(inner) => self.inst_number(inner, param_to_arg_map),
            Obj::Add(inner) => self.inst_add(inner, param_to_arg_map),
            Obj::Sub(inner) => self.inst_sub(inner, param_to_arg_map),
            Obj::Mul(inner) => self.inst_mul(inner, param_to_arg_map),
            Obj::Div(inner) => self.inst_div(inner, param_to_arg_map),
            Obj::Mod(inner) => self.inst_mod(inner, param_to_arg_map),
            Obj::Pow(inner) => self.inst_pow(inner, param_to_arg_map),
            Obj::Union(inner) => self.inst_union(inner, param_to_arg_map),
            Obj::Intersect(inner) => self.inst_intersect(inner, param_to_arg_map),
            Obj::SetMinus(inner) => self.inst_set_minus(inner, param_to_arg_map),
            Obj::SetDiff(inner) => self.inst_set_diff(inner, param_to_arg_map),
            Obj::Cup(inner) => self.inst_cup(inner, param_to_arg_map),
            Obj::Cap(inner) => self.inst_cap(inner, param_to_arg_map),
            Obj::ListSet(inner) => self.inst_list_set(inner, param_to_arg_map),
            Obj::SetBuilder(inner) => self.inst_set_builder(inner, param_to_arg_map),
            Obj::FnSetWithParams(inner) => self.inst_fn_set_with_params(inner, param_to_arg_map),
            Obj::StandardSet(standard_set) => self.inst_standard_set(standard_set),
            Obj::Cart(inner) => self.inst_cart(inner, param_to_arg_map),
            Obj::CartDim(inner) => self.inst_cart_dim(inner, param_to_arg_map),
            Obj::Proj(inner) => self.inst_proj(inner, param_to_arg_map),
            Obj::TupleDim(inner) => self.inst_tuple_dim(inner, param_to_arg_map),
            Obj::Tuple(inner) => self.inst_tuple(inner, param_to_arg_map),
            Obj::Count(inner) => self.inst_count(inner, param_to_arg_map),
            Obj::Range(inner) => self.inst_range(inner, param_to_arg_map),
            Obj::ClosedRange(inner) => self.inst_closed_range(inner, param_to_arg_map),
            Obj::PowerSet(inner) => self.inst_power_set(inner, param_to_arg_map),
            Obj::Choose(inner) => self.inst_choose(inner, param_to_arg_map),
            Obj::ObjAtIndex(inner) => self.inst_obj_at_index(inner, param_to_arg_map),
        }
    }

    pub fn inst_atom(
        &self,
        atom: &Atom,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Atom, RuntimeError> {
        match atom {
            Atom::Identifier(identifier) => match self.inst_identifier(identifier, param_to_arg_map)? {
                Obj::Identifier(new_identifier) => Ok(Atom::Identifier(new_identifier)),
                Obj::IdentifierWithMod(new_identifier_with_mod) => {
                    Ok(Atom::IdentifierWithMod(new_identifier_with_mod))
                }
                Obj::FieldAccess(new_field_access) => Ok(Atom::FieldAccess(new_field_access)),
                Obj::FieldAccessWithMod(new_field_access_with_mod) => {
                    Ok(Atom::FieldAccessWithMod(new_field_access_with_mod))
                }
                _ => Ok(Atom::Identifier(identifier.clone())),
            },
            Atom::IdentifierWithMod(identifier_with_mod) => {
                Ok(Atom::IdentifierWithMod(identifier_with_mod.clone()))
            }
            Atom::FieldAccess(field_access) => match self.inst_field_access(field_access, param_to_arg_map)? {
                Obj::Identifier(new_identifier) => Ok(Atom::Identifier(new_identifier)),
                Obj::IdentifierWithMod(new_identifier_with_mod) => {
                    Ok(Atom::IdentifierWithMod(new_identifier_with_mod))
                }
                Obj::FieldAccess(new_field_access) => Ok(Atom::FieldAccess(new_field_access)),
                Obj::FieldAccessWithMod(new_field_access_with_mod) => {
                    Ok(Atom::FieldAccessWithMod(new_field_access_with_mod))
                }
                _ => Ok(Atom::FieldAccess(field_access.clone())),
            },
            Atom::FieldAccessWithMod(field_access_with_mod) => {
                Ok(Atom::FieldAccessWithMod(field_access_with_mod.clone()))
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
            None => Obj::Identifier(identifier.clone()),
        })
    }

    pub fn inst_identifier_with_mod(
        &self,
        identifier_with_mod: &IdentifierWithMod,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        _ = param_to_arg_map;
        Ok(Obj::IdentifierWithMod(identifier_with_mod.clone()))
    }

    pub fn inst_field_access(
        &self,
        field_access: &FieldAccess,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        match param_to_arg_map.get(&field_access.name) {
            Some(Obj::Identifier(identifier)) => Ok(Obj::FieldAccess(FieldAccess {
                name: identifier.name.clone(),
                field: field_access.field.clone(),
            })),
            Some(Obj::IdentifierWithMod(identifier_with_mod)) => {
                Ok(Obj::FieldAccessWithMod(FieldAccessWithMod {
                    mod_name: identifier_with_mod.mod_name.clone(),
                    name: identifier_with_mod.name.clone(),
                    field: field_access.field.clone(),
                }))
            }
            Some(obj) => {
                let tuple_opt = match obj {
                    Obj::Tuple(t) => Some(t.clone()),
                    _ => self.get_known_tuple_obj_of_obj(&obj.to_string()),
                };
                match tuple_opt {
                    Some(t) => self.inst_field_access_on_struct_tuple(field_access, &t),
                    None => return Err(RuntimeError::InstantiateError(RuntimeErrorStruct::new(
                        None,
                        format!("field `{}` of struct `{}` is not a tuple", field_access.field, field_access.name),
                        DEFAULT_LINE_FILE,
                        None,
                    ))),
                }
            }
            None => Ok(Obj::FieldAccess(field_access.clone())),
        }
    }

    fn inst_field_access_on_struct_tuple(
        &self,
        field_access: &FieldAccess,
        tuple: &Tuple,
    ) -> Result<Obj, RuntimeError> {
        let Some(inst_struct) = self.get_inst_struct_obj_for_field_access_root(&field_access.name)
        else {
            return Ok(Obj::FieldAccess(field_access.clone()));
        };
        let struct_name = inst_struct.struct_name.to_string();
        let Some(def) = self.get_cloned_param_type_struct_definition_by_name(&struct_name) else {
            return Ok(Obj::FieldAccess(field_access.clone()));
        };
        let Some(field_index) = def
            .fields
            .iter()
            .position(|(fname, _)| fname == &field_access.field)
        else {
            return Ok(Obj::FieldAccess(field_access.clone()));
        };
        let Some(component) = tuple.args.get(field_index + def.number_of_params()) else {
            return Err(RuntimeError::InstantiateError(RuntimeErrorStruct::new(
                None,
                format!(
                    "field `{}` of struct `{}` is at index {}, but tuple for `{}` has only {} component(s)",
                    field_access.field,
                    struct_name,
                    field_index,
                    field_access.name,
                    tuple.args.len()
                ),
                DEFAULT_LINE_FILE,
                None,
            )));
        };
        Ok((**component).clone())
    }

    pub fn inst_field_access_with_mod(
        &self,
        field_access_with_mod: &FieldAccessWithMod,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        _ = param_to_arg_map;
        Ok(Obj::FieldAccessWithMod(field_access_with_mod.clone()))
    }

    pub fn inst_fn_obj(
        &self,
        fn_obj: &FnObj,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        let mut body = Vec::with_capacity(fn_obj.body.len());
        for obj_vec in fn_obj.body.iter() {
            let mut new_obj_vec = Vec::with_capacity(obj_vec.len());
            for obj in obj_vec.iter() {
                new_obj_vec.push(Box::new(self.inst_obj(obj, param_to_arg_map)?));
            }
            body.push(new_obj_vec);
        }
        Ok(Obj::FnObj(FnObj {
            head: Box::new(self.inst_atom(&fn_obj.head, param_to_arg_map)?),
            body,
        }))
    }

    pub fn inst_number(
        &self,
        number: &Number,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        _ = param_to_arg_map;
        Ok(Obj::Number(number.clone()))
    }

    pub fn inst_add(&self, add: &Add, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&add.left, param_to_arg_map)?;
        let instantiated_right_obj = self.inst_obj(&add.right, param_to_arg_map)?;
        Ok(Obj::Add(Add::new(instantiated_left_obj, instantiated_right_obj)))
    }

    pub fn inst_sub(&self, sub: &Sub, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&sub.left, param_to_arg_map)?;
        let instantiated_right_obj = self.inst_obj(&sub.right, param_to_arg_map)?;
        Ok(Obj::Sub(Sub::new(instantiated_left_obj, instantiated_right_obj)))
    }

    pub fn inst_mul(&self, mul: &Mul, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&mul.left, param_to_arg_map)?;
        let instantiated_right_obj = self.inst_obj(&mul.right, param_to_arg_map)?;
        Ok(Obj::Mul(Mul::new(instantiated_left_obj, instantiated_right_obj)))
    }

    pub fn inst_div(&self, div: &Div, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        Ok(Obj::Div(Div {
            left: Box::new(self.inst_obj(&div.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj(&div.right, param_to_arg_map)?),
        }))
    }

    pub fn inst_mod(&self, mod_obj: &Mod, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&mod_obj.left, param_to_arg_map)?;
        let instantiated_right_obj = self.inst_obj(&mod_obj.right, param_to_arg_map)?;
        Ok(Obj::Mod(Mod::new(instantiated_left_obj, instantiated_right_obj)))
    }

    pub fn inst_pow(&self, pow: &Pow, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        let instantiated_base_obj = self.inst_obj(&pow.base, param_to_arg_map)?;
        let instantiated_exponent_obj = self.inst_obj(&pow.exponent, param_to_arg_map)?;
        Ok(Obj::Pow(Pow::new(instantiated_base_obj, instantiated_exponent_obj)))
    }

    pub fn inst_union(&self, union: &Union, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        Ok(Obj::Union(Union {
            left: Box::new(self.inst_obj(&union.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj(&union.right, param_to_arg_map)?),
        }))
    }

    pub fn inst_intersect(
        &self,
        intersect: &Intersect,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        Ok(Obj::Intersect(Intersect {
            left: Box::new(self.inst_obj(&intersect.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj(&intersect.right, param_to_arg_map)?),
        }))
    }

    pub fn inst_set_minus(
        &self,
        set_minus: &SetMinus,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        Ok(Obj::SetMinus(SetMinus {
            left: Box::new(self.inst_obj(&set_minus.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj(&set_minus.right, param_to_arg_map)?),
        }))
    }

    pub fn inst_set_diff(
        &self,
        set_diff: &SetDiff,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        Ok(Obj::SetDiff(SetDiff {
            left: Box::new(self.inst_obj(&set_diff.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj(&set_diff.right, param_to_arg_map)?),
        }))
    }

    pub fn inst_cup(&self, cup: &Cup, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        Ok(Obj::Cup(Cup {
            left: Box::new(self.inst_obj(&cup.left, param_to_arg_map)?),
        }))
    }

    pub fn inst_cap(&self, cap: &Cap, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        Ok(Obj::Cap(Cap {
            left: Box::new(self.inst_obj(&cap.left, param_to_arg_map)?),
        }))
    }

    pub fn inst_power_set(
        &self,
        power_set: &PowerSet,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        Ok(Obj::PowerSet(PowerSet {
            set: Box::new(self.inst_obj(&power_set.set, param_to_arg_map)?),
        }))
    }

    pub fn inst_list_set(
        &self,
        list_set: &ListSet,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        let mut list = Vec::with_capacity(list_set.list.len());
        for obj in list_set.list.iter() {
            list.push(Box::new(self.inst_obj(obj, param_to_arg_map)?));
        }
        Ok(Obj::ListSet(ListSet { list }))
    }

    pub fn inst_set_builder(
        &self,
        set_builder: &SetBuilder,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        let param_names = vec![set_builder.param.clone()];
        let filtered_param_to_arg_map =
            remove_param_names_from_param_to_arg_map(param_to_arg_map, &param_names);
        let mut facts = Vec::with_capacity(set_builder.facts.len());
        for fact in set_builder.facts.iter() {
            facts.push(self.inst_or_and_chain_atomic_fact(fact, &filtered_param_to_arg_map)?);
        }
        Ok(Obj::SetBuilder(SetBuilder {
            param: set_builder.param.clone(),
            param_set: Box::new(self.inst_obj(&set_builder.param_set, &filtered_param_to_arg_map)?),
            facts,
        }))
    }

    pub fn inst_fn_set_with_params(
        &self,
        fn_set_with_params: &FnSetWithParams,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        let param_names = ParamDefWithParamSet::collect_param_names(&fn_set_with_params.params_def_with_set);
        let filtered_param_to_arg_map =
            remove_param_names_from_param_to_arg_map(param_to_arg_map, &param_names);
        let mut params_def_with_set = Vec::with_capacity(fn_set_with_params.params_def_with_set.len());
        for param_def_with_set in fn_set_with_params.params_def_with_set.iter() {
            params_def_with_set.push(ParamDefWithParamSet(
                param_def_with_set.0.clone(),
                self.inst_obj(&param_def_with_set.1, &filtered_param_to_arg_map)?,
            ));
        }
        let mut dom_facts = Vec::with_capacity(fn_set_with_params.dom_facts.len());
        for dom_fact in fn_set_with_params.dom_facts.iter() {
            dom_facts.push(self.inst_or_and_chain_atomic_fact(dom_fact, &filtered_param_to_arg_map)?);
        }
        Ok(Obj::FnSetWithParams(FnSetWithParams {
            params_def_with_set,
            dom_facts,
            ret_set: Box::new(self.inst_obj(&fn_set_with_params.ret_set, &filtered_param_to_arg_map)?),
        }))
    }

    pub fn inst_cart(&self, cart: &Cart, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        let mut args = Vec::with_capacity(cart.args.len());
        for arg in cart.args.iter() {
            args.push(Box::new(self.inst_obj(arg, param_to_arg_map)?));
        }
        Ok(Obj::Cart(Cart { args }))
    }

    pub fn inst_cart_dim(
        &self,
        cart_dim: &CartDim,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        Ok(Obj::CartDim(CartDim {
            set: Box::new(self.inst_obj(&cart_dim.set, param_to_arg_map)?),
        }))
    }

    pub fn inst_proj(&self, proj: &Proj, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        Ok(Obj::Proj(Proj {
            set: Box::new(self.inst_obj(&proj.set, param_to_arg_map)?),
            dim: Box::new(self.inst_obj(&proj.dim, param_to_arg_map)?),
        }))
    }

    pub fn inst_tuple_dim(
        &self,
        tuple_dim: &TupleDim,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        Ok(Obj::TupleDim(TupleDim {
            arg: Box::new(self.inst_obj(&tuple_dim.arg, param_to_arg_map)?),
        }))
    }

    pub fn inst_tuple(&self, tuple: &Tuple, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        let mut elements = Vec::with_capacity(tuple.args.len());
        for element in tuple.args.iter() {
            elements.push(Box::new(self.inst_obj(element, param_to_arg_map)?));
        }
        Ok(Obj::Tuple(Tuple { args: elements }))
    }

    pub fn inst_count(&self, count: &Count, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        Ok(Obj::Count(Count {
            set: Box::new(self.inst_obj(&count.set, param_to_arg_map)?),
        }))
    }

    pub fn inst_range(&self, range: &Range, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        Ok(Obj::Range(Range {
            start: Box::new(self.inst_obj(&range.start, param_to_arg_map)?),
            end: Box::new(self.inst_obj(&range.end, param_to_arg_map)?),
        }))
    }

    pub fn inst_closed_range(
        &self,
        closed_range: &ClosedRange,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        Ok(Obj::ClosedRange(ClosedRange {
            start: Box::new(self.inst_obj(&closed_range.start, param_to_arg_map)?),
            end: Box::new(self.inst_obj(&closed_range.end, param_to_arg_map)?),
        }))
    }

    pub fn inst_choose(&self, choose: &Choose, param_to_arg_map: &HashMap<String, Obj>) -> Result<Obj, RuntimeError> {
        Ok(Obj::Choose(Choose {
            set: Box::new(self.inst_obj(&choose.set, param_to_arg_map)?),
        }))
    }

    pub fn inst_obj_at_index(
        &self,
        obj_at_index: &ObjAtIndex,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Obj, RuntimeError> {
        Ok(Obj::ObjAtIndex(ObjAtIndex {
            obj: Box::new(self.inst_obj(&obj_at_index.obj, param_to_arg_map)?),
            index: Box::new(self.inst_obj(&obj_at_index.index, param_to_arg_map)?),
        }))
    }

    pub fn inst_standard_set(&self, standard_set: &StandardSet) -> Result<Obj, RuntimeError> {
        Ok(Obj::StandardSet(standard_set.clone()))
    }

    pub fn inst_param_type(
        &self,
        param_type: &ParamType,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<ParamType, RuntimeError> {
        match param_type {
            ParamType::Set(_) => Ok(param_type.clone()),
            ParamType::FiniteSet(_) => Ok(param_type.clone()),
            ParamType::NonemptySet(_) => Ok(param_type.clone()),
            ParamType::Obj(obj) => Ok(ParamType::Obj(self.inst_obj(obj, param_to_arg_map)?)),
            ParamType::Family(family) => {
                let mut params = Vec::with_capacity(family.params.len());
                for param in family.params.iter() {
                    params.push(self.inst_obj(param, param_to_arg_map)?);
                }
                Ok(ParamType::Family(FamilyParamType {
                    name: family.name.clone(),
                    params,
                }))
            }
            ParamType::Struct(struct_ty) => {
                let mut params = Vec::with_capacity(struct_ty.args.len());
                for param in struct_ty.args.iter() {
                    params.push(self.inst_obj(param, param_to_arg_map)?);
                }
                Ok(ParamType::Struct(StructParamType {
                    name: struct_ty.name.clone(),
                    args: params,
                }))
            }
        }
    }

    pub fn inst_param_def_with_set_one_by_one(
        &self,
        param_defs: &Vec<ParamDefWithParamSet>,
        args: &Vec<Obj>,
    ) -> Result<Vec<Obj>, RuntimeError> {
        let total_param_count = ParamDefWithParamSet::number_of_params(param_defs);
        if total_param_count != args.len() {
            return Err(RuntimeError::InstantiateError(RuntimeErrorStruct::new(
                None,
                format!(
                    "argument count mismatch: expected {} parameter(s), got {} argument(s)",
                    total_param_count,
                    args.len()
                ),
                DEFAULT_LINE_FILE,
                None,
            )));
        }

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::with_capacity(total_param_count);
        let mut arg_index: usize = 0;
        let mut instantiated_param_sets: Vec<Obj> = Vec::with_capacity(param_defs.len());
        for param_def in param_defs.iter() {
            let instantiated_param_set = if arg_index != 0 {
                self.inst_obj(&param_def.1, &param_to_arg_map)?
            } else {
                param_def.1.clone()
            };
            instantiated_param_sets.push(instantiated_param_set);

            for param_name in param_def.0.iter() {
                param_to_arg_map.insert(param_name.clone(), args[arg_index].clone());
                arg_index += 1;
            }
        }

        Ok(instantiated_param_sets)
    }

    pub fn inst_param_def_with_type_one_by_one(
        &self,
        param_defs: &Vec<ParamDefWithParamType>,
        args: &Vec<Obj>,
    ) -> Result<Vec<ParamType>, RuntimeError> {
        let total_param_count = ParamDefWithParamType::number_of_params(param_defs);
        if total_param_count != args.len() {
            return Err(RuntimeError::InstantiateError(RuntimeErrorStruct::new(
                None,
                format!(
                    "argument count mismatch: expected {} parameter(s), got {} argument(s)",
                    total_param_count,
                    args.len()
                ),
                DEFAULT_LINE_FILE,
                None,
            )));
        }

        let mut param_arg_map: HashMap<String, Obj> = HashMap::with_capacity(total_param_count);
        let mut arg_index: usize = 0;
        let mut new_types: Vec<ParamType> = Vec::with_capacity(param_defs.len());
        for param_def in param_defs.iter() {
            let new_type = if arg_index != 0 {
                self.inst_param_type(&param_def.1, &param_arg_map)?
            } else {
                param_def.1.clone()
            };
            new_types.push(new_type);

            for param_name in param_def.0.iter() {
                param_arg_map.insert(param_name.clone(), args[arg_index].clone());
                arg_index += 1;
            }
        }

        Ok(new_types)
    }
}
