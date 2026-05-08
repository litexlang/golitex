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
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        match obj {
            Obj::Atom(AtomObj::Identifier(inner)) => self.inst_identifier(inner, param_to_arg_map),
            Obj::Atom(AtomObj::IdentifierWithMod(inner)) => {
                self.inst_identifier_with_mod(inner, param_to_arg_map)
            }
            Obj::FnObj(inner) => self.inst_fn_obj(inner, param_to_arg_map, param_obj_type),
            Obj::Number(inner) => self.inst_number(inner, param_to_arg_map, param_obj_type),
            Obj::Add(inner) => self.inst_add(inner, param_to_arg_map, param_obj_type),
            Obj::Sub(inner) => self.inst_sub(inner, param_to_arg_map, param_obj_type),
            Obj::Mul(inner) => self.inst_mul(inner, param_to_arg_map, param_obj_type),
            Obj::Div(inner) => self.inst_div(inner, param_to_arg_map, param_obj_type),
            Obj::Mod(inner) => self.inst_mod(inner, param_to_arg_map, param_obj_type),
            Obj::Pow(inner) => self.inst_pow(inner, param_to_arg_map, param_obj_type),
            Obj::MatrixAdd(inner) => self.inst_matrix_add(inner, param_to_arg_map, param_obj_type),
            Obj::MatrixSub(inner) => self.inst_matrix_sub(inner, param_to_arg_map, param_obj_type),
            Obj::MatrixMul(inner) => self.inst_matrix_mul(inner, param_to_arg_map, param_obj_type),
            Obj::MatrixScalarMul(inner) => {
                self.inst_matrix_scalar_mul(inner, param_to_arg_map, param_obj_type)
            }
            Obj::MatrixPow(inner) => self.inst_matrix_pow(inner, param_to_arg_map, param_obj_type),
            Obj::Abs(inner) => self.inst_abs(inner, param_to_arg_map, param_obj_type),
            Obj::Log(inner) => self.inst_log(inner, param_to_arg_map, param_obj_type),
            Obj::Max(inner) => self.inst_max(inner, param_to_arg_map, param_obj_type),
            Obj::Min(inner) => self.inst_min(inner, param_to_arg_map, param_obj_type),
            Obj::Union(inner) => self.inst_union(inner, param_to_arg_map, param_obj_type),
            Obj::Intersect(inner) => self.inst_intersect(inner, param_to_arg_map, param_obj_type),
            Obj::SetMinus(inner) => self.inst_set_minus(inner, param_to_arg_map, param_obj_type),
            Obj::SetDiff(inner) => self.inst_set_diff(inner, param_to_arg_map, param_obj_type),
            Obj::Cup(inner) => self.inst_cup(inner, param_to_arg_map, param_obj_type),
            Obj::Cap(inner) => self.inst_cap(inner, param_to_arg_map, param_obj_type),
            Obj::ListSet(inner) => self.inst_list_set(inner, param_to_arg_map, param_obj_type),
            Obj::SetBuilder(inner) => {
                self.inst_set_builder(inner, param_to_arg_map, param_obj_type)
            }
            Obj::FnSet(inner) => {
                self.inst_fn_set_with_params(inner, param_to_arg_map, param_obj_type)
            }
            Obj::AnonymousFn(inner) => {
                self.inst_anonymous_fn_with_params(inner, param_to_arg_map, param_obj_type)
            }
            Obj::StandardSet(standard_set) => self.inst_standard_set(standard_set),
            Obj::Cart(inner) => self.inst_cart(inner, param_to_arg_map, param_obj_type),
            Obj::CartDim(inner) => self.inst_cart_dim(inner, param_to_arg_map, param_obj_type),
            Obj::Proj(inner) => self.inst_proj(inner, param_to_arg_map, param_obj_type),
            Obj::TupleDim(inner) => self.inst_tuple_dim(inner, param_to_arg_map, param_obj_type),
            Obj::Tuple(inner) => self.inst_tuple(inner, param_to_arg_map, param_obj_type),
            Obj::Count(inner) => self.inst_count(inner, param_to_arg_map, param_obj_type),
            Obj::Sum(inner) => self.inst_sum(inner, param_to_arg_map, param_obj_type),
            Obj::Product(inner) => self.inst_product(inner, param_to_arg_map, param_obj_type),
            Obj::Range(inner) => self.inst_range(inner, param_to_arg_map, param_obj_type),
            Obj::ClosedRange(inner) => {
                self.inst_closed_range(inner, param_to_arg_map, param_obj_type)
            }
            Obj::FiniteSeqSet(inner) => {
                self.inst_finite_seq_set(inner, param_to_arg_map, param_obj_type)
            }
            Obj::SeqSet(inner) => self.inst_seq_set(inner, param_to_arg_map, param_obj_type),
            Obj::FiniteSeqListObj(inner) => {
                self.inst_finite_seq_list_obj(inner, param_to_arg_map, param_obj_type)
            }
            Obj::MatrixSet(inner) => self.inst_matrix_set(inner, param_to_arg_map, param_obj_type),
            Obj::MatrixListObj(inner) => {
                self.inst_matrix_list_obj(inner, param_to_arg_map, param_obj_type)
            }
            Obj::PowerSet(inner) => self.inst_power_set(inner, param_to_arg_map, param_obj_type),
            Obj::Choose(inner) => self.inst_choose(inner, param_to_arg_map, param_obj_type),
            Obj::ObjAtIndex(inner) => {
                self.inst_obj_at_index(inner, param_to_arg_map, param_obj_type)
            }
            Obj::FamilyObj(family) => {
                let mut params = Vec::with_capacity(family.params.len());
                for p in family.params.iter() {
                    params.push(self.inst_obj(p, param_to_arg_map, param_obj_type)?);
                }
                Ok(FamilyObj::new(family.name.clone(), params).into())
            }
            Obj::FieldAccess(field_access) => {
                if let Some(obj) = param_to_arg_map.get(&field_access.to_string()) {
                    return Ok(obj.clone());
                }
                if let Some(Obj::StructInstance(instance)) =
                    param_to_arg_map.get(&field_access.left)
                {
                    if let Some(field_obj) =
                        self.field_obj_from_struct_instance(instance, &field_access.right)?
                    {
                        return Ok(field_obj);
                    }
                }
                let left = match param_to_arg_map.get(&field_access.left) {
                    Some(obj) => Self::obj_name_for_instantiated_field_access_left(obj)
                        .unwrap_or_else(|| field_access.left.clone()),
                    _ => field_access.left.clone(),
                };
                Ok(FieldAccess::new(left, field_access.right.clone()).into())
            }
            Obj::StructInstance(instance) => {
                let name = StructAsParamType::new_with_boxed_args(
                    instance.name.name.clone(),
                    self.inst_boxed_objs(&instance.name.args, param_to_arg_map, param_obj_type)?,
                );
                let fields_equal_to_what = self.inst_boxed_objs(
                    &instance.fields_equal_to_what,
                    param_to_arg_map,
                    param_obj_type,
                )?;
                Ok(StructInstance::new_with_boxed_fields(name, fields_equal_to_what).into())
            }
            Obj::Atom(AtomObj::Forall(p)) => {
                if param_obj_type == ParamObjType::Forall {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                // See `runtime_instantiate_have_fn_forall.rs`: under FnSet inst, align Forall atoms
                // with the canonical forall binder map.
                if param_obj_type == ParamObjType::FnSet {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::Atom(AtomObj::Def(p)) => {
                if param_obj_type == ParamObjType::DefHeader {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::Atom(AtomObj::Exist(p)) => {
                if param_obj_type == ParamObjType::Exist {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::Atom(AtomObj::SetBuilder(p)) => {
                if param_obj_type == ParamObjType::SetBuilder {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::Atom(AtomObj::FnSet(p)) => {
                if param_obj_type == ParamObjType::FnSet {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::Atom(AtomObj::Induc(p)) => {
                if param_obj_type == ParamObjType::Induc || param_obj_type == ParamObjType::Forall {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                if param_obj_type == ParamObjType::FnSet {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::Atom(AtomObj::DefAlgo(p)) => {
                if param_obj_type == ParamObjType::DefAlgo || param_obj_type == ParamObjType::Forall
                {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::Atom(AtomObj::DefStructField(p)) => {
                if param_obj_type == ParamObjType::DefStructField {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
        }
    }

    fn field_obj_from_struct_instance(
        &self,
        instance: &StructInstance,
        field_name: &str,
    ) -> Result<Option<Obj>, RuntimeError> {
        let struct_name = instance.name.struct_name();
        let Some(def) = self.get_struct_definition_by_name(&struct_name) else {
            return Ok(None);
        };
        let Some(index) = def
            .fields
            .iter()
            .position(|(defined_field_name, _)| defined_field_name == field_name)
        else {
            return Ok(None);
        };
        Ok(instance
            .fields_equal_to_what
            .get(index)
            .map(|field| (**field).clone()))
    }

    fn inst_boxed_objs(
        &self,
        objs: &[Box<Obj>],
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Vec<Box<Obj>>, RuntimeError> {
        let mut result = Vec::with_capacity(objs.len());
        for obj in objs.iter() {
            result.push(Box::new(self.inst_obj(
                obj,
                param_to_arg_map,
                param_obj_type,
            )?));
        }
        Ok(result)
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

    pub fn inst_fn_obj(
        &self,
        fn_obj: &FnObj,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let mut merged_body = Vec::with_capacity(fn_obj.body.len());
        for obj_vec in fn_obj.body.iter() {
            let mut new_obj_vec = Vec::with_capacity(obj_vec.len());
            for obj in obj_vec.iter() {
                new_obj_vec.push(Box::new(self.inst_obj(
                    obj,
                    param_to_arg_map,
                    param_obj_type,
                )?));
            }
            merged_body.push(new_obj_vec);
        }

        let inst_head = self.inst_obj(
            &(*fn_obj.head.clone()).into(),
            param_to_arg_map,
            param_obj_type,
        )?;

        let final_head: FnObjHead = match inst_head {
            Obj::Atom(AtomObj::Identifier(x)) => FnObjHead::Identifier(x.clone()),
            Obj::Atom(AtomObj::IdentifierWithMod(x)) => FnObjHead::IdentifierWithMod(x.clone()),
            Obj::Atom(AtomObj::Forall(p)) => p.clone().into(),
            Obj::Atom(AtomObj::Def(p)) => p.clone().into(),
            Obj::Atom(AtomObj::Exist(p)) => p.clone().into(),
            Obj::Atom(AtomObj::SetBuilder(p)) => p.clone().into(),
            Obj::Atom(AtomObj::FnSet(p)) => p.clone().into(),
            Obj::Atom(AtomObj::Induc(p)) => p.clone().into(),
            Obj::Atom(AtomObj::DefAlgo(p)) => p.clone().into(),
            Obj::Atom(AtomObj::DefStructField(_)) => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(
                        "struct field cannot be used as a function head".to_string(),
                    ),
                )));
            }
            Obj::AnonymousFn(a) => FnObjHead::AnonymousFnLiteral(Box::new(a)),
            Obj::FnObj(x) => {
                let merged_body_original = merged_body.clone();
                merged_body = vec![];
                merged_body.extend(x.body);
                merged_body.extend(merged_body_original);
                *x.head.clone()
            }
            _ => return Err(InstantiateRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!("instantiate fn object: after substitution, head must be an atom, curried fn, or free-param binder, got {}", inst_head)))
            .into()),
        };

        Ok(FnObj::new(final_head, merged_body).into())
    }

    pub fn inst_number(
        &self,
        number: &Number,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        _ = param_to_arg_map;
        _ = param_obj_type;
        Ok(number.clone().into())
    }

    pub fn inst_add(
        &self,
        add: &Add,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&add.left, param_to_arg_map, param_obj_type)?;
        let instantiated_right_obj = self.inst_obj(&add.right, param_to_arg_map, param_obj_type)?;
        Ok(Add::new(instantiated_left_obj, instantiated_right_obj).into())
    }

    pub fn inst_matrix_add(
        &self,
        ma: &MatrixAdd,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&ma.left, param_to_arg_map, param_obj_type)?;
        let instantiated_right_obj = self.inst_obj(&ma.right, param_to_arg_map, param_obj_type)?;
        Ok(MatrixAdd::new(instantiated_left_obj, instantiated_right_obj).into())
    }

    pub fn inst_matrix_sub(
        &self,
        ms: &MatrixSub,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let l = self.inst_obj(&ms.left, param_to_arg_map, param_obj_type)?;
        let r = self.inst_obj(&ms.right, param_to_arg_map, param_obj_type)?;
        Ok(MatrixSub::new(l, r).into())
    }

    pub fn inst_matrix_mul(
        &self,
        mm: &MatrixMul,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let l = self.inst_obj(&mm.left, param_to_arg_map, param_obj_type)?;
        let r = self.inst_obj(&mm.right, param_to_arg_map, param_obj_type)?;
        Ok(MatrixMul::new(l, r).into())
    }

    pub fn inst_matrix_scalar_mul(
        &self,
        m: &MatrixScalarMul,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let s = self.inst_obj(&m.scalar, param_to_arg_map, param_obj_type)?;
        let mat = self.inst_obj(&m.matrix, param_to_arg_map, param_obj_type)?;
        Ok(MatrixScalarMul::new(s, mat).into())
    }

    pub fn inst_matrix_pow(
        &self,
        m: &MatrixPow,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let b = self.inst_obj(&m.base, param_to_arg_map, param_obj_type)?;
        let e = self.inst_obj(&m.exponent, param_to_arg_map, param_obj_type)?;
        Ok(MatrixPow::new(b, e).into())
    }

    pub fn inst_sub(
        &self,
        sub: &Sub,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&sub.left, param_to_arg_map, param_obj_type)?;
        let instantiated_right_obj = self.inst_obj(&sub.right, param_to_arg_map, param_obj_type)?;
        Ok(Sub::new(instantiated_left_obj, instantiated_right_obj).into())
    }

    pub fn inst_mul(
        &self,
        mul: &Mul,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj = self.inst_obj(&mul.left, param_to_arg_map, param_obj_type)?;
        let instantiated_right_obj = self.inst_obj(&mul.right, param_to_arg_map, param_obj_type)?;
        Ok(Mul::new(instantiated_left_obj, instantiated_right_obj).into())
    }

    pub fn inst_div(
        &self,
        div: &Div,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Div::new(
            self.inst_obj(&div.left, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&div.right, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_mod(
        &self,
        mod_obj: &Mod,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_left_obj =
            self.inst_obj(&mod_obj.left, param_to_arg_map, param_obj_type)?;
        let instantiated_right_obj =
            self.inst_obj(&mod_obj.right, param_to_arg_map, param_obj_type)?;
        Ok(Mod::new(instantiated_left_obj, instantiated_right_obj).into())
    }

    pub fn inst_pow(
        &self,
        pow: &Pow,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_base_obj = self.inst_obj(&pow.base, param_to_arg_map, param_obj_type)?;
        let instantiated_exponent_obj =
            self.inst_obj(&pow.exponent, param_to_arg_map, param_obj_type)?;
        Ok(Pow::new(instantiated_base_obj, instantiated_exponent_obj).into())
    }

    pub fn inst_abs(
        &self,
        abs: &Abs,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Abs::new(self.inst_obj(&abs.arg, param_to_arg_map, param_obj_type)?).into())
    }

    pub fn inst_log(
        &self,
        log: &Log,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Log::new(
            self.inst_obj(&log.base, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&log.arg, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_max(
        &self,
        max: &Max,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Max::new(
            self.inst_obj(&max.left, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&max.right, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_min(
        &self,
        min: &Min,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Min::new(
            self.inst_obj(&min.left, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&min.right, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_union(
        &self,
        union: &Union,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Union::new(
            self.inst_obj(&union.left, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&union.right, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_intersect(
        &self,
        intersect: &Intersect,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Intersect::new(
            self.inst_obj(&intersect.left, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&intersect.right, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_set_minus(
        &self,
        set_minus: &SetMinus,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(SetMinus::new(
            self.inst_obj(&set_minus.left, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&set_minus.right, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_set_diff(
        &self,
        set_diff: &SetDiff,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(SetDiff::new(
            self.inst_obj(&set_diff.left, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&set_diff.right, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_cup(
        &self,
        cup: &Cup,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Cup::new(self.inst_obj(&cup.left, param_to_arg_map, param_obj_type)?).into())
    }

    pub fn inst_cap(
        &self,
        cap: &Cap,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Cap::new(self.inst_obj(&cap.left, param_to_arg_map, param_obj_type)?).into())
    }

    pub fn inst_power_set(
        &self,
        power_set: &PowerSet,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(PowerSet::new(self.inst_obj(&power_set.set, param_to_arg_map, param_obj_type)?).into())
    }

    pub fn inst_list_set(
        &self,
        list_set: &ListSet,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let mut list = Vec::with_capacity(list_set.list.len());
        for obj in list_set.list.iter() {
            list.push(self.inst_obj(obj, param_to_arg_map, param_obj_type)?);
        }
        Ok(ListSet::new(list).into())
    }

    pub fn inst_set_builder(
        &self,
        set_builder: &SetBuilder,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let param_names = vec![set_builder.param.clone()];
        let filtered_param_to_arg_map =
            remove_param_names_from_param_to_arg_map(param_to_arg_map, &param_names);
        let mut facts = Vec::with_capacity(set_builder.facts.len());
        for fact in set_builder.facts.iter() {
            facts.push(self.inst_or_and_chain_atomic_fact(
                fact,
                &filtered_param_to_arg_map,
                param_obj_type,
                None,
            )?);
        }
        Ok(SetBuilder::new(
            set_builder.param.clone(),
            self.inst_obj(
                &set_builder.param_set,
                &filtered_param_to_arg_map,
                param_obj_type,
            )?,
            facts,
        )?
        .into())
    }

    pub fn inst_fn_set_with_params(
        &self,
        fn_set_with_params: &FnSet,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let param_names =
            ParamGroupWithSet::collect_param_names(&fn_set_with_params.body.params_def_with_set);
        let filtered_param_to_arg_map =
            remove_param_names_from_param_to_arg_map(param_to_arg_map, &param_names);
        let mut params_def_with_set =
            Vec::with_capacity(fn_set_with_params.body.params_def_with_set.len());
        for param_def_with_set in fn_set_with_params.body.params_def_with_set.iter() {
            if let Some(struct_ty) = param_def_with_set.struct_ty() {
                let inst_ty = self.inst_param_type(
                    &ParamType::Struct(struct_ty.clone()),
                    &filtered_param_to_arg_map,
                    param_obj_type,
                )?;
                match inst_ty {
                    ParamType::Struct(s) => params_def_with_set.push(
                        ParamGroupWithSet::new_struct(param_def_with_set.params.clone(), s),
                    ),
                    _ => unreachable!(),
                }
            } else {
                params_def_with_set.push(ParamGroupWithSet::new(
                    param_def_with_set.params.clone(),
                    self.inst_obj(
                        param_def_with_set.set_obj().unwrap(),
                        &filtered_param_to_arg_map,
                        param_obj_type,
                    )?,
                ));
            }
        }
        let mut dom_facts = Vec::with_capacity(fn_set_with_params.body.dom_facts.len());
        for dom_fact in fn_set_with_params.body.dom_facts.iter() {
            dom_facts.push(self.inst_or_and_chain_atomic_fact(
                dom_fact,
                &filtered_param_to_arg_map,
                param_obj_type,
                None,
            )?);
        }
        Ok(FnSet::new(
            params_def_with_set,
            dom_facts,
            self.inst_obj(
                &fn_set_with_params.body.ret_set,
                &filtered_param_to_arg_map,
                param_obj_type,
            )?,
        )?
        .into())
    }

    pub fn inst_anonymous_fn_with_params(
        &self,
        af: &AnonymousFn,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let param_names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
        let filtered_param_to_arg_map =
            remove_param_names_from_param_to_arg_map(param_to_arg_map, &param_names);
        let mut params_def_with_set = Vec::with_capacity(af.body.params_def_with_set.len());
        for param_def_with_set in af.body.params_def_with_set.iter() {
            if let Some(struct_ty) = param_def_with_set.struct_ty() {
                let inst_ty = self.inst_param_type(
                    &ParamType::Struct(struct_ty.clone()),
                    &filtered_param_to_arg_map,
                    param_obj_type,
                )?;
                match inst_ty {
                    ParamType::Struct(s) => params_def_with_set.push(
                        ParamGroupWithSet::new_struct(param_def_with_set.params.clone(), s),
                    ),
                    _ => unreachable!(),
                }
            } else {
                params_def_with_set.push(ParamGroupWithSet::new(
                    param_def_with_set.params.clone(),
                    self.inst_obj(
                        param_def_with_set.set_obj().unwrap(),
                        &filtered_param_to_arg_map,
                        param_obj_type,
                    )?,
                ));
            }
        }
        let mut dom_facts = Vec::with_capacity(af.body.dom_facts.len());
        for dom_fact in af.body.dom_facts.iter() {
            dom_facts.push(self.inst_or_and_chain_atomic_fact(
                dom_fact,
                &filtered_param_to_arg_map,
                param_obj_type,
                None,
            )?);
        }
        Ok(AnonymousFn::new(
            params_def_with_set,
            dom_facts,
            self.inst_obj(
                af.body.ret_set.as_ref(),
                &filtered_param_to_arg_map,
                param_obj_type,
            )?,
            self.inst_obj(
                af.equal_to.as_ref(),
                &filtered_param_to_arg_map,
                param_obj_type,
            )?,
        )?
        .into())
    }

    pub fn inst_cart(
        &self,
        cart: &Cart,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let mut args = Vec::with_capacity(cart.args.len());
        for arg in cart.args.iter() {
            args.push(self.inst_obj(arg, param_to_arg_map, param_obj_type)?);
        }
        Ok(Cart::new(args).into())
    }

    pub fn inst_cart_dim(
        &self,
        cart_dim: &CartDim,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(CartDim::new(self.inst_obj(&cart_dim.set, param_to_arg_map, param_obj_type)?).into())
    }

    pub fn inst_proj(
        &self,
        proj: &Proj,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Proj::new(
            self.inst_obj(&proj.set, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&proj.dim, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_tuple_dim(
        &self,
        tuple_dim: &TupleDim,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(TupleDim::new(self.inst_obj(&tuple_dim.arg, param_to_arg_map, param_obj_type)?).into())
    }

    pub fn inst_tuple(
        &self,
        tuple: &Tuple,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let mut elements = Vec::with_capacity(tuple.args.len());
        for element in tuple.args.iter() {
            elements.push(self.inst_obj(element, param_to_arg_map, param_obj_type)?);
        }
        Ok(Tuple::new(elements).into())
    }

    pub fn inst_count(
        &self,
        count: &Count,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Count::new(self.inst_obj(&count.set, param_to_arg_map, param_obj_type)?).into())
    }

    pub fn inst_sum(
        &self,
        sum: &Sum,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Sum::new(
            self.inst_obj(&sum.start, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&sum.end, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&sum.func, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_product(
        &self,
        product: &Product,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Product::new(
            self.inst_obj(&product.start, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&product.end, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&product.func, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_range(
        &self,
        range: &Range,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Range::new(
            self.inst_obj(&range.start, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&range.end, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_closed_range(
        &self,
        closed_range: &ClosedRange,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(ClosedRange::new(
            self.inst_obj(&closed_range.start, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&closed_range.end, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_finite_seq_set(
        &self,
        fs: &FiniteSeqSet,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(FiniteSeqSet::new(
            self.inst_obj(&fs.set, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&fs.n, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_seq_set(
        &self,
        ss: &SeqSet,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(SeqSet::new(self.inst_obj(&ss.set, param_to_arg_map, param_obj_type)?).into())
    }

    pub fn inst_finite_seq_list_obj(
        &self,
        v: &FiniteSeqListObj,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let mut objs = Vec::with_capacity(v.objs.len());
        for o in v.objs.iter() {
            objs.push(self.inst_obj(o, param_to_arg_map, param_obj_type)?);
        }
        Ok(FiniteSeqListObj::new(objs).into())
    }

    pub fn inst_matrix_set(
        &self,
        ms: &MatrixSet,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(MatrixSet::new(
            self.inst_obj(&ms.set, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&ms.row_len, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&ms.col_len, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_matrix_list_obj(
        &self,
        m: &MatrixListObj,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let mut rows: Vec<Vec<Obj>> = Vec::with_capacity(m.rows.len());
        for row in m.rows.iter() {
            let mut inst_row = Vec::with_capacity(row.len());
            for o in row.iter() {
                inst_row.push(self.inst_obj(o, param_to_arg_map, param_obj_type)?);
            }
            rows.push(inst_row);
        }
        Ok(MatrixListObj::new(rows).into())
    }

    pub fn inst_choose(
        &self,
        choose: &Choose,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Choose::new(self.inst_obj(&choose.set, param_to_arg_map, param_obj_type)?).into())
    }

    pub fn inst_obj_at_index(
        &self,
        obj_at_index: &ObjAtIndex,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(ObjAtIndex::new(
            self.inst_obj(&obj_at_index.obj, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&obj_at_index.index, param_to_arg_map, param_obj_type)?,
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
        param_obj_type: ParamObjType,
    ) -> Result<ParamType, RuntimeError> {
        match param_type {
            ParamType::Set(_) => Ok(param_type.clone()),
            ParamType::FiniteSet(_) => Ok(param_type.clone()),
            ParamType::NonemptySet(_) => Ok(param_type.clone()),
            ParamType::Obj(obj) => Ok(ParamType::Obj(self.inst_obj(
                obj,
                param_to_arg_map,
                param_obj_type,
            )?)),
            ParamType::Struct(struct_ty) => {
                let mut args = Vec::with_capacity(struct_ty.args.len());
                for arg in struct_ty.args.iter() {
                    args.push(self.inst_obj(arg, param_to_arg_map, param_obj_type)?);
                }
                Ok(ParamType::Struct(StructAsParamType::new(
                    struct_ty.name.clone(),
                    args,
                )))
            }
        }
    }

    fn obj_name_for_instantiated_field_access_left(obj: &Obj) -> Option<String> {
        match obj {
            Obj::Atom(AtomObj::Identifier(identifier)) => Some(identifier.name.clone()),
            Obj::Atom(AtomObj::Forall(p)) => Some(p.name.clone()),
            Obj::Atom(AtomObj::Def(p)) => Some(p.name.clone()),
            Obj::Atom(AtomObj::Exist(p)) => Some(p.name.clone()),
            Obj::Atom(AtomObj::SetBuilder(p)) => Some(p.name.clone()),
            Obj::Atom(AtomObj::FnSet(p)) => Some(p.name.clone()),
            Obj::Atom(AtomObj::Induc(p)) => Some(p.name.clone()),
            Obj::Atom(AtomObj::DefAlgo(p)) => Some(p.name.clone()),
            Obj::Atom(AtomObj::DefStructField(p)) => Some(p.name.clone()),
            _ => None,
        }
    }

    pub fn inst_param_def_with_set_one_by_one(
        &self,
        param_defs: &Vec<ParamGroupWithSet>,
        args: &Vec<Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Vec<Obj>, RuntimeError> {
        let total_param_count = ParamGroupWithSet::number_of_params(param_defs);
        if total_param_count != args.len() {
            return Err(
                InstantiateRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
                    "argument count mismatch: expected {} parameter(s), got {} argument(s)",
                    total_param_count,
                    args.len()
                )))
                .into(),
            );
        }

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::with_capacity(total_param_count);
        let mut arg_index: usize = 0;
        let mut instantiated_param_sets: Vec<Obj> = Vec::with_capacity(param_defs.len());
        for param_def in param_defs.iter() {
            if param_def.struct_ty().is_some() {
                return Err(RuntimeError::from(InstantiateRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(
                        "struct fn parameter type cannot be instantiated as a set".to_string(),
                    ),
                )));
            }
            let instantiated_param_set = if arg_index != 0 {
                self.inst_obj(
                    param_def.set_obj().unwrap(),
                    &param_to_arg_map,
                    param_obj_type,
                )?
            } else {
                param_def.set_obj().unwrap().clone()
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
        param_obj_type: ParamObjType,
    ) -> Result<Vec<ParamType>, RuntimeError> {
        let total_param_count = param_defs.number_of_params();
        if total_param_count != args.len() {
            return Err(
                InstantiateRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
                    "argument count mismatch: expected {} parameter(s), got {} argument(s)",
                    total_param_count,
                    args.len()
                )))
                .into(),
            );
        }

        let mut param_arg_map: HashMap<String, Obj> = HashMap::with_capacity(total_param_count);
        let mut arg_index: usize = 0;
        let mut new_types: Vec<ParamType> = Vec::with_capacity(param_defs.groups.len());
        for param_def in param_defs.groups.iter() {
            let new_type = if arg_index != 0 {
                self.inst_param_type(&param_def.param_type, &param_arg_map, param_obj_type)?
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
