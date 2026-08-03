use crate::prelude::*;
use std::collections::HashMap;

fn remove_param_bindings_from_param_to_arg_map(
    param_to_arg_map: &HashMap<String, Obj>,
    param_bindings: &[SymbolBinding],
) -> HashMap<String, Obj> {
    let mut filtered_param_to_arg_map = HashMap::new();
    for (key, arg) in param_to_arg_map.iter() {
        if !param_bindings
            .iter()
            .any(|binding| key == binding.name() || key == &binding.substitution_key())
        {
            filtered_param_to_arg_map.insert(key.clone(), arg.clone());
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
        if let Obj::Atom(atom) = obj {
            if let Some(symbol) = atom.symbol_ref() {
                if let Some(replacement) = param_to_arg_map.get(&symbol.substitution_key()) {
                    return Ok(replacement.clone());
                }
                if param_obj_type == ParamObjType::FnSet {
                    if let Some(replacement) = param_to_arg_map.get(symbol.display_name()) {
                        return Ok(replacement.clone());
                    }
                }
            }
            match param_obj_type {
                ParamObjType::AlphaRename => {
                    return Ok(
                        alpha_renamed_atom(atom, param_to_arg_map).unwrap_or_else(|| obj.clone())
                    );
                }
                ParamObjType::BinderRetag(source) => {
                    return Ok(binder_retagged_atom(atom, param_to_arg_map, source)
                        .unwrap_or_else(|| obj.clone()));
                }
                _ => {}
            }
            if atom.symbol_ref().is_some() {
                return Ok(obj.clone());
            }
        }
        match obj {
            Obj::Atom(AtomObj::Identifier(inner)) => {
                if param_obj_type == ParamObjType::Identifier {
                    self.inst_identifier(inner, param_to_arg_map)
                } else {
                    Ok(inner.clone().into())
                }
            }
            Obj::Atom(AtomObj::IdentifierWithMod(inner)) => {
                if param_obj_type == ParamObjType::Identifier {
                    self.inst_identifier_with_mod(inner, param_to_arg_map)
                } else {
                    Ok(inner.clone().into())
                }
            }
            Obj::FnObj(inner) => self.inst_fn_obj(inner, param_to_arg_map, param_obj_type),
            Obj::Number(inner) => self.inst_number(inner, param_to_arg_map, param_obj_type),
            Obj::ImaginaryUnit(inner) => Ok(inner.clone().into()),
            Obj::EulerNumber(inner) => Ok(inner.clone().into()),
            Obj::Pi(inner) => Ok(inner.clone().into()),
            Obj::Add(inner) => self.inst_add(inner, param_to_arg_map, param_obj_type),
            Obj::Sub(inner) => self.inst_sub(inner, param_to_arg_map, param_obj_type),
            Obj::Mul(inner) => self.inst_mul(inner, param_to_arg_map, param_obj_type),
            Obj::Div(inner) => self.inst_div(inner, param_to_arg_map, param_obj_type),
            Obj::Mod(inner) => self.inst_mod(inner, param_to_arg_map, param_obj_type),
            Obj::Gcd(inner) => Ok(Gcd::new(
                self.inst_obj(&inner.left, param_to_arg_map, param_obj_type)?,
                self.inst_obj(&inner.right, param_to_arg_map, param_obj_type)?,
            )
            .into()),
            Obj::Lcm(inner) => Ok(Lcm::new(
                self.inst_obj(&inner.left, param_to_arg_map, param_obj_type)?,
                self.inst_obj(&inner.right, param_to_arg_map, param_obj_type)?,
            )
            .into()),
            Obj::Floor(inner) => {
                Ok(Floor::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?).into())
            }
            Obj::Ceil(inner) => {
                Ok(Ceil::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?).into())
            }
            Obj::Min(inner) => Ok(Min::new(
                self.inst_obj(&inner.left, param_to_arg_map, param_obj_type)?,
                self.inst_obj(&inner.right, param_to_arg_map, param_obj_type)?,
            )
            .into()),
            Obj::Max(inner) => Ok(Max::new(
                self.inst_obj(&inner.left, param_to_arg_map, param_obj_type)?,
                self.inst_obj(&inner.right, param_to_arg_map, param_obj_type)?,
            )
            .into()),
            Obj::Exp(inner) => {
                Ok(Exp::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?).into())
            }
            Obj::Ln(inner) => {
                Ok(Ln::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?).into())
            }
            Obj::Sign(inner) => {
                Ok(Sign::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?).into())
            }
            Obj::Factorial(inner) => {
                Ok(
                    Factorial::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?)
                        .into(),
                )
            }
            Obj::Pow(inner) => self.inst_pow(inner, param_to_arg_map, param_obj_type),
            Obj::MatrixAdd(inner) => self.inst_matrix_add(inner, param_to_arg_map, param_obj_type),
            Obj::MatrixSub(inner) => self.inst_matrix_sub(inner, param_to_arg_map, param_obj_type),
            Obj::MatrixMul(inner) => self.inst_matrix_mul(inner, param_to_arg_map, param_obj_type),
            Obj::MatrixScalarMul(inner) => {
                self.inst_matrix_scalar_mul(inner, param_to_arg_map, param_obj_type)
            }
            Obj::MatrixPow(inner) => self.inst_matrix_pow(inner, param_to_arg_map, param_obj_type),
            Obj::Abs(inner) => self.inst_abs(inner, param_to_arg_map, param_obj_type),
            Obj::Sin(inner) => {
                Ok(Sin::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?).into())
            }
            Obj::Cos(inner) => {
                Ok(Cos::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?).into())
            }
            Obj::Tan(inner) => {
                Ok(Tan::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?).into())
            }
            Obj::Cot(inner) => {
                Ok(Cot::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?).into())
            }
            Obj::RealPart(inner) => {
                Ok(
                    RealPart::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?)
                        .into(),
                )
            }
            Obj::ImaginaryPart(inner) => Ok(ImaginaryPart::new(self.inst_obj(
                &inner.arg,
                param_to_arg_map,
                param_obj_type,
            )?)
            .into()),
            Obj::ComplexAbs(inner) => {
                Ok(
                    ComplexAbs::new(self.inst_obj(&inner.arg, param_to_arg_map, param_obj_type)?)
                        .into(),
                )
            }
            Obj::Sqrt(inner) => self.inst_sqrt(inner, param_to_arg_map, param_obj_type),
            Obj::Log(inner) => self.inst_log(inner, param_to_arg_map, param_obj_type),
            Obj::Union(inner) => self.inst_union(inner, param_to_arg_map, param_obj_type),
            Obj::Intersect(inner) => self.inst_intersect(inner, param_to_arg_map, param_obj_type),
            Obj::SetMinus(inner) => self.inst_set_minus(inner, param_to_arg_map, param_obj_type),
            Obj::SetDiff(inner) => self.inst_set_diff(inner, param_to_arg_map, param_obj_type),
            Obj::BigUnion(inner) => self.inst_big_union(inner, param_to_arg_map, param_obj_type),
            Obj::BigIntersect(inner) => {
                self.inst_big_intersect(inner, param_to_arg_map, param_obj_type)
            }
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
            Obj::FiniteSetSize(inner) => {
                self.inst_finite_set_size(inner, param_to_arg_map, param_obj_type)
            }
            Obj::FiniteSetMax(inner) => {
                self.inst_finite_set_max(inner, param_to_arg_map, param_obj_type)
            }
            Obj::FiniteSetMin(inner) => {
                self.inst_finite_set_min(inner, param_to_arg_map, param_obj_type)
            }
            Obj::FnRange(inner) => self.inst_fn_range(inner, param_to_arg_map, param_obj_type),
            Obj::Replacement(inner) => {
                self.inst_replacement(inner, param_to_arg_map, param_obj_type)
            }
            Obj::Sum(inner) => self.inst_sum(inner, param_to_arg_map, param_obj_type),
            Obj::SumOfFiniteSet(inner) => {
                self.inst_finite_set_sum(inner, param_to_arg_map, param_obj_type)
            }
            Obj::Product(inner) => self.inst_product(inner, param_to_arg_map, param_obj_type),
            Obj::ProductOfFiniteSet(inner) => {
                self.inst_finite_set_product(inner, param_to_arg_map, param_obj_type)
            }
            Obj::Range(inner) => self.inst_range(inner, param_to_arg_map, param_obj_type),
            Obj::ClosedRange(inner) => {
                self.inst_closed_range(inner, param_to_arg_map, param_obj_type)
            }
            Obj::IntervalObj(inner) => {
                self.inst_interval_obj(inner, param_to_arg_map, param_obj_type)
            }
            Obj::OneSideInfinityIntervalObj(inner) => {
                self.inst_one_side_infinity_interval_obj(inner, param_to_arg_map, param_obj_type)
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
            Obj::GeneralCart(inner) => {
                self.inst_general_cart(inner, param_to_arg_map, param_obj_type)
            }
            Obj::ObjAtIndex(inner) => {
                self.inst_obj_at_index(inner, param_to_arg_map, param_obj_type)
            }
            Obj::StructObj(struct_obj) => {
                let mut params = Vec::with_capacity(struct_obj.params.len());
                for p in struct_obj.params.iter() {
                    params.push(self.inst_obj(p, param_to_arg_map, param_obj_type)?);
                }
                Ok(StructObj::new(struct_obj.name.clone(), params).into())
            }
            Obj::ObjAsStructInstanceWithFieldAccess(field_access) => {
                let mut params = Vec::with_capacity(field_access.struct_obj.params.len());
                for p in field_access.struct_obj.params.iter() {
                    params.push(self.inst_obj(p, param_to_arg_map, param_obj_type)?);
                }
                let struct_obj = StructObj::new(field_access.struct_obj.name.clone(), params);
                let obj = self.inst_obj(&field_access.obj, param_to_arg_map, param_obj_type)?;
                Ok(ObjAsStructInstanceWithFieldAccess::new(
                    struct_obj,
                    obj,
                    field_access.field_name.clone(),
                )
                .into())
            }
            Obj::InstantiatedTemplateObj(template_obj) => {
                let mut args = Vec::with_capacity(template_obj.args.len());
                for arg in template_obj.args.iter() {
                    args.push(self.inst_obj(arg, param_to_arg_map, param_obj_type)?);
                }
                let surface_name = format!(
                    "{}{}{}{}{}",
                    TEMPLATE_INSTANCE_PREFIX,
                    template_obj.template_name,
                    LESS,
                    vec_to_string_join_by_comma(&args),
                    GREATER
                );
                let binding = self.intern_template_instance_symbol_binding(&surface_name)?;
                Ok(InstantiatedTemplateObj::new(
                    template_obj.template_name.clone(),
                    args,
                    binding.as_ref(),
                )
                .into())
            }
            Obj::Atom(AtomObj::Forall(p)) => {
                if param_obj_type == ParamObjType::Forall
                    || param_obj_type == ParamObjType::TheoremInstantiation
                {
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
                if param_obj_type == ParamObjType::Induc {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::Atom(AtomObj::DefAlgo(p)) => {
                if param_obj_type == ParamObjType::DefAlgo {
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
            Obj::Atom(AtomObj::TupleIndex(p)) => {
                if param_obj_type == ParamObjType::TupleIndex {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
            }
            Obj::Atom(AtomObj::CartIndex(p)) => {
                if param_obj_type == ParamObjType::CartIndex {
                    if let Some(obj) = param_to_arg_map.get(&p.name) {
                        return Ok(obj.clone());
                    }
                }
                Ok(p.clone().into())
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
        let key = identifier_with_mod.to_string();
        Ok(match param_to_arg_map.get(&key) {
            Some(obj) => obj.clone(),
            None => identifier_with_mod.clone().into(),
        })
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

        let head_obj: Obj = (*fn_obj.head.clone()).into();
        let inst_head = self.inst_obj(&head_obj, param_to_arg_map, param_obj_type)?;

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
            Obj::Atom(AtomObj::TupleIndex(p)) => p.clone().into(),
            Obj::Atom(AtomObj::CartIndex(p)) => p.clone().into(),
            Obj::Atom(AtomObj::DefStructField(x)) => FnObjHead::DefStructField(x.clone()),
            Obj::AnonymousFn(a) => FnObjHead::AnonymousFnLiteral(Box::new(a)),
            Obj::InstantiatedTemplateObj(t) => FnObjHead::InstantiatedTemplateObj(t),
            Obj::FnObj(x) => {
                let merged_body_original = merged_body.clone();
                merged_body = vec![];
                merged_body.extend(x.body);
                merged_body.extend(merged_body_original);
                *x.head.clone()
            }
            Obj::FiniteSeqListObj(list) => FnObjHead::FiniteSeqListObj(list),
            Obj::ObjAtIndex(x) => FnObjHead::ObjAtIndex(x),
            Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                FnObjHead::ObjAsStructInstanceWithFieldAccess(x)
            }
            Obj::MatrixAdd(_)
            | Obj::MatrixSub(_)
            | Obj::MatrixMul(_)
            | Obj::MatrixScalarMul(_)
            | Obj::MatrixPow(_) => FnObjHead::MatrixOperator(Box::new(inst_head)),
            _ => {
                return Err(InstantiateRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                    format!(
                        "instantiate fn object: after substitution, head must be a callable head, got {}",
                        inst_head
                    ),
                ))
                .into());
            }
        };

        if param_obj_type == ParamObjType::TheoremInstantiation {
            if let FnObjHead::AnonymousFnLiteral(anonymous_fn) = &final_head {
                let args: Vec<Obj> = merged_body
                    .iter()
                    .flat_map(|group| group.iter().map(|arg| (**arg).clone()))
                    .collect();
                let param_defs = &anonymous_fn.body.params_def_with_set;
                if args.len() == ParamGroupWithSet::number_of_params(param_defs) {
                    let param_to_arg_map =
                        ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(
                            param_defs, &args,
                        );
                    // A theorem application substitutes a function-valued parameter into a
                    // theorem fact. Normalize a fully applied anonymous argument here so the
                    // stored fact has the same beta-normal form as handwritten code.
                    return self.inst_obj(
                        anonymous_fn.equal_to.as_ref(),
                        &param_to_arg_map,
                        ParamObjType::FnSet,
                    );
                }
            }
        }

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

    pub fn inst_sqrt(
        &self,
        sqrt: &Sqrt,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Sqrt::new(self.inst_obj(&sqrt.arg, param_to_arg_map, param_obj_type)?).into())
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

    pub fn inst_big_union(
        &self,
        big_union: &BigUnion,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(BigUnion::new(self.inst_obj(&big_union.left, param_to_arg_map, param_obj_type)?).into())
    }

    pub fn inst_big_intersect(
        &self,
        big_intersect: &BigIntersect,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(BigIntersect::new(self.inst_obj(
            &big_intersect.left,
            param_to_arg_map,
            param_obj_type,
        )?)
        .into())
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
        let target: Obj = set_builder.clone().into();
        let rename_map = self.capture_avoiding_obj_binder_rename_map(
            ParamObjType::SetBuilder,
            std::slice::from_ref(&set_builder.param_binding),
            &target,
            param_to_arg_map,
        );
        let renamed_set_builder = self.alpha_rename_set_builder(set_builder, &rename_map)?;
        let instantiated = self.inst_set_builder_without_capture_preparation(
            &renamed_set_builder,
            param_to_arg_map,
            param_obj_type,
        )?;
        let restore_map =
            safe_obj_binder_restore_map(&instantiated, &rename_map, ParamObjType::SetBuilder);
        let Obj::SetBuilder(instantiated) = instantiated else {
            unreachable!("set-builder instantiation must return a set builder");
        };
        let restored = self.alpha_rename_set_builder(&instantiated, &restore_map)?;
        let visible_rename_map = self.visible_binding_conflict_rename_map(
            std::slice::from_ref(&restored.param_binding),
            ParamObjType::SetBuilder,
        )?;
        Ok(self
            .alpha_rename_set_builder(&restored, &visible_rename_map)?
            .into())
    }

    fn inst_set_builder_without_capture_preparation(
        &self,
        set_builder: &SetBuilder,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let filtered_param_to_arg_map = if param_obj_type == ParamObjType::SetBuilder {
            remove_param_bindings_from_param_to_arg_map(
                param_to_arg_map,
                std::slice::from_ref(&set_builder.param_binding),
            )
        } else {
            param_to_arg_map.clone()
        };
        let mut facts = Vec::with_capacity(set_builder.facts.len());
        for fact in set_builder.facts.iter() {
            facts.push(self.inst_exist_body_fact(
                fact,
                &filtered_param_to_arg_map,
                param_obj_type,
                None,
            )?);
        }
        Ok(SetBuilder::new(
            set_builder.param_binding.clone(),
            self.inst_obj(
                &set_builder.param_set,
                &filtered_param_to_arg_map,
                param_obj_type,
            )?,
            facts,
        )?
        .into())
    }

    pub fn inst_general_cart(
        &self,
        general_cart: &GeneralCart,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(GeneralCart::new(
            self.inst_obj(&general_cart.index_set, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&general_cart.family_set, param_to_arg_map, param_obj_type)?,
            self.inst_obj(&general_cart.family_fn, param_to_arg_map, param_obj_type)?,
        )
        .into())
    }

    pub fn inst_fn_set_with_params(
        &self,
        fn_set_with_params: &FnSet,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let param_bindings = fn_set_with_params
            .body
            .params_def_with_set
            .iter()
            .flat_map(|group| group.params.iter().cloned())
            .collect::<Vec<_>>();
        let target: Obj = fn_set_with_params.clone().into();
        let rename_map = self.capture_avoiding_obj_binder_rename_map(
            ParamObjType::FnSet,
            &param_bindings,
            &target,
            param_to_arg_map,
        );
        let renamed_fn_set = self.alpha_rename_fn_set(fn_set_with_params, &rename_map)?;
        let instantiated = self.inst_fn_set_without_capture_preparation(
            &renamed_fn_set,
            param_to_arg_map,
            param_obj_type,
        )?;
        let restore_map =
            safe_obj_binder_restore_map(&instantiated, &rename_map, ParamObjType::FnSet);
        let Obj::FnSet(instantiated) = instantiated else {
            unreachable!("function-set instantiation must return a function set");
        };
        let restored = self.alpha_rename_fn_set(&instantiated, &restore_map)?;
        let restored_bindings = restored.body.params_def_with_set.collect_param_bindings();
        let visible_rename_map =
            self.visible_binding_conflict_rename_map(&restored_bindings, ParamObjType::FnSet)?;
        Ok(self
            .alpha_rename_fn_set(&restored, &visible_rename_map)?
            .into())
    }

    fn inst_fn_set_without_capture_preparation(
        &self,
        fn_set_with_params: &FnSet,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let param_bindings = fn_set_with_params
            .body
            .params_def_with_set
            .collect_param_bindings();
        let filtered_param_to_arg_map = if param_obj_type == ParamObjType::FnSet {
            remove_param_bindings_from_param_to_arg_map(param_to_arg_map, &param_bindings)
        } else {
            param_to_arg_map.clone()
        };
        let mut params_def_with_set =
            Vec::with_capacity(fn_set_with_params.body.params_def_with_set.len());
        for param_def_with_set in fn_set_with_params.body.params_def_with_set.iter() {
            params_def_with_set.push(ParamGroupWithSet::new(
                param_def_with_set.params.clone(),
                self.inst_obj(
                    param_def_with_set.set_obj(),
                    &filtered_param_to_arg_map,
                    param_obj_type,
                )?,
            ));
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
        let param_bindings = af
            .body
            .params_def_with_set
            .iter()
            .flat_map(|group| group.params.iter().cloned())
            .collect::<Vec<_>>();
        let target: Obj = af.clone().into();
        let rename_map = self.capture_avoiding_obj_binder_rename_map(
            ParamObjType::FnSet,
            &param_bindings,
            &target,
            param_to_arg_map,
        );
        let renamed_anonymous_fn = self.alpha_rename_anonymous_fn(af, &rename_map)?;
        let instantiated = self.inst_anonymous_fn_without_capture_preparation(
            &renamed_anonymous_fn,
            param_to_arg_map,
            param_obj_type,
        )?;
        let restore_map =
            safe_obj_binder_restore_map(&instantiated, &rename_map, ParamObjType::FnSet);
        let Obj::AnonymousFn(instantiated) = instantiated else {
            unreachable!("anonymous-function instantiation must return an anonymous function");
        };
        let restored = self.alpha_rename_anonymous_fn(&instantiated, &restore_map)?;
        let restored_bindings = restored.body.params_def_with_set.collect_param_bindings();
        let visible_rename_map =
            self.visible_binding_conflict_rename_map(&restored_bindings, ParamObjType::FnSet)?;
        Ok(self
            .alpha_rename_anonymous_fn(&restored, &visible_rename_map)?
            .into())
    }

    fn inst_anonymous_fn_without_capture_preparation(
        &self,
        af: &AnonymousFn,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let param_bindings = af.body.params_def_with_set.collect_param_bindings();
        let filtered_param_to_arg_map = if param_obj_type == ParamObjType::FnSet {
            remove_param_bindings_from_param_to_arg_map(param_to_arg_map, &param_bindings)
        } else {
            param_to_arg_map.clone()
        };
        let mut params_def_with_set = Vec::with_capacity(af.body.params_def_with_set.len());
        for param_def_with_set in af.body.params_def_with_set.iter() {
            params_def_with_set.push(ParamGroupWithSet::new(
                param_def_with_set.params.clone(),
                self.inst_obj(
                    param_def_with_set.set_obj(),
                    &filtered_param_to_arg_map,
                    param_obj_type,
                )?,
            ));
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

    fn capture_avoiding_obj_binder_rename_map(
        &self,
        binder_kind: ParamObjType,
        binder_bindings: &[SymbolBinding],
        target: &Obj,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> HashMap<String, Obj> {
        let mut replacement_names = std::collections::HashSet::new();
        for replacement in param_to_arg_map.values() {
            replacement_names.extend(replacement.collect_param_obj_names(binder_kind));
        }

        let mut reserved_names = replacement_names.clone();
        reserved_names.extend(target.collect_param_obj_names(binder_kind));
        let mut rename_map = HashMap::new();
        for binding in binder_bindings {
            if !replacement_names.contains(binding.name()) {
                continue;
            }
            let fresh_name = self.generate_one_unused_name_with_reserved(&reserved_names);
            reserved_names.insert(fresh_name.clone());
            let fresh_binding = self
                .allocate_local_symbol_binding(fresh_name)
                .expect("internal binder identity counter exhausted");
            insert_symbol_substitution(
                &mut rename_map,
                binding,
                obj_for_bound_param_in_scope(&fresh_binding, binder_kind),
            );
        }
        rename_map
    }

    pub(crate) fn alpha_rename_set_builder(
        &self,
        set_builder: &SetBuilder,
        rename_map: &HashMap<String, Obj>,
    ) -> Result<SetBuilder, RuntimeError> {
        if rename_map.is_empty() {
            return Ok(set_builder.clone());
        }
        let mut facts = Vec::with_capacity(set_builder.facts.len());
        for fact in set_builder.facts.iter() {
            facts.push(self.inst_exist_body_fact(
                fact,
                rename_map,
                ParamObjType::AlphaRename,
                None,
            )?);
        }
        SetBuilder::new(
            renamed_bound_param_binding(
                &set_builder.param_binding,
                rename_map,
                ParamObjType::SetBuilder,
            ),
            self.inst_obj(
                set_builder.param_set.as_ref(),
                rename_map,
                ParamObjType::AlphaRename,
            )?,
            facts,
        )
    }

    pub(crate) fn alpha_rename_fn_set(
        &self,
        fn_set: &FnSet,
        rename_map: &HashMap<String, Obj>,
    ) -> Result<FnSet, RuntimeError> {
        if rename_map.is_empty() {
            return Ok(fn_set.clone());
        }
        let body = self.alpha_rename_fn_set_body(&fn_set.body, rename_map)?;
        FnSet::from_body(body)
    }

    pub(crate) fn alpha_rename_anonymous_fn(
        &self,
        anonymous_fn: &AnonymousFn,
        rename_map: &HashMap<String, Obj>,
    ) -> Result<AnonymousFn, RuntimeError> {
        if rename_map.is_empty() {
            return Ok(anonymous_fn.clone());
        }
        let body = self.alpha_rename_fn_set_body(&anonymous_fn.body, rename_map)?;
        AnonymousFn::new(
            body.params_def_with_set,
            body.dom_facts,
            *body.ret_set,
            self.inst_obj(
                anonymous_fn.equal_to.as_ref(),
                rename_map,
                ParamObjType::AlphaRename,
            )?,
        )
    }

    pub(crate) fn visible_binding_conflict_rename_map(
        &self,
        bindings: &[SymbolBinding],
        target_kind: ParamObjType,
    ) -> Result<HashMap<String, Obj>, RuntimeError> {
        let mut rename_map = HashMap::new();
        for binding in bindings {
            let Some(visible) = self.visible_symbol_definition(binding.name()) else {
                continue;
            };
            if visible.binding().id() == binding.id() {
                continue;
            }
            let fresh = self.allocate_internal_symbol_binding()?;
            insert_symbol_substitution(
                &mut rename_map,
                binding,
                obj_for_bound_param_in_scope(&fresh, target_kind),
            );
        }
        Ok(rename_map)
    }

    pub(crate) fn alpha_rename_fn_set_body(
        &self,
        body: &FnSetBody,
        rename_map: &HashMap<String, Obj>,
    ) -> Result<FnSetBody, RuntimeError> {
        let mut params_def_with_set = Vec::with_capacity(body.params_def_with_set.len());
        let mut active_rename_map = HashMap::new();
        for group in body.params_def_with_set.iter() {
            let param_set = self.inst_obj(
                group.set_obj(),
                &active_rename_map,
                ParamObjType::AlphaRename,
            )?;
            let params = group
                .params
                .iter()
                .map(|binding| {
                    renamed_bound_param_binding(binding, rename_map, ParamObjType::FnSet)
                })
                .collect::<Vec<_>>();
            params_def_with_set.push(ParamGroupWithSet::new(params, param_set));
            for binding in group.params.iter() {
                if let Some(replacement) = rename_map.get(&binding.substitution_key()) {
                    insert_symbol_substitution(
                        &mut active_rename_map,
                        binding,
                        replacement.clone(),
                    );
                }
            }
        }
        let mut dom_facts = Vec::with_capacity(body.dom_facts.len());
        for fact in body.dom_facts.iter() {
            dom_facts.push(self.inst_or_and_chain_atomic_fact(
                fact,
                rename_map,
                ParamObjType::AlphaRename,
                None,
            )?);
        }
        Ok(FnSetBody::new(
            params_def_with_set,
            dom_facts,
            self.inst_obj(body.ret_set.as_ref(), rename_map, ParamObjType::AlphaRename)?,
        ))
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

    pub fn inst_finite_set_size(
        &self,
        finite_set_size: &FiniteSetSize,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(FiniteSetSize::new(self.inst_obj(
            &finite_set_size.set,
            param_to_arg_map,
            param_obj_type,
        )?)
        .into())
    }

    pub fn inst_finite_set_max(
        &self,
        finite_set_max: &FiniteSetMax,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(FiniteSetMax::new(self.inst_obj(
            &finite_set_max.set,
            param_to_arg_map,
            param_obj_type,
        )?)
        .into())
    }

    pub fn inst_finite_set_min(
        &self,
        finite_set_min: &FiniteSetMin,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(FiniteSetMin::new(self.inst_obj(
            &finite_set_min.set,
            param_to_arg_map,
            param_obj_type,
        )?)
        .into())
    }

    pub fn inst_fn_range(
        &self,
        fn_range: &FnRange,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(
            FnRange::new(self.inst_obj(&fn_range.function, param_to_arg_map, param_obj_type)?)
                .into(),
        )
    }

    pub fn inst_replacement(
        &self,
        replacement: &Replacement,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(Replacement::new(
            replacement.prop_name.clone(),
            self.inst_obj(&replacement.source_set, param_to_arg_map, param_obj_type)?,
        )
        .into())
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

    pub fn inst_finite_set_sum(
        &self,
        sum: &SumOfFiniteSet,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(SumOfFiniteSet::new(
            self.inst_obj(&sum.set, param_to_arg_map, param_obj_type)?,
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

    pub fn inst_finite_set_product(
        &self,
        product: &ProductOfFiniteSet,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        Ok(ProductOfFiniteSet::new(
            self.inst_obj(&product.set, param_to_arg_map, param_obj_type)?,
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

    pub fn inst_interval_obj(
        &self,
        interval: &IntervalObj,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let start = self.inst_obj(interval.start(), param_to_arg_map, param_obj_type)?;
        let end = self.inst_obj(interval.end(), param_to_arg_map, param_obj_type)?;
        Ok(match interval {
            IntervalObj::LeftOpenRightOpen(_) => {
                IntervalObj::new_left_open_right_open(start, end).into()
            }
            IntervalObj::LeftOpenRightClosed(_) => {
                IntervalObj::new_left_open_right_closed(start, end).into()
            }
            IntervalObj::LeftClosedRightOpen(_) => {
                IntervalObj::new_left_closed_right_open(start, end).into()
            }
            IntervalObj::LeftClosedRightClosed(_) => {
                IntervalObj::new_left_closed_right_closed(start, end).into()
            }
        })
    }

    pub fn inst_one_side_infinity_interval_obj(
        &self,
        interval: &OneSideInfinityIntervalObj,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let start = self.inst_obj(interval.start(), param_to_arg_map, param_obj_type)?;
        Ok(match interval {
            OneSideInfinityIntervalObj::LeftOpen(_) => {
                OneSideInfinityIntervalObj::new_left_open(start).into()
            }
            OneSideInfinityIntervalObj::LeftClosed(_) => {
                OneSideInfinityIntervalObj::new_left_closed(start).into()
            }
            OneSideInfinityIntervalObj::RightOpen(_) => {
                OneSideInfinityIntervalObj::new_right_open(start).into()
            }
            OneSideInfinityIntervalObj::RightClosed(_) => {
                OneSideInfinityIntervalObj::new_right_closed(start).into()
            }
        })
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

    pub fn inst_obj_at_index(
        &self,
        obj_at_index: &ObjAtIndex,
        param_to_arg_map: &HashMap<String, Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let instantiated_obj =
            self.inst_obj(&obj_at_index.obj, param_to_arg_map, param_obj_type)?;
        let instantiated_index =
            self.inst_obj(&obj_at_index.index, param_to_arg_map, param_obj_type)?;
        if let Obj::Tuple(tuple) = &instantiated_obj {
            if let Some(index) = instantiated_index.evaluate_to_normalized_decimal_number() {
                if let Ok(one_based) = index.normalized_value.parse::<usize>() {
                    if one_based >= 1 && one_based <= tuple.args.len() {
                        return Ok(tuple.args[one_based - 1].as_ref().clone());
                    }
                }
            }
        }
        Ok(ObjAtIndex::new(instantiated_obj, instantiated_index).into())
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
        }
    }

    pub fn inst_param_def_with_set_one_by_one(
        &self,
        param_defs: &ParamDefWithSet,
        args: &Vec<Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Vec<Obj>, RuntimeError> {
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

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::with_capacity(total_param_count);
        let mut arg_index: usize = 0;
        let mut instantiated_param_sets: Vec<Obj> = Vec::with_capacity(param_defs.groups.len());
        for (group_index, param_def) in param_defs.groups.iter().enumerate() {
            let instantiated_param_set =
                if !param_defs.param_set_cited_param_indices[group_index].is_empty() {
                    self.inst_obj(param_def.set_obj(), &param_to_arg_map, param_obj_type)?
                } else {
                    param_def.set_obj().clone()
                };
            instantiated_param_sets.push(instantiated_param_set);

            for binding in param_def.params.iter() {
                insert_symbol_substitution(&mut param_to_arg_map, binding, args[arg_index].clone());
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
        let mut new_types: Vec<ParamType> = Vec::with_capacity(total_param_count);
        for (group_index, param_def) in param_defs.groups.iter().enumerate() {
            let new_type = if !param_defs.param_type_cited_param_indices[group_index].is_empty() {
                self.inst_param_type(&param_def.param_type, &param_arg_map, param_obj_type)?
            } else {
                param_def.param_type.clone()
            };

            for binding in param_def.params.iter() {
                new_types.push(new_type.clone());
                insert_symbol_substitution(&mut param_arg_map, binding, args[arg_index].clone());
                arg_index += 1;
            }
        }

        Ok(new_types)
    }
}

fn safe_obj_binder_restore_map(
    instantiated: &Obj,
    rename_map: &HashMap<String, Obj>,
    binder_kind: ParamObjType,
) -> HashMap<String, Obj> {
    let remaining_names = instantiated.collect_param_obj_names(binder_kind);
    let mut restore_map = HashMap::new();
    for (source_key, fresh_obj) in rename_map {
        let Some(source_id) = SymbolId::from_substitution_key(source_key) else {
            continue;
        };
        let Obj::Atom(fresh_atom) = fresh_obj else {
            continue;
        };
        let Some(fresh_symbol) = fresh_atom.symbol_ref() else {
            continue;
        };
        let Some(original_name) = rename_map.iter().find_map(|(candidate, candidate_obj)| {
            if SymbolId::from_substitution_key(candidate).is_some() {
                return None;
            }
            let Obj::Atom(candidate_atom) = candidate_obj else {
                return None;
            };
            candidate_atom
                .symbol_ref()
                .is_some_and(|symbol| symbol.id() == fresh_symbol.id())
                .then_some(candidate.as_str())
        }) else {
            continue;
        };
        if remaining_names.contains(original_name) {
            continue;
        }
        let source_binding = SymbolBinding::new(
            source_id,
            original_name.to_string(),
            original_name.to_string(),
        );
        let fresh_binding = fresh_symbol.to_local_binding();
        insert_symbol_substitution(
            &mut restore_map,
            &fresh_binding,
            obj_for_bound_param_in_scope(&source_binding, binder_kind),
        );
    }
    restore_map
}

fn alpha_renamed_atom(atom: &AtomObj, rename_map: &HashMap<String, Obj>) -> Option<Obj> {
    if let Some(symbol) = atom.symbol_ref() {
        return rename_map.get(&symbol.substitution_key()).cloned();
    }
    let name = match atom {
        AtomObj::Identifier(_) | AtomObj::IdentifierWithMod(_) => return None,
        AtomObj::Forall(param) => &param.name,
        AtomObj::Def(param) => &param.name,
        AtomObj::Exist(param) => &param.name,
        AtomObj::SetBuilder(param) => &param.name,
        AtomObj::FnSet(param) => &param.name,
        AtomObj::Induc(param) => &param.name,
        AtomObj::DefAlgo(param) => &param.name,
        AtomObj::DefStructField(param) => &param.name,
        AtomObj::TupleIndex(param) => &param.name,
        AtomObj::CartIndex(param) => &param.name,
    };
    let replacement = rename_map.get(name)?;
    let Obj::Atom(replacement_atom) = replacement else {
        return None;
    };
    if std::mem::discriminant(atom) != std::mem::discriminant(replacement_atom) {
        return None;
    }
    Some(replacement.clone())
}

fn binder_retagged_atom(
    atom: &AtomObj,
    binding_map: &HashMap<String, Obj>,
    source: BinderRetagSource,
) -> Option<Obj> {
    if let Some(symbol) = atom.symbol_ref() {
        return binding_map.get(&symbol.substitution_key()).cloned();
    }
    let name = match (source, atom) {
        (BinderRetagSource::Forall, AtomObj::Forall(param)) => &param.name,
        (BinderRetagSource::Exist, AtomObj::Exist(param)) => &param.name,
        (BinderRetagSource::FnSet, AtomObj::FnSet(param)) => &param.name,
        (BinderRetagSource::Induc, AtomObj::Induc(param)) => &param.name,
        (BinderRetagSource::DefAlgo, AtomObj::DefAlgo(param)) => &param.name,
        _ => return None,
    };
    binding_map.get(name).cloned()
}

fn renamed_bound_param_binding(
    binding: &SymbolBinding,
    rename_map: &HashMap<String, Obj>,
    kind: ParamObjType,
) -> SymbolBinding {
    match (kind, rename_map.get(&binding.substitution_key())) {
        (ParamObjType::SetBuilder, Some(Obj::Atom(AtomObj::SetBuilder(param)))) => {
            param.symbol.to_local_binding()
        }
        (ParamObjType::FnSet, Some(Obj::Atom(AtomObj::FnSet(param)))) => {
            param.symbol.to_local_binding()
        }
        _ => binding.clone(),
    }
}

#[cfg(test)]
mod capture_avoidance_tests {
    use crate::prelude::*;
    use std::collections::HashMap;

    #[test]
    fn exact_symbol_substitution_does_not_replace_a_same_name_binding() {
        let runtime = Runtime::new();
        let target_binding = runtime
            .allocate_local_symbol_binding("x".to_string())
            .unwrap();
        let other_binding = runtime
            .allocate_local_symbol_binding("x".to_string())
            .unwrap();
        let target: Obj = DefHeaderFreeParamObj::new(&target_binding).into();
        let mut map = HashMap::new();
        insert_symbol_substitution(
            &mut map,
            &other_binding,
            Number::new("1".to_string()).into(),
        );

        let instantiated = runtime
            .inst_obj(&target, &map, ParamObjType::DefHeader)
            .unwrap();

        assert!(matches!(
            instantiated,
            Obj::Atom(AtomObj::Def(param)) if param.symbol.id() == target_binding.id()
        ));
    }

    #[test]
    fn set_builder_instantiation_alpha_renames_only_its_own_binder_kind() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("set_builder_capture_avoidance");
        let a_binding = runtime
            .allocate_local_symbol_binding("a".to_string())
            .unwrap();
        let n_binding = runtime
            .allocate_local_symbol_binding("n".to_string())
            .unwrap();
        let replacement_n = runtime
            .allocate_local_symbol_binding("n".to_string())
            .unwrap();
        let body_fact: AtomicFact = EqualFact::new(
            DefHeaderFreeParamObj::new(&a_binding).into(),
            SetBuilderFreeParamObj::new(&n_binding).into(),
            default_line_file(),
        )
        .into();
        let object: Obj = SetBuilder::new(
            n_binding,
            Identifier::new("n".to_string()).into(),
            vec![body_fact.into()],
        )
        .unwrap()
        .into();
        let mut map = HashMap::new();
        insert_symbol_substitution(
            &mut map,
            &a_binding,
            SetBuilderFreeParamObj::new(&replacement_n).into(),
        );

        let instantiated = runtime
            .inst_obj(&object, &map, ParamObjType::DefHeader)
            .unwrap();
        let Obj::SetBuilder(instantiated) = instantiated else {
            panic!("expected set builder");
        };
        assert_ne!(instantiated.param, "n");
        assert!(matches!(
            instantiated.param_set.as_ref(),
            Obj::Atom(AtomObj::Identifier(identifier)) if identifier.name == "n"
        ));
        let ExistBodyFact::AtomicFact(AtomicFact::EqualFact(equality)) = &instantiated.facts[0]
        else {
            panic!("expected equality body");
        };
        assert!(matches!(
            &equality.left,
            Obj::Atom(AtomObj::SetBuilder(param)) if param.name == "n"
        ));
        assert!(matches!(
            &equality.right,
            Obj::Atom(AtomObj::SetBuilder(param)) if param.name == instantiated.param
        ));
    }

    #[test]
    fn surviving_closed_set_builder_replacement_keeps_outer_binder_fresh() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("closed_set_builder_replacement");
        let a_binding = runtime
            .allocate_local_symbol_binding("a".to_string())
            .unwrap();
        let target_n = runtime
            .allocate_local_symbol_binding("n".to_string())
            .unwrap();
        let target: Obj = SetBuilder::new(
            target_n.clone(),
            StandardSet::R.into(),
            vec![EqualFact::new(
                DefHeaderFreeParamObj::new(&a_binding).into(),
                SetBuilderFreeParamObj::new(&target_n).into(),
                default_line_file(),
            )
            .into()],
        )
        .unwrap()
        .into();
        let replacement_n = runtime
            .allocate_local_symbol_binding("n".to_string())
            .unwrap();
        let replacement: Obj = SetBuilder::new(
            replacement_n.clone(),
            StandardSet::R.into(),
            vec![EqualFact::new(
                SetBuilderFreeParamObj::new(&replacement_n).into(),
                SetBuilderFreeParamObj::new(&replacement_n).into(),
                default_line_file(),
            )
            .into()],
        )
        .unwrap()
        .into();
        let mut map = HashMap::new();
        insert_symbol_substitution(&mut map, &a_binding, replacement);

        let instantiated = runtime
            .inst_obj(&target, &map, ParamObjType::DefHeader)
            .unwrap();
        let Obj::SetBuilder(instantiated) = instantiated else {
            panic!("expected set builder");
        };
        assert_ne!(instantiated.param, "n");

        let unused_n = runtime
            .allocate_local_symbol_binding("n".to_string())
            .unwrap();
        let unused_target: Obj = SetBuilder::new(
            unused_n.clone(),
            StandardSet::R.into(),
            vec![EqualFact::new(
                SetBuilderFreeParamObj::new(&unused_n).into(),
                SetBuilderFreeParamObj::new(&unused_n).into(),
                default_line_file(),
            )
            .into()],
        )
        .unwrap()
        .into();
        let restored = runtime
            .inst_obj(&unused_target, &map, ParamObjType::DefHeader)
            .unwrap();
        let Obj::SetBuilder(restored) = restored else {
            panic!("expected set builder");
        };
        assert_eq!(restored.param, "n");
    }

    #[test]
    fn function_binder_instantiation_preserves_outer_argument_and_concrete_type() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("function_binder_capture_avoidance");
        let a_binding = runtime
            .allocate_local_symbol_binding("a".to_string())
            .unwrap();
        let group = runtime
            .fresh_param_group_with_set(
                vec!["n".to_string()],
                Identifier::new("n".to_string()).into(),
            )
            .unwrap();
        let n_binding = group.params[0].clone();
        let dom_fact: AtomicFact = EqualFact::new(
            DefHeaderFreeParamObj::new(&a_binding).into(),
            FnSetFreeParamObj::new(&n_binding).into(),
            default_line_file(),
        )
        .into();
        let object: Obj = FnSet::new(
            vec![group],
            vec![dom_fact.into()],
            Identifier::new("ret".to_string()).into(),
        )
        .unwrap()
        .into();
        let replacement_n = runtime
            .allocate_local_symbol_binding("n".to_string())
            .unwrap();
        let mut map = HashMap::new();
        insert_symbol_substitution(
            &mut map,
            &a_binding,
            FnSetFreeParamObj::new(&replacement_n).into(),
        );

        let instantiated = runtime
            .inst_obj(&object, &map, ParamObjType::DefHeader)
            .unwrap();
        let Obj::FnSet(instantiated) = instantiated else {
            panic!("expected function set");
        };
        let fresh_name = instantiated.body.params_def_with_set[0].params[0].name();
        assert_ne!(fresh_name, "n");
        assert!(matches!(
            instantiated.body.params_def_with_set[0].set_obj(),
            Obj::Atom(AtomObj::Identifier(identifier)) if identifier.name == "n"
        ));
        let OrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equality)) =
            &instantiated.body.dom_facts[0]
        else {
            panic!("expected equality domain fact");
        };
        assert!(matches!(
            &equality.left,
            Obj::Atom(AtomObj::FnSet(param)) if param.name == "n"
        ));
        assert!(matches!(
            &equality.right,
            Obj::Atom(AtomObj::FnSet(param)) if param.name == fresh_name
        ));
    }

    #[test]
    fn anonymous_function_restores_binder_only_after_collision_disappears() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("closed_anonymous_function_replacement");
        let f_binding = runtime
            .allocate_local_symbol_binding("f".to_string())
            .unwrap();
        let target_group = runtime
            .fresh_param_group_with_set(vec!["x".to_string()], StandardSet::R.into())
            .unwrap();
        let target: Obj = AnonymousFn::new(
            vec![target_group],
            vec![],
            StandardSet::R.into(),
            DefHeaderFreeParamObj::new(&f_binding).into(),
        )
        .unwrap()
        .into();
        let replacement_group = runtime
            .fresh_param_group_with_set(vec!["x".to_string()], StandardSet::R.into())
            .unwrap();
        let replacement_x = replacement_group.params[0].clone();
        let replacement: Obj = AnonymousFn::new(
            vec![replacement_group],
            vec![],
            StandardSet::R.into(),
            FnSetFreeParamObj::new(&replacement_x).into(),
        )
        .unwrap()
        .into();
        let mut map = HashMap::new();
        insert_symbol_substitution(&mut map, &f_binding, replacement);

        let instantiated = runtime
            .inst_obj(&target, &map, ParamObjType::DefHeader)
            .unwrap();
        let Obj::AnonymousFn(instantiated) = instantiated else {
            panic!("expected anonymous function");
        };
        assert_ne!(
            instantiated.body.params_def_with_set[0].param_names(),
            vec!["x"]
        );

        let beta_group = runtime
            .fresh_param_group_with_set(vec!["x".to_string()], StandardSet::R.into())
            .unwrap();
        let beta_x = beta_group.params[0].clone();
        let theorem_f = runtime
            .allocate_local_symbol_binding("f".to_string())
            .unwrap();
        let beta_target: Obj = AnonymousFn::new(
            vec![beta_group],
            vec![],
            StandardSet::R.into(),
            FnObj::new(
                ForallFreeParamObj::new(&theorem_f).into(),
                vec![vec![Box::new(FnSetFreeParamObj::new(&beta_x).into())]],
            )
            .into(),
        )
        .unwrap()
        .into();
        let mut theorem_map = HashMap::new();
        insert_symbol_substitution(&mut theorem_map, &theorem_f, map["f"].clone());
        let restored = runtime
            .inst_obj(
                &beta_target,
                &theorem_map,
                ParamObjType::TheoremInstantiation,
            )
            .unwrap();
        let Obj::AnonymousFn(restored) = restored else {
            panic!("expected anonymous function");
        };
        assert_eq!(
            restored.body.params_def_with_set[0].param_names(),
            vec!["x"]
        );
    }

    #[test]
    fn set_builder_alpha_rename_updates_a_dependent_parameter_set() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("set_builder_dependent_type_alpha_rename");
        let n_binding = runtime
            .allocate_local_symbol_binding("n".to_string())
            .unwrap();
        let a_binding = runtime
            .allocate_local_symbol_binding("a".to_string())
            .unwrap();
        let object: Obj = SetBuilder::new(
            n_binding.clone(),
            SetBuilderFreeParamObj::new(&n_binding).into(),
            vec![EqualFact::new(
                DefHeaderFreeParamObj::new(&a_binding).into(),
                SetBuilderFreeParamObj::new(&n_binding).into(),
                default_line_file(),
            )
            .into()],
        )
        .unwrap()
        .into();
        let replacement_n = runtime
            .allocate_local_symbol_binding("n".to_string())
            .unwrap();
        let mut map = HashMap::new();
        insert_symbol_substitution(
            &mut map,
            &a_binding,
            SetBuilderFreeParamObj::new(&replacement_n).into(),
        );

        let instantiated = runtime
            .inst_obj(&object, &map, ParamObjType::DefHeader)
            .unwrap();
        let Obj::SetBuilder(instantiated) = instantiated else {
            panic!("expected set builder");
        };
        assert_ne!(instantiated.param, "n");
        assert!(matches!(
            instantiated.param_set.as_ref(),
            Obj::Atom(AtomObj::SetBuilder(param)) if param.name == instantiated.param
        ));
    }

    #[test]
    fn function_alpha_rename_respects_dependent_parameter_scope() {
        let runtime = Runtime::new();
        let external_n = runtime
            .allocate_local_symbol_binding("n".to_string())
            .unwrap();
        let n_group = runtime
            .fresh_param_group_with_set(
                vec!["n".to_string()],
                FnSetFreeParamObj::new(&external_n).into(),
            )
            .unwrap();
        let n_binding = n_group.params[0].clone();
        let m_group = runtime
            .fresh_param_group_with_set(
                vec!["m".to_string()],
                FnSetFreeParamObj::new(&n_binding).into(),
            )
            .unwrap();
        let m_binding = m_group.params[0].clone();
        let body = FnSetBody::new(
            vec![n_group, m_group],
            vec![],
            FnSetFreeParamObj::new(&m_binding).into(),
        );
        let n_fresh = runtime
            .allocate_local_symbol_binding("n_fresh".to_string())
            .unwrap();
        let m_fresh = runtime
            .allocate_local_symbol_binding("m_fresh".to_string())
            .unwrap();
        let mut rename_map = HashMap::new();
        insert_symbol_substitution(
            &mut rename_map,
            &n_binding,
            FnSetFreeParamObj::new(&n_fresh).into(),
        );
        insert_symbol_substitution(
            &mut rename_map,
            &m_binding,
            FnSetFreeParamObj::new(&m_fresh).into(),
        );

        let renamed = runtime
            .alpha_rename_fn_set_body(&body, &rename_map)
            .unwrap();
        assert!(matches!(
            renamed.params_def_with_set[0].set_obj(),
            Obj::Atom(AtomObj::FnSet(param)) if param.name == "n"
        ));
        assert!(matches!(
            renamed.params_def_with_set[1].set_obj(),
            Obj::Atom(AtomObj::FnSet(param)) if param.name == "n_fresh"
        ));
        assert_eq!(
            renamed.params_def_with_set[0].param_names(),
            vec!["n_fresh"]
        );
        assert_eq!(
            renamed.params_def_with_set[1].param_names(),
            vec!["m_fresh"]
        );
        assert!(matches!(
            renamed.ret_set.as_ref(),
            Obj::Atom(AtomObj::FnSet(param)) if param.name == "m_fresh"
        ));
    }
}
