//! Release exactly one definition-owned struct layer into the current top Env.
//!
//! Shared by direct `&Struct` binding auto-open and (later) `release struct def`.
//! Does not re-check `e $in &Struct`; callers must already have that membership.
//!
//! Example (auto-open on bind):
//!   forall G &Group<s>:
//!       G.mul(G.one, G.one) = G.one
//!   // binding `G` stores bridges and instantiated `<=>:` laws

use std::collections::{HashMap, HashSet};

use crate::new_pipeline::ast::fact::{
    atomic_fact_args_ref, AndChainAtomicFact, AtomicFact, EqualFact, ExistOrAndChainAtomicFact,
    Fact, InFact, IsTupleFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{
    Cart, FieldAccess, FnObjHead, IdentifierObj, Number, Obj, ObjAtIndex, StructObj, TupleDim,
};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::ast::stmt::DefStructStmt;
use crate::new_pipeline::instantiate::quantifier_free_fact_to_fact;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

pub struct ReleaseOneStructLayerProof {
    pub obj: Obj,
    pub struct_obj: StructObj,
    pub store_and_infer: Vec<StoreFactAndInferResult>,
}

pub struct FailToReleaseOneStructLayer {
    pub obj: Obj,
    pub struct_obj: StructObj,
    pub reason: String,
}

pub enum ReleaseOneStructLayerResult {
    Success(ReleaseOneStructLayerProof),
    Failed(FailToReleaseOneStructLayer),
}

impl ReleaseOneStructLayerResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Soft miss: Ok(Failed); operational bug: Err(...).
    pub fn release_one_struct_layer(
        &mut self,
        obj: &Obj,
        struct_obj: &StructObj,
    ) -> RuntimeResult<ReleaseOneStructLayerResult> {
        let def = match self.struct_def_for_release(struct_obj) {
            Ok(d) => d,
            Err(reason) => {
                return Ok(failed_release(obj, struct_obj, reason));
            }
        };

        let subst = match self.struct_release_subst(obj, struct_obj, &def) {
            Ok(s) => s,
            Err(reason) => {
                return Ok(failed_release(obj, struct_obj, reason));
            }
        };

        let mut field_types = Vec::with_capacity(def.fields.len());
        for field in &def.fields {
            match self.inst_obj(&field.field_type, &subst) {
                Ok(o) => field_types.push(o),
                Err(e) => {
                    return Ok(failed_release(
                        obj,
                        struct_obj,
                        format!("instantiate field type `{}`: {e}", field.binding.name),
                    ));
                }
            }
        }

        let mut store_and_infer = Vec::new();

        if def.fields.len() > 1 {
            let cart = Obj::Cart(Cart {
                args: field_types.iter().cloned().map(Box::new).collect(),
            });
            let is_tuple = Fact::AtomicFact(AtomicFact::IsTupleFact(IsTupleFact {
                fact_id: self.ids.allocate_fact_id(),
                set: obj.clone(),
                line_file: None,
            }));
            store_and_infer.push(self.store_fact_and_infer(&is_tuple)?);

            let tuple_dim = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.ids.allocate_fact_id(),
                left: Obj::TupleDim(TupleDim {
                    arg: Box::new(obj.clone()),
                }),
                right: Obj::Number(Number {
                    normalized_value: def.fields.len().to_string(),
                }),
                line_file: None,
            }));
            store_and_infer.push(self.store_fact_and_infer(&tuple_dim)?);

            let cart_membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.ids.allocate_fact_id(),
                element: obj.clone(),
                set: cart,
                line_file: None,
            }));
            store_and_infer.push(self.store_fact_and_infer(&cart_membership)?);
        }

        for (index, field) in def.fields.iter().enumerate() {
            let field_value = field_access_obj(obj, &field.binding.name);
            let projection = if def.fields.len() == 1 {
                obj.clone()
            } else {
                Obj::ObjAtIndex(ObjAtIndex {
                    obj: Box::new(obj.clone()),
                    index: Box::new(Obj::Number(Number {
                        normalized_value: (index + 1).to_string(),
                    })),
                })
            };
            let bridge = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.ids.allocate_fact_id(),
                left: field_value,
                right: projection,
                line_file: None,
            }));
            store_and_infer.push(self.store_fact_and_infer(&bridge)?);
        }

        for (field, named_field_type) in def.fields.iter().zip(field_types.iter()) {
            let field_value = field_access_obj(obj, &field.binding.name);
            let field_membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.ids.allocate_fact_id(),
                element: field_value,
                set: named_field_type.clone(),
                line_file: None,
            }));
            store_and_infer.push(self.store_fact_and_infer(&field_membership)?);
            if def.fields.len() == 1 {
                let carrier_membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.ids.allocate_fact_id(),
                    element: obj.clone(),
                    set: named_field_type.clone(),
                    line_file: None,
                }));
                store_and_infer.push(self.store_fact_and_infer(&carrier_membership)?);
            }
        }

        for fact in &def.equivalent_facts {
            let named = match self.inst_fact(fact, &subst) {
                Ok(f) => f,
                Err(e) => {
                    return Ok(failed_release(
                        obj,
                        struct_obj,
                        format!("instantiate struct law: {e}"),
                    ));
                }
            };
            store_and_infer.push(self.store_fact_and_infer(&named)?);

            if def.fields.len() == 1 {
                let mut carrier_subst = subst.clone();
                carrier_subst.insert(def.fields[0].binding.id, obj.clone());
                let carrier_law = match self.inst_fact(fact, &carrier_subst) {
                    Ok(f) => f,
                    Err(e) => {
                        return Ok(failed_release(
                            obj,
                            struct_obj,
                            format!("instantiate one-field carrier law: {e}"),
                        ));
                    }
                };
                store_and_infer.push(self.store_fact_and_infer(&carrier_law)?);
            }
        }

        Ok(ReleaseOneStructLayerResult::Success(
            ReleaseOneStructLayerProof {
                obj: obj.clone(),
                struct_obj: struct_obj.clone(),
                store_and_infer,
            },
        ))
    }

    // Soft miss: Ok(Err((opened_before_fail, failed))); None when no struct params.
    pub fn auto_open_struct_layers_for_typed_parameters(
        &mut self,
        typed_parameters: &TypedParameterList,
    ) -> RuntimeResult<
        Result<
            Option<Vec<ReleaseOneStructLayerProof>>,
            (Vec<ReleaseOneStructLayerProof>, FailToReleaseOneStructLayer),
        >,
    > {
        let mut opened = Vec::new();
        for group in &typed_parameters.groups {
            let ParamType::Obj(Obj::StructObj(struct_obj)) = &group.param_type else {
                continue;
            };
            for identifier in &group.params {
                let element = Obj::Identifier(self.identifier_obj_for_stored_mention(identifier));
                match self.release_one_struct_layer(&element, struct_obj)? {
                    ReleaseOneStructLayerResult::Success(proof) => opened.push(proof),
                    ReleaseOneStructLayerResult::Failed(failed) => {
                        return Ok(Err((opened, failed)));
                    }
                }
            }
        }
        if opened.is_empty() {
            Ok(Ok(None))
        } else {
            Ok(Ok(Some(opened)))
        }
    }

    fn struct_def_for_release(&self, struct_obj: &StructObj) -> Result<DefStructStmt, String> {
        let name = match &struct_obj.name {
            AtomicName::Plain { name }
            | AtomicName::WithExportFileId { name, .. }
            | AtomicName::WithModAndExportFileId { name, .. } => name.clone(),
        };
        let def = self
            .def_struct_visible_in_stack(&name)
            .cloned()
            .ok_or_else(|| format!("struct `{name}` is not defined"))?;
        let expected = def
            .param_def_with_dom
            .as_ref()
            .map(|(p, _)| p.groups.iter().map(|g| g.params.len()).sum::<usize>())
            .unwrap_or(0);
        if expected != struct_obj.params.len() {
            return Err(format!(
                "struct `{name}` expects {expected} parameter(s), got {}",
                struct_obj.params.len()
            ));
        }
        if def.fields.is_empty() {
            return Err(format!("struct `{name}` has no fields"));
        }
        Ok(def)
    }

    fn struct_release_subst(
        &self,
        obj: &Obj,
        struct_obj: &StructObj,
        def: &DefStructStmt,
    ) -> Result<HashMap<IdentifierId, Obj>, String> {
        let mut subst = HashMap::new();
        if let Some((params, _)) = &def.param_def_with_dom {
            let mut arg_index = 0;
            for group in &params.groups {
                for binding in &group.params {
                    let arg = struct_obj.params.get(arg_index).ok_or_else(|| {
                        format!("missing struct parameter argument for `{}`", binding.name)
                    })?;
                    subst.insert(binding.id, arg.clone());
                    arg_index += 1;
                }
            }
        }

        let field_names: HashSet<String> =
            def.fields.iter().map(|f| f.binding.name.clone()).collect();
        for fact in &def.equivalent_facts {
            visit_plain_ids_in_fact(fact, &mut |id, name| {
                if field_names.contains(name) {
                    subst
                        .entry(id)
                        .or_insert_with(|| field_access_obj(obj, name));
                }
            });
        }
        for field in &def.fields {
            // Prefer the field's own BoundName id for release subst.
            subst
                .entry(field.binding.id)
                .or_insert_with(|| field_access_obj(obj, &field.binding.name));
            visit_plain_ids_in_obj(&field.field_type, &mut |id, name| {
                if field_names.contains(name) {
                    subst
                        .entry(id)
                        .or_insert_with(|| field_access_obj(obj, name));
                }
            });
        }
        Ok(subst)
    }
}

fn failed_release(
    obj: &Obj,
    struct_obj: &StructObj,
    reason: String,
) -> ReleaseOneStructLayerResult {
    ReleaseOneStructLayerResult::Failed(FailToReleaseOneStructLayer {
        obj: obj.clone(),
        struct_obj: struct_obj.clone(),
        reason,
    })
}

fn field_access_obj(obj: &Obj, field: &str) -> Obj {
    Obj::FieldAccess(FieldAccess {
        obj: Box::new(obj.clone()),
        fields: vec![field.to_string()],
    })
}

fn visit_plain_ids_in_fact(fact: &Fact, on_id: &mut dyn FnMut(IdentifierId, &str)) {
    match fact {
        Fact::AtomicFact(a) => {
            for o in atomic_fact_args_ref(a) {
                visit_plain_ids_in_obj(o, on_id);
            }
        }
        Fact::AndFact(a) => {
            for atomic in &a.facts {
                for o in atomic_fact_args_ref(atomic) {
                    visit_plain_ids_in_obj(o, on_id);
                }
            }
        }
        Fact::OrFact(o) => {
            for branch in &o.facts {
                visit_plain_ids_in_and_chain(branch, on_id);
            }
        }
        Fact::ChainFact(c) => {
            for o in &c.objs {
                visit_plain_ids_in_obj(o, on_id);
            }
        }
        Fact::ForallFact(f) => {
            for d in &f.dom_facts {
                visit_plain_ids_in_fact(d, on_id);
            }
            for t in &f.then_facts {
                visit_plain_ids_in_exist_or_and(t, on_id);
            }
        }
        Fact::ForallFactWithIff(f) => {
            visit_plain_ids_in_fact(&Fact::ForallFact(f.forall_fact.clone()), on_id);
            for i in &f.iff_facts {
                visit_plain_ids_in_exist_or_and(i, on_id);
            }
        }
        Fact::ExistFact(e) | Fact::ExistUniqueFact(e) | Fact::NotExistFact(e) => {
            for b in &e.facts {
                visit_plain_ids_in_qf(b, on_id);
            }
        }
        Fact::NotForall(n) => {
            for d in &n.dom_facts {
                visit_plain_ids_in_qf(d, on_id);
            }
            for t in &n.then_facts {
                visit_plain_ids_in_qf(t, on_id);
            }
        }
    }
}

fn visit_plain_ids_in_obj(obj: &Obj, on_id: &mut dyn FnMut(IdentifierId, &str)) {
    match obj {
        Obj::Identifier(IdentifierObj::Plain { id, name }) => on_id(*id, name),
        Obj::FnObj(f) => {
            match f.head.as_ref() {
                FnObjHead::Identifier(IdentifierObj::Plain { id, name }) => on_id(*id, name),
                FnObjHead::FieldAccess(a) => visit_plain_ids_in_obj(&a.obj, on_id),
                FnObjHead::ObjAtIndex(a) => {
                    visit_plain_ids_in_obj(&a.obj, on_id);
                    visit_plain_ids_in_obj(&a.index, on_id);
                }
                FnObjHead::AnonymousFnLiteral(a) => {
                    visit_plain_ids_in_obj(&Obj::AnonymousFn((**a).clone()), on_id);
                }
                FnObjHead::FiniteSeqListObj(a) => {
                    for o in &a.objs {
                        visit_plain_ids_in_obj(o, on_id);
                    }
                }
                FnObjHead::InstantiatedTemplateObj(a) => {
                    for o in &a.args {
                        visit_plain_ids_in_obj(o, on_id);
                    }
                }
                FnObjHead::Identifier(_) => {}
            }
            for row in &f.body {
                for o in row {
                    visit_plain_ids_in_obj(o, on_id);
                }
            }
        }
        Obj::FieldAccess(a) => visit_plain_ids_in_obj(&a.obj, on_id),
        Obj::Add(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Sub(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Mul(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Div(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Mod(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Quot(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Gcd(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Lcm(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Min(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Max(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Union(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Intersect(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::SetMinus(a) => {
            visit_plain_ids_in_obj(&a.left, on_id);
            visit_plain_ids_in_obj(&a.right, on_id);
        }
        Obj::Pow(a) => {
            visit_plain_ids_in_obj(&a.base, on_id);
            visit_plain_ids_in_obj(&a.exponent, on_id);
        }
        Obj::Log(a) => {
            visit_plain_ids_in_obj(&a.base, on_id);
            visit_plain_ids_in_obj(&a.arg, on_id);
        }
        Obj::Floor(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Ceil(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Exp(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Ln(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Sign(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Factorial(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Abs(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Sin(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Arcsin(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Cos(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Tan(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Cot(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::RealPart(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::ImaginaryPart(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::ComplexAbs(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::Sqrt(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::BigUnion(a) => visit_plain_ids_in_obj(&a.left, on_id),
        Obj::BigIntersect(a) => visit_plain_ids_in_obj(&a.left, on_id),
        Obj::PowerSet(a) => visit_plain_ids_in_obj(&a.set, on_id),
        Obj::CartDim(a) => visit_plain_ids_in_obj(&a.set, on_id),
        Obj::TupleDim(a) => visit_plain_ids_in_obj(&a.arg, on_id),
        Obj::ObjAtIndex(a) => {
            visit_plain_ids_in_obj(&a.obj, on_id);
            visit_plain_ids_in_obj(&a.index, on_id);
        }
        Obj::Cart(a) => {
            for o in &a.args {
                visit_plain_ids_in_obj(o, on_id);
            }
        }
        Obj::Tuple(a) => {
            for o in &a.args {
                visit_plain_ids_in_obj(o, on_id);
            }
        }
        Obj::ListSet(a) => {
            for o in &a.list {
                visit_plain_ids_in_obj(o, on_id);
            }
        }
        Obj::StructObj(s) => {
            for o in &s.params {
                visit_plain_ids_in_obj(o, on_id);
            }
        }
        Obj::FnSet(fs) => {
            for group in &fs.set_bound_parameters.groups {
                visit_plain_ids_in_obj(&group.param_type, on_id);
            }
            for d in &fs.dom_facts {
                visit_plain_ids_in_qf(d, on_id);
            }
            visit_plain_ids_in_obj(&fs.ret_set, on_id);
        }
        Obj::AnonymousFn(af) => {
            visit_plain_ids_in_obj(&Obj::FnSet(af.body.clone()), on_id);
            visit_plain_ids_in_obj(&af.equal_to, on_id);
        }
        _ => {}
    }
}

fn visit_plain_ids_in_qf(fact: &QuantifierFreeFact, on_id: &mut dyn FnMut(IdentifierId, &str)) {
    visit_plain_ids_in_fact(&quantifier_free_fact_to_fact(fact.clone()), on_id);
}

fn visit_plain_ids_in_and_chain(
    branch: &AndChainAtomicFact,
    on_id: &mut dyn FnMut(IdentifierId, &str),
) {
    match branch {
        AndChainAtomicFact::AtomicFact(a) => {
            for o in atomic_fact_args_ref(a) {
                visit_plain_ids_in_obj(o, on_id);
            }
        }
        AndChainAtomicFact::AndFact(a) => {
            for atomic in &a.facts {
                for o in atomic_fact_args_ref(atomic) {
                    visit_plain_ids_in_obj(o, on_id);
                }
            }
        }
        AndChainAtomicFact::ChainFact(c) => {
            for o in &c.objs {
                visit_plain_ids_in_obj(o, on_id);
            }
        }
    }
}

fn visit_plain_ids_in_exist_or_and(
    branch: &ExistOrAndChainAtomicFact,
    on_id: &mut dyn FnMut(IdentifierId, &str),
) {
    match branch {
        ExistOrAndChainAtomicFact::AtomicFact(a) => {
            for o in atomic_fact_args_ref(a) {
                visit_plain_ids_in_obj(o, on_id);
            }
        }
        ExistOrAndChainAtomicFact::AndFact(a) => {
            for atomic in &a.facts {
                for o in atomic_fact_args_ref(atomic) {
                    visit_plain_ids_in_obj(o, on_id);
                }
            }
        }
        ExistOrAndChainAtomicFact::ChainFact(c) => {
            for o in &c.objs {
                visit_plain_ids_in_obj(o, on_id);
            }
        }
        ExistOrAndChainAtomicFact::OrFact(o) => {
            for b in &o.facts {
                visit_plain_ids_in_and_chain(b, on_id);
            }
        }
        ExistOrAndChainAtomicFact::ExistFact(e)
        | ExistOrAndChainAtomicFact::ExistUniqueFact(e)
        | ExistOrAndChainAtomicFact::NotExistFact(e) => {
            for b in &e.facts {
                visit_plain_ids_in_qf(b, on_id);
            }
        }
    }
}
