//! Release exactly one definition-owned struct layer into the current top Env.
//!
//! Shared by direct `&Struct` binding auto-open and (later) `release struct def`.
//! Does not re-check `e $in &Struct`; callers must already have that membership.
//!
//! A struct must have at least two fields (parse-enforced). Release always uses
//! the tuple representation: bridges `e.f_i = e[i]`, cart membership, laws.
//!
//! Example (auto-open on bind):
//!   forall G &Group<s>:
//!       G.mul(G.one, G.one) = G.one
//!   // binding `G` stores bridges and instantiated `<=>:` laws

use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, Fact, InFact, IsTupleFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{
    Cart, FieldAccess, Number, Obj, ObjAtIndex, StructObj, TupleDim,
};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::ast::stmt::DefStructStmt;
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

        for (index, field) in def.fields.iter().enumerate() {
            let field_value = field_access_obj(obj, &field.binding.name);
            let projection = Obj::ObjAtIndex(ObjAtIndex {
                obj: Box::new(obj.clone()),
                index: Box::new(Obj::Number(Number {
                    normalized_value: (index + 1).to_string(),
                })),
            });
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
        if def.fields.len() < 2 {
            return Err(format!("struct `{name}` expects at least two fields"));
        }
        Ok(def)
    }

    // Header params + each field BoundName → field access. `<=>:` and field
    // types already reuse those BoundName ids at parse time.
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
        for field in &def.fields {
            subst.insert(field.binding.id, field_access_obj(obj, &field.binding.name));
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
