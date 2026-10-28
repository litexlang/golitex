//! Project an actual tuple through a checked, declaration-selected field view.

use super::by_parent_checked_beta::ParentCheckedBetaFunctionBody;
use crate::execute::execute_fact_stmt::known_tuple::{
    KnownFunctionTupleValueProof, KnownTupleValueProof,
};
use crate::prelude::*;

pub struct StructFieldValueProof {
    pub receiver_well_defined: Box<ObjWellDefinedProof>,
    pub carrier: StructObj,
    pub index: usize,
    pub source: StructTupleValueSource,
}

pub enum StructTupleValueSource {
    Known(KnownTupleValueProof),
    Function(KnownFunctionTupleValueProof),
    Template {
        instance: InstantiatedTemplateObj,
        value: Tuple,
    },
    Returned {
        body: Box<ParentCheckedBetaFunctionBody>,
        value: Tuple,
    },
    ReturnedFunction {
        body: Box<ParentCheckedBetaFunctionBody>,
        application_well_defined: Box<ObjWellDefinedProof>,
        function: KnownFunctionTupleValueProof,
    },
}

impl Runtime {
    // The parent checked the entire field path. Descend only to its shorter
    // receiver; consume stored equality or a checked definition's actual tuple.
    // This does not release struct laws or publish a new view on an alias.
    pub(super) fn struct_field_value(
        &mut self,
        field: &FieldAccess,
        state: VerifyState,
    ) -> RuntimeResult<Option<(StructFieldValueProof, Obj)>> {
        let Some(name) = field.fields.last() else {
            return Ok(None);
        };
        let receiver = if field.fields.len() == 1 {
            field.obj.as_ref().clone()
        } else {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(FieldAccess {
                obj: field.obj.clone(),
                fields: field.fields[..field.fields.len() - 1].to_vec(),
            }))
        };
        let VerifyObjWellDefinedResult::Success(receiver_well_defined) =
            self.verify_obj_well_definedness(&receiver, state)?
        else {
            return Ok(None);
        };
        let Some(carrier) = self.resolve_definition_struct_carrier(&receiver) else {
            return Ok(None);
        };
        let Some(definition) = self.def_struct_visible(&carrier.name) else {
            return Ok(None);
        };
        let Some(index) = definition
            .fields
            .iter()
            .position(|f| &f.binding.name == name)
        else {
            return Ok(None);
        };
        let dimension = definition.fields.len();
        let source = if let Some(known) = self
            .known_literal_tuple_candidates(&receiver)
            .into_iter()
            .next()
        {
            Some(StructTupleValueSource::Known(known))
        } else if let Obj::FnObj(application) = &receiver {
            self.lookup_known_function_tuple_value(application)
                .map(StructTupleValueSource::Function)
        } else if let Obj::InstantiatedTemplateObj(instance) = &receiver {
            match self.expanded_have_obj_equal_rhs_of_instantiated_template(instance)? {
                Some(Obj::ProductShape(ProductShape::Tuple(value))) => {
                    Some(StructTupleValueSource::Template {
                        instance: instance.clone(),
                        value,
                    })
                }
                _ => None,
            }
        } else {
            None
        };
        let source = match source {
            Some(source) => source,
            None => {
                match self.parent_checked_beta_body(
                    &receiver,
                    receiver_well_defined.as_view(),
                    state,
                )? {
                    Some((body, Obj::ProductShape(ProductShape::Tuple(value)))) => {
                        StructTupleValueSource::Returned {
                            body: Box::new(body),
                            value,
                        }
                    }
                    Some((body, Obj::FnObj(application))) => {
                        // For `outer(a) = (make(a), tag)`, the inner field names
                        // one more checked application. Do not chase alias graphs.
                        let VerifyObjWellDefinedResult::Success(application_well_defined) = self
                            .verify_obj_well_definedness(&Obj::FnObj(application.clone()), state)?
                        else {
                            return Ok(None);
                        };
                        let Some(function) = self.lookup_known_function_tuple_value(&application)
                        else {
                            return Ok(None);
                        };
                        StructTupleValueSource::ReturnedFunction {
                            body: Box::new(body),
                            application_well_defined: Box::new(application_well_defined),
                            function,
                        }
                    }
                    _ => return Ok(None),
                }
            }
        };
        let tuple = match &source {
            StructTupleValueSource::Known(proof) => &proof.value,
            StructTupleValueSource::Function(proof) => &proof.value,
            StructTupleValueSource::Template { value, .. }
            | StructTupleValueSource::Returned { value, .. } => value,
            StructTupleValueSource::ReturnedFunction { function, .. } => &function.value,
        };
        if tuple.args.len() != dimension {
            return Ok(None);
        }
        let value = tuple.args[index].as_ref().clone();
        Ok(Some((
            StructFieldValueProof {
                receiver_well_defined: Box::new(receiver_well_defined),
                carrier,
                index: index + 1,
                source,
            },
            value,
        )))
    }
}
