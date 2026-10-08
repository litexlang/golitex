//! Bounded input subsets derived from a checked complete callable domain.
use crate::ast::fact::{AtomicFact, EqualFact, InFact, QuantifierFreeFact};
use crate::ast::obj::{
    Cart, FunctionSpace, IdentifierObj, Literal, Number, Obj, ProductShape, SetBuilder, SetFormer,
};
use crate::display_and_ir::ObjIR;
use crate::execute::execute_fact_stmt::function_domain::{
    function_application, CompleteFunctionDomainProof,
};
use crate::execute::execute_fact_stmt::{
    ObjWellDefinedProof, VerifyObjWellDefinedResult, VerifyState,
};
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::cell::RefCell;
use std::collections::HashMap;

pub struct FunctionPreimageConstructionProof {
    pub source: Box<CompleteFunctionDomainProof>,
    pub builder: SetBuilder,
    pub builder_well_defined: Box<ObjWellDefinedProof>,
}

pub enum FunctionPreimageConstructionFailure {
    NoCompleteDomain,
    Construction(Vec<VerifyObjWellDefinedResult>),
}

impl Runtime {
    pub(crate) fn verify_function_preimage_construction(
        &mut self,
        root: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Result<FunctionPreimageConstructionProof, FunctionPreimageConstructionFailure>>
    {
        let function = match root {
            Obj::FunctionSpace(FunctionSpace::Preimage(value)) => value.function.as_ref(),
            Obj::FunctionSpace(FunctionSpace::PreimageSet(value)) => value.function.as_ref(),
            _ => {
                return Err(RuntimeError::InternalBug(
                    "preimage construction requires a preimage object".to_string(),
                ))
            }
        };
        // A domain alias may name this same preimage. Binder assumptions must
        // not recursively expand the construction currently being checked.
        let _scope = FunctionPreimageScope::new(root);
        let sources = self.complete_function_domains(function, state)?;
        if sources.is_empty() {
            return Ok(Err(FunctionPreimageConstructionFailure::NoCompleteDomain));
        }
        let mut failures = Vec::new();
        for source in sources {
            let builder = self.build_function_preimage(root, &source)?;
            let expanded = Obj::SetFormer(SetFormer::SetBuilder(builder.clone()));
            match self.verify_obj_well_definedness(&expanded, state)? {
                VerifyObjWellDefinedResult::Success(proof) => {
                    return Ok(Ok(FunctionPreimageConstructionProof {
                        source: Box::new(source),
                        builder,
                        builder_well_defined: Box::new(proof),
                    }))
                }
                failed => failures.push(failed),
            }
        }
        Ok(Err(FunctionPreimageConstructionFailure::Construction(
            failures,
        )))
    }

    fn build_function_preimage(
        &mut self,
        root: &Obj,
        source: &CompleteFunctionDomainProof,
    ) -> RuntimeResult<SetBuilder> {
        let signature = &source.signature;
        let parameters: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(move |param| (param, group.param_type.as_ref()))
            })
            .collect();
        let binder = self.fresh_internal_param();
        let input = Obj::Identifier(IdentifierObj::from_bound_name(&binder));
        let base = if parameters.len() == 1 {
            parameters[0].1.clone()
        } else {
            Obj::ProductShape(ProductShape::Cart(Cart {
                args: parameters
                    .iter()
                    .map(|(_, carrier)| Box::new((*carrier).clone()))
                    .collect(),
            }))
        };
        let mut arguments = Vec::with_capacity(parameters.len());
        let mut substitution = HashMap::new();
        for (index, (param, _)) in parameters.iter().enumerate() {
            let argument = if parameters.len() == 1 {
                input.clone()
            } else {
                let coordinate = Obj::Literal(Literal::Number(Number {
                    normalized_value: (index + 1).to_string(),
                }));
                function_application(&input, vec![Box::new(coordinate)])
                    .map_err(RuntimeError::InternalBug)?
            };
            substitution.insert(param.id, argument.clone());
            arguments.push(Box::new(argument));
        }
        let mut facts = Vec::with_capacity(signature.dom_facts.len() + 1);
        for guard in &signature.dom_facts {
            facts.push(
                self.inst_quantifier_free_fact(guard, &substitution)
                    .map_err(|error| {
                        RuntimeError::InternalBug(format!("preimage guard substitution: {error}"))
                    })?,
            );
        }
        let condition: AtomicFact = match root {
            Obj::FunctionSpace(FunctionSpace::Preimage(value)) => EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: function_application(&value.function, arguments)
                    .map_err(RuntimeError::InternalBug)?,
                right: value.value.as_ref().clone(),
                line_file: None,
            }
            .into(),
            Obj::FunctionSpace(FunctionSpace::PreimageSet(value)) => InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: function_application(&value.function, arguments)
                    .map_err(RuntimeError::InternalBug)?,
                set: value.target_set.as_ref().clone(),
                line_file: None,
            }
            .into(),
            _ => {
                return Err(RuntimeError::InternalBug(
                    "preimage condition requires a preimage object".to_string(),
                ))
            }
        };
        facts.push(QuantifierFreeFact::AtomicFact(condition));
        Ok(SetBuilder {
            param_binding: binder,
            param_set: Box::new(base),
            facts,
        })
    }
}

thread_local! {
    static PREIMAGE_SCOPES: RefCell<Vec<ObjIR>> = RefCell::new(Vec::new());
}

pub(crate) struct FunctionPreimageScope {
    root: ObjIR,
}

impl FunctionPreimageScope {
    pub(crate) fn new(root: &Obj) -> Self {
        let root = root.ir();
        PREIMAGE_SCOPES.with(|scopes| scopes.borrow_mut().push(root.clone()));
        Self { root }
    }
}

impl Drop for FunctionPreimageScope {
    fn drop(&mut self) {
        PREIMAGE_SCOPES.with(|scopes| {
            let popped = scopes.borrow_mut().pop();
            debug_assert!(popped.as_ref() == Some(&self.root));
        });
    }
}

pub(crate) fn function_preimage_scope_active(root: &Obj) -> bool {
    let key = root.ir();
    PREIMAGE_SCOPES.with(|scopes| scopes.borrow().iter().any(|active| active == &key))
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/function_preimages/tests.rs"]
mod function_preimages_tests;
