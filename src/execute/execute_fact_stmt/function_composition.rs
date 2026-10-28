//! Strict composition preserves the complete inner domain and checks the
//! expanded lambda with the existing binder WD pipeline. No new runtime state.
use crate::prelude::function_domain::CompleteFunctionDomainSourceProof;
use crate::prelude::*;
use std::collections::HashMap;

pub struct CompositionObjWellDefinedProof {
    pub outer_well_defined: Box<ObjWellDefinedProof>,
    pub inner_well_defined: Box<ObjWellDefinedProof>,
    pub outer_domain: Box<CompleteFunctionDomainProof>,
    pub inner_domain: Box<CompleteFunctionDomainProof>,
    pub function: AnonymousFn,
    pub function_well_defined: Box<ObjWellDefinedProof>,
}

pub enum CompositionFailure {
    Operand(Box<VerifyObjWellDefinedResult>),
    NoUnaryOuterDomain,
    NoInnerDomain,
    Compatibility(Vec<VerifyObjWellDefinedResult>),
}

// A checked composition and its graph presentation. Cached construction WD is
// consumed without repeating its universal compatibility proof. In that case
// complete operand interfaces justify the derived domain and return upper bound.
pub struct CompositionCallableProof {
    pub composition: Composition,
    pub function_equal: KnownEqualityPathProof,
    pub well_defined: CompositionWellDefinedPremise,
    pub signature: CompositionSignatureProof,
    pub function: AnonymousFn,
}

// ParentAtomic is used ONLY by truth rules after the enclosing atomic WD stage.
// Its proof lives in that parent result; it must not authorize construction WD.
pub enum CompositionWellDefinedPremise {
    Checked(Box<ObjWellDefinedProof>),
    ParentAtomic,
}

pub enum CompositionSignatureProof {
    Construction,
    Interfaces {
        outer_domain: Box<CompleteFunctionDomainProof>,
        inner_domain: Box<CompleteFunctionDomainProof>,
    },
}

pub struct CompositionInFunctionSetProof {
    pub callable: Box<CompositionCallableProof>,
}
pub struct CompositionApplicationInCodomainProof {
    pub callable: Box<CompositionCallableProof>,
    pub return_set: Obj,
}

impl Runtime {
    pub(crate) fn verify_composition_obj_well_definedness(
        &mut self,
        value: &Composition,
        state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let root: Obj = value.clone().into();
        let result = self.verify_composition_construction(value, state)?;
        Ok(match result {
            Ok(proof) => VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::composition(
                self.result_detail(),
                &root,
                proof,
            )),
            Err(reason) => VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::FunctionSpace(
                    FailToVerifyFunctionSpaceObjWellDefinedResult::Composition(reason),
                ),
            },
        })
    }

    fn verify_composition_construction(
        &mut self,
        value: &Composition,
        state: VerifyState,
    ) -> RuntimeResult<Result<CompositionObjWellDefinedProof, CompositionFailure>> {
        let outer_well_defined = match self.verify_obj_well_definedness(&value.outer, state)? {
            VerifyObjWellDefinedResult::Success(proof) => Box::new(proof),
            failure => return Ok(Err(CompositionFailure::Operand(Box::new(failure)))),
        };
        let inner_well_defined = match self.verify_obj_well_definedness(&value.inner, state)? {
            VerifyObjWellDefinedResult::Success(proof) => Box::new(proof),
            failure => return Ok(Err(CompositionFailure::Operand(Box::new(failure)))),
        };
        let inner_domains = self.complete_function_domains(&value.inner, state)?;
        if inner_domains.is_empty() {
            return Ok(Err(CompositionFailure::NoInnerDomain));
        }
        let mut unary_outer_found = false;
        let mut failures = Vec::new();
        for inner_domain in inner_domains {
            if composition_arity(&inner_domain.signature) == 0 {
                continue;
            }
            for outer_domain in self.complete_function_domains(&value.outer, state)? {
                if composition_arity(&outer_domain.signature) != 1 {
                    continue;
                }
                unary_outer_found = true;
                let function = self.composition_function(
                    value,
                    &outer_domain.signature,
                    &inner_domain.signature,
                )?;
                let expanded = Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()));
                match self.verify_obj_well_definedness(&expanded, state)? {
                    VerifyObjWellDefinedResult::Success(function_well_defined) => {
                        return Ok(Ok(CompositionObjWellDefinedProof {
                            outer_well_defined,
                            inner_well_defined,
                            outer_domain: Box::new(outer_domain),
                            inner_domain: Box::new(inner_domain),
                            function,
                            function_well_defined: Box::new(function_well_defined),
                        }));
                    }
                    failure => failures.push(failure),
                }
            }
        }
        Ok(Err(if unary_outer_found {
            CompositionFailure::Compatibility(failures)
        } else {
            CompositionFailure::NoUnaryOuterDomain
        }))
    }

    pub(crate) fn composition_callables(
        &mut self,
        subject: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Vec<CompositionCallableProof>> {
        let mut proofs = Vec::new();
        // Exact equality paths are already scoped and bounded by the existing
        // property API. Only a Composition value selects this new branch.
        for (candidate, path) in self.composition_source_values(subject) {
            let Obj::FunctionSpace(FunctionSpace::Composition(value)) = &candidate else {
                continue;
            };
            let VerifyObjWellDefinedResult::Success(well_defined) =
                self.verify_obj_well_definedness(&candidate, state)?
            else {
                continue;
            };
            let (function, signature) =
                if let Some(function) = well_defined.composition_function()? {
                    (function.clone(), CompositionSignatureProof::Construction)
                } else {
                    let Some(inner_domain) = self
                        .complete_function_domains(&value.inner, state)?
                        .into_iter()
                        .find(|p| composition_arity(&p.signature) > 0)
                    else {
                        continue;
                    };
                    let Some(outer_domain) = self
                        .complete_function_domains(&value.outer, state)?
                        .into_iter()
                        .find(|p| composition_arity(&p.signature) == 1)
                    else {
                        continue;
                    };
                    let function = self.composition_function(
                        value,
                        &outer_domain.signature,
                        &inner_domain.signature,
                    )?;
                    (
                        function,
                        CompositionSignatureProof::Interfaces {
                            outer_domain: Box::new(outer_domain),
                            inner_domain: Box::new(inner_domain),
                        },
                    )
                };
            proofs.push(CompositionCallableProof {
                composition: value.clone(),
                function_equal: KnownEqualityPathProof::new(path),
                well_defined: CompositionWellDefinedPremise::Checked(Box::new(well_defined)),
                signature,
                function,
            });
        }
        Ok(proofs)
    }

    // Equality memory can legitimately contain f = compose(id, f). Such a
    // graph identity must not recursively rediscover itself as a definition.
    // Direct syntax is finite; alias candidates are admitted only when their
    // composition dependencies cannot return to the subject. This bounded,
    // read-only guard is private to this new source branch.
    pub(crate) fn composition_source_values(
        &self,
        subject: &Obj,
    ) -> Vec<(Obj, Vec<(Obj, Obj, FactId)>)> {
        if matches!(subject, Obj::FunctionSpace(FunctionSpace::Composition(_))) {
            return vec![(subject.clone(), vec![])];
        }
        self.exact_property_object_values(subject)
            .into_iter()
            .filter(|(candidate, _)| {
                let Obj::FunctionSpace(FunctionSpace::Composition(value)) = candidate else {
                    return false;
                };
                let mut visited = std::collections::HashSet::new();
                let mut remaining = 64;
                self.composition_dependency_avoids(
                    &value.outer,
                    subject,
                    &mut visited,
                    &mut remaining,
                ) && self.composition_dependency_avoids(
                    &value.inner,
                    subject,
                    &mut visited,
                    &mut remaining,
                )
            })
            .collect()
    }

    fn composition_dependency_avoids(
        &self,
        value: &Obj,
        subject: &Obj,
        visited: &mut std::collections::HashSet<String>,
        remaining: &mut usize,
    ) -> bool {
        if self.exact_property_equality_path(value, subject).is_some() {
            return false;
        }
        if !visited.insert(value.ir().to_string()) {
            return true;
        }
        if *remaining == 0 {
            return false;
        }
        *remaining -= 1;
        for (candidate, _) in self.exact_property_object_values(value) {
            if let Obj::FunctionSpace(FunctionSpace::Composition(comp)) = candidate {
                if !self.composition_dependency_avoids(&comp.outer, subject, visited, remaining)
                    || !self.composition_dependency_avoids(&comp.inner, subject, visited, remaining)
                {
                    return false;
                }
            }
        }
        true
    }

    /// Project a complete interface from an already checked atomic subject.
    /// Like parent-checked beta, this consumes the enclosing WD stage instead
    /// of attempting its compatibility proof again at the lower truth ceiling.
    /// Only builtin truth rules may call this entrypoint.
    pub(crate) fn parent_checked_composition_callables(
        &mut self,
        subject: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Vec<CompositionCallableProof>> {
        let mut proofs = Vec::new();
        for (candidate, path) in self.composition_source_values(subject) {
            let Obj::FunctionSpace(FunctionSpace::Composition(value)) = candidate else {
                continue;
            };
            let inner_domains =
                self.parent_checked_composition_operand_domains(&value.inner, state)?;
            for inner_domain in inner_domains {
                if composition_arity(&inner_domain.signature) == 0 {
                    continue;
                }
                let Some(outer_domain) = self
                    .parent_checked_composition_operand_domains(&value.outer, state)?
                    .into_iter()
                    .find(|p| composition_arity(&p.signature) == 1)
                else {
                    continue;
                };
                let function = self.composition_function(
                    &value,
                    &outer_domain.signature,
                    &inner_domain.signature,
                )?;
                proofs.push(CompositionCallableProof {
                    composition: value.clone(),
                    function_equal: KnownEqualityPathProof::new(path.clone()),
                    well_defined: CompositionWellDefinedPremise::ParentAtomic,
                    signature: CompositionSignatureProof::Interfaces {
                        outer_domain: Box::new(outer_domain),
                        inner_domain: Box::new(inner_domain),
                    },
                    function,
                });
            }
        }
        Ok(proofs)
    }

    fn parent_checked_composition_operand_domains(
        &mut self,
        subject: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Vec<CompleteFunctionDomainProof>> {
        let composed = self.parent_checked_composition_callables(subject, state)?;
        if !composed.is_empty() {
            return Ok(composed
                .into_iter()
                .map(|proof| CompleteFunctionDomainProof {
                    signature: proof.function.body.clone(),
                    source: CompleteFunctionDomainSourceProof::Composition(Box::new(proof)),
                })
                .collect());
        }
        self.complete_function_domains(subject, state)
    }

    fn composition_function(
        &mut self,
        value: &Composition,
        outer: &FnSet,
        inner: &FnSet,
    ) -> RuntimeResult<AnonymousFn> {
        let mut signature = inner.clone();
        let mut arguments = Vec::new();
        let mut substitution = HashMap::new();
        for group in &mut signature.set_bound_parameters.groups {
            for parameter in &mut group.params {
                let fresh = self.fresh_internal_param();
                let argument = Obj::Identifier(IdentifierObj::from_bound_name(&fresh));
                substitution.insert(parameter.id, argument.clone());
                arguments.push(Box::new(argument));
                *parameter = fresh;
            }
        }
        for guard in &mut signature.dom_facts {
            *guard = self
                .inst_quantifier_free_fact(guard, &substitution)
                .map_err(|error| {
                    RuntimeError::InternalBug(format!("composition guard substitution: {error}"))
                })?;
        }
        signature.ret_set = outer.ret_set.clone();
        let inner_call =
            function_application(&value.inner, arguments).map_err(RuntimeError::InternalBug)?;
        let body = function_application(&value.outer, vec![Box::new(inner_call)])
            .map_err(RuntimeError::InternalBug)?;
        Ok(AnonymousFn {
            body: signature,
            equal_to: Box::new(body),
        })
    }
}

pub(crate) fn composition_arity(signature: &FnSet) -> usize {
    signature
        .set_bound_parameters
        .groups
        .iter()
        .map(|g| g.params.len())
        .sum()
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/function_composition/tests.rs"]
mod function_composition_tests;
