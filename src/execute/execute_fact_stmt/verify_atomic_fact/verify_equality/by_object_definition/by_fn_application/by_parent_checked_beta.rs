//! Beta substitution using the parent's checked application domain.

use crate::ast::fact::EqualFact;
use crate::ast::obj::{AnonymousFn, FnObjHead, FnSet, FunctionSpace, Obj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::runtime::{Runtime, RuntimeResult};
use crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal;
use crate::execute::execute_fact_stmt::ObjWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{FnObjDomainFnSetEvidence, ObjWellDefinedProofByDef};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;

use super::super::helper::{set_bound_parameter_count, set_bound_params_to_arg_map};

pub enum ByParentCheckedBetaObjectDefinitionProof {
    OneSide(ParentCheckedBetaOneSideProof),
    TwoSides(ParentCheckedBetaTwoSidesProof),
}

pub struct ParentCheckedBetaOneSideProof {
    pub parent_well_defined_side: ParentEqualitySide,
    pub function_body: ParentCheckedBetaFunctionBody,
    pub expanded_body: Obj,
    pub residual_equal: EqualFact,
    pub residual_proof: Box<EqualFactSearchedProof>,
}

pub struct ParentCheckedBetaTwoSidesProof {
    pub left_function_body: ParentCheckedBetaFunctionBody,
    pub left_expanded_body: Obj,
    pub right_function_body: ParentCheckedBetaFunctionBody,
    pub right_expanded_body: Obj,
    pub residual_equal: EqualFact,
    pub residual_proof: Box<EqualFactSearchedProof>,
}

pub enum ParentCheckedBetaFunctionBody {
    KnownFiniteFunctionCoordinate {
        source: Box<crate::execute::execute_fact_stmt::finite_function::FiniteFunctionSignatureProof>,
        index: usize,
    },
    AnonymousLiteral,
    KnownAnonymousFunction {
        function: AnonymousFn,
        function_equal: KnownEqualityPathProof,
        checked_domain: FnSet,
    },
}

pub enum ParentEqualitySide {
    Left,
    Right,
}

impl Runtime {
    pub(in crate::execute) fn try_parent_checked_beta_with_parent_well_definedness(
        &mut self,
        fact: &EqualFact,
        parent_wd: &EqualFactWellDefinedProof,
        state: VerifyState,
    ) -> RuntimeResult<Option<ByParentCheckedBetaObjectDefinitionProof>> {
        let Some(child) = state.for_premises(VerifyStateLevel::DefinitionAndForall) else {
            return Ok(None);
        };
        if parent_wd.left.obj() != &fact.left || parent_wd.right.obj() != &fact.right {
            return Ok(None);
        }
        if let (Some((left_function_body, left_expanded_body)), Some((right_function_body, right_expanded_body))) = (
            self.parent_checked_beta_body(&fact.left, &parent_wd.left)?,
            self.parent_checked_beta_body(&fact.right, &parent_wd.right)?,
        ) {
            let residual_equal = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(), left: left_expanded_body.clone(),
                right: right_expanded_body.clone(), line_file: fact.line_file.clone(),
            };
            if let Some(residual_proof) = self.search_equal_fact_proof(&residual_equal, child)? {
                return Ok(Some(ByParentCheckedBetaObjectDefinitionProof::TwoSides(ParentCheckedBetaTwoSidesProof {
                    left_function_body, left_expanded_body, right_function_body, right_expanded_body,
                    residual_equal, residual_proof: Box::new(residual_proof),
                })));
            }
        }
        for (app_side, other_side, app_wd, side) in [
            (&fact.left, &fact.right, &parent_wd.left, ParentEqualitySide::Left),
            (&fact.right, &fact.left, &parent_wd.right, ParentEqualitySide::Right),
        ] {
            let Some((function_body, expanded_body)) = self.parent_checked_beta_body(app_side, app_wd)?
            else { continue; };
            let residual_equal = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: expanded_body.clone(), right: other_side.clone(), line_file: fact.line_file.clone(),
            };
            // Both arguments and guards were checked by the parent; only the
            // residual truth uses the ordinary restricted definition ceiling.
            let Some(residual_proof) = self.search_equal_fact_proof(&residual_equal, child)? else { continue; };
            return Ok(Some(ByParentCheckedBetaObjectDefinitionProof::OneSide(ParentCheckedBetaOneSideProof {
                parent_well_defined_side: side, function_body, expanded_body,
                residual_equal, residual_proof: Box::new(residual_proof),
            })));
        }
        Ok(None)
    }

    fn parent_checked_beta_body(
        &mut self, side: &Obj, app_wd: &ObjWellDefinedProof,
    ) -> RuntimeResult<Option<(ParentCheckedBetaFunctionBody, Obj)>> {
            let Obj::FnObj(app) = side else { return Ok(None); };
            if let Some(receiver) = self.finite_function_application_receiver(app) {
                if let Some(index) = crate::execute::execute_fact_stmt::known_tuple::literal_positive_usize(&app.body.last().unwrap()[0]) {
                    for source in self.finite_function_signatures(&receiver) {
                        let crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof::TupleEquality(value) = &source.source else { continue; };
                        let Some(coordinate) = value.value.args.get(index - 1) else { continue; };
                        let coordinate = coordinate.as_ref().clone();
                        return Ok(Some((ParentCheckedBetaFunctionBody::KnownFiniteFunctionCoordinate {
                            source: Box::new(source), index,
                        }, coordinate)));
                    }
                }
            }
            let (literal, function_body) = match app.head.as_ref() {
                FnObjHead::AnonymousFnLiteral(literal) =>
                    (literal.as_ref().clone(), ParentCheckedBetaFunctionBody::AnonymousLiteral),
                FnObjHead::Identifier(head) => {
                    // The actual parent application proof identifies the
                    // selected domain. Mere cached WD does not identify it.
                    let Some(checked_domain) = checked_application_domain(app_wd) else { return Ok(None); };
                    let peers = self.exact_property_object_values(&Obj::Identifier(head.clone()));
                    let Some((literal, path)) = peers.into_iter().find_map(|(peer, path)| {
                        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)) = peer else { return None; };
                        function_domains_alpha_equal(&literal.body, checked_domain).then_some((literal, path))
                    }) else { return Ok(None); };
                    let source = ParentCheckedBetaFunctionBody::KnownAnonymousFunction {
                        function: literal.clone(), function_equal: KnownEqualityPathProof::new(path),
                        checked_domain: checked_domain.clone(),
                    };
                    (literal, source)
                }
                _ => return Ok(None),
            };
            if app.body.len() != 1 {
                return Ok(None);
            }
            let args: Vec<Obj> = app.body[0].iter().map(|v| v.as_ref().clone()).collect();
            if args.len() != set_bound_parameter_count(&literal.body.set_bound_parameters) {
                return Ok(None);
            }
            let subst = set_bound_params_to_arg_map(&literal.body.set_bound_parameters, &args);
            let Ok(expanded_body) = self.inst_obj(literal.equal_to.as_ref(), &subst) else {
                return Ok(None);
            };
            Ok(Some((function_body, expanded_body)))
    }
}

fn checked_application_domain(proof: &ObjWellDefinedProof) -> Option<&FnSet> {
    let ObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::FnObj(proof), .. } = proof else {
        return None;
    };
    match proof.domain_fn_set.as_ref()? {
        FnObjDomainFnSetEvidence::FiniteFunction(source) => Some(&source.signature),
        FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }
        | FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }
        | FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. } => Some(fn_set),
    }
}
