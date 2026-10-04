//! Bounded beta substitution inside one function-definition equality route.
//! This expands stored mathematical bodies, never algorithms or proof search.

use crate::ast::obj::{AnonymousFn, ArithmeticOperator, FnObj, FnObjHead, FunctionSpace, Obj};
use crate::ast::stmt::TemplateDefEnum;
use crate::execute::execute_fact_stmt::{ObjWellDefinedProof, VerifyObjWellDefinedResult, VerifyState};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::runtime::{Runtime, RuntimeResult};
use super::super::helper::{set_bound_parameter_count, set_bound_params_to_arg_map};

const MAX_BODY_EXPANSIONS: usize = 64;

pub struct FunctionBodyNormalizationProof {
    // Chronological substitutions; argument substitutions precede their caller.
    pub expansions: Vec<FunctionBodyExpansionProof>,
    pub expanded_body: Obj,
}

pub struct FunctionBodyExpansionProof {
    pub application: Obj,
    pub application_well_defined: ObjWellDefinedProof,
    pub function_body: FunctionBodySourceProof,
    // Check the selected body's own carrier and guard, even if its name also
    // has another callable signature. The literal WD retains its binder env.
    pub body_application_well_defined: ObjWellDefinedProof,
    pub expanded_body: Obj,
    pub continued_body: Obj,
}

pub enum FunctionBodySourceProof {
    KnownEquality(KnownEqualityPathProof),
    Template {
        instance: Obj,
        instantiated_function: AnonymousFn,
    },
}

impl Runtime {
    pub(crate) fn normalize_function_body(
        &mut self,
        obj: &Obj,
        stop_at: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<FunctionBodyNormalizationProof>> {
        let mut expansions = Vec::new();
        let Some(expanded_body) = self.normalize_function_body_rec(
            obj,
            stop_at,
            state,
            0,
            &mut expansions,
            &mut Vec::new(),
        )?
        else {
            return Ok(None);
        };
        if expansions.is_empty() {
            return Ok(None);
        }
        Ok(Some(FunctionBodyNormalizationProof {
            expansions,
            expanded_body,
        }))
    }

    fn normalize_function_body_rec(
        &mut self,
        obj: &Obj,
        stop_at: &Obj,
        state: VerifyState,
        depth: usize,
        expansions: &mut Vec<FunctionBodyExpansionProof>,
        active_heads: &mut Vec<FnObjHead>,
    ) -> RuntimeResult<Option<Obj>> {
        if depth > MAX_BODY_EXPANSIONS {
            return Ok(None);
        }
        if obj == stop_at {
            return Ok(Some(obj.clone()));
        }
        match obj {
            Obj::FnObj(call) => {
                if call.body.is_empty() || active_heads.contains(call.head.as_ref()) {
                    return Ok(None);
                }
                let mut normalized_call = call.clone();
                // Normalize arguments before entering the body, so nested uses
                // such as step(step(2)) are finite ordinary applications.
                for (group, original_group) in normalized_call.body.iter_mut().zip(&call.body) {
                    for (arg, original_arg) in group.iter_mut().zip(original_group) {
                        let Some(value) = self.normalize_function_body_rec(
                            original_arg,
                            stop_at,
                            state,
                            depth + 1,
                            expansions,
                            active_heads,
                        )?
                        else {
                            return Ok(None);
                        };
                        **arg = value;
                    }
                }
                let prefix = FnObj {
                    head: normalized_call.head.clone(),
                    body: vec![normalized_call.body[0].clone()],
                };
                let Some(step) = self.checked_function_body_expansion(&prefix, state)? else {
                    return Ok(Some(Obj::FnObj(normalized_call)));
                };
                if expansions.len() >= MAX_BODY_EXPANSIONS {
                    return Ok(None);
                }
                let Some(continued_body) = append_function_argument_groups(
                    &step.expanded_body,
                    &normalized_call.body[1..],
                ) else {
                    return Ok(None);
                };
                let mut step = step;
                step.continued_body = continued_body.clone();
                expansions.push(step);
                active_heads.push(call.head.as_ref().clone());
                let result = self.normalize_function_body_rec(
                    &continued_body,
                    stop_at,
                    state,
                    depth + 1,
                    expansions,
                    active_heads,
                );
                active_heads.pop();
                result
            }
            Obj::ArithmeticOperator(op) => {
                let mut rebuilt = op.clone();
                let children: Vec<&mut Box<Obj>> = match &mut rebuilt {
                    ArithmeticOperator::Add(v) => vec![&mut v.left, &mut v.right],
                    ArithmeticOperator::Sub(v) => vec![&mut v.left, &mut v.right],
                    ArithmeticOperator::Mul(v) => vec![&mut v.left, &mut v.right],
                    ArithmeticOperator::Div(v) => vec![&mut v.left, &mut v.right],
                    ArithmeticOperator::Pow(v) => vec![&mut v.base, &mut v.exponent],
                    ArithmeticOperator::Min(v) => vec![&mut v.left, &mut v.right],
                    ArithmeticOperator::Max(v) => vec![&mut v.left, &mut v.right],
                    ArithmeticOperator::Neg(v) => vec![&mut v.arg],
                    ArithmeticOperator::Abs(v) => vec![&mut v.arg],
                    ArithmeticOperator::Floor(v) => vec![&mut v.arg],
                    ArithmeticOperator::Ceil(v) => vec![&mut v.arg],
                    ArithmeticOperator::Sign(v) => vec![&mut v.arg],
                };
                for child in children {
                    let Some(value) = self.normalize_function_body_rec(
                        child,
                        stop_at,
                        state,
                        depth + 1,
                        expansions,
                        active_heads,
                    )?
                    else {
                        return Ok(None);
                    };
                    **child = value;
                }
                Ok(Some(Obj::ArithmeticOperator(rebuilt)))
            }
            // Function values and binders remain values. Do not substitute
            // inside their unevaluated bodies or open new proof permissions.
            _ => Ok(Some(obj.clone())),
        }
    }

    fn checked_function_body_expansion(
        &mut self,
        prefix: &FnObj,
        state: VerifyState,
    ) -> RuntimeResult<Option<FunctionBodyExpansionProof>> {
        let application = Obj::FnObj(prefix.clone());
        let application_well_defined =
            match self.verify_obj_well_definedness(&application, state)? {
                VerifyObjWellDefinedResult::Success(p) => p,
                VerifyObjWellDefinedResult::Failed { .. } => return Ok(None),
            };
        let args: Vec<Obj> = prefix.body[0].iter().map(|a| a.as_ref().clone()).collect();
        let candidates = self.function_body_candidates(prefix)?;
        for (anon, function_body) in candidates {
            if args.len() != set_bound_parameter_count(&anon.body.set_bound_parameters) {
                continue;
            }
            let literal_application = Obj::FnObj(FnObj {
                head: Box::new(FnObjHead::AnonymousFnLiteral(Box::new(anon.clone()))),
                body: prefix.body.clone(),
            });
            let body_application_well_defined =
                match self.verify_obj_well_definedness(&literal_application, state)? {
                    VerifyObjWellDefinedResult::Success(p) => p,
                    VerifyObjWellDefinedResult::Failed { .. } => continue,
                };
            let subst = set_bound_params_to_arg_map(&anon.body.set_bound_parameters, &args);
            let Ok(expanded_body) = self.inst_obj(anon.equal_to.as_ref(), &subst) else {
                continue;
            };
            return Ok(Some(FunctionBodyExpansionProof {
                application,
                application_well_defined,
                function_body,
                body_application_well_defined,
                continued_body: expanded_body.clone(),
                expanded_body,
            }));
        }
        Ok(None)
    }

    fn function_body_candidates(
        &mut self,
        prefix: &FnObj,
    ) -> RuntimeResult<Vec<(AnonymousFn, FunctionBodySourceProof)>> {
        let head = match prefix.head.as_ref() {
            FnObjHead::Identifier(v) => Obj::Identifier(v.clone()),
            FnObjHead::AnonymousFnLiteral(v) => {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(v.as_ref().clone()))
            }
            FnObjHead::FieldAccess(_) => return Ok(Vec::new()),
            FnObjHead::InstantiatedTemplateObj(inst) => {
                let Some(def) = self.def_template_visible(&inst.template_name) else {
                    return Ok(Vec::new());
                };
                let TemplateDefEnum::HaveFnEqualStmt(have_fn) = &def.template_def_stmt else {
                    return Ok(Vec::new());
                };
                let ids = def.template_arg_def.ordered_param_ids();
                if ids.len() != inst.args.len() {
                    return Ok(Vec::new());
                }
                let subst = ids.into_iter().zip(inst.args.iter().cloned()).collect();
                let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(
                    have_fn.equal_to_anonymous_fn.clone(),
                ));
                let Ok(Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon))) =
                    self.inst_obj(&literal, &subst)
                else {
                    return Ok(Vec::new());
                };
                return Ok(vec![(
                    anon.clone(),
                    FunctionBodySourceProof::Template {
                        instance: Obj::InstantiatedTemplateObj(inst.clone()),
                        instantiated_function: anon,
                    },
                )]);
            }
        };
        Ok(equivalence_class_members_with_paths_in_adjacency(
            &self.visible_equivalence_class_adjacency(),
            &head,
        )
        .into_iter()
        .filter_map(|(candidate, path)| {
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = candidate else {
                return None;
            };
            Some((
                anon,
                FunctionBodySourceProof::KnownEquality(KnownEqualityPathProof::new(path)),
            ))
        })
        .collect())
    }
}

fn append_function_argument_groups(body: &Obj, groups: &[Vec<Box<Obj>>]) -> Option<Obj> {
    if groups.is_empty() {
        return Some(body.clone());
    }
    let head = match body {
        Obj::Identifier(v) => FnObjHead::Identifier(v.clone()),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(v)) => {
            FnObjHead::AnonymousFnLiteral(Box::new(v.clone()))
        }
        Obj::InstantiatedTemplateObj(v) => FnObjHead::InstantiatedTemplateObj(v.clone()),
        Obj::FnObj(v) => {
            let mut call = v.clone();
            call.body.extend_from_slice(groups);
            return Some(Obj::FnObj(call));
        }
        _ => return None,
    };
    Some(Obj::FnObj(FnObj {
        head: Box::new(head),
        body: groups.to_vec(),
    }))
}
