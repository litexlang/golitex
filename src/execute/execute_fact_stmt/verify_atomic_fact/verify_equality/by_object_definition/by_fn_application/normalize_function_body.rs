//! Bounded beta substitution inside one function-definition equality route.
//! This expands stored mathematical bodies, never algorithms or proof search.

use crate::ast::obj::{AnonymousFn, ArithmeticOperator, FnObj, FnObjHead, FunctionSpace, Obj};
use crate::ast::stmt::TemplateDefEnum;
use crate::execute::execute_fact_stmt::{ObjWellDefinedProof, VerifyObjWellDefinedResult, VerifyState};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::runtime::{Runtime, RuntimeResult};
use crate::execute::execute_fact_stmt::finite_function::FiniteFunctionSignatureProof;
use crate::execute::execute_fact_stmt::known_tuple::{KnownTupleShapeProof, literal_positive_usize, tuple_function_head};
use super::super::helper::{set_bound_parameter_count, set_bound_params_to_arg_map};

const MAX_BODY_EXPANSIONS: usize = 64;

pub struct FunctionBodyNormalizationProof {
    // Chronological substitutions; argument substitutions precede their caller.
    pub expansions: Vec<FunctionBodyExpansionProof>,
    pub expanded_body: Obj,
}

pub enum FunctionBodyExpansionProof {
    Anonymous(AnonymousFunctionBodyExpansionProof),
    FiniteCoordinate(FiniteCoordinateBodyExpansionProof),
}

pub struct AnonymousFunctionBodyExpansionProof {
    pub application: Obj,
    pub application_well_defined: ObjWellDefinedProof,
    pub function_body: FunctionBodySourceProof,
    // Check the selected body's own carrier and guard, even if its name also
    // has another callable signature. The literal WD retains its binder env.
    pub body_application_well_defined: ObjWellDefinedProof,
    pub expanded_body: Obj,
    pub continued_body: Obj,
}

pub struct FiniteCoordinateBodyExpansionProof {
    pub application: Obj,
    pub application_well_defined: ObjWellDefinedProof,
    pub source: Box<FiniteFunctionSignatureProof>,
    pub index: usize,
    pub expanded_body: Obj,
    pub continued_body: Obj,
}

pub enum FunctionBodySourceProof {
    KnownEquality(KnownEqualityPathProof),
    Template {
        instance: Obj,
        instantiated_function: AnonymousFn,
        function_equal: KnownEqualityPathProof,
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
                // Preserve one-step beta equalities such as outer(inner(x)) =
                // inner(x)*inner(x), before normalizing their symbolic arguments.
                if call.body.len() == 1 {
                    if let Some(step) =
                        self.checked_function_body_expansion(call, state, Some(stop_at))?
                    {
                        if expansions.len() >= MAX_BODY_EXPANSIONS {
                            return Ok(None);
                        }
                        let body = step.expanded_body().clone();
                        expansions.push(step);
                        return Ok(Some(body));
                    }
                }
                let mut normalized_call = call.clone();
                // Normalize arguments before entering the body, so nested uses
                // such as step(step(2)) are finite ordinary applications.
                for (group, original_group) in normalized_call.body.iter_mut().zip(&call.body) {
                    for (arg, original_arg) in group.iter_mut().zip(original_group) {
                        let before_argument = expansions.len();
                        match self.normalize_function_body_rec(
                            original_arg,
                            stop_at,
                            state,
                            depth + 1,
                            expansions,
                            active_heads,
                        )? {
                            Some(value) => **arg = value,
                            None => {
                                // A checked function may ignore this argument.
                                // Retain it symbolically; discard incomplete beta
                                // evidence. If the body needs it, normalization
                                // will still encounter the cycle/budget boundary.
                                expansions.truncate(before_argument);
                            }
                        }
                    }
                }
                let prefix = FnObj {
                    head: normalized_call.head.clone(),
                    body: vec![normalized_call.body[0].clone()],
                };
                let Some(step) = self.checked_function_body_expansion(&prefix, state, None)? else {
                    return Ok(Some(Obj::FnObj(normalized_call)));
                };
                if expansions.len() >= MAX_BODY_EXPANSIONS {
                    return Ok(None);
                }
                let Some(continued_body) = append_function_argument_groups(
                    step.expanded_body(),
                    &normalized_call.body[1..],
                ) else {
                    return Ok(None);
                };
                let mut step = step;
                step.set_continued_body(continued_body.clone());
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
        expected_body: Option<&Obj>,
    ) -> RuntimeResult<Option<FunctionBodyExpansionProof>> {
        let application = Obj::FnObj(prefix.clone());
        let args: Vec<Obj> = prefix.body[0].iter().map(|a| a.as_ref().clone()).collect();
        // A finite graph's coordinate is a beta step before any later call.
        // Example: (f, 7)'s named value `p` gives p(1)(x) = f(x).
        if args.len() == 1 {
            if let Some(index) = literal_positive_usize(&args[0]) {
                for source in self.finite_function_signatures(&tuple_function_head(prefix)) {
                    let KnownTupleShapeProof::TupleEquality(value) = &source.source else { continue; };
                    let Some(coordinate) = value.value.args.get(index - 1) else { continue; };
                    let expanded_body = coordinate.as_ref().clone();
                    if expected_body.is_some_and(|expected| expected != &expanded_body) { continue; }
                    let application_well_defined = match self.verify_obj_well_definedness(&application, state)? {
                        VerifyObjWellDefinedResult::Success(proof) => proof,
                        VerifyObjWellDefinedResult::Failed { .. } => return Ok(None),
                    };
                    return Ok(Some(FunctionBodyExpansionProof::FiniteCoordinate(FiniteCoordinateBodyExpansionProof {
                        application, application_well_defined, source: Box::new(source), index,
                        continued_body: expanded_body.clone(), expanded_body,
                    })));
                }
            }
        }
        let candidates = self.function_body_candidates(prefix)?;
        for (anon, function_body) in candidates {
            if args.len() != set_bound_parameter_count(&anon.body.set_bound_parameters) {
                continue;
            }
            let subst = set_bound_params_to_arg_map(&anon.body.set_bound_parameters, &args);
            let Ok(expanded_body) = self.inst_obj(anon.equal_to.as_ref(), &subst) else {
                continue;
            };
            if expected_body.is_some_and(|expected| &expanded_body != expected) {
                continue;
            }
            let application_well_defined =
                match self.verify_obj_well_definedness(&application, state)? {
                    VerifyObjWellDefinedResult::Success(p) => p,
                    VerifyObjWellDefinedResult::Failed { .. } => return Ok(None),
                };
            let literal_application = Obj::FnObj(FnObj {
                head: Box::new(FnObjHead::AnonymousFnLiteral(Box::new(anon.clone()))),
                body: prefix.body.clone(),
            });
            let body_application_well_defined =
                match self.verify_obj_well_definedness(&literal_application, state)? {
                    VerifyObjWellDefinedResult::Success(p) => p,
                    VerifyObjWellDefinedResult::Failed { .. } => continue,
                };
            return Ok(Some(FunctionBodyExpansionProof::Anonymous(AnonymousFunctionBodyExpansionProof {
                application,
                application_well_defined,
                function_body,
                body_application_well_defined,
                continued_body: expanded_body.clone(),
                expanded_body,
            })));
        }
        Ok(None)
    }

    fn function_body_candidates(
        &mut self,
        prefix: &FnObj,
    ) -> RuntimeResult<Vec<(AnonymousFn, FunctionBodySourceProof)>> {
        let head = match prefix.head.as_ref() {
            FnObjHead::Object(obj) => obj.as_ref().clone(),
            FnObjHead::Identifier(v) => Obj::Identifier(v.clone()),
            FnObjHead::AnonymousFnLiteral(v) => {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(v.as_ref().clone()))
            }
            FnObjHead::FieldAccess(v) => Obj::StructAndFieldAccessObj(crate::ast::obj::StructAndFieldAccessObj::FieldAccess(v.clone())),
            FnObjHead::InstantiatedTemplateObj(inst) => Obj::InstantiatedTemplateObj(inst.clone()),
        };
        let mut candidates = Vec::new();
        for (candidate, path) in self.exact_property_object_values(&head) {
            match candidate {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => candidates.push((
                    anon, FunctionBodySourceProof::KnownEquality(KnownEqualityPathProof::new(path)),
                )),
                Obj::InstantiatedTemplateObj(instance) => {
                    let Some(def) = self.def_template_visible(&instance.template_name).cloned() else { continue; };
                    let TemplateDefEnum::HaveFnEqualStmt(have_fn) = &def.template_def_stmt else { continue; };
                    let ids = def.template_arg_def.ordered_param_ids();
                    if ids.len() != instance.args.len() { continue; }
                    let subst = ids.into_iter().zip(instance.args.iter().cloned()).collect();
                    let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(have_fn.equal_to_anonymous_fn.clone()));
                    let Ok(Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon))) = self.inst_obj(&literal, &subst) else { continue; };
                    candidates.push((anon.clone(), FunctionBodySourceProof::Template {
                        instance: Obj::InstantiatedTemplateObj(instance), instantiated_function: anon,
                        function_equal: KnownEqualityPathProof::new(path),
                    }));
                }
                _ => {}
            }
        }
        Ok(candidates)
    }
}

impl FunctionBodyExpansionProof {
    fn expanded_body(&self) -> &Obj {
        match self {
            Self::Anonymous(proof) => &proof.expanded_body,
            Self::FiniteCoordinate(proof) => &proof.expanded_body,
        }
    }

    fn set_continued_body(&mut self, body: Obj) {
        match self {
            Self::Anonymous(proof) => proof.continued_body = body,
            Self::FiniteCoordinate(proof) => proof.continued_body = body,
        }
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
