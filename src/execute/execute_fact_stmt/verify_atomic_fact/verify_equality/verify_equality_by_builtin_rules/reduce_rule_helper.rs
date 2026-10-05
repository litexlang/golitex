//! Checked primitives owned by the ordered-fold rules; no truth-stage escalation.
use crate::ast::fact::{EqualFact, Fact, LessEqualFact};
use crate::ast::obj::{FnObj, FnObjHead, FunctionSpace, Obj, StructAndFieldAccessObj};
use crate::execute::execute_eval_stmt::evaluate_aggregate::unary_application;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_equal::AnonFnApplicationBodyProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::exact_rational::EvalRational;
use crate::rational_expression::NumberCompareResult;
use crate::runtime::{Runtime, RuntimeResult};

pub struct ReduceObjectMatchProof {
    pub left: Obj,
    pub right: Obj,
    pub method: ReduceObjectMatchMethod,
}
pub enum ReduceObjectMatchMethod {
    SameIr,
    RationalNormalization,
    KnownEquality(Box<EqualFactSearchedProof>),
    ApplicationArguments(Vec<ReduceObjectMatchProof>),
}
pub enum ReduceNonemptyProof {
    Known(VerifyFactResult),
    ClosedIntegerComparison { start: Obj, end: Obj },
}

impl Runtime {
    pub(super) fn match_reduce_object(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> Option<ReduceObjectMatchProof> {
        self.match_reduce_object_at_depth(left, right, 0)
    }

    fn match_reduce_object_at_depth(
        &mut self,
        left: &Obj,
        right: &Obj,
        depth: usize,
    ) -> Option<ReduceObjectMatchProof> {
        if depth > 64 {
            return None;
        }
        let method = if left.ir() == right.ir() {
            ReduceObjectMatchMethod::SameIr
        } else if crate::rational_expression::objs_equal_by_rational_expression_evaluation(
            left, right,
        ) {
            ReduceObjectMatchMethod::RationalNormalization
        } else if let Some(proof) = self.lookup_known_obj_equality(left, right) {
            ReduceObjectMatchMethod::KnownEquality(Box::new(proof))
        } else if let (Obj::FnObj(a), Obj::FnObj(b)) = (left, right) {
            // Congruence of the same callable, with independently checked arguments.
            let ah = Obj::FnObj(FnObj {
                head: a.head.clone(),
                body: vec![],
            });
            let bh = Obj::FnObj(FnObj {
                head: b.head.clone(),
                body: vec![],
            });
            if ah.ir() != bh.ir() || a.body.len() != b.body.len() {
                return None;
            }
            let mut arguments = Vec::new();
            for (xs, ys) in a.body.iter().zip(&b.body) {
                if xs.len() != ys.len() {
                    return None;
                }
                for (x, y) in xs.iter().zip(ys) {
                    arguments.push(self.match_reduce_object_at_depth(x, y, depth + 1)?);
                }
            }
            ReduceObjectMatchMethod::ApplicationArguments(arguments)
        } else {
            return None;
        };
        Some(ReduceObjectMatchProof {
            left: left.clone(),
            right: right.clone(),
            method,
        })
    }

    pub(super) fn reduce_nonempty_proof(
        &mut self,
        start: &Obj,
        end: &Obj,
        parent: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ReduceNonemptyProof>> {
        // The enclosing Reduce WD has checked integral endpoints. Exact closed
        // comparison is a primitive of this rule, not another builtin search.
        if let (Some(a), Some(b)) = (EvalRational::from_obj(start), EvalRational::from_obj(end)) {
            if matches!(
                a.compare(&b),
                Some(NumberCompareResult::Less | NumberCompareResult::Equal)
            ) {
                return Ok(Some(ReduceNonemptyProof::ClosedIntegerComparison {
                    start: start.clone(),
                    end: end.clone(),
                }));
            }
            return Ok(None);
        }
        let goal: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: start.clone(),
            right: end.clone(),
            line_file: parent.line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&goal, state)?;
        Ok(if proof.is_failed() {
            None
        } else {
            Some(ReduceNonemptyProof::Known(proof))
        })
    }
}

pub(in crate::execute::execute_fact_stmt::verify_atomic_fact) fn reduce_application(function: &Obj, args: Vec<Obj>) -> Option<Obj> {
    let (head, mut body) = match function {
        Obj::Identifier(id) => (FnObjHead::Identifier(id.clone()), vec![]),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(a)) => {
            (FnObjHead::AnonymousFnLiteral(Box::new(a.clone())), vec![])
        }
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(f)) => {
            (FnObjHead::FieldAccess(f.clone()), vec![])
        }
        Obj::InstantiatedTemplateObj(t) => (FnObjHead::InstantiatedTemplateObj(t.clone()), vec![]),
        Obj::FnObj(f) => (f.head.as_ref().clone(), f.body.clone()),
        _ => return None,
    };
    body.push(args.into_iter().map(Box::new).collect());
    Some(Obj::FnObj(FnObj {
        head: Box::new(head),
        body,
    }))
}

pub(super) fn reduce_function_at(
    rt: &mut Runtime,
    function: &Obj,
    index: &Obj,
    expansions: &mut Vec<AnonFnApplicationBodyProof>,
) -> RuntimeResult<Option<Obj>> {
    let Some(call) = unary_application(function, index.clone()) else {
        return Ok(None);
    };
    if let Some(expansion) = rt.expanded_named_or_literal_anon_fn_application_body(&call)? {
        let body = expansion.expanded_body.clone();
        expansions.push(expansion);
        Ok(Some(body))
    } else {
        Ok(Some(Obj::FnObj(call)))
    }
}
