//! Unordered reduction requires commutativity and associativity on its carrier.
//! Checked beta equations expose small algebraic leaves without extra fuel.
use crate::ast::fact::{AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact};
use crate::ast::obj::{
    FnObj, FnObjHead, FunctionSpace, IdentifierObj, Obj, StructAndFieldAccessObj,
};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn unordered_fold_laws(
        &mut self,
        op: &Obj,
        carrier: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Vec<VerifyFactResult>> {
        let a = self.fresh_internal_param();
        let b = self.fresh_internal_param();
        let c = self.fresh_internal_param();
        let x = Obj::Identifier(IdentifierObj::from_bound_name(&a));
        let y = Obj::Identifier(IdentifierObj::from_bound_name(&b));
        let z = Obj::Identifier(IdentifierObj::from_bound_name(&c));
        let Some(xy) = apply(op, vec![x.clone(), y.clone()]) else {
            return Ok(vec![]);
        };
        let yx = apply(op, vec![y.clone(), x.clone()]).expect("same callable");
        let mut comm_steps = Vec::new();
        if let (Some(u), Some(v)) = (
            self.unordered_fold_body(&xy)?,
            self.unordered_fold_body(&yx)?,
        ) {
            for (left, right) in [(xy.clone(), u.clone()), (yx.clone(), v.clone()), (u, v)] {
                comm_steps.push(self.unordered_fold_equal(left, right));
            }
        }
        comm_steps.push(self.unordered_fold_equal(xy.clone(), yx));
        let comm = Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![a.clone(), b.clone()],
                    param_type: ParamType::Obj(carrier.clone()),
                }],
            },
            dom_facts: vec![],
            then_facts: comm_steps,
            line_file: None,
        });
        let mut law_state = state;
        law_state = law_state.without_rewrite();
        let comm = self.verify_fact(&comm, law_state.clone())?;
        if comm.is_failed() {
            return Ok(vec![comm]);
        }
        let yz = apply(op, vec![y.clone(), z.clone()]).expect("same callable");
        let left = apply(op, vec![xy.clone(), z.clone()]).expect("same callable");
        let right = apply(op, vec![x.clone(), yz.clone()]).expect("same callable");
        let mut assoc_steps = Vec::new();
        if let (Some(u), Some(v)) = (
            self.unordered_fold_body(&xy)?,
            self.unordered_fold_body(&yz)?,
        ) {
            let lapp = apply(op, vec![u.clone(), z]).expect("same callable");
            let rapp = apply(op, vec![x, v.clone()]).expect("same callable");
            if let (Some(l), Some(r)) = (
                self.unordered_fold_body(&lapp)?,
                self.unordered_fold_body(&rapp)?,
            ) {
                for (a, b) in [
                    (xy, u),
                    (yz, v),
                    (left.clone(), lapp.clone()),
                    (lapp, l.clone()),
                    (right.clone(), rapp.clone()),
                    (rapp, r.clone()),
                    (l, r),
                ] {
                    assoc_steps.push(self.unordered_fold_equal(a, b));
                }
            }
        }
        assoc_steps.push(self.unordered_fold_equal(left, right));
        let assoc = Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![a, b, c],
                    param_type: ParamType::Obj(carrier.clone()),
                }],
            },
            dom_facts: vec![],
            then_facts: assoc_steps,
            line_file: None,
        });
        Ok(vec![comm, self.verify_fact(&assoc, law_state)?])
    }
    fn unordered_fold_body(&mut self, obj: &Obj) -> RuntimeResult<Option<Obj>> {
        let Obj::FnObj(f) = obj else {
            return Ok(None);
        };
        Ok(self
            .expanded_named_or_literal_anon_fn_application_body(f)?
            .map(|p| p.expanded_body))
    }
    fn unordered_fold_equal(&mut self, left: Obj, right: Obj) -> ExistOrAndChainAtomicFact {
        ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file: None,
        }))
    }
}
fn apply(op: &Obj, args: Vec<Obj>) -> Option<Obj> {
    let (head, mut body) = match op {
        Obj::Identifier(id) => (FnObjHead::Identifier(id.clone()), vec![]),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(a)) => {
            (FnObjHead::AnonymousFnLiteral(Box::new(a.clone())), vec![])
        }
        Obj::FnObj(f) => (f.head.as_ref().clone(), f.body.clone()),
        Obj::InstantiatedTemplateObj(t) => (FnObjHead::InstantiatedTemplateObj(t.clone()), vec![]),
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(f)) => {
            (FnObjHead::FieldAccess(f.clone()), vec![])
        }
        _ => return None,
    };
    body.push(args.into_iter().map(Box::new).collect());
    Some(Obj::FnObj(FnObj {
        head: Box::new(head),
        body,
    }))
}
