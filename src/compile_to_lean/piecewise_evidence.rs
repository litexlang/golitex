use crate::execute::{
    ExecHaveFnEqualCaseByCaseStmtSuccessResult, HaveFnCaseReturnCheckSuccess,
    HaveFnCasesCoverageSuccess, HaveFnCasesDisjointSuccess, IntroduceFnSetClauseBindersResult,
};
use crate::prelude::*;

/// Borrow one actual local result scope. No facts or WD evidence are copied.
#[derive(Clone, Copy)]
pub(super) enum PiecewiseEvidence<'a> {
    Coverage(
        &'a ExecHaveFnEqualCaseByCaseStmtSuccessResult,
        &'a HaveFnCasesCoverageSuccess,
    ),
    Disjoint(
        &'a ExecHaveFnEqualCaseByCaseStmtSuccessResult,
        &'a HaveFnCasesDisjointSuccess,
    ),
    Return(
        &'a ExecHaveFnEqualCaseByCaseStmtSuccessResult,
        &'a HaveFnCaseReturnCheckSuccess,
    ),
}

impl<'a> PiecewiseEvidence<'a> {
    pub fn declaration(self) -> &'a ExecHaveFnEqualCaseByCaseStmtSuccessResult {
        match self {
            Self::Coverage(p, _) | Self::Disjoint(p, _) | Self::Return(p, _) => p,
        }
    }

    pub fn introduction(self) -> &'a IntroduceFnSetClauseBindersResult {
        match self {
            Self::Coverage(_, p) => &p.binder_introduction,
            Self::Disjoint(_, p) => &p.binder_introduction,
            Self::Return(_, p) => &p.binder_introduction,
        }
    }

    pub fn env(self) -> &'a crate::exec_env::ExecEnv {
        match self {
            Self::Coverage(_, p) => &p.local_env,
            Self::Disjoint(_, p) => &p.local_env,
            Self::Return(_, p) => &p.local_env,
        }
    }

    pub fn assumption(self) -> Option<&'a StoreFactAndInferResult> {
        match self {
            Self::Coverage(..) => None,
            Self::Disjoint(_, p) => Some(&p.assumption_stored),
            Self::Return(_, p) => Some(&p.assumption_stored),
        }
    }

    pub fn stores(self) -> impl Iterator<Item = &'a StoreFactAndInferResult> {
        let head = self.introduction();
        head.defined_params
            .store_and_infer_results
            .iter()
            .map(|s| s.as_ref())
            .chain(head.assumed_dom_facts.iter())
            .chain(self.assumption())
    }

    pub fn head_len(self) -> usize {
        let head = self.introduction();
        head.defined_params.store_and_infer_results.len() + head.assumed_dom_facts.len()
    }

    pub fn parameter(
        self,
        id: IdentifierId,
        before: usize,
    ) -> Option<(&'a BoundName, Option<&'a Obj>, &'a StoreFactAndInferResult)> {
        self.declaration()
            .statement
            .fn_set_clause
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, g.param_type.as_ref())))
            .zip(&self.introduction().defined_params.store_and_infer_results)
            .take(before)
            .find_map(|((p, carrier), store)| {
                (p.id == id).then_some((p, Some(carrier), store.as_ref()))
            })
    }

    pub fn same_scope(self, other: Self) -> bool {
        match (self, other) {
            (Self::Coverage(a, x), Self::Coverage(b, y)) => {
                std::ptr::eq(a, b) && std::ptr::eq(x, y)
            }
            (Self::Disjoint(a, x), Self::Disjoint(b, y)) => {
                std::ptr::eq(a, b) && std::ptr::eq(x, y)
            }
            (Self::Return(a, x), Self::Return(b, y)) => std::ptr::eq(a, b) && std::ptr::eq(x, y),
            _ => false,
        }
    }
}
