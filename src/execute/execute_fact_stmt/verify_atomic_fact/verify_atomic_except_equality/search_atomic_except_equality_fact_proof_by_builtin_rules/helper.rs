//! Actual source-direction evidence for elementary function order builtin leaves.
use crate::ast::fact::{Fact, GreaterEqualFact, GreaterFact, LessEqualFact, LessFact};
use crate::ast::obj::Obj;
use crate::ast::line_file::SourceLine;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};
use crate::prelude::*;

impl Runtime {
    pub(super) fn strict_order_premise(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: Option<SourceLine>,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        let premise: Fact = LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&premise, state)?;
        if !proof.is_failed() {
            return Ok(Some(proof));
        }
        // Keep the actual reverse-written fact and citation, without requesting
        // a builtin direction conversion below the parent premise ceiling.
        let reverse: Fact = GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: right.clone(),
            right: left.clone(),
            line_file: line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&reverse, state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(proof))
    }

    pub(super) fn weak_order_premise(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: Option<SourceLine>,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        let premise: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&premise, state)?;
        if !proof.is_failed() {
            return Ok(Some(proof));
        }
        // Keep the actual reverse-written fact and citation, without requesting
        // a builtin direction conversion below the parent premise ceiling.
        let reverse: Fact = GreaterEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: right.clone(),
            right: left.clone(),
            line_file: line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&reverse, state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(proof))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum BinaryExtremumKind {
    Minimum,
    Maximum,
}

// A binary extremum has the same operands whether written min(a,b) or as
// the extremum of union({a},{b}). This is only a structural view: parent WD
// must check real members, finiteness, nonemptiness and list distinctness.
pub(super) fn binary_extremum_operands(obj: &Obj) -> Option<(BinaryExtremumKind, &Obj, &Obj)> {
    let (kind, set) = match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Min(value)) => {
            return Some((BinaryExtremumKind::Minimum, &value.left, &value.right));
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Max(value)) => {
            return Some((BinaryExtremumKind::Maximum, &value.left, &value.right));
        }
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(value)) =>
            (BinaryExtremumKind::Minimum, &*value.set),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(value)) =>
            (BinaryExtremumKind::Maximum, &*value.set),
        _ => return None,
    };
    match set {
        Obj::SetOperator(SetOperator::Union(union)) => {
            let (Obj::SetFormer(SetFormer::ListSet(left)), Obj::SetFormer(SetFormer::ListSet(right))) =
                (&*union.left, &*union.right) else { return None; };
            if left.list.len() == 1 && right.list.len() == 1 {
                Some((kind, &left.list[0], &right.list[0]))
            } else { None }
        }
        Obj::SetFormer(SetFormer::ListSet(list)) if list.list.len() == 2 =>
            Some((kind, &list.list[0], &list.list[1])),
        _ => None,
    }
}
