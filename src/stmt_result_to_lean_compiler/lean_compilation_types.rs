use crate::prelude::*;

/// Short-lived target choice used while a checked arithmetic Result is
/// rendered. This is compiler control data, not another proof IR.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LeanArithmeticBuiltinCompilationKind {
    AddNonnegative,
    AddPositive,
    AddPositiveLeftStrict,
    AddPositiveRightStrict,
    MulNonnegative,
    MulPositive,
    DivNonnegative,
    DivPositive,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LeanSetBuiltinCompilationKind {
    EmptySubset,
    SubsetTransitivity,
    UnionCommutative,
    UnionAssociative,
    UnionIdempotent,
    UnionEmptyIdentity,
    UnionSetMinusDecomposition,
    UnionAbsorptionFromSubset,
    IntersectCommutative,
    IntersectAssociative,
    IntersectIdempotent,
    IntersectSetMinusSelfEmpty,
    IntersectSetMinusDisjointFromSubset,
    SetMinusSelfEmpty,
    SetMinusEmptyRight,
    SetMinusEmptyLeft,
    SetMinusIntersectSelf,
    UnionMembershipLeft,
    UnionMembershipRight,
    IntersectMembershipBoth,
    SetMinusMembership,
    IntersectEqLeftOfSubset,
    IntersectEqRightOfSubset,
    IntersectFinite,
    IntersectSubsetLeft,
    IntersectSubsetRight,
    IntersectUnionDistributive,
    PowerSetFinite,
    PowerSetMembershipOfSubset,
    PowerSetNonempty,
    SetMinusFiniteLeft,
    SetMinusIntersectDeMorgan,
    SetMinusRecoverSubset,
    SetMinusSubsetLeft,
    SetMinusUnionDeMorgan,
    SubsetEqSetMinusRecovery,
    SubsetUnionLeft,
    SubsetUnionRight,
    UnionFinite,
    UnionNonemptyLeft,
    UnionNonemptyRight,
    UnionSubset,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LeanEqualityApplicationSide {
    Left,
    Right,
}

/// Exact local FactId/proposition pair visible in one compiler environment.
#[derive(Clone, Debug)]
pub(super) struct LeanLocalFactPremise {
    pub(super) fact_id: FactId,
    pub(super) fact: Fact,
}

impl LeanLocalFactPremise {
    pub(super) fn new(fact_id: FactId, fact: Fact) -> Self {
        Self { fact_id, fact }
    }
}

/// One short-lived target-language result produced while compiling a typed
/// inference application.
///
/// This is not another semantic IR. `fact_id` and `fact` come from the
/// canonical recursive `StmtResult`; the remaining fields are the exact Lean
/// names and source fragments constructed for that fact. Keeping them
/// together lets local proof blocks, anonymous-function bodies, and top-level
/// theorem publication consume the same compiled result without parsing a
/// rendered `have` statement back into semantic pieces.
#[derive(Clone, Debug)]
pub(super) struct CompiledInferenceFactProofStep {
    pub(super) fact_id: FactId,
    pub(super) fact: Fact,
    pub(super) local_lean_name: String,
    pub(super) proposition: String,
    pub(super) proof_expression: String,
}

/// How a compiled inference conclusion becomes available to later compiler
/// steps in the current Lean scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CompiledInferenceFactAvailabilityInLeanEnvironment {
    /// Later proof expressions cite a local `have`/`let` name. The enclosing
    /// caller is responsible for rendering the returned step first.
    LocalProofName,
    /// Later proof expressions directly contain the earlier proof expression.
    /// This is used while constructing terms that have no surrounding tactic
    /// block in which a local proof name could be declared.
    InlineProofExpression,
}

impl CompiledInferenceFactProofStep {
    pub(super) fn new(
        fact_id: FactId,
        fact: Fact,
        local_lean_name: String,
        proposition: String,
        proof_expression: String,
    ) -> Self {
        Self {
            fact_id,
            fact,
            local_lean_name,
            proposition,
            proof_expression,
        }
    }

    pub(super) fn render_as_local_have_statement(&self) -> String {
        format!(
            "have {} : {} := {}",
            self.local_lean_name, self.proposition, self.proof_expression
        )
    }

    pub(super) fn render_as_local_let_statement(&self) -> String {
        format!(
            "let {} : {} := {}",
            self.local_lean_name, self.proposition, self.proof_expression
        )
    }
}

pub(super) fn facts_are_comparison_notation_duals(source: &Fact, target: &Fact) -> bool {
    let (Fact::AtomicFact(source), Fact::AtomicFact(target)) = (source, target) else {
        return false;
    };
    let swapped = |source_left: &Obj, source_right: &Obj, target_left: &Obj, target_right: &Obj| {
        obj_equality_key(source_left) == obj_equality_key(target_right)
            && obj_equality_key(source_right) == obj_equality_key(target_left)
    };
    match (source, target) {
        (AtomicFact::LessFact(source), AtomicFact::GreaterFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::GreaterFact(source), AtomicFact::LessFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::LessEqualFact(source), AtomicFact::GreaterEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::GreaterEqualFact(source), AtomicFact::LessEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotLessFact(source), AtomicFact::NotGreaterFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotGreaterFact(source), AtomicFact::NotLessFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotLessEqualFact(source), AtomicFact::NotGreaterEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotGreaterEqualFact(source), AtomicFact::NotLessEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        _ => false,
    }
}

pub(super) fn fact_is_closed_numeric_relation(goal: &Fact) -> bool {
    let Fact::AtomicFact(atomic) = goal else {
        return false;
    };
    match atomic {
        AtomicFact::EqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::NotEqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::LessFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::GreaterFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::LessEqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::GreaterEqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::NotLessFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::NotGreaterFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::NotLessEqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::NotGreaterEqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        _ => false,
    }
}

fn object_is_closed_rational_expression(object: &Obj) -> bool {
    match object {
        Obj::Number(_) => true,
        Obj::Add(value) => {
            object_is_closed_rational_expression(value.left.as_ref())
                && object_is_closed_rational_expression(value.right.as_ref())
        }
        Obj::Sub(value) => {
            object_is_closed_rational_expression(value.left.as_ref())
                && object_is_closed_rational_expression(value.right.as_ref())
        }
        Obj::Mul(value) => {
            object_is_closed_rational_expression(value.left.as_ref())
                && object_is_closed_rational_expression(value.right.as_ref())
        }
        Obj::Div(value) => {
            object_is_closed_rational_expression(value.left.as_ref())
                && object_is_closed_rational_expression(value.right.as_ref())
        }
        _ => false,
    }
}
