use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ComplexOperatorObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::TrigOperatorObjWellDefinedProofByDef;
use super::compile_assumption_stmt_result::{trust_have, assumption_start};
use super::piecewise_evidence::PiecewiseEvidence;
use crate::ast::stmt::DefAbstractPropStmt;
use crate::execute::{ExecHaveFnEqualCaseByCaseStmtResult, ExecHaveFnEqualCaseByCaseStmtSuccessResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_equal_case_by_case::ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IntegerOperatorObjWellDefinedProofByDef;
use super::compile_by_stmt_result::induction_evidence::InductionEvidence;
use crate::execute::ExecHaveObjByExistFactsStmtResult;
use crate::execute::execute_witness_stmt::{ExecWitnessNonemptySetStmtResult, ExecWitnessNonemptySetStmtSuccessResult};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef;
use crate::execute::execute_witness_stmt::{ExecWitnessStmtResult, ExecWitnessExistFactStmtResult, ExecWitnessExistFactStmtSuccessResult, ExecWitnessAtomicFactStmtResult, ExecWitnessAtomicFactStmtSuccessResult};
use crate::execute::execute_witness_stmt::{WitnessExistAmbientSuccess, WitnessExistObligationSuccess};
use crate::execute::execute_by_stmt::{ExecByContraStmtResult, ExecByContraStmtSuccess, ExecByCasesStmtResult, ByCasesBranchSuccess, ByCasesBranchClosingSuccess, ByContradictionClosingSuccess};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef;
use crate::execute::{ExecObtainObjFromExistFactStmtResult, ObtainExistVerifySuccess};
use crate::execute::ExecObtainObjFromAtomicFactStmtResult;
use crate::execute::execute_proof_block_stmt::{ExecClaimBodyProof, ExecClaimStmtResult, ExecClaimStmtSuccess, ExecProofBlockStmtResult, ExecSketchStmtSuccess};
use crate::store_fact_and_infer::{InferInFactResult, InferStrictLowerBoundPositiveResult, InferWeakIntegerLowerBoundInNResult};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{ProductShapeObjWellDefinedProofByDef, SetBuilderObjWellDefinedProof, SetFormerObjWellDefinedProofByDef};
use super::helper::verified_subject;
use super::LeanCompileError;
use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByDefStmtSuccess, ExecByInducStmtResult, ByInducCaseSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::UserDefinedPropDefinitionProof;
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::execute::{ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult, InducCaseSuccess, InducCasesDisjointSuccess, InducCaseBodySuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_by_induc::ByUnfoldHaveFnByInducApplicationObjectDefinitionProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::{FunctionBodyNormalizationProof, AnonymousFunctionBodyExpansionProof, FunctionBodyExpansionProof, FiniteCoordinateBodyExpansionProof, CompositionBodyExpansionProof};
use crate::execute::{ExecDefPropStmtResult, ExecDefPropStmtSuccessResult};
use crate::execute::ExecDefAbstractPropStmtResult;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::VerifyAtomicExceptEqualityFactSuccess;
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rewrite::AtomicExceptEqualityFactSearchProofByFnApplicationUnfoldSubstitution;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::store_fact_and_infer::{
    InferAtomicFactResult,
    InferEqualFactAdditiveCancellationResult, InferEqualFactSubtractiveCancellationResult,
    InferEqualFactNonzeroFactorCancellationResult, InferEqualFactCommonDenominatorCancellationResult,
    InferEqualFactNonzeroNumeratorCancellationResult, InferEqualFactResult, InferResult,
    InferEqualFactPositiveRealPowerResult, InferPositiveRealPowerTransportResult,
    InferPositiveRealPowerPositivityResult,
    StoreInferredFactResult, InferChainTransitiveClosureResult,
};

/// A borrowed position in the original execution evidence, not a replay registry.
#[derive(Clone, Copy)]
pub(super) struct SourcePosition<'a> {
    pub parent: Option<&'a SourcePosition<'a>>,
    pub owner: SourceOwner<'a>,
    pub before: usize,
}

// Run: completed statements. Headers: params, dom assumptions, then/body stages.
// WD/AtomicWD: child WD, then requirements. Call: types, doms, conclusion WD,
// then returned stores. HaveEqual: RHS WD, membership checks, alias definitions.
// Inference: genuine condition proofs, then the direct conclusion store.
// InferredStore: replay a named rule's constructed objects without a Verify WD stage.
#[derive(Clone, Copy)]
pub(super) enum OrderBoundInference<'a> {
    Strict(&'a InferStrictLowerBoundPositiveResult),
    WeakInteger(&'a InferWeakIntegerLowerBoundInNResult),
}

#[derive(Clone, Copy)]
pub(super) enum SourceOwner<'a> {
    Run(&'a RunLitexCodeResult),
    /// A transient Lean lambda; it introduces no source evidence.
    Term,
    Statement(&'a ExecStmtResult),
    Verify(&'a VerifyFactResult),
    AtomicVerify(&'a VerifyAtomicExceptEqualityFactSuccess),
    WD(&'a ObjWellDefinedProof),
    /// The original function WD, then target-signature WD of a domain check.
    FunctionDomainWD(&'a crate::execute::execute_fact_stmt::function_domain::FunctionDomainMatchProof),
    /// Original applicability children of a returned function's domain source.
    CompleteDomainSource(&'a CompleteFunctionDomainProof),
    // This constructor's first `usize` child/requirement stages have already
    // been emitted as lexical lets/haves. Source order still controls visibility.
    WDLocals(&'a ObjWellDefinedProof, usize),
    FormedSubjects(&'a VerifyFactResult, &'a StoreFactAndInferResult),
    /// Lexical endpoint constructors already emitted while replaying this chain.
    ChainObjects(&'a crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult, usize),
    /// Constructor lets emitted for the first clauses of this predicate body.
    /// This cursor adds object bindings, never assumption truth or new fact IDs.
    PropObjects(&'a ExecDefPropStmtSuccessResult, usize),
    /// A required completion boundary, not an additional visible fact prefix.
    Completion(&'a SourcePosition<'a>),
    SetBuilder(&'a SetBuilder, &'a SetBuilderObjWellDefinedProof),
    Named(&'a ExecDefThmStmtSuccess),
    Template(&'a crate::execute::ExecDefTemplateStmtSuccessResult),
    Claim(&'a ExecClaimStmtSuccess),
    Sketch(&'a ExecSketchStmtSuccess),
    Choice(&'a crate::execute::execute_by_stmt::ExecReleaseAxiomOfChoiceStmtSuccess),
    Zorn(&'a crate::execute::execute_by_stmt::ExecReleaseZornLemmaStmtSuccess),
    RangeExpansion(&'a crate::execute::execute_by_stmt::ExecExpandRangeStmtSuccess),
    Forall(&'a VerifyForallFactSuccess),
    EmptyForall(&'a crate::execute::execute_fact_stmt::verify_forall_fact::VerifyEmptyParameterDomainForallProof),
    ForallWD(&'a ForallFact, &'a ForallFactWellDefinedProof),
    NotForallWD(&'a NotForallFact, &'a crate::execute::execute_fact_stmt::verify_not_forall_fact::NotForallFactWellDefinedProof),
    ForallIffWD(&'a ForallFactWithIff, &'a crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::ForallFactWithIffWellDefinedProof),
    // Params, then each sequential body WD/assumption pair.
    ExistWD(&'a PlainExistFact, &'a ExistShapedFactWellDefinedProof),
    // Local stages only: params, equality stores, proof steps, body checks, uniqueness.
    WitnessExist(&'a ExecWitnessExistFactStmtSuccessResult),
    WitnessAtomic(&'a ExecWitnessAtomicFactStmtSuccessResult),
    WitnessNonempty(&'a ExecWitnessNonemptySetStmtSuccessResult),
    // Assumption WD, assumption store, proof steps, closing checks/stores.
    Contra(&'a ExecByContraStmtSuccess),
    Extension(&'a crate::execute::execute_by_stmt::ExecByExtensionStmtSuccess),
    FnExtension(&'a crate::execute::execute_by_stmt::ExecByFnExtensionStmtSuccess),
    EnumerationAssignment(&'a ForallFact, &'a crate::execute::execute_by_stmt::EnumerateAssignmentSuccess),
    OrSelected(&'a crate::execute::execute_fact_stmt::verify_or_fact::OrFactSearchProofBySelectedBranch),
    CasesBranch(&'a ByCasesBranchSuccess),
    KnownForall(&'a VerifyKnownForallFactProof),
    KnownApplication(&'a SearchProofByKnownForallFact),
    CalleeInstance(&'a SearchProofByKnownForallFact),
    Call(&'a ExecByThmStmtSuccess),
    ThmRelease(&'a ExecReleaseThmStmtSuccess),
    HaveEqualType(&'a ExecHaveObjEqualStmtSuccessResult),
    AtomicWD(&'a AtomicFactWellDefinedProof),
    /// Already emitted argument constructors of this exact atomic WD result.
    AtomicWDLocals(&'a AtomicFactWellDefinedProof, usize),
    EqualWDLocals(&'a crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof, usize),
    FactWD(&'a FactWellDefinedProof),
    InferredStore(&'a StoreFactResult),
    HaveGroup(&'a ParamTypeWellDefinedProof, &'a ParamTypeFactCheckResult),
    ParamTypeWD(&'a ParamTypeWellDefinedProof),
    PropDefinition(&'a ExecDefPropStmtSuccessResult),
    StructHeader(&'a crate::execute::ExecDefStructStmtSuccessResult),
    StructFields(&'a crate::execute::ExecDefStructStmtSuccessResult),
    StructLayer(&'a crate::execute::ReleaseOneStructLayerProof),
    StructLayers(&'a [crate::execute::ReleaseOneStructLayerProof]),
    ByDef(&'a ExecByDefStmtSuccess),
    PropRequirements(&'a UserDefinedPropDefinitionProof),
    PropInference(&'a StoreFactAndInferResult),
    AtomicInference(&'a Fact, &'a InferAtomicFactResult),
    CompoundInference(&'a StoreFactAndInferResult),
    ChainClosure(&'a InferChainTransitiveClosureResult),
    OrderBoundInference(OrderBoundInference<'a>),
    EqualityInferences(&'a [InferEqualFactResult]),
    PositivePowerInferences(&'a InferEqualFactPositiveRealPowerResult),
    PositivePowerTransport(&'a InferPositiveRealPowerTransportResult),
    AdditiveInference(&'a InferEqualFactAdditiveCancellationResult),
    SubtractiveInference(&'a InferEqualFactSubtractiveCancellationResult),
    NonzeroFactorInference(&'a InferEqualFactNonzeroFactorCancellationResult),
    CommonDenominatorInference(&'a InferEqualFactCommonDenominatorCancellationResult),
    NonzeroNumeratorInference(&'a InferEqualFactNonzeroNumeratorCancellationResult),
    EqualityRequirements(&'a [VerifyFactResult]),
    AtomicFnUnfold(&'a AtomicExceptEqualityFactSearchProofByFnApplicationUnfoldSubstitution),
    FunctionNormalization(&'a FunctionBodyNormalizationProof),
    FunctionExpansion(&'a AnonymousFunctionBodyExpansionProof),
    FiniteExpansion(&'a FiniteCoordinateBodyExpansionProof),
    CompositionExpansion(&'a CompositionBodyExpansionProof),
    FunctionDefinitionRewrite(&'a [AnonymousFunctionBodyExpansionProof]),
    Piecewise(PiecewiseEvidence<'a>),
    PiecewiseUnfold(&'a ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof),
    RecursiveFunction(&'a ExecHaveFnByInducStmtSuccessResult),
    RecursiveCase(&'a InducCaseSuccess),
    RecursiveDisjoint(&'a InducCasesDisjointSuccess),
    RecursiveUnfold(&'a ByUnfoldHaveFnByInducApplicationObjectDefinitionProof),
    Induction(InductionEvidence<'a>),
    InductionCase(InductionEvidence<'a>, &'a ByInducCaseSuccess),
}

// Constructor evidence comes from a checked source expression or a named infer
// rule's actual conclusion store. The latter does not invent a Verify WD result.
#[derive(Clone, Copy)]
enum SourceConstructor<'a> {
    Checked(&'a ObjWellDefinedProof),
    Inferred(&'a StoreFactResult),
}

impl<'a> SourcePosition<'a> {
    /// Local quantified proofs are Lean terms, whose carrier levels are
    /// inferred at their uses. Only declarations introduce level parameters.
    pub fn parameter_universe(&self, id: IdentifierId) -> String {
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            if parameter_in_owner(position, id).is_some() {
                return if matches!(position.owner, SourceOwner::HaveEqualType(_))
                    || position.parent.is_some_and(|parent| parent.is_local())
                {
                    "_".to_string()
                } else {
                    format!("v{}", id.value())
                };
            }
            cursor = position.parent;
        }
        format!("v{}", id.value())
    }

    pub fn equal_wd_child_name(&self, index: usize) -> String {
        let mut depth = 0;
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            if matches!(position.owner, SourceOwner::EqualWDLocals(..)) {
                depth += 1;
            }
            cursor = position.parent;
        }
        format!("_equal_wd_{depth}_{index}")
    }

    pub fn atomic_wd_child_name(&self, index: usize) -> String {
        let mut depth = 0;
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            if matches!(position.owner, SourceOwner::AtomicWDLocals(..)) {
                depth += 1;
            }
            cursor = position.parent;
        }
        format!("_atomic_wd_{depth}_{index}")
    }

    pub fn wd_child_name(&self, index: usize) -> String {
        if let SourceOwner::WDLocals(proof, _) = self.owner {
            if let Some(scope) = function_argument_scope(proof) {
                if let Some(formed) = scope
                    .formed_children
                    .iter()
                    .find(|formed| formed.child_index == index)
                {
                    return format!("_object_w{}", formed.wd_id.value());
                }
            }
        }
        let mut depth = 0;
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            if matches!(position.owner, SourceOwner::WDLocals(..)) {
                depth += 1;
            }
            cursor = position.parent;
        }
        format!("_wd_{depth}_{index}")
    }

    pub fn bound_wd_child(&self, proof: &ObjWellDefinedProof) -> Option<String> {
        self.bound_child(|child| std::ptr::eq(child, proof))
    }

    pub fn bound_object_child(&self, object: &Obj) -> Option<String> {
        // Equal denotations alone do not identify the same source construction.
        self.bound_child(|child| child.obj() == object)
    }

    /// Finite enumeration constructs its recorded literal before assuming the
    /// binding equality. Keep that native payload even when the source WD cache
    /// identifies its IR with an enclosing negation expression.
    pub fn enumeration_literal(&self, object: &Obj) -> Option<&Number> {
        let Obj::Literal(Literal::Number(_)) = object else {
            return None;
        };
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            if let SourceOwner::EnumerationAssignment(_, assignment) = position.owner {
                for binding in &assignment.binding_assumptions {
                    let StoreFactResult::AtomicFact(stored) = &binding.store_and_infer.store else {
                        continue;
                    };
                    if let AtomicFact::EqualFact(fact) = &stored.fact {
                        if fact.right == *object {
                            if let Obj::Literal(Literal::Number(number)) = &fact.right {
                                return Some(number);
                            }
                        }
                    }
                }
            }
            cursor = position.parent;
        }
        None
    }

    pub fn bound_fn_call(
        &self,
        application: &FnObj,
        proof: &crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof,
    ) -> Option<String> {
        self.bound_child(|child| {
            matches!(child,
                ObjWellDefinedProof::ByDef {
                    obj: Obj::FnObj(original_application),
                    proof: ObjWellDefinedProofByDef::FnObj(original),
                } if original_application == application && std::ptr::eq(original, proof)
            )
        })
    }

    /// A separately checked occurrence can reuse a completed call with the
    /// same source constructor and selected signature. Callers must validate
    /// the occurrence's own WD evidence before using this output-only alias.
    pub fn bound_compatible_fn_call(
        &self,
        application: &FnObj,
        proof: &crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof,
    ) -> Option<String> {
        self.bound_child(|child| {
            matches!(child,
                ObjWellDefinedProof::ByDef {
                    obj: Obj::FnObj(original_application),
                    proof: ObjWellDefinedProofByDef::FnObj(original),
                } if original_application == application && same_call_constructor(original, proof)
            )
        })
    }

    fn bound_child(&self, matches: impl Fn(&ObjWellDefinedProof) -> bool) -> Option<String> {
        self.bound_constructor(matches).map(|(_, term)| term)
    }

    /// Project only a requirement of the exact original constructor node.
    /// Its proof was consumed when that constructor was emitted.
    pub fn bound_wd_requirement(&self, requirement: &VerifyFactResult) -> Option<String> {
        let (proof, term) = self.bound_constructor(|proof| {
            arithmetic_stages(proof).is_some_and(|(_, requirements)| {
                requirements
                    .iter()
                    .any(|original| std::ptr::eq(original, requirement))
            })
        })?;
        let (_, requirements) = arithmetic_stages(proof)?;
        let index = requirements
            .iter()
            .position(|original| std::ptr::eq(original, requirement))?;
        // These are the proof fields of the corresponding Litex.lean wrappers,
        // in the original verifier's requirement order. Other constructors may
        // transform their premises; their proofs are not direct projections.
        let fields: &[&str] = match proof.obj() {
            Obj::ArithmeticOperator(
                ArithmeticOperator::Add(_)
                | ArithmeticOperator::Sub(_)
                | ArithmeticOperator::Mul(_)
                | ArithmeticOperator::Min(_)
                | ArithmeticOperator::Max(_),
            ) => &[".1", ".2"],
            Obj::IntegerOperator(IntegerOperator::Gcd(_)) => {
                return match index {
                    0 => Some(format!("({term}).wd.1")),
                    1 => Some(format!("({term}).wd.2.1")),
                    _ => None, // The original singleton/reversed Or may have been normalized.
                };
            }
            Obj::SetFormer(SetFormer::FiniteSeqSet(_) | SetFormer::IntervalObj(_)) => &[".1", ".2"],
            Obj::SetFormer(SetFormer::SeqSet(_) | SetFormer::OneSideInfinityIntervalObj(_)) => {
                &[""]
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(_)) => &[""],
            Obj::IteratedOperator(
                IteratedOperator::SumOfFiniteSet(_) | IteratedOperator::ProductOfFiniteSet(_),
            ) if requirements.len() == 3 => &[".1", ".2.1", ".2.2.1"],
            Obj::IteratedOperator(IteratedOperator::Sum(_) | IteratedOperator::Product(_))
                if requirements.len() == 4 =>
            {
                &[".1", ".2.1", ".2.2.1", ".2.2.2.2.1"]
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(_) | FiniteSetStat::FiniteSetMin(_)) => {
                &[".1", ".2.1", ".2.2"]
            }
            Obj::IntegerOperator(IntegerOperator::Factorial(_)) => &[""],
            Obj::IntegerOperator(IntegerOperator::Lcm(_)) => &[".1", ".2"],
            Obj::IntegerOperator(IntegerOperator::Quot(_)) => &[".1", ".2"],
            Obj::IntegerOperator(IntegerOperator::Mod(p))
                if requirements.len() == 2
                    && matches!(
                        p.right.as_ref(),
                        Obj::IntegerOperator(IntegerOperator::Gcd(_))
                    ) =>
            {
                &[".1", ".2.1"]
            }
            Obj::IntegerOperator(IntegerOperator::Mod(_)) => &[".1", ".2.1", ".2.2"],
            Obj::ArithmeticOperator(ArithmeticOperator::Div(_)) => &[".2.2", ".1", ".2.1"],
            Obj::ArithmeticOperator(
                ArithmeticOperator::Neg(_)
                | ArithmeticOperator::Abs(_)
                | ArithmeticOperator::Sign(_)
                | ArithmeticOperator::Floor(_)
                | ArithmeticOperator::Ceil(_),
            ) => &[""],
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(_)) => &[".1", ".2"],
            Obj::ComplexOperator(_) => &[""],
            Obj::TrigOperator(
                TrigOperator::Sin(_)
                | TrigOperator::Cos(_)
                | TrigOperator::Arctan(_)
                | TrigOperator::Arccot(_),
            ) => &[""],
            Obj::TrigOperator(TrigOperator::Arcsin(_) | TrigOperator::Arccos(_)) => {
                return match index {
                    0 => Some(format!("({term}).wd.1")),
                    // The constructor normalizes -1; the source certificate
                    // may instead mention an owned negation of 1.
                    1 => None,
                    2 => Some(format!("({term}).wd.2.2")),
                    _ => None,
                };
            }
            Obj::TrigOperator(
                TrigOperator::Tan(_)
                | TrigOperator::Cot(_)
                | TrigOperator::Sec(_)
                | TrigOperator::Csc(_),
            ) => {
                if requirements.len() == 1 {
                    &[".1"]
                } else {
                    &[".1", ".2"]
                }
            }
            Obj::ExpLogOperator(ExpLogOperator::Exp(_) | ExpLogOperator::Ln(_)) => &[""],
            Obj::ExpLogOperator(ExpLogOperator::Log(_)) => {
                &[".1", ".2.1", ".2.2.1", ".2.2.2.1", ".2.2.2.2"]
            }
            _ => return None,
        };
        (fields.len() == requirements.len()).then(|| format!("({term}).wd{}", fields[index]))
    }

    fn bound_constructor(
        &self,
        matches: impl Fn(&ObjWellDefinedProof) -> bool,
    ) -> Option<(&'a ObjWellDefinedProof, String)> {
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            if let SourceOwner::ChainObjects(chain, emitted) = position.owner {
                let crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult::Success(chain) = chain else { return None; };
                for stage in (0..emitted).rev() {
                    let VerifyFactResult::Equality(result) = &chain.adjacent[stage / 2] else {
                        continue;
                    };
                    let VerifyEqualityResult::Success(result) = result.as_ref() else {
                        continue;
                    };
                    let child = if stage % 2 == 0 {
                        &result.well_defined_proof.left
                    } else {
                        &result.well_defined_proof.right
                    };
                    if matches!(
                        child.obj(),
                        Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
                    ) {
                        continue;
                    }
                    let name = format!("_chain_wd_{}_{}", chain.fact.fact_id.value(), stage);
                    if let Some(term) = projected_wd_child(child, name, &matches) {
                        return Some(term);
                    }
                }
            }
            if let SourceOwner::EqualWDLocals(proof, emitted) = position.owner {
                for (index, child) in [&proof.left, &proof.right]
                    .into_iter()
                    .take(emitted)
                    .enumerate()
                    .rev()
                {
                    if matches!(
                        child.obj(),
                        Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
                    ) {
                        continue;
                    }
                    if let Some(term) =
                        projected_wd_child(child, position.equal_wd_child_name(index), &matches)
                    {
                        return Some(term);
                    }
                }
            }
            if let SourceOwner::AtomicWDLocals(proof, emitted) = position.owner {
                for (index, child) in proof
                    .well_defined_of_each_parameter
                    .iter()
                    .take(emitted)
                    .enumerate()
                    .rev()
                {
                    if matches!(
                        child.obj(),
                        Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
                    ) {
                        continue;
                    }
                    if let Some(term) =
                        projected_wd_child(child, position.atomic_wd_child_name(index), &matches)
                    {
                        return Some(term);
                    }
                }
            }
            if let SourceOwner::PropObjects(proof, completed) = position.owner {
                for assumed in proof.assumed_iff_facts.iter().take(completed).rev() {
                    for subject in &assumed.store_and_infer.formed_subjects {
                        if let Ok(Some(wd)) = super::compile_fact_stmt_result::compile_formed_subjects::assumed_subject_proof(assumed, subject.argument_index) {
                            if let Some(term) = projected_wd_child(wd, format!("_object_w{}", subject.wd_id.value()), &matches) {
                                return Some(term);
                            }
                        }
                    }
                }
            }
            if let SourceOwner::FormedSubjects(verify, store) = position.owner {
                for subject in &store.formed_subjects {
                    if let Ok(Some(proof)) = super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
                        verify, subject.argument_index,
                    ) {
                        let name = format!("_object_w{}", subject.wd_id.value());
                        let term = if position.is_local() { name } else { position.context_application(&name) };
                        if let Some(term) = projected_wd_child(proof, term, &matches) {
                            return Some(term);
                        }
                    }
                }
            }
            if let SourceOwner::WDLocals(proof, emitted) = position.owner {
                if let Some((children, _)) = arithmetic_stages(proof) {
                    for (index, child) in children.iter().take(emitted).enumerate().rev() {
                        if let Some(term) =
                            projected_wd_child(child, position.wd_child_name(index), &matches)
                        {
                            return Some(term);
                        }
                    }
                }
            }
            cursor = position.parent;
        }
        None
    }

    pub fn new(parent: Option<&'a Self>, owner: SourceOwner<'a>, before: usize) -> Self {
        Self {
            parent,
            owner,
            before,
        }
    }

    /// Original search child `index`, after this atomic result's complete WD.
    pub fn atomic_search_prior(&self, index: usize) -> Result<Self, LeanCompileError> {
        let proof = match self.owner {
            SourceOwner::AtomicVerify(proof) => proof,
            SourceOwner::Verify(VerifyFactResult::AtomicExceptEquality(result)) => {
                let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_ref() else {
                    return Err(LeanCompileError::new(
                        "Atomic/FailedSearchCursor",
                        "A failed atomic result has no completed search children.",
                    ));
                };
                proof
            }
            _ => {
                return Err(LeanCompileError::new(
                    "Atomic/SearchCursor",
                    "Atomic search must retain its original successful result owner.",
                ))
            }
        };
        Ok(Self {
            before: atomic_formation_stage_count(&proof.well_defined_proof) + index,
            ..*self
        })
    }

    /// Original comparison child after the captured formation/source stages.
    pub fn function_domain_comparison_prior(&self, index: usize) -> Result<Self, LeanCompileError> {
        use crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof;
        let SourceOwner::FunctionDomainWD(proof) = self.owner else {
            return Err(LeanCompileError::unsupported("FunctionDomain/Cursor"));
        };
        if !matches!(
            proof.comparison,
            FunctionDomainComparisonProof::MutualInclusion { .. }
        ) || index > 1
        {
            return Err(LeanCompileError::unsupported(
                "FunctionDomain/ComparisonStage",
            ));
        }
        let mut stages = Vec::new();
        function_domain_search_stages(proof, &mut stages);
        Ok(Self {
            before: stages.len() - 2 + index,
            ..*self
        })
    }

    /// Only already completed top-level ordinary-have introductions are arguments.
    pub fn context_parameters(&self) -> Vec<(&'a BoundName, Option<&'a Obj>, FactId)> {
        let mut parameters = Vec::new();
        let mut position = Some(self);
        while let Some(current) = position {
            if let SourceOwner::Run(run) = current.owner {
                for statement in run.statement_results.iter().take(current.before) {
                    if context_parameter_parts(statement).is_some() {
                        append_have_parameters(statement, usize::MAX, &mut parameters);
                    }
                }
                break;
            }
            position = current.parent;
        }
        let mut position = Some(self);
        while let Some(current) = position {
            if let SourceOwner::Statement(statement) = current.owner {
                // Completion records visibility, not a new lexical scope.
                // Historical constructors still take this have's parameters.
                let mut enclosing = current.parent;
                while let Some(p) = enclosing {
                    if matches!(p.owner, SourceOwner::Completion(_)) {
                        enclosing = p.parent;
                    } else {
                        break;
                    }
                }
                if enclosing.is_some_and(|p| matches!(p.owner, SourceOwner::Run(_))) {
                    if context_parameter_parts(statement).is_some() {
                        append_have_parameters(statement, current.before, &mut parameters);
                    }
                }
            }
            position = current.parent;
        }
        parameters
    }

    /// Original top-level statements and the visible stage of an active declaration.
    pub fn context_statements(
        &self,
    ) -> Vec<(&'a RunLitexCodeResult, usize, &'a ExecStmtResult, usize)> {
        let mut cursor = Some(self);
        let mut active = None;
        while let Some(p) = cursor {
            if let SourceOwner::Statement(statement) = p.owner {
                if p.parent
                    .is_some_and(|q| matches!(q.owner, SourceOwner::Run(_)))
                {
                    active = Some((statement, p.before));
                }
            }
            if let SourceOwner::Run(run) = p.owner {
                let mut result = run
                    .statement_results
                    .iter()
                    .take(p.before)
                    .enumerate()
                    .map(|(index, statement)| (run, index, statement, usize::MAX))
                    .collect::<Vec<_>>();
                if let Some((statement, before)) = active {
                    result.push((run, p.before, statement, before));
                }
                return result;
            }
            cursor = p.parent;
        }
        Vec::new()
    }

    fn context_hypotheses(&self) -> Vec<FactId> {
        self.context_statements()
            .into_iter()
            .flat_map(|(_, _, statement, before)| {
                let stages = super::compile_assumption_stmt_result::assumption_stages(statement);
                let count = before.saturating_sub(assumption_start(statement) + stages.len());
                stages
                    .into_iter()
                    .take(count)
                    .map(|(fact, _, _)| fact.fact_id())
                    .chain(super::compile_local_assumptions::local_assumption_ids(
                        statement,
                    ))
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    pub fn context_abstract_props(&self) -> Vec<(&'a DefAbstractPropStmt, usize)> {
        let mut position = Some(self);
        while let Some(current) = position {
            if let SourceOwner::Run(run) = current.owner {
                return abstract_props_before(run, current.before);
            }
            position = current.parent;
        }
        Vec::new()
    }

    pub fn visible_abstract_prop(
        &self,
        predicate: &AtomicName,
    ) -> Option<(&'a DefAbstractPropStmt, usize)> {
        let AtomicName::Plain { name } = predicate else {
            return None;
        };
        self.context_abstract_props()
            .into_iter()
            .rev()
            .find(|(declaration, _)| &declaration.name == name)
    }

    pub fn context_application(&self, name: &str) -> String {
        let arguments = self
            .context_parameters()
            .iter()
            .flat_map(|(p, _, fact_id)| {
                let id = p.id.value();
                [
                    format!("_Host_i{id}"),
                    format!("_rep_i{id}"),
                    format!("_value_i{id}"),
                    format!("h_{}", fact_id.value()),
                ]
            })
            .collect::<Vec<_>>();
        let predicates = self
            .context_abstract_props()
            .into_iter()
            .map(|(_, index)| format!("abstract_prop_{index}"))
            .collect::<Vec<_>>();
        application(name, &arguments, &predicates, &self.context_hypotheses())
    }

    pub fn is_local(&self) -> bool {
        let mut position = Some(self);
        while let Some(current) = position {
            match current.owner {
                // Tuple-release checks are local proof terms. Their later
                // publications retain the enclosing declaration's scope.
                SourceOwner::Statement(ExecStmtResult::ReleaseAndExpand(
                    ExecReleaseAndExpandStmtResult::TupleDef(
                        crate::execute::execute_release_tuple_def_stmt::ExecReleaseTupleDefStmtResult::Success(proof),
                    ),
                )) if current.before < crate::compile_to_lean::compile_release_tuple_def_result::tuple_release_publication_start(proof) => return true,
                SourceOwner::Term
                | SourceOwner::Named(_)
                | SourceOwner::Claim(_)
                | SourceOwner::Forall(_)
                | SourceOwner::EmptyForall(_)
                | SourceOwner::ExistWD(_, _)
                | SourceOwner::WitnessExist(_)
                | SourceOwner::WitnessAtomic(_)
                | SourceOwner::RangeExpansion(_)
                | SourceOwner::Choice(_)
                | SourceOwner::Zorn(_)
                | SourceOwner::Sketch(_)
                | SourceOwner::WitnessNonempty(_)
                | SourceOwner::Contra(_)
                | SourceOwner::Extension(_)
                | SourceOwner::FnExtension(_)
                | SourceOwner::FunctionDomainWD(_)
                | SourceOwner::CompleteDomainSource(_)
                | SourceOwner::OrSelected(_)
                | SourceOwner::EnumerationAssignment(..)
                | SourceOwner::CasesBranch(_)
                | SourceOwner::ForallWD(_, _)
                | SourceOwner::NotForallWD(_, _)
                | SourceOwner::ForallIffWD(_, _)
                | SourceOwner::KnownForall(_)
                | SourceOwner::Call(_)
                | SourceOwner::ThmRelease(_)
                | SourceOwner::HaveEqualType(_) | SourceOwner::Template(_) => return true,
                SourceOwner::Piecewise(_) | SourceOwner::RecursiveFunction(_)
                | SourceOwner::RecursiveCase(_)
                | SourceOwner::RecursiveDisjoint(_) => return true,
                SourceOwner::Induction(_) | SourceOwner::InductionCase(_, _) => return true,
                SourceOwner::StructHeader(p) if p.introduced_params.is_some() => return true,
                SourceOwner::StructFields(_) | SourceOwner::PropDefinition(_)
                | SourceOwner::ByDef(_)
                | SourceOwner::SetBuilder(_, _) => return true,
                SourceOwner::WD(proof) | SourceOwner::WDLocals(proof, _)
                    if function_binder(proof).is_some() =>
                {
                    return true
                }
                _ => {}
            }
            position = current.parent;
        }
        false
    }

    pub fn user_callee_reference(
        &self,
        name: &AtomicName,
        callee: &ResolvedTheoremCallee,
    ) -> Result<(Fact, String), LeanCompileError> {
        let AtomicName::Plain { name } = name else {
            return Err(LeanCompileError::unsupported("ByThm/QualifiedCallee"));
        };
        match callee {
            ResolvedTheoremCallee::UserTheorem(declaration) => {
                let (registered, site, _) = self.visible_theorem(name)?;
                if registered != declaration || &declaration.name != name {
                    return Err(LeanCompileError::unsupported("ByThm/Callee"));
                }
                let reference = format!("h_{}", registered.fact.fact_id().value());
                Ok((
                    registered.fact.clone(),
                    if site.is_local() {
                        reference
                    } else {
                        let mut reference = site.context_application(&reference);
                        if let SourceOwner::Run(run) = site.owner {
                            let ids = super::compile_local_assumptions::local_assumption_ids(
                                &run.statement_results[site.before],
                            );
                            if !ids.is_empty() {
                                reference = format!(
                                    "({reference} {})",
                                    ids.iter()
                                        .map(|id| format!("(h_{0} := h_{0})", id.value()))
                                        .collect::<Vec<_>>()
                                        .join(" ")
                                );
                            }
                        }
                        reference
                    },
                ))
            }
            ResolvedTheoremCallee::UserAxiom(declaration) => {
                for (_, _, statement, before) in self.context_statements().into_iter().rev() {
                    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::Axiom(
                        crate::execute::ExecAxiomStmtResult::Success(p),
                    )) = statement
                    {
                        if &p.statement.name == name && before > 1 {
                            if p.statement != *declaration {
                                return Err(LeanCompileError::unsupported("ByThm/AxiomCapture"));
                            }
                            return Ok((
                                Fact::ForallFact(p.statement.forall_fact.clone()),
                                format!("h_{}", p.statement.forall_fact.fact_id.value()),
                            ));
                        }
                    }
                }
                Err(LeanCompileError::unsupported("ByThm/AxiomProducer"))
            }
            _ => Err(LeanCompileError::unsupported("ByThm/Callee")),
        }
    }

    pub fn visible_theorem(
        &self,
        name: &str,
    ) -> Result<(&'a DefThmStmt, Self, usize), LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            let steps = match current.owner {
                SourceOwner::Run(run) => Some((run.statement_results.as_slice(), 0)),
                SourceOwner::Named(proof) => Some(named_steps(proof)),
                SourceOwner::Claim(proof) => Some(claim_steps(proof)),
                owner => local_steps(owner),
            };
            if let Some((steps, head)) = steps {
                for (index, statement) in steps
                    .iter()
                    .take(current.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                        ExecDefThmStmtResult::Success(proof),
                    )) = statement
                    {
                        let completed = Self {
                            before: head + index + 1,
                            ..*current
                        };
                        if proof.statement.name == name
                            && obeys_active_stage_ceilings(self, &completed)
                        {
                            return Ok((
                                &proof.statement,
                                Self {
                                    before: head + index,
                                    ..*current
                                },
                                index,
                            ));
                        }
                    }
                }
            }
            position = current.parent;
        }
        Err(LeanCompileError::new(
            "ByThm/Producer",
            "The named theorem has no prior declaration in the active source results.",
        ))
    }

    /// Resolve the exact registered property in the visible source prefix.
    /// This is declaration lookup, not a search for a new proof.
    pub fn visible_registration(
        &self,
        matches: impl Fn(&crate::execute::execute_register_stmt::ExecRegisterStmtResult) -> bool,
    ) -> Result<
        (
            &'a crate::execute::execute_register_stmt::ExecRegisterStmtResult,
            Self,
        ),
        LeanCompileError,
    > {
        let mut scope = Some(self);
        while let Some(current) = scope {
            let steps = match current.owner {
                SourceOwner::Run(run) => Some((run.statement_results.as_slice(), 0)),
                SourceOwner::Named(proof) => Some(named_steps(proof)),
                SourceOwner::Claim(proof) => Some(claim_steps(proof)),
                owner => local_steps(owner),
            };
            if let Some((steps, head)) = steps {
                for (index, statement) in steps
                    .iter()
                    .take(current.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    if let ExecStmtResult::Register(result) = statement {
                        let completed = Self {
                            before: head + index + 1,
                            ..*current
                        };
                        if matches(result) && obeys_active_stage_ceilings(self, &completed) {
                            return Ok((
                                result,
                                Self {
                                    before: head + index,
                                    ..*current
                                },
                            ));
                        }
                    }
                }
            }
            scope = current.parent;
        }
        Err(LeanCompileError::unsupported("Register/Producer"))
    }

    pub fn visible_struct(
        &self,
        name: &AtomicName,
    ) -> Result<
        (
            &'a crate::execute::ExecDefStructStmtSuccessResult,
            Self,
            usize,
        ),
        LeanCompileError,
    > {
        let AtomicName::Plain { name } = name else {
            return Err(LeanCompileError::unsupported("Struct/QualifiedDeclaration"));
        };
        let mut position = Some(self);
        while let Some(current) = position {
            if current.before > 0 {
                if let SourceOwner::Statement(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::DefStruct(
                        crate::execute::ExecDefStructStmtResult::Success(p),
                    ),
                )) = current.owner
                {
                    if &p.statement.name == name {
                        if let Some(parent) = current.parent {
                            if let SourceOwner::Run(run) = parent.owner {
                                return Ok((
                                    p,
                                    Self::new(None, SourceOwner::Run(run), parent.before),
                                    parent.before,
                                ));
                            }
                        }
                    }
                }
            }

            if let SourceOwner::Run(run) = current.owner {
                for (index, statement) in run
                    .statement_results
                    .iter()
                    .take(current.before)
                    .enumerate()
                    .rev()
                {
                    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
                        crate::execute::ExecDefStructStmtResult::Success(proof),
                    )) = statement
                    {
                        if &proof.statement.name == name {
                            return Ok((
                                proof,
                                Self::new(None, SourceOwner::Run(run), index),
                                index,
                            ));
                        }
                    }
                }
            }
            position = current.parent;
        }
        Err(LeanCompileError::unsupported("Struct/Producer"))
    }

    pub fn visible_template(
        &self,
        name: &AtomicName,
    ) -> Result<
        (
            &'a crate::execute::ExecDefTemplateStmtSuccessResult,
            Self,
            usize,
        ),
        LeanCompileError,
    > {
        let AtomicName::Plain { name } = name else {
            return Err(LeanCompileError::unsupported(
                "Template/QualifiedDeclaration",
            ));
        };
        let mut cursor = Some(self);
        while let Some(scope) = cursor {
            if let SourceOwner::Run(run) = scope.owner {
                for (index, statement) in run
                    .statement_results
                    .iter()
                    .take(scope.before)
                    .enumerate()
                    .rev()
                {
                    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
                        crate::execute::ExecDefTemplateStmtResult::Success(p),
                    )) = statement
                    {
                        if &p.statement.template_name == name {
                            return Ok((p, Self::new(None, SourceOwner::Run(run), index), index));
                        }
                    }
                }
            }
            cursor = scope.parent;
        }
        Err(LeanCompileError::unsupported("Template/Producer"))
    }

    pub fn visible_prop(
        &self,
        predicate: &AtomicName,
    ) -> Result<(&'a ExecDefPropStmtSuccessResult, Self, usize), LeanCompileError> {
        let AtomicName::Plain { name } = predicate else {
            return Err(LeanCompileError::unsupported("Prop/QualifiedDeclaration"));
        };
        let mut position = Some(self);
        while let Some(current) = position {
            if let SourceOwner::Run(run) = current.owner {
                for (index, statement) in run
                    .statement_results
                    .iter()
                    .take(current.before)
                    .enumerate()
                    .rev()
                {
                    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
                        ExecDefPropStmtResult::Success(proof),
                    )) = statement
                    {
                        if &proof.statement.name == name {
                            return Ok((
                                proof,
                                Self::new(None, SourceOwner::Run(run), index),
                                index,
                            ));
                        }
                    }
                }
            }
            position = current.parent;
        }
        Err(LeanCompileError::new(
            "Prop/Producer",
            "The predicate has no preceding concrete definition in the original results.",
        ))
    }

    /// Resolve an exact introducing declaration in the active source prefix.
    /// The caller matches the captured definition and identifier, never facts.
    pub fn visible_object_definition(
        &self,
        matches: impl Fn(&ExecDefinitionStmtResult) -> bool,
    ) -> Result<&'a ExecDefinitionStmtResult, LeanCompileError> {
        let mut scope = Some(self);
        while let Some(current) = scope {
            let steps = match current.owner {
                SourceOwner::Run(run) => Some((run.statement_results.as_slice(), 0)),
                SourceOwner::Named(proof) => Some(named_steps(proof)),
                SourceOwner::Claim(proof) => Some(claim_steps(proof)),
                owner => local_steps(owner),
            };
            if let Some((steps, head)) = steps {
                for (index, statement) in steps
                    .iter()
                    .take(current.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    if let ExecStmtResult::Definition(definition) = statement {
                        let completed = Self {
                            before: head + index + 1,
                            ..*current
                        };
                        if matches(definition) && obeys_active_stage_ceilings(self, &completed) {
                            return Ok(definition);
                        }
                    }
                }
            }
            scope = current.parent;
        }
        Err(LeanCompileError::unsupported(
            "ReleaseObj/DefinitionProducer",
        ))
    }

    pub fn visible_function(
        &self,
        id: &IdentifierId,
    ) -> Result<(&'a ExecHaveFnEqualStmtSuccessResult, Self, usize), LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            match current.owner {
                SourceOwner::Run(run) => {
                    for (index, statement) in run
                        .statement_results
                        .iter()
                        .take(current.before)
                        .enumerate()
                        .rev()
                    {
                        if let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
                            ExecHaveFnEqualStmtResult::Success(proof),
                        )) = statement
                        {
                            if &proof.statement.name.id == id {
                                return Ok((
                                    proof,
                                    Self::new(None, SourceOwner::Run(run), index),
                                    index,
                                ));
                            }
                        }
                    }
                }
                SourceOwner::Statement(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveFnEqual(ExecHaveFnEqualStmtResult::Success(
                        proof,
                    )),
                )) if current.before >= 2 && &proof.statement.name.id == id => {
                    if let Some(parent) = current.parent {
                        return Ok((proof, *parent, parent.before));
                    }
                }
                _ => {}
            }
            position = current.parent;
        }
        Err(LeanCompileError::new(
            "Function/Producer",
            "The function has no preceding definition in the original result prefix.",
        ))
    }

    /// A selected function is available inside its declaration after the
    /// source/signature checks, and outside it only in the completed prefix.
    pub fn visible_replacement(
        &self,
        id: IdentifierId,
    ) -> Option<(
        &'a crate::execute::ExecHaveByReplacementAxiomStmtSuccessResult,
        Self,
    )> {
        let mut cursor = Some(self);
        while let Some(current) = cursor {
            if let SourceOwner::Run(run) = current.owner {
                for (index, statement) in run
                    .statement_results
                    .iter()
                    .take(current.before)
                    .enumerate()
                    .rev()
                {
                    if let Some(p) =
                        super::compile_replacement_result::replacement_statement(statement)
                    {
                        if p.statement.name.id == id {
                            return Some((
                                p,
                                Self {
                                    before: index,
                                    ..*current
                                },
                            ));
                        }
                    }
                }
            }
            if let SourceOwner::Statement(statement) = current.owner {
                if let Some(p) = super::compile_replacement_result::replacement_statement(statement)
                {
                    if current.before > 1 && p.statement.name.id == id {
                        return Some((p, *current));
                    }
                }
            }
            cursor = current.parent;
        }
        None
    }

    pub fn visible_selected_function(
        &self,
        id: &IdentifierId,
    ) -> Result<
        (
            &'a crate::execute::ExecHaveFnByForallExistUniqueStmtSuccessResult,
            Self,
        ),
        LeanCompileError,
    > {
        use crate::execute::ExecHaveFnByForallExistUniqueStmtResult as Selected;
        let mut cursor = Some(self);
        while let Some(current) = cursor {
            match current.owner {
                SourceOwner::Run(run) => {
                    for (index, statement) in run
                        .statement_results
                        .iter()
                        .take(current.before)
                        .enumerate()
                        .rev()
                    {
                        if let ExecStmtResult::Definition(
                            ExecDefinitionStmtResult::HaveFnByForallExistUnique(Selected::Success(
                                p,
                            )),
                        ) = statement
                        {
                            if p.statement.name.id == *id {
                                return Ok((
                                    p,
                                    Self {
                                        before: index,
                                        ..*current
                                    },
                                ));
                            }
                        }
                    }
                }
                SourceOwner::Statement(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveFnByForallExistUnique(Selected::Success(p)),
                )) if current.before >= 2 && p.statement.name.id == *id => {
                    return Ok((p, *current));
                }
                _ => {}
            }
            cursor = current.parent;
        }
        Err(LeanCompileError::unsupported("SelectedFunction/Producer"))
    }

    /// The source self binder denotes the exact restricted prefix graph while
    /// its declaration is checked. It never cites the final total graph store.
    pub fn visible_recursive_self(
        &self,
        id: &IdentifierId,
    ) -> Result<(&'a ExecHaveFnByInducStmtSuccessResult, Self), LeanCompileError> {
        let mut current = Some(self);
        while let Some(position) = current {
            if let SourceOwner::RecursiveFunction(proof) = position.owner {
                if &proof.statement.name.id == id {
                    if position.before > 6 {
                        return Ok((proof, *position));
                    }
                    return Err(LeanCompileError::new("RecursiveFunction/FutureSelfProducer", "The exact recursive self membership has not been stored at the active formation stage."));
                }
            }
            current = position.parent;
        }
        Err(LeanCompileError::new(
            "RecursiveFunction/SelfProducer",
            "The recursive self binder has no preceding restricted membership stage.",
        ))
    }

    pub fn visible_piecewise_function(
        &self,
        id: &IdentifierId,
    ) -> Result<(&'a ExecHaveFnEqualCaseByCaseStmtSuccessResult, Self), LeanCompileError> {
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            match position.owner {
                SourceOwner::Run(run) => {
                    for (index, statement) in run
                        .statement_results
                        .iter()
                        .take(position.before)
                        .enumerate()
                        .rev()
                    {
                        if let ExecStmtResult::Definition(
                            ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
                                ExecHaveFnEqualCaseByCaseStmtResult::Success(p),
                            ),
                        ) = statement
                        {
                            if p.statement.name.id == *id {
                                return Ok((p, Self::new(None, SourceOwner::Run(run), index)));
                            }
                        }
                    }
                }
                SourceOwner::Statement(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
                        ExecHaveFnEqualCaseByCaseStmtResult::Success(p),
                    ),
                )) if position.before >= 5 && p.statement.name.id == *id => {
                    return Ok((p, *position));
                }
                _ => {}
            }
            cursor = position.parent;
        }
        Err(LeanCompileError::unsupported("PiecewiseFunction/Producer"))
    }

    pub fn visible_recursive_function(
        &self,
        id: &IdentifierId,
    ) -> Result<(&'a ExecHaveFnByInducStmtSuccessResult, Self, usize), LeanCompileError> {
        let mut current = Some(self);
        while let Some(position) = current {
            match position.owner {
                SourceOwner::Run(run) => {
                    for (index, statement) in run
                        .statement_results
                        .iter()
                        .take(position.before)
                        .enumerate()
                        .rev()
                    {
                        if let ExecStmtResult::Definition(
                            ExecDefinitionStmtResult::HaveFnByInduc(
                                ExecHaveFnByInducStmtResult::Success(proof),
                            ),
                        ) = statement
                        {
                            if &proof.statement.name.id == id {
                                return Ok((
                                    proof,
                                    Self::new(None, SourceOwner::Run(run), index),
                                    index,
                                ));
                            }
                        }
                    }
                }
                SourceOwner::Statement(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveFnByInduc(ExecHaveFnByInducStmtResult::Success(
                        proof,
                    )),
                )) if position.before >= 8 && &proof.statement.name.id == id => {
                    if let Some(parent) = position.parent {
                        return Ok((proof, *parent, parent.before));
                    }
                }
                _ => {}
            }
            current = position.parent;
        }
        Err(LeanCompileError::new("RecursiveFunction/Producer", "The recursive function has no preceding completed declaration in the original source prefix."))
    }

    /// The declaration rule constructs this exact restricted signature before
    /// storing its self membership; it does not run an additional WD verifier.
    pub fn generated_recursive_signature(
        &self,
        object: &Obj,
    ) -> Option<(&'a FnSet, &'a StoreFactAndInferResult, Self)> {
        let mut current = Some(self);
        while let Some(position) = current {
            if let SourceOwner::RecursiveFunction(proof) = position.owner {
                let store = &proof.restricted_self_membership;
                if let StoreFactResult::AtomicFact(stored) = &store.store {
                    if let AtomicFact::InFact(member) = &stored.fact {
                        if let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set {
                            if member.set == *object {
                                return if position.before > 6 {
                                    Some((signature, store, *position))
                                } else {
                                    None
                                };
                            }
                        }
                    }
                }
            }
            current = position.parent;
        }
        None
    }

    pub fn source_fact(
        &self,
        id: FactId,
        runtime: &'a Runtime,
    ) -> Result<&'a Fact, LeanCompileError> {
        let mut position = Some(self);
        let mut captured = None;
        while let Some(current) = position {
            if let SourceOwner::KnownApplication(proof) = current.owner {
                if let Some(fact) = known_application_requirements(proof)
                    .into_iter()
                    .find_map(|(fact, _)| (fact.fact_id() == id).then_some(fact))
                {
                    captured = Some(fact);
                }
            }
            if let SourceOwner::AtomicInference(seed, _) = current.owner {
                if seed.fact_id() == id {
                    captured = Some(seed);
                }
            }
            if let SourceOwner::CompoundInference(store) = current.owner {
                if let Some(InferResult::ChainFact(chain)) = &store.infer {
                    if let Some(edge) = chain
                        .adjacent_infers
                        .iter()
                        .find(|edge| edge.fact.fact_id() == id)
                    {
                        captured = Some(&edge.fact);
                    }
                }
            }
            let env = match current.owner {
                SourceOwner::Named(p) => Some(p.local_env.as_ref()),
                SourceOwner::Template(p) => Some(p.local_env.as_ref()),
                SourceOwner::Claim(p) => Some(p.local_env.as_ref()),
                SourceOwner::Sketch(p) => Some(p.local_env.as_ref()),
                SourceOwner::RangeExpansion(p) => Some(p.local_env.as_ref()),
                SourceOwner::Choice(p) => Some(p.local_env.as_ref()),
                SourceOwner::Zorn(p) => Some(p.local_env.as_ref()),
                SourceOwner::Forall(p) => Some(p.local_env.as_ref()),
                SourceOwner::EmptyForall(p) => Some(p.local_env.as_ref()),
                SourceOwner::ForallWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::NotForallWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::ForallIffWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::ExistWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::WitnessExist(p) => Some(p.local_env.as_ref()),
                SourceOwner::WitnessAtomic(p) => Some(p.local_env.as_ref()),
                SourceOwner::WitnessNonempty(p) => Some(p.local_env.as_ref()),
                SourceOwner::Contra(p) => Some(p.local_env.as_ref()),
                SourceOwner::Extension(p) => Some(p.local_env.as_ref()),
                SourceOwner::FnExtension(p) => Some(p.local_env.as_ref()),
                SourceOwner::OrSelected(p) => Some(p.local_env.as_ref()),
                SourceOwner::EnumerationAssignment(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::CasesBranch(p) => Some(p.local_env.as_ref()),
                SourceOwner::KnownForall(p) => Some(p.well_defined.local_env.as_ref()),
                SourceOwner::Call(p) => Some(p.local_env.as_ref()),
                SourceOwner::ThmRelease(p) => Some(p.local_env.as_ref()),
                SourceOwner::HaveEqualType(p) => Some(p.type_local_env.as_ref()),
                SourceOwner::PropDefinition(p) => Some(p.local_env.as_ref()),
                SourceOwner::StructHeader(p) => Some(p.local_env.as_ref()),
                SourceOwner::StructFields(p) => Some(p.field_scope.field_local_env.as_ref()),
                SourceOwner::ByDef(p) => Some(p.local_env.as_ref()),
                SourceOwner::SetBuilder(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::WD(p) | SourceOwner::WDLocals(p, _) => function_binder(p)
                    .map(|(_, _, _, _, env)| env)
                    .or_else(|| function_argument_scope(p).map(|scope| scope.local_env.as_ref())),
                SourceOwner::CompleteDomainSource(p) => {
                    complete_domain_argument_scope(p).map(|scope| scope.local_env.as_ref())
                }
                SourceOwner::Piecewise(p) => Some(p.env()),
                SourceOwner::RecursiveFunction(p) => Some(p.local_env.as_ref()),
                SourceOwner::RecursiveCase(p) => Some(p.local_env.as_ref()),
                SourceOwner::RecursiveDisjoint(p) => Some(p.local_env.as_ref()),
                SourceOwner::Induction(p) => Some(p.goal_wd_env.as_ref()),
                SourceOwner::InductionCase(_, p) => Some(p.local_env.as_ref()),
                _ => None,
            };
            if let Some(fact) = env.and_then(|env| env.facts.facts_by_id.get(&id)) {
                return Ok(fact);
            }
            position = current.parent;
        }
        runtime.fact_by_id_in_stack(id).or(captured).ok_or_else(|| {
            LeanCompileError::new(
                "FactId/Resolution",
                "The cited fact is absent from the live scope context.",
            )
        })
    }

    pub fn source_wd(
        &self,
        id: WellDefinednessId,
        runtime: &'a Runtime,
    ) -> Result<&'a Obj, LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            let env = match current.owner {
                SourceOwner::Named(p) => Some(p.local_env.as_ref()),
                SourceOwner::Template(p) => Some(p.local_env.as_ref()),
                SourceOwner::Claim(p) => Some(p.local_env.as_ref()),
                SourceOwner::Sketch(p) => Some(p.local_env.as_ref()),
                SourceOwner::RangeExpansion(p) => Some(p.local_env.as_ref()),
                SourceOwner::Choice(p) => Some(p.local_env.as_ref()),
                SourceOwner::Zorn(p) => Some(p.local_env.as_ref()),
                SourceOwner::Forall(p) => Some(p.local_env.as_ref()),
                SourceOwner::EmptyForall(p) => Some(p.local_env.as_ref()),
                SourceOwner::ForallWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::NotForallWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::ForallIffWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::ExistWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::WitnessExist(p) => Some(p.local_env.as_ref()),
                SourceOwner::WitnessAtomic(p) => Some(p.local_env.as_ref()),
                SourceOwner::WitnessNonempty(p) => Some(p.local_env.as_ref()),
                SourceOwner::Contra(p) => Some(p.local_env.as_ref()),
                SourceOwner::Extension(p) => Some(p.local_env.as_ref()),
                SourceOwner::FnExtension(p) => Some(p.local_env.as_ref()),
                SourceOwner::OrSelected(p) => Some(p.local_env.as_ref()),
                SourceOwner::EnumerationAssignment(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::CasesBranch(p) => Some(p.local_env.as_ref()),
                SourceOwner::KnownForall(p) => Some(p.well_defined.local_env.as_ref()),
                SourceOwner::Call(p) => Some(p.local_env.as_ref()),
                SourceOwner::ThmRelease(p) => Some(p.local_env.as_ref()),
                SourceOwner::HaveEqualType(p) => Some(p.type_local_env.as_ref()),
                SourceOwner::PropDefinition(p) => Some(p.local_env.as_ref()),
                SourceOwner::StructHeader(p) => Some(p.local_env.as_ref()),
                SourceOwner::StructFields(p) => Some(p.field_scope.field_local_env.as_ref()),
                SourceOwner::ByDef(p) => Some(p.local_env.as_ref()),
                SourceOwner::SetBuilder(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::WD(p) | SourceOwner::WDLocals(p, _) => function_binder(p)
                    .map(|(_, _, _, _, env)| env)
                    .or_else(|| function_argument_scope(p).map(|scope| scope.local_env.as_ref())),
                SourceOwner::CompleteDomainSource(p) => {
                    complete_domain_argument_scope(p).map(|scope| scope.local_env.as_ref())
                }
                SourceOwner::Piecewise(p) => Some(p.env()),
                SourceOwner::RecursiveFunction(p) => Some(p.local_env.as_ref()),
                SourceOwner::RecursiveCase(p) => Some(p.local_env.as_ref()),
                SourceOwner::RecursiveDisjoint(p) => Some(p.local_env.as_ref()),
                SourceOwner::Induction(p) => Some(p.goal_wd_env.as_ref()),
                SourceOwner::InductionCase(_, p) => Some(p.local_env.as_ref()),
                _ => None,
            };
            if let Some(object) =
                env.and_then(|env| env.well_defined_objects.wd_id_to_object.get(&id))
            {
                return Ok(object);
            }
            position = current.parent;
        }
        for env in runtime.execution_environments_stack.iter().rev() {
            if let Some(object) = env.well_defined_objects.wd_id_to_object.get(&id) {
                return Ok(object);
            }
        }
        Err(LeanCompileError::new(
            "WdId/Resolution",
            "The cited WD record is absent from the live scope context.",
        ))
    }

    /// Env resolution identifies a subject; the result prefix identifies its producer.
    pub fn visible_fact(
        &self,
        id: FactId,
        runtime: &'a Runtime,
    ) -> Result<(&'a Fact, String), LeanCompileError> {
        let actual = self.source_fact(id, runtime)?;
        let mut ceiling = Some(self);
        let mut cancellation_primary_is_stored = false;
        let mut local_primary_is_stored = false;
        while let Some(current) = ceiling {
            // A statement's inner store/inference can publish a fact before
            // the whole statement completes in its enclosing proof block.
            // Its own stage checks below still reject unfinished producers.
            local_primary_is_stored |= cancellation_primary_is_stored;
            if let SourceOwner::PropInference(store) = current.owner {
                if store.primary_fact_id() == id {
                    local_primary_is_stored = true;
                }
            }
            if matches!(
                current.owner,
                SourceOwner::ExistWD(_, _)
                    | SourceOwner::StructLayer(_)
                    | SourceOwner::StructLayers(_)
                    | SourceOwner::HaveEqualType(_)
                    | SourceOwner::StructHeader(_)
                    | SourceOwner::StructFields(_)
                    | SourceOwner::WitnessExist(_)
                    | SourceOwner::WitnessAtomic(_)
                    | SourceOwner::Sketch(_)
                    | SourceOwner::WitnessNonempty(_)
                    | SourceOwner::Contra(_)
                    | SourceOwner::Extension(_)
                    | SourceOwner::FnExtension(_)
                    | SourceOwner::OrSelected(_)
                    | SourceOwner::EnumerationAssignment(..)
                    | SourceOwner::CasesBranch(_)
            ) {
                let complete = SourcePosition {
                    before: usize::MAX,
                    ..*current
                };
                let present = fact_reference_in_owner(current, id, actual)?.is_some();
                if !local_primary_is_stored
                    && fact_reference_in_owner(&complete, id, actual)?.is_some()
                    && !present
                {
                    let scope = match current.owner {
                        SourceOwner::Sketch(..) => "sketch",
                        SourceOwner::StructLayer(..) => "structure release",
                        SourceOwner::StructLayers(..) => "structure auto-open layers",
                        SourceOwner::HaveEqualType(..) => "typed definition preflight",
                        SourceOwner::StructHeader(..) => "structure header",
                        SourceOwner::StructFields(..) => "structure fields",
                        SourceOwner::ExistWD(..) => "existential formation",
                        SourceOwner::WitnessExist(..) => "existential witness",
                        SourceOwner::WitnessAtomic(..) => "atomic witness",
                        SourceOwner::WitnessNonempty(..) => "nonempty witness",
                        SourceOwner::Contra(..) => "contradiction",
                        SourceOwner::Extension(..) => "set extensionality",
                        SourceOwner::FnExtension(..) => "function extensionality",
                        SourceOwner::OrSelected(..) => "selected disjunction branch",
                        SourceOwner::EnumerationAssignment(..) => "finite assignment",
                        SourceOwner::CasesBranch(..) => "case branch",
                        _ => unreachable!("local producer boundary checked above"),
                    };
                    return Err(LeanCompileError::new(
                        "Scope/FutureProducer",
                        &format!(
                            "The producer of h_{} is after stage {} in this {scope}.",
                            id.value(),
                            current.before,
                        ),
                    ));
                }
                local_primary_is_stored |= present;
            }
            if let SourceOwner::Statement(statement) = current.owner {
                if witness_statement(statement).is_some()
                    || nonempty_witness_statement(statement).is_some()
                    || obtain_parts(statement).is_some()
                    || context_parameter_parts(statement).is_some()
                    || matches!(
                        statement,
                        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                            ExecDefineObjStmtResult::HaveObjEqual(_)
                        )) | ExecStmtResult::ReleaseAndExpand(
                            ExecReleaseAndExpandStmtResult::StructDef(_)
                        )
                    )
                    || matches!(
                        statement,
                        ExecStmtResult::By(
                            ExecByStmtResult::Contra(_)
                                | ExecByStmtResult::Cases(_)
                                | ExecByStmtResult::Extension(_)
                                | ExecByStmtResult::FnExtension(_)
                        )
                    )
                {
                    let present =
                        statement_reference(statement, id, actual, None, current.before)?.is_some();
                    if !local_primary_is_stored
                        && statement_reference(statement, id, actual, None, usize::MAX)?.is_some()
                        && !present
                    {
                        return Err(LeanCompileError::new(
                            "Scope/FutureReturn",
                            "The output store is after this original statement stage.",
                        ));
                    }
                    // A completed return inside this statement precedes its
                    // enclosing block's next statement, even while later
                    // returns of the same statement are still being compiled.
                    local_primary_is_stored |= present;
                }
            }
            let recursive_future = match current.owner {
                SourceOwner::Induction(proof) => {
                    (current.before == 0
                        && proof
                            .introduced_parameter
                            .defined_params
                            .stored_fact_ids
                            .contains(&id))
                        || (current.before < 2
                            && proof
                                .goal_domain
                                .store_and_infer
                                .stored_fact_ids()
                                .contains(&id))
                }
                SourceOwner::InductionCase(_, proof) => {
                    (current.before == 0
                        && proof
                            .introduced_parameter
                            .defined_params
                            .stored_fact_ids
                            .contains(&id))
                        || proof
                            .assumptions
                            .iter()
                            .enumerate()
                            .any(|(index, assumption)| {
                                current.before < index + 2
                                    && assumption.store_and_infer.stored_fact_ids().contains(&id)
                            })
                }
                SourceOwner::Piecewise(p) => p
                    .stores()
                    .enumerate()
                    .any(|(i, store)| current.before <= i && store.stored_fact_ids().contains(&id)),
                SourceOwner::Statement(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
                        ExecHaveFnEqualCaseByCaseStmtResult::Success(p),
                    ),
                )) => std::iter::once(&p.store_and_infer_result.membership)
                    .chain(&p.store_and_infer_result.case_defining)
                    .enumerate()
                    .any(|(i, store)| {
                        current.before < 6 + i && store.stored_fact_ids().contains(&id)
                    }),
                SourceOwner::RecursiveFunction(proof) => {
                    (current.before == 0
                        && (proof
                            .binder_introduction
                            .defined_params
                            .stored_fact_ids
                            .contains(&id)
                            || proof
                                .binder_introduction
                                .assumed_dom_facts
                                .iter()
                                .any(|s| s.stored_fact_ids().contains(&id))))
                        || (current.before <= 6
                            && proof
                                .restricted_self_membership
                                .stored_fact_ids()
                                .contains(&id))
                }
                SourceOwner::RecursiveCase(proof) => {
                    current.before == 0 && proof.assumption_stored.stored_fact_ids().contains(&id)
                }
                SourceOwner::RecursiveDisjoint(proof) => {
                    current.before == 0 && proof.assumption_stored.stored_fact_ids().contains(&id)
                }
                SourceOwner::Statement(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveFnByInduc(ExecHaveFnByInducStmtResult::Success(
                        proof,
                    )),
                )) => {
                    current.before < 8 && proof.store_and_infer_result.stored_fact_ids.contains(&id)
                }
                _ => false,
            };
            if recursive_future {
                let route = if matches!(
                    current.owner,
                    SourceOwner::Induction(_) | SourceOwner::InductionCase(_, _)
                ) {
                    "Induction/FutureProducer"
                } else {
                    "RecursiveFunction/FutureProducer"
                };
                return Err(LeanCompileError::new(route, "The cited binder, assumption, self restriction, or final equation store is after this original source stage."));
            }
            // A theorem may return the same FactId as an already proved
            // premise. The later return does not hide that earlier producer.
            if matches!(
                current.owner,
                SourceOwner::Call(_) | SourceOwner::ThmRelease(_)
            ) {
                local_primary_is_stored |= fact_reference_in_owner(current, id, actual)?.is_some();
            }
            if let SourceOwner::Call(proof) = current.owner {
                if proof
                    .type_stores
                    .iter()
                    .skip(current.before)
                    .any(|store| store.stored_fact_ids().contains(&id))
                    && !local_primary_is_stored
                {
                    return Err(LeanCompileError::new(
                        "ByThm/FutureTypeProducer",
                        "The original type store is after its checked membership stage.",
                    ));
                }
                if proof
                    .dom_stores
                    .iter()
                    .skip(current.before.saturating_sub(proof.type_proofs.len()))
                    .any(|store| store.stored_fact_ids().contains(&id))
                    && !local_primary_is_stored
                {
                    return Err(LeanCompileError::new(
                        "ByThm/FutureDomainProducer",
                        "The domain store is after its original verification and inference stage.",
                    ));
                }
                let head =
                    proof.type_proofs.len() + proof.dom_proofs.len() + proof.conclusions_wd.len();
                if proof
                    .returned_conclusions
                    .iter()
                    .skip(current.before.saturating_sub(head))
                    .any(|store| store.stored_fact_ids().contains(&id))
                    && !local_primary_is_stored
                {
                    return Err(LeanCompileError::new("ByThm/FutureProducer", "The returned package is after all conclusion formation and its original store stage."));
                }
            }
            if let SourceOwner::ThmRelease(proof) = current.owner {
                if !local_primary_is_stored
                    && (proof
                        .type_stores
                        .iter()
                        .skip(current.before)
                        .any(|store| store.stored_fact_ids().contains(&id))
                        || proof
                            .dom_stores
                            .iter()
                            .skip(current.before.saturating_sub(proof.type_proofs.len()))
                            .any(|store| store.stored_fact_ids().contains(&id))
                        || proof
                            .stored
                            .iter()
                            .any(|store| store.stored_fact_ids().contains(&id)))
                {
                    return Err(LeanCompileError::new("ReleaseThm/FutureProducer", "The cited type/domain store or caller return is after this original invocation stage."));
                }
            }
            if let SourceOwner::Statement(ExecStmtResult::ReleaseAndExpand(
                ExecReleaseAndExpandStmtResult::Thm(ExecReleaseThmStmtResult::Success(proof)),
            )) = current.owner
            {
                if !local_primary_is_stored
                    && proof
                        .stored
                        .iter()
                        .skip(current.before / 2)
                        .any(|store| store.stored_fact_ids().contains(&id))
                {
                    return Err(LeanCompileError::new(
                        "ReleaseThm/FutureReturn",
                        "The returned package is after its original caller WD/store pair.",
                    ));
                }
            }
            if let SourceOwner::Statement(ExecStmtResult::ReleaseAndExpand(
                ExecReleaseAndExpandStmtResult::ExpandRange(
                    crate::execute::execute_by_stmt::ExecExpandRangeStmtResult::Success(p),
                ),
            )) = current.owner
            {
                if !local_primary_is_stored
                    && current.before <= 1
                    && p.stored.stored_fact_ids().contains(&id)
                {
                    return Err(LeanCompileError::unsupported("ExpandRange/FutureReturn"));
                }
            }
            if let SourceOwner::Statement(ExecStmtResult::ReleaseAndExpand(
                ExecReleaseAndExpandStmtResult::StructDef(
                    crate::execute::ExecReleaseStructDefStmtResult::Success(p),
                ),
            )) = current.owner
            {
                if !local_primary_is_stored
                    && p.release
                        .store_and_infer
                        .iter()
                        .skip(current.before.saturating_sub(1))
                        .any(|store| store.stored_fact_ids().contains(&id))
                {
                    return Err(LeanCompileError::unsupported("StructRelease/FutureReturn"));
                }
            }
            if let SourceOwner::Statement(ExecStmtResult::ReleaseAndExpand(
                ExecReleaseAndExpandStmtResult::CartDef(
                    crate::execute::execute_release_cart_def_stmt::ExecReleaseCartDefStmtResult::Success(proof),
                ),
            )) = current.owner {
                if !local_primary_is_stored && current.before <= 3
                    && proof.store_and_infer.stored_fact_ids().contains(&id) {
                    return Err(LeanCompileError::unsupported("ReleaseCart/FutureReturn"));
                }
            }
            if let SourceOwner::Statement(ExecStmtResult::ReleaseAndExpand(
                ExecReleaseAndExpandStmtResult::TupleDef(
                    crate::execute::execute_release_tuple_def_stmt::ExecReleaseTupleDefStmtResult::Success(proof),
                ),
            )) = current.owner {
                let head = super::compile_release_tuple_def_result::tuple_release_publication_start(proof);
                if !local_primary_is_stored && proof.stored.iter()
                    .skip(current.before.saturating_sub(head)).any(|store| store.stored_fact_ids().contains(&id)) {
                    return Err(LeanCompileError::unsupported("ReleaseTuple/FutureReturn"));
                }
            }
            if let SourceOwner::Statement(ExecStmtResult::ReleaseAndExpand(
                ExecReleaseAndExpandStmtResult::ObjDef(
                    crate::execute::execute_release_obj_def_stmt::ExecReleaseObjDefStmtResult::Success(proof),
                ),
            )) = current.owner {
                if !local_primary_is_stored && proof.store_and_infer.iter()
                    .skip(current.before).any(|store| store.stored_fact_ids().contains(&id)) {
                    return Err(LeanCompileError::unsupported("ReleaseObj/FutureReturn"));
                }
            }
            if let SourceOwner::KnownApplication(proof) = current.owner {
                let completed = current.before.saturating_sub(proof.arg_match_proofs.len());
                if known_application_requirements(proof)
                    .into_iter()
                    .skip(completed)
                    .any(|(fact, _)| fact.fact_id() == id)
                {
                    return Err(LeanCompileError::new("CompoundKnown/FutureRequirement", "Argument matching and requirement replay cannot cite a later application obligation."));
                }
            }
            let cancellation = cancellation_stages(current.owner);
            if let Some((checks, captured)) = &cancellation {
                if current.before > checks.len() && captured.store.primary_fact_id() == id {
                    cancellation_primary_is_stored = true;
                }
            }
            if let SourceOwner::OrderBoundInference(rule) = current.owner {
                let (checks, captured) = order_bound_stages(rule).expect("conditional order owner");
                if current.before > checks.len() && captured.store.primary_fact_id() == id {
                    cancellation_primary_is_stored = true;
                }
                if current.before <= checks.len() && captured.store.stored_fact_ids().contains(&id)
                {
                    return Err(LeanCompileError::new("Inference/FutureProducer", "The conditional order conclusion is after its original certificate/formation stages."));
                }
            }
            if let SourceOwner::PositivePowerTransport(transport) = current.owner {
                if current.before > 2 && transport.derived.store.primary_fact_id() == id {
                    cancellation_primary_is_stored = true;
                }
                if current.before <= 2 && transport.derived.stored_fact_ids().contains(&id) {
                    return Err(LeanCompileError::new("Inference/FutureProducer", "The positive-power conclusion is after its original positivity and real-exponent proofs."));
                }
            }
            if let SourceOwner::PositivePowerInferences(rule) = current.owner {
                if rule
                    .transports
                    .iter()
                    .take(current.before)
                    .any(|transport| transport.derived.store.primary_fact_id() == id)
                {
                    cancellation_primary_is_stored = true;
                }
            }
            if let SourceOwner::ChainClosure(closure) = current.owner {
                if current.before > 0 && closure.derived.store.primary_fact_id() == id {
                    cancellation_primary_is_stored = true;
                }
            }
            if let SourceOwner::AtomicInference(seed, infer) = current.owner {
                if seed.fact_id() == id
                    || atomic_inference_stages_before(infer, current.before)
                        .iter()
                        .any(|captured| captured.store.stored_fact_ids().contains(&id))
                {
                    cancellation_primary_is_stored = true;
                }
            }
            if let SourceOwner::CompoundInference(_) = current.owner {
                if fact_reference_in_owner(current, id, actual)?.is_some() {
                    cancellation_primary_is_stored = true;
                }
            }
            let future = match current.owner {
                // An inner rule may already have published this exact primary
                // fact while an enclosing rule's nested inference is unfinished.
                SourceOwner::EqualityInferences(rules) => {
                    !cancellation_primary_is_stored
                        && rules
                            .iter()
                            .skip(current.before)
                            .any(|rule| rule.stored_fact_ids().contains(&id))
                }
                SourceOwner::PositivePowerInferences(rule) => {
                    !cancellation_primary_is_stored
                        && rule
                            .transports
                            .iter()
                            .skip(current.before)
                            .any(|transport| transport.derived.stored_fact_ids().contains(&id))
                }
                _ => cancellation
                    .as_ref()
                    .map(|(checks, captured)| {
                        current.before <= checks.len()
                            && captured.store.stored_fact_ids().contains(&id)
                    })
                    .unwrap_or(false),
            };
            if future {
                return Err(LeanCompileError::new(
                    "Inference/FutureProducer",
                    "The cited cancellation has not occurred at this original inference stage.",
                ));
            }
            let compound_future = match current.owner {
                SourceOwner::AtomicInference(_, infer) => {
                    !cancellation_primary_is_stored
                        && atomic_inference_future_ids(infer, current.before).contains(&id)
                }
                SourceOwner::CompoundInference(store) => {
                    !cancellation_primary_is_stored
                        && compound_inference_future_ids(store, current.before).contains(&id)
                }
                SourceOwner::ChainClosure(closure) if current.before == 0 => {
                    closure.derived.store.stored_fact_ids().contains(&id)
                }
                _ => false,
            };
            if compound_future {
                return Err(LeanCompileError::new(
                    "Inference/FutureProducer",
                    "The cited compound inference has not occurred at this original stage.",
                ));
            }
            if let SourceOwner::PropInference(store) = current.owner {
                if matches!(
                    &store.infer,
                    Some(InferResult::AndFact(_)) | Some(InferResult::ChainFact(_))
                ) && !cancellation_primary_is_stored
                    && compound_inference_future_ids(store, current.before).contains(&id)
                {
                    return Err(LeanCompileError::new(
                        "Inference/FutureProducer",
                        "The compound store's derived producer is after the active stage.",
                    ));
                }
                let future =
                    if let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
                        &store.infer
                    {
                        !cancellation_primary_is_stored
                            && rules
                                .iter()
                                .skip(current.before)
                                .any(|rule| rule.stored_fact_ids().contains(&id))
                    } else {
                        prop_inference_stages(store)
                            .iter()
                            .skip(current.before)
                            .any(|stage| stage.store.stored_fact_ids().contains(&id))
                    };
                if future {
                    return Err(LeanCompileError::new(
                        "Inference/FutureProducer",
                        "The cited inference has not occurred at this captured formation stage.",
                    ));
                }
            }
            ceiling = current.parent;
        }
        let mut position = Some(self);
        while let Some(current) = position {
            if let Some(reference) = fact_reference_in_owner(current, id, actual)? {
                return Ok((actual, reference));
            }
            position = current.parent;
        }
        Err(LeanCompileError::new(
            "FactId/Producer",
            &format!(
                "FactId {} has no prior producer in the active source results.",
                id.value()
            ),
        ))
    }

    pub fn visible_parameter(
        &self,
        id: IdentifierId,
        runtime: &'a Runtime,
    ) -> Result<(&'a BoundName, Option<&'a Obj>, FactId, String), LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            if matches!(
                current.owner,
                SourceOwner::ExistWD(_, _)
                    | SourceOwner::WitnessExist(_)
                    | SourceOwner::WitnessAtomic(_)
                    | SourceOwner::Sketch(_)
                    | SourceOwner::WitnessNonempty(_)
                    | SourceOwner::Contra(_)
                    | SourceOwner::Extension(_)
                    | SourceOwner::FnExtension(_)
                    | SourceOwner::OrSelected(_)
                    | SourceOwner::EnumerationAssignment(..)
                    | SourceOwner::CasesBranch(_)
            ) {
                let complete = SourcePosition {
                    before: usize::MAX,
                    ..*current
                };
                if parameter_in_owner(&complete, id).is_some()
                    && parameter_in_owner(current, id).is_none()
                {
                    return Err(LeanCompileError::new(
                        "Identifier/FutureProducer",
                        "The local binder is introduced after this source stage.",
                    ));
                }
            }
            if let SourceOwner::Statement(statement) = current.owner {
                if obtain_parts(statement).is_some()
                    && parameter_in_statement(statement, usize::MAX, id).is_some()
                    && parameter_in_statement(statement, current.before, id).is_none()
                {
                    return Err(LeanCompileError::new(
                        "Identifier/FutureProducer",
                        "The obtained binder is introduced after this source stage.",
                    ));
                }
            }
            if let Some((name, carrier, store)) = parameter_in_owner(current, id) {
                let fact_id = store.primary_fact_id();
                let fact = self.source_fact(fact_id, runtime)?;
                let object = Obj::Identifier(IdentifierObj::from_bound_name(name));
                match (fact, carrier) {
                    (Fact::AtomicFact(AtomicFact::InFact(f)), Some(carrier))
                        if f.element.ir() == object.ir() && f.set.ir() == carrier.ir() => {}
                    (Fact::AtomicFact(AtomicFact::IsSetFact(f)), None)
                        if f.set.ir() == object.ir() => {}
                    (Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)), None)
                        if f.set.ir() == object.ir() => {}
                    (Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)), None)
                        if f.set.ir() == object.ir() => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "Parameters/Subject",
                            "The actual parameter store differs from its source header.",
                        ))
                    }
                }
                check_store_subject(&store.store, fact)?;
                let reference = if self.global_obtain_position(id).is_some() {
                    self.visible_fact(fact_id, runtime)?.1
                } else {
                    format!("h_{}", fact_id.value())
                };
                return Ok((name, carrier, fact_id, reference));
            }
            position = current.parent;
        }
        Err(LeanCompileError::new(
            "Identifier/Producer",
            "The identifier has no introduction in the active source results.",
        ))
    }

    /// The original top-level context of an obtained name. Local eliminations
    /// are absent from Run and keep their lexical name without new arguments.
    pub fn global_obtain_position(&self, id: IdentifierId) -> Option<Self> {
        let mut cursor = Some(self);
        while let Some(current) = cursor {
            if let SourceOwner::Statement(statement) = current.owner {
                if obtain_parts(statement)
                    .is_some_and(|(names, _)| names.iter().any(|n| n.id == id))
                {
                    if let Some(parent) = current.parent {
                        if matches!(parent.owner, SourceOwner::Run(_)) {
                            return Some(*parent);
                        }
                    }
                    return None;
                }
            }
            // A nearer lexical binder owns this occurrence. Have-by-existence
            // retains the same IDs inside its existential and in its exported
            // choices; the bound occurrences must not acquire global arguments.
            if !matches!(current.owner, SourceOwner::Run(_))
                && parameter_in_owner(current, id).is_some()
            {
                return None;
            }
            if let SourceOwner::Run(run) = current.owner {
                for (index, statement) in run
                    .statement_results
                    .iter()
                    .take(current.before)
                    .enumerate()
                {
                    if obtain_parts(statement)
                        .is_some_and(|(names, _)| names.iter().any(|n| n.id == id))
                    {
                        return Some(Self {
                            before: index,
                            ..*current
                        });
                    }
                }
            }
            cursor = current.parent;
        }
        None
    }

    pub fn with_visible_wd<T>(
        &self,
        object: &Obj,
        callback: &mut impl FnMut(
            &ObjWellDefinedProof,
            &SourcePosition<'_>,
        ) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let object_ir = object.ir();
        visit_visible(
            self,
            object,
            closed_leaf(object),
            &mut |evidence, position| {
                let SourceConstructor::Checked(proof) = evidence else {
                    return Ok(None);
                };
                if matches!(proof, ObjWellDefinedProof::ByDef { obj, .. } if obj.ir() == object_ir)
                {
                    callback(proof, position).map(Some)
                } else {
                    Ok(None)
                }
            },
            &mut |_, _| Ok(None),
        )
    }

    /// Read only completed statement stores; do not traverse WD/search trees to
    /// discover a registration that already has an exact source-owned identity.
    pub fn registered_wd_reference(
        &self,
        object: &Obj,
        id: Option<WellDefinednessId>,
    ) -> Result<Option<String>, LeanCompileError> {
        self.registered_wd_constructor(object, id, None)
    }

    /// Reuse an earlier host constructor only after the caller has checked the
    /// new occurrence's own WD. No child WD registration is required: a parent
    /// can already retain that certified child in a projection field.
    pub fn compatible_wd_reference(
        &self,
        proof: &ObjWellDefinedProof,
    ) -> Result<Option<String>, LeanCompileError> {
        if matches!(
            proof.obj(),
            Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
        ) {
            return Ok(None);
        }
        if let Some((_, term)) =
            self.bound_constructor(|original| same_wd_constructor(original, proof))
        {
            return Ok(Some(term));
        }
        self.registered_wd_constructor(proof.obj(), None, Some(proof))
    }

    fn registered_wd_constructor(
        &self,
        object: &Obj,
        id: Option<WellDefinednessId>,
        expected: Option<&ObjWellDefinedProof>,
    ) -> Result<Option<String>, LeanCompileError> {
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            if let SourceOwner::PropObjects(proof, completed) = position.owner {
                for assumed in proof.assumed_iff_facts.iter().take(completed).rev() {
                    for subject in &assumed.store_and_infer.formed_subjects {
                        if id.is_some_and(|id| id != subject.wd_id) {
                            continue;
                        }
                        let Some(wd) = super::compile_fact_stmt_result::compile_formed_subjects::assumed_subject_proof(assumed, subject.argument_index)? else { continue; };
                        let term = format!("_object_w{}", subject.wd_id.value());
                        if id.is_some() {
                            if wd.obj() != object {
                                return Err(LeanCompileError::new(
                                    "WD/Registration",
                                    "Registered WD id has another subject.",
                                ));
                            }
                            return Ok(Some(term));
                        }
                        if let Some((_, term)) = projected_wd_child(wd, term, &|child| {
                            child.obj() == object
                                && expected
                                    .is_none_or(|expected| same_wd_constructor(child, expected))
                        }) {
                            return Ok(Some(term));
                        }
                    }
                }
            }
            let (children, scope, completed) = match position.owner {
                SourceOwner::WDLocals(proof, emitted) => (
                    arithmetic_stages(proof).map(|(children, _)| children),
                    function_argument_scope(proof), emitted),
                SourceOwner::WD(proof) => (
                    arithmetic_stages(proof).map(|(children, _)| children),
                    function_argument_scope(proof), position.before),
                SourceOwner::CompleteDomainSource(proof) => match &proof.source {
                    crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof::ApplicationReturn { application_children, argument_scope, .. } =>
                        (Some(application_children.as_slice()), argument_scope.as_ref(), position.before),
                    _ => (None, None, 0),
                },
                _ => (None, None, 0),
            };
            if let Some(scope) = scope {
                if let Some(id) = id {
                    if scope
                        .local_env
                        .well_defined_objects
                        .wd_id_to_object
                        .contains_key(&id)
                        && !scope
                            .formed_children
                            .iter()
                            .any(|formed| formed.wd_id == id)
                    {
                        return Err(LeanCompileError::new(
                            "WD/FnObj/Registration",
                            "The local WD ID has no recorded argument producer.",
                        ));
                    }
                }
                for formed in &scope.formed_children {
                    let stored = scope
                        .local_env
                        .well_defined_objects
                        .wd_id_to_object
                        .get(&formed.wd_id);
                    let selected = match id {
                        Some(id) => id == formed.wd_id,
                        None => stored.is_some_and(|subject| subject == object),
                    };
                    if !selected {
                        continue;
                    }
                    if formed.child_index >= completed {
                        if id.is_some() {
                            return Err(LeanCompileError::new(
                                "WD/FnObj/ForwardReference",
                                "The argument WD producer has not completed.",
                            ));
                        }
                        continue;
                    }
                    let original = children.and_then(|children| children.get(formed.child_index));
                    let Some(original) = original else {
                        return Err(LeanCompileError::new(
                            "WD/FnObj/Registration",
                            "The WD registration has no producing child.",
                        ));
                    };
                    if stored != Some(object) || original.obj() != object {
                        return Err(LeanCompileError::new(
                            "WD/FnObj/Registration",
                            "The WD registration and producing child have different subjects.",
                        ));
                    }
                    if expected.is_none_or(|expected| same_wd_constructor(original, expected)) {
                        if let Some(term) = self.bound_wd_child(original) {
                            return Ok(Some(term));
                        }
                    }
                }
            }
            cursor = position.parent;
        }
        if matches!(
            object,
            Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
        ) {
            return Ok(None);
        }
        fn in_result(
            verify: &VerifyFactResult,
            store: &StoreFactAndInferResult,
            producer: &SourcePosition<'_>,
            active: &SourcePosition<'_>,
            object: &Obj,
            id: Option<WellDefinednessId>,
            expected: Option<&ObjWellDefinedProof>,
        ) -> Result<Option<String>, LeanCompileError> {
            if !obeys_active_stage_ceilings(active, producer) {
                return Ok(None);
            }
            for subject in &store.formed_subjects {
                if id.is_some_and(|id| id != subject.wd_id) {
                    continue;
                }
                let proof =
                    super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
                        verify,
                        subject.argument_index,
                    )?;
                if let Some(proof) = proof {
                    let name = format!("_object_w{}", subject.wd_id.value());
                    let term = if producer.is_local() {
                        name
                    } else {
                        producer.context_application(&name)
                    };
                    if id.is_some() {
                        if proof.obj() == object {
                            return Ok(Some(term));
                        }
                    } else if let Some((_, term)) = projected_wd_child(proof, term, &|child| {
                        child.obj() == object
                            && expected.is_none_or(|expected| same_wd_constructor(child, expected))
                    }) {
                        return Ok(Some(term));
                    }
                }
            }
            Ok(None)
        }
        let in_statement = |statement: &ExecStmtResult, producer: &SourcePosition<'_>| {
            match statement {
                ExecStmtResult::Fact(ExecFactStmtResult::Success(result)) => in_result(
                    &result.verify_result,
                    &result.store_and_infer_result,
                    producer,
                    self,
                    object,
                    id,
                    expected,
                ),
                ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                    ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(
                        proof,
                    )),
                )) => {
                    let count = proof.statement.objs_equal_to.len();
                    for (index, parameter) in proof
                        .statement
                        .param_def
                        .groups
                        .iter()
                        .flat_map(|group| &group.params)
                        .enumerate()
                    {
                        let ready = SourcePosition {
                            before: 2 * count + index + 1,
                            ..*producer
                        };
                        if producer.before < ready.before
                            || !obeys_active_stage_ceilings(self, &ready)
                        {
                            continue;
                        }
                        let Some(store) = proof
                            .store_and_infer_result
                            .store_and_infer_results
                            .get(count + index)
                        else {
                            return Err(LeanCompileError::new(
                                "WD/HaveEqualRegistration",
                                "Missing original equality store.",
                            ));
                        };
                        for subject in &store.formed_subjects {
                            if id.is_some_and(|id| id != subject.wd_id) {
                                continue;
                            }
                            // The alias is the original certified RHS value. Its equality
                            // store registers argument 1; argument 0 is the named alias.
                            if subject.argument_index != 1 {
                                return Err(LeanCompileError::new(
                                    "WD/HaveEqualRegistration",
                                    "Registration is not the original RHS argument.",
                                ));
                            }
                            let value = &proof.statement.objs_equal_to[index];
                            let checked = super::helper::success_object_wd(
                                &proof.equal_to_well_defined[index],
                                value,
                            )?;
                            let name = format!("_object_i{}", parameter.id.value());
                            let term = if producer.is_local() {
                                name
                            } else {
                                producer.context_application(&name)
                            };
                            if id.is_some() {
                                if checked.obj() != object {
                                    return Err(LeanCompileError::new(
                                        "WD/HaveEqualRegistration",
                                        "WD id refers to another declared value.",
                                    ));
                                }
                                return Ok(Some(term));
                            }
                            if let Some((_, term)) = projected_wd_child(checked, term, &|child| {
                                child.obj() == object
                                    && expected
                                        .is_none_or(|expected| same_wd_constructor(child, expected))
                            }) {
                                return Ok(Some(term));
                            }
                        }
                    }
                    Ok(None)
                }
                _ => Ok(None),
            }
        };
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            if let SourceOwner::Statement(statement) = position.owner {
                if position.before > 0 {
                    if let Some(name) = in_statement(statement, position)? {
                        return Ok(Some(name));
                    }
                }
            }
            let statements = match position.owner {
                SourceOwner::Run(run) => Some((run.statement_results.as_slice(), 0)),
                SourceOwner::Named(proof) => Some(named_steps(proof)),
                SourceOwner::Claim(proof) => Some(claim_steps(proof)),
                owner => local_steps(owner),
            };
            if let Some((statements, head)) = statements {
                for (index, statement) in statements
                    .iter()
                    .take(position.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    let completed = SourcePosition {
                        before: head + index + 1,
                        ..*position
                    };
                    if !obeys_active_stage_ceilings(self, &completed) {
                        continue;
                    }
                    let prior = SourcePosition {
                        before: head + index,
                        ..*position
                    };
                    let producer = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::Statement(statement),
                        usize::MAX,
                    );
                    if let Some(name) = in_statement(statement, &producer)? {
                        return Ok(Some(name));
                    }
                }
            }
            if let SourceOwner::Forall(proof) = position.owner {
                let head = parameter_count(&proof.fact.typed_parameters.groups)
                    + proof.assumed_dom_facts.len();
                for (index, conclusion) in proof
                    .proved_then_facts
                    .iter()
                    .take(position.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    let producer = SourcePosition {
                        before: head + index + 1,
                        ..*position
                    };
                    if let Some(name) = in_result(
                        &conclusion.verify_result,
                        &conclusion.store_and_infer,
                        &producer,
                        self,
                        object,
                        id,
                        expected,
                    )? {
                        return Ok(Some(name));
                    }
                }
            }
            cursor = position.parent;
        }
        Ok(None)
    }

    pub fn with_visible_inferred_subject<T>(
        &self,
        object: &Obj,
        callback: &mut impl FnMut(&StoreFactResult, &SourcePosition<'_>) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        self.with_visible_inferred_subject_filter(object, &mut |store, producer| {
            callback(store, producer).map(Some)
        })
    }

    pub fn with_visible_inferred_subject_filter<T>(
        &self,
        object: &Obj,
        callback: &mut impl FnMut(
            &StoreFactResult,
            &SourcePosition<'_>,
        ) -> Result<Option<T>, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let object_ir = object.ir();
        visit_visible(
            self,
            object,
            true,
            &mut |evidence, position| {
                let SourceConstructor::Inferred(store) = evidence else {
                    return Ok(None);
                };
                if store.atomic_components().iter().any(|(_, fact)| {
                    atomic_fact_args_ref(fact)
                        .iter()
                        .any(|arg| arg.ir() == object_ir)
                }) {
                    callback(store, position)
                } else {
                    Ok(None)
                }
            },
            &mut |_, _| Ok(None),
        )
    }

    pub fn inferred_builder_step(
        &self,
        store: &StoreFactResult,
    ) -> Option<&'a crate::store_fact_and_infer::SetBuilderMembershipProjectionStep> {
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            let rules = match position.owner {
                SourceOwner::PropInference(p) => match &p.infer {
                    Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(r))) => Some(r),
                    _ => None,
                },
                SourceOwner::AtomicInference(_, InferAtomicFactResult::InFact(r)) => Some(r),
                _ => None,
            };
            if let Some(rules) = rules {
                for rule in rules {
                    if let InferInFactResult::SetBuilder(proof) = rule {
                        for step in &proof.steps {
                            if step
                                .projections
                                .iter()
                                .any(|p| std::ptr::eq(&p.stored().store, store))
                            {
                                return Some(step);
                            }
                        }
                    }
                }
            }
            cursor = position.parent;
        }
        None
    }

    pub fn inferred_preimage_step(
        &self,
        store: &StoreFactResult,
    ) -> Option<(
        FactId,
        &'a KnownEqualityPathProof,
        &'a crate::store_fact_and_infer::InferPreimageConstructionResult,
    )> {
        let mut cursor = Some(self);
        while let Some(position) = cursor {
            let rules = match position.owner {
                SourceOwner::PropInference(p) => match &p.infer {
                    Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(r))) => Some(r),
                    _ => None,
                },
                SourceOwner::AtomicInference(_, InferAtomicFactResult::InFact(r)) => Some(r),
                _ => None,
            };
            if let Some(rules) = rules {
                for rule in rules {
                    let (id, path, construction, derived) = match rule {
                        InferInFactResult::Preimage(p) => (
                            p.source_fact_id,
                            &p.source_equal,
                            &p.construction,
                            &p.derived,
                        ),
                        InferInFactResult::PreimageSet(p) => (
                            p.source_fact_id,
                            &p.source_equal,
                            &p.construction,
                            &p.derived,
                        ),
                        _ => continue,
                    };
                    if derived.iter().any(|p| std::ptr::eq(&p.store, store)) {
                        return Some((id, path, construction));
                    }
                }
            }
            cursor = position.parent;
        }
        None
    }

    pub fn with_visible_nonzero<T>(
        &self,
        object: &Obj,
        callback: &mut impl FnMut(FactId, &SourcePosition<'_>) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let object_ir = object.ir();
        let inferred = visit_visible(
            self,
            object,
            true,
            &mut |evidence, producer| {
                let SourceConstructor::Inferred(store) = evidence else {
                    return Ok(None);
                };
                for (id, fact) in store.atomic_components() {
                    if matches!(&fact, AtomicFact::NotEqualFact(f)
                        if f.left.ir() == object_ir && super::helper::is_exact_zero(&f.right))
                    {
                        return callback(id, producer).map(Some);
                    }
                }
                Ok(None)
            },
            &mut |_, _| Ok(None),
        )?;
        if inferred.is_some() {
            return Ok(inferred);
        }
        visit_visible(
            self,
            object,
            false,
            &mut |_, _| Ok(None),
            &mut |proof, producer| {
                if let Some(Fact::AtomicFact(AtomicFact::NotEqualFact(fact))) =
                    verified_subject(proof)
                {
                    if fact.left.ir() == object_ir && super::helper::is_exact_zero(&fact.right) {
                        return callback(fact.fact_id, producer).map(Some);
                    }
                }
                Ok(None)
            },
        )
    }

    pub fn with_visible_membership<T>(
        &self,
        object: &Obj,
        set: &Obj,
        callback: &mut impl FnMut(&VerifyFactResult, &SourcePosition<'_>) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let object_ir = object.ir();
        let set_ir = set.ir();
        visit_visible(
            self,
            object,
            false,
            &mut |_, _| Ok(None),
            &mut |proof, position| match verified_subject(proof) {
                Some(Fact::AtomicFact(AtomicFact::InFact(f)))
                    if f.element.ir() == object_ir && f.set.ir() == set_ir =>
                {
                    callback(proof, position).map(Some)
                }
                _ => Ok(None),
            },
        )
    }

    pub fn with_visible_alias<T>(
        &self,
        object: &Obj,
        callback: &mut impl FnMut(
            &BoundName,
            &Obj,
            &VerifyObjWellDefinedResult,
            &SourcePosition<'_>,
        ) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let mut cursor = Some(self);
        while let Some(current) = cursor {
            let steps = match current.owner {
                SourceOwner::Run(run) => Some((run.statement_results.as_slice(), 0)),
                SourceOwner::Named(proof) => Some(named_steps(proof)),
                SourceOwner::Claim(proof) => Some(claim_steps(proof)),
                SourceOwner::InductionCase(_, proof) => {
                    Some((proof.proof_steps.as_slice(), 1 + proof.assumptions.len()))
                }
                _ => local_steps(current.owner),
            };
            if let Some((steps, head)) = steps {
                for (index, statement) in steps
                    .iter()
                    .take(current.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    let completed = Self {
                        before: head + index + 1,
                        ..*current
                    };
                    if !obeys_active_stage_ceilings(self, &completed) {
                        continue;
                    }
                    let prior = Self {
                        before: head + index,
                        ..*current
                    };
                    if let Some(value) =
                        alias_in_statement(statement, object, usize::MAX, &prior, self, callback)?
                    {
                        return Ok(Some(value));
                    }
                }
            }
            if let SourceOwner::Statement(statement) = current.owner {
                if let Some(parent) = current.parent {
                    if let Some(value) = alias_in_statement(
                        statement,
                        object,
                        current.before,
                        parent,
                        self,
                        callback,
                    )? {
                        return Ok(Some(value));
                    }
                }
            }
            cursor = current.parent;
        }
        Ok(None)
    }

    /// Borrow only active or completed obtain results in the lexical prefix.
    /// The callback keeps the original producer context when used later.
    pub fn with_visible_obtain<T>(
        &self,
        callback: &mut impl FnMut(
            &ExecDefineObjStmtResult,
            &SourcePosition<'_>,
        ) -> Result<Option<T>, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let mut cursor = Some(self);
        while let Some(current) = cursor {
            let steps = match current.owner {
                SourceOwner::Run(run) => Some((run.statement_results.as_slice(), 0)),
                SourceOwner::Named(proof) => Some(named_steps(proof)),
                SourceOwner::Claim(proof) => Some(claim_steps(proof)),
                SourceOwner::InductionCase(_, proof) => {
                    Some((proof.proof_steps.as_slice(), 1 + proof.assumptions.len()))
                }
                _ => local_steps(current.owner),
            };
            if let Some((steps, head)) = steps {
                for (index, statement) in steps
                    .iter()
                    .take(current.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    let completed = Self {
                        before: head + index + 1,
                        ..*current
                    };
                    if !obeys_active_stage_ceilings(self, &completed) {
                        continue;
                    }
                    let prior = Self {
                        before: head + index,
                        ..*current
                    };
                    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                        proof @ (ExecDefineObjStmtResult::HaveObjByExistFacts(
                            ExecHaveObjByExistFactsStmtResult::Success(_),
                        )
                        | ExecDefineObjStmtResult::ObtainObjFromExistFact(
                            ExecObtainObjFromExistFactStmtResult::Success(_),
                        )
                        | ExecDefineObjStmtResult::HaveByFnPreimage(
                            crate::execute::ExecHaveByFnPreimageStmtResult::Success(_),
                        )
                        | ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                            ExecObtainObjFromAtomicFactStmtResult::Success(_),
                        )),
                    )) = statement
                    {
                        let producer = SourcePosition::new(
                            Some(&prior),
                            SourceOwner::Statement(statement),
                            usize::MAX,
                        );
                        if !obeys_active_stage_ceilings(self, &producer) {
                            continue;
                        }
                        if let Some(value) = callback(proof, &producer)? {
                            return Ok(Some(value));
                        }
                    }
                }
            }
            if let SourceOwner::Statement(ExecStmtResult::Definition(
                ExecDefinitionStmtResult::DefineObj(
                    proof @ (ExecDefineObjStmtResult::HaveObjByExistFacts(
                        ExecHaveObjByExistFactsStmtResult::Success(_),
                    )
                    | ExecDefineObjStmtResult::ObtainObjFromExistFact(
                        ExecObtainObjFromExistFactStmtResult::Success(_),
                    )
                    | ExecDefineObjStmtResult::HaveByFnPreimage(
                        crate::execute::ExecHaveByFnPreimageStmtResult::Success(_),
                    )
                    | ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                        ExecObtainObjFromAtomicFactStmtResult::Success(_),
                    )),
                ),
            )) = current.owner
            {
                if obeys_active_stage_ceilings(self, current) {
                    if let Some(value) = callback(proof, current)? {
                        return Ok(Some(value));
                    }
                }
            }
            cursor = current.parent;
        }
        Ok(None)
    }

    pub fn callee_header(&self) -> Option<&Self> {
        let mut position = Some(self);
        while let Some(current) = position {
            if matches!(
                current.owner,
                SourceOwner::Forall(_) | SourceOwner::ForallWD(_, _) | SourceOwner::Induction(_)
            ) {
                return Some(current);
            }
            position = current.parent;
        }
        None
    }

    pub fn with_visible_callee_instance<T>(
        &self,
        callback: &mut impl FnMut(
            &SearchProofByKnownForallFact,
            &SourcePosition<'_>,
        ) -> Result<Option<T>, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            if let Some((steps, head)) = local_steps(current.owner) {
                for (index, statement) in steps
                    .iter()
                    .take(current.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    let prior = SourcePosition {
                        before: head + index,
                        ..*current
                    };
                    let completed = SourcePosition {
                        before: head + index + 1,
                        ..*current
                    };
                    if !obeys_active_stage_ceilings(self, &completed) {
                        continue;
                    }
                    if let Some(proof) = statement_known_application(statement) {
                        let caller =
                            SourcePosition::new(Some(&prior), SourceOwner::Statement(statement), 0);
                        if let Some(value) = callback(proof, &caller)? {
                            return Ok(Some(value));
                        }
                    }
                }
            }
            match current.owner {
                SourceOwner::CalleeInstance(proof) => {
                    let mut caller = current
                        .parent
                        .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeCaller"))?;
                    if matches!(caller.owner, SourceOwner::KnownApplication(other) if std::ptr::eq(other, proof))
                    {
                        caller = caller
                            .parent
                            .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeCaller"))?;
                    }
                    if let Some(value) = callback(proof, caller)? {
                        return Ok(Some(value));
                    }
                }
                SourceOwner::InductionCase(_, proof) => {
                    let head = 1 + proof.assumptions.len();
                    for (index, statement) in proof
                        .proof_steps
                        .iter()
                        .take(current.before.saturating_sub(head))
                        .enumerate()
                        .rev()
                    {
                        if let Some(proof) = statement_known_application(statement) {
                            let prior = SourcePosition {
                                before: head + index,
                                ..*current
                            };
                            let caller = SourcePosition::new(
                                Some(&prior),
                                SourceOwner::Statement(statement),
                                0,
                            );
                            if let Some(value) = callback(proof, &caller)? {
                                return Ok(Some(value));
                            }
                        }
                    }
                }
                SourceOwner::Statement(statement) if current.before > 0 => {
                    if let Some(proof) = statement_known_application(statement) {
                        let prior = SourcePosition {
                            before: 0,
                            ..*current
                        };
                        if let Some(value) = callback(proof, &prior)? {
                            return Ok(Some(value));
                        }
                    }
                }
                SourceOwner::Run(run) => {
                    for (index, statement) in run
                        .statement_results
                        .iter()
                        .take(current.before)
                        .enumerate()
                        .rev()
                    {
                        if let Some(proof) = statement_known_application(statement) {
                            let prior = SourcePosition::new(None, SourceOwner::Run(run), index);
                            let caller = SourcePosition::new(
                                Some(&prior),
                                SourceOwner::Statement(statement),
                                0,
                            );
                            if let Some(value) = callback(proof, &caller)? {
                                return Ok(Some(value));
                            }
                        }
                    }
                }
                SourceOwner::Named(proof) => {
                    let (steps, head) = named_steps(proof);
                    for (index, statement) in steps
                        .iter()
                        .take(current.before.saturating_sub(head))
                        .enumerate()
                        .rev()
                    {
                        if let Some(proof) = statement_known_application(statement) {
                            let prior = SourcePosition {
                                before: head + index,
                                ..*current
                            };
                            let caller = SourcePosition::new(
                                Some(&prior),
                                SourceOwner::Statement(statement),
                                0,
                            );
                            if let Some(value) = callback(proof, &caller)? {
                                return Ok(Some(value));
                            }
                        }
                    }
                }
                SourceOwner::Claim(proof) => {
                    let (steps, head) = claim_steps(proof);
                    for (index, statement) in steps
                        .iter()
                        .take(current.before.saturating_sub(head))
                        .enumerate()
                        .rev()
                    {
                        if let Some(proof) = statement_known_application(statement) {
                            let prior = SourcePosition {
                                before: head + index,
                                ..*current
                            };
                            let caller = SourcePosition::new(
                                Some(&prior),
                                SourceOwner::Statement(statement),
                                0,
                            );
                            if let Some(value) = callback(proof, &caller)? {
                                return Ok(Some(value));
                            }
                        }
                    }
                }
                _ => {}
            }
            position = current.parent;
        }
        Ok(None)
    }

    pub fn with_visible_forall_constructor<T>(
        &self,
        id: FactId,
        then_index: usize,
        pattern: &Obj,
        callback: &mut impl FnMut(
            &ForallFact,
            &IntroduceTypedParametersResult,
            &[AssumeDomFactResult],
            &ObjWellDefinedProof,
            &SourcePosition<'_>,
            &SourcePosition<'_>,
        ) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            if let Some((steps, head)) = local_steps(current.owner) {
                for (index, statement) in steps
                    .iter()
                    .take(current.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    let prior = SourcePosition {
                        before: head + index,
                        ..*current
                    };
                    let completed = SourcePosition {
                        before: head + index + 1,
                        ..*current
                    };
                    if !obeys_active_stage_ceilings(self, &completed) {
                        continue;
                    }
                    if let Some(owner) = statement_forall_constructor_owner(statement, id) {
                        let declaration =
                            SourcePosition::new(Some(&prior), SourceOwner::Statement(statement), 0);
                        return visit_forall_constructor(
                            owner,
                            then_index,
                            pattern,
                            &declaration,
                            callback,
                        );
                    }
                }
            }
            match current.owner {
                SourceOwner::InductionCase(_, proof) => {
                    let head = 1 + proof.assumptions.len();
                    for (index, statement) in proof
                        .proof_steps
                        .iter()
                        .take(current.before.saturating_sub(head))
                        .enumerate()
                        .rev()
                    {
                        if let Some(owner) = statement_forall_constructor_owner(statement, id) {
                            let prior = SourcePosition {
                                before: head + index,
                                ..*current
                            };
                            let declaration = SourcePosition::new(
                                Some(&prior),
                                SourceOwner::Statement(statement),
                                0,
                            );
                            return visit_forall_constructor(
                                owner,
                                then_index,
                                pattern,
                                &declaration,
                                callback,
                            );
                        }
                    }
                }
                SourceOwner::Run(run) => {
                    for (index, statement) in run
                        .statement_results
                        .iter()
                        .take(current.before)
                        .enumerate()
                        .rev()
                    {
                        if let Some(owner) = statement_forall_constructor_owner(statement, id) {
                            let prior = SourcePosition::new(None, SourceOwner::Run(run), index);
                            let declaration = SourcePosition::new(
                                Some(&prior),
                                SourceOwner::Statement(statement),
                                0,
                            );
                            return visit_forall_constructor(
                                owner,
                                then_index,
                                pattern,
                                &declaration,
                                callback,
                            );
                        }
                    }
                }
                SourceOwner::Named(proof) => {
                    let (steps, head) = named_steps(proof);
                    for (index, statement) in steps
                        .iter()
                        .take(current.before.saturating_sub(head))
                        .enumerate()
                        .rev()
                    {
                        if let Some(owner) = statement_forall_constructor_owner(statement, id) {
                            let prior = SourcePosition {
                                before: head + index,
                                ..*current
                            };
                            let declaration = SourcePosition::new(
                                Some(&prior),
                                SourceOwner::Statement(statement),
                                0,
                            );
                            return visit_forall_constructor(
                                owner,
                                then_index,
                                pattern,
                                &declaration,
                                callback,
                            );
                        }
                    }
                }
                SourceOwner::Claim(proof) => {
                    let (steps, head) = claim_steps(proof);
                    for (index, statement) in steps
                        .iter()
                        .take(current.before.saturating_sub(head))
                        .enumerate()
                        .rev()
                    {
                        if let Some(owner) = statement_forall_constructor_owner(statement, id) {
                            let prior = SourcePosition {
                                before: head + index,
                                ..*current
                            };
                            let declaration = SourcePosition::new(
                                Some(&prior),
                                SourceOwner::Statement(statement),
                                0,
                            );
                            return visit_forall_constructor(
                                owner,
                                then_index,
                                pattern,
                                &declaration,
                                callback,
                            );
                        }
                    }
                }
                _ => {}
            }
            position = current.parent;
        }
        Ok(None)
    }
}

pub(super) fn context_parameter_parts(
    statement: &ExecStmtResult,
) -> Option<(&[TypedParameterGroup], &StoreHaveObjAndInferResult)> {
    if let Some(p) = ordinary_have(statement) {
        Some((&p.statement.param_def.groups, &p.store_and_infer_result))
    } else {
        trust_have(statement).map(|p| {
            (
                p.statement.param_def.groups.as_slice(),
                &p.defined_param_store_and_infer,
            )
        })
    }
}

pub(super) fn append_have_parameters<'a>(
    statement: &'a ExecStmtResult,
    before: usize,
    out: &mut Vec<(&'a BoundName, Option<&'a Obj>, FactId)>,
) {
    let Some((groups, stores)) = context_parameter_parts(statement) else {
        return;
    };
    let mut index = 0;
    for group in groups {
        for parameter in &group.params {
            if index >= before {
                return;
            }
            let carrier = match &group.param_type {
                ParamType::Obj(carrier) => Some(carrier),
                ParamType::Set(_) => None,
                _ => {
                    index += 1;
                    continue;
                }
            };
            if let Some(store) = stores.store_and_infer_results.get(index) {
                out.push((parameter, carrier, store.primary_fact_id()));
            }
            index += 1;
        }
    }
}

fn context_arguments_before(run: &RunLitexCodeResult, before: usize) -> Vec<String> {
    let mut arguments = Vec::new();
    for statement in run.statement_results.iter().take(before) {
        if context_parameter_parts(statement).is_some() {
            let mut parameters = Vec::new();
            append_have_parameters(statement, usize::MAX, &mut parameters);
            for (parameter, _, fact_id) in parameters {
                let id = parameter.id.value();
                arguments.extend([
                    format!("_Host_i{id}"),
                    format!("_rep_i{id}"),
                    format!("_value_i{id}"),
                    format!("h_{}", fact_id.value()),
                ]);
            }
        }
    }
    arguments
}

fn hypotheses_before(run: &RunLitexCodeResult, before: usize) -> Vec<FactId> {
    SourcePosition::new(None, SourceOwner::Run(run), before).context_hypotheses()
}

fn abstract_props_before(
    run: &RunLitexCodeResult,
    before: usize,
) -> Vec<(&DefAbstractPropStmt, usize)> {
    run.statement_results
        .iter()
        .take(before)
        .enumerate()
        .filter_map(|(index, statement)| match statement {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefAbstractProp(
                ExecDefAbstractPropStmtResult::Success(proof),
            )) => Some((&proof.statement, index + 1)),
            _ => None,
        })
        .collect()
}

fn abstract_arguments_before(run: &RunLitexCodeResult, before: usize) -> Vec<String> {
    abstract_props_before(run, before)
        .into_iter()
        .map(|(_, index)| format!("abstract_prop_{index}"))
        .collect()
}

fn application(
    name: &str,
    arguments: &[String],
    predicates: &[String],
    hypotheses: &[FactId],
) -> String {
    let hypotheses = hypotheses
        .iter()
        .map(|id| format!(" (h_{0} := h_{0})", id.value()))
        .collect::<String>();
    let predicate_arguments = if predicates.is_empty() {
        String::new()
    } else {
        format!(" {}", predicates.join(" "))
    };
    if arguments.is_empty() {
        format!("({name} (M := M){predicate_arguments}{hypotheses})")
    } else {
        let arguments = arguments
            .chunks_exact(4)
            .map(|group| {
                format!(
                    "({} := {}) ({} := {}) {} {}",
                    group[0], group[0], group[1], group[1], group[2], group[3]
                )
            })
            .collect::<Vec<_>>()
            .join(" ");
        format!("({name} (M := M){predicate_arguments} {arguments}{hypotheses})")
    }
}

pub(super) fn ordinary_have(
    statement: &ExecStmtResult,
) -> Option<&ExecHaveObjInNonemptySetStmtSuccessResult> {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(p),
            ),
        )) => Some(p),
        _ => None,
    }
}

fn parameter_from_groups<'a>(
    groups: &'a [TypedParameterGroup],
    stores: &'a [std::rc::Rc<StoreFactAndInferResult>],
    before: usize,
    id: IdentifierId,
) -> Option<(&'a BoundName, Option<&'a Obj>, &'a StoreFactAndInferResult)> {
    let mut index = 0;
    for group in groups {
        for parameter in &group.params {
            if index < before && parameter.id == id {
                let carrier = match &group.param_type {
                    ParamType::Obj(carrier) => Some(carrier),
                    ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => None,
                };
                return stores
                    .get(index)
                    .map(|store| (parameter, carrier, store.as_ref()));
            }
            index += 1;
        }
    }
    None
}

// These views borrow the original stage owners; they do not cache introductions or proofs.
fn nonempty_witness_statement(
    statement: &ExecStmtResult,
) -> Option<&ExecWitnessNonemptySetStmtSuccessResult> {
    match statement {
        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessNonemptySet(
            ExecWitnessNonemptySetStmtResult::Success(p),
        )) => Some(p),
        _ => None,
    }
}

fn local_steps(owner: SourceOwner<'_>) -> Option<(&[ExecStmtResult], usize)> {
    match owner {
        SourceOwner::Template(p) => Some((
            std::slice::from_ref(p.body.as_ref()),
            p.statement.template_arg_def.ordered_param_ids().len() + p.assumed_dom_facts.len(),
        )),
        SourceOwner::Sketch(p) => Some((&p.proof_steps, 0)),
        SourceOwner::Choice(p) => Some((&p.proof_steps, 0)),
        SourceOwner::Zorn(p) => Some((&p.proof_steps, 0)),
        SourceOwner::WitnessExist(p) => Some((
            &p.proof_steps,
            p.introduced_params
                .defined_params
                .store_and_infer_results
                .len()
                + p.witness_equalities.len(),
        )),
        SourceOwner::WitnessAtomic(p) => Some((
            &p.proof_steps,
            p.introduced_params
                .defined_params
                .store_and_infer_results
                .len()
                + p.witness_equalities.len(),
        )),
        SourceOwner::WitnessNonempty(p) => Some((&p.proof_steps, 0)),
        SourceOwner::Contra(p) => Some((&p.proof_steps, 2)),
        SourceOwner::Extension(p) => Some((&p.proof_steps, 0)),
        SourceOwner::FnExtension(p) => Some((&p.proof_steps, 0)),
        SourceOwner::EnumerationAssignment(_, p) => {
            let (premises, steps, _) = enumeration_outcome(p);
            Some((
                steps,
                p.introduced_params
                    .defined_params
                    .store_and_infer_results
                    .len()
                    + p.binding_assumptions.len()
                    + premises.len(),
            ))
        }
        SourceOwner::CasesBranch(p) => Some((&p.proof_steps, 2)),
        _ => None,
    }
}

fn witness_header(
    owner: SourceOwner<'_>,
) -> Option<(
    &PlainExistFact,
    &IntroduceTypedParametersResult,
    &[StoreFactAndInferResult],
)> {
    match owner {
        SourceOwner::WitnessExist(p) => Some((
            p.statement.exist_shaped_fact_in_witness.plain(),
            &p.introduced_params,
            &p.witness_equalities,
        )),
        SourceOwner::WitnessAtomic(p) => Some((
            p.projected_exist.plain(),
            &p.introduced_params,
            &p.witness_equalities,
        )),
        _ => None,
    }
}

fn witness_statement(
    statement: &ExecStmtResult,
) -> Option<(
    &WitnessExistAmbientSuccess,
    &[VerifyFactResult],
    SourceOwner<'_>,
    &StoreFactAndInferResult,
)> {
    match statement {
        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
            ExecWitnessExistFactStmtResult::Success(p),
        )) => Some((
            &p.ambient,
            &[],
            SourceOwner::WitnessExist(p),
            &p.store_and_infer_result,
        )),
        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessAtomicFact(
            ExecWitnessAtomicFactStmtResult::Success(p),
        )) => Some((
            &p.ambient,
            &p.prop_argument_type_checks,
            SourceOwner::WitnessAtomic(p),
            &p.store_and_infer_result,
        )),
        _ => None,
    }
}

fn witness_ambient_len(
    ambient: &WitnessExistAmbientSuccess,
    arguments: &[VerifyFactResult],
) -> usize {
    arguments.len() + 1 + ambient.witness_obj_well_defined.len() + ambient.witness_type_checks.len()
}

fn obtain_parts(
    statement: &ExecStmtResult,
) -> Option<(Vec<&BoundName>, &StoreHaveObjAndInferResult)> {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromExistFact(
                ExecObtainObjFromExistFactStmtResult::Success(p),
            ),
        )) => Some((
            p.statement.equal_tos.iter().collect(),
            &p.store_and_infer_result,
        )),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                ExecObtainObjFromAtomicFactStmtResult::Success(p),
            ),
        )) => Some((
            p.statement.equal_tos.iter().collect(),
            &p.store_and_infer_result,
        )),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjByExistFacts(
                ExecHaveObjByExistFactsStmtResult::Success(p),
            ),
        )) => Some((
            p.statement
                .param_def
                .groups
                .iter()
                .flat_map(|g| g.params.iter())
                .collect(),
            &p.store_and_infer_result,
        )),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveByFnPreimage(
                crate::execute::ExecHaveByFnPreimageStmtResult::Success(p),
            ),
        )) => Some((
            p.statement.preimage_names.iter().collect(),
            &p.store_and_infer_result,
        )),
        _ => None,
    }
}

fn parameter_in_statement(
    statement: &ExecStmtResult,
    before: usize,
    id: IdentifierId,
) -> Option<(&BoundName, Option<&Obj>, &StoreFactAndInferResult)> {
    if let Some((groups, stores)) = context_parameter_parts(statement) {
        return parameter_from_groups(groups, &stores.store_and_infer_results, before, id);
    }
    let (names, stores) = obtain_parts(statement)?;
    let (index, name) = names.iter().enumerate().find(|(_, name)| name.id == id)?;
    if index >= before.saturating_sub(1) {
        return None;
    }
    let store = stores.store_and_infer_results.get(index)?;
    let carrier = match &store.store {
        StoreFactResult::AtomicFact(p) => match &p.fact {
            AtomicFact::InFact(f) => Some(&f.set),
            AtomicFact::IsSetFact(_) => None,
            _ => return None,
        },
        _ => return None,
    };
    Some((name, carrier, store.as_ref()))
}

fn stored_reference(
    store: &StoreFactAndInferResult,
    id: FactId,
    actual: &Fact,
) -> Result<Option<String>, LeanCompileError> {
    if store.primary_fact_id() == id {
        check_store_subject(&store.store, actual)?;
        return Ok(Some(format!("h_{}", id.value())));
    }
    Ok(infer_has_fact(store, id, actual)?.then(|| format!("h_{}", id.value())))
}

fn parameter_in_owner<'a>(
    position: &SourcePosition<'a>,
    id: IdentifierId,
) -> Option<(&'a BoundName, Option<&'a Obj>, &'a StoreFactAndInferResult)> {
    if let SourceOwner::Piecewise(p) = position.owner {
        return p.parameter(id, position.before);
    }
    if let SourceOwner::HaveEqualType(p) = position.owner {
        return parameter_from_groups(
            &p.statement.param_def.groups,
            &p.type_preflight.defined_params.store_and_infer_results,
            position.before,
            id,
        );
    }
    if let Some((steps, head)) = local_steps(position.owner) {
        for statement in steps
            .iter()
            .take(position.before.saturating_sub(head))
            .rev()
        {
            if let Some(parameter) = parameter_in_statement(statement, usize::MAX, id) {
                return Some(parameter);
            }
        }
    }
    if let Some((fact, introduced, _)) = witness_header(position.owner) {
        return parameter_from_groups(
            &fact.typed_parameters.groups,
            &introduced.defined_params.store_and_infer_results,
            position.before,
            id,
        );
    }
    match position.owner {
        SourceOwner::ExistWD(fact, p) => parameter_from_groups(
            &fact.typed_parameters.groups,
            &p.introduced_params.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::EnumerationAssignment(fact, p) => parameter_from_groups(
            &fact.typed_parameters.groups,
            &p.introduced_params.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::Induction(proof) if position.before > 0 => {
            induction_parameter(&proof.parameter, &proof.introduced_parameter, id)
        }
        SourceOwner::InductionCase(header, proof) => {
            let head = 1 + proof.assumptions.len();
            for statement in proof
                .proof_steps
                .iter()
                .take(position.before.saturating_sub(head))
                .rev()
            {
                if let Some(parameter) = parameter_in_statement(statement, usize::MAX, id) {
                    return Some(parameter);
                }
            }
            if position.before > 0 {
                induction_parameter(&header.parameter, &proof.introduced_parameter, id)
            } else {
                None
            }
        }
        SourceOwner::RecursiveFunction(proof) if position.before > 0 => {
            let mut index = 0;
            for group in &proof.statement.fn_set_clause.set_bound_parameters.groups {
                for parameter in &group.params {
                    if parameter.id == id {
                        return proof
                            .binder_introduction
                            .defined_params
                            .store_and_infer_results
                            .get(index)
                            .map(|store| {
                                (parameter, Some(group.param_type.as_ref()), store.as_ref())
                            });
                    }
                    index += 1;
                }
            }
            None
        }
        SourceOwner::Forall(p) => parameter_from_groups(
            &p.fact.typed_parameters.groups,
            &p.introduced_params.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::ForallIffWD(fact, p) => parameter_from_groups(
            &fact.forall_fact.typed_parameters.groups,
            &p.introduced_params.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::ForallWD(fact, p) => parameter_from_groups(
            &fact.typed_parameters.groups,
            &p.introduced_params.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::NotForallWD(fact, p) => parameter_from_groups(
            &fact.typed_parameters.groups,
            &p.introduced_params.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::KnownForall(p) => parameter_from_groups(
            &p.fact.typed_parameters.groups,
            &p.well_defined
                .introduced_params
                .defined_params
                .store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::Template(p) => parameter_from_groups(
            &p.statement.template_arg_def.groups,
            &p.introduced_params.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::StructHeader(p) => p
            .statement
            .param_def_with_dom
            .as_ref()
            .zip(p.introduced_params.as_ref())
            .and_then(|((params, _), introduced)| {
                parameter_from_groups(
                    &params.groups,
                    &introduced.defined_params.store_and_infer_results,
                    position.before,
                    id,
                )
            }),
        SourceOwner::StructFields(p) => p
            .statement
            .fields
            .iter()
            .zip(&p.field_scope.fields)
            .take(position.before)
            .find(|(field, _)| field.binding.id == id)
            .and_then(|(field, stage)| {
                stage
                    .defined
                    .store_and_infer_results
                    .first()
                    .map(|store| (&field.binding, Some(&field.field_type), store.as_ref()))
            }),
        SourceOwner::PropDefinition(p) => parameter_from_groups(
            &p.statement.typed_parameters.groups,
            &p.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::SetBuilder(set, proof)
            if position.before > 1 && set.param_binding.id == id =>
        {
            proof
                .defined_params
                .store_and_infer_results
                .first()
                .map(|store| {
                    (
                        &set.param_binding,
                        Some(set.param_set.as_ref()),
                        store.as_ref(),
                    )
                })
        }
        SourceOwner::WD(proof) | SourceOwner::WDLocals(proof, _) => {
            let (signature, carriers, parameters, _, _) = function_binder(proof)?;
            let before = position.before.saturating_sub(carriers.len());
            let mut index = 0;
            for group in &signature.set_bound_parameters.groups {
                for parameter in &group.params {
                    if index < before && parameter.id == id {
                        return parameters.store_and_infer_results.get(index).map(|store| {
                            (parameter, Some(group.param_type.as_ref()), store.as_ref())
                        });
                    }
                    index += 1;
                }
            }
            None
        }
        SourceOwner::Named(p) => {
            let (steps, head) = named_steps(p);
            for step in steps
                .iter()
                .take(position.before.saturating_sub(head))
                .rev()
            {
                if let Some(parameter) = parameter_in_statement(step, usize::MAX, id) {
                    return Some(parameter);
                }
            }
            match (&p.statement.fact, &p.body) {
                (Fact::ForallFact(fact), ExecDefThmBodyProof::Forall(body)) => {
                    parameter_from_groups(
                        &fact.typed_parameters.groups,
                        &body
                            .introduced_params
                            .defined_params
                            .store_and_infer_results,
                        position.before,
                        id,
                    )
                }
                _ => None,
            }
        }
        SourceOwner::Claim(p) => {
            let (steps, head) = claim_steps(p);
            for step in steps
                .iter()
                .take(position.before.saturating_sub(head))
                .rev()
            {
                if let Some(parameter) = parameter_in_statement(step, usize::MAX, id) {
                    return Some(parameter);
                }
            }
            match (&p.statement.fact, &p.body) {
                (Fact::ForallFact(fact), ExecClaimBodyProof::Forall(body)) => {
                    parameter_from_groups(
                        &fact.typed_parameters.groups,
                        &body
                            .introduced_params
                            .defined_params
                            .store_and_infer_results,
                        position.before,
                        id,
                    )
                }
                _ => None,
            }
        }
        SourceOwner::Statement(statement) => parameter_in_statement(statement, position.before, id),
        SourceOwner::Run(run) => run
            .statement_results
            .iter()
            .take(position.before)
            .rev()
            .find_map(|statement| parameter_in_statement(statement, usize::MAX, id)),
        _ => None,
    }
}

fn function_binder(
    proof: &ObjWellDefinedProof,
) -> Option<(
    &FnSet,
    &[Box<ObjWellDefinedProof>],
    &StoreHaveObjAndInferResult,
    &[AssumeDomFactResult],
    &crate::exec_env::ExecEnv,
)> {
    match proof {
        ObjWellDefinedProof::ByDef {
            obj: Obj::FunctionSpace(FunctionSpace::FnSet(signature)),
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnSet(
                    proof,
                )),
        } => Some((
            signature,
            &proof.param_type_well_defined,
            &proof.defined_params,
            &proof.assumed_dom_facts,
            &proof.local_env,
        )),
        ObjWellDefinedProof::ByDef {
            obj: Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)),
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(proof),
                ),
        } => Some((
            &function.body,
            &proof.param_type_well_defined,
            &proof.defined_params,
            &proof.assumed_dom_facts,
            &proof.local_env,
        )),
        _ => None,
    }
}

fn induction_parameter<'a>(
    parameter: &'a BoundName,
    introduced: &'a IntroduceTypedParametersResult,
    id: IdentifierId,
) -> Option<(&'a BoundName, Option<&'a Obj>, &'a StoreFactAndInferResult)> {
    if parameter.id != id {
        return None;
    }
    let ParamTypeWellDefinedProof::Obj(carrier) = introduced.param_type_well_defined.first()?
    else {
        return None;
    };
    if carrier.obj() != &Obj::StandardSet(StandardSet::Z) {
        return None;
    }
    introduced
        .defined_params
        .store_and_infer_results
        .first()
        .map(|store| (parameter, Some(carrier.obj()), store.as_ref()))
}

fn check_subject(expected: &Fact, actual: &Fact) -> Result<(), LeanCompileError> {
    if expected == actual {
        Ok(())
    } else {
        Err(LeanCompileError::new(
            "FactId/Producer",
            "The result producer differs from the exact cited source subject.",
        ))
    }
}

fn check_store_subject(store: &StoreFactResult, actual: &Fact) -> Result<(), LeanCompileError> {
    let expected = match store {
        StoreFactResult::AtomicFact(p) => Fact::AtomicFact(p.fact.clone()),
        StoreFactResult::ForallFact(p) => Fact::ForallFact(p.fact.clone()),
        StoreFactResult::ForallFactWithIff(p) => Fact::ForallFactWithIff(p.fact.clone()),
        StoreFactResult::AndFact(p) => Fact::AndFact(p.fact.clone()),
        StoreFactResult::ChainFact(p) => Fact::ChainFact(p.fact.clone()),
        StoreFactResult::OrFact(p) => Fact::OrFact(p.fact.clone()),
        StoreFactResult::ExistShapedFact(p) => crate::ast::fact::exist_shaped_fact_to_fact(&p.fact),
        StoreFactResult::NotForallFact(p) => Fact::NotForall(p.fact.clone()),
    };
    if store.primary_fact_id() != actual.fact_id() {
        return Err(LeanCompileError::new(
            "Store/Subject",
            "The producer store ID differs from its subject.",
        ));
    }
    check_subject(&expected, actual)
}

fn infer_has_fact(
    store: &StoreFactAndInferResult,
    id: FactId,
    actual: &Fact,
) -> Result<bool, LeanCompileError> {
    if stored_projection_has_fact(&store.store, id, actual)? {
        return Ok(true);
    }
    match &store.infer {
        Some(InferResult::AtomicFact(infer)) => atomic_infer_has_fact(infer, id, actual),
        Some(InferResult::AndFact(infer)) => {
            for component in &infer.components {
                if atomic_infer_has_fact(component, id, actual)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Some(InferResult::ChainFact(infer)) => {
            for edge in &infer.adjacent_infers {
                if edge.fact.fact_id() == id {
                    check_subject(&edge.fact, actual)?;
                    return Ok(true);
                }
                if atomic_infer_has_fact(&edge.infer, id, actual)? {
                    return Ok(true);
                }
            }
            for closure in &infer.transitive_closures {
                let derived = &closure.derived.store;
                if derived.primary_fact_id() == id {
                    check_store_subject(derived, actual)?;
                    return Ok(true);
                }
                if stored_projection_has_fact(derived, id, actual)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Some(InferResult::NotForall(infer)) => {
            let derived = &infer.derived_exist.store;
            if derived.primary_fact_id() != id {
                return Ok(false);
            }
            check_store_subject(derived, actual)?;
            Ok(true)
        }
        Some(InferResult::ExistUniqueFact(
            crate::store_fact_and_infer::InferExistUniqueFactResult::UniquenessForall(infer),
        )) => {
            if infer.derived.store.primary_fact_id() != id {
                return Ok(false);
            }
            check_store_subject(&infer.derived.store, actual)?;
            Ok(true)
        }
        Some(InferResult::NotExistFact(
            crate::store_fact_and_infer::InferNotExistFactResult::DemorganForall(infer),
        )) => {
            let derived = &infer.derived.store;
            if derived.primary_fact_id() != id {
                return Ok(false);
            }
            check_store_subject(derived, actual)?;
            Ok(true)
        }
        _ => Ok(false),
    }
}

fn atomic_infer_has_fact(
    infer: &InferAtomicFactResult,
    id: FactId,
    actual: &Fact,
) -> Result<bool, LeanCompileError> {
    for captured in atomic_inference_stages(infer) {
        let store = &captured.store;
        if store.primary_fact_id() == id {
            check_store_subject(store, actual)?;
            return Ok(true);
        }
        if stored_projection_has_fact(store, id, actual)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn prop_inference_stages(
    store: &StoreFactAndInferResult,
) -> Vec<&crate::store_fact_and_infer::StoreInferredFactResult> {
    match &store.infer {
        Some(InferResult::AtomicFact(infer)) => atomic_inference_stages(infer),
        _ => Vec::new(),
    }
}

fn atomic_inference_stages(infer: &InferAtomicFactResult) -> Vec<&StoreInferredFactResult> {
    match infer {
        InferAtomicFactResult::MultivariableAnalysisFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotMultivariableAnalysisFact(_) => Vec::new(),
        InferAtomicFactResult::RealSetBoundFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotRealSetBoundFact(_) => Vec::new(),
        InferAtomicFactResult::RealSetBoundedFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotRealSetBoundedFact(_) => Vec::new(),
        InferAtomicFactResult::SequenceAnalysisFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotSequenceAnalysisFact(_) => Vec::new(),
        InferAtomicFactResult::RealAccumulationFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotRealAccumulationFact(_) => Vec::new(),
        InferAtomicFactResult::HasRiemannIntegralFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotHasRiemannIntegralFact(_) => Vec::new(),
        InferAtomicFactResult::FunctionRiemannIntegrableFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotFunctionRiemannIntegrableFact(_) => Vec::new(),
        InferAtomicFactResult::HasDerivativeAtFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotHasDerivativeAtFact(_) => Vec::new(),
        InferAtomicFactResult::FunctionDifferentiableAtFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotFunctionDifferentiableAtFact(_) => Vec::new(),
        InferAtomicFactResult::FunctionContinuousAtFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotFunctionContinuousAtFact(_) => Vec::new(),
        InferAtomicFactResult::FunctionContinuousFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotFunctionContinuousFact(_) => Vec::new(),
        InferAtomicFactResult::FunctionLipschitzFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::NotFunctionLipschitzFact(_) => Vec::new(),
        InferAtomicFactResult::HasFunctionLimitFact(_)
        | InferAtomicFactResult::NotHasFunctionLimitFact(_)
        | InferAtomicFactResult::HasSequenceLimsupFact(_)
        | InferAtomicFactResult::HasSequenceLiminfFact(_)
        | InferAtomicFactResult::HasSequenceLimitFact(_)
        | InferAtomicFactResult::NotHasSequenceLimsupFact(_)
        | InferAtomicFactResult::NotHasSequenceLiminfFact(_)
        | InferAtomicFactResult::NotHasSequenceLimitFact(_) => Vec::new(),
        InferAtomicFactResult::EqualFact(rules) => rules
            .iter()
            .flat_map(|rule| rule.stored_conclusions())
            .collect(),
        InferAtomicFactResult::NormalAtomicFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::InFact(rules) => rules
            .iter()
            .flat_map(|r| match r {
                InferInFactResult::SetBuilder(p) => p
                    .steps
                    .iter()
                    .flat_map(|s| s.stored_conclusions())
                    .collect::<Vec<_>>(),
                InferInFactResult::SignedStandardSetSign(p) => p.derived.iter().collect(),
                InferInFactResult::CartCoordinates(_)
                | InferInFactResult::Range(_)
                | InferInFactResult::ClosedRange(_)
                | InferInFactResult::UnionOr(_)
                | InferInFactResult::IntersectBoth(_)
                | InferInFactResult::SetMinusSplit(_)
                | InferInFactResult::Preimage(_)
                | InferInFactResult::PreimageSet(_)
                | InferInFactResult::SeqExpand(_)
                | InferInFactResult::RealInterval(_)
                | InferInFactResult::OneSideRealInterval(_)
                | InferInFactResult::FiniteSeqExpand(_)
                | InferInFactResult::FnRange(_)
                | InferInFactResult::ListSetSingletonEqual(_) => r.stored_conclusions(),
                _ => Vec::new(),
            })
            .collect(),
        InferAtomicFactResult::LessFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::GreaterFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::LessEqualFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::GreaterEqualFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::InjectiveFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::SurjectiveFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::BijectiveFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::ProperSubsetFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::ProperSupersetFact(rules) => {
            rules.iter().flat_map(|r| r.stored_conclusions()).collect()
        }
        InferAtomicFactResult::IsSetFact(_)
        | InferAtomicFactResult::IsNonemptySetFact(_)
        | InferAtomicFactResult::IsFiniteSetFact(_)
        | InferAtomicFactResult::SubsetFact(_)
        | InferAtomicFactResult::SupersetFact(_)
        | InferAtomicFactResult::PrimeFact(_)
        | InferAtomicFactResult::CoprimeFact(_)
        | InferAtomicFactResult::DvdFact(_)
        | InferAtomicFactResult::IsChoiceFunctionForFact(_)
        | InferAtomicFactResult::NotNormalAtomicFact(_)
        | InferAtomicFactResult::NotEqualFact(_)
        | InferAtomicFactResult::NotLessFact(_)
        | InferAtomicFactResult::NotGreaterFact(_)
        | InferAtomicFactResult::NotLessEqualFact(_)
        | InferAtomicFactResult::NotGreaterEqualFact(_)
        | InferAtomicFactResult::NotIsSetFact(_)
        | InferAtomicFactResult::NotIsNonemptySetFact(_)
        | InferAtomicFactResult::NotIsFiniteSetFact(_)
        | InferAtomicFactResult::NotInFact(_)
        | InferAtomicFactResult::NotSubsetFact(_)
        | InferAtomicFactResult::NotSupersetFact(_)
        | InferAtomicFactResult::NotProperSubsetFact(_)
        | InferAtomicFactResult::NotProperSupersetFact(_)
        | InferAtomicFactResult::NotPrimeFact(_)
        | InferAtomicFactResult::NotCoprimeFact(_)
        | InferAtomicFactResult::NotDvdFact(_)
        | InferAtomicFactResult::NotInjectiveFact(_)
        | InferAtomicFactResult::NotSurjectiveFact(_)
        | InferAtomicFactResult::NotBijectiveFact(_)
        | InferAtomicFactResult::NotIsChoiceFunctionForFact(_) => Vec::new(),
    }
}

fn atomic_inference_stages_before(
    infer: &InferAtomicFactResult,
    before: usize,
) -> Vec<&StoreInferredFactResult> {
    match infer {
        InferAtomicFactResult::EqualFact(rules) => rules
            .iter()
            .take(before)
            .flat_map(|rule| rule.stored_conclusions())
            .collect(),
        _ => atomic_inference_stages(infer)
            .into_iter()
            .take(before)
            .collect(),
    }
}

fn have_reference(
    proof: &ExecHaveObjInNonemptySetStmtSuccessResult,
    before: usize,
    id: FactId,
    actual: &Fact,
) -> Result<Option<String>, LeanCompileError> {
    let mut index = 0;
    for group in &proof.statement.param_def.groups {
        for _parameter in &group.params {
            if index >= before {
                return Ok(None);
            }
            let Some(store) = proof
                .store_and_infer_result
                .store_and_infer_results
                .get(index)
            else {
                return Ok(None);
            };
            if store.primary_fact_id() == id {
                check_store_subject(&store.store, actual)?;
                return Ok(Some(format!("h_{}", id.value())));
            }
            if infer_has_fact(store, id, actual)? {
                return Ok(Some(format!("h_{}", id.value())));
            }
            index += 1;
        }
    }
    Ok(None)
}

fn header_reference(
    groups: &[TypedParameterGroup],
    introduced: &IntroduceTypedParametersResult,
    doms: &[AssumeDomFactResult],
    before: usize,
    id: FactId,
    actual: &Fact,
) -> Result<Option<String>, LeanCompileError> {
    let mut index = 0;
    for group in groups {
        for _parameter in &group.params {
            if index >= before {
                return Ok(None);
            }
            let Some(store) = introduced.defined_params.store_and_infer_results.get(index) else {
                return Ok(None);
            };
            if store.primary_fact_id() == id {
                check_store_subject(&store.store, actual)?;
                return Ok(Some(format!("h_{}", id.value())));
            }
            if infer_has_fact(store, id, actual)? {
                return Ok(Some(format!("h_{}", id.value())));
            }
            index += 1;
        }
    }
    if before >= index {
        for layer in introduced.auto_opened_struct_layers.iter().flatten() {
            for store in &layer.store_and_infer {
                if let Some(reference) = stored_reference(store, id, actual)? {
                    return Ok(Some(reference));
                }
            }
        }
    }
    for dom in doms.iter().take(before.saturating_sub(index)) {
        if dom.store_and_infer.primary_fact_id() == id {
            check_store_subject(&dom.store_and_infer.store, actual)?;
            return Ok(Some(format!("h_{}", id.value())));
        }
        if infer_has_fact(&dom.store_and_infer, id, actual)? {
            return Ok(Some(format!("h_{}", id.value())));
        }
    }
    Ok(None)
}

fn parameter_count(groups: &[TypedParameterGroup]) -> usize {
    groups.iter().map(|group| group.params.len()).sum()
}

fn statement_reference(
    statement: &ExecStmtResult,
    id: FactId,
    actual: &Fact,
    top: Option<(&RunLitexCodeResult, usize)>,
    before: usize,
) -> Result<Option<String>, LeanCompileError> {
    let internal = || format!("h_{}", id.value());
    let global_reference = |name: String| match top {
        Some((run, index)) => application(
            &name,
            &context_arguments_before(run, index),
            &abstract_arguments_before(run, index),
            &hypotheses_before(run, index)
                .into_iter()
                .chain(super::compile_local_assumptions::local_assumption_ids(
                    statement,
                ))
                .collect::<Vec<_>>(),
        ),
        None => name,
    };
    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        crate::execute::ExecDefTemplateStmtResult::Success(p),
    )) = statement
    {
        for published in p.definition_facts.iter().take(before) {
            if let Some(reference) = stored_reference(&published.store_and_infer, id, actual)? {
                return Ok(Some(global_reference(reference)));
            }
        }
        return Ok(None);
    }
    if let Some(p) = super::compile_release_choice_result::choice_statement(statement) {
        return if before > 3 {
            Ok(stored_reference(&p.stored, id, actual)?.map(global_reference))
        } else {
            Ok(None)
        };
    }
    if let Some(p) = super::compile_release_zorn_result::zorn_statement(statement) {
        return if before > 3 {
            Ok(stored_reference(&p.stored, id, actual)?.map(global_reference))
        } else {
            Ok(None)
        };
    }
    if let Some(p) = super::compile_release_regularity_result::regularity_statement(statement) {
        return if before > 3 {
            Ok(stored_reference(&p.stored, id, actual)?.map(global_reference))
        } else {
            Ok(None)
        };
    }
    if let Some(p) = super::compile_replacement_result::replacement_statement(statement) {
        for (stage, store) in p
            .defined_params
            .store_and_infer_results
            .iter()
            .map(|s| s.as_ref())
            .chain([&p.introduction, &p.elimination])
            .enumerate()
        {
            if before > 1 + stage {
                if let Some(reference) = stored_reference(store, id, actual)? {
                    return Ok(Some(global_reference(reference)));
                }
            }
        }
        return Ok(None);
    }
    if let Some(p) = trust_have(statement) {
        for (i, store) in p
            .defined_param_store_and_infer
            .store_and_infer_results
            .iter()
            .take(before)
            .enumerate()
        {
            if let Some(reference) = stored_reference(store, id, actual)? {
                if store.primary_fact_id() == id {
                    return Ok(Some(reference));
                }
                return Ok(Some(match top {
                    Some((run, index)) => {
                        let mut arguments = context_arguments_before(run, index);
                        let mut parameters = Vec::new();
                        append_have_parameters(statement, i + 1, &mut parameters);
                        for (p, _, fact_id) in parameters {
                            let n = p.id.value();
                            arguments.extend([
                                format!("_Host_i{n}"),
                                format!("_rep_i{n}"),
                                format!("_value_i{n}"),
                                format!("h_{}", fact_id.value()),
                            ]);
                        }
                        application(
                            &reference,
                            &arguments,
                            &abstract_arguments_before(run, index),
                            &hypotheses_before(run, index),
                        )
                    }
                    None => reference,
                }));
            }
        }
        if before >= assumption_start(statement) {
            for layer in p.auto_opened_struct_layers.iter().flatten() {
                for store in &layer.store_and_infer {
                    if let Some(reference) = stored_reference(store, id, actual)? {
                        return Ok(Some(match top {
                            Some((run, index)) => application(
                                &reference,
                                &context_arguments_before(run, index + 1),
                                &abstract_arguments_before(run, index),
                                &hypotheses_before(run, index),
                            ),
                            None => reference,
                        }));
                    }
                }
            }
        }
    }
    let assumptions = super::compile_assumption_stmt_result::assumption_stages(statement);
    for (j, (_, _, store)) in assumptions
        .iter()
        .take(before.saturating_sub(assumption_start(statement) + assumptions.len()))
        .enumerate()
    {
        if let Some(reference) = stored_reference(store, id, actual)? {
            if store.primary_fact_id() == id {
                return Ok(Some(reference));
            }
            let reference = match top {
                Some((run, index)) => {
                    let mut hypotheses = hypotheses_before(run, index);
                    hypotheses.extend(
                        assumptions
                            .iter()
                            .take(j + 1)
                            .map(|(fact, _, _)| fact.fact_id()),
                    );
                    application(
                        &reference,
                        &context_arguments_before(
                            run,
                            index + usize::from(trust_have(statement).is_some()),
                        ),
                        &abstract_arguments_before(run, index),
                        &hypotheses,
                    )
                }
                None => reference,
            };
            return Ok(Some(reference));
        }
    }
    if let Some(proof) = nonempty_witness_statement(statement) {
        return if before > 2 {
            Ok(stored_reference(&proof.store_and_infer_result, id, actual)?.map(global_reference))
        } else {
            Ok(None)
        };
    }
    if let Some((ambient, arguments, _, store)) = witness_statement(statement) {
        return if before > witness_ambient_len(ambient, arguments) {
            Ok(stored_reference(store, id, actual)?.map(global_reference))
        } else {
            Ok(None)
        };
    }
    if let Some((_, stores)) = obtain_parts(statement) {
        for store in stores
            .store_and_infer_results
            .iter()
            .take(before.saturating_sub(1))
        {
            if let Some(reference) = stored_reference(store, id, actual)? {
                return Ok(Some(global_reference(reference)));
            }
        }
        return Ok(None);
    }
    if let Some((formation, _, store)) = enumeration_statement(statement) {
        if before <= 1 {
            return Ok(None);
        }
        if store.primary_fact_id() == id {
            check_store_subject(&store.store, actual)?;
            if top.is_none() {
                let Fact::ForallFact(fact) = actual else {
                    return Err(LeanCompileError::unsupported("Enumeration/CitationGoal"));
                };
                let count = parameter_count(&fact.typed_parameters.groups);
                if count > 1 {
                    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(wd)) =
                        formation
                    else {
                        return Err(LeanCompileError::unsupported("Enumeration/CitationWD"));
                    };
                    let stores = &wd.introduced_params.defined_params.store_and_infer_results;
                    if stores.len() != count {
                        return Err(LeanCompileError::unsupported("Enumeration/ParameterStore"));
                    }
                    // Local enumeration quantifies over semantic values. Adapt
                    // every original argument and membership, leaving the
                    // source guards as the resulting function's next inputs.
                    let mut binders = Vec::new();
                    let mut arguments = Vec::new();
                    for (parameter, store) in fact
                        .typed_parameters
                        .groups
                        .iter()
                        .flat_map(|g| &g.params)
                        .zip(stores)
                    {
                        let n = parameter.id.value();
                        let h = format!("h_{}", store.primary_fact_id().value());
                        binders.push(format!("{{_Host_i{n} : Type _}} [_rep_i{n} : Litex.Representation M _Host_i{n}] (_value_i{n} : Litex.Obj (M := M) _Host_i{n}) {h}"));
                        arguments.extend([format!("(Litex.denote _value_i{n})"), h]);
                    }
                    return Ok(Some(format!(
                        "(fun {} => {} {})",
                        binders.join(" "),
                        internal(),
                        arguments.join(" ")
                    )));
                }
                return Ok(Some(format!("(fun {{_Host : Type _}} [_rep : Litex.Representation M _Host] (_value : Litex.Obj (M := M) _Host) => {} (Litex.denote _value))", internal())));
            }
            return Ok(Some(global_reference(internal())));
        }
        return Ok(stored_reference(store, id, actual)?.map(global_reference));
    }
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
            crate::execute::ExecDefStructStmtResult::Success(p),
        )) => {
            for law in p.definition_facts.iter().take(before.saturating_sub(1)) {
                if let Some(reference) = stored_reference(&law.store_and_infer, id, actual)? {
                    return Ok(Some(global_reference(reference)));
                }
            }
            Ok(None)
        }
        ExecStmtResult::By(ExecByStmtResult::Extension(
            crate::execute::execute_by_stmt::ExecByExtensionStmtResult::Success(p),
        )) => {
            if before > 2 {
                Ok(stored_reference(&p.stored, id, actual)?.map(global_reference))
            } else {
                Ok(None)
            }
        }
        ExecStmtResult::By(ExecByStmtResult::FnExtension(
            crate::execute::execute_by_stmt::ExecByFnExtensionStmtResult::Success(p),
        )) => {
            if before > 3 {
                Ok(stored_reference(&p.stored, id, actual)?.map(global_reference))
            } else {
                Ok(None)
            }
        }
        ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) => {
            if before > 3 {
                Ok(stored_reference(&p.stored, id, actual)?.map(global_reference))
            } else {
                Ok(None)
            }
        }
        ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(p))) => {
            let head = p.then_facts_wd.len() + 2;
            for store in p.stored.iter().take(before.saturating_sub(head) / 2) {
                if let Some(reference) = stored_reference(store, id, actual)? {
                    return Ok(Some(global_reference(reference)));
                }
            }
            Ok(None)
        }
        ExecStmtResult::By(ExecByStmtResult::Induc(ExecByInducStmtResult::Success(proof)))
            if before > 0 =>
        {
            if proof.stored.primary_fact_id() == id {
                check_store_subject(&proof.stored.store, actual)?;
                if top.is_none() {
                    // A local have cannot quantify over a fresh declaration
                    // universe. Its raw semantic induction proof is observed
                    // through this original caller's inferred representation.
                    return Ok(Some(format!("(fun {{_Host : Type _}} [_rep : Litex.Representation M _Host] (_value : Litex.Obj (M := M) _Host) => {} (Litex.denote _value))", internal())));
                }
                return Ok(Some(global_reference(internal())));
            }
            if infer_has_fact(&proof.stored, id, actual)? {
                return Ok(Some(global_reference(internal())));
            }
            Ok(None)
        }
        ExecStmtResult::By(ExecByStmtResult::StrongInduc(
            crate::execute::execute_by_stmt::ExecByStrongInducStmtResult::Success(proof),
        )) if before > 0 => {
            if proof.stored.primary_fact_id() == id {
                check_store_subject(&proof.stored.store, actual)?;
                if top.is_none() {
                    // A local have cannot quantify over a fresh declaration
                    // universe. Its raw semantic induction proof is observed
                    // through this original caller's inferred representation.
                    return Ok(Some(format!("(fun {{_Host : Type _}} [_rep : Litex.Representation M _Host] (_value : Litex.Obj (M := M) _Host) => {} (Litex.denote _value))", internal())));
                }
                return Ok(Some(global_reference(internal())));
            }
            if infer_has_fact(&proof.stored, id, actual)? {
                return Ok(Some(global_reference(internal())));
            }
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
            ExecHaveFnByInducStmtResult::Success(proof),
        )) if before >= 8 => {
            for store in std::iter::once(&proof.store_and_infer_result.membership)
                .chain(&proof.store_and_infer_result.case_defining)
            {
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(global_reference(internal())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(global_reference(internal())));
                }
            }
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
            crate::execute::ExecHaveFnByForallExistUniqueStmtResult::Success(p),
        )) => {
            for (stage, store) in [(3, &p.membership), (5, &p.property), (6, &p.uniqueness)] {
                if before < stage {
                    continue;
                }
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(global_reference(internal())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(global_reference(internal())));
                }
            }
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
            ExecHaveFnEqualCaseByCaseStmtResult::Success(p),
        )) => {
            for (index, store) in std::iter::once(&p.store_and_infer_result.membership)
                .chain(&p.store_and_infer_result.case_defining)
                .enumerate()
            {
                if before >= 6 + index {
                    if let Some(reference) = stored_reference(store, id, actual)? {
                        return Ok(Some(global_reference(reference)));
                    }
                }
            }
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(p),
        )) => {
            let stores = &p.store_and_infer_result;
            for (stage, store) in [(3, &stores.membership), (4, &stores.defining_equal)] {
                if before < stage {
                    continue;
                }
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(global_reference(internal())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(global_reference(internal())));
                }
            }
            Ok(None)
        }
        ExecStmtResult::Fact(ExecFactStmtResult::Success(p))
            if before > 0 && p.store_and_infer_result.primary_fact_id() == id =>
        {
            check_store_subject(&p.store_and_infer_result.store, actual)?;
            check_subject(
                &verified_subject(&p.verify_result)
                    .ok_or_else(|| LeanCompileError::unsupported("Fact/Subject"))?,
                actual,
            )?;
            Ok(Some(global_reference(internal())))
        }
        ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p)))
            if before > 0 =>
        {
            if p.stored.primary_fact_id() == id {
                check_store_subject(&p.stored.store, actual)?;
                check_subject(
                    &verified_subject(&p.proof)
                        .ok_or_else(|| LeanCompileError::unsupported("ByDef/Subject"))?,
                    actual,
                )?;
                return Ok(Some(global_reference(internal())));
            }
            if infer_has_fact(&p.stored, id, actual)? {
                return Ok(Some(global_reference(internal())));
            }
            Ok(None)
        }
        ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) if before > 0 => {
            if infer_has_fact(&p.store_and_infer_result, id, actual)? {
                Ok(Some(global_reference(internal())))
            } else {
                Ok(None)
            }
        }
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p)))
            if before > 0 =>
        {
            if p.stored.primary_fact_id() == id {
                check_store_subject(&p.stored.store, actual)?;
                check_subject(
                    &verified_subject(&p.selected_proof)
                        .ok_or_else(|| LeanCompileError::unsupported("ByThm/Subject"))?,
                    actual,
                )?;
                return Ok(Some(global_reference(internal())));
            }
            if infer_has_fact(&p.stored, id, actual)? {
                return Ok(Some(global_reference(internal())));
            }
            Ok(None)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ExpandRange(
            crate::execute::execute_by_stmt::ExecExpandRangeStmtResult::Success(p),
        )) => {
            if before > 1 {
                return Ok(stored_reference(&p.stored, id, actual)?.map(global_reference));
            }
            Ok(None)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::StructDef(
            crate::execute::ExecReleaseStructDefStmtResult::Success(p),
        )) => {
            for store in p
                .release
                .store_and_infer
                .iter()
                .take(before.saturating_sub(1))
            {
                if let Some(reference) = stored_reference(store, id, actual)? {
                    return Ok(Some(global_reference(reference)));
                }
            }
            Ok(None)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::CartDef(
            crate::execute::execute_release_cart_def_stmt::ExecReleaseCartDefStmtResult::Success(
                proof,
            ),
        )) => {
            if before > 3 {
                return Ok(
                    stored_reference(&proof.store_and_infer, id, actual)?.map(global_reference)
                );
            }
            Ok(None)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::TupleDef(
            crate::execute::execute_release_tuple_def_stmt::ExecReleaseTupleDefStmtResult::Success(
                proof,
            ),
        )) => {
            let head =
                super::compile_release_tuple_def_result::tuple_release_publication_start(proof);
            for store in proof.stored.iter().take(before.saturating_sub(head)) {
                if let Some(reference) = stored_reference(store, id, actual)? {
                    return Ok(Some(global_reference(reference)));
                }
            }
            Ok(None)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ObjDef(
            crate::execute::execute_release_obj_def_stmt::ExecReleaseObjDefStmtResult::Success(
                proof,
            ),
        )) => {
            for store in proof.store_and_infer.iter().take(before) {
                if let Some(reference) = stored_reference(store, id, actual)? {
                    return Ok(Some(global_reference(reference)));
                }
            }
            Ok(None)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(proof),
        )) => {
            for store in proof.stored.iter().take(before / 2) {
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    if matches!(&proof.callee, ResolvedTheoremCallee::UserTheorem(declaration) if declaration.fact.fact_id() == id)
                        && matches!(proof.call.arguments, TheoremCallArguments::Bare)
                    {
                        continue;
                    }
                    return Ok(Some(global_reference(internal())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(global_reference(internal())));
                }
            }
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) if before > 0 => {
            if p.stored.primary_fact_id() == id {
                check_store_subject(&p.stored.store, actual)?;
                check_subject(&p.statement.fact, actual)?;
                return Ok(Some(global_reference(internal())));
            }
            // These named goals emit their retained logical inference stores
            // alongside the primary theorem. Other theorem families do not.
            if matches!(
                p.statement.fact,
                Fact::NotForall(_) | Fact::NotExistFact(_) | Fact::ExistUniqueFact(_)
            ) && infer_has_fact(&p.stored, id, actual)?
            {
                return Ok(Some(global_reference(internal())));
            }
            Ok(None)
        }
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Success(p),
        )) if before > 0 => {
            if p.stored.primary_fact_id() == id {
                check_store_subject(&p.stored.store, actual)?;
                check_subject(&p.statement.fact, actual)?;
                return Ok(Some(global_reference(internal())));
            }
            if infer_has_fact(&p.stored, id, actual)? {
                return Ok(Some(global_reference(internal())));
            }
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
        )) if before > 0 && p.stored_fact_ids.contains(&id) => {
            Ok(Some(global_reference(internal())))
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
        )) => {
            let count = p.statement.objs_equal_to.len();
            if before > 3 * count {
                for layer in p.auto_opened_struct_layers.iter().flatten() {
                    for store in &layer.store_and_infer {
                        if let Some(reference) = stored_reference(store, id, actual)? {
                            return Ok(Some(global_reference(reference)));
                        }
                    }
                }
            }
            for (index, store) in p
                .store_and_infer_result
                .store_and_infer_results
                .iter()
                .enumerate()
            {
                let alias = if index < count { index } else { index - count };
                if before <= 2 * count + alias {
                    continue;
                }
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(global_reference(internal())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(global_reference(internal())));
                }
            }
            Ok(None)
        }
        _ => {
            if let Some(p) = ordinary_have(statement) {
                let count = parameter_count(&p.statement.param_def.groups);
                if before > count {
                    for layer in p.auto_opened_struct_layers.iter().flatten() {
                        for store in &layer.store_and_infer {
                            if let Some(reference) = stored_reference(store, id, actual)? {
                                return Ok(Some(match top {
                                    Some((run, index)) => application(
                                        &reference,
                                        &context_arguments_before(run, index + 1),
                                        &abstract_arguments_before(run, index),
                                        &hypotheses_before(run, index),
                                    ),
                                    None => reference,
                                }));
                            }
                        }
                    }
                }
                let reference = have_reference(p, before, id, actual)?;
                if let Some(reference) = reference {
                    if p.store_and_infer_result
                        .store_and_infer_results
                        .iter()
                        .take(before)
                        .any(|store| store.primary_fact_id() == id)
                    {
                        return Ok(Some(reference));
                    }
                    if let Some((run, statement_index)) = top {
                        let mut arguments = context_arguments_before(run, statement_index);
                        let mut prefix = 0;
                        for (index, store) in p
                            .store_and_infer_result
                            .store_and_infer_results
                            .iter()
                            .enumerate()
                        {
                            if infer_has_fact(store, id, actual)? {
                                prefix = index + 1;
                                break;
                            }
                        }
                        let mut parameters = Vec::new();
                        append_have_parameters(statement, prefix, &mut parameters);
                        for (parameter, _, fact_id) in parameters {
                            let number = parameter.id.value();
                            arguments.extend([
                                format!("_Host_i{number}"),
                                format!("_rep_i{number}"),
                                format!("_value_i{number}"),
                                format!("h_{}", fact_id.value()),
                            ]);
                        }
                        return Ok(Some(application(
                            &reference,
                            &arguments,
                            &abstract_arguments_before(run, statement_index),
                            &hypotheses_before(run, statement_index),
                        )));
                    }
                    return Ok(Some(reference));
                }
            }
            Ok(None)
        }
    }
}

fn fact_reference_in_owner(
    position: &SourcePosition<'_>,
    id: FactId,
    actual: &Fact,
) -> Result<Option<String>, LeanCompileError> {
    if let SourceOwner::Choice(p) = position.owner {
        for (i, o) in p.obligations.iter().enumerate() {
            if position.before > p.proof_steps.len() + 3 * i + 2 {
                if let Ok((_, store)) = &o.stored {
                    if let Some(reference) = stored_reference(store, id, actual)? {
                        return Ok(Some(reference));
                    }
                }
            }
        }
    }
    if let SourceOwner::Zorn(p) = position.owner {
        for (i, o) in p.obligations.iter().enumerate() {
            if position.before > p.proof_steps.len() + 3 * i + 2 {
                if let Ok((_, store)) = &o.stored {
                    if let Some(reference) = stored_reference(store, id, actual)? {
                        return Ok(Some(reference));
                    }
                }
            }
        }
    }
    if let SourceOwner::Piecewise(p) = position.owner {
        for store in p.stores().take(position.before) {
            if let Some(reference) = stored_reference(store, id, actual)? {
                return Ok(Some(reference));
            }
        }
        return Ok(None);
    }
    if let Some((steps, head)) = local_steps(position.owner) {
        for statement in steps
            .iter()
            .take(position.before.saturating_sub(head))
            .rev()
        {
            if let Some(reference) = statement_reference(statement, id, actual, None, usize::MAX)? {
                return Ok(Some(reference));
            }
        }
    }
    if let Some((fact, introduced, equalities)) = witness_header(position.owner) {
        let count = parameter_count(&fact.typed_parameters.groups);
        for store in equalities
            .iter()
            .take(position.before.saturating_sub(count))
            .rev()
        {
            if let Some(reference) = stored_reference(store, id, actual)? {
                return Ok(Some(reference));
            }
        }
        return header_reference(
            &fact.typed_parameters.groups,
            introduced,
            &[],
            position.before,
            id,
            actual,
        );
    }
    match position.owner {
        SourceOwner::OrSelected(p) => {
            for assumed in p.assumed_negated_branches.iter().take(position.before / 2) {
                if let Some(value) = stored_reference(&assumed.store_and_infer, id, actual)? {
                    return Ok(Some(value));
                }
            }
            Ok(None)
        }

        SourceOwner::EnumerationAssignment(_, p) => {
            let (premises, steps, goals) = enumeration_outcome(p);
            let count = p
                .introduced_params
                .defined_params
                .store_and_infer_results
                .len();
            let head = count + p.binding_assumptions.len() + premises.len() + steps.len();
            for proved in goals.iter().take(position.before.saturating_sub(head)) {
                if let Some(value) = stored_reference(&proved.store_and_infer, id, actual)? {
                    return Ok(Some(value));
                }
            }
            for assumed in p
                .binding_assumptions
                .iter()
                .chain(premises)
                .take(position.before.saturating_sub(count))
            {
                if let Some(value) = stored_reference(&assumed.store_and_infer, id, actual)? {
                    return Ok(Some(value));
                }
            }
            for store in p
                .introduced_params
                .defined_params
                .store_and_infer_results
                .iter()
                .take(position.before)
            {
                if let Some(value) = stored_reference(store, id, actual)? {
                    return Ok(Some(value));
                }
            }
            Ok(None)
        }

        SourceOwner::ExistWD(fact, p) => header_reference(
            &fact.typed_parameters.groups,
            &p.introduced_params,
            &p.assumed_body_facts,
            position.before,
            id,
            actual,
        ),
        SourceOwner::FnExtension(p) => {
            if let crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof::MutualInclusion { forward, reverse, .. } = &p.domain_match.comparison {
                for fact in [forward, reverse] {
                    if fact.fact_id() == id {
                        if fact != actual {
                            return Err(LeanCompileError::unsupported("FunctionDomain/CitationSubject"));
                        }
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                }
            }
            Ok(None)
        }
        SourceOwner::Sketch(_) | SourceOwner::WitnessNonempty(_) | SourceOwner::Extension(_) => {
            Ok(None)
        }
        SourceOwner::WitnessExist(_) | SourceOwner::WitnessAtomic(_) => {
            unreachable!("witness header handled above")
        }
        SourceOwner::Contra(p) => {
            if position.before > 1 {
                stored_reference(&p.negation_assumed, id, actual)
            } else {
                Ok(None)
            }
        }
        SourceOwner::CasesBranch(p) => {
            let head = 2 + p.proof_steps.len();
            if let ByCasesBranchClosingSuccess::ThenFacts { proved_then_facts } = &p.closing {
                for proved in proved_then_facts
                    .iter()
                    .take(position.before.saturating_sub(head) / 2)
                {
                    if let Some(reference) = stored_reference(&proved.store_and_infer, id, actual)?
                    {
                        return Ok(Some(reference));
                    }
                }
            }
            if position.before > 1 {
                stored_reference(&p.assumptions_stored, id, actual)
            } else {
                Ok(None)
            }
        }
        SourceOwner::Induction(proof) => {
            let mut stores = Vec::new();
            if position.before > 0 {
                stores.extend(
                    proof
                        .introduced_parameter
                        .defined_params
                        .store_and_infer_results
                        .iter()
                        .map(|s| s.as_ref()),
                );
            }
            if position.before > 1 {
                stores.push(&proof.goal_domain.store_and_infer);
            }
            for store in stores {
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::InductionCase(_, proof) => {
            let mut stores = Vec::new();
            if position.before > 0 {
                stores.extend(
                    proof
                        .introduced_parameter
                        .defined_params
                        .store_and_infer_results
                        .iter()
                        .map(|s| s.as_ref()),
                );
            }
            stores.extend(
                proof
                    .assumptions
                    .iter()
                    .take(position.before.saturating_sub(1))
                    .map(|s| &s.store_and_infer),
            );
            for store in stores {
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            let head = 1 + proof.assumptions.len();
            for statement in proof
                .proof_steps
                .iter()
                .take(position.before.saturating_sub(head))
                .rev()
            {
                if let Some(reference) =
                    statement_reference(statement, id, actual, None, usize::MAX)?
                {
                    return Ok(Some(reference));
                }
            }
            Ok(None)
        }
        SourceOwner::RecursiveFunction(proof) => {
            let introduction = &proof.binder_introduction;
            let mut stores = Vec::new();
            if position.before > 0 {
                stores.extend(
                    introduction
                        .defined_params
                        .store_and_infer_results
                        .iter()
                        .map(|store| store.as_ref()),
                );
                stores.extend(introduction.assumed_dom_facts.iter());
            }
            if position.before > 6 {
                stores.push(&proof.restricted_self_membership);
            }
            for store in stores {
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::RecursiveCase(proof) if position.before > 0 => {
            let store = &proof.assumption_stored;
            if store.primary_fact_id() == id {
                check_store_subject(&store.store, actual)?;
                return Ok(Some(format!("h_{}", id.value())));
            }
            if infer_has_fact(store, id, actual)? {
                return Ok(Some(format!("h_{}", id.value())));
            }
            Ok(None)
        }
        SourceOwner::RecursiveDisjoint(proof) if position.before > 0 => {
            let store = &proof.assumption_stored;
            if store.primary_fact_id() == id {
                check_store_subject(&store.store, actual)?;
                return Ok(Some(format!("h_{}", id.value())));
            }
            if infer_has_fact(store, id, actual)? {
                return Ok(Some(format!("h_{}", id.value())));
            }
            Ok(None)
        }
        SourceOwner::RecursiveCase(_)
        | SourceOwner::RecursiveDisjoint(_)
        | SourceOwner::RecursiveUnfold(_)
        | SourceOwner::PiecewiseUnfold(_)
        | SourceOwner::Piecewise(_) => Ok(None),
        SourceOwner::InferredStore(_) => Ok(None),
        SourceOwner::Run(run) => {
            for (index, statement) in run
                .statement_results
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                if let Some(reference) =
                    statement_reference(statement, id, actual, Some((run, index)), usize::MAX)?
                {
                    return Ok(Some(reference));
                }
            }
            Ok(None)
        }
        SourceOwner::Statement(statement) => {
            let top = position.parent.and_then(|parent| match parent.owner {
                SourceOwner::Run(run) => Some((run, parent.before)),
                _ => None,
            });
            statement_reference(statement, id, actual, top, position.before)
        }
        SourceOwner::EmptyForall(p) => {
            if position.before > 0 && p.empty_carrier_store.primary_fact_id() == id {
                check_store_subject(&p.empty_carrier_store.store, actual)?;
                Ok(Some(format!("h_{}", id.value())))
            } else {
                Ok(None)
            }
        }
        SourceOwner::Forall(p) => {
            if let Some(reference) = header_reference(
                &p.fact.typed_parameters.groups,
                &p.introduced_params,
                &p.assumed_dom_facts,
                position.before,
                id,
                actual,
            )? {
                return Ok(Some(reference));
            }
            let head = parameter_count(&p.fact.typed_parameters.groups) + p.assumed_dom_facts.len();
            for then in p
                .proved_then_facts
                .iter()
                .take(position.before.saturating_sub(head))
            {
                if then.store_and_infer.primary_fact_id() == id {
                    check_store_subject(&then.store_and_infer.store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(&then.store_and_infer, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::ForallIffWD(fact, p) => header_reference(
            &fact.forall_fact.typed_parameters.groups,
            &p.introduced_params,
            &p.assumed_dom_facts,
            position.before,
            id,
            actual,
        ),
        SourceOwner::ForallWD(fact, p) => header_reference(
            &fact.typed_parameters.groups,
            &p.introduced_params,
            &p.assumed_dom_facts,
            position.before,
            id,
            actual,
        ),
        SourceOwner::NotForallWD(fact, p) => header_reference(
            &fact.typed_parameters.groups,
            &p.introduced_params,
            &p.assumed_dom_facts,
            position.before,
            id,
            actual,
        ),
        SourceOwner::KnownForall(p) => header_reference(
            &p.fact.typed_parameters.groups,
            &p.well_defined.introduced_params,
            &p.well_defined.assumed_dom_facts,
            position.before,
            id,
            actual,
        ),
        SourceOwner::Named(p) => {
            let (steps, head) = match (&p.statement.fact, &p.body) {
                (Fact::ForallFact(fact), ExecDefThmBodyProof::Forall(body)) => {
                    if let Some(reference) = header_reference(
                        &fact.typed_parameters.groups,
                        &body.introduced_params,
                        &body.assumed_dom_facts,
                        position.before,
                        id,
                        actual,
                    )? {
                        return Ok(Some(reference));
                    }
                    (
                        &body.proof_steps,
                        parameter_count(&fact.typed_parameters.groups)
                            + body.assumed_dom_facts.len(),
                    )
                }
                (_, ExecDefThmBodyProof::NonForall(body)) => (&body.proof_steps, 0),
                _ => return Ok(None),
            };
            for statement in steps
                .iter()
                .take(position.before.saturating_sub(head))
                .rev()
            {
                if let Some(reference) =
                    statement_reference(statement, id, actual, None, usize::MAX)?
                {
                    return Ok(Some(reference));
                }
            }
            Ok(None)
        }
        SourceOwner::Claim(p) => {
            let (steps, head) = match (&p.statement.fact, &p.body) {
                (Fact::ForallFact(fact), ExecClaimBodyProof::Forall(body)) => {
                    if let Some(reference) = header_reference(
                        &fact.typed_parameters.groups,
                        &body.introduced_params,
                        &body.assumed_dom_facts,
                        position.before,
                        id,
                        actual,
                    )? {
                        return Ok(Some(reference));
                    }
                    (
                        &body.proof_steps,
                        parameter_count(&fact.typed_parameters.groups)
                            + body.assumed_dom_facts.len(),
                    )
                }
                (_, ExecClaimBodyProof::NonForall(body)) => (&body.proof_steps, 0),
                _ => return Ok(None),
            };
            for statement in steps
                .iter()
                .take(position.before.saturating_sub(head))
                .rev()
            {
                if let Some(reference) =
                    statement_reference(statement, id, actual, None, usize::MAX)?
                {
                    return Ok(Some(reference));
                }
            }
            Ok(None)
        }
        SourceOwner::Call(p) => {
            for store in p.type_stores.iter().take(position.before) {
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            for proof in p
                .type_proofs
                .iter()
                .chain(&p.dom_proofs)
                .take(position.before)
            {
                if let Some(subject) = verified_subject(proof) {
                    if subject.fact_id() == id {
                        check_subject(&subject, actual)?;
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                }
            }
            for store in p
                .dom_stores
                .iter()
                .take(position.before.saturating_sub(p.type_proofs.len()))
            {
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            let head = p.type_proofs.len() + p.dom_proofs.len() + p.conclusions_wd.len();
            for store in p
                .returned_conclusions
                .iter()
                .take(position.before.saturating_sub(head))
            {
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::ThmRelease(p) => {
            for store in p.type_stores.iter().take(position.before).chain(
                p.dom_stores
                    .iter()
                    .take(position.before.saturating_sub(p.type_proofs.len())),
            ) {
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::SetBuilder(_, p) => {
            for store in p
                .defined_params
                .store_and_infer_results
                .iter()
                .take(position.before.saturating_sub(1))
            {
                if store.primary_fact_id() == id || infer_has_fact(store, id, actual)? {
                    if store.primary_fact_id() == id {
                        check_store_subject(&store.store, actual)?;
                    }
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            for assumed in p
                .assumed_facts
                .iter()
                .take(position.before.saturating_sub(2))
            {
                let store = &assumed.store_and_infer;
                if store.primary_fact_id() == id || infer_has_fact(store, id, actual)? {
                    if store.primary_fact_id() == id {
                        check_store_subject(&store.store, actual)?;
                    }
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::HaveEqualType(p) => header_reference(
            &p.statement.param_def.groups,
            &p.type_preflight,
            &[],
            position.before,
            id,
            actual,
        ),
        SourceOwner::StructLayers(layers) => {
            for layer in layers.iter().take(position.before) {
                for store in &layer.store_and_infer {
                    if let Some(reference) = stored_reference(store, id, actual)? {
                        return Ok(Some(if position.is_local() {
                            reference
                        } else {
                            position.context_application(&reference)
                        }));
                    }
                }
            }
            Ok(None)
        }
        SourceOwner::StructLayer(layer) => {
            for store in layer.store_and_infer.iter().take(position.before) {
                if let Some(reference) = stored_reference(store, id, actual)? {
                    return Ok(Some(if position.is_local() {
                        reference
                    } else {
                        position.context_application(&reference)
                    }));
                }
            }
            Ok(None)
        }
        SourceOwner::Template(p) => {
            if let Some(reference) = header_reference(
                &p.statement.template_arg_def.groups,
                &p.introduced_params,
                &p.assumed_dom_facts,
                position.before,
                id,
                actual,
            )? {
                return Ok(Some(reference));
            }
            let head =
                p.statement.template_arg_def.ordered_param_ids().len() + p.assumed_dom_facts.len();
            if position.before > head {
                statement_reference(&p.body, id, actual, None, usize::MAX)
            } else {
                Ok(None)
            }
        }
        SourceOwner::StructHeader(p) => {
            if let Some(introduced) = &p.introduced_params {
                for store in introduced
                    .defined_params
                    .store_and_infer_results
                    .iter()
                    .take(position.before)
                {
                    if let Some(reference) = stored_reference(store, id, actual)? {
                        return Ok(Some(reference));
                    }
                }
                let count = introduced.defined_params.store_and_infer_results.len();
                if position.before >= count {
                    for layer in introduced
                        .auto_opened_struct_layers
                        .as_deref()
                        .unwrap_or(&[])
                    {
                        for store in &layer.store_and_infer {
                            if let Some(reference) = stored_reference(store, id, actual)? {
                                return Ok(Some(reference));
                            }
                        }
                    }
                }
            }
            Ok(None)
        }
        SourceOwner::StructFields(p) => {
            for stage in p
                .field_scope
                .equivalent_facts
                .iter()
                .take(position.before.saturating_sub(p.statement.fields.len()))
            {
                if stage.store.primary_fact_id() == id {
                    check_store_subject(&stage.store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if stored_projection_has_fact(&stage.store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            for stage in p.field_scope.fields.iter().take(position.before) {
                for store in &stage.defined.store_and_infer_results {
                    if store.primary_fact_id() == id {
                        check_store_subject(&store.store, actual)?;
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                    if infer_has_fact(store, id, actual)? {
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                }
            }
            Ok(None)
        }
        SourceOwner::PropDefinition(p) => {
            let stores = &p.defined_params.store_and_infer_results;
            for store in stores.iter().take(position.before) {
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            for assumption in p
                .assumed_iff_facts
                .iter()
                .take(position.before.saturating_sub(stores.len()))
            {
                let store = &assumption.store_and_infer;
                if store.primary_fact_id() == id {
                    check_store_subject(&store.store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::AtomicInference(seed, infer) => {
            if seed.fact_id() == id {
                check_subject(seed, actual)?;
                return Ok(Some(inference_fact_reference(position, id)));
            }
            for captured in atomic_inference_stages_before(infer, position.before).into_iter() {
                let store = &captured.store;
                if store.primary_fact_id() == id {
                    check_store_subject(store, actual)?;
                    return Ok(Some(inference_fact_reference(position, id)));
                }
                if stored_projection_has_fact(store, id, actual)? {
                    return Ok(Some(inference_fact_reference(position, id)));
                }
            }
            Ok(None)
        }
        SourceOwner::CompoundInference(store) => {
            compound_inference_reference(store, position.before, id, actual)
                .map(|reference| reference.map(|_| inference_fact_reference(position, id)))
        }
        SourceOwner::OrderBoundInference(rule) => {
            let (checks, captured) = order_bound_stages(rule).expect("conditional order owner");
            if position.before > checks.len() && captured.store.primary_fact_id() == id {
                check_store_subject(&captured.store, actual)?;
                return Ok(Some(inference_fact_reference(position, id)));
            }
            Ok(None)
        }
        SourceOwner::KnownApplication(proof) => {
            for (fact, _) in known_application_requirements(proof)
                .into_iter()
                .take(position.before.saturating_sub(proof.arg_match_proofs.len()))
            {
                if fact.fact_id() == id {
                    check_subject(fact, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::ChainClosure(closure) => {
            let store = &closure.derived.store;
            if position.before > 0 && store.primary_fact_id() == id {
                check_store_subject(store, actual)?;
                return Ok(Some(inference_fact_reference(position, id)));
            }
            Ok(None)
        }
        SourceOwner::PropInference(store) => {
            if matches!(
                &store.infer,
                Some(InferResult::AndFact(_)) | Some(InferResult::ChainFact(_))
            ) {
                return compound_inference_reference(store, position.before, id, actual)
                    .map(|reference| reference.map(|_| inference_fact_reference(position, id)));
            }
            if let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
                &store.infer
            {
                let group = SourcePosition {
                    owner: SourceOwner::EqualityInferences(rules),
                    ..*position
                };
                return fact_reference_in_owner(&group, id, actual);
            }
            for derived in prop_inference_stages(store)
                .into_iter()
                .take(position.before)
            {
                let store = &derived.store;
                if store.primary_fact_id() == id {
                    check_store_subject(store, actual)?;
                    return Ok(Some(inference_fact_reference(position, id)));
                }
                if stored_projection_has_fact(store, id, actual)? {
                    return Ok(Some(inference_fact_reference(position, id)));
                }
            }
            Ok(None)
        }
        SourceOwner::EqualityInferences(rules) => {
            for rule in rules.iter().take(position.before) {
                for captured in rule.stored_conclusions() {
                    let store = &captured.store;
                    if store.primary_fact_id() == id {
                        check_store_subject(store, actual)?;
                        return Ok(Some(inference_fact_reference(position, id)));
                    }
                    if stored_projection_has_fact(store, id, actual)? {
                        return Ok(Some(inference_fact_reference(position, id)));
                    }
                }
            }
            Ok(None)
        }
        SourceOwner::PositivePowerInferences(rule) => {
            for transport in rule.transports.iter().take(position.before) {
                if transport.derived.store.primary_fact_id() == id {
                    check_store_subject(&transport.derived.store, actual)?;
                    return Ok(Some(inference_fact_reference(position, id)));
                }
            }
            Ok(None)
        }
        SourceOwner::PositivePowerTransport(transport) => {
            if position.before > 2 && transport.derived.store.primary_fact_id() == id {
                check_store_subject(&transport.derived.store, actual)?;
                Ok(Some(inference_fact_reference(position, id)))
            } else {
                Ok(None)
            }
        }
        owner @ (SourceOwner::AdditiveInference(_)
        | SourceOwner::SubtractiveInference(_)
        | SourceOwner::NonzeroFactorInference(_)
        | SourceOwner::CommonDenominatorInference(_)
        | SourceOwner::NonzeroNumeratorInference(_)) => {
            let (checks, captured) = cancellation_stages(owner).expect("cancellation owner");
            let store = &captured.store;
            if position.before > checks.len() && store.primary_fact_id() == id {
                check_store_subject(store, actual)?;
                Ok(Some(inference_fact_reference(position, id)))
            } else {
                Ok(None)
            }
        }
        SourceOwner::WD(proof) | SourceOwner::WDLocals(proof, _) => {
            if let Some((_, carriers, parameters, domains, _)) = function_binder(proof) {
                for store in parameters
                    .store_and_infer_results
                    .iter()
                    .take(position.before.saturating_sub(carriers.len()))
                {
                    if store.primary_fact_id() == id {
                        check_store_subject(&store.store, actual)?;
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                    if infer_has_fact(store, id, actual)? {
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                }
                let head = carriers.len() + parameters.store_and_infer_results.len();
                for domain in domains.iter().take(position.before.saturating_sub(head)) {
                    let store = &domain.store_and_infer;
                    if store.primary_fact_id() == id {
                        check_store_subject(&store.store, actual)?;
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                    if infer_has_fact(store, id, actual)? {
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                }
            }
            Ok(None)
        }
        // Formation children can supply construction evidence, never a truth producer.
        SourceOwner::Verify(_)
        | SourceOwner::AtomicVerify(_)
        | SourceOwner::AtomicWD(_)
        | SourceOwner::AtomicWDLocals(..)
        | SourceOwner::EqualWDLocals(..)
        | SourceOwner::FactWD(_)
        | SourceOwner::HaveGroup(_, _)
        | SourceOwner::ParamTypeWD(_)
        | SourceOwner::ByDef(_)
        | SourceOwner::PropRequirements(_)
        | SourceOwner::EqualityRequirements(_)
        | SourceOwner::CalleeInstance(_)
        | SourceOwner::AtomicFnUnfold(_) => Ok(None),
        SourceOwner::FunctionNormalization(_)
        | SourceOwner::FunctionExpansion(_)
        | SourceOwner::CompositionExpansion(_)
        | SourceOwner::FiniteExpansion(_)
        | SourceOwner::RangeExpansion(_)
        | SourceOwner::Choice(_)
        | SourceOwner::Zorn(_)
        | SourceOwner::FunctionDefinitionRewrite(_)
        | SourceOwner::FormedSubjects(..)
        | SourceOwner::ChainObjects(..)
        | SourceOwner::PropObjects(..)
        | SourceOwner::Term
        | SourceOwner::Completion(_)
        | SourceOwner::FunctionDomainWD(_)
        | SourceOwner::CompleteDomainSource(_) => Ok(None),
    }
}

fn named_steps(proof: &ExecDefThmStmtSuccess) -> (&[ExecStmtResult], usize) {
    match (&proof.statement.fact, &proof.body) {
        (Fact::ForallFact(fact), ExecDefThmBodyProof::Forall(body)) => (
            &body.proof_steps,
            parameter_count(&fact.typed_parameters.groups) + body.assumed_dom_facts.len(),
        ),
        (_, ExecDefThmBodyProof::NonForall(body)) => (&body.proof_steps, 0),
        _ => (&[], 0),
    }
}
fn claim_steps(proof: &ExecClaimStmtSuccess) -> (&[ExecStmtResult], usize) {
    match (&proof.statement.fact, &proof.body) {
        (Fact::ForallFact(fact), ExecClaimBodyProof::Forall(body)) => (
            &body.proof_steps,
            parameter_count(&fact.typed_parameters.groups) + body.assumed_dom_facts.len(),
        ),
        (_, ExecClaimBodyProof::NonForall(body)) => (&body.proof_steps, 0),
        _ => (&[], 0),
    }
}

fn alias_in_statement<T>(
    statement: &ExecStmtResult,
    object: &Obj,
    before: usize,
    parent: &SourcePosition<'_>,
    active: &SourcePosition<'_>,
    callback: &mut impl FnMut(
        &BoundName,
        &Obj,
        &VerifyObjWellDefinedResult,
        &SourcePosition<'_>,
    ) -> Result<T, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    // This exact literal already has a source declaration. Reuse its emitted
    // constructor only after both original formation stages have completed.
    if let (
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(proof),
        )),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)),
    ) = (statement, object)
    {
        if before >= 2 && &proof.statement.equal_to_anonymous_fn == literal {
            let completed = SourcePosition::new(Some(parent), SourceOwner::Statement(statement), 2);
            if !obeys_active_stage_ceilings(active, &completed) {
                return Ok(None);
            }
            let original =
                super::helper::success_object_wd(&proof.anonymous_fn_well_defined, object)?;
            let producer = SourcePosition::new(Some(parent), SourceOwner::Statement(statement), 0);
            return callback(
                &proof.statement.name,
                original.obj(),
                &proof.anonymous_fn_well_defined,
                &producer,
            )
            .map(Some);
        }
    }
    let Obj::Identifier(IdentifierObj::Plain { id, .. }) = object else {
        return Ok(None);
    };
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
        )) if before > 0 && p.statement.name.id == *id => {
            let completed = SourcePosition::new(Some(parent), SourceOwner::Statement(statement), 1);
            if !obeys_active_stage_ceilings(active, &completed) {
                return Ok(None);
            }
            let position = SourcePosition::new(Some(parent), SourceOwner::Statement(statement), 0);
            callback(
                &p.statement.name,
                &p.statement.value,
                &p.value_well_defined,
                &position,
            )
            .map(Some)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
        )) => {
            let count = p.statement.objs_equal_to.len();
            for (index, parameter) in p
                .statement
                .param_def
                .groups
                .iter()
                .flat_map(|group| &group.params)
                .enumerate()
            {
                if parameter.id == *id && before > 2 * count + index {
                    if let (Some(value), Some(wd)) = (
                        p.statement.objs_equal_to.get(index),
                        p.equal_to_well_defined.get(index),
                    ) {
                        let completed = SourcePosition::new(
                            Some(parent),
                            SourceOwner::Statement(statement),
                            2 * count + index + 1,
                        );
                        if !obeys_active_stage_ceilings(active, &completed) {
                            return Ok(None);
                        }
                        let position = SourcePosition::new(
                            Some(parent),
                            SourceOwner::Statement(statement),
                            index,
                        );
                        return callback(parameter, value, wd, &position).map(Some);
                    }
                }
            }
            Ok(None)
        }
        _ => Ok(None),
    }
}

fn constructor_has_closed_leaf(evidence: SourceConstructor<'_>) -> bool {
    match evidence {
        SourceConstructor::Checked(proof) => closed_leaf(proof.obj()),
        SourceConstructor::Inferred(store) => store.atomic_components().iter().any(|(_, fact)| {
            atomic_fact_args_ref(fact)
                .iter()
                .any(|obj| closed_leaf(obj))
        }),
    }
}

fn visit_visible<T>(
    start: &SourcePosition<'_>,
    object: &Obj,
    visit_closed_statements: bool,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    // Only matching subjects need the full ancestry check. Keep that check in
    // this shared visitor so every caller retains the same scope boundary.
    let object_ir = object.ir();
    let mut bounded_wd = |proof: SourceConstructor<'_>, producer: &SourcePosition<'_>| {
        let relevant = match proof {
            SourceConstructor::Checked(proof) => proof.obj().ir() == object_ir,
            SourceConstructor::Inferred(store) => {
                store.atomic_components().iter().any(|(_, fact)| {
                    atomic_fact_args_ref(fact)
                        .iter()
                        .any(|arg| arg.ir() == object_ir)
                })
            }
        };
        if relevant && obeys_active_stage_ceilings(start, producer) {
            wd(proof, producer)
        } else {
            Ok(None)
        }
    };
    let mut bounded_verify = |proof: &VerifyFactResult, producer: &SourcePosition<'_>| {
        let relevant = match proof {
            VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
                VerifyAtomicExceptEqualityFactResult::Success(result) => match &result.fact {
                    AtomicFact::InFact(fact) => fact.element.ir() == object_ir,
                    AtomicFact::NotEqualFact(fact) => fact.left.ir() == object_ir,
                    _ => false,
                },
                _ => false,
            },
            _ => false,
        };
        if relevant && obeys_active_stage_ceilings(start, producer) {
            verify(proof, producer)
        } else {
            Ok(None)
        }
    };
    let mut free_ids = std::collections::HashSet::new();
    crate::instantiate::collect_free_plain_ids(object, &Default::default(), &mut free_ids);
    let mut position = Some(start);
    let mut requires_local_producer = false;
    while let Some(current) = position {
        if matches!(current.owner, SourceOwner::Run(_)) {
            break;
        }
        if free_ids
            .iter()
            .any(|id| parameter_in_owner(current, *id).is_some())
        {
            requires_local_producer = true;
            break;
        }
        position = current.parent;
    }
    let mut position = Some(start);
    while let Some(current) = position {
        // A source-owned local IdentifierId cannot occur in any earlier global
        // statement. Retain all local ancestors, but do not search beyond its
        // introduction for an object that depends on that binder.
        if requires_local_producer && matches!(current.owner, SourceOwner::Run(_)) {
            return Ok(None);
        }
        if !visit_closed_statements {
            if let SourceOwner::Run(run) = current.owner {
                // A completed named theorem exports only closed primitive WD
                // leaves through this visitor, and no internal truth proofs.
                // Queries for other checked constructors or verified membership
                // cannot match there; avoid walking their entire proof trees.
                for (index, statement) in run
                    .statement_results
                    .iter()
                    .take(current.before)
                    .enumerate()
                    .rev()
                {
                    if matches!(
                        statement,
                        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(_))
                    ) {
                        continue;
                    }
                    let prior = SourcePosition::new(None, SourceOwner::Run(run), index);
                    if let Some(value) = visit_statement(
                        statement,
                        usize::MAX,
                        &prior,
                        &mut bounded_wd,
                        &mut bounded_verify,
                    )? {
                        return Ok(Some(value));
                    }
                }
                position = current.parent;
                continue;
            }
        }
        if let Some(value) = visit_owner(current, &mut bounded_wd, &mut bounded_verify)? {
            return Ok(Some(value));
        }
        position = current.parent;
    }
    Ok(None)
}

fn obeys_active_stage_ceilings(start: &SourcePosition<'_>, producer: &SourcePosition<'_>) -> bool {
    // Check only newly opened candidate stages. A callback can inherit a
    // completed-child marker followed by its pre-stage replay cursor; the
    // shared suffix was already admitted by the original lookup and is not
    // another attempt to reopen that child while replaying its internal WD.
    let mut candidate = Some(producer);
    while let Some(stage) = candidate {
        let mut shared = Some(start);
        while let Some(active) = shared {
            if std::ptr::eq(stage, active) {
                return true;
            }
            shared = active.parent;
        }
        let mut active = Some(start);
        while let Some(ceiling) = active {
            let boundary = match stage.owner {
                SourceOwner::Completion(boundary) => boundary,
                _ => stage,
            };
            if same_source_owner(ceiling.owner, boundary.owner) && boundary.before > ceiling.before
            {
                return false;
            }
            active = ceiling.parent;
        }
        candidate = stage.parent;
    }
    true
}

fn same_source_owner(left: SourceOwner<'_>, right: SourceOwner<'_>) -> bool {
    match (left, right) {
        (SourceOwner::Run(a), SourceOwner::Run(b)) => std::ptr::eq(a, b),
        (SourceOwner::Statement(a), SourceOwner::Statement(b)) => std::ptr::eq(a, b),
        (SourceOwner::Verify(a), SourceOwner::Verify(b)) => std::ptr::eq(a, b),
        (SourceOwner::AtomicVerify(a), SourceOwner::AtomicVerify(b)) => std::ptr::eq(a, b),
        (
            SourceOwner::AtomicVerify(a),
            SourceOwner::Verify(VerifyFactResult::AtomicExceptEquality(b)),
        )
        | (
            SourceOwner::Verify(VerifyFactResult::AtomicExceptEquality(b)),
            SourceOwner::AtomicVerify(a),
        ) => {
            matches!(b.as_ref(), VerifyAtomicExceptEqualityFactResult::Success(b) if std::ptr::eq(a, b))
        }
        (
            SourceOwner::WD(a) | SourceOwner::WDLocals(a, _),
            SourceOwner::WD(b) | SourceOwner::WDLocals(b, _),
        ) => std::ptr::eq(a, b),
        (SourceOwner::SetBuilder(a, pa), SourceOwner::SetBuilder(b, pb)) => {
            std::ptr::eq(a, b) && std::ptr::eq(pa, pb)
        }
        (SourceOwner::Named(a), SourceOwner::Named(b)) => std::ptr::eq(a, b),
        (SourceOwner::Template(a), SourceOwner::Template(b)) => std::ptr::eq(a, b),
        (SourceOwner::Claim(a), SourceOwner::Claim(b)) => std::ptr::eq(a, b),
        (SourceOwner::Sketch(a), SourceOwner::Sketch(b)) => std::ptr::eq(a, b),
        (SourceOwner::RangeExpansion(a), SourceOwner::RangeExpansion(b)) => std::ptr::eq(a, b),
        (SourceOwner::Choice(a), SourceOwner::Choice(b)) => std::ptr::eq(a, b),
        (SourceOwner::Zorn(a), SourceOwner::Zorn(b)) => std::ptr::eq(a, b),
        (SourceOwner::Forall(a), SourceOwner::Forall(b)) => std::ptr::eq(a, b),
        (SourceOwner::EmptyForall(a), SourceOwner::EmptyForall(b)) => std::ptr::eq(a, b),
        (SourceOwner::ForallWD(_, a), SourceOwner::ForallWD(_, b)) => std::ptr::eq(a, b),
        (SourceOwner::NotForallWD(_, a), SourceOwner::NotForallWD(_, b)) => std::ptr::eq(a, b),
        (SourceOwner::ForallIffWD(_, a), SourceOwner::ForallIffWD(_, b)) => std::ptr::eq(a, b),
        (SourceOwner::ExistWD(_, a), SourceOwner::ExistWD(_, b)) => std::ptr::eq(a, b),
        (SourceOwner::WitnessExist(a), SourceOwner::WitnessExist(b)) => std::ptr::eq(a, b),
        (SourceOwner::WitnessAtomic(a), SourceOwner::WitnessAtomic(b)) => std::ptr::eq(a, b),
        (SourceOwner::WitnessNonempty(a), SourceOwner::WitnessNonempty(b)) => std::ptr::eq(a, b),
        (SourceOwner::Contra(a), SourceOwner::Contra(b)) => std::ptr::eq(a, b),
        (SourceOwner::Extension(a), SourceOwner::Extension(b)) => std::ptr::eq(a, b),
        (SourceOwner::FnExtension(a), SourceOwner::FnExtension(b)) => std::ptr::eq(a, b),
        (SourceOwner::OrSelected(a), SourceOwner::OrSelected(b)) => std::ptr::eq(a, b),
        (SourceOwner::EnumerationAssignment(a, pa), SourceOwner::EnumerationAssignment(b, pb)) => {
            std::ptr::eq(a, b) && std::ptr::eq(pa, pb)
        }
        (SourceOwner::CasesBranch(a), SourceOwner::CasesBranch(b)) => std::ptr::eq(a, b),
        (SourceOwner::KnownForall(a), SourceOwner::KnownForall(b)) => std::ptr::eq(a, b),
        (SourceOwner::KnownApplication(a), SourceOwner::KnownApplication(b)) => std::ptr::eq(a, b),
        (SourceOwner::CalleeInstance(a), SourceOwner::CalleeInstance(b)) => std::ptr::eq(a, b),
        (SourceOwner::Call(a), SourceOwner::Call(b)) => std::ptr::eq(a, b),
        (SourceOwner::ThmRelease(a), SourceOwner::ThmRelease(b)) => std::ptr::eq(a, b),
        (SourceOwner::FunctionDomainWD(a), SourceOwner::FunctionDomainWD(b)) => std::ptr::eq(a, b),
        (SourceOwner::CompleteDomainSource(a), SourceOwner::CompleteDomainSource(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::HaveEqualType(a), SourceOwner::HaveEqualType(b)) => std::ptr::eq(a, b),
        (
            SourceOwner::AtomicWD(a) | SourceOwner::AtomicWDLocals(a, _),
            SourceOwner::AtomicWD(b) | SourceOwner::AtomicWDLocals(b, _),
        ) => std::ptr::eq(a, b),
        (SourceOwner::ChainObjects(a, _), SourceOwner::ChainObjects(b, _)) => std::ptr::eq(a, b),
        (SourceOwner::EqualWDLocals(a, _), SourceOwner::EqualWDLocals(b, _)) => std::ptr::eq(a, b),
        (SourceOwner::FactWD(a), SourceOwner::FactWD(b)) => std::ptr::eq(a, b),
        (SourceOwner::InferredStore(a), SourceOwner::InferredStore(b)) => std::ptr::eq(a, b),
        (SourceOwner::HaveGroup(a, pa), SourceOwner::HaveGroup(b, pb)) => {
            std::ptr::eq(a, b) && std::ptr::eq(pa, pb)
        }
        (SourceOwner::ParamTypeWD(a), SourceOwner::ParamTypeWD(b)) => std::ptr::eq(a, b),
        (SourceOwner::PropDefinition(a), SourceOwner::PropDefinition(b)) => std::ptr::eq(a, b),
        (SourceOwner::StructHeader(a), SourceOwner::StructHeader(b)) => std::ptr::eq(a, b),
        (SourceOwner::StructFields(a), SourceOwner::StructFields(b)) => std::ptr::eq(a, b),
        (SourceOwner::StructLayer(a), SourceOwner::StructLayer(b)) => std::ptr::eq(a, b),
        (SourceOwner::StructLayers(a), SourceOwner::StructLayers(b)) => std::ptr::eq(a, b),
        (SourceOwner::ByDef(a), SourceOwner::ByDef(b)) => std::ptr::eq(a, b),
        (SourceOwner::PropRequirements(a), SourceOwner::PropRequirements(b)) => std::ptr::eq(a, b),
        (SourceOwner::PropInference(a), SourceOwner::PropInference(b)) => std::ptr::eq(a, b),
        (SourceOwner::AtomicInference(a, ia), SourceOwner::AtomicInference(b, ib)) => {
            std::ptr::eq(a, b) && std::ptr::eq(ia, ib)
        }
        (SourceOwner::AtomicInference(_, infer), SourceOwner::PropInference(store))
        | (SourceOwner::PropInference(store), SourceOwner::AtomicInference(_, infer)) => {
            matches!(&store.infer, Some(InferResult::AtomicFact(actual)) if std::ptr::eq(infer, actual))
        }
        (SourceOwner::CompoundInference(a), SourceOwner::CompoundInference(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::ChainClosure(a), SourceOwner::ChainClosure(b)) => std::ptr::eq(a, b),
        (SourceOwner::OrderBoundInference(a), SourceOwner::OrderBoundInference(b)) => {
            match (a, b) {
                (OrderBoundInference::Strict(a), OrderBoundInference::Strict(b)) => {
                    std::ptr::eq(a, b)
                }
                (OrderBoundInference::WeakInteger(a), OrderBoundInference::WeakInteger(b)) => {
                    std::ptr::eq(a, b)
                }
                _ => false,
            }
        }
        (SourceOwner::EqualityInferences(a), SourceOwner::EqualityInferences(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::PositivePowerInferences(a), SourceOwner::PositivePowerInferences(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::PositivePowerTransport(a), SourceOwner::PositivePowerTransport(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::AdditiveInference(a), SourceOwner::AdditiveInference(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::SubtractiveInference(a), SourceOwner::SubtractiveInference(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::NonzeroFactorInference(a), SourceOwner::NonzeroFactorInference(b)) => {
            std::ptr::eq(a, b)
        }
        (
            SourceOwner::CommonDenominatorInference(a),
            SourceOwner::CommonDenominatorInference(b),
        ) => std::ptr::eq(a, b),
        (SourceOwner::NonzeroNumeratorInference(a), SourceOwner::NonzeroNumeratorInference(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::AtomicFnUnfold(a), SourceOwner::AtomicFnUnfold(b)) => std::ptr::eq(a, b),
        (SourceOwner::EqualityRequirements(a), SourceOwner::EqualityRequirements(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::FunctionNormalization(a), SourceOwner::FunctionNormalization(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::FunctionExpansion(a), SourceOwner::FunctionExpansion(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::FiniteExpansion(a), SourceOwner::FiniteExpansion(b)) => std::ptr::eq(a, b),
        (SourceOwner::CompositionExpansion(a), SourceOwner::CompositionExpansion(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::FunctionDefinitionRewrite(a), SourceOwner::FunctionDefinitionRewrite(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::Piecewise(a), SourceOwner::Piecewise(b)) => a.same_scope(b),
        (SourceOwner::PiecewiseUnfold(a), SourceOwner::PiecewiseUnfold(b)) => std::ptr::eq(a, b),
        (SourceOwner::RecursiveFunction(a), SourceOwner::RecursiveFunction(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::RecursiveCase(a), SourceOwner::RecursiveCase(b)) => std::ptr::eq(a, b),
        (SourceOwner::RecursiveDisjoint(a), SourceOwner::RecursiveDisjoint(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::RecursiveUnfold(a), SourceOwner::RecursiveUnfold(b)) => std::ptr::eq(a, b),
        (SourceOwner::Induction(a), SourceOwner::Induction(b)) => {
            std::ptr::eq(a.stored, b.stored) && a.strong == b.strong
        }
        (SourceOwner::InductionCase(a, ca), SourceOwner::InductionCase(b, cb)) => {
            std::ptr::eq(a.stored, b.stored) && a.strong == b.strong && std::ptr::eq(ca, cb)
        }
        _ => false,
    }
}

fn visit_function_formation<T>(
    proof: &ObjWellDefinedProof,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let Some((_, carriers, parameters, domains, _)) = function_binder(proof) else {
        return Ok(None);
    };
    let head = carriers.len() + parameters.store_and_infer_results.len();
    let end = head + domains.len();
    let ret = match proof {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(p),
                ),
            ..
        } => {
            if position.before > end + 2 {
                if let AnonymousFnBodyInReturnSetProof::CheckedMembership(member) =
                    &p.body_in_ret_set
                {
                    let prior = SourcePosition {
                        before: end + 2,
                        ..*position
                    };
                    if let Some(value) = visit_complete_verify(member, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            if position.before > end + 1 {
                let prior = SourcePosition {
                    before: end + 1,
                    ..*position
                };
                if let Some(value) = visit_complete_wd(&p.body_well_defined, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            &p.ret_set_well_defined
        }
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnSet(p)),
            ..
        } => &p.ret_set_well_defined,
        _ => return Ok(None),
    };
    if position.before > end {
        let prior = SourcePosition {
            before: end,
            ..*position
        };
        if let Some(value) = visit_complete_wd(ret, &prior, wd, verify)? {
            return Ok(Some(value));
        }
    }
    for (index, domain) in domains
        .iter()
        .take(position.before.saturating_sub(head))
        .enumerate()
        .rev()
    {
        let prior = SourcePosition {
            before: head + index,
            ..*position
        };
        let inferred = SourcePosition::new(
            Some(&prior),
            SourceOwner::PropInference(&domain.store_and_infer),
            usize::MAX,
        );
        if let Some(value) = visit_owner(&inferred, wd, verify)? {
            return Ok(Some(value));
        }
        let formation = SourcePosition::new(
            Some(&prior),
            SourceOwner::FactWD(&domain.well_defined),
            usize::MAX,
        );
        if let Some(value) =
            visit_fact_formation(&domain.well_defined, usize::MAX, &formation, wd, verify)?
        {
            return Ok(Some(value));
        }
    }
    for (index, store) in parameters
        .store_and_infer_results
        .iter()
        .take(position.before.saturating_sub(carriers.len()))
        .enumerate()
        .rev()
    {
        let prior = SourcePosition {
            before: carriers.len() + index + 1,
            ..*position
        };
        let inference =
            SourcePosition::new(Some(&prior), SourceOwner::PropInference(store), usize::MAX);
        if let Some(value) = visit_owner(&inference, wd, verify)? {
            return Ok(Some(value));
        }
    }
    for (index, carrier) in carriers.iter().take(position.before).enumerate().rev() {
        let prior = SourcePosition {
            before: index,
            ..*position
        };
        if let Some(value) = visit_complete_wd(carrier, &prior, wd, verify)? {
            return Ok(Some(value));
        }
    }
    Ok(None)
}

fn visit_fact_stage<T>(
    proof: &FactWellDefinedProof,
    stage: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if position.before <= stage {
        return Ok(None);
    }
    let prior = SourcePosition {
        before: stage,
        ..*position
    };
    let formation = SourcePosition::new(Some(&prior), SourceOwner::FactWD(proof), usize::MAX);
    visit_fact_formation(proof, usize::MAX, &formation, wd, verify)
}

// Quantified formation closes its binders before the next statement stage.
// Only closed constructors may be recovered from that completed scope.
fn visit_source_fact_stage<T>(
    fact: &Fact,
    proof: &FactWellDefinedProof,
    stage: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if position.before <= stage {
        return Ok(None);
    }
    if let (
        Fact::ExistFact(fact) | Fact::NotExistFact(fact),
        FactWellDefinedProof::ExistFact(proof),
    ) = (fact, proof)
    {
        let prior = SourcePosition {
            before: stage,
            ..*position
        };
        return visit_closed_scope(SourceOwner::ExistWD(fact, proof), &prior, wd);
    }
    if let (Fact::NotForall(fact), FactWellDefinedProof::NotForall(proof)) = (fact, proof) {
        let prior = SourcePosition {
            before: stage,
            ..*position
        };
        return visit_not_forall_outer_carrier(fact, proof, &prior, wd, verify);
    }
    visit_fact_stage(proof, stage, position, wd, verify)
}

// The first carrier is formed before any quantified parameter or hypothetical
// premise exists. Its original constructor can therefore be reused in the
// enclosing scope (for example, {a} in `not forall x {a}: ...`). Later carrier
// and body evidence stays inside the quantified formation.
fn visit_not_forall_outer_carrier<T>(
    fact: &NotForallFact,
    proof: &crate::execute::execute_fact_stmt::verify_not_forall_fact::NotForallFactWellDefinedProof,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let Some(ParamTypeWellDefinedProof::Obj(carrier)) =
        proof.introduced_params.param_type_well_defined.first()
    else {
        return Ok(None);
    };
    let scope = SourcePosition::new(Some(position), SourceOwner::NotForallWD(fact, proof), 0);
    visit_complete_wd(carrier, &scope, wd, verify)
}

fn visit_verify_stage<T>(
    proof: &VerifyFactResult,
    stage: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if position.before <= stage {
        return Ok(None);
    }
    let prior = SourcePosition {
        before: stage,
        ..*position
    };
    visit_complete_verify(proof, &prior, wd, verify)
}

fn visit_store_stage<T>(
    store: &StoreFactAndInferResult,
    stage: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if position.before <= stage {
        return Ok(None);
    }
    let completed = SourcePosition {
        before: stage + 1,
        ..*position
    };
    let inference = SourcePosition::new(
        Some(&completed),
        SourceOwner::PropInference(store),
        usize::MAX,
    );
    visit_owner(&inference, wd, verify)
}

fn visit_closed_scope<T>(
    owner: SourceOwner<'_>,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let mut closed = |evidence: SourceConstructor<'_>, cursor: &SourcePosition<'_>| {
        let closed = match evidence {
            SourceConstructor::Checked(proof) => closed_leaf(proof.obj()),
            SourceConstructor::Inferred(store) => {
                store.atomic_components().iter().all(|(_, fact)| {
                    atomic_fact_args_ref(fact)
                        .iter()
                        .all(|object| closed_leaf(object))
                })
            }
        };
        if closed {
            wd(evidence, cursor)
        } else {
            Ok(None)
        }
    };
    let scope = SourcePosition::new(Some(position), owner, usize::MAX);
    visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
}

fn visit_contradiction_closing<T>(
    closing: &ByContradictionClosingSuccess,
    head: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if let Some(value) =
        visit_verify_stage(&closing.negated_impossible, head + 1, position, wd, verify)?
    {
        return Ok(Some(value));
    }
    visit_verify_stage(&closing.impossible, head, position, wd, verify)
}

fn visit_local_scope<T>(
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let (steps, head) = local_steps(position.owner).expect("local proof owner");
    let closing_head = head + steps.len();
    match position.owner {
        SourceOwner::Sketch(_) => {}
        SourceOwner::FnExtension(p) => {
            if let Some(value) =
                visit_verify_stage(&p.pointwise_proof, closing_head, position, wd, verify)?
            {
                return Ok(Some(value));
            }
        }
        SourceOwner::Extension(p) => {
            if let Some(value) =
                visit_verify_stage(&p.right_to_left, closing_head + 1, position, wd, verify)?
            {
                return Ok(Some(value));
            }
            if let Some(value) =
                visit_verify_stage(&p.left_to_right, closing_head, position, wd, verify)?
            {
                return Ok(Some(value));
            }
        }
        SourceOwner::WitnessNonempty(p) => {
            if let Some(value) =
                visit_verify_stage(&p.membership_check, closing_head, position, wd, verify)?
            {
                return Ok(Some(value));
            }
        }
        SourceOwner::WitnessExist(p) => {
            if let Some(value) =
                visit_witness_obligations(&p.obligations, closing_head, position, wd, verify)?
            {
                return Ok(Some(value));
            }
        }
        SourceOwner::WitnessAtomic(p) => {
            if let Some(value) =
                visit_witness_obligations(&p.obligations, closing_head, position, wd, verify)?
            {
                return Ok(Some(value));
            }
        }
        SourceOwner::Contra(p) => {
            if let Some(value) =
                visit_contradiction_closing(&p.closing, closing_head, position, wd, verify)?
            {
                return Ok(Some(value));
            }
        }
        SourceOwner::CasesBranch(p) => match &p.closing {
            ByCasesBranchClosingSuccess::Impossible(closing) => {
                if let Some(value) =
                    visit_contradiction_closing(closing, closing_head, position, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            ByCasesBranchClosingSuccess::ThenFacts { proved_then_facts } => {
                for (index, proof) in proved_then_facts.iter().enumerate().rev() {
                    if let Some(value) = visit_store_stage(
                        &proof.store_and_infer,
                        closing_head + 2 * index + 1,
                        position,
                        wd,
                        verify,
                    )? {
                        return Ok(Some(value));
                    }
                    if let Some(value) = visit_verify_stage(
                        &proof.verify_result,
                        closing_head + 2 * index,
                        position,
                        wd,
                        verify,
                    )? {
                        return Ok(Some(value));
                    }
                }
            }
        },
        _ => unreachable!("local proof owner"),
    }
    for (index, statement) in steps
        .iter()
        .take(position.before.saturating_sub(head))
        .enumerate()
        .rev()
    {
        let prior = SourcePosition {
            before: head + index,
            ..*position
        };
        if let Some(value) = visit_statement(statement, usize::MAX, &prior, wd, verify)? {
            return Ok(Some(value));
        }
    }
    if let Some((fact, introduced, equalities)) = witness_header(position.owner) {
        let count = parameter_count(&fact.typed_parameters.groups);
        for (index, store) in equalities.iter().enumerate().rev() {
            if let Some(value) = visit_store_stage(store, count + index, position, wd, verify)? {
                return Ok(Some(value));
            }
        }
        return visit_header(
            &fact.typed_parameters.groups,
            introduced,
            &[],
            position,
            wd,
            verify,
        );
    }
    if matches!(
        position.owner,
        SourceOwner::Sketch(_)
            | SourceOwner::WitnessNonempty(_)
            | SourceOwner::Extension(_)
            | SourceOwner::FnExtension(_)
            | SourceOwner::OrSelected(_)
            | SourceOwner::EnumerationAssignment(..)
    ) {
        return Ok(None);
    }
    let (assumption, store) = match position.owner {
        SourceOwner::Contra(p) => (&p.reverse_assumption_wd, &p.negation_assumed),
        SourceOwner::CasesBranch(p) => (&p.assumption_wd, &p.assumptions_stored),
        _ => unreachable!("local assumption owner"),
    };
    if let Some(value) = visit_store_stage(store, 1, position, wd, verify)? {
        return Ok(Some(value));
    }
    match position.owner {
        SourceOwner::Contra(p) => {
            visit_source_fact_stage(&p.reverse_assumption, assumption, 0, position, wd, verify)
        }
        _ => visit_fact_stage(assumption, 0, position, wd, verify),
    }
}

fn visit_witness_obligations<T>(
    obligations: &WitnessExistObligationSuccess,
    head: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if let Some(proof) = &obligations.uniqueness_check {
        if let Some(value) = visit_verify_stage(
            proof,
            head + obligations.body_checks.len(),
            position,
            wd,
            verify,
        )? {
            return Ok(Some(value));
        }
    }
    for (index, proof) in obligations.body_checks.iter().enumerate().rev() {
        if let Some(value) = visit_verify_stage(proof, head + index, position, wd, verify)? {
            return Ok(Some(value));
        }
    }
    Ok(None)
}

fn visit_witness_statement<T>(
    ambient: &WitnessExistAmbientSuccess,
    arguments: &[VerifyFactResult],
    owner: SourceOwner<'_>,
    store: &StoreFactAndInferResult,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let ambient_end = witness_ambient_len(ambient, arguments);
    if let Some(value) = visit_store_stage(store, ambient_end, position, wd, verify)? {
        return Ok(Some(value));
    }
    if position.before > ambient_end {
        let caller = SourcePosition {
            before: ambient_end,
            ..*position
        };
        if let Some(value) = visit_closed_scope(owner, &caller, wd)? {
            return Ok(Some(value));
        }
    }
    let obj_head = arguments.len() + 1;
    let type_head = obj_head + ambient.witness_obj_well_defined.len();
    for (index, proof) in ambient.witness_type_checks.iter().enumerate().rev() {
        if let Some(value) = visit_verify_stage(proof, type_head + index, position, wd, verify)? {
            return Ok(Some(value));
        }
    }
    for (index, proof) in ambient.witness_obj_well_defined.iter().enumerate().rev() {
        if position.before > obj_head + index {
            if let VerifyObjWellDefinedResult::Success(proof) = proof {
                let prior = SourcePosition {
                    before: obj_head + index,
                    ..*position
                };
                if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
    }
    if position.before > arguments.len() {
        let (fact, _, _) = witness_header(owner).expect("witness owner");
        if let FactWellDefinedProof::ExistFact(proof) = &ambient.exist_fact_well_defined {
            let prior = SourcePosition {
                before: arguments.len(),
                ..*position
            };
            if let Some(value) = visit_closed_scope(SourceOwner::ExistWD(fact, proof), &prior, wd)?
            {
                return Ok(Some(value));
            }
        }
    }
    for (index, proof) in arguments.iter().enumerate().rev() {
        if let Some(value) = visit_verify_stage(proof, index, position, wd, verify)? {
            return Ok(Some(value));
        }
    }
    Ok(None)
}

fn visit_owner<T>(
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    match position.owner {
        SourceOwner::Choice(p) => {
            for (i, o) in p.obligations.iter().enumerate().rev() {
                let stage = p.proof_steps.len() + 3 * i;
                if let Ok((formation, store)) = &o.stored {
                    if let Some(v) = visit_store_stage(store, stage + 2, position, wd, verify)? {
                        return Ok(Some(v));
                    }
                    if let Some(v) = visit_fact_stage(formation, stage + 1, position, wd, verify)? {
                        return Ok(Some(v));
                    }
                }
                if let Some(v) = visit_verify_stage(&o.verified, stage, position, wd, verify)? {
                    return Ok(Some(v));
                }
            }
            for (i, stmt) in p.proof_steps.iter().enumerate().take(position.before).rev() {
                let prior = SourcePosition {
                    before: i,
                    ..*position
                };
                if let Some(v) = visit_statement(stmt, usize::MAX, &prior, wd, verify)? {
                    return Ok(Some(v));
                }
            }
            return Ok(None);
        }

        SourceOwner::Zorn(p) => {
            for (i, o) in p.obligations.iter().enumerate().rev() {
                let stage = p.proof_steps.len() + 3 * i;
                if let Ok((formation, store)) = &o.stored {
                    if let Some(v) = visit_store_stage(store, stage + 2, position, wd, verify)? {
                        return Ok(Some(v));
                    }
                    if let Some(v) = visit_fact_stage(formation, stage + 1, position, wd, verify)? {
                        return Ok(Some(v));
                    }
                }
                if let Some(v) = visit_verify_stage(&o.verified, stage, position, wd, verify)? {
                    return Ok(Some(v));
                }
            }
            for (i, stmt) in p.proof_steps.iter().enumerate().take(position.before).rev() {
                let prior = SourcePosition {
                    before: i,
                    ..*position
                };
                if let Some(v) = visit_statement(stmt, usize::MAX, &prior, wd, verify)? {
                    return Ok(Some(v));
                }
            }
            return Ok(None);
        }

        SourceOwner::RangeExpansion(p) => {
            return visit_verify_stage(&p.membership, 0, position, wd, verify)
        }
        SourceOwner::OrSelected(p) => {
            if let Some(value) = visit_verify_stage(
                &p.selected_branch,
                2 * p.assumed_negated_branches.len(),
                position,
                wd,
                verify,
            )? {
                return Ok(Some(value));
            }
            for (i, assumed) in p.assumed_negated_branches.iter().enumerate().rev() {
                if let Some(value) =
                    visit_store_stage(&assumed.store_and_infer, 2 * i + 1, position, wd, verify)?
                {
                    return Ok(Some(value));
                }
                if let Some(value) =
                    visit_fact_stage(&assumed.well_defined, 2 * i, position, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            return Ok(None);
        }

        SourceOwner::EnumerationAssignment(fact, p) => {
            let (premises, steps, goals) = enumeration_outcome(p);
            let count = p
                .introduced_params
                .defined_params
                .store_and_infer_results
                .len();
            let head = count + p.binding_assumptions.len() + premises.len();
            for (i, goal) in goals
                .iter()
                .take(position.before.saturating_sub(head + steps.len()))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + steps.len() + i,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(&goal.verify_result, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            for (i, step) in steps
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + i,
                    ..*position
                };
                if let Some(value) = visit_statement(step, usize::MAX, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            let assumptions: Vec<_> = p.binding_assumptions.iter().chain(premises).collect();
            for (i, assumed) in assumptions
                .iter()
                .take(position.before.saturating_sub(count))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: count + i,
                    ..*position
                };
                let complete = SourcePosition {
                    before: count + i + 1,
                    ..*position
                };
                if let Some(value) =
                    visit_store_stage(&assumed.store_and_infer, count + i, &complete, wd, verify)?
                {
                    return Ok(Some(value));
                }
                if let Some(value) =
                    visit_fact_stage(&assumed.well_defined, count + i, &complete, wd, verify)?
                {
                    return Ok(Some(value));
                }
                let _ = prior;
            }
            return visit_header(
                &fact.typed_parameters.groups,
                &p.introduced_params,
                &[],
                position,
                wd,
                verify,
            );
        }

        SourceOwner::FormedSubjects(..)
        | SourceOwner::ChainObjects(..)
        | SourceOwner::PropObjects(..)
        | SourceOwner::Term
        | SourceOwner::Completion(_) => {}
        SourceOwner::ExistWD(fact, proof) => {
            return visit_header(
                &fact.typed_parameters.groups,
                &proof.introduced_params,
                &proof.assumed_body_facts,
                position,
                wd,
                verify,
            )
        }
        SourceOwner::WitnessExist(_)
        | SourceOwner::WitnessAtomic(_)
        | SourceOwner::Sketch(_)
        | SourceOwner::WitnessNonempty(_)
        | SourceOwner::Contra(_)
        | SourceOwner::Extension(_)
        | SourceOwner::FnExtension(_)
        | SourceOwner::CasesBranch(_) => return visit_local_scope(position, wd, verify),
        SourceOwner::Induction(proof) => {
            for (index, result) in proof
                .goals_wd
                .iter()
                .take(position.before.saturating_sub(2))
                .enumerate()
                .rev()
            {
                if let VerifyFactWellDefinedResult::Success(result) = result {
                    let prior = SourcePosition {
                        before: 2 + index,
                        ..*position
                    };
                    let formation =
                        SourcePosition::new(Some(&prior), SourceOwner::FactWD(result), usize::MAX);
                    if let Some(value) =
                        visit_fact_formation(result, usize::MAX, &formation, wd, verify)?
                    {
                        return Ok(Some(value));
                    }
                }
            }
            if position.before > 1 {
                let prior = SourcePosition {
                    before: 1,
                    ..*position
                };
                let formation = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FactWD(&proof.goal_domain.well_defined),
                    usize::MAX,
                );
                if let Some(value) = visit_fact_formation(
                    &proof.goal_domain.well_defined,
                    usize::MAX,
                    &formation,
                    wd,
                    verify,
                )? {
                    return Ok(Some(value));
                }
                let complete = SourcePosition {
                    before: 2,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&complete),
                    SourceOwner::PropInference(&proof.goal_domain.store_and_infer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if position.before > 0 {
                let completed = SourcePosition {
                    before: 1,
                    ..*position
                };
                for store in proof
                    .introduced_parameter
                    .defined_params
                    .store_and_infer_results
                    .iter()
                    .rev()
                {
                    let inference = SourcePosition::new(
                        Some(&completed),
                        SourceOwner::PropInference(store),
                        usize::MAX,
                    );
                    if let Some(value) = visit_owner(&inference, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
                for carrier in proof
                    .introduced_parameter
                    .param_type_well_defined
                    .iter()
                    .rev()
                {
                    if let ParamTypeWellDefinedProof::Obj(carrier) = carrier {
                        if let Some(value) = visit_complete_wd(carrier, position, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                }
            }
            // The induction header starts after the already checked lower
            // bound. Its constructors can precede parameter-type cache hits,
            // while its verification introduces no stored truth hypothesis.
            let prior = SourcePosition {
                before: 0,
                ..*position
            };
            if let Some(value) = visit_complete_verify(&proof.from_in_z, &prior, wd, verify)? {
                return Ok(Some(value));
            }
        }
        SourceOwner::InductionCase(_, proof) => {
            let head = 1 + proof.assumptions.len();
            let closed = head + proof.proof_steps.len();
            for (index, goal) in proof
                .goals_verified
                .iter()
                .take(position.before.saturating_sub(closed))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: closed + index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(goal, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            for (index, statement) in proof
                .proof_steps
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                if let Some(value) = visit_statement(statement, usize::MAX, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            for (index, assumption) in proof
                .assumptions
                .iter()
                .take(position.before.saturating_sub(1))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index + 1,
                    ..*position
                };
                let formation = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FactWD(&assumption.well_defined),
                    usize::MAX,
                );
                if let Some(value) = visit_fact_formation(
                    &assumption.well_defined,
                    usize::MAX,
                    &formation,
                    wd,
                    verify,
                )? {
                    return Ok(Some(value));
                }
                let complete = SourcePosition {
                    before: index + 2,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&complete),
                    SourceOwner::PropInference(&assumption.store_and_infer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if position.before > 0 {
                let completed = SourcePosition {
                    before: 1,
                    ..*position
                };
                for store in proof
                    .introduced_parameter
                    .defined_params
                    .store_and_infer_results
                    .iter()
                    .rev()
                {
                    let inference = SourcePosition::new(
                        Some(&completed),
                        SourceOwner::PropInference(store),
                        usize::MAX,
                    );
                    if let Some(value) = visit_owner(&inference, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
                for carrier in proof
                    .introduced_parameter
                    .param_type_well_defined
                    .iter()
                    .rev()
                {
                    if let ParamTypeWellDefinedProof::Obj(carrier) = carrier {
                        if let Some(value) = visit_complete_wd(carrier, position, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                }
            }
        }
        SourceOwner::Piecewise(p) => {
            let head = p.head_len();
            let truth = match p {
                PiecewiseEvidence::Coverage(_, proof) => Some((head, &proof.coverage_check)),
                PiecewiseEvidence::Disjoint(_, proof) => Some((head + 1, &proof.negated_component)),
                PiecewiseEvidence::Return(_, proof) => Some((head + 2, &proof.body_in_ret_set)),
            };
            if let Some((stage, checked)) = truth {
                if let Some(value) = visit_verify_stage(checked, stage, position, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if let PiecewiseEvidence::Return(_, proof) = p {
                if position.before > head + 1 {
                    if let VerifyObjWellDefinedResult::Success(checked) = &proof.body_well_defined {
                        let prior = SourcePosition {
                            before: head + 1,
                            ..*position
                        };
                        if let Some(value) = visit_complete_wd(checked, &prior, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                }
            }
            for (stage, store) in p.stores().enumerate().collect::<Vec<_>>().into_iter().rev() {
                if let Some(value) = visit_store_stage(store, stage, position, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::PiecewiseUnfold(proof) => {
            for (stage, checked) in [(1, &proof.residual_equal), (0, &proof.guard)] {
                if let Some(value) = visit_verify_stage(checked, stage, position, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::RecursiveFunction(proof) => {
            for (stage, checked) in [
                (3, &proof.measure_in_z),
                (4, &proof.lower_in_z),
                (5, &proof.measure_ge_lower),
            ]
            .into_iter()
            .rev()
            {
                if position.before > stage {
                    let prior = SourcePosition {
                        before: stage,
                        ..*position
                    };
                    if let Some(value) = visit_complete_verify(checked, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            for (stage, checked) in [
                (1, &proof.measure_well_defined),
                (2, &proof.lower_bound_well_defined),
            ]
            .into_iter()
            .rev()
            {
                if position.before > stage {
                    if let VerifyObjWellDefinedResult::Success(checked) = checked {
                        let prior = SourcePosition {
                            before: stage,
                            ..*position
                        };
                        if let Some(value) = visit_complete_wd(checked, &prior, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                }
            }
            if position.before > 0 {
                let completed = SourcePosition {
                    before: 1,
                    ..*position
                };
                for store in proof
                    .binder_introduction
                    .defined_params
                    .store_and_infer_results
                    .iter()
                    .rev()
                {
                    let inference = SourcePosition::new(
                        Some(&completed),
                        SourceOwner::PropInference(store),
                        usize::MAX,
                    );
                    if let Some(value) = visit_owner(&inference, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            if let VerifyObjWellDefinedResult::Success(signature) = &proof.fn_set_well_defined {
                let prior = SourcePosition {
                    before: 0,
                    ..*position
                };
                if let Some(value) = visit_complete_wd(signature, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::RecursiveCase(proof) => {
            if let InducCaseBodySuccess::EqualTo {
                well_defined,
                in_ret_set,
            } = &proof.body
            {
                if position.before > 2 {
                    let prior = SourcePosition {
                        before: 2,
                        ..*position
                    };
                    if let Some(value) = visit_complete_verify(in_ret_set, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
                if position.before > 1 {
                    if let VerifyObjWellDefinedResult::Success(checked) = well_defined {
                        let prior = SourcePosition {
                            before: 1,
                            ..*position
                        };
                        if let Some(value) = visit_complete_wd(checked, &prior, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                }
            }
            if position.before > 0 {
                let inference = SourcePosition::new(
                    Some(position),
                    SourceOwner::PropInference(&proof.assumption_stored),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::RecursiveDisjoint(proof) => {
            if position.before > 1 {
                let prior = SourcePosition {
                    before: 1,
                    ..*position
                };
                if let Some(value) =
                    visit_complete_verify(&proof.negated_component, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            if position.before > 0 {
                let inference = SourcePosition::new(
                    Some(position),
                    SourceOwner::PropInference(&proof.assumption_stored),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::RecursiveUnfold(proof) => {
            if position.before > proof.selected_case_path.len() {
                let prior = SourcePosition {
                    before: proof.selected_case_path.len(),
                    ..*position
                };
                if let Some(value) =
                    visit_complete_verify(&proof.residual_equal, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            for (index, selected) in proof
                .selected_case_path
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(&selected.guard, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::InferredStore(store) => {
            return wd(SourceConstructor::Inferred(store), position)
        }

        SourceOwner::Run(run) => {
            for (index, statement) in run
                .statement_results
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition::new(None, SourceOwner::Run(run), index);
                if let Some(value) = visit_statement(statement, usize::MAX, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::Statement(statement) => {
            if let Some(parent) = position.parent {
                return visit_statement(statement, position.before, parent, wd, verify);
            }
        }
        SourceOwner::Verify(proof) => {
            return visit_verify_formation(proof, position.before, position, wd, verify)
        }
        SourceOwner::AtomicVerify(proof) => {
            return visit_atomic_verify_formation(proof, position.before, position, wd, verify)
        }
        owner @ (SourceOwner::FunctionDomainWD(_) | SourceOwner::CompleteDomainSource(_)) => {
            let mut stages = Vec::new();
            match owner {
                SourceOwner::FunctionDomainWD(domain) => {
                    function_domain_search_stages(domain, &mut stages)
                }
                SourceOwner::CompleteDomainSource(domain) => {
                    complete_domain_source_stages(domain, &mut stages)
                }
                _ => unreachable!(),
            }
            for (index, child) in stages
                .into_iter()
                .take(position.before)
                .enumerate()
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                let found = match child {
                    AtomicSearchStage::WD(proof) => visit_complete_wd(proof, &prior, wd, verify)?,
                    AtomicSearchStage::Verify(proof) => {
                        visit_complete_verify(proof, &prior, wd, verify)?
                    }
                    AtomicSearchStage::Atomic(_) => unreachable!("function domain stages"),
                };
                if let Some(value) = found {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::WD(proof) | SourceOwner::WDLocals(proof, _) => {
            if let Some(value) = visit_function_formation(proof, position, wd, verify)? {
                return Ok(Some(value));
            }
            if let ObjWellDefinedProof::ByDef {
                obj: Obj::SetFormer(SetFormer::SetBuilder(set)),
                proof:
                    ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(
                        captured,
                    )),
            } = proof
            {
                let scope = SourcePosition::new(
                    Some(position),
                    SourceOwner::SetBuilder(set, captured),
                    position.before,
                );
                let mut closed = |evidence: SourceConstructor<'_>,
                                  position: &SourcePosition<'_>| {
                    if constructor_has_closed_leaf(evidence) {
                        wd(evidence, position)
                    } else {
                        Ok(None)
                    }
                };
                if let Some(value) = visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))? {
                    return Ok(Some(value));
                }
            }
            if let ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FunctionSpace(p),
                ..
            } = proof
            {
                let construction = match p {
                    FunctionSpaceObjWellDefinedProofByDef::Preimage(p) => {
                        Some((&p.construction, 2 + p.requirement_fact_verified.len()))
                    }
                    FunctionSpaceObjWellDefinedProofByDef::PreimageSet(p) => {
                        Some((&p.construction, 2 + p.requirement_fact_verified.len()))
                    }
                    _ => None,
                };
                if let Some((p, index)) = construction {
                    if position.before > index {
                        let prior = SourcePosition {
                            before: index,
                            ..*position
                        };
                        if let Some(value) =
                            visit_complete_wd(&p.builder_well_defined, &prior, wd, verify)?
                        {
                            return Ok(Some(value));
                        }
                    }
                }
            }
            if let ObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::FunctionSpace(
                        FunctionSpaceObjWellDefinedProofByDef::Composition(p),
                    ),
                ..
            } = proof
            {
                for (i, child) in [
                    &p.outer_well_defined,
                    &p.inner_well_defined,
                    &p.function_well_defined,
                ]
                .into_iter()
                .enumerate()
                .rev()
                {
                    if position.before > i {
                        let prior = SourcePosition {
                            before: i,
                            ..*position
                        };
                        if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                }
            }
            if let Some((children, requirements)) = arithmetic_stages(proof) {
                for (index, requirement) in requirements
                    .iter()
                    .take(position.before.saturating_sub(children.len()))
                    .enumerate()
                    .rev()
                {
                    let prior = SourcePosition {
                        before: children.len() + index,
                        ..*position
                    };
                    if let Some(value) = visit_complete_verify(requirement, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
                for (index, child) in children.iter().take(position.before).enumerate().rev() {
                    let prior = SourcePosition {
                        before: index + 1,
                        ..*position
                    };
                    if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            if let ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(p),
                ..
            } = proof
            {
                if let Some(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence::Composition(c)) = &p.domain_fn_set {
                    if let crate::execute::execute_fact_stmt::function_composition::CompositionWellDefinedPremise::Checked(root) = &c.well_defined {
                        if let Some(parent) = position.parent {
                            if let Some(value) = visit_complete_wd(root, parent, wd, verify)? {return Ok(Some(value));}
                        }
                    }
                }
            }
        }
        SourceOwner::AtomicWD(proof) | SourceOwner::AtomicWDLocals(proof, _) => {
            return visit_atomic_formation(proof, position.before, position, wd, verify)
        }
        SourceOwner::EqualWDLocals(proof, _) => {
            for (index, child) in [&proof.left, &proof.right]
                .into_iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index + 1,
                    ..*position
                };
                if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::FactWD(proof) => {
            return visit_fact_formation(proof, position.before, position, wd, verify)
        }
        SourceOwner::EmptyForall(proof) => {
            if position.before > 0 {
                let prior = SourcePosition {
                    before: 0,
                    ..*position
                };
                if let Some(value) =
                    visit_complete_verify(&proof.empty_carrier_proof, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::Forall(proof) => {
            let head = parameter_count(&proof.fact.typed_parameters.groups)
                + proof.assumed_dom_facts.len();
            for (index, then) in proof
                .proved_then_facts
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let complete = SourcePosition {
                    before: head + index + 1,
                    ..*position
                };
                let boundary =
                    SourcePosition::new(position.parent, SourceOwner::Completion(&complete), 0);
                let prior = SourcePosition {
                    parent: Some(&boundary),
                    before: head + index,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&complete),
                    SourceOwner::PropInference(&then.store_and_infer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
                if let Some(value) = visit_stored_verify(
                    &then.verify_result,
                    &then.store_and_infer,
                    &prior,
                    wd,
                    verify,
                )? {
                    return Ok(Some(value));
                }
            }
            return visit_header(
                &proof.fact.typed_parameters.groups,
                &proof.introduced_params,
                &proof.assumed_dom_facts,
                position,
                wd,
                verify,
            );
        }
        SourceOwner::ForallIffWD(fact, proof) => {
            // Both sides are formed under the common domain only. No side is
            // a truth assumption while forming the opposite side.
            return visit_header(
                &fact.forall_fact.typed_parameters.groups,
                &proof.introduced_params,
                &proof.assumed_dom_facts,
                position,
                wd,
                verify,
            );
        }
        SourceOwner::ForallWD(fact, proof) => {
            let head =
                parameter_count(&fact.typed_parameters.groups) + proof.assumed_dom_facts.len();
            for (index, then) in proof
                .then
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::FactWD(then), usize::MAX);
                if let Some(value) = visit_fact_formation(then, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            return visit_header(
                &fact.typed_parameters.groups,
                &proof.introduced_params,
                &proof.assumed_dom_facts,
                position,
                wd,
                verify,
            );
        }
        SourceOwner::NotForallWD(fact, proof) => {
            let head =
                parameter_count(&fact.typed_parameters.groups) + proof.assumed_dom_facts.len();
            for (index, then) in proof
                .then
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::FactWD(then), usize::MAX);
                if let Some(value) = visit_fact_formation(then, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            return visit_header(
                &fact.typed_parameters.groups,
                &proof.introduced_params,
                &proof.assumed_dom_facts,
                position,
                wd,
                verify,
            );
        }
        SourceOwner::KnownForall(proof) => {
            let head = parameter_count(&proof.fact.typed_parameters.groups)
                + proof.well_defined.assumed_dom_facts.len();
            for (index, then) in proof
                .well_defined
                .then
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::FactWD(then), usize::MAX);
                if let Some(value) = visit_fact_formation(then, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            return visit_header(
                &proof.fact.typed_parameters.groups,
                &proof.well_defined.introduced_params,
                &proof.well_defined.assumed_dom_facts,
                position,
                wd,
                verify,
            );
        }
        SourceOwner::Named(proof) => {
            let (steps, head) = named_steps(proof);
            for (index, statement) in steps
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                if let Some(value) = visit_statement(statement, usize::MAX, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if let (Fact::ForallFact(fact), ExecDefThmBodyProof::Forall(body)) =
                (&proof.statement.fact, &proof.body)
            {
                return visit_header(
                    &fact.typed_parameters.groups,
                    &body.introduced_params,
                    &body.assumed_dom_facts,
                    position,
                    wd,
                    verify,
                );
            }
        }
        SourceOwner::Claim(proof) => {
            let (steps, head) = claim_steps(proof);
            for (index, statement) in steps
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                if let Some(value) = visit_statement(statement, usize::MAX, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if let (Fact::ForallFact(fact), ExecClaimBodyProof::Forall(body)) =
                (&proof.statement.fact, &proof.body)
            {
                return visit_header(
                    &fact.typed_parameters.groups,
                    &body.introduced_params,
                    &body.assumed_dom_facts,
                    position,
                    wd,
                    verify,
                );
            }
        }
        SourceOwner::Call(proof) => {
            let head = proof.type_proofs.len() + proof.dom_proofs.len();
            let return_head = head + proof.conclusions_wd.len();
            for (index, store) in proof
                .returned_conclusions
                .iter()
                .take(position.before.saturating_sub(return_head))
                .enumerate()
                .rev()
            {
                let published = SourcePosition {
                    before: return_head + index + 1,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&published),
                    SourceOwner::PropInference(store),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            for (index, conclusion) in proof
                .conclusions_wd
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::FactWD(conclusion), usize::MAX);
                if let Some(value) =
                    visit_fact_formation(conclusion, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            for (index, store) in proof
                .dom_stores
                .iter()
                .take(position.before.saturating_sub(proof.type_proofs.len()))
                .enumerate()
                .rev()
            {
                let published = SourcePosition {
                    before: proof.type_proofs.len() + index + 1,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&published),
                    SourceOwner::PropInference(store),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            for (index, store) in proof
                .type_stores
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let published = SourcePosition {
                    before: index + 1,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&published),
                    SourceOwner::PropInference(store),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            let completed = position
                .before
                .min(proof.type_proofs.len() + proof.dom_proofs.len());
            for index in (0..completed).rev() {
                let proof = if index < proof.type_proofs.len() {
                    &proof.type_proofs[index]
                } else {
                    &proof.dom_proofs[index - proof.type_proofs.len()]
                };
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::ThmRelease(proof) => {
            let head = proof.type_proofs.len() + proof.dom_proofs.len();
            for (index, conclusion) in proof
                .conclusions_wd
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::FactWD(conclusion), usize::MAX);
                if let Some(value) =
                    visit_fact_formation(conclusion, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            for (index, store) in proof
                .type_stores
                .iter()
                .enumerate()
                .chain(
                    proof
                        .dom_stores
                        .iter()
                        .enumerate()
                        .map(|(i, store)| (proof.type_proofs.len() + i, store)),
                )
                .take(position.before.min(head))
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
            {
                let published = SourcePosition {
                    before: index + 1,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&published),
                    SourceOwner::PropInference(store),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            let completed = position.before.min(head);
            for index in (0..completed).rev() {
                let proof = if index < proof.type_proofs.len() {
                    &proof.type_proofs[index]
                } else {
                    &proof.dom_proofs[index - proof.type_proofs.len()]
                };
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::HaveEqualType(p) => {
            return visit_header(
                &p.statement.param_def.groups,
                &p.type_preflight,
                &[],
                position,
                wd,
                verify,
            );
        }
        SourceOwner::HaveGroup(carrier, nonempty) => {
            if position.before > 1 {
                if let ParamTypeFactCheckResult::Obj(proof) = nonempty {
                    let prior = SourcePosition {
                        before: 1,
                        ..*position
                    };
                    if let Some(value) = visit_complete_verify(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            if position.before > 0 {
                if let ParamTypeWellDefinedProof::Obj(proof) = carrier {
                    let prior = SourcePosition {
                        before: 0,
                        ..*position
                    };
                    if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
        }
        SourceOwner::ParamTypeWD(carrier) => {
            if position.before > 0 {
                if let ParamTypeWellDefinedProof::Obj(proof) = carrier {
                    let prior = SourcePosition {
                        before: 0,
                        ..*position
                    };
                    if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
        }
        SourceOwner::SetBuilder(_, proof) => {
            for (i, assumed) in proof
                .assumed_facts
                .iter()
                .take(position.before.saturating_sub(2))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: 2 + i,
                    ..*position
                };
                let inferred = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::PropInference(&assumed.store_and_infer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inferred, wd, verify)? {
                    return Ok(Some(value));
                }
                let formation = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FactWD(&assumed.well_defined),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&formation, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            for (index, store) in proof
                .defined_params
                .store_and_infer_results
                .iter()
                .take(position.before.saturating_sub(1))
                .enumerate()
                .rev()
            {
                let published = SourcePosition {
                    before: index + 2,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&published),
                    SourceOwner::PropInference(store),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if position.before > 0 {
                let prior = SourcePosition {
                    before: 0,
                    ..*position
                };
                if let Some(value) =
                    visit_complete_wd(&proof.param_set_well_defined, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::StructLayers(layers) => {
            for (index, layer) in layers.iter().take(position.before).enumerate().rev() {
                let published = SourcePosition {
                    before: index + 1,
                    ..*position
                };
                let scope = SourcePosition::new(
                    Some(&published),
                    SourceOwner::StructLayer(layer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&scope, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::StructLayer(layer) => {
            for (index, store) in layer
                .store_and_infer
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::PropInference(store),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
                if let Some(value) = wd(
                    SourceConstructor::Inferred(&store.store),
                    &SourcePosition {
                        before: index + 1,
                        ..prior
                    },
                )? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::Template(proof) => {
            let head = proof.statement.template_arg_def.ordered_param_ids().len()
                + proof.assumed_dom_facts.len();
            if position.before > head {
                let prior = SourcePosition {
                    before: head,
                    ..*position
                };
                if let Some(value) = visit_statement(&proof.body, usize::MAX, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            return visit_header(
                &proof.statement.template_arg_def.groups,
                &proof.introduced_params,
                &proof.assumed_dom_facts,
                position,
                wd,
                verify,
            );
        }
        SourceOwner::StructHeader(proof) => {
            if let (Some((parameters, _)), Some(introduced)) = (
                &proof.statement.param_def_with_dom,
                &proof.introduced_params,
            ) {
                let count = parameters.ordered_param_ids().len();
                for (index, domain) in proof
                    .structure_domains
                    .iter()
                    .take(position.before.saturating_sub(count))
                    .enumerate()
                    .rev()
                {
                    let prior = SourcePosition {
                        before: count + index,
                        ..*position
                    };
                    let formed =
                        SourcePosition::new(Some(&prior), SourceOwner::FactWD(domain), usize::MAX);
                    if let Some(value) =
                        visit_fact_formation(domain, usize::MAX, &formed, wd, verify)?
                    {
                        return Ok(Some(value));
                    }
                }
                return visit_header(&parameters.groups, introduced, &[], position, wd, verify);
            }
        }
        SourceOwner::StructFields(proof) => {
            let n = proof.statement.fields.len();
            for (index, stage) in proof
                .field_scope
                .equivalent_facts
                .iter()
                .take(position.before.saturating_sub(n))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: n + index,
                    ..*position
                };
                let formation = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FactWD(&stage.well_defined),
                    usize::MAX,
                );
                if let Some(value) =
                    visit_fact_formation(&stage.well_defined, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            for (index, stage) in proof
                .field_scope
                .fields
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                let introduced = SourcePosition {
                    before: index + 1,
                    ..prior
                };
                for store in stage.defined.store_and_infer_results.iter().rev() {
                    let inference = SourcePosition::new(
                        Some(&introduced),
                        SourceOwner::PropInference(store),
                        usize::MAX,
                    );
                    if let Some(value) = visit_owner(&inference, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
                if let Some(value) = visit_complete_wd(&stage.well_defined, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::PropDefinition(proof) => {
            let count = parameter_count(&proof.statement.typed_parameters.groups);
            for (index, assumed) in proof
                .assumed_iff_facts
                .iter()
                .take(position.before.saturating_sub(count))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: count + index,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::PropInference(&assumed.store_and_infer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
                let formation = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FactWD(&assumed.well_defined),
                    usize::MAX,
                );
                if let Some(value) =
                    visit_fact_formation(&assumed.well_defined, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            for (index, store) in proof
                .defined_params
                .store_and_infer_results
                .iter()
                .take(position.before.min(count))
                .enumerate()
                .rev()
            {
                let published = SourcePosition {
                    before: index + 1,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&published),
                    SourceOwner::PropInference(store),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            let mut offset = 0;
            for (group, carrier) in proof
                .statement
                .typed_parameters
                .groups
                .iter()
                .zip(&proof.param_type_well_defined)
            {
                if offset < position.before {
                    if let ParamTypeWellDefinedProof::Obj(carrier) = carrier {
                        let prior = SourcePosition {
                            before: offset,
                            ..*position
                        };
                        if let Some(value) = visit_complete_wd(carrier, &prior, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                }
                offset += group.params.len();
            }
        }
        SourceOwner::ByDef(proof) => {
            if position.before > 1 {
                let prior = SourcePosition {
                    before: 1,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(&proof.proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if position.before > 0 {
                if let VerifyFactWellDefinedResult::Success(goal) = &proof.goal_wd {
                    let prior = SourcePosition {
                        before: 0,
                        ..*position
                    };
                    let formation =
                        SourcePosition::new(Some(&prior), SourceOwner::FactWD(goal), usize::MAX);
                    return visit_fact_formation(goal, usize::MAX, &formation, wd, verify);
                }
            }
        }
        SourceOwner::PropRequirements(proof) => {
            for (index, child) in proof
                .proof_of_requirement_facts
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(child, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::AtomicInference(_, infer) => {
            if let InferAtomicFactResult::EqualFact(rules) = infer {
                let group = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityInferences(rules),
                    position.before,
                );
                return visit_owner(&group, wd, verify);
            }
            for (index, captured) in atomic_inference_stages(infer)
                .into_iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    // This visitor reopens an already completed capture. Its
                    // availability follows the original formation/publication
                    // stage; the consumer validates WD at `index` beforehand.
                    before: index + 1,
                    ..*position
                };

                if let Some(value) = wd(SourceConstructor::Inferred(&captured.store), &prior)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::CompoundInference(store) => {
            return visit_compound_inference(store, position, wd, verify)
        }
        SourceOwner::OrderBoundInference(rule) => {
            let (checks, captured) = order_bound_stages(rule).expect("conditional order owner");
            let head = checks.len();

            if position.before > head {
                let prior = SourcePosition {
                    before: head + 1,
                    ..*position
                };
                if let Some(value) = wd(SourceConstructor::Inferred(&captured.store), &prior)? {
                    return Ok(Some(value));
                }
            }
            for (index, checked) in checks
                .into_iter()
                .take(position.before.min(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(checked, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::ChainClosure(closure) => {
            if position.before > 0 {
                if let Some(value) = wd(
                    SourceConstructor::Inferred(&closure.derived.store),
                    position,
                )? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::PropInference(store) => {
            if matches!(
                &store.infer,
                Some(InferResult::AndFact(_)) | Some(InferResult::ChainFact(_))
            ) {
                let group = SourcePosition::new(
                    Some(position),
                    SourceOwner::CompoundInference(store),
                    position.before,
                );
                return visit_owner(&group, wd, verify);
            }
            if let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
                &store.infer
            {
                let group = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityInferences(rules),
                    position.before,
                );
                return visit_owner(&group, wd, verify);
            }
            for (index, derived) in prop_inference_stages(store)
                .into_iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    // Tag completed evidence with its completed prefix, so an
                    // active cursor at `index` cannot recover this full WD by
                    // reopening an enclosing finished owner.
                    before: index + 1,
                    ..*position
                };

                if let Some(value) = wd(SourceConstructor::Inferred(&derived.store), &prior)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::EqualityInferences(rules) => {
            for (index, rule) in rules.iter().take(position.before).enumerate().rev() {
                if let InferEqualFactResult::PositiveRealPower(rule) = rule {
                    let prior = SourcePosition {
                        before: index + 1,
                        ..*position
                    };
                    let complete = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::PositivePowerInferences(rule),
                        rule.transports.len(),
                    );
                    if let Some(value) = visit_owner(&complete, wd, verify)? {
                        return Ok(Some(value));
                    }
                    continue;
                }
                if let Some(owner) = equality_cancellation_owner(rule) {
                    let (checks, _) = cancellation_stages(owner).expect("cancellation owner");
                    let prior = SourcePosition {
                        before: index + 1,
                        ..*position
                    };
                    let complete = SourcePosition::new(Some(&prior), owner, checks.len() + 2);
                    if let Some(value) = visit_owner(&complete, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
        }
        SourceOwner::PositivePowerInferences(rule) => {
            for (index, transport) in rule
                .transports
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index + 1,
                    ..*position
                };
                let complete = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::PositivePowerTransport(transport),
                    3,
                );
                if let Some(value) = visit_owner(&complete, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::PositivePowerTransport(transport) => {
            if position.before > 2 {
                let prior = SourcePosition {
                    before: 3,
                    ..*position
                };
                if let Some(value) = wd(
                    SourceConstructor::Inferred(&transport.derived.store),
                    &prior,
                )? {
                    return Ok(Some(value));
                }
            }
            let positivity = match &transport.positivity {
                InferPositiveRealPowerPositivityResult::PowerPositive(proof)
                | InferPositiveRealPowerPositivityResult::BasePositive(proof) => proof,
            };
            for (index, proof) in [positivity, &transport.exponent_real]
                .into_iter()
                .take(position.before.min(2))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        owner @ (SourceOwner::AdditiveInference(_)
        | SourceOwner::SubtractiveInference(_)
        | SourceOwner::NonzeroFactorInference(_)
        | SourceOwner::CommonDenominatorInference(_)
        | SourceOwner::NonzeroNumeratorInference(_)) => {
            let (checks, captured) = cancellation_stages(owner).expect("cancellation owner");
            let head = checks.len();

            if position.before > head {
                let prior = SourcePosition {
                    before: head + 1,
                    ..*position
                };
                if let Some(value) = wd(SourceConstructor::Inferred(&captured.store), &prior)? {
                    return Ok(Some(value));
                }
            }
            for (index, proof) in checks
                .into_iter()
                .take(position.before.min(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::AtomicFnUnfold(proof) => {
            if position.before > proof.unfold_equal_proofs.len() {
                let prior = SourcePosition {
                    before: proof.unfold_equal_proofs.len(),
                    ..*position
                };
                if let Some(value) =
                    visit_complete_verify(&proof.proof_of_rewritten_fact, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            for (index, checked) in proof
                .unfold_equal_proofs
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(checked, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::KnownApplication(proof) => {
            let requirements = known_application_requirements(proof);
            let completed = position.before.saturating_sub(proof.arg_match_proofs.len());
            for (index, (_, checked)) in requirements.iter().take(completed).enumerate().rev() {
                let prior = SourcePosition {
                    before: proof.arg_match_proofs.len() + index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(checked, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            // Matching has no constructor capture of its own. These are only
            // the formation certificates already returned by the selected
            // application's original type/domain checks; no pending truth
            // producer or replacement verification is exposed here.
            for (_, checked) in requirements.into_iter().rev() {
                let formation =
                    SourcePosition::new(Some(position), SourceOwner::Verify(checked), usize::MAX);
                if let Some(value) =
                    visit_verify_formation(checked, usize::MAX, &formation, wd, &mut |_, _| {
                        Ok(None)
                    })?
                {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::CalleeInstance(_) => {}
        SourceOwner::EqualityRequirements(proofs) => {
            for (index, proof) in proofs.iter().take(position.before).enumerate().rev() {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(proof, &prior, wd, &mut |_, _| Ok(None))?
                {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::FunctionNormalization(proof) => {
            for (index, step) in proof
                .expansions
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                if let Some(owner) = match step {
                    FunctionBodyExpansionProof::Anonymous(step) => {
                        Some(SourceOwner::FunctionExpansion(step))
                    }
                    FunctionBodyExpansionProof::FiniteCoordinate(step) => {
                        Some(SourceOwner::FiniteExpansion(step))
                    }
                    FunctionBodyExpansionProof::Composition(step) => {
                        Some(SourceOwner::CompositionExpansion(step))
                    }
                } {
                    let prior = SourcePosition {
                        before: index,
                        ..*position
                    };
                    let expansion = SourcePosition::new(Some(&prior), owner, usize::MAX);
                    if let Some(value) = visit_owner(&expansion, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
        }
        SourceOwner::FunctionDefinitionRewrite(steps) => {
            for (index, step) in steps.iter().take(position.before).enumerate().rev() {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                let expansion = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FunctionExpansion(step),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&expansion, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::CompositionExpansion(proof) => {
            if position.before > 0 {
                let prior = SourcePosition {
                    before: 0,
                    ..*position
                };
                return visit_complete_wd(&proof.application_well_defined, &prior, wd, verify);
            }
        }
        SourceOwner::FiniteExpansion(proof) => {
            if position.before > 0 {
                let prior = SourcePosition {
                    before: 0,
                    ..*position
                };
                return visit_complete_wd(&proof.application_well_defined, &prior, wd, verify);
            }
        }
        SourceOwner::FunctionExpansion(proof) => {
            if position.before > 2 {
                let prior = SourcePosition {
                    before: 2,
                    ..*position
                };
                if let Some(value) =
                    visit_complete_wd(&proof.body_application_well_defined, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            if position.before > 0 {
                let prior = SourcePosition {
                    before: 0,
                    ..*position
                };
                if let Some(value) =
                    visit_complete_wd(&proof.application_well_defined, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
        }
    }
    Ok(None)
}

fn visit_header<T>(
    groups: &[TypedParameterGroup],
    introduced: &IntroduceTypedParametersResult,
    doms: &[AssumeDomFactResult],
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let count = parameter_count(groups);
    if position.before >= count {
        let scope = SourcePosition::new(
            Some(position),
            SourceOwner::StructLayers(
                introduced
                    .auto_opened_struct_layers
                    .as_deref()
                    .unwrap_or(&[]),
            ),
            usize::MAX,
        );
        if let Some(value) = visit_owner(&scope, wd, verify)? {
            return Ok(Some(value));
        }
    }

    for (index, dom) in doms
        .iter()
        .take(position.before.saturating_sub(count))
        .enumerate()
        .rev()
    {
        let prior = SourcePosition {
            before: count + index,
            ..*position
        };
        let inference = SourcePosition::new(
            Some(&prior),
            SourceOwner::PropInference(&dom.store_and_infer),
            usize::MAX,
        );
        if let Some(value) = visit_owner(&inference, wd, verify)? {
            return Ok(Some(value));
        }
        let formation = SourcePosition::new(
            Some(&prior),
            SourceOwner::FactWD(&dom.well_defined),
            usize::MAX,
        );
        if let (StoreFactResult::NotForallFact(fact), FactWellDefinedProof::NotForall(proof)) =
            (&dom.store_and_infer.store, &dom.well_defined)
        {
            if let Some(value) =
                visit_not_forall_outer_carrier(&fact.fact, proof, &prior, wd, verify)?
            {
                return Ok(Some(value));
            }
        }
        if let Some(value) =
            visit_fact_formation(&dom.well_defined, usize::MAX, &formation, wd, verify)?
        {
            return Ok(Some(value));
        }
    }
    for (index, store) in introduced
        .defined_params
        .store_and_infer_results
        .iter()
        .take(position.before)
        .enumerate()
        .rev()
    {
        let prior = SourcePosition {
            before: index + 1,
            ..*position
        };
        let inference =
            SourcePosition::new(Some(&prior), SourceOwner::PropInference(store), usize::MAX);
        if let Some(value) = visit_owner(&inference, wd, verify)? {
            return Ok(Some(value));
        }
    }
    let mut offset = 0;
    for (group, proof) in groups.iter().zip(&introduced.param_type_well_defined) {
        let end = offset + group.params.len();
        if offset < position.before {
            if let ParamTypeWellDefinedProof::Obj(proof) = proof {
                let prior = SourcePosition {
                    before: offset,
                    ..*position
                };
                if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        offset = end;
    }
    Ok(None)
}

fn visit_statement<T>(
    statement: &ExecStmtResult,
    before: usize,
    parent: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    // Historical statement traversal requires its enclosing scope to have
    // completed this statement. Keep that boundary while callbacks replay
    // the original pre-statement fact prefix.
    let completion;
    let boundary;
    let parent = if before == usize::MAX {
        completion = SourcePosition {
            before: parent.before.saturating_add(1),
            ..*parent
        };
        boundary = SourcePosition::new(Some(parent), SourceOwner::Completion(&completion), 0);
        &boundary
    } else {
        parent
    };
    let position = SourcePosition::new(Some(parent), SourceOwner::Statement(statement), 0);
    let completed = SourcePosition { before, ..position };
    if let Some(p) = super::compile_release_choice_result::choice_statement(statement) {
        if let Some(v) = visit_store_stage(&p.stored, 3, &completed, wd, verify)? {
            return Ok(Some(v));
        }
        if let Some(v) = visit_fact_stage(&p.stored_wd, 2, &completed, wd, verify)? {
            return Ok(Some(v));
        }
        // The proof block closes before publication. Its local facts cannot escape.
        if before > 0 {
            if let VerifyObjWellDefinedResult::Success(proof) = &p.family_wd {
                if let Some(v) = visit_complete_wd(proof, &position, wd, verify)? {
                    return Ok(Some(v));
                }
            }
        }
        return Ok(None);
    }
    if let Some(p) = super::compile_release_zorn_result::zorn_statement(statement) {
        if let Some(v) = visit_store_stage(&p.stored, 3, &completed, wd, verify)? {
            return Ok(Some(v));
        }
        if let Some(v) = visit_fact_stage(&p.stored_wd, 2, &completed, wd, verify)? {
            return Ok(Some(v));
        }
        // The proof block closes before publication. Its local facts cannot escape.
        if before > 0 {
            if let VerifyObjWellDefinedResult::Success(proof) = &p.set_wd {
                if let Some(v) = visit_complete_wd(proof, &position, wd, verify)? {
                    return Ok(Some(v));
                }
            }
        }
        return Ok(None);
    }
    if let Some(p) = super::compile_release_regularity_result::regularity_statement(statement) {
        if let Some(value) = visit_store_stage(&p.stored, 3, &completed, wd, verify)? {
            return Ok(Some(value));
        }
        if before > 2 {
            let prior = SourcePosition {
                before: 2,
                ..position
            };
            let formation =
                SourcePosition::new(Some(&prior), SourceOwner::FactWD(&p.stored_wd), usize::MAX);
            if let Some(value) =
                visit_fact_formation(&p.stored_wd, usize::MAX, &formation, wd, verify)?
            {
                return Ok(Some(value));
            }
        }
        if before > 1 {
            let prior = SourcePosition {
                before: 1,
                ..position
            };
            if let Some(value) = visit_complete_verify(&p.nonempty, &prior, wd, verify)? {
                return Ok(Some(value));
            }
        }
        if before > 0 {
            if let VerifyObjWellDefinedResult::Success(proof) = &p.set_wd {
                if let Some(value) = visit_complete_wd(proof, &position, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        return Ok(None);
    }
    if let Some(p) = super::compile_replacement_result::replacement_statement(statement) {
        for (stage, store) in p
            .defined_params
            .store_and_infer_results
            .iter()
            .map(|s| s.as_ref())
            .chain([&p.introduction, &p.elimination])
            .enumerate()
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
        {
            if let Some(value) = visit_store_stage(store, 1 + stage, &completed, wd, verify)? {
                return Ok(Some(value));
            }
        }
        if before > 0 {
            if let VerifyObjWellDefinedResult::Success(proof) = &p.source_wd {
                if let Some(value) = visit_complete_wd(proof, &position, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        return Ok(None);
    }
    let assumptions = super::compile_assumption_stmt_result::assumption_stages(statement);
    for (index, (_, formation, store)) in assumptions.iter().enumerate().rev() {
        if let Some(value) = visit_store_stage(
            store,
            assumption_start(statement) + assumptions.len() + index,
            &completed,
            wd,
            verify,
        )? {
            return Ok(Some(value));
        }
        if before > assumption_start(statement) + index {
            let prior = SourcePosition {
                before: assumption_start(statement) + index,
                ..position
            };
            let formed =
                SourcePosition::new(Some(&prior), SourceOwner::FactWD(formation), usize::MAX);
            if let Some(value) = visit_fact_formation(formation, usize::MAX, &formed, wd, verify)? {
                return Ok(Some(value));
            }
        }
    }
    if let Some(p) = trust_have(statement) {
        let count = parameter_count(&p.statement.param_def.groups);
        if before > count {
            let scope = SourcePosition::new(
                Some(&completed),
                SourceOwner::StructLayers(p.auto_opened_struct_layers.as_deref().unwrap_or(&[])),
                usize::MAX,
            );
            if let Some(value) = visit_owner(&scope, wd, verify)? {
                return Ok(Some(value));
            }
        }
        for (i, store) in p
            .defined_param_store_and_infer
            .store_and_infer_results
            .iter()
            .take(before)
            .enumerate()
            .rev()
        {
            let prior = SourcePosition {
                before: i + 1,
                ..position
            };
            let scope =
                SourcePosition::new(Some(&prior), SourceOwner::PropInference(store), usize::MAX);
            if let Some(value) = visit_owner(&scope, wd, verify)? {
                return Ok(Some(value));
            }
        }
        let mut offset = 0;
        for (group, captured) in p
            .statement
            .param_def
            .groups
            .iter()
            .zip(&p.param_type_well_defined)
        {
            if offset < before {
                let prior = SourcePosition {
                    before: offset,
                    ..position
                };
                let scope =
                    SourcePosition::new(Some(&prior), SourceOwner::ParamTypeWD(captured), 1);
                if let Some(value) = visit_owner(&scope, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            offset += group.params.len();
        }
        return Ok(None);
    }
    if let Some(proof) = nonempty_witness_statement(statement) {
        if let Some(value) =
            visit_store_stage(&proof.store_and_infer_result, 2, &completed, wd, verify)?
        {
            return Ok(Some(value));
        }
        if before > 2 {
            let caller = SourcePosition {
                before: 2,
                ..completed
            };
            if let Some(value) =
                visit_closed_scope(SourceOwner::WitnessNonempty(proof), &caller, wd)?
            {
                return Ok(Some(value));
            }
        }
        for (index, result) in [&proof.obj_well_defined, &proof.set_well_defined]
            .into_iter()
            .enumerate()
            .rev()
        {
            if before > index {
                if let VerifyObjWellDefinedResult::Success(proof) = result {
                    let prior = SourcePosition {
                        before: index,
                        ..completed
                    };
                    if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
        }
        return Ok(None);
    }
    if let Some((ambient, arguments, owner, store)) = witness_statement(statement) {
        return visit_witness_statement(ambient, arguments, owner, store, &completed, wd, verify);
    }
    if let Some((_, stores)) = obtain_parts(statement) {
        for (index, store) in stores.store_and_infer_results.iter().enumerate().rev() {
            if let Some(value) = visit_store_stage(store, 1 + index, &completed, wd, verify)? {
                return Ok(Some(value));
            }
        }
        if before == 0 {
            return Ok(None);
        }
        return match statement {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::ObtainObjFromExistFact(
                    ExecObtainObjFromExistFactStmtResult::Success(p),
                ),
            )) => {
                let (fact, proof) = match &p.verify_exist {
                    ObtainExistVerifySuccess::Exist(p) => (p.fact.plain(), &p.well_defined_proof),
                    ObtainExistVerifySuccess::ExistUnique(p) => {
                        (p.fact.plain(), &p.well_defined_proof)
                    }
                };
                visit_closed_scope(SourceOwner::ExistWD(fact, proof), &position, wd)
            }
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                    ExecObtainObjFromAtomicFactStmtResult::Success(p),
                ),
            )) => visit_complete_verify(&p.verify_atomic, &position, wd, verify),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjByExistFacts(
                    ExecHaveObjByExistFactsStmtResult::Success(p),
                ),
            )) => visit_closed_scope(
                SourceOwner::ExistWD(
                    p.verify_exist.fact.plain(),
                    &p.verify_exist.well_defined_proof,
                ),
                &position,
                wd,
            ),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveByFnPreimage(
                    crate::execute::ExecHaveByFnPreimageStmtResult::Success(p),
                ),
            )) => visit_complete_verify(&p.source_membership, &position, wd, verify),
            _ => unreachable!("obtain statement"),
        };
    }
    if let Some((goal, _, store)) = enumeration_statement(statement) {
        if let Some(value) = visit_store_stage(store, 1, &completed, wd, verify)? {
            return Ok(Some(value));
        }
        if let VerifyFactWellDefinedResult::Success(goal) = goal {
            return visit_fact_stage(goal, 0, &completed, wd, verify);
        }
        return Ok(None);
    }
    match statement {
        ExecStmtResult::By(ExecByStmtResult::Extension(
            crate::execute::execute_by_stmt::ExecByExtensionStmtResult::Success(p),
        )) => {
            if let Some(value) = visit_store_stage(&p.stored, 2, &completed, wd, verify)? {
                return Ok(Some(value));
            }
            if before > 1 {
                let caller = SourcePosition {
                    before: 1,
                    ..position
                };
                if let Some(value) = visit_closed_scope(SourceOwner::Extension(p), &caller, wd)? {
                    return Ok(Some(value));
                }
            }
            if let VerifyFactWellDefinedResult::Success(proof) = &p.goal_wd {
                return visit_fact_stage(proof, 0, &completed, wd, verify);
            }
            Ok(None)
        }
        ExecStmtResult::By(ExecByStmtResult::FnExtension(
            crate::execute::execute_by_stmt::ExecByFnExtensionStmtResult::Success(p),
        )) => {
            if let Some(value) = visit_store_stage(&p.stored, 3, &completed, wd, verify)? {
                return Ok(Some(value));
            }
            if before > 2 {
                let caller = SourcePosition {
                    before: 2,
                    ..position
                };
                if let Some(value) = visit_closed_scope(SourceOwner::FnExtension(p), &caller, wd)? {
                    return Ok(Some(value));
                }
            }
            if let VerifyFactWellDefinedResult::Success(proof) = &p.goal_wd {
                return visit_fact_stage(proof, 0, &completed, wd, verify);
            }
            Ok(None)
        }
        ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) => {
            if let Some(value) = visit_store_stage(&p.stored, 3, &completed, wd, verify)? {
                return Ok(Some(value));
            }
            if let Some(value) =
                visit_source_fact_stage(&p.goal, &p.stored_wd, 2, &completed, wd, verify)?
            {
                return Ok(Some(value));
            }
            if before > 1 {
                let caller = SourcePosition {
                    before: 1,
                    ..position
                };
                if let Some(value) = visit_closed_scope(SourceOwner::Contra(p), &caller, wd)? {
                    return Ok(Some(value));
                }
            }
            if let VerifyFactWellDefinedResult::Success(proof) = &p.goal_wd {
                return visit_source_fact_stage(&p.goal, proof, 0, &completed, wd, verify);
            }
            Ok(None)
        }
        ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(p))) => {
            let head = p.then_facts_wd.len() + 2;
            for (index, (formation, store)) in p.stored_wd.iter().zip(&p.stored).enumerate().rev() {
                if let Some(value) =
                    visit_store_stage(store, head + 2 * index + 1, &completed, wd, verify)?
                {
                    return Ok(Some(value));
                }
                if let Some(value) =
                    visit_fact_stage(formation, head + 2 * index, &completed, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            if before >= head {
                let caller = SourcePosition {
                    before: head - 1,
                    ..position
                };
                for branch in p.branches.iter().rev() {
                    if let Some(value) =
                        visit_closed_scope(SourceOwner::CasesBranch(branch), &caller, wd)?
                    {
                        return Ok(Some(value));
                    }
                }
            }
            if let Some(value) =
                visit_verify_stage(&p.coverage, p.then_facts_wd.len(), &completed, wd, verify)?
            {
                return Ok(Some(value));
            }
            for (index, formation) in p.then_facts_wd.iter().enumerate().rev() {
                if let VerifyFactWellDefinedResult::Success(proof) = formation {
                    if let Some(value) = visit_fact_stage(proof, index, &completed, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            Ok(None)
        }
        ExecStmtResult::By(ExecByStmtResult::Induc(ExecByInducStmtResult::Success(proof)))
            if before > 0 =>
        {
            let mut closed = |evidence: SourceConstructor<'_>, position: &SourcePosition<'_>| {
                if constructor_has_closed_leaf(evidence) {
                    wd(evidence, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(
                Some(&position),
                SourceOwner::Induction(proof.into()),
                usize::MAX,
            );
            visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
        }
        ExecStmtResult::By(ExecByStmtResult::StrongInduc(
            crate::execute::execute_by_stmt::ExecByStrongInducStmtResult::Success(proof),
        )) if before > 0 => {
            let mut closed = |evidence: SourceConstructor<'_>, position: &SourcePosition<'_>| {
                if constructor_has_closed_leaf(evidence) {
                    wd(evidence, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(
                Some(&position),
                SourceOwner::Induction(proof.into()),
                usize::MAX,
            );
            visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
            crate::execute::ExecHaveFnByForallExistUniqueStmtResult::Success(p),
        )) => {
            for (stage, store) in [(5, &p.uniqueness), (4, &p.property), (2, &p.membership)] {
                if let Some(value) = visit_store_stage(store, stage, &completed, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if let Some(value) =
                visit_fact_stage(&p.property_well_defined, 3, &completed, wd, verify)?
            {
                return Ok(Some(value));
            }
            if before > 1 {
                if let VerifyObjWellDefinedResult::Success(checked) = &p.fn_set_well_defined {
                    let prior = SourcePosition {
                        before: 1,
                        ..position
                    };
                    if let Some(value) = visit_complete_wd(checked, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            visit_verify_stage(&p.source_forall, 0, &completed, wd, verify)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
            ExecHaveFnEqualCaseByCaseStmtResult::Success(p),
        )) if before > 0 => {
            if let VerifyObjWellDefinedResult::Success(checked) = &p.fn_set_well_defined {
                return visit_complete_wd(checked, &position, wd, verify);
            }
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
            ExecHaveFnByInducStmtResult::Success(proof),
        )) if before > 0 => {
            // A completed declaration exports its function graph and signature,
            // never a constructor from one of its closed branch assumptions.
            if let VerifyObjWellDefinedResult::Success(checked) = &proof.fn_set_well_defined {
                return visit_complete_wd(checked, &position, wd, verify);
            }
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(proof),
        )) if before > 0 => {
            if before > 1 {
                let prior = SourcePosition {
                    before: 1,
                    ..position
                };
                if let VerifyObjWellDefinedResult::Success(proof) = &proof.fn_set_well_defined {
                    if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            if let VerifyObjWellDefinedResult::Success(proof) = &proof.anonymous_fn_well_defined {
                return visit_complete_wd(proof, &position, wd, verify);
            }
            Ok(None)
        }
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) if before > 0 => {
            let seed = SourcePosition {
                before: 1,
                ..position
            };
            let inference = SourcePosition::new(
                Some(&seed),
                SourceOwner::PropInference(&proof.store_and_infer_result),
                usize::MAX,
            );
            if let Some(value) = visit_owner(&inference, wd, verify)? {
                return Ok(Some(value));
            }
            visit_stored_verify(
                &proof.verify_result,
                &proof.store_and_infer_result,
                &position,
                wd,
                verify,
            )
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
            crate::execute::ExecDefStructStmtResult::Success(proof),
        )) if before > 0 => {
            let mut closed = |evidence: SourceConstructor<'_>, producer: &SourcePosition<'_>| {
                if constructor_has_closed_leaf(evidence) {
                    wd(evidence, producer)
                } else {
                    Ok(None)
                }
            };
            let header = SourcePosition::new(
                Some(&position),
                SourceOwner::StructHeader(proof),
                usize::MAX,
            );
            let scope =
                SourcePosition::new(Some(&header), SourceOwner::StructFields(proof), usize::MAX);
            visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
            ExecDefPropStmtResult::Success(proof),
        )) if before > 0 => {
            let mut closed = |evidence: SourceConstructor<'_>, position: &SourcePosition<'_>| {
                if constructor_has_closed_leaf(evidence) {
                    wd(evidence, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(
                Some(&position),
                SourceOwner::PropDefinition(proof),
                usize::MAX,
            );
            visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
        }
        ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(proof)))
            if before > 0 =>
        {
            if let VerifyFactWellDefinedResult::Success(goal) = &proof.goal_wd {
                let formation =
                    SourcePosition::new(Some(&position), SourceOwner::FactWD(goal), usize::MAX);
                if let Some(value) = visit_fact_formation(goal, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            let seed = SourcePosition {
                before: 1,
                ..position
            };
            let inference = SourcePosition::new(
                Some(&seed),
                SourceOwner::PropInference(&proof.stored),
                usize::MAX,
            );
            if let Some(value) = visit_owner(&inference, wd, verify)? {
                return Ok(Some(value));
            }
            let mut closed = |evidence: SourceConstructor<'_>, position: &SourcePosition<'_>| {
                if constructor_has_closed_leaf(evidence) {
                    wd(evidence, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(Some(&position), SourceOwner::ByDef(proof), usize::MAX);
            visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
        }
        // A completed theorem or call exports only its selected whole statement,
        // never its closed binder/call-local construction records.
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(proof),
        )) if before > 0 => {
            let mut closed = |evidence: SourceConstructor<'_>, position: &SourcePosition<'_>| {
                if constructor_has_closed_leaf(evidence) {
                    wd(evidence, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(Some(&position), SourceOwner::Named(proof), usize::MAX);
            if let Some(value) = visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))? {
                return Ok(Some(value));
            }
            if let VerifyFactWellDefinedResult::Success(goal) = &proof.goal_wd {
                if let (Fact::ForallFact(fact), FactWellDefinedProof::ForallFact(goal)) =
                    (&proof.statement.fact, goal)
                {
                    let scope = SourcePosition::new(
                        Some(&position),
                        SourceOwner::ForallWD(fact, goal),
                        usize::MAX,
                    );
                    visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
                } else {
                    let scope =
                        SourcePosition::new(Some(&position), SourceOwner::FactWD(goal), usize::MAX);
                    visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
                }
            } else {
                Ok(None)
            }
        }
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Success(proof),
        )) if before > 0 => {
            let mut closed = |evidence: SourceConstructor<'_>, position: &SourcePosition<'_>| {
                if constructor_has_closed_leaf(evidence) {
                    wd(evidence, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(Some(&position), SourceOwner::Claim(proof), usize::MAX);
            if let Some(value) = visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))? {
                return Ok(Some(value));
            }
            if let VerifyFactWellDefinedResult::Success(goal) = &proof.goal_wd {
                if let (Fact::ForallFact(fact), FactWellDefinedProof::ForallFact(goal)) =
                    (&proof.statement.fact, goal)
                {
                    let scope = SourcePosition::new(
                        Some(&position),
                        SourceOwner::ForallWD(fact, goal),
                        usize::MAX,
                    );
                    visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
                } else {
                    let scope =
                        SourcePosition::new(Some(&position), SourceOwner::FactWD(goal), usize::MAX);
                    visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
                }
            } else {
                Ok(None)
            }
        }
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof)))
            if before > 0 =>
        {
            // Selection closes the invocation scope, then stores and infers
            // its selected fact in the caller. These caller-owned conclusions
            // have their own original formation provenance.
            if let Some(value) = visit_store_stage(&proof.stored, 0, &completed, wd, verify)? {
                return Ok(Some(value));
            }
            let formation = SourcePosition::new(
                Some(&position),
                SourceOwner::FactWD(&proof.selected_wd),
                usize::MAX,
            );
            if let Some(value) =
                visit_fact_formation(&proof.selected_wd, usize::MAX, &formation, wd, verify)?
            {
                return Ok(Some(value));
            }
            let mut closed = |evidence: SourceConstructor<'_>, position: &SourcePosition<'_>| {
                if constructor_has_closed_leaf(evidence) {
                    wd(evidence, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(Some(&position), SourceOwner::Call(proof), usize::MAX);
            if let Some(value) = visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))? {
                return Ok(Some(value));
            }
            visit_complete_verify(&proof.selected_proof, &scope, &mut closed, &mut |_, _| {
                Ok(None)
            })
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ExpandRange(
            crate::execute::execute_by_stmt::ExecExpandRangeStmtResult::Success(p),
        )) => visit_store_stage(&p.stored, 1, &completed, wd, verify),
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::StructDef(
            crate::execute::ExecReleaseStructDefStmtResult::Success(p),
        )) => {
            if before > 0 {
                let member_done = SourcePosition {
                    before: 1,
                    ..position
                };
                let scope = SourcePosition::new(
                    Some(&member_done),
                    SourceOwner::StructLayer(&p.release),
                    before.saturating_sub(1),
                );
                if let Some(value) = visit_owner(&scope, wd, verify)? {
                    return Ok(Some(value));
                }
                if let Some(value) = visit_complete_verify(&p.membership, &position, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            Ok(None)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::CartDef(
            crate::execute::execute_release_cart_def_stmt::ExecReleaseCartDefStmtResult::Success(
                proof,
            ),
        )) => {
            if let Some(value) =
                visit_store_stage(&proof.store_and_infer, 3, &completed, wd, verify)?
            {
                return Ok(Some(value));
            }
            for (index, child) in [
                &proof.verification.well_defined_proof.left,
                &proof.verification.well_defined_proof.right,
            ]
            .into_iter()
            .take(before.min(2))
            .enumerate()
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..position
                };
                if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            Ok(None)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::TupleDef(
            crate::execute::execute_release_tuple_def_stmt::ExecReleaseTupleDefStmtResult::Success(
                proof,
            ),
        )) => {
            let head =
                super::compile_release_tuple_def_result::tuple_release_publication_start(proof);
            for (index, store) in proof
                .stored
                .iter()
                .take(before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                if let Some(value) = visit_store_stage(store, head + index, &completed, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            let member_stage = 2 + proof.return_proofs.len();
            for (index, checked) in proof
                .coordinate_proofs
                .iter()
                .take(before.saturating_sub(member_stage + 1))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: member_stage + 1 + index,
                    ..position
                };
                if let Some(value) = visit_complete_verify(checked, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if before > member_stage {
                let prior = SourcePosition {
                    before: member_stage,
                    ..position
                };
                let formed = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FactWD(&proof.membership_wd),
                    usize::MAX,
                );
                if let Some(value) =
                    visit_fact_formation(&proof.membership_wd, usize::MAX, &formed, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            for (index, checked) in proof
                .return_proofs
                .iter()
                .take(before.saturating_sub(2))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: 2 + index,
                    ..position
                };
                if let Some(value) = visit_complete_verify(checked, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            for (index, checked) in [&proof.domain.function_wd, &proof.domain.target_wd]
                .into_iter()
                .take(before.min(2))
                .enumerate()
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..position
                };
                if let Some(value) = visit_complete_wd(checked, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            Ok(None)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ObjDef(
            crate::execute::execute_release_obj_def_stmt::ExecReleaseObjDefStmtResult::Success(
                proof,
            ),
        )) => {
            for (index, store) in proof.store_and_infer.iter().take(before).enumerate().rev() {
                if let Some(value) = visit_store_stage(store, index, &completed, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            Ok(None)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(proof),
        )) => {
            for (index, store) in proof.stored.iter().take(before / 2).enumerate().rev() {
                let published = SourcePosition {
                    before: 2 * index + 2,
                    ..position
                };
                let inference = SourcePosition::new(
                    Some(&published),
                    SourceOwner::PropInference(store),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            for (index, caller_wd) in proof
                .stored_wd
                .iter()
                .take(before.saturating_add(1) / 2)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: 2 * index,
                    ..position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::FactWD(caller_wd), usize::MAX);
                if let Some(value) =
                    visit_fact_formation(caller_wd, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(_)) | ExecStmtResult::By(_) => {
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(proof)),
        )) if before > 0 => {
            if let VerifyObjWellDefinedResult::Success(proof) = &proof.value_well_defined {
                visit_complete_wd(proof, &position, wd, verify)
            } else {
                Ok(None)
            }
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
        )) => {
            if before > 3 * proof.statement.objs_equal_to.len() {
                let scope = SourcePosition::new(
                    Some(&completed),
                    SourceOwner::StructLayers(
                        proof.auto_opened_struct_layers.as_deref().unwrap_or(&[]),
                    ),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&scope, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            let count = proof.equal_to_well_defined.len();
            for (index, proof) in proof
                .membership_checks
                .iter()
                .take(before.saturating_sub(count))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: count + index,
                    ..position
                };
                if let Some(value) = visit_complete_verify(proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            for (index, proof) in proof
                .equal_to_well_defined
                .iter()
                .take(before)
                .enumerate()
                .rev()
            {
                if let VerifyObjWellDefinedResult::Success(proof) = proof {
                    let prior = SourcePosition {
                        before: index,
                        ..position
                    };
                    if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            Ok(None)
        }
        _ => {
            if let Some(proof) = ordinary_have(statement) {
                if before > parameter_count(&proof.statement.param_def.groups) {
                    let scope = SourcePosition::new(
                        Some(&completed),
                        SourceOwner::StructLayers(
                            proof.auto_opened_struct_layers.as_deref().unwrap_or(&[]),
                        ),
                        usize::MAX,
                    );
                    if let Some(value) = visit_owner(&scope, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
                for (index, store) in proof
                    .store_and_infer_result
                    .store_and_infer_results
                    .iter()
                    .take(before)
                    .enumerate()
                    .rev()
                {
                    let prior = SourcePosition {
                        before: index + 1,
                        ..position
                    };
                    let inference = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::PropInference(store),
                        usize::MAX,
                    );
                    if let Some(value) = visit_owner(&inference, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
                let mut offset = 0;
                for (group, captured) in proof.statement.param_def.groups.iter().zip(&proof.groups)
                {
                    if offset < before {
                        let prior = SourcePosition {
                            before: offset,
                            ..position
                        };
                        let group_position = SourcePosition::new(
                            Some(&prior),
                            SourceOwner::HaveGroup(
                                &captured.param_type_well_defined,
                                &captured.nonempty_check,
                            ),
                            2,
                        );
                        if let Some(value) = visit_owner(&group_position, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                    offset += group.params.len();
                }
            }
            Ok(None)
        }
    }
}

fn visit_complete_wd<T>(
    proof: &ObjWellDefinedProof,
    parent: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if let Some(value) = wd(SourceConstructor::Checked(proof), parent)? {
        return Ok(Some(value));
    }
    let position = SourcePosition::new(Some(parent), SourceOwner::WD(proof), usize::MAX);
    visit_owner(&position, wd, verify)
}

/// A completed statement has emitted its registered object definitions. Keep
/// those bindings when observing their original WD, without advancing the
/// original proof's fact prefix or exposing its later store/inferences.
fn visit_stored_verify<T>(
    proof: &VerifyFactResult,
    store: &StoreFactAndInferResult,
    parent: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if store.formed_subjects.is_empty() {
        return visit_complete_verify(proof, parent, wd, verify);
    }
    let mut formed_wd = |evidence: SourceConstructor<'_>, original: &SourcePosition<'_>| {
        let formed =
            SourcePosition::new(Some(original), SourceOwner::FormedSubjects(proof, store), 0);
        wd(evidence, &formed)
    };
    visit_complete_verify(proof, parent, &mut formed_wd, verify)
}

fn visit_complete_verify<T>(
    proof: &VerifyFactResult,
    parent: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if let Some(value) = verify(proof, parent)? {
        return Ok(Some(value));
    }
    let position = SourcePosition::new(Some(parent), SourceOwner::Verify(proof), usize::MAX);
    if let VerifyFactResult::ForallFact(proof) = proof {
        if let VerifyForallFactResult::Success(proof) = proof.as_ref() {
            let owner = match proof {
                VerifyForallFactProof::ByLocalIntroduction(p) => Some(SourceOwner::Forall(p)),
                VerifyForallFactProof::ByKnownForallFact(p) => Some(SourceOwner::KnownForall(p)),
                _ => None,
            };
            if let Some(owner) = owner {
                let mut closed = |evidence: SourceConstructor<'_>,
                                  position: &SourcePosition<'_>| {
                    if constructor_has_closed_leaf(evidence) {
                        wd(evidence, position)
                    } else {
                        Ok(None)
                    }
                };
                let scope = SourcePosition::new(Some(&position), owner, usize::MAX);
                return visit_owner(&scope, &mut closed, &mut |_, _| Ok(None));
            }
        }
    }
    if let VerifyFactResult::ExistShapedFact(result) = proof {
        let formation = match result.as_ref() {
            VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) => {
                Some((p.fact.plain(), &p.well_defined_proof))
            }
            VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(
                p,
            )) => Some((p.fact.plain(), &p.well_defined_proof)),
            VerifyExistShapedFactResult::NotExistFact(crate::execute::execute_fact_stmt::verify_exist_shaped_fact::VerifyNotExistFactResult::Success(p)) => Some((p.fact.plain(), &p.well_defined_proof)),
            _ => None,
        };
        if let Some((fact, formation)) = formation {
            return visit_closed_scope(SourceOwner::ExistWD(fact, formation), parent, wd);
        }
    }
    visit_verify_formation(proof, usize::MAX, &position, wd, verify)
}

fn closed_leaf(object: &Obj) -> bool {
    match object {
        Obj::Literal(Literal::Number(_) | Literal::ImaginaryUnit(_)) | Obj::StandardSet(_) => true,
        // Enumeration has no domain conditions beyond its children's WD.
        // Restrict recovery to the same closed leaves recursively: a set of
        // local variables or guarded arithmetic must stay in its own scope.
        Obj::SetFormer(SetFormer::ListSet(set)) => set.list.iter().all(|item| closed_leaf(item)),
        _ => false,
    }
}

fn visit_verify_formation<T>(
    proof: &VerifyFactResult,
    before: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    match proof {
        VerifyFactResult::NotForall(result) if before > 0 => {
            if let crate::execute::execute_fact_stmt::verify_not_forall_fact::VerifyNotForallFactResult::Success(p) = result.as_ref() {
                return visit_complete_verify(&p.prove_derived_exist, position, wd, verify);
            }
        }
        VerifyFactResult::Equality(proof) => match proof.as_ref() {
            VerifyEqualityResult::Success(proof) => {
                if before == usize::MAX {
                    let known = match &proof.searched_proof {
                        EqualFactSearchedProof::ByKnownForallFact(known) => Some(known.as_ref()),
                        EqualFactSearchedProof::ByKnownForallFactViaSymmetry(known) => {
                            Some(&known.known_forall)
                        }
                        _ => None,
                    };
                    if let Some(known) = known {
                        let scope = SourcePosition::new(
                            Some(position),
                            SourceOwner::KnownApplication(known),
                            known.arg_match_proofs.len() + known_application_requirements(known).len(),
                        );
                        if let Some(value) = visit_owner(&scope, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                    if let EqualFactSearchedProof::ByObjectDefinition(
                        crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::EqualitySearchProofByObjectDefinition::ByFnApplication(
                            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqualCaseByCase(unfold),
                        ),
                    ) = &proof.searched_proof {
                        let scope = SourcePosition::new(Some(position), SourceOwner::PiecewiseUnfold(unfold), 2);
                        if let Some(value) = visit_owner(&scope, wd, verify)? { return Ok(Some(value)); }
                    }
                    if let EqualFactSearchedProof::ByObjectDefinition(
                        crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::EqualitySearchProofByObjectDefinition::ByFnApplication(
                            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition::HaveFnByInduc(unfold),
                        ),
                    ) = &proof.searched_proof {
                        let scope = SourcePosition::new(Some(position), SourceOwner::RecursiveUnfold(unfold), unfold.selected_case_path.len() + 1);
                        if let Some(value) = visit_owner(&scope, wd, verify)? { return Ok(Some(value)); }
                    }
                }
                let children = [
                    &proof.well_defined_proof.left,
                    &proof.well_defined_proof.right,
                ];
                for (index, child) in children.iter().take(before).enumerate().rev() {
                    let prior = SourcePosition {
                        before: index,
                        ..*position
                    };
                    if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            _ => {}
        },
        VerifyFactResult::AtomicExceptEquality(proof) => {
            if let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() {
                return visit_atomic_verify_formation(proof, before, position, wd, verify);
            }
        }
        VerifyFactResult::AndFact(result) => {
            if let crate::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactResult::Success(proof) = result.as_ref() {
                if let Some(known)=&proof.known_forall {
                    let scope=SourcePosition::new(Some(position),SourceOwner::KnownApplication(known),known.arg_match_proofs.len()+known_application_requirements(known).len());
                    if let Some(value)=visit_owner(&scope,wd,verify)? { return Ok(Some(value)); }
                }
                for (index, child) in proof.components.iter().take(before).enumerate().rev() {
                    let prior = SourcePosition { before: index, ..*position };
                    if let Some(value) = visit_complete_verify(child, &prior, wd, verify)? { return Ok(Some(value)); }
                }
            }
        }
        VerifyFactResult::ChainFact(result) => {
            if let crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult::Success(proof) = result.as_ref() {
                if let Some(known)=&proof.known_forall {
                    let scope=SourcePosition::new(Some(position),SourceOwner::KnownApplication(known),known.arg_match_proofs.len()+known_application_requirements(known).len());
                    if let Some(value)=visit_owner(&scope,wd,verify)? { return Ok(Some(value)); }
                }
                for (index, child) in proof.adjacent.iter().take(before).enumerate().rev() {
                    let prior = SourcePosition { before: index, ..*position };
                    if let Some(value) = visit_complete_verify(child, &prior, wd, verify)? { return Ok(Some(value)); }
                }
            }
        }
        VerifyFactResult::OrFact(result) => {
            if let VerifyOrFactResult::Success(proof) = result.as_ref() {
                let split_members = match &proof.searched_proof {
                    OrFactSearchedProof::ByBuiltinRule(OrFactSearchProofByBuiltinRule::LessOrGreaterEqual(p)) => Some([&p.left_in_r, &p.right_in_r]),
                    OrFactSearchedProof::ByBuiltinRule(OrFactSearchProofByBuiltinRule::GreaterOrLessEqual(p)) => Some([&p.left_in_r, &p.right_in_r]),
                    _ => None,
                };
                if let Some(children) = split_members {
                    for (i, child) in children.into_iter().take(before.saturating_sub(proof.fact.facts.len())).enumerate().rev() {
                        let prior = SourcePosition { before: proof.fact.facts.len() + i, ..*position };
                        if let Some(value) = visit_complete_verify(child, &prior, wd, verify)? { return Ok(Some(value)); }
                    }
                }
                if let OrFactSearchedProof::ByBuiltinRule(OrFactSearchProofByBuiltinRule::ZeroProductSplit(selected)) = &proof.searched_proof {
                    let head = proof.well_defined_proof.branches.len();
                    for (i, child) in [&selected.left_in_r, &selected.right_in_r, &selected.product_zero].into_iter().take(before.saturating_sub(head)).enumerate().collect::<Vec<_>>().into_iter().rev() {
                        let prior = SourcePosition { before: head + i, ..*position };
                        if let Some(value) = visit_complete_verify(child, &prior, wd, verify)? { return Ok(Some(value)); }
                    }
                }

                for (index, child) in proof.well_defined_proof.branches.iter().take(before).enumerate().rev() {
                    let prior = SourcePosition { before: index, ..*position };
                    let formation = SourcePosition::new(Some(&prior), SourceOwner::FactWD(child), usize::MAX);
                    if let Some(value) = visit_fact_formation(child, usize::MAX, &formation, wd, verify)? { return Ok(Some(value)); }
                }
            }
        }
        // Completed quantified proofs cannot reopen their closed source scope.
        _ => {}
    }
    Ok(None)
}

fn visit_atomic_verify_formation<T>(
    proof: &VerifyAtomicExceptEqualityFactSuccess,
    before: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let head = atomic_formation_stage_count(&proof.well_defined_proof);
    for (index, child) in atomic_search_stages(proof)
        .into_iter()
        .take(before.saturating_sub(head))
        .enumerate()
        .rev()
    {
        // Keep the completion boundary in ancestry while the child callback
        // receives its actual pre-stage cursor. Ancestor scans must not make
        // this child available at its own pending prefix.
        let completed = SourcePosition {
            before: head + index + 1,
            ..*position
        };
        let prior = SourcePosition {
            parent: Some(&completed),
            before: head + index,
            ..*position
        };
        let found = match child {
            AtomicSearchStage::WD(child) => visit_complete_wd(child, &prior, wd, verify)?,
            AtomicSearchStage::Verify(child) => visit_complete_verify(child, &prior, wd, verify)?,
            AtomicSearchStage::Atomic(child) => {
                let child_scope =
                    SourcePosition::new(Some(&prior), SourceOwner::AtomicVerify(child), usize::MAX);
                visit_owner(&child_scope, wd, verify)?
            }
        };
        if found.is_some() {
            return Ok(found);
        }
    }
    if before == usize::MAX {
        if let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(known) =
            &proof.searched_proof
        {
            let scope = SourcePosition::new(
                Some(position),
                SourceOwner::KnownApplication(known),
                known.arg_match_proofs.len() + known_application_requirements(known).len(),
            );
            if let Some(value) = visit_owner(&scope, wd, verify)? {
                return Ok(Some(value));
            }
        }
        if let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(
            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(unfold),
        ) = &proof.searched_proof {
            let scope = SourcePosition::new(Some(position), SourceOwner::AtomicFnUnfold(unfold), unfold.unfold_equal_proofs.len() + 1);
            if let Some(value) = visit_owner(&scope, wd, verify)? { return Ok(Some(value)); }
        }
    }
    visit_atomic_formation(&proof.well_defined_proof, before, position, wd, verify)
}

fn atomic_formation_stage_count(proof: &AtomicFactWellDefinedProof) -> usize {
    proof.well_defined_of_each_parameter.len()
        + match &proof.predicate_domain {
            PredicateDomainProof::ByRequirements(requirements) => requirements.len(),
            _ => 0,
        }
}

enum AtomicSearchStage<'a> {
    WD(&'a ObjWellDefinedProof),
    Verify(&'a VerifyFactResult),
    Atomic(&'a VerifyAtomicExceptEqualityFactSuccess),
}

fn function_domain_search_stages<'a>(
    proof: &'a crate::execute::execute_fact_stmt::function_domain::FunctionDomainMatchProof,
    stages: &mut Vec<AtomicSearchStage<'a>>,
) {
    use crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof;
    stages.push(AtomicSearchStage::WD(&proof.function_wd));
    stages.push(AtomicSearchStage::WD(&proof.target_wd));
    complete_domain_source_stages(&proof.source, stages);
    if let FunctionDomainComparisonProof::MutualInclusion {
        forward_proof,
        reverse_proof,
        ..
    } = &proof.comparison
    {
        stages.push(AtomicSearchStage::Verify(forward_proof));
        stages.push(AtomicSearchStage::Verify(reverse_proof));
    }
}

fn complete_domain_source_stages<'a>(
    proof: &'a CompleteFunctionDomainProof,
    stages: &mut Vec<AtomicSearchStage<'a>>,
) {
    use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof;
    match &proof.source {
        CompleteFunctionDomainSourceProof::TemplateDefinition { instance_wd, .. } => {
            stages.push(AtomicSearchStage::WD(instance_wd))
        }
        CompleteFunctionDomainSourceProof::ApplicationReturn {
            application_children,
            application_requirements,
            ..
        } => {
            stages.extend(
                application_children
                    .iter()
                    .map(|child| AtomicSearchStage::WD(child)),
            );
            stages.extend(
                application_requirements
                    .iter()
                    .map(AtomicSearchStage::Verify),
            );
        }
        _ => {}
    }
}

fn complete_domain_argument_scope(
    proof: &CompleteFunctionDomainProof,
) -> Option<&crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjArgumentScope>
{
    match &proof.source {
        crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof::ApplicationReturn { argument_scope, .. } => argument_scope.as_ref(),
        _ => None,
    }
}

// Borrow the children retained by these selected search routes. No new proof,
// wrapper result, or persistent lookup table is manufactured here.
fn atomic_search_stages(
    proof: &VerifyAtomicExceptEqualityFactSuccess,
) -> Vec<AtomicSearchStage<'_>> {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::{InFactSearchProofByBuiltinRule, PowerSetMembershipSubsetProof};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
        not_greater::NotGreaterFactSearchProofByBuiltinRule,
        not_less::NotLessFactSearchProofByBuiltinRule,
        not_greater_equal::NotGreaterEqualFactSearchProofByBuiltinRule,
        not_less_equal::NotLessEqualFactSearchProofByBuiltinRule,
    };
    let mut stages = Vec::new();
    match &proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ListSetSubsetFromMembers(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PreimageMembership(p)) => {
            stages.push(AtomicSearchStage::WD(&p.construction.builder_well_defined));
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PreimageSetMembership(p)) => {
            stages.push(AtomicSearchStage::WD(&p.construction.builder_well_defined));
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }

        AtomicExceptEqualityFactSearchedProof::ByDefinition(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(p)) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::BuiltinPropDefinitionProof;
            let children = match p {
                BuiltinPropDefinitionProof::Subset(p) => &p.proof_of_requirement_facts,
                BuiltinPropDefinitionProof::Superset(p) => &p.proof_of_requirement_facts,
                BuiltinPropDefinitionProof::ProperSubset(p) => &p.proof_of_requirement_facts,
                BuiltinPropDefinitionProof::ProperSuperset(p) => &p.proof_of_requirement_facts,
                BuiltinPropDefinitionProof::Prime(p) => &p.proof_of_requirement_facts,
                BuiltinPropDefinitionProof::Coprime(p) => &p.proof_of_requirement_facts,
                BuiltinPropDefinitionProof::Dvd(p) => &p.proof_of_requirement_facts,
                BuiltinPropDefinitionProof::Injective(p) => &p.proof_of_requirement_facts,
                BuiltinPropDefinitionProof::Surjective(p) => &p.proof_of_requirement_facts,
                BuiltinPropDefinitionProof::Bijective(p) => &p.proof_of_requirement_facts,
                _ => return stages,
            };
            stages.extend(children.iter().map(AtomicSearchStage::Verify));
        }

        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::AddLeftCongruenceStrict(p))) => {
            stages.push(AtomicSearchStage::Verify(&p.premise_proof));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::ModRemainderStrictUpperBound(p))) => {
            stages.push(AtomicSearchStage::Verify(&p.dividend_in_z_proof));
            stages.push(AtomicSearchStage::Verify(&p.modulus_in_n_pos_proof));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::AddRightCongruenceStrict(p))) => {
            stages.push(AtomicSearchStage::Verify(&p.premise_proof));
        }

        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::MulLeftPositiveMonotoneStrict(p))) => {
            stages.push(AtomicSearchStage::Verify(&p.positive_factor_proof));
            stages.push(AtomicSearchStage::Verify(&p.order_premise_proof));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::MulRightPositiveMonotoneStrict(p))) => {
            stages.push(AtomicSearchStage::Verify(&p.positive_factor_proof));
            stages.push(AtomicSearchStage::Verify(&p.order_premise_proof));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::FiniteSetSubsetMembership(p))) => {
            stages.push(AtomicSearchStage::Verify(&p.source_membership_proof));
            stages.extend(p.member_in_proofs.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CommonPositiveFactorLess(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }

        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::FromKnownOrderComplement(p))
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater::GreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(p))
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(NotGreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(p))
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(NotLessFactSearchProofByBuiltinRule::FromKnownOrderComplement(p))
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact(NotGreaterEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(p))
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact(NotLessEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(p))
        ) => {
            stages.extend(p.real_carrier_proofs.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLessEqual(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLessEqual(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLess(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLess(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseLessEqual(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddCrossedLessEqual(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddDoubleUpperBound(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictLeft(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictRight(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftLeft(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftRight(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftLeft(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftRight(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftLeftWeak(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowSharedExponentLessEqual(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(
            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(p))) => {
            stages.extend(p.real_carrier_proofs.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::SumOfNonnegatives(proof),
            ),
        ) => {
            fn visit<'a>(
                tree: &'a crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::NonnegativeSumTree,
                stages: &mut Vec<AtomicSearchStage<'a>>,
            ) {
                use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::NonnegativeSumTree;
                match tree {
                    NonnegativeSumTree::Leaf(proof) => stages.push(AtomicSearchStage::Verify(proof)),
                    NonnegativeSumTree::Add { left, right } => {
                        visit(left, stages);
                        visit(right, stages);
                    }
                }
            }
            visit(&proof.constructor_tree, &mut stages);
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(rule),
        ) => match rule {
            LessEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof) => {
                stages.extend(proof.real_carrier_proofs.iter().map(AtomicSearchStage::Verify));
            }
            LessEqualFactSearchProofByBuiltinRule::AddRightNonnegative(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.nonnegative_addend_proof));
            }
            LessEqualFactSearchProofByBuiltinRule::AddLeftNonnegative(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.nonnegative_addend_proof));
            }
            LessEqualFactSearchProofByBuiltinRule::SumOfNonnegatives(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.left_nonnegative_proof));
                stages.push(AtomicSearchStage::Verify(&proof.right_nonnegative_proof));
            }
            LessEqualFactSearchProofByBuiltinRule::ProductOfNonnegatives(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.left_nonnegative_proof));
                stages.push(AtomicSearchStage::Verify(&proof.right_nonnegative_proof));
            }
            LessEqualFactSearchProofByBuiltinRule::ModRemainderNonnegative(p) => {
                stages.push(AtomicSearchStage::Verify(&p.dividend_in_z_proof));
                stages.push(AtomicSearchStage::Verify(&p.modulus_in_n_pos_proof));
            }
            LessEqualFactSearchProofByBuiltinRule::FloorMonotone(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.argument_order));
            }
            LessEqualFactSearchProofByBuiltinRule::CeilMonotone(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.argument_order));
            }
            LessEqualFactSearchProofByBuiltinRule::MinWeakMonotone(proof) => {
                use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::sign_extremum_order::WeakOrderArgumentProof;
                for child in [&proof.left_order, &proof.right_order] {
                    if let WeakOrderArgumentProof::ByOrder(result) = child {
                        stages.push(AtomicSearchStage::Verify(result));
                    }
                }
            }
            LessEqualFactSearchProofByBuiltinRule::MaxWeakMonotone(proof) => {
                use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::sign_extremum_order::WeakOrderArgumentProof;
                for child in [&proof.left_order, &proof.right_order] {
                    if let WeakOrderArgumentProof::ByOrder(result) = child {
                        stages.push(AtomicSearchStage::Verify(result));
                    }
                }
            }
            _ => {}
        },
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(rule),
        ) => match rule {
            InFactSearchProofByBuiltinRule::StructObjMembership(proof) => {
                stages.extend(proof.carrier_obligations.iter().chain(&proof.equivalent_fact_proofs).map(AtomicSearchStage::Verify));
            }
            InFactSearchProofByBuiltinRule::CartMembership(proof) => {
                function_domain_search_stages(&proof.domain, &mut stages);
                stages.extend(
                    proof
                        .proof_of_requirement_facts
                        .iter()
                        .map(AtomicSearchStage::Verify),
                );
            }
            InFactSearchProofByBuiltinRule::PowerSetMembership(proof) => {
                if let PowerSetMembershipSubsetProof::VerifiedSubset(child) = &proof.subset_proof {
                    stages.push(AtomicSearchStage::Atomic(child));
                }
            }
            InFactSearchProofByBuiltinRule::SetMinusMembership(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.left_membership_proof));
                stages.push(AtomicSearchStage::Verify(&proof.right_non_membership_proof));
            }
            InFactSearchProofByBuiltinRule::IntersectMembership(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.left_membership_proof));
                stages.push(AtomicSearchStage::Verify(&proof.right_membership_proof));
            }
            InFactSearchProofByBuiltinRule::UnionMembershipFromLeft(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.left_membership_proof))
            }
            InFactSearchProofByBuiltinRule::UnionMembershipFromRight(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.right_membership_proof))
            }
            _ => {}
        },
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartMembership(proof),
        ) => {
            function_domain_search_stages(&proof.domain, &mut stages);
            stages.extend(
                proof
                    .proof_of_requirement_facts
                    .iter()
                    .map(AtomicSearchStage::Verify),
            );
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowerSetMembership(proof),
        ) => {
            stages.extend(
                proof
                    .proof_of_requirement_facts
                    .iter()
                    .map(AtomicSearchStage::Verify),
            );
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(proof)) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::SubsetFactSearchProofByBuiltinRule as Rule;
            match proof {
                Rule::FunctionPreimageSubsetOfInputCarrier(p) => stages.push(AtomicSearchStage::WD(&p.construction.builder_well_defined)),
                Rule::SubsetSetMinusCommonRightMonotone(p) => stages.push(AtomicSearchStage::Verify(&p.left_operand_subset_proof)),
                Rule::SubsetPowerSetMonotone(p) => stages.push(AtomicSearchStage::Verify(&p.base_subset_proof)),
                Rule::SubsetTransitivity(p) => {
                    stages.push(AtomicSearchStage::Verify(&p.left_to_middle_proof));
                    stages.push(AtomicSearchStage::Verify(&p.middle_to_right_proof));
                }
                Rule::UnionSubsetFromBothOperands(p) => {
                    stages.push(AtomicSearchStage::Verify(&p.left_operand_subset_proof));
                    stages.push(AtomicSearchStage::Verify(&p.right_operand_subset_proof));
                }
                Rule::UnionSubsetFromComponentwise(p) => stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify)),
                Rule::IntersectSubsetFromLeftUpperBound(p) => stages.push(AtomicSearchStage::Verify(&p.left_operand_subset_proof)),
                Rule::IntersectSubsetFromRightUpperBound(p) => stages.push(AtomicSearchStage::Verify(&p.right_operand_subset_proof)),
                _ => {}
            }
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionSubsetFromBothOperands(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusSubsetFromLeft(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromLeftOperand(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromRightOperand(p)) => {
            stages.extend(p.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusMembership(proof)) => {
            stages.extend(proof.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(proof)) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_in_fact::NotInFactSearchProofByBuiltinRule as Rule;
            match proof {
                Rule::NonMembershipOfIntersectFromLeft(p) => stages.push(AtomicSearchStage::Verify(&p.left_non_membership_proof)),
                Rule::NonMembershipOfIntersectFromRight(p) => stages.push(AtomicSearchStage::Verify(&p.right_non_membership_proof)),
                Rule::NonMembershipOfUnion(p) => {
                    stages.push(AtomicSearchStage::Verify(&p.left_non_membership_proof));
                    stages.push(AtomicSearchStage::Verify(&p.right_non_membership_proof));
                }
                Rule::NonMembershipOfSetMinusFromRight(p) => stages.push(AtomicSearchStage::Verify(&p.right_membership_proof)),
                Rule::NonMembershipOfSetMinusFromLeft(p) => stages.push(AtomicSearchStage::Verify(&p.left_non_membership_proof)),
                _ => {}
            }
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectMembership(proof)) => {
            stages.extend(proof.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubsetOfIntersectFromBothBounds(proof)) => {
            stages.extend(proof.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }


        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromLeft(proof)) => {
            stages.extend(proof.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromRight(proof)) => {
            stages.extend(proof.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartNonemptyFromAllFactors(proof)) => {
            stages.extend(proof.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteFunctionApplicationMembership(proof)) => {
            stages.extend(proof.proof_of_requirement_facts.iter().map(AtomicSearchStage::Verify));
        }
        _ => {}
    }
    stages
}

fn visit_atomic_formation<T>(
    proof: &AtomicFactWellDefinedProof,
    before: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let children = &proof.well_defined_of_each_parameter;
    if let PredicateDomainProof::ByRequirements(requirements) = &proof.predicate_domain {
        for (index, requirement) in requirements
            .iter()
            .take(before.saturating_sub(children.len()))
            .enumerate()
            .rev()
        {
            let prior = SourcePosition {
                before: children.len() + index,
                ..*position
            };
            if let Some(value) = visit_complete_verify(&requirement.result, &prior, wd, verify)? {
                return Ok(Some(value));
            }
        }
    }
    for (index, child) in children.iter().take(before).enumerate().rev() {
        let prior = SourcePosition {
            before: index,
            ..*position
        };
        if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
            return Ok(Some(value));
        }
    }
    Ok(None)
}

fn visit_fact_formation<T>(
    proof: &FactWellDefinedProof,
    before: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    match proof {
        FactWellDefinedProof::Equality(proof) => {
            let children = [&proof.left, &proof.right];
            for (index, child) in children.iter().take(before).enumerate().rev() {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        FactWellDefinedProof::AtomicExceptEquality(proof) => {
            return visit_atomic_formation(proof, before, position, wd, verify)
        }
        FactWellDefinedProof::AndFact { components }
        | FactWellDefinedProof::ChainFact {
            adjacent: components,
        } => {
            for (index, child) in components.iter().take(before).enumerate().rev() {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::AtomicWD(child), usize::MAX);
                if let Some(value) =
                    visit_atomic_formation(child, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
        }
        FactWellDefinedProof::OrFact(proof) => {
            for (index, child) in proof.branches.iter().take(before).enumerate().rev() {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::FactWD(child), usize::MAX);
                if let Some(value) =
                    visit_fact_formation(child, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
        }
        _ => {}
    }
    Ok(None)
}

/// A completed constructor already owns these certified children. Follow only
/// fields which preserve the original host object, never denotation equality or
/// a searched proof tree. Tuples, for example, retain values but not child hosts.
fn projected_wd_child<'a>(
    proof: &'a ObjWellDefinedProof,
    term: String,
    matches: &impl Fn(&ObjWellDefinedProof) -> bool,
) -> Option<(&'a ObjWellDefinedProof, String)> {
    if matches(proof) {
        return Some((proof, term));
    }
    if let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::Composition(
                p,
            )),
        ..
    } = proof
    {
        for (child, field) in [
            (&p.outer_well_defined, "outer"),
            (&p.inner_well_defined, "inner"),
        ] {
            if matches!(
                child.obj(),
                Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
            ) {
                continue;
            }
            if let Some(found) = projected_wd_child(child, format!("({term}).val.{field}"), matches)
            {
                return Some(found);
            }
        }
        return None;
    }
    let fields: &[&str] = match proof {
        ObjWellDefinedProof::ByDef {
            obj: Obj::FnObj(application),
            proof: ObjWellDefinedProofByDef::FnObj(call),
        } => {
            use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
            if let Some(FnObjDomainFnSetEvidence::Composition(p)) = &call.domain_fn_set {
                if p.function_equal.path.is_empty() {
                    if let crate::execute::execute_fact_stmt::function_composition::CompositionWellDefinedPremise::Checked(root) = &p.well_defined {
                        let mut head = term.clone();
                        for _ in &application.body {
                            head = format!("({head}).val.function");
                        }
                        if let Some(found) = projected_wd_child(root, head, matches) {
                            return Some(found);
                        }
                    }
                }
            }
            match call.domain_fn_set.as_ref()? {
                FnObjDomainFnSetEvidence::FiniteFunction(_) => &["function", "argument"],
                FnObjDomainFnSetEvidence::Composition(p) if application.body.len() == 1 => {
                    match application.body[0].len() {
                        1 => &["argument"],
                        2 if super::LitexToLeanCompiler::function_uses_numeric_interface(
                            &p.function.body,
                        ) =>
                        {
                            &["first", "second"]
                        }
                        2 => &["argument.val.first", "argument.val.second"],
                        _ => return None,
                    }
                }
                FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }
                | FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }
                    if application.body.len() == 1 =>
                {
                    // CallObj2 stores numeric arguments directly. Generic
                    // two-argument calls retain them in CallArguments2.
                    let anonymous = matches!(
                        call.domain_fn_set,
                        Some(FnObjDomainFnSetEvidence::AnonymousLiteral { .. })
                    );
                    match (application.body[0].len(), anonymous) {
                        (1, false) => &["argument"],
                        (1, true) => &["function", "argument"],
                        (2, false)
                            if super::LitexToLeanCompiler::function_uses_numeric_interface(
                                fn_set,
                            ) =>
                        {
                            &["first", "second"]
                        }
                        (2, true)
                            if super::LitexToLeanCompiler::function_uses_numeric_interface(
                                fn_set,
                            ) =>
                        {
                            &["function", "first", "second"]
                        }
                        (2, false) => &["argument.val.first", "argument.val.second"],
                        (2, true) => &["function", "argument.val.first", "argument.val.second"],
                        _ => return None,
                    }
                }
                _ => return None,
            }
        }
        _ => match proof.obj() {
            Obj::ArithmeticOperator(
                ArithmeticOperator::Add(_)
                | ArithmeticOperator::Sub(_)
                | ArithmeticOperator::Mul(_)
                | ArithmeticOperator::Div(_)
                | ArithmeticOperator::Min(_)
                | ArithmeticOperator::Max(_),
            ) => &["left", "right"],
            Obj::FunctionSpace(FunctionSpace::Preimage(_) | FunctionSpace::PreimageSet(_)) => {
                &["function", "target"]
            }
            Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => &["carrier", "length"],
            Obj::SetFormer(SetFormer::SeqSet(_)) => &["carrier"],
            Obj::SetFormer(SetFormer::IntervalObj(_)) => &["lower", "upper"],
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(_)) => &["endpoint"],
            Obj::FiniteSetStat(_) => &["set"],
            Obj::IteratedOperator(IteratedOperator::Sum(_) | IteratedOperator::Product(_)) => {
                &["first", "last", "function"]
            }
            Obj::IteratedOperator(
                IteratedOperator::SumOfFiniteSet(_) | IteratedOperator::ProductOfFiniteSet(_),
            ) => &["set", "function"],
            Obj::IntegerOperator(IntegerOperator::Factorial(_)) => &["arg"],
            Obj::IntegerOperator(
                IntegerOperator::Mod(_)
                | IntegerOperator::Quot(_)
                | IntegerOperator::Gcd(_)
                | IntegerOperator::Lcm(_),
            ) => &["left", "right"],
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(_)) => &["base", "exponent"],
            Obj::ComplexOperator(_) => &["arg"],
            Obj::TrigOperator(_) => &["arg"],
            Obj::ExpLogOperator(ExpLogOperator::Exp(_) | ExpLogOperator::Ln(_)) => &["arg"],
            Obj::ExpLogOperator(ExpLogOperator::Log(_)) => &["base", "arg"],
            Obj::ArithmeticOperator(
                ArithmeticOperator::Neg(_)
                | ArithmeticOperator::Abs(_)
                | ArithmeticOperator::Sign(_)
                | ArithmeticOperator::Floor(_)
                | ArithmeticOperator::Ceil(_),
            )
            | Obj::ExpLogOperator(ExpLogOperator::Sqrt(_)) => &["arg"],
            _ => return None,
        },
    };
    let (children, _) = arithmetic_stages(proof)?;
    if children.len() != fields.len() {
        return None;
    }
    for (child, field) in children.iter().zip(fields) {
        // Canonical leaves are shorter than a projection and need no sharing.
        if matches!(
            child.obj(),
            Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
        ) {
            continue;
        }
        if let Some(found) = projected_wd_child(child, format!("({term}).val.{field}"), matches) {
            return Some(found);
        }
    }
    None
}

pub(super) fn arithmetic_stages(
    proof: &ObjWellDefinedProof,
) -> Option<(&[Box<ObjWellDefinedProof>], &[VerifyFactResult])> {
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetFormer(p),
        ..
    } = proof
    {
        match p {
            SetFormerObjWellDefinedProofByDef::IntervalObj(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified));
            }
            SetFormerObjWellDefinedProofByDef::OneSideInfinityIntervalObj(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified));
            }
            SetFormerObjWellDefinedProofByDef::SeqSet(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified));
            }
            _ => (),
        }
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::IteratedOperator(p),
        ..
    } = proof
    {
        use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef as P;
        return match p {
            P::Sum(p) => Some((&p.child_obj_well_defined, &p.requirement_fact_verified)),
            P::SumOfFiniteSet(p) => Some((&p.child_obj_well_defined, &p.requirement_fact_verified)),
            P::ProductOfFiniteSet(p) => {
                Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            P::Product(p) => Some((&p.child_obj_well_defined, &p.requirement_fact_verified)),
            _ => None,
        };
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FiniteSetStat(p),
        ..
    } = proof
    {
        use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FiniteSetStatObjWellDefinedProofByDef;
        return Some(match p {
            FiniteSetStatObjWellDefinedProofByDef::FiniteSetSize(p) => {
                (&p.child_obj_well_defined, &p.requirement_fact_verified)
            }
            FiniteSetStatObjWellDefinedProofByDef::FiniteSetMax(p) => {
                (&p.child_obj_well_defined, &p.requirement_fact_verified)
            }
            FiniteSetStatObjWellDefinedProofByDef::FiniteSetMin(p) => {
                (&p.child_obj_well_defined, &p.requirement_fact_verified)
            }
        });
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::StructObj(p)),
        ..
    } = proof
    {
        return Some((&p.child_obj_well_defined, &p.requirement_fact_verified));
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FunctionSpace(p),
        ..
    } = proof
    {
        match p {
            FunctionSpaceObjWellDefinedProofByDef::Preimage(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            FunctionSpaceObjWellDefinedProofByDef::PreimageSet(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            _ => {}
        }
    }
    if let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnRange(p)),
        ..
    } = proof
    {
        return Some((&p.child_obj_well_defined, &p.requirement_fact_verified));
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ComplexOperator(p),
        ..
    } = proof
    {
        return Some(match p {
            ComplexOperatorObjWellDefinedProofByDef::Conjugate(p) => {
                (&p.child_obj_well_defined, &p.requirement_fact_verified)
            }
            ComplexOperatorObjWellDefinedProofByDef::RealPart(p) => {
                (&p.child_obj_well_defined, &p.requirement_fact_verified)
            }
            ComplexOperatorObjWellDefinedProofByDef::ImaginaryPart(p) => {
                (&p.child_obj_well_defined, &p.requirement_fact_verified)
            }
            ComplexOperatorObjWellDefinedProofByDef::ComplexAbs(p) => {
                (&p.child_obj_well_defined, &p.requirement_fact_verified)
            }
        });
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::TrigOperator(p),
        ..
    } = proof
    {
        match p {
            TrigOperatorObjWellDefinedProofByDef::Sin(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            TrigOperatorObjWellDefinedProofByDef::Cos(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            TrigOperatorObjWellDefinedProofByDef::Tan(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            TrigOperatorObjWellDefinedProofByDef::Cot(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            TrigOperatorObjWellDefinedProofByDef::Sec(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            TrigOperatorObjWellDefinedProofByDef::Csc(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            TrigOperatorObjWellDefinedProofByDef::Arcsin(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            TrigOperatorObjWellDefinedProofByDef::Arccos(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            TrigOperatorObjWellDefinedProofByDef::Arctan(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            TrigOperatorObjWellDefinedProofByDef::Arccot(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
        }
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ExpLogOperator(p),
        ..
    } = proof
    {
        match p {
            ExpLogOperatorObjWellDefinedProofByDef::Exp(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            ExpLogOperatorObjWellDefinedProofByDef::Ln(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            ExpLogOperatorObjWellDefinedProofByDef::Log(p) => {
                return Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            _ => (),
        }
    }
    if let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Sqrt(
                proof,
            )),
        ..
    } = proof
    {
        return Some((
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
        ));
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::IntegerOperator(proof),
        ..
    } = proof
    {
        return match proof {
            IntegerOperatorObjWellDefinedProofByDef::Factorial(p) => {
                Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            IntegerOperatorObjWellDefinedProofByDef::Gcd(p) => {
                Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            IntegerOperatorObjWellDefinedProofByDef::Lcm(p) => {
                Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            IntegerOperatorObjWellDefinedProofByDef::Mod(p) => {
                Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            IntegerOperatorObjWellDefinedProofByDef::Quot(p) => {
                Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
        };
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ProductShape(proof),
        ..
    } = proof
    {
        return match proof {
            ProductShapeObjWellDefinedProofByDef::Cart(proof) => Some((
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            )),
            ProductShapeObjWellDefinedProofByDef::Tuple(proof) => Some((
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            )),
        };
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(proof),
        ..
    } = proof
    {
        return Some((
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
        ));
    }
    if let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::ListSet(proof)),
        ..
    } = proof
    {
        return Some((
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
        ));
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::Range(proof)),
        ..
    } = proof
    {
        return Some((
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
        ));
    }
    if let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::ClosedRange(proof)),
        ..
    } = proof
    {
        return Some((
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
        ));
    }
    if let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::FiniteSeqSet(proof)),
        ..
    } = proof
    {
        return Some((
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
        ));
    }
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetOperator(proof),
        ..
    } = proof
    {
        return match proof {
            SetOperatorObjWellDefinedProofByDef::SetMinus(p) => {
                Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            SetOperatorObjWellDefinedProofByDef::Intersect(p) => {
                Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            SetOperatorObjWellDefinedProofByDef::Union(p) => {
                Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            SetOperatorObjWellDefinedProofByDef::PowerSet(p) => {
                Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
            }
            _ => None,
        };
    }
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ArithmeticOperator(proof),
        ..
    } = proof
    else {
        return None;
    };
    match proof {
        ArithmeticOperatorObjWellDefinedProofByDef::Add(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Sub(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Mul(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Div(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Neg(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Abs(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Sign(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Floor(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Ceil(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Min(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Max(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Pow(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
    }
}

fn equality_cancellation_owner(rule: &InferEqualFactResult) -> Option<SourceOwner<'_>> {
    match rule {
        InferEqualFactResult::AdditiveCancellation(rule) => {
            Some(SourceOwner::AdditiveInference(rule))
        }
        InferEqualFactResult::SubtractiveCancellation(rule) => {
            Some(SourceOwner::SubtractiveInference(rule))
        }
        InferEqualFactResult::NonzeroFactorCancellation(rule) => {
            Some(SourceOwner::NonzeroFactorInference(rule))
        }
        InferEqualFactResult::CommonDenominatorCancellation(rule) => {
            Some(SourceOwner::CommonDenominatorInference(rule))
        }
        InferEqualFactResult::NonzeroNumeratorCancellation(rule) => {
            Some(SourceOwner::NonzeroNumeratorInference(rule))
        }
        InferEqualFactResult::PositiveRealPower(_) => None,
    }
}

fn cancellation_stages(
    owner: SourceOwner<'_>,
) -> Option<(Vec<&VerifyFactResult>, &StoreInferredFactResult)> {
    match owner {
        SourceOwner::AdditiveInference(rule) => Some((
            vec![
                &rule.left_in_c_proof,
                &rule.right_in_c_proof,
                &rule.common_in_c_proof,
            ],
            &rule.derived,
        )),
        SourceOwner::SubtractiveInference(rule) => Some((
            vec![
                &rule.left_in_c_proof,
                &rule.right_in_c_proof,
                &rule.common_in_c_proof,
            ],
            &rule.derived,
        )),
        SourceOwner::NonzeroFactorInference(rule) => Some((
            vec![
                &rule.left_in_c_proof,
                &rule.right_in_c_proof,
                &rule.common_in_c_proof,
                &rule.factor_nonzero_proof,
            ],
            &rule.derived,
        )),
        SourceOwner::CommonDenominatorInference(rule) => Some((
            vec![
                &rule.left_in_c_proof,
                &rule.right_in_c_proof,
                &rule.common_in_c_proof,
                &rule.denominator_nonzero_proof,
            ],
            &rule.derived,
        )),
        SourceOwner::NonzeroNumeratorInference(rule) => Some((
            vec![
                &rule.left_in_c_proof,
                &rule.right_in_c_proof,
                &rule.common_in_c_proof,
                &rule.numerator_nonzero_proof,
                &rule.left_denominator_nonzero_proof,
                &rule.right_denominator_nonzero_proof,
            ],
            &rule.derived,
        )),
        _ => None,
    }
}

fn stored_projection_has_fact(
    store: &StoreFactResult,
    id: FactId,
    actual: &Fact,
) -> Result<bool, LeanCompileError> {
    if let StoreFactResult::ForallFactWithIff(stored) = store {
        for direction in [&stored.forward, &stored.reverse] {
            if direction.fact_id == id {
                check_subject(&Fact::ForallFact(direction.fact.clone()), actual)?;
                return Ok(true);
            }
        }
    }
    for (stored_id, atomic) in store.atomic_components() {
        if stored_id == id {
            check_subject(&Fact::AtomicFact(atomic), actual)?;
            return Ok(true);
        }
    }
    Ok(false)
}

fn atomic_inference_future_ids(infer: &InferAtomicFactResult, before: usize) -> Vec<FactId> {
    match infer {
        InferAtomicFactResult::EqualFact(rules) => rules
            .iter()
            .skip(before)
            .flat_map(|rule| rule.stored_fact_ids())
            .collect(),
        _ => atomic_inference_stages(infer)
            .into_iter()
            .skip(before)
            .flat_map(|captured| captured.store.stored_fact_ids())
            .collect(),
    }
}

fn compound_inference_future_ids(store: &StoreFactAndInferResult, before: usize) -> Vec<FactId> {
    match &store.infer {
        Some(InferResult::AndFact(infer)) => infer
            .components
            .iter()
            .skip(before)
            .flat_map(|infer| infer.stored_fact_ids())
            .collect(),
        Some(InferResult::ChainFact(infer)) => {
            let mut ids = Vec::new();
            for captured in infer.adjacent_infers.iter().skip(before) {
                ids.push(captured.fact.fact_id());
                ids.extend(captured.infer.stored_fact_ids());
            }
            for closure in infer
                .transitive_closures
                .iter()
                .skip(before.saturating_sub(infer.adjacent_infers.len()))
            {
                ids.extend(closure.derived.stored_fact_ids());
            }
            ids
        }
        _ => Vec::new(),
    }
}

fn compound_inference_reference(
    store: &StoreFactAndInferResult,
    before: usize,
    id: FactId,
    actual: &Fact,
) -> Result<Option<String>, LeanCompileError> {
    if stored_projection_has_fact(&store.store, id, actual)? {
        return Ok(Some(format!("h_{}", id.value())));
    }
    match &store.infer {
        Some(InferResult::AndFact(infer)) => {
            for component in infer.components.iter().take(before) {
                if atomic_infer_has_fact(component, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
        }
        Some(InferResult::ChainFact(infer)) => {
            for edge in infer.adjacent_infers.iter().take(before) {
                if edge.fact.fact_id() == id {
                    check_subject(&edge.fact, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if atomic_infer_has_fact(&edge.infer, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            for closure in infer
                .transitive_closures
                .iter()
                .take(before.saturating_sub(infer.adjacent_infers.len()))
            {
                let derived = &closure.derived.store;
                if derived.primary_fact_id() == id {
                    check_store_subject(derived, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if stored_projection_has_fact(derived, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
        }
        _ => {}
    }
    Ok(None)
}

fn visit_compound_inference<T>(
    store: &StoreFactAndInferResult,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    match (&store.store, &store.infer) {
        (StoreFactResult::AndFact(stored), Some(InferResult::AndFact(inferred))) => {
            for (index, infer) in inferred
                .components
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let Some(component) = stored.components.get(index) else {
                    return Err(LeanCompileError::unsupported("And/StoreArity"));
                };
                let fact = Fact::AtomicFact(component.fact.clone());
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                let current = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::AtomicInference(&fact, infer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&current, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        (StoreFactResult::ChainFact(_), Some(InferResult::ChainFact(inferred))) => {
            let head = inferred.adjacent_infers.len();
            for (index, closure) in inferred
                .transitive_closures
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                let current =
                    SourcePosition::new(Some(&prior), SourceOwner::ChainClosure(closure), 2);
                if let Some(value) = visit_owner(&current, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            for (index, edge) in inferred
                .adjacent_infers
                .iter()
                .take(position.before.min(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                let current = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::AtomicInference(&edge.fact, &edge.infer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&current, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        _ => return Err(LeanCompileError::unsupported("Compound/InferenceFamily")),
    }
    Ok(None)
}

fn inference_fact_reference(position: &SourcePosition<'_>, id: FactId) -> String {
    let name = format!("h_{}", id.value());
    if position.is_local() {
        name
    } else {
        position.context_application(&name)
    }
}

fn statement_known_application(
    statement: &ExecStmtResult,
) -> Option<&SearchProofByKnownForallFact> {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) = statement else {
        return None;
    };
    match &proof.verify_result {
        VerifyFactResult::Equality(proof) => match proof.as_ref() {
            VerifyEqualityResult::Success(proof) => match &proof.searched_proof {
                EqualFactSearchedProof::ByKnownForallFact(known) => Some(known.as_ref()),
                EqualFactSearchedProof::ByKnownForallFactViaSymmetry(known) => {
                    Some(&known.known_forall)
                }
                _ => None,
            },
            _ => None,
        },
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => match &proof.searched_proof {
                AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(known) => Some(known),
                _ => None,
            },
            _ => None,
        },
        VerifyFactResult::ChainFact(proof)=>match proof.as_ref() {
            crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult::Success(proof)=>proof.known_forall.as_ref(),
            _=>None,
        },
        VerifyFactResult::AndFact(proof)=>match proof.as_ref() {
            crate::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactResult::Success(proof)=>proof.known_forall.as_ref(),
            _=>None,
        },
        _=>None,
    }
}

fn statement_forall_constructor_owner(
    statement: &ExecStmtResult,
    id: FactId,
) -> Option<SourceOwner<'_>> {
    if let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = statement {
        if let (
            VerifyFactResult::ForallFactWithIff(result),
            StoreFactResult::ForallFactWithIff(stored),
        ) = (
            &statement.verify_result,
            &statement.store_and_infer_result.store,
        ) {
            let VerifyForallFactWithIffResult::Success(proof) = result.as_ref() else {
                return None;
            };
            let direction = if stored.forward.fact_id == id {
                &proof.then_implies_iff
            } else if stored.reverse.fact_id == id {
                &proof.iff_implies_then
            } else {
                return None;
            };
            let VerifyFactResult::ForallFact(result) = direction else {
                return None;
            };
            return match result.as_ref() {
                VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(
                    proof,
                )) => Some(SourceOwner::Forall(proof)),
                VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(
                    proof,
                )) => Some(SourceOwner::ForallWD(&proof.fact, &proof.well_defined)),
                _ => None,
            };
        }
    }
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
            crate::execute::ExecHaveFnByForallExistUniqueStmtResult::Success(p),
        )) if p.property.primary_fact_id() == id => {
            let (StoreFactResult::ForallFact(stored), FactWellDefinedProof::ForallFact(wd)) =
                (&p.property.store, &p.property_well_defined)
            else {
                return None;
            };
            Some(SourceOwner::ForallWD(&stored.fact, wd))
        }
        ExecStmtResult::By(ExecByStmtResult::Induc(ExecByInducStmtResult::Success(proof)))
            if proof.stored.primary_fact_id() == id =>
        {
            Some(SourceOwner::Induction(proof.into()))
        }
        ExecStmtResult::By(ExecByStmtResult::StrongInduc(
            crate::execute::execute_by_stmt::ExecByStrongInducStmtResult::Success(proof),
        )) if proof.stored.primary_fact_id() == id => Some(SourceOwner::Induction(proof.into())),
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof))
            if proof.store_and_infer_result.primary_fact_id() == id =>
        {
            let VerifyFactResult::ForallFact(proof) = &proof.verify_result else {
                return None;
            };
            match proof.as_ref() {
                VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(
                    proof,
                )) if proof.fact.fact_id == id => Some(SourceOwner::Forall(proof)),
                VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(
                    proof,
                )) if proof.fact.fact_id == id => {
                    Some(SourceOwner::ForallWD(&proof.fact, &proof.well_defined))
                }
                _ => None,
            }
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(proof),
        )) if proof.stored.primary_fact_id() == id => {
            let (
                Fact::ForallFact(fact),
                VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(wd)),
            ) = (&proof.statement.fact, &proof.goal_wd)
            else {
                return None;
            };
            (fact.fact_id == id).then_some(SourceOwner::ForallWD(fact, wd))
        }
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Success(proof),
        )) if proof.stored.primary_fact_id() == id => {
            let (
                Fact::ForallFact(fact),
                VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(wd)),
            ) = (&proof.statement.fact, &proof.goal_wd)
            else {
                return None;
            };
            (fact.fact_id == id).then_some(SourceOwner::ForallWD(fact, wd))
        }
        _ => None,
    }
}

fn visit_forall_constructor<T>(
    owner: SourceOwner<'_>,
    then_index: usize,
    pattern: &Obj,
    declaration: &SourcePosition<'_>,
    callback: &mut impl FnMut(
        &ForallFact,
        &IntroduceTypedParametersResult,
        &[AssumeDomFactResult],
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
        &SourcePosition<'_>,
    ) -> Result<T, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    // The selected property's formation ran after the function membership was
    // published. Its factory may cite that membership, but not the later
    // property/uniqueness stores or its hypothetical input facts globally.
    let declaration = match (declaration.owner, owner) {
        (
            SourceOwner::Statement(ExecStmtResult::Definition(
                ExecDefinitionStmtResult::HaveFnByForallExistUnique(
                    crate::execute::ExecHaveFnByForallExistUniqueStmtResult::Success(p),
                ),
            )),
            SourceOwner::ForallWD(fact, _),
        ) if p.property.primary_fact_id() == fact.fact_id => SourcePosition {
            before: 3,
            ..*declaration
        },
        _ => *declaration,
    };
    let declaration = &declaration;
    let (fact, introduced, assumed) = match owner {
        SourceOwner::Induction(proof) => {
            let StoreFactResult::ForallFact(source) = &proof.stored.store else {
                return Err(LeanCompileError::unsupported("WD/InductionForallStore"));
            };
            (
                &source.fact,
                proof.introduced_parameter,
                std::slice::from_ref(proof.goal_domain),
            )
        }
        SourceOwner::Forall(proof) => (
            &proof.fact,
            &proof.introduced_params,
            proof.assumed_dom_facts.as_slice(),
        ),
        SourceOwner::ForallWD(fact, proof) => (
            fact,
            &proof.introduced_params,
            proof.assumed_dom_facts.as_slice(),
        ),
        _ => return Err(LeanCompileError::unsupported("WD/CalleeSourceOwner")),
    };
    let selected = fact
        .then_facts
        .get(then_index)
        .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeThenIndex"))?;
    let header = SourcePosition::new(
        Some(declaration),
        owner,
        parameter_count(&fact.typed_parameters.groups) + assumed.len(),
    );
    let mut checked = |evidence: SourceConstructor<'_>, site: &SourcePosition<'_>| {
        let SourceConstructor::Checked(wd) = evidence else {
            return Ok(None);
        };
        if wd.obj().ir() == pattern.ir() {
            callback(fact, introduced, assumed, wd, site, declaration).map(Some)
        } else {
            Ok(None)
        }
    };
    match owner {
        SourceOwner::Induction(proof) => {
            if proof.goals.get(then_index) != Some(&selected.clone().into()) {
                return Err(LeanCompileError::new(
                    "WD/InductionGoalSubject",
                    "The stored induction conclusion differs from its original goal formation.",
                ));
            }
            let VerifyFactWellDefinedResult::Success(captured) = proof
                .goals_wd
                .get(then_index)
                .ok_or_else(|| LeanCompileError::unsupported("WD/InductionGoalCapture"))?
            else {
                return Err(LeanCompileError::unsupported(
                    "WD/InductionFailedGoalFormation",
                ));
            };
            let formation =
                SourcePosition::new(Some(&header), SourceOwner::FactWD(captured), usize::MAX);
            visit_fact_formation(
                captured,
                usize::MAX,
                &formation,
                &mut checked,
                &mut |_, _| Ok(None),
            )
        }
        SourceOwner::Forall(proof) => {
            let result = &proof
                .proved_then_facts
                .get(then_index)
                .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeThenCapture"))?
                .verify_result;
            if verified_subject(result) != Some(selected.clone().into()) {
                return Err(LeanCompileError::unsupported("WD/CalleeThenSubject"));
            }
            let inner_application=match result {
                VerifyFactResult::ChainFact(result)=>match result.as_ref() {
                    crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult::Success(proof)=>proof.known_forall.as_ref(),
                    _=>None,
                },
                VerifyFactResult::AndFact(result)=>match result.as_ref() {
                    crate::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactResult::Success(proof)=>proof.known_forall.as_ref(),
                    _=>None,
                },
                _=>None,
            };
            if let Some(application) = inner_application {
                // The factory publishes this header's bindings only. Reuse
                // original inner formation, but not its call-local truth IDs.
                let formation = SourcePosition::new(
                    Some(&header),
                    SourceOwner::KnownApplication(application),
                    0,
                );
                return visit_owner(&formation, &mut checked, &mut |_, _| Ok(None));
            }
            let scope = SourcePosition::new(Some(&header), SourceOwner::Verify(result), usize::MAX);
            // Exact selected then formation only. The callee's then stores and
            // inferred truth remain outside the header/dom closure.
            visit_verify_formation(result, usize::MAX, &scope, &mut checked, &mut |_, _| {
                Ok(None)
            })
        }
        SourceOwner::ForallWD(_, proof) => {
            let wd = proof
                .then
                .get(then_index)
                .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeThenCapture"))?;
            let formation = SourcePosition::new(Some(&header), SourceOwner::FactWD(wd), usize::MAX);
            visit_fact_formation(wd, usize::MAX, &formation, &mut checked, &mut |_, _| {
                Ok(None)
            })
        }
        _ => unreachable!(),
    }
}

fn known_application_requirements(
    proof: &SearchProofByKnownForallFact,
) -> Vec<(&Fact, &VerifyFactResult)> {
    proof
        .instantiation_requirements
        .param_type_requirements
        .iter()
        .map(|item| (&item.type_fact, &item.proof))
        .chain(
            proof
                .instantiation_requirements
                .dom_facts
                .iter()
                .zip(&proof.instantiation_requirements.proof_of_dom_facts),
        )
        .collect()
}

fn order_bound_stages(
    rule: OrderBoundInference<'_>,
) -> Option<(Vec<&VerifyFactResult>, &StoreInferredFactResult)> {
    match rule {
        OrderBoundInference::WeakInteger(rule) => Some((
            vec![&rule.integer_proof, &rule.bound_nonnegative_proof],
            &rule.derived,
        )),
        OrderBoundInference::Strict(rule) => {
            Some((vec![&rule.bound_nonnegative_proof], &rule.derived))
        }
    }
}

#[cfg(test)]
#[path = "../../tests/unit/compile_to_lean/geo_scope_cursor/tests.rs"]
mod geo_scope_cursor_tests;

fn function_argument_scope(
    proof: &ObjWellDefinedProof,
) -> Option<&crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjArgumentScope>
{
    match proof {
        ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } => call.argument_scope.as_ref(),
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(
                    access,
                )),
            ..
        } => access.argument_scope.as_ref(),
        _ => None,
    }
}

// This compares host-constructor shape, not mathematical equality. Arithmetic
// variants and alternative signatures are deliberately not interchangeable.
fn same_call_constructor(
    left: &crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof,
    right: &crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof,
) -> bool {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
    let (
        Some(FnObjDomainFnSetEvidence::InFunctionSet {
            fn_set: a,
            fact_id: a_id,
            ..
        }),
        Some(FnObjDomainFnSetEvidence::InFunctionSet {
            fn_set: b,
            fact_id: b_id,
            ..
        }),
    ) = (&left.domain_fn_set, &right.domain_fn_set)
    else {
        return false;
    };
    if a != b
        || a_id != b_id
        || left.child_obj_well_defined.len() != right.child_obj_well_defined.len()
    {
        return false;
    }
    left.child_obj_well_defined
        .iter()
        .zip(&right.child_obj_well_defined)
        .all(|(a, b)| same_wd_constructor(a, b))
}

// This is host-constructor compatibility, not a new mathematical proof rule.
// Distinct WD proofs may certify the same representation; selected function
// signatures and every compound child's representation must still agree.
fn same_wd_constructor(left: &ObjWellDefinedProof, right: &ObjWellDefinedProof) -> bool {
    if left.obj() != right.obj() {
        return false;
    }
    if std::ptr::eq(left, right)
        || matches!(
            left.obj(),
            Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
        )
    {
        return true;
    }
    match (left, right) {
        (
            ObjWellDefinedProof::ByKnown { wd_id: a, .. },
            ObjWellDefinedProof::ByKnown { wd_id: b, .. },
        ) => a == b,
        (
            ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(a),
                ..
            },
            ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(b),
                ..
            },
        ) => same_call_constructor(a, b),
        (
            ObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::ExpLogOperator(
                        ExpLogOperatorObjWellDefinedProofByDef::Sqrt(a),
                    ),
                ..
            },
            ObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::ExpLogOperator(
                        ExpLogOperatorObjWellDefinedProofByDef::Sqrt(b),
                    ),
                ..
            },
        ) => {
            a.child_obj_well_defined.len() == 1
                && b.child_obj_well_defined.len() == 1
                && same_wd_constructor(&a.child_obj_well_defined[0], &b.child_obj_well_defined[0])
        }
        (
            ObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::SetFormer(
                        SetFormerObjWellDefinedProofByDef::FiniteSeqSet(a),
                    ),
                ..
            },
            ObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::SetFormer(
                        SetFormerObjWellDefinedProofByDef::FiniteSeqSet(b),
                    ),
                ..
            },
        ) => {
            a.child_obj_well_defined.len() == 2
                && b.child_obj_well_defined.len() == 2
                && a.child_obj_well_defined
                    .iter()
                    .zip(&b.child_obj_well_defined)
                    .all(|(a, b)| same_wd_constructor(a, b))
        }
        (
            ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::IntegerOperator(a),
                ..
            },
            ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::IntegerOperator(b),
                ..
            },
        ) if std::mem::discriminant(a) == std::mem::discriminant(b) => {
            let (Some((a, _)), Some((b, _))) = (arithmetic_stages(left), arithmetic_stages(right))
            else {
                return false;
            };
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| same_wd_constructor(a, b))
        }
        (
            ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::ArithmeticOperator(a),
                ..
            },
            ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::ArithmeticOperator(b),
                ..
            },
        ) if std::mem::discriminant(a) == std::mem::discriminant(b) => {
            let (Some((a, _)), Some((b, _))) = (arithmetic_stages(left), arithmetic_stages(right))
            else {
                return false;
            };
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| same_wd_constructor(a, b))
        }
        _ => false,
    }
}

fn enumeration_outcome(
    p: &crate::execute::execute_by_stmt::EnumerateAssignmentSuccess,
) -> (
    &[AssumeDomFactResult],
    &[ExecStmtResult],
    &[ProveAndStoreThenFactResult],
) {
    use crate::execute::execute_by_stmt::EnumerateAssignmentOutcome;
    match &p.outcome {
        EnumerateAssignmentOutcome::Proved {
            premise_assumptions,
            proof_steps,
            then_proofs,
        } => (premise_assumptions, proof_steps, then_proofs),
        EnumerateAssignmentOutcome::Skipped {
            premise_assumptions,
            ..
        } => (premise_assumptions, &[], &[]),
    }
}

pub(in crate::compile_to_lean) fn enumeration_statement(
    statement: &ExecStmtResult,
) -> Option<(
    &VerifyFactWellDefinedResult,
    &[crate::execute::execute_by_stmt::EnumerateAssignmentSuccess],
    &StoreFactAndInferResult,
)> {
    use crate::execute::execute_by_stmt::{
        ExecByEnumerateFiniteSetStmtResult, ExecByForStmtResult,
    };
    match statement {
        ExecStmtResult::By(ExecByStmtResult::EnumerateFiniteSet(
            ExecByEnumerateFiniteSetStmtResult::Success(p),
        )) => Some((&p.goal_wd, &p.assignments, &p.stored)),
        ExecStmtResult::By(ExecByStmtResult::For(ExecByForStmtResult::Success(p))) => {
            Some((&p.goal_wd, &p.assignments, &p.stored))
        }
        _ => None,
    }
}
