use crate::execute::execute_witness_stmt::{ExecWitnessStmtResult, ExecWitnessExistFactStmtResult, ExecWitnessExistFactStmtSuccessResult, ExecWitnessAtomicFactStmtResult, ExecWitnessAtomicFactStmtSuccessResult};
use crate::execute::execute_witness_stmt::{WitnessExistAmbientSuccess, WitnessExistObligationSuccess};
use crate::execute::execute_by_stmt::{ExecByContraStmtResult, ExecByContraStmtSuccess, ExecByCasesStmtResult, ByCasesBranchSuccess, ByCasesBranchClosingSuccess, ByContradictionClosingSuccess};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef;
use crate::execute::{ExecObtainObjFromExistFactStmtResult, ObtainExistVerifySuccess};
use crate::execute::ExecObtainObjFromAtomicFactStmtResult;
use crate::execute::execute_proof_block_stmt::{ExecClaimBodyProof, ExecClaimStmtResult, ExecClaimStmtSuccess, ExecProofBlockStmtResult};
use crate::store_fact_and_infer::{InferInFactResult, InferStrictLowerBoundPositiveResult, InferWeakIntegerLowerBoundInNResult};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{ProductShapeObjWellDefinedProofByDef, SetBuilderObjWellDefinedProof, SetFormerObjWellDefinedProofByDef};
use super::helper::verified_subject;
use super::LeanCompileError;
use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByDefStmtSuccess, ExecByInducStmtResult, ExecByInducStmtSuccess, ByInducCaseSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::UserDefinedPropDefinitionProof;
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::execute::{ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult, InducCaseSuccess, InducCasesDisjointSuccess, InducCaseBodySuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_by_induc::ByUnfoldHaveFnByInducApplicationObjectDefinitionProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::{FunctionBodyNormalizationProof, AnonymousFunctionBodyExpansionProof, FunctionBodyExpansionProof};
use crate::execute::{ExecDefPropStmtResult, ExecDefPropStmtSuccessResult};
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
    Statement(&'a ExecStmtResult),
    Verify(&'a VerifyFactResult),
    AtomicVerify(&'a VerifyAtomicExceptEqualityFactSuccess),
    WD(&'a ObjWellDefinedProof),
    // This constructor's first `usize` child/requirement stages have already
    // been emitted as lexical lets/haves. Source order still controls visibility.
    WDLocals(&'a ObjWellDefinedProof, usize),
    FormedSubjects(&'a VerifyFactResult, &'a StoreFactAndInferResult),
    SetBuilder(&'a SetBuilder, &'a SetBuilderObjWellDefinedProof),
    Named(&'a ExecDefThmStmtSuccess),
    Claim(&'a ExecClaimStmtSuccess),
    Forall(&'a VerifyForallFactSuccess),
    EmptyForall(&'a crate::execute::execute_fact_stmt::verify_forall_fact::VerifyEmptyParameterDomainForallProof),
    ForallWD(&'a ForallFact, &'a ForallFactWellDefinedProof),
    // Params, then each sequential body WD/assumption pair.
    ExistWD(&'a PlainExistFact, &'a ExistShapedFactWellDefinedProof),
    // Local stages only: params, equality stores, proof steps, body checks, uniqueness.
    WitnessExist(&'a ExecWitnessExistFactStmtSuccessResult),
    WitnessAtomic(&'a ExecWitnessAtomicFactStmtSuccessResult),
    // Assumption WD, assumption store, proof steps, closing checks/stores.
    Contra(&'a ExecByContraStmtSuccess),
    CasesBranch(&'a ByCasesBranchSuccess),
    KnownForall(&'a VerifyKnownForallFactProof),
    KnownApplication(&'a SearchProofByKnownForallFact),
    CalleeInstance(&'a SearchProofByKnownForallFact),
    Call(&'a ExecByThmStmtSuccess),
    ThmRelease(&'a ExecReleaseThmStmtSuccess),
    HaveEqualType(&'a ExecHaveObjEqualStmtSuccessResult),
    AtomicWD(&'a AtomicFactWellDefinedProof),
    FactWD(&'a FactWellDefinedProof),
    InferredStore(&'a StoreFactResult),
    HaveGroup(&'a ParamTypeWellDefinedProof, &'a ParamTypeFactCheckResult),
    ParamTypeWD(&'a ParamTypeWellDefinedProof),
    PropDefinition(&'a ExecDefPropStmtSuccessResult),
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
    FunctionDefinitionRewrite(&'a [AnonymousFunctionBodyExpansionProof]),
    RecursiveFunction(&'a ExecHaveFnByInducStmtSuccessResult),
    RecursiveCase(&'a InducCaseSuccess),
    RecursiveDisjoint(&'a InducCasesDisjointSuccess),
    RecursiveUnfold(&'a ByUnfoldHaveFnByInducApplicationObjectDefinitionProof),
    Induction(&'a ExecByInducStmtSuccess),
    InductionCase(&'a ExecByInducStmtSuccess, &'a ByInducCaseSuccess),
}

// Constructor evidence comes from a checked source expression or a named infer
// rule's actual conclusion store. The latter does not invent a Verify WD result.
#[derive(Clone, Copy)]
enum SourceConstructor<'a> {
    Checked(&'a ObjWellDefinedProof),
    Inferred(&'a StoreFactResult),
}

impl<'a> SourcePosition<'a> {
    pub fn wd_child_name(&self, index: usize) -> String {
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

    fn bound_child(&self, matches: impl Fn(&ObjWellDefinedProof) -> bool) -> Option<String> {
        let mut cursor = Some(self);
        while let Some(position) = cursor {
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

    /// Only already completed top-level ordinary-have introductions are arguments.
    pub fn context_parameters(&self) -> Vec<(&'a BoundName, Option<&'a Obj>, FactId)> {
        let mut parameters = Vec::new();
        let mut position = Some(self);
        while let Some(current) = position {
            if let SourceOwner::Run(run) = current.owner {
                for statement in run.statement_results.iter().take(current.before) {
                    if let Some(proof) = ordinary_have(statement) {
                        append_have_parameters(proof, usize::MAX, &mut parameters);
                    }
                }
                break;
            }
            position = current.parent;
        }
        let mut position = Some(self);
        while let Some(current) = position {
            if let SourceOwner::Statement(statement) = current.owner {
                if current
                    .parent
                    .map(|p| matches!(p.owner, SourceOwner::Run(_)))
                    .unwrap_or(false)
                {
                    if let Some(proof) = ordinary_have(statement) {
                        append_have_parameters(proof, current.before, &mut parameters);
                    }
                }
            }
            position = current.parent;
        }
        parameters
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
        application(name, &arguments)
    }

    pub fn is_local(&self) -> bool {
        let mut position = Some(self);
        while let Some(current) = position {
            match current.owner {
                SourceOwner::Named(_)
                | SourceOwner::Claim(_)
                | SourceOwner::Forall(_)
                | SourceOwner::EmptyForall(_)
                | SourceOwner::ExistWD(_, _)
                | SourceOwner::WitnessExist(_)
                | SourceOwner::WitnessAtomic(_)
                | SourceOwner::Contra(_)
                | SourceOwner::CasesBranch(_)
                | SourceOwner::ForallWD(_, _)
                | SourceOwner::KnownForall(_)
                | SourceOwner::Call(_)
                | SourceOwner::ThmRelease(_)
                | SourceOwner::HaveEqualType(_) => return true,
                SourceOwner::RecursiveFunction(_)
                | SourceOwner::RecursiveCase(_)
                | SourceOwner::RecursiveDisjoint(_) => return true,
                SourceOwner::Induction(_) | SourceOwner::InductionCase(_, _) => return true,
                SourceOwner::PropDefinition(_)
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

    pub fn visible_theorem(
        &self,
        name: &str,
    ) -> Result<(&'a DefThmStmt, Self, usize), LeanCompileError> {
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
                    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                        ExecDefThmStmtResult::Success(p),
                    )) = statement
                    {
                        if p.statement.name == name {
                            return Ok((
                                &p.statement,
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
            "ByThm/Producer",
            "The named theorem has no prior declaration in the active source results.",
        ))
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
                SourceOwner::Claim(p) => Some(p.local_env.as_ref()),
                SourceOwner::Forall(p) => Some(p.local_env.as_ref()),
                SourceOwner::EmptyForall(p) => Some(p.local_env.as_ref()),
                SourceOwner::ForallWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::ExistWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::WitnessExist(p) => Some(p.local_env.as_ref()),
                SourceOwner::WitnessAtomic(p) => Some(p.local_env.as_ref()),
                SourceOwner::Contra(p) => Some(p.local_env.as_ref()),
                SourceOwner::CasesBranch(p) => Some(p.local_env.as_ref()),
                SourceOwner::KnownForall(p) => Some(p.well_defined.local_env.as_ref()),
                SourceOwner::Call(p) => Some(p.local_env.as_ref()),
                SourceOwner::ThmRelease(p) => Some(p.local_env.as_ref()),
                SourceOwner::HaveEqualType(p) => Some(p.type_local_env.as_ref()),
                SourceOwner::PropDefinition(p) => Some(p.local_env.as_ref()),
                SourceOwner::ByDef(p) => Some(p.local_env.as_ref()),
                SourceOwner::SetBuilder(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::WD(p) | SourceOwner::WDLocals(p, _) => {
                    function_binder(p).map(|(_, _, _, _, env)| env)
                }
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
                SourceOwner::Claim(p) => Some(p.local_env.as_ref()),
                SourceOwner::Forall(p) => Some(p.local_env.as_ref()),
                SourceOwner::EmptyForall(p) => Some(p.local_env.as_ref()),
                SourceOwner::ForallWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::ExistWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::WitnessExist(p) => Some(p.local_env.as_ref()),
                SourceOwner::WitnessAtomic(p) => Some(p.local_env.as_ref()),
                SourceOwner::Contra(p) => Some(p.local_env.as_ref()),
                SourceOwner::CasesBranch(p) => Some(p.local_env.as_ref()),
                SourceOwner::KnownForall(p) => Some(p.well_defined.local_env.as_ref()),
                SourceOwner::Call(p) => Some(p.local_env.as_ref()),
                SourceOwner::ThmRelease(p) => Some(p.local_env.as_ref()),
                SourceOwner::HaveEqualType(p) => Some(p.type_local_env.as_ref()),
                SourceOwner::PropDefinition(p) => Some(p.local_env.as_ref()),
                SourceOwner::ByDef(p) => Some(p.local_env.as_ref()),
                SourceOwner::SetBuilder(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::WD(p) | SourceOwner::WDLocals(p, _) => {
                    function_binder(p).map(|(_, _, _, _, env)| env)
                }
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
            if let SourceOwner::PropInference(store) = current.owner {
                if store.primary_fact_id() == id {
                    local_primary_is_stored = true;
                }
            }
            if matches!(
                current.owner,
                SourceOwner::ExistWD(_, _)
                    | SourceOwner::WitnessExist(_)
                    | SourceOwner::WitnessAtomic(_)
                    | SourceOwner::Contra(_)
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
                    return Err(LeanCompileError::new(
                        "Scope/FutureProducer",
                        "The exact local store is after this original source stage.",
                    ));
                }
                local_primary_is_stored |= present;
            }
            if let SourceOwner::Statement(statement) = current.owner {
                if witness_statement(statement).is_some()
                    || obtain_parts(statement).is_some()
                    || matches!(
                        statement,
                        ExecStmtResult::By(
                            ExecByStmtResult::Contra(_) | ExecByStmtResult::Cases(_)
                        )
                    )
                {
                    if !local_primary_is_stored
                        && statement_reference(statement, id, actual, None, usize::MAX)?.is_some()
                        && statement_reference(statement, id, actual, None, current.before)?
                            .is_none()
                    {
                        return Err(LeanCompileError::new(
                            "Scope/FutureReturn",
                            "The output store is after this original statement stage.",
                        ));
                    }
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
            if let SourceOwner::Call(proof) = current.owner {
                if proof
                    .type_stores
                    .iter()
                    .skip(current.before)
                    .any(|store| store.stored_fact_ids().contains(&id))
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
                {
                    return Err(LeanCompileError::new("ByThm/FutureProducer", "The returned package is after all conclusion formation and its original store stage."));
                }
            }
            if let SourceOwner::ThmRelease(proof) = current.owner {
                if proof
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
                        .any(|store| store.stored_fact_ids().contains(&id))
                {
                    return Err(LeanCompileError::new("ReleaseThm/FutureProducer", "The cited type/domain store or caller return is after this original invocation stage."));
                }
            }
            if let SourceOwner::Statement(ExecStmtResult::ReleaseAndExpand(
                ExecReleaseAndExpandStmtResult::Thm(ExecReleaseThmStmtResult::Success(proof)),
            )) = current.owner
            {
                if proof
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
                    | SourceOwner::Contra(_)
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
        visit_visible(
            self,
            &mut |evidence, position| {
                let SourceConstructor::Checked(proof) = evidence else {
                    return Ok(None);
                };
                if matches!(proof, ObjWellDefinedProof::ByDef { obj, .. } if obj.ir() == object.ir())
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
                    } else if let Some(term) =
                        projected_wd_child(proof, term, &|child| child.obj() == object)
                    {
                        return Ok(Some(term));
                    }
                }
            }
            Ok(None)
        }
        let in_statement = |statement: &ExecStmtResult, producer: &SourcePosition<'_>| {
            if let ExecStmtResult::Fact(ExecFactStmtResult::Success(result)) = statement {
                in_result(
                    &result.verify_result,
                    &result.store_and_infer_result,
                    producer,
                    self,
                    object,
                    id,
                )
            } else {
                Ok(None)
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
                _ => None,
            };
            if let Some((statements, head)) = statements {
                for (index, statement) in statements
                    .iter()
                    .take(position.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    let prior = SourcePosition {
                        before: head + index,
                        ..*position
                    };
                    let producer =
                        SourcePosition::new(Some(&prior), SourceOwner::Statement(statement), 1);
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
        visit_visible(
            self,
            &mut |evidence, position| {
                let SourceConstructor::Inferred(store) = evidence else {
                    return Ok(None);
                };
                if store.atomic_components().iter().any(|(_, fact)| {
                    atomic_fact_args_ref(fact)
                        .iter()
                        .any(|arg| arg.ir() == object.ir())
                }) {
                    callback(store, position).map(Some)
                } else {
                    Ok(None)
                }
            },
            &mut |_, _| Ok(None),
        )
    }

    pub fn with_visible_nonzero<T>(
        &self,
        object: &Obj,
        callback: &mut impl FnMut(FactId, &SourcePosition<'_>) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let inferred = visit_visible(
            self,
            &mut |evidence, producer| {
                let SourceConstructor::Inferred(store) = evidence else {
                    return Ok(None);
                };
                for (id, fact) in store.atomic_components() {
                    if matches!(&fact, AtomicFact::NotEqualFact(f)
                        if f.left.ir() == object.ir() && super::helper::is_exact_zero(&f.right))
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
        visit_visible(self, &mut |_, _| Ok(None), &mut |proof, producer| {
            if let Some(Fact::AtomicFact(AtomicFact::NotEqualFact(fact))) = verified_subject(proof)
            {
                if fact.left.ir() == object.ir() && super::helper::is_exact_zero(&fact.right) {
                    return callback(fact.fact_id, producer).map(Some);
                }
            }
            Ok(None)
        })
    }

    pub fn with_visible_membership<T>(
        &self,
        object: &Obj,
        set: &Obj,
        callback: &mut impl FnMut(&VerifyFactResult, &SourcePosition<'_>) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        visit_visible(
            self,
            &mut |_, _| Ok(None),
            &mut |proof, position| match verified_subject(proof) {
                Some(Fact::AtomicFact(AtomicFact::InFact(f)))
                    if f.element.ir() == object.ir() && f.set.ir() == set.ir() =>
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
                        proof @ (ExecDefineObjStmtResult::ObtainObjFromExistFact(
                            ExecObtainObjFromExistFactStmtResult::Success(_),
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
                    proof @ (ExecDefineObjStmtResult::ObtainObjFromExistFact(
                        ExecObtainObjFromExistFactStmtResult::Success(_),
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

fn append_have_parameters<'a>(
    proof: &'a ExecHaveObjInNonemptySetStmtSuccessResult,
    before: usize,
    out: &mut Vec<(&'a BoundName, Option<&'a Obj>, FactId)>,
) {
    let mut index = 0;
    for group in &proof.statement.param_def.groups {
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
            if let Some(store) = proof
                .store_and_infer_result
                .store_and_infer_results
                .get(index)
            {
                out.push((parameter, carrier, store.primary_fact_id()));
            }
            index += 1;
        }
    }
}

fn context_arguments_before(run: &RunLitexCodeResult, before: usize) -> Vec<String> {
    let mut arguments = Vec::new();
    for statement in run.statement_results.iter().take(before) {
        if let Some(proof) = ordinary_have(statement) {
            let mut parameters = Vec::new();
            append_have_parameters(proof, usize::MAX, &mut parameters);
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

fn application(name: &str, arguments: &[String]) -> String {
    if arguments.is_empty() {
        format!("({name} (M := M))")
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
        format!("({name} (M := M) {arguments})")
    }
}

fn ordinary_have(statement: &ExecStmtResult) -> Option<&ExecHaveObjInNonemptySetStmtSuccessResult> {
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
                    ParamType::Set(_) => None,
                    _ => return None,
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
fn local_steps(owner: SourceOwner<'_>) -> Option<(&[ExecStmtResult], usize)> {
    match owner {
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
        SourceOwner::Contra(p) => Some((&p.proof_steps, 2)),
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

fn obtain_parts(statement: &ExecStmtResult) -> Option<(&[BoundName], &StoreHaveObjAndInferResult)> {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromExistFact(
                ExecObtainObjFromExistFactStmtResult::Success(p),
            ),
        )) => Some((&p.statement.equal_tos, &p.store_and_infer_result)),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                ExecObtainObjFromAtomicFactStmtResult::Success(p),
            ),
        )) => Some((&p.statement.equal_tos, &p.store_and_infer_result)),
        _ => None,
    }
}

fn parameter_in_statement(
    statement: &ExecStmtResult,
    before: usize,
    id: IdentifierId,
) -> Option<(&BoundName, Option<&Obj>, &StoreFactAndInferResult)> {
    if let Some(have) = ordinary_have(statement) {
        return parameter_from_groups(
            &have.statement.param_def.groups,
            &have.store_and_infer_result.store_and_infer_results,
            before,
            id,
        );
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
        SourceOwner::ForallWD(fact, p) => parameter_from_groups(
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
        StoreFactResult::AndFact(p) => Fact::AndFact(p.fact.clone()),
        StoreFactResult::ChainFact(p) => Fact::ChainFact(p.fact.clone()),
        StoreFactResult::OrFact(p) => Fact::OrFact(p.fact.clone()),
        StoreFactResult::ExistShapedFact(p) => crate::ast::fact::exist_shaped_fact_to_fact(&p.fact),
        _ => return Err(LeanCompileError::unsupported("Store/Compound")),
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
        InferAtomicFactResult::HasFunctionLimitFact(_)
        | InferAtomicFactResult::NotHasFunctionLimitFact(_)
        | InferAtomicFactResult::HasSequenceLimitFact(_)
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
                InferInFactResult::CartCoordinates(_) | InferInFactResult::ClosedRange(_) => {
                    r.stored_conclusions()
                }
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
        InferAtomicFactResult::IsSetFact(_)
        | InferAtomicFactResult::IsNonemptySetFact(_)
        | InferAtomicFactResult::IsFiniteSetFact(_)
        | InferAtomicFactResult::SubsetFact(_)
        | InferAtomicFactResult::SupersetFact(_)
        | InferAtomicFactResult::ProperSubsetFact(_)
        | InferAtomicFactResult::ProperSupersetFact(_)
        | InferAtomicFactResult::PrimeFact(_)
        | InferAtomicFactResult::CoprimeFact(_)
        | InferAtomicFactResult::DvdFact(_)
        | InferAtomicFactResult::InjectiveFact(_)
        | InferAtomicFactResult::SurjectiveFact(_)
        | InferAtomicFactResult::BijectiveFact(_)
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
        Some((run, index)) => application(&name, &context_arguments_before(run, index)),
        None => name,
    };
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
    match statement {
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
            if before > 0 && p.stored.primary_fact_id() == id =>
        {
            check_store_subject(&p.stored.store, actual)?;
            check_subject(
                &verified_subject(&p.selected_proof)
                    .ok_or_else(|| LeanCompileError::unsupported("ByThm/Subject"))?,
                actual,
            )?;
            Ok(Some(global_reference(internal())))
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
        )) if before > 0 && p.stored.primary_fact_id() == id => {
            check_store_subject(&p.stored.store, actual)?;
            check_subject(&p.statement.fact, actual)?;
            Ok(Some(global_reference(internal())))
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
                        append_have_parameters(p, prefix, &mut parameters);
                        for (parameter, _, fact_id) in parameters {
                            let number = parameter.id.value();
                            arguments.extend([
                                format!("_Host_i{number}"),
                                format!("_rep_i{number}"),
                                format!("_value_i{number}"),
                                format!("h_{}", fact_id.value()),
                            ]);
                        }
                        return Ok(Some(application(&reference, &arguments)));
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
        SourceOwner::ExistWD(fact, p) => header_reference(
            &fact.typed_parameters.groups,
            &p.introduced_params,
            &p.assumed_body_facts,
            position.before,
            id,
            actual,
        ),
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
        | SourceOwner::RecursiveUnfold(_) => Ok(None),
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
        SourceOwner::ForallWD(fact, p) => header_reference(
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
        | SourceOwner::FactWD(_)
        | SourceOwner::HaveEqualType(_)
        | SourceOwner::HaveGroup(_, _)
        | SourceOwner::ParamTypeWD(_)
        | SourceOwner::ByDef(_)
        | SourceOwner::PropRequirements(_)
        | SourceOwner::EqualityRequirements(_)
        | SourceOwner::CalleeInstance(_)
        | SourceOwner::AtomicFnUnfold(_) => Ok(None),
        SourceOwner::FunctionNormalization(_)
        | SourceOwner::FunctionExpansion(_)
        | SourceOwner::FunctionDefinitionRewrite(_)
        | SourceOwner::FormedSubjects(..) => Ok(None),
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
    wd: &mut dyn FnMut(
        SourceConstructor<'_>,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let mut bounded_wd = |proof: SourceConstructor<'_>, producer: &SourcePosition<'_>| {
        if obeys_active_stage_ceilings(start, producer) {
            wd(proof, producer)
        } else {
            Ok(None)
        }
    };
    let mut bounded_verify = |proof: &VerifyFactResult, producer: &SourcePosition<'_>| {
        if obeys_active_stage_ceilings(start, producer) {
            verify(proof, producer)
        } else {
            Ok(None)
        }
    };
    let mut position = Some(start);
    while let Some(current) = position {
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
            if same_source_owner(ceiling.owner, stage.owner) && stage.before > ceiling.before {
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
        (SourceOwner::Claim(a), SourceOwner::Claim(b)) => std::ptr::eq(a, b),
        (SourceOwner::Forall(a), SourceOwner::Forall(b)) => std::ptr::eq(a, b),
        (SourceOwner::EmptyForall(a), SourceOwner::EmptyForall(b)) => std::ptr::eq(a, b),
        (SourceOwner::ForallWD(_, a), SourceOwner::ForallWD(_, b)) => std::ptr::eq(a, b),
        (SourceOwner::ExistWD(_, a), SourceOwner::ExistWD(_, b)) => std::ptr::eq(a, b),
        (SourceOwner::WitnessExist(a), SourceOwner::WitnessExist(b)) => std::ptr::eq(a, b),
        (SourceOwner::WitnessAtomic(a), SourceOwner::WitnessAtomic(b)) => std::ptr::eq(a, b),
        (SourceOwner::Contra(a), SourceOwner::Contra(b)) => std::ptr::eq(a, b),
        (SourceOwner::CasesBranch(a), SourceOwner::CasesBranch(b)) => std::ptr::eq(a, b),
        (SourceOwner::KnownForall(a), SourceOwner::KnownForall(b)) => std::ptr::eq(a, b),
        (SourceOwner::KnownApplication(a), SourceOwner::KnownApplication(b)) => std::ptr::eq(a, b),
        (SourceOwner::CalleeInstance(a), SourceOwner::CalleeInstance(b)) => std::ptr::eq(a, b),
        (SourceOwner::Call(a), SourceOwner::Call(b)) => std::ptr::eq(a, b),
        (SourceOwner::ThmRelease(a), SourceOwner::ThmRelease(b)) => std::ptr::eq(a, b),
        (SourceOwner::HaveEqualType(a), SourceOwner::HaveEqualType(b)) => std::ptr::eq(a, b),
        (SourceOwner::AtomicWD(a), SourceOwner::AtomicWD(b)) => std::ptr::eq(a, b),
        (SourceOwner::FactWD(a), SourceOwner::FactWD(b)) => std::ptr::eq(a, b),
        (SourceOwner::InferredStore(a), SourceOwner::InferredStore(b)) => std::ptr::eq(a, b),
        (SourceOwner::HaveGroup(a, pa), SourceOwner::HaveGroup(b, pb)) => {
            std::ptr::eq(a, b) && std::ptr::eq(pa, pb)
        }
        (SourceOwner::ParamTypeWD(a), SourceOwner::ParamTypeWD(b)) => std::ptr::eq(a, b),
        (SourceOwner::PropDefinition(a), SourceOwner::PropDefinition(b)) => std::ptr::eq(a, b),
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
        (SourceOwner::FunctionDefinitionRewrite(a), SourceOwner::FunctionDefinitionRewrite(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::RecursiveFunction(a), SourceOwner::RecursiveFunction(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::RecursiveCase(a), SourceOwner::RecursiveCase(b)) => std::ptr::eq(a, b),
        (SourceOwner::RecursiveDisjoint(a), SourceOwner::RecursiveDisjoint(b)) => {
            std::ptr::eq(a, b)
        }
        (SourceOwner::RecursiveUnfold(a), SourceOwner::RecursiveUnfold(b)) => std::ptr::eq(a, b),
        (SourceOwner::Induction(a), SourceOwner::Induction(b)) => std::ptr::eq(a, b),
        (SourceOwner::InductionCase(a, ca), SourceOwner::InductionCase(b, cb)) => {
            std::ptr::eq(a, b) && std::ptr::eq(ca, cb)
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
    let (assumption, store) = match position.owner {
        SourceOwner::Contra(p) => (&p.reverse_assumption_wd, &p.negation_assumed),
        SourceOwner::CasesBranch(p) => (&p.assumption_wd, &p.assumptions_stored),
        _ => unreachable!("local assumption owner"),
    };
    if let Some(value) = visit_store_stage(store, 1, position, wd, verify)? {
        return Ok(Some(value));
    }
    visit_fact_stage(assumption, 0, position, wd, verify)
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
        SourceOwner::FormedSubjects(..) => {}
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
        | SourceOwner::Contra(_)
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
        }
        SourceOwner::AtomicWD(proof) => {
            return visit_atomic_formation(proof, position.before, position, wd, verify)
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
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                let complete = SourcePosition {
                    before: head + index + 1,
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
                if let Some(value) = visit_complete_verify(&then.verify_result, &prior, wd, verify)?
                {
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
        SourceOwner::HaveEqualType(_) => {}
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
                if let FunctionBodyExpansionProof::Anonymous(step) = step {
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
    let position = SourcePosition::new(Some(parent), SourceOwner::Statement(statement), 0);
    let completed = SourcePosition { before, ..position };
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
            _ => unreachable!("obtain statement"),
        };
    }
    match statement {
        ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) => {
            if let Some(value) = visit_store_stage(&p.stored, 3, &completed, wd, verify)? {
                return Ok(Some(value));
            }
            if let Some(value) = visit_fact_stage(&p.stored_wd, 2, &completed, wd, verify)? {
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
                return visit_fact_stage(proof, 0, &completed, wd, verify);
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
            let scope =
                SourcePosition::new(Some(&position), SourceOwner::Induction(proof), usize::MAX);
            visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
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
            visit_complete_verify(&proof.verify_result, &position, wd, verify)
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
            _ => None,
        };
        if let Some((fact, formation)) = formation {
            return visit_closed_scope(SourceOwner::ExistWD(fact, formation), parent, wd);
        }
    }
    visit_verify_formation(proof, usize::MAX, &position, wd, verify)
}

fn closed_leaf(object: &Obj) -> bool {
    matches!(
        object,
        Obj::Literal(Literal::Number(_)) | Obj::StandardSet(_)
    )
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
    use crate::execute::execute_fact_stmt::function_domain::{
        CompleteFunctionDomainSourceProof, FunctionDomainComparisonProof,
    };
    stages.push(AtomicSearchStage::WD(&proof.function_wd));
    stages.push(AtomicSearchStage::WD(&proof.target_wd));
    match &proof.source.source {
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

// Borrow the children retained by these selected search routes. No new proof,
// wrapper result, or persistent lookup table is manufactured here.
fn atomic_search_stages(
    proof: &VerifyAtomicExceptEqualityFactSuccess,
) -> Vec<AtomicSearchStage<'_>> {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::{InFactSearchProofByBuiltinRule, PowerSetMembershipSubsetProof};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;
    let mut stages = Vec::new();
    match &proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(rule),
        ) => match rule {
            LessEqualFactSearchProofByBuiltinRule::SumOfNonnegatives(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.left_nonnegative_proof));
                stages.push(AtomicSearchStage::Verify(&proof.right_nonnegative_proof));
            }
            LessEqualFactSearchProofByBuiltinRule::ProductOfNonnegatives(proof) => {
                stages.push(AtomicSearchStage::Verify(&proof.left_nonnegative_proof));
                stages.push(AtomicSearchStage::Verify(&proof.right_nonnegative_proof));
            }
            _ => {}
        },
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(rule),
        ) => match rule {
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
fn projected_wd_child(
    proof: &ObjWellDefinedProof,
    term: String,
    matches: &impl Fn(&ObjWellDefinedProof) -> bool,
) -> Option<String> {
    if matches(proof) {
        return Some(term);
    }
    let fields: &[&str] = match proof {
        ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } if matches!(call.domain_fn_set, Some(
            crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence::FiniteFunction(_)
        )) => &["function", "argument"],
        _ => match proof.obj() {
        Obj::ArithmeticOperator(
            ArithmeticOperator::Add(_)
            | ArithmeticOperator::Sub(_)
            | ArithmeticOperator::Mul(_)
            | ArithmeticOperator::Div(_),
        ) => &["left", "right"],
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(_)) => &["base", "exponent"],
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(_) | ArithmeticOperator::Abs(_))
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
        proof: ObjWellDefinedProofByDef::SetOperator(proof),
        ..
    } = proof
    {
        return match proof {
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
        ArithmeticOperatorObjWellDefinedProofByDef::Pow(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        _ => None,
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
    match statement {
        ExecStmtResult::By(ExecByStmtResult::Induc(ExecByInducStmtResult::Success(proof)))
            if proof.stored.primary_fact_id() == id =>
        {
            Some(SourceOwner::Induction(proof))
        }
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
    let (fact, introduced, assumed) = match owner {
        SourceOwner::Induction(proof) => {
            let StoreFactResult::ForallFact(source) = &proof.stored.store else {
                return Err(LeanCompileError::unsupported("WD/InductionForallStore"));
            };
            (
                &source.fact,
                &proof.introduced_parameter,
                std::slice::from_ref(&proof.goal_domain),
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
