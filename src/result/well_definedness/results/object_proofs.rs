//! Object well-definedness results, recursive steps, and target requirements.

use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WellDefinednessRequirementRole {
    BuiltinArgumentMembership {
        argument_index: usize,
    },
    BuiltinArgumentNonzero {
        argument_index: usize,
    },
    ConstructorPairwiseDistinct {
        left_index: usize,
        right_index: usize,
    },
    FunctionArgumentMembership {
        layer_index: usize,
        parameter_index: usize,
    },
    FunctionDomain {
        layer_index: usize,
        domain_index: usize,
    },
    AnonymousFunctionBodyMembership,
    AnonymousFunctionBoundParameterSubset {
        parameter_group_index: usize,
        parameter_index: usize,
    },
}

/// Successful output of checking one object for well-definedness.
/// Direct checks own their recursively returned children; cache hits retain
/// the current source occurrence and cite the exact earlier proof node.
#[derive(Debug)]
pub enum SuccessVerifyObjWellDefinedResult {
    Direct(Rc<SuccessVerifyDirectObjWellDefinedResult>),
    Reuse(Box<SuccessReuseObjWellDefinedResult>),
}

pub struct SuccessVerifyDirectObjWellDefinedResult {
    pub object: Obj,
    pub object_key: ObjString,
    pub function_contracts: Vec<WellDefinedFunctionContract>,
    pub steps: SuccessVerifyObjWellDefinedStepsResult,
    pub intrinsic_result_set: Option<Obj>,
}

impl SuccessVerifyDirectObjWellDefinedResult {
    pub fn new(
        object: Obj,
        object_key: ObjString,
        function_contracts: Vec<WellDefinedFunctionContract>,
        steps: SuccessVerifyObjWellDefinedStepsResult,
        intrinsic_result_set: Option<Obj>,
    ) -> Self {
        Self {
            object,
            object_key,
            function_contracts,
            steps,
            intrinsic_result_set,
        }
    }
}

pub struct SuccessReuseObjWellDefinedResult {
    pub object: Obj,
    pub source: Rc<SuccessVerifyDirectObjWellDefinedResult>,
}

impl SuccessReuseObjWellDefinedResult {
    pub fn new(object: Obj, source: Rc<SuccessVerifyDirectObjWellDefinedResult>) -> Self {
        Self { object, source }
    }
}

/// Ordered semantic outputs produced by one constructor-specific WD check.
#[derive(Debug, Default)]
pub struct SuccessVerifyObjWellDefinedStepsResult {
    pub children: Vec<SuccessVerifyChildObjWellDefinedResult>,
    pub fact_checks: Vec<SuccessVerifyFactForObjWellDefinedResult>,
    pub target_requirements: Vec<SuccessVerifyObjTargetRequirementResult>,
    pub stores: Vec<SuccessStoreFactResult>,
    pub binder: Option<Box<SuccessVerifyBinderObjectWellDefinedResult>>,
    pub template_instantiation: Option<Box<SuccessTemplateInstantiationResult>>,
}

impl SuccessVerifyObjWellDefinedStepsResult {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_child(&mut self, child: SuccessVerifyChildObjWellDefinedResult) {
        self.children.push(child);
    }

    pub fn push_fact_check(&mut self, check: SuccessVerifyFactForObjWellDefinedResult) {
        self.fact_checks.push(check);
    }

    pub fn push_target_requirement(
        &mut self,
        requirement: SuccessVerifyObjTargetRequirementResult,
    ) {
        self.target_requirements.push(requirement);
    }

    pub fn push_store(&mut self, store: SuccessStoreFactResult) {
        self.stores.push(store);
    }

    pub fn append(&mut self, mut other: Self) {
        self.children.append(&mut other.children);
        self.fact_checks.append(&mut other.fact_checks);
        self.target_requirements
            .append(&mut other.target_requirements);
        self.stores.append(&mut other.stores);
        if self.binder.is_none() {
            self.binder = other.binder;
        }
        if self.template_instantiation.is_none() {
            self.template_instantiation = other.template_instantiation;
        }
    }
}

pub struct SuccessVerifyChildObjWellDefinedResult {
    pub role: WellDefinedObjChildRole,
    pub source_object: Obj,
    pub result: Rc<SuccessVerifyObjWellDefinedResult>,
}

impl SuccessVerifyChildObjWellDefinedResult {
    pub fn new(
        role: WellDefinedObjChildRole,
        source_object: Obj,
        result: Rc<SuccessVerifyObjWellDefinedResult>,
    ) -> Self {
        Self {
            role,
            source_object,
            result,
        }
    }
}

#[derive(Debug)]
pub struct SuccessVerifyFactForObjWellDefinedResult {
    pub expected_proposition: Fact,
    pub verification: Rc<SuccessFactProofNode>,
}

impl SuccessVerifyFactForObjWellDefinedResult {
    pub fn new(expected_proposition: Fact, verification: Rc<SuccessFactProofNode>) -> Self {
        Self {
            expected_proposition,
            verification,
        }
    }
}

pub struct SuccessVerifyObjTargetRequirementResult {
    pub source_object: Obj,
    pub role: WellDefinednessRequirementRole,
    pub expected_proposition: Fact,
    pub verification: Rc<SuccessFactProofNode>,
}

impl SuccessVerifyObjTargetRequirementResult {
    pub fn new(
        source_object: Obj,
        role: WellDefinednessRequirementRole,
        expected_proposition: Fact,
        verification: Rc<SuccessFactProofNode>,
    ) -> Self {
        Self {
            source_object,
            role,
            expected_proposition,
            verification,
        }
    }
}

#[derive(Debug)]
pub enum SuccessVerifyBinderObjectWellDefinedResult {
    SetBuilder(Box<SuccessVerifySetBuilderWellDefinedResult>),
    FunctionSet(Box<SuccessVerifyFunctionSetWellDefinedResult>),
    AnonymousFunction(Box<SuccessVerifyAnonymousFunctionWellDefinedResult>),
    Iteration(Box<SuccessVerifyIterationWellDefinedResult>),
    FiniteAggregate(Box<SuccessVerifyFiniteAggregateWellDefinedResult>),
    Reduce(Box<SuccessVerifyReduceWellDefinedResult>),
    Structure(Box<SuccessVerifyStructureWellDefinedResult>),
}

#[derive(Debug)]
pub struct SuccessVerifyBinderPremiseResult {
    pub role: WellDefinedBinderPremiseRole,
    pub symbol_id: Option<SymbolId>,
    pub proposition: Fact,
    pub well_definedness: Box<WellDefinedFactResult>,
    pub infers: SuccessInferResult,
}

impl SuccessVerifyBinderPremiseResult {
    pub fn new(
        role: WellDefinedBinderPremiseRole,
        symbol_id: Option<SymbolId>,
        proposition: Fact,
        well_definedness: WellDefinedFactResult,
        infers: SuccessInferResult,
    ) -> Self {
        Self {
            role,
            symbol_id,
            proposition,
            well_definedness: Box::new(well_definedness),
            infers,
        }
    }
}

impl SuccessVerifyObjWellDefinedResult {
    pub fn object(&self) -> &Obj {
        match self {
            Self::Direct(result) => &result.object,
            Self::Reuse(result) => &result.object,
        }
    }
}

impl fmt::Debug for SuccessVerifyDirectObjWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyDirectObjWellDefinedResult")
            .field("object", &self.object.to_string())
            .field("object_key", &self.object_key)
            .field("function_contracts", &self.function_contracts)
            .field("steps", &self.steps)
            .field(
                "intrinsic_result_set",
                &self.intrinsic_result_set.as_ref().map(ToString::to_string),
            )
            .finish()
    }
}

impl fmt::Debug for SuccessReuseObjWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessReuseObjWellDefinedResult")
            .field("object", &self.object.to_string())
            .field("source", &self.source)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyChildObjWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyChildObjWellDefinedResult")
            .field("role", &self.role)
            .field("source_object", &self.source_object.to_string())
            .field("result", &self.result)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyObjTargetRequirementResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyObjTargetRequirementResult")
            .field("source_object", &self.source_object.to_string())
            .field("role", &self.role)
            .field(
                "expected_proposition",
                &self.expected_proposition.to_string(),
            )
            .field("verification", &self.verification)
            .finish()
    }
}
