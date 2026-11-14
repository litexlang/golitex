//! Checked, size-bounded native entry expansion; no scalar truth is assumed.
use crate::execute::execute_fact_stmt::native_matrix::MatrixCallableProof;
use crate::prelude::*;

pub struct MatrixEntryNormalizationProof {
    pub source_wd: ObjWellDefinedProof,
    pub value: Obj,
    pub step: MatrixEntryNormalizationStep,
}

pub enum MatrixEntryNormalizationStep {
    Unchanged,
    NativeCall(MatrixEntryNativeCallProof),
    Add(
        Box<MatrixEntryNormalizationProof>,
        Box<MatrixEntryNormalizationProof>,
    ),
    Subtract(
        Box<MatrixEntryNormalizationProof>,
        Box<MatrixEntryNormalizationProof>,
    ),
    Multiply(
        Box<MatrixEntryNormalizationProof>,
        Box<MatrixEntryNormalizationProof>,
    ),
    Conjugate(Box<MatrixEntryNormalizationProof>),
}

pub struct MatrixEntryNativeCallProof {
    pub callable: Box<MatrixCallableProof>,
    pub body: Obj,
    pub continuation: Box<MatrixEntryNormalizationProof>,
}

pub struct MatrixEntryReductionProof {
    pub left: MatrixEntryNormalizationProof,
    pub right: MatrixEntryNormalizationProof,
    pub scalar_equality: VerifyFactResult,
}

pub struct MatrixStructuralEqualityProof {
    pub right_domain:
        crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof,
    pub domain_match: crate::execute::execute_fact_stmt::function_domain::FunctionDomainMatchProof,
    pub pointwise: VerifyFactResult,
}
