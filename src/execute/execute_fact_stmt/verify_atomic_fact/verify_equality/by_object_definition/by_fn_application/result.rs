use super::by_have_fn_by_induc::ByUnfoldHaveFnByInducApplicationObjectDefinitionProof;
use super::by_have_fn_equal::ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof;
use super::by_have_fn_equal_case_by_case::ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof;

// Anonymous-function equality evidence, or named cases/induction definitions.
pub enum EqualitySearchProofByFnApplicationObjectDefinition {
    HaveFnEqual(ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof),
    BothFunctionBodies(super::by_both_function_bodies::ByBothFunctionBodiesObjectDefinitionProof),
    HaveFnEqualCaseByCase(ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof),
    HaveFnByInduc(ByUnfoldHaveFnByInducApplicationObjectDefinitionProof),
    ParentCheckedBeta(super::by_parent_checked_beta::ByParentCheckedBetaObjectDefinitionProof),
}
