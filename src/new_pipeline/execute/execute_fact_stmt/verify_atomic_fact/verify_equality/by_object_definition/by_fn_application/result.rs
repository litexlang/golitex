use super::by_have_fn_by_induc::ByUnfoldHaveFnByInducApplicationObjectDefinitionProof;
use super::by_have_fn_equal::ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof;
use super::by_have_fn_equal_case_by_case::ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof;

// FnObj with identifier head: have-fn definition table only.
pub enum EqualitySearchProofByFnApplicationObjectDefinition {
    HaveFnEqual(ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof),
    HaveFnEqualCaseByCase(ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof),
    HaveFnByInduc(ByUnfoldHaveFnByInducApplicationObjectDefinitionProof),
}
