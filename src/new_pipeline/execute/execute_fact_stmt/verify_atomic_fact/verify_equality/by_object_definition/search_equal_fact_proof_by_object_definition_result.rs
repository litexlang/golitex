use super::by_have_obj_equal::ByHaveObjEqualObjectDefinitionProof;
use super::by_let_obj::ByLetObjObjectDefinitionProof;
use super::by_unfold_have_fn_by_induc_application::ByUnfoldHaveFnByInducApplicationObjectDefinitionProof;
use super::by_unfold_have_fn_equal_case_by_case_application::ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof;
use super::by_unfold_instantiated_template_have_fn_equal_application::ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof;
use super::by_unfold_instantiated_template_have_obj_equal::ByUnfoldInstantiatedTemplateHaveObjEqualObjectDefinitionProof;
use super::by_unfold_named_have_fn_equal_application::ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof;

// Each object-definition equality rule gets its own variant and payload.
pub enum EqualitySearchProofByObjectDefinition {
    ByHaveObjEqual(ByHaveObjEqualObjectDefinitionProof),
    ByLetObj(ByLetObjObjectDefinitionProof),
    ByUnfoldNamedHaveFnEqualApplication(
        ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof,
    ),
    ByUnfoldHaveFnEqualCaseByCaseApplication(
        ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof,
    ),
    ByUnfoldHaveFnByInducApplication(ByUnfoldHaveFnByInducApplicationObjectDefinitionProof),
    ByUnfoldInstantiatedTemplateHaveObjEqual(
        ByUnfoldInstantiatedTemplateHaveObjEqualObjectDefinitionProof,
    ),
    ByUnfoldInstantiatedTemplateHaveFnEqualApplication(
        ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof,
    ),
}
