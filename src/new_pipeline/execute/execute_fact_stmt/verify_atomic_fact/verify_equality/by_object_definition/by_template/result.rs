use super::by_have_fn_equal_application::ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof;
use super::by_have_obj_equal::ByUnfoldInstantiatedTemplateHaveObjEqualObjectDefinitionProof;

// Instantiated template obj / template-headed application.
pub enum EqualitySearchProofByTemplateObjectDefinition {
    HaveObjEqual(ByUnfoldInstantiatedTemplateHaveObjEqualObjectDefinitionProof),
    HaveFnEqualApplication(
        ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof,
    ),
}
