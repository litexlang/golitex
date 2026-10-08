use super::by_have_fn_by_induc_application::ByUnfoldInstantiatedTemplateHaveFnByInducApplicationObjectDefinitionProof;
use super::by_have_fn_equal_application::ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof;
use super::by_have_fn_equal_case_by_case_application::ByUnfoldInstantiatedTemplateHaveFnEqualCaseByCaseApplicationObjectDefinitionProof;
use super::by_have_obj_equal::ByUnfoldInstantiatedTemplateHaveObjEqualObjectDefinitionProof;

// Instantiated template obj / template-headed application.
// Variants mirror TemplateDefEnum have-fn / have-obj equality shapes.
pub enum EqualitySearchProofByTemplateObjectDefinition {
    HaveObjEqual(ByUnfoldInstantiatedTemplateHaveObjEqualObjectDefinitionProof),
    HaveFnEqualApplication(ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof),
    HaveFnEqualCaseByCaseApplication(
        ByUnfoldInstantiatedTemplateHaveFnEqualCaseByCaseApplicationObjectDefinitionProof,
    ),
    HaveFnByInducApplication(
        ByUnfoldInstantiatedTemplateHaveFnByInducApplicationObjectDefinitionProof,
    ),
}
