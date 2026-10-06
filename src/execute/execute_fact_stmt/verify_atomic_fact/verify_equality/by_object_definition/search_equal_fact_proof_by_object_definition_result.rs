use super::by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition;
use super::by_identifier::EqualitySearchProofByIdentifierObjectDefinition;
use super::by_template::EqualitySearchProofByTemplateObjectDefinition;

// Object-definition equality: dispatch by the definition-side object shape first.
pub enum EqualitySearchProofByObjectDefinition {
    CartesianDefinition(super::cart_definition::CartesianDefinitionProof),
    ByIdentifier(EqualitySearchProofByIdentifierObjectDefinition),
    ByFnApplication(EqualitySearchProofByFnApplicationObjectDefinition),
    ByTemplate(EqualitySearchProofByTemplateObjectDefinition),
}
