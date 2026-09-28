use super::by_have_obj_equal::ByHaveObjEqualObjectDefinitionProof;
use super::by_let_obj::ByLetObjObjectDefinitionProof;

// Identifier def-side only: look up that name's identifier definition.
pub enum EqualitySearchProofByIdentifierObjectDefinition {
    HaveObjEqual(ByHaveObjEqualObjectDefinitionProof),
    LetObj(ByLetObjObjectDefinitionProof),
}
