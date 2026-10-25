use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::ExecDefAbstractPropStmtResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_abstract_prop_statement(
        &self,
        result: &ExecDefAbstractPropStmtResult,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local {
            return Err(LeanCompileError::unsupported(
                "AbstractProp/LocalDeclaration",
            ));
        }
        let ExecDefAbstractPropStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("AbstractProp/Failed"));
        };
        // A declaration supplies an arbitrary interpretation, never a truth
        // assumption. Fin retains the source arity, including a nullary prop.
        Ok(format!(
            "variable (abstract_prop_{index} : (Fin {} → M.Value) → Prop)",
            proof.statement.params.len()
        ))
    }

    pub(super) fn compile_abstract_predicate_proposition(
        &self,
        predicate: &AtomicName,
        arguments: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let Some((declaration, index)) = position.visible_abstract_prop(predicate) else {
            return Ok(None);
        };
        if declaration.params.len() != arguments.len() {
            return Err(LeanCompileError::unsupported("AbstractProp/Arity"));
        }
        let values = if arguments.is_empty() {
            "(fun i : Fin 0 => Fin.elim0 i)".to_string()
        } else {
            format!("![{}]", arguments.join(", "))
        };
        Ok(Some(format!("(abstract_prop_{index} {values})")))
    }

    pub(super) fn validate_abstract_predicate_signature(
        &self,
        signature: &PredicateSignatureWellDefinedProof,
        fact: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        let PredicateSignatureWellDefinedProof::AbstractProp { predicate, arity } = signature
        else {
            return Err(LeanCompileError::unsupported(
                "AbstractProp/SignatureFamily",
            ));
        };
        let (name, arguments) = match fact {
            AtomicFact::NormalAtomicFact(f) => (&f.predicate, &f.body),
            AtomicFact::NotNormalAtomicFact(f) => (&f.predicate, &f.body),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "AbstractProp/SignatureFamily",
                ))
            }
        };
        let Some((declaration, _)) = position.visible_abstract_prop(name) else {
            return Err(LeanCompileError::unsupported("AbstractProp/Producer"));
        };
        if predicate != name || *arity != arguments.len() || *arity != declaration.params.len() {
            return Err(LeanCompileError::unsupported("AbstractProp/Signature"));
        }
        Ok(())
    }
}
