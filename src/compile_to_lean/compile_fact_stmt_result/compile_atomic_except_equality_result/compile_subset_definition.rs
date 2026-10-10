use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_subset_definition(
        &self,
        fact: &SubsetFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 || proofs.len() != 1 {
            return Err(LeanCompileError::new(
                "Subset/DefinitionArity",
                "Subset definition needs its one actual universal child.",
            ));
        }
        let Fact::ForallFact(child) = &requirements[0] else {
            return Err(LeanCompileError::new(
                "Subset/DefinitionFamily",
                "The recorded definition child is not universal membership.",
            ));
        };
        if child.typed_parameters.groups.len() != 1
            || !child.dom_facts.is_empty()
            || child.then_facts.len() != 1
        {
            return Err(LeanCompileError::new(
                "Subset/DefinitionShape",
                "Subset formation has another binder, premise or conclusion shape.",
            ));
        }
        let group = &child.typed_parameters.groups[0];
        if group.params.len() != 1
            || !matches!(&group.param_type, ParamType::Obj(a) if a.ir() == fact.left.ir())
        {
            return Err(LeanCompileError::new(
                "Subset/DefinitionBound",
                "Subset definition binds a member of another source set.",
            ));
        }
        let object = Obj::Identifier(IdentifierObj::from_bound_name(&group.params[0]));
        if !matches!(&child.then_facts[0], ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == object.ir() && f.set.ir() == fact.right.ir())
            || source_subject(&proofs[0])? != requirements[0]
        {
            return Err(LeanCompileError::new(
                "Subset/DefinitionSubject",
                "Subset definition child has another source element, upper bound or identity.",
            ));
        }
        let compiled = self.compile_verify(&proofs[0], position)?;
        Ok(format!(
            "(Litex.subsetOfForall {} {} {})",
            self.compile_object_reference(&fact.left, position)?,
            self.compile_object_reference(&fact.right, position)?,
            compiled.1
        ))
    }
}
