use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::ExecDefPropStmtSuccessResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Instantiate the original declaration's clause; the projection itself has
    /// no second WD run. Domain witnesses come from the proved predicate.
    pub(in crate::compile_to_lean) fn compile_prop_clause_instance(
        &self,
        normal: &NormalAtomicFact,
        index: usize,
        predicate_proof: &str,
        caller: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, parent, _) = caller.visible_prop(&normal.predicate)?;
        if index != 0 || declaration.statement.iff_facts.len() != 1 {
            return Err(LeanCompileError::unsupported("Prop/DependentExistClause"));
        }
        let scope = SourcePosition::new(
            Some(&parent),
            SourceOwner::PropDefinition(declaration),
            declaration
                .statement
                .typed_parameters
                .ordered_param_ids()
                .len(),
        );
        let fact = &declaration.statement.iff_facts[index];
        let captured = declaration
            .assumed_iff_facts
            .get(index)
            .ok_or_else(|| LeanCompileError::unsupported("Prop/ClauseCapture"))?;
        self.compile_fact_wd(&captured.well_defined, fact, &scope)?;
        let formed = SourcePosition::new(
            Some(&scope),
            SourceOwner::FactWD(&captured.well_defined),
            usize::MAX,
        );
        let body = self.fact_proposition(fact, &formed)?;
        self.compile_prop_parameter_instance(
            declaration,
            normal,
            body,
            predicate_proof,
            &scope,
            caller,
        )
    }

    /// Apply the original outer prop binders before the inner existential
    /// binders. Proof-valued domain witnesses never select an object meaning.
    pub(in crate::compile_to_lean) fn compile_prop_parameter_instance(
        &self,
        declaration: &ExecDefPropStmtSuccessResult,
        normal: &NormalAtomicFact,
        body: String,
        predicate_proof: &str,
        original: &SourcePosition<'_>,
        caller: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.prop_argument_substitution(declaration, normal)?;
        let (mut binders, memberships, definitions) =
            self.compile_prop_parameter_prefix(declaration, original, true)?;
        let mut arguments = normal
            .body
            .iter()
            .map(|object| self.compile_object_reference(object, caller))
            .collect::<Result<Vec<_>, _>>()?;
        let mut tail = predicate_proof.to_owned();
        for (name, member) in memberships {
            binders.push(format!("({name} : {member})"));
            arguments.push(format!("(Classical.choose ({tail}))"));
            tail = format!("(Classical.choose_spec ({tail}))");
        }
        let body = self.scope_proposition(body, &definitions);
        Ok(if binders.is_empty() {
            body
        } else {
            format!(
                "((fun {} => {body}) {})",
                binders.join(" "),
                arguments.join(" ")
            )
        })
    }
}
