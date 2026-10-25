use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// The selected builtin asserts the literal's entire declared signature,
    /// modulo binder renaming. It does not weaken guards or widen its codomain.
    pub(super) fn compile_literal_function_member(
        &self,
        goal: &InFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)),
            Obj::FunctionSpace(FunctionSpace::FnSet(signature)),
        ) = (&goal.element, &goal.set)
        else {
            return Err(LeanCompileError::unsupported(
                "FunctionLiteral/DeclaredSetSubject",
            ));
        };
        if !crate::execute::execute_fact_stmt::fn_sets_alpha_equal(&function.body, signature) {
            return Err(LeanCompileError::unsupported(
                "FunctionLiteral/DeclaredSignature",
            ));
        }
        let object = self.compile_object_reference(&goal.element, position)?;
        let set = self.compile_object_reference(&goal.set, position)?;
        Ok(format!(
            "(show Litex.In {object} {set} from by exact Litex.formulaFnInFnSet {object})"
        ))
    }

    /// Membership of a returned function comes from this exact checked call.
    /// The applicability result owns its own argument WD registrations.
    pub(super) fn compile_application_return_member(
        &self,
        subject: &Obj,
        proof: &CompleteFunctionDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let CompleteFunctionDomainSourceProof::ApplicationReturn {
            application,
            subject_equal,
            signature_source,
            application_children,
            application_requirements,
            return_space,
            carrier_equal,
            ..
        } = &proof.source
        else {
            return Err(LeanCompileError::unsupported("ReturnedFunction/Source"));
        };
        let local =
            SourcePosition::new(Some(position), SourceOwner::CompleteDomainSource(proof), 0);
        let head = match application.head.as_ref() {
            FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
            FnObjHead::Object(object) => object.as_ref().clone(),
            FnObjHead::AnonymousFnLiteral(f) => {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(f.as_ref().clone()))
            }
            _ => return Err(LeanCompileError::unsupported("ReturnedFunction/Head")),
        };
        let head_term = self.compile_object_reference(&head, &local)?;
        let (signature, member) = match signature_source {
            FnObjDomainFnSetEvidence::InFunctionSet {
                fn_set,
                fact_id,
                function_equal,
            } => {
                let (original, member) = self.compile_fn_return_citation(
                    *fact_id,
                    &head,
                    &head_term,
                    Some(function_equal),
                    &local,
                )?;
                if original != fn_set {
                    return Err(LeanCompileError::unsupported(
                        "ReturnedFunction/SignatureCitation",
                    ));
                }
                (fn_set, member)
            }
            FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set } => {
                if !matches!(&head, Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) if &f.body == fn_set)
                {
                    return Err(LeanCompileError::unsupported(
                        "ReturnedFunction/LiteralSignature",
                    ));
                }
                (fn_set, format!("(Litex.formulaFnInFnSet {head_term})"))
            }
            FnObjDomainFnSetEvidence::Composition(callable) => (
                &callable.function.body,
                self.compile_composition_member(&head, callable, &local)?,
            ),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "ReturnedFunction/SignatureSource",
                ))
            }
        };
        // FunctionSignature currently has a fixed codomain. Dependent return
        // carriers need their own semantic contract, not erased substitution.
        if signature.ret_set.ir() != return_space.ir() {
            return Err(LeanCompileError::unsupported(
                "ReturnedFunction/DependentReturn",
            ));
        }
        let (input, domain) = self.compile_captured_call_domain(
            application,
            application_children,
            application_requirements,
            0,
            signature,
            &local,
        )?;
        let sig = self.compile_fn_signature(signature, &local)?;
        let source = Obj::FnObj(application.clone());
        let source_term = self.compile_object_reference(&source, position)?;
        let target = self.compile_object_reference(subject, position)?;
        let carrier = self.compile_object_reference(return_space, position)?;
        let target_carrier = Obj::FunctionSpace(FunctionSpace::FnSet(proof.signature.clone()));
        let result_sig = self.compile_fn_signature(&proof.signature, position)?;
        let same = self.compile_equality_path(subject, &source, subject_equal, position)?;
        let carrier_same =
            self.compile_equality_path(return_space, &target_carrier, carrier_equal, position)?;
        Ok(format!("(by\n  let _returned_signature : Litex.FunctionSignature M := {sig}\n  have _returned_source : Litex.In {head_term} (Litex.fnSet _returned_signature) := {member}\n  have _returned_input : M.mem {input} _returned_signature.domain := {domain}\n  have _returned_member : Litex.In {source_term} {carrier} := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote {head_term}) {input} _returned_source _returned_input\n  exact Litex.inOfSame {source_term} {target} {carrier} (Litex.fnSet {result_sig}) ({same}).symm {carrier_same} _returned_member)"))
    }
}
