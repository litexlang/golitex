use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn validate_function_carrier_signature(
        &self,
        carrier: &Obj,
        signature: &FnSet,
    ) -> Result<(), LeanCompileError> {
        match carrier {
            Obj::FunctionSpace(FunctionSpace::FnSet(actual))
                if crate::execute::execute_fact_stmt::fn_sets_alpha_equal(actual, signature) =>
            {
                Ok(())
            }
            Obj::SetFormer(SetFormer::SeqSet(sequence)) => {
                Self::validate_seq_signature(sequence, signature)
            }
            Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) => {
                Self::validate_finite_seq_signature(sequence, signature)
            }
            Obj::SetFormer(SetFormer::MatrixSet(matrix)) => {
                Self::validate_matrix_signature(matrix, signature)
            }
            _ => Err(LeanCompileError::unsupported(
                "FunctionCarrier/SignatureSubject",
            )),
        }
    }

    /// Read a membership certificate's signature from its original carrier.
    /// Expanded carriers retain implicit domains, such as the N+ of seq(A),
    /// without requiring separately registered constructors for those domains.
    pub(in crate::compile_to_lean) fn compile_complete_domain_signature(
        &self,
        proof: &crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let CompleteFunctionDomainSourceProof::Membership {
            membership,
            carrier_equal,
            ..
        } = &proof.source
        {
            let endpoint = carrier_equal
                .path
                .last()
                .map(|(_, to, _)| to)
                .unwrap_or(&membership.set);
            self.validate_function_carrier_signature(endpoint, &proof.signature)?;
            let object = self.compile_object_reference(endpoint, position)?;
            return Ok(match endpoint {
                Obj::FunctionSpace(FunctionSpace::FnSet(_)) => format!("({object}).val"),
                Obj::SetFormer(SetFormer::SeqSet(_)) => {
                    format!("(Litex.seqSignature ({object}).val.carrier)")
                }
                Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => {
                    format!("(Litex.finiteSeqSignature {object})")
                }
                Obj::SetFormer(SetFormer::MatrixSet(_)) => {
                    format!("(Litex.matrixSignature {object})")
                }
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "FunctionCarrier/SignatureSubject",
                    ))
                }
            });
        }
        self.compile_fn_signature(&proof.signature, position)
    }

    /// The recorded path ends at a source carrier; its wrapper determines the
    /// corresponding signature without an extra source object or WD producer.
    pub(in crate::compile_to_lean) fn compile_function_carrier_path(
        &self,
        carrier: &Obj,
        signature: &FnSet,
        path: &KnownEqualityPathProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let endpoint = path.path.last().map(|(_, to, _)| to).unwrap_or(carrier);
        self.validate_function_carrier_signature(endpoint, signature)?;
        let same = self.compile_equality_path(carrier, endpoint, path, position)?;
        let law = match endpoint {
            Obj::SetFormer(SetFormer::MatrixSet(_)) => "matrixSet_eq_fnSet",
            Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => "finiteSeq_eq_fnSet",
            Obj::SetFormer(SetFormer::SeqSet(_)) => "seqSet_eq_fnSet",
            _ => return Ok(same),
        };
        let object = self.compile_object_reference(endpoint, position)?;
        Ok(format!("({same}.trans (Litex.{law} {object}))"))
    }

    /// The selected builtin asserts the literal's entire declared signature,
    /// modulo binder renaming. It does not weaken guards or widen its codomain.
    pub(super) fn compile_literal_function_member(
        &self,
        goal: &InFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) = &goal.element else {
            return Err(LeanCompileError::unsupported(
                "FunctionLiteral/DeclaredSetSubject",
            ));
        };
        self.validate_function_carrier_signature(&goal.set, &function.body)?;
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
            application_check,
            return_space,
            carrier_equal,
            ..
        } = &proof.source
        else {
            return Err(LeanCompileError::unsupported("ReturnedFunction/Source"));
        };
        let checks = application_check.detailed_ref();
        let application_children = &checks.child_obj_well_defined;
        let application_requirements = &checks.requirement_fact_verified;
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
        let endpoint = carrier_equal
            .path
            .last()
            .map(|(_, to, _)| to)
            .unwrap_or(return_space);
        self.validate_function_carrier_signature(endpoint, &proof.signature)?;
        let result_sig = match endpoint {
            Obj::SetFormer(SetFormer::MatrixSet(_)) => format!(
                "(Litex.matrixSignature {})",
                self.compile_object_reference(endpoint, position)?
            ),
            Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => format!(
                "(Litex.finiteSeqSignature {})",
                self.compile_object_reference(endpoint, position)?
            ),
            _ => self.compile_fn_signature(&proof.signature, position)?,
        };
        let same = self.compile_equality_path(subject, &source, subject_equal, position)?;
        let carrier_same = self.compile_function_carrier_path(
            return_space,
            &proof.signature,
            carrier_equal,
            position,
        )?;
        Ok(format!("(by\n  let _returned_signature : Litex.FunctionSignature M := {sig}\n  have _returned_source : Litex.In {head_term} (Litex.fnSet _returned_signature) := {member}\n  have _returned_input : M.mem {input} _returned_signature.domain := {domain}\n  have _returned_member : Litex.In {source_term} {carrier} := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote {head_term}) {input} _returned_source _returned_input\n  exact Litex.inOfSame {source_term} {target} {carrier} (Litex.fnSet {result_sig}) ({same}).symm {carrier_same} _returned_member)"))
    }
}
