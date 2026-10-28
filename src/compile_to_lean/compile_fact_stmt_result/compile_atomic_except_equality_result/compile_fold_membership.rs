use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::FoldScalarCodomainBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{FoldInCarrierProof, FoldOperationSignatureProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef as P;
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Use the already formed fold, retaining the constructor's exact output
    /// carrier rather than reopening function-signature lookup.
    fn compile_fold_output(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(FnSet, String), LeanCompileError> {
        let signature = position
            .with_visible_wd(object, &mut |wd, _| {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::IteratedOperator(p),
                    ..
                } = (wd).detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported("FoldMember/Constructor"));
                };
                let selected = match p {
                    P::Reduce(p) => &p.operation_signature_selection,
                    P::FiniteSetReduce(p) => &p.operation_signature_selection,
                    _ => return Err(LeanCompileError::unsupported("FoldMember/Constructor")),
                };
                selected
                    .as_ref()
                    .map(|s| s.signature().clone())
                    .ok_or_else(|| LeanCompileError::unsupported("FoldMember/SignatureCapture"))
            })?
            .ok_or_else(|| LeanCompileError::unsupported("FoldMember/Producer"))?;
        let term = self.compile_object_reference(object, position)?;
        let law = match object {
            Obj::IteratedOperator(IteratedOperator::Reduce(_)) => "rangeFoldInOutput",
            Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(_)) => "finiteFoldInOutput",
            _ => return Err(LeanCompileError::unsupported("FoldMember/Subject")),
        };
        Ok((signature, format!("(Litex.{law} {term})")))
    }

    pub(in crate::compile_to_lean) fn compile_fold_scalar_member(
        &self,
        fact: &InFact,
        proof: &FoldScalarCodomainBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::StandardSet(target) = &fact.set else {
            return Err(LeanCompileError::unsupported("FoldMember/ScalarTarget"));
        };
        let (signature, member) = self.compile_fold_output(&fact.element, position)?;
        if signature.ret_set.as_ref() != &proof.operation_return_set
            || proof.operation_return_set != Obj::StandardSet(proof.codomain.clone())
        {
            return Err(LeanCompileError::unsupported("FoldMember/ScalarSignature"));
        }
        standard_inclusion_term(
            &proof.codomain,
            target,
            &self.compile_object_reference(&fact.element, position)?,
            &member,
        )
    }

    pub(in crate::compile_to_lean) fn compile_fold_carrier_member(
        &self,
        fact: &InFact,
        proof: &FoldInCarrierProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (signature, member) = self.compile_fold_output(&fact.element, position)?;
        if signature.ret_set.ir() != proof.carrier.ir() {
            return Err(LeanCompileError::unsupported("FoldMember/Carrier"));
        }
        let operation = match &fact.element {
            Obj::IteratedOperator(IteratedOperator::Reduce(p)) => &p.op,
            Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(p)) => &p.op,
            _ => return Err(LeanCompileError::unsupported("FoldMember/Subject")),
        };
        let (proposition, selected) = match &proof.operation_signature {
            FoldOperationSignatureProof::Literal(s) => {
                if s != &signature
                    || !matches!(operation.as_ref(), Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) if f.body == *s)
                {
                    return Err(LeanCompileError::unsupported("FoldMember/LiteralSignature"));
                }
                let term = self.compile_object_reference(operation, position)?;
                (
                    format!(
                        "Litex.In {term} (Litex.fnSet {})",
                        self.compile_fn_signature(s, position)?
                    ),
                    format!("(Litex.formulaFnInFnSet {term})"),
                )
            }
            FoldOperationSignatureProof::Known(p) => {
                if !matches!(&p.fact, AtomicFact::InFact(f) if f.element.ir() == operation.ir()
                    && matches!(&f.set, Obj::FunctionSpace(FunctionSpace::FnSet(s)) if s == &signature))
                {
                    return Err(LeanCompileError::unsupported("FoldMember/KnownSignature"));
                }
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
                    p.searched_proof.as_ref()
                else {
                    return Err(LeanCompileError::unsupported("FoldMember/SignatureRoute"));
                };
                (
                    format!(
                        "Litex.In {} (Litex.fnSet {})",
                        self.compile_object_reference(operation, position)?,
                        self.compile_fn_signature(&signature, position)?
                    ),
                    self.compile_known_atomic(citation, &p.fact, position)?,
                )
            }
        };
        let equality = self.compile_fn_return_set_match(
            &proof.carrier,
            &fact.set,
            &proof.carrier_match,
            position,
        )?;
        let object = self.compile_object_reference(&fact.element, position)?;
        let source = self.compile_object_reference(&proof.carrier, position)?;
        let target = self.compile_object_reference(&fact.set, position)?;
        Ok(format!("(by\n  have _selected_operation : {proposition} := {selected}\n  exact Litex.inOfSame {object} {object} {source} {target} (Litex.sameRefl {object}) {equality} {member})"))
    }
}
