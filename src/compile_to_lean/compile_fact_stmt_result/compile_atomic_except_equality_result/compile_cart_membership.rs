use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::validate_finite_signature;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::{
    function_domains_alpha_equal, CompleteFunctionDomainSourceProof, FunctionDomainComparisonProof,
    FunctionDomainMatchProof,
};
use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_cart_membership(
        &self,
        fact: &InFact,
        domain: &FunctionDomainMatchProof,
        requirements: Option<&[Fact]>,
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let first = proofs.first().ok_or_else(|| {
            LeanCompileError::new(
                "CartMembership/Requirements",
                "Cartesian membership must retain its carrier equality and coordinate proofs.",
            )
        })?;
        let Fact::AtomicFact(AtomicFact::EqualFact(definition)) = source_subject(first)? else {
            return Err(LeanCompileError::new(
                "CartMembership/CarrierEquality",
                "The first premise is not the original Cartesian carrier equality.",
            ));
        };
        let Obj::ProductShape(ProductShape::Cart(cart)) = &definition.right else {
            return Err(LeanCompileError::new(
                "CartMembership/CarrierEquality",
                "The carrier equality must end at its recorded Cartesian definition.",
            ));
        };
        if definition.left.ir() != fact.set.ir() || proofs.len() != cart.args.len() + 1 {
            return Err(LeanCompileError::new(
                "CartMembership/Requirements",
                "The premises differ from the source carrier and complete coordinate count.",
            ));
        }
        if let Some(requirements) = requirements {
            if requirements.len() != proofs.len() {
                return Err(LeanCompileError::new(
                    "CartMembership/Requirements",
                    "The original strategy requirements and their proofs have different lengths.",
                ));
            }
            for (requirement, proof) in requirements.iter().zip(proofs) {
                if source_subject(proof)? != *requirement {
                    return Err(LeanCompileError::new(
                        "CartMembership/RequirementSubject",
                        "A strategy proof establishes another original requirement.",
                    ));
                }
            }
        }
        let CompleteFunctionDomainSourceProof::FiniteFunction(finite) = &domain.source.source
        else {
            return Err(LeanCompileError::unsupported(
                "CartMembership/CompleteDomainSource",
            ));
        };
        validate_finite_signature(finite)?;
        let KnownTupleShapeProof::TupleEquality(tuple_source) = &finite.source else {
            return Err(LeanCompileError::unsupported(
                "CartMembership/NonliteralSource",
            ));
        };
        let n = cart.args.len();
        if tuple_source.value.args.len() != n
            || domain.source.signature.ir() != finite.signature.ir()
            || !matches!(
                domain.comparison,
                FunctionDomainComparisonProof::AlphaEquivalent
            )
            || !function_domains_alpha_equal(&finite.signature, &domain.target)
        {
            return Err(LeanCompileError::new("CartMembership/CompleteDomain", "The retained tuple constructor and target must have the same complete original domain."));
        }
        let mut factors = cart.args.iter();
        let mut output = factors
            .next()
            .map(|factor| factor.as_ref().clone())
            .unwrap_or_else(|| Obj::SetFormer(SetFormer::ListSet(ListSet { list: Vec::new() })));
        for factor in factors {
            output = Obj::SetOperator(SetOperator::Union(Union {
                left: Box::new(output),
                right: factor.clone(),
            }));
        }
        if output.ir() != domain.target.ret_set.ir() {
            return Err(LeanCompileError::new("CartMembership/TargetFactors", "The target signature does not retain the ordered union of the source Cartesian factors."));
        }
        ensure_object(&fact.element, &domain.function_wd)?;
        let target_signature = Obj::FunctionSpace(FunctionSpace::FnSet(domain.target.clone()));
        ensure_object(&target_signature, &domain.target_wd)?;
        let function_prior = position.atomic_search_prior(0)?;
        let function = self.compile_wd(&domain.function_wd, &function_prior)?;
        let target_prior = position.atomic_search_prior(1)?;
        let checked_target = self.compile_wd(&domain.target_wd, &target_prior)?;
        let carrier_prior = position.atomic_search_prior(2)?;
        let tuple_object = Obj::ProductShape(ProductShape::Tuple(tuple_source.value.clone()));
        let tuple = self.compile_object_reference(&tuple_object, &carrier_prior)?;
        let tuple_equal = self.compile_equality_path(
            &fact.element,
            &tuple_object,
            &tuple_source.tuple_equal,
            &carrier_prior,
        )?;
        let carrier_equal = self.compile_verify(first, &carrier_prior)?.1;
        let mut coordinates = Vec::new();
        for (index, proof) in proofs[1..].iter().enumerate() {
            match source_subject(proof)? {
                Fact::AtomicFact(AtomicFact::InFact(member))
                    if member.element.ir() == tuple_source.value.args[index].ir()
                        && member.set.ir() == cart.args[index].ir() => {}
                _ => return Err(LeanCompileError::new(
                    "CartMembership/CoordinateSubject",
                    "A coordinate proof differs from its original tuple value or Cartesian factor.",
                )),
            }
            let coordinate_prior = position.atomic_search_prior(3 + index)?;
            coordinates.push(self.compile_verify(proof, &coordinate_prior)?.1);
        }
        let coordinate_proof = if coordinates.is_empty() {
            "(by intro i; exact Fin.elim0 i)".into()
        } else {
            format!(
                "(by\n  intro i\n  fin_cases i\n  · {})",
                coordinates
                    .iter()
                    .map(|proof| format!("exact {proof}"))
                    .collect::<Vec<_>>()
                    .join("\n  · ")
            )
        };
        let complete = position.atomic_search_prior(2 + proofs.len())?;
        let carrier = self.compile_object_reference(&definition.right, &complete)?;
        let target = self.compile_object_reference(&fact.set, &complete)?;
        Ok(format!("(by\n  let _checked_domain_target := {checked_target}\n  let _function := {function}\n  let _tuple := {tuple}\n  let _cart := {carrier}\n  let _target := {target}\n  have _tupleMember : Litex.In _tuple _cart := Litex.tupleInCart _tuple _cart {}\n  have _tupleSame : Litex.Same _function _tuple := {tuple_equal}\n  have _carrierSame : Litex.Same _target _cart := {carrier_equal}\n  exact Litex.inOfSame _tuple _function _cart _target _tupleSame.symm _carrierSame.symm _tupleMember)", coordinate_proof.replace('\n', "\n  ")))
    }
}
