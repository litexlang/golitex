use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::compile_fact_stmt_result::validate_finite_signature;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, ExecReleaseThmStmtSuccess, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate;
use crate::execute::execute_fact_stmt::function_domain::{
    function_domains_alpha_equal, CompleteFunctionDomainSourceProof, FunctionDomainComparisonProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_builtin_tuple_theorem(
        &self,
        proof: &ExecReleaseThmStmtSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        let Some(builtin) = &proof.builtin else {
            return Err(LeanCompileError::unsupported("TupleTheorem/Application"));
        };
        if builtin.theorem != BuiltinTheoremId::TupleEqualFromCoordinates
            || !matches!(
                proof.theorem_derivation,
                TheoremDerivationProof::NativeSchema
            )
            || !proof.type_proofs.is_empty()
            || !proof.type_stores.is_empty()
        {
            return Err(LeanCompileError::unsupported("TupleTheorem/Contract"));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &proof.call.arguments else {
            return Err(LeanCompileError::unsupported("TupleTheorem/Arguments"));
        };
        if proof.call.name.local_name() != "tuple_equal_from_coordinates"
            || arguments != &builtin.arguments
            || arguments.len() != 2
            || builtin.conclusions.len() != 1
            || proof.conclusions_wd.len() != 1
        {
            return Err(LeanCompileError::unsupported("TupleTheorem/Arguments"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported("TupleTheorem/Conclusion"));
        };
        if conclusion.left.ir() != arguments[0].ir() || conclusion.right.ir() != arguments[1].ir() {
            return Err(LeanCompileError::unsupported("TupleTheorem/Conclusion"));
        }
        let Some(BuiltinFunctionDomainProof::TupleEquality { left, right }) =
            &proof.function_domain
        else {
            return Err(LeanCompileError::unsupported(
                "TupleTheorem/CompleteDomains",
            ));
        };
        if !function_domains_alpha_equal(&left.target, &right.target) {
            return Err(LeanCompileError::unsupported(
                "TupleTheorem/DomainAgreement",
            ));
        }
        let mut definitions = Vec::new();
        let mut arity = None;
        let left_complete =
            SourcePosition::new(Some(position), SourceOwner::FunctionDomainWD(left), 2);
        let right_complete = SourcePosition::new(
            Some(&left_complete),
            SourceOwner::FunctionDomainWD(right),
            2,
        );
        for (index, (argument, domain)) in arguments.iter().zip([left, right]).enumerate() {
            let CompleteFunctionDomainSourceProof::FiniteFunction(finite) = &domain.source.source
            else {
                return Err(LeanCompileError::unsupported("TupleTheorem/FiniteDomain"));
            };
            validate_finite_signature(finite)?;
            let n = finite.source.dimension();
            if arity.is_some_and(|expected| expected != n)
                || domain.source.signature.ir() != finite.signature.ir()
                || !matches!(
                    domain.comparison,
                    FunctionDomainComparisonProof::AlphaEquivalent
                )
                || !function_domains_alpha_equal(&finite.signature, &domain.target)
            {
                return Err(LeanCompileError::unsupported(
                    "TupleTheorem/CompleteDomains",
                ));
            }
            arity = Some(n);
            ensure_object(argument, &domain.function_wd)?;
            ensure_object(
                &Obj::FunctionSpace(FunctionSpace::FnSet(domain.target.clone())),
                &domain.target_wd,
            )?;
            let domain_position = SourcePosition::new(
                Some(if index == 0 { position } else { &left_complete }),
                SourceOwner::FunctionDomainWD(domain),
                0,
            );
            let function = self.compile_wd(&domain.function_wd, &domain_position)?;
            let function_formed = SourcePosition {
                before: 1,
                ..domain_position
            };
            let target = self.compile_wd(&domain.target_wd, &function_formed)?;
            let formed = SourcePosition {
                before: 2,
                ..domain_position
            };
            let (cart, member) =
                self.compile_cart_shape_member(argument, &finite.source, &formed)?;
            definitions.push(format!("let _checked_domain_{index} := {target}"));
            definitions.push(format!("let _tuple_peer_{index} := {function}"));
            definitions.push(format!(
                "have _tuple_member_{index} : Litex.In _tuple_peer_{index} {cart} := {member}"
            ));
        }
        let n = arity.unwrap();
        let invocation = SourcePosition {
            parent: Some(&right_complete),
            ..*position
        };
        let position = &invocation;
        if builtin.requirements.len() != n
            || proof.dom_proofs.len() != n
            || proof.dom_stores.len() != n
        {
            return Err(LeanCompileError::unsupported(
                "TupleTheorem/CoordinateCount",
            ));
        }
        let mut coordinates = Vec::new();
        for index in 0..n {
            let requirement = &builtin.requirements[index];
            let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = requirement else {
                return Err(LeanCompileError::unsupported(
                    "TupleTheorem/CoordinateFamily",
                ));
            };
            let a = finite_function_coordinate(&arguments[0], index)
                .map_err(|e| LeanCompileError::new("TupleTheorem/Coordinate", &e))?;
            let b = finite_function_coordinate(&arguments[1], index)
                .map_err(|e| LeanCompileError::new("TupleTheorem/Coordinate", &e))?;
            if equality.left.ir() != a.ir()
                || equality.right.ir() != b.ir()
                || source_subject(&proof.dom_proofs[index])? != *requirement
            {
                return Err(LeanCompileError::unsupported(
                    "TupleTheorem/CoordinateSubject",
                ));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(&proof.dom_proofs[index], &prior)?;
            self.validate_store(&proof.dom_stores[index].store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            let reference = format!("h_{}", requirement.fact_id().value());
            let published = SourcePosition {
                before: index + 1,
                ..*position
            };
            definitions.extend(self.compile_stored_inferences(
                &proof.dom_stores[index],
                requirement,
                &(compiled.0, reference.clone()),
                &published,
            )?);
            let mut sides = Vec::new();
            for (peer, coordinate) in [&a, &b].into_iter().enumerate() {
                let value = self.compile_normalization_value(coordinate, &published)?;
                let body = if matches!(arguments[peer], Obj::ProductShape(ProductShape::Tuple(_))) {
                    format!("Litex.tuple_coordinate _tuple_peer_{peer} ({index} : Fin {n})")
                } else {
                    format!("by\n    have _index : Litex.FiniteFunction.index (M := M) ({index} : Fin {n}) = M.number ({} : ℂ) := by norm_num [Litex.FiniteFunction.index]\n    exact congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple_peer_{peer})) _index", index+1)
                };
                sides.push(format!("(show Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple_peer_{peer}) (Litex.FiniteFunction.index ({index} : Fin {n})) = {value} from {body})"));
            }
            coordinates.push(format!(
                "({}).trans ({reference}.trans ({}).symm)",
                sides[0], sides[1]
            ));
        }
        let formed = SourcePosition {
            before: n,
            ..*position
        };
        self.compile_fact_wd(&proof.conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let application = format!(
            "(Litex.FiniteFunction.cart_ext (M := M) _tuple_member_0 _tuple_member_1 {})",
            finite_vector_proof(&coordinates)
        );
        Ok((definitions, application, builtin.conclusions.clone()))
    }
}
