use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_register_stmt::*;
use crate::parse::prop_registration_shape::*;
use crate::prelude::*;

/// The registration's checked forall is its entire mathematical content.
/// Search registration stays in Runtime; Lean consumes an ordinary theorem.
pub(super) fn registration_proof(
    result: &ExecRegisterStmtResult,
) -> Result<&VerifyFactResult, LeanCompileError> {
    let (predicate, proof, shape) = match result {
        ExecRegisterStmtResult::ReflexiveProp(ExecRegisterReflexivePropStmtResult::Success(p)) => {
            (&p.prop, &p.forall_proof, 0)
        }
        ExecRegisterStmtResult::SymmetricProp(ExecRegisterSymmetricPropStmtResult::Success(p)) => {
            (&p.prop, &p.forall_proof, 1)
        }
        ExecRegisterStmtResult::TransitiveProp(ExecRegisterTransitivePropStmtResult::Success(
            p,
        )) => (&p.prop, &p.forall_proof, 2),
        _ => return Err(LeanCompileError::unsupported("Register/Failed")),
    };
    let Fact::ForallFact(fact) = source_subject(proof)? else {
        return Err(LeanCompileError::unsupported("Register/Forall"));
    };
    let actual = match shape {
        0 => reflexive_prop_name_from_forall(&fact),
        1 => symmetric_prop_registration_from_forall(&fact).map(|(name, _)| name),
        _ => transitive_prop_name_from_forall(&fact),
    }
    .map_err(|error| LeanCompileError::new("Register/Shape", &error))?;
    if &actual != predicate {
        return Err(LeanCompileError::unsupported("Register/Predicate"));
    }
    Ok(proof)
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_register_statement(
        &self,
        result: &ExecRegisterStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let proof = registration_proof(result)?;
        self.emit_fact(
            &source_subject(proof)?,
            self.compile_verify(proof, position)?,
            index,
            local,
            position,
        )
    }

    pub(in crate::compile_to_lean) fn apply_registered_law(
        &self,
        proof: &VerifyFactResult,
        declaration: &SourcePosition<'_>,
        arguments: &[&Obj],
        premises: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::ForallFact(fact) = source_subject(proof)? else {
            return Err(LeanCompileError::unsupported("Register/Forall"));
        };
        if fact.typed_parameters.ordered_param_ids().len() != arguments.len()
            || fact.dom_facts.len() != premises.len()
        {
            return Err(LeanCompileError::unsupported("Register/ApplicationArity"));
        }
        let name = format!("h_{}", fact.fact_id.value());
        let mut terms = vec![if declaration.is_local() {
            name
        } else {
            declaration.context_application(&name)
        }];
        for argument in arguments {
            let term = self.compile_object_reference(argument, position)?;
            terms.push(format!("{term} (Litex.isSet {term})"));
        }
        terms.extend(premises.iter().map(|proof| format!("({proof})")));
        Ok(format!("({})", terms.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_registered_rewrite(
        &self,
        fact: &AtomicFact,
        rule: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_rewrite::AtomicExceptEqualityFactSearchProofByKnownRewrite,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_rewrite::AtomicExceptEqualityFactSearchProofByKnownRewrite as Rule;
        let AtomicFact::NormalAtomicFact(target) = fact else {
            return Err(LeanCompileError::unsupported("Register/Target"));
        };
        match rule {
            Rule::Reflexivity(p) => {
                if p.cite_prop != target.predicate
                    || target.body.len() != 2
                    || target.body[0].ir() != target.body[1].ir()
                {
                    return Err(LeanCompileError::unsupported("Register/ReflexiveSubject"));
                }
                let (law, declaration) = position.visible_registration(|r| matches!(r,
                    ExecRegisterStmtResult::ReflexiveProp(ExecRegisterReflexivePropStmtResult::Success(s)) if s.prop == p.cite_prop))?;
                self.apply_registered_law(
                    registration_proof(law)?,
                    &declaration,
                    &[&target.body[0]],
                    &[],
                    position,
                )
            }
            Rule::Symmetry(p) => {
                if p.cite_prop != target.predicate
                    || source_subject(&p.proof_of_alternate_fact)? != p.alternate_fact
                {
                    return Err(LeanCompileError::unsupported("Register/SymmetricSubject"));
                }
                let (law, declaration) = position.visible_registration(|r| {
                    let ExecRegisterStmtResult::SymmetricProp(
                        ExecRegisterSymmetricPropStmtResult::Success(s),
                    ) = r
                    else {
                        return false;
                    };
                    let Ok(Fact::ForallFact(f)) = source_subject(&s.forall_proof) else {
                        return false;
                    };
                    s.prop == p.cite_prop
                        && symmetric_prop_registration_from_forall(&f)
                            .is_ok_and(|(_, g)| g == p.argument_permutation)
                })?;
                let proof = registration_proof(law)?;
                let Fact::ForallFact(source) = source_subject(proof)? else {
                    unreachable!()
                };
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NormalAtomicFact(conclusion)) =
                    &source.then_facts[0]
                else {
                    unreachable!()
                };
                let Fact::AtomicFact(AtomicFact::NormalAtomicFact(premise)) = &source.dom_facts[0]
                else {
                    unreachable!()
                };
                let Fact::AtomicFact(AtomicFact::NormalAtomicFact(alternate)) = &p.alternate_fact
                else {
                    return Err(LeanCompileError::unsupported("Register/SymmetricPremise"));
                };
                if conclusion.body.len() != target.body.len()
                    || premise.body.len() != alternate.body.len()
                    || alternate.predicate != target.predicate
                {
                    return Err(LeanCompileError::unsupported("Register/SymmetricArity"));
                }
                let argument = |obj: &Obj| -> Result<&Obj, LeanCompileError> {
                    conclusion
                        .body
                        .iter()
                        .position(|x| x.ir() == obj.ir())
                        .map(|i| &target.body[i])
                        .ok_or_else(|| LeanCompileError::unsupported("Register/Parameter"))
                };
                for (original, actual) in premise.body.iter().zip(&alternate.body) {
                    if argument(original)?.ir() != actual.ir() {
                        return Err(LeanCompileError::unsupported(
                            "Register/PermutationDirection",
                        ));
                    }
                }
                let mut arguments = Vec::new();
                for id in source.typed_parameters.ordered_param_ids() {
                    let original = conclusion.body.iter().find(|obj| matches!(obj, Obj::Identifier(IdentifierObj::Plain { id: bound, .. }) if *bound == id))
                        .ok_or_else(|| LeanCompileError::unsupported("Register/Parameter"))?;
                    arguments.push(argument(original)?);
                }
                let premise = self.compile_verify(&p.proof_of_alternate_fact, position)?.1;
                self.apply_registered_law(proof, &declaration, &arguments, &[premise], position)
            }
        }
    }
}
