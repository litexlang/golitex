//! Replay the actual inverse predicate definitions and determinant evidence.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::*;
use std::collections::HashMap;

pub(super) fn is_matrix_inverse_predicate(fact: &AtomicFact) -> bool {
    matches!(
        fact,
        AtomicFact::IsMatrixInvFact(_)
            | AtomicFact::NotIsMatrixInvFact(_)
            | AtomicFact::MatrixInversibleFact(_)
            | AtomicFact::NotMatrixInversibleFact(_)
    )
}
pub(super) fn raw_matrix_inverse_predicate(
    fact: &AtomicFact,
    args: &[String],
) -> Result<String, LeanCompileError> {
    let (name, negative, arity) = match fact {
        AtomicFact::IsMatrixInvFact(_) => ("IsMatrixInvValue", false, 3),
        AtomicFact::NotIsMatrixInvFact(_) => ("IsMatrixInvValue", true, 3),
        AtomicFact::MatrixInversibleFact(_) => ("MatrixInversibleValue", false, 2),
        AtomicFact::NotMatrixInversibleFact(_) => ("MatrixInversibleValue", true, 2),
        _ => return Err(invalid("Family")),
    };
    if args.len() != arity {
        return Err(invalid("Arity"));
    }
    Ok(format!(
        "({}Litex.{name} M {})",
        if negative { "¬ " } else { "" },
        args.join(" ")
    ))
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("MatrixInversePredicate/{stage}"))
}
fn square(set: &Obj, n: &Obj) -> bool {
    matches!(set, Obj::SetFormer(SetFormer::MatrixSet(s)) if s.set.as_ref()==&Obj::StandardSet(StandardSet::C) && s.rows.ir()==n.ir() && s.cols.ir()==n.ir())
}
fn nonzero(fact: &Fact, a: &Obj, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if is_exact_zero(&f.right) && matches!(&f.left, Obj::MatrixOperator(MatrixOperator::Determinant(d)) if d.matrix.ir()==a.ir() && d.order.ir()==n.ir()))
}
fn product(fact: &Fact, a: &Obj, b: &Obj, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::EqualFact(f)) if matches!(&f.left,Obj::MatrixOperator(MatrixOperator::Multiply(p)) if p.left.ir()==a.ir() && p.right.ir()==b.ir() && p.rows.ir()==n.ir() && p.inner.ir()==n.ir() && p.cols.ir()==n.ir()) && matches!(&f.right,Obj::MatrixOperator(MatrixOperator::IdentityMatrix(i)) if i.order.ir()==n.ir()))
}
fn existence(fact: &Fact, a: &Obj, n: &Obj) -> bool {
    let Fact::ExistFact(e) = fact else {
        return false;
    };
    let [group] = e.typed_parameters.groups.as_slice() else {
        return false;
    };
    let [binding] = group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(set) = &group.param_type else {
        return false;
    };
    square(set, n)
        && matches!(e.facts.as_slice(),[QuantifierFreeFact::AtomicFact(AtomicFact::IsMatrixInvFact(f))] if f.matrix.ir()==a.ir() && f.order.ir()==n.ir() && f.inverse==Obj::Identifier(IdentifierObj::from_bound_name(binding)))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_selected_matrix_inverse_rule(
        &self,
        goal: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        proof: &crate::execute::execute_fact_stmt::matrix_inverse_predicates::IsMatrixInvSelectedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::IsMatrixInvFact(f) = goal else {
            return Err(invalid("SelectedFamily"));
        };
        if !matches!(&f.inverse,Obj::MatrixOperator(MatrixOperator::Inverse(p)) if p.matrix.ir()==f.matrix.ir() && p.order.ir()==f.order.ir())
            || !nonzero(
                &source_subject(&proof.determinant_nonzero)?,
                &f.matrix,
                &f.order,
            )
        {
            return Err(invalid("SelectedSubject"));
        }
        let d = self.matrix_inverse_domain_terms(goal, wd, position)?;
        let a = self.compile_object_reference(&f.matrix, position)?;
        let b = self.compile_object_reference(&f.inverse, position)?;
        let n = self.compile_object_reference(&f.order, position)?;
        let hd = self
            .compile_verify(
                &proof.determinant_nonzero,
                &position.atomic_search_prior(0)?,
            )?
            .1;
        Ok(format!("(Litex.isMatrixInvOfProducts {a} {b} {n} ({}) ({}) ({}) (Litex.matrixMultiplyInverseRight {a} {n} ({}) ({}) ({hd})) (Litex.matrixMultiplyInverseLeft {a} {n} ({}) ({}) ({hd})))",d[0],d[1],d[2],d[0],d[1],d[0],d[1]))
    }

    // Construct only native objects actually introduced by this recorded
    // inverse inference. Domain evidence comes from its cited source predicate.
    pub(super) fn compile_matrix_inverse_inferred_subject(
        &self,
        object: &Obj,
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        if !matches!(
            object,
            Obj::MatrixOperator(
                MatrixOperator::Determinant(_)
                    | MatrixOperator::Multiply(_)
                    | MatrixOperator::IdentityMatrix(_)
            )
        ) {
            return Ok(None);
        }
        let StoreFactResult::AtomicFact(stored) = store else {
            return Ok(None);
        };
        let fact = Fact::AtomicFact(stored.fact.clone());
        let mut current = Some(position);
        while let Some(cursor) = current {
            let context = match cursor.owner {
                SourceOwner::AtomicInference(Fact::AtomicFact(seed), infer) => Some((seed, infer)),
                SourceOwner::PropInference(captured) => match (&captured.store, &captured.infer) {
                    (StoreFactResult::AtomicFact(seed), Some(InferResult::AtomicFact(infer))) => {
                        Some((&seed.fact, infer))
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some((seed, infer)) = context {
                let (id, derived) = match infer {
                    InferAtomicFactResult::IsMatrixInvFact(r) if r.len() == 1 => {
                        let InferIsMatrixInvFactResult::DefinitionAndDeterminant(p) = &r[0];
                        (p.source_fact_id, &p.derived)
                    }
                    InferAtomicFactResult::MatrixInversibleFact(r) if r.len() == 1 => {
                        let InferMatrixInversibleFactResult::DefinitionAndDeterminant(p) = &r[0];
                        (p.source_fact_id, &p.derived)
                    }
                    _ => {
                        current = cursor.parent;
                        continue;
                    }
                };
                if id != seed.fact_id() {
                    return Err(invalid("ConstructorSeed"));
                }
                if !derived
                    .iter()
                    .any(|d| d.primary_fact_id() == store.primary_fact_id())
                {
                    current = cursor.parent;
                    continue;
                }
                let (a, b, n) = match seed {
                    AtomicFact::IsMatrixInvFact(f) => (&f.matrix, Some(&f.inverse), &f.order),
                    AtomicFact::MatrixInversibleFact(f) => (&f.matrix, None, &f.order),
                    _ => return Err(invalid("ConstructorFamily")),
                };
                // This cursor owns the already-emitted source fact. In a PropInference
                // frame its seed is not a derived conclusion of that frame.
                let name = format!("h_{}", id.value());
                let h = if cursor.is_local() {
                    name
                } else {
                    cursor.context_application(&name)
                };
                let h = format!("({h})");
                let aa = self.compile_object_reference(a, position)?;
                let nn = self.compile_object_reference(n, position)?;
                let hn = if b.is_some() {
                    format!("{h}.1")
                } else {
                    format!("(Litex.matrixInversibleNatural {aa} {nn} {h})")
                };
                let ha = if b.is_some() {
                    format!("{h}.2.1")
                } else {
                    format!("(Litex.matrixInversibleCarrier {aa} {nn} {h})")
                };
                return match object {
                    Obj::MatrixOperator(MatrixOperator::Determinant(d))
                        if d.matrix.ir() == a.ir()
                            && d.order.ir() == n.ir()
                            && nonzero(&fact, a, n) =>
                    {
                        Ok(Some(format!(
                            "(Litex.matrixDeterminant {aa} {nn} ({hn}) ({ha}))"
                        )))
                    }
                    Obj::MatrixOperator(MatrixOperator::Multiply(p)) if matches!(&stored.fact,AtomicFact::EqualFact(f) if f.left.ir()==object.ir()) =>
                    {
                        let Some(b) = b else {
                            return Err(invalid("ConstructorProductSeed"));
                        };
                        let reversed = product(&fact, b, a, n);
                        if !reversed && !product(&fact, a, b, n) {
                            return Err(invalid("ConstructorProduct"));
                        }
                        if p.rows.ir() != n.ir() || p.cols.ir() != n.ir() {
                            return Err(invalid("ConstructorShape"));
                        }
                        let bb = self.compile_object_reference(b, position)?;
                        let hb = format!("{h}.2.2.1");
                        let (left, right, hl, hr) = if reversed {
                            (&bb, &aa, &hb, &ha)
                        } else {
                            (&aa, &bb, &ha, &hb)
                        };
                        Ok(Some(format!("(Litex.matrixMultiply {left} {right} {nn} {nn} {nn} ({hn}) ({hn}) ({hn}) ({hl}) ({hr}))")))
                    }
                    Obj::MatrixOperator(MatrixOperator::IdentityMatrix(i))
                        if i.order.ir() == n.ir() =>
                    {
                        let Some(b) = b else {
                            return Err(invalid("ConstructorIdentitySeed"));
                        };
                        if !product(&fact, a, b, n) && !product(&fact, b, a, n) {
                            return Err(invalid("ConstructorIdentity"));
                        }
                        Ok(Some(format!("(Litex.identityMatrix {nn} ({hn}))")))
                    }
                    _ => Err(invalid("ConstructorSubject")),
                };
            }
            current = cursor.parent;
        }
        Ok(None)
    }
    fn matrix_inverse_domain_terms(
        &self,
        fact: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let args = atomic_fact_args_ref(fact);
        let n = *args.last().ok_or_else(|| invalid("DomainArguments"))?;
        let PredicateDomainProof::ByRequirements(requirements) =
            &wd.detailed_ref().predicate_domain
        else {
            return Err(invalid("DomainEvidence"));
        };
        if requirements.len() != args.len() {
            return Err(invalid("DomainStages"));
        }
        let mut terms = Vec::new();
        for (i, r) in requirements.iter().enumerate() {
            let valid = matches!(&r.requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if (i==0 && f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N)) || (i>0 && f.element.ir()==args[i-1].ir() && square(&f.set,n)));
            if !valid {
                return Err(invalid("DomainSubject"));
            }
            let prior = SourcePosition {
                before: args.len() + i,
                ..*position
            };
            let term = match &r.result {
                PredicateDomainRequirementProof::Verified(p) => {
                    if source_subject(p)? != r.requirement {
                        return Err(invalid("DomainProof"));
                    }
                    self.compile_verify(p, &prior)?.1
                }
                PredicateDomainRequirementProof::CheckedArgument(p) => {
                    self.compile_checked_domain_argument(&r.requirement, p, &args, i, &prior)?
                }
            };
            terms.push(term);
        }
        Ok(terms)
    }
    pub(super) fn compile_matrix_inverse_definition(
        &self,
        goal: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        facts: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if facts.len() != proofs.len() {
            return Err(invalid("DefinitionStages"));
        }
        for (f, p) in facts.iter().zip(proofs) {
            if source_subject(p)? != *f {
                return Err(invalid("DefinitionProof"));
            }
        }
        match goal {
            AtomicFact::IsMatrixInvFact(f) => {
                if facts.len() != 2
                    || !product(&facts[0], &f.matrix, &f.inverse, &f.order)
                    || !product(&facts[1], &f.inverse, &f.matrix, &f.order)
                {
                    return Err(invalid("CandidateClauses"));
                }
                let d = self.matrix_inverse_domain_terms(goal, wd, position)?;
                Ok(format!(
                    "(Litex.isMatrixInvOfProducts {} {} {} ({}) ({}) ({}) ({}) ({}))",
                    self.compile_object_reference(&f.matrix, position)?,
                    self.compile_object_reference(&f.inverse, position)?,
                    self.compile_object_reference(&f.order, position)?,
                    d[0],
                    d[1],
                    d[2],
                    self.compile_verify(&proofs[0], &position.atomic_search_prior(0)?)?
                        .1,
                    self.compile_verify(&proofs[1], &position.atomic_search_prior(1)?)?
                        .1
                ))
            }
            AtomicFact::MatrixInversibleFact(f) => {
                if facts.len() != 1 || !existence(&facts[0], &f.matrix, &f.order) {
                    return Err(invalid("ExistenceClause"));
                }
                Ok(self
                    .compile_verify(&proofs[0], &position.atomic_search_prior(0)?)?
                    .1)
            }
            _ => Err(invalid("DefinitionFamily")),
        }
    }
    pub(super) fn compile_matrix_inversible_rule(
        &self,
        goal: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        proof: &crate::execute::execute_fact_stmt::matrix_inverse_predicates::MatrixInversibleFromDeterminantProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::MatrixInversibleFact(f) = goal else {
            return Err(invalid("NonzeroFamily"));
        };
        if !nonzero(
            &source_subject(&proof.determinant_nonzero)?,
            &f.matrix,
            &f.order,
        ) {
            return Err(invalid("NonzeroSubject"));
        }
        let d = self.matrix_inverse_domain_terms(goal, wd, position)?;
        Ok(format!(
            "(Litex.matrixInversibleOfNonzero {} {} ({}) ({}) ({}))",
            self.compile_object_reference(&f.matrix, position)?,
            self.compile_object_reference(&f.order, position)?,
            d[0],
            d[1],
            self.compile_verify(
                &proof.determinant_nonzero,
                &position.atomic_search_prior(0)?
            )?
            .1
        ))
    }
    pub(super) fn compile_matrix_not_inversible_rule(
        &self,
        goal: &AtomicFact,
        proof: &crate::execute::execute_fact_stmt::matrix_inverse_predicates::NotMatrixInversibleFromDeterminantProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotMatrixInversibleFact(f) = goal else {
            return Err(invalid("ZeroFamily"));
        };
        let zero = source_subject(&proof.determinant_zero)?;
        let Fact::AtomicFact(zero) = zero else {
            return Err(invalid("ZeroSubject"));
        };
        let reversed =
            negate_atomic_fact(&zero, zero.fact_id()).ok_or_else(|| invalid("ZeroNegation"))?;
        if !nonzero(&Fact::AtomicFact(reversed), &f.matrix, &f.order) {
            return Err(invalid("ZeroSubject"));
        }
        Ok(format!(
            "(fun _inverse => (Litex.matrixInversibleNonzero {} {} _inverse) ({}))",
            self.compile_object_reference(&f.matrix, position)?,
            self.compile_object_reference(&f.order, position)?,
            self.compile_verify(&proof.determinant_zero, &position.atomic_search_prior(0)?)?
                .1
        ))
    }
    pub(super) fn compile_matrix_inverse_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (source, derived, candidate) = match infer {
            InferAtomicFactResult::IsMatrixInvFact(r) if r.len() == 1 => {
                let InferIsMatrixInvFactResult::DefinitionAndDeterminant(p) = &r[0];
                (p.source_fact_id, &p.derived, true)
            }
            InferAtomicFactResult::MatrixInversibleFact(r) if r.len() == 1 => {
                let InferMatrixInversibleFactResult::DefinitionAndDeterminant(p) = &r[0];
                (p.source_fact_id, &p.derived, false)
            }
            _ => return Err(invalid("InferenceFamily")),
        };
        let (a, b, n) = match seed {
            Fact::AtomicFact(AtomicFact::IsMatrixInvFact(f)) if candidate => {
                (&f.matrix, Some(&f.inverse), &f.order)
            }
            Fact::AtomicFact(AtomicFact::MatrixInversibleFact(f)) if !candidate => {
                (&f.matrix, None, &f.order)
            }
            _ => return Err(invalid("InferenceSeed")),
        };
        if source != seed.fact_id() || derived.len() != if candidate { 5 } else { 2 } {
            return Err(invalid("InferenceIdentity"));
        }
        let aa = self.compile_object_reference(a, position)?;
        let nn = self.compile_object_reference(n, position)?;
        let h = format!("({})", compiled.1);
        let inverse = if let Some(b) = b {
            format!(
                "(Litex.isMatrixInvInversible {aa} {} {nn} {h})",
                self.compile_object_reference(b, position)?
            )
        } else {
            h.clone()
        };
        let mut out = Vec::new();
        for (i, store) in derived.iter().enumerate() {
            let prior = SourcePosition {
                before: position.before + i,
                ..*position
            };
            let fact = self.resolve_fact(store.primary_fact_id(), &prior)?;
            self.validate_store(&store.store, &fact)?;
            let term = if let Some(b) = b {
                match i {
                    0 | 1 => {
                        if !product(
                            &fact,
                            if i == 0 { a } else { b },
                            if i == 0 { b } else { a },
                            n,
                        ) {
                            return Err(invalid("InferenceProduct"));
                        }
                        format!("(Litex.isMatrixInvProducts {aa} {} {nn} {h}.1 {h}.2.1 {h}.2.2.1 {h}).{}",self.compile_object_reference(b,&prior)?,i+1)
                    }
                    2 => {
                        if !existence(&fact, a, n) {
                            return Err(invalid("InferenceExistence"));
                        }
                        inverse.clone()
                    }
                    3 => {
                        if !matches!(&fact,Fact::AtomicFact(AtomicFact::MatrixInversibleFact(f)) if f.matrix.ir()==a.ir() && f.order.ir()==n.ir())
                        {
                            return Err(invalid("InferenceInversible"));
                        }
                        inverse.clone()
                    }
                    4 => {
                        if !nonzero(&fact, a, n) {
                            return Err(invalid("InferenceNonzero"));
                        }
                        format!("(Litex.matrixInversibleNonzero {aa} {nn} {inverse})")
                    }
                    _ => return Err(invalid("InferenceIndex")),
                }
            } else if i == 0 {
                if !existence(&fact, a, n) {
                    return Err(invalid("InferenceExistence"));
                }
                h.clone()
            } else {
                if !nonzero(&fact, a, n) {
                    return Err(invalid("InferenceNonzero"));
                }
                format!("(Litex.matrixInversibleNonzero {aa} {nn} {h})")
            };
            let prop = self.compile_function_raw_predicate(&fact, &prior, &HashMap::new())?;
            out.push(self.emit_internal_fact(&fact, &(prop, term), &prior)?);
        }
        Ok(out)
    }
}
