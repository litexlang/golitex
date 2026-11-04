//! Replay a selected native property, its exact matches and checked premises.
use super::compile_builtin_laplace_determinant::{
    laplace_determinant_law_term, validate_laplace_determinant_law,
};
use super::compile_builtin_triangular_determinant::{
    triangular_determinant_law_term, validate_triangular_determinant_law,
};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::search_native_matrix_property::{
    matrix_property_natural_sum_matches, matrix_property_selection_matches, MatrixPropertyKind,
    MatrixPropertyRequirementProof, MatrixPropertySumForm, NativeMatrixPropertyProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_native_matrix_property(
        &self,
        goal: &AtomicFact,
        proof: &NativeMatrixPropertyProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use MatrixPropertyKind as K;
        let a = proof.application();
        let kind = proof.kind();
        let count = match kind {
            K::DetLaplaceRow | K::DetLaplaceColumn => 5,
            K::DetUpperTriangular | K::DetLowerTriangular => 4,
            K::RankRows | K::RankCols => 3,
            K::RankProductLeft | K::RankProductRight | K::FrobeniusTriangle => 6,
            K::InnerSelfReal
            | K::InnerSelfNonnegative
            | K::InnerSelfImaginary
            | K::EuclideanNonnegative
            | K::EuclideanSquareSum => 2,
            K::FrobeniusNonnegative
            | K::FrobeniusSquareSum
            | K::EuclideanScale
            | K::EuclideanZeroElim
            | K::EuclideanZeroIntro => 3,
            K::CauchySchwarz
            | K::EuclideanTriangle
            | K::FrobeniusZeroElim
            | K::FrobeniusZeroIntro => 4,
            K::InnerLinearRight => 8,
            K::ApplyAdjoint => 7,
            K::InverseFromCandidate => 9,
        };
        if a.arguments.len() != kind.theorem().arity()
            || a.requirements.len() != count
            || a.requirement_proofs.len() != count
            || a.matching.comparisons.len() != 2
            || std::mem::discriminant(&a.conclusion) != std::mem::discriminant(goal)
            || !matrix_property_selection_matches(kind, &a.arguments, &a.conclusion)
        {
            return Err(invalid("SelectionOrStages"));
        }
        let original = match &a.schema {
            Fact::AtomicFact(atomic) => atomic,
            Fact::ForallFact(f)
                if f.typed_parameters.groups.is_empty()
                    && f.dom_facts.len() == 1
                    && f.then_facts.len() == 1 =>
            {
                if a.requirements.last() != f.dom_facts.first() {
                    return Err(invalid("ConditionalPremise"));
                }
                let ExistOrAndChainAtomicFact::AtomicFact(atomic) = &f.then_facts[0] else {
                    return Err(invalid("ConditionalConclusion"));
                };
                atomic
            }
            _ => return Err(invalid("Schema")),
        };
        if !matrix_property_selection_matches(kind, &a.arguments, original) {
            return Err(invalid("OriginalSelection"));
        }
        match &a.sum_form {
            MatrixPropertySumForm::Original if original.ir() != a.conclusion.ir() => {
                return Err(invalid("OriginalConclusion"))
            }
            MatrixPropertySumForm::Natural {
                original: old,
                natural,
            } => {
                let (AtomicFact::LessEqualFact(before), AtomicFact::LessEqualFact(after)) =
                    (original, &a.conclusion)
                else {
                    return Err(invalid("NaturalTriangleFamily"));
                };
                let (
                    Obj::MatrixOperator(MatrixOperator::EuclideanNorm(b)),
                    Obj::MatrixOperator(MatrixOperator::EuclideanNorm(c)),
                ) = (&before.left, &after.left)
                else {
                    return Err(invalid("NaturalTriangleNorm"));
                };
                if kind != K::EuclideanTriangle
                    || b.vector.as_ref() != old
                    || c.vector.as_ref() != natural
                    || b.dimension != c.dimension
                    || before.right != after.right
                    || !matrix_property_natural_sum_matches(old, natural, &a.arguments)
                {
                    return Err(invalid("NaturalTriangleSubjects"));
                }
            }
            _ => {}
        }
        if a.matching.reversed && !matches!(goal, AtomicFact::EqualFact(_)) {
            return Err(invalid("Orientation"));
        }
        let source_args = crate::ast::fact::atomic_fact_args_ref(&a.conclusion);
        let goal_args = crate::ast::fact::atomic_fact_args_ref(goal);
        if source_args.len() != 2 || goal_args.len() != 2 {
            return Err(invalid("Arity"));
        }
        let mut lines = Vec::new();
        let mut terms = Vec::new();
        for (index, child) in a.matching.comparisons.iter().enumerate() {
            let source = source_args[if a.matching.reversed {
                1 - index
            } else {
                index
            }];
            let target = goal_args[index];
            let target_term = self.compile_object_reference(target, position)?;
            // Structural alpha identity reuses the parent's actual formation;
            // it does not manufacture WD for the schema's fresh binder names.
            let (source_term, equal) = match child {
                EqualFactSearchedProof::ByTheyAreTheSame(p) => {
                    let subject = EqualFact {
                        fact_id: goal.fact_id(),
                        left: source.clone(),
                        right: target.clone(),
                        line_file: None,
                    };
                    let Some(actual) = search_equal_fact_proof_by_they_are_the_same(&subject)
                    else {
                        return Err(invalid("IdentitySubject"));
                    };
                    if !same_identity_route(p, &actual) {
                        return Err(invalid("IdentityEvidence"));
                    }
                    (target_term.clone(), "rfl".to_string())
                }
                EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(_),
                )
                | EqualFactSearchedProof::ByClosedCalculation(_) => {
                    let subject = EqualFact {
                        fact_id: goal.fact_id(),
                        left: source.clone(),
                        right: target.clone(),
                        line_file: None,
                    };
                    (
                        self.compile_object_reference(source, position)?,
                        self.compile_equality_search(&subject, child, position)?,
                    )
                }
                _ => return Err(invalid("DirectMatchRoute")),
            };
            lines.push(format!("have _matrix_match_{index} : Litex.Same ({source_term}) ({target_term}) := {equal}"));
            terms.push(source_term);
        }
        if a.matching.reversed {
            terms.reverse();
        }
        let mut references = Vec::new();
        for (index, (requirement, child)) in
            a.requirements.iter().zip(&a.requirement_proofs).enumerate()
        {
            let checked = match child {
                MatrixPropertyRequirementProof::Verified(p) => {
                    if source_subject(p)? != *requirement {
                        return Err(invalid("RequirementSubject"));
                    }
                    p
                }
                MatrixPropertyRequirementProof::ZeroVectorAlpha {
                    source,
                    comparison,
                    alpha,
                } => {
                    let source_fact = source_subject(source)?;
                    let (
                        Fact::AtomicFact(AtomicFact::EqualFact(actual)),
                        Fact::AtomicFact(AtomicFact::EqualFact(wanted)),
                    ) = (&source_fact, requirement)
                    else {
                        return Err(invalid("AlphaPremiseFamily"));
                    };
                    let Some(actual_alpha) =
                        search_equal_fact_proof_by_they_are_the_same(comparison)
                    else {
                        return Err(invalid("AlphaPremiseMatch"));
                    };
                    if kind != K::EuclideanZeroIntro
                        || actual.left != wanted.left
                        || actual.right != comparison.left
                        || wanted.right != comparison.right
                        || !same_identity_route(alpha, &actual_alpha)
                    {
                        return Err(invalid("AlphaPremiseSubject"));
                    }
                    source
                }
            };
            let compiled = self.compile_verify(checked, position)?;
            let reference = format!("_matrix_requirement_{index}");
            lines.push(format!(
                "have {reference} : {} := {}",
                compiled.0, compiled.1
            ));
            references.push(reference);
        }
        let objects = a
            .arguments
            .iter()
            .map(|o| self.compile_object_reference(o, position))
            .collect::<Result<Vec<_>, _>>()?;
        let l = &terms[0];
        let r = &terms[1];
        let h = &references;
        let law=match kind {
            K::DetLaplaceRow|K::DetLaplaceColumn=>{
                let AtomicFact::EqualFact(f)=&a.conclusion else {return Err(invalid("LaplaceFamily"));};
                validate_laplace_determinant_law(kind==K::DetLaplaceRow, &a.arguments, &a.requirements, f)?;
                laplace_determinant_law_term(kind==K::DetLaplaceRow,&objects[0],&objects[1],&objects[2],r,h)
            }
            K::DetUpperTriangular|K::DetLowerTriangular=>{
                let AtomicFact::EqualFact(f)=&a.conclusion else {return Err(invalid("TriangularFamily"));};
                validate_triangular_determinant_law(kind==K::DetUpperTriangular, &a.arguments, &a.requirements, f)?;
                triangular_determinant_law_term(kind==K::DetUpperTriangular,&objects[0],&objects[1],r,h)
            }
            K::RankRows=>format!("Litex.matrixRankLeRows ({l})"),
            K::RankCols=>format!("Litex.matrixRankLeCols ({l})"),
            K::RankProductLeft|K::RankProductRight=>format!("(Litex.matrixRankProductBounds {} {} {} {} {} {}).{}",objects.join(" "),h[0],h[1],h[4],h[2],h[5],if kind==K::RankProductLeft{1}else{2}),
            K::InnerSelfReal=>format!("(Litex.finiteInnerProductSelfPositive ({l}) (by rfl)).1"),
            K::InnerSelfNonnegative=>format!("(by\n  let _inner_re := {r}\n  have _positive := Litex.finiteInnerProductSelfPositive _inner_re.val.arg (by rfl)\n  change Litex.realBound true (M.number 0) (Litex.complexUnaryValue (fun z : ℂ => (z.re : ℂ)) (Litex.denote _inner_re.val.arg))\n  rw [Litex.realPartOfRealValue _ _positive.1]\n  exact _positive.2\n)"),
            K::InnerSelfImaginary=>format!("(by\n  let _inner_img := {l}\n  have _positive := Litex.finiteInnerProductSelfPositive _inner_img.val.arg (by rfl)\n  exact Litex.imaginaryPartOfRealValue (Litex.denote _inner_img.val.arg) _positive.1\n)"),
            K::EuclideanNonnegative=>format!("Litex.euclideanNormNonnegative ({r})"),
            K::FrobeniusNonnegative=>format!("Litex.frobeniusNormNonnegative ({r})"),
            K::CauchySchwarz=>format!("(by\n  let _modulus := {l}\n  exact Litex.finiteInnerProductCauchySchwarz _modulus.val.arg\n)"),
            K::EuclideanScale=>format!("(by\n  let _scaled := {l}\n  exact Litex.euclideanNormScale _scaled _scaled.val.vector (Litex.denote {}) (Litex.denote {}) {} {} (by rfl) (by rfl) (by rfl)\n)",objects[0],objects[1],h[0],h[2]),
            K::InnerLinearRight=>format!("(by\n  let _inner := {l}\n  exact Litex.finiteInnerProductLinearRight _inner _inner.val.right (Litex.denote {}) (Litex.denote {}) (Litex.denote {}) (Litex.denote {}) {} {} {} {} (by rfl) (by rfl) (by rfl)\n)",objects[1],objects[2],objects[3],objects[4],h[3],h[5],h[6],h[7]),
            K::EuclideanTriangle=>format!("(by\n  let _triangle := {l}\n  exact Litex.{} _triangle _triangle.val.vector {} {} {} {} (by rfl) (by rfl) (by rfl)\n)",if matches!(a.sum_form,MatrixPropertySumForm::Natural{..}){"euclideanNormTriangleNaturalFormula"}else{"euclideanNormTriangleFormula"},objects[0],objects[1],h[1],h[3]),
            K::FrobeniusTriangle=>format!("(by\n  let _triangle := {l}\n  exact Litex.frobeniusNormTriangleEntrywise _triangle.val.matrix (by rfl)\n)"),
            K::EuclideanSquareSum|K::FrobeniusSquareSum=>{
                let AtomicFact::EqualFact(f)=&a.conclusion else {return Err(invalid("SquareFamily"));};
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power))=&f.left else {return Err(invalid("SquareRoot"));};
                let norm=self.compile_object_reference(&power.base,position)?;
                let name=if kind==K::EuclideanSquareSum{"euclideanNorm"}else{"frobeniusNorm"};
                format!("(Litex.{name}Square ({norm})).trans (congrArg M.number (Litex.{name}SumFormula ({norm}) ({r}).val.function (by rfl) (by rfl)))")
            }
            K::EuclideanZeroElim|K::EuclideanZeroIntro=>{
                let zero=if kind==K::EuclideanZeroElim {r.clone()}else{
                    let checked=match a.requirement_proofs.last().ok_or_else(||invalid("ZeroPremise"))? {MatrixPropertyRequirementProof::Verified(p)=>p,MatrixPropertyRequirementProof::ZeroVectorAlpha{source,..}=>source};
                    let Fact::AtomicFact(AtomicFact::EqualFact(f))=source_subject(checked)? else {return Err(invalid("ZeroPremise"));};
                    let scope=SourcePosition::new(Some(position),SourceOwner::Verify(checked),usize::MAX);
                    self.compile_object_reference(&f.right,&scope)?
                };
                format!("(Litex.euclideanNormZeroFormula {} {} ({zero}) {} {} (by rfl) (by rfl) (by intro k; rfl)).{} {}",objects[0],objects[1],h[0],h[1],if kind==K::EuclideanZeroElim{1}else{2},h[2])
            }
            K::FrobeniusZeroElim|K::FrobeniusZeroIntro=>format!("(Litex.frobeniusNormZeroCharacterization {} {} {} {} {} {}).{} {}",objects[0],objects[1],objects[2],h[0],h[1],h[2],if kind==K::FrobeniusZeroElim{1}else{2},h[3]),
            K::ApplyAdjoint=>format!("Litex.matrixInnerProductAdjoint {} {} {} {} {} {}",objects.join(" "),h[0],h[1],h[2],h[4],h[6]),
            K::InverseFromCandidate=>format!("Litex.matrixInverseOfCandidate {} {} {} {} {} {} {}",objects.join(" "),h[0],h[2],h[5],h[6],h[7],h[8]),
        };
        let raw = terms
            .iter()
            .map(|s| format!("(Litex.denote ({s}))"))
            .collect::<Vec<_>>();
        let proposition = self.compile_atomic_raw_proposition(&a.conclusion, &raw, position)?;
        lines.push(format!("have _matrix_law : {proposition} := {law}"));
        let predicate =
            self.compile_atomic_raw_proposition(goal, &["x".into(), "y".into()], position)?;
        let law = if a.matching.reversed {
            "_matrix_law.symm"
        } else {
            "_matrix_law"
        };
        lines.push(format!("exact (congrArg₂ (fun (x y : M.Value) => {predicate}) _matrix_match_0 _matrix_match_1).mp ({law})"));
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("NativeMatrixProperty/{stage}"))
}

fn same_identity_route(left: &TheyAreTheSameProof, right: &TheyAreTheSameProof) -> bool {
    match (left, right) {
        (TheyAreTheSameProof::SameIr(_), TheyAreTheSameProof::SameIr(_)) => true,
        (
            TheyAreTheSameProof::SameFreeParamShape(left),
            TheyAreTheSameProof::SameFreeParamShape(right),
        ) => std::mem::discriminant(left) == std::mem::discriminant(right),
        _ => false,
    }
}
