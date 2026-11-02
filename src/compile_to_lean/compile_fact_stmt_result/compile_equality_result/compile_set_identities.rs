use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_sym_diff_identity(
        &self,
        fact: &EqualFact,
        rule: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_symmetric_difference::SymmetricDifferenceEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_symmetric_difference::SymmetricDifferenceEqualityProof as Rule;
        if let Rule::SymDiffFiniteRationals(proof) = rule {
            return self.compile_sym_diff_finite_rationals(fact, proof, position);
        }
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if let Rule::IntersectionDistributesSymDiff(_) = rule {
                let Obj::SetOperator(SetOperator::Intersect(intersection)) = left else {
                    continue;
                };
                let Obj::SetOperator(SetOperator::SymmetricDifference(inner)) =
                    intersection.right.as_ref()
                else {
                    continue;
                };
                let Obj::SetOperator(SetOperator::SymmetricDifference(result)) = right else {
                    continue;
                };
                let (
                    Obj::SetOperator(SetOperator::Intersect(a)),
                    Obj::SetOperator(SetOperator::Intersect(b)),
                ) = (result.left.as_ref(), result.right.as_ref())
                else {
                    continue;
                };
                if a.left.ir() != intersection.left.ir()
                    || b.left.ir() != intersection.left.ir()
                    || a.right.ir() != inner.left.ir()
                    || b.right.ir() != inner.right.ir()
                {
                    continue;
                }
                let term = self.compile_object_reference(left, position)?;
                self.compile_object_reference(right, position)?;
                let orientation = if reversed { ".symm" } else { "" };
                return Ok(format!("(let _litex_set := {term}; (Litex.intersectDistributesSymmetricDifference _litex_set.val.left _litex_set.val.right.val.left _litex_set.val.right.val.right){orientation})"));
            }
            let Obj::SetOperator(SetOperator::SymmetricDifference(p)) = left else {
                continue;
            };
            let law = match rule {
                Rule::SymDiffSelf(_) if p.left.ir() == p.right.ir() && empty_set(right) => {
                    "symmetricDifferenceSelf _litex_set.val.left"
                }
                Rule::SymDiffDefinition(_) => {
                    let Obj::SetOperator(SetOperator::Union(u)) = right else {
                        continue;
                    };
                    let (
                        Obj::SetOperator(SetOperator::SetMinus(a)),
                        Obj::SetOperator(SetOperator::SetMinus(b)),
                    ) = (u.left.as_ref(), u.right.as_ref())
                    else {
                        continue;
                    };
                    if a.left.ir() != p.left.ir()
                        || a.right.ir() != p.right.ir()
                        || b.left.ir() != p.right.ir()
                        || b.right.ir() != p.left.ir()
                    {
                        continue;
                    }
                    "symmetricDifferenceDefinition _litex_set.val.left _litex_set.val.right"
                }
                Rule::SymDiffCommutative(_) => {
                    let Obj::SetOperator(SetOperator::SymmetricDifference(q)) = right else {
                        continue;
                    };
                    if q.left.ir() != p.right.ir() || q.right.ir() != p.left.ir() {
                        continue;
                    }
                    "symmetricDifferenceCommutative _litex_set.val.left _litex_set.val.right"
                }
                Rule::SymDiffEmpty(_) if empty_set(&p.right) && right.ir() == p.left.ir() => {
                    "symmetricDifferenceEmpty _litex_set.val.left"
                }
                Rule::SymDiffEmptyLeft(_) if empty_set(&p.left) && right.ir() == p.right.ir() => {
                    "symmetricDifferenceEmptyLeft _litex_set.val.right"
                }
                Rule::SymDiffCancel(_) => {
                    let Obj::SetOperator(SetOperator::SymmetricDifference(inner)) = p.left.as_ref()
                    else {
                        continue;
                    };
                    if inner.right.ir() != p.right.ir() || inner.left.ir() != right.ir() {
                        continue;
                    }
                    "symmetricDifferenceCancel _litex_set.val.left.val.left _litex_set.val.left.val.right"
                }
                Rule::SymDiffUnionMinusIntersection(_) => {
                    let Obj::SetOperator(SetOperator::SetMinus(q)) = right else {
                        continue;
                    };
                    let (
                        Obj::SetOperator(SetOperator::Union(a)),
                        Obj::SetOperator(SetOperator::Intersect(b)),
                    ) = (q.left.as_ref(), q.right.as_ref())
                    else {
                        continue;
                    };
                    if a.left.ir() != p.left.ir()
                        || a.right.ir() != p.right.ir()
                        || b.left.ir() != p.left.ir()
                        || b.right.ir() != p.right.ir()
                    {
                        continue;
                    }
                    "symmetricDifferenceUnionMinusIntersection _litex_set.val.left _litex_set.val.right"
                }
                Rule::SymDiffAssociative(_) => {
                    let Obj::SetOperator(SetOperator::SymmetricDifference(a)) = p.left.as_ref()
                    else {
                        continue;
                    };
                    let Obj::SetOperator(SetOperator::SymmetricDifference(q)) = right else {
                        continue;
                    };
                    let Obj::SetOperator(SetOperator::SymmetricDifference(b)) = q.right.as_ref()
                    else {
                        continue;
                    };
                    if q.left.ir() != a.left.ir()
                        || b.left.ir() != a.right.ir()
                        || b.right.ir() != p.right.ir()
                    {
                        continue;
                    }
                    "symmetricDifferenceAssociative _litex_set.val.left.val.left _litex_set.val.left.val.right _litex_set.val.right"
                }
                _ => continue,
            };
            let term = self.compile_object_reference(left, position)?;
            self.compile_object_reference(right, position)?;
            let orientation = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "(let _litex_set := {term}; (Litex.{law}){orientation})"
            ));
        }
        Err(LeanCompileError::unsupported("SymDiff/SelectedIdentity"))
    }

    fn compile_sym_diff_finite_rationals(
        &self,
        fact: &EqualFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_symmetric_difference::SymDiffFiniteRationalsProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        // Validate the retained finite certificate without selecting a new proof.
        if proof
            .left_values
            .iter()
            .chain(&proof.right_values)
            .any(|value| {
                (proof.left_values.contains(value) ^ proof.right_values.contains(value))
                    != proof.result_values.contains(value)
            })
            || proof.result_values.iter().any(|value| {
                !(proof.left_values.contains(value) ^ proof.right_values.contains(value))
            })
        {
            return Err(LeanCompileError::unsupported("SymDiff/FiniteCertificate"));
        }
        for (native, target, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::SetOperator(SetOperator::SymmetricDifference(pair)) = native else {
                continue;
            };
            let source = self.compile_object_reference(native, position)?;
            let result = self.compile_object_reference(target, position)?;
            let (left_value, left_equal) =
                self.compile_sym_diff_numeric_list(&pair.left, &proof.left_values, position)?;
            let (right_value, right_equal) =
                self.compile_sym_diff_numeric_list(&pair.right, &proof.right_values, position)?;
            let (result_value, result_equal) =
                self.compile_sym_diff_numeric_list(target, &proof.result_values, position)?;
            // This finite case split is determined only by the retained values.
            // The kernel checks membership equivalence; no replacement native search.
            let mut cases = Vec::new();
            for value in proof
                .left_values
                .iter()
                .chain(&proof.right_values)
                .chain(&proof.result_values)
            {
                if !cases.contains(value) {
                    cases.push(value.clone());
                }
            }
            let mut membership = String::from("classical\n");
            let mut excluded = Vec::new();
            for (index, value) in cases.iter().enumerate() {
                let literal = crate::compile_to_lean::helper::exact_rational_literal(value, "ℂ")?;
                let indent = "  ".repeat(index);
                membership.push_str(&format!("by_cases _symdiff_case_{index} : _symdiff_x = M.number {literal}\n{indent}· rw [_symdiff_case_{index}]\n{indent}  (norm_num only [Litex.symmetricDifference_members, Litex.SetSemantics.insert_members, Litex.SetSemantics.empty_members, M.number_injective.eq_iff]; decide)\n{indent}· "));
                excluded.push(format!("_symdiff_case_{index}"));
            }
            membership.push_str(&format!("(norm_num only [Litex.symmetricDifference_members, Litex.SetSemantics.insert_members, Litex.SetSemantics.empty_members{}]; decide)\n", if excluded.is_empty() { String::new() } else { format!(", {}", excluded.join(", ")) }));
            let term = format!("(by\n  let _symdiff_source := {source}\n  let _symdiff_result := {result}\n  have _symdiff_left : Litex.denote _symdiff_source.val.left = {left_value} := {left_equal}\n  have _symdiff_right : Litex.denote _symdiff_source.val.right = {right_value} := {right_equal}\n  have _symdiff_target : Litex.denote _symdiff_result = {result_value} := {result_equal}\n  apply Litex.SetSemantics.ext _ _ (Litex.isSet _symdiff_source) (Litex.isSet _symdiff_result)\n  intro _symdiff_x\n  have _symdiff_members : M.mem _symdiff_x (Litex.symmetricDifferenceValue {left_value} {right_value}) ↔ M.mem _symdiff_x {result_value} := by\n    {}\n  exact (iff_of_eq (congrArg (fun value => M.mem _symdiff_x value) (congrArg₂ (Litex.symmetricDifferenceValue (M := M)) _symdiff_left _symdiff_right))).trans (_symdiff_members.trans (iff_of_eq (congrArg (fun value => M.mem _symdiff_x value) _symdiff_target)).symm)\n)", membership.trim_end().replace('\n', "\n    "));
            return Ok(if reversed {
                format!("(Eq.symm (show Litex.Same {source} {result} from {term}))")
            } else {
                term
            });
        }
        Err(LeanCompileError::unsupported("SymDiff/FiniteSubject"))
    }

    fn compile_sym_diff_numeric_list(
        &self,
        object: &Obj,
        values: &[EvalRational],
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let Obj::SetFormer(SetFormer::ListSet(list)) = object else {
            return Err(LeanCompileError::unsupported("SymDiff/FiniteList"));
        };
        if list.list.len() != values.len() {
            return Err(LeanCompileError::unsupported("SymDiff/ValueArity"));
        }
        let original = self.compile_object_reference(object, position)?;
        let mut elements = Vec::new();
        for (element, value) in list.list.iter().zip(values) {
            let observation = self.compile_numeric_observation(element, position)?;
            if observation.3.as_ref() != Some(value) {
                return Err(LeanCompileError::unsupported("SymDiff/RetainedValue"));
            }
            let literal = crate::compile_to_lean::helper::exact_rational_literal(value, "ℂ")?;
            let equal = format!(
                "(({}).trans (congrArg M.number (by norm_num : {} = {literal})))",
                observation.1, observation.0
            );
            elements.push((literal, equal));
        }
        let mut value = "(Litex.SetSemantics.emptyValue (M := M))".to_string();
        let mut equal = format!("(Eq.refl {value})");
        for (literal, element_equal) in elements.into_iter().rev() {
            value =
                format!("(Litex.SetSemantics.insertValue (M := M) (M.number {literal}) {value})");
            equal = format!(
                "(congrArg₂ (Litex.SetSemantics.insertValue (M := M)) {element_equal} {equal})"
            );
        }
        Ok((
            value.clone(),
            format!("(show Litex.denote {original} = {value} from {equal})"),
        ))
    }

    pub(super) fn compile_set_identity(
        &self,
        fact: &EqualFact,
        rule: &EqualitySearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if let Some((law, arguments)) = set_identity_shape(left, right, rule) {
                let object = self.compile_object_reference(left, position)?;
                let symm = if reversed { ".symm" } else { "" };
                // Project children from the original formed object. Their WD is
                // already carried by this producer; do not rebuild each child.
                return Ok(format!(
                    "(let _litex_set := {object}; (Litex.{law} {arguments}){symm})"
                ));
            }
        }
        Err(LeanCompileError::unsupported("SetIdentity/Endpoints"))
    }

    pub(super) fn compile_intersect_from_subset(
        &self,
        fact: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "IntersectFromSubset/Requirements",
            ));
        }
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = source_subject(&requirements[0])?
        else {
            return Err(LeanCompileError::unsupported("IntersectFromSubset/Premise"));
        };
        for (intersection, retained, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((a, b)) = set_operands(intersection, true) else {
                continue;
            };
            let side = if retained.ir() == a.ir()
                && subset.left.ir() == a.ir()
                && subset.right.ir() == b.ir()
            {
                "Left"
            } else if retained.ir() == b.ir()
                && subset.left.ir() == b.ir()
                && subset.right.ir() == a.ir()
            {
                "Right"
            } else {
                continue;
            };
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            let proof = self.compile_verify(&requirements[0], &prior)?.1;
            let object = self.compile_object_reference(intersection, position)?;
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!("(let _litex_set := {object}; (Litex.intersectOfSubset{side} _litex_set.val.left _litex_set.val.right {proof}){symm})"));
        }
        Err(LeanCompileError::unsupported(
            "IntersectFromSubset/Endpoints",
        ))
    }
}

fn set_operands(object: &Obj, intersection: bool) -> Option<(&Obj, &Obj)> {
    match object {
        Obj::SetOperator(SetOperator::Intersect(p)) if intersection => Some((&p.left, &p.right)),
        Obj::SetOperator(SetOperator::Union(p)) if !intersection => Some((&p.left, &p.right)),
        _ => None,
    }
}

fn empty_set(object: &Obj) -> bool {
    matches!(object, Obj::SetFormer(SetFormer::ListSet(p)) if p.list.is_empty())
}

/// Validate only the selected builtin. This is not a search over set identities.
fn set_identity_shape(
    left: &Obj,
    right: &Obj,
    rule: &EqualitySearchProofByBuiltinRule,
) -> Option<(&'static str, &'static str)> {
    use EqualitySearchProofByBuiltinRule as Rule;
    let intersection = matches!(
        rule,
        Rule::IntersectCommutative(_)
            | Rule::IntersectIdempotent(_)
            | Rule::IntersectEmptyLeft(_)
            | Rule::IntersectEmptyRight(_)
            | Rule::IntersectAssociative(_)
            | Rule::IntersectUnionDistributive(_)
    );
    let (a, b) = set_operands(left, intersection)?;
    match rule {
        Rule::IntersectCommutative(_) | Rule::UnionCommutative(_) => {
            let (c, d) = set_operands(right, intersection)?;
            (a.ir() == d.ir() && b.ir() == c.ir()).then_some((
                if intersection {
                    "intersectComm"
                } else {
                    "unionComm"
                },
                "_litex_set.val.left _litex_set.val.right",
            ))
        }
        Rule::IntersectIdempotent(_) | Rule::UnionIdempotent(_) => {
            (a.ir() == b.ir() && a.ir() == right.ir()).then_some((
                if intersection {
                    "intersectIdem"
                } else {
                    "unionIdem"
                },
                "_litex_set.val.left",
            ))
        }
        Rule::IntersectEmptyLeft(_) | Rule::UnionEmptyLeft(_) => (empty_set(a)
            && if intersection {
                empty_set(right)
            } else {
                b.ir() == right.ir()
            })
        .then_some((
            if intersection {
                "intersectEmptyLeft"
            } else {
                "unionEmptyLeft"
            },
            "_litex_set.val.right",
        )),
        Rule::IntersectEmptyRight(_) | Rule::UnionEmptyRight(_) => (empty_set(b)
            && if intersection {
                empty_set(right)
            } else {
                a.ir() == right.ir()
            })
        .then_some((
            if intersection {
                "intersectEmptyRight"
            } else {
                "unionEmptyRight"
            },
            "_litex_set.val.left",
        )),
        Rule::IntersectAssociative(_) | Rule::UnionAssociative(_) => {
            let (aa, ab) = set_operands(a, intersection)?;
            let (c, d) = set_operands(right, intersection)?;
            let (da, db) = set_operands(d, intersection)?;
            (aa.ir() == c.ir() && ab.ir() == da.ir() && b.ir() == db.ir()).then_some((
                if intersection {
                    "intersectAssoc"
                } else {
                    "unionAssoc"
                },
                "_litex_set.val.left.val.left _litex_set.val.left.val.right _litex_set.val.right",
            ))
        }
        Rule::IntersectUnionDistributive(_) => {
            let (ba, bb) = set_operands(b, false)?;
            let (c, d) = set_operands(right, false)?;
            let (ca, cb) = set_operands(c, true)?;
            let (da, db) = set_operands(d, true)?;
            (a.ir() == ca.ir() && a.ir() == da.ir() && ba.ir() == cb.ir() && bb.ir() == db.ir())
                .then_some((
                "intersectUnionDistrib",
                "_litex_set.val.left _litex_set.val.right.val.left _litex_set.val.right.val.right",
            ))
        }
        _ => None,
    }
}
