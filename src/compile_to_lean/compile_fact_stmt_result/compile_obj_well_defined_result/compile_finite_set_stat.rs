use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FiniteSetStatObjWellDefinedProofByDef;
use crate::prelude::*;
use crate::rational_expression::NumberCompareResult;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_stat_wd(
        &self,
        object: &FiniteSetStat,
        proof: &FiniteSetStatObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (set, children, requirements, name) = match (object, proof) {
            (
                FiniteSetStat::FiniteSetSize(s),
                FiniteSetStatObjWellDefinedProofByDef::FiniteSetSize(p),
            ) => (
                &s.set,
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                "finiteSetSize",
            ),
            (
                FiniteSetStat::FiniteSetMax(s),
                FiniteSetStatObjWellDefinedProofByDef::FiniteSetMax(p),
            ) => (
                &s.set,
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                "finiteExtremum true",
            ),
            (
                FiniteSetStat::FiniteSetMin(s),
                FiniteSetStatObjWellDefinedProofByDef::FiniteSetMin(p),
            ) => (
                &s.set,
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                "finiteExtremum false",
            ),
            _ => return Err(LeanCompileError::unsupported("FiniteSetStat/Constructor")),
        };
        let [child] = children.as_slice() else {
            return Err(LeanCompileError::unsupported("FiniteSetStat/Stages"));
        };
        let expected = if name == "finiteSetSize" { 1 } else { 3 };
        if requirements.len() != expected {
            return Err(LeanCompileError::unsupported("FiniteSetStat/Stages"));
        }
        let requirement = &requirements[0];
        ensure_object(set, child)?;
        if !matches!(source_subject(requirement)?, Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir() == set.ir())
        {
            return Err(LeanCompileError::unsupported("FiniteSetStat/FiniteSubject"));
        }
        let term = self.compile_wd(
            child,
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let finite = self.compile_wd_requirement(
            requirement,
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        let mut args = vec![term, finite];
        if expected == 3 {
            if !matches!(source_subject(&requirements[1])?, Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir() == set.ir())
                || !matches!(source_subject(&requirements[2])?, Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir() == set.ir() && f.right == Obj::StandardSet(StandardSet::R))
            {
                return Err(LeanCompileError::unsupported(
                    "FiniteSetStat/ExtremumDomain",
                ));
            }
            for (i, p) in requirements.iter().enumerate().skip(1) {
                args.push(self.compile_wd_requirement(
                    p,
                    &SourcePosition {
                        before: i + 1,
                        ..*position
                    },
                )?);
            }
        }
        Ok(format!("(Litex.{name} {})", args.join(" ")))
    }

    // The original enumeration constructor already contains each freshness proof.
    // Traverse its certified tails, without recovering inequalities by search.
    pub(in crate::compile_to_lean) fn compile_list_finite(
        &self,
        set: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetFormer(SetFormer::ListSet(list)) = set else {
            return Err(LeanCompileError::unsupported("FiniteSet/ListSubject"));
        };
        let term = self.compile_object_reference(set, position)?;
        let (setup, finite, _) = finite_list_certificate(&term, list.list.len(), false);
        Ok(format!("({setup}\n{finite})"))
    }

    pub(in crate::compile_to_lean) fn numeric_finite_stat_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        match wd.obj() {
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(p)) => {
                return self.numeric_finite_extremum(wd, &p.set, true, position)
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(p)) => {
                return self.numeric_finite_extremum(wd, &p.set, false, position)
            }
            _ => {}
        }
        let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(size)) = wd.obj() else {
            return Err(LeanCompileError::unsupported("FiniteSetStat/Numeric"));
        };
        let term = self.compile_wd(wd, position)?;
        let setup = format!("let _stat := {term};\n");
        let member = format!("(Litex.naturalToComplex _stat (Litex.finiteSetSizeInN _stat))");
        if let Obj::SetFormer(SetFormer::ListSet(list)) = size.set.as_ref() {
            let n = list.list.len();
            let (certificate, _, card) = finite_list_certificate("_stat.val.set", n, true);
            return Ok((
                format!("({n} : ℂ)"),
                format!("({setup}{certificate}\n(Litex.finiteSetSizeDenote _stat {n} {card}).trans (congrArg M.number (by norm_num : (({n} : ℕ) : ℂ) = ({n} : ℂ))))"),
                format!("({setup}{member})"),
                EvalRational::new(n as i128, 1),
            ));
        }
        Ok((
            format!("({setup}Litex.NativeBridge.asComplex _stat {member})"),
            format!("({setup}Litex.NativeBridge.asComplex_spec _stat {member})"),
            format!("({setup}{member})"),
            None,
        ))
    }
    fn numeric_finite_extremum(
        &self,
        wd: &ObjWellDefinedProof,
        set: &Obj,
        maximum: bool,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let term = self.compile_wd(wd, position)?;
        let prefix = format!("let _stat := {term};\n");
        let member = "(Litex.realToComplex _stat (Litex.finiteExtremumInR _stat))";
        let fallback = || {
            Ok((
                format!("({prefix}Litex.NativeBridge.asComplex _stat {member})"),
                format!("({prefix}Litex.NativeBridge.asComplex_spec _stat {member})"),
                format!("({prefix}{member})"),
                None,
            ))
        };
        let Obj::SetFormer(SetFormer::ListSet(list)) = set else {
            return fallback();
        };
        if list.list.is_empty() {
            return Err(LeanCompileError::unsupported("FiniteSetStat/EmptyExtremum"));
        }
        let observations = list
            .list
            .iter()
            .map(|x| self.compile_numeric_observation(x, position))
            .collect::<Result<Vec<_>, _>>()?;
        let Some(values) = observations
            .iter()
            .map(|o| o.3.clone())
            .collect::<Option<Vec<_>>>()
        else {
            return fallback();
        };
        let preferred = if maximum {
            NumberCompareResult::Greater
        } else {
            NumberCompareResult::Less
        };
        let mut selected = 0;
        for i in 1..values.len() {
            if values[i]
                .compare(&values[selected])
                .ok_or_else(|| LeanCompileError::unsupported("FiniteExtremum/ExactComparison"))?
                == preferred
            {
                selected = i;
            }
        }
        let real_values = values
            .iter()
            .map(|v| exact_rational_literal(v, "ℝ"))
            .collect::<Result<Vec<_>, _>>()?;
        let n = values.len();
        let mut lines = vec![prefix.clone(), "let _stat_tail_0 := _stat.val.set;".into()];
        for i in 0..n {
            lines.push(format!(
                "let _stat_tail_{} := _stat_tail_{i}.val.tail;",
                i + 1
            ));
        }
        lines.push(format!("have _members_{n} : ∀ x, M.mem x (Litex.denote _stat_tail_{n}) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty;"));
        for i in (0..n).rev() {
            let obs = &observations[i];
            let r = &real_values[i];
            lines.push(format!("have _number_{i} : Litex.denote _stat_tail_{i}.val.element = M.number (({r} : ℝ) : ℂ) := ({}).trans (congrArg M.number (by norm_num : {} = (({r} : ℝ) : ℂ)));", obs.1, obs.0));
            let tail = real_values[i + 1..]
                .iter()
                .map(|r| format!("M.number (({r} : ℝ) : ℂ)"))
                .collect::<Vec<_>>()
                .join(", ");
            lines.push(format!("have _members_{i} := Litex.finiteMembersInsert _stat_tail_{i} (M.number (({r} : ℝ) : ℂ)) [{tail}] _number_{i} _members_{};", i+1));
        }
        lines.push(format!(
            "Litex.finiteExtremumListDenote _stat [{}] {} _members_0 (by norm_num) (by norm_num)",
            real_values.join(", "),
            real_values[selected]
        ));
        Ok((
            exact_rational_literal(&values[selected], "ℂ")?,
            format!(
                "(({}).trans (congrArg M.number (by norm_num : (({} : ℝ) : ℂ) = {})))",
                lines.join("\n"),
                real_values[selected],
                exact_rational_literal(&values[selected], "ℂ")?
            ),
            format!("({prefix}{member})"),
            Some(values[selected].clone()),
        ))
    }

    pub(in crate::compile_to_lean) fn compile_finite_extremum_selection(
        &self,
        goal: &EqualFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::ScalarIdentityBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::ScalarIdentityBuiltinRuleProof as P;
        let (maximum, index, selected, comparisons) = match proof {
            P::FiniteSetMaxSelection(p) => {
                (true, p.selected_index, &p.selected_member, &p.comparisons)
            }
            P::FiniteSetMinSelection(p) => {
                (false, p.selected_index, &p.selected_member, &p.comparisons)
            }
            _ => return Err(LeanCompileError::unsupported("FiniteExtremum/SelectedRule")),
        };
        let parts = |obj: &Obj| match obj {
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(p)) if maximum => {
                Some(p.set.as_ref().clone())
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(p)) if !maximum => {
                Some(p.set.as_ref().clone())
            }
            _ => None,
        };
        let (set, extremum, other, reversed) = if let Some(set) = parts(&goal.left) {
            (set, &goal.left, &goal.right, false)
        } else if let Some(set) = parts(&goal.right) {
            (set, &goal.right, &goal.left, true)
        } else {
            return Err(LeanCompileError::unsupported(
                "FiniteExtremum/SelectedSubject",
            ));
        };
        let Obj::SetFormer(SetFormer::ListSet(list)) = set else {
            return Err(LeanCompileError::unsupported("FiniteExtremum/SelectedList"));
        };
        if list.list.get(index).is_none_or(|x| x.ir() != selected.ir())
            || comparisons.len() != list.list.len()
        {
            return Err(LeanCompileError::unsupported(
                "FiniteExtremum/SelectionCapture",
            ));
        }
        let selected_value = EvalRational::from_obj(selected)
            .ok_or_else(|| LeanCompileError::unsupported("FiniteExtremum/SelectedValue"))?;
        let forbidden = if maximum {
            NumberCompareResult::Greater
        } else {
            NumberCompareResult::Less
        };
        for (item, comparison) in list.list.iter().zip(comparisons) {
            let value = EvalRational::from_obj(item)
                .ok_or_else(|| LeanCompileError::unsupported("FiniteExtremum/MemberValue"))?;
            if comparison.member.ir() != item.ir()
                || comparison.member_normal != value.to_obj()
                || comparison.selected_normal != selected_value.to_obj()
                || value.compare(&selected_value) != Some(comparison.ordering)
                || comparison.ordering == forbidden
            {
                return Err(LeanCompileError::unsupported(
                    "FiniteExtremum/ComparisonCapture",
                ));
            }
        }
        let x = self.compile_numeric_observation(extremum, position)?;
        let y = self.compile_numeric_observation(other, position)?;
        if x.3.as_ref() != Some(&selected_value) || y.3.as_ref() != Some(&selected_value) {
            return Err(LeanCompileError::unsupported(
                "FiniteExtremum/SelectedEndpoint",
            ));
        }
        let result = format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {} {} {} {} {} {} (by norm_num))",
            self.compile_object_reference(extremum, position)?,
            self.compile_object_reference(other, position)?,
            x.0,
            y.0,
            x.1,
            y.1
        );
        Ok(if reversed {
            format!("Litex.sameSymm {result}")
        } else {
            result
        })
    }

    pub(in crate::compile_to_lean) fn compile_finite_extremum_bound(
        &self,
        goal: &AtomicFact,
        maximum: bool,
        member: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (extremum, value) = if maximum { (high, low) } else { (low, high) };
        let set = match extremum {
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(p)) if maximum => &p.set,
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(p)) if !maximum => &p.set,
            _ => return Err(LeanCompileError::unsupported("FiniteExtremum/BoundSubject")),
        };
        if strict
            || !matches!(source_subject(member)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == value.ir() && f.set.ir() == set.ir())
        {
            return Err(LeanCompileError::unsupported("FiniteExtremum/BoundPremise"));
        }
        let (_, proof) = self.compile_verify(member, position)?;
        Ok(format!(
            "(Litex.finiteExtremumBound {} {} {proof})",
            self.compile_object_reference(extremum, position)?,
            self.compile_object_reference(value, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_finite_extremum_member(
        &self,
        goal: &InFact,
        maximum: bool,
        equality: &EqualFactSearchedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let set = match &goal.element {
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(p)) if maximum => &p.set,
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(p)) if !maximum => &p.set,
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FiniteExtremum/MemberSubject",
                ))
            }
        };
        // Endpoint view of the producer's retained set-equality proof; no new fact is stored.
        let endpoints = EqualFact {
            fact_id: goal.fact_id,
            left: *set.clone(),
            right: goal.set.clone(),
            line_file: goal.line_file.clone(),
        };
        let equality = self.compile_equality_search(&endpoints, equality, position)?;
        let term = self.compile_object_reference(&goal.element, position)?;
        Ok(format!("(Eq.mp (congrArg (M.mem (Litex.denote {term})) {equality}) (Litex.finiteExtremumInSet {term}))"))
    }

    pub(in crate::compile_to_lean) fn compile_finite_size_nonnegative(
        &self,
        goal: &AtomicFact,
        finite: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(p)) = high else {
            return Err(LeanCompileError::unsupported("FiniteSetSize/BoundSubject"));
        };
        if strict
            || !matches!(low, Obj::Literal(Literal::Number(n)) if n.normalized_value == "0")
            || !matches!(source_subject(finite)?, Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir() == p.set.ir())
        {
            return Err(LeanCompileError::unsupported("FiniteSetSize/BoundSubject"));
        }
        let (_, proof) = self.compile_verify(finite, position)?;
        Ok(format!(
            "(by have _finite := {proof}; exact Litex.finiteSetSizeNonnegative {})",
            self.compile_object_reference(high, position)?
        ))
    }
}

fn finite_list_certificate(term: &str, len: usize, cardinality: bool) -> (String, String, String) {
    let mut lines = vec![format!("let _finite_tail_0 := {term};")];
    for i in 0..len {
        lines.push(format!(
            "let _finite_tail_{} := _finite_tail_{i}.val.tail;",
            i + 1
        ));
    }
    lines.push(format!(
        "have _finite_{len} : Litex.IsFiniteSet _finite_tail_{len} := Litex.finiteSetEmpty;"
    ));
    if cardinality {
        lines.push(format!("have _card_{len} : Litex.finiteCard (Litex.denote _finite_tail_{len}) = 0 := Litex.finiteCardEmpty;"));
    }
    for i in (0..len).rev() {
        lines.push(format!(
            "have _finite_{i} := Litex.finiteSetInsert _finite_tail_{i} _finite_{};",
            i + 1
        ));
        if cardinality {
            lines.push(format!("have _card_{i} : Litex.finiteCard (Litex.denote _finite_tail_{i}) = {} := (Litex.finiteCardInsert _finite_tail_{i} _finite_{}).trans (congrArg (fun n : ℕ => n + 1) _card_{});", len - i, i + 1, i + 1));
        }
    }
    (lines.join("\n"), "_finite_0".into(), "_card_0".into())
}
