use super::compile_by_stmt_result::compile_classified_negation::quantifier_free_terms;
use super::compile_general_recursive_result::{and_intro, general_error, lean_by};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::{HaveFnByInducCase, HaveFnByInducCaseBody};
use crate::execute::{
    ExecHaveFnByInducStmtSuccessResult, InducCaseBodySuccess, InducCaseListSuccess,
    InducCaseSuccess,
};
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

impl LitexToLeanCompiler {
    pub(super) fn compile_general_recursive_body(
        &self,
        cases: &[HaveFnByInducCase],
        checks: &InducCaseListSuccess,
        site: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let mut result = "M.number 0".to_string();
        if cases.len() != checks.cases.len() {
            return Err(general_error("CaseCapture"));
        }
        for (case, evidence) in cases.iter().zip(&checks.cases).rev() {
            let branch = SourcePosition::new(Some(site), SourceOwner::RecursiveCase(evidence), 2);
            let guard = self.compile_function_raw_predicate(
                &and_chain_as_fact(&case.case_fact),
                site,
                bindings,
            )?;
            let value = match (&case.body, &evidence.body) {
                (
                    HaveFnByInducCaseBody::EqualTo(body),
                    InducCaseBodySuccess::EqualTo { well_defined, .. },
                ) => {
                    success_object_wd(well_defined, body)?;
                    self.compile_function_raw_expression_bound(body, &branch, bindings)?
                }
                (
                    HaveFnByInducCaseBody::NestedCases(children),
                    InducCaseBodySuccess::NestedCases(child_checks),
                ) => {
                    self.compile_general_recursive_body(children, child_checks, &branch, bindings)?
                }
                _ => return Err(general_error("CaseCapture")),
            };
            result = format!("(if {guard} then {value} else {result})");
        }
        Ok(result)
    }

    pub(super) fn compile_recursive_leaf_value(
        &self,
        cases: &[HaveFnByInducCase],
        checks: &InducCaseListSuccess,
        path: &[usize],
        site: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let (index, tail) = path
            .split_first()
            .ok_or_else(|| general_error("EquationPath"))?;
        let case = cases
            .get(*index)
            .ok_or_else(|| general_error("EquationPath"))?;
        let evidence = checks
            .cases
            .get(*index)
            .ok_or_else(|| general_error("CaseCapture"))?;
        let branch = SourcePosition::new(Some(site), SourceOwner::RecursiveCase(evidence), 2);
        match (&case.body, &evidence.body) {
            (
                HaveFnByInducCaseBody::EqualTo(body),
                InducCaseBodySuccess::EqualTo { well_defined, .. },
            ) if tail.is_empty() => {
                success_object_wd(well_defined, body)?;
                self.compile_function_raw_expression_bound(body, &branch, bindings)
            }
            (
                HaveFnByInducCaseBody::NestedCases(children),
                InducCaseBodySuccess::NestedCases(child_checks),
            ) if !tail.is_empty() => {
                self.compile_recursive_leaf_value(children, child_checks, tail, &branch, bindings)
            }
            _ => Err(general_error("CaseCapture")),
        }
    }

    pub(super) fn compile_recursive_case_tree(
        &self,
        p: &ExecHaveFnByInducStmtSuccessResult,
        cases: &[HaveFnByInducCase],
        checks: &InducCaseListSuccess,
        site: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        let mut returned = Vec::new();
        let mut congruent = Vec::new();
        let mut indent = String::new();
        for (case, evidence) in cases.iter().zip(&checks.cases) {
            let guard = self.compile_function_raw_predicate(
                &and_chain_as_fact(&case.case_fact),
                site,
                bindings,
            )?;
            // Source IDs distinguish hypotheses at different depths.
            let guard_name = format!(
                "_case_h{}",
                evidence.assumption_stored.primary_fact_id().value()
            );
            for lines in [&mut returned, &mut congruent] {
                lines.push(format!("{indent}by_cases {guard_name} : {guard}"));
            }
            let branch_scope =
                SourcePosition::new(Some(site), SourceOwner::RecursiveCase(evidence), 1);
            let mut common =
                self.compile_recursive_tree_assumption(case, evidence, &guard_name, &branch_scope)?;
            let (return_lines, congruence_lines) = match (&case.body, &evidence.body) {
                (
                    HaveFnByInducCaseBody::EqualTo(value),
                    InducCaseBodySuccess::EqualTo {
                        well_defined,
                        in_ret_set,
                    },
                ) => {
                    let checked =
                        self.compile_wd(success_object_wd(well_defined, value)?, &branch_scope)?;
                    common.push(format!("have _checked_body := {checked}"));
                    let body_site = SourcePosition {
                        before: 2,
                        ..branch_scope
                    };
                    if !matches!(source_subject(in_ret_set)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==value.ir() && f.set==p.statement.fn_set_clause.ret_set)
                    {
                        return Err(general_error("ReturnSubject"));
                    }
                    let member = self.compile_verify(in_ret_set, &body_site)?;
                    let equality =
                        self.compile_general_recursive_congruence(value, p, &body_site, bindings)?;
                    (
                        vec![format!("exact {}", member.1)],
                        vec![format!("exact {equality}")],
                    )
                }
                (
                    HaveFnByInducCaseBody::NestedCases(children),
                    InducCaseBodySuccess::NestedCases(child_checks),
                ) => {
                    common.extend(self.compile_recursive_nested_checks(
                        children,
                        child_checks,
                        &branch_scope,
                    )?);
                    let completed = SourcePosition {
                        before: 2,
                        ..branch_scope
                    };
                    self.compile_recursive_case_tree(
                        p,
                        children,
                        child_checks,
                        &completed,
                        bindings,
                    )?
                }
                _ => return Err(general_error("CaseCapture")),
            };
            for (congr, lines, suffix) in [
                (false, &mut returned, return_lines),
                (true, &mut congruent, congruence_lines),
            ] {
                lines.push(if congr {
                    format!("{indent}· refine (if_pos {guard_name}).trans (Eq.trans ?_ (if_pos {guard_name}).symm)")
                } else { format!("{indent}· rw [if_pos {guard_name}]") });
                for line in common.iter().chain(&suffix) {
                    lines.push(format!(
                        "{indent}  {}",
                        line.replace('\n', &format!("\n{indent}  "))
                    ));
                }
                lines.push(if congr {
                    format!("{indent}· refine (if_neg {guard_name}).trans (Eq.trans ?_ (if_neg {guard_name}).symm)")
                } else { format!("{indent}· rw [if_neg {guard_name}]") });
            }
            indent.push_str("  ");
        }
        let coverage = format!("h_{}", source_subject(&checks.coverage)?.fact_id().value());
        let refutations = checks
            .cases
            .iter()
            .map(|c| {
                format!(
                    "(fun h => False.elim (_case_h{} h))",
                    c.assumption_stored.primary_fact_id().value()
                )
            })
            .collect::<Vec<_>>();
        let mut eliminate = refutations
            .last()
            .ok_or_else(|| general_error("EmptyCases"))?
            .clone();
        for prior in refutations[..refutations.len() - 1].iter().rev() {
            eliminate = format!("(fun h => Or.elim h {prior} {eliminate})");
        }
        for lines in [&mut returned, &mut congruent] {
            lines.push(format!("{indent}exact {eliminate} {coverage}"));
        }
        Ok((returned, congruent))
    }

    fn compile_recursive_tree_assumption(
        &self,
        case: &HaveFnByInducCase,
        evidence: &InducCaseSuccess,
        hypothesis: &str,
        site: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let store = &evidence.assumption_stored;
        let fact = self.resolve_fact(store.primary_fact_id(), site)?;
        if fact != and_chain_as_fact(&case.case_fact) {
            return Err(general_error("CaseAssumption"));
        }
        self.validate_store(&store.store, &fact)?;
        let proposition = self.fact_proposition(&fact, site)?;
        let name = format!("h_{}", store.primary_fact_id().value());
        let mut lines = vec![format!("have {name} : {proposition} := {hypothesis}")];
        lines.extend(self.compile_stored_inferences(store, &fact, &(proposition, name), site)?);
        Ok(lines)
    }

    fn compile_recursive_nested_checks(
        &self,
        cases: &[HaveFnByInducCase],
        checks: &InducCaseListSuccess,
        site: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let coverage = self.compile_verify(&checks.coverage, site)?;
        let mut lines =
            vec![self.emit_internal_fact(&source_subject(&checks.coverage)?, &coverage, site)?];
        let completed = SourcePosition { before: 2, ..*site };
        for checked in &checks.disjoint {
            let branch =
                SourcePosition::new(Some(&completed), SourceOwner::RecursiveDisjoint(checked), 1);
            let assumption =
                self.resolve_fact(checked.assumption_stored.primary_fact_id(), &branch)?;
            let assumed_left = assumption == and_chain_as_fact(&cases[checked.i].case_fact);
            if !assumed_left && assumption != and_chain_as_fact(&cases[checked.j].case_fact) {
                return Err(general_error("DisjointSubject"));
            }
            self.validate_store(&checked.assumption_stored.store, &assumption)?;
            let prop = self.fact_proposition(&assumption, &branch)?;
            let name = format!("h_{}", assumption.fact_id().value());
            let mut proof = vec![format!("intro {name}")];
            proof.extend(self.compile_stored_inferences(
                &checked.assumption_stored,
                &assumption,
                &(prop.clone(), name),
                &branch,
            )?);
            let negated = self.compile_verify(&checked.negated_component, &branch)?;
            proof.push(format!("exact {}", negated.1));
            lines.push(format!(
                "have _disjoint_{}_{} : {prop} → {} := {}",
                checked.i,
                checked.j,
                self.scope_proposition(negated.0, &proof[1..proof.len() - 1]),
                lean_by(proof)
            ));
        }
        Ok(lines)
    }

    /// Keep each original ancestor scope alive while visiting one published leaf's WD.
    pub(super) fn visit_recursive_case_wd<T>(
        &self,
        cases: &[HaveFnByInducCase],
        checks: &InducCaseListSuccess,
        path: &[usize],
        guards: &[String],
        site: &SourcePosition<'_>,
        mut definitions: Vec<String>,
        visitor: &mut impl FnMut(
            &ObjWellDefinedProof,
            &VerifyFactResult,
            &SourcePosition<'_>,
            Vec<String>,
        ) -> Result<Option<T>, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let (index, tail) = path
            .split_first()
            .ok_or_else(|| general_error("EquationPath"))?;
        let (guard, remaining_guards) = guards
            .split_first()
            .ok_or_else(|| general_error("EquationPathGuard"))?;
        let case = cases
            .get(*index)
            .ok_or_else(|| general_error("EquationPath"))?;
        let evidence = checks
            .cases
            .get(*index)
            .ok_or_else(|| general_error("CaseCapture"))?;
        let scope = SourcePosition::new(Some(site), SourceOwner::RecursiveCase(evidence), 1);
        definitions.extend(self.compile_recursive_tree_assumption(case, evidence, guard, &scope)?);
        match (&case.body, &evidence.body) {
            (
                HaveFnByInducCaseBody::EqualTo(value),
                InducCaseBodySuccess::EqualTo {
                    well_defined,
                    in_ret_set,
                },
            ) if tail.is_empty() && remaining_guards.is_empty() => visitor(
                success_object_wd(well_defined, value)?,
                in_ret_set,
                &scope,
                definitions,
            ),
            (
                HaveFnByInducCaseBody::NestedCases(children),
                InducCaseBodySuccess::NestedCases(child_checks),
            ) if !tail.is_empty() => {
                definitions.extend(self.compile_recursive_nested_checks(
                    children,
                    child_checks,
                    &scope,
                )?);
                let completed = SourcePosition { before: 2, ..scope };
                self.visit_recursive_case_wd(
                    children,
                    child_checks,
                    tail,
                    remaining_guards,
                    &completed,
                    definitions,
                    visitor,
                )
            }
            _ => Err(general_error("CaseCapture")),
        }
    }

    pub(super) fn compile_recursive_equation_path(
        &self,
        cases: &[HaveFnByInducCase],
        checks: &InducCaseListSuccess,
        path: &[usize],
        merged_guard: &str,
        total_atoms: usize,
        offset: usize,
        bindings: &HashMap<IdentifierId, String>,
        site: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (&index, tail) = path
            .split_first()
            .ok_or_else(|| general_error("EquationPath"))?;
        let case = cases
            .get(index)
            .ok_or_else(|| general_error("EquationPath"))?;
        let evidence = &checks.cases[index];
        let atoms = recursive_guard_atoms(&and_chain_as_fact(&case.case_fact))?;
        let selected = if offset == 0 && tail.is_empty() {
            merged_guard.to_string()
        } else {
            and_intro(
                (offset..offset + atoms.len())
                    .map(|i| conjunction_projection(merged_guard, i, total_atoms))
                    .collect(),
            )
        };
        let guard_name = format!("h_{}", evidence.assumption_stored.primary_fact_id().value());
        let branch_site = SourcePosition::new(Some(site), SourceOwner::RecursiveCase(evidence), 1);
        let mut lines =
            self.compile_recursive_tree_assumption(case, evidence, &selected, &branch_site)?;
        for checked in checks.disjoint.iter().filter(|p| p.j == index) {
            let i = checked.i;
            let branch =
                SourcePosition::new(Some(site), SourceOwner::RecursiveDisjoint(checked), 1);
            let assumption =
                self.resolve_fact(checked.assumption_stored.primary_fact_id(), &branch)?;
            let earlier = and_chain_as_fact(&cases[i].case_fact);
            let selected_fact = and_chain_as_fact(&case.case_fact);
            let assumed_left = assumption == earlier;
            if !assumed_left && assumption != selected_fact {
                return Err(general_error("DisjointSubject"));
            }
            self.validate_store(&checked.assumption_stored.store, &assumption)?;
            let prop = self.fact_proposition(&assumption, &branch)?;
            let h = format!("h_{}", assumption.fact_id().value());
            let mut exclude = vec![
                "intro _earlier_guard".into(),
                format!(
                    "have {h} : {prop} := {}",
                    if assumed_left {
                        "_earlier_guard"
                    } else {
                        &guard_name
                    }
                ),
            ];
            exclude.extend(self.compile_stored_inferences(
                &checked.assumption_stored,
                &assumption,
                &(prop, h),
                &branch,
            )?);
            let negated = self.compile_verify(&checked.negated_component, &branch)?;
            exclude.push(format!("have _excluded := {}", negated.1));
            exclude.push(format!(
                "have _other := {}",
                if assumed_left {
                    &guard_name
                } else {
                    "_earlier_guard"
                }
            ));
            exclude.push(format!(
                "exact {}",
                self.compile_piecewise_disjoint_component(
                    if assumed_left {
                        &selected_fact
                    } else {
                        &earlier
                    },
                    &source_subject(&checked.negated_component)?,
                    &branch
                )?
            ));
            let raw = self.compile_function_raw_predicate(&earlier, site, bindings)?;
            lines.push(format!(
                "have _not_case_{i} : ¬ {raw} := {}",
                lean_by(exclude)
            ));
            lines.push(format!("rw [if_neg _not_case_{i}]"));
        }
        match (&case.body, &evidence.body) {
            (HaveFnByInducCaseBody::EqualTo(_), InducCaseBodySuccess::EqualTo { .. })
                if tail.is_empty() =>
            {
                lines.push(format!("exact if_pos {guard_name}"));
            }
            (
                HaveFnByInducCaseBody::NestedCases(children),
                InducCaseBodySuccess::NestedCases(child_checks),
            ) if !tail.is_empty() => {
                let raw = self.compile_function_raw_predicate(
                    &and_chain_as_fact(&case.case_fact),
                    site,
                    bindings,
                )?;
                lines.push(format!("have _selected_condition : {raw} := {guard_name}"));
                lines.push("rw [if_pos _selected_condition]".into());
                lines.extend(self.compile_recursive_nested_checks(
                    children,
                    child_checks,
                    &branch_site,
                )?);
                let completed = SourcePosition {
                    before: 2,
                    ..branch_site
                };
                lines.extend(self.compile_recursive_equation_path(
                    children,
                    child_checks,
                    tail,
                    merged_guard,
                    total_atoms,
                    offset + atoms.len(),
                    bindings,
                    &completed,
                )?);
            }
            _ => return Err(general_error("EquationPath")),
        }
        Ok(lines)
    }
}

pub(super) fn validate_recursive_case_tree(
    cases: &[HaveFnByInducCase],
    checks: &InducCaseListSuccess,
    name: IdentifierId,
) -> Result<(), LeanCompileError> {
    if cases.is_empty()
        || cases.len() != checks.cases.len()
        || checks.disjoint.len() != cases.len() * (cases.len() - 1) / 2
    {
        return Err(general_error("CaseListShape"));
    }
    if !matches!(source_subject(&checks.coverage)?,Fact::OrFact(f) if f.facts==cases.iter().map(|c|c.case_fact.clone()).collect::<Vec<_>>())
    {
        return Err(general_error("CoverageSubject"));
    }
    let expected = (0..cases.len()).flat_map(|i| (i + 1..cases.len()).map(move |j| (i, j)));
    if checks
        .disjoint
        .iter()
        .zip(expected)
        .any(|(p, (i, j))| p.i != i || p.j != j)
    {
        return Err(general_error("DisjointOrder"));
    }
    for (case, check) in cases.iter().zip(&checks.cases) {
        let qf = match &case.case_fact {
            AndChainAtomicFact::AtomicFact(f) => QuantifierFreeFact::AtomicFact(f.clone()),
            AndChainAtomicFact::AndFact(f) => QuantifierFreeFact::AndFact(f.clone()),
            AndChainAtomicFact::ChainFact(f) => QuantifierFreeFact::ChainFact(f.clone()),
        };
        let mut free = HashSet::new();
        crate::instantiate::collect_free_plain_ids_in_qf_fact(&qf, &HashSet::new(), &mut free);
        if free.contains(&name) {
            return Err(LeanCompileError::unsupported(
                "RecursiveGeneral/SelfDependentGuard",
            ));
        }
        match (&case.body, &check.body) {
            (HaveFnByInducCaseBody::EqualTo(_), InducCaseBodySuccess::EqualTo { .. }) => {}
            (
                HaveFnByInducCaseBody::NestedCases(children),
                InducCaseBodySuccess::NestedCases(child_checks),
            ) => validate_recursive_case_tree(children, child_checks, name)?,
            _ => return Err(general_error("CaseCapture")),
        }
    }
    Ok(())
}

pub(super) fn recursive_leaf_paths(cases: &[HaveFnByInducCase]) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    for (index, case) in cases.iter().enumerate() {
        match &case.body {
            HaveFnByInducCaseBody::EqualTo(_) => result.push(vec![index]),
            HaveFnByInducCaseBody::NestedCases(children) => {
                for mut path in recursive_leaf_paths(children) {
                    path.insert(0, index);
                    result.push(path);
                }
            }
        }
    }
    result
}

pub(super) fn recursive_path_guards<'a>(
    mut cases: &'a [HaveFnByInducCase],
    path: &[usize],
) -> Result<Vec<&'a AndChainAtomicFact>, LeanCompileError> {
    let mut guards = Vec::new();
    for (depth, index) in path.iter().enumerate() {
        let case = cases
            .get(*index)
            .ok_or_else(|| general_error("EquationPath"))?;
        guards.push(&case.case_fact);
        match &case.body {
            HaveFnByInducCaseBody::EqualTo(_) if depth + 1 == path.len() => return Ok(guards),
            HaveFnByInducCaseBody::NestedCases(children) => cases = children,
            _ => return Err(general_error("EquationPath")),
        }
    }
    Err(general_error("EquationPath"))
}

pub(super) fn recursive_guard_atoms(fact: &Fact) -> Result<Vec<AtomicFact>, LeanCompileError> {
    let mut terms = quantifier_free_terms(fact)?;
    if terms.len() != 1 {
        return Err(general_error("CaseGuardFamily"));
    }
    Ok(terms.remove(0))
}
