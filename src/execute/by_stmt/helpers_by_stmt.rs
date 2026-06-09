use crate::common::helper::is_number_string_literally_integer_without_dot;
use crate::prelude::*;

pub(super) fn impossible_proof_error_message(
    impossible_fact: &AtomicFact,
    option_case_fact_string: Option<String>,
) -> String {
    match option_case_fact_string {
        Some(case_fact) => format!(
            "failed to prove impossible `{}` under case `{}`",
            impossible_fact, case_fact
        ),
        None => format!("failed to prove impossible `{}`", impossible_fact),
    }
}

pub(super) fn user_defined_prop_arity(rt: &Runtime, prop_name: &str) -> Option<usize> {
    if let Some(definition) = rt.get_abstract_prop_definition_by_name(prop_name) {
        return Some(definition.params.len());
    }
    if let Some(definition) = rt.get_prop_definition_by_name(prop_name) {
        return Some(definition.params_def_with_type.collect_param_names().len());
    }
    None
}

pub(super) fn section_inferred_fact(inside_results: &[StmtResult], fact: &Fact) -> bool {
    let target = fact.to_string();
    for result in inside_results.iter() {
        if stmt_result_inferred_fact(result, &target) {
            return true;
        }
    }
    false
}

fn stmt_result_inferred_fact(result: &StmtResult, target: &str) -> bool {
    if let Some(success) = result.non_factual_success() {
        success
            .infers
            .inferred_facts()
            .iter()
            .any(|fact| fact.to_string() == target)
            || success
                .inside_results
                .iter()
                .any(|inside| stmt_result_inferred_fact(inside, target))
    } else if let Some(success) = result.factual_success() {
        success
            .infers
            .inferred_facts()
            .iter()
            .any(|fact| fact.to_string() == target)
    } else {
        false
    }
}

pub(super) fn or_branches_integer_closed_range_equalities(
    element: Obj,
    closed: &ClosedRange,
    line_file: &LineFile,
    stmt_name: &str,
) -> Result<Vec<AndChainAtomicFact>, String> {
    let start_s = range_endpoint_integer_string(closed.start.as_ref(), stmt_name)?;
    let end_s = range_endpoint_integer_string(closed.end.as_ref(), stmt_name)?;
    let start_i: i128 = start_s
        .parse()
        .map_err(|_| format!("{}: invalid integer `{}`", stmt_name, start_s))?;
    let end_i: i128 = end_s
        .parse()
        .map_err(|_| format!("{}: invalid integer `{}`", stmt_name, end_s))?;

    let mut branches: Vec<AndChainAtomicFact> = Vec::new();
    let mut v = start_i;
    while v <= end_i {
        let eq = EqualFact::new(
            element.clone(),
            Number::new(v.to_string()).into(),
            line_file.clone(),
        );
        branches.push(AndChainAtomicFact::AtomicFact(eq.into()));
        v += 1;
    }
    Ok(branches)
}

pub(super) fn or_branches_integer_range_equalities(
    element: Obj,
    range: &Range,
    line_file: &LineFile,
    stmt_name: &str,
) -> Result<Vec<AndChainAtomicFact>, String> {
    let start_s = range_endpoint_integer_string(range.start.as_ref(), stmt_name)?;
    let end_s = range_endpoint_integer_string(range.end.as_ref(), stmt_name)?;
    let start_i: i128 = start_s
        .parse()
        .map_err(|_| format!("{}: invalid integer `{}`", stmt_name, start_s))?;
    let end_i: i128 = end_s
        .parse()
        .map_err(|_| format!("{}: invalid integer `{}`", stmt_name, end_s))?;

    let mut branches: Vec<AndChainAtomicFact> = Vec::new();
    let mut v = start_i;
    while v < end_i {
        let eq = EqualFact::new(
            element.clone(),
            Number::new(v.to_string()).into(),
            line_file.clone(),
        );
        branches.push(AndChainAtomicFact::AtomicFact(eq.into()));
        v += 1;
    }
    Ok(branches)
}

pub(super) fn or_branches_closed_range_start_plus_offset_equalities(
    element: Obj,
    closed: &ClosedRange,
    line_file: &LineFile,
    stmt_name: &str,
) -> Result<Vec<AndChainAtomicFact>, String> {
    let start = closed.start.as_ref();
    let end = closed.end.as_ref();
    let Obj::Add(add) = end else {
        return Err(format!(
            "{}: when start is not an integer literal, end must be start + N",
            stmt_name
        ));
    };
    if add.left.as_ref().to_string() != start.to_string() {
        return Err(format!(
            "{}: end must be start + N (left addend equals range start)",
            stmt_name
        ));
    }
    let offset = offset_integer_literal(add.right.as_ref(), stmt_name)?;
    if offset < 0 {
        return Err(format!(
            "{}: offset N in start + N must be non-negative",
            stmt_name
        ));
    }
    Ok(start_plus_offset_equalities(
        element, start, offset, true, line_file,
    ))
}

pub(super) fn or_branches_range_start_plus_offset_equalities(
    element: Obj,
    range: &Range,
    line_file: &LineFile,
    stmt_name: &str,
) -> Result<Vec<AndChainAtomicFact>, String> {
    let start = range.start.as_ref();
    let end = range.end.as_ref();
    let Obj::Add(add) = end else {
        return Err(format!(
            "{}: when start is not an integer literal, end must be start + N",
            stmt_name
        ));
    };
    if add.left.as_ref().to_string() != start.to_string() {
        return Err(format!(
            "{}: end must be start + N (left addend equals range start)",
            stmt_name
        ));
    }
    let offset = offset_integer_literal(add.right.as_ref(), stmt_name)?;
    if offset < 0 {
        return Err(format!(
            "{}: offset N in start + N must be non-negative",
            stmt_name
        ));
    }
    Ok(start_plus_offset_equalities(
        element, start, offset, false, line_file,
    ))
}

fn range_endpoint_integer_string(obj: &Obj, stmt_name: &str) -> Result<String, String> {
    let Obj::Number(n) = obj else {
        return Err(format!(
            "{}: range endpoints must be integer literals",
            stmt_name
        ));
    };
    let s = n.normalized_value.clone();
    if !is_number_string_literally_integer_without_dot(s.clone()) {
        return Err(format!(
            "{}: range endpoints must be integers (no decimal point)",
            stmt_name
        ));
    }
    Ok(s)
}

fn offset_integer_literal(obj: &Obj, stmt_name: &str) -> Result<i128, String> {
    let Obj::Number(n) = obj else {
        return Err(format!(
            "{}: N in start + N must be an integer literal",
            stmt_name
        ));
    };
    let s = n.normalized_value.clone();
    if !is_number_string_literally_integer_without_dot(s.clone()) {
        return Err(format!(
            "{}: N in start + N must be an integer (no decimal point)",
            stmt_name
        ));
    }
    s.parse()
        .map_err(|_| format!("{}: invalid integer offset `{}`", stmt_name, s))
}

fn start_plus_offset_equalities(
    element: Obj,
    start: &Obj,
    offset: i128,
    end_inclusive: bool,
    line_file: &LineFile,
) -> Vec<AndChainAtomicFact> {
    let mut branches: Vec<AndChainAtomicFact> = Vec::new();
    let right_offset = if end_inclusive { offset } else { offset - 1 };
    let mut i = 0_i128;
    while i <= right_offset {
        let rhs = if i == 0 {
            start.clone()
        } else {
            Add::new(start.clone(), Number::new(i.to_string()).into()).into()
        };
        let eq = EqualFact::new(element.clone(), rhs, line_file.clone());
        branches.push(AndChainAtomicFact::AtomicFact(eq.into()));
        i += 1;
    }
    branches
}
