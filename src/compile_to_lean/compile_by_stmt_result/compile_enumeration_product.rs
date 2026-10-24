use super::compile_by_enumeration::enumeration_conjunction;
use crate::compile_to_lean::compile_expand_range_stmt_result::integer_interval_parts;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::EnumerateAssignmentSuccess;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

pub(super) fn enumeration_parameters(
    fact: &ForallFact,
) -> Result<Vec<(&BoundName, &Obj)>, LeanCompileError> {
    let ids: HashSet<_> = fact
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(|p| p.id))
        .collect();
    let mut parameters = Vec::new();
    for group in &fact.typed_parameters.groups {
        let ParamType::Obj(
            carrier @ Obj::SetFormer(
                SetFormer::ListSet(_) | SetFormer::Range(_) | SetFormer::ClosedRange(_),
            ),
        ) = &group.param_type
        else {
            return Err(LeanCompileError::unsupported("Enumeration/FiniteDomain"));
        };
        let mut free = HashSet::new();
        crate::instantiate::collect_free_plain_ids(carrier, &HashSet::new(), &mut free);
        if !free.is_disjoint(&ids) {
            return Err(LeanCompileError::unsupported("Enumeration/DependentDomain"));
        }
        parameters.extend(group.params.iter().map(|p| (p, carrier)));
    }
    if parameters.is_empty() {
        return Err(LeanCompileError::unsupported("Enumeration/Parameters"));
    }
    Ok(parameters)
}

pub(super) fn enumeration_case_name(index: usize, count: usize) -> String {
    if count == 1 {
        "_enumerated_case".into()
    } else {
        format!("_enumerated_case_{index}")
    }
}

fn binding_value(
    assignment: &EnumerateAssignmentSuccess,
    index: usize,
) -> Result<&Obj, LeanCompileError> {
    let binding = assignment
        .binding_assumptions
        .get(index)
        .ok_or_else(|| LeanCompileError::unsupported("Enumeration/AssignmentStages"))?;
    let StoreFactResult::AtomicFact(stored) = &binding.store_and_infer.store else {
        return Err(LeanCompileError::unsupported(
            "Enumeration/AssignmentBinding",
        ));
    };
    let AtomicFact::EqualFact(fact) = &stored.fact else {
        return Err(LeanCompileError::unsupported(
            "Enumeration/AssignmentBinding",
        ));
    };
    Ok(&fact.right)
}

impl LitexToLeanCompiler {
    // Validate the source's entire product, not just the leaves we happen to emit.
    // Counts are temporary rendering data; values still belong to source domains
    // and the original binding stores, never a second object/proof registry.
    pub(super) fn validate_enumeration_product(
        &self,
        parameters: &[(&BoundName, &Obj)],
        assignments: &[EnumerateAssignmentSuccess],
        position: &SourcePosition<'_>,
    ) -> Result<Vec<usize>, LeanCompileError> {
        let mut counts = Vec::new();
        let mut lowers = Vec::new();
        for (_, carrier) in parameters {
            if let Obj::SetFormer(SetFormer::ListSet(values)) = carrier {
                counts.push(values.list.len());
                lowers.push(None);
            } else {
                let (start, end, closed) = integer_interval_parts(carrier)?;
                let (lower, _) = self.compile_interval_integer_endpoint(start, position)?;
                let (upper, _) = self.compile_interval_integer_endpoint(end, position)?;
                let count = if upper < lower || (!closed && upper == lower) {
                    Some(0)
                } else {
                    upper.checked_sub(lower).and_then(|n| {
                        if closed {
                            n.checked_add(1)
                        } else {
                            Some(n)
                        }
                    })
                };
                let count = count
                    .filter(|n| *n <= 1024)
                    .ok_or_else(|| LeanCompileError::unsupported("Enumeration/IntervalCoverage"))?;
                counts.push(count as usize);
                lowers.push(Some(lower));
            }
        }
        // Match Runtime's ordered, bounded product (including the empty-domain
        // early return). No enumeration work is allocated before this check.
        let mut total = 1usize;
        for count in &counts {
            if *count == 0 {
                total = 0;
                break;
            }
            total = total
                .checked_mul(*count)
                .filter(|n| *n <= 1024)
                .ok_or_else(|| LeanCompileError::unsupported("Enumeration/ProductBudget"))?;
        }
        if total != assignments.len() {
            return Err(LeanCompileError::unsupported("Enumeration/Coverage"));
        }
        for (index, assignment) in assignments.iter().enumerate() {
            if assignment.binding_assumptions.len() != parameters.len() {
                return Err(LeanCompileError::unsupported(
                    "Enumeration/AssignmentStages",
                ));
            }
            let mut remaining = index;
            for j in (0..parameters.len()).rev() {
                let choice = remaining % counts[j];
                remaining /= counts[j];
                let value = binding_value(assignment, j)?;
                if let Some(lower) = lowers[j] {
                    let n = lower.checked_add(choice as i128).ok_or_else(|| {
                        LeanCompileError::unsupported("Enumeration/IntervalValue")
                    })?;
                    if !matches!(value, Obj::Literal(Literal::Number(v)) if v.normalized_value == n.to_string())
                    {
                        return Err(LeanCompileError::unsupported("Enumeration/IntervalOrder"));
                    }
                } else if let Obj::SetFormer(SetFormer::ListSet(values)) = parameters[j].1 {
                    if value != values.list[choice].as_ref() {
                        return Err(LeanCompileError::unsupported("Enumeration/AssignmentOrder"));
                    }
                }
            }
        }
        Ok(counts)
    }

    pub(super) fn compile_enumeration_product(
        &self,
        fact: &ForallFact,
        parameters: &[(&BoundName, &Obj)],
        counts: &[usize],
        assignments: &[EnumerateAssignmentSuccess],
        depth: usize,
        raw_goal: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if depth == parameters.len() {
            let [assignment] = assignments else {
                return Err(LeanCompileError::unsupported("Enumeration/Coverage"));
            };
            let values = (0..parameters.len())
                .map(|i| binding_value(assignment, i))
                .collect::<Result<Vec<_>, _>>()?;
            return self.compile_enumeration_assignment(
                fact, parameters, assignment, &values, raw_goal, position,
            );
        }
        // An empty factor closes the whole product directly. Do not expand all
        // preceding factors to manufacture many identical vacuous branches.
        let depth = if assignments.is_empty() {
            counts
                .iter()
                .position(|n| *n == 0)
                .ok_or_else(|| LeanCompileError::unsupported("Enumeration/Coverage"))?
        } else {
            depth
        };
        let (parameter, carrier) = parameters[depth];
        let SourceOwner::ForallWD(_, wd) = position.owner else {
            return Err(LeanCompileError::unsupported("Enumeration/Header"));
        };
        let member = format!(
            "h_{}",
            wd.introduced_params.defined_params.store_and_infer_results[depth]
                .primary_fact_id()
                .value()
        );
        let input = format!("_value_i{}", parameter.id.value());
        let case = enumeration_case_name(depth, parameters.len());
        let stride = if counts[depth] == 0 {
            0
        } else {
            assignments.len() / counts[depth]
        };
        let branch = |i: usize| {
            self.compile_enumeration_product(
                fact,
                parameters,
                counts,
                &assignments[i * stride..(i + 1) * stride],
                depth + 1,
                raw_goal,
                position,
            )
        };
        if let Obj::SetFormer(SetFormer::ListSet(values)) = carrier {
            let observed = format!("(Litex.denote {input})");
            if values.list.is_empty() {
                return Ok(format!(
                    "(False.elim (Litex.SetSemantics.empty_members {observed} {member}))"
                ));
            }
            let raw_values = values
                .list
                .iter()
                .map(|v| self.compile_function_raw_expression_bound(v, position, &HashMap::new()))
                .collect::<Result<Vec<_>, _>>()?;
            let mut tails =
                vec!["(Litex.SetSemantics.emptyValue (M := M))".to_string(); raw_values.len() + 1];
            for i in (0..raw_values.len()).rev() {
                tails[i] = format!(
                    "(Litex.SetSemantics.insertValue {} {})",
                    raw_values[i],
                    tails[i + 1]
                );
            }
            let mut proof = format!(
                "(False.elim (Litex.SetSemantics.empty_members {observed} _enumerated_tail))"
            );
            for i in (0..counts[depth]).rev() {
                let membership = if i == 0 {
                    member.as_str()
                } else {
                    "_enumerated_tail"
                };
                let child = branch(i)?;
                proof = format!("(Or.elim ((Litex.SetSemantics.insert_members {} {} {observed}).mp {membership}) (fun {case} => {child}) (fun _enumerated_tail => {proof}))", raw_values[i], tails[i+1]);
            }
            Ok(proof)
        } else {
            self.compile_integer_enumeration(carrier, &input, &member, &case, position, branch)
        }
    }

    pub(super) fn compile_enumeration_transport(
        &self,
        facts: &[Fact],
        parameters: &[(&BoundName, &Obj)],
        values: &[&Obj],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let mut raw: HashMap<_, _> = parameters
            .iter()
            .map(|(p, _)| (p.id, format!("(Litex.denote _value_i{})", p.id.value())))
            .collect();
        let mut equality = None;
        for (i, ((parameter, _), value)) in parameters.iter().zip(values).enumerate() {
            raw.insert(parameter.id, "_enumeration_value".into());
            let predicate = enumeration_conjunction(
                facts
                    .iter()
                    .map(|f| self.compile_function_raw_predicate(f, position, &raw))
                    .collect::<Result<_, _>>()?,
            )?;
            let case = enumeration_case_name(i, parameters.len());
            let next =
                format!("(congrArg (fun (_enumeration_value : M.Value) => {predicate}) {case})");
            equality = Some(match equality {
                None => next,
                Some(previous) => format!("(Eq.trans {previous} {next})"),
            });
            raw.insert(
                parameter.id,
                self.compile_function_raw_expression_bound(value, position, &HashMap::new())?,
            );
        }
        equality.ok_or_else(|| LeanCompileError::unsupported("Enumeration/Parameters"))
    }
}
