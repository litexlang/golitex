use super::{
    atomic_fact_head, canonical_obj_view, CanonicalMatchError, CompiledRuleSchema, RuleSubstitution,
};
use crate::prelude::*;

#[derive(Clone, Copy, Debug)]
pub struct MatchLimits {
    pub max_nodes: usize,
    pub max_depth: usize,
}

impl Default for MatchLimits {
    fn default() -> Self {
        Self {
            max_nodes: 4096,
            max_depth: 256,
        }
    }
}

fn variable_index(schema: &CompiledRuleSchema, obj: &Obj) -> Option<usize> {
    let Obj::Atom(atom) = obj else {
        return None;
    };
    let symbol = atom.symbol_ref()?;
    schema
        .variables
        .iter()
        .position(|variable| variable.binding.id() == symbol.id())
}

pub fn canonical_objs_equal(
    left: &Obj,
    right: &Obj,
    limits: MatchLimits,
) -> Result<bool, CanonicalMatchError> {
    let mut work = vec![(left, right, 0usize)];
    let mut consumed = 0usize;
    while let Some((left, right, depth)) = work.pop() {
        consumed += 1;
        if consumed > limits.max_nodes || depth > limits.max_depth {
            return Err(CanonicalMatchError {
                message: "canonical object comparison exceeded its structural limit".to_string(),
            });
        }
        let left = canonical_obj_view(left)?;
        let right = canonical_obj_view(right)?;
        if left.tag != right.tag
            || left.scalars != right.scalars
            || left.children.len() != right.children.len()
        {
            return Ok(false);
        }
        work.extend(
            left.children
                .into_iter()
                .zip(right.children)
                .map(|(left, right)| (left, right, depth + 1)),
        );
    }
    Ok(true)
}

pub fn match_conclusion(
    schema: &CompiledRuleSchema,
    goal: &AtomicFact,
    limits: MatchLimits,
) -> Result<Option<RuleSubstitution>, CanonicalMatchError> {
    if schema.head_key != atomic_fact_head(goal) {
        return Ok(None);
    }
    let pattern_args = schema.conclusion.args_ref();
    let goal_args = goal.args_ref();
    if pattern_args.len() != goal_args.len() {
        return Ok(None);
    }

    let mut bindings = vec![None; schema.variables.len()];
    let mut work = pattern_args
        .into_iter()
        .zip(goal_args)
        .map(|(pattern, goal)| (pattern, goal, 0usize))
        .collect::<Vec<_>>();
    let mut consumed = 0usize;

    while let Some((pattern, goal, depth)) = work.pop() {
        consumed += 1;
        if consumed > limits.max_nodes || depth > limits.max_depth {
            return Err(CanonicalMatchError {
                message: "local-rule conclusion match exceeded its structural limit".to_string(),
            });
        }
        if let Some(index) = variable_index(schema, pattern) {
            match &bindings[index] {
                Some(previous) if !canonical_objs_equal(previous, goal, limits)? => {
                    return Ok(None)
                }
                Some(_) => {}
                None => bindings[index] = Some(goal.clone()),
            }
            continue;
        }

        let pattern = canonical_obj_view(pattern)?;
        let goal = match canonical_obj_view(goal) {
            Ok(goal) => goal,
            Err(_) => return Ok(None),
        };
        if pattern.tag != goal.tag
            || pattern.scalars != goal.scalars
            || pattern.children.len() != goal.children.len()
        {
            return Ok(None);
        }
        work.extend(
            pattern
                .children
                .into_iter()
                .zip(goal.children)
                .map(|(pattern, goal)| (pattern, goal, depth + 1)),
        );
    }

    let Some(bindings) = bindings.into_iter().collect::<Option<Vec<_>>>() else {
        return Ok(None);
    };
    Ok(Some(RuleSubstitution::new(bindings)))
}

#[cfg(test)]
#[path = "../../../tests/unit/verify/rule_schema/matcher/tests.rs"]
mod tests;
