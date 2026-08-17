use super::{
    atomic_fact_head, canonical_obj_view, CompiledRuleSchema, RuleFingerprint, RuleId,
    RuleSourceRef, RuleVariable,
};
use crate::prelude::*;
use std::collections::HashSet;
use std::rc::Rc;

fn schema_error(message: impl Into<String>) -> RuntimeError {
    RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(
        message.into(),
    )))
}

fn parameter_requirement(
    binding: &SymbolBinding,
    param_type: &ParamType,
    line_file: LineFile,
) -> AtomicFact {
    let parameter = obj_for_bound_param_in_scope(binding, ParamObjType::Forall);
    match param_type {
        ParamType::Obj(set) => InFact::new(parameter, set.clone(), line_file).into(),
        ParamType::Set(_) => IsSetFact::new(parameter, line_file).into(),
        ParamType::NonemptySet(_) => IsNonemptySetFact::new(parameter, line_file).into(),
        ParamType::FiniteSet(_) => IsFiniteSetFact::new(parameter, line_file).into(),
    }
}

fn validate_pattern_and_collect_variables(
    root: &Obj,
    variable_ids: &HashSet<SymbolId>,
    used: &mut HashSet<SymbolId>,
) -> Result<(), RuntimeError> {
    let mut work = vec![root];
    let mut consumed = 0usize;
    while let Some(obj) = work.pop() {
        consumed += 1;
        if consumed > 4096 {
            return Err(schema_error(
                "local builtin schema exceeds the structural node limit",
            ));
        }
        if let Obj::Atom(atom) = obj {
            if let Some(symbol) = atom.symbol_ref() {
                if variable_ids.contains(&symbol.id()) {
                    used.insert(symbol.id());
                    continue;
                }
            }
        }
        let view = canonical_obj_view(obj).map_err(|error| schema_error(error.message))?;
        work.extend(view.children);
    }
    Ok(())
}

pub(crate) fn compile_local_builtin_schema(
    source: &str,
    rule_id: RuleId,
    semantic_fingerprint: RuleFingerprint,
) -> Result<CompiledRuleSchema, RuntimeError> {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(&format!("local_builtin::{}", rule_id.as_str()));
    let mut blocks =
        Tokenizer::new().parse_blocks(source, Rc::from(format!("{}.lit", rule_id.as_str())))?;
    if blocks.len() != 1 {
        return Err(schema_error(format!(
            "local builtin `{}` must contain exactly one statement",
            rule_id.as_str()
        )));
    }
    let statement = runtime.parse_stmt(&mut blocks[0])?;
    let Stmt::Fact(Fact::ForallFact(forall)) = statement else {
        return Err(schema_error(format!(
            "local builtin `{}` must be one ordinary forall fact",
            rule_id.as_str()
        )));
    };
    if forall.then_facts.len() != 1 {
        return Err(schema_error(format!(
            "local builtin `{}` must have exactly one conclusion",
            rule_id.as_str()
        )));
    }
    let ExistOrAndChainAtomicFact::AtomicFact(conclusion) = &forall.then_facts[0] else {
        return Err(schema_error(format!(
            "local builtin `{}` conclusion must be atomic",
            rule_id.as_str()
        )));
    };

    let mut premises = Vec::with_capacity(forall.dom_facts.len());
    for premise in &forall.dom_facts {
        let premise = match premise {
            Fact::AtomicFact(fact) => QuantifierFreeFact::AtomicFact(fact.clone()),
            Fact::AndFact(fact) => QuantifierFreeFact::AndFact(fact.clone()),
            Fact::ChainFact(fact) => QuantifierFreeFact::ChainFact(fact.clone()),
            Fact::OrFact(fact) => QuantifierFreeFact::OrFact(fact.clone()),
            Fact::ExistFact(_)
            | Fact::ForallFact(_)
            | Fact::ForallFactWithIff(_)
            | Fact::NotForall(_) => {
                return Err(schema_error(format!(
                    "local builtin `{}` premises must be quantifier-free",
                    rule_id.as_str()
                )));
            }
        };
        premises.push(premise);
    }

    let variables = forall
        .params_def_with_type
        .collect_param_bindings_with_types()
        .into_iter()
        .map(|(binding, param_type)| RuleVariable {
            binding,
            param_type,
        })
        .collect::<Vec<_>>();
    if variables.is_empty() {
        return Err(schema_error(format!(
            "local builtin `{}` must bind at least one object",
            rule_id.as_str()
        )));
    }
    let variable_ids = variables
        .iter()
        .map(|variable| variable.binding.id())
        .collect::<HashSet<_>>();

    let mut used_in_conclusion = HashSet::new();
    for obj in conclusion.args_ref() {
        validate_pattern_and_collect_variables(obj, &variable_ids, &mut used_in_conclusion)?;
    }
    if let Some(missing) = variables
        .iter()
        .find(|variable| !used_in_conclusion.contains(&variable.binding.id()))
    {
        return Err(schema_error(format!(
            "local builtin `{}` parameter `{}` does not occur in its conclusion",
            rule_id.as_str(),
            missing.binding.name()
        )));
    }

    for variable in &variables {
        if let ParamType::Obj(obj) = &variable.param_type {
            validate_pattern_and_collect_variables(obj, &variable_ids, &mut HashSet::new())?;
        }
    }
    for premise in &premises {
        for obj in premise.get_args_from_fact_ref() {
            validate_pattern_and_collect_variables(obj, &variable_ids, &mut HashSet::new())?;
        }
    }

    let parameter_requirements = variables
        .iter()
        .map(|variable| {
            parameter_requirement(
                &variable.binding,
                &variable.param_type,
                forall.line_file.clone(),
            )
        })
        .collect();
    let conclusion = conclusion.clone();
    Ok(CompiledRuleSchema {
        source: RuleSourceRef::LocalBuiltin {
            rule_id,
            semantic_fingerprint,
        },
        variables,
        parameter_requirements,
        premises,
        head_key: atomic_fact_head(&conclusion),
        conclusion,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_builtin_schema_accepts_every_quantifier_free_premise_shape() {
        let schema = compile_local_builtin_schema(
            r#"
forall a, b, c R:
    a <= b
    a <= b and b <= c
    a <= b <= c
    a = b or b = c
    =>:
        a + b <= c
"#,
            RuleId::new("test.quantifier_free_premises").expect("valid test rule id"),
            RuleFingerprint::from_hex("0".repeat(64)).expect("valid test fingerprint"),
        )
        .expect("all quantifier-free premise variants should compile");

        assert!(matches!(
            schema.premises[0],
            QuantifierFreeFact::AtomicFact(_)
        ));
        assert!(matches!(schema.premises[1], QuantifierFreeFact::AndFact(_)));
        assert!(matches!(
            schema.premises[2],
            QuantifierFreeFact::ChainFact(_)
        ));
        assert!(matches!(schema.premises[3], QuantifierFreeFact::OrFact(_)));
    }
}
