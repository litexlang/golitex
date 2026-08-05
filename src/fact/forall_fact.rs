use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ForallFact {
    pub params_def_with_type: ParamDefWithType,
    pub dom_facts: Vec<Fact>,
    pub then_facts: Vec<ExistOrAndChainAtomicFact>,
    pub line_file: LineFile,
}

impl ForallFact {
    /// Build a forall from surface facts, flattening a sole positive forall conclusion.
    ///
    /// `forall x: P => forall y: Q => R` is stored canonically as
    /// `forall x, y: P, Q => R`. A nested forall must be the only direct
    /// conclusion because one canonical [`ForallFact`] cannot represent the
    /// distributive result of mixing quantified and unquantified conclusions.
    pub fn new(
        params_def_with_type: ParamDefWithType,
        mut dom_facts: Vec<Fact>,
        mut then_facts: Vec<Fact>,
        line_file: LineFile,
    ) -> Result<Self, RuntimeError> {
        if then_facts.len() == 1 {
            let only_fact = then_facts.remove(0);
            if let Fact::ForallFact(inner_forall) = only_fact {
                let mut groups = params_def_with_type.groups;
                groups.extend(inner_forall.params_def_with_type.groups);
                dom_facts.extend(inner_forall.dom_facts);
                return Self::new_canonical_forall(
                    ParamDefWithType::new(groups),
                    dom_facts,
                    inner_forall.then_facts,
                    line_file,
                );
            }
            then_facts.push(only_fact);
        }

        let mut canonical_then_facts = Vec::with_capacity(then_facts.len());
        for fact in then_facts {
            match fact {
                Fact::AtomicFact(fact) => canonical_then_facts.push(fact.into()),
                Fact::ExistFact(fact) => canonical_then_facts.push(fact.into()),
                Fact::OrFact(fact) => canonical_then_facts.push(fact.into()),
                Fact::AndFact(fact) => canonical_then_facts.push(fact.into()),
                Fact::ChainFact(fact) => canonical_then_facts.push(fact.into()),
                Fact::ForallFact(_) => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "a nested forall must be the only direct fact in a forall then clause"
                                .to_string(),
                            line_file,
                        ),
                    )))
                }
                Fact::ForallFactWithIff(_) | Fact::NotForall(_) => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "this quantified fact is not supported in a forall then clause"
                                .to_string(),
                            line_file,
                        ),
                    )))
                }
            }
        }

        Self::new_canonical_forall(
            params_def_with_type,
            dom_facts,
            canonical_then_facts,
            line_file,
        )
    }

    /// Build the canonical internal forall representation.
    ///
    /// The restricted conclusion type is intentional: parameters and premises
    /// from every positive nested forall must already be flattened before this
    /// constructor is called, so stored forall conclusions can never contain
    /// another forall.
    pub fn new_canonical_forall(
        params_def_with_type: ParamDefWithType,
        dom_facts: Vec<Fact>,
        then_facts: Vec<ExistOrAndChainAtomicFact>,
        line_file: LineFile,
    ) -> Result<Self, RuntimeError> {
        let forall_fact = ForallFact {
            params_def_with_type,
            dom_facts,
            then_facts,
            line_file,
        };
        check_forall_fact_has_no_duplicate_forall_free_parameter(&forall_fact)?;
        Ok(forall_fact)
    }

    pub fn expand_then_facts_with_order_chain_closure(&mut self) -> Result<(), RuntimeError> {
        let mut new_then: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        for tf in std::mem::take(&mut self.then_facts) {
            match tf {
                ExistOrAndChainAtomicFact::ChainFact(c) => {
                    let atomics = c.facts_with_order_transitive_closure()?;
                    new_then.push(ExistOrAndChainAtomicFact::ChainFact(c));
                    for af in atomics {
                        new_then.push(ExistOrAndChainAtomicFact::AtomicFact(af));
                    }
                }
                other => new_then.push(other),
            }
        }
        self.then_facts = new_then;
        Ok(())
    }

    pub fn premise_store_reason() -> &'static str {
        "forall premise"
    }
}

impl fmt::Display for ForallFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self.dom_facts.len() {
            0 => write!(
                f,
                "{} {}{}\n{}",
                FORALL,
                self.params_def_with_type.to_string(),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1)
            ),
            _ => write!(
                f,
                "{} {}{}\n{}\n{}{}\n{}",
                FORALL,
                self.params_def_with_type.to_string(),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.dom_facts, 1),
                to_string_and_add_four_spaces_at_beginning_of_each_line(&RIGHT_ARROW, 1),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 2)
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    fn set_param(runtime: &Runtime, name: &str) -> ParamDefWithType {
        ParamDefWithType::new(vec![runtime
            .fresh_param_group_with_type(vec![name.to_string()], ParamType::Set(Set::new()))
            .unwrap()])
    }

    #[test]
    fn new_rejects_nested_forall_reusing_outer_param() {
        let runtime = Runtime::new();
        let inner = ForallFact::new_canonical_forall(
            set_param(&runtime, "x"),
            vec![],
            vec![],
            default_line_file(),
        )
        .unwrap();

        let outer = ForallFact::new_canonical_forall(
            set_param(&runtime, "x"),
            vec![inner.into()],
            vec![],
            default_line_file(),
        );

        assert!(outer.is_err());
    }
}
