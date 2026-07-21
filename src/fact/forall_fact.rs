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
    pub fn new(
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

    fn set_param(name: &str) -> ParamDefWithType {
        ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![name.to_string()],
            ParamType::Set(Set::new()),
        )])
    }

    #[test]
    fn new_rejects_nested_forall_reusing_outer_param() {
        let inner = ForallFact::new(set_param("x"), vec![], vec![], default_line_file()).unwrap();

        let outer = ForallFact::new(
            set_param("x"),
            vec![inner.into()],
            vec![],
            default_line_file(),
        );

        assert!(outer.is_err());
    }
}
