use crate::prelude::*;
use std::fmt;

impl fmt::Display for ExecEnv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "Environment {{\n")?;
        write!(
            f,
            "    objs: {:?}\n",
            self.definitions.object_symbol_count()
        )?;
        write!(
            f,
            "    def_props: {:?}\n",
            self.definitions.predicate_definitions.len()
        )?;
        write!(
            f,
            "    algorithms: {:?}\n",
            self.definitions.algorithm_definitions.len()
        )?;
        write!(
            f,
            "    structs: {:?}\n",
            self.definitions.structure_definitions.len()
        )?;
        write!(
            f,
            "    templates: {:?}\n",
            self.definitions.template_definitions.len()
        )?;
        write!(
            f,
            "    settings: {:?}\n",
            self.definitions.setting_definitions.len()
        )?;
        write!(
            f,
            "    known_equality: {:?}\n",
            self.facts.known_equality.len()
        )?;
        write!(
            f,
            "    known_fn_in_fn_set: {:?}\n",
            self.object_properties.function_set_count()
        )?;
        write!(
            f,
            "    known_transitive_props: {:?}\n",
            self.prop_algebraic_properties.transitive_predicate_count()
        )?;
        write!(
            f,
            "    known_symmetric_props: {} predicates, {} permutations\n",
            self.prop_algebraic_properties.symmetric_predicate_count(),
            self.prop_algebraic_properties.symmetric_permutation_count()
        )?;
        write!(
            f,
            "    known_reflexive_props: {:?}\n",
            self.prop_algebraic_properties.reflexive_predicate_count()
        )?;
        write!(
            f,
            "    known_atomic_facts_with_0_or_more_than_two_params: {:?}\n",
            self.facts
                .known_atomic_except_equality_facts
                .by_other_arg_count
                .len()
        )?;
        write!(
            f,
            "    known_atomic_facts_with_1_arg: {:?}\n",
            self.facts
                .known_atomic_except_equality_facts
                .by_one_arg
                .len()
        )?;
        write!(
            f,
            "    known_atomic_facts_with_2_args: {:?}\n",
            self.facts
                .known_atomic_except_equality_facts
                .by_two_args
                .len()
        )?;
        write!(
            f,
            "    known_exist_facts_with_more_than_two_params: {:?}\n",
            self.facts.known_exist.by_key.len()
        )?;
        write!(
            f,
            "    known_or_facts_with_more_than_two_params: {:?}\n",
            self.facts.known_or.by_key.len()
        )?;
        write!(
            f,
            "    known_atomic_facts_in_forall_facts: {:?}\n",
            self.facts
                .forall_conclusions
                .atomic_with_parameterized_head
                .len()
        )?;
        write!(
            f,
            "    known_atomic_facts_in_forall_facts_by_arg_shape: {:?}\n",
            self.facts.forall_conclusions.atomic_by_argument_shape.len()
        )?;
        write!(
            f,
            "    known_exist_facts_in_forall_facts: {:?}\n",
            self.facts.forall_conclusions.existential.len()
        )?;
        write!(
            f,
            "    known_and_facts_in_forall_facts: {:?}\n",
            self.facts.forall_conclusions.conjunction.len()
        )?;
        write!(
            f,
            "    known_or_facts_in_forall_facts: {:?}\n",
            self.facts.forall_conclusions.disjunction.len()
        )?;
        write!(
            f,
            "    stored_fact_lookup_keys: {:?}\n",
            self.facts.stored_facts.lookup_key_count()
        )?;
        write!(f, "}}")
    }
}
