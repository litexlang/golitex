//! Registration rules for Environment predicate algebraic properties.

use crate::prelude::*;

impl ExecEnv {
    pub fn store_transitive_prop_name(&mut self, prop_name: String) {
        self.predicate_algebraic_properties
            .properties_mut(prop_name)
            .is_transitive = true;
    }

    pub fn store_reflexive_prop_name(&mut self, prop_name: String) {
        self.predicate_algebraic_properties
            .properties_mut(prop_name)
            .is_reflexive = true;
    }

    pub fn store_antisymmetric_prop_name(&mut self, prop_name: String) {
        self.predicate_algebraic_properties
            .properties_mut(prop_name)
            .is_antisymmetric = true;
    }

    pub fn store_symmetric_prop_permutation(
        &mut self,
        prop_name: String,
        gather: Vec<usize>,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let n = gather.len();
        if n < 2 {
            return Err(
                StoreFactRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "store_symmetric_prop_permutation: arity must be at least 2".to_string(),
                    line_file,
                ))
                .into(),
            );
        }
        if !symmetric_gather_is_valid_permutation(&gather, n) {
            return Err(
                StoreFactRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "store_symmetric_prop_permutation: gather is not a valid permutation"
                        .to_string(),
                    line_file,
                ))
                .into(),
            );
        }
        if symmetric_gather_is_identity(&gather) {
            return Err(
                StoreFactRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "store_symmetric_prop_permutation: identity permutation is not allowed"
                        .to_string(),
                    line_file,
                ))
                .into(),
            );
        }
        if let Some(existing) = self
            .predicate_algebraic_properties
            .symmetric_argument_permutations(&prop_name)
        {
            if let Some(first) = existing.first() {
                if first.len() != n {
                    return Err(StoreFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                            "store_symmetric_prop_permutation: `{}` already has arity {}, got {}",
                            prop_name,
                            first.len(),
                            n
                        ),
                            line_file,
                        ),
                    )
                    .into());
                }
            }
        }
        let entry = &mut self
            .predicate_algebraic_properties
            .properties_mut(prop_name)
            .symmetric_argument_permutations;
        if entry.iter().any(|g| g == &gather) {
            return Ok(());
        }
        entry.push(gather);
        Ok(())
    }
}

fn symmetric_gather_is_identity(gather: &[usize]) -> bool {
    gather.iter().enumerate().all(|(i, &g)| g == i)
}

fn symmetric_gather_is_valid_permutation(gather: &[usize], n: usize) -> bool {
    if gather.len() != n {
        return false;
    }
    let mut seen = vec![false; n];
    for &i in gather {
        if i >= n {
            return false;
        }
        if seen[i] {
            return false;
        }
        seen[i] = true;
    }
    true
}
