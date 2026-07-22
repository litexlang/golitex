use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::time::{SystemTime, UNIX_EPOCH};

impl Runtime {
    pub(crate) fn generate_internal_binder_name(&self) -> String {
        let id = self.next_internal_binder_id.get();
        self.next_internal_binder_id.set(
            id.checked_add(1)
                .expect("internal binder identity counter exhausted"),
        );
        format!("#binder_{}", id)
    }

    pub(crate) fn fresh_binder_retag_plan(
        &self,
        source_names: &[String],
        target_kind: ParamObjType,
    ) -> (Vec<String>, HashMap<String, Obj>) {
        let mut target_names = Vec::with_capacity(source_names.len());
        let mut source_to_target = HashMap::with_capacity(source_names.len());
        for source_name in source_names {
            let target_name = self.generate_internal_binder_name();
            source_to_target.insert(
                source_name.clone(),
                obj_for_bound_param_in_scope(target_name.clone(), target_kind),
            );
            target_names.push(target_name);
        }
        (target_names, source_to_target)
    }

    fn generated_name_is_available_with_reserved(
        &self,
        candidate_name: &str,
        reserved_names: &HashSet<String>,
    ) -> bool {
        if is_valid_litex_name(candidate_name).is_err() {
            return false;
        }
        if reserved_names.contains(candidate_name) {
            return false;
        }
        if self.is_name_used_for_identifier(candidate_name) {
            return false;
        }
        true
    }

    pub fn generate_one_unused_name_with_reserved(
        &self,
        reserved_names: &HashSet<String>,
    ) -> String {
        for i in 1..=4096usize {
            let candidate_name = format!("x{}", i);
            if self.generated_name_is_available_with_reserved(&candidate_name, reserved_names) {
                return candidate_name;
            }
        }

        let available_chars: Vec<char> = "abcdefghijklmnopqrstuvwxyz".chars().collect();
        let first_char_candidates: Vec<char> = "abcdefghijklmnopqrstuvwxyz".chars().collect();
        let mut try_index: usize = 0;
        loop {
            let current_time_nanos: u128 = match SystemTime::now().duration_since(UNIX_EPOCH) {
                Ok(current_duration) => current_duration.as_nanos(),
                Err(_) => 0,
            };
            let mixed_seed_value: u128 =
                current_time_nanos ^ ((try_index as u128 + 1) * 0x9e3779b97f4a7c15u128);
            let generated_name_length: usize = 8 + (mixed_seed_value as usize % 17);

            let mut generated_chars: Vec<char> = Vec::new();
            let first_char_index = ((mixed_seed_value >> 1) as usize) % first_char_candidates.len();
            generated_chars.push(first_char_candidates[first_char_index]);

            let mut current_state_value: u128 = mixed_seed_value;
            for character_index in 1..generated_name_length {
                current_state_value = current_state_value
                    .wrapping_mul(6364136223846793005u128)
                    .wrapping_add(1442695040888963407u128 + character_index as u128);
                let available_char_index = (current_state_value as usize) % available_chars.len();
                generated_chars.push(available_chars[available_char_index]);
            }

            let candidate_name: String = generated_chars.into_iter().collect();
            if !self.generated_name_is_available_with_reserved(&candidate_name, reserved_names) {
                try_index += 1;
                continue;
            }
            return candidate_name;
        }
    }

    pub fn generate_random_unused_names(&self, count: usize) -> Vec<String> {
        (0..count)
            .map(|_| self.generate_internal_binder_name())
            .collect()
    }

    pub fn generate_random_unused_name(&self) -> String {
        self.generate_internal_binder_name()
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn generated_kernel_binders_are_unique_and_not_user_names() {
        let runtime = Runtime::new();
        let first = runtime.generate_random_unused_name();
        let second = runtime.generate_random_unused_name();

        assert_ne!(first, second);
        assert!(first.starts_with("#binder_"));
        assert!(is_valid_litex_name(&first).is_err());
    }
}
