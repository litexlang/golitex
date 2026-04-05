use crate::prelude::*;
use std::collections::HashSet;
use std::time::{SystemTime, UNIX_EPOCH};

impl Runtime {
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
        if self.is_name_used(candidate_name) {
            return false;
        }
        for names_in_scope in self.parsing_time_name_scope_stack.iter() {
            if names_in_scope.contains_key(candidate_name) {
                return false;
            }
        }
        true
    }

    fn generate_one_unused_name_with_reserved(&self, reserved_names: &HashSet<String>) -> String {
        const READABLE_GENERATED_NAME_CHARS: &str = "abcdefghijklmnopqrstuvwxyz";

        for readable_round in 0..4096usize {
            let readable_char = READABLE_GENERATED_NAME_CHARS
                .chars()
                .nth(readable_round % READABLE_GENERATED_NAME_CHARS.len())
                .unwrap();
            let candidate_name = if readable_round < READABLE_GENERATED_NAME_CHARS.len() {
                format!("_{}_", readable_char)
            } else {
                format!(
                    "_{}{}_",
                    readable_char,
                    readable_round / READABLE_GENERATED_NAME_CHARS.len()
                )
            };
            if self.generated_name_is_available_with_reserved(&candidate_name, reserved_names) {
                return candidate_name;
            }
        }

        let available_chars: Vec<char> = "abcdefghijklmnopqrstuvwxyz0123456789".chars().collect();
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
        let mut reserved_names: HashSet<String> = HashSet::with_capacity(count);
        let mut generated_names: Vec<String> = Vec::with_capacity(count);
        for _ in 0..count {
            let generated_name = self.generate_one_unused_name_with_reserved(&reserved_names);
            reserved_names.insert(generated_name.clone());
            generated_names.push(generated_name);
        }
        generated_names
    }
}
