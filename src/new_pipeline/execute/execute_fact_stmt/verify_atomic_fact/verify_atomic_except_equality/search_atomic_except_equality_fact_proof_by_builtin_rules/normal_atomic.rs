use crate::new_pipeline::ast::fact::{NormalAtomicFact, NotNormalAtomicFact};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::gcd_decimal_str_and_normalize;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::syntax::keywords::{COPRIME, PRIME};

use super::search_atomic_except_equality_fact_proof_by_builtin_rule_result::{
    NormalAtomicCoprimeByComputation, NormalAtomicFactSearchProofByBuiltinRule,
    NormalAtomicPrimeByComputation, NotNormalAtomicFactSearchProofByBuiltinRule,
    NotNormalAtomicNotCoprimeByComputation, NotNormalAtomicNotPrimeByComputation,
};

impl Runtime {
    pub fn search_normal_atomic_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NormalAtomicFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NormalAtomicFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.search_normal_atomic_prime_by_computation(fact)? {
            return Ok(Some(NormalAtomicFactSearchProofByBuiltinRule::PrimeByComputation(
                proof,
            )));
        }
        if let Some(proof) = self.search_normal_atomic_coprime_by_computation(fact)? {
            return Ok(Some(
                NormalAtomicFactSearchProofByBuiltinRule::CoprimeByComputation(proof),
            ));
        }
        Ok(None)
    }

    pub fn search_not_normal_atomic_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotNormalAtomicFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotNormalAtomicFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.search_not_normal_atomic_not_prime_by_computation(fact)? {
            return Ok(Some(
                NotNormalAtomicFactSearchProofByBuiltinRule::NotPrimeByComputation(proof),
            ));
        }
        if let Some(proof) = self.search_not_normal_atomic_not_coprime_by_computation(fact)? {
            return Ok(Some(
                NotNormalAtomicFactSearchProofByBuiltinRule::NotCoprimeByComputation(proof),
            ));
        }
        Ok(None)
    }

    // Deterministic primality for a closed natural/u64 value.
    // Mathematical property: `$prime(n)` holds exactly when the resolved
    // nonnegative integer is prime.
    // Example: `$prime(17)`.
    fn search_normal_atomic_prime_by_computation(
        &self,
        fact: &NormalAtomicFact,
    ) -> RuntimeResult<Option<NormalAtomicPrimeByComputation>> {
        if fact.predicate.local_name() != PRIME || fact.body.len() != 1 {
            return Ok(None);
        }
        let Some(value) = self.resolve_obj_to_normalized_number(&fact.body[0]) else {
            return Ok(None);
        };
        let Ok(n) = value.parse::<u64>() else {
            return Ok(None);
        };
        if !is_prime_u64(n) {
            return Ok(None);
        }
        Ok(Some(NormalAtomicPrimeByComputation {
            resolved_value: value,
        }))
    }

    // Deterministic natural coprimality via gcd-one.
    // Mathematical property: `$coprime(a, b)` when both resolve to nonnegative
    // integers that are not both zero and `gcd(a, b) = 1`.
    // Example: `$coprime(14, 25)`.
    fn search_normal_atomic_coprime_by_computation(
        &self,
        fact: &NormalAtomicFact,
    ) -> RuntimeResult<Option<NormalAtomicCoprimeByComputation>> {
        if fact.predicate.local_name() != COPRIME || fact.body.len() != 2 {
            return Ok(None);
        }
        let Some((left, right)) = self.resolve_nonneg_integer_pair(&fact.body[0], &fact.body[1])
        else {
            return Ok(None);
        };
        if !values_are_coprime(&left, &right) {
            return Ok(None);
        }
        Ok(Some(NormalAtomicCoprimeByComputation {
            left_resolved: left,
            right_resolved: right,
        }))
    }

    // Deterministic non-primality for a closed natural/u64 value.
    // Mathematical property: `not $prime(n)` when the resolved nonnegative
    // integer is composite or below 2.
    // Example: `not $prime(1)`, `not $prime(9)`.
    fn search_not_normal_atomic_not_prime_by_computation(
        &self,
        fact: &NotNormalAtomicFact,
    ) -> RuntimeResult<Option<NotNormalAtomicNotPrimeByComputation>> {
        if fact.predicate.local_name() != PRIME || fact.body.len() != 1 {
            return Ok(None);
        }
        let Some(value) = self.resolve_obj_to_normalized_number(&fact.body[0]) else {
            return Ok(None);
        };
        let Ok(n) = value.parse::<u64>() else {
            return Ok(None);
        };
        if is_prime_u64(n) {
            return Ok(None);
        }
        Ok(Some(NotNormalAtomicNotPrimeByComputation {
            resolved_value: value,
        }))
    }

    // Deterministic non-coprimality via gcd.
    // Mathematical property: `not $coprime(a, b)` when both resolve to
    // nonnegative integers with `gcd != 1` (including `0, 0`).
    // Example: `not $coprime(14, 21)`, `not $coprime(0, 0)`.
    fn search_not_normal_atomic_not_coprime_by_computation(
        &self,
        fact: &NotNormalAtomicFact,
    ) -> RuntimeResult<Option<NotNormalAtomicNotCoprimeByComputation>> {
        if fact.predicate.local_name() != COPRIME || fact.body.len() != 2 {
            return Ok(None);
        }
        let Some((left, right)) = self.resolve_nonneg_integer_pair(&fact.body[0], &fact.body[1])
        else {
            return Ok(None);
        };
        if values_are_coprime(&left, &right) {
            return Ok(None);
        }
        Ok(Some(NotNormalAtomicNotCoprimeByComputation {
            left_resolved: left,
            right_resolved: right,
        }))
    }

    fn resolve_nonneg_integer_pair(
        &self,
        left: &crate::new_pipeline::ast::obj::Obj,
        right: &crate::new_pipeline::ast::obj::Obj,
    ) -> Option<(String, String)> {
        let left = self.resolve_obj_to_normalized_number(left)?;
        let right = self.resolve_obj_to_normalized_number(right)?;
        if left.starts_with('-')
            || right.starts_with('-')
            || left.contains('.')
            || right.contains('.')
        {
            return None;
        }
        Some((left, right))
    }
}

fn values_are_coprime(left: &str, right: &str) -> bool {
    if left == "0" && right == "0" {
        return false;
    }
    gcd_decimal_str_and_normalize(left, right).is_some_and(|gcd| gcd == "1")
}

// Deterministic Miller–Rabin-style primality for u64 (same bases as legacy).
fn is_prime_u64(value: u64) -> bool {
    if value < 2 {
        return false;
    }
    for prime in [2_u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if value == prime {
            return true;
        }
        if value % prime == 0 {
            return false;
        }
    }

    let mut odd_part = value - 1;
    let mut power_of_two = 0_u32;
    while odd_part % 2 == 0 {
        odd_part /= 2;
        power_of_two += 1;
    }
    for base in [2_u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut witness = mod_pow_u64(base % value, odd_part, value);
        if witness == 1 || witness == value - 1 {
            continue;
        }
        let mut passed = false;
        for _ in 1..power_of_two {
            witness = mod_mul_u64(witness, witness, value);
            if witness == value - 1 {
                passed = true;
                break;
            }
        }
        if !passed {
            return false;
        }
    }
    true
}

fn mod_pow_u64(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut result = 1_u64;
    while exponent > 0 {
        if exponent % 2 == 1 {
            result = mod_mul_u64(result, base, modulus);
        }
        exponent /= 2;
        if exponent > 0 {
            base = mod_mul_u64(base, base, modulus);
        }
    }
    result
}

fn mod_mul_u64(left: u64, right: u64, modulus: u64) -> u64 {
    ((left as u128 * right as u128) % modulus as u128) as u64
}
