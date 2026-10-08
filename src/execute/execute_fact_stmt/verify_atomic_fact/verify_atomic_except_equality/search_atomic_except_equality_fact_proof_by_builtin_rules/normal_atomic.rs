use crate::ast::fact::{
    CoprimeFact, NormalAtomicFact, NotCoprimeFact, NotNormalAtomicFact, NotPrimeFact, PrimeFact,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::gcd_decimal_str_and_normalize;
use crate::runtime::{Runtime, RuntimeResult};

use super::search_atomic_except_equality_fact_proof_by_builtin_rule_result::{
    CoprimeByComputation, CoprimeFactSearchProofByBuiltinRule,
    NormalAtomicFactSearchProofByBuiltinRule, NotCoprimeByComputation,
    NotCoprimeFactSearchProofByBuiltinRule, NotNormalAtomicFactSearchProofByBuiltinRule,
    NotPrimeByComputation, NotPrimeFactSearchProofByBuiltinRule, PrimeByComputation,
    PrimeFactSearchProofByBuiltinRule,
};

impl Runtime {
    // Official `$prime` / `$coprime` now use dedicated AtomicFact variants.
    // User-defined `$prop(...)` has no NormalAtomic builtin search yet.
    pub fn search_normal_atomic_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NormalAtomicFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NormalAtomicFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_normal_atomic_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotNormalAtomicFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotNormalAtomicFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_prime_fact_proof_by_builtin_rule(
        &mut self,
        fact: &PrimeFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<PrimeFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.search_prime_by_computation(fact)? {
            return Ok(Some(PrimeFactSearchProofByBuiltinRule::PrimeByComputation(
                proof,
            )));
        }
        Ok(None)
    }

    pub fn search_coprime_fact_proof_by_builtin_rule(
        &mut self,
        fact: &CoprimeFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<CoprimeFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.search_coprime_by_computation(fact)? {
            return Ok(Some(
                CoprimeFactSearchProofByBuiltinRule::CoprimeByComputation(proof),
            ));
        }
        Ok(None)
    }

    pub fn search_not_prime_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotPrimeFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotPrimeFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.search_not_prime_by_computation(fact)? {
            return Ok(Some(
                NotPrimeFactSearchProofByBuiltinRule::NotPrimeByComputation(proof),
            ));
        }
        Ok(None)
    }

    pub fn search_not_coprime_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotCoprimeFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotCoprimeFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.search_not_coprime_by_computation(fact)? {
            return Ok(Some(
                NotCoprimeFactSearchProofByBuiltinRule::NotCoprimeByComputation(proof),
            ));
        }
        Ok(None)
    }

    // Deterministic primality for a closed natural/u64 value.
    // Mathematical property: `$prime(n)` holds exactly when the resolved
    // nonnegative integer is prime.
    // Example: `$prime(17)`.
    fn search_prime_by_computation(
        &self,
        fact: &PrimeFact,
    ) -> RuntimeResult<Option<PrimeByComputation>> {
        let Some(value) = self.resolve_obj_to_normalized_number(&fact.value) else {
            return Ok(None);
        };
        let Ok(n) = value.parse::<u64>() else {
            return Ok(None);
        };
        if !is_prime_u64(n) {
            return Ok(None);
        }
        Ok(Some(PrimeByComputation {
            resolved_value: value,
        }))
    }

    // Deterministic natural coprimality via gcd-one.
    // Mathematical property: `$coprime(a, b)` when both resolve to nonnegative
    // integers that are not both zero and `gcd(a, b) = 1`.
    // Example: `$coprime(14, 25)`.
    fn search_coprime_by_computation(
        &self,
        fact: &CoprimeFact,
    ) -> RuntimeResult<Option<CoprimeByComputation>> {
        let Some((left, right)) = self.resolve_nonneg_integer_pair(&fact.left, &fact.right) else {
            return Ok(None);
        };
        if !values_are_coprime(&left, &right) {
            return Ok(None);
        }
        Ok(Some(CoprimeByComputation {
            left_resolved: left,
            right_resolved: right,
        }))
    }

    // Deterministic non-primality for a closed natural/u64 value.
    // Mathematical property: `not $prime(n)` when the resolved nonnegative
    // integer is composite or below 2.
    // Example: `not $prime(1)`, `not $prime(9)`.
    fn search_not_prime_by_computation(
        &self,
        fact: &NotPrimeFact,
    ) -> RuntimeResult<Option<NotPrimeByComputation>> {
        let Some(value) = self.resolve_obj_to_normalized_number(&fact.value) else {
            return Ok(None);
        };
        let Ok(n) = value.parse::<u64>() else {
            return Ok(None);
        };
        if is_prime_u64(n) {
            return Ok(None);
        }
        Ok(Some(NotPrimeByComputation {
            resolved_value: value,
        }))
    }

    // Deterministic non-coprimality via gcd.
    // Mathematical property: `not $coprime(a, b)` when both resolve to
    // nonnegative integers with `gcd != 1` (including `0, 0`).
    // Example: `not $coprime(14, 21)`, `not $coprime(0, 0)`.
    fn search_not_coprime_by_computation(
        &self,
        fact: &NotCoprimeFact,
    ) -> RuntimeResult<Option<NotCoprimeByComputation>> {
        let Some((left, right)) = self.resolve_nonneg_integer_pair(&fact.left, &fact.right) else {
            return Ok(None);
        };
        if values_are_coprime(&left, &right) {
            return Ok(None);
        }
        Ok(Some(NotCoprimeByComputation {
            left_resolved: left,
            right_resolved: right,
        }))
    }

    fn resolve_nonneg_integer_pair(
        &self,
        left: &crate::ast::obj::Obj,
        right: &crate::ast::obj::Obj,
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
