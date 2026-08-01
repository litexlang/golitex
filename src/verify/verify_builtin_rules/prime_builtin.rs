use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_prime_fact_by_computation(&self, atomic_fact: &AtomicFact) -> StmtResult {
        let (fact_is_positive, predicate, args) = match atomic_fact {
            AtomicFact::NormalAtomicFact(f) => (true, &f.predicate, &f.body),
            AtomicFact::NotNormalAtomicFact(f) => (false, &f.predicate, &f.body),
            _ => return StmtUnknown::new().into(),
        };
        if !matches!(predicate, AtomicName::WithoutMod(name) if name == PRIME) || args.len() != 1 {
            return StmtUnknown::new().into();
        }

        let Obj::Number(number) = self.resolve_obj(&args[0]) else {
            return StmtUnknown::new().into();
        };
        let Ok(value) = number.normalized_value.parse::<u64>() else {
            return StmtUnknown::new().into();
        };
        if is_prime_u64(value) != fact_is_positive {
            return StmtUnknown::new().into();
        }
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            atomic_fact.clone().into(),
            "deterministic primality computation for u64".to_string(),
            Vec::new(),
        )
        .into()
    }

    pub(crate) fn builtin_prime_definition_facts(
        &mut self,
        normal_fact: &NormalAtomicFact,
    ) -> Result<Option<Vec<Fact>>, RuntimeError> {
        if !matches!(&normal_fact.predicate, AtomicName::WithoutMod(name) if name == PRIME)
            || normal_fact.body.len() != 1
        {
            return Ok(None);
        }
        let value = normal_fact.body[0].clone();
        let line_file = normal_fact.line_file.clone();
        let lower_bound: Fact = LessEqualFact::new(
            Number::new("2".to_string()).into(),
            value.clone(),
            line_file.clone(),
        )
        .into();

        let divisor_name = self.generate_random_unused_name();
        let divisor_group = self.fresh_param_group_with_type(
            vec![divisor_name],
            ParamType::Obj(Range::new(Number::new("2".to_string()).into(), value.clone()).into()),
        )?;
        let divisor = obj_for_bound_param_in_scope(&divisor_group.params[0], ParamObjType::Forall);
        let no_divisor: AtomicFact = NotEqualFact::new(
            Mod::new(value, divisor).into(),
            Number::new("0".to_string()).into(),
            line_file.clone(),
        )
        .into();
        let trial_division: Fact = ForallFact::new(
            ParamDefWithType::new(vec![divisor_group]),
            Vec::new(),
            vec![no_divisor.into()],
            line_file,
        )?
        .into();
        Ok(Some(vec![lower_bound, trial_division]))
    }
}

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
