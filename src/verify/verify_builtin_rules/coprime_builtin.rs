use crate::prelude::*;

impl Runtime {
    // Decides natural-number coprimality by the gcd-one criterion.
    // Example: `$coprime(14, 25)` and `not $coprime(14, 21)`.
    pub(crate) fn verify_coprime_fact_by_computation(
        &self,
        atomic_fact: &AtomicFact,
    ) -> StmtResult {
        let (fact_is_positive, predicate, args) = match atomic_fact {
            AtomicFact::NormalAtomicFact(f) => (true, &f.predicate, &f.body),
            AtomicFact::NotNormalAtomicFact(f) => (false, &f.predicate, &f.body),
            _ => return StmtUnknown::new().into(),
        };
        if !matches!(predicate, AtomicName::WithoutMod(name) if name == COPRIME) || args.len() != 2
        {
            return StmtUnknown::new().into();
        }

        let Obj::Number(left) = self.resolve_obj(&args[0]) else {
            return StmtUnknown::new().into();
        };
        let Obj::Number(right) = self.resolve_obj(&args[1]) else {
            return StmtUnknown::new().into();
        };
        if left.normalized_value.starts_with('-')
            || right.normalized_value.starts_with('-')
            || left.normalized_value.contains('.')
            || right.normalized_value.contains('.')
        {
            return StmtUnknown::new().into();
        }
        let values_are_coprime = if left.normalized_value == "0" && right.normalized_value == "0" {
            false
        } else {
            gcd_decimal_str_and_normalize(&left.normalized_value, &right.normalized_value)
                .is_some_and(|gcd| gcd == "1")
        };
        if values_are_coprime != fact_is_positive {
            return StmtUnknown::new().into();
        }
        FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
            atomic_fact.clone().into(),
            "deterministic natural coprimality computation".to_string(),
            BuiltinRuleEvidence::CoprimeNaturalReflection,
            Vec::new(),
        )
        .into()
    }

    pub(crate) fn builtin_coprime_definition_facts(
        &self,
        normal_fact: &NormalAtomicFact,
    ) -> Option<Vec<Fact>> {
        if !matches!(&normal_fact.predicate, AtomicName::WithoutMod(name) if name == COPRIME)
            || normal_fact.body.len() != 2
        {
            return None;
        }
        let left = normal_fact.body[0].clone();
        let right = normal_fact.body[1].clone();
        let line_file = normal_fact.line_file.clone();
        let zero: Obj = Number::new("0".to_string()).into();
        let left_nonzero: AtomicFact =
            NotEqualFact::new(left.clone(), zero.clone(), line_file.clone()).into();
        let right_nonzero: AtomicFact =
            NotEqualFact::new(right.clone(), zero, line_file.clone()).into();
        let non_all_zero: Fact = OrFact::new(
            vec![
                AndChainAtomicFact::AtomicFact(left_nonzero),
                AndChainAtomicFact::AtomicFact(right_nonzero),
            ],
            line_file.clone(),
        )
        .into();
        let gcd_is_one: Fact = EqualFact::new(
            Gcd::new(left, right).into(),
            Number::new("1".to_string()).into(),
            line_file,
        )
        .into();
        Some(vec![non_all_zero, gcd_is_one])
    }
}
