use crate::prelude::*;

impl Runtime {
    // `$dvd(x, y)` means that the nonzero integer `y` divides the integer `x`.
    // Example: `$dvd(12, 3)` unfolds to `12 % 3 = 0` and `exist a Z st {12 = a * 3}`.
    pub(crate) fn builtin_dvd_definition_facts(
        &mut self,
        normal_fact: &NormalAtomicFact,
    ) -> Result<Option<Vec<Fact>>, RuntimeError> {
        if !matches!(&normal_fact.predicate, AtomicName::WithoutMod(name) if name == DVD)
            || normal_fact.body.len() != 2
        {
            return Ok(None);
        }

        let dividend = normal_fact.body[0].clone();
        let divisor = normal_fact.body[1].clone();
        let line_file = normal_fact.line_file.clone();
        let zero_remainder: Fact = EqualFact::new(
            Mod::new(dividend.clone(), divisor.clone()).into(),
            Number::new("0".to_string()).into(),
            line_file.clone(),
        )
        .into();

        let witness_name = self.generate_random_unused_name();
        let witness_group = self.fresh_param_group_with_type(
            vec![witness_name],
            ParamType::Obj(StandardSet::Z.into()),
        )?;
        let witness = obj_for_bound_param_in_scope(&witness_group.params[0], ParamObjType::Exist);
        let multiple_equality: AtomicFact = EqualFact::new(
            dividend,
            Mul::new(witness, divisor).into(),
            line_file.clone(),
        )
        .into();
        let multiple_witness: Fact = ExistFactEnum::ExistFact(ExistentialSpec::new(
            ParamDefWithType::new(vec![witness_group]),
            vec![multiple_equality.into()],
            line_file,
        )?)
        .into();

        Ok(Some(vec![zero_remainder, multiple_witness]))
    }
}
