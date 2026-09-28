use crate::new_pipeline::ast::fact::{
    Fact, GreaterEqualFact, GreaterFact, InFact, IsFiniteSetFact, IsNonemptySetFact, LessEqualFact,
    LessFact, NotEqualFact, NotInFact, SubsetFact,
};
use crate::new_pipeline::ast::line_file::SourceLine;
use crate::new_pipeline::ast::obj::{Literal, Number, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub(super) fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }))
}

pub(super) fn one_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "1".to_string(),
    }))
}

pub(super) fn two_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "2".to_string(),
    }))
}

pub(super) fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "0"
    )
}


impl Runtime {
    pub(super) fn verify_strategy_requirements(
        &mut self,
        requirement_facts: Vec<Fact>,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<(Vec<Fact>, Vec<VerifyFactResult>)>> {
        let child_state = verify_state.without_well_defined_storage();
        let mut proof_of_requirement_facts = Vec::with_capacity(requirement_facts.len());
        for requirement in &requirement_facts {
            let proof = self.verify_fact(requirement, child_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proof_of_requirement_facts.push(proof);
        }
        Ok(Some((requirement_facts, proof_of_requirement_facts)))
    }

    pub(super) fn try_strategy_requirement_alternatives(
        &mut self,
        alternatives: Vec<Vec<Fact>>,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<(Vec<Fact>, Vec<VerifyFactResult>)>> {
        for required in alternatives {
            if let Some(ok) = self.verify_strategy_requirements(required, verify_state.clone())? {
                return Ok(Some(ok));
            }
        }
        Ok(None)
    }

    pub(super) fn strategy_less_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_greater_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_less_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file,
        }
        .into()
    }


    pub(super) fn strategy_not_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_in_fact(
        &mut self,
        element: Obj,
        set: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element,
            set,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_not_in_fact(
        &mut self,
        element: Obj,
        set: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        NotInFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element,
            set,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_subset_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_is_finite_set_fact(
        &mut self,
        set: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        IsFiniteSetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_is_nonempty_set_fact(
        &mut self,
        set: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        IsNonemptySetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set,
            line_file,
        }
        .into()
    }
}
