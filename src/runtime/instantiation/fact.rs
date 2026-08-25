//! Capture-avoiding fact instantiation.

use crate::prelude::*;
use std::collections::{HashMap, HashSet};

impl Runtime {
    fn line_file_after_inst(original: &LineFile, inst_to_line_file: Option<&LineFile>) -> LineFile {
        inst_to_line_file
            .cloned()
            .unwrap_or_else(|| original.clone())
    }

    /// `inst_to_line_file`: `None` keeps each node's original line file (verify, exec, parsing).
    /// `Some(lf)` assigns `lf` throughout the instance (infer: tie the new fact to the use site).
    pub fn inst_fact(
        &self,
        fact: &Fact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_to_line_file: Option<LineFile>,
    ) -> Result<Fact, RuntimeError> {
        let inst_lf = inst_to_line_file.as_ref();
        Ok(match fact {
            Fact::AtomicFact(atomic_fact) => Fact::AtomicFact(self.inst_atomic_fact(
                atomic_fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            Fact::ExistFact(exist_fact) => Fact::ExistFact(self.inst_exist_fact(
                exist_fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            Fact::OrFact(or_fact) => Fact::OrFact(self.inst_or_fact(
                or_fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            Fact::AndFact(and_fact) => Fact::AndFact(self.inst_and_fact(
                and_fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            Fact::ChainFact(chain_fact) => Fact::ChainFact(self.inst_chain_fact(
                chain_fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            Fact::ForallFact(forall_fact) => Fact::ForallFact(self.inst_forall_fact(
                forall_fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                Fact::ForallFactWithIff(self.inst_forall_fact_with_iff(
                    forall_fact_with_iff,
                    param_to_arg_map,
                    to_inst_param_type,
                    inst_lf,
                )?)
            }
            Fact::NotForall(not_forall) => {
                Fact::NotForall(NotForallFact::new(self.inst_forall_fact(
                    &not_forall.forall_fact,
                    param_to_arg_map,
                    to_inst_param_type,
                    inst_lf,
                )?))
            }
        })
    }

    pub fn inst_exist_or_and_chain_atomic_fact(
        &self,
        fact: &ExistOrAndChainAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<ExistOrAndChainAtomicFact, RuntimeError> {
        Ok(match fact {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                ExistOrAndChainAtomicFact::AtomicFact(self.inst_atomic_fact(
                    atomic_fact,
                    param_to_arg_map,
                    to_inst_param_type,
                    inst_lf,
                )?)
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => ExistOrAndChainAtomicFact::AndFact(
                self.inst_and_fact(and_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                ExistOrAndChainAtomicFact::ChainFact(self.inst_chain_fact(
                    chain_fact,
                    param_to_arg_map,
                    to_inst_param_type,
                    inst_lf,
                )?)
            }
            ExistOrAndChainAtomicFact::OrFact(or_fact) => ExistOrAndChainAtomicFact::OrFact(
                self.inst_or_fact(or_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
                ExistOrAndChainAtomicFact::ExistFact(self.inst_exist_fact(
                    exist_fact,
                    param_to_arg_map,
                    to_inst_param_type,
                    inst_lf,
                )?)
            }
        })
    }

    pub fn inst_quantifier_free_fact(
        &self,
        fact: &QuantifierFreeFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<QuantifierFreeFact, RuntimeError> {
        Ok(match fact {
            QuantifierFreeFact::AtomicFact(atomic_fact) => QuantifierFreeFact::AtomicFact(
                self.inst_atomic_fact(atomic_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            QuantifierFreeFact::AndFact(and_fact) => QuantifierFreeFact::AndFact(
                self.inst_and_fact(and_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            QuantifierFreeFact::ChainFact(chain_fact) => QuantifierFreeFact::ChainFact(
                self.inst_chain_fact(chain_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            QuantifierFreeFact::OrFact(or_fact) => QuantifierFreeFact::OrFact(self.inst_or_fact(
                or_fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
        })
    }

    pub fn inst_and_chain_atomic_fact(
        &self,
        fact: &AndChainAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<AndChainAtomicFact, RuntimeError> {
        Ok(match fact {
            AndChainAtomicFact::AtomicFact(atomic_fact) => AndChainAtomicFact::AtomicFact(
                self.inst_atomic_fact(atomic_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AndChainAtomicFact::AndFact(and_fact) => AndChainAtomicFact::AndFact(
                self.inst_and_fact(and_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AndChainAtomicFact::ChainFact(chain_fact) => AndChainAtomicFact::ChainFact(
                self.inst_chain_fact(chain_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
        })
    }

    pub fn inst_atomic_fact(
        &self,
        atomic_fact: &AtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<AtomicFact, RuntimeError> {
        Ok(match atomic_fact {
            AtomicFact::NormalAtomicFact(fact) => AtomicFact::NormalAtomicFact(
                self.inst_normal_atomic_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AtomicFact::EqualFact(fact) => AtomicFact::EqualFact(self.inst_equal_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::LessFact(fact) => AtomicFact::LessFact(self.inst_less_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::GreaterFact(fact) => AtomicFact::GreaterFact(self.inst_greater_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::LessEqualFact(fact) => AtomicFact::LessEqualFact(
                self.inst_less_equal_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AtomicFact::GreaterEqualFact(fact) => AtomicFact::GreaterEqualFact(
                self.inst_greater_equal_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AtomicFact::IsSetFact(fact) => AtomicFact::IsSetFact(self.inst_is_set_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::IsNonemptySetFact(fact) => {
                AtomicFact::IsNonemptySetFact(self.inst_is_nonempty_set_fact(
                    fact,
                    param_to_arg_map,
                    to_inst_param_type,
                    inst_lf,
                )?)
            }
            AtomicFact::IsFiniteSetFact(fact) => AtomicFact::IsFiniteSetFact(
                self.inst_is_finite_set_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AtomicFact::InFact(fact) => AtomicFact::InFact(self.inst_in_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::IsCartFact(fact) => AtomicFact::IsCartFact(self.inst_is_cart_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::IsTupleFact(fact) => AtomicFact::IsTupleFact(self.inst_is_tuple_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::SubsetFact(fact) => AtomicFact::SubsetFact(self.inst_subset_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::SupersetFact(fact) => AtomicFact::SupersetFact(self.inst_superset_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::NotNormalAtomicFact(fact) => {
                AtomicFact::NotNormalAtomicFact(self.inst_not_normal_atomic_fact(
                    fact,
                    param_to_arg_map,
                    to_inst_param_type,
                    inst_lf,
                )?)
            }
            AtomicFact::NotEqualFact(fact) => AtomicFact::NotEqualFact(self.inst_not_equal_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::NotLessFact(fact) => AtomicFact::NotLessFact(self.inst_not_less_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::NotGreaterFact(fact) => AtomicFact::NotGreaterFact(
                self.inst_not_greater_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AtomicFact::NotLessEqualFact(fact) => AtomicFact::NotLessEqualFact(
                self.inst_not_less_equal_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AtomicFact::NotGreaterEqualFact(fact) => {
                AtomicFact::NotGreaterEqualFact(self.inst_not_greater_equal_fact(
                    fact,
                    param_to_arg_map,
                    to_inst_param_type,
                    inst_lf,
                )?)
            }
            AtomicFact::NotIsSetFact(fact) => AtomicFact::NotIsSetFact(self.inst_not_is_set_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::NotIsNonemptySetFact(fact) => {
                AtomicFact::NotIsNonemptySetFact(self.inst_not_is_nonempty_set_fact(
                    fact,
                    param_to_arg_map,
                    to_inst_param_type,
                    inst_lf,
                )?)
            }
            AtomicFact::NotIsFiniteSetFact(fact) => {
                AtomicFact::NotIsFiniteSetFact(self.inst_not_is_finite_set_fact(
                    fact,
                    param_to_arg_map,
                    to_inst_param_type,
                    inst_lf,
                )?)
            }
            AtomicFact::NotInFact(fact) => AtomicFact::NotInFact(self.inst_not_in_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::NotIsCartFact(fact) => AtomicFact::NotIsCartFact(
                self.inst_not_is_cart_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AtomicFact::NotIsTupleFact(fact) => AtomicFact::NotIsTupleFact(
                self.inst_not_is_tuple_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AtomicFact::NotSubsetFact(fact) => AtomicFact::NotSubsetFact(
                self.inst_not_subset_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AtomicFact::NotSupersetFact(fact) => AtomicFact::NotSupersetFact(
                self.inst_not_superset_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            AtomicFact::FnEqualInFact(fact) => AtomicFact::FnEqualInFact(FnEqualInFact::new(
                self.inst_obj(&fact.left, param_to_arg_map, to_inst_param_type)?,
                self.inst_obj(&fact.right, param_to_arg_map, to_inst_param_type)?,
                self.inst_obj(&fact.set, param_to_arg_map, to_inst_param_type)?,
                Self::line_file_after_inst(&fact.line_file, inst_lf),
            )),
            AtomicFact::FnEqualFact(fact) => AtomicFact::FnEqualFact(FnEqualFact::new(
                self.inst_obj(&fact.left, param_to_arg_map, to_inst_param_type)?,
                self.inst_obj(&fact.right, param_to_arg_map, to_inst_param_type)?,
                Self::line_file_after_inst(&fact.line_file, inst_lf),
            )),
        })
    }

    pub fn inst_normal_atomic_fact(
        &self,
        normal_atomic_fact: &NormalAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NormalAtomicFact, RuntimeError> {
        let mut body = Vec::with_capacity(normal_atomic_fact.body.len());
        for obj in normal_atomic_fact.body.iter() {
            body.push(self.inst_obj(obj, param_to_arg_map, to_inst_param_type)?);
        }
        Ok(NormalAtomicFact::new(
            normal_atomic_fact.predicate.clone(),
            body,
            Self::line_file_after_inst(&normal_atomic_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_equal_fact(
        &self,
        equal_fact: &EqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<EqualFact, RuntimeError> {
        Ok(EqualFact::new(
            self.inst_obj(&equal_fact.left, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&equal_fact.right, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&equal_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_less_fact(
        &self,
        less_fact: &LessFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<LessFact, RuntimeError> {
        Ok(LessFact::new(
            self.inst_obj(&less_fact.left, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&less_fact.right, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&less_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_greater_fact(
        &self,
        greater_fact: &GreaterFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<GreaterFact, RuntimeError> {
        Ok(GreaterFact::new(
            self.inst_obj(&greater_fact.left, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&greater_fact.right, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&greater_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_less_equal_fact(
        &self,
        less_equal_fact: &LessEqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<LessEqualFact, RuntimeError> {
        Ok(LessEqualFact::new(
            self.inst_obj(&less_equal_fact.left, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&less_equal_fact.right, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&less_equal_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_greater_equal_fact(
        &self,
        greater_equal_fact: &GreaterEqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<GreaterEqualFact, RuntimeError> {
        Ok(GreaterEqualFact::new(
            self.inst_obj(
                &greater_equal_fact.left,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            self.inst_obj(
                &greater_equal_fact.right,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&greater_equal_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_is_set_fact(
        &self,
        is_set_fact: &IsSetFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<IsSetFact, RuntimeError> {
        Ok(IsSetFact::new(
            self.inst_obj(&is_set_fact.set, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&is_set_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_is_nonempty_set_fact(
        &self,
        is_nonempty_set_fact: &IsNonemptySetFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<IsNonemptySetFact, RuntimeError> {
        Ok(IsNonemptySetFact::new(
            self.inst_obj(
                &is_nonempty_set_fact.set,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&is_nonempty_set_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_is_finite_set_fact(
        &self,
        is_finite_set_fact: &IsFiniteSetFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<IsFiniteSetFact, RuntimeError> {
        Ok(IsFiniteSetFact::new(
            self.inst_obj(
                &is_finite_set_fact.set,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&is_finite_set_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_in_fact(
        &self,
        in_fact: &InFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<InFact, RuntimeError> {
        Ok(InFact::new(
            self.inst_obj(&in_fact.element, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&in_fact.set, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&in_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_is_cart_fact(
        &self,
        is_cart_fact: &IsCartFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<IsCartFact, RuntimeError> {
        Ok(IsCartFact::new(
            self.inst_obj(&is_cart_fact.set, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&is_cart_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_is_tuple_fact(
        &self,
        is_tuple_fact: &IsTupleFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<IsTupleFact, RuntimeError> {
        Ok(IsTupleFact::new(
            self.inst_obj(&is_tuple_fact.set, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&is_tuple_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_subset_fact(
        &self,
        subset_fact: &SubsetFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<SubsetFact, RuntimeError> {
        Ok(SubsetFact::new(
            self.inst_obj(&subset_fact.left, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&subset_fact.right, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&subset_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_superset_fact(
        &self,
        superset_fact: &SupersetFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<SupersetFact, RuntimeError> {
        Ok(SupersetFact::new(
            self.inst_obj(&superset_fact.left, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&superset_fact.right, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&superset_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_normal_atomic_fact(
        &self,
        not_normal_atomic_fact: &NotNormalAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotNormalAtomicFact, RuntimeError> {
        let mut body = Vec::with_capacity(not_normal_atomic_fact.body.len());
        for obj in not_normal_atomic_fact.body.iter() {
            body.push(self.inst_obj(obj, param_to_arg_map, to_inst_param_type)?);
        }
        Ok(NotNormalAtomicFact::new(
            not_normal_atomic_fact.predicate.clone(),
            body,
            Self::line_file_after_inst(&not_normal_atomic_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_equal_fact(
        &self,
        not_equal_fact: &NotEqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotEqualFact, RuntimeError> {
        Ok(NotEqualFact::new(
            self.inst_obj(&not_equal_fact.left, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&not_equal_fact.right, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&not_equal_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_less_fact(
        &self,
        not_less_fact: &NotLessFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotLessFact, RuntimeError> {
        Ok(NotLessFact::new(
            self.inst_obj(&not_less_fact.left, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&not_less_fact.right, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&not_less_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_greater_fact(
        &self,
        not_greater_fact: &NotGreaterFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotGreaterFact, RuntimeError> {
        Ok(NotGreaterFact::new(
            self.inst_obj(&not_greater_fact.left, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(
                &not_greater_fact.right,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&not_greater_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_less_equal_fact(
        &self,
        not_less_equal_fact: &NotLessEqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotLessEqualFact, RuntimeError> {
        Ok(NotLessEqualFact::new(
            self.inst_obj(
                &not_less_equal_fact.left,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            self.inst_obj(
                &not_less_equal_fact.right,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&not_less_equal_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_greater_equal_fact(
        &self,
        not_greater_equal_fact: &NotGreaterEqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotGreaterEqualFact, RuntimeError> {
        Ok(NotGreaterEqualFact::new(
            self.inst_obj(
                &not_greater_equal_fact.left,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            self.inst_obj(
                &not_greater_equal_fact.right,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&not_greater_equal_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_is_set_fact(
        &self,
        not_is_set_fact: &NotIsSetFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotIsSetFact, RuntimeError> {
        Ok(NotIsSetFact::new(
            self.inst_obj(&not_is_set_fact.set, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&not_is_set_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_is_nonempty_set_fact(
        &self,
        not_is_nonempty_set_fact: &NotIsNonemptySetFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotIsNonemptySetFact, RuntimeError> {
        Ok(NotIsNonemptySetFact::new(
            self.inst_obj(
                &not_is_nonempty_set_fact.set,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&not_is_nonempty_set_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_is_finite_set_fact(
        &self,
        not_is_finite_set_fact: &NotIsFiniteSetFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotIsFiniteSetFact, RuntimeError> {
        Ok(NotIsFiniteSetFact::new(
            self.inst_obj(
                &not_is_finite_set_fact.set,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&not_is_finite_set_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_in_fact(
        &self,
        not_in_fact: &NotInFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotInFact, RuntimeError> {
        Ok(NotInFact::new(
            self.inst_obj(&not_in_fact.element, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&not_in_fact.set, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&not_in_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_is_cart_fact(
        &self,
        not_is_cart_fact: &NotIsCartFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotIsCartFact, RuntimeError> {
        Ok(NotIsCartFact::new(
            self.inst_obj(&not_is_cart_fact.set, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&not_is_cart_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_is_tuple_fact(
        &self,
        not_is_tuple_fact: &NotIsTupleFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotIsTupleFact, RuntimeError> {
        Ok(NotIsTupleFact::new(
            self.inst_obj(&not_is_tuple_fact.set, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&not_is_tuple_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_subset_fact(
        &self,
        not_subset_fact: &NotSubsetFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotSubsetFact, RuntimeError> {
        Ok(NotSubsetFact::new(
            self.inst_obj(&not_subset_fact.left, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(&not_subset_fact.right, param_to_arg_map, to_inst_param_type)?,
            Self::line_file_after_inst(&not_subset_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_superset_fact(
        &self,
        not_superset_fact: &NotSupersetFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotSupersetFact, RuntimeError> {
        Ok(NotSupersetFact::new(
            self.inst_obj(
                &not_superset_fact.left,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            self.inst_obj(
                &not_superset_fact.right,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&not_superset_fact.line_file, inst_lf),
        ))
    }

    /// Reconstruct the exact existential denoted by a concrete proposition
    /// call. This is shared by execution and compiler-certificate checking so
    /// neither path trusts the parser's cached expansion.
    pub fn instantiate_existential_prop_definition(
        &self,
        fact: &NormalAtomicFact,
        definition: &DefPropStmt,
        line_file: &LineFile,
    ) -> Result<ExistFactEnum, RuntimeError> {
        let invalid_source = |message: String| {
            RuntimeError::from(InstantiateRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(message, line_file.clone()),
            ))
        };
        let predicate_name = fact.predicate.to_string();
        let local_predicate_name = predicate_name
            .rsplit_once(MOD_SIGN)
            .map(|(_, local_name)| local_name)
            .unwrap_or(predicate_name.as_str());
        if local_predicate_name != definition.name {
            return Err(invalid_source(format!(
                "source prop `{}` does not match retained definition `{}`",
                predicate_name, definition.name
            )));
        }
        if definition.iff_facts.len() != 1 {
            return Err(invalid_source(format!(
                "prop `{}` must have exactly one definition clause",
                predicate_name
            )));
        }
        let Fact::ExistFact(definition_exist_fact) = &definition.iff_facts[0] else {
            return Err(invalid_source(format!(
                "the sole definition clause of `{}` must be `exist` or `exist!`",
                predicate_name
            )));
        };
        if definition_exist_fact.is_not_exist() {
            return Err(invalid_source(format!(
                "the definition clause of `{}` is `not exist`",
                predicate_name
            )));
        }

        let param_to_arg_map = self.params_to_arg_map(&definition.typed_parameters, &fact.body)?;
        self.inst_exist_fact(
            definition_exist_fact,
            &param_to_arg_map,
            SubstitutionMode::Exact,
            Some(line_file),
        )
    }

    pub fn inst_exist_fact(
        &self,
        exist_fact: &ExistFactEnum,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<ExistFactEnum, RuntimeError> {
        let rename_map = self.exist_capture_avoiding_rename_map(exist_fact, param_to_arg_map);
        let renamed_exist_fact = self.alpha_rename_exist_fact(exist_fact, &rename_map)?;
        self.inst_exist_fact_without_capture_preparation(
            &renamed_exist_fact,
            param_to_arg_map,
            to_inst_param_type,
            inst_lf,
        )
    }

    fn inst_exist_fact_without_capture_preparation(
        &self,
        exist_fact: &ExistFactEnum,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<ExistFactEnum, RuntimeError> {
        let mut groups = Vec::with_capacity(exist_fact.typed_parameters().groups.len());
        for param_def_with_type in exist_fact.typed_parameters().groups.iter() {
            groups.push(TypedParameterGroup::new(
                param_def_with_type.params.clone(),
                self.inst_param_type(
                    &param_def_with_type.param_type,
                    param_to_arg_map,
                    to_inst_param_type,
                )?,
            ));
        }
        let typed_parameters = TypedParameterList::new(groups);
        let mut facts = Vec::with_capacity(exist_fact.facts().len());
        for fact in exist_fact.facts().iter() {
            facts.push(self.inst_quantifier_free_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?);
        }
        let body = ExistentialSpec::new(
            typed_parameters,
            facts,
            Self::line_file_after_inst(&exist_fact.spec().line_file, inst_lf),
        )?;
        Ok(match exist_fact {
            ExistFactEnum::ExistFact(_) => ExistFactEnum::ExistFact(body),
            ExistFactEnum::ExistUniqueFact(_) => ExistFactEnum::ExistUniqueFact(body),
            ExistFactEnum::NotExistFact(_) => ExistFactEnum::NotExistFact(body),
        })
    }

    fn exist_capture_avoiding_rename_map(
        &self,
        exist_fact: &ExistFactEnum,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> HashMap<String, Obj> {
        let mut replacement_exist_names = HashSet::new();
        for replacement in param_to_arg_map.values() {
            replacement_exist_names.extend(replacement.collect_bound_param_names());
        }

        let mut reserved_names = replacement_exist_names.clone();
        collect_bound_param_names_in_exist_fact(exist_fact, &mut reserved_names);

        let mut rename_map = HashMap::new();
        for group in &exist_fact.typed_parameters().groups {
            for binding in &group.params {
                let conflicts_with_visible_binding = self
                    .visible_symbol_definition(binding.name())
                    .is_some_and(|visible| visible.binding().id() != binding.id());
                if !replacement_exist_names.contains(binding.name())
                    && !conflicts_with_visible_binding
                {
                    continue;
                }
                let fresh_binding = if conflicts_with_visible_binding {
                    self.allocate_internal_symbol_binding()
                        .expect("internal binder identity counter exhausted")
                } else {
                    let fresh_name = self.generate_one_unused_name_with_reserved(&reserved_names);
                    reserved_names.insert(fresh_name.clone());
                    self.allocate_local_symbol_binding(fresh_name)
                        .expect("internal binder identity counter exhausted")
                };
                insert_symbol_substitution(
                    &mut rename_map,
                    binding,
                    BoundParamObj::new(&fresh_binding).into(),
                );
            }
        }
        rename_map
    }

    pub fn alpha_rename_exist_fact(
        &self,
        exist_fact: &ExistFactEnum,
        rename_map: &HashMap<String, Obj>,
    ) -> Result<ExistFactEnum, RuntimeError> {
        if rename_map.is_empty() {
            return Ok(exist_fact.clone());
        }

        let mut groups = Vec::with_capacity(exist_fact.typed_parameters().groups.len());
        let mut active_rename_map = HashMap::new();
        for group in exist_fact.typed_parameters().groups.iter() {
            let param_type = self.inst_param_type(
                &group.param_type,
                &active_rename_map,
                SubstitutionMode::Exact,
            )?;
            let params = group
                .params
                .iter()
                .map(|binding| renamed_exist_param_binding(binding, rename_map))
                .collect::<Vec<_>>();
            groups.push(TypedParameterGroup::new(params, param_type));
            for binding in group.params.iter() {
                if let Some(replacement) = rename_map.get(&binding.substitution_key()) {
                    insert_symbol_substitution(
                        &mut active_rename_map,
                        binding,
                        replacement.clone(),
                    );
                }
            }
        }

        let mut facts = Vec::with_capacity(exist_fact.facts().len());
        for fact in exist_fact.facts().iter() {
            facts.push(self.inst_quantifier_free_fact(
                fact,
                rename_map,
                SubstitutionMode::Exact,
                None,
            )?);
        }
        let body = ExistentialSpec::new(
            TypedParameterList::new(groups),
            facts,
            exist_fact.spec().line_file.clone(),
        )?;
        Ok(match exist_fact {
            ExistFactEnum::ExistFact(_) => ExistFactEnum::ExistFact(body),
            ExistFactEnum::ExistUniqueFact(_) => ExistFactEnum::ExistUniqueFact(body),
            ExistFactEnum::NotExistFact(_) => ExistFactEnum::NotExistFact(body),
        })
    }

    pub fn inst_or_fact(
        &self,
        or_fact: &OrFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<OrFact, RuntimeError> {
        let mut facts = Vec::with_capacity(or_fact.facts.len());
        for fact in or_fact.facts.iter() {
            facts.push(self.inst_and_chain_atomic_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?);
        }
        Ok(OrFact::new(
            facts,
            Self::line_file_after_inst(&or_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_and_fact(
        &self,
        and_fact: &AndFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<AndFact, RuntimeError> {
        let mut facts = Vec::with_capacity(and_fact.facts.len());
        for fact in and_fact.facts.iter() {
            facts.push(self.inst_atomic_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?);
        }
        Ok(AndFact::new(
            facts,
            Self::line_file_after_inst(&and_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_chain_fact(
        &self,
        chain_fact: &ChainFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<ChainFact, RuntimeError> {
        let mut objs = Vec::with_capacity(chain_fact.objs.len());
        for obj in chain_fact.objs.iter() {
            objs.push(self.inst_obj(obj, param_to_arg_map, to_inst_param_type)?);
        }
        Ok(ChainFact::new(
            objs,
            chain_fact.prop_names.clone(),
            Self::line_file_after_inst(&chain_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_forall_fact(
        &self,
        forall_fact: &ForallFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<ForallFact, RuntimeError> {
        let rename_map =
            self.forall_capture_avoiding_rename_map(forall_fact, &[], param_to_arg_map);
        let renamed_forall_fact = self.alpha_rename_forall_fact(forall_fact, &rename_map)?;
        self.inst_forall_fact_without_capture_preparation(
            &renamed_forall_fact,
            param_to_arg_map,
            to_inst_param_type,
            inst_lf,
        )
    }

    pub fn inst_forall_fact_without_capture_preparation(
        &self,
        forall_fact: &ForallFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<ForallFact, RuntimeError> {
        let mut groups = Vec::with_capacity(forall_fact.typed_parameters.groups.len());
        for param_def_with_type in forall_fact.typed_parameters.groups.iter() {
            groups.push(TypedParameterGroup::new(
                param_def_with_type.params.clone(),
                self.inst_param_type(
                    &param_def_with_type.param_type,
                    param_to_arg_map,
                    to_inst_param_type,
                )?,
            ));
        }
        let typed_parameters = TypedParameterList::new(groups);
        let mut dom_facts = Vec::with_capacity(forall_fact.dom_facts.len());
        for dom_fact in forall_fact.dom_facts.iter() {
            dom_facts.push(self.inst_fact(
                dom_fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf.cloned(),
            )?);
        }
        let mut then_facts = Vec::with_capacity(forall_fact.then_facts.len());
        for then_fact in forall_fact.then_facts.iter() {
            then_facts.push(self.inst_exist_or_and_chain_atomic_fact(
                then_fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?);
        }
        Ok(ForallFact::new_canonical_forall(
            typed_parameters,
            dom_facts,
            then_facts,
            Self::line_file_after_inst(&forall_fact.line_file, inst_lf),
        )?)
    }

    pub fn inst_forall_fact_with_iff(
        &self,
        forall_fact_with_iff: &ForallFactWithIff,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: SubstitutionMode,
        inst_lf: Option<&LineFile>,
    ) -> Result<ForallFactWithIff, RuntimeError> {
        let rename_map = self.forall_capture_avoiding_rename_map(
            &forall_fact_with_iff.forall_fact,
            &forall_fact_with_iff.iff_facts,
            param_to_arg_map,
        );
        let renamed_forall_fact =
            self.alpha_rename_forall_fact(&forall_fact_with_iff.forall_fact, &rename_map)?;
        let forall_fact = self.inst_forall_fact_without_capture_preparation(
            &renamed_forall_fact,
            param_to_arg_map,
            to_inst_param_type,
            inst_lf,
        )?;
        let mut iff_facts = Vec::with_capacity(forall_fact_with_iff.iff_facts.len());
        for iff_fact in forall_fact_with_iff.iff_facts.iter() {
            let renamed_iff_fact = self.inst_exist_or_and_chain_atomic_fact(
                iff_fact,
                &rename_map,
                SubstitutionMode::Exact,
                None,
            )?;
            iff_facts.push(self.inst_exist_or_and_chain_atomic_fact(
                &renamed_iff_fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?);
        }
        Ok(ForallFactWithIff::new(
            forall_fact,
            iff_facts,
            Self::line_file_after_inst(&forall_fact_with_iff.line_file, inst_lf),
        )?)
    }

    fn forall_capture_avoiding_rename_map(
        &self,
        forall_fact: &ForallFact,
        extra_scope_facts: &[ExistOrAndChainAtomicFact],
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> HashMap<String, Obj> {
        let mut replacement_forall_names = HashSet::new();
        for replacement in param_to_arg_map.values() {
            replacement_forall_names.extend(replacement.collect_forall_free_param_names());
        }

        let mut reserved_names = replacement_forall_names.clone();
        collect_bound_param_names_in_forall_fact(forall_fact, &mut reserved_names);
        for fact in extra_scope_facts {
            collect_bound_param_names_in_exist_or_fact(fact, &mut reserved_names);
        }

        let mut rename_map = HashMap::new();
        for group in &forall_fact.typed_parameters.groups {
            for binding in &group.params {
                let conflicts_with_visible_binding = self
                    .visible_symbol_definition(binding.name())
                    .is_some_and(|visible| visible.binding().id() != binding.id());
                if !replacement_forall_names.contains(binding.name())
                    && !conflicts_with_visible_binding
                {
                    continue;
                }
                let fresh_binding = if conflicts_with_visible_binding {
                    self.allocate_internal_symbol_binding()
                        .expect("internal binder identity counter exhausted")
                } else {
                    let fresh_name = self.generate_one_unused_name_with_reserved(&reserved_names);
                    reserved_names.insert(fresh_name.clone());
                    self.allocate_local_symbol_binding(fresh_name)
                        .expect("internal binder identity counter exhausted")
                };
                insert_symbol_substitution(
                    &mut rename_map,
                    binding,
                    BoundParamObj::new(&fresh_binding).into(),
                );
            }
        }
        rename_map
    }

    pub fn alpha_rename_forall_fact(
        &self,
        forall_fact: &ForallFact,
        rename_map: &HashMap<String, Obj>,
    ) -> Result<ForallFact, RuntimeError> {
        if rename_map.is_empty() {
            return Ok(forall_fact.clone());
        }

        let mut groups = Vec::with_capacity(forall_fact.typed_parameters.groups.len());
        let mut active_rename_map = HashMap::new();
        for group in forall_fact.typed_parameters.groups.iter() {
            let param_type = self.inst_param_type(
                &group.param_type,
                &active_rename_map,
                SubstitutionMode::Exact,
            )?;
            let params = group
                .params
                .iter()
                .map(|binding| renamed_forall_param_binding(binding, rename_map))
                .collect::<Vec<_>>();
            groups.push(TypedParameterGroup::new(params, param_type));
            for binding in group.params.iter() {
                if let Some(replacement) = rename_map.get(&binding.substitution_key()) {
                    insert_symbol_substitution(
                        &mut active_rename_map,
                        binding,
                        replacement.clone(),
                    );
                }
            }
        }

        let mut dom_facts = Vec::with_capacity(forall_fact.dom_facts.len());
        for fact in forall_fact.dom_facts.iter() {
            dom_facts.push(self.inst_fact(fact, rename_map, SubstitutionMode::Exact, None)?);
        }
        let mut then_facts = Vec::with_capacity(forall_fact.then_facts.len());
        for fact in forall_fact.then_facts.iter() {
            then_facts.push(self.inst_exist_or_and_chain_atomic_fact(
                fact,
                rename_map,
                SubstitutionMode::Exact,
                None,
            )?);
        }

        ForallFact::new_canonical_forall(
            TypedParameterList::new(groups),
            dom_facts,
            then_facts,
            forall_fact.line_file.clone(),
        )
    }

    pub fn alpha_normalized_forall_cache_key(
        &self,
        forall_fact: &ForallFact,
    ) -> Result<String, RuntimeError> {
        let mut rename_map = HashMap::new();
        let mut index = 0;
        for group in &forall_fact.typed_parameters.groups {
            for source_binding in &group.params {
                let target_binding =
                    SymbolBinding::alpha_canonical(index, format!("#forall_cache_{}", index));
                insert_symbol_substitution(
                    &mut rename_map,
                    source_binding,
                    BoundParamObj::new(&target_binding).into(),
                );
                index += 1;
            }
        }
        let mut normalized = self.alpha_rename_forall_fact(forall_fact, &rename_map)?;
        let groups = normalized
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| {
                group.params.iter().map(|param| {
                    TypedParameterGroup::new(vec![param.clone()], group.param_type.clone())
                })
            })
            .collect();
        normalized.typed_parameters = TypedParameterList::new(groups);
        Ok(nested_obj_binder_normalized_fact_key(&Fact::from(
            normalized,
        )))
    }

    pub fn collect_bound_param_names_in_exist_fact(
        &self,
        exist_fact: &ExistFactEnum,
        names: &mut HashSet<String>,
    ) {
        collect_bound_param_names_in_exist_fact(exist_fact, names);
    }
}

fn renamed_forall_param_binding(
    binding: &SymbolBinding,
    rename_map: &HashMap<String, Obj>,
) -> SymbolBinding {
    match rename_map.get(&binding.substitution_key()) {
        Some(Obj::Atom(AtomObj::Bound(param))) => param.symbol.to_local_binding(),
        _ => binding.clone(),
    }
}

fn renamed_exist_param_binding(
    binding: &SymbolBinding,
    rename_map: &HashMap<String, Obj>,
) -> SymbolBinding {
    match rename_map.get(&binding.substitution_key()) {
        Some(Obj::Atom(AtomObj::Bound(param))) => param.symbol.to_local_binding(),
        _ => binding.clone(),
    }
}

fn collect_bound_param_names_in_forall_fact(forall_fact: &ForallFact, names: &mut HashSet<String>) {
    collect_bound_param_names_in_param_def(&forall_fact.typed_parameters, names);
    for fact in forall_fact.dom_facts.iter() {
        collect_bound_param_names_in_fact(fact, names);
    }
    for fact in forall_fact.then_facts.iter() {
        collect_bound_param_names_in_exist_or_fact(fact, names);
    }
}

fn collect_bound_param_names_in_fact(fact: &Fact, names: &mut HashSet<String>) {
    match fact {
        Fact::ExistFact(fact) => collect_bound_param_names_in_exist_fact(fact, names),
        Fact::ForallFact(fact) => collect_bound_param_names_in_forall_fact(fact, names),
        Fact::ForallFactWithIff(fact) => {
            collect_bound_param_names_in_forall_fact(&fact.forall_fact, names);
            for iff_fact in fact.iff_facts.iter() {
                collect_bound_param_names_in_exist_or_fact(iff_fact, names);
            }
        }
        Fact::NotForall(fact) => collect_bound_param_names_in_forall_fact(&fact.forall_fact, names),
        Fact::AtomicFact(fact) => {
            collect_bound_param_names_in_args(fact.get_args_from_fact_ref(), names)
        }
        Fact::OrFact(fact) => {
            collect_bound_param_names_in_args(fact.get_args_from_fact_ref(), names)
        }
        Fact::AndFact(fact) => {
            collect_bound_param_names_in_args(fact.get_args_from_fact_ref(), names)
        }
        Fact::ChainFact(fact) => {
            collect_bound_param_names_in_args(fact.get_args_from_fact_ref(), names)
        }
    }
}

pub fn collect_bound_param_names_in_exist_fact(
    exist_fact: &ExistFactEnum,
    names: &mut HashSet<String>,
) {
    collect_bound_param_names_in_param_def(exist_fact.typed_parameters(), names);
    for fact in exist_fact.facts().iter() {
        collect_bound_param_names_in_args(fact.get_args_from_fact_ref(), names);
    }
}

fn collect_bound_param_names_in_exist_or_fact(
    fact: &ExistOrAndChainAtomicFact,
    names: &mut HashSet<String>,
) {
    match fact {
        ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
            collect_bound_param_names_in_exist_fact(exist_fact, names)
        }
        ExistOrAndChainAtomicFact::AtomicFact(fact) => {
            collect_bound_param_names_in_args(fact.get_args_from_fact_ref(), names)
        }
        ExistOrAndChainAtomicFact::AndFact(fact) => {
            collect_bound_param_names_in_args(fact.get_args_from_fact_ref(), names)
        }
        ExistOrAndChainAtomicFact::ChainFact(fact) => {
            collect_bound_param_names_in_args(fact.get_args_from_fact_ref(), names)
        }
        ExistOrAndChainAtomicFact::OrFact(fact) => {
            collect_bound_param_names_in_args(fact.get_args_from_fact_ref(), names)
        }
    }
}

fn collect_bound_param_names_in_param_def(
    params: &TypedParameterList,
    names: &mut HashSet<String>,
) {
    for group in params.groups.iter() {
        names.extend(
            group
                .params
                .iter()
                .map(|binding| binding.name().to_string()),
        );
        if let ParamType::Obj(obj) = &group.param_type {
            names.extend(obj.collect_bound_param_names());
        }
    }
}

fn collect_bound_param_names_in_args(args: Vec<&Obj>, names: &mut HashSet<String>) {
    for arg in args {
        names.extend(arg.collect_bound_param_names());
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/runtime/instantiation/fact/capture_avoidance_tests.rs"]
mod capture_avoidance_tests;
