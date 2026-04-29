use crate::prelude::*;
use std::collections::HashMap;

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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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

    pub fn inst_or_and_chain_atomic_fact(
        &self,
        fact: &OrAndChainAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: ParamObjType,
        inst_lf: Option<&LineFile>,
    ) -> Result<OrAndChainAtomicFact, RuntimeError> {
        Ok(match fact {
            OrAndChainAtomicFact::AtomicFact(atomic_fact) => OrAndChainAtomicFact::AtomicFact(
                self.inst_atomic_fact(atomic_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            OrAndChainAtomicFact::AndFact(and_fact) => OrAndChainAtomicFact::AndFact(
                self.inst_and_fact(and_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            OrAndChainAtomicFact::ChainFact(chain_fact) => OrAndChainAtomicFact::ChainFact(
                self.inst_chain_fact(chain_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
            OrAndChainAtomicFact::OrFact(or_fact) => OrAndChainAtomicFact::OrFact(
                self.inst_or_fact(or_fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
            ),
        })
    }

    pub fn inst_and_chain_atomic_fact(
        &self,
        fact: &AndChainAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
            AtomicFact::RestrictFact(fact) => AtomicFact::RestrictFact(self.inst_restrict_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?),
            AtomicFact::NotRestrictFact(fact) => AtomicFact::NotRestrictFact(
                self.inst_not_restrict_fact(fact, param_to_arg_map, to_inst_param_type, inst_lf)?,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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

    pub fn inst_exist_fact(
        &self,
        exist_fact: &ExistFactEnum,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: ParamObjType,
        inst_lf: Option<&LineFile>,
    ) -> Result<ExistFactEnum, RuntimeError> {
        let mut groups = Vec::with_capacity(exist_fact.params_def_with_type().groups.len());
        for param_def_with_type in exist_fact.params_def_with_type().groups.iter() {
            groups.push(ParamGroupWithParamType::new(
                param_def_with_type.params.clone(),
                self.inst_param_type(
                    &param_def_with_type.param_type,
                    param_to_arg_map,
                    to_inst_param_type,
                )?,
            ));
        }
        let params_def_with_type = ParamDefWithType::new(groups);
        let mut facts = Vec::with_capacity(exist_fact.facts().len());
        for fact in exist_fact.facts().iter() {
            facts.push(self.inst_or_and_chain_atomic_fact(
                fact,
                param_to_arg_map,
                to_inst_param_type,
                inst_lf,
            )?);
        }
        let body = ExistFactBody::new(
            params_def_with_type,
            facts,
            Self::line_file_after_inst(&exist_fact.body().line_file, inst_lf),
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
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
        to_inst_param_type: ParamObjType,
        inst_lf: Option<&LineFile>,
    ) -> Result<ForallFact, RuntimeError> {
        let mut groups = Vec::with_capacity(forall_fact.params_def_with_type.groups.len());
        for param_def_with_type in forall_fact.params_def_with_type.groups.iter() {
            groups.push(ParamGroupWithParamType::new(
                param_def_with_type.params.clone(),
                self.inst_param_type(
                    &param_def_with_type.param_type,
                    param_to_arg_map,
                    to_inst_param_type,
                )?,
            ));
        }
        let params_def_with_type = ParamDefWithType::new(groups);
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
        Ok(ForallFact::new(
            params_def_with_type,
            dom_facts,
            then_facts,
            Self::line_file_after_inst(&forall_fact.line_file, inst_lf),
        )?)
    }

    pub fn inst_forall_fact_with_iff(
        &self,
        forall_fact_with_iff: &ForallFactWithIff,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: ParamObjType,
        inst_lf: Option<&LineFile>,
    ) -> Result<ForallFactWithIff, RuntimeError> {
        let forall_fact = self.inst_forall_fact(
            &forall_fact_with_iff.forall_fact,
            param_to_arg_map,
            to_inst_param_type,
            inst_lf,
        )?;
        let mut iff_facts = Vec::with_capacity(forall_fact_with_iff.iff_facts.len());
        for iff_fact in forall_fact_with_iff.iff_facts.iter() {
            iff_facts.push(self.inst_exist_or_and_chain_atomic_fact(
                iff_fact,
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

    pub fn inst_restrict_fact(
        &self,
        restrict_fact: &RestrictFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: ParamObjType,
        inst_lf: Option<&LineFile>,
    ) -> Result<RestrictFact, RuntimeError> {
        Ok(RestrictFact::new(
            self.inst_obj(&restrict_fact.obj, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(
                &restrict_fact.obj_can_restrict_to_fn_set,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&restrict_fact.line_file, inst_lf),
        ))
    }

    pub fn inst_not_restrict_fact(
        &self,
        not_restrict_fact: &NotRestrictFact,
        param_to_arg_map: &HashMap<String, Obj>,
        to_inst_param_type: ParamObjType,
        inst_lf: Option<&LineFile>,
    ) -> Result<NotRestrictFact, RuntimeError> {
        Ok(NotRestrictFact::new(
            self.inst_obj(&not_restrict_fact.obj, param_to_arg_map, to_inst_param_type)?,
            self.inst_obj(
                &not_restrict_fact.obj_cannot_restrict_to_fn_set,
                param_to_arg_map,
                to_inst_param_type,
            )?,
            Self::line_file_after_inst(&not_restrict_fact.line_file, inst_lf),
        ))
    }
}
