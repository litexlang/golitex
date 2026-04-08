use crate::common::defaults::DEFAULT_MANGLED_FN_PARAM_PREFIX;
use crate::common::is_valid_litex_name::is_valid_litex_name;
use crate::common::mangled_fn_param::mangled_fn_param_binding;
use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    /// 在 [`mangled_fn_param_binding`] 之后：把用户符形参表 + 用户符 dom/ret 换成存储形参并 [`FnSet::new`]。
    pub(crate) fn fn_set_from_user_param_ast_after_binding(
        &self,
        params_def_with_user: Vec<ParamGroupWithSet>,
        new_param_names: &[String],
        param_arg_map: &HashMap<String, Obj>,
        dom_facts_user: Vec<OrAndChainAtomicFact>,
        ret_set_user: Obj,
    ) -> Result<FnSet, RuntimeError> {
        let mut flat_stored_idx: usize = 0;
        let new_def_with_set: Vec<ParamGroupWithSet> = params_def_with_user
            .iter()
            .map(|param_group| {
                let new_params: Vec<String> = param_group
                    .params
                    .iter()
                    .map(|_| {
                        let s = new_param_names[flat_stored_idx].clone();
                        flat_stored_idx += 1;
                        s
                    })
                    .collect();
                ParamGroupWithSet::new(new_params, param_group.set.clone())
            })
            .collect();
        let mut dom_facts = vec![];
        for d in dom_facts_user {
            dom_facts.push(self.inst_or_and_chain_atomic_fact(&d, param_arg_map)?);
        }
        let ret_set = self.inst_obj(&ret_set_user, param_arg_map)?;
        Ok(FnSet::new(new_def_with_set, dom_facts, ret_set))
    }

    /// 用户符 `fn` 形参 + dom/ret → 存储用 [`FnSet`]（`__` 形参）；不登记 parse 期 mangled 名。
    pub fn fn_set_for_storage_from_have_fn_clause(
        &self,
        clause: &HaveFnFnSetClause,
        line_file: LineFile,
    ) -> Result<FnSet, RuntimeError> {
        let names = ParamGroupWithSet::collect_param_names(&clause.params_def_with_set);
        for name in &names {
            if let Err(e) = is_valid_litex_name(name) {
                return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                    e,
                    line_file.clone(),
                    None,
                ));
            }
        }
        let (new_param_names, param_arg_map) =
            mangled_fn_param_binding(&names, DEFAULT_MANGLED_FN_PARAM_PREFIX);
        self.fn_set_from_user_param_ast_after_binding(
            clause.params_def_with_set.clone(),
            &new_param_names,
            &param_arg_map,
            clause.dom_facts.clone(),
            clause.ret_set.clone(),
        )
    }

    pub fn inst_fact(
        &self,
        fact: &Fact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<Fact, RuntimeError> {
        Ok(match fact {
            Fact::AtomicFact(atomic_fact) => {
                Fact::AtomicFact(self.inst_atomic_fact(atomic_fact, param_to_arg_map)?)
            }
            Fact::ExistFact(exist_fact) => {
                Fact::ExistFact(self.inst_exist_fact(exist_fact, param_to_arg_map)?)
            }
            Fact::OrFact(or_fact) => Fact::OrFact(self.inst_or_fact(or_fact, param_to_arg_map)?),
            Fact::AndFact(and_fact) => Fact::AndFact(self.inst_and_fact(and_fact, param_to_arg_map)?),
            Fact::ChainFact(chain_fact) => {
                Fact::ChainFact(self.inst_chain_fact(chain_fact, param_to_arg_map)?)
            }
            Fact::ForallFact(forall_fact) => {
                Fact::ForallFact(self.inst_forall_fact(forall_fact, param_to_arg_map)?)
            }
            Fact::ForallFactWithIff(forall_fact_with_iff) => Fact::ForallFactWithIff(
                self.inst_forall_fact_with_iff(forall_fact_with_iff, param_to_arg_map)?,
            ),
        })
    }

    pub fn inst_exist_or_and_chain_atomic_fact(
        &self,
        fact: &ExistOrAndChainAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<ExistOrAndChainAtomicFact, RuntimeError> {
        Ok(match fact {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                ExistOrAndChainAtomicFact::AtomicFact(
                    self.inst_atomic_fact(atomic_fact, param_to_arg_map)?,
                )
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => {
                ExistOrAndChainAtomicFact::AndFact(self.inst_and_fact(and_fact, param_to_arg_map)?)
            }
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => ExistOrAndChainAtomicFact::ChainFact(
                self.inst_chain_fact(chain_fact, param_to_arg_map)?,
            ),
            ExistOrAndChainAtomicFact::OrFact(or_fact) => {
                ExistOrAndChainAtomicFact::OrFact(self.inst_or_fact(or_fact, param_to_arg_map)?)
            }
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
                ExistOrAndChainAtomicFact::ExistFact(self.inst_exist_fact(exist_fact, param_to_arg_map)?)
            }
        })
    }

    pub fn inst_or_and_chain_atomic_fact(
        &self,
        fact: &OrAndChainAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<OrAndChainAtomicFact, RuntimeError> {
        Ok(match fact {
            OrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                OrAndChainAtomicFact::AtomicFact(self.inst_atomic_fact(atomic_fact, param_to_arg_map)?)
            }
            OrAndChainAtomicFact::AndFact(and_fact) => {
                OrAndChainAtomicFact::AndFact(self.inst_and_fact(and_fact, param_to_arg_map)?)
            }
            OrAndChainAtomicFact::ChainFact(chain_fact) => {
                OrAndChainAtomicFact::ChainFact(self.inst_chain_fact(chain_fact, param_to_arg_map)?)
            }
            OrAndChainAtomicFact::OrFact(or_fact) => {
                OrAndChainAtomicFact::OrFact(self.inst_or_fact(or_fact, param_to_arg_map)?)
            }
        })
    }

    pub fn inst_and_chain_atomic_fact(
        &self,
        fact: &AndChainAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<AndChainAtomicFact, RuntimeError> {
        Ok(match fact {
            AndChainAtomicFact::AtomicFact(atomic_fact) => {
                AndChainAtomicFact::AtomicFact(self.inst_atomic_fact(atomic_fact, param_to_arg_map)?)
            }
            AndChainAtomicFact::AndFact(and_fact) => {
                AndChainAtomicFact::AndFact(self.inst_and_fact(and_fact, param_to_arg_map)?)
            }
            AndChainAtomicFact::ChainFact(chain_fact) => {
                AndChainAtomicFact::ChainFact(self.inst_chain_fact(chain_fact, param_to_arg_map)?)
            }
        })
    }

    pub fn inst_atomic_fact(
        &self,
        atomic_fact: &AtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<AtomicFact, RuntimeError> {
        Ok(match atomic_fact {
            AtomicFact::NormalAtomicFact(fact) => {
                AtomicFact::NormalAtomicFact(self.inst_normal_atomic_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::EqualFact(fact) => {
                AtomicFact::EqualFact(self.inst_equal_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::LessFact(fact) => AtomicFact::LessFact(self.inst_less_fact(fact, param_to_arg_map)?),
            AtomicFact::GreaterFact(fact) => {
                AtomicFact::GreaterFact(self.inst_greater_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::LessEqualFact(fact) => {
                AtomicFact::LessEqualFact(self.inst_less_equal_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::GreaterEqualFact(fact) => {
                AtomicFact::GreaterEqualFact(self.inst_greater_equal_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::IsSetFact(fact) => {
                AtomicFact::IsSetFact(self.inst_is_set_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::IsNonemptySetFact(fact) => {
                AtomicFact::IsNonemptySetFact(self.inst_is_nonempty_set_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::IsFiniteSetFact(fact) => {
                AtomicFact::IsFiniteSetFact(self.inst_is_finite_set_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::InFact(fact) => AtomicFact::InFact(self.inst_in_fact(fact, param_to_arg_map)?),
            AtomicFact::IsCartFact(fact) => {
                AtomicFact::IsCartFact(self.inst_is_cart_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::IsTupleFact(fact) => {
                AtomicFact::IsTupleFact(self.inst_is_tuple_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::SubsetFact(fact) => {
                AtomicFact::SubsetFact(self.inst_subset_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::SupersetFact(fact) => {
                AtomicFact::SupersetFact(self.inst_superset_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotNormalAtomicFact(fact) => {
                AtomicFact::NotNormalAtomicFact(self.inst_not_normal_atomic_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotEqualFact(fact) => {
                AtomicFact::NotEqualFact(self.inst_not_equal_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotLessFact(fact) => {
                AtomicFact::NotLessFact(self.inst_not_less_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotGreaterFact(fact) => {
                AtomicFact::NotGreaterFact(self.inst_not_greater_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotLessEqualFact(fact) => {
                AtomicFact::NotLessEqualFact(self.inst_not_less_equal_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotGreaterEqualFact(fact) => {
                AtomicFact::NotGreaterEqualFact(self.inst_not_greater_equal_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotIsSetFact(fact) => {
                AtomicFact::NotIsSetFact(self.inst_not_is_set_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotIsNonemptySetFact(fact) => {
                AtomicFact::NotIsNonemptySetFact(self.inst_not_is_nonempty_set_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotIsFiniteSetFact(fact) => {
                AtomicFact::NotIsFiniteSetFact(self.inst_not_is_finite_set_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotInFact(fact) => {
                AtomicFact::NotInFact(self.inst_not_in_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotIsCartFact(fact) => {
                AtomicFact::NotIsCartFact(self.inst_not_is_cart_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotIsTupleFact(fact) => {
                AtomicFact::NotIsTupleFact(self.inst_not_is_tuple_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotSubsetFact(fact) => {
                AtomicFact::NotSubsetFact(self.inst_not_subset_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotSupersetFact(fact) => {
                AtomicFact::NotSupersetFact(self.inst_not_superset_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::RestrictFact(fact) => {
                AtomicFact::RestrictFact(self.inst_restrict_fact(fact, param_to_arg_map)?)
            }
            AtomicFact::NotRestrictFact(fact) => {
                AtomicFact::NotRestrictFact(self.inst_not_restrict_fact(fact, param_to_arg_map)?)
            }
        })
    }

    pub fn inst_normal_atomic_fact(
        &self,
        normal_atomic_fact: &NormalAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NormalAtomicFact, RuntimeError> {
        let mut body = Vec::with_capacity(normal_atomic_fact.body.len());
        for obj in normal_atomic_fact.body.iter() {
            body.push(self.inst_obj(obj, param_to_arg_map)?);
        }
        Ok(NormalAtomicFact {
            predicate: normal_atomic_fact.predicate.clone(),
            body,
            line_file: normal_atomic_fact.line_file.clone(),
        })
    }

    pub fn inst_equal_fact(
        &self,
        equal_fact: &EqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<EqualFact, RuntimeError> {
        Ok(EqualFact {
            left: self.inst_obj(&equal_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&equal_fact.right, param_to_arg_map)?,
            line_file: equal_fact.line_file.clone(),
        })
    }

    pub fn inst_less_fact(
        &self,
        less_fact: &LessFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<LessFact, RuntimeError> {
        Ok(LessFact {
            left: self.inst_obj(&less_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&less_fact.right, param_to_arg_map)?,
            line_file: less_fact.line_file.clone(),
        })
    }

    pub fn inst_greater_fact(
        &self,
        greater_fact: &GreaterFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<GreaterFact, RuntimeError> {
        Ok(GreaterFact {
            left: self.inst_obj(&greater_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&greater_fact.right, param_to_arg_map)?,
            line_file: greater_fact.line_file.clone(),
        })
    }

    pub fn inst_less_equal_fact(
        &self,
        less_equal_fact: &LessEqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<LessEqualFact, RuntimeError> {
        Ok(LessEqualFact {
            left: self.inst_obj(&less_equal_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&less_equal_fact.right, param_to_arg_map)?,
            line_file: less_equal_fact.line_file.clone(),
        })
    }

    pub fn inst_greater_equal_fact(
        &self,
        greater_equal_fact: &GreaterEqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<GreaterEqualFact, RuntimeError> {
        Ok(GreaterEqualFact {
            left: self.inst_obj(&greater_equal_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&greater_equal_fact.right, param_to_arg_map)?,
            line_file: greater_equal_fact.line_file.clone(),
        })
    }

    pub fn inst_is_set_fact(
        &self,
        is_set_fact: &IsSetFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<IsSetFact, RuntimeError> {
        Ok(IsSetFact {
            set: self.inst_obj(&is_set_fact.set, param_to_arg_map)?,
            line_file: is_set_fact.line_file.clone(),
        })
    }

    pub fn inst_is_nonempty_set_fact(
        &self,
        is_nonempty_set_fact: &IsNonemptySetFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<IsNonemptySetFact, RuntimeError> {
        Ok(IsNonemptySetFact {
            set: self.inst_obj(&is_nonempty_set_fact.set, param_to_arg_map)?,
            line_file: is_nonempty_set_fact.line_file.clone(),
        })
    }

    pub fn inst_is_finite_set_fact(
        &self,
        is_finite_set_fact: &IsFiniteSetFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<IsFiniteSetFact, RuntimeError> {
        Ok(IsFiniteSetFact {
            set: self.inst_obj(&is_finite_set_fact.set, param_to_arg_map)?,
            line_file: is_finite_set_fact.line_file.clone(),
        })
    }

    pub fn inst_in_fact(
        &self,
        in_fact: &InFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<InFact, RuntimeError> {
        Ok(InFact {
            element: self.inst_obj(&in_fact.element, param_to_arg_map)?,
            set: self.inst_obj(&in_fact.set, param_to_arg_map)?,
            line_file: in_fact.line_file.clone(),
        })
    }

    pub fn inst_is_cart_fact(
        &self,
        is_cart_fact: &IsCartFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<IsCartFact, RuntimeError> {
        Ok(IsCartFact {
            set: self.inst_obj(&is_cart_fact.set, param_to_arg_map)?,
            line_file: is_cart_fact.line_file.clone(),
        })
    }

    pub fn inst_is_tuple_fact(
        &self,
        is_tuple_fact: &IsTupleFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<IsTupleFact, RuntimeError> {
        Ok(IsTupleFact {
            set: self.inst_obj(&is_tuple_fact.set, param_to_arg_map)?,
            line_file: is_tuple_fact.line_file.clone(),
        })
    }

    pub fn inst_subset_fact(
        &self,
        subset_fact: &SubsetFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<SubsetFact, RuntimeError> {
        Ok(SubsetFact {
            left: self.inst_obj(&subset_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&subset_fact.right, param_to_arg_map)?,
            line_file: subset_fact.line_file.clone(),
        })
    }

    pub fn inst_superset_fact(
        &self,
        superset_fact: &SupersetFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<SupersetFact, RuntimeError> {
        Ok(SupersetFact {
            left: self.inst_obj(&superset_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&superset_fact.right, param_to_arg_map)?,
            line_file: superset_fact.line_file.clone(),
        })
    }

    pub fn inst_not_normal_atomic_fact(
        &self,
        not_normal_atomic_fact: &NotNormalAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotNormalAtomicFact, RuntimeError> {
        let mut body = Vec::with_capacity(not_normal_atomic_fact.body.len());
        for obj in not_normal_atomic_fact.body.iter() {
            body.push(self.inst_obj(obj, param_to_arg_map)?);
        }
        Ok(NotNormalAtomicFact {
            predicate: not_normal_atomic_fact.predicate.clone(),
            body,
            line_file: not_normal_atomic_fact.line_file.clone(),
        })
    }

    pub fn inst_not_equal_fact(
        &self,
        not_equal_fact: &NotEqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotEqualFact, RuntimeError> {
        Ok(NotEqualFact {
            left: self.inst_obj(&not_equal_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&not_equal_fact.right, param_to_arg_map)?,
            line_file: not_equal_fact.line_file.clone(),
        })
    }

    pub fn inst_not_less_fact(
        &self,
        not_less_fact: &NotLessFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotLessFact, RuntimeError> {
        Ok(NotLessFact {
            left: self.inst_obj(&not_less_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&not_less_fact.right, param_to_arg_map)?,
            line_file: not_less_fact.line_file.clone(),
        })
    }

    pub fn inst_not_greater_fact(
        &self,
        not_greater_fact: &NotGreaterFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotGreaterFact, RuntimeError> {
        Ok(NotGreaterFact {
            left: self.inst_obj(&not_greater_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&not_greater_fact.right, param_to_arg_map)?,
            line_file: not_greater_fact.line_file.clone(),
        })
    }

    pub fn inst_not_less_equal_fact(
        &self,
        not_less_equal_fact: &NotLessEqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotLessEqualFact, RuntimeError> {
        Ok(NotLessEqualFact {
            left: self.inst_obj(&not_less_equal_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&not_less_equal_fact.right, param_to_arg_map)?,
            line_file: not_less_equal_fact.line_file.clone(),
        })
    }

    pub fn inst_not_greater_equal_fact(
        &self,
        not_greater_equal_fact: &NotGreaterEqualFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotGreaterEqualFact, RuntimeError> {
        Ok(NotGreaterEqualFact {
            left: self.inst_obj(&not_greater_equal_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&not_greater_equal_fact.right, param_to_arg_map)?,
            line_file: not_greater_equal_fact.line_file.clone(),
        })
    }

    pub fn inst_not_is_set_fact(
        &self,
        not_is_set_fact: &NotIsSetFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotIsSetFact, RuntimeError> {
        Ok(NotIsSetFact {
            set: self.inst_obj(&not_is_set_fact.set, param_to_arg_map)?,
            line_file: not_is_set_fact.line_file.clone(),
        })
    }

    pub fn inst_not_is_nonempty_set_fact(
        &self,
        not_is_nonempty_set_fact: &NotIsNonemptySetFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotIsNonemptySetFact, RuntimeError> {
        Ok(NotIsNonemptySetFact {
            set: self.inst_obj(&not_is_nonempty_set_fact.set, param_to_arg_map)?,
            line_file: not_is_nonempty_set_fact.line_file.clone(),
        })
    }

    pub fn inst_not_is_finite_set_fact(
        &self,
        not_is_finite_set_fact: &NotIsFiniteSetFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotIsFiniteSetFact, RuntimeError> {
        Ok(NotIsFiniteSetFact {
            set: self.inst_obj(&not_is_finite_set_fact.set, param_to_arg_map)?,
            line_file: not_is_finite_set_fact.line_file.clone(),
        })
    }

    pub fn inst_not_in_fact(
        &self,
        not_in_fact: &NotInFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotInFact, RuntimeError> {
        Ok(NotInFact {
            element: self.inst_obj(&not_in_fact.element, param_to_arg_map)?,
            set: self.inst_obj(&not_in_fact.set, param_to_arg_map)?,
            line_file: not_in_fact.line_file.clone(),
        })
    }

    pub fn inst_not_is_cart_fact(
        &self,
        not_is_cart_fact: &NotIsCartFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotIsCartFact, RuntimeError> {
        Ok(NotIsCartFact {
            set: self.inst_obj(&not_is_cart_fact.set, param_to_arg_map)?,
            line_file: not_is_cart_fact.line_file.clone(),
        })
    }

    pub fn inst_not_is_tuple_fact(
        &self,
        not_is_tuple_fact: &NotIsTupleFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotIsTupleFact, RuntimeError> {
        Ok(NotIsTupleFact {
            set: self.inst_obj(&not_is_tuple_fact.set, param_to_arg_map)?,
            line_file: not_is_tuple_fact.line_file.clone(),
        })
    }

    pub fn inst_not_subset_fact(
        &self,
        not_subset_fact: &NotSubsetFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotSubsetFact, RuntimeError> {
        Ok(NotSubsetFact {
            left: self.inst_obj(&not_subset_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&not_subset_fact.right, param_to_arg_map)?,
            line_file: not_subset_fact.line_file.clone(),
        })
    }

    pub fn inst_not_superset_fact(
        &self,
        not_superset_fact: &NotSupersetFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotSupersetFact, RuntimeError> {
        Ok(NotSupersetFact {
            left: self.inst_obj(&not_superset_fact.left, param_to_arg_map)?,
            right: self.inst_obj(&not_superset_fact.right, param_to_arg_map)?,
            line_file: not_superset_fact.line_file.clone(),
        })
    }

    pub fn inst_exist_fact(
        &self,
        exist_fact: &ExistFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<ExistFact, RuntimeError> {
        let mut params_def_with_type = Vec::with_capacity(exist_fact.params_def_with_type.len());
        for param_def_with_type in exist_fact.params_def_with_type.iter() {
            params_def_with_type.push(ParamGroupWithParamType::new(
                param_def_with_type.params.clone(),
                self.inst_param_type(&param_def_with_type.param_type, param_to_arg_map)?,
            ));
        }
        let mut facts = Vec::with_capacity(exist_fact.facts.len());
        for fact in exist_fact.facts.iter() {
            facts.push(self.inst_or_and_chain_atomic_fact(fact, param_to_arg_map)?);
        }
        Ok(ExistFact {
            params_def_with_type,
            facts,
            line_file: exist_fact.line_file.clone(),
        })
    }

    pub fn inst_or_fact(
        &self,
        or_fact: &OrFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<OrFact, RuntimeError> {
        let mut facts = Vec::with_capacity(or_fact.facts.len());
        for fact in or_fact.facts.iter() {
            facts.push(self.inst_and_chain_atomic_fact(fact, param_to_arg_map)?);
        }
        Ok(OrFact {
            facts,
            line_file: or_fact.line_file.clone(),
        })
    }

    pub fn inst_and_fact(
        &self,
        and_fact: &AndFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<AndFact, RuntimeError> {
        let mut facts = Vec::with_capacity(and_fact.facts.len());
        for fact in and_fact.facts.iter() {
            facts.push(self.inst_atomic_fact(fact, param_to_arg_map)?);
        }
        Ok(AndFact {
            facts,
            line_file: and_fact.line_file.clone(),
        })
    }

    pub fn inst_chain_fact(
        &self,
        chain_fact: &ChainFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<ChainFact, RuntimeError> {
        let mut objs = Vec::with_capacity(chain_fact.objs.len());
        for obj in chain_fact.objs.iter() {
            objs.push(self.inst_obj(obj, param_to_arg_map)?);
        }
        Ok(ChainFact {
            objs,
            prop_names: chain_fact.prop_names.clone(),
            line_file: chain_fact.line_file.clone(),
        })
    }

    pub fn inst_forall_fact(
        &self,
        forall_fact: &ForallFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<ForallFact, RuntimeError> {
        let mut params_def_with_type = Vec::with_capacity(forall_fact.params_def_with_type.len());
        for param_def_with_type in forall_fact.params_def_with_type.iter() {
            params_def_with_type.push(ParamGroupWithParamType::new(
                param_def_with_type.params.clone(),
                self.inst_param_type(&param_def_with_type.param_type, param_to_arg_map)?,
            ));
        }
        let mut dom_facts = Vec::with_capacity(forall_fact.dom_facts.len());
        for dom_fact in forall_fact.dom_facts.iter() {
            dom_facts.push(self.inst_exist_or_and_chain_atomic_fact(dom_fact, param_to_arg_map)?);
        }
        let mut then_facts = Vec::with_capacity(forall_fact.then_facts.len());
        for then_fact in forall_fact.then_facts.iter() {
            then_facts.push(self.inst_exist_or_and_chain_atomic_fact(then_fact, param_to_arg_map)?);
        }
        Ok(ForallFact {
            params_def_with_type,
            dom_facts,
            then_facts,
            line_file: forall_fact.line_file.clone(),
        })
    }

    pub fn inst_forall_fact_with_iff(
        &self,
        forall_fact_with_iff: &ForallFactWithIff,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<ForallFactWithIff, RuntimeError> {
        let forall_fact = self.inst_forall_fact(&forall_fact_with_iff.forall_fact, param_to_arg_map)?;
        let mut iff_facts = Vec::with_capacity(forall_fact_with_iff.iff_facts.len());
        for iff_fact in forall_fact_with_iff.iff_facts.iter() {
            iff_facts.push(self.inst_exist_or_and_chain_atomic_fact(iff_fact, param_to_arg_map)?);
        }
        Ok(ForallFactWithIff {
            forall_fact,
            iff_facts,
            line_file: forall_fact_with_iff.line_file.clone(),
        })
    }

    pub fn inst_restrict_fact(
        &self,
        restrict_fact: &RestrictFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<RestrictFact, RuntimeError> {
        Ok(RestrictFact {
            obj: self.inst_obj(&restrict_fact.obj, param_to_arg_map)?,
            obj_can_restrict_to_fn_set: self
                .inst_obj(&restrict_fact.obj_can_restrict_to_fn_set, param_to_arg_map)?,
            line_file: restrict_fact.line_file.clone(),
        })
    }

    pub fn inst_not_restrict_fact(
        &self,
        not_restrict_fact: &NotRestrictFact,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<NotRestrictFact, RuntimeError> {
        Ok(NotRestrictFact {
            obj: self.inst_obj(&not_restrict_fact.obj, param_to_arg_map)?,
            obj_cannot_restrict_to_fn_set: self
                .inst_obj(&not_restrict_fact.obj_cannot_restrict_to_fn_set, param_to_arg_map)?,
            line_file: not_restrict_fact.line_file.clone(),
        })
    }
}
