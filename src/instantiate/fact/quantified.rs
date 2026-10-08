use std::collections::HashMap;

use crate::runtime::runtime_ids::IdentifierId;

use crate::ast::fact::{
    ExistOrAndChainAtomicFact, ExistShapedFact, Fact, ForallFact, ForallFactWithIff, NotForallFact,
    PlainExistFact,
};
use crate::ast::obj::Obj;
use crate::runtime::Runtime;

use super::super::capture;
use super::super::error::InstError;
use super::super::param;

impl Runtime {
    pub(crate) fn inst_fact_rec(
        &mut self,
        fact: &Fact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<Fact, InstError> {
        match fact {
            Fact::AtomicFact(a) => Ok(Fact::AtomicFact(
                self.inst_atomic_fact_rec(a, param_to_arg_map)?,
            )),
            Fact::AndFact(a) => {
                let mut facts = Vec::with_capacity(a.facts.len());
                for f in &a.facts {
                    facts.push(self.inst_atomic_fact_rec(f, param_to_arg_map)?);
                }
                Ok(Fact::AndFact(crate::ast::fact::AndFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    facts,
                    line_file: a.line_file.clone(),
                }))
            }
            Fact::ChainFact(c) => {
                let mut objs = Vec::with_capacity(c.objs.len());
                for o in &c.objs {
                    objs.push(self.inst_obj_rec(o, param_to_arg_map)?);
                }
                Ok(Fact::ChainFact(crate::ast::fact::ChainFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    objs,
                    prop_names: c.prop_names.clone(),
                    line_file: c.line_file.clone(),
                }))
            }
            Fact::OrFact(o) => {
                let mut facts = Vec::with_capacity(o.facts.len());
                for f in &o.facts {
                    facts.push(self.inst_and_chain_atomic(f, param_to_arg_map)?);
                }
                Ok(Fact::OrFact(crate::ast::fact::OrFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    facts,
                    line_file: o.line_file.clone(),
                }))
            }
            Fact::ExistFact(_e) | Fact::ExistUniqueFact(_e) | Fact::NotExistFact(_e) => {
                let family = match fact {
                    Fact::ExistFact(p) => ExistShapedFact::Exist(p.clone()),
                    Fact::ExistUniqueFact(p) => ExistShapedFact::ExistUnique(p.clone()),
                    Fact::NotExistFact(p) => ExistShapedFact::NotExist(p.clone()),
                    _ => unreachable!(),
                };
                let inst = self.inst_exist_fact(&family, param_to_arg_map)?;
                Ok(crate::ast::fact::exist_shaped_fact_to_fact(&inst))
            }
            Fact::ForallFact(f) => Ok(Fact::ForallFact(
                self.inst_forall_fact(f, param_to_arg_map)?,
            )),
            Fact::ForallFactWithIff(f) => Ok(Fact::ForallFactWithIff(
                self.inst_forall_fact_with_iff(f, param_to_arg_map)?,
            )),
            Fact::NotForall(f) => Ok(Fact::NotForall(
                self.inst_not_forall_fact(f, param_to_arg_map)?,
            )),
        }
    }

    fn inst_plain_exist_fact_contents(
        &mut self,
        plain: &PlainExistFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<PlainExistFact, InstError> {
        let typed_parameters =
            self.inst_typed_parameter_list(&plain.typed_parameters, param_to_arg_map)?;
        let facts = self.inst_qf_facts_rec(&plain.facts, param_to_arg_map)?;
        Ok(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters,
            facts,
            line_file: plain.line_file.clone(),
        })
    }

    fn inst_plain_exist_fact(
        &mut self,
        plain: &PlainExistFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<PlainExistFact, InstError> {
        let ids = param::typed_param_ids(&plain.typed_parameters);
        let shadowed = capture::shadow_binder_ids(param_to_arg_map, &ids);
        self.inst_plain_exist_fact_contents(plain, &shadowed)
    }

    fn inst_exist_fact(
        &mut self,
        exist: &ExistShapedFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<ExistShapedFact, InstError> {
        match exist {
            ExistShapedFact::Exist(p) => Ok(ExistShapedFact::Exist(
                self.inst_plain_exist_fact(p, param_to_arg_map)?,
            )),
            ExistShapedFact::ExistUnique(p) => Ok(ExistShapedFact::ExistUnique(
                self.inst_plain_exist_fact(p, param_to_arg_map)?,
            )),
            ExistShapedFact::NotExist(p) => Ok(ExistShapedFact::NotExist(
                self.inst_plain_exist_fact(p, param_to_arg_map)?,
            )),
        }
    }

    fn inst_forall_fact_contents(
        &mut self,
        forall: &ForallFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<ForallFact, InstError> {
        let typed_parameters =
            self.inst_typed_parameter_list(&forall.typed_parameters, param_to_arg_map)?;
        let mut dom_facts = Vec::with_capacity(forall.dom_facts.len());
        for dom in &forall.dom_facts {
            dom_facts.push(self.inst_fact_rec(dom, param_to_arg_map)?);
        }
        let mut then_facts = Vec::with_capacity(forall.then_facts.len());
        for then in &forall.then_facts {
            then_facts.push(self.inst_exist_or_and_chain_atomic(then, param_to_arg_map)?);
        }
        Ok(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters,
            dom_facts,
            then_facts,
            line_file: forall.line_file.clone(),
        })
    }

    fn inst_forall_fact(
        &mut self,
        forall: &ForallFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<ForallFact, InstError> {
        let ids = param::typed_param_ids(&forall.typed_parameters);
        let shadowed = capture::shadow_binder_ids(param_to_arg_map, &ids);
        self.inst_forall_fact_contents(forall, &shadowed)
    }

    fn inst_forall_fact_with_iff(
        &mut self,
        f: &ForallFactWithIff,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<ForallFactWithIff, InstError> {
        let ids = param::typed_param_ids(&f.forall_fact.typed_parameters);
        let shadowed = capture::shadow_binder_ids(param_to_arg_map, &ids);
        let forall_fact = self.inst_forall_fact_contents(&f.forall_fact, &shadowed)?;
        let mut iff_facts = Vec::with_capacity(f.iff_facts.len());
        for iff in &f.iff_facts {
            iff_facts.push(self.inst_exist_or_and_chain_atomic(iff, &shadowed)?);
        }
        Ok(ForallFactWithIff {
            fact_id: self.global_ids.allocate_fact_id(),
            forall_fact,
            iff_facts,
            line_file: f.line_file.clone(),
        })
    }

    fn inst_not_forall_fact(
        &mut self,
        f: &NotForallFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<NotForallFact, InstError> {
        let ids = param::typed_param_ids(&f.typed_parameters);
        let shadowed = capture::shadow_binder_ids(param_to_arg_map, &ids);
        let typed_parameters = self.inst_typed_parameter_list(&f.typed_parameters, &shadowed)?;
        let mut dom_facts = Vec::with_capacity(f.dom_facts.len());
        for dom in &f.dom_facts {
            dom_facts.push(self.inst_quantifier_free_fact_rec(dom, &shadowed)?);
        }
        let mut then_facts = Vec::with_capacity(f.then_facts.len());
        for then in &f.then_facts {
            then_facts.push(self.inst_quantifier_free_fact_rec(then, &shadowed)?);
        }
        Ok(NotForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters,
            dom_facts,
            then_facts,
            line_file: f.line_file.clone(),
        })
    }

    fn inst_exist_or_and_chain_atomic(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<ExistOrAndChainAtomicFact, InstError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(a) => Ok(ExistOrAndChainAtomicFact::AtomicFact(
                self.inst_atomic_fact_rec(a, param_to_arg_map)?,
            )),
            ExistOrAndChainAtomicFact::AndFact(a) => {
                let mut facts = Vec::with_capacity(a.facts.len());
                for f in &a.facts {
                    facts.push(self.inst_atomic_fact_rec(f, param_to_arg_map)?);
                }
                Ok(ExistOrAndChainAtomicFact::AndFact(
                    crate::ast::fact::AndFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        facts,
                        line_file: a.line_file.clone(),
                    },
                ))
            }
            ExistOrAndChainAtomicFact::ChainFact(c) => {
                let mut objs = Vec::with_capacity(c.objs.len());
                for o in &c.objs {
                    objs.push(self.inst_obj_rec(o, param_to_arg_map)?);
                }
                Ok(ExistOrAndChainAtomicFact::ChainFact(
                    crate::ast::fact::ChainFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        objs,
                        prop_names: c.prop_names.clone(),
                        line_file: c.line_file.clone(),
                    },
                ))
            }
            ExistOrAndChainAtomicFact::OrFact(o) => {
                let mut facts = Vec::with_capacity(o.facts.len());
                for f in &o.facts {
                    facts.push(self.inst_and_chain_atomic(f, param_to_arg_map)?);
                }
                Ok(ExistOrAndChainAtomicFact::OrFact(
                    crate::ast::fact::OrFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        facts,
                        line_file: o.line_file.clone(),
                    },
                ))
            }
            ExistOrAndChainAtomicFact::ExistFact(e) => Ok(ExistOrAndChainAtomicFact::ExistFact(
                self.inst_plain_exist_fact(e, param_to_arg_map)?,
            )),
            ExistOrAndChainAtomicFact::ExistUniqueFact(e) => {
                Ok(ExistOrAndChainAtomicFact::ExistUniqueFact(
                    self.inst_plain_exist_fact(e, param_to_arg_map)?,
                ))
            }
            ExistOrAndChainAtomicFact::NotExistFact(e) => {
                Ok(ExistOrAndChainAtomicFact::NotExistFact(
                    self.inst_plain_exist_fact(e, param_to_arg_map)?,
                ))
            }
        }
    }
}
