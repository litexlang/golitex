use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{
    ExistFact, ExistOrAndChainAtomicFact, Fact, ForallFact, ForallFactWithIff, NotForallFact,
    PlainExistFact,
};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::runtime::Runtime;

use super::super::capture;
use super::super::error::InstError;
use super::super::param;

impl Runtime {
    pub(crate) fn inst_fact_rec(
        &mut self,
        fact: &Fact,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Fact, InstError> {
        match fact {
            Fact::AtomicFact(a) => Ok(Fact::AtomicFact(
                self.inst_atomic_fact_rec(a, param_to_arg_map, fresh, binder_renames)?,
            )),
            Fact::AndFact(a) => {
                let mut facts = Vec::with_capacity(a.facts.len());
                for f in &a.facts {
                    facts.push(self.inst_atomic_fact_rec(f, param_to_arg_map, fresh, binder_renames)?);
                }
                Ok(Fact::AndFact(crate::new_pipeline::ast::fact::AndFact {
                    fact_id: self.ids.allocate_fact_id(),
                    facts,
                    line_file: a.line_file.clone(),
                }))
            }
            Fact::ChainFact(c) => {
                let mut objs = Vec::with_capacity(c.objs.len());
                for o in &c.objs {
                    objs.push(self.inst_obj_rec(o, param_to_arg_map, fresh, binder_renames)?);
                }
                Ok(Fact::ChainFact(crate::new_pipeline::ast::fact::ChainFact {
                    fact_id: self.ids.allocate_fact_id(),
                    objs,
                    prop_names: c.prop_names.clone(),
                    line_file: c.line_file.clone(),
                }))
            }
            Fact::OrFact(o) => {
                let mut facts = Vec::with_capacity(o.facts.len());
                for f in &o.facts {
                    facts.push(self.inst_and_chain_atomic(f, param_to_arg_map, fresh, binder_renames)?);
                }
                Ok(Fact::OrFact(crate::new_pipeline::ast::fact::OrFact {
                    fact_id: self.ids.allocate_fact_id(),
                    facts,
                    line_file: o.line_file.clone(),
                }))
            }
            Fact::ExistFact(e) => Ok(Fact::ExistFact(self.inst_exist_fact(
                e,
                param_to_arg_map,
                fresh,
                binder_renames,
            )?)),
            Fact::ForallFact(f) => Ok(Fact::ForallFact(self.inst_forall_fact(
                f,
                param_to_arg_map,
                fresh,
                binder_renames,
            )?)),
            Fact::ForallFactWithIff(f) => Ok(Fact::ForallFactWithIff(
                self.inst_forall_fact_with_iff(f, param_to_arg_map, fresh, binder_renames)?,
            )),
            Fact::NotForall(f) => Ok(Fact::NotForall(self.inst_not_forall_fact(
                f,
                param_to_arg_map,
                fresh,
                binder_renames,
            )?)),
        }
    }

    fn inst_plain_exist_fact_contents(
        &mut self,
        plain: &PlainExistFact,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<PlainExistFact, InstError> {
        let typed_parameters = self.inst_typed_parameter_list(
            &plain.typed_parameters,
            param_to_arg_map,
            fresh,
            binder_renames,
        )?;
        let facts = self.inst_qf_facts_rec(&plain.facts, param_to_arg_map, fresh, binder_renames)?;
        Ok(PlainExistFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters,
            facts,
            line_file: plain.line_file.clone(),
        })
    }

    fn inst_plain_exist_fact(
        &mut self,
        plain: &PlainExistFact,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<PlainExistFact, InstError> {
        let names = param::typed_param_names(&plain.typed_parameters);
        let binders = capture::prepare_binders(&names, param_to_arg_map, fresh);
        let (shadowed, new_renames) =
            capture::shadowed_subst_and_renames(param_to_arg_map, binder_renames, &binders);
        self.inst_plain_exist_fact_contents(plain, &shadowed, fresh, &new_renames)
    }

    fn inst_exist_fact(
        &mut self,
        exist: &ExistFact,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<ExistFact, InstError> {
        match exist {
            ExistFact::PlainExistFact(p) => Ok(ExistFact::PlainExistFact(self.inst_plain_exist_fact(
                p,
                param_to_arg_map,
                fresh,
                binder_renames,
            )?)),
            ExistFact::ExistUniqueFact(p) => Ok(ExistFact::ExistUniqueFact(self.inst_plain_exist_fact(
                p,
                param_to_arg_map,
                fresh,
                binder_renames,
            )?)),
            ExistFact::NotExistFact(p) => Ok(ExistFact::NotExistFact(self.inst_plain_exist_fact(
                p,
                param_to_arg_map,
                fresh,
                binder_renames,
            )?)),
        }
    }

    fn inst_forall_fact_contents(
        &mut self,
        forall: &ForallFact,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<ForallFact, InstError> {
        let typed_parameters = self.inst_typed_parameter_list(
            &forall.typed_parameters,
            param_to_arg_map,
            fresh,
            binder_renames,
        )?;
        let mut dom_facts = Vec::with_capacity(forall.dom_facts.len());
        for dom in &forall.dom_facts {
            dom_facts.push(self.inst_fact_rec(dom, param_to_arg_map, fresh, binder_renames)?);
        }
        let mut then_facts = Vec::with_capacity(forall.then_facts.len());
        for then in &forall.then_facts {
            then_facts.push(self.inst_exist_or_and_chain_atomic(
                then,
                param_to_arg_map,
                fresh,
                binder_renames,
            )?);
        }
        Ok(ForallFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters,
            dom_facts,
            then_facts,
            line_file: forall.line_file.clone(),
        })
    }

    fn inst_forall_fact(
        &mut self,
        forall: &ForallFact,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<ForallFact, InstError> {
        let names = param::typed_param_names(&forall.typed_parameters);
        let binders = capture::prepare_binders(&names, param_to_arg_map, fresh);
        let (shadowed, new_renames) =
            capture::shadowed_subst_and_renames(param_to_arg_map, binder_renames, &binders);
        self.inst_forall_fact_contents(forall, &shadowed, fresh, &new_renames)
    }

    fn inst_forall_fact_with_iff(
        &mut self,
        f: &ForallFactWithIff,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<ForallFactWithIff, InstError> {
        let names = param::typed_param_names(&f.forall_fact.typed_parameters);
        let binders = capture::prepare_binders(&names, param_to_arg_map, fresh);
        let (shadowed, new_renames) =
            capture::shadowed_subst_and_renames(param_to_arg_map, binder_renames, &binders);
        let forall_fact = self.inst_forall_fact_contents(&f.forall_fact, &shadowed, fresh, &new_renames)?;
        let mut iff_facts = Vec::with_capacity(f.iff_facts.len());
        for iff in &f.iff_facts {
            iff_facts.push(self.inst_exist_or_and_chain_atomic(
                iff,
                &shadowed,
                fresh,
                &new_renames,
            )?);
        }
        Ok(ForallFactWithIff {
            fact_id: self.ids.allocate_fact_id(),
            forall_fact,
            iff_facts,
            line_file: f.line_file.clone(),
        })
    }

    fn inst_not_forall_fact(
        &mut self,
        f: &NotForallFact,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<NotForallFact, InstError> {
        Ok(NotForallFact {
            fact_id: self.ids.allocate_fact_id(),
            forall_fact: self.inst_forall_fact(&f.forall_fact, param_to_arg_map, fresh, binder_renames)?,
        })
    }

    fn inst_exist_or_and_chain_atomic(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<ExistOrAndChainAtomicFact, InstError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(a) => Ok(ExistOrAndChainAtomicFact::AtomicFact(
                self.inst_atomic_fact_rec(a, param_to_arg_map, fresh, binder_renames)?,
            )),
            ExistOrAndChainAtomicFact::AndFact(a) => {
                let mut facts = Vec::with_capacity(a.facts.len());
                for f in &a.facts {
                    facts.push(self.inst_atomic_fact_rec(f, param_to_arg_map, fresh, binder_renames)?);
                }
                Ok(ExistOrAndChainAtomicFact::AndFact(
                    crate::new_pipeline::ast::fact::AndFact {
                        fact_id: self.ids.allocate_fact_id(),
                        facts,
                        line_file: a.line_file.clone(),
                    },
                ))
            }
            ExistOrAndChainAtomicFact::ChainFact(c) => {
                let mut objs = Vec::with_capacity(c.objs.len());
                for o in &c.objs {
                    objs.push(self.inst_obj_rec(o, param_to_arg_map, fresh, binder_renames)?);
                }
                Ok(ExistOrAndChainAtomicFact::ChainFact(
                    crate::new_pipeline::ast::fact::ChainFact {
                        fact_id: self.ids.allocate_fact_id(),
                        objs,
                        prop_names: c.prop_names.clone(),
                        line_file: c.line_file.clone(),
                    },
                ))
            }
            ExistOrAndChainAtomicFact::OrFact(o) => {
                let mut facts = Vec::with_capacity(o.facts.len());
                for f in &o.facts {
                    facts.push(self.inst_and_chain_atomic(f, param_to_arg_map, fresh, binder_renames)?);
                }
                Ok(ExistOrAndChainAtomicFact::OrFact(
                    crate::new_pipeline::ast::fact::OrFact {
                        fact_id: self.ids.allocate_fact_id(),
                        facts,
                        line_file: o.line_file.clone(),
                    },
                ))
            }
            ExistOrAndChainAtomicFact::ExistFact(e) => Ok(ExistOrAndChainAtomicFact::ExistFact(
                self.inst_exist_fact(e, param_to_arg_map, fresh, binder_renames)?,
            )),
        }
    }
}
