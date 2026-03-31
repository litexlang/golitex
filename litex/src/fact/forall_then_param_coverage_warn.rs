use crate::prelude::*;
use std::collections::HashSet;

fn insert_param_type_names_for_coverage(
    param_type: &ParamType,
    name_binders: &HashSet<String>,
    collected_names: &mut HashSet<String>,
) {
    match param_type {
        ParamType::Obj(obj) => {
            insert_obj_identifier_names_for_coverage(obj, name_binders, collected_names);
        }
        ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {}
        ParamType::InstantiatedStruct(instantiated_struct) => {
            for param_obj in instantiated_struct.params.iter() {
                insert_obj_identifier_names_for_coverage(param_obj, name_binders, collected_names);
            }
        }
    }
}

fn insert_atom_identifier_names_for_coverage(
    atom: &Atom,
    name_binders: &HashSet<String>,
    collected_names: &mut HashSet<String>,
) {
    match atom {
        Atom::Identifier(identifier) => {
            if !name_binders.contains(&identifier.name) {
                collected_names.insert(identifier.name.clone());
            }
        }
        Atom::IdentifierWithMod(_) => {}
        Atom::FieldAccess(field_access) => {
            if !name_binders.contains(&field_access.name) {
                collected_names.insert(field_access.name.clone());
            }
        }
        Atom::FieldAccessWithMod(_) => {}
    }
}

fn insert_obj_identifier_names_for_coverage(
    obj: &Obj,
    name_binders: &HashSet<String>,
    collected_names: &mut HashSet<String>,
) {
    match obj {
        Obj::Identifier(identifier) => {
            if !name_binders.contains(&identifier.name) {
                collected_names.insert(identifier.name.clone());
            }
        }
        Obj::IdentifierWithMod(_) => {}
        Obj::FieldAccess(field_access) => {
            if !name_binders.contains(&field_access.name) {
                collected_names.insert(field_access.name.clone());
            }
        }
        Obj::FieldAccessWithMod(_) => {}
        Obj::FnObj(fn_obj) => {
            insert_atom_identifier_names_for_coverage(
                fn_obj.head.as_ref(),
                name_binders,
                collected_names,
            );
            for group in fn_obj.body.iter() {
                for boxed_obj in group.iter() {
                    insert_obj_identifier_names_for_coverage(
                        boxed_obj.as_ref(),
                        name_binders,
                        collected_names,
                    );
                }
            }
        }
        Obj::Number(_) | Obj::StandardSet(_) => {}
        Obj::Add(binary) => {
            insert_obj_identifier_names_for_coverage(
                binary.left.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                binary.right.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Sub(binary) => {
            insert_obj_identifier_names_for_coverage(
                binary.left.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                binary.right.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Mul(binary) => {
            insert_obj_identifier_names_for_coverage(
                binary.left.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                binary.right.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Div(binary) => {
            insert_obj_identifier_names_for_coverage(
                binary.left.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                binary.right.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Mod(binary) => {
            insert_obj_identifier_names_for_coverage(
                binary.left.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                binary.right.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Pow(binary) => {
            insert_obj_identifier_names_for_coverage(
                binary.base.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                binary.exponent.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Union(binary) => {
            insert_obj_identifier_names_for_coverage(
                binary.left.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                binary.right.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Intersect(binary) => {
            insert_obj_identifier_names_for_coverage(
                binary.left.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                binary.right.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::SetMinus(binary) => {
            insert_obj_identifier_names_for_coverage(
                binary.left.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                binary.right.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::SetDiff(binary) => {
            insert_obj_identifier_names_for_coverage(
                binary.left.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                binary.right.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Cup(unary) => {
            insert_obj_identifier_names_for_coverage(
                unary.left.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Cap(unary) => {
            insert_obj_identifier_names_for_coverage(
                unary.left.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::PowerSet(unary) => {
            insert_obj_identifier_names_for_coverage(
                unary.set.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::ListSet(list_set) => {
            for boxed_obj in list_set.list.iter() {
                insert_obj_identifier_names_for_coverage(
                    boxed_obj.as_ref(),
                    name_binders,
                    collected_names,
                );
            }
        }
        Obj::SetBuilder(set_builder) => {
            insert_obj_identifier_names_for_coverage(
                set_builder.param_set.as_ref(),
                name_binders,
                collected_names,
            );
            let mut inner_binders = name_binders.clone();
            inner_binders.insert(set_builder.param.clone());
            for inner_fact in set_builder.facts.iter() {
                insert_or_and_chain_atomic_fact_names_for_coverage(
                    inner_fact,
                    &inner_binders,
                    collected_names,
                );
            }
        }
        Obj::FnSetWithoutParams(fn_set) => {
            for boxed_obj in fn_set.param_sets.iter() {
                insert_obj_identifier_names_for_coverage(
                    boxed_obj.as_ref(),
                    name_binders,
                    collected_names,
                );
            }
            insert_obj_identifier_names_for_coverage(
                fn_set.ret_set.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::FnSetWithParams(fn_set) => {
            let mut sequential_binders = name_binders.clone();
            for param_def_with_set in fn_set.params_def_with_set.iter() {
                insert_obj_identifier_names_for_coverage(
                    &param_def_with_set.1,
                    &sequential_binders,
                    collected_names,
                );
                for param_name in param_def_with_set.0.iter() {
                    sequential_binders.insert(param_name.clone());
                }
            }
            for dom_fact in fn_set.dom_facts.iter() {
                insert_or_and_chain_atomic_fact_names_for_coverage(
                    dom_fact,
                    &sequential_binders,
                    collected_names,
                );
            }
            insert_obj_identifier_names_for_coverage(
                fn_set.ret_set.as_ref(),
                &sequential_binders,
                collected_names,
            );
        }
        Obj::Cart(cart) => {
            for boxed_arg in cart.args.iter() {
                insert_obj_identifier_names_for_coverage(
                    boxed_arg.as_ref(),
                    name_binders,
                    collected_names,
                );
            }
        }
        Obj::CartDim(cart_dim) => {
            insert_obj_identifier_names_for_coverage(
                cart_dim.set.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Proj(proj) => {
            insert_obj_identifier_names_for_coverage(
                proj.set.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                proj.dim.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::TupleDim(tuple_dim) => {
            insert_obj_identifier_names_for_coverage(
                tuple_dim.arg.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Tuple(tuple_obj) => {
            for boxed_arg in tuple_obj.args.iter() {
                insert_obj_identifier_names_for_coverage(
                    boxed_arg.as_ref(),
                    name_binders,
                    collected_names,
                );
            }
        }
        Obj::Count(count) => {
            insert_obj_identifier_names_for_coverage(
                count.set.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Range(range) => {
            insert_obj_identifier_names_for_coverage(
                range.start.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                range.end.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::ClosedRange(closed_range) => {
            insert_obj_identifier_names_for_coverage(
                closed_range.start.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                closed_range.end.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::Choose(choose) => {
            insert_obj_identifier_names_for_coverage(
                choose.set.as_ref(),
                name_binders,
                collected_names,
            );
        }
        Obj::ObjAtIndex(obj_at_index) => {
            insert_obj_identifier_names_for_coverage(
                obj_at_index.obj.as_ref(),
                name_binders,
                collected_names,
            );
            insert_obj_identifier_names_for_coverage(
                obj_at_index.index.as_ref(),
                name_binders,
                collected_names,
            );
        }
    }
}

fn insert_atomic_fact_identifier_names_for_coverage(
    atomic_fact: &AtomicFact,
    name_binders: &HashSet<String>,
    collected_names: &mut HashSet<String>,
) {
    match atomic_fact {
        AtomicFact::NormalAtomicFact(fact) => {
            for body_obj in fact.body.iter() {
                insert_obj_identifier_names_for_coverage(body_obj, name_binders, collected_names);
            }
        }
        AtomicFact::NotNormalAtomicFact(fact) => {
            for body_obj in fact.body.iter() {
                insert_obj_identifier_names_for_coverage(body_obj, name_binders, collected_names);
            }
        }
        AtomicFact::EqualFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::LessFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::GreaterFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::LessEqualFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::GreaterEqualFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::NotEqualFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::NotLessFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::NotGreaterFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::NotLessEqualFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::NotGreaterEqualFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::IsSetFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::NotIsSetFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::IsNonemptySetFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::NotIsNonemptySetFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::IsFiniteSetFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::NotIsFiniteSetFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::InFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.element, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::NotInFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.element, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::IsCartFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::NotIsCartFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::IsTupleFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::NotIsTupleFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.set, name_binders, collected_names);
        }
        AtomicFact::SubsetFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::SupersetFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::NotSubsetFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::NotSupersetFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.left, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(&fact.right, name_binders, collected_names);
        }
        AtomicFact::RestrictFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.obj, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(
                &fact.obj_can_restrict_to_fn_set,
                name_binders,
                collected_names,
            );
        }
        AtomicFact::NotRestrictFact(fact) => {
            insert_obj_identifier_names_for_coverage(&fact.obj, name_binders, collected_names);
            insert_obj_identifier_names_for_coverage(
                &fact.obj_cannot_restrict_to_fn_set,
                name_binders,
                collected_names,
            );
        }
    }
}

fn insert_and_chain_atomic_fact_names_for_coverage(
    fact: &AndChainAtomicFact,
    name_binders: &HashSet<String>,
    collected_names: &mut HashSet<String>,
) {
    match fact {
        AndChainAtomicFact::AtomicFact(atomic_fact) => {
            insert_atomic_fact_identifier_names_for_coverage(
                atomic_fact,
                name_binders,
                collected_names,
            );
        }
        AndChainAtomicFact::AndFact(and_fact) => {
            for inner_atomic in and_fact.facts.iter() {
                insert_atomic_fact_identifier_names_for_coverage(
                    inner_atomic,
                    name_binders,
                    collected_names,
                );
            }
        }
        AndChainAtomicFact::ChainFact(chain_fact) => {
            for chain_obj in chain_fact.objs.iter() {
                insert_obj_identifier_names_for_coverage(chain_obj, name_binders, collected_names);
            }
        }
    }
}

fn insert_or_and_chain_atomic_fact_names_for_coverage(
    fact: &OrAndChainAtomicFact,
    name_binders: &HashSet<String>,
    collected_names: &mut HashSet<String>,
) {
    match fact {
        OrAndChainAtomicFact::AtomicFact(atomic_fact) => {
            insert_atomic_fact_identifier_names_for_coverage(
                atomic_fact,
                name_binders,
                collected_names,
            );
        }
        OrAndChainAtomicFact::AndFact(and_fact) => {
            for inner_atomic in and_fact.facts.iter() {
                insert_atomic_fact_identifier_names_for_coverage(
                    inner_atomic,
                    name_binders,
                    collected_names,
                );
            }
        }
        OrAndChainAtomicFact::ChainFact(chain_fact) => {
            for chain_obj in chain_fact.objs.iter() {
                insert_obj_identifier_names_for_coverage(chain_obj, name_binders, collected_names);
            }
        }
        OrAndChainAtomicFact::OrFact(or_fact) => {
            for branch in or_fact.facts.iter() {
                insert_and_chain_atomic_fact_names_for_coverage(
                    branch,
                    name_binders,
                    collected_names,
                );
            }
        }
    }
}

fn insert_exist_fact_identifier_names_for_coverage(
    exist_fact: &ExistFact,
    outer_name_binders: &HashSet<String>,
    collected_names: &mut HashSet<String>,
) {
    let mut sequential_binders = outer_name_binders.clone();
    for param_def_with_type in exist_fact.params_def_with_type.iter() {
        insert_param_type_names_for_coverage(
            &param_def_with_type.1,
            &sequential_binders,
            collected_names,
        );
        for param_name in param_def_with_type.0.iter() {
            sequential_binders.insert(param_name.clone());
        }
    }
    for inner_fact in exist_fact.facts.iter() {
        insert_or_and_chain_atomic_fact_names_for_coverage(
            inner_fact,
            &sequential_binders,
            collected_names,
        );
    }
}

fn insert_exist_or_and_chain_atomic_fact_names_for_coverage(
    fact: &ExistOrAndChainAtomicFact,
    name_binders: &HashSet<String>,
    collected_names: &mut HashSet<String>,
) {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
            insert_atomic_fact_identifier_names_for_coverage(
                atomic_fact,
                name_binders,
                collected_names,
            );
        }
        ExistOrAndChainAtomicFact::AndFact(and_fact) => {
            for inner_atomic in and_fact.facts.iter() {
                insert_atomic_fact_identifier_names_for_coverage(
                    inner_atomic,
                    name_binders,
                    collected_names,
                );
            }
        }
        ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
            for chain_obj in chain_fact.objs.iter() {
                insert_obj_identifier_names_for_coverage(chain_obj, name_binders, collected_names);
            }
        }
        ExistOrAndChainAtomicFact::OrFact(or_fact) => {
            for branch in or_fact.facts.iter() {
                insert_and_chain_atomic_fact_names_for_coverage(
                    branch,
                    name_binders,
                    collected_names,
                );
            }
        }
        ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
            insert_exist_fact_identifier_names_for_coverage(
                exist_fact,
                name_binders,
                collected_names,
            );
        }
    }
}

impl ForallFact {
    pub fn error_messages_if_forall_param_missing_in_some_then_clause(&self) -> Vec<String> {
        let forall_param_names =
            ParamDefWithParamType::collect_param_names(&self.params_def_with_type);
        if forall_param_names.is_empty() {
            return Vec::new();
        }
        let empty_binders = HashSet::new();
        let line_file = self.line_file;
        let mut error_messages = Vec::new();
        let mut then_index: usize = 0;
        while then_index < self.then_facts.len() {
            let then_fact = &self.then_facts[then_index];
            let mut identifier_names_in_then = HashSet::new();
            insert_exist_or_and_chain_atomic_fact_names_for_coverage(
                then_fact,
                &empty_binders,
                &mut identifier_names_in_then,
            );
            let mut missing_param_names = Vec::new();
            for param_name in forall_param_names.iter() {
                if !identifier_names_in_then.contains(param_name) {
                    missing_param_names.push(param_name.clone());
                }
            }
            if !missing_param_names.is_empty() {
                let missing_list = missing_param_names.join(", ");
                error_messages.push(format!(
                    "forall at {:?}: then-clause #{} does not mention forall parameter(s) {{{}}}",
                    line_file, then_index, missing_list,
                ));
            }
            then_index += 1;
        }
        error_messages
    }
}

impl ForallFactWithIff {
    pub fn error_messages_if_forall_param_missing_in_then_or_iff_clause(&self) -> Vec<String> {
        let mut error_messages = self
            .forall_fact
            .error_messages_if_forall_param_missing_in_some_then_clause();
        let forall_param_names =
            ParamDefWithParamType::collect_param_names(&self.forall_fact.params_def_with_type);
        if forall_param_names.is_empty() {
            return error_messages;
        }
        let empty_binders = HashSet::new();
        let line_file = self.line_file;
        let mut iff_index: usize = 0;
        while iff_index < self.iff_facts.len() {
            let iff_fact = &self.iff_facts[iff_index];
            let mut identifier_names_in_iff = HashSet::new();
            insert_exist_or_and_chain_atomic_fact_names_for_coverage(
                iff_fact,
                &empty_binders,
                &mut identifier_names_in_iff,
            );
            let mut missing_param_names = Vec::new();
            for param_name in forall_param_names.iter() {
                if !identifier_names_in_iff.contains(param_name) {
                    missing_param_names.push(param_name.clone());
                }
            }
            if !missing_param_names.is_empty() {
                let missing_list = missing_param_names.join(", ");
                error_messages.push(format!(
                    "forall-with-iff at {:?}: iff-clause #{} does not mention forall parameter(s) {{{}}}",
                    line_file,
                    iff_index,
                    missing_list,
                ));
            }
            iff_index += 1;
        }
        error_messages
    }
}
