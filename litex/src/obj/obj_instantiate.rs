use crate::prelude::*;
use std::collections::HashMap;

impl Obj {
    fn remove_param_names_from_param_to_arg_map(
        param_to_arg_map: &HashMap<String, Obj>,
        param_names: &Vec<String>,
    ) -> HashMap<String, Obj> {
        let mut filtered_param_to_arg_map = HashMap::new();
        for (param_name, arg) in param_to_arg_map.iter() {
            if !param_names.contains(param_name) {
                filtered_param_to_arg_map.insert(param_name.clone(), arg.clone());
            }
        }
        filtered_param_to_arg_map
    }
}

impl Identifier {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        match param_to_arg_map.get(&self.name) {
            Some(obj) => obj.clone(),
            None => Obj::Identifier(self.clone()),
        }
    }
}

impl IdentifierWithMod {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        _ = param_to_arg_map;
        Obj::IdentifierWithMod(self.clone())
    }
}

impl FieldAccess {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        match param_to_arg_map.get(&self.name) {
            Some(Obj::Identifier(identifier)) => Obj::FieldAccess(FieldAccess {
                name: identifier.name.clone(),
                fields: self.fields.clone(),
            }),
            Some(Obj::IdentifierWithMod(identifier_with_mod)) => {
                Obj::FieldAccessWithMod(FieldAccessWithMod {
                    mod_name: identifier_with_mod.mod_name.clone(),
                    name: identifier_with_mod.name.clone(),
                    fields: self.fields.clone(),
                })
            }
            Some(Obj::FieldAccess(existing_field_access)) => {
                let mut fields = existing_field_access.fields.clone();
                for field in self.fields.iter() {
                    fields.push(field.clone());
                }
                Obj::FieldAccess(FieldAccess {
                    name: existing_field_access.name.clone(),
                    fields,
                })
            }
            Some(Obj::FieldAccessWithMod(existing_field_access_with_mod)) => {
                let mut fields = existing_field_access_with_mod.fields.clone();
                for field in self.fields.iter() {
                    fields.push(field.clone());
                }
                Obj::FieldAccessWithMod(FieldAccessWithMod {
                    mod_name: existing_field_access_with_mod.mod_name.clone(),
                    name: existing_field_access_with_mod.name.clone(),
                    fields,
                })
            }
            _ => Obj::FieldAccess(self.clone()),
        }
    }
}

impl FieldAccessWithMod {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        _ = param_to_arg_map;
        Obj::FieldAccessWithMod(self.clone())
    }
}

impl Atom {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Atom {
        match self {
            Atom::Identifier(identifier) => match identifier.instantiate(param_to_arg_map) {
                Obj::Identifier(new_identifier) => Atom::Identifier(new_identifier),
                Obj::IdentifierWithMod(new_identifier_with_mod) => {
                    Atom::IdentifierWithMod(new_identifier_with_mod)
                }
                Obj::FieldAccess(new_field_access) => Atom::FieldAccess(new_field_access),
                Obj::FieldAccessWithMod(new_field_access_with_mod) => {
                    Atom::FieldAccessWithMod(new_field_access_with_mod)
                }
                _ => Atom::Identifier(identifier.clone()),
            },
            Atom::IdentifierWithMod(identifier_with_mod) => {
                Atom::IdentifierWithMod(identifier_with_mod.clone())
            }
            Atom::FieldAccess(field_access) => match field_access.instantiate(param_to_arg_map) {
                Obj::Identifier(new_identifier) => Atom::Identifier(new_identifier),
                Obj::IdentifierWithMod(new_identifier_with_mod) => {
                    Atom::IdentifierWithMod(new_identifier_with_mod)
                }
                Obj::FieldAccess(new_field_access) => Atom::FieldAccess(new_field_access),
                Obj::FieldAccessWithMod(new_field_access_with_mod) => {
                    Atom::FieldAccessWithMod(new_field_access_with_mod)
                }
                _ => Atom::FieldAccess(field_access.clone()),
            },
            Atom::FieldAccessWithMod(field_access_with_mod) => {
                Atom::FieldAccessWithMod(field_access_with_mod.clone())
            }
        }
    }
}

impl FnObj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let mut body = Vec::with_capacity(self.body.len());
        for obj_vec in self.body.iter() {
            let mut new_obj_vec = Vec::with_capacity(obj_vec.len());
            for obj in obj_vec.iter() {
                new_obj_vec.push(Box::new(obj.instantiate(param_to_arg_map)));
            }
            body.push(new_obj_vec);
        }
        Obj::FnObj(FnObj {
            head: Box::new(self.head.instantiate(param_to_arg_map)),
            body,
        })
    }
}

impl Number {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        _ = param_to_arg_map;
        Obj::Number(self.clone())
    }
}

impl Add {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let instantiated_left_obj = self.left.instantiate(param_to_arg_map);
        let instantiated_right_obj = self.right.instantiate(param_to_arg_map);
        Obj::Add(Add::new(instantiated_left_obj, instantiated_right_obj))
    }
}

impl Sub {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let instantiated_left_obj = self.left.instantiate(param_to_arg_map);
        let instantiated_right_obj = self.right.instantiate(param_to_arg_map);
        Obj::Sub(Sub::new(instantiated_left_obj, instantiated_right_obj))
    }
}

impl Mul {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let instantiated_left_obj = self.left.instantiate(param_to_arg_map);
        let instantiated_right_obj = self.right.instantiate(param_to_arg_map);
        Obj::Mul(Mul::new(instantiated_left_obj, instantiated_right_obj))
    }
}

impl Div {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::Div(Div {
            left: Box::new(self.left.instantiate(param_to_arg_map)),
            right: Box::new(self.right.instantiate(param_to_arg_map)),
        })
    }
}

impl Mod {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let instantiated_left_obj = self.left.instantiate(param_to_arg_map);
        let instantiated_right_obj = self.right.instantiate(param_to_arg_map);
        Obj::Mod(Mod::new(instantiated_left_obj, instantiated_right_obj))
    }
}

impl Pow {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let instantiated_base_obj = self.base.instantiate(param_to_arg_map);
        let instantiated_exponent_obj = self.exponent.instantiate(param_to_arg_map);
        Obj::Pow(Pow::new(instantiated_base_obj, instantiated_exponent_obj))
    }
}

impl Union {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::Union(Union {
            left: Box::new(self.left.instantiate(param_to_arg_map)),
            right: Box::new(self.right.instantiate(param_to_arg_map)),
        })
    }
}

impl Intersect {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::Intersect(Intersect {
            left: Box::new(self.left.instantiate(param_to_arg_map)),
            right: Box::new(self.right.instantiate(param_to_arg_map)),
        })
    }
}

impl SetMinus {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::SetMinus(SetMinus {
            left: Box::new(self.left.instantiate(param_to_arg_map)),
            right: Box::new(self.right.instantiate(param_to_arg_map)),
        })
    }
}

impl SetDiff {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::SetDiff(SetDiff {
            left: Box::new(self.left.instantiate(param_to_arg_map)),
            right: Box::new(self.right.instantiate(param_to_arg_map)),
        })
    }
}

impl Cup {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::Cup(Cup {
            left: Box::new(self.left.instantiate(param_to_arg_map)),
        })
    }
}

impl Cap {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::Cap(Cap {
            left: Box::new(self.left.instantiate(param_to_arg_map)),
        })
    }
}

impl ListSet {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let mut list = Vec::with_capacity(self.list.len());
        for obj in self.list.iter() {
            list.push(Box::new(obj.instantiate(param_to_arg_map)));
        }
        Obj::ListSet(ListSet { list })
    }
}

impl SetBuilder {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let param_names = vec![self.param.clone()];
        let filtered_param_to_arg_map =
            Obj::remove_param_names_from_param_to_arg_map(param_to_arg_map, &param_names);
        let mut facts = Vec::with_capacity(self.facts.len());
        for fact in self.facts.iter() {
            facts.push(fact.instantiate(&filtered_param_to_arg_map));
        }
        Obj::SetBuilder(SetBuilder {
            param: self.param.clone(),
            param_set: Box::new(self.param_set.instantiate(&filtered_param_to_arg_map)),
            facts,
        })
    }
}

impl FnSetWithoutParams {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let mut param_sets = Vec::with_capacity(self.param_sets.len());
        for param_set in self.param_sets.iter() {
            param_sets.push(Box::new(param_set.instantiate(param_to_arg_map)));
        }
        Obj::FnSetWithoutParams(FnSetWithoutParams {
            param_sets,
            ret_set: Box::new(self.ret_set.instantiate(param_to_arg_map)),
        })
    }
}

impl FnSetWithParams {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let param_names = ParamDefWithParamSet::collect_param_names(&self.params_def_with_set);
        let filtered_param_to_arg_map =
            Obj::remove_param_names_from_param_to_arg_map(param_to_arg_map, &param_names);
        let mut params_def_with_set = Vec::with_capacity(self.params_def_with_set.len());
        for param_def_with_set in self.params_def_with_set.iter() {
            params_def_with_set.push(ParamDefWithParamSet(
                param_def_with_set.0.clone(),
                param_def_with_set.1.instantiate(&filtered_param_to_arg_map),
            ));
        }
        let mut dom_facts = Vec::with_capacity(self.dom_facts.len());
        for dom_fact in self.dom_facts.iter() {
            dom_facts.push(dom_fact.instantiate(&filtered_param_to_arg_map));
        }
        Obj::FnSetWithParams(FnSetWithParams {
            params_def_with_set,
            dom_facts,
            ret_set: Box::new(self.ret_set.instantiate(&filtered_param_to_arg_map)),
        })
    }
}

impl InstStructObj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let mut args = Vec::with_capacity(self.args.len());
        for arg in self.args.iter() {
            args.push(Box::new(arg.instantiate(param_to_arg_map)));
        }
        Obj::InstSetStructObj(InstStructObj {
            struct_name: self.struct_name.clone(),
            args,
        })
    }
}

impl Cart {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let mut args = Vec::with_capacity(self.args.len());
        for arg in self.args.iter() {
            args.push(Box::new(arg.instantiate(param_to_arg_map)));
        }
        Obj::Cart(Cart { args })
    }
}

impl CartDim {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::CartDim(CartDim {
            set: Box::new(self.set.instantiate(param_to_arg_map)),
        })
    }
}

impl Proj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::Proj(Proj {
            set: Box::new(self.set.instantiate(param_to_arg_map)),
            dim: Box::new(self.dim.instantiate(param_to_arg_map)),
        })
    }
}

impl TupleDim {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::TupleDim(TupleDim {
            arg: Box::new(self.arg.instantiate(param_to_arg_map)),
        })
    }
}

impl Tuple {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        let mut elements = Vec::with_capacity(self.args.len());
        for element in self.args.iter() {
            elements.push(Box::new(element.instantiate(param_to_arg_map)));
        }
        Obj::Tuple(Tuple { args: elements })
    }
}

impl Count {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::Count(Count {
            set: Box::new(self.set.instantiate(param_to_arg_map)),
        })
    }
}

impl Range {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::Range(Range {
            start: Box::new(self.start.instantiate(param_to_arg_map)),
            end: Box::new(self.end.instantiate(param_to_arg_map)),
        })
    }
}

impl ClosedRange {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::ClosedRange(ClosedRange {
            start: Box::new(self.start.instantiate(param_to_arg_map)),
            end: Box::new(self.end.instantiate(param_to_arg_map)),
        })
    }
}

impl Val {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::Val(Val {
            value: Box::new(self.value.instantiate(param_to_arg_map)),
        })
    }
}

impl PowerSet {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::PowerSet(PowerSet {
            set: Box::new(self.set.instantiate(param_to_arg_map)),
        })
    }
}

impl Choose {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::Choose(Choose {
            set: Box::new(self.set.instantiate(param_to_arg_map)),
        })
    }
}

impl ObjAtIndex {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        Obj::ObjAtIndex(ObjAtIndex {
            obj: Box::new(self.obj.instantiate(param_to_arg_map)),
            index: Box::new(self.index.instantiate(param_to_arg_map)),
        })
    }
}

