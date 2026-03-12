use std::collections::HashMap;
use super::atom::{FieldAccess, FieldAccessWithMod, Identifier, IdentifierWithMod};
use super::obj::{
    Add, Cap, Cart, CartDim, Choose, ClosedRange, Count, Cup, Dim, Div, FnObj, FnSetWithDom,
    FnSetWithoutDom, InstStructObj, Intersect, ListSet, Mod, Mul, NObj, NPosObj, Number, Obj,
    ObjAtIndex, Pow, PowerSet, Proj, QNeg, QNz, QObj, QPos, Range, RNeg, RNz, RObj, RPos, SetBuilder,
    SetDiff, SetMinus, Sub, Tuple, Union, Val, ZNeg, ZNz,     ZObj, ZPos,
};

fn not_implemented(param_to_arg_map: &HashMap<String, Obj>) -> ! {
    _ = param_to_arg_map;
    panic!("instantiate not yet implemented for this type")
}

impl Identifier {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl IdentifierWithMod {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl FieldAccess {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl FieldAccessWithMod {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl FnObj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Number {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Add {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Sub {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Mul {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Div {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Mod {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Pow {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Union {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Intersect {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl SetMinus {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl SetDiff {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Cup {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Cap {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl ListSet {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl SetBuilder {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl FnSetWithoutDom {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl FnSetWithDom {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl NPosObj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl NObj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl QObj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl ZObj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl RObj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl InstStructObj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Cart {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl CartDim {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Proj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Dim {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Tuple {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Count {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Range {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl ClosedRange {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Val {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl PowerSet {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl Choose {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl ObjAtIndex {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl QPos {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl ZPos {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl RPos {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl QNeg {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl ZNeg {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl RNeg {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl QNz {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl ZNz {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}

impl RNz {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        not_implemented(param_to_arg_map)
    }
}
