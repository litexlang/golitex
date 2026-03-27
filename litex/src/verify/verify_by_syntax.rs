use crate::execute::Runtime;
use crate::obj::Obj;

impl Runtime {
    pub fn equal_literally(&self, left: &Obj, right: &Obj) -> bool {
        match left {
            Obj::Identifier(a) => match right {
                Obj::Identifier(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::IdentifierWithMod(a) => match right {
                Obj::IdentifierWithMod(b) => {
                    if a.mod_name == b.mod_name {
                        a.name == b.name
                    } else {
                        match (
                            self.module_manager
                                .module_name_and_path_map
                                .get(&a.mod_name),
                            self.module_manager
                                .module_name_and_path_map
                                .get(&b.mod_name),
                        ) {
                            (Some(p1), Some(p2)) => p1 == p2 && a.name == b.name,
                            _ => false,
                        }
                    }
                }
                _ => false,
            },
            Obj::FieldAccess(a) => match right {
                Obj::FieldAccess(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::FieldAccessWithMod(a) => match right {
                Obj::FieldAccessWithMod(b) => {
                    if a.mod_name == b.mod_name {
                        a.name == b.name
                            && a.fields.len() == b.fields.len()
                            && a.fields
                                .iter()
                                .zip(b.fields.iter())
                                .all(|(a_field, b_field)| {
                                    a_field.to_string() == b_field.to_string()
                                })
                    } else {
                        match (
                            self.module_manager
                                .module_name_and_path_map
                                .get(&a.mod_name),
                            self.module_manager
                                .module_name_and_path_map
                                .get(&b.mod_name),
                        ) {
                            (Some(p1), Some(p2)) => {
                                p1 == p2
                                    && a.name == b.name
                                    && a.fields.len() == b.fields.len()
                                    && a.fields.iter().zip(b.fields.iter()).all(
                                        |(a_field, b_field)| {
                                            a_field.to_string() == b_field.to_string()
                                        },
                                    )
                            }
                            _ => false,
                        }
                    }
                }
                _ => false,
            },
            Obj::FnObj(f) => match right {
                Obj::FnObj(g) => f.to_string() == g.to_string(),
                _ => false,
            },
            Obj::Number(n) => match right {
                Obj::Number(m) => n.to_string() == m.to_string(),
                _ => false,
            },
            Obj::Add(a) => match right {
                Obj::Add(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Sub(a) => match right {
                Obj::Sub(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Mul(a) => match right {
                Obj::Mul(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Div(a) => match right {
                Obj::Div(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Mod(a) => match right {
                Obj::Mod(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Pow(a) => match right {
                Obj::Pow(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Union(a) => match right {
                Obj::Union(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Intersect(a) => match right {
                Obj::Intersect(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::SetMinus(a) => match right {
                Obj::SetMinus(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::SetDiff(a) => match right {
                Obj::SetDiff(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Cup(a) => match right {
                Obj::Cup(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Cap(a) => match right {
                Obj::Cap(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::ListSet(a) => match right {
                Obj::ListSet(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::SetBuilder(a) => match right {
                Obj::SetBuilder(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::FnSetWithoutParams(a) => match right {
                Obj::FnSetWithoutParams(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::FnSetWithParams(a) => match right {
                Obj::FnSetWithParams(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::NPosObj(_) => match right {
                Obj::NPosObj(_) => true,
                _ => false,
            },
            Obj::NObj(_) => match right {
                Obj::NObj(_) => true,
                _ => false,
            },
            Obj::QObj(_) => match right {
                Obj::QObj(_) => true,
                _ => false,
            },
            Obj::ZObj(_) => match right {
                Obj::ZObj(_) => true,
                _ => false,
            },
            Obj::RObj(_) => match right {
                Obj::RObj(_) => true,
                _ => false,
            },
            Obj::InstSetStructObj(a) => match right {
                Obj::InstSetStructObj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Cart(a) => match right {
                Obj::Cart(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::CartDim(a) => match right {
                Obj::CartDim(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Proj(a) => match right {
                Obj::Proj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::TupleDim(a) => match right {
                Obj::TupleDim(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Tuple(a) => match right {
                Obj::Tuple(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Count(a) => match right {
                Obj::Count(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Range(a) => match right {
                Obj::Range(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::ClosedRange(a) => match right {
                Obj::ClosedRange(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Val(a) => match right {
                Obj::Val(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::PowerSet(a) => match right {
                Obj::PowerSet(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Choose(a) => match right {
                Obj::Choose(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::ObjAtIndex(a) => match right {
                Obj::ObjAtIndex(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::QPos(_) => match right {
                Obj::QPos(_) => true,
                _ => false,
            },
            Obj::RPos(_) => match right {
                Obj::RPos(_) => true,
                _ => false,
            },
            Obj::QNeg(_) => match right {
                Obj::QNeg(_) => true,
                _ => false,
            },
            Obj::ZNeg(_) => match right {
                Obj::ZNeg(_) => true,
                _ => false,
            },
            Obj::RNeg(_) => match right {
                Obj::RNeg(_) => true,
                _ => false,
            },
            Obj::QNz(_) => match right {
                Obj::QNz(_) => true,
                _ => false,
            },
            Obj::ZNz(_) => match right {
                Obj::ZNz(_) => true,
                _ => false,
            },
            Obj::RNz(_) => match right {
                Obj::RNz(_) => true,
                _ => false,
            },
        }
    }
}
