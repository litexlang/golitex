use crate::prelude::*;

impl Runtime {
    pub fn equal_literally(&self, left: &Obj, right: &Obj) -> bool {
        match left {
            Obj::Atom(AtomObj::Identifier(a)) => match right {
                Obj::Atom(AtomObj::Identifier(b)) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Atom(AtomObj::IdentifierWithMod(a)) => match right {
                Obj::Atom(AtomObj::IdentifierWithMod(b)) => {
                    if a.mod_name == b.mod_name {
                        a.to_string() == b.to_string()
                    } else {
                        match (
                            self.module_manager
                                .borrow()
                                .module_name_and_path_map
                                .get(&a.mod_name),
                            self.module_manager
                                .borrow()
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
            Obj::MatrixAdd(a) => match right {
                Obj::MatrixAdd(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::MatrixSub(a) => match right {
                Obj::MatrixSub(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::MatrixMul(a) => match right {
                Obj::MatrixMul(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::MatrixScalarMul(a) => match right {
                Obj::MatrixScalarMul(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::MatrixPow(a) => match right {
                Obj::MatrixPow(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Abs(a) => match right {
                Obj::Abs(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Sqrt(a) => match right {
                Obj::Sqrt(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Log(a) => match right {
                Obj::Log(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Max(a) => match right {
                Obj::Max(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Min(a) => match right {
                Obj::Min(b) => a.to_string() == b.to_string(),
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
            Obj::FnSet(a) => match right {
                Obj::FnSet(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::AnonymousFn(a) => match right {
                Obj::AnonymousFn(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::StandardSet(StandardSet::NPos) => match right {
                Obj::StandardSet(StandardSet::NPos) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::N) => match right {
                Obj::StandardSet(StandardSet::N) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::Q) => match right {
                Obj::StandardSet(StandardSet::Q) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::Z) => match right {
                Obj::StandardSet(StandardSet::Z) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::R) => match right {
                Obj::StandardSet(StandardSet::R) => true,
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
            Obj::Sum(a) => match right {
                Obj::Sum(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Product(a) => match right {
                Obj::Product(b) => a.to_string() == b.to_string(),
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
            Obj::FiniteSeqSet(a) => match right {
                Obj::FiniteSeqSet(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::SeqSet(a) => match right {
                Obj::SeqSet(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::FiniteSeqListObj(a) => match right {
                Obj::FiniteSeqListObj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::MatrixSet(a) => match right {
                Obj::MatrixSet(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::MatrixListObj(a) => match right {
                Obj::MatrixListObj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::PowerSet(a) => match right {
                Obj::PowerSet(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::ObjAtIndex(a) => match right {
                Obj::ObjAtIndex(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::StandardSet(StandardSet::QPos) => match right {
                Obj::StandardSet(StandardSet::QPos) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::RPos) => match right {
                Obj::StandardSet(StandardSet::RPos) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::QNeg) => match right {
                Obj::StandardSet(StandardSet::QNeg) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::ZNeg) => match right {
                Obj::StandardSet(StandardSet::ZNeg) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::RNeg) => match right {
                Obj::StandardSet(StandardSet::RNeg) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::QNz) => match right {
                Obj::StandardSet(StandardSet::QNz) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::ZNz) => match right {
                Obj::StandardSet(StandardSet::ZNz) => true,
                _ => false,
            },
            Obj::StandardSet(StandardSet::RNz) => match right {
                Obj::StandardSet(StandardSet::RNz) => true,
                _ => false,
            },
            Obj::StructObj(a) => match right {
                Obj::StructObj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::ObjAsStructInstanceWithFieldAccess(a) => match right {
                Obj::ObjAsStructInstanceWithFieldAccess(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::InstantiatedTemplateObj(a) => match right {
                Obj::InstantiatedTemplateObj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::IntervalObj(a) => match right {
                Obj::IntervalObj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::OneSideInfinityIntervalObj(a) => match right {
                Obj::OneSideInfinityIntervalObj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            // Parsing-time free params: compare [`fmt::Display`] (`~tag` + spine), not only `.name`.
            Obj::Atom(AtomObj::Forall(a)) => {
                matches!(right, Obj::Atom(AtomObj::Forall(b)) if a.to_string() == b.to_string())
            }
            Obj::Atom(AtomObj::Def(a)) => {
                matches!(right, Obj::Atom(AtomObj::Def(b)) if a.to_string() == b.to_string())
            }
            Obj::Atom(AtomObj::Exist(a)) => {
                matches!(right, Obj::Atom(AtomObj::Exist(b)) if a.to_string() == b.to_string())
            }
            Obj::Atom(AtomObj::SetBuilder(a)) => {
                matches!(right, Obj::Atom(AtomObj::SetBuilder(b)) if a.to_string() == b.to_string())
            }
            Obj::Atom(AtomObj::FnSet(a)) => {
                matches!(right, Obj::Atom(AtomObj::FnSet(b)) if a.to_string() == b.to_string())
            }
            Obj::Atom(AtomObj::Induc(a)) => {
                matches!(right, Obj::Atom(AtomObj::Induc(b)) if a.to_string() == b.to_string())
            }
            Obj::Atom(AtomObj::DefAlgo(a)) => {
                matches!(right, Obj::Atom(AtomObj::DefAlgo(b)) if a.to_string() == b.to_string())
            }
            Obj::Atom(AtomObj::DefStructField(a)) => {
                matches!(right, Obj::Atom(AtomObj::DefStructField(b)) if a.to_string() == b.to_string())
            }
        }
    }
}
