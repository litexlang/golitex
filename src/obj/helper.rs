use crate::prelude::*;

impl FnSetBody {
    pub(crate) fn contains_native_complex_builtin(&self) -> bool {
        self.params_def_with_set
            .iter()
            .any(|group| group.set_obj().contains_native_complex_builtin())
            || self.dom_facts.iter().any(|fact| {
                fact.get_args_from_fact_ref()
                    .into_iter()
                    .any(Obj::contains_native_complex_builtin)
            })
            || self.ret_set.contains_native_complex_builtin()
    }
}

impl AnonymousFn {
    pub(crate) fn contains_native_complex_builtin(&self) -> bool {
        self.body.contains_native_complex_builtin()
            || self.equal_to.contains_native_complex_builtin()
    }
}

impl Obj {
    /// Detect native complex syntax by stable builtin identity before a symbolic-only backend
    /// attempts to lower the object as a real-valued expression.
    pub(crate) fn contains_native_complex_builtin(&self) -> bool {
        match self {
            Obj::Atom(AtomObj::Identifier(identifier)) => identifier.is_builtin(I),
            Obj::Atom(_) | Obj::Number(_) => false,
            Obj::StandardSet(set) => matches!(set, StandardSet::C),
            Obj::FnObj(fn_obj) => {
                let native_head = match fn_obj.head.as_ref() {
                    FnObjHead::Identifier(identifier) => {
                        identifier.is_builtin(RE)
                            || identifier.is_builtin(IMG)
                            || identifier.is_builtin(C_ABS)
                    }
                    FnObjHead::AnonymousFnLiteral(function) => {
                        function.contains_native_complex_builtin()
                    }
                    FnObjHead::FiniteSeqListObj(list) => list
                        .objs
                        .iter()
                        .any(|obj| obj.contains_native_complex_builtin()),
                    FnObjHead::ObjAtIndex(index) => {
                        index.obj.contains_native_complex_builtin()
                            || index.index.contains_native_complex_builtin()
                    }
                    FnObjHead::ObjAsStructInstanceWithFieldAccess(access) => {
                        access
                            .struct_obj
                            .params
                            .iter()
                            .any(|obj| obj.contains_native_complex_builtin())
                            || access.obj.contains_native_complex_builtin()
                    }
                    FnObjHead::InstantiatedTemplateObj(template) => template
                        .args
                        .iter()
                        .any(|obj| obj.contains_native_complex_builtin()),
                    FnObjHead::MatrixOperator(matrix) => matrix.contains_native_complex_builtin(),
                    _ => false,
                };
                native_head
                    || fn_obj
                        .body
                        .iter()
                        .flatten()
                        .any(|arg| arg.contains_native_complex_builtin())
            }
            Obj::Add(binary) => {
                binary.left.contains_native_complex_builtin()
                    || binary.right.contains_native_complex_builtin()
            }
            Obj::Sub(binary) => {
                binary.left.contains_native_complex_builtin()
                    || binary.right.contains_native_complex_builtin()
            }
            Obj::Mul(binary) => {
                binary.left.contains_native_complex_builtin()
                    || binary.right.contains_native_complex_builtin()
            }
            Obj::Div(binary) => {
                binary.left.contains_native_complex_builtin()
                    || binary.right.contains_native_complex_builtin()
            }
            Obj::Mod(binary) => {
                binary.left.contains_native_complex_builtin()
                    || binary.right.contains_native_complex_builtin()
            }
            Obj::Pow(pow) => {
                pow.base.contains_native_complex_builtin()
                    || pow.exponent.contains_native_complex_builtin()
            }
            Obj::Abs(abs) => abs.arg.contains_native_complex_builtin(),
            Obj::Sqrt(sqrt) => sqrt.arg.contains_native_complex_builtin(),
            Obj::Log(log) => {
                log.base.contains_native_complex_builtin()
                    || log.arg.contains_native_complex_builtin()
            }
            Obj::Union(binary) => {
                binary.left.contains_native_complex_builtin()
                    || binary.right.contains_native_complex_builtin()
            }
            Obj::Intersect(binary) => {
                binary.left.contains_native_complex_builtin()
                    || binary.right.contains_native_complex_builtin()
            }
            Obj::SetMinus(binary) => {
                binary.left.contains_native_complex_builtin()
                    || binary.right.contains_native_complex_builtin()
            }
            Obj::SetDiff(binary) => {
                binary.left.contains_native_complex_builtin()
                    || binary.right.contains_native_complex_builtin()
            }
            Obj::BigUnion(union) => union.left.contains_native_complex_builtin(),
            Obj::BigIntersect(intersect) => intersect.left.contains_native_complex_builtin(),
            Obj::PowerSet(power_set) => power_set.set.contains_native_complex_builtin(),
            Obj::ListSet(list) => list
                .list
                .iter()
                .any(|obj| obj.contains_native_complex_builtin()),
            Obj::SetBuilder(builder) => {
                builder.param_set.contains_native_complex_builtin()
                    || builder.facts.iter().any(|fact| {
                        fact.get_args_from_fact_ref()
                            .into_iter()
                            .any(Obj::contains_native_complex_builtin)
                    })
            }
            Obj::FnSet(function) => function.body.contains_native_complex_builtin(),
            Obj::AnonymousFn(function) => function.contains_native_complex_builtin(),
            Obj::GeneralCart(cart) => {
                cart.index_set.contains_native_complex_builtin()
                    || cart.family_set.contains_native_complex_builtin()
                    || cart.family_fn.contains_native_complex_builtin()
            }
            Obj::Cart(cart) => cart
                .args
                .iter()
                .any(|obj| obj.contains_native_complex_builtin()),
            Obj::CartDim(dim) => dim.set.contains_native_complex_builtin(),
            Obj::Proj(proj) => {
                proj.set.contains_native_complex_builtin()
                    || proj.dim.contains_native_complex_builtin()
            }
            Obj::TupleDim(dim) => dim.arg.contains_native_complex_builtin(),
            Obj::Tuple(tuple) => tuple
                .args
                .iter()
                .any(|obj| obj.contains_native_complex_builtin()),
            Obj::FiniteSetSize(size) => size.set.contains_native_complex_builtin(),
            Obj::FiniteSetMax(max) => max.set.contains_native_complex_builtin(),
            Obj::FiniteSetMin(min) => min.set.contains_native_complex_builtin(),
            Obj::FnRange(range) => range.function.contains_native_complex_builtin(),
            Obj::Replacement(replacement) => {
                replacement.source_set.contains_native_complex_builtin()
            }
            Obj::Sum(sum) => {
                sum.start.contains_native_complex_builtin()
                    || sum.end.contains_native_complex_builtin()
                    || sum.func.contains_native_complex_builtin()
            }
            Obj::SumOfFiniteSet(sum) => {
                sum.set.contains_native_complex_builtin()
                    || sum.func.contains_native_complex_builtin()
            }
            Obj::Product(product) => {
                product.start.contains_native_complex_builtin()
                    || product.end.contains_native_complex_builtin()
                    || product.func.contains_native_complex_builtin()
            }
            Obj::ProductOfFiniteSet(product) => {
                product.set.contains_native_complex_builtin()
                    || product.func.contains_native_complex_builtin()
            }
            Obj::Range(range) => {
                range.start.contains_native_complex_builtin()
                    || range.end.contains_native_complex_builtin()
            }
            Obj::ClosedRange(range) => {
                range.start.contains_native_complex_builtin()
                    || range.end.contains_native_complex_builtin()
            }
            Obj::IntervalObj(interval) => {
                interval.start().contains_native_complex_builtin()
                    || interval.end().contains_native_complex_builtin()
            }
            Obj::OneSideInfinityIntervalObj(interval) => {
                interval.start().contains_native_complex_builtin()
            }
            Obj::FiniteSeqSet(sequence) => {
                sequence.set.contains_native_complex_builtin()
                    || sequence.n.contains_native_complex_builtin()
            }
            Obj::SeqSet(sequence) => sequence.set.contains_native_complex_builtin(),
            Obj::FiniteSeqListObj(sequence) => sequence
                .objs
                .iter()
                .any(|obj| obj.contains_native_complex_builtin()),
            Obj::ObjAtIndex(index) => {
                index.obj.contains_native_complex_builtin()
                    || index.index.contains_native_complex_builtin()
            }
            Obj::MatrixSet(matrix) => {
                matrix.set.contains_native_complex_builtin()
                    || matrix.row_len.contains_native_complex_builtin()
                    || matrix.col_len.contains_native_complex_builtin()
            }
            Obj::MatrixListObj(matrix) => matrix
                .rows
                .iter()
                .flatten()
                .any(|obj| obj.contains_native_complex_builtin()),
            Obj::MatrixAdd(matrix) => {
                matrix.left.contains_native_complex_builtin()
                    || matrix.right.contains_native_complex_builtin()
            }
            Obj::MatrixSub(matrix) => {
                matrix.left.contains_native_complex_builtin()
                    || matrix.right.contains_native_complex_builtin()
            }
            Obj::MatrixMul(matrix) => {
                matrix.left.contains_native_complex_builtin()
                    || matrix.right.contains_native_complex_builtin()
            }
            Obj::MatrixScalarMul(matrix) => {
                matrix.scalar.contains_native_complex_builtin()
                    || matrix.matrix.contains_native_complex_builtin()
            }
            Obj::MatrixPow(matrix) => {
                matrix.base.contains_native_complex_builtin()
                    || matrix.exponent.contains_native_complex_builtin()
            }
            Obj::StructObj(object) => object
                .params
                .iter()
                .any(|obj| obj.contains_native_complex_builtin()),
            Obj::ObjAsStructInstanceWithFieldAccess(access) => {
                access
                    .struct_obj
                    .params
                    .iter()
                    .any(|obj| obj.contains_native_complex_builtin())
                    || access.obj.contains_native_complex_builtin()
            }
            Obj::InstantiatedTemplateObj(template) => template
                .args
                .iter()
                .any(|obj| obj.contains_native_complex_builtin()),
        }
    }
}
