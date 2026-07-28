use crate::prelude::*;

impl FnSetBody {
    pub(crate) fn contains_native_complex_syntax(&self) -> bool {
        self.params_def_with_set
            .iter()
            .any(|group| group.set_obj().contains_native_complex_syntax())
            || self.dom_facts.iter().any(|fact| {
                fact.get_args_from_fact_ref()
                    .into_iter()
                    .any(Obj::contains_native_complex_syntax)
            })
            || self.ret_set.contains_native_complex_syntax()
    }

    pub(crate) fn contains_native_transcendental_syntax(&self) -> bool {
        self.params_def_with_set
            .iter()
            .any(|group| group.set_obj().contains_native_transcendental_syntax())
            || self.dom_facts.iter().any(|fact| {
                fact.get_args_from_fact_ref()
                    .into_iter()
                    .any(Obj::contains_native_transcendental_syntax)
            })
            || self.ret_set.contains_native_transcendental_syntax()
    }
}

impl AnonymousFn {
    pub(crate) fn contains_native_complex_syntax(&self) -> bool {
        self.body.contains_native_complex_syntax() || self.equal_to.contains_native_complex_syntax()
    }

    pub(crate) fn contains_native_transcendental_syntax(&self) -> bool {
        self.body.contains_native_transcendental_syntax()
            || self.equal_to.contains_native_transcendental_syntax()
    }
}

impl Obj {
    /// Detect native complex syntax before a symbolic-only backend attempts to lower the object
    /// as a real-valued expression.
    pub(crate) fn contains_native_complex_syntax(&self) -> bool {
        match self {
            Obj::ImaginaryUnit(_)
            | Obj::RealPart(_)
            | Obj::ImaginaryPart(_)
            | Obj::ComplexAbs(_) => true,
            Obj::Atom(_) | Obj::Number(_) | Obj::EulerNumber(_) | Obj::Pi(_) => false,
            Obj::StandardSet(set) => matches!(set, StandardSet::C),
            Obj::FnObj(fn_obj) => {
                let native_head = match fn_obj.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(function) => {
                        function.contains_native_complex_syntax()
                    }
                    FnObjHead::FiniteSeqListObj(list) => list
                        .objs
                        .iter()
                        .any(|obj| obj.contains_native_complex_syntax()),
                    FnObjHead::ObjAtIndex(index) => {
                        index.obj.contains_native_complex_syntax()
                            || index.index.contains_native_complex_syntax()
                    }
                    FnObjHead::ObjAsStructInstanceWithFieldAccess(access) => {
                        access
                            .struct_obj
                            .params
                            .iter()
                            .any(|obj| obj.contains_native_complex_syntax())
                            || access.obj.contains_native_complex_syntax()
                    }
                    FnObjHead::InstantiatedTemplateObj(template) => template
                        .args
                        .iter()
                        .any(|obj| obj.contains_native_complex_syntax()),
                    FnObjHead::MatrixOperator(matrix) => matrix.contains_native_complex_syntax(),
                    _ => false,
                };
                native_head
                    || fn_obj
                        .body
                        .iter()
                        .flatten()
                        .any(|arg| arg.contains_native_complex_syntax())
            }
            Obj::Add(binary) => {
                binary.left.contains_native_complex_syntax()
                    || binary.right.contains_native_complex_syntax()
            }
            Obj::Sub(binary) => {
                binary.left.contains_native_complex_syntax()
                    || binary.right.contains_native_complex_syntax()
            }
            Obj::Mul(binary) => {
                binary.left.contains_native_complex_syntax()
                    || binary.right.contains_native_complex_syntax()
            }
            Obj::Div(binary) => {
                binary.left.contains_native_complex_syntax()
                    || binary.right.contains_native_complex_syntax()
            }
            Obj::Mod(binary) => {
                binary.left.contains_native_complex_syntax()
                    || binary.right.contains_native_complex_syntax()
            }
            Obj::Pow(pow) => {
                pow.base.contains_native_complex_syntax()
                    || pow.exponent.contains_native_complex_syntax()
            }
            Obj::Abs(abs) => abs.arg.contains_native_complex_syntax(),
            Obj::Sqrt(sqrt) => sqrt.arg.contains_native_complex_syntax(),
            Obj::Log(log) => {
                log.base.contains_native_complex_syntax()
                    || log.arg.contains_native_complex_syntax()
            }
            Obj::Union(binary) => {
                binary.left.contains_native_complex_syntax()
                    || binary.right.contains_native_complex_syntax()
            }
            Obj::Intersect(binary) => {
                binary.left.contains_native_complex_syntax()
                    || binary.right.contains_native_complex_syntax()
            }
            Obj::SetMinus(binary) => {
                binary.left.contains_native_complex_syntax()
                    || binary.right.contains_native_complex_syntax()
            }
            Obj::SetDiff(binary) => {
                binary.left.contains_native_complex_syntax()
                    || binary.right.contains_native_complex_syntax()
            }
            Obj::BigUnion(union) => union.left.contains_native_complex_syntax(),
            Obj::BigIntersect(intersect) => intersect.left.contains_native_complex_syntax(),
            Obj::PowerSet(power_set) => power_set.set.contains_native_complex_syntax(),
            Obj::ListSet(list) => list
                .list
                .iter()
                .any(|obj| obj.contains_native_complex_syntax()),
            Obj::SetBuilder(builder) => {
                builder.param_set.contains_native_complex_syntax()
                    || builder.facts.iter().any(|fact| {
                        fact.get_args_from_fact_ref()
                            .into_iter()
                            .any(Obj::contains_native_complex_syntax)
                    })
            }
            Obj::FnSet(function) => function.body.contains_native_complex_syntax(),
            Obj::AnonymousFn(function) => function.contains_native_complex_syntax(),
            Obj::GeneralCart(cart) => {
                cart.index_set.contains_native_complex_syntax()
                    || cart.family_set.contains_native_complex_syntax()
                    || cart.family_fn.contains_native_complex_syntax()
            }
            Obj::Cart(cart) => cart
                .args
                .iter()
                .any(|obj| obj.contains_native_complex_syntax()),
            Obj::CartDim(dim) => dim.set.contains_native_complex_syntax(),
            Obj::Proj(proj) => {
                proj.set.contains_native_complex_syntax()
                    || proj.dim.contains_native_complex_syntax()
            }
            Obj::TupleDim(dim) => dim.arg.contains_native_complex_syntax(),
            Obj::Tuple(tuple) => tuple
                .args
                .iter()
                .any(|obj| obj.contains_native_complex_syntax()),
            Obj::FiniteSetSize(size) => size.set.contains_native_complex_syntax(),
            Obj::FiniteSetMax(max) => max.set.contains_native_complex_syntax(),
            Obj::FiniteSetMin(min) => min.set.contains_native_complex_syntax(),
            Obj::FnRange(range) => range.function.contains_native_complex_syntax(),
            Obj::Replacement(replacement) => {
                replacement.source_set.contains_native_complex_syntax()
            }
            Obj::Sum(sum) => {
                sum.start.contains_native_complex_syntax()
                    || sum.end.contains_native_complex_syntax()
                    || sum.func.contains_native_complex_syntax()
            }
            Obj::SumOfFiniteSet(sum) => {
                sum.set.contains_native_complex_syntax()
                    || sum.func.contains_native_complex_syntax()
            }
            Obj::Product(product) => {
                product.start.contains_native_complex_syntax()
                    || product.end.contains_native_complex_syntax()
                    || product.func.contains_native_complex_syntax()
            }
            Obj::ProductOfFiniteSet(product) => {
                product.set.contains_native_complex_syntax()
                    || product.func.contains_native_complex_syntax()
            }
            Obj::Range(range) => {
                range.start.contains_native_complex_syntax()
                    || range.end.contains_native_complex_syntax()
            }
            Obj::ClosedRange(range) => {
                range.start.contains_native_complex_syntax()
                    || range.end.contains_native_complex_syntax()
            }
            Obj::IntervalObj(interval) => {
                interval.start().contains_native_complex_syntax()
                    || interval.end().contains_native_complex_syntax()
            }
            Obj::OneSideInfinityIntervalObj(interval) => {
                interval.start().contains_native_complex_syntax()
            }
            Obj::FiniteSeqSet(sequence) => {
                sequence.set.contains_native_complex_syntax()
                    || sequence.n.contains_native_complex_syntax()
            }
            Obj::SeqSet(sequence) => sequence.set.contains_native_complex_syntax(),
            Obj::FiniteSeqListObj(sequence) => sequence
                .objs
                .iter()
                .any(|obj| obj.contains_native_complex_syntax()),
            Obj::ObjAtIndex(index) => {
                index.obj.contains_native_complex_syntax()
                    || index.index.contains_native_complex_syntax()
            }
            Obj::MatrixSet(matrix) => {
                matrix.set.contains_native_complex_syntax()
                    || matrix.row_len.contains_native_complex_syntax()
                    || matrix.col_len.contains_native_complex_syntax()
            }
            Obj::MatrixListObj(matrix) => matrix
                .rows
                .iter()
                .flatten()
                .any(|obj| obj.contains_native_complex_syntax()),
            Obj::MatrixAdd(matrix) => {
                matrix.left.contains_native_complex_syntax()
                    || matrix.right.contains_native_complex_syntax()
            }
            Obj::MatrixSub(matrix) => {
                matrix.left.contains_native_complex_syntax()
                    || matrix.right.contains_native_complex_syntax()
            }
            Obj::MatrixMul(matrix) => {
                matrix.left.contains_native_complex_syntax()
                    || matrix.right.contains_native_complex_syntax()
            }
            Obj::MatrixScalarMul(matrix) => {
                matrix.scalar.contains_native_complex_syntax()
                    || matrix.matrix.contains_native_complex_syntax()
            }
            Obj::MatrixPow(matrix) => {
                matrix.base.contains_native_complex_syntax()
                    || matrix.exponent.contains_native_complex_syntax()
            }
            Obj::StructObj(object) => object
                .params
                .iter()
                .any(|obj| obj.contains_native_complex_syntax()),
            Obj::ObjAsStructInstanceWithFieldAccess(access) => {
                access
                    .struct_obj
                    .params
                    .iter()
                    .any(|obj| obj.contains_native_complex_syntax())
                    || access.obj.contains_native_complex_syntax()
            }
            Obj::InstantiatedTemplateObj(template) => template
                .args
                .iter()
                .any(|obj| obj.contains_native_complex_syntax()),
        }
    }

    /// Detect native named transcendental constants before a backend attempts to lower them as
    /// ordinary identifiers.
    pub(crate) fn contains_native_transcendental_syntax(&self) -> bool {
        match self {
            Obj::EulerNumber(_) | Obj::Pi(_) => true,
            Obj::Atom(_) | Obj::Number(_) | Obj::ImaginaryUnit(_) | Obj::StandardSet(_) => false,
            Obj::FnObj(fn_obj) => {
                let native_head = match fn_obj.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(function) => {
                        function.contains_native_transcendental_syntax()
                    }
                    FnObjHead::FiniteSeqListObj(list) => list
                        .objs
                        .iter()
                        .any(|obj| obj.contains_native_transcendental_syntax()),
                    FnObjHead::ObjAtIndex(index) => {
                        index.obj.contains_native_transcendental_syntax()
                            || index.index.contains_native_transcendental_syntax()
                    }
                    FnObjHead::ObjAsStructInstanceWithFieldAccess(access) => {
                        access
                            .struct_obj
                            .params
                            .iter()
                            .any(|obj| obj.contains_native_transcendental_syntax())
                            || access.obj.contains_native_transcendental_syntax()
                    }
                    FnObjHead::InstantiatedTemplateObj(template) => template
                        .args
                        .iter()
                        .any(|obj| obj.contains_native_transcendental_syntax()),
                    FnObjHead::MatrixOperator(matrix) => {
                        matrix.contains_native_transcendental_syntax()
                    }
                    _ => false,
                };
                native_head
                    || fn_obj
                        .body
                        .iter()
                        .flatten()
                        .any(|arg| arg.contains_native_transcendental_syntax())
            }
            Obj::Add(binary) => {
                binary.left.contains_native_transcendental_syntax()
                    || binary.right.contains_native_transcendental_syntax()
            }
            Obj::Sub(binary) => {
                binary.left.contains_native_transcendental_syntax()
                    || binary.right.contains_native_transcendental_syntax()
            }
            Obj::Mul(binary) => {
                binary.left.contains_native_transcendental_syntax()
                    || binary.right.contains_native_transcendental_syntax()
            }
            Obj::Div(binary) => {
                binary.left.contains_native_transcendental_syntax()
                    || binary.right.contains_native_transcendental_syntax()
            }
            Obj::Mod(binary) => {
                binary.left.contains_native_transcendental_syntax()
                    || binary.right.contains_native_transcendental_syntax()
            }
            Obj::Pow(pow) => {
                pow.base.contains_native_transcendental_syntax()
                    || pow.exponent.contains_native_transcendental_syntax()
            }
            Obj::Abs(abs) => abs.arg.contains_native_transcendental_syntax(),
            Obj::RealPart(real_part) => real_part.arg.contains_native_transcendental_syntax(),
            Obj::ImaginaryPart(imaginary_part) => {
                imaginary_part.arg.contains_native_transcendental_syntax()
            }
            Obj::ComplexAbs(complex_abs) => complex_abs.arg.contains_native_transcendental_syntax(),
            Obj::Sqrt(sqrt) => sqrt.arg.contains_native_transcendental_syntax(),
            Obj::Log(log) => {
                log.base.contains_native_transcendental_syntax()
                    || log.arg.contains_native_transcendental_syntax()
            }
            Obj::Union(binary) => {
                binary.left.contains_native_transcendental_syntax()
                    || binary.right.contains_native_transcendental_syntax()
            }
            Obj::Intersect(binary) => {
                binary.left.contains_native_transcendental_syntax()
                    || binary.right.contains_native_transcendental_syntax()
            }
            Obj::SetMinus(binary) => {
                binary.left.contains_native_transcendental_syntax()
                    || binary.right.contains_native_transcendental_syntax()
            }
            Obj::SetDiff(binary) => {
                binary.left.contains_native_transcendental_syntax()
                    || binary.right.contains_native_transcendental_syntax()
            }
            Obj::BigUnion(union) => union.left.contains_native_transcendental_syntax(),
            Obj::BigIntersect(intersect) => intersect.left.contains_native_transcendental_syntax(),
            Obj::PowerSet(power_set) => power_set.set.contains_native_transcendental_syntax(),
            Obj::ListSet(list) => list
                .list
                .iter()
                .any(|obj| obj.contains_native_transcendental_syntax()),
            Obj::SetBuilder(builder) => {
                builder.param_set.contains_native_transcendental_syntax()
                    || builder.facts.iter().any(|fact| {
                        fact.get_args_from_fact_ref()
                            .into_iter()
                            .any(Obj::contains_native_transcendental_syntax)
                    })
            }
            Obj::FnSet(function) => function.body.contains_native_transcendental_syntax(),
            Obj::AnonymousFn(function) => function.contains_native_transcendental_syntax(),
            Obj::GeneralCart(cart) => {
                cart.index_set.contains_native_transcendental_syntax()
                    || cart.family_set.contains_native_transcendental_syntax()
                    || cart.family_fn.contains_native_transcendental_syntax()
            }
            Obj::Cart(cart) => cart
                .args
                .iter()
                .any(|obj| obj.contains_native_transcendental_syntax()),
            Obj::CartDim(dim) => dim.set.contains_native_transcendental_syntax(),
            Obj::Proj(proj) => {
                proj.set.contains_native_transcendental_syntax()
                    || proj.dim.contains_native_transcendental_syntax()
            }
            Obj::TupleDim(dim) => dim.arg.contains_native_transcendental_syntax(),
            Obj::Tuple(tuple) => tuple
                .args
                .iter()
                .any(|obj| obj.contains_native_transcendental_syntax()),
            Obj::FiniteSetSize(size) => size.set.contains_native_transcendental_syntax(),
            Obj::FiniteSetMax(max) => max.set.contains_native_transcendental_syntax(),
            Obj::FiniteSetMin(min) => min.set.contains_native_transcendental_syntax(),
            Obj::FnRange(range) => range.function.contains_native_transcendental_syntax(),
            Obj::Replacement(replacement) => replacement
                .source_set
                .contains_native_transcendental_syntax(),
            Obj::Sum(sum) => {
                sum.start.contains_native_transcendental_syntax()
                    || sum.end.contains_native_transcendental_syntax()
                    || sum.func.contains_native_transcendental_syntax()
            }
            Obj::SumOfFiniteSet(sum) => {
                sum.set.contains_native_transcendental_syntax()
                    || sum.func.contains_native_transcendental_syntax()
            }
            Obj::Product(product) => {
                product.start.contains_native_transcendental_syntax()
                    || product.end.contains_native_transcendental_syntax()
                    || product.func.contains_native_transcendental_syntax()
            }
            Obj::ProductOfFiniteSet(product) => {
                product.set.contains_native_transcendental_syntax()
                    || product.func.contains_native_transcendental_syntax()
            }
            Obj::Range(range) => {
                range.start.contains_native_transcendental_syntax()
                    || range.end.contains_native_transcendental_syntax()
            }
            Obj::ClosedRange(range) => {
                range.start.contains_native_transcendental_syntax()
                    || range.end.contains_native_transcendental_syntax()
            }
            Obj::IntervalObj(interval) => {
                interval.start().contains_native_transcendental_syntax()
                    || interval.end().contains_native_transcendental_syntax()
            }
            Obj::OneSideInfinityIntervalObj(interval) => {
                interval.start().contains_native_transcendental_syntax()
            }
            Obj::FiniteSeqSet(sequence) => {
                sequence.set.contains_native_transcendental_syntax()
                    || sequence.n.contains_native_transcendental_syntax()
            }
            Obj::SeqSet(sequence) => sequence.set.contains_native_transcendental_syntax(),
            Obj::FiniteSeqListObj(sequence) => sequence
                .objs
                .iter()
                .any(|obj| obj.contains_native_transcendental_syntax()),
            Obj::ObjAtIndex(index) => {
                index.obj.contains_native_transcendental_syntax()
                    || index.index.contains_native_transcendental_syntax()
            }
            Obj::MatrixSet(matrix) => {
                matrix.set.contains_native_transcendental_syntax()
                    || matrix.row_len.contains_native_transcendental_syntax()
                    || matrix.col_len.contains_native_transcendental_syntax()
            }
            Obj::MatrixListObj(matrix) => matrix
                .rows
                .iter()
                .flatten()
                .any(|obj| obj.contains_native_transcendental_syntax()),
            Obj::MatrixAdd(matrix) => {
                matrix.left.contains_native_transcendental_syntax()
                    || matrix.right.contains_native_transcendental_syntax()
            }
            Obj::MatrixSub(matrix) => {
                matrix.left.contains_native_transcendental_syntax()
                    || matrix.right.contains_native_transcendental_syntax()
            }
            Obj::MatrixMul(matrix) => {
                matrix.left.contains_native_transcendental_syntax()
                    || matrix.right.contains_native_transcendental_syntax()
            }
            Obj::MatrixScalarMul(matrix) => {
                matrix.scalar.contains_native_transcendental_syntax()
                    || matrix.matrix.contains_native_transcendental_syntax()
            }
            Obj::MatrixPow(matrix) => {
                matrix.base.contains_native_transcendental_syntax()
                    || matrix.exponent.contains_native_transcendental_syntax()
            }
            Obj::StructObj(object) => object
                .params
                .iter()
                .any(|obj| obj.contains_native_transcendental_syntax()),
            Obj::ObjAsStructInstanceWithFieldAccess(access) => {
                access
                    .struct_obj
                    .params
                    .iter()
                    .any(|obj| obj.contains_native_transcendental_syntax())
                    || access.obj.contains_native_transcendental_syntax()
            }
            Obj::InstantiatedTemplateObj(template) => template
                .args
                .iter()
                .any(|obj| obj.contains_native_transcendental_syntax()),
        }
    }
}
