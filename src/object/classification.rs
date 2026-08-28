//! Object kind, source identity, and equality-key classification.

use crate::prelude::*;

impl Obj {
    pub fn kind(&self) -> ObjKind {
        match self {
            Obj::Atom(atom) => match atom {
                AtomObj::Identifier(_) => ObjKind::Identifier,
                AtomObj::IdentifierWithMod(_) => ObjKind::IdentifierWithMod,
                AtomObj::Bound(_) => ObjKind::BoundParam,
            },
            Obj::FnObj(_) => ObjKind::FnObj,
            Obj::Number(_) => ObjKind::Number,
            Obj::ImaginaryUnit(_) => ObjKind::ImaginaryUnit,
            Obj::EulerNumber(_) => ObjKind::EulerNumber,
            Obj::Pi(_) => ObjKind::Pi,
            Obj::Add(_) => ObjKind::Add,
            Obj::Sub(_) => ObjKind::Sub,
            Obj::Mul(_) => ObjKind::Mul,
            Obj::Div(_) => ObjKind::Div,
            Obj::Mod(_) => ObjKind::Mod,
            Obj::Quot(_) => ObjKind::Quot,
            Obj::Gcd(_) => ObjKind::Gcd,
            Obj::Lcm(_) => ObjKind::Lcm,
            Obj::Floor(_) => ObjKind::Floor,
            Obj::Ceil(_) => ObjKind::Ceil,
            Obj::Min(_) => ObjKind::Min,
            Obj::Max(_) => ObjKind::Max,
            Obj::Exp(_) => ObjKind::Exp,
            Obj::Ln(_) => ObjKind::Ln,
            Obj::Sign(_) => ObjKind::Sign,
            Obj::Factorial(_) => ObjKind::Factorial,
            Obj::Pow(_) => ObjKind::Pow,
            Obj::Abs(_) => ObjKind::Abs,
            Obj::Sin(_) => ObjKind::Sin,
            Obj::Arcsin(_) => ObjKind::Arcsin,
            Obj::Cos(_) => ObjKind::Cos,
            Obj::Tan(_) => ObjKind::Tan,
            Obj::Cot(_) => ObjKind::Cot,
            Obj::RealPart(_) => ObjKind::RealPart,
            Obj::ImaginaryPart(_) => ObjKind::ImaginaryPart,
            Obj::ComplexAbs(_) => ObjKind::ComplexAbs,
            Obj::Sqrt(_) => ObjKind::Sqrt,
            Obj::Log(_) => ObjKind::Log,
            Obj::Union(_) => ObjKind::Union,
            Obj::Intersect(_) => ObjKind::Intersect,
            Obj::SetMinus(_) => ObjKind::SetMinus,
            Obj::BigUnion(_) => ObjKind::BigUnion,
            Obj::BigIntersect(_) => ObjKind::BigIntersect,
            Obj::IndexUnion(_) => ObjKind::IndexUnion,
            Obj::IndexIntersect(_) => ObjKind::IndexIntersect,
            Obj::PowerSet(_) => ObjKind::PowerSet,
            Obj::GeneralCart(_) => ObjKind::GeneralCart,
            Obj::ListSet(_) => ObjKind::ListSet,
            Obj::SetBuilder(_) => ObjKind::SetBuilder,
            Obj::FnSet(_) => ObjKind::FnSet,
            Obj::AnonymousFn(_) => ObjKind::AnonymousFn,
            Obj::Cart(_) => ObjKind::Cart,
            Obj::CartDim(_) => ObjKind::CartDim,
            Obj::Proj(_) => ObjKind::Proj,
            Obj::TupleDim(_) => ObjKind::TupleDim,
            Obj::Tuple(_) => ObjKind::Tuple,
            Obj::FiniteSetSize(_) => ObjKind::FiniteSetSize,
            Obj::FiniteSetMax(_) => ObjKind::FiniteSetMax,
            Obj::FiniteSetMin(_) => ObjKind::FiniteSetMin,
            Obj::FnRange(_) => ObjKind::FnRange,
            Obj::Replacement(_) => ObjKind::Replacement,
            Obj::Sum(_) => ObjKind::Sum,
            Obj::SumOfFiniteSet(_) => ObjKind::SumOfFiniteSet,
            Obj::Product(_) => ObjKind::Product,
            Obj::ProductOfFiniteSet(_) => ObjKind::ProductOfFiniteSet,
            Obj::Reduce(_) => ObjKind::Reduce,
            Obj::FiniteSetReduce(_) => ObjKind::FiniteSetReduce,
            Obj::Range(_) => ObjKind::Range,
            Obj::ClosedRange(_) => ObjKind::ClosedRange,
            Obj::FiniteSeqSet(_) => ObjKind::FiniteSeqSet,
            Obj::SeqSet(_) => ObjKind::SeqSet,
            Obj::FiniteSeqListObj(_) => ObjKind::FiniteSeqListObj,
            Obj::ObjAtIndex(_) => ObjKind::ObjAtIndex,
            Obj::StandardSet(_) => ObjKind::StandardSet,
            Obj::MatrixSet(_) => ObjKind::MatrixSet,
            Obj::MatrixListObj(_) => ObjKind::MatrixListObj,
            Obj::MatrixAdd(_) => ObjKind::MatrixAdd,
            Obj::MatrixSub(_) => ObjKind::MatrixSub,
            Obj::MatrixMul(_) => ObjKind::MatrixMul,
            Obj::MatrixScalarMul(_) => ObjKind::MatrixScalarMul,
            Obj::MatrixPow(_) => ObjKind::MatrixPow,
            Obj::StructObj(_) => ObjKind::StructObj,
            Obj::ObjAsStructInstanceWithFieldAccess(_) => {
                ObjKind::ObjAsStructInstanceWithFieldAccess
            }
            Obj::InstantiatedTemplateObj(_) => ObjKind::InstantiatedTemplateObj,
            Obj::OneSideInfinityIntervalObj(_) => ObjKind::OneSideInfinityIntervalObj,
            Obj::IntervalObj(_) => ObjKind::IntervalObj,
        }
    }

    /// Parser-owned identity of this exact source occurrence when the object
    /// currently participates in the recursive Result-to-Lean pipeline. Synthetic
    /// kernel objects deliberately return `None`; they cannot be joined to a
    /// source WD-use edge by rendered text.
    pub fn source_occurrence_id(&self) -> Option<SourceObjectOccurrenceId> {
        match self {
            Obj::FnObj(value) => value.source_occurrence_id,
            Obj::Add(value) => value.source_occurrence_id,
            Obj::Sub(value) => value.source_occurrence_id,
            Obj::Mul(value) => value.source_occurrence_id,
            Obj::Div(value) => value.source_occurrence_id,
            Obj::ListSet(value) => value.source_occurrence_id,
            Obj::AnonymousFn(value) => value.source_occurrence_id,
            Obj::Sum(value) => value.source_occurrence_id,
            _ => None,
        }
    }

    pub fn kind_id(&self) -> u8 {
        self.kind().as_u8()
    }

    pub fn equality_in_forall_key_part(&self) -> (ObjKind, ObjOperatorString) {
        (self.kind(), self.obj_operator_string())
    }

    fn obj_operator_string(&self) -> ObjOperatorString {
        match self {
            Obj::FnObj(fn_obj) => fn_obj.head.to_string(),
            Obj::Add(_) => ADD.to_string(),
            Obj::Sub(_) => SUB.to_string(),
            Obj::Mul(_) => MUL.to_string(),
            Obj::Div(_) => DIV.to_string(),
            Obj::Mod(_) => MOD.to_string(),
            Obj::Quot(_) => QUOT.to_string(),
            Obj::Gcd(_) => GCD.to_string(),
            Obj::Lcm(_) => LCM.to_string(),
            Obj::Floor(_) => FLOOR.to_string(),
            Obj::Ceil(_) => CEIL.to_string(),
            Obj::Min(_) => MIN.to_string(),
            Obj::Max(_) => MAX.to_string(),
            Obj::Exp(_) => EXP.to_string(),
            Obj::Ln(_) => LN.to_string(),
            Obj::Sign(_) => SIGN.to_string(),
            Obj::Factorial(_) => FACTORIAL.to_string(),
            Obj::Pow(_) => POW.to_string(),
            Obj::Abs(_) => ABS.to_string(),
            Obj::Sin(_) => SIN.to_string(),
            Obj::Arcsin(_) => ARCSIN.to_string(),
            Obj::Cos(_) => COS.to_string(),
            Obj::Tan(_) => TAN.to_string(),
            Obj::Cot(_) => COT.to_string(),
            Obj::RealPart(_) => RE.to_string(),
            Obj::ImaginaryPart(_) => IMG.to_string(),
            Obj::ComplexAbs(_) => C_ABS.to_string(),
            Obj::Sqrt(_) => SQRT.to_string(),
            Obj::Log(_) => LOG.to_string(),
            Obj::Union(_) => UNION.to_string(),
            Obj::Intersect(_) => INTERSECT.to_string(),
            Obj::SetMinus(_) => SET_MINUS.to_string(),
            Obj::BigUnion(_) => BIG_UNION.to_string(),
            Obj::BigIntersect(_) => BIG_INTERSECT.to_string(),
            Obj::IndexUnion(_) => INDEX_UNION.to_string(),
            Obj::IndexIntersect(_) => INDEX_INTERSECT.to_string(),
            Obj::PowerSet(_) => POWER_SET.to_string(),
            Obj::GeneralCart(_) => GENERAL_CART.to_string(),
            Obj::Cart(_) => CART.to_string(),
            Obj::CartDim(_) => CART_DIM.to_string(),
            Obj::Proj(_) => PROJ.to_string(),
            Obj::TupleDim(_) => TUPLE_DIM.to_string(),
            Obj::FiniteSetSize(_) => FINITE_SET_SIZE.to_string(),
            Obj::FiniteSetMax(_) => FINITE_SET_MAX.to_string(),
            Obj::FiniteSetMin(_) => FINITE_SET_MIN.to_string(),
            Obj::FnRange(_) => FN_RANGE.to_string(),
            Obj::Replacement(_) => REPLACEMENT.to_string(),
            Obj::Sum(_) => SUM.to_string(),
            Obj::SumOfFiniteSet(_) => FINITE_SET_SUM.to_string(),
            Obj::Product(_) => PRODUCT.to_string(),
            Obj::ProductOfFiniteSet(_) => FINITE_SET_PRODUCT.to_string(),
            Obj::Reduce(_) => REDUCE.to_string(),
            Obj::FiniteSetReduce(_) => FINITE_SET_REDUCE.to_string(),
            Obj::Range(_) => RANGE.to_string(),
            Obj::ClosedRange(_) => CLOSED_RANGE.to_string(),
            Obj::MatrixAdd(_) => MATRIX_ADD.to_string(),
            Obj::MatrixSub(_) => MATRIX_SUB.to_string(),
            Obj::MatrixMul(_) => MATRIX_MUL.to_string(),
            Obj::MatrixScalarMul(_) => MATRIX_SCALAR_MUL.to_string(),
            Obj::MatrixPow(_) => MATRIX_POW.to_string(),
            Obj::StructObj(struct_obj) => struct_obj.name.to_string(),
            Obj::InstantiatedTemplateObj(template_obj) => template_obj.template_name.to_string(),
            Obj::ObjAsStructInstanceWithFieldAccess(field_access) => {
                field_access.field_name.clone()
            }
            _ => String::new(),
        }
    }
}
