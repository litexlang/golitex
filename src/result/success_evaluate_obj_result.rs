use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct SuccessEvaluateObjResult {
    pub expression: Obj,
    pub value: Number,
    pub step: SuccessEvaluateObjStepResult,
}

#[derive(Clone, Debug)]
pub enum SuccessEvaluateObjStepResult {
    Literal(SuccessEvaluateLiteralResult),
    Unary(Box<SuccessEvaluateUnaryObjResult>),
    Binary(Box<SuccessEvaluateBinaryObjResult>),
    Shape(Box<SuccessEvaluateObjByShapeResult>),
}

#[derive(Clone)]
pub struct SuccessEvaluateLiteralResult {
    pub literal: Number,
}

#[derive(Clone, Debug)]
pub struct SuccessEvaluateUnaryObjResult {
    pub operator: EvaluateUnaryObjOperator,
    pub argument: Box<SuccessEvaluateObjResult>,
}

#[derive(Clone, Debug)]
pub struct SuccessEvaluateBinaryObjResult {
    pub operator: EvaluateBinaryObjOperator,
    pub left: Box<SuccessEvaluateObjResult>,
    pub right: Box<SuccessEvaluateObjResult>,
}

#[derive(Clone)]
pub struct SuccessEvaluateObjByShapeResult {
    pub operator: EvaluateObjShapeOperator,
    pub inputs: Vec<Obj>,
    pub evaluated_children: Vec<SuccessEvaluateObjResult>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvaluateUnaryObjOperator {
    Floor,
    Ceil,
    Exp,
    Ln,
    Sign,
    Factorial,
    Abs,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvaluateBinaryObjOperator {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Quot,
    Gcd,
    Lcm,
    Min,
    Max,
    Pow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvaluateObjShapeOperator {
    CartDim,
    TupleDim,
    ListSetSize,
    ClosedRangeSize,
    RangeSize,
    CartSize,
    FiniteSetMax,
    FiniteSetMin,
}

impl SuccessEvaluateObjResult {
    pub fn new(expression: Obj, value: Number, step: SuccessEvaluateObjStepResult) -> Self {
        Self {
            expression,
            value,
            step,
        }
    }

    pub fn literal(number: Number) -> Self {
        Self::new(
            number.clone().into(),
            number.clone(),
            SuccessEvaluateObjStepResult::Literal(SuccessEvaluateLiteralResult::new(number)),
        )
    }
}

impl SuccessEvaluateLiteralResult {
    pub fn new(literal: Number) -> Self {
        Self { literal }
    }
}

impl SuccessEvaluateUnaryObjResult {
    pub fn new(operator: EvaluateUnaryObjOperator, argument: SuccessEvaluateObjResult) -> Self {
        Self {
            operator,
            argument: Box::new(argument),
        }
    }
}

impl SuccessEvaluateBinaryObjResult {
    pub fn new(
        operator: EvaluateBinaryObjOperator,
        left: SuccessEvaluateObjResult,
        right: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            operator,
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl SuccessEvaluateObjByShapeResult {
    pub fn new(
        operator: EvaluateObjShapeOperator,
        inputs: Vec<Obj>,
        evaluated_children: Vec<SuccessEvaluateObjResult>,
    ) -> Self {
        Self {
            operator,
            inputs,
            evaluated_children,
        }
    }
}

impl fmt::Debug for SuccessEvaluateObjResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SuccessEvaluateObjResult")
            .field("expression", &self.expression.to_string())
            .field("value", &self.value.to_string())
            .field("step", &self.step)
            .finish()
    }
}

impl fmt::Debug for SuccessEvaluateLiteralResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SuccessEvaluateLiteralResult")
            .field("literal", &self.literal.to_string())
            .finish()
    }
}

impl fmt::Debug for SuccessEvaluateObjByShapeResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inputs = self
            .inputs
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        f.debug_struct("SuccessEvaluateObjByShapeResult")
            .field("operator", &self.operator)
            .field("inputs", &inputs)
            .field("evaluated_children", &self.evaluated_children)
            .finish()
    }
}
