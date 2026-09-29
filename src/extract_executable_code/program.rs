//! Target-independent extracted program IR and Litex AST → IR.

use crate::ast::fact::{
    AndChainAtomicFact, AtomicFact, EqualFact, Fact, GreaterEqualFact, GreaterFact, LessEqualFact,
    LessFact, NotEqualFact,
};
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{
    AnonymousFn, ArithmeticOperator, ComplexOperator, ExpLogOperator, FnObj, FnObjHead,
    IdentifierObj, IntegerOperator, Literal, Obj, StandardSet, TrigOperator,
};
use crate::ast::param::{ParamType, SetBoundParameterList, TypedParameterList};
use crate::ast::stmt::{
    DefAlgoByCasesStmt, DefineObjStmt, DefinitionStmt, HaveFnEqualCaseByCaseStmt, HaveFnEqualStmt,
    HaveObjEqualStmt, Stmt,
};
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::collections::HashSet;

pub(super) struct ExtractedProgram {
    pub(super) statements: Vec<ExtractedStatement>,
}

pub(super) enum ExtractedStatement {
    Constant(ExtractedConstant),
    Function(ExtractedFunction),
}

pub(super) struct ExtractedConstant {
    pub(super) name: String,
    pub(super) value: ExtractedExpression,
    pub(super) line_file: SourceLine,
}

pub(super) struct ExtractedFunction {
    pub(super) name: String,
    pub(super) params: Vec<String>,
    pub(super) cases: Vec<ExtractedCase>,
    pub(super) default_return: Option<ExtractedExpression>,
    pub(super) line_file: SourceLine,
}

pub(super) struct ExtractedCase {
    pub(super) condition: ExtractedCondition,
    pub(super) value: ExtractedExpression,
}

pub(super) struct ExtractedCondition {
    pub(super) left: ExtractedExpression,
    pub(super) operator: ExtractedComparisonOperator,
    pub(super) right: ExtractedExpression,
}

pub(super) enum ExtractedComparisonOperator {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

pub(super) struct ExtractedExpression {
    pub(super) kind: ExtractedExpressionKind,
    pub(super) line_file: SourceLine,
}

pub(super) enum ExtractedExpressionKind {
    Number(String),
    EulerNumber,
    Pi,
    Name(String),
    Add(Box<ExtractedExpression>, Box<ExtractedExpression>),
    Sub(Box<ExtractedExpression>, Box<ExtractedExpression>),
    Mul(Box<ExtractedExpression>, Box<ExtractedExpression>),
    Div(Box<ExtractedExpression>, Box<ExtractedExpression>),
    Pow(Box<ExtractedExpression>, Box<ExtractedExpression>),
    Lcm(Box<ExtractedExpression>, Box<ExtractedExpression>),
    Floor(Box<ExtractedExpression>),
    Ceil(Box<ExtractedExpression>),
    Min(Box<ExtractedExpression>, Box<ExtractedExpression>),
    Max(Box<ExtractedExpression>, Box<ExtractedExpression>),
    Exp(Box<ExtractedExpression>),
    Ln(Box<ExtractedExpression>),
    Sign(Box<ExtractedExpression>),
    Factorial(Box<ExtractedExpression>),
    Call {
        name: String,
        args: Vec<ExtractedExpression>,
    },
}

pub(super) struct ProgramExtractor {
    statements: Vec<ExtractedStatement>,
    constants: HashSet<String>,
    functions: HashSet<String>,
}

impl ProgramExtractor {
    pub(super) fn new() -> Self {
        Self {
            statements: vec![],
            constants: HashSet::new(),
            functions: HashSet::new(),
        }
    }

    pub(super) fn into_program(self) -> ExtractedProgram {
        ExtractedProgram {
            statements: self.statements,
        }
    }

    pub(super) fn extract_stmt(&mut self, stmt: &Stmt) -> RuntimeResult<()> {
        match stmt {
            Stmt::Fact(fact) => reject_unsupported_fact(fact),
            Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::HaveObjEqualStmt(stmt))) => {
                self.extract_constant_definitions(stmt)
            }
            Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(stmt)) => {
                reject_unsupported_have_fn_equal(stmt)
            }
            Stmt::Definition(DefinitionStmt::HaveFnEqualCaseByCaseStmt(stmt)) => {
                reject_unsupported_have_fn_cases(stmt)
            }
            Stmt::Definition(DefinitionStmt::DefAlgoByCasesStmt(stmt)) => {
                self.extract_algo_by_cases(stmt)
            }
            Stmt::Definition(DefinitionStmt::DefAlgoByInducStmt(stmt)) => {
                Err(code_extraction_error(
                    &stmt.line_file,
                    "code extractor v1 does not support `algo … by induc`",
                ))
            }
            _ => Ok(()),
        }
    }

    fn extract_constant_definitions(&mut self, stmt: &HaveObjEqualStmt) -> RuntimeResult<()> {
        let names_with_types = collect_typed_param_names_with_types(&stmt.param_def);
        if names_with_types.len() != stmt.objs_equal_to.len() {
            return Err(code_extraction_error(
                &stmt.line_file,
                "code extractor internal error: object definition arity mismatch",
            ));
        }

        let params = HashSet::new();
        for ((name, param_type), obj) in names_with_types.iter().zip(stmt.objs_equal_to.iter()) {
            if matches!(param_type, ParamType::Obj(obj) if obj_has_complex_syntax(obj)) {
                return Err(code_extraction_error(
                    &stmt.line_file,
                    "code extractor v1 does not support complex-valued definitions",
                ));
            }
            if !is_numeric_param_type(param_type) {
                continue;
            }
            let value = self.extract_expression(obj, &params, &stmt.line_file)?;
            self.statements
                .push(ExtractedStatement::Constant(ExtractedConstant {
                    name: name.clone(),
                    value,
                    line_file: stmt.line_file.clone(),
                }));
            self.constants.insert(name.clone());
        }
        Ok(())
    }

    fn extract_algo_by_cases(&mut self, stmt: &DefAlgoByCasesStmt) -> RuntimeResult<()> {
        validate_real_function_signature(
            &stmt.name,
            &stmt.fn_set_clause.set_bound_parameters,
            &stmt.fn_set_clause.dom_facts,
            &stmt.fn_set_clause.ret_set,
            &stmt.line_file,
        )?;

        let params = collect_set_bound_param_names(&stmt.fn_set_clause.set_bound_parameters);
        if stmt.cases.is_empty() {
            return Err(code_extraction_error(
                &stmt.line_file,
                format!(
                    "code extractor v1 needs at least one case for function implementation `{}`",
                    stmt.name
                ),
            ));
        }
        if stmt.cases.len() != stmt.equal_tos.len() {
            return Err(code_extraction_error(
                &stmt.line_file,
                format!(
                    "code extractor internal error: algo `{}` case/value arity mismatch",
                    stmt.name
                ),
            ));
        }

        let params_in_scope = params.iter().cloned().collect::<HashSet<String>>();
        self.functions.insert(stmt.name.clone());
        let mut cases = vec![];
        for (case, value) in stmt.cases.iter().zip(stmt.equal_tos.iter()) {
            cases.push(ExtractedCase {
                condition: self.extract_case_condition(case, &params_in_scope, &stmt.line_file)?,
                value: self.extract_expression(value, &params_in_scope, &stmt.line_file)?,
            });
        }
        self.statements
            .push(ExtractedStatement::Function(ExtractedFunction {
                name: stmt.name.clone(),
                params,
                cases,
                default_return: None,
                line_file: stmt.line_file.clone(),
            }));
        Ok(())
    }

    fn extract_case_condition(
        &self,
        case: &AndChainAtomicFact,
        params: &HashSet<String>,
        line_file: &SourceLine,
    ) -> RuntimeResult<ExtractedCondition> {
        match case {
            AndChainAtomicFact::AtomicFact(fact) => self.extract_condition(fact, params, line_file),
            AndChainAtomicFact::AndFact(_) | AndChainAtomicFact::ChainFact(_) => {
                Err(code_extraction_error(
                    line_file,
                    "code extractor v1 supports only a single equality or order comparison per case",
                ))
            }
        }
    }

    fn extract_condition(
        &self,
        fact: &AtomicFact,
        params: &HashSet<String>,
        fallback_line: &SourceLine,
    ) -> RuntimeResult<ExtractedCondition> {
        let (left, operator, right, line_file) = match fact {
            AtomicFact::EqualFact(EqualFact {
                left,
                right,
                line_file,
                ..
            }) => (
                left,
                ExtractedComparisonOperator::Equal,
                right,
                line_file.as_ref().unwrap_or(fallback_line),
            ),
            AtomicFact::NotEqualFact(NotEqualFact {
                left,
                right,
                line_file,
                ..
            }) => (
                left,
                ExtractedComparisonOperator::NotEqual,
                right,
                line_file.as_ref().unwrap_or(fallback_line),
            ),
            AtomicFact::LessFact(LessFact {
                left,
                right,
                line_file,
                ..
            }) => (
                left,
                ExtractedComparisonOperator::Less,
                right,
                line_file.as_ref().unwrap_or(fallback_line),
            ),
            AtomicFact::LessEqualFact(LessEqualFact {
                left,
                right,
                line_file,
                ..
            }) => (
                left,
                ExtractedComparisonOperator::LessEqual,
                right,
                line_file.as_ref().unwrap_or(fallback_line),
            ),
            AtomicFact::GreaterFact(GreaterFact {
                left,
                right,
                line_file,
                ..
            }) => (
                left,
                ExtractedComparisonOperator::Greater,
                right,
                line_file.as_ref().unwrap_or(fallback_line),
            ),
            AtomicFact::GreaterEqualFact(GreaterEqualFact {
                left,
                right,
                line_file,
                ..
            }) => (
                left,
                ExtractedComparisonOperator::GreaterEqual,
                right,
                line_file.as_ref().unwrap_or(fallback_line),
            ),
            _ => {
                return Err(code_extraction_error(
                    fallback_line,
                    format!(
                        "code extractor v1 supports only equality and order comparison cases; got `{}`",
                        fact.readable_string()
                    ),
                ));
            }
        };
        Ok(ExtractedCondition {
            left: self.extract_expression(left, params, line_file)?,
            operator,
            right: self.extract_expression(right, params, line_file)?,
        })
    }

    fn extract_expression(
        &self,
        obj: &Obj,
        params: &HashSet<String>,
        line_file: &SourceLine,
    ) -> RuntimeResult<ExtractedExpression> {
        let kind = match obj {
            Obj::Literal(Literal::Number(number)) => {
                ExtractedExpressionKind::Number(number.normalized_value.clone())
            }
            Obj::Literal(Literal::EulerNumber(_)) => ExtractedExpressionKind::EulerNumber,
            Obj::Literal(Literal::Pi(_)) => ExtractedExpressionKind::Pi,
            Obj::Literal(Literal::ImaginaryUnit(_)) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native complex expressions",
                ));
            }
            Obj::ComplexOperator(
                ComplexOperator::RealPart(_)
                | ComplexOperator::ImaginaryPart(_)
                | ComplexOperator::ComplexAbs(_),
            ) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native complex coordinate or modulus expressions",
                ));
            }
            Obj::TrigOperator(
                TrigOperator::Sin(_)
                | TrigOperator::Arcsin(_)
                | TrigOperator::Cos(_)
                | TrigOperator::Tan(_)
                | TrigOperator::Cot(_)
                | TrigOperator::Arccos(_)
                | TrigOperator::Arctan(_)
                | TrigOperator::Arccot(_),
            ) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native trigonometric expressions",
                ));
            }
            Obj::IntegerOperator(IntegerOperator::Gcd(_)) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native gcd",
                ));
            }
            Obj::IntegerOperator(IntegerOperator::Quot(_)) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native quot",
                ));
            }
            Obj::IntegerOperator(IntegerOperator::Mod(_)) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native mod",
                ));
            }
            Obj::IntegerOperator(IntegerOperator::Lcm(value)) => ExtractedExpressionKind::Lcm(
                Box::new(self.extract_expression(&value.left, params, line_file)?),
                Box::new(self.extract_expression(&value.right, params, line_file)?),
            ),
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(value)) => {
                ExtractedExpressionKind::Floor(Box::new(self.extract_expression(
                    &value.arg,
                    params,
                    line_file,
                )?))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(value)) => {
                ExtractedExpressionKind::Ceil(Box::new(self.extract_expression(
                    &value.arg,
                    params,
                    line_file,
                )?))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Min(value)) => ExtractedExpressionKind::Min(
                Box::new(self.extract_expression(&value.left, params, line_file)?),
                Box::new(self.extract_expression(&value.right, params, line_file)?),
            ),
            Obj::ArithmeticOperator(ArithmeticOperator::Max(value)) => ExtractedExpressionKind::Max(
                Box::new(self.extract_expression(&value.left, params, line_file)?),
                Box::new(self.extract_expression(&value.right, params, line_file)?),
            ),
            Obj::ExpLogOperator(ExpLogOperator::Exp(value)) => ExtractedExpressionKind::Exp(
                Box::new(self.extract_expression(&value.arg, params, line_file)?),
            ),
            Obj::ExpLogOperator(ExpLogOperator::Ln(value)) => ExtractedExpressionKind::Ln(
                Box::new(self.extract_expression(&value.arg, params, line_file)?),
            ),
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(value)) => {
                ExtractedExpressionKind::Sign(Box::new(self.extract_expression(
                    &value.arg,
                    params,
                    line_file,
                )?))
            }
            Obj::IntegerOperator(IntegerOperator::Factorial(value)) => {
                ExtractedExpressionKind::Factorial(Box::new(self.extract_expression(
                    &value.arg,
                    params,
                    line_file,
                )?))
            }
            Obj::Identifier(identifier) => self.extract_identifier(identifier, params, line_file)?,
            Obj::ArithmeticOperator(ArithmeticOperator::Add(value)) => self
                .extract_binary_expression(
                    &value.left,
                    &value.right,
                    params,
                    line_file,
                    ExtractedExpressionKind::Add,
                )?,
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(value)) => self
                .extract_binary_expression(
                    &value.left,
                    &value.right,
                    params,
                    line_file,
                    ExtractedExpressionKind::Sub,
                )?,
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(value)) => {
                // Render unary minus as `0 - arg`.
                let zero = ExtractedExpression {
                    kind: ExtractedExpressionKind::Number("0".to_string()),
                    line_file: line_file.clone(),
                };
                ExtractedExpressionKind::Sub(
                    Box::new(zero),
                    Box::new(self.extract_expression(&value.arg, params, line_file)?),
                )
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(value)) => self
                .extract_binary_expression(
                    &value.left,
                    &value.right,
                    params,
                    line_file,
                    ExtractedExpressionKind::Mul,
                )?,
            Obj::ArithmeticOperator(ArithmeticOperator::Div(value)) => self
                .extract_binary_expression(
                    &value.left,
                    &value.right,
                    params,
                    line_file,
                    ExtractedExpressionKind::Div,
                )?,
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(value)) => self
                .extract_binary_expression(
                    &value.base,
                    &value.exponent,
                    params,
                    line_file,
                    ExtractedExpressionKind::Pow,
                )?,
            Obj::FnObj(function) => self.extract_function_call(function, params, line_file)?,
            _ => {
                return Err(code_extraction_error(
                    line_file,
                    format!(
                        "code extractor v1 cannot translate object `{}`",
                        obj.readable_string()
                    ),
                ));
            }
        };
        Ok(ExtractedExpression {
            kind,
            line_file: line_file.clone(),
        })
    }

    fn extract_binary_expression(
        &self,
        left: &Obj,
        right: &Obj,
        params: &HashSet<String>,
        line_file: &SourceLine,
        constructor: fn(
            Box<ExtractedExpression>,
            Box<ExtractedExpression>,
        ) -> ExtractedExpressionKind,
    ) -> RuntimeResult<ExtractedExpressionKind> {
        Ok(constructor(
            Box::new(self.extract_expression(left, params, line_file)?),
            Box::new(self.extract_expression(right, params, line_file)?),
        ))
    }

    fn extract_identifier(
        &self,
        identifier: &IdentifierObj,
        params: &HashSet<String>,
        line_file: &SourceLine,
    ) -> RuntimeResult<ExtractedExpressionKind> {
        let name = match identifier {
            IdentifierObj::Plain { name, .. } => name.as_str(),
            _ => {
                return Err(code_extraction_error(
                    line_file,
                    format!(
                        "code extractor v1 cannot translate qualified name `{}`",
                        identifier.display_string()
                    ),
                ));
            }
        };
        if params.contains(name) || self.constants.contains(name) {
            return Ok(ExtractedExpressionKind::Name(name.to_string()));
        }
        Err(code_extraction_error(
            line_file,
            format!(
                "code extractor v1 cannot translate name `{}` because it is not a function parameter or extracted constant",
                name
            ),
        ))
    }

    fn extract_function_call(
        &self,
        function: &FnObj,
        params: &HashSet<String>,
        line_file: &SourceLine,
    ) -> RuntimeResult<ExtractedExpressionKind> {
        if function.body.len() != 1 {
            return Err(code_extraction_error(
                line_file,
                format!(
                    "code extractor v1 does not support curried function call `{}`",
                    Obj::FnObj(function.clone()).readable_string()
                ),
            ));
        }
        let name = match function.head.as_ref() {
            FnObjHead::Identifier(IdentifierObj::Plain { name, .. }) => name.as_str(),
            _ => {
                return Err(code_extraction_error(
                    line_file,
                    format!(
                        "code extractor v1 supports calls only to named extracted functions; got `{}`",
                        Obj::FnObj(function.clone()).readable_string()
                    ),
                ));
            }
        };
        if !self.functions.contains(name) {
            return Err(code_extraction_error(
                line_file,
                format!(
                    "code extractor v1 cannot call `{}` because it has not been extracted earlier",
                    name
                ),
            ));
        }
        let args = function.body[0]
            .iter()
            .map(|arg| self.extract_expression(arg.as_ref(), params, line_file))
            .collect::<RuntimeResult<Vec<ExtractedExpression>>>()?;
        Ok(ExtractedExpressionKind::Call {
            name: name.to_string(),
            args,
        })
    }
}

#[allow(dead_code)]
pub(super) fn extract_program_from_stmts(stmts: &[Stmt]) -> RuntimeResult<ExtractedProgram> {
    let mut extractor = ProgramExtractor::new();
    for stmt in stmts.iter() {
        extractor.extract_stmt(stmt)?;
    }
    Ok(extractor.into_program())
}

pub(super) fn code_extraction_error(
    line_file: &SourceLine,
    msg: impl Into<String>,
) -> RuntimeError {
    RuntimeError::Unsupported(format!(
        "line {}: {}",
        line_file.line,
        msg.into()
    ))
}

fn reject_unsupported_have_fn_equal(stmt: &HaveFnEqualStmt) -> RuntimeResult<()> {
    if anonymous_fn_has_complex_syntax(&stmt.equal_to_anonymous_fn) {
        return Err(code_extraction_error(
            &stmt.line_file,
            "code extractor v1 does not support native complex function signatures or bodies",
        ));
    }
    Ok(())
}

fn reject_unsupported_have_fn_cases(stmt: &HaveFnEqualCaseByCaseStmt) -> RuntimeResult<()> {
    if obj_has_complex_syntax(&stmt.fn_set_clause.ret_set)
        || stmt
            .fn_set_clause
            .set_bound_parameters
            .groups
            .iter()
            .any(|g| obj_has_complex_syntax(g.param_type.as_ref()))
        || stmt.equal_tos.iter().any(obj_has_complex_syntax)
    {
        return Err(code_extraction_error(
            &stmt.line_file,
            "code extractor v1 does not support native complex function signatures or bodies",
        ));
    }
    Ok(())
}

fn reject_unsupported_fact(fact: &Fact) -> RuntimeResult<()> {
    let rendered = fact.readable_string();
    if contains_unqualified_function_call(&rendered, "quot") {
        return Err(code_extraction_error_fact(
            fact,
            "code extractor v1 does not support native quot",
        ));
    }
    if contains_unqualified_function_call(&rendered, "gcd") {
        return Err(code_extraction_error_fact(
            fact,
            "code extractor v1 does not support native gcd",
        ));
    }
    for (predicate, name) in [
        ("$prime(", "prime"),
        ("$coprime(", "coprime"),
        ("$dvd(", "dvd"),
    ] {
        if rendered.contains(predicate) {
            return Err(code_extraction_error_fact(
                fact,
                format!("code extractor v1 does not support builtin {}", name),
            ));
        }
    }
    if fact_has_complex_syntax(fact) {
        return Err(code_extraction_error_fact(
            fact,
            "code extractor v1 does not support native complex expressions in facts",
        ));
    }
    Ok(())
}

fn code_extraction_error_fact(fact: &Fact, msg: impl Into<String>) -> RuntimeError {
    RuntimeError::Unsupported(format!(
        "fact `{}`: {}",
        fact.readable_string(),
        msg.into()
    ))
}

fn validate_real_function_signature(
    name: &str,
    params_def: &SetBoundParameterList,
    dom_facts: &[crate::ast::fact::QuantifierFreeFact],
    ret_set: &Obj,
    line_file: &SourceLine,
) -> RuntimeResult<()> {
    if !dom_facts.is_empty() {
        return Err(code_extraction_error(
            line_file,
            format!(
                "code extractor v1 does not support domain restrictions in `{}`",
                name
            ),
        ));
    }
    for group in params_def.groups.iter() {
        if !is_real_set_obj(group.param_type.as_ref()) {
            return Err(code_extraction_error(
                line_file,
                format!(
                    "code extractor v1 supports only `R` function parameters; `{}` has parameter set `{}`",
                    name,
                    group.param_type.readable_string()
                ),
            ));
        }
    }
    if !is_real_set_obj(ret_set) {
        return Err(code_extraction_error(
            line_file,
            format!(
                "code extractor v1 supports only `R` function return values; `{}` returns `{}`",
                name,
                ret_set.readable_string()
            ),
        ));
    }
    Ok(())
}

fn is_real_set_obj(obj: &Obj) -> bool {
    matches!(obj, Obj::StandardSet(StandardSet::R))
}

fn is_numeric_param_type(param_type: &ParamType) -> bool {
    match param_type {
        ParamType::Obj(obj) => is_numeric_set_obj(obj),
        ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => false,
    }
}

fn is_numeric_set_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::StandardSet(
            StandardSet::NPos
                | StandardSet::N
                | StandardSet::Q
                | StandardSet::Z
                | StandardSet::R
                | StandardSet::QPos
                | StandardSet::RPos
                | StandardSet::QNeg
                | StandardSet::ZNeg
                | StandardSet::RNeg
                | StandardSet::QStar
                | StandardSet::ZStar
                | StandardSet::RStar
        )
    )
}

fn collect_typed_param_names_with_types(list: &TypedParameterList) -> Vec<(String, ParamType)> {
    let mut out = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            out.push((param.name.clone(), group.param_type.clone()));
        }
    }
    out
}

fn collect_set_bound_param_names(list: &SetBoundParameterList) -> Vec<String> {
    let mut out = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            out.push(param.name.clone());
        }
    }
    out
}

fn contains_unqualified_function_call(rendered: &str, name: &str) -> bool {
    rendered.match_indices(name).any(|(index, _)| {
        let before_is_identifier = rendered[..index]
            .chars()
            .next_back()
            .is_some_and(|ch| ch.is_alphanumeric() || ch == '_' || ch == ':');
        !before_is_identifier && rendered[index + name.len()..].starts_with('(')
    })
}

fn anonymous_fn_has_complex_syntax(anon: &AnonymousFn) -> bool {
    obj_has_complex_syntax(anon.equal_to.as_ref())
        || anon
            .body
            .set_bound_parameters
            .groups
            .iter()
            .any(|g| obj_has_complex_syntax(g.param_type.as_ref()))
        || obj_has_complex_syntax(anon.body.ret_set.as_ref())
}

fn fact_has_complex_syntax(fact: &Fact) -> bool {
    fact.readable_string().contains('i') && obj_text_suggests_complex(&fact.readable_string())
}

fn obj_text_suggests_complex(text: &str) -> bool {
    text.contains("C_abs")
        || text.contains("re(")
        || text.contains("img(")
        || text.contains(" $in C")
        || text.contains("C*")
}

fn obj_has_complex_syntax(obj: &Obj) -> bool {
    match obj {
        Obj::Literal(Literal::ImaginaryUnit(_)) => true,
        Obj::StandardSet(StandardSet::C | StandardSet::CStar) => true,
        Obj::ComplexOperator(_) => true,
        Obj::ArithmeticOperator(ArithmeticOperator::Add(v)) => {
            obj_has_complex_syntax(&v.left) || obj_has_complex_syntax(&v.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(v)) => {
            obj_has_complex_syntax(&v.left) || obj_has_complex_syntax(&v.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(v)) => {
            obj_has_complex_syntax(&v.left) || obj_has_complex_syntax(&v.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(v)) => {
            obj_has_complex_syntax(&v.left) || obj_has_complex_syntax(&v.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(v)) => {
            obj_has_complex_syntax(&v.base) || obj_has_complex_syntax(&v.exponent)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(v)) => obj_has_complex_syntax(&v.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(v)) => obj_has_complex_syntax(&v.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(v)) => obj_has_complex_syntax(&v.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(v)) => obj_has_complex_syntax(&v.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(v)) => obj_has_complex_syntax(&v.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Min(v)) => {
            obj_has_complex_syntax(&v.left) || obj_has_complex_syntax(&v.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Max(v)) => {
            obj_has_complex_syntax(&v.left) || obj_has_complex_syntax(&v.right)
        }
        Obj::FnObj(f) => {
            f.body
                .iter()
                .flatten()
                .any(|arg| obj_has_complex_syntax(arg.as_ref()))
                || match f.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(anon) => {
                        anonymous_fn_has_complex_syntax(anon.as_ref())
                    }
                    _ => false,
                }
        }
        _ => false,
    }
}
