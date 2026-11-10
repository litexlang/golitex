//! Target-independent extracted program IR and Litex AST → IR.

use crate::ast::fact::{
    AndChainAtomicFact, AtomicFact, EqualFact, Fact, GreaterEqualFact, GreaterFact, LessEqualFact,
    LessFact, NotEqualFact,
};
use crate::ast::line_file::SourceLine;
use crate::ast::names::BoundName;
use crate::ast::obj::{
    AnonymousFn, ArithmeticOperator, ComplexOperator, ExpLogOperator, FnObj, FnObjHead,
    IdentifierObj, IntegerOperator, Literal, Obj, StandardSet, TrigOperator,
};
use crate::ast::param::{ParamType, SetBoundParameterList, TypedParameterList};
use crate::ast::stmt::{
    DefAlgoByCasesStmt, DefineObjStmt, DefinitionStmt, HaveFnEqualCaseByCaseStmt, HaveFnEqualStmt,
    HaveObjEqualStmt, Stmt,
};
use crate::runtime::{CodeSource, IdentifierId};
use crate::runtime::{RuntimeError, RuntimeResult};
use std::collections::{HashMap, HashSet};

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
    constants: HashMap<String, String>,
    functions: HashMap<String, String>,
}

impl ProgramExtractor {
    pub(super) fn new() -> Self {
        Self {
            statements: vec![],
            constants: HashMap::new(),
            functions: HashMap::new(),
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

        let params = HashMap::new();
        for ((binding, param_type), obj) in names_with_types.iter().zip(stmt.objs_equal_to.iter()) {
            let name = &binding.name;
            if matches!(param_type, ParamType::Obj(obj) if obj_has_complex_syntax(obj)) {
                return Err(code_extraction_error(
                    &stmt.line_file,
                    "code extractor v1 does not support complex-valued definitions",
                ));
            }
            if !is_numeric_param_type(param_type) {
                continue;
            }
            self.require_available_name(name, &stmt.line_file)?;
            let value = self.extract_expression(obj, &params, &stmt.line_file)?;
            self.statements
                .push(ExtractedStatement::Constant(ExtractedConstant {
                    name: name.clone(),
                    value,
                    line_file: stmt.line_file.clone(),
                }));
            self.constants
                .insert(declaration_key(binding, &stmt.line_file), name.clone());
        }
        Ok(())
    }

    fn extract_algo_by_cases(&mut self, stmt: &DefAlgoByCasesStmt) -> RuntimeResult<()> {
        self.require_available_name(&stmt.name.name, &stmt.line_file)?;
        validate_real_function_signature(
            &stmt.name.name,
            &stmt.fn_set_clause.set_bound_parameters,
            &stmt.fn_set_clause.dom_facts,
            &stmt.fn_set_clause.ret_set,
            &stmt.line_file,
        )?;

        let bindings: Vec<_> = stmt
            .fn_set_clause
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .collect();
        let globals: HashSet<_> = self
            .constants
            .values()
            .chain(self.functions.values())
            .chain(std::iter::once(&stmt.name.name))
            .cloned()
            .collect();
        let mut reserved = globals.clone();
        reserved.extend(bindings.iter().map(|binding| binding.name.clone()));
        let mut params = Vec::new();
        let mut params_in_scope = HashMap::new();
        for binding in bindings {
            let mut name = binding.name.clone();
            if globals.contains(&name) {
                name.push_str("_arg");
                while reserved.contains(&name) {
                    name.push('_');
                }
            }
            reserved.insert(name.clone());
            params_in_scope.insert(binding.id, name.clone());
            params.push(name);
        }
        if stmt.cases.is_empty() {
            return Err(code_extraction_error(
                &stmt.line_file,
                format!(
                    "code extractor v1 needs at least one case for function implementation `{}`",
                    stmt.name.name
                ),
            ));
        }
        if stmt.cases.len() != stmt.equal_tos.len() {
            return Err(code_extraction_error(
                &stmt.line_file,
                format!(
                    "code extractor internal error: algo `{}` case/value arity mismatch",
                    stmt.name.name
                ),
            ));
        }

        self.functions.insert(
            declaration_key(&stmt.name, &stmt.line_file),
            stmt.name.name.clone(),
        );
        let mut cases = vec![];
        for (case, value) in stmt.cases.iter().zip(stmt.equal_tos.iter()) {
            cases.push(ExtractedCase {
                condition: self.extract_case_condition(case, &params_in_scope, &stmt.line_file)?,
                value: self.extract_expression(value, &params_in_scope, &stmt.line_file)?,
            });
        }
        self.statements
            .push(ExtractedStatement::Function(ExtractedFunction {
                name: stmt.name.name.clone(),
                params,
                cases,
                default_return: None,
                line_file: stmt.line_file.clone(),
            }));
        Ok(())
    }

    fn require_available_name(&self, name: &str, line_file: &SourceLine) -> RuntimeResult<()> {
        if self
            .constants
            .values()
            .chain(self.functions.values())
            .any(|existing| existing == name)
        {
            return Err(code_extraction_error(
                line_file,
                format!("duplicate extracted name `{name}`: repository extraction uses one flat namespace; choose distinct exported constant and algorithm names"),
            ));
        }
        Ok(())
    }

    fn extract_case_condition(
        &self,
        case: &AndChainAtomicFact,
        params: &HashMap<IdentifierId, String>,
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
        params: &HashMap<IdentifierId, String>,
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
        params: &HashMap<IdentifierId, String>,
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
                ExtractedExpressionKind::Floor(Box::new(
                    self.extract_expression(&value.arg, params, line_file)?,
                ))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(value)) => {
                ExtractedExpressionKind::Ceil(Box::new(
                    self.extract_expression(&value.arg, params, line_file)?,
                ))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Min(value)) => {
                ExtractedExpressionKind::Min(
                    Box::new(self.extract_expression(&value.left, params, line_file)?),
                    Box::new(self.extract_expression(&value.right, params, line_file)?),
                )
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Max(value)) => {
                ExtractedExpressionKind::Max(
                    Box::new(self.extract_expression(&value.left, params, line_file)?),
                    Box::new(self.extract_expression(&value.right, params, line_file)?),
                )
            }
            Obj::ExpLogOperator(ExpLogOperator::Exp(value)) => ExtractedExpressionKind::Exp(
                Box::new(self.extract_expression(&value.arg, params, line_file)?),
            ),
            Obj::ExpLogOperator(ExpLogOperator::Ln(value)) => ExtractedExpressionKind::Ln(
                Box::new(self.extract_expression(&value.arg, params, line_file)?),
            ),
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(value)) => {
                ExtractedExpressionKind::Sign(Box::new(
                    self.extract_expression(&value.arg, params, line_file)?,
                ))
            }
            Obj::IntegerOperator(IntegerOperator::Factorial(value)) => {
                ExtractedExpressionKind::Factorial(Box::new(
                    self.extract_expression(&value.arg, params, line_file)?,
                ))
            }
            Obj::Identifier(identifier) => {
                self.extract_identifier(identifier, params, line_file)?
            }
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
        params: &HashMap<IdentifierId, String>,
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
        params: &HashMap<IdentifierId, String>,
        line_file: &SourceLine,
    ) -> RuntimeResult<ExtractedExpressionKind> {
        if let IdentifierObj::Plain { id, .. } = identifier {
            if let Some(name) = params.get(id) {
                return Ok(ExtractedExpressionKind::Name(name.clone()));
            }
        }
        if let Some(name) = self.constants.get(&identifier.ir_string()) {
            return Ok(ExtractedExpressionKind::Name(name.clone()));
        }
        let name = identifier.display_string();
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
        params: &HashMap<IdentifierId, String>,
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
        let FnObjHead::Identifier(identifier) = function.head.as_ref() else {
            return Err(code_extraction_error(
                line_file,
                "code extractor v1 supports calls only to named extracted functions",
            ));
        };
        let Some(name) = self.functions.get(&identifier.ir_string()) else {
            return Err(code_extraction_error(
                line_file,
                format!(
                    "code extractor v1 cannot call `{}` because it has not been extracted earlier",
                    identifier.display_string()
                ),
            ));
        };
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
    RuntimeError::Unsupported(format!("line {}: {}", line_file.line, msg.into()))
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
    RuntimeError::Unsupported(format!("fact `{}`: {}", fact.readable_string(), msg.into()))
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

fn collect_typed_param_names_with_types(list: &TypedParameterList) -> Vec<(BoundName, ParamType)> {
    let mut out = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            out.push((param.clone(), group.param_type.clone()));
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
    fn_set_has_complex_syntax(&anon.body) || obj_has_complex_syntax(&anon.equal_to)
}

fn fact_has_complex_syntax(fact: &Fact) -> bool {
    use crate::ast::fact::Fact::*;
    match fact {
        AtomicFact(fact) => crate::ast::fact::atomic_fact_args_ref(fact)
            .into_iter()
            .any(obj_has_complex_syntax),
        AndFact(fact) => fact.facts.iter().any(|fact| {
            crate::ast::fact::atomic_fact_args_ref(fact)
                .into_iter()
                .any(obj_has_complex_syntax)
        }),
        ChainFact(fact) => fact.objs.iter().any(obj_has_complex_syntax),
        OrFact(fact) => fact.facts.iter().any(|branch| match branch {
            AndChainAtomicFact::AtomicFact(fact) => {
                fact_has_complex_syntax(&Fact::AtomicFact(fact.clone()))
            }
            AndChainAtomicFact::AndFact(fact) => {
                fact_has_complex_syntax(&Fact::AndFact(fact.clone()))
            }
            AndChainAtomicFact::ChainFact(fact) => {
                fact_has_complex_syntax(&Fact::ChainFact(fact.clone()))
            }
        }),
        ExistFact(fact) | ExistUniqueFact(fact) | NotExistFact(fact) => {
            typed_parameters_have_complex_syntax(&fact.typed_parameters)
                || fact.facts.iter().any(qf_has_complex_syntax)
        }
        ForallFact(fact) => forall_has_complex_syntax(fact),
        ForallFactWithIff(fact) => {
            forall_has_complex_syntax(&fact.forall_fact)
                || fact
                    .iff_facts
                    .iter()
                    .any(|fact| fact_has_complex_syntax(&fact.clone().into()))
        }
        NotForall(fact) => {
            typed_parameters_have_complex_syntax(&fact.typed_parameters)
                || fact
                    .dom_facts
                    .iter()
                    .chain(&fact.then_facts)
                    .any(qf_has_complex_syntax)
        }
    }
}

fn qf_has_complex_syntax(fact: &crate::ast::fact::QuantifierFreeFact) -> bool {
    fact_has_complex_syntax(&crate::instantiate::quantifier_free_fact_to_fact(
        fact.clone(),
    ))
}

fn forall_has_complex_syntax(fact: &crate::ast::fact::ForallFact) -> bool {
    typed_parameters_have_complex_syntax(&fact.typed_parameters)
        || fact.dom_facts.iter().any(fact_has_complex_syntax)
        || fact
            .then_facts
            .iter()
            .any(|fact| fact_has_complex_syntax(&fact.clone().into()))
}

fn typed_parameters_have_complex_syntax(parameters: &TypedParameterList) -> bool {
    parameters.groups.iter().any(|group| {
        matches!(&group.param_type,
        ParamType::Obj(obj) if obj_has_complex_syntax(obj))
    })
}

fn fn_set_has_complex_syntax(signature: &crate::ast::obj::FnSet) -> bool {
    signature
        .set_bound_parameters
        .groups
        .iter()
        .any(|group| obj_has_complex_syntax(&group.param_type))
        || signature.dom_facts.iter().any(qf_has_complex_syntax)
        || obj_has_complex_syntax(&signature.ret_set)
}

fn obj_has_complex_syntax(obj: &Obj) -> bool {
    use crate::ast::obj::{FunctionSpace, SetFormer, StructAndFieldAccessObj};
    match obj {
        Obj::Literal(Literal::ImaginaryUnit(_))
        | Obj::StandardSet(StandardSet::C | StandardSet::CStar)
        | Obj::ComplexOperator(_) => true,
        Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_) => false,
        Obj::FunctionSpace(FunctionSpace::FnSet(signature)) => fn_set_has_complex_syntax(signature),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) =>
            fn_set_has_complex_syntax(&function.body) || obj_has_complex_syntax(&function.equal_to),
        Obj::SetFormer(SetFormer::SetBuilder(builder)) =>
            obj_has_complex_syntax(&builder.param_set) || builder.facts.iter().any(qf_has_complex_syntax),
        Obj::InstantiatedTemplateObj(instance) => instance.args.iter().any(obj_has_complex_syntax),
        Obj::FnObj(function) => {
            let head = match function.head.as_ref() {
                FnObjHead::Identifier(identifier) => Obj::Identifier(identifier.clone()),
                FnObjHead::AnonymousFnLiteral(function) => Obj::FunctionSpace(
                    FunctionSpace::AnonymousFn(function.as_ref().clone())),
                FnObjHead::FieldAccess(field) => Obj::StructAndFieldAccessObj(
                    StructAndFieldAccessObj::FieldAccess(field.clone())),
                FnObjHead::InstantiatedTemplateObj(instance) => Obj::InstantiatedTemplateObj(instance.clone()),
                FnObjHead::Object(obj) => obj.as_ref().clone(),
            };
            obj_has_complex_syntax(&head) || function.body.iter().flatten()
                .any(|arg| obj_has_complex_syntax(arg))
        }
        Obj::MatrixOperator(_) | Obj::BoundOperator(_) | Obj::IntegralOperator(_)
        | Obj::DerivativeOperator(_) | Obj::ArithmeticOperator(_) | Obj::IntegerOperator(_)
        | Obj::TrigOperator(_) | Obj::HyperbolicOperator(_) | Obj::LimitOperator(_)
        | Obj::ExpLogOperator(_) | Obj::SetOperator(_) | Obj::SetFormer(_)
        | Obj::ProductShape(_) | Obj::FunctionSpace(_) | Obj::IteratedOperator(_)
        | Obj::FiniteSetStat(_) | Obj::StructAndFieldAccessObj(_) => {
            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs(obj, obj)
                .unwrap_or_default().into_iter().any(|(child, _)| obj_has_complex_syntax(&child))
        }
    }
}

/// Keep publication identity in the lookup key while retaining the public
/// extracted spelling in the flat target-language namespace.
fn declaration_key(binding: &BoundName, source: &SourceLine) -> String {
    let identifier = match &source.origin {
        CodeSource::RootExport { export_file_id, .. } => {
            IdentifierObj::with_export_file_id(*export_file_id, binding.name.clone())
        }
        CodeSource::ImportedExport {
            global_mod_id,
            export_file_id,
            ..
        } => IdentifierObj::with_mod_and_export_file_id(
            *global_mod_id,
            *export_file_id,
            binding.name.clone(),
        ),
        CodeSource::Eval | CodeSource::Repl | CodeSource::Real(_) => {
            IdentifierObj::from_bound_name(binding)
        }
    };
    identifier.ir_string()
}

#[cfg(test)]
mod syntax_tests {
    use super::*;
    use crate::prelude::*;

    #[test]
    fn complex_detection_traverses_fact_operands_and_elementary_operators() {
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        for source in [
            "i=i",
            "re(i)=0",
            "C_abs(i)>=0",
            "exp(i)=exp(i)",
            "sin(i)=sin(i)",
        ] {
            let tokens = crate::tokenize::Tokenizer::new()
                .tokenize(source, runtime.current_file.clone())
                .unwrap();
            let Stmt::Fact(fact) = runtime.parse(&tokens).unwrap().remove(0) else {
                panic!("fact")
            };
            assert!(fact_has_complex_syntax(&fact), "{source}");
        }
        for source in ["1=1", "exp(1)=exp(1)", "sin(0)=sin(0)"] {
            let tokens = crate::tokenize::Tokenizer::new()
                .tokenize(source, runtime.current_file.clone())
                .unwrap();
            let Stmt::Fact(fact) = runtime.parse(&tokens).unwrap().remove(0) else {
                panic!("fact")
            };
            assert!(!fact_has_complex_syntax(&fact), "{source}");
        }
    }
}
