use crate::prelude::*;
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
    pub(super) line_file: LineFile,
}

pub(super) struct ExtractedFunction {
    pub(super) name: String,
    pub(super) params: Vec<String>,
    pub(super) cases: Vec<ExtractedCase>,
    pub(super) default_return: Option<ExtractedExpression>,
    pub(super) line_file: LineFile,
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
    pub(super) line_file: LineFile,
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

struct ProgramExtractor {
    statements: Vec<ExtractedStatement>,
    constants: HashSet<String>,
    functions: HashSet<String>,
}

impl ProgramExtractor {
    fn new() -> Self {
        Self {
            statements: vec![],
            constants: HashSet::new(),
            functions: HashSet::new(),
        }
    }

    fn extract_stmt(&mut self, stmt: &Stmt, runtime: &Runtime) -> Result<(), RuntimeError> {
        match stmt {
            Stmt::Fact(fact) => reject_unsupported_fact(fact),
            Stmt::Definition(DefinitionStmt::HaveObjEqualStmt(stmt)) => {
                self.extract_constant_definitions(stmt)
            }
            Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(stmt)) => {
                reject_unsupported_function_definition(stmt)
            }
            Stmt::Definition(DefinitionStmt::DefAlgoStmt(stmt)) => {
                self.extract_algorithm(stmt, runtime)
            }
            _ => Ok(()),
        }
    }

    fn extract_constant_definitions(
        &mut self,
        stmt: &HaveObjEqualStmt,
    ) -> Result<(), RuntimeError> {
        let names_with_types = stmt.param_def.collect_param_names_with_types();
        if names_with_types.len() != stmt.objs_equal_to.len() {
            return Err(code_extraction_error(
                &stmt.line_file,
                "code extractor internal error: object definition arity mismatch",
            ));
        }

        let params = HashSet::new();
        for ((name, param_type), obj) in names_with_types.iter().zip(stmt.objs_equal_to.iter()) {
            if matches!(param_type, ParamType::Obj(obj) if obj.contains_native_complex_syntax()) {
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

    fn extract_algorithm(
        &mut self,
        stmt: &DefAlgoStmt,
        runtime: &Runtime,
    ) -> Result<(), RuntimeError> {
        let function = runtime.definition_identifier_obj(&stmt.name);
        let Some(fn_set) = runtime.get_fn_range_function_body(&function) else {
            return Err(code_extraction_error(
                &stmt.line_file,
                format!(
                    "code extractor v1 cannot find the function definition for implementation `{}`",
                    stmt.name
                ),
            ));
        };
        validate_real_function_signature(
            &stmt.name,
            &fn_set.set_bound_parameters,
            &fn_set.dom_facts,
            fn_set.ret_set.as_ref(),
            &stmt.line_file,
        )?;

        let expected_params =
            SetBoundParameterGroup::collect_param_names(&fn_set.set_bound_parameters);
        let params = stmt
            .param_names()
            .map(str::to_string)
            .collect::<Vec<String>>();
        if params.len() != expected_params.len() {
            return Err(code_extraction_error(
                &stmt.line_file,
                format!(
                    "code extractor v1 found {} algorithm parameters for `{}`, but its function definition has {}",
                    params.len(),
                    stmt.name,
                    expected_params.len()
                ),
            ));
        }
        if stmt.cases.is_empty() && stmt.default_return.is_none() {
            return Err(code_extraction_error(
                &stmt.line_file,
                format!(
                    "code extractor v1 needs a return expression for function implementation `{}`",
                    stmt.name
                ),
            ));
        }

        let params_in_scope = params.iter().cloned().collect::<HashSet<String>>();
        self.functions.insert(stmt.name.clone());
        let mut cases = vec![];
        for case in stmt.cases.iter() {
            cases.push(ExtractedCase {
                condition: self.extract_condition(&case.condition, &params_in_scope)?,
                value: self.extract_expression(
                    &case.return_stmt.value,
                    &params_in_scope,
                    &case.return_stmt.line_file,
                )?,
            });
        }
        let default_return = match &stmt.default_return {
            Some(value) => Some(self.extract_expression(
                &value.value,
                &params_in_scope,
                &value.line_file,
            )?),
            None => None,
        };
        self.statements
            .push(ExtractedStatement::Function(ExtractedFunction {
                name: stmt.name.clone(),
                params,
                cases,
                default_return,
                line_file: stmt.line_file.clone(),
            }));
        Ok(())
    }

    fn extract_condition(
        &self,
        fact: &AtomicFact,
        params: &HashSet<String>,
    ) -> Result<ExtractedCondition, RuntimeError> {
        let (left, operator, right, line_file) = match fact {
            AtomicFact::EqualFact(fact) => (
                &fact.left,
                ExtractedComparisonOperator::Equal,
                &fact.right,
                &fact.line_file,
            ),
            AtomicFact::NotEqualFact(fact) => (
                &fact.left,
                ExtractedComparisonOperator::NotEqual,
                &fact.right,
                &fact.line_file,
            ),
            AtomicFact::LessFact(fact) => (
                &fact.left,
                ExtractedComparisonOperator::Less,
                &fact.right,
                &fact.line_file,
            ),
            AtomicFact::LessEqualFact(fact) => (
                &fact.left,
                ExtractedComparisonOperator::LessEqual,
                &fact.right,
                &fact.line_file,
            ),
            AtomicFact::GreaterFact(fact) => (
                &fact.left,
                ExtractedComparisonOperator::Greater,
                &fact.right,
                &fact.line_file,
            ),
            AtomicFact::GreaterEqualFact(fact) => (
                &fact.left,
                ExtractedComparisonOperator::GreaterEqual,
                &fact.right,
                &fact.line_file,
            ),
            _ => {
                return Err(code_extraction_error(
                    &fact.line_file(),
                    format!(
                        "code extractor v1 supports only equality and order comparison cases; got `{}`",
                        fact
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
        line_file: &LineFile,
    ) -> Result<ExtractedExpression, RuntimeError> {
        let kind = match obj {
            Obj::Number(number) => {
                ExtractedExpressionKind::Number(number.normalized_value.clone())
            }
            Obj::EulerNumber(_) => ExtractedExpressionKind::EulerNumber,
            Obj::Pi(_) => ExtractedExpressionKind::Pi,
            Obj::ImaginaryUnit(_) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native complex expressions",
                ));
            }
            Obj::RealPart(_) | Obj::ImaginaryPart(_) | Obj::ComplexAbs(_) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native complex coordinate or modulus expressions",
                ));
            }
            Obj::Sin(_) | Obj::Arcsin(_) | Obj::Cos(_) | Obj::Tan(_) | Obj::Cot(_) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native trigonometric expressions",
                ));
            }
            Obj::Gcd(_) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native gcd",
                ));
            }
            Obj::Quot(_) => {
                return Err(code_extraction_error(
                    line_file,
                    "code extractor v1 does not support native quot",
                ));
            }
            Obj::Lcm(value) => ExtractedExpressionKind::Lcm(
                Box::new(self.extract_expression(&value.left, params, line_file)?),
                Box::new(self.extract_expression(&value.right, params, line_file)?),
            ),
            Obj::Floor(value) => ExtractedExpressionKind::Floor(Box::new(
                self.extract_expression(&value.arg, params, line_file)?,
            )),
            Obj::Ceil(value) => ExtractedExpressionKind::Ceil(Box::new(
                self.extract_expression(&value.arg, params, line_file)?,
            )),
            Obj::Min(value) => ExtractedExpressionKind::Min(
                Box::new(self.extract_expression(&value.left, params, line_file)?),
                Box::new(self.extract_expression(&value.right, params, line_file)?),
            ),
            Obj::Max(value) => ExtractedExpressionKind::Max(
                Box::new(self.extract_expression(&value.left, params, line_file)?),
                Box::new(self.extract_expression(&value.right, params, line_file)?),
            ),
            Obj::Exp(value) => ExtractedExpressionKind::Exp(Box::new(
                self.extract_expression(&value.arg, params, line_file)?,
            )),
            Obj::Ln(value) => ExtractedExpressionKind::Ln(Box::new(
                self.extract_expression(&value.arg, params, line_file)?,
            )),
            Obj::Sign(value) => ExtractedExpressionKind::Sign(Box::new(
                self.extract_expression(&value.arg, params, line_file)?,
            )),
            Obj::Factorial(value) => ExtractedExpressionKind::Factorial(Box::new(
                self.extract_expression(&value.arg, params, line_file)?,
            )),
            Obj::Atom(atom) => self.extract_atom(atom, params, line_file)?,
            Obj::Add(value) => self.extract_binary_expression(
                &value.left,
                &value.right,
                params,
                line_file,
                ExtractedExpressionKind::Add,
            )?,
            Obj::Sub(value) => self.extract_binary_expression(
                &value.left,
                &value.right,
                params,
                line_file,
                ExtractedExpressionKind::Sub,
            )?,
            Obj::Mul(value) => self.extract_binary_expression(
                &value.left,
                &value.right,
                params,
                line_file,
                ExtractedExpressionKind::Mul,
            )?,
            Obj::Div(value) => self.extract_binary_expression(
                &value.left,
                &value.right,
                params,
                line_file,
                ExtractedExpressionKind::Div,
            )?,
            Obj::Pow(value) => self.extract_binary_expression(
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
                    format!("code extractor v1 cannot translate object `{}`", obj),
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
        line_file: &LineFile,
        constructor: fn(
            Box<ExtractedExpression>,
            Box<ExtractedExpression>,
        ) -> ExtractedExpressionKind,
    ) -> Result<ExtractedExpressionKind, RuntimeError> {
        Ok(constructor(
            Box::new(self.extract_expression(left, params, line_file)?),
            Box::new(self.extract_expression(right, params, line_file)?),
        ))
    }

    fn extract_atom(
        &self,
        atom: &AtomObj,
        params: &HashSet<String>,
        line_file: &LineFile,
    ) -> Result<ExtractedExpressionKind, RuntimeError> {
        let name = match atom {
            AtomObj::Identifier(identifier) => identifier.name.as_str(),
            AtomObj::Bound(parameter) => parameter.name(),
            _ => {
                return Err(code_extraction_error(
                    line_file,
                    format!("code extractor v1 cannot translate atom `{}`", atom),
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
        line_file: &LineFile,
    ) -> Result<ExtractedExpressionKind, RuntimeError> {
        if function.body.len() != 1 {
            return Err(code_extraction_error(
                line_file,
                format!(
                    "code extractor v1 does not support curried function call `{}`",
                    function
                ),
            ));
        }
        let name = match function.head.as_ref() {
            FnObjHead::Identifier(identifier) => identifier.name.as_str(),
            _ => {
                return Err(code_extraction_error(
                    line_file,
                    format!(
                        "code extractor v1 supports calls only to named extracted functions; got `{}`",
                        function.head
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
            .collect::<Result<Vec<ExtractedExpression>, RuntimeError>>()?;
        Ok(ExtractedExpressionKind::Call {
            name: name.to_string(),
            args,
        })
    }
}

pub(super) fn extract_program_from_stmts(
    stmts: &[Stmt],
    runtime: &Runtime,
) -> Result<ExtractedProgram, RuntimeError> {
    let mut extractor = ProgramExtractor::new();
    for stmt in stmts.iter() {
        extractor.extract_stmt(stmt, runtime)?;
    }
    Ok(ExtractedProgram {
        statements: extractor.statements,
    })
}

pub(super) fn code_extraction_error(
    line_file: &LineFile,
    msg: impl Into<String>,
) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        msg.into(),
        line_file.clone(),
        None,
        vec![],
    ))
    .into()
}

fn reject_unsupported_function_definition(stmt: &HaveFnEqualStmt) -> Result<(), RuntimeError> {
    if stmt.equal_to_anonymous_fn.contains_native_complex_syntax() {
        return Err(code_extraction_error(
            &stmt.line_file,
            "code extractor v1 does not support native complex function signatures or bodies",
        ));
    }
    Ok(())
}

fn reject_unsupported_fact(fact: &Fact) -> Result<(), RuntimeError> {
    let rendered = fact.to_string();
    if contains_unqualified_function_call(&rendered, QUOT) {
        return Err(code_extraction_error(
            &fact.line_file(),
            "code extractor v1 does not support native quot",
        ));
    }
    if contains_unqualified_function_call(&rendered, GCD) {
        return Err(code_extraction_error(
            &fact.line_file(),
            "code extractor v1 does not support native gcd",
        ));
    }
    for (predicate, name) in [
        ("$prime(", "prime"),
        ("$coprime(", "coprime"),
        ("$dvd(", "dvd"),
    ] {
        if rendered.contains(predicate) {
            return Err(code_extraction_error(
                &fact.line_file(),
                format!("code extractor v1 does not support builtin {}", name),
            ));
        }
    }
    if fact.contains_native_complex_syntax() {
        return Err(code_extraction_error(
            &fact.line_file(),
            "code extractor v1 does not support native complex expressions in facts",
        ));
    }
    Ok(())
}

fn validate_real_function_signature(
    name: &str,
    params_def: &SetBoundParameterList,
    dom_facts: &[QuantifierFreeFact],
    ret_set: &Obj,
    line_file: &LineFile,
) -> Result<(), RuntimeError> {
    if !dom_facts.is_empty() {
        return Err(code_extraction_error(
            line_file,
            format!(
                "code extractor v1 does not support domain restrictions in `{}`",
                name
            ),
        ));
    }
    for group in params_def.iter() {
        if !is_real_set_obj(group.set_obj()) {
            return Err(code_extraction_error(
                line_file,
                format!(
                    "code extractor v1 supports only `R` function parameters; `{}` has parameter set `{}`",
                    name,
                    group.set_obj()
                ),
            ));
        }
    }
    if !is_real_set_obj(ret_set) {
        return Err(code_extraction_error(
            line_file,
            format!(
                "code extractor v1 supports only `R` function return values; `{}` returns `{}`",
                name, ret_set
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

fn contains_unqualified_function_call(rendered: &str, name: &str) -> bool {
    rendered.match_indices(name).any(|(index, _)| {
        let before_is_identifier = rendered[..index]
            .chars()
            .next_back()
            .is_some_and(|ch| ch.is_alphanumeric() || ch == '_' || ch == ':');
        !before_is_identifier && rendered[index + name.len()..].starts_with('(')
    })
}
