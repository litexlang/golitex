use super::super::program::*;
use crate::runtime::RuntimeResult;

struct CRenderer {
    lines: Vec<String>,
    needs_math: bool,
    needs_stdlib: bool,
    needs_lcm_helper: bool,
    needs_factorial_helper: bool,
}

impl CRenderer {
    fn new() -> Self {
        Self {
            lines: vec![],
            needs_math: false,
            needs_stdlib: false,
            needs_lcm_helper: false,
            needs_factorial_helper: false,
        }
    }

    fn render_statement(&mut self, statement: &ExtractedStatement) -> RuntimeResult<()> {
        match statement {
            ExtractedStatement::Constant(constant) => self.render_constant(constant),
            ExtractedStatement::Function(function) => self.render_function(function),
        }
    }

    fn render_constant(&mut self, constant: &ExtractedConstant) -> RuntimeResult<()> {
        validate_c_name(&constant.name, &constant.line_file)?;
        let value = self.render_file_scope_expression(&constant.value)?;
        self.lines
            .push(format!("double {} = {};", constant.name, value));
        Ok(())
    }

    fn render_function(&mut self, function: &ExtractedFunction) -> RuntimeResult<()> {
        validate_c_name(&function.name, &function.line_file)?;
        let mut params = vec![];
        for param in function.params.iter() {
            validate_c_name(param, &function.line_file)?;
            params.push(format!("double {}", param));
        }
        if !self.lines.is_empty() {
            self.lines.push(String::new());
        }
        let params = if params.is_empty() {
            "void".to_string()
        } else {
            params.join(", ")
        };
        self.lines
            .push(format!("double {}({}) {{", function.name, params));
        for (index, case) in function.cases.iter().enumerate() {
            let keyword = if index == 0 { "if" } else { "else if" };
            let condition = self.render_condition(&case.condition)?;
            let value = self.render_expression(&case.value)?;
            self.lines
                .push(format!("    {} ({}) {{", keyword, condition));
            self.lines.push(format!("        return {};", value));
            self.lines.push("    }".to_string());
        }
        if let Some(default_return) = &function.default_return {
            let value = self.render_expression(default_return)?;
            self.lines.push(format!("    return {};", value));
        } else {
            self.needs_stdlib = true;
            self.lines.push("    abort();".to_string());
        }
        self.lines.push("}".to_string());
        Ok(())
    }

    fn render_condition(&mut self, condition: &ExtractedCondition) -> RuntimeResult<String> {
        Ok(format!(
            "{} {} {}",
            self.render_expression(&condition.left)?,
            comparison_operator(&condition.operator),
            self.render_expression(&condition.right)?
        ))
    }

    fn render_file_scope_expression(
        &mut self,
        expression: &ExtractedExpression,
    ) -> RuntimeResult<String> {
        match &expression.kind {
            ExtractedExpressionKind::Number(value) => Ok(c_double_literal(value)),
            ExtractedExpressionKind::EulerNumber => {
                Ok("2.7182818284590452353602874713526625".to_string())
            }
            ExtractedExpressionKind::Pi => Ok("3.1415926535897932384626433832795029".to_string()),
            ExtractedExpressionKind::Add(left, right) => {
                self.render_file_scope_binary_expression(left, "+", right)
            }
            ExtractedExpressionKind::Sub(left, right) => {
                self.render_file_scope_binary_expression(left, "-", right)
            }
            ExtractedExpressionKind::Mul(left, right) => {
                self.render_file_scope_binary_expression(left, "*", right)
            }
            ExtractedExpressionKind::Div(left, right) => {
                self.render_file_scope_binary_expression(left, "/", right)
            }
            _ => Err(super::super::program::code_extraction_error(
                &expression.line_file,
                "C extractor v1 supports only literal arithmetic in module-level constants",
            )),
        }
    }

    fn render_file_scope_binary_expression(
        &mut self,
        left: &ExtractedExpression,
        operator: &str,
        right: &ExtractedExpression,
    ) -> RuntimeResult<String> {
        Ok(format!(
            "({} {} {})",
            self.render_file_scope_expression(left)?,
            operator,
            self.render_file_scope_expression(right)?
        ))
    }

    fn render_expression(&mut self, expression: &ExtractedExpression) -> RuntimeResult<String> {
        match &expression.kind {
            ExtractedExpressionKind::Number(value) => Ok(c_double_literal(value)),
            ExtractedExpressionKind::EulerNumber => {
                Ok("2.7182818284590452353602874713526625".to_string())
            }
            ExtractedExpressionKind::Pi => Ok("3.1415926535897932384626433832795029".to_string()),
            ExtractedExpressionKind::Name(name) => {
                validate_c_name(name, &expression.line_file)?;
                Ok(name.clone())
            }
            ExtractedExpressionKind::Add(left, right) => {
                self.render_binary_expression(left, "+", right)
            }
            ExtractedExpressionKind::Sub(left, right) => {
                self.render_binary_expression(left, "-", right)
            }
            ExtractedExpressionKind::Mul(left, right) => {
                self.render_binary_expression(left, "*", right)
            }
            ExtractedExpressionKind::Div(left, right) => {
                self.render_binary_expression(left, "/", right)
            }
            ExtractedExpressionKind::Pow(left, right) => {
                self.needs_math = true;
                Ok(format!(
                    "pow({}, {})",
                    self.render_expression(left)?,
                    self.render_expression(right)?
                ))
            }
            ExtractedExpressionKind::Lcm(left, right) => {
                self.needs_lcm_helper = true;
                Ok(format!(
                    "litex_lcm({}, {})",
                    self.render_expression(left)?,
                    self.render_expression(right)?
                ))
            }
            ExtractedExpressionKind::Floor(value) => {
                self.needs_math = true;
                Ok(format!("floor({})", self.render_expression(value)?))
            }
            ExtractedExpressionKind::Ceil(value) => {
                self.needs_math = true;
                Ok(format!("ceil({})", self.render_expression(value)?))
            }
            ExtractedExpressionKind::Min(left, right) => {
                self.needs_math = true;
                Ok(format!(
                    "fmin({}, {})",
                    self.render_expression(left)?,
                    self.render_expression(right)?
                ))
            }
            ExtractedExpressionKind::Max(left, right) => {
                self.needs_math = true;
                Ok(format!(
                    "fmax({}, {})",
                    self.render_expression(left)?,
                    self.render_expression(right)?
                ))
            }
            ExtractedExpressionKind::Exp(value) => {
                self.needs_math = true;
                Ok(format!("exp({})", self.render_expression(value)?))
            }
            ExtractedExpressionKind::Ln(value) => {
                self.needs_math = true;
                Ok(format!("log({})", self.render_expression(value)?))
            }
            ExtractedExpressionKind::Sign(value) => {
                let value = self.render_expression(value)?;
                Ok(format!(
                    "({0} > 0.0 ? 1.0 : ({0} < 0.0 ? -1.0 : 0.0))",
                    value
                ))
            }
            ExtractedExpressionKind::Factorial(value) => {
                self.needs_factorial_helper = true;
                Ok(format!(
                    "litex_factorial({})",
                    self.render_expression(value)?
                ))
            }
            ExtractedExpressionKind::Call { name, args } => {
                validate_c_name(name, &expression.line_file)?;
                let args = args
                    .iter()
                    .map(|arg| self.render_expression(arg))
                    .collect::<RuntimeResult<Vec<String>>>()?;
                Ok(format!("{}({})", name, args.join(", ")))
            }
        }
    }

    fn render_binary_expression(
        &mut self,
        left: &ExtractedExpression,
        operator: &str,
        right: &ExtractedExpression,
    ) -> RuntimeResult<String> {
        Ok(format!(
            "({} {} {})",
            self.render_expression(left)?,
            operator,
            self.render_expression(right)?
        ))
    }

    fn finish(self) -> String {
        if self.lines.is_empty() {
            return "/* No C-extractable Litex definitions. */".to_string();
        }
        let mut sections = vec![];
        let mut includes = vec![];
        if self.needs_math {
            includes.push("#include <math.h>");
        }
        if self.needs_stdlib {
            includes.push("#include <stdlib.h>");
        }
        if !includes.is_empty() {
            sections.push(includes.join("\n"));
        }
        if self.needs_lcm_helper {
            sections.push(lcm_helper().to_string());
        }
        if self.needs_factorial_helper {
            sections.push(factorial_helper().to_string());
        }
        sections.push(self.lines.join("\n"));
        sections.join("\n\n")
    }
}

pub(in crate::extract_executable_code) fn render_program(
    program: &ExtractedProgram,
) -> RuntimeResult<String> {
    let mut renderer = CRenderer::new();
    for statement in program.statements.iter() {
        renderer.render_statement(statement)?;
    }
    Ok(renderer.finish())
}

fn comparison_operator(operator: &ExtractedComparisonOperator) -> &'static str {
    match operator {
        ExtractedComparisonOperator::Equal => "==",
        ExtractedComparisonOperator::NotEqual => "!=",
        ExtractedComparisonOperator::Less => "<",
        ExtractedComparisonOperator::LessEqual => "<=",
        ExtractedComparisonOperator::Greater => ">",
        ExtractedComparisonOperator::GreaterEqual => ">=",
    }
}

fn c_double_literal(value: &str) -> String {
    if value.contains('.') || value.contains('e') || value.contains('E') {
        return value.to_string();
    }
    format!("{}.0", value)
}

fn validate_c_name(name: &str, line_file: &crate::ast::line_file::SourceLine) -> RuntimeResult<()> {
    if is_c_identifier(name) {
        return Ok(());
    }
    Err(super::super::program::code_extraction_error(
        line_file,
        format!("C extractor v1 cannot emit `{}` as an identifier", name),
    ))
}

fn is_c_identifier(name: &str) -> bool {
    if is_c_keyword(name) {
        return false;
    }
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if first != '_' && !first.is_ascii_alphabetic() {
        return false;
    }
    chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn is_c_keyword(name: &str) -> bool {
    matches!(
        name,
        "auto"
            | "break"
            | "case"
            | "char"
            | "const"
            | "continue"
            | "default"
            | "do"
            | "double"
            | "else"
            | "enum"
            | "extern"
            | "float"
            | "for"
            | "goto"
            | "if"
            | "inline"
            | "int"
            | "long"
            | "register"
            | "restrict"
            | "return"
            | "short"
            | "signed"
            | "sizeof"
            | "static"
            | "struct"
            | "switch"
            | "typedef"
            | "union"
            | "unsigned"
            | "void"
            | "volatile"
            | "while"
            | "_Bool"
            | "_Complex"
            | "_Imaginary"
    )
}

fn lcm_helper() -> &'static str {
    "static long long litex_gcd_ll(long long left, long long right) {\n    left = left < 0 ? -left : left;\n    right = right < 0 ? -right : right;\n    while (right != 0) {\n        long long remainder = left % right;\n        left = right;\n        right = remainder;\n    }\n    return left;\n}\n\nstatic double litex_lcm(double left, double right) {\n    long long left_integer = (long long)left;\n    long long right_integer = (long long)right;\n    if (left_integer == 0 || right_integer == 0) {\n        return 0.0;\n    }\n    long long value = (left_integer / litex_gcd_ll(left_integer, right_integer)) * right_integer;\n    return (double)(value < 0 ? -value : value);\n}"
}

fn factorial_helper() -> &'static str {
    "static double litex_factorial(double value) {\n    long long upper = (long long)value;\n    double result = 1.0;\n    for (long long index = 2; index <= upper; ++index) {\n        result *= (double)index;\n    }\n    return result;\n}"
}
