use super::super::program::*;
use crate::runtime::RuntimeResult;

struct PythonRenderer {
    lines: Vec<String>,
    needs_math: bool,
}

impl PythonRenderer {
    fn new() -> Self {
        Self {
            lines: vec![],
            needs_math: false,
        }
    }

    fn render_statement(&mut self, statement: &ExtractedStatement) -> RuntimeResult<()> {
        match statement {
            ExtractedStatement::Constant(constant) => self.render_constant(constant),
            ExtractedStatement::Function(function) => self.render_function(function),
        }
    }

    fn render_constant(&mut self, constant: &ExtractedConstant) -> RuntimeResult<()> {
        validate_python_name(&constant.name, &constant.line_file)?;
        let value = self.render_expression(&constant.value)?;
        self.lines.push(format!("{} = {}", constant.name, value));
        Ok(())
    }

    fn render_function(&mut self, function: &ExtractedFunction) -> RuntimeResult<()> {
        validate_python_name(&function.name, &function.line_file)?;
        for param in function.params.iter() {
            validate_python_name(param, &function.line_file)?;
        }
        if !self.lines.is_empty() {
            self.lines.push(String::new());
        }
        self.lines.push(format!(
            "def {}({}):",
            function.name,
            function.params.join(", ")
        ));
        for (index, case) in function.cases.iter().enumerate() {
            let keyword = if index == 0 { "if" } else { "elif" };
            let condition = self.render_condition(&case.condition)?;
            let value = self.render_expression(&case.value)?;
            self.lines.push(format!("    {} {}:", keyword, condition));
            self.lines.push(format!("        return {}", value));
        }
        if let Some(default_return) = &function.default_return {
            let value = self.render_expression(default_return)?;
            self.lines.push(format!("    return {}", value));
        } else {
            self.lines
                .push("    raise AssertionError(\"unreachable verified Litex cases\")".to_string());
        }
        Ok(())
    }

    fn render_condition(&mut self, condition: &ExtractedCondition) -> RuntimeResult<String> {
        let left = self.render_expression(&condition.left)?;
        let right = self.render_expression(&condition.right)?;
        Ok(format!(
            "{} {} {}",
            left,
            comparison_operator(&condition.operator),
            right
        ))
    }

    fn render_expression(&mut self, expression: &ExtractedExpression) -> RuntimeResult<String> {
        match &expression.kind {
            ExtractedExpressionKind::Number(value) => Ok(python_float_literal(value)),
            ExtractedExpressionKind::EulerNumber => {
                self.needs_math = true;
                Ok("math.e".to_string())
            }
            ExtractedExpressionKind::Pi => {
                self.needs_math = true;
                Ok("math.pi".to_string())
            }
            ExtractedExpressionKind::Name(name) => {
                validate_python_name(name, &expression.line_file)?;
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
                self.render_binary_expression(left, "**", right)
            }
            ExtractedExpressionKind::Lcm(left, right) => {
                self.needs_math = true;
                let left = self.render_expression(left)?;
                let right = self.render_expression(right)?;
                Ok(format!("math.lcm(int({}), int({}))", left, right))
            }
            ExtractedExpressionKind::Floor(value) => {
                self.needs_math = true;
                Ok(format!("math.floor({})", self.render_expression(value)?))
            }
            ExtractedExpressionKind::Ceil(value) => {
                self.needs_math = true;
                Ok(format!("math.ceil({})", self.render_expression(value)?))
            }
            ExtractedExpressionKind::Min(left, right) => Ok(format!(
                "min({}, {})",
                self.render_expression(left)?,
                self.render_expression(right)?
            )),
            ExtractedExpressionKind::Max(left, right) => Ok(format!(
                "max({}, {})",
                self.render_expression(left)?,
                self.render_expression(right)?
            )),
            ExtractedExpressionKind::Exp(value) => {
                self.needs_math = true;
                Ok(format!("math.exp({})", self.render_expression(value)?))
            }
            ExtractedExpressionKind::Ln(value) => {
                self.needs_math = true;
                Ok(format!("math.log({})", self.render_expression(value)?))
            }
            ExtractedExpressionKind::Sign(value) => {
                let value = self.render_expression(value)?;
                Ok(format!("(1 if {0} > 0 else (-1 if {0} < 0 else 0))", value))
            }
            ExtractedExpressionKind::Factorial(value) => {
                self.needs_math = true;
                Ok(format!(
                    "math.factorial(int({}))",
                    self.render_expression(value)?
                ))
            }
            ExtractedExpressionKind::Call { name, args } => {
                validate_python_name(name, &expression.line_file)?;
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
            return "# No Python-extractable Litex definitions.".to_string();
        }
        if !self.needs_math {
            return self.lines.join("\n");
        }
        let mut lines = vec!["import math".to_string(), String::new()];
        lines.extend(self.lines);
        lines.join("\n")
    }
}

pub(in crate::extract_executable_code) fn render_program(
    program: &ExtractedProgram,
) -> RuntimeResult<String> {
    let mut renderer = PythonRenderer::new();
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

fn python_float_literal(value: &str) -> String {
    if value.contains('.') || value.contains('e') || value.contains('E') {
        return value.to_string();
    }
    format!("{}.0", value)
}

fn validate_python_name(
    name: &str,
    line_file: &crate::ast::line_file::SourceLine,
) -> RuntimeResult<()> {
    if is_python_identifier(name) {
        return Ok(());
    }
    Err(super::super::program::code_extraction_error(
        line_file,
        format!(
            "Python extractor v1 cannot emit `{}` as an identifier",
            name
        ),
    ))
}

fn is_python_identifier(name: &str) -> bool {
    if is_python_keyword(name) {
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

fn is_python_keyword(name: &str) -> bool {
    matches!(
        name,
        "False"
            | "None"
            | "True"
            | "and"
            | "as"
            | "assert"
            | "async"
            | "await"
            | "break"
            | "class"
            | "continue"
            | "def"
            | "del"
            | "elif"
            | "else"
            | "except"
            | "finally"
            | "for"
            | "from"
            | "global"
            | "if"
            | "import"
            | "in"
            | "is"
            | "lambda"
            | "nonlocal"
            | "not"
            | "or"
            | "pass"
            | "raise"
            | "return"
            | "try"
            | "while"
            | "with"
            | "yield"
    )
}
