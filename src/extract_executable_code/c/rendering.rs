use super::super::program::*;
use crate::runtime::RuntimeResult;

struct CRenderer {
    lines: Vec<String>,
    needs_math: bool,
    needs_stdlib: bool,
    needs_lcm_helper: bool,
    needs_factorial_helper: bool,
    needs_sign: bool,
}

impl CRenderer {
    fn new() -> Self {
        Self {
            lines: vec![],
            needs_math: false,
            needs_stdlib: false,
            needs_lcm_helper: false,
            needs_factorial_helper: false,
            needs_sign: false,
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
            .push(format!("double {} = {};", c_name(&constant.name), value));
        Ok(())
    }

    fn render_function(&mut self, function: &ExtractedFunction) -> RuntimeResult<()> {
        validate_c_name(&function.name, &function.line_file)?;
        let mut params = vec![];
        for param in function.params.iter() {
            validate_c_name(param, &function.line_file)?;
            params.push(format!("double {}", c_name(param)));
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
            .push(format!("double {}({}) {{", c_name(&function.name), params));
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
                Ok(c_name(name))
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
                self.needs_math = true;
                self.needs_stdlib = true;
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
                self.needs_sign = true;
                let value = self.render_expression(value)?;
                Ok(format!("litex_sign({value})"))
            }
            ExtractedExpressionKind::Factorial(value) => {
                self.needs_factorial_helper = true;
                self.needs_math = true;
                self.needs_stdlib = true;
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
                Ok(format!("{}({})", c_name(name), args.join(", ")))
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
        if self.needs_sign {
            sections.push("static double litex_sign(double value) {\n    return value > 0.0 ? 1.0 : (value < 0.0 ? -1.0 : 0.0);\n}".to_string());
        }
        if self.needs_factorial_helper {
            sections.push(factorial_helper().to_string());
        }
        sections.push(self.lines.join("\n"));
        sections.join("\n\n")
    }
}

fn c_name(name: &str) -> String {
    // Prefix inputs already in the escape namespace too, keeping this mapping
    // injective without adding a renderer-owned name registry.
    if name.starts_with("litex_user_") || is_c_runtime_name(name) {
        format!("litex_user_{name}")
    } else {
        name.to_string()
    }
}

fn is_c_runtime_name(name: &str) -> bool {
    if matches!(
        name,
        "abort"
            | "exit"
            | "_Exit"
            | "atexit"
            | "system"
            | "getenv"
            | "malloc"
            | "calloc"
            | "realloc"
            | "free"
            | "bsearch"
            | "qsort"
            | "abs"
            | "labs"
            | "llabs"
            | "div"
            | "ldiv"
            | "lldiv"
            | "div_t"
            | "ldiv_t"
            | "lldiv_t"
            | "size_t"
            | "wchar_t"
            | "rand"
            | "srand"
            | "atof"
            | "atoi"
            | "atol"
            | "atoll"
            | "strtod"
            | "strtof"
            | "strtold"
            | "strtol"
            | "strtoll"
            | "strtoul"
            | "strtoull"
            | "mblen"
            | "mbtowc"
            | "wctomb"
            | "mbstowcs"
            | "wcstombs"
            | "NULL"
            | "EXIT_SUCCESS"
            | "EXIT_FAILURE"
            | "RAND_MAX"
            | "MB_CUR_MAX"
            | "HUGE_VAL"
            | "HUGE_VALF"
            | "HUGE_VALL"
            | "INFINITY"
            | "NAN"
            | "FP_INFINITE"
            | "FP_NAN"
            | "FP_NORMAL"
            | "FP_SUBNORMAL"
            | "FP_ZERO"
            | "FP_FAST_FMA"
            | "FP_FAST_FMAF"
            | "FP_FAST_FMAL"
            | "FP_ILOGB0"
            | "FP_ILOGBNAN"
            | "MATH_ERRNO"
            | "MATH_ERREXCEPT"
            | "math_errhandling"
            | "float_t"
            | "double_t"
            | "fpclassify"
            | "isfinite"
            | "isinf"
            | "isnan"
            | "isnormal"
            | "signbit"
            | "isgreater"
            | "isgreaterequal"
            | "isless"
            | "islessequal"
            | "islessgreater"
            | "isunordered"
            | "litex_gcd_ll"
            | "litex_lcm"
            | "litex_factorial"
            | "litex_sign"
    ) {
        return true;
    }
    let base = name
        .strip_suffix('f')
        .or_else(|| name.strip_suffix('l'))
        .unwrap_or(name);
    [name, base].iter().any(|name| {
        matches!(
            *name,
            "acos"
                | "asin"
                | "atan"
                | "atan2"
                | "cos"
                | "sin"
                | "tan"
                | "acosh"
                | "asinh"
                | "atanh"
                | "cosh"
                | "sinh"
                | "tanh"
                | "exp"
                | "exp2"
                | "expm1"
                | "frexp"
                | "ilogb"
                | "ldexp"
                | "log"
                | "log10"
                | "log1p"
                | "log2"
                | "logb"
                | "modf"
                | "scalbn"
                | "scalbln"
                | "cbrt"
                | "fabs"
                | "hypot"
                | "pow"
                | "sqrt"
                | "erf"
                | "erfc"
                | "lgamma"
                | "tgamma"
                | "ceil"
                | "floor"
                | "nearbyint"
                | "rint"
                | "lrint"
                | "llrint"
                | "round"
                | "lround"
                | "llround"
                | "trunc"
                | "fmod"
                | "remainder"
                | "remquo"
                | "copysign"
                | "nan"
                | "nextafter"
                | "nexttoward"
                | "fdim"
                | "fmax"
                | "fmin"
                | "fma"
        )
    })
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
    "static unsigned long long litex_gcd_ll(unsigned long long left, unsigned long long right) {\n    while (right != 0) {\n        unsigned long long remainder = left % right;\n        left = right;\n        right = remainder;\n    }\n    return left;\n}\n\nstatic double litex_lcm(double left, double right) {\n    if (!isfinite(left) || !isfinite(right) || floor(left) != left || floor(right) != right || left < -9223372036854775808.0 || left >= 9223372036854775808.0 || right < -9223372036854775808.0 || right >= 9223372036854775808.0) {\n        abort();\n    }\n    long long li = (long long)left;\n    long long ri = (long long)right;\n    unsigned long long a = li < 0 ? 0ULL - (unsigned long long)li : (unsigned long long)li;\n    unsigned long long b = ri < 0 ? 0ULL - (unsigned long long)ri : (unsigned long long)ri;\n    if (a == 0 || b == 0) {\n        return 0.0;\n    }\n    return (double)(a / litex_gcd_ll(a, b)) * (double)b;\n}"
}

fn factorial_helper() -> &'static str {
    "static double litex_factorial(double value) {\n    if (!isfinite(value) || value < 0.0 || floor(value) != value) {\n        abort();\n    }\n    if (value > 170.0) {\n        return INFINITY;\n    }\n    int upper = (int)value;\n    double result = 1.0;\n    for (int index = 2; index <= upper; ++index) {\n        result *= (double)index;\n    }\n    return result;\n}"
}
