use crate::prelude::*;

const LEAN_ONE: &str = "(1 : ℝ)";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LeanRationalExpression {
    pub expression: String,
    pub numerator: String,
    pub denominator: String,
}

impl LeanRationalExpression {
    pub fn from_obj(obj: &Obj) -> Result<Self, RuntimeError> {
        match obj {
            Obj::Number(number) => Ok(Self::atom(format!("({} : ℝ)", number.normalized_value))),
            Obj::Atom(atom) => Ok(Self::atom(lean_atom_name(atom)?)),
            Obj::Add(add) => {
                let left = Self::from_obj(&add.left)?;
                let right = Self::from_obj(&add.right)?;
                let numerator = add_expression(
                    multiply_expression(&left.numerator, &right.denominator),
                    multiply_expression(&right.numerator, &left.denominator),
                );
                let denominator = multiply_expression(&left.denominator, &right.denominator);
                Ok(Self::new(
                    binary_expression(&left.expression, "+", &right.expression),
                    numerator,
                    denominator,
                ))
            }
            Obj::Sub(sub) => {
                let left = Self::from_obj(&sub.left)?;
                let right = Self::from_obj(&sub.right)?;
                let numerator = subtract_expression(
                    multiply_expression(&left.numerator, &right.denominator),
                    multiply_expression(&right.numerator, &left.denominator),
                );
                let denominator = multiply_expression(&left.denominator, &right.denominator);
                Ok(Self::new(
                    binary_expression(&left.expression, "-", &right.expression),
                    numerator,
                    denominator,
                ))
            }
            Obj::Mul(mul) => {
                let left = Self::from_obj(&mul.left)?;
                let right = Self::from_obj(&mul.right)?;
                Ok(Self::new(
                    binary_expression(&left.expression, "*", &right.expression),
                    multiply_expression(&left.numerator, &right.numerator),
                    multiply_expression(&left.denominator, &right.denominator),
                ))
            }
            Obj::Div(div) => {
                let left = Self::from_obj(&div.left)?;
                let right = Self::from_obj(&div.right)?;
                Ok(Self::new(
                    binary_expression(&left.expression, "/", &right.expression),
                    multiply_expression(&left.numerator, &right.denominator),
                    multiply_expression(&left.denominator, &right.numerator),
                ))
            }
            Obj::Pow(pow) => {
                let base = Self::from_obj(&pow.base)?;
                let exponent = natural_exponent(&pow.exponent)?;
                Ok(Self::new(
                    format!("({} ^ {})", base.expression, exponent),
                    power_expression(&base.numerator, &exponent),
                    power_expression(&base.denominator, &exponent),
                ))
            }
            other => Err(rational_expression_error(format!(
                "Litex-to-Lean rational experiment does not support object `{}`",
                other
            ))),
        }
    }

    pub fn has_denominator(&self) -> bool {
        self.denominator != LEAN_ONE
    }

    pub fn fraction(&self) -> String {
        format!("{} / {}", self.numerator, self.denominator)
    }

    fn atom(expression: String) -> Self {
        Self::new(expression.clone(), expression, LEAN_ONE.to_string())
    }

    fn new(expression: String, numerator: String, denominator: String) -> Self {
        LeanRationalExpression {
            expression,
            numerator,
            denominator,
        }
    }
}

fn lean_atom_name(atom: &AtomObj) -> Result<String, RuntimeError> {
    let name = match atom {
        AtomObj::Identifier(identifier) => identifier.name.as_str(),
        AtomObj::Forall(parameter) => parameter.name.as_str(),
        AtomObj::Def(parameter) => parameter.name.as_str(),
        other => {
            return Err(rational_expression_error(format!(
                "Litex-to-Lean rational experiment does not support atom `{}`",
                other
            )));
        }
    };
    Ok(lean_name(name))
}

fn natural_exponent(obj: &Obj) -> Result<String, RuntimeError> {
    let Obj::Number(number) = obj else {
        return Err(rational_expression_error(format!(
            "Litex-to-Lean rational experiment requires a literal natural exponent; got `{}`",
            obj
        )));
    };
    if number.normalized_value.is_empty()
        || !number
            .normalized_value
            .chars()
            .all(|character| character.is_ascii_digit())
    {
        return Err(rational_expression_error(format!(
            "Litex-to-Lean rational experiment requires a literal natural exponent; got `{}`",
            number.normalized_value
        )));
    }
    Ok(number.normalized_value.clone())
}

fn binary_expression(left: &str, operator: &str, right: &str) -> String {
    format!("({} {} {})", left, operator, right)
}

fn add_expression(left: String, right: String) -> String {
    binary_expression(&left, "+", &right)
}

fn subtract_expression(left: String, right: String) -> String {
    binary_expression(&left, "-", &right)
}

fn multiply_expression(left: &str, right: &str) -> String {
    if left == LEAN_ONE {
        return right.to_string();
    }
    if right == LEAN_ONE {
        return left.to_string();
    }
    binary_expression(left, "*", right)
}

fn power_expression(base: &str, exponent: &str) -> String {
    if exponent == "0" || base == LEAN_ONE {
        return LEAN_ONE.to_string();
    }
    if exponent == "1" {
        return base.to_string();
    }
    format!("({} ^ {})", base, exponent)
}

pub(super) fn lean_name(name: &str) -> String {
    let mut output = String::new();
    for character in name.chars() {
        if character == '_' || character.is_ascii_alphanumeric() {
            output.push(character);
        } else {
            output.push('_');
        }
    }
    if output.is_empty() || output.starts_with(|character: char| character.is_ascii_digit()) {
        output.insert_str(0, "litex_");
    }
    if matches!(
        output.as_str(),
        "axiom"
            | "by"
            | "def"
            | "do"
            | "else"
            | "end"
            | "example"
            | "false"
            | "for"
            | "forall"
            | "fun"
            | "have"
            | "if"
            | "import"
            | "in"
            | "inductive"
            | "let"
            | "match"
            | "namespace"
            | "open"
            | "opaque"
            | "partial"
            | "private"
            | "protected"
            | "structure"
            | "theorem"
            | "then"
            | "true"
            | "where"
            | "with"
    ) {
        output.insert_str(0, "litex_");
    }
    output
}

fn rational_expression_error(message: impl Into<String>) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.into(),
        default_line_file(),
        None,
        vec![],
    ))
    .into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recursively_builds_numerator_and_denominator() {
        let a: Obj = Identifier::new("a".to_string()).into();
        let b: Obj = Identifier::new("b".to_string()).into();
        let x: Obj = Identifier::new("x".to_string()).into();

        let left: Obj = Div::new(Add::new(a.clone(), b.clone()).into(), x.clone()).into();
        let left = LeanRationalExpression::from_obj(&left).unwrap();
        assert_eq!(left.numerator, "(a + b)");
        assert_eq!(left.denominator, "x");

        let right: Obj =
            Add::new(Div::new(a, x.clone()).into(), Div::new(b, x.clone()).into()).into();
        let right = LeanRationalExpression::from_obj(&right).unwrap();
        assert_eq!(right.numerator, "((a * x) + (b * x))");
        assert_eq!(right.denominator, "(x * x)");
    }

    #[test]
    fn recursively_pushes_natural_power_into_fraction() {
        let a: Obj = Identifier::new("a".to_string()).into();
        let b: Obj = Identifier::new("b".to_string()).into();
        let two: Obj = Number::new("2".to_string()).into();
        let expression: Obj = Pow::new(Div::new(a, b).into(), two).into();

        let rational = LeanRationalExpression::from_obj(&expression).unwrap();
        assert_eq!(rational.numerator, "(a ^ 2)");
        assert_eq!(rational.denominator, "(b ^ 2)");
    }

    #[test]
    fn recursively_accumulates_left_associative_divisors() {
        let one: Obj = Number::new("1".to_string()).into();
        let two: Obj = Number::new("2".to_string()).into();
        let three: Obj = Number::new("3".to_string()).into();
        let four: Obj = Number::new("4".to_string()).into();
        let expression: Obj =
            Div::new(Div::new(Div::new(one, two).into(), three).into(), four).into();

        let rational = LeanRationalExpression::from_obj(&expression).unwrap();
        assert_eq!(rational.numerator, "(1 : ℝ)");
        assert_eq!(rational.denominator, "(((2 : ℝ) * (3 : ℝ)) * (4 : ℝ))");
    }
}
