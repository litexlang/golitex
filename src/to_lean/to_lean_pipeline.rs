use crate::prelude::*;

use super::rational_expression::{lean_name, LeanRationalExpression};

pub fn to_lean(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;
    let mut declarations = Vec::new();

    for (index, mut block) in blocks.into_iter().enumerate() {
        let statement = runtime.parse_stmt(&mut block)?;
        let result = run_stmt_at_global_env(&statement, runtime)?;
        if result.is_unknown() {
            return Err(to_lean_error(
                &statement.line_file(),
                "To-Lean received an unverified Litex statement",
            ));
        }
        declarations.push(lean_declaration(&statement, index + 1)?);
    }

    if declarations.is_empty() {
        return Err(to_lean_error(
            &default_line_file(),
            "To-Lean rational experiment requires at least one equality",
        ));
    }

    Ok(format!(
        "import Mathlib\n\nnamespace LitexGenerated\n\n-- Experimental recursive rational-expression translation.\n{}\n\nend LitexGenerated",
        declarations.join("\n\n")
    ))
}

pub fn to_lean_from_source(source_code: &str, entry_label: &str) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_lean(&normalized, &mut runtime)
}

fn lean_declaration(statement: &Stmt, index: usize) -> Result<String, RuntimeError> {
    let Stmt::Fact(fact) = statement else {
        return Err(to_lean_error(
            &statement.line_file(),
            format!(
                "To-Lean rational experiment supports only equality facts; got `{}`",
                statement.stmt_type_name()
            ),
        ));
    };

    match fact {
        Fact::AtomicFact(AtomicFact::EqualFact(equality)) => {
            if !closed_rational_expression(&equality.left)
                || !closed_rational_expression(&equality.right)
            {
                return Err(to_lean_error(
                    &equality.line_file,
                    "To-Lean direct equalities must be closed rational expressions",
                ));
            }
            lean_equality_declaration(equality, index, String::new(), Vec::new(), true)
        }
        Fact::ForallFact(forall) => lean_forall_equality_declaration(forall, index),
        _ => Err(to_lean_error(
            &fact.line_file(),
            format!(
                "To-Lean rational experiment supports only equality facts; got `{}`",
                fact.fact_type_string()
            ),
        )),
    }
}

fn lean_forall_equality_declaration(
    forall: &ForallFact,
    index: usize,
) -> Result<String, RuntimeError> {
    let mut binder_parts = Vec::new();
    for group in forall.params_def_with_type.iter() {
        if !matches!(
            &group.param_type,
            ParamType::Obj(Obj::StandardSet(StandardSet::R))
        ) {
            return Err(to_lean_error(
                &forall.line_file,
                "To-Lean rational experiment supports only `R` parameters",
            ));
        }
        let names = group
            .params
            .iter()
            .map(|parameter| lean_name(parameter.name()))
            .collect::<Vec<_>>();
        binder_parts.push(format!("({} : ℝ)", names.join(" ")));
    }

    let mut nonzero_names = Vec::new();
    for (premise_index, premise) in forall.dom_facts.iter().enumerate() {
        let Fact::AtomicFact(AtomicFact::NotEqualFact(not_equal)) = premise else {
            return Err(to_lean_error(
                &premise.line_file(),
                "To-Lean rational experiment accepts only explicit nonzero premises",
            ));
        };
        let name = format!("h{}", premise_index + 1);
        if !forall_rational_expression(&not_equal.left)
            || !forall_rational_expression(&not_equal.right)
        {
            return Err(to_lean_error(
                &not_equal.line_file,
                "To-Lean universal premises may contain only their `R` parameters",
            ));
        }
        let left = LeanRationalExpression::from_obj(&not_equal.left)?;
        let right = LeanRationalExpression::from_obj(&not_equal.right)?;
        binder_parts.push(format!(
            "({} : {} ≠ {})",
            name, left.expression, right.expression
        ));
        nonzero_names.push(name);
    }

    if forall.then_facts.len() != 1 {
        return Err(to_lean_error(
            &forall.line_file,
            "To-Lean rational experiment requires exactly one equality conclusion",
        ));
    }
    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equality)) =
        &forall.then_facts[0]
    else {
        return Err(to_lean_error(
            &forall.then_facts[0].line_file(),
            "To-Lean rational experiment requires an equality conclusion",
        ));
    };
    if !forall_rational_expression(&equality.left) || !forall_rational_expression(&equality.right) {
        return Err(to_lean_error(
            &equality.line_file,
            "To-Lean universal conclusions may contain only their `R` parameters",
        ));
    }

    let binders = if binder_parts.is_empty() {
        String::new()
    } else {
        format!(" {}", binder_parts.join(" "))
    };
    lean_equality_declaration(equality, index, binders, nonzero_names, false)
}

fn lean_equality_declaration(
    equality: &EqualFact,
    index: usize,
    binders: String,
    nonzero_names: Vec<String>,
    closed_numeric: bool,
) -> Result<String, RuntimeError> {
    let left = LeanRationalExpression::from_obj(&equality.left)?;
    let right = LeanRationalExpression::from_obj(&equality.right)?;
    let tactic = if closed_numeric {
        "norm_num".to_string()
    } else if left.has_denominator() || right.has_denominator() {
        let field_simp = if nonzero_names.is_empty() {
            "field_simp".to_string()
        } else {
            format!("field_simp [{}]", nonzero_names.join(", "))
        };
        format!(
            "solve\n        | {}\n        | {} <;> ring",
            field_simp, field_simp
        )
    } else {
        "ring".to_string()
    };
    let left_fraction = left.fraction_expression();
    let right_fraction = right.fraction_expression();

    Ok(format!(
        "-- left recursive fraction: {}\n-- right recursive fraction: {}\ntheorem litex_rational_{}{} : {} = {} := by\n  calc\n    {} = {} := by\n      {}\n    _ = {} := by\n      {}\n    _ = {} := by\n      {}",
        left.fraction(),
        right.fraction(),
        index,
        binders,
        left.expression,
        right.expression,
        left.expression,
        left_fraction,
        tactic,
        right_fraction,
        tactic,
        right.expression,
        tactic
    ))
}

fn to_lean_error(line_file: &LineFile, message: impl Into<String>) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.into(),
        line_file.clone(),
        None,
        vec![],
    ))
    .into()
}

fn closed_rational_expression(obj: &Obj) -> bool {
    match obj {
        Obj::Number(_) => true,
        Obj::Add(add) => {
            closed_rational_expression(&add.left) && closed_rational_expression(&add.right)
        }
        Obj::Sub(sub) => {
            closed_rational_expression(&sub.left) && closed_rational_expression(&sub.right)
        }
        Obj::Mul(mul) => {
            closed_rational_expression(&mul.left) && closed_rational_expression(&mul.right)
        }
        Obj::Div(div) => {
            closed_rational_expression(&div.left) && closed_rational_expression(&div.right)
        }
        Obj::Pow(pow) => {
            closed_rational_expression(&pow.base) && matches!(pow.exponent.as_ref(), Obj::Number(_))
        }
        _ => false,
    }
}

fn forall_rational_expression(obj: &Obj) -> bool {
    match obj {
        Obj::Number(_) | Obj::Atom(AtomObj::Forall(_)) => true,
        Obj::Add(add) => {
            forall_rational_expression(&add.left) && forall_rational_expression(&add.right)
        }
        Obj::Sub(sub) => {
            forall_rational_expression(&sub.left) && forall_rational_expression(&sub.right)
        }
        Obj::Mul(mul) => {
            forall_rational_expression(&mul.left) && forall_rational_expression(&mul.right)
        }
        Obj::Div(div) => {
            forall_rational_expression(&div.left) && forall_rational_expression(&div.right)
        }
        Obj::Pow(pow) => {
            forall_rational_expression(&pow.base) && matches!(pow.exponent.as_ref(), Obj::Number(_))
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tracer_uses_recursive_fraction_then_field_simp_and_ring() {
        run_with_large_stack(
            "tracer_uses_recursive_fraction_then_field_simp_and_ring",
            || {
                let source = r#"
forall a, b, x R:
    x != 0
    =>:
        (a + b) / x = a / x + b / x
"#;
                let output = to_lean_from_source(source, "to-lean-rational-tracer").unwrap();

                assert!(output.contains("-- left recursive fraction: (a + b) / x"));
                assert!(
                    output.contains("-- right recursive fraction: ((a * x) + (b * x)) / (x * x)")
                );
                assert!(output.contains("(a b x : ℝ) (h1 : x ≠ (0 : ℝ))"));
                assert!(output.contains("field_simp [h1] <;> ring"));
                assert!(output.contains("\n  calc\n"));
                assert!(output.contains("_ = (((a * x) + (b * x)) / (x * x)) := by"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn polynomial_identity_uses_ring_directly() {
        run_with_large_stack("polynomial_identity_uses_ring_directly", || {
            let source = r#"
forall a, b R:
    (a + b)^2 = a^2 + 2 * a * b + b^2
"#;
            let output = to_lean_from_source(source, "to-lean-ring-tracer").unwrap();

            assert!(output.contains("theorem litex_rational_1 (a b : ℝ)"));
            assert!(output.contains("\n      ring\n"));
            assert!(!output.contains("field_simp"));
        });
    }

    #[test]
    fn closed_numeric_equality_keeps_the_public_interface() {
        run_with_large_stack("closed_numeric_equality_keeps_the_public_interface", || {
            let output = to_lean_from_source("1 + 1 = 2", "to-lean-closed-test").unwrap();

            assert!(output.starts_with("import Mathlib"));
            assert!(output.contains("theorem litex_rational_1"));
            assert!(output.ends_with("end LitexGenerated"));
        });
    }

    #[test]
    fn chained_numeric_division_reaches_the_recursive_fraction_pipeline() {
        run_with_large_stack(
            "chained_numeric_division_reaches_the_recursive_fraction_pipeline",
            || {
                let output = to_lean_from_source(
                    "1 / 2 / 3 / 4 = 1 / 24",
                    "to-lean-chained-division-tracer",
                )
                .unwrap();

                assert!(output.contains(
                    "-- left recursive fraction: (1 : ℝ) / (((2 : ℝ) * (3 : ℝ)) * (4 : ℝ))"
                ));
                assert!(output.contains("-- right recursive fraction: (1 : ℝ) / (24 : ℝ)"));
                assert!(output.contains("theorem litex_rational_1"));
                assert!(output.contains("\n      norm_num\n"));
                assert!(!output.contains("field_simp"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn rejects_non_rational_objects() {
        run_with_large_stack("rejects_non_rational_objects", || {
            let error = to_lean_from_source("sin(0) = 0", "to-lean-boundary-test")
                .expect_err("trigonometry is outside the rational experiment")
                .trace_message();

            assert!(
                error.contains("direct equalities must be closed rational expressions"),
                "{error}"
            );
        });
    }

    #[test]
    fn rejects_a_symbolic_denominator_without_nonzero_evidence() {
        run_with_large_stack(
            "rejects_a_symbolic_denominator_without_nonzero_evidence",
            || {
                let source = r#"
forall a, x R:
    a / x = a / x
"#;
                let result = to_lean_from_source(source, "to-lean-nonzero-boundary-test");

                assert!(result.is_err());
            },
        );
    }

    fn run_with_large_stack(test_name: &str, action: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name(test_name.to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(action)
            .unwrap()
            .join()
            .unwrap();
    }
}
