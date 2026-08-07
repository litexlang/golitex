use crate::prelude::*;
use std::collections::{HashMap, HashSet};

use super::rational_expression::{lean_name, LeanRationalExpression};

pub fn to_lean(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let previous_mode = runtime.replace_to_lean_mode(true);
    let result = to_lean_in_mode(source_code, runtime);
    runtime.replace_to_lean_mode(previous_mode);
    result
}

fn to_lean_in_mode(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;
    let mut ir = Vec::new();

    for mut block in blocks {
        let statement = runtime.parse_stmt(&mut block)?;
        let result = run_stmt_at_global_env(&statement, runtime)?;
        if result.is_unknown() {
            return Err(to_lean_error(
                &statement.line_file(),
                "To-Lean received an unverified Litex statement",
            ));
        }
        let Some(statement_ir) = result.to_lean_ir() else {
            return Err(to_lean_error(
                &statement.line_file(),
                "To-Lean mode completed a statement without producing IR",
            ));
        };
        ir.push(statement_ir.clone());
    }

    if ir.is_empty() {
        return Err(to_lean_error(
            &default_line_file(),
            "To-Lean requires at least one supported statement",
        ));
    }

    emit_lean_from_ir(&ir)
}

pub fn to_lean_from_source(source_code: &str, entry_label: &str) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_lean(&normalized, &mut runtime)
}

/// Pure backend boundary: this function has no Runtime and cannot inspect raw
/// Litex statements or re-run proof search.
pub fn emit_lean_from_ir(ir: &[StmtToLeanIR]) -> Result<String, RuntimeError> {
    let mut emitter = LeanEmitter::new();
    for statement in ir {
        emitter.emit_statement(statement)?;
    }
    Ok(emitter.finish())
}

struct LeanEmitter {
    declarations: Vec<String>,
    emitted_fact_ids: HashSet<FactId>,
}

#[derive(Default)]
struct LeanProofContext {
    local_fact_names: HashMap<FactId, String>,
    nonzero_names: Vec<String>,
}

impl LeanEmitter {
    fn new() -> Self {
        LeanEmitter {
            declarations: Vec::new(),
            emitted_fact_ids: HashSet::new(),
        }
    }

    fn finish(self) -> String {
        format!(
            "import Mathlib\n\nnamespace LitexGenerated\n\nuniverse u\n\n-- Litex's primitive notion of a set.\nabbrev LitexSet := Type u\n\n-- Every generated proposition has this codomain.\nabbrev LitexFact := Prop\n\n{}\n\nend LitexGenerated",
            self.declarations.join("\n\n")
        )
    }

    fn emit_statement(&mut self, statement: &StmtToLeanIR) -> Result<(), RuntimeError> {
        match statement {
            StmtToLeanIR::AbstractProp(ir) => {
                self.declarations.push(lean_abstract_prop(ir));
                Ok(())
            }
            StmtToLeanIR::Prop(ir) => {
                self.declarations.push(lean_prop(ir)?);
                Ok(())
            }
            StmtToLeanIR::Trust(ir) => {
                for fact in ir.facts.iter() {
                    self.emit_trusted_fact(fact)?;
                }
                for fact in ir.inferred_facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                Ok(())
            }
            StmtToLeanIR::Fact(ir) => {
                self.emit_proved_fact(&ir.fact)?;
                for fact in ir.inferred_facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                Ok(())
            }
        }
    }

    fn emit_trusted_fact(&mut self, fact: &FactToLeanIR) -> Result<(), RuntimeError> {
        if !matches!(fact.proof, FactProofToLeanIR::Trusted) {
            return Err(to_lean_error(
                &fact.proposition.line_file(),
                "only an explicit Litex `trust` statement may emit a Lean axiom",
            ));
        }
        let fact_id = required_fact_id(fact)?;
        if !self.emitted_fact_ids.insert(fact_id) {
            return Ok(());
        }
        self.declarations.push(format!(
            "-- Litex trust boundary: {}\naxiom {} : {}",
            fact_id,
            lean_fact_name(fact_id),
            lean_fact(&fact.proposition)?
        ));
        Ok(())
    }

    fn emit_proved_fact(&mut self, fact: &FactToLeanIR) -> Result<(), RuntimeError> {
        let fact_id = required_fact_id(fact)?;
        if self.emitted_fact_ids.contains(&fact_id) {
            return Ok(());
        }
        if matches!(fact.proof, FactProofToLeanIR::Trusted) {
            return Err(to_lean_error(
                &fact.proposition.line_file(),
                "trusted evidence reached theorem emission outside a `trust` statement",
            ));
        }
        let proof =
            self.lean_proof(&fact.proposition, &fact.proof, &LeanProofContext::default())?;
        self.emitted_fact_ids.insert(fact_id);
        self.declarations.push(format!(
            "-- Litex stored fact {}\ntheorem {} : {} := {}",
            fact_id,
            lean_fact_name(fact_id),
            lean_fact(&fact.proposition)?,
            proof
        ));
        Ok(())
    }

    fn lean_proof(
        &self,
        proposition: &Fact,
        proof: &FactProofToLeanIR,
        context: &LeanProofContext,
    ) -> Result<String, RuntimeError> {
        match proof {
            FactProofToLeanIR::KnownFact { source_fact_id } => {
                let source = self.available_fact_name(*source_fact_id, proposition, context)?;
                Ok(format!("by\n  exact {}", source))
            }
            FactProofToLeanIR::KnownForall {
                source_fact_id,
                arguments,
                parameter_requirements: _,
                requirements,
            } => {
                let source = self.available_fact_name(*source_fact_id, proposition, context)?;
                let mut terms = vec![source];
                for argument in arguments {
                    terms.push(lean_obj(&argument.argument)?);
                }
                for requirement in requirements {
                    terms.push(self.lean_proof_term(requirement, context)?);
                }
                Ok(format!("by\n  exact {}", terms.join(" ")))
            }
            FactProofToLeanIR::Builtin {
                kind: BuiltinProofKindToLeanIR::Rule,
                rule: BuiltinRuleToLeanIR::RationalExpressionSimplification,
                subgoals,
            } if subgoals.is_empty() => lean_rational_builtin_proof(proposition, context),
            FactProofToLeanIR::Builtin { kind, rule, .. } => Err(to_lean_error(
                &proposition.line_file(),
                format!(
                    "To-Lean has no checked backend for {:?} builtin proof {:?}",
                    kind, rule
                ),
            )),
            FactProofToLeanIR::Definition { name } => {
                Ok(format!("by\n  simp [{}]", lean_name(name)))
            }
            FactProofToLeanIR::ForallIntroduction {
                parameter_assumptions: _,
                assumptions,
                conclusions,
            } => self.lean_forall_introduction(proposition, assumptions, conclusions),
            FactProofToLeanIR::Memo { proof } => self.lean_proof(proposition, proof, context),
            FactProofToLeanIR::Composite { steps } if steps.len() == 1 => {
                self.lean_proof(&steps[0].proposition, &steps[0].proof, context)
            }
            FactProofToLeanIR::UserStrategy { name } => Err(to_lean_error(
                &proposition.line_file(),
                format!("To-Lean does not yet lower user strategy `{}`", name),
            )),
            FactProofToLeanIR::Inference { reason, .. } => Err(to_lean_error(
                &proposition.line_file(),
                format!(
                    "To-Lean does not yet lower inferred fact origin `{}`",
                    reason
                ),
            )),
            FactProofToLeanIR::Unsupported { reason } => {
                Err(to_lean_error(&proposition.line_file(), reason.clone()))
            }
            FactProofToLeanIR::Trusted => Err(to_lean_error(
                &proposition.line_file(),
                "trusted proof cannot be emitted as a theorem",
            )),
            FactProofToLeanIR::Assumption => Err(to_lean_error(
                &proposition.line_file(),
                "a local assumption escaped its proof scope",
            )),
            FactProofToLeanIR::Composite { .. } => Err(to_lean_error(
                &proposition.line_file(),
                "To-Lean does not yet lower multi-step composite evidence",
            )),
        }
    }

    fn lean_proof_term(
        &self,
        fact: &FactToLeanIR,
        context: &LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if let Some(fact_id) = fact.fact_id {
            if let Some(local) = context.local_fact_names.get(&fact_id) {
                return Ok(local.clone());
            }
        }
        match &fact.proof {
            FactProofToLeanIR::KnownFact { source_fact_id } => {
                self.available_fact_name(*source_fact_id, &fact.proposition, context)
            }
            FactProofToLeanIR::KnownForall {
                source_fact_id,
                arguments,
                parameter_requirements: _,
                requirements,
            } => {
                let mut terms =
                    vec![self.available_fact_name(*source_fact_id, &fact.proposition, context)?];
                for argument in arguments {
                    terms.push(lean_obj(&argument.argument)?);
                }
                for requirement in requirements {
                    terms.push(self.lean_proof_term(requirement, context)?);
                }
                Ok(format!("({})", terms.join(" ")))
            }
            _ => Err(to_lean_error(
                &fact.proposition.line_file(),
                format!(
                    "nested proof {:?} for FactId {:?} does not yet have a Lean term backend",
                    fact.proof, fact.fact_id
                ),
            )),
        }
    }

    fn available_fact_name(
        &self,
        fact_id: FactId,
        proposition: &Fact,
        context: &LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if let Some(local_name) = context.local_fact_names.get(&fact_id) {
            return Ok(local_name.clone());
        }
        if self.emitted_fact_ids.contains(&fact_id) {
            return Ok(lean_fact_name(fact_id));
        }
        Err(to_lean_error(
            &proposition.line_file(),
            format!(
                "To-Lean proof references {} before that fact has a Lean declaration",
                fact_id
            ),
        ))
    }

    fn lean_forall_introduction(
        &self,
        proposition: &Fact,
        assumptions: &[FactToLeanIR],
        conclusions: &[FactToLeanIR],
    ) -> Result<String, RuntimeError> {
        let Fact::ForallFact(forall) = proposition else {
            return Err(to_lean_error(
                &proposition.line_file(),
                "forall-introduction evidence was attached to a non-forall proposition",
            ));
        };
        if conclusions.len() != 1 || forall.then_facts.len() != 1 {
            return Err(to_lean_error(
                &forall.line_file,
                "To-Lean MVP requires one conclusion in a forall proof",
            ));
        }

        let mut context = LeanProofContext::default();
        let mut intro_names = forall
            .params_def_with_type
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|binding| lean_name(binding.name())))
            .collect::<Vec<_>>();
        for (index, assumption) in assumptions.iter().enumerate() {
            let local_name = assumption
                .fact_id
                .map(lean_local_fact_name)
                .unwrap_or_else(|| format!("h_tmp_{}", index + 1));
            if let Some(fact_id) = assumption.fact_id {
                context.local_fact_names.insert(fact_id, local_name.clone());
            }
            if is_nonzero_fact(&assumption.proposition) {
                context.nonzero_names.push(local_name.clone());
            }
            intro_names.push(local_name);
        }
        let conclusion = &conclusions[0];
        let inner = self.lean_proof(&conclusion.proposition, &conclusion.proof, &context)?;
        let inner = inner.strip_prefix("by\n").unwrap_or(inner.as_str());
        Ok(format!("by\n  intro {}\n{}", intro_names.join(" "), inner))
    }
}

fn lean_abstract_prop(ir: &AbstractPropToLeanIR) -> String {
    let name = lean_name(&ir.name);
    if ir.params.is_empty() {
        return format!("opaque {} : LitexFact", name);
    }
    let type_names = ir
        .params
        .iter()
        .enumerate()
        .map(|(index, param)| format!("α_{}_{}", lean_name(param), index + 1))
        .collect::<Vec<_>>();
    format!(
        "opaque {} {{{} : Sort u}} : {} → LitexFact",
        name,
        type_names.join(" "),
        type_names.join(" → ")
    )
}

fn lean_prop(ir: &PropToLeanIR) -> Result<String, RuntimeError> {
    let binders = ir
        .params
        .iter()
        .map(|group| {
            Ok(format!(
                "({} : {})",
                group
                    .names
                    .iter()
                    .map(|name| lean_name(name))
                    .collect::<Vec<_>>()
                    .join(" "),
                lean_ir_param_type(&group.param_type)?
            ))
        })
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    let binder_text = if binders.is_empty() {
        String::new()
    } else {
        format!(" {}", binders.join(" "))
    };
    if ir.iff_facts.is_empty() {
        return Ok(format!(
            "opaque {}{} : LitexFact",
            lean_name(&ir.name),
            binder_text
        ));
    }
    let body = ir
        .iff_facts
        .iter()
        .map(lean_fact)
        .collect::<Result<Vec<_>, RuntimeError>>()?
        .join(" ∧ ");
    Ok(format!(
        "def {}{} : LitexFact := {}",
        lean_name(&ir.name),
        binder_text,
        parenthesize_if_many(&body, ir.iff_facts.len())
    ))
}

fn lean_ir_param_type(param_type: &ParamTypeToLeanIR) -> Result<&'static str, RuntimeError> {
    match param_type {
        ParamTypeToLeanIR::Real => Ok("ℝ"),
        ParamTypeToLeanIR::LitexSet => Ok("LitexSet"),
        ParamTypeToLeanIR::Rational
        | ParamTypeToLeanIR::Integer
        | ParamTypeToLeanIR::Natural
        | ParamTypeToLeanIR::LitexNonemptySet
        | ParamTypeToLeanIR::Unsupported(_) => Err(to_lean_error(
            &default_line_file(),
            format!("To-Lean does not support parameter type {:?}", param_type),
        )),
    }
}

fn lean_fact(fact: &Fact) -> Result<String, RuntimeError> {
    match fact {
        Fact::AtomicFact(atomic) => lean_atomic_fact(atomic),
        Fact::AndFact(and_fact) => Ok(parenthesized_join(
            and_fact
                .facts
                .iter()
                .map(lean_atomic_fact)
                .collect::<Result<Vec<_>, RuntimeError>>()?,
            " ∧ ",
        )),
        Fact::OrFact(or_fact) => Ok(parenthesized_join(
            or_fact
                .facts
                .iter()
                .map(|branch| lean_fact(&branch.clone().into()))
                .collect::<Result<Vec<_>, RuntimeError>>()?,
            " ∨ ",
        )),
        Fact::ForallFact(forall) => lean_forall_fact(forall),
        other => Err(to_lean_error(
            &other.line_file(),
            format!(
                "To-Lean proposition backend does not support `{}`",
                other.fact_type_string()
            ),
        )),
    }
}

fn lean_atomic_fact(fact: &AtomicFact) -> Result<String, RuntimeError> {
    match fact {
        AtomicFact::NormalAtomicFact(normal) => {
            lean_prop_application(&normal.predicate.to_string(), &normal.body, false)
        }
        AtomicFact::NotNormalAtomicFact(normal) => {
            lean_prop_application(&normal.predicate.to_string(), &normal.body, true)
        }
        AtomicFact::EqualFact(fact) => lean_binary_fact(&fact.left, "=", &fact.right),
        AtomicFact::NotEqualFact(fact) => lean_binary_fact(&fact.left, "≠", &fact.right),
        AtomicFact::LessFact(fact) => lean_binary_fact(&fact.left, "<", &fact.right),
        AtomicFact::LessEqualFact(fact) => lean_binary_fact(&fact.left, "≤", &fact.right),
        AtomicFact::GreaterFact(fact) => lean_binary_fact(&fact.left, ">", &fact.right),
        AtomicFact::GreaterEqualFact(fact) => lean_binary_fact(&fact.left, "≥", &fact.right),
        other => Err(to_lean_error(
            &other.line_file(),
            format!("To-Lean does not support atomic proposition `{}`", other),
        )),
    }
}

fn lean_prop_application(name: &str, args: &[Obj], negated: bool) -> Result<String, RuntimeError> {
    let mut application = lean_name(name);
    for arg in args {
        application.push(' ');
        application.push_str(&lean_obj(arg)?);
    }
    if negated {
        Ok(format!("¬ ({})", application))
    } else {
        Ok(application)
    }
}

fn lean_binary_fact(left: &Obj, operator: &str, right: &Obj) -> Result<String, RuntimeError> {
    Ok(format!(
        "{} {} {}",
        lean_obj(left)?,
        operator,
        lean_obj(right)?
    ))
}

fn lean_forall_fact(forall: &ForallFact) -> Result<String, RuntimeError> {
    let mut binders = Vec::new();
    for group in forall.params_def_with_type.groups.iter() {
        let names = group
            .params
            .iter()
            .map(|binding| lean_name(binding.name()))
            .collect::<Vec<_>>()
            .join(" ");
        binders.push(format!(
            "({} : {})",
            names,
            lean_param_type(&group.param_type)?
        ));
    }
    let conclusions = forall
        .then_facts
        .iter()
        .map(|fact| lean_fact(&fact.clone().to_fact()))
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    let mut body = parenthesized_join(conclusions, " ∧ ");
    for premise in forall.dom_facts.iter().rev() {
        body = format!("{} → {}", lean_fact(premise)?, body);
    }
    Ok(format!("∀ {}, {}", binders.join(" "), body))
}

fn lean_param_type(param_type: &ParamType) -> Result<&'static str, RuntimeError> {
    match param_type {
        ParamType::Obj(Obj::StandardSet(StandardSet::R)) => Ok("ℝ"),
        ParamType::Set(_) => Ok("LitexSet"),
        other => Err(to_lean_error(
            &default_line_file(),
            format!(
                "To-Lean does not support quantified parameter type `{}`",
                other
            ),
        )),
    }
}

fn lean_obj(obj: &Obj) -> Result<String, RuntimeError> {
    match obj {
        Obj::StandardSet(StandardSet::R) => Ok("ℝ".to_string()),
        Obj::StandardSet(StandardSet::Q) => Ok("ℚ".to_string()),
        Obj::StandardSet(StandardSet::Z) => Ok("ℤ".to_string()),
        Obj::StandardSet(StandardSet::N) => Ok("ℕ".to_string()),
        _ => LeanRationalExpression::from_obj(obj).map(|expression| expression.expression),
    }
}

fn lean_rational_builtin_proof(
    proposition: &Fact,
    context: &LeanProofContext,
) -> Result<String, RuntimeError> {
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = proposition else {
        return Err(to_lean_error(
            &proposition.line_file(),
            "rational-expression evidence was attached to a non-equality",
        ));
    };
    let left = LeanRationalExpression::from_obj(&equality.left)?;
    let right = LeanRationalExpression::from_obj(&equality.right)?;
    let closed_numeric =
        closed_rational_expression(&equality.left) && closed_rational_expression(&equality.right);
    let tactic = rational_tactic(&left, &right, closed_numeric, &context.nonzero_names);
    Ok(format!(
        "by\n  -- left recursive fraction: {}\n  -- right recursive fraction: {}\n  calc\n    {} = {} := by\n      {}\n    _ = {} := by\n      {}\n    _ = {} := by\n      {}",
        left.fraction(),
        right.fraction(),
        left.expression,
        left.fraction_expression(),
        tactic,
        right.fraction_expression(),
        tactic,
        right.expression,
        tactic
    ))
}

fn rational_tactic(
    left: &LeanRationalExpression,
    right: &LeanRationalExpression,
    closed_numeric: bool,
    nonzero_names: &[String],
) -> String {
    if closed_numeric {
        return "norm_num".to_string();
    }
    if !left.has_denominator() && !right.has_denominator() {
        return "ring".to_string();
    }
    let field_simp = if nonzero_names.is_empty() {
        "field_simp".to_string()
    } else {
        format!("field_simp [{}]", nonzero_names.join(", "))
    };
    format!(
        "solve\n        | {}\n        | {} <;> ring",
        field_simp, field_simp
    )
}

fn required_fact_id(fact: &FactToLeanIR) -> Result<FactId, RuntimeError> {
    fact.fact_id.ok_or_else(|| {
        to_lean_error(
            &fact.proposition.line_file(),
            "a top-level stored fact reached To-Lean without a FactId",
        )
    })
}

fn lean_fact_name(fact_id: FactId) -> String {
    format!("litex_fact_{}", fact_id.value())
}

fn lean_local_fact_name(fact_id: FactId) -> String {
    format!("h_f{}", fact_id.value())
}

fn is_nonzero_fact(fact: &Fact) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::NotEqualFact(_)))
}

fn parenthesized_join(items: Vec<String>, separator: &str) -> String {
    if items.len() == 1 {
        return items
            .into_iter()
            .next()
            .unwrap_or_else(|| "True".to_string());
    }
    format!("({})", items.join(separator))
}

fn parenthesize_if_many(body: &str, count: usize) -> String {
    if count > 1 {
        format!("({})", body)
    } else {
        body.to_string()
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn ordinary_runtime_does_not_return_to_lean_ir() {
        run_with_large_stack("ordinary_runtime_does_not_return_to_lean_ir", || {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("ordinary-runtime-ir-boundary");
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(
                    "1 + 1 = 2\n\n1 + 1 = 2\n\n2 + 2 = 4",
                    runtime.current_file_path_rc(),
                )
                .unwrap();
            let mut results = Vec::new();
            for mut block in blocks {
                let stmt = runtime.parse_stmt(&mut block).unwrap();
                results.push(run_stmt_at_global_env(&stmt, &mut runtime).unwrap());
            }

            let first_id = results[0].fact_id().expect("stored fact should have an ID");
            assert_eq!(results[1].fact_id(), Some(first_id));
            let VerifiedByResult::Fact(citation) =
                &results[1].factual_success().unwrap().verified_by
            else {
                panic!("repeated fact should cite the stored fact");
            };
            assert_eq!(citation.source_fact_id, Some(first_id));
            assert!(results[2].fact_id().expect("new fact should have an ID") > first_id);
            assert!(results.iter().all(|result| result.to_lean_ir().is_none()));
            assert!(!runtime.to_lean_mode());
        });
    }

    #[test]
    fn to_lean_mode_records_recursive_ir_and_emits_only_trust_as_axiom() {
        run_with_large_stack(
            "to_lean_mode_records_recursive_ir_and_emits_only_trust_as_axiom",
            || {
                let source = r#"
abstract_prop marked(x)

prop is_one(x R):
    x = 1

trust forall x R:
    x != 0
    =>:
        $marked(x)

$is_one(1)

forall x R:
    x != 0
    x < 10
    =>:
        $marked(x)

forall a, b, x R:
    x != 0
    =>:
        (a + b) / x = a / x + b / x

forall x R:
    x != 0
    =>:
        x != 0
"#;
                let output = to_lean_from_source(source, "to-lean-ir-mvp").unwrap();

                assert!(output.contains("abbrev LitexSet := Type u"));
                assert!(output.contains("abbrev LitexFact := Prop"));
                assert!(
                    output.find("abbrev LitexSet").unwrap()
                        < output.find("abbrev LitexFact").unwrap()
                );
                assert!(output.contains("opaque marked"));
                assert!(output.contains("def is_one (x : ℝ) : LitexFact :="));
                assert_eq!(output.matches("\naxiom litex_fact_").count(), 1);
                assert!(output.contains("exact litex_fact_"));
                assert!(output.contains(" (1 : ℝ)"));
                assert!(output.contains("simp [is_one]"));
                assert!(output.contains(" x h_f"));
                assert!(output.contains("intro a b x h_f"));
                assert!(output.contains("field_simp [h_f"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn to_lean_ir_preserves_fact_ids_and_verified_routes() {
        run_with_large_stack("to_lean_ir_preserves_fact_ids_and_verified_routes", || {
            let source = r#"
abstract_prop marked(x)

prop is_one(x R):
    x = 1

trust forall x R:
    x != 0
    =>:
        $marked(x)

$is_one(1)

forall x R:
    x != 0
    x < 10
    =>:
        $marked(x)

forall a, b, x R:
    x != 0
    =>:
        (a + b) / x = a / x + b / x
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("to-lean-ir-shape");
            runtime.replace_to_lean_mode(true);
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .unwrap();
            let mut statement_irs = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).unwrap();
                let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                statement_irs.push(result.to_lean_ir().unwrap().clone());
            }

            assert!(matches!(statement_irs[0], StmtToLeanIR::AbstractProp(_)));
            assert!(matches!(statement_irs[1], StmtToLeanIR::Prop(_)));
            let StmtToLeanIR::Trust(trust) = &statement_irs[2] else {
                panic!("third IR item should be trust");
            };
            let trusted_forall_id = trust.facts[0]
                .fact_id
                .expect("trusted fact must have an ID");
            assert!(matches!(trust.facts[0].proof, FactProofToLeanIR::Trusted));

            let StmtToLeanIR::Fact(by_definition) = &statement_irs[3] else {
                panic!("fourth IR item should be a fact");
            };
            assert!(matches!(
                underlying_test_proof(&by_definition.fact.proof),
                FactProofToLeanIR::Definition { name } if name == "is_one"
            ));

            let StmtToLeanIR::Fact(local_requirement_forall) = &statement_irs[4] else {
                panic!("fifth IR item should be a forall fact");
            };
            let FactProofToLeanIR::ForallIntroduction {
                assumptions,
                conclusions,
                ..
            } = &local_requirement_forall.fact.proof
            else {
                panic!("sixth fact should retain forall-introduction evidence");
            };
            assert_eq!(assumptions.len(), 2);
            let local_nonzero_id = assumptions[0].fact_id.expect("local nonzero FactId");
            let FactProofToLeanIR::KnownForall {
                source_fact_id,
                parameter_requirements,
                requirements,
                ..
            } = underlying_test_proof(&conclusions[0].proof)
            else {
                panic!("conclusion should retain known-forall evidence");
            };
            assert_eq!(*source_fact_id, trusted_forall_id);
            assert_eq!(parameter_requirements.len(), 1);
            assert_eq!(requirements.len(), 1);
            assert!(matches!(
                underlying_test_proof(&requirements[0].proof),
                FactProofToLeanIR::KnownFact { source_fact_id }
                    if *source_fact_id == local_nonzero_id
            ));

            let StmtToLeanIR::Fact(forall) = &statement_irs[5] else {
                panic!("sixth IR item should be a fact");
            };
            let FactProofToLeanIR::ForallIntroduction {
                parameter_assumptions,
                assumptions,
                conclusions,
            } = &forall.fact.proof
            else {
                panic!("last fact should retain forall-introduction evidence");
            };
            assert_eq!(parameter_assumptions.len(), 3);
            assert!(parameter_assumptions
                .iter()
                .all(|assumption| assumption.fact_id.is_some()));
            assert_eq!(assumptions.len(), 1);
            assert!(assumptions[0].fact_id.is_some());
            let forall_id = forall.fact.fact_id.expect("stored forall must have an ID");
            assert!(parameter_assumptions
                .iter()
                .chain(assumptions.iter())
                .all(|assumption| assumption.fact_id.expect("local fact ID") < forall_id));
            assert!(matches!(
                underlying_test_proof(&conclusions[0].proof),
                FactProofToLeanIR::Builtin {
                    rule: BuiltinRuleToLeanIR::RationalExpressionSimplification,
                    ..
                }
            ));
        });
    }

    #[test]
    fn closed_rational_builtin_is_emitted_from_ir() {
        run_with_large_stack("closed_rational_builtin_is_emitted_from_ir", || {
            let output = to_lean_from_source("1 / 2 / 3 / 4 = 1 / 24", "closed-ir").unwrap();

            assert!(output.contains("theorem litex_fact_1"));
            assert!(output
                .contains("-- left recursive fraction: (1 : ℝ) / (((2 : ℝ) * (3 : ℝ)) * (4 : ℝ))"));
            assert!(output.contains("norm_num"));
            assert!(!output.contains("sorry"));
        });
    }

    #[test]
    fn temporary_forall_assumption_is_emitted_as_local_exact() {
        run_with_large_stack(
            "temporary_forall_assumption_is_emitted_as_local_exact",
            || {
                let output = to_lean_from_source(
                    "forall x R:\n    x != 0\n    =>:\n        x != 0",
                    "temporary-local-fact",
                )
                .unwrap();

                assert!(output.contains("intro x h_f"));
                assert!(output.contains("exact h_f"));
                assert!(!output.contains("axiom"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn temporary_fact_id_survives_as_known_forall_domain_evidence() {
        run_with_large_stack(
            "temporary_fact_id_survives_as_known_forall_domain_evidence",
            || {
                let source = r#"
abstract_prop marked(x)

trust forall x R:
    x != 0
    =>:
        $marked(x)

forall x R:
    x != 0
    x < 10
    =>:
        $marked(x)
"#;
                let output = to_lean_from_source(source, "temporary-domain-evidence").unwrap();

                assert!(output.contains("intro x h_f"));
                assert!(output.contains("exact litex_fact_"));
                assert!(output.contains(" x h_f"));
                assert_eq!(output.matches("\naxiom litex_fact_").count(), 1);
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn preloaded_fact_id_without_ir_declaration_is_rejected() {
        run_with_large_stack(
            "preloaded_fact_id_without_ir_declaration_is_rejected",
            || {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("preloaded-fact-boundary");
                let tokenizer = Tokenizer::new();
                let mut blocks = tokenizer
                    .parse_blocks("trust 1 = 1", runtime.current_file_path_rc())
                    .unwrap();
                let mut block = blocks.remove(0);
                let statement = runtime.parse_stmt(&mut block).unwrap();
                run_stmt_at_global_env(&statement, &mut runtime).unwrap();

                let error = to_lean("1 = 1", &mut runtime)
                    .expect_err("a preloaded ID has no declaration in this emitted Lean module")
                    .trace_message();
                assert!(error.contains("before that fact has a Lean declaration"));
                assert!(!runtime.to_lean_mode());
            },
        );
    }

    #[test]
    fn unsupported_builtin_never_falls_back_to_axiom_or_sorry() {
        run_with_large_stack(
            "unsupported_builtin_never_falls_back_to_axiom_or_sorry",
            || {
                let error = to_lean_from_source("sin(0) = 0", "unsupported-builtin")
                    .expect_err("unsupported builtin must stop emission")
                    .trace_message();

                assert!(error.contains("no checked backend") || error.contains("does not support"));
            },
        );
    }

    #[test]
    fn unsupported_nested_requirement_builtin_is_rejected() {
        run_with_large_stack("unsupported_nested_requirement_builtin_is_rejected", || {
            let source = r#"
abstract_prop marked(x)

trust forall x R:
    x != 0
    =>:
        $marked(x)

$marked(1)
"#;
            let error = to_lean_from_source(source, "unsupported-nested-requirement")
                .expect_err("numeric nonzero requirement has no Lean backend yet")
                .trace_message();

            assert!(error.contains("does not yet have a Lean term backend"));
            assert!(error.contains("not_equal_numeric"));
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn generated_to_lean_mvp_compiles_with_lean() {
        run_with_large_stack("generated_to_lean_mvp_compiles_with_lean", || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
            let source = r#"
abstract_prop marked(x)

prop is_one(x R):
    x = 1

trust forall x R:
    x != 0
    =>:
        $marked(x)

$is_one(1)

forall x R:
    x != 0
    x < 10
    =>:
        $marked(x)

forall a, b, x R:
    x != 0
    =>:
        (a + b) / x = a / x + b / x

forall x R:
    x != 0
    =>:
        x != 0
"#;
            let generated = to_lean_from_source(source, "lean-kernel-mvp").unwrap();
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let lean_file = std::env::temp_dir().join(format!(
                "litex_to_lean_mvp_{}_{}.lean",
                std::process::id(),
                nonce
            ));
            fs::write(&lean_file, &generated).unwrap();
            let output = Command::new("lake")
                .args(["env", "lean"])
                .arg(&lean_file)
                .current_dir(project)
                .output()
                .unwrap();
            let _ = fs::remove_file(&lean_file);
            assert!(
                output.status.success(),
                "generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
                generated
            );
        });
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

    fn underlying_test_proof(mut proof: &FactProofToLeanIR) -> &FactProofToLeanIR {
        while let FactProofToLeanIR::Memo { proof: source } = proof {
            proof = source.as_ref();
        }
        proof
    }
}
