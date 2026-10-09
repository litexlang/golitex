use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_fn_signature(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domains = self.compile_function_domains(signature)?;
        let guard = self.compile_function_guard_template(signature, position)?;
        let constructor = if domains.len() == 2 { "one" } else { "two" };
        Ok(format!(
            "(Litex.FunctionSignature.{constructor} (M := M) {} {guard})",
            domains.join(" ")
        ))
    }

    pub(in crate::compile_to_lean) fn compile_function_domains(
        &self,
        signature: &FnSet,
    ) -> Result<Vec<String>, LeanCompileError> {
        let parameters: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|parameter| (parameter, &group.param_type)))
            .collect();
        if parameters.is_empty() || parameters.len() > 2 {
            return Err(LeanCompileError::unsupported("Function/Arity"));
        }
        let mut domains = Vec::new();
        for (index, (parameter, carrier)) in parameters.iter().enumerate() {
            if parameters[..index].iter().any(|(earlier, _)| earlier.id == parameter.id) {
                return Err(LeanCompileError::new(
                    "Function/ParameterIdentity",
                    "Function parameters must have distinct source identities.",
                ));
            }
            let Obj::StandardSet(set) = carrier.as_ref() else {
                return Err(LeanCompileError::unsupported("Function/ParameterCarrier"));
            };
            domains.push(format!("Litex.StandardSetValue.{}", standard_value_constructor(set)?));
        }
        let Obj::StandardSet(set) = signature.ret_set.as_ref() else {
            return Err(LeanCompileError::unsupported("Function/ReturnCarrier"));
        };
        domains.push(format!("Litex.StandardSetValue.{}", standard_value_constructor(set)?));
        Ok(domains)
    }

    pub(in crate::compile_to_lean) fn compile_function_guard_template(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_function_domains(signature)?;
        let parameters = signature.set_bound_parameters.groups.iter()
            .flat_map(|group| &group.params)
            .map(|parameter| format!("(_raw_i{} : M.Value)", parameter.id.value()))
            .collect::<Vec<_>>();
        let mut guards = Vec::new();
        for fact in &signature.dom_facts {
            let QuantifierFreeFact::AtomicFact(fact) = fact else {
                return Err(LeanCompileError::unsupported("Function/CompoundGuard"));
            };
            guards.push(self.compile_function_raw_fact(fact, signature, position)?);
        }
        let guard = guards.into_iter().rev().reduce(|tail, head| format!("({head} ∧ {tail})"))
            .unwrap_or_else(|| "True".into());
        Ok(format!("(fun {} => {guard})", parameters.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_function_body_template(
        &self,
        function: &AnonymousFn,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_function_domains(&function.body)?;
        let parameters = function.body.set_bound_parameters.groups.iter()
            .flat_map(|group| &group.params)
            .map(|parameter| format!("(_raw_i{} : M.Value)", parameter.id.value()))
            .collect::<Vec<_>>();
        let body = self.compile_function_raw_expression(&function.equal_to, &function.body, position)?;
        Ok(format!("(fun {} => {body})", parameters.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_function_raw_expression(
        &self,
        object: &Obj,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match object {
            Obj::Identifier(IdentifierObj::Plain { id, .. }) => {
                if signature.set_bound_parameters.groups.iter().flat_map(|group| &group.params)
                    .any(|parameter| parameter.id == *id) {
                    Ok(format!("_raw_i{}", id.value()))
                } else {
                    Ok(format!("(Litex.denote {})", self.compile_object_reference(object, position)?))
                }
            }
            Obj::Literal(Literal::Number(number)) =>
                Ok(format!("(M.number {})", number_literal(number, "ℂ")?)),
            Obj::StandardSet(set) =>
                Ok(format!("(M.standard Litex.StandardSetValue.{})", standard_value_constructor(set)?)),
            Obj::ArithmeticOperator(operator) => {
                let (name, left, right) = match operator {
                    ArithmeticOperator::Add(value) => ("addValue", &value.left, Some(&value.right)),
                    ArithmeticOperator::Sub(value) => ("subValue", &value.left, Some(&value.right)),
                    ArithmeticOperator::Mul(value) => ("mulValue", &value.left, Some(&value.right)),
                    ArithmeticOperator::Div(value) => ("divValue", &value.left, Some(&value.right)),
                    ArithmeticOperator::Pow(value) => ("powValue", &value.base, Some(&value.exponent)),
                    ArithmeticOperator::Neg(value) => ("negValue", &value.arg, None),
                    _ => return Err(LeanCompileError::unsupported("Function/BodyOperator")),
                };
                let left = self.compile_function_raw_expression(left, signature, position)?;
                let right = match right {
                    Some(right) => format!(" {}", self.compile_function_raw_expression(right, signature, position)?),
                    None => String::new(),
                };
                Ok(format!("(M.{name} {left}{right})"))
            }
            _ => Err(LeanCompileError::unsupported("Function/BodyObject")),
        }
    }

    pub(in crate::compile_to_lean) fn compile_function_raw_fact(
        &self,
        fact: &AtomicFact,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let compiled = match fact {
            AtomicFact::EqualFact(value) => format!("({} = {})",
                self.compile_function_raw_expression(&value.left, signature, position)?,
                self.compile_function_raw_expression(&value.right, signature, position)?),
            AtomicFact::NotEqualFact(value) => format!("(¬ ({} = {}))",
                self.compile_function_raw_expression(&value.left, signature, position)?,
                self.compile_function_raw_expression(&value.right, signature, position)?),
            AtomicFact::InFact(value) => format!("(M.mem {} {})",
                self.compile_function_raw_expression(&value.element, signature, position)?,
                self.compile_function_raw_expression(&value.set, signature, position)?),
            AtomicFact::NotInFact(value) => format!("(¬ M.mem {} {})",
                self.compile_function_raw_expression(&value.element, signature, position)?,
                self.compile_function_raw_expression(&value.set, signature, position)?),
            AtomicFact::LessFact(_) | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterFact(_) | AtomicFact::GreaterEqualFact(_) => {
                let (left, right, strict) = source_order_oriented(fact)?;
                format!("(∃ (_r _s : ℝ), {} = M.number (_r : ℂ) ∧ {} = M.number (_s : ℂ) ∧ _r {} _s)",
                    self.compile_function_raw_expression(left, signature, position)?,
                    self.compile_function_raw_expression(right, signature, position)?,
                    if strict { "<" } else { "≤" })
            }
            _ => return Err(LeanCompileError::unsupported("Function/GuardPredicate")),
        };
        Ok(compiled)
    }
}
