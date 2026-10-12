use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_fn_signature(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domains = self.compile_function_domains(signature, position)?;
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
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let parameters: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(|parameter| (parameter, &group.param_type))
            })
            .collect();
        if parameters.is_empty() || parameters.len() > 2 {
            return Err(LeanCompileError::unsupported("Function/Arity"));
        }
        let mut domains = Vec::new();
        for (index, (parameter, carrier)) in parameters.iter().enumerate() {
            if parameters[..index]
                .iter()
                .any(|(earlier, _)| earlier.id == parameter.id)
            {
                return Err(LeanCompileError::new(
                    "Function/ParameterIdentity",
                    "Function parameters must have distinct source identities.",
                ));
            }
            let set = self.compile_numeric_carrier(carrier, position)?;
            domains.push(format!(
                "Litex.StandardSetValue.{}",
                standard_value_constructor(&set)?
            ));
        }
        let set = self.compile_numeric_carrier(&signature.ret_set, position)?;
        domains.push(format!(
            "Litex.StandardSetValue.{}",
            standard_value_constructor(&set)?
        ));
        Ok(domains)
    }

    pub(in crate::compile_to_lean) fn compile_numeric_carrier(
        &self,
        carrier: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<StandardSet, LeanCompileError> {
        self.compile_numeric_carrier_alias(carrier, position)
    }

    fn compile_numeric_carrier_alias(
        &self,
        carrier: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<StandardSet, LeanCompileError> {
        if let Obj::StandardSet(set) = carrier {
            standard_term(set)?;
            return Ok(set.clone());
        }
        position.with_visible_alias(carrier, &mut |_, value, result, producer| {
            let wd = success_object_wd(result, value)?;
            self.compile_wd(wd, producer)?;
            self.compile_numeric_carrier_alias(value, producer)
        })?.ok_or_else(|| LeanCompileError::new(
            "Function/NumericCarrierProducer",
            "A numeric carrier needs its preceding original RHS/let alias producer, not an equality discovered from the final environment.",
        ))
    }

    pub(in crate::compile_to_lean) fn compile_function_guard_template(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_function_domains(signature, position)?;
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .map(|parameter| format!("(_raw_i{} : M.Value)", parameter.id.value()))
            .collect::<Vec<_>>();
        let mut guards = Vec::new();
        for fact in &signature.dom_facts {
            guards.push(self.compile_function_raw_clause(
                &function_guard_fact(fact)?,
                signature,
                position,
            )?);
        }
        let guard = guards
            .into_iter()
            .rev()
            .reduce(|tail, head| format!("({head} ∧ {tail})"))
            .unwrap_or_else(|| "True".into());
        Ok(format!("(fun {} => {guard})", parameters.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_function_body_template(
        &self,
        function: &AnonymousFn,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_function_domains(&function.body, position)?;
        let parameters = function
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .map(|parameter| format!("(_raw_i{} : M.Value)", parameter.id.value()))
            .collect::<Vec<_>>();
        let body =
            self.compile_function_raw_expression(&function.equal_to, &function.body, position)?;
        Ok(format!("(fun {} => {body})", parameters.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_function_raw_expression(
        &self,
        object: &Obj,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_function_raw_expression_bound(
            object,
            position,
            &function_raw_bindings(signature),
        )
    }

    fn compile_function_raw_expression_bound(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let expression =
            |object: &Obj| self.compile_function_raw_expression_bound(object, position, bindings);
        match object {
            Obj::Identifier(IdentifierObj::Plain { id, .. }) => {
                if let Some(value) = bindings.get(id) {
                    return Ok(value.clone());
                }
                Ok(format!(
                    "(Litex.denote {})",
                    self.compile_object_reference(object, position)?
                ))
            }
            Obj::Literal(Literal::Number(number)) => {
                Ok(format!("(M.number {})", number_literal(number, "ℂ")?))
            }
            Obj::StandardSet(set) => Ok(format!(
                "(M.standard Litex.StandardSetValue.{})",
                standard_value_constructor(set)?
            )),
            Obj::ArithmeticOperator(operator) => {
                let (name, left, right) = match operator {
                    ArithmeticOperator::Add(value) => ("addValue", &value.left, Some(&value.right)),
                    ArithmeticOperator::Sub(value) => ("subValue", &value.left, Some(&value.right)),
                    ArithmeticOperator::Mul(value) => ("mulValue", &value.left, Some(&value.right)),
                    ArithmeticOperator::Div(value) => ("divValue", &value.left, Some(&value.right)),
                    ArithmeticOperator::Pow(value) => {
                        ("powValue", &value.base, Some(&value.exponent))
                    }
                    ArithmeticOperator::Neg(value) => ("negValue", &value.arg, None),
                    _ => return Err(LeanCompileError::unsupported("Function/BodyOperator")),
                };
                let left = expression(left)?;
                let right = right
                    .map(|right| expression(right).map(|term| format!(" {term}")))
                    .transpose()?
                    .unwrap_or_default();
                Ok(format!("(M.{name} {left}{right})"))
            }
            Obj::FnObj(application) => {
                if application.body.len() != 1 || !(1..=2).contains(&application.body[0].len()) {
                    return Err(LeanCompileError::unsupported("Function/BodyCallArity"));
                }
                let FnObjHead::Identifier(identifier @ IdentifierObj::Plain { .. }) =
                    application.head.as_ref()
                else {
                    return Err(LeanCompileError::unsupported("Function/BodyCallHead"));
                };
                let object = Obj::Identifier(identifier.clone());
                self.validate_formula_head_producer(&object, position)?;
                let head = self.compile_object_reference(&object, position)?;
                let arguments = application.body[0]
                    .iter()
                    .map(|argument| expression(argument))
                    .collect::<Result<Vec<_>, _>>()?;
                let argument = if arguments.len() == 1 {
                    arguments[0].clone()
                } else {
                    format!(
                        "(Litex.FunctionSemantics.pairValue (M := M) {} {})",
                        arguments[0], arguments[1]
                    )
                };
                Ok(format!(
                    "(Litex.FunctionSemantics.callValue (M := M) (Litex.denote {head}) {argument})"
                ))
            }
            _ => Err(LeanCompileError::unsupported("Function/BodyObject")),
        }
    }

    fn validate_formula_head_producer(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = object {
            if position.visible_function(id).is_ok() {
                return Ok(());
            }
        }
        if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(_)) = object {
            return Ok(());
        }
        position.with_visible_alias(object, &mut |_, value, result, producer| {
            self.compile_wd(success_object_wd(result, value)?, producer)?;
            self.validate_formula_head_producer(value, producer)
        })?.ok_or_else(|| LeanCompileError::new("Function/BodyCallProducer", "The raw call must cite a preceding original formula-function constructor or its RHS/let alias."))
    }

    pub(in crate::compile_to_lean) fn compile_function_raw_clause(
        &self,
        fact: &Fact,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_function_raw_predicate(fact, position, &function_raw_bindings(signature))
    }

    fn compile_function_raw_predicate(
        &self,
        fact: &Fact,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let clauses = match fact {
            Fact::AtomicFact(fact) => {
                return self.compile_function_raw_fact_bound(fact, position, bindings)
            }
            Fact::AndFact(fact) => fact
                .facts
                .iter()
                .map(|atomic| self.compile_function_raw_fact_bound(atomic, position, bindings))
                .collect::<Result<Vec<_>, _>>()?,
            Fact::ChainFact(fact) => (0..fact.prop_names.len())
                .map(|index| {
                    // Pure proposition shape only: no new verification or citation identity.
                    let edge = crate::compile_to_lean::compile_compound_fact::chain_edge(
                        fact,
                        index,
                        fact.fact_id,
                    )?;
                    self.compile_function_raw_fact_bound(&edge, position, bindings)
                })
                .collect::<Result<Vec<_>, _>>()?,
            _ => {
                return Err(LeanCompileError::unsupported(
                    "Function/GuardPredicateClause",
                ))
            }
        };
        clauses
            .into_iter()
            .rev()
            .reduce(|tail, head| format!("({head} ∧ {tail})"))
            .ok_or_else(|| LeanCompileError::unsupported("Function/EmptyCompoundClause"))
    }

    fn compile_function_raw_fact_bound(
        &self,
        fact: &AtomicFact,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let arguments = atomic_fact_args_ref(fact)
            .iter()
            .map(|argument| {
                self.compile_function_raw_expression_bound(argument, position, bindings)
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.compile_atomic_raw_proposition(fact, &arguments, position)
    }

    /// Render this exact atomic shape over semantic argument values. Only the
    /// supplied original arguments change; concrete predicates use their prior
    /// captured definition and original binder identities, never a new proof route.
    pub(in crate::compile_to_lean) fn compile_atomic_raw_proposition(
        &self,
        fact: &AtomicFact,
        arguments: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if arguments.len() != atomic_fact_args_ref(fact).len() {
            return Err(LeanCompileError::new(
                "AtomicRaw/Arity",
                "The semantic argument values differ from the original atomic arity.",
            ));
        }
        Ok(match fact {
            AtomicFact::EqualFact(_) => format!("({} = {})", arguments[0], arguments[1]),
            AtomicFact::NotEqualFact(_) => format!("(¬ ({} = {}))", arguments[0], arguments[1]),
            AtomicFact::InFact(_) => format!("(M.mem {} {})", arguments[0], arguments[1]),
            AtomicFact::NotInFact(_) => format!("(¬ M.mem {} {})", arguments[0], arguments[1]),
            AtomicFact::IsSetFact(_) => format!("(M.isSet {})", arguments[0]),
            AtomicFact::IsNonemptySetFact(_) => {
                format!("(∃ _member : M.Value, M.mem _member {})", arguments[0])
            }
            AtomicFact::SubsetFact(_) => format!(
                "(∀ _member : M.Value, M.mem _member {} → M.mem _member {})",
                arguments[0], arguments[1]
            ),
            AtomicFact::LessFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                let reversed = matches!(
                    fact,
                    AtomicFact::GreaterFact(_) | AtomicFact::GreaterEqualFact(_)
                );
                let strict = matches!(fact, AtomicFact::LessFact(_) | AtomicFact::GreaterFact(_));
                let (left, right) = if reversed {
                    (&arguments[1], &arguments[0])
                } else {
                    (&arguments[0], &arguments[1])
                };
                format!("(∃ (_r _s : ℝ), {left} = M.number (_r : ℂ) ∧ {right} = M.number (_s : ℂ) ∧ _r {} _s)", if strict { "<" } else { "≤" })
            }
            AtomicFact::NormalAtomicFact(normal) => {
                let (definition, producer, _) = position.visible_prop(&normal.predicate)?;
                let parameters = definition
                    .statement
                    .typed_parameters
                    .groups
                    .iter()
                    .flat_map(|group| {
                        group
                            .params
                            .iter()
                            .map(|parameter| (parameter, &group.param_type))
                    })
                    .collect::<Vec<_>>();
                if parameters.len() != arguments.len() || definition.statement.iff_facts.is_empty()
                {
                    return Err(LeanCompileError::new(
                        "Function/GuardPredicateArity",
                        "The concrete predicate occurrence differs from its preceding definition.",
                    ));
                }
                // Temporary rendering substitutions; original WD and stores own evidence.
                let substituted = parameters
                    .iter()
                    .zip(arguments)
                    .map(|((parameter, _), argument)| (parameter.id, argument.clone()))
                    .collect::<HashMap<_, _>>();
                let mut clauses = Vec::new();
                for ((_, carrier), argument) in parameters.iter().zip(arguments) {
                    let ParamType::Obj(carrier) = carrier else {
                        return Err(LeanCompileError::unsupported(
                            "Function/GuardPredicateCarrier",
                        ));
                    };
                    self.compile_numeric_carrier(carrier, &producer)?;
                    clauses.push(format!(
                        "(M.mem {argument} {})",
                        self.compile_function_raw_expression_bound(
                            carrier,
                            &producer,
                            &substituted
                        )?
                    ));
                }
                for clause in &definition.statement.iff_facts {
                    clauses.push(self.compile_function_raw_predicate(
                        clause,
                        &producer,
                        &substituted,
                    )?);
                }
                let mut meaning = clauses.pop().expect("nonempty concrete clauses");
                for clause in clauses.into_iter().rev() {
                    meaning = format!("(∃ (_predicate_witness : {clause}), {meaning})");
                }
                meaning
            }
            _ => return Err(LeanCompileError::unsupported("Function/GuardPredicate")),
        })
    }
}

fn function_raw_bindings(signature: &FnSet) -> HashMap<IdentifierId, String> {
    signature
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|group| &group.params)
        .map(|parameter| (parameter.id, format!("_raw_i{}", parameter.id.value())))
        .collect()
}

pub(super) fn function_guard_fact(source: &QuantifierFreeFact) -> Result<Fact, LeanCompileError> {
    match source {
        QuantifierFreeFact::AtomicFact(fact) => Ok(Fact::AtomicFact(fact.clone())),
        QuantifierFreeFact::AndFact(fact) => Ok(Fact::AndFact(fact.clone())),
        QuantifierFreeFact::ChainFact(fact) => Ok(Fact::ChainFact(fact.clone())),
        QuantifierFreeFact::OrFact(_) => {
            Err(LeanCompileError::unsupported("Function/DisjunctiveGuard"))
        }
    }
}
