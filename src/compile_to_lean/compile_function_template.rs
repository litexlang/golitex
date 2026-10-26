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
        if !Self::function_uses_numeric_interface(signature) {
            let (domain, domain_set) = self.compile_function_base_domain(signature, position)?;
            let output = self.compile_object_reference(&signature.ret_set, position)?;
            let guard = self.compile_function_packed_guard_template(signature, position)?;
            return Ok(format!(
                "(let _litex_output := {output}; Litex.FunctionSignature.withGuard (M := M) {domain} (Litex.denote _litex_output) {domain_set} (Litex.isSet _litex_output) {guard})"
            ));
        }
        let domains = self.compile_function_domains(signature, position)?;
        let guard = self.compile_function_guard_template(signature, position)?;
        let (arguments, target) =
            self.compile_function_constructor_arguments(signature, position)?;
        let constructor = match (domains.len() == 2, target) {
            (true, false) => "one",
            (false, false) => "two",
            (true, true) => "oneTarget",
            (false, true) => "twoTarget",
        };
        Ok(format!(
            "(Litex.FunctionSignature.{constructor} (M := M) {arguments} {guard})"
        ))
    }

    pub(in crate::compile_to_lean) fn function_uses_numeric_interface(signature: &FnSet) -> bool {
        let numeric_carrier = |object: &Obj| {
            matches!(
                object,
                Obj::StandardSet(
                    StandardSet::N
                        | StandardSet::Z
                        | StandardSet::Q
                        | StandardSet::R
                        | StandardSet::C
                        | StandardSet::RPos
                )
            )
        };
        let count: usize = signature
            .set_bound_parameters
            .groups
            .iter()
            .map(|group| group.params.len())
            .sum();
        (1..=2).contains(&count)
            && signature
                .set_bound_parameters
                .groups
                .iter()
                .all(|group| numeric_carrier(&group.param_type))
            && numeric_carrier(&signature.ret_set)
    }

    pub(in crate::compile_to_lean) fn compile_function_input_sets(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut identities = Vec::new();
        let mut sets = Vec::new();
        for group in &signature.set_bound_parameters.groups {
            let set = self.compile_object_reference(&group.param_type, position)?;
            for parameter in &group.params {
                if identities.contains(&parameter.id) {
                    return Err(LeanCompileError::new(
                        "Function/ParameterIdentity",
                        "Function parameters repeat a source identity.",
                    ));
                }
                identities.push(parameter.id);
                sets.push(set.clone());
            }
        }
        if !(1..=3).contains(&sets.len()) {
            return Err(LeanCompileError::unsupported("Function/Arity"));
        }
        Ok(sets)
    }

    pub(in crate::compile_to_lean) fn compile_function_semantic_base_domain(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        if !Self::function_uses_numeric_interface(signature) {
            return self.compile_function_base_domain(signature, position);
        }
        let mut domains = self.compile_function_domains(signature, position)?;
        domains.pop();
        let values: Vec<_> = domains
            .iter()
            .map(|d| format!("(M.standard {d})"))
            .collect();
        let proofs: Vec<_> = domains
            .iter()
            .map(|d| format!("(M.standard_isSet {d})"))
            .collect();
        if values.len() == 1 {
            return Ok((values[0].clone(), proofs[0].clone()));
        }
        let vector = format!("![{}]", values.join(", "));
        Ok((
            format!("(Litex.FiniteFunction.cartValue (M := M) {vector})"),
            format!(
                "(Litex.FiniteFunction.cart_isSet (M := M) {vector} {})",
                finite_vector_proof(&proofs)
            ),
        ))
    }

    pub(in crate::compile_to_lean) fn compile_function_base_domain(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let sets = self.compile_function_input_sets(signature, position)?;
        if sets.len() == 1 {
            return Ok((
                format!("(Litex.denote {})", sets[0]),
                format!("(Litex.isSet {})", sets[0]),
            ));
        }
        let values = format!(
            "![{}]",
            sets.iter()
                .map(|set| format!("(Litex.denote {set})"))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let proofs = sets
            .iter()
            .map(|set| format!("Litex.isSet {set}"))
            .collect::<Vec<_>>();
        let proofs = finite_vector_proof(&proofs);
        Ok((
            format!("(Litex.FiniteFunction.cartValue (M := M) {values})"),
            format!("(Litex.FiniteFunction.cart_isSet (M := M) {values} {proofs})"),
        ))
    }

    pub(in crate::compile_to_lean) fn compile_function_packed_values(
        &self,
        signature: &FnSet,
        input: &str,
    ) -> Result<Vec<String>, LeanCompileError> {
        let count: usize = signature
            .set_bound_parameters
            .groups
            .iter()
            .map(|group| group.params.len())
            .sum();
        if !(1..=3).contains(&count) {
            return Err(LeanCompileError::unsupported("Function/Arity"));
        }
        if count == 1 {
            return Ok(vec![input.to_string()]);
        }
        Ok((1..=count)
            .map(|index| {
                format!(
                    "(Litex.FunctionSemantics.callValue (M := M) {input} (M.number ({index} : ℂ)))"
                )
            })
            .collect())
    }

    pub(in crate::compile_to_lean) fn compile_function_packed_guard_template(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let guard = self.compile_function_guard_template(signature, position)?;
        let values = self.compile_function_packed_values(signature, "_litex_input")?;
        Ok(format!(
            "(fun (_litex_input : M.Value) => {guard} {})",
            values.join(" ")
        ))
    }

    pub(in crate::compile_to_lean) fn compile_function_packed_reduction_laws(
        &self,
        values: &[String],
    ) -> Result<Vec<String>, LeanCompileError> {
        if !(1..=3).contains(&values.len()) {
            return Err(LeanCompileError::unsupported("Function/Arity"));
        }
        if values.len() == 1 {
            return Ok(Vec::new());
        }
        let vector = format!("![{}]", values.join(", "));
        Ok(values.iter().enumerate().map(|(index, value)| format!(
            "(show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue {vector}) (M.number ({} : ℂ)) = {value} from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple {vector} ({index} : Fin {}))",
            index + 1, values.len()
        )).collect())
    }

    pub(in crate::compile_to_lean) fn compile_function_packed_application_equality(
        &self,
        template: &str,
        values: &[String],
    ) -> Result<String, LeanCompileError> {
        let laws = self.compile_function_packed_reduction_laws(values)?;
        Ok(match laws.as_slice() {
            [] => "rfl".into(),
            [first, second] => format!("(congrArg₂ {template} {first} {second})"),
            [first, second, third] => format!(
                "(congrArg₂ (fun _f _x => _f _x) (congrArg₂ {template} {first} {second}) {third})"
            ),
            _ => return Err(LeanCompileError::unsupported("Function/Arity")),
        })
    }

    pub(in crate::compile_to_lean) fn compile_function_packed_body_template(
        &self,
        function: &AnonymousFn,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let body = self.compile_function_body_template(function, position)?;
        let values = self.compile_function_packed_values(&function.body, "_litex_input")?;
        Ok(format!(
            "(fun (_litex_input : M.Value) => {body} {})",
            values.join(" ")
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
            let set = if set == StandardSet::RPos {
                StandardSet::R
            } else {
                set
            };
            domains.push(format!(
                "Litex.StandardSetValue.{}",
                standard_value_constructor(&set)?
            ));
        }
        let set = self.compile_numeric_carrier(&signature.ret_set, position)?;
        let set = if set == StandardSet::RPos {
            StandardSet::R
        } else {
            set
        };
        domains.push(format!(
            "Litex.StandardSetValue.{}",
            standard_value_constructor(&set)?
        ));
        Ok(domains)
    }

    pub(in crate::compile_to_lean) fn compile_function_constructor_arguments(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<(String, bool), LeanCompileError> {
        let mut domains = self.compile_function_domains(signature, position)?;
        let target =
            self.compile_numeric_carrier(&signature.ret_set, position)? == StandardSet::RPos;
        if target {
            domains.pop();
            let object = self.compile_object_reference(&signature.ret_set, position)?;
            domains.push(format!("(Litex.denote {object})"));
            domains.push(format!("(Litex.isSet {object})"));
        }
        Ok((domains.join(" "), target))
    }

    pub(in crate::compile_to_lean) fn compile_function_positive_inputs(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<IdentifierId>, LeanCompileError> {
        if !Self::function_uses_numeric_interface(signature) {
            return Ok(Vec::new());
        }
        let mut positive = Vec::new();
        for group in &signature.set_bound_parameters.groups {
            if self.compile_numeric_carrier(&group.param_type, position)? == StandardSet::RPos {
                positive.extend(group.params.iter().map(|parameter| parameter.id));
            }
        }
        Ok(positive)
    }

    pub(in crate::compile_to_lean) fn compile_function_domain_certificates(
        &self,
        signature: &FnSet,
        arguments: &[String],
        requirements: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String), LeanCompileError> {
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .collect::<Vec<_>>();
        if arguments.len() != parameters.len()
            || requirements.len() != parameters.len() + signature.dom_facts.len()
        {
            return Err(LeanCompileError::new(
                "Function/DomainCertificates",
                "The exact call must retain each ordered input and explicit guard certificate.",
            ));
        }
        let positive = self.compile_function_positive_inputs(signature, position)?;
        let mut members = requirements[..parameters.len()].to_vec();
        let mut guards = Vec::new();
        for (index, parameter) in parameters.iter().enumerate() {
            if positive.contains(&parameter.id) {
                let original = &requirements[index];
                let argument = &arguments[index];
                members[index] = format!("(Litex.inRPos_real {argument} {original})");
                guards.push(format!("((Litex.positiveReal_members (M := M) (Litex.denote {argument})).mp {original}).2"));
            }
        }
        guards.extend_from_slice(&requirements[parameters.len()..]);
        let guard = guards
            .into_iter()
            .rev()
            .reduce(|tail, head| format!("(And.intro {head} {tail})"))
            .unwrap_or_else(|| "True.intro".into());
        Ok((members, guard))
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
        self.compile_function_guard_template_bound(
            signature,
            position,
            &function_raw_bindings(signature),
        )
    }

    pub(super) fn compile_function_guard_template_bound(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        if Self::function_uses_numeric_interface(signature) {
            self.compile_function_domains(signature, position)?;
        }
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .map(|parameter| format!("(_raw_i{} : M.Value)", parameter.id.value()))
            .collect::<Vec<_>>();
        let mut guards = self
            .compile_function_positive_inputs(signature, position)?
            .iter()
            .map(|id| {
                format!(
                    "(Litex.positiveRealPredicate (M := M) _raw_i{})",
                    id.value()
                )
            })
            .collect::<Vec<_>>();
        for fact in &signature.dom_facts {
            guards.push(self.compile_function_raw_predicate(
                &function_guard_fact(fact)?,
                position,
                bindings,
            )?);
        }
        let guard = guards
            .into_iter()
            .rev()
            .reduce(|tail, head| format!("(({head}) ∧ ({tail}))"))
            .unwrap_or_else(|| "True".into());
        Ok(format!("(fun {} => {guard})", parameters.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_function_body_template(
        &self,
        function: &AnonymousFn,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if Self::function_uses_numeric_interface(&function.body) {
            self.compile_function_domains(&function.body, position)?;
        }
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

    pub(in crate::compile_to_lean) fn compile_function_raw_expression_bound(
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
            Obj::Literal(Literal::ImaginaryUnit(_)) => Ok("(M.number Complex.I)".into()),
            Obj::Literal(Literal::EulerNumber(_)) => Ok("(M.number ((Real.exp 1 : ℝ) : ℂ))".into()),
            Obj::Literal(Literal::Pi(_)) => Ok("(M.number (Real.pi : ℂ))".into()),
            Obj::StandardSet(StandardSet::RPos) => Ok("(Litex.positiveReal (M := M))".into()),
            Obj::StandardSet(set)
                if *set == StandardSet::NPos || numeric_refinement(set).is_some() =>
            {
                Ok(format!("(Litex.denote {})", standard_term(set)?))
            }
            Obj::StandardSet(set) => Ok(format!(
                "(M.standard Litex.StandardSetValue.{})",
                standard_value_constructor(set)?
            )),
            Obj::ProductShape(shape) => {
                let (constructor, children) = match shape {
                    ProductShape::Cart(value) => ("cartValue", &value.args),
                    ProductShape::Tuple(value) => ("tupleValue", &value.args),
                };
                let values = children
                    .iter()
                    .map(|child| expression(child))
                    .collect::<Result<Vec<_>, _>>()?;
                let vector = if values.is_empty() {
                    "(fun i : Fin 0 => Fin.elim0 i)".to_string()
                } else {
                    format!("![{}]", values.join(", "))
                };
                Ok(format!(
                    "(Litex.FiniteFunction.{constructor} (M := M) {vector})"
                ))
            }
            Obj::SetFormer(SetFormer::ListSet(value)) => {
                let values = value
                    .list
                    .iter()
                    .map(|child| expression(child))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(values.into_iter().rev().fold(
                    "(Litex.SetSemantics.emptyValue (M := M))".to_string(),
                    |tail, value| format!("(Litex.SetSemantics.insertValue {value} {tail})"),
                ))
            }
            Obj::SetFormer(SetFormer::SetBuilder(value)) => {
                let bound = expression(&value.param_set)?;
                let variable = format!("_raw_i{}", value.param_binding.id.value());
                let mut inner = bindings.clone();
                inner.insert(value.param_binding.id, variable.clone());
                let mut clauses = Vec::new();
                for clause in &value.facts {
                    let fact = function_guard_fact(clause)?;
                    clauses.push((
                        fact.fact_id(),
                        self.compile_function_raw_predicate(&fact, position, &inner)?,
                    ));
                }
                let mut predicate = clauses
                    .pop()
                    .map(|(_, clause)| clause)
                    .unwrap_or_else(|| "True".into());
                for (id, clause) in clauses.into_iter().rev() {
                    predicate = format!("(∃ (h_{} : {clause}), {predicate})", id.value());
                }
                // Match SetBuilderObj.condition and the ordered assumptions
                // emitted by compile_set_builder_wd, including certification of
                // the bound member. Its witness changes no object denotation.
                Ok(format!("(Litex.SetSemantics.sepValue (M := M) {bound} (fun ({variable} : M.Value) => ∃ (_ : M.mem {variable} {bound}), {predicate}))"))
            }
            Obj::SetOperator(SetOperator::FamilyUnion(value)) => Ok(format!(
                "(Litex.IndexedUnionSemantics.indexedUnionValue (M := M) {} id)",
                expression(&value.left)?
            )),
            Obj::SetOperator(SetOperator::PowerSet(value)) => Ok(format!(
                "(Litex.SetSemantics.powerValue (M := M) {})",
                expression(&value.set)?
            )),
            Obj::SetOperator(SetOperator::SetMinus(value)) => Ok(format!(
                "(Litex.SetSemantics.sepValue (M := M) {} (fun _difference_element : M.Value => ¬ M.mem _difference_element {}))",
                expression(&value.left)?, expression(&value.right)?
            )),
            Obj::SetOperator(SetOperator::Intersect(value)) => Ok(format!(
                "(Litex.SetSemantics.sepValue (M := M) {} (fun _intersection_element : M.Value => M.mem _intersection_element {}))",
                expression(&value.left)?, expression(&value.right)?
            )),
            Obj::SetOperator(SetOperator::Union(value)) => Ok(format!(
                "(Litex.SetSemantics.unionValue (M := M) {} {})",
                expression(&value.left)?,
                expression(&value.right)?
            )),
            Obj::ComplexOperator(ComplexOperator::Conjugate(p)) => Ok(format!("(Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) {})",expression(&p.arg)?)),
            Obj::ComplexOperator(ComplexOperator::RealPart(p)) => Ok(format!("(Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ)) {})",expression(&p.arg)?)),
            Obj::ComplexOperator(ComplexOperator::ImaginaryPart(p)) => Ok(format!("(Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.im : ℂ)) {})",expression(&p.arg)?)),
            Obj::ComplexOperator(ComplexOperator::ComplexAbs(p)) => Ok(format!("(Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) {})",expression(&p.arg)?)),
            Obj::TrigOperator(TrigOperator::Sin(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Real.sin {})", expression(&p.arg)?)),
            Obj::TrigOperator(TrigOperator::Cos(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Real.cos {})", expression(&p.arg)?)),
            Obj::TrigOperator(TrigOperator::Tan(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Real.tan {})", expression(&p.arg)?)),
            Obj::TrigOperator(TrigOperator::Cot(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Litex.nativeCot {})", expression(&p.arg)?)),
            Obj::TrigOperator(TrigOperator::Sec(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Litex.nativeSec {})", expression(&p.arg)?)),
            Obj::TrigOperator(TrigOperator::Csc(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Litex.nativeCsc {})", expression(&p.arg)?)),
            Obj::TrigOperator(TrigOperator::Arcsin(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Real.arcsin {})", expression(&p.arg)?)),
            Obj::TrigOperator(TrigOperator::Arccos(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Real.arccos {})", expression(&p.arg)?)),
            Obj::TrigOperator(TrigOperator::Arctan(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Real.arctan {})", expression(&p.arg)?)),
            Obj::TrigOperator(TrigOperator::Arccot(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Litex.nativeArccot {})", expression(&p.arg)?)),
            Obj::ExpLogOperator(ExpLogOperator::Exp(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Real.exp {})", expression(&p.arg)?)),
            Obj::ExpLogOperator(ExpLogOperator::Ln(p)) => Ok(format!("(Litex.realUnaryValue (M := M) Real.log {})", expression(&p.arg)?)),
            Obj::ExpLogOperator(ExpLogOperator::Log(p)) => Ok(format!("(M.divValue (Litex.realUnaryValue (M := M) Real.log {}) (Litex.realUnaryValue (M := M) Real.log {}))", expression(&p.arg)?, expression(&p.base)?)),
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(value)) => Ok(format!(
                "(Litex.sqrtValue (M := M) {})",
                expression(&value.arg)?
            )),
            Obj::IntegerOperator(IntegerOperator::Factorial(p)) => Ok(format!(
                "(Litex.factorialValue (M := M) {})",
                expression(&p.arg)?
            )),
            Obj::IntegerOperator(operator) => {
                let (operation, left, right) = match operator {
                    IntegerOperator::Mod(p) => ("modValue", &p.left, &p.right),
                    IntegerOperator::Quot(p) => ("quotValue", &p.left, &p.right),
                    IntegerOperator::Gcd(p) => ("gcdValue", &p.left, &p.right),
                    IntegerOperator::Lcm(p) => ("lcmValue", &p.left, &p.right),
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "FunctionTemplate/IntegerOperator",
                        ))
                    }
                };
                Ok(format!(
                    "({} {} {})",
                    arithmetic_operation_term(operation),
                    expression(left)?,
                    expression(right)?
                ))
            }
            Obj::ArithmeticOperator(operator) => {
                let rounding = match operator {
                    ArithmeticOperator::Floor(value) => Some((false, &value.arg)),
                    ArithmeticOperator::Ceil(value) => Some((true, &value.arg)),
                    _ => None,
                };
                if let Some((ceiling, argument)) = rounding {
                    return Ok(format!(
                        "(Litex.roundingValue (M := M) {ceiling} {})",
                        expression(argument)?
                    ));
                }
                if let ArithmeticOperator::Sign(value) = operator {
                    return Ok(format!(
                        "(Litex.signValue (M := M) {})",
                        expression(&value.arg)?
                    ));
                }
                if let ArithmeticOperator::Abs(value) = operator {
                    return Ok(format!(
                        "(Litex.absValue (M := M) {})",
                        expression(&value.arg)?
                    ));
                }
                let extremum = match operator {
                    ArithmeticOperator::Min(value) => Some((false, &value.left, &value.right)),
                    ArithmeticOperator::Max(value) => Some((true, &value.left, &value.right)),
                    _ => None,
                };
                if let Some((maximum, left, right)) = extremum {
                    return Ok(format!(
                        "(Litex.minMaxValue (M := M) {maximum} {} {})",
                        expression(left)?,
                        expression(right)?
                    ));
                }
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
            Obj::SetFormer(SetFormer::Range(_) | SetFormer::ClosedRange(_)) => {
                let mut free = std::collections::HashSet::new();
                crate::instantiate::collect_free_plain_ids(
                    object,
                    &std::collections::HashSet::new(),
                    &mut free,
                );
                if free.iter().any(|id| bindings.contains_key(id)) {
                    return Err(LeanCompileError::unsupported(
                        "Function/BoundIntegerInterval",
                    ));
                }
                Ok(format!(
                    "(Litex.denote {})",
                    self.compile_object_reference(object, position)?
                ))
            }
            Obj::FunctionSpace(FunctionSpace::FnRange(r)) => Ok(format!(
                "(Litex.FunctionSemantics.rangeValue {})",
                expression(&r.function)?
            )),
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => {
                // A captured literal needs lexical raw bindings for its graph
                // value; unchanged literals reuse their certified constructor.
                let mut free = std::collections::HashSet::new();
                crate::instantiate::collect_free_plain_ids(
                    object,
                    &std::collections::HashSet::new(),
                    &mut free,
                );
                if free.iter().any(|id| bindings.contains_key(id)) {
                    return self.compile_function_literal_value(function, position, bindings);
                }
                Ok(format!(
                    "(Litex.denote {})",
                    self.compile_object_reference(object, position)?
                ))
            }
            Obj::FunctionSpace(FunctionSpace::Composition(c)) => Ok(format!(
                "(Litex.FunctionSemantics.compositionValue (M := M) {} {})",
                expression(&c.outer)?, expression(&c.inner)?,
            )),
            Obj::FnObj(application) => {
                if application.body.is_empty()
                    || application
                        .body
                        .iter()
                        .any(|group| !(1..=3).contains(&group.len()))
                {
                    return Err(LeanCompileError::unsupported("Function/BodyCallArity"));
                }
                let object = match application.head.as_ref() {
                    FnObjHead::Identifier(identifier) => Obj::Identifier(identifier.clone()),
                    FnObjHead::Object(object) => object.as_ref().clone(),
                    FnObjHead::AnonymousFnLiteral(literal) => {
                        Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal.as_ref().clone()))
                    }
                    _ => return Err(LeanCompileError::unsupported("Function/BodyCallHead")),
                };
                let mut head = if let Some(value) = match &object {
                    Obj::Identifier(IdentifierObj::Plain { id, .. }) => bindings.get(id),
                    _ => None,
                } {
                    // A recursive interpretation is supplied by this exact
                    // source binder, not by a compiler-owned function registry.
                    value.clone()
                } else {
                    if matches!(object, Obj::Identifier(_)) {
                        self.validate_formula_head_producer(&object, position)?;
                    }
                    expression(&object)?
                };
                for group in &application.body {
                    let arguments = group
                        .iter()
                        .map(|argument| expression(argument))
                        .collect::<Result<Vec<_>, _>>()?;
                    let argument = if arguments.len() == 1 {
                        arguments[0].clone()
                    } else {
                        format!(
                            "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                            arguments.join(", ")
                        )
                    };
                    head =
                        format!("(Litex.FunctionSemantics.callValue (M := M) {head} {argument})");
                }
                Ok(head)
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
            if matches!(
                position.visible_parameter(*id, &self.runtime),
                Ok((_, Some(Obj::FunctionSpace(FunctionSpace::FnSet(_))), _, _))
            ) || position.visible_function(id).is_ok()
                || position.visible_recursive_function(id).is_ok()
            {
                return Ok(());
            }
        }
        if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(_)) = object {
            return Ok(());
        }
        position.with_visible_alias(object, &mut |_, value, result, producer| {
            self.compile_wd(success_object_wd(result, value)?, producer)?;
            self.validate_formula_head_producer(value, producer)
        })?.ok_or_else(|| LeanCompileError::new("Function/BodyCallProducer", &format!("The raw call head `{}` must cite an original function parameter, formula constructor or its RHS/let alias.", object.readable_string())))
    }

    pub(in crate::compile_to_lean) fn compile_function_raw_clause(
        &self,
        fact: &Fact,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_function_raw_predicate(fact, position, &function_raw_bindings(signature))
    }

    pub(in crate::compile_to_lean) fn compile_function_raw_predicate(
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
            Fact::OrFact(fact) => {
                let mut clauses = Vec::new();
                for branch in &fact.facts {
                    let source = match branch {
                        AndChainAtomicFact::AtomicFact(value) => Fact::AtomicFact(value.clone()),
                        AndChainAtomicFact::AndFact(value) => Fact::AndFact(value.clone()),
                        AndChainAtomicFact::ChainFact(value) => Fact::ChainFact(value.clone()),
                    };
                    clauses.push(self.compile_function_raw_predicate(&source, position, bindings)?);
                }
                return clauses
                    .into_iter()
                    .rev()
                    .reduce(|tail, head| format!("(({head}) ∨ ({tail}))"))
                    .ok_or_else(|| LeanCompileError::unsupported("Function/EmptyCompoundClause"));
            }
            Fact::ForallFact(fact) => {
                let mut bound = bindings.clone();
                let mut prefix = Vec::new();
                for group in &fact.typed_parameters.groups {
                    for parameter in &group.params {
                        let value = format!("_raw_i{}", parameter.id.value());
                        let carrier = match &group.param_type {
                            ParamType::Obj(s) => format!(
                                "M.mem {value} {}",
                                self.compile_function_raw_expression_bound(s, position, &bound)?
                            ),
                            ParamType::Set(_) => format!("M.isSet {value}"),
                            _ => {
                                return Err(LeanCompileError::unsupported(
                                    "Forall/RawParameterKind",
                                ))
                            }
                        };
                        prefix.push(format!("∀ ({value} : M.Value), {carrier} → "));
                        bound.insert(parameter.id, value);
                    }
                }
                for premise in &fact.dom_facts {
                    prefix.push(format!(
                        "({}) → ",
                        self.compile_function_raw_predicate(premise, position, &bound)?
                    ));
                }
                let conclusions = fact
                    .then_facts
                    .iter()
                    .map(|f| {
                        self.compile_function_raw_predicate(&f.clone().into(), position, &bound)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let body = conclusions
                    .into_iter()
                    .rev()
                    .reduce(|tail, head| format!("({head}) ∧ ({tail})"))
                    .unwrap_or_else(|| "True".into());
                return Ok(format!("({}{body})", prefix.join("")));
            }
            Fact::ExistFact(fact) => {
                return self.compile_exist_raw_predicate(fact, position, bindings)
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "Function/GuardPredicateClause",
                ))
            }
        };
        clauses
            .into_iter()
            .rev()
            .reduce(|tail, head| format!("(({head}) ∧ ({tail}))"))
            .ok_or_else(|| LeanCompileError::unsupported("Function/EmptyCompoundClause"))
    }

    fn compile_function_raw_fact_bound(
        &self,
        fact: &AtomicFact,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        if matches!(
            fact,
            AtomicFact::NotLessFact(_)
                | AtomicFact::NotLessEqualFact(_)
                | AtomicFact::NotGreaterFact(_)
                | AtomicFact::NotGreaterEqualFact(_)
                | AtomicFact::NotSubsetFact(_)
                | AtomicFact::NotNormalAtomicFact(_)
        ) {
            let positive = crate::ast::fact::negate_atomic_fact(fact, fact.fact_id())
                .ok_or_else(|| LeanCompileError::unsupported("Function/RawNegation"))?;
            return Ok(format!(
                "(¬ ({}))",
                self.compile_function_raw_fact_bound(&positive, position, bindings)?
            ));
        }
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
        if matches!(
            fact,
            AtomicFact::NotNormalAtomicFact(_)
                | AtomicFact::NotSupersetFact(_)
                | AtomicFact::NotProperSubsetFact(_)
                | AtomicFact::NotProperSupersetFact(_)
                | AtomicFact::NotIsSetFact(_)
                | AtomicFact::NotIsNonemptySetFact(_)
                | AtomicFact::NotIsFiniteSetFact(_)
                | AtomicFact::NotPrimeFact(_)
                | AtomicFact::NotCoprimeFact(_)
                | AtomicFact::NotDvdFact(_)
        ) {
            let positive = crate::ast::fact::negate_atomic_fact(fact, fact.fact_id())
                .ok_or_else(|| LeanCompileError::unsupported("Function/RawNegation"))?;
            return Ok(format!(
                "(¬ ({}))",
                self.compile_atomic_raw_proposition(&positive, arguments, position)?
            ));
        }
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
            AtomicFact::IsFiniteSetFact(_) => {
                format!("(Litex.memberSet (M := M) {}).Finite", arguments[0])
            }
            AtomicFact::IsNonemptySetFact(_) => {
                format!("(∃ _member : M.Value, M.mem _member {})", arguments[0])
            }
            AtomicFact::SubsetFact(_) => format!(
                "(∀ _member : M.Value, M.mem _member {} → M.mem _member {})",
                arguments[0], arguments[1]
            ),
            AtomicFact::SupersetFact(_) => format!(
                "(∀ _member : M.Value, M.mem _member {} → M.mem _member {})",
                arguments[1], arguments[0]
            ),
            AtomicFact::ProperSubsetFact(_) => format!(
                "((∀ _member : M.Value, M.mem _member {} → M.mem _member {}) ∧ {} ≠ {})",
                arguments[0], arguments[1], arguments[0], arguments[1]
            ),
            AtomicFact::ProperSupersetFact(_) => format!(
                "((∀ _member : M.Value, M.mem _member {} → M.mem _member {}) ∧ {} ≠ {})",
                arguments[1], arguments[0], arguments[0], arguments[1]
            ),
            AtomicFact::PrimeFact(_) => format!("(Litex.PrimeValue M {})", arguments[0]),
            AtomicFact::CoprimeFact(_) => {
                format!("(Litex.CoprimeValue M {} {})", arguments[0], arguments[1])
            }
            AtomicFact::DvdFact(_) => {
                format!("(Litex.DvdValue M {} {})", arguments[0], arguments[1])
            }
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
            fact if crate::compile_to_lean::compile_mapping_properties::mapping_parts(fact)
                .is_some() =>
            {
                let (kind, negative, _) =
                    crate::compile_to_lean::compile_mapping_properties::mapping_parts(fact)
                        .unwrap();
                format!(
                    "({}Litex.{kind}Value {} {} {})",
                    if negative { "¬ " } else { "" },
                    arguments[0],
                    arguments[1],
                    arguments[2]
                )
            }
            AtomicFact::NormalAtomicFact(normal) => {
                if let Some(proposition) = self.compile_abstract_predicate_proposition(
                    &normal.predicate,
                    arguments,
                    position,
                )? {
                    return Ok(proposition);
                }
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
                    if matches!(carrier, ParamType::Set(_)) {
                        clauses.push(format!("(M.isSet {argument})"));
                        continue;
                    }
                    let ParamType::Obj(carrier) = carrier else {
                        return Err(LeanCompileError::unsupported(
                            "Function/GuardPredicateCarrier",
                        ));
                    };
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
        QuantifierFreeFact::OrFact(fact) => Ok(Fact::OrFact(fact.clone())),
    }
}
