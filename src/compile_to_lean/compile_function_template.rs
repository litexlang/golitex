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
        if sets.is_empty() {
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
        if count == 0 {
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
        if values.is_empty() {
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
        let [first, second, rest @ ..] = laws.as_slice() else {
            return Ok("rfl".into());
        };
        // The same ordered coordinate equalities apply each curried argument.
        // This is finite tuple decoding, independent of the function's arity.
        Ok(rest.iter().fold(
            format!("(congrArg₂ {template} {first} {second})"),
            |prior, next| format!("(congrArg₂ (fun _f _x => _f _x) {prior} {next})"),
        ))
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

    // The recorded guard is the conjunction of source conditions. Reuse the
    // ordinary call bridge to add any carrier refinement (notably R+) exactly once.
    pub(in crate::compile_to_lean) fn compile_unary_function_domain_certificates(
        &self,
        signature: &FnSet,
        argument: &str,
        membership: String,
        recorded_guard: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let mut requirements = vec![membership];
        let count = signature.dom_facts.len();
        for index in 0..count {
            let mut projection = format!("({recorded_guard})");
            for _ in 0..index {
                projection.push_str(".2");
            }
            if index + 1 < count {
                projection.push_str(".1");
            }
            requirements.push(projection);
        }
        let (members, guard) = self.compile_function_domain_certificates(
            signature,
            &[argument.into()],
            &requirements,
            position,
        )?;
        Ok((members[0].clone(), guard))
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
        position.with_visible_alias(carrier, &self.runtime, &mut |_, value, result, producer| {
            let wd = success_object_wd(result, value)?;
            self.compile_wd(wd, producer)?;
            self.compile_numeric_carrier_alias(value, producer)
        })?.ok_or_else(|| {
            #[cfg(test)]
            eprintln!("Numeric carrier diagnostic: {}\n{}", carrier.readable_string(), std::backtrace::Backtrace::force_capture());
            LeanCompileError::new(
                "Function/NumericCarrierProducer",
                "A numeric carrier needs its preceding original RHS/let alias producer, not an equality discovered from the final environment.",
            )
        })
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
        guards.extend(
            self.compile_function_explicit_guard_conditions(signature, position, bindings)?,
        );
        Ok(function_guard_template(signature, guards))
    }

    pub(in crate::compile_to_lean) fn compile_function_explicit_guard_template(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let guards = self.compile_function_explicit_guard_conditions(
            signature,
            position,
            &function_raw_bindings(signature),
        )?;
        Ok(function_guard_template(signature, guards))
    }

    fn compile_function_explicit_guard_conditions(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<Vec<String>, LeanCompileError> {
        signature
            .dom_facts
            .iter()
            .map(|fact| {
                self.compile_function_raw_predicate(&function_guard_fact(fact)?, position, bindings)
            })
            .collect()
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
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access)) =>
                self.compile_struct_field_raw_value(access, position, bindings),
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier)) => {
                let mut free = std::collections::HashSet::new();
                crate::instantiate::collect_free_plain_ids(object, &std::collections::HashSet::new(), &mut free);
                if free.iter().any(|id| bindings.contains_key(id)) {
                    return self.compile_struct_raw_value(carrier, position, bindings);
                }
                Ok(format!("(Litex.denote {})", self.compile_object_reference(object, position)?))
            }
            Obj::InstantiatedTemplateObj(instance) =>
                self.compile_template_raw_value(instance, position, bindings),
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
            Obj::LimitOperator(LimitOperator::MultivariableVector(a)) => Ok(format!(
                "(Litex.multivariableVectorLimitValue {} {} {} {})",
                expression(&a.function)?,
                expression(&a.point)?,
                expression(&a.input_dimension)?,
                expression(&a.output_dimension)?
            )),
            Obj::LimitOperator(LimitOperator::MultivariableScalar(a)) => Ok(format!(
                "(Litex.multivariableScalarLimitValue {} {} {})",
                expression(&a.function)?,
                expression(&a.point)?,
                expression(&a.dimension)?
            )),
            Obj::MatrixOperator(MatrixOperator::IdentityMatrix(a)) => Ok(format!(
                "(Litex.identityMatrixValue {})",
                expression(&a.order)?
            )),
            Obj::MatrixOperator(MatrixOperator::ZeroMatrix(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {} {}) (M.standard .real) (fun _ => M.number 0))",
                expression(&a.rows)?, expression(&a.cols)?
            )),
            Obj::MatrixOperator(MatrixOperator::Transpose(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {} {}) (M.standard .complex) (Litex.matrixTransposeBody {}))",
                expression(&a.cols)?, expression(&a.rows)?, expression(&a.matrix)?
            )),
            Obj::MatrixOperator(MatrixOperator::ConjugateTranspose(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {} {}) (M.standard .complex) (Litex.matrixConjugateTransposeBody {}))",
                expression(&a.cols)?, expression(&a.rows)?, expression(&a.matrix)?
            )),
            Obj::MatrixOperator(MatrixOperator::Add(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {} {}) (M.standard .complex) (Litex.matrixEntrywiseBody .add {} {}))",
                expression(&a.rows)?, expression(&a.cols)?, expression(&a.left)?, expression(&a.right)?
            )),
            Obj::MatrixOperator(MatrixOperator::Subtract(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {} {}) (M.standard .complex) (Litex.matrixEntrywiseBody .sub {} {}))",
                expression(&a.rows)?, expression(&a.cols)?, expression(&a.left)?, expression(&a.right)?
            )),
            Obj::MatrixOperator(MatrixOperator::Scale(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {} {}) (M.standard .complex) (Litex.matrixScaleBody {} {}))",
                expression(&a.rows)?, expression(&a.cols)?, expression(&a.scalar)?, expression(&a.matrix)?
            )),
            Obj::MatrixOperator(MatrixOperator::Multiply(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {} {}) (M.standard .complex) (Litex.matrixMultiplyRawBody {} {} {}))",
                expression(&a.rows)?, expression(&a.cols)?, expression(&a.left)?, expression(&a.right)?, expression(&a.inner)?
            )),
            Obj::MatrixOperator(MatrixOperator::Diagonal(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {n} {n}) (M.standard .complex) (Litex.matrixDiagonalBody {v}))",
                n = expression(&a.order)?, v = expression(&a.vector)?
            )),
            Obj::MatrixOperator(MatrixOperator::OuterProduct(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {} {}) (M.standard .complex) (Litex.matrixOuterBody {} {}))",
                expression(&a.rows)?, expression(&a.cols)?, expression(&a.left)?, expression(&a.right)?
            )),
            Obj::MatrixOperator(MatrixOperator::Power(a)) => Ok(format!(
                "(Litex.matrixPowerRawValue {} {} (Litex.NativeBridge.naturalValue {}))",
                expression(&a.matrix)?, expression(&a.order)?, expression(&a.exponent)?
            )),
            Obj::MatrixOperator(MatrixOperator::Minor(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue (M.subValue {n} (M.number 1)) (M.subValue {n} (M.number 1))) (M.standard .complex) (Litex.matrixMinorBody {matrix} {n} {row} {col}))",
                n = expression(&a.order)?, matrix = expression(&a.matrix)?,
                row = expression(&a.row)?, col = expression(&a.col)?
            )),
            Obj::MatrixOperator(MatrixOperator::Adjugate(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {n} {n}) (M.standard .complex) (fun _adjugate_index => Litex.matrixCofactorRawValue {matrix} {n} (Litex.FiniteFunction.unpack2 _adjugate_index).2 (Litex.FiniteFunction.unpack2 _adjugate_index).1))",
                n = expression(&a.order)?, matrix = expression(&a.matrix)?
            )),
            Obj::MatrixOperator(MatrixOperator::Inverse(a)) => Ok(format!(
                "(Litex.FunctionSemantics.graphValue (Litex.realMatrixDomainValue {n} {n}) (M.standard .complex) (fun _inverse_index => M.divValue (Litex.matrixCofactorRawValue {matrix} {n} (Litex.FiniteFunction.unpack2 _inverse_index).2 (Litex.FiniteFunction.unpack2 _inverse_index).1) (M.number (Litex.matrixComplexOn {matrix} (Litex.NativeBridge.naturalValue {n}) (Litex.NativeBridge.naturalValue {n})).det)))",
                n = expression(&a.order)?, matrix = expression(&a.matrix)?
            )),
            Obj::DerivativeOperator(DerivativeOperator::TotalDifferential(a)) => Ok(format!(
                "(Litex.totalDifferentialValue {} {} {} {})",
                expression(&a.function)?,
                expression(&a.point)?,
                expression(&a.input_dimension)?,
                expression(&a.output_dimension)?
            )),
            Obj::DerivativeOperator(DerivativeOperator::Jacobian(a)) => Ok(format!(
                "(Litex.jacobianValue {} {} {} {})",
                expression(&a.function)?,
                expression(&a.point)?,
                expression(&a.input_dimension)?,
                expression(&a.output_dimension)?
            )),
            Obj::DerivativeOperator(DerivativeOperator::Curl(a)) => Ok(format!(
                "(Litex.curlValue {} {})",
                expression(&a.function)?,
                expression(&a.point)?
            )),
            Obj::DerivativeOperator(DerivativeOperator::Divergence(a)) => Ok(format!(
                "(Litex.divergenceValue {} {} {})",
                expression(&a.function)?,
                expression(&a.point)?,
                expression(&a.dimension)?
            )),
            Obj::MatrixOperator(MatrixOperator::Apply(a)) => Ok(format!(
                "(Litex.matrixApplyValue {} {} {} {})",
                expression(&a.matrix)?,
                expression(&a.vector)?,
                expression(&a.rows)?,
                expression(&a.cols)?
            )),
            Obj::DerivativeOperator(DerivativeOperator::ScalarDifferential(a)) => Ok(format!(
                "(Litex.scalarDifferentialValue {} {} {})",
                expression(&a.function)?,
                expression(&a.point)?,
                expression(&a.dimension)?
            )),
            Obj::DerivativeOperator(DerivativeOperator::Hessian(a)) => Ok(format!(
                "(Litex.hessianValue {} {} {})",
                expression(&a.function)?,
                expression(&a.point)?,
                expression(&a.dimension)?
            )),
            Obj::DerivativeOperator(DerivativeOperator::Laplacian(a)) => Ok(format!(
                "(Litex.laplacianValue {} {} {})",
                expression(&a.function)?,
                expression(&a.point)?,
                expression(&a.dimension)?
            )),
            Obj::DerivativeOperator(DerivativeOperator::Gradient(a)) => Ok(format!(
                "(Litex.gradientValue {} {} {})",
                expression(&a.function)?,
                expression(&a.point)?,
                expression(&a.dimension)?
            )),
            Obj::DerivativeOperator(DerivativeOperator::Partial(a)) => Ok(format!(
                "(Litex.partialDerivativeValue {} {} {} {})",
                expression(&a.function)?,
                expression(&a.point)?,
                expression(&a.dimension)?,
                expression(&a.coordinate)?
            )),
            Obj::MatrixOperator(MatrixOperator::EuclideanNorm(a)) => Ok(format!(
                "(Litex.sqrtValue (M.number (Litex.finiteAggregateValue false (Litex.closedRangeValue (M.number 1) {}) (fun _norm_index => ((‖Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue {} _norm_index)‖ ^ 2 : ℝ) : ℂ)))))",
                expression(&a.dimension)?,
                expression(&a.vector)?
            )),
            Obj::MatrixOperator(MatrixOperator::Trace(a)) => Ok(format!(
                "(M.number (Litex.matrixTraceRawValue {} {}))",
                expression(&a.matrix)?, expression(&a.order)?
            )),
            Obj::MatrixOperator(MatrixOperator::InnerProduct(a)) => Ok(format!(
                "(M.number (Litex.finiteInnerProductRawValue {} {} {}))",
                expression(&a.left)?, expression(&a.right)?, expression(&a.dimension)?
            )),
            Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(a)) => Ok(format!(
                "(Litex.sqrtValue (M.number (Litex.frobeniusNormRawSum {} {} {})))",
                expression(&a.matrix)?, expression(&a.rows)?, expression(&a.cols)?
            )),
            Obj::IntegralOperator(IntegralOperator::Riemann(a)) => Ok(format!(
                "(Litex.riemannIntegralValue {} {} {})",
                expression(&a.function)?,
                expression(&a.lower)?,
                expression(&a.upper)?
            )),
            Obj::DerivativeOperator(DerivativeOperator::AtPoint(a)) => Ok(format!(
                "(Litex.derivativeValue {} {})",
                expression(&a.function)?,
                expression(&a.point)?
            )),
            Obj::LimitOperator(LimitOperator::Sequence(a)) => Ok(format!(
                "(Litex.sequenceLimitValue {})",
                expression(&a.sequence)?
            )),
            Obj::LimitOperator(LimitOperator::SequenceLimsup(a)) => Ok(format!(
                "(Litex.sequenceExtremumValue true {})",
                expression(&a.sequence)?
            )),
            Obj::LimitOperator(LimitOperator::SequenceLiminf(a)) => Ok(format!(
                "(Litex.sequenceExtremumValue false {})",
                expression(&a.sequence)?
            )),
            Obj::LimitOperator(LimitOperator::Function(a)) => {
                if a.approach.point().is_some() {
                    let (side, point) = super::compile_function_limit::finite_side(&a.approach)?;
                    Ok(format!(
                        "(Litex.finiteFunctionLimitValue .{side} {} {})",
                        expression(&a.function)?,
                        expression(point)?
                    ))
                } else {
                    let direction = super::compile_function_limit::infinite_direction(&a.approach)?;
                    Ok(format!(
                        "(Litex.infiniteFunctionLimitValue .{direction} {})",
                        expression(&a.function)?
                    ))
                }
            }
            Obj::BoundOperator(BoundOperator::Supremum(a)) => {
                Ok(format!("(Litex.supremumValue {})", expression(&a.set)?))
            }
            Obj::BoundOperator(BoundOperator::Infimum(a)) => {
                Ok(format!("(Litex.infimumValue {})", expression(&a.set)?))
            }
            Obj::MatrixOperator(MatrixOperator::Rank(m)) => Ok(format!(
                "(Litex.matrixRankValue {} {} {})",
                expression(&m.matrix)?,
                expression(&m.rows)?,
                expression(&m.cols)?
            )),
            Obj::MatrixOperator(MatrixOperator::Determinant(m)) => {
                let matrix = expression(&m.matrix)?;
                let size = format!(
                    "(Litex.NativeBridge.naturalValue {})",
                    expression(&m.order)?
                );
                Ok(format!(
                    "(M.number (Litex.matrixComplexOn {matrix} {size} {size}).det)"
                ))
            }
            Obj::MatrixOperator(MatrixOperator::Cofactor(m)) => Ok(format!(
                "(Litex.matrixCofactorRawValue {} {} {} {})",
                expression(&m.matrix)?,
                expression(&m.order)?,
                expression(&m.row)?,
                expression(&m.col)?,
            )),
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
            Obj::SetFormer(SetFormer::FiniteSeqSet(value)) => Ok(format!(
                "(Litex.FunctionSemantics.fnSetValue (Litex.SetSemantics.sepValue (Litex.closedRangeValue (M.number 1) {}) (fun _ => True)) {})",
                expression(&value.n)?,
                expression(&value.set)?
            )),
            Obj::SetFormer(SetFormer::SeqSet(value)) => Ok(format!(
                "(Litex.FunctionSemantics.fnSetValue (Litex.SetSemantics.sepValue (Litex.denote (Litex.NPos (M := M))) (fun _ => True)) {})",
                expression(&value.set)?
            )),
            Obj::SetFormer(SetFormer::MatrixSet(value)) => Ok(format!(
                "(Litex.FunctionSemantics.fnSetValue (Litex.realMatrixDomainValue {} {}) {})",
                expression(&value.rows)?,
                expression(&value.cols)?,
                expression(&value.set)?
            )),
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
                Ok(format!(
                    "(Litex.SetSemantics.sepValue (M := M) {bound} (fun ({variable} : M.Value) => ∃ (_ : M.mem {variable} {bound}), {predicate}))"
                ))
            }
            Obj::IteratedOperator(IteratedOperator::Sum(_) | IteratedOperator::Product(_)) => {
                let (product, first, last, function) = match object {
                    Obj::IteratedOperator(IteratedOperator::Sum(s)) => {
                        (false, &s.start, &s.end, &s.func)
                    }
                    Obj::IteratedOperator(IteratedOperator::Product(s)) => {
                        (true, &s.start, &s.end, &s.func)
                    }
                    _ => unreachable!(),
                };
                let iterand =
                    if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = function.as_ref() {
                        self.compile_function_literal_value(f, position, bindings)?
                    } else {
                        expression(function)?
                    };
                Ok(format!(
                    "(M.number (Litex.nativeRangeAggregate {product} (Litex.NativeBridge.integerValue {}) (Litex.NativeBridge.integerValue {}) (fun _aggregate_index => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue {iterand} (M.number (_aggregate_index : ℂ))))))",
                    expression(first)?,
                    expression(last)?
                ))
            }
            Obj::IteratedOperator(
                IteratedOperator::SumOfFiniteSet(_) | IteratedOperator::ProductOfFiniteSet(_),
            ) => {
                let (product, set, function) = match object {
                    Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(s)) => {
                        (false, &s.set, &s.func)
                    }
                    Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(s)) => {
                        (true, &s.set, &s.func)
                    }
                    _ => unreachable!(),
                };
                let iterand =
                    if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = function.as_ref() {
                        self.compile_function_literal_value(f, position, bindings)?
                    } else {
                        expression(function)?
                    };
                Ok(format!(
                    "(M.number (Litex.finiteAggregateValue {product} {} (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue {iterand} _aggregate_item))))",
                    expression(set)?
                ))
            }
            Obj::IteratedOperator(IteratedOperator::Reduce(value)) => Ok(format!(
                "(Litex.rangeFoldValue (M := M) {} {} {} {} {})",
                expression(&value.start)?,
                expression(&value.end)?,
                expression(&value.func)?,
                expression(&value.op)?,
                expression(&value.seed)?
            )),
            Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(value)) => Ok(format!(
                "(Litex.finiteFoldValue (M := M) {} {} {} {})",
                expression(&value.set)?,
                expression(&value.func)?,
                expression(&value.op)?,
                expression(&value.seed)?
            )),
            Obj::SetOperator(SetOperator::FamilyIntersect(value)) => Ok(format!(
                "(Litex.familyIntersectValue {})",
                expression(&value.left)?
            )),
            Obj::SetOperator(SetOperator::FamilyUnion(value)) => Ok(format!(
                "(Litex.IndexedUnionSemantics.indexedUnionValue (M := M) {} id)",
                expression(&value.left)?
            )),
            Obj::SetOperator(SetOperator::SymmetricDifference(value)) => Ok(format!(
                "(Litex.symmetricDifferenceValue (M := M) {} {})",
                expression(&value.left)?,
                expression(&value.right)?
            )),
            Obj::SetOperator(SetOperator::IndexUnion(value)) => Ok(format!(
                "(Litex.indexUnionValue (M := M) {} {} {})",
                expression(&value.index_set)?,
                expression(&value.ambient_set)?,
                expression(&value.family_fn)?
            )),
            Obj::SetOperator(SetOperator::IndexIntersect(value)) => Ok(format!(
                "(Litex.indexIntersectValue (M := M) {} {} {})",
                expression(&value.index_set)?,
                expression(&value.ambient_set)?,
                expression(&value.family_fn)?
            )),
            Obj::SetOperator(SetOperator::IndexCart(value)) => Ok(format!(
                "(Litex.indexCartValue (M := M) {} {} {})",
                expression(&value.index_set)?,
                expression(&value.family_set)?,
                expression(&value.family_fn)?
            )),
            Obj::SetOperator(SetOperator::PowerSet(value)) => Ok(format!(
                "(Litex.SetSemantics.powerValue (M := M) {})",
                expression(&value.set)?
            )),
            Obj::SetOperator(SetOperator::SetMinus(value)) => Ok(format!(
                "(Litex.SetSemantics.sepValue (M := M) {} (fun _difference_element : M.Value => ¬ M.mem _difference_element {}))",
                expression(&value.left)?,
                expression(&value.right)?
            )),
            Obj::SetOperator(SetOperator::Intersect(value)) => Ok(format!(
                "(Litex.SetSemantics.sepValue (M := M) {} (fun _intersection_element : M.Value => M.mem _intersection_element {}))",
                expression(&value.left)?,
                expression(&value.right)?
            )),
            Obj::SetOperator(SetOperator::Union(value)) => Ok(format!(
                "(Litex.SetSemantics.unionValue (M := M) {} {})",
                expression(&value.left)?,
                expression(&value.right)?
            )),
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(p)) => Ok(format!(
                "(M.number (Litex.finiteCard {} : ℂ))",
                expression(&p.set)?
            )),
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(p)) => Ok(format!(
                "(M.number (Litex.finiteExtremumValue true {} : ℂ))",
                expression(&p.set)?
            )),
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(p)) => Ok(format!(
                "(M.number (Litex.finiteExtremumValue false {} : ℂ))",
                expression(&p.set)?
            )),
            Obj::ComplexOperator(ComplexOperator::Conjugate(p)) => Ok(format!(
                "(Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) {})",
                expression(&p.arg)?
            )),
            Obj::ComplexOperator(ComplexOperator::RealPart(p)) => Ok(format!(
                "(Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ)) {})",
                expression(&p.arg)?
            )),
            Obj::ComplexOperator(ComplexOperator::ImaginaryPart(p)) => Ok(format!(
                "(Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.im : ℂ)) {})",
                expression(&p.arg)?
            )),
            Obj::ComplexOperator(ComplexOperator::ComplexAbs(p)) => Ok(format!(
                "(Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) {})",
                expression(&p.arg)?
            )),
            Obj::HyperbolicOperator(HyperbolicOperator::Sinh(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.sinh {})",
                expression(&p.arg)?
            )),
            Obj::HyperbolicOperator(HyperbolicOperator::Cosh(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.cosh {})",
                expression(&p.arg)?
            )),
            Obj::HyperbolicOperator(HyperbolicOperator::Tanh(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.tanh {})",
                expression(&p.arg)?
            )),
            Obj::HyperbolicOperator(HyperbolicOperator::Coth(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Litex.nativeCoth {})",
                expression(&p.arg)?
            )),
            Obj::HyperbolicOperator(HyperbolicOperator::Sech(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Litex.nativeSech {})",
                expression(&p.arg)?
            )),
            Obj::HyperbolicOperator(HyperbolicOperator::Csch(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Litex.nativeCsch {})",
                expression(&p.arg)?
            )),
            Obj::TrigOperator(TrigOperator::Sin(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.sin {})",
                expression(&p.arg)?
            )),
            Obj::TrigOperator(TrigOperator::Cos(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.cos {})",
                expression(&p.arg)?
            )),
            Obj::TrigOperator(TrigOperator::Tan(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.tan {})",
                expression(&p.arg)?
            )),
            Obj::TrigOperator(TrigOperator::Cot(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Litex.nativeCot {})",
                expression(&p.arg)?
            )),
            Obj::TrigOperator(TrigOperator::Sec(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Litex.nativeSec {})",
                expression(&p.arg)?
            )),
            Obj::TrigOperator(TrigOperator::Csc(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Litex.nativeCsc {})",
                expression(&p.arg)?
            )),
            Obj::TrigOperator(TrigOperator::Arcsin(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.arcsin {})",
                expression(&p.arg)?
            )),
            Obj::TrigOperator(TrigOperator::Arccos(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.arccos {})",
                expression(&p.arg)?
            )),
            Obj::TrigOperator(TrigOperator::Arctan(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.arctan {})",
                expression(&p.arg)?
            )),
            Obj::TrigOperator(TrigOperator::Arccot(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Litex.nativeArccot {})",
                expression(&p.arg)?
            )),
            Obj::ExpLogOperator(ExpLogOperator::Exp(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.exp {})",
                expression(&p.arg)?
            )),
            Obj::ExpLogOperator(ExpLogOperator::Ln(p)) => Ok(format!(
                "(Litex.realUnaryValue (M := M) Real.log {})",
                expression(&p.arg)?
            )),
            Obj::ExpLogOperator(ExpLogOperator::Log(p)) => Ok(format!(
                "(M.divValue (Litex.realUnaryValue (M := M) Real.log {}) (Litex.realUnaryValue (M := M) Real.log {}))",
                expression(&p.arg)?,
                expression(&p.base)?
            )),
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
                        ));
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
            // A value-level interval does not introduce a new certified host
            // object. Its enclosing constructor still consumes original WD.
            Obj::SetFormer(SetFormer::IntervalObj(interval)) => {
                let (lower, upper, lc, rc) = real_interval_parts(interval);
                Ok(format!(
                    "(Litex.SetSemantics.sepValue (M := M) (M.standard .real) (fun _interval_x => Litex.realBound {lc} {} _interval_x ∧ Litex.realBound {rc} _interval_x {}))",
                    expression(lower)?,
                    expression(upper)?
                ))
            }
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(ray)) => {
                let (endpoint, lower, closed) = real_ray_parts(ray);
                let endpoint = expression(endpoint)?;
                let bound = if lower {
                    format!("Litex.realBound {closed} {endpoint} _ray_value")
                } else {
                    format!("Litex.realBound {closed} _ray_value {endpoint}")
                };
                Ok(format!(
                    "(Litex.SetSemantics.sepValue (M := M) (M.standard .real) (fun _ray_value => {bound}))"
                ))
            }
            Obj::SetFormer(SetFormer::ClosedRange(r)) => Ok(format!(
                "(Litex.closedRangeValue {} {})",
                expression(&r.start)?,
                expression(&r.end)?
            )),
            Obj::SetFormer(SetFormer::Range(r)) => Ok(format!(
                "(Litex.SetSemantics.sepValue (M := M) (M.standard .integer) (fun _range_value => ∃ _range_lower _range_upper _range_index : ℤ, {} = M.number (_range_lower : ℂ) ∧ {} = M.number (_range_upper : ℂ) ∧ _range_value = M.number (_range_index : ℂ) ∧ _range_lower ≤ _range_index ∧ _range_index < _range_upper))",
                expression(&r.start)?,
                expression(&r.end)?
            )),
            Obj::FunctionSpace(FunctionSpace::Preimage(p)) => Ok(format!(
                "(Litex.FunctionSemantics.preimageValue {} (fun _preimage_y => _preimage_y = {}))",
                expression(&p.function)?,
                expression(&p.value)?
            )),
            Obj::FunctionSpace(FunctionSpace::PreimageSet(p)) => Ok(format!(
                "(Litex.FunctionSemantics.preimageValue {} (fun _preimage_y => M.mem _preimage_y {}))",
                expression(&p.function)?,
                expression(&p.target_set)?
            )),
            Obj::FunctionSpace(FunctionSpace::FnRange(r)) => Ok(format!(
                "(Litex.FunctionSemantics.rangeValue {})",
                expression(&r.function)?
            )),
            Obj::FunctionSpace(FunctionSpace::FnSet(signature)) => {
                let (domain, output, _) =
                    self.compile_function_signature_value_parts(signature, position, bindings)?;
                Ok(format!(
                    "(Litex.FunctionSemantics.fnSetValue (M := M) {domain} {output})"
                ))
            }
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => {
                // Raw predicates need the graph value, not an inline copy of
                // the constructor's WD proof. Closed captures must still cite
                // an original constructor; open captures use the binder's WD.
                let mut free = std::collections::HashSet::new();
                crate::instantiate::collect_free_plain_ids(
                    object,
                    &std::collections::HashSet::new(),
                    &mut free,
                );
                if free.iter().any(|id| bindings.contains_key(id)) {
                    return self.compile_function_literal_value(function, position, bindings);
                }
                self.compile_object_reference(object, position)?;
                self.compile_function_literal_value(function, position, bindings)
            }
            Obj::FunctionSpace(FunctionSpace::Composition(c)) => Ok(format!(
                "(Litex.FunctionSemantics.compositionValue (M := M) {} {})",
                expression(&c.outer)?,
                expression(&c.inner)?,
            )),
            Obj::FnObj(application) => {
                if application.body.is_empty()
                    || application.body.iter().any(|group| group.is_empty())
                {
                    return Err(LeanCompileError::unsupported("Function/BodyCallArity"));
                }
                let object = match application.head.as_ref() {
                    FnObjHead::Identifier(identifier) => Obj::Identifier(identifier.clone()),
                    FnObjHead::Object(object) => object.as_ref().clone(),
                    FnObjHead::AnonymousFnLiteral(literal) => {
                        Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal.as_ref().clone()))
                    }
                    FnObjHead::InstantiatedTemplateObj(instance) => Obj::InstantiatedTemplateObj(instance.clone()),
                    FnObjHead::FieldAccess(field) => Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(field.clone())),
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
            _ => Err(LeanCompileError::new(
                "Function/BodyObject",
                &format!(
                    "No raw denotation for `{}` in the selected source context.",
                    object.readable_string()
                ),
            )),
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
                Ok((
                    _,
                    Some(
                        Obj::FunctionSpace(FunctionSpace::FnSet(_))
                            | Obj::SetFormer(
                                SetFormer::MatrixSet(_)
                                    | SetFormer::FiniteSeqSet(_)
                                    | SetFormer::SeqSet(_)
                            )
                    ),
                    _,
                    _
                ))
            ) || position.visible_function(id).is_ok()
                || position.visible_recursive_function(id).is_ok()
            {
                return Ok(());
            }
        }
        if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(_)) = object {
            return Ok(());
        }
        position.with_visible_alias(object, &self.runtime, &mut |_, value, result, producer| {
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
                return self.compile_function_raw_fact_bound(fact, position, bindings);
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
                                ));
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
                return self.compile_exist_raw_predicate(fact, position, bindings);
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "Function/GuardPredicateClause",
                ));
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
        if super::compile_matrix_inverse_predicates::is_matrix_inverse_predicate(fact) {
            return super::compile_matrix_inverse_predicates::raw_matrix_inverse_predicate(
                fact, arguments,
            );
        }
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
                | AtomicFact::NotSequenceAnalysisFact(_)
                | AtomicFact::NotHasSequenceLimitFact(_)
                | AtomicFact::NotHasSequenceLimsupFact(_)
                | AtomicFact::NotHasSequenceLiminfFact(_)
                | AtomicFact::NotHasFunctionLimitFact(_)
                | AtomicFact::NotFunctionContinuousAtFact(_)
                | AtomicFact::NotHasDerivativeAtFact(_)
                | AtomicFact::NotFunctionDifferentiableAtFact(_)
                | AtomicFact::NotRealAccumulationFact(_)
                | AtomicFact::NotMultivariableAnalysisFact(_)
                | AtomicFact::NotRealSetBoundFact(_)
                | AtomicFact::NotRealSetBoundedFact(_)
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
            f @ (AtomicFact::RealSetBoundFact(_) | AtomicFact::RealSetBoundedFact(_)) => {
                let (name, _, _, bound) = super::compile_real_set_bounds::bound_parts(f).unwrap();
                if bound.is_some() {
                    format!("(Litex.{name}Value M {} {})", arguments[0], arguments[1])
                } else {
                    format!("(Litex.{name}Value M {})", arguments[0])
                }
            }
            AtomicFact::FunctionContinuousAtFact(f) => format!(
                "(Litex.FunctionContinuousAtValue M .{} {} {})",
                super::compile_function_continuity::continuity_side(f.side),
                arguments[0],
                arguments[1]
            ),
            f @ (AtomicFact::HasSequenceLimsupFact(_) | AtomicFact::HasSequenceLiminfFact(_)) => {
                let (_, _, upper, _) = super::compile_sequence_extremum::extremum_parts(f).unwrap();
                format!(
                    "(Litex.HasSequenceExtremumValue M {upper} {} {})",
                    arguments[0], arguments[1]
                )
            }
            f @ (AtomicFact::HasRiemannIntegralFact(_)
            | AtomicFact::NotHasRiemannIntegralFact(_)
            | AtomicFact::FunctionRiemannIntegrableFact(_)
            | AtomicFact::NotFunctionRiemannIntegrableFact(_)) => {
                super::compile_riemann_integral::raw_proposition(f, arguments)?
            }
            f @ (AtomicFact::HasDerivativeAtFact(_)
            | AtomicFact::FunctionDifferentiableAtFact(_)) => {
                let (_, _, value, _) =
                    super::compile_function_derivative::derivative_parts(f).unwrap();
                if value.is_some() {
                    format!(
                        "(Litex.HasDerivativeAtValue M {} {} {})",
                        arguments[0], arguments[1], arguments[2]
                    )
                } else {
                    format!(
                        "(Litex.DerivativeExistsValue M {} {})",
                        arguments[0], arguments[1]
                    )
                }
            }
            AtomicFact::MultivariableAnalysisFact(f) => {
                let name = match &f.relation {
                    MultivariableAnalysisRelation::ScalarLimit(_) => {
                        "HasMultivariableScalarLimitValue"
                    }
                    MultivariableAnalysisRelation::VectorLimit(_) => {
                        "HasMultivariableVectorLimitValue"
                    }
                    MultivariableAnalysisRelation::PartialDerivativeAt(_) => {
                        "HasPartialDerivativeAtValue"
                    }
                    MultivariableAnalysisRelation::GradientAt(_) => "HasGradientAtValue",
                    MultivariableAnalysisRelation::HessianAt(_) => "HasHessianAtValue",
                    MultivariableAnalysisRelation::ScalarDifferentialAt(_) => {
                        "HasScalarDifferentialAtValue"
                    }
                    MultivariableAnalysisRelation::TotalDerivativeAt(_) => {
                        "HasTotalDifferentialAtValue"
                    }
                    MultivariableAnalysisRelation::LaplacianAt(_) => "HasLaplacianAtValue",
                    MultivariableAnalysisRelation::JacobianAt(_) => "HasJacobianAtValue",
                    MultivariableAnalysisRelation::DivergenceAt(_) => "HasDivergenceAtValue",
                    MultivariableAnalysisRelation::CurlAt(_) => "HasCurlAtValue",
                    MultivariableAnalysisRelation::SecondPartialDerivativeAt(_) => {
                        "HasSecondPartialAtValue"
                    }
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "Function/MultivariableFamily",
                        ));
                    }
                };
                format!("(Litex.{name} M {})", arguments.join(" "))
            }
            AtomicFact::HasSequenceLimitFact(_) => format!(
                "(Litex.HasSequenceLimitValue M {} {})",
                arguments[0], arguments[1]
            ),
            AtomicFact::HasFunctionLimitFact(f) => {
                if f.approach.point().is_some() {
                    let (side, _) = super::compile_function_limit::finite_side(&f.approach)?;
                    format!(
                        "(Litex.HasFiniteFunctionLimitValue M .{side} {} {} {})",
                        arguments[0], arguments[1], arguments[2]
                    )
                } else {
                    let direction = super::compile_function_limit::infinite_direction(&f.approach)?;
                    format!(
                        "(Litex.HasInfiniteFunctionLimitValue M .{direction} {} {})",
                        arguments[0], arguments[1]
                    )
                }
            }
            AtomicFact::SequenceAnalysisFact(f) => {
                let name = super::compile_sequence_analysis::sequence_name(f.property)?;
                format!("(Litex.Sequence{name}Value M {})", arguments[0])
            }
            AtomicFact::RealAccumulationFact(f) => {
                let side = super::compile_function_continuity::continuity_side(f.side);
                format!(
                    "(Litex.RealAccumulationValue M .{side} {} {})",
                    arguments[0], arguments[1]
                )
            }
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
                format!(
                    "(∃ (_r _s : ℝ), {left} = M.number (_r : ℂ) ∧ {right} = M.number (_s : ℂ) ∧ _r {} _s)",
                    if strict { "<" } else { "≤" }
                )
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
                if super::compile_riemann_integral::is_enclosure(&normal.predicate) {
                    if arguments.len() != 7 {
                        return Err(super::compile_riemann_integral::invalid("EnclosureArity"));
                    }
                    return Ok(format!(
                        "(Litex.DarbouxEnclosureValue {})",
                        arguments.join(" ")
                    ));
                }
                if let Some(name) = super::compile_real_extrema::certificate_name(&normal.predicate)
                {
                    if arguments.len() != 2 {
                        return Err(LeanCompileError::unsupported(
                            "RealExtremum/CertificateArity",
                        ));
                    }
                    return Ok(format!(
                        "(Litex.{name}Value M {} {})",
                        arguments[0], arguments[1]
                    ));
                }
                if let Some(proposition) = self.compile_abstract_predicate_proposition(
                    &normal.predicate,
                    arguments,
                    position,
                )? {
                    return Ok(proposition);
                }
                let (definition, producer, _) =
                    position.visible_prop(&normal.predicate, &self.runtime)?;
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
                    if matches!(carrier, ParamType::NonemptySet(_)) {
                        clauses.push(format!("(∃ _member : M.Value, M.mem _member {argument})"));
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

fn function_guard_template(signature: &FnSet, guards: Vec<String>) -> String {
    let parameters = signature
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|group| &group.params)
        .map(|parameter| format!("(_raw_i{} : M.Value)", parameter.id.value()))
        .collect::<Vec<_>>();
    let guard = guards
        .into_iter()
        .rev()
        .reduce(|tail, head| format!("(({head}) ∧ ({tail}))"))
        .unwrap_or_else(|| "True".into());
    format!("(fun {} => {guard})", parameters.join(" "))
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
