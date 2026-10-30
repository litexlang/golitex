use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::FiniteSetProductPointwiseEqualityStrategySingleStep;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_product_pointwise(
        &self,
        goal: &EqualFact,
        proof: &FiniteSetProductPointwiseEqualityStrategySingleStep,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(left)),
            Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(right)),
        ) = (&goal.left, &goal.right)
        else {
            return Err(LeanCompileError::unsupported(
                "FiniteProductPointwise/Constructor",
            ));
        };
        let (parameter, carrier, store) = finite_product_parameter(proof)?;
        self.validate_parameter_store_capture(&proof.introduced_parameter)?;
        if carrier.ir() != left.set.ir() {
            return Err(LeanCompileError::unsupported(
                "FiniteProductPointwise/Carrier",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(sets)) = source_subject(&proof.set_equality)?
        else {
            return Err(LeanCompileError::unsupported(
                "FiniteProductPointwise/SetEquality",
            ));
        };
        if sets.left.ir() != left.set.ir() || sets.right.ir() != right.set.ir() {
            return Err(LeanCompileError::unsupported(
                "FiniteProductPointwise/SetEndpoints",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(pointwise)) =
            source_subject(&proof.pointwise_equality)?
        else {
            return Err(LeanCompileError::unsupported(
                "FiniteProductPointwise/PointwiseEquality",
            ));
        };
        let argument = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let mut anonymous = Vec::new();
        for (function, endpoint) in [
            (&left.func, &pointwise.left),
            (&right.func, &pointwise.right),
        ] {
            if let Some(function) = pointwise_anonymous_function(function) {
                let parameters = function
                    .body
                    .set_bound_parameters
                    .groups
                    .iter()
                    .flat_map(|group| &group.params)
                    .collect::<Vec<_>>();
                let [source_parameter] = parameters.as_slice() else {
                    return Err(LeanCompileError::unsupported(
                        "FiniteProductPointwise/FunctionArity",
                    ));
                };
                let substitution = HashMap::from([(source_parameter.id, argument.clone())]);
                if !instantiated_object_matches(&function.equal_to, endpoint, &substitution) {
                    return Err(LeanCompileError::unsupported(
                        "FiniteProductPointwise/PointwiseSubject",
                    ));
                }
                anonymous.push(true);
            } else {
                let expected =
                    crate::execute::execute_fact_stmt::function_domain::function_application(
                        function,
                        vec![Box::new(argument.clone())],
                    )
                    .map_err(|_| {
                        LeanCompileError::unsupported("FiniteProductPointwise/FunctionApplication")
                    })?;
                if expected.ir() != endpoint.ir() {
                    return Err(LeanCompileError::unsupported(
                        "FiniteProductPointwise/PointwiseSubject",
                    ));
                }
                anonymous.push(false);
            }
        }
        let outer = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(std::slice::from_ref(&proof.set_equality)),
            0,
        );
        let set_equality = self.compile_verify(&proof.set_equality, &outer)?;
        let completed_set = SourcePosition { before: 1, ..outer };
        let local = SourcePosition::new(
            Some(&completed_set),
            SourceOwner::FiniteProductPointwise(proof),
            1,
        );
        let left_object = self.compile_object_reference(&goal.left, position)?;
        let right_object = self.compile_object_reference(&goal.right, position)?;
        let StoreFactResult::AtomicFact(member) = &store.store else {
            unreachable!()
        };
        let membership = Fact::AtomicFact(member.fact.clone());
        let member_type = self.fact_proposition(&membership, &local)?;
        let member_name = format!("h_{}", store.primary_fact_id().value());
        let mut local_lines = vec![
            "intro _product_x _product_member".to_string(),
            format!("let _value_i{} : Litex.Obj (M := M) M.Value := Litex.semanticObject _product_x (M.member_isSet _product_member)", parameter.id.value()),
            format!("have {member_name} : {member_type} := _product_member"),
        ];
        local_lines.extend(self.compile_parameter_inferences(
            store,
            &membership,
            &(member_type, member_name),
            &local,
        )?);
        let child = self.compile_verify(&proof.pointwise_equality, &local)?;
        local_lines.push(format!(
            "have _product_pointwise : {} := {}",
            child.0, child.1
        ));
        let bindings = HashMap::from([(parameter.id, "_product_x".to_string())]);
        let bodies = [&pointwise.left, &pointwise.right]
            .iter()
            .map(|endpoint| self.compile_function_raw_expression_bound(endpoint, &local, &bindings))
            .collect::<Result<Vec<_>, _>>()?;
        local_lines.push(format!(
            "have _product_raw : {} = {} := _product_pointwise",
            bodies[0], bodies[1]
        ));
        local_lines.push("have _product_right_member : M.mem _product_x (Litex.denote _product_right.val.set) := Eq.mp (congrArg (fun s => M.mem _product_x s) _product_sets) _product_member".into());
        for (index, side) in ["left", "right"].iter().enumerate() {
            let product = format!("_product_{side}");
            let function = format!("{product}.val.function");
            let body = &bodies[index];
            let call = format!(
                "Litex.FunctionSemantics.callValue (M := M) (Litex.denote {function}) _product_x"
            );
            let equality = if anonymous[index] {
                let member = if index == 0 {
                    "_product_member"
                } else {
                    "_product_right_member"
                };
                let domain = format!("(Litex.FunctionSemantics.domain_mem_iff {product}.wd.2.2.2.1 (Litex.formulaFnInFnSet {function})).mp ({product}.wd.2.2.2.2 _product_x ({product}.wd.2.1 _product_x {member}))");
                format!("Litex.FunctionSemantics.call_graphValue {function}.val.signature.domain {function}.val.signature.output {function}.val.bodyValue {function}.wd _product_x ({domain})")
            } else {
                "rfl".to_string()
            };
            local_lines.push(format!(
                "have _product_{side}_call : {call} = {body} := {equality}"
            ));
        }
        local_lines.push("exact congrArg (Litex.NativeBridge.complexValue (M := M)) (_product_left_call.trans (_product_raw.trans _product_right_call.symm))".into());
        let values = ["left", "right"].map(|side| format!("(fun x => Litex.NativeBridge.complexValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _product_{side}.val.function) x))"));
        let left_set = "(Litex.denote _product_left.val.set)";
        let right_set = "(Litex.denote _product_right.val.set)";
        Ok(format!(
            "(by\n  let _product_left := {left_object}\n  let _product_right := {right_object}\n  have _product_sets : {left_set} = {right_set} := {}\n  change M.number (Litex.finiteAggregateValue true {left_set} {}) = M.number (Litex.finiteAggregateValue true {right_set} {})\n  apply congrArg M.number\n  exact Eq.trans (Litex.finiteAggregateValue_congr true {left_set} {} {} (by\n    {}\n  )) (congrArg (fun s => Litex.finiteAggregateValue true s {}) _product_sets)\n)",
            set_equality.1, values[0], values[1], values[0], values[1], local_lines.join("\n").replace('\n', "\n    "), values[1]
        ))
    }
}

fn pointwise_anonymous_function(function: &Obj) -> Option<&AnonymousFn> {
    match function {
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => Some(function),
        Obj::FnObj(call) if call.body.is_empty() => match call.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(function) => Some(function),
            _ => None,
        },
        _ => None,
    }
}
