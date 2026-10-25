use super::compile_def_struct_stmt_result::{has_dependent_fields, validate_struct};
use super::compile_struct_header::header_substitution;
use super::compile_struct_conditions::coordinate_bindings;
use super::helper::{finite_vector_proof, source_subject, instantiated_fact_matches, instantiated_object_matches, conjunction_proposition};
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::StructObjMembershipBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_struct_membership(
        &self,
        fact: &InFact,
        proof: &StructObjMembershipBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier)) = &fact.set
        else {
            return Err(LeanCompileError::unsupported("StructMembership/Carrier"));
        };
        let (declaration, _, _) = position.visible_struct(&carrier.name)?;
        validate_struct(declaration)?;
        if proof.equivalent_fact_proofs.len() != declaration.statement.equivalent_facts.len() {
            return Err(LeanCompileError::unsupported("StructMembership/Conditions"));
        }
        let mut substitution = header_substitution(&declaration.statement, carrier)?;
        let fields = &declaration.statement.fields;
        let field_values = match &fact.element {
            Obj::ProductShape(ProductShape::Tuple(tuple)) => {
                if tuple.args.len() != fields.len() {
                    return Err(LeanCompileError::unsupported("StructMembership/FieldCount"));
                }
                tuple
                    .args
                    .iter()
                    .map(|v| v.as_ref().clone())
                    .collect::<Vec<_>>()
            }
            _ => (0..fields.len())
                .map(|index| {
                    crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate(
                        &fact.element,
                        index,
                    )
                    .map_err(|e| LeanCompileError::new("StructMembership/Coordinate", &e))
                })
                .collect::<Result<Vec<_>, _>>()?,
        };
        substitution.extend(
            fields
                .iter()
                .zip(&field_values)
                .map(|(f, v)| (f.binding.id, v.clone())),
        );
        let dependent = has_dependent_fields(&declaration.statement);
        let element = self.compile_object_reference(&fact.element, position)?;
        let target = self.compile_struct_base_reference(carrier, position)?;
        let cart_member = match &fact.element {
            Obj::ProductShape(ProductShape::Tuple(tuple)) => {
                if tuple.args.len() != fields.len()
                    || proof.carrier_obligations.len() != fields.len()
                {
                    return Err(LeanCompileError::unsupported("StructMembership/FieldCount"));
                }
                let mut members = Vec::new();
                for (index, ((value, field), child)) in tuple
                    .args
                    .iter()
                    .zip(fields)
                    .zip(&proof.carrier_obligations)
                    .enumerate()
                {
                    if !matches!(source_subject(child)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == value.ir() && instantiated_object_matches(&field.field_type, &f.set, &substitution))
                    {
                        return Err(LeanCompileError::unsupported(
                            "StructMembership/FieldSubject",
                        ));
                    }
                    members.push(
                        self.compile_verify(child, &position.atomic_search_prior(index)?)?
                            .1,
                    );
                }
                if dependent {
                    let accepted = members
                        .into_iter()
                        .rev()
                        .fold("True.intro".to_string(), |tail, member| {
                            format!("⟨{member}, {tail}⟩")
                        });
                    Ok(format!(
                        "(Litex.tupleInDependentCart {element} {target} (by exact {accepted}))"
                    ))
                } else {
                    Ok(format!(
                        "(Litex.tupleInCart {element} {target} {})",
                        finite_vector_proof(&members)
                    ))
                }
            }
            _ => {
                let [child] = proof.carrier_obligations.as_slice() else {
                    return Err(LeanCompileError::unsupported(
                        "StructMembership/CompleteCarrier",
                    ));
                };
                let Fact::AtomicFact(AtomicFact::InFact(member)) = source_subject(child)? else {
                    return Err(LeanCompileError::unsupported(
                        "StructMembership/CompleteCarrier",
                    ));
                };
                let Obj::ProductShape(ProductShape::Cart(cart)) = &member.set else {
                    return Err(LeanCompileError::unsupported(
                        "StructMembership/CompleteCarrier",
                    ));
                };
                if member.element.ir() != fact.element.ir()
                    || cart.args.len() != fields.len()
                    || cart.args.iter().zip(fields).any(|(factor, field)| {
                        !instantiated_object_matches(&field.field_type, factor, &substitution)
                    })
                {
                    return Err(LeanCompileError::unsupported(
                        "StructMembership/CarrierSubject",
                    ));
                }
                let cited = self
                    .compile_verify(child, &position.atomic_search_prior(0)?)?
                    .1;
                Ok(if dependent {
                    let indices = self.compile_struct_coordinate_indices(carrier, position)?;
                    format!(
                        "((Litex.inDependentCart_iff {element} {target} {indices}).mpr {cited})"
                    )
                } else {
                    format!("(show Litex.In {element} {target} from {cited})")
                })
            }
        }?;
        if declaration.statement.equivalent_facts.is_empty() {
            return Ok(cart_member);
        }
        let mut raw_bindings =
            self.struct_header_raw_bindings(&declaration.statement, carrier, position)?;
        let mut coordinate_equalities = Vec::new();
        let mut coordinate_names = Vec::new();
        for (index, (field, value)) in fields.iter().zip(&field_values).enumerate() {
            let term = self.compile_object_reference(value, position)?;
            raw_bindings.insert(field.binding.id, format!("(Litex.denote {term})"));
            if matches!(&fact.element, Obj::ProductShape(ProductShape::Tuple(_))) {
                let name = format!("_struct_coordinate_{index}");
                coordinate_equalities.push(format!("have {name} : Litex.FunctionSemantics.callValue (M := M) (Litex.denote {element}) (M.number ({} : ℂ)) = Litex.denote {term} := by\n  calc\n    _ = {element}.val.values ({index} : Fin {}) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate {element} ({index} : Fin {}))\n    _ = _ := by rfl", index + 1, fields.len(), fields.len()));
                coordinate_names.push(name);
            }
        }
        let mut laws = Vec::new();
        let mut law_names = Vec::new();
        for (index, (source, evidence)) in declaration
            .statement
            .equivalent_facts
            .iter()
            .zip(&proof.equivalent_fact_proofs)
            .enumerate()
        {
            let actual = source_subject(evidence)?;
            if !instantiated_fact_matches(source, &actual, &substitution) {
                return Err(LeanCompileError::unsupported(
                    "StructMembership/ConditionSubject",
                ));
            }
            let prior = position.atomic_search_prior(proof.carrier_obligations.len() + index)?;
            let checked = self.compile_verify(evidence, &prior)?;
            let raw = self.compile_function_raw_predicate(source, &prior, &raw_bindings)?;
            let name = format!("h_{}", actual.fact_id().value());
            laws.push(format!("have {name} : {raw} := {}", checked.1));
            law_names.push(name);
        }
        let mut condition_bindings =
            self.struct_header_raw_bindings(&declaration.statement, carrier, position)?;
        condition_bindings.extend(coordinate_bindings(
            &declaration.statement,
            &format!("(Litex.denote {element})"),
        ));
        let condition = conjunction_proposition(
            declaration
                .statement
                .equivalent_facts
                .iter()
                .map(|fact| {
                    self.compile_function_raw_predicate(fact, position, &condition_bindings)
                })
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        let bridge = self.compile_struct_members_reference(carrier, &element, position)?;
        let finish = if law_names.len() == 1 {
            law_names[0].clone()
        } else {
            format!("⟨{}⟩", law_names.join(", "))
        };
        let conclusion = if coordinate_names.is_empty() {
            format!("exact {finish}")
        } else {
            // A condition may ignore a coordinate or simplify to reflexivity.
            // Keep the recorded proof and fixed coordinate rewrites in either case.
            format!(
                "set_option linter.unusedSimpArgs false in\n    set_option linter.unnecessarySimpa false in\n      simpa only [{}] using {finish}",
                coordinate_names.join(", ")
            )
        };
        let mut lines = coordinate_equalities;
        lines.extend(laws);
        Ok(format!("(by\n  {}\n  refine {bridge}.mpr ⟨{cart_member}, ?_⟩\n  change {condition}\n  {conclusion})", lines.join("\n").replace('\n', "\n  ")))
    }
}
