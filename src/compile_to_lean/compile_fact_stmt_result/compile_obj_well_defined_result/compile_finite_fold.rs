use crate::compile_to_lean::compile_function_template::function_guard_fact;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FiniteSetReduceObjWellDefinedProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_fold_wd(
        &self,
        value: &FiniteSetReduce,
        proof: &FiniteSetReduceObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let operation = proof
            .operation_signature_selection
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("FiniteFold/OperationSignatureCapture"))?;
        let iterand = proof
            .iterand_signature_selection
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("FiniteFold/IterandSignatureCapture"))?;
        let signature = iterand.signature();
        let op_signature = operation.signature();
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |_| g.param_type.as_ref()))
            .collect::<Vec<_>>();
        let op_parameters = op_signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |_| g.param_type.as_ref()))
            .collect::<Vec<_>>();
        let [input] = parameters.as_slice() else {
            return Err(LeanCompileError::unsupported("FiniteFold/IterandArity"));
        };
        if !op_signature.dom_facts.is_empty()
            || op_parameters.len() != 2
            || op_parameters
                .iter()
                .any(|p| p.ir() != signature.ret_set.ir())
            || op_signature.ret_set.ir() != signature.ret_set.ir()
        {
            return Err(LeanCompileError::unsupported(
                "FiniteFold/SignatureContract",
            ));
        }
        // Positive-real numeric signatures encode their input predicates in
        // the signature itself; they need a separate domain-equality bridge.
        if op_signature.ret_set.as_ref() == &Obj::StandardSet(StandardSet::RPos)
            || (Self::function_uses_numeric_interface(signature)
                && matches!(input, Obj::StandardSet(StandardSet::RPos)))
        {
            return Err(LeanCompileError::unsupported(
                "FiniteFold/PositiveNumericSignature",
            ));
        }
        let children = &proof.child_obj_well_defined;
        let requirements = &proof.requirement_fact_verified;
        let guarded = !signature.dom_facts.is_empty();
        if children.len() != 4 || requirements.len() < 5 {
            return Err(LeanCompileError::unsupported("FiniteFold/Stages"));
        }
        if !matches!(source_subject(&requirements[0])?, Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir() == value.set.ir())
            || !matches!(source_subject(&requirements[1])?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == value.seed.ir() && f.set.ir() == signature.ret_set.ir())
            || !matches!(source_subject(&requirements[4])?, Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir() == value.set.ir() && f.right.ir() == input.ir())
        {
            return Err(LeanCompileError::unsupported("FiniteFold/Requirements"));
        }
        let literal = match value.set.as_ref() {
            Obj::SetFormer(SetFormer::ListSet(list)) if guarded => Some(list),
            _ => None,
        };
        if let Some(list) = literal {
            if list.list.len().checked_mul(signature.dom_facts.len())
                != Some(requirements.len() - 5)
            {
                return Err(LeanCompileError::unsupported("FiniteFold/GuardCount"));
            }
            let original = signature
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|g| &g.params)
                .next()
                .unwrap();
            for (argument, row) in list
                .list
                .iter()
                .zip(requirements[5..].chunks(signature.dom_facts.len()))
            {
                let substitution =
                    std::collections::HashMap::from([(original.id, argument.as_ref().clone())]);
                for (condition, proof) in signature.dom_facts.iter().zip(row) {
                    if !instantiated_fact_matches(
                        &function_guard_fact(condition)?,
                        &source_subject(proof)?,
                        &substitution,
                    ) {
                        return Err(LeanCompileError::unsupported("FiniteFold/GuardSubject"));
                    }
                }
            }
        } else if guarded {
            if requirements.len() != 6 {
                return Err(LeanCompileError::unsupported(
                    "FiniteFold/UniversalGuardCount",
                ));
            }
            validate_fold_universal_guard(
                signature,
                &value.set,
                &source_subject(&requirements[5])?,
            )?;
        } else if requirements.len() != 5 {
            return Err(LeanCompileError::unsupported(
                "FiniteFold/ExtraRequirements",
            ));
        }
        let mut objects = Vec::new();
        for (index, subject) in [&value.set, &value.func, &value.op, &value.seed]
            .into_iter()
            .enumerate()
        {
            ensure_object(subject, &children[index])?;
            objects.push(self.compile_wd(
                &children[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: children.len(),
            ..*position
        };
        let hf = self.compile_selected_signature(&value.func, iterand, &formed)?;
        let hop = self.compile_selected_signature(&value.op, operation, &formed)?;
        let signature_term = self.compile_fn_signature(signature, &formed)?;
        let carrier = self.compile_object_reference(&signature.ret_set, &formed)?;
        let mut proofs = Vec::new();
        let mut bindings = String::new();
        for (index, source) in requirements.iter().enumerate() {
            let prior = SourcePosition {
                before: children.len() + index,
                ..*position
            };
            let checked = self.compile_verify(source, &prior)?;
            let reference = format!("h_{}", source_subject(source)?.fact_id().value());
            bindings.push_str(&format!(
                "let {reference} : {} := {};\n",
                checked.0, checked.1
            ));
            proofs.push(if matches!(index, 2 | 3) {
                compile_fold_law(
                    &source_subject(source)?,
                    &value.op,
                    &signature.ret_set,
                    &carrier,
                    &reference,
                    index == 3,
                )?
            } else {
                reference
            });
        }
        let (domain, domain_set) =
            self.compile_function_semantic_base_domain(signature, &formed)?;
        let guard = self.compile_function_guard_template(signature, &formed)?;
        let guard_proof = if let Some(list) = literal {
            bindings.push_str(&format!("let _fold_tail_0 := {};\n", objects[0]));
            for i in 0..list.list.len() {
                bindings.push_str(&format!(
                    "let _fold_tail_{} := _fold_tail_{i}.val.tail;\n",
                    i + 1
                ));
            }
            let mut term = format!("Litex.finiteGuardEmpty {guard}");
            for i in (0..list.list.len()).rev() {
                let row = &proofs
                    [5 + i * signature.dom_facts.len()..5 + (i + 1) * signature.dom_facts.len()];
                let head = row
                    .iter()
                    .cloned()
                    .rev()
                    .reduce(|tail, head| format!("⟨{head}, {tail}⟩"))
                    .unwrap();
                term = format!("Litex.finiteGuardInsert _fold_tail_{i} {guard} ({head}) ({term})");
            }
            bindings.push_str(&format!(
                "let _fold_guard : ∀ i, M.mem i (Litex.denote {}) → {guard} i := {term};\n",
                objects[0]
            ));
            "_fold_guard i hi"
        } else if guarded {
            bindings.push_str(&format!("let _fold_guard : ∀ i, M.mem i (Litex.denote {}) → {guard} i := Litex.forallMembersOfRepresentations {} (fun _fold_index _fold_member => {} _fold_index _fold_member);\n", objects[0], objects[0], proofs[5]));
            "_fold_guard i hi"
        } else {
            "True.intro"
        };
        let cover = format!("(fun i hi => (Litex.FunctionSignature.withGuard_domain {domain} (Litex.denote {carrier}) {domain_set} (Litex.isSet {carrier}) {guard} i).mpr ⟨{} i hi, {guard_proof}⟩)", proofs[4]);
        Ok(format!(
            "({bindings}Litex.finiteFold {} {} {} {} {signature_term} {} {hf} {hop} {} {cover} {} {})",
            objects[0],
            objects[1],
            objects[2],
            objects[3],
            proofs[0],
            proofs[1],
            proofs[2],
            proofs[3]
        ))
    }
}

fn validate_fold_universal_guard(
    signature: &FnSet,
    set: &Obj,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(all) = fact else {
        return Err(LeanCompileError::unsupported("FiniteFold/GuardCoverage"));
    };
    let parameters = all
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
        .collect::<Vec<_>>();
    let [(parameter, ParamType::Obj(domain))] = parameters.as_slice() else {
        return Err(LeanCompileError::unsupported("FiniteFold/GuardParameter"));
    };
    if domain.ir() != set.ir()
        || !all.dom_facts.is_empty()
        || all.then_facts.len() != signature.dom_facts.len()
    {
        return Err(LeanCompileError::unsupported("FiniteFold/GuardDomain"));
    }
    let original = signature
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .next()
        .unwrap();
    let substitution = std::collections::HashMap::from([(
        original.id,
        Obj::Identifier(IdentifierObj::from_bound_name(parameter)),
    )]);
    for (expected, actual) in signature.dom_facts.iter().zip(&all.then_facts) {
        if !instantiated_fact_matches(
            &function_guard_fact(expected)?,
            &actual.clone().into(),
            &substitution,
        ) {
            return Err(LeanCompileError::unsupported("FiniteFold/GuardSubject"));
        }
    }
    Ok(())
}

/// Replay the selected universal law, then project its final equation. Earlier
/// beta equations remain compiled evidence; they are not replacement premises.
fn compile_fold_law(
    fact: &Fact,
    operation: &Obj,
    carrier: &Obj,
    carrier_term: &str,
    proof: &str,
    associative: bool,
) -> Result<String, LeanCompileError> {
    let Fact::ForallFact(all) = fact else {
        return Err(LeanCompileError::unsupported("FiniteFold/LawUniversal"));
    };
    let parameters = all
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
        .collect::<Vec<_>>();
    if !all.dom_facts.is_empty()
        || parameters.len() != if associative { 3 } else { 2 }
        || parameters
            .iter()
            .any(|(_, domain)| !matches!(domain, ParamType::Obj(o) if o.ir() == carrier.ir()))
    {
        return Err(LeanCompileError::unsupported("FiniteFold/LawParameters"));
    }
    let args = parameters
        .iter()
        .map(|(p, _)| Obj::Identifier(IdentifierObj::from_bound_name(p)))
        .collect::<Vec<_>>();
    let xy = fold_application(operation, &[args[0].clone(), args[1].clone()])?;
    let (left, right) = if associative {
        let yz = fold_application(operation, &[args[1].clone(), args[2].clone()])?;
        (
            fold_application(operation, &[xy, args[2].clone()])?,
            fold_application(operation, &[args[0].clone(), yz])?,
        )
    } else {
        (
            xy,
            fold_application(operation, &[args[1].clone(), args[0].clone()])?,
        )
    };
    if !matches!(all.then_facts.last(), Some(ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)))
        if eq.left.ir() == left.ir() && eq.right.ir() == right.ir())
    {
        return Err(LeanCompileError::unsupported("FiniteFold/LawEquation"));
    }
    let arguments = (0..args.len())
        .map(|i| format!("_fold_x{i} _fold_h{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    let mut term = conjunction_projection(
        &format!("({proof} {arguments})"),
        all.then_facts.len() - 1,
        all.then_facts.len(),
    );
    for i in (0..args.len()).rev() {
        term = format!("(Litex.forallMembersOfRepresentations {carrier_term} (fun _fold_x{i} _fold_h{i} => {term}))");
    }
    Ok(term)
}
