use crate::compile_to_lean::compile_function_template::function_guard_fact;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    AnonymousFnBodyInReturnSetProof, AnonymousFnObjWellDefinedProof, FnSetObjWellDefinedProof,
    FunctionSpaceObjWellDefinedProofByDef,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_function_space_wd(
        &self,
        space: &FunctionSpace,
        proof: &FunctionSpaceObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match (space, proof) {
            (FunctionSpace::FnSet(signature), FunctionSpaceObjWellDefinedProofByDef::FnSet(wd)) => {
                self.compile_function_set_wd(signature, wd, position)
            }
            (
                FunctionSpace::AnonymousFn(function),
                FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(wd),
            ) => self.compile_formula_function_wd(function, wd, position),
            (FunctionSpace::FnSet(_) | FunctionSpace::AnonymousFn(_), _) => {
                Err(LeanCompileError::new(
                    "Function/WDSubject",
                    "Function-space evidence has another source constructor.",
                ))
            }
            _ => Err(LeanCompileError::unsupported("Function/Space")),
        }
    }

    fn compile_function_set_wd(
        &self,
        signature: &FnSet,
        wd: &FnSetObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let head = self.compile_function_binder_head(
            signature,
            &wd.param_type_well_defined,
            &wd.defined_params,
            &wd.assumed_dom_facts,
            position,
        )?;
        let return_position = SourcePosition {
            before: self.function_header_stages(signature),
            ..*position
        };
        ensure_object(&signature.ret_set, &wd.ret_set_well_defined)?;
        self.compile_wd(&wd.ret_set_well_defined, &return_position)?;
        let checked_header = self.compile_function_raw_header(signature, position)?;
        let signature = self.compile_fn_signature(signature, position)?;
        Ok(format!(
            "(by\n  have _checked_header : {checked_header} := by\n    {}\n    exact True.intro\n  exact Litex.fnSet {signature})",
            head.replace('\n', "\n    ")
        ))
    }

    fn compile_formula_function_wd(
        &self,
        function: &AnonymousFn,
        wd: &AnonymousFnObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let signature = &function.body;
        let head = self.compile_function_binder_head(
            signature,
            &wd.param_type_well_defined,
            &wd.defined_params,
            &wd.assumed_dom_facts,
            position,
        )?;
        let return_position = SourcePosition {
            before: self.function_header_stages(signature),
            ..*position
        };
        ensure_object(&signature.ret_set, &wd.ret_set_well_defined)?;
        self.compile_wd(&wd.ret_set_well_defined, &return_position)?;
        let body_position = SourcePosition {
            before: return_position.before + 1,
            ..*position
        };
        ensure_object(&function.equal_to, &wd.body_well_defined)?;
        self.compile_wd(&wd.body_well_defined, &body_position)?;
        let membership = match &wd.body_in_ret_set {
            AnonymousFnBodyInReturnSetProof::CheckedMembership(proof) => proof,
            AnonymousFnBodyInReturnSetProof::EmptyCompleteDomain(_) => {
                return Err(LeanCompileError::unsupported(
                    "Function/EmptyCompleteDomain",
                ))
            }
        };
        match source_subject(membership)? {
            Fact::AtomicFact(AtomicFact::InFact(member))
                if member.element.ir() == function.equal_to.ir()
                    && member.set.ir() == signature.ret_set.ir() => {}
            _ => return Err(LeanCompileError::new(
                "Function/ReturnSubject",
                "The recorded return proof does not establish this body in its declared carrier.",
            )),
        }
        let membership_position = SourcePosition {
            before: body_position.before + 1,
            ..*position
        };
        let member = self.compile_verify(membership, &membership_position)?;
        let h_return = format!(
            "(by\n  {}\n  change {}\n  exact {})",
            head.replace('\n', "\n  "),
            member.0.replace('\n', "\n  "),
            member.1.replace('\n', "\n  ")
        );
        let domains = self.compile_function_domains(signature, position)?;
        let guard = self.compile_function_guard_template(signature, position)?;
        let body = self.compile_function_body_template(function, position)?;
        let constructor = if domains.len() == 2 {
            "formulaFn"
        } else {
            "formulaFn2"
        };
        Ok(format!(
            "(Litex.{constructor} (M := M) {} {guard} {body} {h_return})",
            domains.join(" ")
        ))
    }

    fn compile_function_binder_head(
        &self,
        signature: &FnSet,
        carriers: &[Box<ObjWellDefinedProof>],
        defined: &StoreHaveObjAndInferResult,
        assumed: &[AssumeDomFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_function_domains(signature, position)?;
        let groups = &signature.set_bound_parameters.groups;
        let parameters = groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(|parameter| (parameter, &group.param_type))
            })
            .collect::<Vec<_>>();
        self.validate_parameter_store_capture(defined)?;
        if carriers.len() != groups.len()
            || defined.store_and_infer_results.len() != parameters.len()
            || assumed.len() != signature.dom_facts.len()
        {
            return Err(LeanCompileError::new(
                "Function/BinderArity",
                "Function carrier, parameter and domain captures must match their ordered source stages.",
            ));
        }
        for (index, (group, carrier)) in groups.iter().zip(carriers).enumerate() {
            ensure_object(&group.param_type, carrier)?;
            self.compile_wd(
                carrier,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?;
        }
        let raw = parameters
            .iter()
            .map(|(parameter, _)| format!("_raw_i{}", parameter.id.value()))
            .collect::<Vec<_>>();
        let inputs = defined
            .store_and_infer_results
            .iter()
            .map(|store| format!("h_{}", store.primary_fact_id().value()))
            .collect::<Vec<_>>();
        let introductions = format!("intro {} {}", raw.join(" "), inputs.join(" "));
        let guards = assumed
            .iter()
            .map(|paired| format!("h_{}", paired.store_and_infer.primary_fact_id().value()))
            .collect::<Vec<_>>();
        let mut lines = match guards.len() {
            0 => vec![format!("{introductions} _")],
            1 => vec![format!("{introductions} {}", guards[0])],
            _ => vec![format!(
                "rintro {} {} ⟨{}⟩",
                raw.join(" "),
                inputs.join(" "),
                guards.join(", ")
            )],
        };
        for (index, ((parameter, carrier), store)) in parameters
            .iter()
            .zip(&defined.store_and_infer_results)
            .enumerate()
        {
            let introduced = SourcePosition {
                before: groups.len() + index + 1,
                ..*position
            };
            let fact = self.resolve_fact(store.primary_fact_id(), &introduced)?;
            let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
            match &fact {
                Fact::AtomicFact(AtomicFact::InFact(member))
                    if member.element.ir() == object.ir() && member.set.ir() == carrier.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "Function/ParameterSubject",
                        "A captured function parameter store has another object or carrier.",
                    ))
                }
            }
            self.validate_store(&store.store, &fact)?;
            let id = parameter.id.value();
            let hypothesis = format!("h_{}", fact.fact_id().value());
            lines.push(format!(
                "let _value_i{id} := Litex.semanticObject (M := M) _raw_i{id} (M.member_isSet {hypothesis})"
            ));
            let member = (self.fact_proposition(&fact, &introduced)?, hypothesis);
            lines.push(format!("have {} : {} := {}", member.1, member.0, member.1));
            lines.extend(self.compile_parameter_inferences(store, &fact, &member, &introduced)?);
        }
        for (index, (source, paired)) in signature.dom_facts.iter().zip(assumed).enumerate() {
            let fact = function_guard_fact(source)?;
            let prior = SourcePosition {
                before: groups.len() + parameters.len() + index,
                ..*position
            };
            self.compile_fact_wd(&paired.well_defined, &fact, &prior)?;
            self.validate_store(&paired.store_and_infer.store, &fact)?;
            let formed = SourcePosition {
                parent: Some(&prior),
                owner: SourceOwner::FactWD(&paired.well_defined),
                before: usize::MAX,
            };
            let raw = self.compile_function_raw_clause(&fact, signature, position)?;
            let compiled = (
                self.fact_proposition(&fact, &formed)?,
                format!("(by\n  change {raw}\n  exact {})", guards[index]),
            );
            let completed = SourcePosition {
                before: prior.before + 1,
                ..*position
            };
            lines.push(self.emit_internal_fact(&fact, &compiled, &completed));
            let compiled = (compiled.0, format!("h_{}", fact.fact_id().value()));
            lines.extend(self.compile_set_builder_parameter_inferences(
                &paired.store_and_infer,
                &fact,
                &compiled,
                &completed,
            )?);
            lines.extend(self.compile_stored_inferences(
                &paired.store_and_infer,
                &fact,
                &compiled,
                &completed,
            )?);
        }
        Ok(lines.join("\n"))
    }

    fn function_header_stages(&self, signature: &FnSet) -> usize {
        signature.set_bound_parameters.groups.len()
            + signature
                .set_bound_parameters
                .groups
                .iter()
                .map(|group| group.params.len())
                .sum::<usize>()
            + signature.dom_facts.len()
    }

    fn compile_function_raw_header(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domains = self.compile_function_domains(signature, position)?;
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .collect::<Vec<_>>();
        let variables = parameters
            .iter()
            .map(|parameter| format!("_raw_i{}", parameter.id.value()))
            .collect::<Vec<_>>();
        let binders = variables
            .iter()
            .map(|name| format!("({name} : M.Value)"))
            .collect::<Vec<_>>()
            .join(" ");
        let members = variables
            .iter()
            .zip(&domains)
            .map(|(name, domain)| format!("M.mem {name} (M.standard {domain})"))
            .collect::<Vec<_>>()
            .join(" → ");
        let guard = self.compile_function_guard_template(signature, position)?;
        Ok(format!(
            "∀ {binders}, {members} → ({guard} {}) → True",
            variables.join(" ")
        ))
    }
}
