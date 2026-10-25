use crate::compile_to_lean::compile_function_template::function_guard_fact;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::{
    function_application, function_domains_alpha_equal, CompleteFunctionDomainSourceProof,
    FunctionDomainComparisonProof, FunctionDomainMatchProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_builtin_function_membership(
        &self,
        member: &InFact,
        domain: &FunctionDomainMatchProof,
        domain_equality: &str,
        requirements: &[Fact],
        references: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let source = &domain.source.signature;
        let target = &domain.target;
        let target_obj = Obj::FunctionSpace(FunctionSpace::FnSet(target.clone()));
        let target_matches = match &member.set {
            Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) => {
                Self::validate_finite_seq_signature(sequence, target)?;
                true
            }
            _ => member.set.ir() == target_obj.ir(),
        };
        if !target_matches {
            return Err(LeanCompileError::unsupported(
                "FunctionTheorem/CompleteDomain",
            ));
        }
        if let CompleteFunctionDomainSourceProof::FiniteFunction(finite) = &domain.source.source {
            if !matches!(
                domain.comparison,
                FunctionDomainComparisonProof::AlphaEquivalent
            ) || !function_domains_alpha_equal(source, target)
            {
                return Err(LeanCompileError::unsupported(
                    "FiniteMembership/CompleteDomain",
                ));
            }
            return self.compile_finite_function_membership(
                member,
                domain,
                finite,
                requirements,
                references,
                position,
            );
        }
        let source_signature = self.compile_fn_signature(source, position)?;
        let source_member =
            self.compile_complete_domain_member(&member.element, &domain.source, position)?;
        let body = self.compile_function_return_forall(
            &member.element,
            target,
            requirements,
            references,
            position,
        )?;
        Ok(format!("(by\n  let _source_signature := {source_signature}\n  have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := {source_member}\n  have _same_domain : _source_signature.domain = _membership_target.val.domain := {domain_equality}\n  change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)\n  have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member\n  rw [_same_domain] at _source_graph\n  apply Litex.FunctionSemantics.fnSet_of_returns _source_graph\n  {})", body.replace('\n', "\n  ")))
    }

    pub(in crate::compile_to_lean) fn compile_function_return_forall(
        &self,
        function: &Obj,
        target: &FnSet,
        requirements: &[Fact],
        references: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [Fact::ForallFact(forall)] = requirements else {
            return Err(LeanCompileError::unsupported(
                "FunctionTheorem/ReturnForall",
            ));
        };
        if references.len() != 1
            || forall.typed_parameters.groups.len() != target.set_bound_parameters.groups.len()
            || forall.dom_facts.len() != target.dom_facts.len()
            || forall.then_facts.len() != 1
        {
            return Err(LeanCompileError::unsupported(
                "FunctionTheorem/ReturnStages",
            ));
        }
        for (group, expected) in forall
            .typed_parameters
            .groups
            .iter()
            .zip(&target.set_bound_parameters.groups)
        {
            if group.params != expected.params
                || !matches!(&group.param_type, ParamType::Obj(set) if set.ir() == expected.param_type.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "FunctionTheorem/ReturnParameters",
                ));
            }
        }
        for (fact, expected) in forall.dom_facts.iter().zip(&target.dom_facts) {
            if fact.ir() != function_guard_fact(expected)?.ir() {
                return Err(LeanCompileError::unsupported("FunctionTheorem/ReturnGuard"));
            }
        }
        let parameters = target
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
            .collect::<Vec<_>>();
        if !(1..=2).contains(&parameters.len()) {
            return Err(LeanCompileError::unsupported("FunctionTheorem/Arity"));
        }
        let call = function_application(
            function,
            parameters
                .iter()
                .map(|(p, _)| Box::new(Obj::Identifier(IdentifierObj::from_bound_name(p))))
                .collect(),
        )
        .map_err(|e| LeanCompileError::new("FunctionTheorem/Call", &e))?;
        if !matches!(&forall.then_facts[0], ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(ret))
            if ret.element.ir() == call.ir() && ret.set.ir() == target.ret_set.ir())
        {
            return Err(LeanCompileError::unsupported(
                "FunctionTheorem/ReturnSubject",
            ));
        }
        let positive = self.compile_function_positive_inputs(target, position)?;
        let guard_count = positive.len() + target.dom_facts.len();
        let mut body = vec![
            "intro _input _hin".to_string(),
            "change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin".to_string(),
            "obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin"
                .to_string(),
        ];
        if parameters.len() == 1 {
            body.push("let _raw_0 := _input".into());
            body.push("have _member_0 := _members".into());
        } else {
            body.push("obtain ⟨_raw_0, _member_0, _raw_1, _member_1, rfl⟩ := (Litex.FiniteFunction.cart2_members _ _ _).mp _members".into());
            body.push("simp only [Litex.FiniteFunction.unpack_pack2] at _guard".into());
        }
        let mut arguments = Vec::new();
        for (index, (parameter, _)) in parameters.iter().enumerate() {
            body.push(format!("let _arg_{index} := Litex.semanticObject (M := M) _raw_{index} (M.member_isSet _member_{index})"));
            let membership = if let Some(guard_index) =
                positive.iter().position(|id| *id == parameter.id)
            {
                let guard = conjunction_projection("_guard", guard_index, guard_count);
                format!("((Litex.positiveReal_members (M := M) _raw_{index}).mpr ⟨_member_{index}, {guard}⟩)")
            } else {
                format!("_member_{index}")
            };
            arguments.push(format!("_arg_{index} {membership}"));
        }
        for index in 0..target.dom_facts.len() {
            arguments.push(conjunction_projection(
                "_guard",
                positive.len() + index,
                guard_count,
            ));
        }
        body.push(format!("exact {} {}", references[0], arguments.join(" ")));
        Ok(body.join("\n"))
    }
}
