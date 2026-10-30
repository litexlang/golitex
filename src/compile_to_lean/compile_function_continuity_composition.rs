//! Replay inner/outer continuity, domain mapping and the original composition formula.
use super::compile_function_continuity::continuity_side;
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_continuity_composition(
        &self,
        call: &TheoremCall,
        builtin: &BuiltinThmApplication,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        use BuiltinTheoremId::*;
        let side = match builtin.theorem {
            FnContinuousAtCompose => RealApproachSide::Both,
            FnContinuousLeftCompose => RealApproachSide::Left,
            FnContinuousRightCompose => RealApproachSide::Right,
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != 4
            || builtin.requirements.len() != 16
            || dom_proofs.len() != 16
            || dom_stores.len() != 16
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let req = &builtin.requirements;
        let (inner, _) = real_limit_signature(&req[..3], &args[0])?;
        let (outer, _) = real_limit_signature(&req[4..7], &args[1])?;
        let (output, _) = real_limit_signature(&req[7..10], &args[2])?;
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = &req[10] else {
            return Err(invalid("DomainSubset"));
        };
        if !signature_domain_matches(&subset.left, output)
            || !signature_domain_matches(&subset.right, inner)
        {
            return Err(invalid("DomainSubsetSubject"));
        }
        for (index, domain) in [(3, &subset.right), (11, &subset.left)] {
            if !matches!(&req[index],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[3].ir()&&f.set.ir()==domain.ir())
            {
                return Err(invalid("PointDomain"));
            }
        }
        if !matches!(&req[12],Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) if f.side==side&&f.function.ir()==args[0].ir()&&f.point.ir()==args[3].ir())
            || !matches!(&req[13],Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) if f.side==RealApproachSide::Both&&f.function.ir()==args[1].ir()&&call_matches(&f.point,&args[0],&args[3]))
        {
            return Err(invalid("ContinuityPremises"));
        }
        let Fact::ForallFact(mapping) = &req[14] else {
            return Err(invalid("Mapping"));
        };
        let x = parameter(&mapping.typed_parameters, &subset.left)?;
        let value = Obj::Identifier(IdentifierObj::from_bound_name(x));
        let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(member))] =
            mapping.then_facts.as_slice()
        else {
            return Err(invalid("MappingClause"));
        };
        if !mapping.dom_facts.is_empty()
            || args
                .iter()
                .chain([&subset.left, &subset.right, &member.set])
                .any(|a| contains_parameter(a, x.id))
            || !call_matches(&member.element, &args[0], &value)
            || !signature_domain_matches(&member.set, outer)
        {
            return Err(invalid("MappingSubject"));
        }
        let Fact::ForallFact(formula) = &req[15] else {
            return Err(invalid("Formula"));
        };
        let x = parameter(&formula.typed_parameters, &subset.left)?;
        let value = Obj::Identifier(IdentifierObj::from_bound_name(x));
        if !formula.dom_facts.is_empty()
            || args
                .iter()
                .chain([&subset.left, &subset.right, &member.set])
                .any(|a| contains_parameter(a, x.id))
            || !matches!(formula.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))]
                if call_matches(&eq.left,&args[2],&value)&&composition_matches(&eq.right,&args[1],&args[0],&value))
        {
            return Err(invalid("FormulaSubject"));
        }
        let goal = &builtin.conclusions[0];
        if !matches!(goal,Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) if f.side==side&&f.function.ir()==args[2].ir()&&f.point.ir()==args[3].ir())
        {
            return Err(invalid("Conclusion"));
        }
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: 16,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let mut steps = self.compile_function_limit_context(
            0,
            &args[0],
            &subset.right,
            &req[..3],
            &refs[..3],
            &scope,
        )?;
        steps.extend(self.compile_function_limit_context(
            1,
            &args[1],
            &member.set,
            &req[4..7],
            &refs[4..7],
            &scope,
        )?);
        steps.extend(self.compile_function_limit_context(
            2,
            &args[2],
            &subset.left,
            &req[7..10],
            &refs[7..10],
            &scope,
        )?);
        let object = |a: &Obj| {
            self.compile_object_reference(a, &scope)
                .map(|s| format!("(Litex.denote {s})"))
        };
        steps.push(format!("have _law_subset : ∀ input, M.mem input (Litex.FunctionSemantics.domainValue {}) → M.mem input (Litex.FunctionSemantics.domainValue {}) := by\n  intro input hinput\n  have _law_input : M.mem input (Litex.denote _law2_domain) := _law_domain_2.symm ▸ hinput\n  exact _law_domain_0 ▸ ({} input _law_input)",object(&args[2])?,object(&args[0])?,refs[10]));
        steps.push(format!("have _law_maps : ∀ input, M.mem input (Litex.FunctionSemantics.domainValue {}) → M.mem (Litex.FunctionSemantics.callValue {} input) (Litex.FunctionSemantics.domainValue {}) := by\n  intro input hinput\n  have _law_input : M.mem input (Litex.denote _law2_domain) := _law_domain_2.symm ▸ hinput\n  exact _law_domain_1 ▸ ({} (Litex.semanticObject input (M.member_isSet _law_input)) _law_input)",object(&args[2])?,object(&args[0])?,object(&args[1])?,refs[14]));
        let point_member = format!(
            "(show M.mem {} (Litex.FunctionSemantics.domainValue {}) from _law_domain_2 ▸ {})",
            object(&args[3])?,
            object(&args[2])?,
            refs[11]
        );
        let formula=format!("(by\n  intro input hinput\n  have _law_input : M.mem input (Litex.denote _law2_domain) := _law_domain_2.symm ▸ hinput\n  exact {} (Litex.semanticObject input (M.member_isSet _law_input)) _law_input\n)",refs[15]);
        let side = continuity_side(side);
        steps.push(format!("exact Litex.functionContinuousAtCompose .{side} {} {} {} {} _law_real_0 _law_real_1 _law_real_2 _law_subset {point_member} _law_maps {formula} {} {}",object(&args[0])?,object(&args[1])?,object(&args[2])?,object(&args[3])?,refs[12],refs[13]));
        Ok((
            definitions,
            format!(
                "(show {statement} from by\n  {}\n)",
                steps.join("\n").replace('\n', "\n  ")
            ),
            builtin.conclusions.clone(),
        ))
    }
}
fn composition_matches(object: &Obj, outer: &Obj, inner: &Obj, input: &Obj) -> bool {
    let Obj::FnObj(call) = object else {
        return false;
    };
    let [args] = call.body.as_slice() else {
        return false;
    };
    let [value] = args.as_slice() else {
        return false;
    };
    call_matches(object, outer, value) && call_matches(value, inner, input)
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ContinuityComposition/{stage}"))
}
