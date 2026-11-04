//! Exact ordered partition clauses; no enclosure or domain proof search.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_riemann_definition::index_signature;
use super::compile_riemann_integral::{is_enclosure, validate_domain_requirement};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::real_analysis::analysis_apply as call;
use crate::execute::execute_fact_stmt::riemann_integral::helper::{
    id, integer_interval, interval, num, sub,
};
use crate::prelude::*;
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DarbouxDefinition/{stage}"))
}
fn le(fact: &AtomicFact, left: &Obj, right: &Obj) -> bool {
    matches!(fact,AtomicFact::LessEqualFact(p) if p.left.ir()==left.ir() && p.right.ir()==right.ir())
}
fn validate_clauses(args: &[Obj], clauses: &[Fact]) -> Result<(), LeanCompileError> {
    let [f, a, b, n, p, lower, upper] = args else {
        return Err(invalid("Arity"));
    };
    if clauses.len() != 9 {
        return Err(invalid("Clauses"));
    }
    if !matches!(&clauses[0],Fact::AtomicFact(AtomicFact::LessFact(q)) if q.left.ir()==a.ir() && q.right.ir()==b.ir())
        || !matches!(&clauses[1],Fact::AtomicFact(AtomicFact::InFact(q)) if q.element.ir()==n.ir() && q.set==Obj::StandardSet(StandardSet::NPos))
    {
        return Err(invalid("OrderAndSize"));
    }
    for (i, object, start) in [(2, p, "0"), (3, lower, "1"), (4, upper, "1")] {
        let Fact::AtomicFact(AtomicFact::InFact(q)) = &clauses[i] else {
            return Err(invalid("FunctionMembership"));
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &q.set else {
            return Err(invalid("FunctionCarrier"));
        };
        if q.element.ir() != object.ir() {
            return Err(invalid("FunctionSubject"));
        }
        index_signature(signature, &num(start), n)?;
    }
    for (i, input, value) in [(5, num("0"), a), (6, n.clone(), b)] {
        if !matches!(&clauses[i],Fact::AtomicFact(AtomicFact::EqualFact(q)) if q.left.ir()==call(p.clone(),input).ir() && q.right.ir()==value.ir())
        {
            return Err(invalid("PartitionEndpoints"));
        }
    }
    let Fact::ForallFact(order) = &clauses[7] else {
        return Err(invalid("PartitionOrder"));
    };
    let k = parameter(
        &order.typed_parameters,
        &integer_interval(num("1"), n.clone()),
    )?;
    if !order.dom_facts.is_empty() || args.iter().any(|o| contains_parameter(o, k.id)) {
        return Err(invalid("PartitionOrderScope"));
    }
    let left = call(p.clone(), sub(id(k), num("1")));
    let right = call(p.clone(), id(k));
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessFact(step)), ExistOrAndChainAtomicFact::AtomicFact(first), ExistOrAndChainAtomicFact::AtomicFact(last)] =
        order.then_facts.as_slice()
    else {
        return Err(invalid("PartitionOrderConclusions"));
    };
    if step.left.ir() != left.ir()
        || step.right.ir() != right.ir()
        || !le(first, a, &left)
        || !le(last, &right, b)
    {
        return Err(invalid("PartitionOrderSubjects"));
    }
    let Fact::ForallFact(bounds) = &clauses[8] else {
        return Err(invalid("CellBounds"));
    };
    let [kg, xg] = bounds.typed_parameters.groups.as_slice() else {
        return Err(invalid("CellParameters"));
    };
    let ([k], [x], ParamType::Obj(ks), ParamType::Obj(xs)) = (
        kg.params.as_slice(),
        xg.params.as_slice(),
        &kg.param_type,
        &xg.param_type,
    ) else {
        return Err(invalid("CellArity"));
    };
    if ks.ir() != integer_interval(num("1"), n.clone()).ir()
        || xs.ir() != interval(a.clone(), b.clone()).ir()
        || k.id == x.id
        || args
            .iter()
            .any(|o| contains_parameter(o, k.id) || contains_parameter(o, x.id))
    {
        return Err(invalid("CellCarriersAndScope"));
    }
    let left = call(p.clone(), sub(id(k), num("1")));
    let right = call(p.clone(), id(k));
    let [Fact::AtomicFact(lo), Fact::AtomicFact(hi)] = bounds.dom_facts.as_slice() else {
        return Err(invalid("CellGuards"));
    };
    let [ExistOrAndChainAtomicFact::AtomicFact(lb), ExistOrAndChainAtomicFact::AtomicFact(ub)] =
        bounds.then_facts.as_slice()
    else {
        return Err(invalid("CellConclusions"));
    };
    if !le(lo, &left, &id(x))
        || !le(hi, &id(x), &right)
        || !le(lb, &call(lower.clone(), id(k)), &call(f.clone(), id(x)))
        || !le(ub, &call(f.clone(), id(x)), &call(upper.clone(), id(k)))
    {
        return Err(invalid("CellBoundSubjects"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_darboux_definition(
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
        let (fold, count, outputs) = match builtin.theorem {
            DarbouxEnclosureFromDefinition => (true, 12, 1),
            DarbouxEnclosureToDefinition => (false, 4, 9),
            _ => return Err(invalid("Identity")),
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
            || args.len() != 7
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != outputs
            || conclusions_wd.len() != outputs
        {
            return Err(invalid("OriginalStages"));
        }
        let candidate = if fold {
            &builtin.conclusions[0]
        } else {
            &builtin.requirements[3]
        };
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(source)) = candidate else {
            return Err(invalid("PositiveEnclosure"));
        };
        if !is_enclosure(&source.predicate)
            || source.body.len() != 7
            || !source.body.iter().zip(args).all(|(a, b)| a.ir() == b.ir())
        {
            return Err(invalid("OriginalArguments"));
        }
        validate_clauses(
            args,
            if fold {
                &builtin.requirements[3..]
            } else {
                &builtin.conclusions
            },
        )?;
        let (definitions, refs) = self.compile_function_limit_requirements(
            &builtin.requirements,
            dom_proofs,
            dom_stores,
            position,
        )?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        for (fact, wd) in builtin.conclusions.iter().zip(conclusions_wd) {
            self.compile_fact_wd(wd, fact, &formed)?;
        }
        let (domain, real, _) = if fold {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                return Err(invalid("OriginalFormation"));
            };
            self.riemann_certificate_domain(
                &AtomicFact::NormalAtomicFact(source.clone()),
                wd,
                &formed,
            )?
        } else {
            let VerifyFactResult::AtomicExceptEquality(p) = &dom_proofs[3] else {
                return Err(invalid("OriginalProof"));
            };
            let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
                return Err(invalid("OriginalSuccess"));
            };
            self.riemann_certificate_domain(
                &p.fact,
                &p.well_defined_proof,
                &SourcePosition {
                    before: 3,
                    ..*position
                },
            )?
        };
        for (i, r) in builtin.requirements[..3].iter().enumerate() {
            validate_domain_requirement(r, i, &args[1], &args[2], &domain)?;
        }
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let raw = args
            .iter()
            .map(|o| self.compile_function_raw_expression_bound(o, &scope, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let statements = builtin
            .conclusions
            .iter()
            .zip(conclusions_wd)
            .map(|(f, w)| self.compile_formed_fact_proposition(w, f, &formed))
            .collect::<Result<Vec<_>, _>>()?;
        let all = raw.join(" ");
        let proof = if fold {
            let mut clauses = refs[3..].to_vec();
            clauses[7] = format!(
                "(by\n  intro k hk\n  exact {} (Litex.semanticObject k (M.member_isSet hk)) hk\n)",
                refs[10]
            );
            clauses[8]=format!("(by\n  intro k hk x hx hlo hhi\n  exact {} (Litex.semanticObject k (M.member_isSet hk)) hk (Litex.semanticObject x (M.member_isSet hx)) hx hlo hhi\n)",refs[11]);
            format!(
                "Litex.darbouxEnclosureFromDefiningClauses {all} ⟨{}⟩",
                clauses.join(", ")
            )
        } else {
            let terms=statements.iter().enumerate().map(|(i,statement)| {
                let projection=conjunction_projection("_darboux_clauses",i,9);
                let term=if i==7 {
                    format!("(by\n  intro _KHost _KRep k hk\n  exact {projection} (Litex.denote k) hk\n)")
                } else if i==8 {
                    format!("(by\n  intro _KHost _KRep k hk _XHost _XRep x hx hlo hhi\n  exact {projection} (Litex.denote k) hk (Litex.denote x) hx hlo hhi\n)")
                } else {projection};
                format!("(show {statement} from {term})")
            }).collect::<Vec<_>>();
            format!("(by\n  have _darboux_clauses := Litex.darbouxEnclosureDefiningClauses {all} {}\n  exact ⟨{}⟩\n)",refs[3],terms.join(", "))
        };
        let statement = conjunction_proposition(statements)?;
        Ok((definitions,format!("(show {statement} from (by\n  have _darboux_original_real := {real}\n  exact {proof}\n))"),builtin.conclusions.clone()))
    }
}
