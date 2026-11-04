//! Replay the original rank-sized four-matrix existential schema.
use super::compile_real_set_bounds::contains_parameter;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef;
use crate::prelude::*;
use std::collections::HashSet;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RankExistence/{stage}"))
}
fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
}
fn matrix_space(obj: &Obj, rows: &Obj, cols: &Obj) -> bool {
    matches!(obj,Obj::SetFormer(SetFormer::MatrixSet(s))
        if s.set.as_ref()==&Obj::StandardSet(StandardSet::C)
            && s.rows.ir()==rows.ir() && s.cols.ir()==cols.ir())
}
fn product(obj: &Obj, a: &Obj, b: &Obj, m: &Obj, k: &Obj, n: &Obj) -> bool {
    matches!(obj,Obj::MatrixOperator(MatrixOperator::Multiply(p))
        if p.left.ir()==a.ir() && p.right.ir()==b.ir()
            && p.rows.ir()==m.ir() && p.inner.ir()==k.ir() && p.cols.ir()==n.ir())
}
fn split_identity(fact: &AtomicFact, a: &Obj, b: &Obj, k: &Obj, inner: &Obj) -> bool {
    matches!(fact,AtomicFact::EqualFact(f)
        if product(&f.left,a,b,k,inner,k)
            && matches!(&f.right,Obj::MatrixOperator(MatrixOperator::IdentityMatrix(i)) if i.order.ir()==k.ir()))
}
fn validate_exist<'a>(
    fact: &'a Fact,
    a: &Obj,
    m: &Obj,
    n: &Obj,
) -> Result<&'a Obj, LeanCompileError> {
    let Fact::ExistFact(exists) = fact else {
        return Err(invalid("OriginalExistential"));
    };
    let [ug, vg, lg, rg] = exists.typed_parameters.groups.as_slice() else {
        return Err(invalid("FourBinderGroups"));
    };
    let ParamType::Obj(Obj::SetFormer(SetFormer::MatrixSet(first))) = &ug.param_type else {
        return Err(invalid("OriginalMatrixDomain"));
    };
    let k = first.cols.as_ref();
    if !matches!(k,Obj::MatrixOperator(MatrixOperator::Rank(r))
        if r.matrix.ir()==a.ir() && r.rows.ir()==m.ir() && r.cols.ir()==n.ir())
    {
        return Err(invalid("OriginalRankDimension"));
    }
    let mut ids = HashSet::new();
    let mut witnesses = Vec::new();
    for (group, rows, cols) in [(ug, m, k), (vg, k, n), (lg, k, m), (rg, n, k)] {
        let [parameter] = group.params.as_slice() else {
            return Err(invalid("FourWitnesses"));
        };
        if !ids.insert(parameter.id)
            || [a, m, n]
                .iter()
                .any(|obj| contains_parameter(obj, parameter.id))
        {
            return Err(invalid("WitnessIdentityOrCapture"));
        }
        if !matches!(&group.param_type,ParamType::Obj(domain) if matrix_space(domain,rows,cols)) {
            return Err(invalid("FourOriginalMatrixDomains"));
        }
        witnesses.push(Obj::Identifier(IdentifierObj::from_bound_name(parameter)));
    }
    let [QuantifierFreeFact::AndFact(body)] = exists.facts.as_slice() else {
        return Err(invalid("OriginalConjunction"));
    };
    let [factor, left, right] = body.facts.as_slice() else {
        return Err(invalid("ThreeOriginalEqualities"));
    };
    if !matches!(factor,AtomicFact::EqualFact(f) if f.left.ir()==a.ir()
        && product(&f.right,&witnesses[0],&witnesses[1],m,k,n))
        || !split_identity(left, &witnesses[2], &witnesses[0], k, m)
        || !split_identity(right, &witnesses[1], &witnesses[3], k, n)
    {
        return Err(invalid("OriginalFactorizationAndSplittings"));
    }
    Ok(k)
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_rank_existence(
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
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if builtin.theorem != BuiltinTheoremId::MatrixRankFactorizationExists
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != 3
            || builtin.requirements.len() != 3
            || dom_proofs.len() != 3
            || dom_stores.len() != 3
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let (a, m, n) = (&args[0], &args[1], &args[2]);
        let req = &builtin.requirements;
        if !natural(&req[0], m)
            || !natural(&req[1], n)
            || !matches!(&req[2],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==a.ir() && matrix_space(&f.set,m,n))
        {
            return Err(invalid("OriginalMatrixContext"));
        }
        let fact = &builtin.conclusions[0];
        let k = validate_exist(fact, a, m, n)?;
        let FactWellDefinedProof::ExistFact(formation) = &conclusions_wd[0] else {
            return Err(invalid("OriginalExistentialWD"));
        };
        let mut definitions = Vec::new();
        let mut refs = Vec::new();
        for (index, ((requirement, checked), stored)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("OriginalProofSubject"));
            }
            self.validate_store(&stored.store, requirement)?;
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            let reference = format!("h_{}", requirement.fact_id().value());
            definitions.extend(self.compile_stored_inferences(
                stored,
                requirement,
                &(compiled.0, reference.clone()),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
            refs.push(reference);
        }
        let formed = SourcePosition {
            before: 3,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], fact, &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let statement = self.compile_formed_fact_proposition(&conclusions_wd[0], fact, &formed)?;
        let first = formation
            .detailed_ref()
            .introduced_params
            .param_type_well_defined
            .first()
            .ok_or_else(|| invalid("OriginalFirstDomainWD"))?;
        let ParamTypeWellDefinedProof::Obj(matrix_wd) = first else {
            return Err(invalid("OriginalFirstDomainWD"));
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::MatrixSet(
                    matrix_wd_children,
                )),
            ..
        } = matrix_wd.detailed_ref()
        else {
            return Err(invalid("OriginalMatrixDomainWD"));
        };
        let [_, _, rank_wd] = matrix_wd_children.child_obj_well_defined.as_slice() else {
            return Err(invalid("OriginalRankWD"));
        };
        ensure_object(k, rank_wd)?;
        // The first carrier is formed before any existential witness exists.
        let rank_scope = SourcePosition::new(Some(&formed), SourceOwner::WD(matrix_wd), 2);
        let rank = self.compile_wd(rank_wd, &rank_scope)?.replace('\n', "\n  ");
        let a = self.compile_object_reference(a, &scope)?;
        let m = self.compile_object_reference(m, &scope)?;
        let n = self.compile_object_reference(n, &scope)?;
        let proof=format!("(show {statement} from (by\n  let _rank_dimension := {rank}\n  rcases Litex.matrixRankFactorizationExists {a} {m} {n} _rank_dimension {} {} {} (by rfl) with ⟨_rank_u, _rank_hu, _rank_v, _rank_hv, _rank_l, _rank_hl, _rank_r, _rank_hr, _rank_hk, _rank_product, _rank_left, _rank_right⟩\n  exact ⟨_rank_u, _rank_hu, _rank_v, _rank_hv, _rank_l, _rank_hl, _rank_r, _rank_hr, _rank_product, _rank_left, _rank_right⟩\n))",refs[0],refs[1],refs[2]);
        Ok((definitions, proof, builtin.conclusions.clone()))
    }
}
