//! Triangular determinant schemas, their original forall and diagonal callback.
use super::compile_real_set_bounds::contains_parameter;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("TriangularDeterminant/{stage}"))
}
fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
}
fn interval(obj: &Obj, n: &Obj) -> bool {
    matches!(obj,Obj::SetFormer(SetFormer::ClosedRange(s)) if closed_integer(&s.start)==Some(1) && s.end.ir()==n.ir())
}
fn identifier(obj: &Obj, id: IdentifierId) -> bool {
    matches!(obj,Obj::Identifier(IdentifierObj::Plain {id:source,..}) if *source==id)
}
fn matrix_call(obj: &Obj, a: &Obj, row: IdentifierId, col: IdentifierId) -> bool {
    matches!(obj,Obj::FnObj(call) if *call.head==FnObjHead::from_obj(a.clone())
        && matches!(call.body.as_slice(),[args] if matches!(args.as_slice(),[r,c] if identifier(r,row)&&identifier(c,col))))
}
fn validate_forall(fact: &Fact, a: &Obj, n: &Obj, upper: bool) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(all) = fact else {
        return Err(invalid("OriginalForall"));
    };
    let [row_group, col_group] = all.typed_parameters.groups.as_slice() else {
        return Err(invalid("OriginalForallBinders"));
    };
    let [row] = row_group.params.as_slice() else {
        return Err(invalid("OriginalForallBinders"));
    };
    let [col] = col_group.params.as_slice() else {
        return Err(invalid("OriginalForallBinders"));
    };
    for group in [row_group, col_group] {
        if !matches!(&group.param_type,ParamType::Obj(domain) if interval(domain,n)) {
            return Err(invalid("OriginalForallRanges"));
        }
    }
    if row.id == col.id
        || [a, n]
            .iter()
            .any(|o| contains_parameter(o, row.id) || contains_parameter(o, col.id))
    {
        return Err(invalid("ForallBinderIdentity"));
    }
    let [Fact::AtomicFact(AtomicFact::LessFact(guard))] = all.dom_facts.as_slice() else {
        return Err(invalid("OriginalStrictGuard"));
    };
    let (left, right) = if upper {
        (col.id, row.id)
    } else {
        (row.id, col.id)
    };
    if !identifier(&guard.left, left) || !identifier(&guard.right, right) {
        return Err(invalid("OriginalGuardOrientation"));
    }
    if !matches!(all.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e))]
        if matrix_call(&e.left,a,row.id,col.id) && closed_integer(&e.right)==Some(0))
    {
        return Err(invalid("OriginalZeroEntry"));
    }
    Ok(())
}
fn validate_product(obj: &Obj, a: &Obj, n: &Obj) -> Result<(), LeanCompileError> {
    let Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(p)) = obj else {
        return Err(invalid("OriginalDiagonalProduct"));
    };
    if !interval(&p.set, n) {
        return Err(invalid("OriginalProductRange"));
    }
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(g)) = p.func.as_ref() else {
        return Err(invalid("OriginalDiagonalFormula"));
    };
    let [group] = g.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("FormulaBinder"));
    };
    let [parameter] = group.params.as_slice() else {
        return Err(invalid("FormulaBinder"));
    };
    if !interval(&group.param_type, n)
        || g.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C)
        || !g.body.dom_facts.is_empty()
        || [a, n].iter().any(|o| contains_parameter(o, parameter.id))
        || !matrix_call(&g.equal_to, a, parameter.id, parameter.id)
    {
        return Err(invalid("ExactDiagonalFormula"));
    }
    Ok(())
}

pub(super) fn validate_triangular_determinant_law(
    upper: bool,
    args: &[Obj],
    req: &[Fact],
    goal: &EqualFact,
) -> Result<(), LeanCompileError> {
    if args.len() != 2 || req.len() != 4 {
        return Err(invalid("OriginalStages"));
    }
    let (a, n) = (&args[0], &args[1]);
    if !natural(&req[0], n)
        || !natural(&req[1], n)
        || !matches!(&req[2],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==a.ir()
                && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(s))
                    if s.set.as_ref()==&Obj::StandardSet(StandardSet::C) && s.rows.ir()==n.ir() && s.cols.ir()==n.ir()))
    {
        return Err(invalid("OriginalSquareContexts"));
    }
    validate_forall(&req[3], a, n, upper)?;
    if !matches!(&goal.left,Obj::MatrixOperator(MatrixOperator::Determinant(d)) if d.matrix.ir()==a.ir() && d.order.ir()==n.ir())
    {
        return Err(invalid("OriginalDeterminant"));
    }
    validate_product(&goal.right, a, n)?;
    Ok(())
}

pub(super) fn triangular_determinant_law_term(
    upper: bool,
    a: &str,
    n: &str,
    product: &str,
    refs: &[String],
) -> String {
    let (left, right, name) = if upper {
        ("c", "r", "Upper")
    } else {
        ("r", "c", "Lower")
    };
    let row = "(Litex.semanticObject (M := M) r (M.member_isSet hr))";
    let col = "(Litex.semanticObject (M := M) c (M.member_isSet hc))";
    let hr = format!("(by change M.mem (Litex.denote {row}) (Litex.matrixIndexValue {n}); rw [Litex.semanticObject_denote]; exact hr)");
    let hc = format!("(by change M.mem (Litex.denote {col}) (Litex.matrixIndexValue {n}); rw [Litex.semanticObject_denote]; exact hc)");
    let (guard_left, guard_right) = if upper { (col, row) } else { (row, col) };
    let less = format!("(by change Litex.RealLtValue M (Litex.denote {guard_left}) (Litex.denote {guard_right}); simpa only [Litex.semanticObject_denote] using less)");
    let zero=format!("have _triangular_zero : ∀ (r : M.Value), M.mem r (Litex.matrixIndexValue {n}) → ∀ (c : M.Value), M.mem c (Litex.matrixIndexValue {n}) → Litex.RealLtValue M {left} {right} → Litex.FunctionSemantics.callValue (Litex.denote {a}) (Litex.FiniteFunction.pack2 r c) = M.number 0 := by\n    intro r hr c hc less\n    have step := {} {row} {hr} {col} {hc} {less}\n    change Litex.FunctionSemantics.callValue (Litex.denote {a}) (Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col})) = M.number 0 at step\n    simpa only [Litex.semanticObject_denote] using step",refs[3]);
    format!("(by\n  let _diagonal_product := {product}\n  {zero}\n  exact Litex.matrixDeterminant{name}TriangularFormula {a} {n} _diagonal_product.val.function {} {} _triangular_zero (by rfl) (by rfl)\n)",refs[0],refs[2])
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_triangular_determinant(
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
        let upper = match builtin.theorem {
            BuiltinTheoremId::MatrixDetUpperTriangular => true,
            BuiltinTheoremId::MatrixDetLowerTriangular => false,
            _ => return Err(invalid("Theorem")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != 2
            || builtin.requirements.len() != 4
            || dom_proofs.len() != 4
            || dom_stores.len() != 4
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(goal)) = &builtin.conclusions[0] else {
            return Err(invalid("OriginalEquality"));
        };
        let FactWellDefinedProof::Equality(wd) = &conclusions_wd[0] else {
            return Err(invalid("OriginalEqualityWD"));
        };
        let req = &builtin.requirements;
        validate_triangular_determinant_law(upper, args, req, goal)?;
        let (a, n) = (&args[0], &args[1]);
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
            before: 4,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let bindings = self.compile_equal_wd_locals(goal, wd, &formed)?;
        let complete =
            SourcePosition::new(Some(&formed), SourceOwner::EqualWDLocals(wd, 2), usize::MAX);
        let a = self.compile_object_reference(a, &complete)?;
        let n = self.compile_object_reference(n, &complete)?;
        let product = self
            .compile_object_reference(&goal.right, &complete)?
            .replace('\n', "\n  ");
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let proof = triangular_determinant_law_term(upper, &a, &n, &product, &refs);
        let proof = Self::scope_equal_wd_proof(statement.clone(), proof, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
