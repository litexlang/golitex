//! Laplace determinant schemas and their original cofactor summand.
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
    LeanCompileError::unsupported(&format!("LaplaceDeterminant/{stage}"))
}
fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
}
fn interval(obj: &Obj, n: &Obj) -> bool {
    matches!(obj,Obj::SetFormer(SetFormer::ClosedRange(s)) if closed_integer(&s.start)==Some(1) && s.end.ir()==n.ir())
}
fn same(obj: &Obj, fixed: &Obj, variable: IdentifierId, bound: bool) -> bool {
    if bound {
        matches!(obj,Obj::Identifier(IdentifierObj::Plain {id,..}) if *id==variable)
    } else {
        obj.ir() == fixed.ir()
    }
}
fn validate_sum(
    obj: &Obj,
    a: &Obj,
    n: &Obj,
    fixed: &Obj,
    row: bool,
) -> Result<(), LeanCompileError> {
    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(p)) = obj else {
        return Err(invalid("OriginalLaplaceSum"));
    };
    if !interval(&p.set, n) {
        return Err(invalid("OriginalSumRange"));
    }
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(g)) = p.func.as_ref() else {
        return Err(invalid("OriginalSummandFormula"));
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
        || [a, n, fixed]
            .iter()
            .any(|o| contains_parameter(o, parameter.id))
    {
        return Err(invalid("OriginalFormulaDomain"));
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(term)) = g.equal_to.as_ref() else {
        return Err(invalid("OriginalProductTerm"));
    };
    let Obj::FnObj(call) = term.left.as_ref() else {
        return Err(invalid("OriginalMatrixEntry"));
    };
    if *call.head != FnObjHead::from_obj(a.clone())
        || !matches!(call.body.as_slice(),[args] if matches!(args.as_slice(),[r,c]
            if same(r,fixed,parameter.id,!row) && same(c,fixed,parameter.id,row)))
    {
        return Err(invalid("OriginalMatrixEntry"));
    }
    if !matches!(term.right.as_ref(),Obj::MatrixOperator(MatrixOperator::Cofactor(c))
        if c.matrix.ir()==a.ir() && c.order.ir()==n.ir()
            && same(&c.row,fixed,parameter.id,!row) && same(&c.col,fixed,parameter.id,row))
    {
        return Err(invalid("OriginalCofactor"));
    }
    Ok(())
}

pub(super) fn validate_laplace_determinant_law(
    row: bool,
    args: &[Obj],
    req: &[Fact],
    goal: &EqualFact,
) -> Result<(), LeanCompileError> {
    if args.len() != 3 || req.len() != 5 {
        return Err(invalid("OriginalStages"));
    }
    let (a, n, fixed) = (&args[0], &args[1], &args[2]);
    if !natural(&req[0], n)
        || !natural(&req[1], n)
        || !matches!(&req[2],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==a.ir()
                && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(s))
                    if s.set.as_ref()==&Obj::StandardSet(StandardSet::C) && s.rows.ir()==n.ir() && s.cols.ir()==n.ir()))
    {
        return Err(invalid("OriginalSquareContexts"));
    }
    if !matches!(&req[3],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::NPos))
        || !matches!(&req[4],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==fixed.ir() && interval(&f.set,n))
    {
        return Err(invalid("OriginalPositiveOrderAndIndex"));
    }
    if !matches!(&goal.left,Obj::MatrixOperator(MatrixOperator::Determinant(d)) if d.matrix.ir()==a.ir() && d.order.ir()==n.ir())
    {
        return Err(invalid("OriginalDeterminant"));
    }
    validate_sum(&goal.right, a, n, fixed, row)?;
    Ok(())
}

pub(super) fn laplace_determinant_law_term(
    row: bool,
    a: &str,
    n: &str,
    fixed: &str,
    sum: &str,
    refs: &[String],
) -> String {
    let name = if row { "Row" } else { "Column" };
    format!("(by\n  let _laplace_sum := {sum}\n  exact Litex.matrixDeterminantLaplace{name}Formula {a} {n} {fixed} _laplace_sum.val.function {} {} {} {} (by rfl) (by rfl)\n)",refs[0],refs[2],refs[3],refs[4])
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_laplace_determinant(
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
        let row = match builtin.theorem {
            BuiltinTheoremId::MatrixDetLaplaceRow => true,
            BuiltinTheoremId::MatrixDetLaplaceColumn => false,
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
            || args.len() != 3
            || builtin.requirements.len() != 5
            || dom_proofs.len() != 5
            || dom_stores.len() != 5
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
        validate_laplace_determinant_law(row, args, req, goal)?;
        let (a, n, fixed) = (&args[0], &args[1], &args[2]);
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
            before: 5,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let bindings = self.compile_equal_wd_locals(goal, wd, &formed)?;
        let complete =
            SourcePosition::new(Some(&formed), SourceOwner::EqualWDLocals(wd, 2), usize::MAX);
        let a = self.compile_object_reference(a, &complete)?;
        let n = self.compile_object_reference(n, &complete)?;
        let fixed = self.compile_object_reference(fixed, &complete)?;
        let sum = self
            .compile_object_reference(&goal.right, &complete)?
            .replace('\n', "\n  ");
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let proof = laplace_determinant_law_term(row, &a, &n, &fixed, &sum, &refs);
        let proof = Self::scope_equal_wd_proof(statement.clone(), proof, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
