//! Trace laws consume their own recorded schemas, including repeated premises.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

#[derive(Clone, Copy)]
pub(super) enum TraceLaw {
    Add,
    Scale,
    Cyclic,
}

fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir() == n.ir() && f.set == Obj::StandardSet(StandardSet::N))
}
fn matrix(fact: &Fact, a: &Obj, rows: &Obj, cols: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == a.ir()
        && matches!(&f.set, Obj::SetFormer(SetFormer::MatrixSet(m))
            if m.set.as_ref() == &Obj::StandardSet(StandardSet::C)
                && m.rows.ir() == rows.ir() && m.cols.ir() == cols.ir()))
}
fn trace(object: &Obj, a: &Obj, n: &Obj) -> bool {
    matches!(object, Obj::MatrixOperator(MatrixOperator::Trace(p))
        if p.matrix.ir() == a.ir() && p.order.ir() == n.ir())
}
fn product(object: &Obj, a: &Obj, b: &Obj, rows: &Obj, inner: &Obj, cols: &Obj) -> bool {
    matches!(object, Obj::MatrixOperator(MatrixOperator::Multiply(p))
        if p.left.ir() == a.ir() && p.right.ir() == b.ir() && p.rows.ir() == rows.ir()
            && p.inner.ir() == inner.ir() && p.cols.ir() == cols.ir())
}

pub(super) fn validate_trace_law(
    kind: TraceLaw,
    args: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    let (arity, count) = match kind {
        TraceLaw::Add => (3, 6),
        TraceLaw::Scale => (3, 4),
        TraceLaw::Cyclic => (4, 6),
    };
    if args.len() != arity || requirements.len() != count {
        return Err(LeanCompileError::unsupported("Trace/Stages"));
    }
    let Obj::MatrixOperator(MatrixOperator::Trace(left)) = &conclusion.left else {
        return Err(LeanCompileError::unsupported("Trace/Conclusion"));
    };
    let (subject_matches, premises_match) = match kind {
        TraceLaw::Add => {
            let (a, b, n) = (&args[0], &args[1], &args[2]);
            let subject = matches!(left.matrix.as_ref(), Obj::MatrixOperator(MatrixOperator::Add(p))
                if p.left.ir() == a.ir() && p.right.ir() == b.ir()
                    && p.rows.ir() == n.ir() && p.cols.ir() == n.ir())
                && left.order.ir() == n.ir()
                && matches!(&conclusion.right, Obj::ArithmeticOperator(ArithmeticOperator::Add(p))
                    if trace(&p.left, a, n) && trace(&p.right, b, n));
            let premises = natural(&requirements[0], n)
                && natural(&requirements[1], n)
                && matrix(&requirements[2], a, n, n)
                && natural(&requirements[3], n)
                && natural(&requirements[4], n)
                && matrix(&requirements[5], b, n, n);
            (subject, premises)
        }
        TraceLaw::Scale => {
            let (z, a, n) = (&args[0], &args[1], &args[2]);
            let subject = matches!(left.matrix.as_ref(), Obj::MatrixOperator(MatrixOperator::Scale(p))
                if p.scalar.ir() == z.ir() && p.matrix.ir() == a.ir()
                    && p.rows.ir() == n.ir() && p.cols.ir() == n.ir())
                && left.order.ir() == n.ir()
                && matches!(&conclusion.right, Obj::ArithmeticOperator(ArithmeticOperator::Mul(p))
                    if p.left.ir() == z.ir() && trace(&p.right, a, n));
            let premises = natural(&requirements[0], n)
                && natural(&requirements[1], n)
                && matrix(&requirements[2], a, n, n)
                && matches!(&requirements[3], Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir() == z.ir() && f.set == Obj::StandardSet(StandardSet::C));
            (subject, premises)
        }
        TraceLaw::Cyclic => {
            let (a, b, m, n) = (&args[0], &args[1], &args[2], &args[3]);
            let subject = product(&left.matrix, a, b, m, n, m)
                && left.order.ir() == m.ir()
                && matches!(&conclusion.right, Obj::MatrixOperator(MatrixOperator::Trace(right))
                    if product(&right.matrix, b, a, n, m, n) && right.order.ir() == n.ir());
            let premises = natural(&requirements[0], m)
                && natural(&requirements[1], n)
                && matrix(&requirements[2], a, m, n)
                && natural(&requirements[3], n)
                && natural(&requirements[4], m)
                && matrix(&requirements[5], b, n, m);
            (subject, premises)
        }
    };
    if !subject_matches {
        return Err(LeanCompileError::unsupported("Trace/Subjects"));
    }
    if !premises_match {
        return Err(LeanCompileError::unsupported("Trace/Premise"));
    }
    Ok(count)
}

pub(super) fn trace_law_term(kind: TraceLaw, root: &str, statement: &str) -> String {
    let law = match kind {
        TraceLaw::Add => "Litex.matrixTraceAdd _trace.val.matrix.val.left _trace.val.matrix.val.right _trace.val.order _trace.wd.1 _trace.val.matrix.wd.2.2.1 _trace.val.matrix.wd.2.2.2",
        TraceLaw::Scale => "Litex.matrixTraceScale _trace.val.matrix.val.scalar _trace.val.matrix.val.matrix _trace.val.order _trace.val.matrix.wd.1 _trace.wd.1 _trace.val.matrix.wd.2.2.2",
        TraceLaw::Cyclic => "Litex.matrixTraceCyclic _trace.val.matrix.val.left _trace.val.matrix.val.right _trace.val.order _trace.val.matrix.val.inner _trace.wd.1 _trace.val.matrix.wd.2.1 _trace.val.matrix.wd.2.2.2.1 _trace.val.matrix.wd.2.2.2.2",
    };
    format!("(show {statement} from by\n  let _trace := {root}\n  exact {law}\n)")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_trace_theorem(
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
        let linear = match builtin.theorem {
            BuiltinTheoremId::MatrixTraceLinearity => true,
            BuiltinTheoremId::MatrixTraceCyclic => false,
            _ => return Err(LeanCompileError::unsupported("Trace/Theorem")),
        };
        let count = if linear { 7 } else { 6 };
        let clauses = if linear { 2 } else { 1 };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(LeanCompileError::unsupported("Trace/Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != 4
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != clauses
            || conclusions_wd.len() != clauses
        {
            return Err(LeanCompileError::unsupported("Trace/TheoremStages"));
        }
        let mut kinds = Vec::new();
        for (index, fact) in builtin.conclusions.iter().enumerate() {
            let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = fact else {
                return Err(LeanCompileError::unsupported("Trace/Conclusion"));
            };
            let kind = if !linear {
                TraceLaw::Cyclic
            } else if index == 0 {
                TraceLaw::Add
            } else {
                TraceLaw::Scale
            };
            if linear {
                // Pure views of actual schema subjects, never new execution or
                // verification results. Every original requirement is replayed
                // below in its original seven-stage order.
                if index == 0 {
                    validate_trace_law(
                        kind,
                        &[args[0].clone(), args[1].clone(), args[3].clone()],
                        &builtin.requirements[..6],
                        conclusion,
                    )?;
                } else {
                    validate_trace_law(
                        kind,
                        &[args[2].clone(), args[0].clone(), args[3].clone()],
                        &[
                            builtin.requirements[0].clone(),
                            builtin.requirements[1].clone(),
                            builtin.requirements[2].clone(),
                            builtin.requirements[6].clone(),
                        ],
                        conclusion,
                    )?;
                }
            } else {
                validate_trace_law(kind, args, &builtin.requirements, conclusion)?;
            }
            kinds.push(kind);
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(LeanCompileError::unsupported("Trace/RequirementIdentity"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, format!("h_{}", requirement.fact_id().value())),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let mut proofs = Vec::new();
        for ((fact, wd), kind) in builtin.conclusions.iter().zip(conclusions_wd).zip(kinds) {
            self.compile_fact_wd(wd, fact, &formed)?;
            let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
            let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = fact else {
                unreachable!()
            };
            let root = self.compile_object_reference(&conclusion.left, &scope)?;
            let statement = self.compile_formed_fact_proposition(wd, fact, &formed)?;
            proofs.push(trace_law_term(kind, &root, &statement));
        }
        Ok((
            definitions,
            proofs
                .into_iter()
                .rev()
                .reduce(|right, left| format!("(And.intro {left} {right})"))
                .expect("nonempty trace conclusions"),
            builtin.conclusions.clone(),
        ))
    }
}
