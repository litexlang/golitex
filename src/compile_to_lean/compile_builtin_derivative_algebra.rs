//! Replay derivative algebra from its original domains, candidates and formula.
use super::compile_function_derivative_definition::validate_derivative_interior;
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::real_analysis::analysis_apply as call;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DerivativeAlgebraBuiltin/{stage}"))
}
#[derive(Clone, Copy)]
enum Law {
    Neg,
    Scale,
    Power,
    Add,
    Subtract,
    Multiply,
    Divide,
    Compose,
}
impl Law {
    fn selected(id: BuiltinTheoremId) -> Option<Self> {
        use BuiltinTheoremId::*;
        Some(match id {
            FnDerivativeAtNeg => Self::Neg,
            FnDerivativeAtScale => Self::Scale,
            FnDerivativeAtPower => Self::Power,
            FnDerivativeAtAdd => Self::Add,
            FnDerivativeAtSubtract => Self::Subtract,
            FnDerivativeAtMultiply => Self::Multiply,
            FnDerivativeAtDivide => Self::Divide,
            FnDerivativeAtCompose => Self::Compose,
            _ => return None,
        })
    }
    fn binary(self) -> bool {
        matches!(
            self,
            Self::Add | Self::Subtract | Self::Multiply | Self::Divide | Self::Compose
        )
    }
    fn count(self) -> usize {
        match self {
            Self::Neg => 12,
            Self::Scale | Self::Power => 13,
            Self::Divide => 18,
            _ => 17,
        }
    }
    // These constructors validate the already selected kernel schema; they are
    // never used as a replacement source proof or as verifier input.
    fn body(self, args: &[Obj], x: Obj) -> Obj {
        let f = call(args[0].clone(), x.clone());
        match self {
            Self::Neg => neg(f),
            Self::Scale => mul_objs(args[4].clone(), f),
            Self::Power => power(f, args[4].clone()),
            Self::Add => add_objs(f, call(args[1].clone(), x)),
            Self::Subtract => sub_objs(f, call(args[1].clone(), x)),
            Self::Multiply => mul_objs(f, call(args[1].clone(), x)),
            Self::Divide => div_objs(f, call(args[1].clone(), x)),
            Self::Compose => call(args[1].clone(), f),
        }
    }
    fn value(self, args: &[Obj]) -> Obj {
        let p = &args[if self.binary() { 3 } else { 2 }];
        let a = args[if self.binary() { 4 } else { 3 }].clone();
        match self {
            Self::Neg => neg(a),
            Self::Scale => mul_objs(args[4].clone(), a),
            Self::Power => {
                let n = args[4].clone();
                let index = sub_objs(
                    Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                        left: Box::new(n.clone()),
                        right: Box::new(number("1")),
                    })),
                    number("1"),
                );
                mul_objs(
                    mul_objs(n, power(call(args[0].clone(), p.clone()), index)),
                    a,
                )
            }
            Self::Add => add_objs(a, args[5].clone()),
            Self::Subtract => sub_objs(a, args[5].clone()),
            Self::Multiply => add_objs(
                mul_objs(a, call(args[1].clone(), p.clone())),
                mul_objs(call(args[0].clone(), p.clone()), args[5].clone()),
            ),
            Self::Divide => {
                let gp = call(args[1].clone(), p.clone());
                div_objs(
                    div_objs(
                        sub_objs(
                            mul_objs(a, gp.clone()),
                            mul_objs(call(args[0].clone(), p.clone()), args[5].clone()),
                        ),
                        gp.clone(),
                    ),
                    gp,
                )
            }
            Self::Compose => mul_objs(args[5].clone(), a),
        }
    }
}
fn number(s: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(s.into())))
}
fn neg(a: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(a) }))
}
fn power(a: Obj, n: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(a),
        exponent: Box::new(n),
    }))
}
fn candidate(fact: &Fact, f: &Obj, p: &Obj, a: &Obj) -> Result<(), LeanCompileError> {
    if matches!(fact,Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(h)) if h.function.ir()==f.ir()&&h.point.ir()==p.ir()&&h.value.ir()==a.ir())
    {
        Ok(())
    } else {
        Err(invalid("OriginalCandidate"))
    }
}
fn subset(fact: &Fact, left: &Obj, right: &Obj) -> Result<(), LeanCompileError> {
    if matches!(fact,Fact::AtomicFact(AtomicFact::SubsetFact(s)) if s.left.ir()==left.ir()&&s.right.ir()==right.ir())
    {
        Ok(())
    } else {
        Err(invalid("OriginalDomainSubset"))
    }
}
fn point_domain<'a>(
    fact: &'a Fact,
    p: &Obj,
    signature: &FnSet,
) -> Result<&'a Obj, LeanCompileError> {
    if let Fact::AtomicFact(AtomicFact::InFact(m)) = fact {
        if m.element.ir() == p.ir() && signature_domain_matches(&m.set, signature) {
            return Ok(&m.set);
        }
    }
    Err(invalid("OriginalPointDomain"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_derivative_algebra(
        &self,
        call_stmt: &TheoremCall,
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
        let law = Law::selected(builtin.theorem).ok_or_else(|| invalid("Identity"))?;
        let TheoremCallArguments::Parenthesized(args) = &call_stmt.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = law.count();
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call_stmt.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != builtin.theorem.arity()
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let req = &builtin.requirements;
        let f = &args[0];
        let out = &args[if law.binary() { 2 } else { 1 }];
        let p = &args[if law.binary() { 3 } else { 2 }];
        let a = &args[if law.binary() { 4 } else { 3 }];
        let (first, _) = real_limit_signature(&req[..3], f)?;
        let df = point_domain(&req[3], p, first)?;
        let (output, _) = real_limit_signature(&req[4..7], out)?;
        let dout = point_domain(&req[7], p, output)?;
        subset(&req[8], dout, df)?;
        validate_derivative_interior(out, p, dout, &req[9])?;
        candidate(&req[10], f, p, a)?;
        let dg = if law.binary() {
            let (second, _) = real_limit_signature(&req[11..14], &args[1])?;
            if matches!(law, Law::Compose) {
                candidate(&req[14], &args[1], &call(f.clone(), p.clone()), &args[5])?;
                let Fact::ForallFact(image) = &req[15] else {
                    return Err(invalid("OriginalImageForall"));
                };
                let x = parameter(&image.typed_parameters, dout)?;
                let input = Obj::Identifier(IdentifierObj::from_bound_name(x));
                let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(member))] =
                    image.then_facts.as_slice()
                else {
                    return Err(invalid("OriginalImageMember"));
                };
                if !image.dom_facts.is_empty()
                    || member.element.ir() != call(f.clone(), input).ir()
                    || !signature_domain_matches(&member.set, second)
                    || args.iter().any(|v| contains_parameter(v, x.id))
                    || [df, dout, &member.set]
                        .iter()
                        .any(|v| contains_parameter(v, x.id))
                {
                    return Err(invalid("OriginalImageDomain"));
                }
                Some(&member.set)
            } else {
                let Fact::AtomicFact(AtomicFact::SubsetFact(s)) = &req[14] else {
                    return Err(invalid("SecondDomainSubset"));
                };
                if s.left.ir() != dout.ir() || !signature_domain_matches(&s.right, second) {
                    return Err(invalid("SecondActualDomain"));
                }
                candidate(&req[15], &args[1], p, &args[5])?;
                if matches!(law, Law::Divide)
                    && !matches!(&req[16],Fact::AtomicFact(AtomicFact::NotEqualFact(n)) if n.left.ir()==call(args[1].clone(),p.clone()).ir()&&is_zero(&n.right))
                {
                    return Err(invalid("OriginalDenominatorNonzero"));
                }
                Some(&s.right)
            }
        } else {
            if matches!(law, Law::Scale | Law::Power) {
                let carrier = Obj::StandardSet(if matches!(law, Law::Scale) {
                    StandardSet::R
                } else {
                    StandardSet::N
                });
                if !matches!(&req[11],Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==args[4].ir()&&m.set==carrier)
                {
                    return Err(invalid("OriginalScalarOrExponent"));
                }
            }
            None
        };
        let Fact::ForallFact(formula) = &req[count - 1] else {
            return Err(invalid("OriginalFormula"));
        };
        let x = parameter(&formula.typed_parameters, dout)?;
        let input = Obj::Identifier(IdentifierObj::from_bound_name(x));
        if !formula.dom_facts.is_empty()
            || args.iter().any(|v| contains_parameter(v, x.id))
            || [df, dout].iter().any(|v| contains_parameter(v, x.id))
            || dg.is_some_and(|v| contains_parameter(v, x.id))
            || !matches!(formula.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] if eq.left.ir()==call(out.clone(),input.clone()).ir()&&eq.right.ir()==law.body(args,input).ir())
        {
            return Err(invalid("OriginalFormulaBody"));
        }
        candidate(&builtin.conclusions[0], out, p, &law.value(args))?;
        let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(goal)) = &builtin.conclusions[0]
        else {
            unreachable!()
        };
        let mut definitions = Vec::new();
        let mut references = Vec::new();
        for (index, ((fact, checked), store)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(checked)? != *fact {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, fact)?;
            definitions.push(self.emit_internal_fact(fact, &compiled, &prior)?);
            let reference = format!("h_{}", fact.fact_id().value());
            definitions.extend(self.compile_stored_inferences(
                store,
                fact,
                &(compiled.0, reference.clone()),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
            references.push(reference);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let objects = args
            .iter()
            .map(|v| self.compile_object_reference(v, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let fobj = &objects[0];
        let outobj = &objects[if law.binary() { 2 } else { 1 }];
        let pobj = &objects[if law.binary() { 3 } else { 2 }];
        let aobj = &objects[if law.binary() { 4 } else { 3 }];
        let mut steps =
            self.compile_function_limit_context(0, f, df, &req[..3], &references[..3], &scope)?;
        steps.extend(self.compile_function_limit_context(
            1,
            out,
            dout,
            &req[4..7],
            &references[4..7],
            &scope,
        )?);
        if let Some(domain) = dg {
            steps.extend(self.compile_function_limit_context(
                2,
                &args[1],
                domain,
                &req[11..14],
                &references[11..14],
                &scope,
            )?);
        }
        let real = self.compile_real_membership_certificate(p, &scope)?;
        steps.push(format!(
            "have _point_real : Litex.In {pobj} Litex.R := {real}"
        ));
        steps.push(format!(
            "let _real_point := Litex.NativeBridge.asReal {pobj} _point_real"
        ));
        steps.push(format!("have _point_value : Litex.denote {pobj}=M.number (_real_point : ℂ) := Litex.NativeBridge.asReal_spec {pobj} _point_real"));
        steps.push(format!("have _interior : Litex.DerivativeInteriorClauseValue M (Litex.denote {outobj}) (Litex.denote {pobj}) := by\n  unfold Litex.DerivativeInteriorClauseValue\n  rw [← _law_domain_1]\n  exact {}",references[9]));
        let fraw=format!("(fun (x : ℝ) => Litex.FunctionSemantics.callValue (Litex.denote {fobj}) (M.number (x : ℂ)))");
        steps.push(format!("have _first : Litex.SemanticDerivativeAtValue M {fraw} _real_point (Litex.denote {aobj}) := Litex.semanticDerivativeOfCandidate (Litex.denote {fobj}) (Litex.denote {pobj}) (Litex.denote {aobj}) _real_point _point_value _law_real_0 {}",references[10]));
        let draw = format!("(Litex.denote {aobj})");
        let (raw,term)=match law {
            Law::Neg=>(format!("(fun x => M.negValue ({fraw} x))"),format!("Litex.semanticDerivativeNeg {fraw} _real_point {draw} _first")),
            Law::Scale=>(format!("(fun x => M.mulValue (Litex.denote {}) ({fraw} x))",objects[4]),format!("Litex.semanticDerivativeScale {fraw} _real_point (Litex.denote {}) {draw} {} _first",objects[4],references[11])),
            Law::Power=>(format!("(fun x => M.powValue ({fraw} x) (Litex.denote {}))",objects[4]),format!("Litex.semanticDerivativePower {fraw} _real_point {draw} (Litex.denote {}) (Litex.NativeBridge.asNat {} {}) (Litex.NativeBridge.asNat_spec {} {}) _first",objects[4],objects[4],references[11],objects[4],references[11])),
            Law::Compose=>{
                let g=&objects[1];let b=&objects[5];
                (format!("(fun x => Litex.FunctionSemantics.callValue (Litex.denote {g}) ({fraw} x))"),format!("Litex.semanticDerivativeComposeCandidates (Litex.denote {fobj}) (Litex.denote {g}) (Litex.denote {pobj}) {draw} (Litex.denote {b}) _real_point _point_value _law_real_0 _law_real_2 {} {}",references[10],references[14]))
            }
            _=>{
                let g=&objects[1];let b=&objects[5];
                let graw=format!("(fun (x : ℝ) => Litex.FunctionSemantics.callValue (Litex.denote {g}) (M.number (x : ℂ)))");
                steps.push(format!("have _second : Litex.SemanticDerivativeAtValue M {graw} _real_point (Litex.denote {b}) := Litex.semanticDerivativeOfCandidate (Litex.denote {g}) (Litex.denote {pobj}) (Litex.denote {b}) _real_point _point_value _law_real_2 {}",references[15]));
                let(operation,name)=match law{Law::Add=>("addValue","Add"),Law::Subtract=>("subValue","Sub"),Law::Multiply=>("mulValue","Mul"),Law::Divide=>("divValue","Div"),_=>unreachable!()};
                let nonzero=if matches!(law,Law::Divide){format!(" (by rw [← _point_value]; exact {})",references[16])}else{String::new()};
                (format!("(fun x => M.{operation} ({fraw} x) ({graw} x))"),format!("Litex.semanticDerivative{name} {fraw} {graw} _real_point {draw} (Litex.denote {b}) _first _second{nonzero}"))
            }
        };
        let coefficient =
            self.compile_function_raw_expression_bound(&goal.value, &scope, &HashMap::new())?;
        let rewrite = if matches!(law, Law::Power | Law::Multiply | Law::Divide) {
            "\n  rw [← _point_value] at _step"
        } else {
            ""
        };
        let derivative = format!("(by\n  have _step := {term}{rewrite}\n  exact _step\n)");
        let formula=format!("(by\n  intro x hx\n  exact {} (Litex.semanticObject (M.number (x : ℂ)) (M.member_isSet hx)) (show M.mem (M.number (x : ℂ)) (Litex.denote _law1_domain) from _law_domain_1.symm ▸ hx)\n)",references[count-1]);
        steps.push(format!("exact Litex.derivativeOfSemanticFormula (Litex.denote {outobj}) (Litex.denote {pobj}) {coefficient} _real_point {raw} _point_value _interior {formula} {derivative}"));
        let proof = format!(
            "(by\n{}\n)",
            steps
                .join("\n")
                .lines()
                .map(|l| format!("  {l}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
