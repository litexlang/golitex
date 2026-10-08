use super::LeanCompileError;
use crate::prelude::*;
use std::collections::HashMap;

/// Replay a successful typed execution result while its citation context is live.
/// The complete artifact is returned only after every selected route succeeds.
pub fn compile_run(
    result: &RunLitexCodeResult,
    runtime: &Runtime,
    artifact_namespace: &str,
) -> Result<String, LeanCompileError> {
    validate_namespace(artifact_namespace)?;
    if !result.success
        || result.session_error.is_some()
        || result
            .statement_results
            .iter()
            .any(ExecStmtResult::is_failed)
    {
        return Err(LeanCompileError::new(
            "source_failed",
            "Only a complete successful source run can be compiled.",
        ));
    }
    let mut compiler = LeanCompiler::new();
    let mut declarations = Vec::new();
    for (index, result) in result.statement_results.iter().enumerate() {
        let compiled = compiler
            .compile_statement(result, runtime, index + 1)
            .map_err(|mut error| {
                error.statement_index = Some(index + 1);
                error
            })?;
        declarations.push(compiled);
    }
    let universes = if compiler.universes.is_empty() {
        "u".to_string()
    } else {
        format!("u {}", compiler.universes.join(" "))
    };
    Ok(format!("import Litex\n\nnamespace LitexCompiled.{artifact_namespace}\n\nuniverse {universes}\nvariable {{M : Litex.Semantics.{{u}}}}\n\n{}\nend LitexCompiled.{artifact_namespace}\n", declarations.join("\n\n")))
}

#[derive(Clone)]
struct ObjectTerm {
    object: Obj,
    term: String,
    numeric: Option<NumericTerm>,
}

#[derive(Clone)]
struct NumericTerm {
    value: String,
    denotation: String,
    member: String,
}

#[derive(Clone)]
struct FactTerm {
    fact: Fact,
    proposition: String,
    proof: String,
}

#[derive(Default)]
struct CompilerScope {
    env: Option<Box<ExecEnv>>,
    identifiers: HashMap<IdentifierId, ObjectTerm>,
    objects: HashMap<ObjIR, ObjectTerm>,
    facts: HashMap<FactId, FactTerm>,
    wds: HashMap<WellDefinednessId, ObjectTerm>,
}

struct LeanCompiler {
    scopes: Vec<CompilerScope>,
    universes: Vec<String>,
}

impl LeanCompiler {
    fn new() -> Self {
        Self {
            scopes: vec![CompilerScope::default()],
            universes: Vec::new(),
        }
    }

    fn compile_statement(
        &mut self,
        result: &ExecStmtResult,
        runtime: &Runtime,
        index: usize,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => {
                let compiled = self.compile_verify(&success.verify_result, runtime)?;
                self.validate_store(&success.store_and_infer_result, &compiled.fact)?;
                let name = format!("fact_{index}");
                let declaration = format!(
                    "theorem {name} : {} :=\n  {}",
                    compiled.proposition,
                    compiled.proof.replace('\n', "\n  ")
                );
                let mut exported = compiled;
                exported.proof = format!("({name} (M := M))");
                self.remember_fact(exported);
                Ok(declaration)
            }
            ExecStmtResult::Fact(ExecFactStmtResult::Failed(_)) => Err(LeanCompileError::new(
                "Fact/Failed",
                "A failed fact is not proof evidence.",
            )),
            ExecStmtResult::Definition(_) => Err(LeanCompileError::unsupported("Definition")),
            ExecStmtResult::Witness(_) => Err(LeanCompileError::unsupported("Witness")),
            ExecStmtResult::Trust(_) => Err(LeanCompileError::unsupported("Trust")),
            ExecStmtResult::By(_) => Err(LeanCompileError::unsupported("By")),
            ExecStmtResult::Register(_) => Err(LeanCompileError::unsupported("Register")),
            ExecStmtResult::ReleaseAndExpand(_) => {
                Err(LeanCompileError::unsupported("ReleaseAndExpand"))
            }
            ExecStmtResult::ProofBlock(_) => Err(LeanCompileError::unsupported("ProofBlock")),
            ExecStmtResult::Command(_) => Err(LeanCompileError::unsupported("Command")),
        }
    }

    fn compile_verify(
        &mut self,
        result: &VerifyFactResult,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        match result {
            VerifyFactResult::Equality(result) => match result.as_ref() {
                VerifyEqualityResult::Success(success) => {
                    let left = self.compile_wd(&success.well_defined_proof.left, runtime)?;
                    let right = self.compile_wd(&success.well_defined_proof.right, runtime)?;
                    ensure_object(&success.fact.left, &success.well_defined_proof.left)?;
                    ensure_object(&success.fact.right, &success.well_defined_proof.right)?;
                    let proof = match &success.searched_proof {
                        EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(
                            _,
                        )) => {
                            if success.fact.left.ir() != success.fact.right.ir() {
                                return Err(LeanCompileError::new(
                                    "SameIr",
                                    "Identity evidence has different endpoints.",
                                ));
                            }
                            format!("(Litex.sameRefl {left})")
                        }
                        EqualFactSearchedProof::ByTheyAreTheSame(
                            TheyAreTheSameProof::SameFreeParamShape(_),
                        ) => {
                            return Err(LeanCompileError::unsupported(
                                "Equality/SameFreeParamShape",
                            ))
                        }
                        EqualFactSearchedProof::ByClosedCalculation(proof) => {
                            self.compile_closed_equality(&success.fact, proof)?
                        }
                        EqualFactSearchedProof::ByKnownSpecialProperty(_) => {
                            return Err(LeanCompileError::unsupported(
                                "Equality/KnownSpecialProperty",
                            ))
                        }
                        EqualFactSearchedProof::ByBuiltinRule(
                            EqualitySearchProofByBuiltinRule::Calculation(
                                EqualitySearchProofByCalculation::Rational {},
                            ),
                        ) => self.compile_rational(&success.fact, &[], &[], false, runtime)?,
                        EqualFactSearchedProof::ByBuiltinRule(
                            EqualitySearchProofByBuiltinRule::ScalarDivisionRelation(proof),
                        ) => {
                            self.compile_scalar_division_relation(&success.fact, proof, runtime)?
                        }
                        EqualFactSearchedProof::ByBuiltinRule(_) => {
                            return Err(LeanCompileError::unsupported("Equality/BuiltinRule"))
                        }
                        EqualFactSearchedProof::ByEquivalenceClass(_) => {
                            return Err(LeanCompileError::unsupported("Equality/EquivalenceClass"))
                        }
                        EqualFactSearchedProof::ByObjectDefinition(_) => {
                            return Err(LeanCompileError::unsupported("Equality/ObjectDefinition"))
                        }
                        EqualFactSearchedProof::ByBuiltinStrategy(
                            EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(
                                proof,
                            ),
                        ) => self.compile_rational(
                            &success.fact,
                            &proof.requirement_facts,
                            &proof.proof_of_requirement_facts,
                            true,
                            runtime,
                        )?,
                        EqualFactSearchedProof::ByBuiltinStrategy(_) => {
                            return Err(LeanCompileError::unsupported("Equality/BuiltinStrategy"))
                        }
                        EqualFactSearchedProof::ByMatchingOneArgByOne(proof) => self
                            .compile_arithmetic_congruence(
                                &success.fact,
                                &proof.corresponding_arg_equal_proofs,
                                runtime,
                            )?,
                        EqualFactSearchedProof::ByKnownForallFact(_) => {
                            return Err(LeanCompileError::unsupported("Equality/KnownForallFact"))
                        }
                        EqualFactSearchedProof::ByKnownForallFactViaSymmetry(_) => {
                            return Err(LeanCompileError::unsupported(
                                "Equality/KnownForallFactViaSymmetry",
                            ))
                        }
                        EqualFactSearchedProof::ByBuiltinRewrite(_) => {
                            return Err(LeanCompileError::unsupported("Equality/BuiltinRewrite"))
                        }
                    };
                    Ok(FactTerm {
                        fact: Fact::AtomicFact(AtomicFact::EqualFact(success.fact.clone())),
                        proposition: format!("Litex.Same {left} {right}"),
                        proof,
                    })
                }
                VerifyEqualityResult::Failed(_) => Err(LeanCompileError::new(
                    "Equality/Failed",
                    "Failed verification is not proof evidence.",
                )),
            },
            VerifyFactResult::AtomicExceptEquality(result) => {
                match result.as_ref() {
                    VerifyAtomicExceptEqualityFactResult::Success(success) => {
                        self.compile_atomic_wd(
                            &success.well_defined_proof,
                            &success.fact,
                            runtime,
                        )?;
                        let proposition = self.atomic_proposition(&success.fact)?;
                        let proof = match &success.searched_proof {
                        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) => {
                            match &success.fact {
                                AtomicFact::InFact(fact)
                                    if fact.element.ir() == proof.element.ir()
                                        && fact.set.ir()
                                            == Obj::StandardSet(proof.set.clone()).ir() => {}
                                _ => {
                                    return Err(LeanCompileError::new(
                                        "StructuralMembership",
                                        "Evidence does not describe the verified membership.",
                                    ))
                                }
                            }
                            self.compile_structural(proof, runtime)?
                        }
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
                            ClosedAtomicExceptEqualityCalculationProof::In(proof),
                        ) => match &success.fact {
                            AtomicFact::InFact(fact) => {
                                self.compile_closed_membership(&fact.element, &fact.set, proof)?
                            }
                            _ => {
                                return Err(LeanCompileError::new(
                                    "ClosedMembership",
                                    "Membership calculation has another fact family.",
                                ))
                            }
                        },
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(ClosedAtomicExceptEqualityCalculationProof::NotEqual(proof)) =>
                            self.compile_closed_not_equal(&success.fact, proof)?,
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(_) => {
                            return Err(LeanCompileError::unsupported(
                                "Atomic/ClosedCalculationNonMembership",
                            ))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => {
                            self.compile_known_atomic(proof, &success.fact, runtime)?
                        }
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) => match rule {
                            AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact(
                                IsSetFactSearchProofByBuiltinRule::AlwaysTrue(_),
                            ) => match &success.fact {
                                AtomicFact::IsSetFact(fact) => {
                                    format!("(Litex.isSet {})", self.object_term(&fact.set)?)
                                }
                                _ => {
                                    return Err(LeanCompileError::new(
                                        "IsSetAlwaysTrue",
                                        "Sethood evidence has another fact family.",
                                    ))
                                }
                            },
                            other => return Err(unsupported_atomic_builtin(other)),
                        },
                        AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(_) => {
                            return Err(LeanCompileError::unsupported(
                                "Atomic/KnownSpecialProperty",
                            ))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonzeroProduct(proof)) =>
                            self.compile_nonzero_product(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, runtime)?,
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/BuiltinStrategy"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/KnownStrategy"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByDefinition(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/Definition"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/KnownForallFact"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/BuiltinRewrite"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/KnownRewrite"))
                        }
                    };
                        if let AtomicFact::InFact(member) = &success.fact {
                            if member.set == Obj::StandardSet(StandardSet::C) {
                                self.remember_complex_member(&member.element, &proof)?;
                            }
                        }
                        Ok(FactTerm {
                            fact: Fact::AtomicFact(success.fact.clone()),
                            proposition,
                            proof,
                        })
                    }
                    VerifyAtomicExceptEqualityFactResult::Failed(_) => Err(LeanCompileError::new(
                        "Atomic/Failed",
                        "Failed verification is not proof evidence.",
                    )),
                }
            }
            VerifyFactResult::ForallFact(result) => match result.as_ref() {
                VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(
                    proof,
                )) => self.compile_forall(proof, runtime),
                VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(_)) => {
                    Err(LeanCompileError::unsupported("Forall/KnownForallFact"))
                }
                VerifyForallFactResult::Success(VerifyForallFactProof::ByEmptyParameterDomain(
                    _,
                )) => Err(LeanCompileError::unsupported("Forall/EmptyParameterDomain")),
                VerifyForallFactResult::Failed(_) => Err(LeanCompileError::new(
                    "Forall/Failed",
                    "Failed verification is not proof evidence.",
                )),
            },
            VerifyFactResult::AndFact(_) => Err(LeanCompileError::unsupported("AndFact")),
            VerifyFactResult::ChainFact(_) => Err(LeanCompileError::unsupported("ChainFact")),
            VerifyFactResult::OrFact(_) => Err(LeanCompileError::unsupported("OrFact")),
            VerifyFactResult::ExistShapedFact(_) => {
                Err(LeanCompileError::unsupported("ExistShapedFact"))
            }
            VerifyFactResult::ForallFactWithIff(_) => {
                Err(LeanCompileError::unsupported("ForallFactWithIff"))
            }
            VerifyFactResult::NotForall(_) => Err(LeanCompileError::unsupported("NotForall")),
        }
    }

    fn compile_closed_equality(
        &self,
        fact: &EqualFact,
        proof: &ClosedEqualityCalculationProof,
    ) -> Result<String, LeanCompileError> {
        let left = EvalRational::from_obj(&fact.left)
            .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
        let right = EvalRational::from_obj(&fact.right)
            .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
        let matching = match &proof.values {
            ClosedValuePair::Decimal { left: a, right: b } => {
                scalar_decimal(a)? == left && scalar_decimal(b)? == right
            }
            ClosedValuePair::Rational { left: a, right: b } => a == &left && b == &right,
            ClosedValuePair::Complex {
                left_real: a,
                left_imaginary: ai,
                right_real: b,
                right_imaginary: bi,
            } => a == &left && b == &right && ai.is_zero() && bi.is_zero(),
            ClosedValuePair::Radical { .. } => {
                return Err(LeanCompileError::unsupported("ClosedEquality/Radical"))
            }
        };
        if !matching || left != right {
            return Err(LeanCompileError::new("ClosedEquality/Values", "Closed equality values differ from their exact source endpoints or from each other."));
        }
        let x = self.numeric_term(&fact.left)?;
        let y = self.numeric_term(&fact.right)?;
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {} {} {} {} {} {} (by norm_num))",
            self.object_term(&fact.left)?,
            self.object_term(&fact.right)?,
            x.value,
            y.value,
            x.denotation,
            y.denotation
        ))
    }

    fn compile_arithmetic_congruence(
        &mut self,
        fact: &EqualFact,
        children: &[VerifyFactResult],
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (operation, pairs) = match (&fact.left, &fact.right) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Add(b)),
            ) => (
                "addValue",
                vec![
                    (a.left.as_ref(), b.left.as_ref()),
                    (a.right.as_ref(), b.right.as_ref()),
                ],
            ),
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(b)),
            ) => (
                "subValue",
                vec![
                    (a.left.as_ref(), b.left.as_ref()),
                    (a.right.as_ref(), b.right.as_ref()),
                ],
            ),
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(b)),
            ) => (
                "mulValue",
                vec![
                    (a.left.as_ref(), b.left.as_ref()),
                    (a.right.as_ref(), b.right.as_ref()),
                ],
            ),
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Div(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Div(b)),
            ) => (
                "divValue",
                vec![
                    (a.left.as_ref(), b.left.as_ref()),
                    (a.right.as_ref(), b.right.as_ref()),
                ],
            ),
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(b)),
            ) => (
                "powValue",
                vec![
                    (a.base.as_ref(), b.base.as_ref()),
                    (a.exponent.as_ref(), b.exponent.as_ref()),
                ],
            ),
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(b)),
            ) => ("negValue", vec![(a.arg.as_ref(), b.arg.as_ref())]),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "Equality/MatchingOneArgByOne/Constructor",
                ))
            }
        };
        if children.len() != pairs.len() {
            return Err(LeanCompileError::new(
                "ArithmeticCongruence/Children",
                "Constructor congruence has the wrong ordered child arity.",
            ));
        }
        let mut compiled = Vec::new();
        for (child, (left, right)) in children.iter().zip(pairs) {
            let child = self.compile_verify(child, runtime)?;
            match &child.fact {
                Fact::AtomicFact(AtomicFact::EqualFact(eq))
                    if eq.left.ir() == left.ir() && eq.right.ir() == right.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "ArithmeticCongruence/ChildSubject",
                        "Congruence child does not prove this exact ordered operand pair.",
                    ))
                }
            }
            compiled.push(child.proof);
        }
        if compiled.len() == 1 {
            Ok(format!("(congrArg M.{operation} {})", compiled[0]))
        } else {
            Ok(format!(
                "(congrArg₂ M.{operation} {} {})",
                compiled[0], compiled[1]
            ))
        }
    }

    fn compile_scalar_division_relation(
        &mut self,
        fact: &EqualFact,
        proof: &ScalarDivisionRelationProof,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (child, product_from_division) = match proof {
            ScalarDivisionRelationProof::ProductFromDivision(p) => (&p.division_equation, true),
            ScalarDivisionRelationProof::DivisionFromProduct(p) => (&p.product_equation, false),
        };
        let compiled = self.compile_verify(child, runtime)?;
        let equation = match &compiled.fact {
            Fact::AtomicFact(AtomicFact::EqualFact(x)) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "ScalarDivisionRelation/Child",
                    "The source equation is not an equality.",
                ))
            }
        };
        let (_numerator, denominator, factor, quotient, reversed, commuted) =
            if product_from_division {
                let quotient = match &equation.left {
                    Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => x,
                    _ => {
                        return Err(LeanCompileError::new(
                            "ScalarDivisionRelation/DivisionSubject",
                            "ProductFromDivision must cite a quotient equation.",
                        ))
                    }
                };
                let mut matched = None;
                for (other, product, reversed) in [
                    (&fact.left, &fact.right, false),
                    (&fact.right, &fact.left, true),
                ] {
                    if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = product {
                        if other.ir() != quotient.left.ir() {
                            continue;
                        }
                        if p.left.ir() == equation.right.ir() && p.right.ir() == quotient.right.ir()
                        {
                            matched = Some((reversed, false));
                            break;
                        }
                        if p.right.ir() == equation.right.ir() && p.left.ir() == quotient.right.ir()
                        {
                            matched = Some((reversed, true));
                            break;
                        }
                    }
                }
                let (reversed, commuted) = matched.ok_or_else(|| LeanCompileError::new("ScalarDivisionRelation/ParentSubject", "The source quotient equation does not describe the parent product endpoints."))?;
                (
                    quotient.left.as_ref(),
                    quotient.right.as_ref(),
                    &equation.right,
                    &equation.left,
                    reversed,
                    commuted,
                )
            } else {
                let mut matched = None;
                for (quotient_obj, factor, reversed) in [
                    (&fact.left, &fact.right, false),
                    (&fact.right, &fact.left, true),
                ] {
                    if let Obj::ArithmeticOperator(ArithmeticOperator::Div(q)) = quotient_obj {
                        if equation.left.ir() != q.left.ir() {
                            continue;
                        }
                        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = &equation.right
                        {
                            if p.left.ir() == factor.ir() && p.right.ir() == q.right.ir() {
                                matched = Some((q, factor, quotient_obj, reversed, false));
                                break;
                            }
                            if p.right.ir() == factor.ir() && p.left.ir() == q.right.ir() {
                                matched = Some((q, factor, quotient_obj, reversed, true));
                                break;
                            }
                        }
                    }
                }
                let (q, factor, quotient_obj, reversed, commuted) = matched.ok_or_else(|| LeanCompileError::new("ScalarDivisionRelation/ParentSubject", "The source product equation does not describe the parent quotient endpoints."))?;
                (
                    q.left.as_ref(),
                    q.right.as_ref(),
                    factor,
                    quotient_obj,
                    reversed,
                    commuted,
                )
            };
        let b = self.numeric_term(denominator)?;
        let c = self.numeric_term(factor)?;
        let x = self.numeric_term(&equation.left)?;
        let y = self.numeric_term(&equation.right)?;
        let source_eq = format!(
            "(Litex.NativeBridge.nativeEqOfDenoteNumber {} {} {} {} {} {} {})",
            self.object_term(&equation.left)?,
            self.object_term(&equation.right)?,
            x.value,
            y.value,
            x.denotation,
            y.denotation,
            compiled.proof
        );
        let guard = format!(
            "(Litex.NativeBridge.nativeNonzeroOfDenote {} {} {} ({}).wd.2.2)",
            self.object_term(denominator)?,
            b.value,
            b.denotation,
            self.object_term(quotient)?
        );
        let native_proof = if product_from_division {
            let product = format!("((div_eq_iff {guard}).mp {source_eq})");
            let oriented = if commuted {
                format!("({product}.trans (mul_comm {} {}))", c.value, b.value)
            } else {
                product
            };
            if reversed {
                format!("({oriented}.symm)")
            } else {
                oriented
            }
        } else {
            let product = if commuted {
                format!("({source_eq}.trans (mul_comm {} {}))", b.value, c.value)
            } else {
                source_eq
            };
            let quotient = format!("((div_eq_iff {guard}).mpr {product})");
            if reversed {
                format!("({quotient}.symm)")
            } else {
                quotient
            }
        };
        let left = self.numeric_term(&fact.left)?;
        let right = self.numeric_term(&fact.right)?;
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {} {} {} {} {} {} {native_proof})",
            self.object_term(&fact.left)?,
            self.object_term(&fact.right)?,
            left.value,
            right.value,
            left.denotation,
            right.denotation
        ))
    }

    fn compile_rational(
        &mut self,
        fact: &EqualFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        guarded: bool,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        validate_arithmetic_expression(&fact.left)?;
        validate_arithmetic_expression(&fact.right)?;
        let expected = normalization_nonzero_subjects(&fact.left, &fact.right)?;
        if requirements.len() != expected.len()
            || proofs.len() != expected.len()
            || guarded != !expected.is_empty()
        {
            return Err(LeanCompileError::new("Rational/Requirements", "The selected normalization family or ordered guard arity differs from the source expression."));
        }
        let mut native_guards = Vec::new();
        for (index, ((requirement, proof), object)) in
            requirements.iter().zip(proofs).zip(expected).enumerate()
        {
            ensure_nonzero_subject(requirement, &object)?;
            let proved = self.compile_verify(proof, runtime)?;
            if &proved.fact != requirement {
                return Err(LeanCompileError::new(
                    "Rational/RequirementSubject",
                    "A guard's verify result differs from its exact ordered requirement.",
                ));
            }
            let term = self.object_term(&object)?;
            let native = self.numeric_term(&object)?;
            native_guards.push(format!("have _litex_nz_{index} : {} ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote {term} {} {} {}", native.value, native.value, native.denotation, proved.proof));
        }
        let left = self.object_term(&fact.left)?;
        let right = self.object_term(&fact.right)?;
        let x = self.numeric_term(&fact.left)?;
        let y = self.numeric_term(&fact.right)?;
        // The empty Rational tag contains no monomial trace. The Lean kernel
        // checks the fixed normalization proof, including forged false tags.
        let normalization = if guarded {
            let guard_names = (0..native_guards.len())
                .map(|i| format!("_litex_nz_{i}"))
                .collect::<Vec<_>>();
            let exact_guards = guard_names
                .iter()
                .map(|n| format!("exact {n}"))
                .collect::<Vec<_>>()
                .join(" | ");
            format!("(by\n  {}\n  field_simp (disch := repeat' first | {exact_guards} | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero) <;> ring\n)", native_guards.join("\n  "))
        } else {
            "(by ring)".to_string()
        };
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {left} {right} {} {} {} {} {normalization})",
            x.value, y.value, x.denotation, y.denotation
        ))
    }

    fn compile_nonzero_product(
        &mut self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let goal = match fact {
            AtomicFact::NotEqualFact(x) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/Subject",
                    "Product nonzero evidence has another fact family.",
                ))
            }
        };
        let (expression, reversed) = if is_zero(&goal.right) {
            (&goal.left, false)
        } else if is_zero(&goal.left) {
            (&goal.right, true)
        } else {
            return Err(LeanCompileError::new(
                "NonzeroProduct/Subject",
                "The product guard does not compare with zero.",
            ));
        };
        let product = match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/Subject",
                    "The certified nonzero object is not a product.",
                ))
            }
        };
        if requirements.len() != 2 || proofs.len() != 2 {
            return Err(LeanCompileError::new(
                "NonzeroProduct/Requirements",
                "The product needs two ordered factor proofs.",
            ));
        }
        let mut compiled = Vec::new();
        for ((requirement, proof), child) in requirements
            .iter()
            .zip(proofs)
            .zip([product.left.as_ref(), product.right.as_ref()])
        {
            ensure_nonzero_subject(requirement, child)?;
            let proved = self.compile_verify(proof, runtime)?;
            if &proved.fact != requirement {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/RequirementSubject",
                    "A factor proof differs from its ordered requirement.",
                ));
            }
            let native = self.numeric_term(child)?;
            compiled.push(format!(
                "(Litex.NativeBridge.nativeNonzeroOfDenote {} {} {} {})",
                self.object_term(child)?,
                native.value,
                native.denotation,
                proved.proof
            ));
        }
        let native = self.numeric_term(expression)?;
        let proof = format!("(Litex.NativeBridge.notSameOfDenoteNumber {} (Litex.number (M := M) (0 : ℂ)) {} (0 : ℂ) {} (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (mul_ne_zero {} {}))", self.object_term(expression)?, native.value, native.denotation, compiled[0], compiled[1]);
        Ok(if reversed {
            format!("(fun h => {proof} h.symm)")
        } else {
            proof
        })
    }

    fn compile_closed_not_equal(
        &self,
        fact: &AtomicFact,
        proof: &ClosedNotEqualCalculationProof,
    ) -> Result<String, LeanCompileError> {
        let goal = match fact {
            AtomicFact::NotEqualFact(x) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "ClosedNotEqual/Subject",
                    "Closed inequality evidence has another fact family.",
                ))
            }
        };
        let left = EvalRational::from_obj(&goal.left)
            .ok_or_else(|| LeanCompileError::unsupported("ClosedNotEqual/Expression"))?;
        let right = EvalRational::from_obj(&goal.right)
            .ok_or_else(|| LeanCompileError::unsupported("ClosedNotEqual/Expression"))?;
        let matching = match &proof.values {
            ClosedValuePair::Decimal { left: a, right: b } => {
                scalar_decimal(a)? == left && scalar_decimal(b)? == right
            }
            ClosedValuePair::Rational { left: a, right: b } => a == &left && b == &right,
            ClosedValuePair::Complex {
                left_real: a,
                left_imaginary: ai,
                right_real: b,
                right_imaginary: bi,
            } => a == &left && b == &right && ai.is_zero() && bi.is_zero(),
            ClosedValuePair::Radical { .. } => {
                return Err(LeanCompileError::unsupported("ClosedNotEqual/Radical"))
            }
        };
        if !matching || left == right {
            return Err(LeanCompileError::new(
                "ClosedNotEqual/Values",
                "Closed scalar values differ from the source endpoints or are equal.",
            ));
        }
        let x = self.numeric_term(&goal.left)?;
        let y = self.numeric_term(&goal.right)?;
        Ok(format!(
            "(Litex.NativeBridge.notSameOfDenoteNumber {} {} {} {} {} {} (by norm_num))",
            self.object_term(&goal.left)?,
            self.object_term(&goal.right)?,
            x.value,
            y.value,
            x.denotation,
            y.denotation
        ))
    }

    fn compile_forall(
        &mut self,
        proof: &VerifyForallFactSuccess,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        let scope = CompilerScope {
            env: Some(proof.local_env.clone()),
            ..CompilerScope::default()
        };
        self.scopes.push(scope);
        let compiled = self.compile_forall_body(proof, runtime);
        self.scopes.pop();
        compiled
    }

    fn compile_forall_body(
        &mut self,
        proof: &VerifyForallFactSuccess,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        let groups = &proof.fact.typed_parameters.groups;
        if proof.introduced_params.param_type_well_defined.len() != groups.len()
            || proof.introduced_params.auto_opened_struct_layers.is_some()
        {
            return Err(LeanCompileError::new(
                "Forall/Parameters",
                "Parameter evidence does not match the supported plain groups.",
            ));
        }
        let expected_count: usize = groups.iter().map(|group| group.params.len()).sum();
        let stored_ids = &proof.introduced_params.defined_params.stored_fact_ids;
        if stored_ids.len() != expected_count {
            return Err(LeanCompileError::unsupported("Forall/ParameterInference"));
        }
        let mut binders = Vec::new();
        let mut introductions = Vec::new();
        let mut offset = 0;
        for (group, wd) in groups
            .iter()
            .zip(&proof.introduced_params.param_type_well_defined)
        {
            let set = match &group.param_type {
                ParamType::Obj(set) => set,
                ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                    return Err(LeanCompileError::unsupported("Forall/ParameterKind"))
                }
            };
            match wd {
                ParamTypeWellDefinedProof::Obj(VerifyObjWellDefinedResult::Success(wd)) => {
                    ensure_object(set, wd)?;
                    self.compile_wd(wd, runtime)?;
                }
                ParamTypeWellDefinedProof::Obj(VerifyObjWellDefinedResult::Failed { .. }) => {
                    return Err(LeanCompileError::new(
                        "Forall/ParameterWD",
                        "Parameter WD failed.",
                    ))
                }
                ParamTypeWellDefinedProof::Set
                | ParamTypeWellDefinedProof::NonemptySet
                | ParamTypeWellDefinedProof::FiniteSet => {
                    return Err(LeanCompileError::unsupported("Forall/ParameterKindWD"))
                }
            }
            for parameter in &group.params {
                let id = parameter.id;
                let host = format!("_Host_i{}", id.value());
                let universe = format!("v{}", id.value());
                if !self.universes.contains(&universe) {
                    self.universes.push(universe.clone());
                }
                let instance = format!("_rep_i{}", id.value());
                let value = format!("_value_i{}", id.value());
                let hypothesis = format!("_h_param_i{}", id.value());
                let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
                let term = ObjectTerm {
                    object: object.clone(),
                    term: value.clone(),
                    numeric: None,
                };
                let scope = self.scopes.last_mut().expect("compiler scope");
                if scope.identifiers.insert(id, term.clone()).is_some() {
                    return Err(LeanCompileError::new(
                        "Forall/Parameters",
                        "Duplicate parameter identity.",
                    ));
                }
                scope.objects.insert(object.ir(), term);
                binders.push(format!("{{{host} : Type {universe}}} [{instance} : Litex.Representation M {host}] ({value} : Litex.Obj (M := M) {host})"));
                introductions.extend([host, instance, value]);
                let fact = self.resolve_fact(stored_ids[offset], runtime)?;
                let atomic = match &fact {
                    Fact::AtomicFact(AtomicFact::InFact(fact))
                        if fact.element.ir() == object.ir() && fact.set.ir() == set.ir() =>
                    {
                        AtomicFact::InFact(fact.clone())
                    }
                    _ => {
                        return Err(LeanCompileError::new(
                            "Forall/ParameterFact",
                            "Stored parameter fact differs from the introducing header.",
                        ))
                    }
                };
                let proposition = self.atomic_proposition(&atomic)?;
                binders.push(format!("({hypothesis} : {proposition})"));
                introductions.push(hypothesis.clone());
                if set == &Obj::StandardSet(StandardSet::C) {
                    self.remember_complex_member(&object, &hypothesis)?;
                }
                self.remember_fact(FactTerm {
                    fact,
                    proposition,
                    proof: hypothesis,
                });
                offset += 1;
            }
        }
        if proof.assumed_dom_facts.len() != proof.fact.dom_facts.len() {
            return Err(LeanCompileError::new(
                "Forall/Domain",
                "Domain evidence has the wrong arity.",
            ));
        }
        for (fact, assumed) in proof.fact.dom_facts.iter().zip(&proof.assumed_dom_facts) {
            self.compile_fact_wd(&assumed.well_defined, fact, runtime)?;
            self.validate_store(&assumed.store_and_infer, fact)?;
            let atomic = match fact {
                Fact::AtomicFact(atomic) => atomic,
                _ => return Err(LeanCompileError::unsupported("Forall/CompoundDomain")),
            };
            let proposition = self.atomic_proposition(atomic)?;
            let hypothesis = format!("_h_dom_f{}", fact.fact_id().value());
            binders.push(format!("({hypothesis} : {proposition})"));
            introductions.push(hypothesis.clone());
            self.remember_fact(FactTerm {
                fact: fact.clone(),
                proposition,
                proof: hypothesis,
            });
        }
        if proof.proved_then_facts.len() != proof.fact.then_facts.len()
            || proof.proved_then_facts.is_empty()
        {
            return Err(LeanCompileError::new(
                "Forall/Then",
                "Conclusion evidence has the wrong arity.",
            ));
        }
        let mut conclusions = Vec::new();
        for (fact, proved) in proof.fact.then_facts.iter().zip(&proof.proved_then_facts) {
            let expected = match fact {
                ExistOrAndChainAtomicFact::AtomicFact(atomic) => Fact::AtomicFact(atomic.clone()),
                ExistOrAndChainAtomicFact::AndFact(_)
                | ExistOrAndChainAtomicFact::ChainFact(_)
                | ExistOrAndChainAtomicFact::OrFact(_)
                | ExistOrAndChainAtomicFact::ExistFact(_)
                | ExistOrAndChainAtomicFact::ExistUniqueFact(_)
                | ExistOrAndChainAtomicFact::NotExistFact(_) => {
                    return Err(LeanCompileError::unsupported("Forall/CompoundThen"))
                }
            };
            let compiled = self.compile_verify(&proved.verify_result, runtime)?;
            if compiled.fact != expected {
                return Err(LeanCompileError::new(
                    "Forall/Then",
                    "Verified conclusion differs from the source conclusion.",
                ));
            }
            self.validate_store(&proved.store_and_infer, &compiled.fact)?;
            self.remember_fact(compiled.clone());
            conclusions.push(compiled);
        }
        let mut conclusion = conclusions.pop().expect("nonempty conclusions");
        while let Some(left) = conclusions.pop() {
            conclusion.proposition = format!("({} ∧ {})", left.proposition, conclusion.proposition);
            conclusion.proof = format!("(And.intro {} {})", left.proof, conclusion.proof);
        }
        let proposition = if binders.is_empty() {
            conclusion.proposition
        } else {
            format!("∀ {}, {}", binders.join(" "), conclusion.proposition)
        };
        let intro = if introductions.is_empty() {
            String::new()
        } else {
            format!("  intro {}\n", introductions.join(" "))
        };
        Ok(FactTerm {
            fact: Fact::ForallFact(proof.fact.clone()),
            proposition,
            proof: format!("(by\n{intro}  exact {}\n)", conclusion.proof),
        })
    }

    fn compile_wd(
        &mut self,
        proof: &ObjWellDefinedProof,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        match proof {
            ObjWellDefinedProof::ByKnown { obj, wd_id } => {
                let recorded = self.resolve_wd(*wd_id, runtime)?;
                if recorded.ir() != obj.ir() {
                    return Err(LeanCompileError::new(
                        "WD/ByKnown",
                        "WD id resolves to another object.",
                    ));
                }
                // A cache record is not a proof. Only an earlier replayed constructor
                // or an explicitly introduced certified parameter supplies this term.
                let term = self.object_term(obj)?;
                self.scopes.last_mut().expect("compiler scope").wds.insert(
                    *wd_id,
                    ObjectTerm {
                        object: obj.clone(),
                        term: term.clone(),
                        numeric: None,
                    },
                );
                Ok(term)
            }
            ObjWellDefinedProof::ByDef { obj, proof } => {
                let (term, numeric) = match (obj, proof) {
                    (
                        Obj::Identifier(IdentifierObj::Plain { id, .. }),
                        ObjWellDefinedProofByDef::Identifier(_),
                    ) => (self.identifier_term(*id)?, None),
                    (
                        Obj::Literal(Literal::Number(number)),
                        ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Number(
                            _,
                        )),
                    ) => {
                        let value = number_literal(number, "ℂ")?;
                        (
                            format!("(Litex.number (M := M) {value})"),
                            Some(NumericTerm {
                                denotation: format!(
                                    "(Litex.NativeBridge.denoteNumber (M := M) {value})"
                                ),
                                member: format!("(Litex.numberInC (M := M) {value})"),
                                value,
                            }),
                        )
                    }
                    (Obj::StandardSet(set), ObjWellDefinedProofByDef::StandardSet(_)) => {
                        (standard_term(set)?, None)
                    }
                    (
                        Obj::ArithmeticOperator(operator),
                        ObjWellDefinedProofByDef::ArithmeticOperator(wd),
                    ) => {
                        let (term, numeric) = match (operator, wd) {
                            (
                                ArithmeticOperator::Add(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Add(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Add,
                                runtime,
                            )?,
                            (
                                ArithmeticOperator::Sub(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Sub(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Sub,
                                runtime,
                            )?,
                            (
                                ArithmeticOperator::Mul(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Mul(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Mul,
                                runtime,
                            )?,
                            (
                                ArithmeticOperator::Div(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Div,
                                runtime,
                            )?,
                            (
                                ArithmeticOperator::Neg(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Neg(p),
                            ) => self.compile_neg_wd(
                                &x.arg,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                runtime,
                            )?,
                            (
                                ArithmeticOperator::Pow(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Pow(p),
                            ) => self.compile_pow_wd(
                                &x.base,
                                &x.exponent,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                runtime,
                            )?,
                            _ => {
                                return Err(LeanCompileError::unsupported("WD/ArithmeticOperator"))
                            }
                        };
                        (term, Some(numeric))
                    }
                    (_, unsupported) => return Err(unsupported_wd_definition(unsupported)),
                };
                // Only replayed closed leaves leave a binder scope.
                let closed_leaf =
                    matches!(obj, Obj::Literal(Literal::Number(_)) | Obj::StandardSet(_));
                let scope = if closed_leaf {
                    &mut self.scopes[0]
                } else {
                    self.scopes.last_mut().expect("compiler scope")
                };
                let entry = scope.objects.entry(obj.ir()).or_insert(ObjectTerm {
                    object: obj.clone(),
                    term,
                    numeric,
                });
                Ok(entry.term.clone())
            }
        }
    }

    fn compile_binary_wd(
        &mut self,
        left: &Obj,
        right: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        operation: BinaryArithmetic,
        runtime: &Runtime,
    ) -> Result<(String, NumericTerm), LeanCompileError> {
        let division = matches!(operation, BinaryArithmetic::Div);
        if children.len() != 2 || requirements.len() != if division { 3 } else { 2 } {
            return Err(LeanCompileError::new(
                "WD/Arithmetic",
                "Arithmetic evidence has the wrong stage arity.",
            ));
        }
        ensure_object(left, &children[0])?;
        ensure_object(right, &children[1])?;
        let a = self.compile_wd(&children[0], runtime)?;
        let b = self.compile_wd(&children[1], runtime)?;
        let mut proofs = Vec::new();
        for requirement in requirements {
            proofs.push(self.compile_verify(requirement, runtime)?);
        }
        let offset = usize::from(division);
        ensure_complex_member(&proofs[offset].fact, left)?;
        ensure_complex_member(&proofs[offset + 1].fact, right)?;
        let guard = if division {
            ensure_nonzero_subject(&proofs[0].fact, right)?;
            format!(" {}", proofs[0].proof)
        } else {
            String::new()
        };
        let (name, symbol, bridge) = match operation {
            BinaryArithmetic::Add => ("add", "+", "Add"),
            BinaryArithmetic::Sub => ("sub", "-", "Sub"),
            BinaryArithmetic::Mul => ("mul", "*", "Mul"),
            BinaryArithmetic::Div => ("div", "/", "Div"),
        };
        let arguments = format!(
            "{a} {b} {} {}{guard}",
            proofs[offset].proof,
            proofs[offset + 1].proof
        );
        let x = self.numeric_term(left)?;
        let y = self.numeric_term(right)?;
        Ok((
            format!("(Litex.{name} {arguments})"),
            NumericTerm {
                value: format!("({} {symbol} {})", x.value, y.value),
                denotation: format!(
                    "(Litex.NativeBridge.denote{bridge} {arguments} {} {} {} {})",
                    x.value, y.value, x.denotation, y.denotation
                ),
                member: format!("(Litex.{name}InC {arguments})"),
            },
        ))
    }

    fn compile_neg_wd(
        &mut self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        runtime: &Runtime,
    ) -> Result<(String, NumericTerm), LeanCompileError> {
        if children.len() != 1 || requirements.len() != 1 {
            return Err(LeanCompileError::new(
                "WD/Neg",
                "Negation evidence has the wrong stage arity.",
            ));
        }
        ensure_object(argument, &children[0])?;
        let a = self.compile_wd(&children[0], runtime)?;
        let member = self.compile_verify(&requirements[0], runtime)?;
        ensure_complex_member(&member.fact, argument)?;
        let x = self.numeric_term(argument)?;
        Ok((
            format!("(Litex.neg {a} {})", member.proof),
            NumericTerm {
                value: format!("(- {})", x.value),
                denotation: format!(
                    "(Litex.NativeBridge.denoteNeg {a} {} {} {})",
                    member.proof, x.value, x.denotation
                ),
                member: format!("(Litex.negInC {a} {})", member.proof),
            },
        ))
    }

    fn compile_pow_wd(
        &mut self,
        base: &Obj,
        exponent: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        runtime: &Runtime,
    ) -> Result<(String, NumericTerm), LeanCompileError> {
        if children.len() != 2 || !(requirements.len() == 2 || requirements.len() == 3) {
            return Err(LeanCompileError::new(
                "WD/Pow",
                "Integer-power evidence has the wrong stage arity.",
            ));
        }
        ensure_object(base, &children[0])?;
        ensure_object(exponent, &children[1])?;
        let a = self.compile_wd(&children[0], runtime)?;
        let e = self.compile_wd(&children[1], runtime)?;
        let integer = closed_integer(exponent)
            .ok_or_else(|| LeanCompileError::unsupported("WD/Pow/NonClosedIntegerExponent"))?;
        let mut proved = Vec::new();
        for requirement in requirements {
            proved.push(self.compile_verify(requirement, runtime)?);
        }
        let base_set = membership_subject(&proved[0].fact, base)?;
        let exponent_set = membership_subject(&proved[1].fact, exponent)?;
        let (name, bridge, exponent_value) =
            match (base_set.clone(), exponent_set, requirements.len()) {
                (StandardSet::R, StandardSet::N, 2) if integer >= 0 => {
                    ("powNatReal", "PowNatReal", format!("({integer} : ℕ)"))
                }
                (StandardSet::C, StandardSet::N, 2) if integer >= 0 => {
                    ("powNat", "PowNat", format!("({integer} : ℕ)"))
                }
                (StandardSet::C, StandardSet::Z, 3) => {
                    ensure_nonzero_subject(&proved[2].fact, base)?;
                    ("powInt", "PowInt", format!("({integer} : ℤ)"))
                }
                _ => return Err(LeanCompileError::unsupported("WD/Pow/Domain")),
            };
        if base_set == StandardSet::R {
            self.remember_complex_member(
                base,
                &format!("(Litex.realToComplex {a} {})", proved[0].proof),
            )?;
        }
        // The exponent remains its own owned object; this proof connects its
        // checked closed arithmetic denotation to the exact integer argument.
        let exp_native = self.numeric_term(exponent)?;
        let integer_complex = format!("({exponent_value} : ℂ)");
        let he_value = format!("(Litex.NativeBridge.sameOfDenoteNumber {e} (Litex.number (M := M) {integer_complex}) {} {integer_complex} {} (Litex.NativeBridge.denoteNumber (M := M) {integer_complex}) (by norm_num))", exp_native.value, exp_native.denotation);
        let guard = if requirements.len() == 3 {
            format!(" {}", proved[2].proof)
        } else {
            String::new()
        };
        let arguments = format!(
            "{a} {e} {exponent_value} {} {}{guard} {he_value}",
            proved[0].proof, proved[1].proof
        );
        let x = self.numeric_term(base)?;
        Ok((
            format!("(Litex.{name} {arguments})"),
            NumericTerm {
                value: format!("({} ^ {exponent_value})", x.value),
                denotation: format!(
                    "(Litex.NativeBridge.denote{bridge} {arguments} {} {})",
                    x.value, x.denotation
                ),
                member: format!("(Litex.{name}InC {arguments})"),
            },
        ))
    }

    fn compile_atomic_wd(
        &mut self,
        wd: &AtomicFactWellDefinedProof,
        fact: &AtomicFact,
        runtime: &Runtime,
    ) -> Result<(), LeanCompileError> {
        let args = atomic_fact_args_ref(fact);
        if wd.well_defined_of_each_parameter.len() != args.len() {
            return Err(LeanCompileError::new(
                "WD/Atomic",
                "Object WD evidence has the wrong argument arity.",
            ));
        }
        for (arg, proof) in args.iter().zip(&wd.well_defined_of_each_parameter) {
            ensure_object(arg, proof)?;
            self.compile_wd(proof, runtime)?;
        }
        match &wd.predicate_signature {
            PredicateSignatureWellDefinedProof::Builtin => {}
            PredicateSignatureWellDefinedProof::Prop { .. }
            | PredicateSignatureWellDefinedProof::AbstractProp { .. } => {
                return Err(LeanCompileError::unsupported("WD/UserPredicate"))
            }
        }
        match &wd.predicate_domain {
            PredicateDomainProof::ByRequirements(requirements) => {
                for requirement in requirements {
                    let compiled = self.compile_verify(&requirement.result, runtime)?;
                    if compiled.fact != requirement.requirement {
                        return Err(LeanCompileError::new(
                            "WD/PredicateDomain",
                            "Verified domain requirement has another subject.",
                        ));
                    }
                }
            }
            PredicateDomainProof::ByKnownFact(proof) => {
                self.compile_known_atomic(proof, fact, runtime)?;
            }
        }
        Ok(())
    }

    fn compile_fact_wd(
        &mut self,
        wd: &FactWellDefinedProof,
        fact: &Fact,
        runtime: &Runtime,
    ) -> Result<(), LeanCompileError> {
        match (wd, fact) {
            (FactWellDefinedProof::AtomicExceptEquality(wd), Fact::AtomicFact(atomic)) => {
                self.compile_atomic_wd(wd, atomic, runtime)
            }
            (
                FactWellDefinedProof::Equality(wd),
                Fact::AtomicFact(AtomicFact::EqualFact(equal)),
            ) => {
                ensure_object(&equal.left, &wd.left)?;
                ensure_object(&equal.right, &wd.right)?;
                self.compile_wd(&wd.left, runtime)?;
                self.compile_wd(&wd.right, runtime)?;
                Ok(())
            }
            (FactWellDefinedProof::Equality(_), _) => Err(LeanCompileError::new(
                "WD/Fact",
                "Equality WD has another subject.",
            )),
            (FactWellDefinedProof::AtomicExceptEquality(_), _) => Err(LeanCompileError::new(
                "WD/Fact",
                "Atomic WD has another subject.",
            )),
            (
                FactWellDefinedProof::AndFact { .. }
                | FactWellDefinedProof::ChainFact { .. }
                | FactWellDefinedProof::OrFact(_)
                | FactWellDefinedProof::ExistFact(_)
                | FactWellDefinedProof::ForallFact(_)
                | FactWellDefinedProof::ForallFactWithIff(_)
                | FactWellDefinedProof::NotForall(_),
                _,
            ) => Err(LeanCompileError::unsupported("WD/CompoundFact")),
        }
    }

    fn compile_known_atomic(
        &self,
        proof: &AtomicExceptEqualityFactSearchProofByKnownAtomicFact,
        goal: &AtomicFact,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let resolved = self.resolve_fact(proof.cite_fact_id, runtime)?;
        let cited = match &resolved {
            Fact::AtomicFact(cited) => cited,
            _ => {
                return Err(LeanCompileError::new(
                    "KnownAtomic",
                    "Citation resolves to a non-atomic fact.",
                ))
            }
        };
        let registered = self.fact_term(proof.cite_fact_id)?;
        if registered.fact != resolved || !same_atomic_subject(cited, goal) {
            return Err(LeanCompileError::new(
                "KnownAtomic",
                "Citation or its target differs from the registered proof.",
            ));
        }
        let cited_args = atomic_fact_args_ref(cited);
        let goal_args = atomic_fact_args_ref(goal);
        if proof.why_parameters_of_known_fact_are_equal_to_givens.len() != goal_args.len() {
            return Err(LeanCompileError::new(
                "KnownAtomic",
                "Argument identity evidence has the wrong arity.",
            ));
        }
        for ((cited, goal), identity) in cited_args
            .iter()
            .zip(goal_args)
            .zip(&proof.why_parameters_of_known_fact_are_equal_to_givens)
        {
            match identity {
                EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_))
                    if cited.ir() == goal.ir() => {}
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "KnownAtomic/NonIdentityArgument",
                    ))
                }
            }
        }
        Ok(registered.proof.clone())
    }

    fn compile_structural(
        &mut self,
        proof: &StructuralMembershipProof,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        match &proof.reason {
            StructuralMembershipReason::Known(known) => {
                let fact = self.resolve_fact(known.cite_fact_id, runtime)?;
                let atomic = match &fact {
                    Fact::AtomicFact(AtomicFact::InFact(fact))
                        if fact.element.ir() == proof.element.ir()
                            && fact.set.ir() == Obj::StandardSet(proof.set.clone()).ir() =>
                    {
                        AtomicFact::InFact(fact.clone())
                    }
                    _ => {
                        return Err(LeanCompileError::new(
                            "StructuralMembership/Known",
                            "Cited member has another element or set.",
                        ))
                    }
                };
                self.compile_known_atomic(known, &atomic, runtime)
            }
            StructuralMembershipReason::Closed(closed) => self.compile_closed_membership(
                &proof.element,
                &Obj::StandardSet(proof.set.clone()),
                closed,
            ),
            StructuralMembershipReason::StandardSuperset(child) => {
                if child.element.ir() != proof.element.ir() {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/SupersetSubject",
                        "Standard inclusion evidence changes its element.",
                    ));
                }
                let bridge = match (&child.set, &proof.set) {
                    (StandardSet::R, StandardSet::C) => "realToComplex",
                    (StandardSet::Z, StandardSet::C) => "integerToComplex",
                    (StandardSet::N, StandardSet::C) => "naturalToComplex",
                    (StandardSet::N, StandardSet::Z) => "naturalToInteger",
                    (StandardSet::N, StandardSet::R) => "naturalToReal",
                    (StandardSet::Z, StandardSet::R) => "integerToReal",
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "StructuralMembership/StandardSuperset",
                        ))
                    }
                };
                let child = self.compile_structural(child, runtime)?;
                Ok(format!(
                    "(Litex.{bridge} {} {child})",
                    self.object_term(&proof.element)?
                ))
            }
            StructuralMembershipReason::KnownSubset(_) => Err(LeanCompileError::unsupported(
                "StructuralMembership/KnownSubset",
            )),
            StructuralMembershipReason::Add { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Add, runtime)
            }
            StructuralMembershipReason::Sub { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Sub, runtime)
            }
            StructuralMembershipReason::Mul { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Mul, runtime)
            }
            StructuralMembershipReason::Div { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Div, runtime)
            }
            StructuralMembershipReason::Neg { argument } => {
                let operand = match &proof.element {
                    Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) => x.arg.as_ref(),
                    _ => {
                        return Err(LeanCompileError::new(
                            "StructuralMembership/NegSubject",
                            "Negation membership evidence has another constructor.",
                        ))
                    }
                };
                if operand.ir() != argument.element.ir() || proof.set != argument.set {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/NegChild",
                        "Negation membership changes its operand or carrier.",
                    ));
                }
                let child = self.compile_structural(argument, runtime)?;
                match proof.set {
                    StandardSet::C => Ok(format!(
                        "(Litex.negInC {} {child})",
                        self.object_term(operand)?
                    )),
                    StandardSet::R => Ok(format!(
                        "(Litex.negInR {} {child})",
                        self.object_term(operand)?
                    )),
                    StandardSet::Z => Ok(format!(
                        "(Litex.negInZ {} {child})",
                        self.object_term(operand)?
                    )),
                    _ => Err(LeanCompileError::unsupported(
                        "StructuralMembership/NegCarrier",
                    )),
                }
            }
            StructuralMembershipReason::Abs { .. } => {
                Err(LeanCompileError::unsupported("StructuralMembership/Abs"))
            }
            StructuralMembershipReason::Pow { base, exponent } => {
                let power = match &proof.element {
                    Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => x,
                    _ => {
                        return Err(LeanCompileError::new(
                            "StructuralMembership/PowSubject",
                            "Power membership evidence has another constructor.",
                        ))
                    }
                };
                let expected_exponent = if matches!(proof.set, StandardSet::N | StandardSet::Z) {
                    StandardSet::N
                } else {
                    StandardSet::Z
                };
                if power.base.ir() != base.element.ir()
                    || power.exponent.ir() != exponent.element.ir()
                    || base.set != proof.set
                    || exponent.set != expected_exponent
                {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/PowChild",
                        "Power membership changes its operand or integer carrier.",
                    ));
                }
                let ha_c = self.compile_structural(base, runtime)?;
                let he_z = self.compile_structural(exponent, runtime)?;
                match proof.set {
                    StandardSet::C => Ok(format!(
                        "(Litex.powStructuralInC {} {ha_c} {he_z})",
                        self.object_term(&proof.element)?
                    )),
                    _ => Err(LeanCompileError::unsupported(
                        "StructuralMembership/PowCarrier",
                    )),
                }
            }
            StructuralMembershipReason::Intrinsic(_) => Err(LeanCompileError::unsupported(
                "StructuralMembership/Intrinsic",
            )),
        }
    }

    fn compile_structural_binary(
        &mut self,
        root: &StructuralMembershipProof,
        left: &StructuralMembershipProof,
        right: &StructuralMembershipProof,
        operation: BinaryArithmetic,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (a, b, name) = match (&root.element, operation) {
            (Obj::ArithmeticOperator(ArithmeticOperator::Add(x)), BinaryArithmetic::Add) => {
                (x.left.as_ref(), x.right.as_ref(), "add")
            }
            (Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)), BinaryArithmetic::Sub) => {
                (x.left.as_ref(), x.right.as_ref(), "sub")
            }
            (Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)), BinaryArithmetic::Mul) => {
                (x.left.as_ref(), x.right.as_ref(), "mul")
            }
            (Obj::ArithmeticOperator(ArithmeticOperator::Div(x)), BinaryArithmetic::Div) => {
                (x.left.as_ref(), x.right.as_ref(), "div")
            }
            _ => {
                return Err(LeanCompileError::new(
                    "StructuralMembership/ArithmeticSubject",
                    "Arithmetic membership evidence has another constructor.",
                ))
            }
        };
        if left.element.ir() != a.ir()
            || right.element.ir() != b.ir()
            || left.set != root.set
            || right.set != root.set
        {
            return Err(LeanCompileError::new(
                "StructuralMembership/ArithmeticChild",
                "Arithmetic membership changes its exact children or carrier.",
            ));
        }
        let ha = self.compile_structural(left, runtime)?;
        let hb = self.compile_structural(right, runtime)?;
        match root.set {
            StandardSet::C => {
                let guard = if matches!(operation, BinaryArithmetic::Div) {
                    format!(" ({}).wd.2.2", self.object_term(&root.element)?)
                } else {
                    String::new()
                };
                Ok(format!(
                    "(Litex.{name}InC {} {} {ha} {hb}{guard})",
                    self.object_term(a)?,
                    self.object_term(b)?
                ))
            }
            StandardSet::R => {
                let guard = if matches!(operation, BinaryArithmetic::Div) {
                    format!(" ({}).wd.2.2", self.object_term(&root.element)?)
                } else {
                    String::new()
                };
                Ok(format!(
                    "(Litex.{name}InR {} {} {ha} {hb}{guard})",
                    self.object_term(a)?,
                    self.object_term(b)?
                ))
            }
            _ => Err(LeanCompileError::unsupported(
                "StructuralMembership/ArithmeticCarrier",
            )),
        }
    }

    fn compile_closed_membership(
        &self,
        element: &Obj,
        set: &Obj,
        proof: &ClosedMembershipCalculationProof,
    ) -> Result<String, LeanCompileError> {
        let (value, target) = match proof {
            ClosedMembershipCalculationProof::StandardSet { value, set: target }
                if set.ir() == Obj::StandardSet(target.clone()).ir() =>
            {
                (value, target)
            }
            ClosedMembershipCalculationProof::StandardSet { .. } => {
                return Err(LeanCompileError::new(
                    "ClosedMembership/Set",
                    "Closed membership changes the target set.",
                ))
            }
            ClosedMembershipCalculationProof::IntegerRange { .. } => {
                return Err(LeanCompileError::unsupported(
                    "ClosedMembership/IntegerRange",
                ))
            }
        };
        // Existing literal membership is unbounded integer syntax. It must not
        // inherit the i128 bound of the new closed-arithmetic evaluator.
        if let (Obj::Literal(Literal::Number(number)), ClosedScalarValue::Decimal(recorded)) =
            (element, value)
        {
            if &number.normalized_value != recorded {
                return Err(LeanCompileError::new(
                    "ClosedMembership/Value",
                    "The literal certificate records another numeric payload.",
                ));
            }
            let native = self.numeric_term(element)?;
            if *target == StandardSet::C {
                return Ok(format!("(Litex.numberInC (M := M) {})", native.value));
            }
            let (bridge, representative) = match target {
                StandardSet::R => ("numberInROfEq", number_literal(number, "ℝ")?),
                StandardSet::N | StandardSet::Z => {
                    let value = &number.normalized_value;
                    let unsigned = value.strip_prefix('-').unwrap_or(value);
                    if !unsigned.bytes().all(|b| b.is_ascii_digit())
                        || (*target == StandardSet::N && value.starts_with('-'))
                    {
                        return Err(LeanCompileError::unsupported(
                            "ClosedMembership/IntegerLiteral",
                        ));
                    }
                    if *target == StandardSet::N {
                        ("numberInNOfEq", format!("({value} : ℕ)"))
                    } else {
                        ("numberInZOfEq", format!("({value} : ℤ)"))
                    }
                }
                _ => return Err(LeanCompileError::unsupported("ClosedMembership/Carrier")),
            };
            return Ok(format!("(Litex.NativeBridge.inOfDenoteNumber {} {} {} {} (Litex.NativeBridge.{bridge} {} {representative} (by norm_num)))", self.object_term(element)?, native.value, standard_term(target)?, native.denotation, native.value));
        }
        let calculated = EvalRational::from_obj(element)
            .ok_or_else(|| LeanCompileError::unsupported("ClosedMembership/Expression"))?;
        let scalar = match value {
            ClosedScalarValue::Decimal(value) => scalar_decimal(value)?,
            ClosedScalarValue::ExactComplex { real, imaginary } if imaginary.is_zero() => {
                real.clone()
            }
            ClosedScalarValue::ExactComplex { .. } => {
                return Err(LeanCompileError::unsupported(
                    "ClosedMembership/ComplexScalar",
                ))
            }
        };
        if calculated != scalar {
            return Err(LeanCompileError::new(
                "ClosedMembership/Value",
                "The recorded exact scalar differs from its source arithmetic.",
            ));
        }
        let object = self.object_term(element)?;
        let native = self.numeric_term(element)?;
        if *target == StandardSet::C {
            let scalar = exact_rational_literal(&scalar, "ℂ")?;
            let denotation = format!(
                "({}).trans (congrArg M.number (by norm_num : {} = {scalar}))",
                native.denotation, native.value
            );
            return Ok(format!("(Litex.NativeBridge.inOfDenoteNumber {object} {scalar} {} ({denotation}) (Litex.numberInC (M := M) {scalar}))", standard_term(target)?));
        }
        let (bridge, representative) = match target {
            StandardSet::N => {
                let integer = scalar
                    .to_i128_if_integer()
                    .filter(|n| *n >= 0)
                    .ok_or_else(|| {
                        LeanCompileError::new(
                            "ClosedMembership/N",
                            "A natural certificate has no exact natural value.",
                        )
                    })?;
                ("numberInNOfEq", format!("({integer} : ℕ)"))
            }
            StandardSet::Z => {
                let integer = scalar.to_i128_if_integer().ok_or_else(|| {
                    LeanCompileError::new(
                        "ClosedMembership/Z",
                        "An integer certificate has no exact integer value.",
                    )
                })?;
                ("numberInZOfEq", format!("({integer} : ℤ)"))
            }
            StandardSet::R => ("numberInROfEq", exact_rational_literal(&scalar, "ℝ")?),
            _ => return Err(LeanCompileError::unsupported("ClosedMembership/Carrier")),
        };
        let number_member = format!(
            "(Litex.NativeBridge.{bridge} {} {representative} (by norm_num))",
            native.value
        );
        Ok(format!(
            "(Litex.NativeBridge.inOfDenoteNumber {object} {} {} {} {number_member})",
            native.value,
            standard_term(target)?,
            native.denotation
        ))
    }

    fn atomic_proposition(&self, fact: &AtomicFact) -> Result<String, LeanCompileError> {
        match fact {
            AtomicFact::EqualFact(fact) => Ok(format!(
                "Litex.Same {} {}",
                self.object_term(&fact.left)?,
                self.object_term(&fact.right)?
            )),
            AtomicFact::NotEqualFact(fact) => Ok(format!(
                "¬ Litex.Same {} {}",
                self.object_term(&fact.left)?,
                self.object_term(&fact.right)?
            )),
            AtomicFact::InFact(fact) => Ok(format!(
                "Litex.In {} {}",
                self.object_term(&fact.element)?,
                self.object_term(&fact.set)?
            )),
            AtomicFact::IsSetFact(fact) => {
                Ok(format!("Litex.IsSet {}", self.object_term(&fact.set)?))
            }
            AtomicFact::NormalAtomicFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_)
            | AtomicFact::IsNonemptySetFact(_)
            | AtomicFact::IsFiniteSetFact(_)
            | AtomicFact::SubsetFact(_)
            | AtomicFact::SupersetFact(_)
            | AtomicFact::ProperSubsetFact(_)
            | AtomicFact::ProperSupersetFact(_)
            | AtomicFact::PrimeFact(_)
            | AtomicFact::CoprimeFact(_)
            | AtomicFact::DvdFact(_)
            | AtomicFact::InjectiveFact(_)
            | AtomicFact::SurjectiveFact(_)
            | AtomicFact::BijectiveFact(_)
            | AtomicFact::IsChoiceFunctionForFact(_)
            | AtomicFact::NotNormalAtomicFact(_)
            | AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::NotIsSetFact(_)
            | AtomicFact::NotIsNonemptySetFact(_)
            | AtomicFact::NotIsFiniteSetFact(_)
            | AtomicFact::NotInFact(_)
            | AtomicFact::NotSubsetFact(_)
            | AtomicFact::NotSupersetFact(_)
            | AtomicFact::NotProperSubsetFact(_)
            | AtomicFact::NotProperSupersetFact(_)
            | AtomicFact::NotPrimeFact(_)
            | AtomicFact::NotCoprimeFact(_)
            | AtomicFact::NotDvdFact(_)
            | AtomicFact::NotInjectiveFact(_)
            | AtomicFact::NotSurjectiveFact(_)
            | AtomicFact::NotBijectiveFact(_)
            | AtomicFact::NotIsChoiceFunctionForFact(_) => {
                Err(LeanCompileError::unsupported("Atomic/PropositionFamily"))
            }
        }
    }

    fn validate_store(
        &self,
        store: &StoreFactAndInferResult,
        expected: &Fact,
    ) -> Result<(), LeanCompileError> {
        let actual = match &store.store {
            StoreFactResult::AtomicFact(stored) => Fact::AtomicFact(stored.fact.clone()),
            StoreFactResult::ForallFact(stored) => Fact::ForallFact(stored.fact.clone()),
            StoreFactResult::AndFact(_)
            | StoreFactResult::ChainFact(_)
            | StoreFactResult::OrFact(_)
            | StoreFactResult::ExistShapedFact(_)
            | StoreFactResult::NotForallFact(_)
            | StoreFactResult::ForallFactWithIff(_) => {
                return Err(LeanCompileError::unsupported("Store/Compound"))
            }
        };
        if &actual != expected || store.primary_fact_id() != expected.fact_id() {
            return Err(LeanCompileError::new(
                "Store/Subject",
                "The stored target differs from the replayed verification.",
            ));
        }
        // Additional inferred facts are not promoted to assumptions. A future
        // citation of an uncompiled inference fails the producer-registry lookup.
        Ok(())
    }

    fn remember_complex_member(
        &mut self,
        object: &Obj,
        member: &str,
    ) -> Result<(), LeanCompileError> {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(entry) = scope.objects.get_mut(&object.ir()) {
                if entry.numeric.is_none() {
                    entry.numeric = Some(NumericTerm {
                        value: format!("(Litex.NativeBridge.asComplex {} {member})", entry.term),
                        denotation: format!(
                            "(Litex.NativeBridge.asComplex_spec {} {member})",
                            entry.term
                        ),
                        member: member.to_string(),
                    });
                }
                return Ok(());
            }
        }
        Err(LeanCompileError::new(
            "Arithmetic/Producer",
            "A membership proof has no previously certified object.",
        ))
    }

    fn numeric_term(&self, object: &Obj) -> Result<NumericTerm, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(entry) = scope.objects.get(&object.ir()) {
                return entry.numeric.clone().ok_or_else(|| LeanCompileError::new("Arithmetic/NumericEvidence", "No recorded numeric construction or C-membership proof supplies this denotation."));
            }
        }
        Err(LeanCompileError::new(
            "Arithmetic/Producer",
            "No replayed object supplies this numeric denotation.",
        ))
    }

    fn remember_fact(&mut self, fact: FactTerm) {
        self.scopes
            .last_mut()
            .expect("compiler scope")
            .facts
            .insert(fact.fact.fact_id(), fact);
    }

    fn object_term(&self, object: &Obj) -> Result<String, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(entry) = scope.objects.get(&object.ir()) {
                if entry.object.ir() == object.ir() {
                    return Ok(entry.term.clone());
                }
            }
        }
        Err(LeanCompileError::new(
            "WD/Producer",
            "No earlier replayed constructor or certified parameter supplies this object.",
        ))
    }

    fn identifier_term(&self, id: IdentifierId) -> Result<String, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(entry) = scope.identifiers.get(&id) {
                return Ok(entry.term.clone());
            }
        }
        Err(LeanCompileError::new(
            "Identifier/Producer",
            "The identifier was not introduced in an active compiled scope.",
        ))
    }

    fn fact_term(&self, id: FactId) -> Result<&FactTerm, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(entry) = scope.facts.get(&id) {
                return Ok(entry);
            }
        }
        Err(LeanCompileError::new(
            "FactId/Producer",
            "The cited fact has no compiled proof or active source assumption.",
        ))
    }

    fn resolve_fact(&self, id: FactId, runtime: &Runtime) -> Result<Fact, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(env) = &scope.env {
                if let Some(fact) = env.facts.facts_by_id.get(&id) {
                    return Ok(fact.clone());
                }
            }
        }
        runtime.fact_by_id_in_stack(id).cloned().ok_or_else(|| {
            LeanCompileError::new(
                "FactId/Resolution",
                "The cited fact is absent from the live scope context.",
            )
        })
    }

    fn resolve_wd(
        &self,
        id: WellDefinednessId,
        runtime: &Runtime,
    ) -> Result<Obj, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(env) = &scope.env {
                if let Some(object) = env.well_defined_objects.wd_id_to_object.get(&id) {
                    return Ok(object.clone());
                }
            }
        }
        for env in runtime.execution_environments_stack.iter().rev() {
            if let Some(object) = env.well_defined_objects.wd_id_to_object.get(&id) {
                return Ok(object.clone());
            }
        }
        Err(LeanCompileError::new(
            "WdId/Resolution",
            "The cited WD record is absent from the live scope context.",
        ))
    }
}

#[derive(Clone, Copy)]
enum BinaryArithmetic {
    Add,
    Sub,
    Mul,
    Div,
}

fn ensure_nonzero_subject(fact: &Fact, object: &Obj) -> Result<(), LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::NotEqualFact(x)) if x.left.ir() == object.ir() && is_zero(&x.right) => Ok(()),
        _ => Err(LeanCompileError::new("Arithmetic/NonzeroSubject", "The requirement must be this exact object's inequality with zero, in source orientation.")),
    }
}

fn membership_subject(fact: &Fact, object: &Obj) -> Result<StandardSet, LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::InFact(x)) if x.element.ir() == object.ir() => match &x.set {
            Obj::StandardSet(set) => Ok(set.clone()),
            _ => Err(LeanCompileError::unsupported(
                "Arithmetic/NonstandardDomain",
            )),
        },
        _ => Err(LeanCompileError::new(
            "Arithmetic/MembershipSubject",
            "Membership evidence describes another operand.",
        )),
    }
}

fn closed_integer(object: &Obj) -> Option<i128> {
    EvalRational::from_obj(object)?.to_i128_if_integer()
}

fn validate_arithmetic_expression(object: &Obj) -> Result<(), LeanCompileError> {
    match object {
        Obj::Identifier(IdentifierObj::Plain { .. }) => Ok(()),
        Obj::Literal(Literal::Number(n)) => number_literal(n, "ℂ").map(|_| ()),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) => {
            validate_arithmetic_expression(&x.arg)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => {
            validate_arithmetic_expression(&x.base)?;
            validate_arithmetic_expression(&x.exponent)?;
            closed_integer(&x.exponent)
                .ok_or_else(|| LeanCompileError::unsupported("Rational/NonClosedIntegerPower"))?;
            Ok(())
        }
        _ => Err(LeanCompileError::unsupported("Rational/ExpressionDomain")),
    }
}

fn normalization_nonzero_subjects(left: &Obj, right: &Obj) -> Result<Vec<Obj>, LeanCompileError> {
    fn collect(object: &Obj, subjects: &mut Vec<Obj>) -> Result<(), LeanCompileError> {
        match object {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
                if !subjects.iter().any(|o| o.ir() == x.right.ir()) {
                    subjects.push(x.right.as_ref().clone());
                }
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) => collect(&x.arg, subjects)?,
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => {
                collect(&x.base, subjects)?;
                collect(&x.exponent, subjects)?;
                let value = evaluate_obj_to_normalized_decimal_number(&x.exponent)
                    .and_then(|n| n.normalized_value.parse::<i128>().ok());
                if closed_integer(&x.exponent).is_some_and(|z| z < 0) && value.is_none() {
                    return Err(LeanCompileError::unsupported(
                        "Rational/NegativePowerGuardProfile",
                    ));
                }
                if value.is_some_and(|z| z < 0) && !subjects.iter().any(|o| o.ir() == x.base.ir()) {
                    subjects.push(x.base.as_ref().clone());
                }
            }
            _ => {}
        }
        Ok(())
    }
    fn factors(object: &Obj, result: &mut Vec<Obj>) {
        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) = object {
            factors(&x.left, result);
            factors(&x.right, result);
        } else if !result.iter().any(|o| o.ir() == object.ir()) {
            result.push(object.clone());
        }
    }
    let mut subjects = Vec::new();
    collect(left, &mut subjects)?;
    collect(right, &mut subjects)?;
    let mut result = Vec::new();
    for subject in subjects {
        factors(&subject, &mut result);
    }
    Ok(result)
}

fn exact_rational_literal(value: &EvalRational, ty: &str) -> Result<String, LeanCompileError> {
    match value.to_obj() {
        Obj::Literal(Literal::Number(n)) => number_literal(&n, ty),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => match (*x.left, *x.right) {
            (Obj::Literal(Literal::Number(a)), Obj::Literal(Literal::Number(b))) => Ok(format!(
                "({} / {})",
                number_literal(&a, ty)?,
                number_literal(&b, ty)?
            )),
            _ => Err(LeanCompileError::new(
                "Number/ExactRational",
                "The exact scalar has an unexpected canonical shape.",
            )),
        },
        _ => Err(LeanCompileError::new(
            "Number/ExactRational",
            "The exact scalar has an unexpected canonical shape.",
        )),
    }
}

fn scalar_decimal(value: &str) -> Result<EvalRational, LeanCompileError> {
    let number = Number::new(value.to_string());
    number_literal(&number, "ℂ")?;
    EvalRational::from_obj(&Obj::Literal(Literal::Number(number)))
        .ok_or_else(|| LeanCompileError::unsupported("Number/ExactEvaluationBound"))
}

fn number_literal(number: &Number, ty: &str) -> Result<String, LeanCompileError> {
    let value = &number.normalized_value;
    let unsigned = value.strip_prefix('-').unwrap_or(value);
    let mut parts = unsigned.split('.');
    let whole = parts.next().unwrap_or("");
    let fractional = parts.next();
    if whole.is_empty()
        || !whole.bytes().all(|b| b.is_ascii_digit())
        || fractional.is_some_and(|s| s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()))
        || parts.next().is_some()
    {
        return Err(LeanCompileError::unsupported("Number/FiniteDecimalLiteral"));
    }
    Ok(format!("({value} : {ty})"))
}

fn ensure_object(object: &Obj, proof: &ObjWellDefinedProof) -> Result<(), LeanCompileError> {
    if object.ir() != proof.obj().ir() {
        return Err(LeanCompileError::new(
            "WD/Subject",
            "Object WD describes a different subject.",
        ));
    }
    Ok(())
}

fn ensure_complex_member(fact: &Fact, object: &Obj) -> Result<(), LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::InFact(fact))
            if fact.element.ir() == object.ir() && fact.set == Obj::StandardSet(StandardSet::C) =>
        {
            Ok(())
        }
        _ => Err(LeanCompileError::new(
            "WD/ArithmeticDomain",
            "An operand requirement is not membership of this operand in C.",
        )),
    }
}

fn same_atomic_subject(left: &AtomicFact, right: &AtomicFact) -> bool {
    if std::mem::discriminant(left) != std::mem::discriminant(right) {
        return false;
    }
    let left = atomic_fact_args_ref(left);
    let right = atomic_fact_args_ref(right);
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| left.ir() == right.ir())
}

fn is_zero(object: &Obj) -> bool {
    matches!(object, Obj::Literal(Literal::Number(number)) if number.normalized_value == "0")
}

fn standard_term(set: &StandardSet) -> Result<String, LeanCompileError> {
    let name = match set {
        StandardSet::N => "N",
        StandardSet::Z => "Z",
        StandardSet::Q => "Q",
        StandardSet::R => "R",
        StandardSet::C => "C",
        StandardSet::NPos
        | StandardSet::QPos
        | StandardSet::RPos
        | StandardSet::QNeg
        | StandardSet::ZNeg
        | StandardSet::RNeg
        | StandardSet::QStar
        | StandardSet::ZStar
        | StandardSet::RStar
        | StandardSet::CStar => {
            return Err(LeanCompileError::unsupported("StandardSet/SignedOrNonzero"))
        }
    };
    Ok(format!("(Litex.{name} (M := M))"))
}

fn unsupported_wd_definition(proof: &ObjWellDefinedProofByDef) -> LeanCompileError {
    match proof {
        ObjWellDefinedProofByDef::Identifier(_) => {
            LeanCompileError::unsupported("WD/IdentifierShape")
        }
        ObjWellDefinedProofByDef::Literal(_) => LeanCompileError::unsupported("WD/Literal"),
        ObjWellDefinedProofByDef::StandardSet(_) => LeanCompileError::new(
            "WD/StandardSet",
            "Definition evidence has another object family.",
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(_) => {
            LeanCompileError::unsupported("WD/ArithmeticOperator")
        }
        ObjWellDefinedProofByDef::FnObj(_) => LeanCompileError::unsupported("WD/FnObj"),
        ObjWellDefinedProofByDef::IntegerOperator(_) => {
            LeanCompileError::unsupported("WD/IntegerOperator")
        }
        ObjWellDefinedProofByDef::TrigOperator(_) => {
            LeanCompileError::unsupported("WD/TrigOperator")
        }
        ObjWellDefinedProofByDef::ExpLogOperator(_) => {
            LeanCompileError::unsupported("WD/ExpLogOperator")
        }
        ObjWellDefinedProofByDef::ComplexOperator(_) => {
            LeanCompileError::unsupported("WD/ComplexOperator")
        }
        ObjWellDefinedProofByDef::SetOperator(_) => LeanCompileError::unsupported("WD/SetOperator"),
        ObjWellDefinedProofByDef::SetFormer(_) => LeanCompileError::unsupported("WD/SetFormer"),
        ObjWellDefinedProofByDef::ProductShape(_) => {
            LeanCompileError::unsupported("WD/ProductShape")
        }
        ObjWellDefinedProofByDef::FunctionSpace(_) => {
            LeanCompileError::unsupported("WD/FunctionSpace")
        }
        ObjWellDefinedProofByDef::IteratedOperator(_) => {
            LeanCompileError::unsupported("WD/IteratedOperator")
        }
        ObjWellDefinedProofByDef::FiniteSetStat(_) => {
            LeanCompileError::unsupported("WD/FiniteSetStat")
        }
        ObjWellDefinedProofByDef::Structish(_) => LeanCompileError::unsupported("WD/Structish"),
        ObjWellDefinedProofByDef::InstantiatedTemplateObj(_) => {
            LeanCompileError::unsupported("WD/InstantiatedTemplateObj")
        }
    }
}

fn unsupported_atomic_builtin(
    proof: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
) -> LeanCompileError {
    match proof {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact(_) => LeanCompileError::new(
            "Builtin/IsSet",
            "Sethood certificate does not match its subject.",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NormalAtomicFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::SupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::PrimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::CoprimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::DvdFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::InjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::SurjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::BijectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::IsChoiceFunctionForFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotNormalAtomicFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsSetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsNonemptySetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsFiniteSetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotPrimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotCoprimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotDvdFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSurjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotBijectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsChoiceFunctionForFact(_) => {
            LeanCompileError::unsupported("Atomic/BuiltinRule")
        }
    }
}

fn validate_namespace(value: &str) -> Result<(), LeanCompileError> {
    let mut bytes = value.bytes();
    let valid_start = bytes
        .next()
        .map(|byte| byte.is_ascii_alphabetic() || byte == b'_')
        .unwrap_or(false);
    let reserved = [
        "_",
        "axiom",
        "by",
        "class",
        "def",
        "do",
        "else",
        "end",
        "example",
        "export",
        "false",
        "forall",
        "from",
        "fun",
        "if",
        "import",
        "in",
        "inductive",
        "instance",
        "let",
        "macro",
        "match",
        "mutual",
        "namespace",
        "noncomputable",
        "opaque",
        "open",
        "partial",
        "private",
        "protected",
        "section",
        "set_option",
        "structure",
        "syntax",
        "then",
        "theorem",
        "true",
        "universe",
        "unsafe",
        "variable",
        "where",
        "with",
    ];
    if !valid_start
        || !bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        || reserved.contains(&value)
    {
        return Err(LeanCompileError::new(
            "artifact_namespace",
            "The artifact namespace must be a simple nonreserved ASCII Lean identifier.",
        ));
    }
    Ok(())
}
