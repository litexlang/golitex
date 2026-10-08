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
                        EqualFactSearchedProof::ByClosedCalculation(_) => {
                            return Err(LeanCompileError::unsupported("Equality/ClosedCalculation"))
                        }
                        EqualFactSearchedProof::ByKnownSpecialProperty(_) => {
                            return Err(LeanCompileError::unsupported(
                                "Equality/KnownSpecialProperty",
                            ))
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
                        EqualFactSearchedProof::ByBuiltinStrategy(_) => {
                            return Err(LeanCompileError::unsupported("Equality/BuiltinStrategy"))
                        }
                        EqualFactSearchedProof::ByMatchingOneArgByOne(_) => {
                            return Err(LeanCompileError::unsupported(
                                "Equality/MatchingOneArgByOne",
                            ))
                        }
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
            VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
                VerifyAtomicExceptEqualityFactResult::Success(success) => {
                    self.compile_atomic_wd(&success.well_defined_proof, &success.fact, runtime)?;
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
            },
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
                    },
                );
                Ok(term)
            }
            ObjWellDefinedProof::ByDef { obj, proof } => {
                let term = match (obj, proof) {
                    (
                        Obj::Identifier(IdentifierObj::Plain { id, .. }),
                        ObjWellDefinedProofByDef::Identifier(_),
                    ) => self.identifier_term(*id)?,
                    (
                        Obj::Literal(Literal::Number(number)),
                        ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Number(
                            _,
                        )),
                    ) => format!("(Litex.number (M := M) ({} : ℂ))", integer_literal(number)?),
                    (Obj::StandardSet(set), ObjWellDefinedProofByDef::StandardSet(_)) => {
                        standard_term(set)?
                    }
                    (
                        Obj::ArithmeticOperator(ArithmeticOperator::Add(add)),
                        ObjWellDefinedProofByDef::ArithmeticOperator(
                            ArithmeticOperatorObjWellDefinedProofByDef::Add(proof),
                        ),
                    ) => self.compile_binary_wd(
                        &add.left,
                        &add.right,
                        &proof.child_obj_well_defined,
                        &proof.requirement_fact_verified,
                        false,
                        runtime,
                    )?,
                    (
                        Obj::ArithmeticOperator(ArithmeticOperator::Div(div)),
                        ObjWellDefinedProofByDef::ArithmeticOperator(
                            ArithmeticOperatorObjWellDefinedProofByDef::Div(proof),
                        ),
                    ) => self.compile_binary_wd(
                        &div.left,
                        &div.right,
                        &proof.child_obj_well_defined,
                        &proof.requirement_fact_verified,
                        true,
                        runtime,
                    )?,
                    (_, unsupported) => return Err(unsupported_wd_definition(unsupported)),
                };
                // Closed factory certificates do not depend on a binder scope.
                // Retain an actually replayed leaf for later WD-id citations;
                // never hoist generic operands, arithmetic terms or local facts.
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
        division: bool,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
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
        let membership_offset = if division { 1 } else { 0 };
        ensure_complex_member(&proofs[membership_offset].fact, left)?;
        ensure_complex_member(&proofs[membership_offset + 1].fact, right)?;
        if division {
            match &proofs[0].fact {
                Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero))
                    if nonzero.left.ir() == right.ir() && is_zero(&nonzero.right) => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "WD/Div",
                        "The first division requirement must certify this divisor is nonzero.",
                    ))
                }
            }
            Ok(format!(
                "(Litex.div {a} {b} {} {} {})",
                proofs[1].proof, proofs[2].proof, proofs[0].proof
            ))
        } else {
            Ok(format!(
                "(Litex.add {a} {b} {} {})",
                proofs[0].proof, proofs[1].proof
            ))
        }
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
                if proof.set != StandardSet::C
                    || child.set != StandardSet::R
                    || child.element.ir() != proof.element.ir()
                {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/StandardSupersetOutsideRtoC",
                    ));
                }
                let child = self.compile_structural(child, runtime)?;
                Ok(format!(
                    "(Litex.realToComplex {} {child})",
                    self.object_term(&proof.element)?
                ))
            }
            StructuralMembershipReason::KnownSubset(_) => Err(LeanCompileError::unsupported(
                "StructuralMembership/KnownSubset",
            )),
            StructuralMembershipReason::Add { .. } => {
                Err(LeanCompileError::unsupported("StructuralMembership/Add"))
            }
            StructuralMembershipReason::Sub { .. } => {
                Err(LeanCompileError::unsupported("StructuralMembership/Sub"))
            }
            StructuralMembershipReason::Mul { .. } => {
                Err(LeanCompileError::unsupported("StructuralMembership/Mul"))
            }
            StructuralMembershipReason::Div { .. } => {
                Err(LeanCompileError::unsupported("StructuralMembership/Div"))
            }
            StructuralMembershipReason::Neg { .. } => {
                Err(LeanCompileError::unsupported("StructuralMembership/Neg"))
            }
            StructuralMembershipReason::Abs { .. } => {
                Err(LeanCompileError::unsupported("StructuralMembership/Abs"))
            }
            StructuralMembershipReason::Pow { .. } => {
                Err(LeanCompileError::unsupported("StructuralMembership/Pow"))
            }
            StructuralMembershipReason::Intrinsic(_) => Err(LeanCompileError::unsupported(
                "StructuralMembership/Intrinsic",
            )),
        }
    }

    fn compile_closed_membership(
        &self,
        element: &Obj,
        set: &Obj,
        proof: &ClosedMembershipCalculationProof,
    ) -> Result<String, LeanCompileError> {
        let number = match element {
            Obj::Literal(Literal::Number(number)) => integer_literal(number)?,
            _ => return Err(LeanCompileError::unsupported("ClosedMembership/NonLiteral")),
        };
        match proof {
            ClosedMembershipCalculationProof::StandardSet {
                value: ClosedScalarValue::Decimal(value),
                set: target,
            } if value == &number && set.ir() == Obj::StandardSet(target.clone()).ir() => {
                match target {
                    StandardSet::R => Ok(format!(
                        "(Litex.NativeBridge.numberInR (M := M) ({number} : ℝ))"
                    )),
                    StandardSet::C => Ok(format!("(Litex.numberInC (M := M) ({number} : ℂ))")),
                    StandardSet::NPos
                    | StandardSet::N
                    | StandardSet::Q
                    | StandardSet::Z
                    | StandardSet::QPos
                    | StandardSet::RPos
                    | StandardSet::QNeg
                    | StandardSet::ZNeg
                    | StandardSet::RNeg
                    | StandardSet::QStar
                    | StandardSet::ZStar
                    | StandardSet::RStar
                    | StandardSet::CStar => {
                        Err(LeanCompileError::unsupported("ClosedMembership/Carrier"))
                    }
                }
            }
            ClosedMembershipCalculationProof::StandardSet { .. } => Err(LeanCompileError::new(
                "ClosedMembership",
                "Only the matching exact integer literal certificate is supported.",
            )),
            ClosedMembershipCalculationProof::IntegerRange { .. } => Err(
                LeanCompileError::unsupported("ClosedMembership/IntegerRange"),
            ),
        }
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

fn integer_literal(number: &Number) -> Result<String, LeanCompileError> {
    if number.normalized_value.is_empty()
        || !number
            .normalized_value
            .bytes()
            .all(|byte| byte.is_ascii_digit())
    {
        return Err(LeanCompileError::unsupported("Number/NonIntegerLiteral"));
    }
    Ok(number.normalized_value.clone())
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
