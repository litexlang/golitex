use super::helper::validate_namespace;
use super::helper::verified_subject;
use super::source_position::{SourceOwner, SourcePosition};
use super::LeanCompileError;
use crate::execute::execute_by_stmt::{
    ByInducBodySuccess, ExecByDefStmtResult, ExecByInducStmtResult, ExecByStmtResult,
    ExecByThmStmtResult, ExecReleaseThmStmtResult,
};
use crate::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactResult;
use crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult;
use crate::execute::execute_proof_block_stmt::{ExecClaimStmtResult, ExecProofBlockStmtResult};
use crate::execute::ExecDefPropStmtResult;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferEqualFactResult, InferResult};

/// Compile one complete execution result by dispatching its original result enums.
/// Runtime supplies read-only exact citation subjects; source positions enforce
/// producer order and lexical visibility without a compiler-owned proof world.
pub struct LitexToLeanCompiler {
    pub(super) runtime: Runtime,
}

impl LitexToLeanCompiler {
    pub fn new(runtime: Runtime) -> Self {
        Self { runtime }
    }

    /// Produce one complete artifact; an error returns no partial Lean output.
    pub fn compile_run(
        &self,
        result: &RunLitexCodeResult,
        artifact_namespace: &str,
    ) -> Result<String, LeanCompileError> {
        let position = SourcePosition {
            parent: None,
            owner: SourceOwner::Run(result),
            before: 0,
        };
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
        let mut declarations = Vec::new();
        for (index, result) in result.statement_results.iter().enumerate() {
            let compiled = self
                .compile_statement(
                    result,
                    &SourcePosition {
                        before: index,
                        ..position
                    },
                    index + 1,
                )
                .map_err(|mut error| {
                    error.statement_index = Some(index + 1);
                    error
                })?;
            declarations.push(compiled);
        }
        let universes = self.source_universes(result)?;
        let uses_functions = result
            .statement_results
            .iter()
            .any(statement_uses_functions);
        // FunctionSemantics already supplies its SetSemantics parent. A
        // second data-carrying instance would give mixed set/function terms
        // conflicting interpretations of the same source set constructors.
        let sets = if !uses_functions && result.statement_results.iter().any(statement_uses_sets) {
            "\nset_option linter.unusedSectionVars false\nvariable [_setSemantics : Litex.SetSemantics M]"
        } else {
            ""
        };
        let functions = if uses_functions {
            "\nset_option linter.unusedSectionVars false\nvariable [_functionSemantics : Litex.FunctionSemantics M]"
        } else {
            ""
        };
        Ok(format!("import Litex\n\nset_option linter.unusedVariables false\n\nnamespace LitexCompiled.{artifact_namespace}\n\nuniverse {universes}\nvariable {{M : Litex.Semantics.{{u}}}}{sets}{functions}\n\n{}\nend LitexCompiled.{artifact_namespace}\n", declarations.join("\n\n")))
    }
}

fn object_uses_functions(object: &Obj) -> bool {
    match object {
        Obj::FnObj(_) | Obj::FunctionSpace(_) => true,
        Obj::ArithmeticOperator(operation) => match operation {
            ArithmeticOperator::Add(x) => {
                object_uses_functions(&x.left) || object_uses_functions(&x.right)
            }
            ArithmeticOperator::Sub(x) => {
                object_uses_functions(&x.left) || object_uses_functions(&x.right)
            }
            ArithmeticOperator::Mul(x) => {
                object_uses_functions(&x.left) || object_uses_functions(&x.right)
            }
            ArithmeticOperator::Div(x) => {
                object_uses_functions(&x.left) || object_uses_functions(&x.right)
            }
            ArithmeticOperator::Neg(x) => object_uses_functions(&x.arg),
            ArithmeticOperator::Abs(x) => object_uses_functions(&x.arg),
            ArithmeticOperator::Pow(x) => {
                object_uses_functions(&x.base) || object_uses_functions(&x.exponent)
            }
            _ => false,
        },
        _ => false,
    }
}

fn fact_uses_functions(fact: &Fact) -> bool {
    match fact {
        Fact::AtomicFact(fact) => atomic_fact_args_ref(fact)
            .into_iter()
            .any(object_uses_functions),
        Fact::AndFact(fact) => fact.facts.iter().any(|fact| {
            atomic_fact_args_ref(fact)
                .into_iter()
                .any(object_uses_functions)
        }),
        Fact::ChainFact(fact) => fact.objs.iter().any(object_uses_functions),
        Fact::OrFact(fact) => fact
            .facts
            .iter()
            .any(|branch| fact_uses_functions(&crate::ast::fact::and_chain_as_fact(branch))),
        Fact::ForallFact(fact) => {
            fact.dom_facts.iter().any(fact_uses_functions)
                || fact.then_facts.iter().any(|fact| match fact {
                    ExistOrAndChainAtomicFact::AtomicFact(fact) => atomic_fact_args_ref(fact)
                        .into_iter()
                        .any(object_uses_functions),
                    ExistOrAndChainAtomicFact::AndFact(fact) => fact.facts.iter().any(|fact| {
                        atomic_fact_args_ref(fact)
                            .into_iter()
                            .any(object_uses_functions)
                    }),
                    ExistOrAndChainAtomicFact::ChainFact(fact) => {
                        fact.objs.iter().any(object_uses_functions)
                    }
                    ExistOrAndChainAtomicFact::OrFact(fact) => {
                        fact_uses_functions(&Fact::OrFact(fact.clone()))
                    }
                    _ => false,
                })
        }
        _ => false,
    }
}

fn statement_uses_functions(statement: &ExecStmtResult) -> bool {
    match statement {
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Success(proof),
        )) => {
            fact_uses_functions(&proof.statement.fact)
                || proof
                    .body
                    .proof_steps()
                    .iter()
                    .any(statement_uses_functions)
        }
        ExecStmtResult::Definition(
            ExecDefinitionStmtResult::HaveFnEqual(_) | ExecDefinitionStmtResult::HaveFnByInduc(_),
        ) => true,
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => {
            verified_subject(&proof.verify_result)
                .as_ref()
                .is_some_and(fact_uses_functions)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
            ExecDefPropStmtResult::Success(proof),
        )) => proof.statement.iff_facts.iter().any(fact_uses_functions),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(proof),
        )) => {
            fact_uses_functions(&proof.statement.fact)
                || match &proof.body {
                    ExecDefThmBodyProof::Forall(body) => {
                        body.proof_steps.iter().any(statement_uses_functions)
                    }
                    ExecDefThmBodyProof::NonForall(body) => {
                        body.proof_steps.iter().any(statement_uses_functions)
                    }
                }
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(proof)),
        )) => object_uses_functions(&proof.statement.value),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
        )) => proof
            .statement
            .objs_equal_to
            .iter()
            .any(object_uses_functions),
        _ => false,
    }
}

fn object_uses_sets(object: &Obj) -> bool {
    match object {
        Obj::StandardSet(StandardSet::RPos) => true,
        Obj::SetFormer(SetFormer::ListSet(_) | SetFormer::SetBuilder(_)) => true,
        Obj::ArithmeticOperator(operator) => match operator {
            ArithmeticOperator::Add(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Sub(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Mul(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Div(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Neg(x) => object_uses_sets(&x.arg),
            ArithmeticOperator::Abs(x) => object_uses_sets(&x.arg),
            ArithmeticOperator::Pow(x) => {
                object_uses_sets(&x.base) || object_uses_sets(&x.exponent)
            }
            _ => false,
        },
        _ => false,
    }
}

fn fact_uses_sets(fact: &Fact) -> bool {
    match fact {
        Fact::AtomicFact(f) => atomic_fact_args_ref(f).iter().any(|a| object_uses_sets(a)),
        Fact::AndFact(f) => f
            .facts
            .iter()
            .any(|f| atomic_fact_args_ref(f).iter().any(|a| object_uses_sets(a))),
        Fact::ChainFact(f) => f.objs.iter().any(object_uses_sets),
        Fact::OrFact(f) => f
            .facts
            .iter()
            .any(|branch| fact_uses_sets(&crate::ast::fact::and_chain_as_fact(branch))),
        Fact::ForallFact(f) => {
            f.typed_parameters
                .groups
                .iter()
                .any(|g| matches!(&g.param_type, ParamType::Obj(a) if object_uses_sets(a)))
                || f.dom_facts.iter().any(fact_uses_sets)
                || f.then_facts.iter().any(|f| match f {
                    ExistOrAndChainAtomicFact::AtomicFact(a) => {
                        atomic_fact_args_ref(a).iter().any(|a| object_uses_sets(a))
                    }
                    ExistOrAndChainAtomicFact::AndFact(f) => f
                        .facts
                        .iter()
                        .any(|f| atomic_fact_args_ref(f).iter().any(|a| object_uses_sets(a))),
                    ExistOrAndChainAtomicFact::ChainFact(f) => f.objs.iter().any(object_uses_sets),
                    ExistOrAndChainAtomicFact::OrFact(f) => {
                        fact_uses_sets(&Fact::OrFact(f.clone()))
                    }
                    _ => false,
                })
        }
        _ => false,
    }
}

fn statement_uses_sets(statement: &ExecStmtResult) -> bool {
    if statement_has_set_inference(statement) {
        return true;
    }
    match statement {
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Success(proof),
        )) => {
            fact_uses_sets(&proof.statement.fact)
                || proof.body.proof_steps().iter().any(statement_uses_sets)
        }
        ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) => verified_subject(&p.verify_result)
            .as_ref()
            .is_some_and(fact_uses_sets),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
        )) => object_uses_sets(&p.statement.value),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
        )) => p.statement.objs_equal_to.iter().any(object_uses_sets),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) => {
            fact_uses_sets(&p.statement.fact)
                || match &p.body {
                    ExecDefThmBodyProof::Forall(b) => b.proof_steps.iter().any(statement_uses_sets),
                    ExecDefThmBodyProof::NonForall(b) => {
                        b.proof_steps.iter().any(statement_uses_sets)
                    }
                }
        }
        _ => false,
    }
}

// Inference may introduce R+ even when the authored statement mentions only
// natural numbers. Derive that semantic dependency from the reviewed original
// rule/store tree; no generated text or compiler-owned dependency registry.
fn store_has_set_inference(store: &StoreFactAndInferResult) -> bool {
    let atomic_has_set_inference = |infer: &InferAtomicFactResult| {
        let InferAtomicFactResult::EqualFact(rules) = infer else {
            return false;
        };
        rules.iter().any(|rule| {
            let InferEqualFactResult::PositiveRealPower(power) = rule else { return false; };
            power.transports.iter().any(|transport| {
                transport.derived.store.atomic_components().iter().any(|(_, fact)| {
                    matches!(fact, AtomicFact::InFact(member) if member.set == Obj::StandardSet(StandardSet::RPos))
                })
            })
        })
    };
    match &store.infer {
        Some(InferResult::AtomicFact(infer)) => atomic_has_set_inference(infer),
        Some(InferResult::AndFact(infer)) => infer.components.iter().any(atomic_has_set_inference),
        Some(InferResult::ChainFact(infer)) => infer
            .adjacent_infers
            .iter()
            .any(|edge| atomic_has_set_inference(&edge.infer)),
        _ => false,
    }
}

fn domains_have_set_inference(domains: &[AssumeDomFactResult]) -> bool {
    domains
        .iter()
        .any(|domain| store_has_set_inference(&domain.store_and_infer))
}

fn verify_has_set_inference(proof: &VerifyFactResult) -> bool {
    match proof {
        VerifyFactResult::ForallFact(proof) => match proof.as_ref() {
            VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) => {
                domains_have_set_inference(&proof.assumed_dom_facts)
                    || proof.proved_then_facts.iter().any(|proved| {
                        store_has_set_inference(&proved.store_and_infer)
                            || verify_has_set_inference(&proved.verify_result)
                    })
            }
            VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) => {
                domains_have_set_inference(&proof.well_defined.assumed_dom_facts)
            }
            VerifyForallFactResult::Success(VerifyForallFactProof::ByEmptyParameterDomain(
                proof,
            )) => domains_have_set_inference(&proof.well_defined.assumed_dom_facts),
            _ => false,
        },
        VerifyFactResult::AndFact(proof) => {
            matches!(proof.as_ref(), VerifyAndFactResult::Success(proof) if proof.components.iter().any(verify_has_set_inference))
        }
        VerifyFactResult::ChainFact(proof) => {
            matches!(proof.as_ref(), VerifyChainFactResult::Success(proof) if proof.adjacent.iter().any(verify_has_set_inference))
        }
        _ => false,
    }
}

fn statement_has_set_inference(statement: &ExecStmtResult) -> bool {
    match statement {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => {
            store_has_set_inference(&proof.store_and_infer_result)
                || verify_has_set_inference(&proof.verify_result)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
        )) => proof
            .store_and_infer_result
            .store_and_infer_results
            .iter()
            .any(|store| store_has_set_inference(store)),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
            ExecDefPropStmtResult::Success(proof),
        )) => {
            proof
                .defined_params
                .store_and_infer_results
                .iter()
                .any(|store| store_has_set_inference(store))
                || domains_have_set_inference(&proof.assumed_iff_facts)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(proof),
        )) => {
            store_has_set_inference(&proof.stored)
                || match &proof.body {
                    ExecDefThmBodyProof::Forall(body) => {
                        domains_have_set_inference(&body.assumed_dom_facts)
                            || body.conclusion_proofs.iter().any(verify_has_set_inference)
                    }
                    ExecDefThmBodyProof::NonForall(body) => {
                        verify_has_set_inference(&body.conclusion_proof)
                    }
                }
        }
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Success(proof),
        )) => {
            store_has_set_inference(&proof.stored)
                || proof
                    .body
                    .conclusion_proofs()
                    .iter()
                    .any(verify_has_set_inference)
                || matches!(&proof.body, crate::execute::execute_proof_block_stmt::ExecClaimBodyProof::Forall(body) if domains_have_set_inference(&body.assumed_dom_facts))
        }
        ExecStmtResult::By(ExecByStmtResult::Induc(ExecByInducStmtResult::Success(proof))) => {
            let (base, step) = match &proof.body {
                ByInducBodySuccess::Unstructured { base, step }
                | ByInducBodySuccess::Structured { base, step } => (base, step),
            };
            proof.goals.iter().any(fact_uses_sets)
                || store_has_set_inference(&proof.goal_domain.store_and_infer)
                || [base, step].iter().any(|case| {
                    domains_have_set_inference(&case.assumptions)
                        || case.proof_steps.iter().any(statement_uses_sets)
                        || case.goals_verified.iter().any(verify_has_set_inference)
                })
                || store_has_set_inference(&proof.stored)
        }
        ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(proof))) => {
            store_has_set_inference(&proof.stored) || verify_has_set_inference(&proof.proof)
        }
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))) => proof
            .type_stores
            .iter()
            .chain(&proof.dom_stores)
            .chain(&proof.returned_conclusions)
            .chain(std::iter::once(&proof.stored))
            .any(store_has_set_inference),
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(proof),
        )) => proof
            .type_stores
            .iter()
            .chain(&proof.dom_stores)
            .chain(&proof.stored)
            .any(store_has_set_inference),
        _ => false,
    }
}
