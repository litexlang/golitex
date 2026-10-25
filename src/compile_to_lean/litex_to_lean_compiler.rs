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
use crate::execute::execute_proof_block_stmt::{
    ExecClaimStmtResult, ExecProofBlockStmtResult, ExecSketchStmtResult,
};
use crate::execute::execute_witness_stmt::{
    ExecWitnessAtomicFactStmtResult, ExecWitnessExistFactStmtResult, ExecWitnessStmtResult,
};
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
        let indexed_unions = if result.statement_results.iter().any(|statement|
            statement_uses_choice(statement) || super::compile_replacement_result::replacement_statement(statement).is_some() || matches!(statement, ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
                crate::execute::ExecDefStructStmtResult::Success(p)))
                if super::compile_def_struct_stmt_result::has_dependent_fields(&p.statement))) {
            "\nvariable [_indexedUnionSemantics : Litex.IndexedUnionSemantics M]"
        } else { "" };
        let regularity = if result
            .statement_results
            .iter()
            .any(statement_uses_regularity)
        {
            "\nvariable [_regularitySemantics : Litex.RegularitySemantics M]"
        } else {
            ""
        };
        let output = format!("import Litex\n\nset_option linter.unusedVariables false\n\nnamespace LitexCompiled.{artifact_namespace}\n\nuniverse {universes}\nvariable {{M : Litex.Semantics.{{u}}}}{sets}{functions}{indexed_unions}{regularity}\n\n{}\nend LitexCompiled.{artifact_namespace}\n", declarations.join("\n\n"));
        Ok(output
            .lines()
            .map(str::trim_end)
            .collect::<Vec<_>>()
            .join("\n")
            + "\n")
    }
}

fn object_uses_functions(object: &Obj) -> bool {
    match object {
        Obj::IteratedOperator(_) => true,
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(p)) => object_uses_functions(&p.set),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(p)) => object_uses_functions(&p.set),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(p)) => object_uses_functions(&p.set),

        Obj::IntegerOperator(IntegerOperator::Factorial(p)) => object_uses_functions(&p.arg),
        Obj::IntegerOperator(IntegerOperator::Gcd(p)) => {
            object_uses_functions(&p.left) || object_uses_functions(&p.right)
        }
        Obj::IntegerOperator(IntegerOperator::Lcm(p)) => {
            object_uses_functions(&p.left) || object_uses_functions(&p.right)
        }
        Obj::IntegerOperator(IntegerOperator::Mod(p)) => {
            object_uses_functions(&p.left) || object_uses_functions(&p.right)
        }
        Obj::IntegerOperator(IntegerOperator::Quot(p)) => {
            object_uses_functions(&p.left) || object_uses_functions(&p.right)
        }
        Obj::FnObj(_)
        | Obj::FunctionSpace(_)
        | Obj::ProductShape(_)
        | Obj::StructAndFieldAccessObj(_) => true,
        Obj::SetFormer(SetFormer::ListSet(set)) => {
            set.list.iter().any(|item| object_uses_functions(item))
        }
        Obj::SetFormer(SetFormer::SetBuilder(set)) => {
            object_uses_functions(&set.param_set)
                || set.facts.iter().any(|fact| {
                    fact_uses_functions(&crate::instantiate::quantifier_free_fact_to_fact(
                        fact.clone(),
                    ))
                })
        }
        Obj::SetFormer(SetFormer::Range(r)) => {
            object_uses_functions(&r.start) || object_uses_functions(&r.end)
        }
        Obj::SetFormer(SetFormer::ClosedRange(r)) => {
            object_uses_functions(&r.start) || object_uses_functions(&r.end)
        }
        Obj::SetFormer(SetFormer::FiniteSeqSet(_) | SetFormer::SeqSet(_)) => true,
        Obj::SetOperator(SetOperator::PowerSet(set)) => object_uses_functions(&set.set),
        Obj::SetOperator(SetOperator::SetMinus(set)) => {
            object_uses_functions(&set.left) || object_uses_functions(&set.right)
        }
        Obj::SetOperator(SetOperator::Intersect(set)) => {
            object_uses_functions(&set.left) || object_uses_functions(&set.right)
        }
        Obj::SetOperator(SetOperator::Union(set)) => {
            object_uses_functions(&set.left) || object_uses_functions(&set.right)
        }
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
            ArithmeticOperator::Min(x) => {
                object_uses_functions(&x.left) || object_uses_functions(&x.right)
            }
            ArithmeticOperator::Sign(x) => object_uses_functions(&x.arg),
            ArithmeticOperator::Floor(x) => object_uses_functions(&x.arg),
            ArithmeticOperator::Ceil(x) => object_uses_functions(&x.arg),
            ArithmeticOperator::Max(x) => {
                object_uses_functions(&x.left) || object_uses_functions(&x.right)
            }
            ArithmeticOperator::Pow(x) => {
                object_uses_functions(&x.base) || object_uses_functions(&x.exponent)
            }
        },
        _ => false,
    }
}

fn fact_uses_functions(fact: &Fact) -> bool {
    // Multi-variable uniqueness is checked as equality of complete tuples,
    // including when no tuple constructor occurs in the user's body clauses.
    if let Fact::ExistUniqueFact(source) = fact {
        if source.typed_parameters.ordered_param_ids().len() > 1 {
            return true;
        }
    }
    match fact {
        Fact::NotForall(fact) => {
            fact.typed_parameters.groups.iter().any(|g| matches!(&g.param_type, ParamType::Obj(o) if object_uses_functions(o)))
                || fact.dom_facts.iter().chain(&fact.then_facts).any(|f|
                    fact_uses_functions(&crate::instantiate::quantifier_free_fact_to_fact(f.clone())))
        }
        Fact::ForallFactWithIff(fact) => {
            fact_uses_functions(&Fact::ForallFact(fact.forall_fact.clone()))
                || fact.iff_facts.iter().any(|clause| fact_uses_functions(&clause.clone().into()))
        }
        Fact::AtomicFact(fact) => crate::compile_to_lean::compile_mapping_properties::mapping_parts(fact).is_some() || atomic_fact_args_ref(fact)
            .into_iter()
            .any(object_uses_functions),
        Fact::AndFact(fact) => fact.facts.iter().any(|fact| {
            crate::compile_to_lean::compile_mapping_properties::mapping_parts(fact).is_some() || atomic_fact_args_ref(fact)
                .into_iter()
                .any(object_uses_functions)
        }),
        Fact::ChainFact(fact) => fact.objs.iter().any(object_uses_functions),
        Fact::OrFact(fact) => fact
            .facts
            .iter()
            .any(|branch| fact_uses_functions(&crate::ast::fact::and_chain_as_fact(branch))),
        Fact::ExistFact(fact) | Fact::ExistUniqueFact(fact) | Fact::NotExistFact(fact) => {
            fact.typed_parameters.groups.iter().any(|group| {
                matches!(&group.param_type, ParamType::Obj(carrier) if object_uses_functions(carrier))
            }) || fact.facts.iter().any(|clause| {
                fact_uses_functions(&crate::instantiate::quantifier_free_fact_to_fact(clause.clone()))
            })
        }
        Fact::ForallFact(fact) => {
            fact.typed_parameters.groups.iter().any(|group| {
                matches!(&group.param_type, ParamType::Obj(carrier) if object_uses_functions(carrier))
            }) || fact.dom_facts.iter().any(fact_uses_functions)
                || fact.then_facts.iter().any(|fact| match fact {
                    ExistOrAndChainAtomicFact::AtomicFact(fact) => crate::compile_to_lean::compile_mapping_properties::mapping_parts(fact).is_some() || atomic_fact_args_ref(fact)
                        .into_iter()
                        .any(object_uses_functions),
                    ExistOrAndChainAtomicFact::AndFact(fact) => fact.facts.iter().any(|fact| {
                        crate::compile_to_lean::compile_mapping_properties::mapping_parts(fact).is_some() || atomic_fact_args_ref(fact)
                            .into_iter()
                            .any(object_uses_functions)
                    }),
                    ExistOrAndChainAtomicFact::ChainFact(fact) => {
                        fact.objs.iter().any(object_uses_functions)
                    }
                    ExistOrAndChainAtomicFact::OrFact(fact) => {
                        fact_uses_functions(&Fact::OrFact(fact.clone()))
                    }
                    ExistOrAndChainAtomicFact::ExistUniqueFact(fact) => {
                        fact_uses_functions(&Fact::ExistUniqueFact(fact.clone()))
                    }
                    ExistOrAndChainAtomicFact::ExistFact(fact)
                    | ExistOrAndChainAtomicFact::NotExistFact(fact) => {
                        fact_uses_functions(&Fact::ExistFact(fact.clone()))
                    }
                })
        }
    }
}

fn statement_uses_functions(statement: &ExecStmtResult) -> bool {
    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        crate::execute::ExecDefTemplateStmtResult::Success(p),
    )) = statement
    {
        return statement_uses_functions(&p.body);
    }
    if statement_uses_choice(statement) {
        return true;
    }
    if let Some((_, assignments, store)) = super::source_position::enumeration_statement(statement)
    {
        if let StoreFactResult::ForallFact(f) = &store.store {
            if fact_uses_functions(&Fact::ForallFact(f.fact.clone())) {
                return true;
            }
        }
        return assignments.iter().any(|p| match &p.outcome {
            crate::execute::execute_by_stmt::EnumerateAssignmentOutcome::Proved {
                proof_steps,
                ..
            } => proof_steps.iter().any(statement_uses_functions),
            _ => false,
        });
    }
    match statement {
        ExecStmtResult::Trust(_) | ExecStmtResult::Definition(ExecDefinitionStmtResult::Axiom(_)) =>
            super::compile_assumption_stmt_result::assumption_stages(statement).iter().any(|(fact, _, _store)| fact_uses_functions(fact)),

        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(_)) => true,
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ExpandRange(crate::execute::execute_by_stmt::ExecExpandRangeStmtResult::Success(p))) => verified_subject(&p.membership).as_ref().is_some_and(fact_uses_functions),
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(ExecSketchStmtResult::Success(p))) => p.proof_steps.iter().any(statement_uses_functions),
        ExecStmtResult::By(ExecByStmtResult::FnExtension(_)) => true,
        ExecStmtResult::By(ExecByStmtResult::Extension(crate::execute::execute_by_stmt::ExecByExtensionStmtResult::Success(proof))) => {
            verified_subject(&proof.left_to_right).as_ref().is_some_and(fact_uses_functions)
                || proof.proof_steps.iter().any(statement_uses_functions)
        }
        ExecStmtResult::Register(result) =>
            super::compile_register_stmt_result::registration_proof(result).ok()
                .and_then(verified_subject).as_ref().is_some_and(fact_uses_functions),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjByExistFacts(crate::execute::ExecHaveObjByExistFactsStmtResult::Success(p)),
        )) => fact_uses_functions(&crate::ast::fact::exist_shaped_fact_to_fact(&p.verify_exist.fact)),

        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessNonemptySet(crate::execute::execute_witness_stmt::ExecWitnessNonemptySetStmtResult::Success(p))) =>
            object_uses_functions(&p.statement.set) || object_uses_functions(&p.statement.obj) || p.proof_steps.iter().any(statement_uses_functions),
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))) =>
            verified_subject(&proof.selected_proof).as_ref().is_some_and(fact_uses_functions)
                || proof.builtin.as_ref().is_some_and(|b| b.conclusions.iter().any(fact_uses_functions)),
        ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::Thm(
            crate::execute::execute_by_stmt::ExecReleaseThmStmtResult::Success(proof))) =>
            proof.builtin.as_ref().is_some_and(|b| b.conclusions.iter().any(fact_uses_functions)),
        ExecStmtResult::By(ExecByStmtResult::Contra(crate::execute::execute_by_stmt::ExecByContraStmtResult::Success(proof))) => {
            fact_uses_functions(&proof.goal)
                || fact_uses_functions(&proof.reverse_assumption)
                || proof.proof_steps.iter().any(statement_uses_functions)
                || verified_subject(&proof.closing.impossible).as_ref().is_some_and(fact_uses_functions)
                || verified_subject(&proof.closing.negated_impossible).as_ref().is_some_and(fact_uses_functions)
        }

        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromAtomicFact(crate::execute::ExecObtainObjFromAtomicFactStmtResult::Success(proof)),
        )) => fact_uses_functions(&crate::ast::fact::exist_shaped_fact_to_fact(&proof.projected_exist))
            || proof.statement.fact.body.iter().any(object_uses_functions),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromExistFact(crate::execute::ExecObtainObjFromExistFactStmtResult::Success(proof)),
        )) => fact_uses_functions(&crate::ast::fact::exist_shaped_fact_to_fact(&proof.statement.fact)),
        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessAtomicFact(ExecWitnessAtomicFactStmtResult::Success(proof))) => {
            fact_uses_functions(&crate::ast::fact::exist_shaped_fact_to_fact(&proof.projected_exist))
                || proof.statement.witnesses.iter().any(object_uses_functions)
                || proof.proof_steps.iter().any(statement_uses_functions)
        }
        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(ExecWitnessExistFactStmtResult::Success(proof))) => {
            fact_uses_functions(&crate::ast::fact::exist_shaped_fact_to_fact(&proof.statement.exist_shaped_fact_in_witness))
                || proof.statement.equal_tos.iter().any(object_uses_functions)
                || proof.proof_steps.iter().any(statement_uses_functions)
        }

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
            ExecDefinitionStmtResult::HaveFnEqual(_) | ExecDefinitionStmtResult::HaveFnEqualCaseByCase(_) | ExecDefinitionStmtResult::HaveFnByInduc(_)
            | ExecDefinitionStmtResult::HaveFnByForallExistUnique(_),
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
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(proof),
            ),
        )) => proof.statement.param_def.groups.iter().any(|group| {
            matches!(&group.param_type, ParamType::Obj(carrier) if object_uses_functions(carrier))
        }),
        _ => false,
    }
}

fn object_uses_sets(object: &Obj) -> bool {
    match object {
        // Native constants have intrinsic R+ membership; source WD may use that
        // proof even when the enclosing source proposition mentions only R/C.
        Obj::Literal(Literal::EulerNumber(_) | Literal::Pi(_)) => true,
        Obj::ComplexOperator(ComplexOperator::Conjugate(p)) => object_uses_sets(&p.arg),
        Obj::ComplexOperator(ComplexOperator::RealPart(p)) => object_uses_sets(&p.arg),
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(p)) => object_uses_sets(&p.arg),
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(p)) => object_uses_sets(&p.arg),
        Obj::TrigOperator(TrigOperator::Sin(p)) => object_uses_sets(&p.arg),
        Obj::TrigOperator(TrigOperator::Cos(p)) => object_uses_sets(&p.arg),
        Obj::TrigOperator(TrigOperator::Tan(p)) => object_uses_sets(&p.arg),
        Obj::ExpLogOperator(ExpLogOperator::Exp(p)) => object_uses_sets(&p.arg),
        Obj::ExpLogOperator(ExpLogOperator::Log(p)) => {
            object_uses_sets(&p.base) || object_uses_sets(&p.arg)
        }
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(p)) => object_uses_sets(&p.arg),
        Obj::ExpLogOperator(ExpLogOperator::Ln(_)) => true,
        Obj::IteratedOperator(_) => true,
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(p)) => object_uses_sets(&p.set),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(p)) => object_uses_sets(&p.set),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(p)) => object_uses_sets(&p.set),
        Obj::IntegerOperator(IntegerOperator::Factorial(_)) => true, // Intrinsic codomain is N+.
        Obj::IntegerOperator(IntegerOperator::Gcd(_)) => true,       // Intrinsic codomain is N+.
        Obj::IntegerOperator(IntegerOperator::Lcm(p)) => {
            object_uses_sets(&p.left) || object_uses_sets(&p.right)
        }
        Obj::IntegerOperator(IntegerOperator::Mod(p)) => {
            object_uses_sets(&p.left) || object_uses_sets(&p.right)
        }
        Obj::IntegerOperator(IntegerOperator::Quot(_)) => true,
        Obj::StandardSet(set)
            if !matches!(
                set,
                StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C
            ) =>
        {
            true
        }
        Obj::SetFormer(
            SetFormer::ListSet(_)
            | SetFormer::SetBuilder(_)
            | SetFormer::Range(_)
            | SetFormer::ClosedRange(_)
            | SetFormer::IntervalObj(_)
            | SetFormer::OneSideInfinityIntervalObj(_),
        ) => true,
        Obj::SetOperator(
            SetOperator::Union(_)
            | SetOperator::Intersect(_)
            | SetOperator::SetMinus(_)
            | SetOperator::PowerSet(_),
        ) => true,
        Obj::ArithmeticOperator(operator) => match operator {
            ArithmeticOperator::Add(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Sub(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Mul(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Div(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Min(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Sign(x) => object_uses_sets(&x.arg),
            ArithmeticOperator::Floor(x) => object_uses_sets(&x.arg),
            ArithmeticOperator::Ceil(x) => object_uses_sets(&x.arg),
            ArithmeticOperator::Max(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Neg(x) => object_uses_sets(&x.arg),
            ArithmeticOperator::Abs(x) => object_uses_sets(&x.arg),
            ArithmeticOperator::Pow(x) => {
                object_uses_sets(&x.base) || object_uses_sets(&x.exponent)
            }
        },
        _ => false,
    }
}

fn fact_uses_sets(fact: &Fact) -> bool {
    match fact {
        Fact::NotForall(fact) => {
            fact.typed_parameters.groups.iter().any(|g| matches!(&g.param_type, ParamType::Obj(o) if object_uses_sets(o)))
                || fact.dom_facts.iter().chain(&fact.then_facts).any(|f|
                    fact_uses_sets(&crate::instantiate::quantifier_free_fact_to_fact(f.clone())))
        }
        Fact::ForallFactWithIff(fact) => {
            fact_uses_sets(&Fact::ForallFact(fact.forall_fact.clone()))
                || fact.iff_facts.iter().any(|clause| fact_uses_sets(&clause.clone().into()))
        }
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
        Fact::ExistFact(fact) | Fact::ExistUniqueFact(fact) | Fact::NotExistFact(fact) => {
            fact.typed_parameters.groups.iter().any(|group| {
                matches!(&group.param_type, ParamType::Obj(carrier) if object_uses_sets(carrier))
            }) || fact.facts.iter().any(|clause| {
                fact_uses_sets(&crate::instantiate::quantifier_free_fact_to_fact(clause.clone()))
            })
        }
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
                    ExistOrAndChainAtomicFact::ExistFact(fact)
                    | ExistOrAndChainAtomicFact::ExistUniqueFact(fact)
                    | ExistOrAndChainAtomicFact::NotExistFact(fact) => {
                        fact_uses_sets(&Fact::ExistFact(fact.clone()))
                    }
                })
        }
    }
}

fn statement_uses_sets(statement: &ExecStmtResult) -> bool {
    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        crate::execute::ExecDefTemplateStmtResult::Success(p),
    )) = statement
    {
        return statement_uses_sets(&p.body);
    }
    if statement_has_set_inference(statement) {
        return true;
    }
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(ExecDefineObjStmtResult::HaveByReplacementAxiom(_))) => true,

        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::RegularityAxiom(_) | ExecReleaseAndExpandStmtResult::ZornLemma(_)) => true,

        ExecStmtResult::Trust(_) | ExecStmtResult::Definition(ExecDefinitionStmtResult::Axiom(_)) =>
            super::compile_assumption_stmt_result::assumption_stages(statement).iter().any(|(fact, _, store)| fact_uses_sets(fact) || store_has_set_inference(store)),

        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ExpandRange(crate::execute::execute_by_stmt::ExecExpandRangeStmtResult::Success(_))) => true,
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(ExecSketchStmtResult::Success(p))) => p.proof_steps.iter().any(statement_uses_sets),
        ExecStmtResult::By(ExecByStmtResult::Extension(_) | ExecByStmtResult::FnExtension(_) | ExecByStmtResult::For(_) | ExecByStmtResult::EnumerateFiniteSet(_)) => true,
        ExecStmtResult::Register(result) =>
            super::compile_register_stmt_result::registration_proof(result).ok()
                .and_then(verified_subject).as_ref().is_some_and(fact_uses_sets),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjByExistFacts(crate::execute::ExecHaveObjByExistFactsStmtResult::Success(p)),
        )) => fact_uses_sets(&crate::ast::fact::exist_shaped_fact_to_fact(&p.verify_exist.fact)),

        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessNonemptySet(crate::execute::execute_witness_stmt::ExecWitnessNonemptySetStmtResult::Success(p))) =>
            object_uses_sets(&p.statement.set) || object_uses_sets(&p.statement.obj) || p.proof_steps.iter().any(statement_uses_sets),
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))) => {
            proof.builtin.as_ref().is_some_and(|b| b.conclusions.iter().any(fact_uses_sets))
                || verified_subject(&proof.selected_proof).as_ref().is_some_and(fact_uses_sets)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(proof),
        )) => proof.builtin.as_ref().is_some_and(|b| b.conclusions.iter().any(fact_uses_sets)),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(proof),
            ),
        )) => proof.statement.param_def.groups.iter().any(|group| {
            matches!(&group.param_type, ParamType::Obj(carrier) if object_uses_sets(carrier))
        }),
        ExecStmtResult::By(ExecByStmtResult::Contra(
            crate::execute::execute_by_stmt::ExecByContraStmtResult::Success(proof),
        )) => {
            fact_uses_sets(&proof.goal)
                || fact_uses_sets(&proof.reverse_assumption)
                || store_has_set_inference(&proof.negation_assumed)
                || proof.proof_steps.iter().any(statement_uses_sets)
                || verify_has_set_inference(&proof.closing.impossible)
                || verify_has_set_inference(&proof.closing.negated_impossible)
                || verified_subject(&proof.closing.impossible).as_ref().is_some_and(fact_uses_sets)
                || verified_subject(&proof.closing.negated_impossible).as_ref().is_some_and(fact_uses_sets)
                || store_has_set_inference(&proof.stored)
        }

        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                crate::execute::ExecObtainObjFromAtomicFactStmtResult::Success(proof),
            ),
        )) => {
            fact_uses_sets(&crate::ast::fact::exist_shaped_fact_to_fact(
                &proof.projected_exist,
            )) || proof
                .store_and_infer_result
                .store_and_infer_results
                .iter()
                .any(|store| store_has_set_inference(store))
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromExistFact(
                crate::execute::ExecObtainObjFromExistFactStmtResult::Success(proof),
            ),
        )) => {
            fact_uses_sets(&crate::ast::fact::exist_shaped_fact_to_fact(
                &proof.statement.fact,
            )) || proof
                .store_and_infer_result
                .store_and_infer_results
                .iter()
                .any(|store| store_has_set_inference(store))
        }
        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessAtomicFact(
            ExecWitnessAtomicFactStmtResult::Success(proof),
        )) => {
            fact_uses_sets(&crate::ast::fact::exist_shaped_fact_to_fact(
                &proof.projected_exist,
            )) || proof.statement.witnesses.iter().any(object_uses_sets)
                || proof.proof_steps.iter().any(statement_uses_sets)
        }
        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
            ExecWitnessExistFactStmtResult::Success(proof),
        )) => {
            fact_uses_sets(&crate::ast::fact::exist_shaped_fact_to_fact(
                &proof.statement.exist_shaped_fact_in_witness,
            )) || proof.statement.equal_tos.iter().any(object_uses_sets)
                || proof.proof_steps.iter().any(statement_uses_sets)
        }

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
        VerifyFactResult::ForallFactWithIff(result) => match result.as_ref() {
            VerifyForallFactWithIffResult::Success(proof) => {
                verify_has_set_inference(&proof.then_implies_iff)
                    || verify_has_set_inference(&proof.iff_implies_then)
            }
            _ => false,
        },
        VerifyFactResult::AtomicExceptEquality(proof) => matches!(proof.as_ref(),
            VerifyAtomicExceptEqualityFactResult::Success(proof) if matches!(&proof.searched_proof,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowSharedExponentLessEqual(_)))),
        VerifyFactResult::Equality(proof) => matches!(proof.as_ref(),
            VerifyEqualityResult::Success(proof) if matches!(&proof.searched_proof,
                EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
                    crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::ElementaryArithmeticProof::PositivePowerZero { .. },
                ))
            )
        ),
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
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(
            ExecSketchStmtResult::Success(p),
        )) => p.proof_steps.iter().any(statement_has_set_inference),
        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessAtomicFact(
            ExecWitnessAtomicFactStmtResult::Success(proof),
        )) => {
            proof
                .prop_argument_type_checks
                .iter()
                .any(verify_has_set_inference)
                || proof
                    .introduced_params
                    .defined_params
                    .store_and_infer_results
                    .iter()
                    .any(|store| store_has_set_inference(store))
                || proof.witness_equalities.iter().any(store_has_set_inference)
                || proof
                    .obligations
                    .body_checks
                    .iter()
                    .any(verify_has_set_inference)
                || store_has_set_inference(&proof.store_and_infer_result)
        }
        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
            ExecWitnessExistFactStmtResult::Success(proof),
        )) => {
            proof
                .introduced_params
                .defined_params
                .store_and_infer_results
                .iter()
                .any(|store| store_has_set_inference(store))
                || proof.witness_equalities.iter().any(store_has_set_inference)
                || proof
                    .obligations
                    .body_checks
                    .iter()
                    .any(verify_has_set_inference)
                || store_has_set_inference(&proof.store_and_infer_result)
        }

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
        ExecStmtResult::By(ExecByStmtResult::StrongInduc(
            crate::execute::execute_by_stmt::ExecByStrongInducStmtResult::Success(proof),
        )) => {
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

fn statement_uses_regularity(statement: &ExecStmtResult) -> bool {
    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        crate::execute::ExecDefTemplateStmtResult::Success(p),
    )) = statement
    {
        return statement_uses_regularity(&p.body);
    }
    if super::compile_release_regularity_result::regularity_statement(statement).is_some() {
        return true;
    }
    let steps = match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) => match &p.body {
            ExecDefThmBodyProof::Forall(b) => &b.proof_steps,
            ExecDefThmBodyProof::NonForall(b) => &b.proof_steps,
        },
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(
            ExecSketchStmtResult::Success(p),
        )) => &p.proof_steps,
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            crate::execute::execute_proof_block_stmt::ExecClaimStmtResult::Success(p),
        )) => p.body.proof_steps(),
        _ => return false,
    };
    steps.iter().any(statement_uses_regularity)
}

fn statement_uses_choice(statement: &ExecStmtResult) -> bool {
    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        crate::execute::ExecDefTemplateStmtResult::Success(p),
    )) = statement
    {
        return statement_uses_choice(&p.body);
    }
    if super::compile_release_choice_result::choice_statement(statement).is_some() {
        return true;
    }
    let steps = match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) => match &p.body {
            ExecDefThmBodyProof::Forall(b) => &b.proof_steps,
            ExecDefThmBodyProof::NonForall(b) => &b.proof_steps,
        },
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(
            ExecSketchStmtResult::Success(p),
        )) => &p.proof_steps,
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            crate::execute::execute_proof_block_stmt::ExecClaimStmtResult::Success(p),
        )) => p.body.proof_steps(),
        _ => return false,
    };
    steps.iter().any(statement_uses_choice)
}
