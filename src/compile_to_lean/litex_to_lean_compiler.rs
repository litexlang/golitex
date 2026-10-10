use super::helper::validate_namespace;
use super::helper::verified_subject;
use super::source_position::{SourceOwner, SourcePosition};
use super::LeanCompileError;
use crate::execute::ExecDefPropStmtResult;
use crate::prelude::*;

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
        let sets = if result.statement_results.iter().any(statement_uses_sets) {
            "\nset_option linter.unusedSectionVars false\nvariable [_setSemantics : Litex.SetSemantics M]"
        } else {
            ""
        };
        let functions = if result
            .statement_results
            .iter()
            .any(statement_uses_functions)
        {
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
        Fact::ForallFact(fact) => {
            fact.dom_facts.iter().any(fact_uses_functions)
                || fact.then_facts.iter().any(|fact| match fact {
                    ExistOrAndChainAtomicFact::AtomicFact(fact) => atomic_fact_args_ref(fact)
                        .into_iter()
                        .any(object_uses_functions),
                    _ => false,
                })
        }
        _ => false,
    }
}

fn statement_uses_functions(statement: &ExecStmtResult) -> bool {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(_)) => true,
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
        Obj::SetFormer(SetFormer::ListSet(_) | SetFormer::SetBuilder(_)) => true,
        Obj::ArithmeticOperator(operator) => match operator {
            ArithmeticOperator::Add(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Sub(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Mul(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Div(x) => object_uses_sets(&x.left) || object_uses_sets(&x.right),
            ArithmeticOperator::Neg(x) => object_uses_sets(&x.arg),
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
                    _ => false,
                })
        }
        _ => false,
    }
}

fn statement_uses_sets(statement: &ExecStmtResult) -> bool {
    match statement {
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
