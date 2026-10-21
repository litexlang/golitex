//! Explicit source-checked real sequence theorems. WD never calls this engine.
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::result::*;
use crate::prelude::*;
pub(super) fn derive(
    rt: &mut Runtime,
    application: &BuiltinThmApplication,
    line: &crate::ast::line_file::SourceLine,
) -> RuntimeResult<Option<Result<TheoremDerivationProof, ExecReleaseThmStmtFailed>>> {
    use BuiltinTheoremId::*;
    let theorem = match application.theorem {
        SequenceMonotoneBoundedAbove => "analysis_monotone_bounded_above",
        SequenceMonotoneBoundedBelow => "analysis_monotone_bounded_below",
        SequenceCauchyBounded => "analysis_cauchy_bounded",
        SequenceCauchyConvergent => "analysis_cauchy_convergent",
        SequenceConvergentBounded => "analysis_convergent_bounded",
        _ => return Ok(None),
    };
    let (result, _) = rt.run_in_temporary_parse_scopes_and_take_scopes(|rt| {
        let prefix = loop {
            let prefix = format!(
                "native_real_sequence_{}_",
                rt.fresh_internal_param().id.value()
            );
            if !NAMES
                .iter()
                .any(|name| rt.resolve_plain_atom(&format!("{prefix}{name}")).is_ok())
            {
                break prefix;
            }
        };
        let source = rename(SOURCE, &prefix);
        let origin =
            crate::runtime::CodeSource::Real("<builtin>/real_sequence_completeness.lit".into());
        let blocks = crate::tokenize::Tokenizer::new().tokenize(&source, origin)?;
        let mut steps = Vec::new();
        let mut callee = None;
        let expected = format!("{prefix}{theorem}");
        for block in blocks {
            let stmt = rt.parse_token_block(&block)?;
            if let Stmt::Definition(crate::ast::stmt::DefinitionStmt::DefThmStmt(def)) = &stmt {
                if def.name == expected {
                    callee = Some(def.name.clone());
                }
            }
            let result = rt.exec_stmt(&stmt)?;
            if result.is_failed() {
                return Ok(Err(ExecReleaseThmStmtFailed::BuiltinShape {
                    theorem: application.theorem,
                    message: format!(
                        "checked real sequence derivation failed at {}",
                        stmt.readable_string()
                    ),
                }));
            }
            steps.push(result);
        }
        let Some(name) = callee else {
            return Ok(Err(ExecReleaseThmStmtFailed::BuiltinShape {
                theorem: application.theorem,
                message: "source did not define the requested theorem".into(),
            }));
        };
        let stmt = Stmt::ReleaseAndExpand(crate::ast::stmt::ReleaseAndExpandStmt::ReleaseThmStmt(
            crate::ast::stmt::ReleaseThmStmt {
                call: crate::ast::stmt::TheoremCall {
                    name: AtomicName::plain(name),
                    arguments: crate::ast::stmt::TheoremCallArguments::Parenthesized(
                        application.arguments.clone(),
                    ),
                },
                line_file: line.clone(),
            },
        ));
        let applied = rt.exec_stmt(&stmt)?;
        if applied.is_failed() {
            return Ok(Err(ExecReleaseThmStmtFailed::BuiltinShape {
                theorem: application.theorem,
                message: "source theorem application failed".into(),
            }));
        }
        let conclusion = rt.verify_fact(&application.conclusions[0], VerifyState::top_level())?;
        if conclusion.is_failed() {
            return Ok(Err(ExecReleaseThmStmtFailed::BuiltinShape {
                theorem: application.theorem,
                message: "source theorem did not prove the actual conclusion".into(),
            }));
        }
        let completeness = RealSequenceCompletenessProof {
            derivation_steps: steps,
            application: Box::new(applied),
            conclusion: Box::new(conclusion),
        };
        Ok(Ok(match application.theorem {
            SequenceMonotoneBoundedAbove => TheoremDerivationProof::SequenceMonotoneBoundedAbove(
                SequenceMonotoneBoundedAboveProof { completeness },
            ),
            SequenceMonotoneBoundedBelow => TheoremDerivationProof::SequenceMonotoneBoundedBelow(
                SequenceMonotoneBoundedBelowProof { completeness },
            ),
            SequenceCauchyBounded => {
                TheoremDerivationProof::SequenceCauchyBounded(SequenceCauchyBoundedProof {
                    completeness,
                })
            }
            SequenceCauchyConvergent => {
                TheoremDerivationProof::SequenceCauchyConvergent(SequenceCauchyConvergentProof {
                    completeness,
                })
            }
            SequenceConvergentBounded => {
                TheoremDerivationProof::SequenceConvergentBounded(SequenceConvergentBoundedProof {
                    completeness,
                })
            }
            _ => unreachable!(),
        }))
    })?;
    Ok(Some(result))
}
const SOURCE: &str = include_str!("real_sequence_completeness.lit");
const NAMES: &[&str] = &[
    "analysis_nondecreasing_converges",
    "analysis_nonincreasing_converges",
    "analysis_cauchy_bounded",
    "analysis_cauchy_limsup_limit",
    "analysis_cauchy_complete",
    "analysis_monotone_bounded_above",
    "analysis_monotone_bounded_below",
    "analysis_convergent_bounded",
    "analysis_cauchy_convergent",
    "a",
    "L",
    "M",
    "B",
    "N0",
    "U0",
    "prefix",
    "prefix_max",
    "epsilon",
    "cutoff",
    "m",
    "n",
    "k",
    "n1",
    "x",
    "v",
    "p",
    "value",
    "lower",
    "upper",
];
// Fixed template identifiers only. User operands remain typed AST arguments.
fn rename(source: &str, prefix: &str) -> String {
    let mut result = String::new();
    let mut word = String::new();
    let flush = |result: &mut String, word: &mut String| {
        if NAMES.contains(&word.as_str()) {
            result.push_str(prefix);
        }
        result.push_str(word);
        word.clear();
    };
    for c in source.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            word.push(c)
        } else {
            flush(&mut result, &mut word);
            result.push(c);
        }
    }
    flush(&mut result, &mut word);
    result
}
