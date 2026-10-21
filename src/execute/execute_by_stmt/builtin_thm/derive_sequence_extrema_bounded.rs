//! Checked source derivation of bounded extremal existence, scoped to one explicit call.
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::result::*;
use crate::prelude::*;

pub(crate) fn derive_sequence_extrema_bounded(
    rt: &mut Runtime,
    builtin: &Option<BuiltinThmApplication>,
    line: &crate::ast::line_file::SourceLine,
) -> RuntimeResult<Result<TheoremDerivationProof, ExecReleaseThmStmtFailed>> {
    let Some(application) = builtin else {
        return Ok(Ok(TheoremDerivationProof::UserTheorem));
    };
    if let Some(result) = super::derive_real_sequence::derive(rt, application, line)? {
        return Ok(result);
    }
    let upper = match application.theorem {
        BuiltinTheoremId::SequenceLimsupBoundedExists => true,
        BuiltinTheoremId::SequenceLiminfBoundedExists => false,
        _ => return Ok(Ok(TheoremDerivationProof::NativeSchema)),
    };
    // Isolate only parse bindings through the existing transaction API. The caller's
    // local proof environment owns the returned source and application evidence.
    let (result, _discarded_parse_bindings) =
        rt.run_in_temporary_parse_scopes_and_take_scopes(|rt| {
            let prefix = loop {
                let id = rt.fresh_internal_param().id.value();
                let prefix = format!("native_extrema_{id}_");
                if !NAMES
                    .iter()
                    .any(|name| rt.resolve_plain_atom(&format!("{prefix}{name}")).is_ok())
                {
                    break prefix;
                }
            };
            let source = rename_identifiers(SOURCE, &prefix);
            let origin = crate::runtime::CodeSource::Real(
                "<builtin>/sequence_extrema_completeness.lit".into(),
            );
            let blocks = crate::tokenize::Tokenizer::new().tokenize(&source, origin)?;
            let mut derivation_steps = Vec::new();
            let expected_name = format!(
                "{prefix}extrema_bounded_has_{}",
                if upper { "limsup" } else { "liminf" }
            );
            let mut callee = None;
            for block in blocks {
                let statement = rt.parse_token_block(&block)?;
                if let Stmt::Definition(crate::ast::stmt::DefinitionStmt::DefThmStmt(def)) =
                    &statement
                {
                    if def.name == expected_name {
                        callee = Some(def.name.clone());
                    }
                }
                let result = rt.exec_stmt(&statement)?;
                if result.is_failed() {
                    return Ok(Err(ExecReleaseThmStmtFailed::BuiltinShape {
                        theorem: application.theorem,
                        message: format!(
                            "checked completeness derivation failed at {}",
                            statement.readable_string()
                        ),
                    }));
                }
                derivation_steps.push(result);
            }
            let Some(name) = callee else {
                return Ok(Err(ExecReleaseThmStmtFailed::BuiltinShape {
                    theorem: application.theorem,
                    message: "completeness template did not declare its concluding theorem".into(),
                }));
            };
            let stmt =
                Stmt::ReleaseAndExpand(crate::ast::stmt::ReleaseAndExpandStmt::ReleaseThmStmt(
                    crate::ast::stmt::ReleaseThmStmt {
                        call: crate::ast::stmt::TheoremCall {
                            name: crate::ast::names::AtomicName::Plain { name },
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
                    message:
                        "checked completeness theorem could not be applied to the supplied operands"
                            .into(),
                }));
            }
            let conclusion = rt.verify_fact(
                &application.conclusions[0],
                crate::execute::execute_fact_stmt::VerifyState::top_level(),
            )?;
            if conclusion.is_failed() {
                return Ok(Err(ExecReleaseThmStmtFailed::BuiltinShape {
                    theorem: application.theorem,
                    message:
                        "checked derivation did not establish this extremal existence conclusion"
                            .into(),
                }));
            }
            let completeness = SequenceExtremaCompletenessProof {
                derivation_steps,
                application: Box::new(applied),
                conclusion: Box::new(conclusion),
            };
            Ok(Ok(if upper {
                TheoremDerivationProof::SequenceLimsupBounded(SequenceLimsupBoundedProof {
                    completeness,
                })
            } else {
                TheoremDerivationProof::SequenceLiminfBounded(SequenceLiminfBoundedProof {
                    completeness,
                })
            }))
        })?;
    Ok(result)
}

const SOURCE: &str = include_str!("sequence_extrema_completeness.lit");
const NAMES: &[&str] = &[
    "B",
    "L",
    "M",
    "a",
    "answer",
    "b",
    "chosen",
    "cutoff",
    "epsilon",
    "extrema_bounded",
    "extrema_bounded_has_liminf",
    "extrema_bounded_has_limsup",
    "extrema_bounded_tail_lub",
    "extrema_decreasing",
    "extrema_decreasing_converges",
    "extrema_lower_bounded_tail_glb",
    "extrema_sup_sequence",
    "extrema_sup_sequence_decreases",
    "extrema_sup_sequence_lower_bound",
    "extrema_tail_glb",
    "extrema_tail_glb_crosses",
    "extrema_tail_lower",
    "extrema_tail_lub",
    "extrema_tail_lub_crosses",
    "extrema_tail_lub_unique",
    "extrema_tail_sup",
    "extrema_tail_upper",
    "extrema_tail_value",
    "j",
    "k",
    "m",
    "n",
    "n0",
    "n1",
    "s",
    "tail_range",
    "u",
    "v",
    "x",
    "y",
];

// Token-wise alpha renaming of this fixed proof template, never interpolation of
// user expressions. Actual arguments remain typed ASTs in TheoremCall above.
fn rename_identifiers(source: &str, prefix: &str) -> String {
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
            word.push(c);
        } else {
            flush(&mut result, &mut word);
            result.push(c);
        }
    }
    flush(&mut result, &mut word);
    result
}
