//! Check real parsed statement variants, not fixture names alone.

use litex::ast::fact::Fact;
use litex::ast::stmt::*;
use litex::execute::execute_eval_stmt::{ExecCommandStmtResult, ExecEvalStmtResult};
use litex::execute::ExecStmtResult;
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::runtime::Runtime;
use litex::tokenize::Tokenizer;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

#[test]
fn statement_fixtures_cover_actual_ast_leaves_and_nested_bodies() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(check_fixtures)
        .unwrap()
        .join()
        .unwrap();
}

fn check_fixtures() {
    let suite = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/test_statements");
    let mut paths = fs::read_dir(&suite)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "lit"))
        .collect::<Vec<_>>();
    paths.sort();
    assert_eq!(
        paths.len(),
        50,
        "update the explicit inventory when Stmt changes"
    );
    let mut all = BTreeSet::new();
    let mut evaluated = Vec::new();
    for path in paths {
        let source = fs::read_to_string(&path).unwrap();
        let target = source
            .lines()
            .find_map(|line| line.strip_prefix("# Stmt: "))
            .unwrap();
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: false,
            language: OutputLanguage::English,
        });
        let blocks = Tokenizer::new()
            .tokenize(&source, runtime.current_file.clone())
            .unwrap();
        let mut seen = BTreeSet::new();
        for block in blocks {
            let statements = runtime
                .parse(&[block])
                .unwrap_or_else(|error| panic!("{}: parse failed: {error:?}", path.display()));
            for statement in statements {
                collect_stmt(&statement, &mut seen);
                let result = runtime.exec_stmt(&statement).unwrap_or_else(|error| {
                    panic!("{}: exec_stmt failed: {error:?}", path.display())
                });
                assert!(!result.is_failed(), "{}: {statement:?}", path.display());
                if path.file_name().unwrap() == "eval_stmt.lit" {
                    if let ExecStmtResult::Command(ExecCommandStmtResult::Eval(
                        ExecEvalStmtResult::Success(success),
                    )) = result
                    {
                        evaluated.push(success.evaluated_object.readable_string().replace(' ', ""));
                    }
                }
            }
        }
        assert!(
            seen.contains(target),
            "{} never parses {target}",
            path.display()
        );
        all.extend(seen);
    }
    let templates = all
        .iter()
        .filter(|tag| tag.starts_with("Template."))
        .count();
    assert_eq!(templates, 11, "exercise every TemplateDefEnum body");
    let facts = all.iter().filter(|tag| tag.starts_with("Fact.")).count();
    assert_eq!(facts, 10, "exercise every Fact shape inside Stmt::Fact");
    assert!(all.contains("Induction.NestedCases"));
    assert_eq!(evaluated, ["9", "1/2", "3", "6", "2", "11", "0", "2", "0", "0", "3"]);
}

fn collect_stmt(statement: &Stmt, seen: &mut BTreeSet<String>) {
    let tag = match statement {
        Stmt::Fact(fact) => {
            collect_fact(fact, seen);
            "Fact"
        }
        Stmt::Trust(trust) => match trust {
            TrustBoundaryStmt::TrustStmt(_) => "TrustStmt",
            TrustBoundaryStmt::TrustHaveStmt(_) => "TrustHaveStmt",
        },
        Stmt::Definition(definition) => match definition {
            DefinitionStmt::DefineObj(object) => match object {
                DefineObjStmt::LetObjStmt(_) => "LetObjStmt",
                DefineObjStmt::HaveObjInNonemptySetStmt(_) => "HaveObjInNonemptySetStmt",
                DefineObjStmt::HaveObjEqualStmt(_) => "HaveObjEqualStmt",
                DefineObjStmt::HaveObjByExistFactsStmt(_) => "HaveObjByExistFactsStmt",
                DefineObjStmt::ObtainObjFromExistFact(_) => "ObtainObjFromExistFact",
                DefineObjStmt::ObtainObjFromAtomicFact(_) => "ObtainObjFromAtomicFact",
                DefineObjStmt::HaveByPreimageStmt(_) => "HaveByPreimageStmt",
                DefineObjStmt::HaveByReplacementAxiomStmt(_) => "HaveByReplacementAxiomStmt",
            },
            DefinitionStmt::HaveFnEqualStmt(_) => "HaveFnEqualStmt",
            DefinitionStmt::HaveFnEqualCaseByCaseStmt(_) => "HaveFnEqualCaseByCaseStmt",
            DefinitionStmt::HaveFnByInducStmt(stmt) => {
                collect_induction_cases(&stmt.cases, seen);
                "HaveFnByInducStmt"
            }
            DefinitionStmt::HaveFnByForallExistUniqueStmt(_) => "HaveFnByForallExistUniqueStmt",
            DefinitionStmt::DefPropStmt(_) => "DefPropStmt",
            DefinitionStmt::DefAbstractPropStmt(_) => "DefAbstractPropStmt",
            DefinitionStmt::DefTemplateStmt(stmt) => {
                collect_template(&stmt.template_def_stmt, seen);
                "DefTemplateStmt"
            }
            DefinitionStmt::DefStructStmt(_) => "DefStructStmt",
            DefinitionStmt::DefAlgoByCasesStmt(_) => "DefAlgoByCasesStmt",
            DefinitionStmt::DefAlgoByInducStmt(stmt) => {
                collect_induction_cases(&stmt.cases, seen);
                "DefAlgoByInducStmt"
            }
            DefinitionStmt::DefThmStmt(stmt) => {
                collect_stmts(&stmt.prove_process, seen);
                "DefThmStmt"
            }
            DefinitionStmt::AxiomStmt(_) => "AxiomStmt",
            DefinitionStmt::DefStrategyStmt(stmt) => {
                collect_stmts(&stmt.prove_process, seen);
                "DefStrategyStmt"
            }
        },
        Stmt::ReleaseAndExpand(release) => match release {
            ReleaseAndExpandStmt::ReleaseThmStmt(_) => "ReleaseThmStmt",
            ReleaseAndExpandStmt::ReleaseStructDefStmt(_) => "ReleaseStructDefStmt",
            ReleaseAndExpandStmt::ReleaseObjDefStmt(_) => "ReleaseObjDefStmt",
            ReleaseAndExpandStmt::ExpandRangeStmt(_) => "ExpandRangeStmt",
            ReleaseAndExpandStmt::ReleaseZornLemmaStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "ReleaseZornLemmaStmt"
            }
            ReleaseAndExpandStmt::ReleaseAxiomOfChoiceStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "ReleaseAxiomOfChoiceStmt"
            }
            ReleaseAndExpandStmt::ReleaseRegularityAxiomStmt(_) => "ReleaseRegularityAxiomStmt",
        },
        Stmt::By(by) => match by {
            ByStmt::ByCasesStmt(stmt) => {
                for proof in &stmt.proofs {
                    collect_stmts(proof, seen);
                }
                "ByCasesStmt"
            }
            ByStmt::ByContraStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "ByContraStmt"
            }
            ByStmt::ByEnumerateFiniteSetStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "ByEnumerateFiniteSetStmt"
            }
            ByStmt::ByInducStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                if let Some(proof) = &stmt.base_proof {
                    collect_stmts(proof, seen);
                }
                if let Some(proof) = &stmt.step_proof {
                    collect_stmts(proof, seen);
                }
                "ByInducStmt"
            }
            ByStmt::ByStrongInducStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                if let Some(proof) = &stmt.base_proof {
                    collect_stmts(proof, seen);
                }
                if let Some(proof) = &stmt.step_proof {
                    collect_stmts(proof, seen);
                }
                "ByStrongInducStmt"
            }
            ByStmt::ByForStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "ByForStmt"
            }
            ByStmt::ByExtensionStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "ByExtensionStmt"
            }
            ByStmt::ByFnExtensionStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "ByFnExtensionStmt"
            }
            ByStmt::ByDefStmt(_) => "ByDefStmt",
            ByStmt::ByThmStmt(_) => "ByThmStmt",
        },
        Stmt::Register(register) => match register {
            RegisterStmt::RegisterTransitivePropStmt(_) => "RegisterTransitivePropStmt",
            RegisterStmt::RegisterSymmetricPropStmt(_) => "RegisterSymmetricPropStmt",
            RegisterStmt::RegisterReflexivePropStmt(_) => "RegisterReflexivePropStmt",
        },
        Stmt::Witness(witness) => match witness {
            WitnessStmt::WitnessExistFact(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "WitnessExistFact"
            }
            WitnessStmt::WitnessAtomicFact(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "WitnessAtomicFact"
            }
            WitnessStmt::WitnessNonemptySet(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "WitnessNonemptySet"
            }
        },
        Stmt::ProofBlock(proof) => match proof {
            ProofBlockStmt::ClaimStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "ClaimStmt"
            }
            ProofBlockStmt::SketchStmt(stmt) => {
                collect_stmts(&stmt.proof, seen);
                "SketchStmt"
            }
        },
        Stmt::Command(command) => match command {
            CommandStmt::EvalStmt(_) => "EvalStmt",
        },
    };
    seen.insert(tag.into());
}

fn collect_stmts(statements: &[Stmt], seen: &mut BTreeSet<String>) {
    for statement in statements {
        collect_stmt(statement, seen);
    }
}

fn collect_fact(fact: &Fact, seen: &mut BTreeSet<String>) {
    let tag = match fact {
        Fact::AtomicFact(_) => "AtomicFact",
        Fact::ExistFact(_) => "ExistFact",
        Fact::ExistUniqueFact(_) => "ExistUniqueFact",
        Fact::NotExistFact(_) => "NotExistFact",
        Fact::OrFact(_) => "OrFact",
        Fact::AndFact(_) => "AndFact",
        Fact::ChainFact(_) => "ChainFact",
        Fact::ForallFact(_) => "ForallFact",
        Fact::ForallFactWithIff(_) => "ForallFactWithIff",
        Fact::NotForall(_) => "NotForall",
    };
    seen.insert(format!("Fact.{tag}"));
}

fn collect_template(body: &TemplateDefEnum, seen: &mut BTreeSet<String>) {
    let tag = match body {
        TemplateDefEnum::HaveObjInNonemptySetStmt(_) => "HaveObjInNonemptySetStmt",
        TemplateDefEnum::HaveObjEqualStmt(_) => "HaveObjEqualStmt",
        TemplateDefEnum::HaveObjByExistFactsStmt(_) => "HaveObjByExistFactsStmt",
        TemplateDefEnum::HaveByReplacementAxiomStmt(_) => "HaveByReplacementAxiomStmt",
        TemplateDefEnum::TrustHaveStmt(_) => "TrustHaveStmt",
        TemplateDefEnum::ObtainObjFromExistFact(_) => "ObtainObjFromExistFact",
        TemplateDefEnum::ObtainObjFromAtomicFact(_) => "ObtainObjFromAtomicFact",
        TemplateDefEnum::HaveFnEqualStmt(_) => "HaveFnEqualStmt",
        TemplateDefEnum::HaveFnEqualCaseByCaseStmt(_) => "HaveFnEqualCaseByCaseStmt",
        TemplateDefEnum::HaveFnByInducStmt(_) => "HaveFnByInducStmt",
        TemplateDefEnum::HaveFnByForallExistUniqueStmt(_) => "HaveFnByForallExistUniqueStmt",
    };
    seen.insert(format!("Template.{tag}"));
}

fn collect_induction_cases(cases: &[HaveFnByInducCase], seen: &mut BTreeSet<String>) {
    for case in cases {
        match &case.body {
            HaveFnByInducCaseBody::EqualTo(_) => {
                seen.insert("Induction.EqualTo".into());
            }
            HaveFnByInducCaseBody::NestedCases(nested) => {
                seen.insert("Induction.NestedCases".into());
                collect_induction_cases(nested, seen);
            }
        }
    }
}
