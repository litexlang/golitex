use crate::prelude::*;
fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}
fn check(rt: &mut Runtime, source: &str, wanted: bool) {
    let result = rt.run_litex_code(source).expect("public entry");
    assert!(
        result.session_error.is_none(),
        "{source}: {:?}",
        result.session_error
    );
    assert_eq!(
        result.success,
        wanted,
        "{source}\n{}",
        crate::json_output::project_run_detailed(&result, rt, "eval", None).stringify_pretty()
    );
}
#[test]
fn infinity_proof_consuming_selection_direction_and_recovery() {
    for (side, other) in [("pos_inf", "neg_inf"), ("neg_inf", "pos_inf")] {
        let mut rt = runtime();
        check(&mut rt, "have fn c(x R) R=3", true);
        check(&mut rt, &format!("0*lim_{side}(c)=0"), false);
        check(
            &mut rt,
            &format!("release thm fn_limit_{other}_real_accumulation()"),
            true,
        );
        check(
            &mut rt,
            &format!("release thm fn_limit_{other}_constant(c,3)"),
            true,
        );
        check(&mut rt, &format!("lim_{side}(c)=3"), false);
        check(
            &mut rt,
            &format!("release thm fn_limit_{side}_real_accumulation()"),
            true,
        );
        check(
            &mut rt,
            &format!("release thm fn_limit_{side}_constant(c,3)"),
            true,
        );
        check(&mut rt, &format!("lim_{side}(c)=3"), true);
        check(&mut rt, &format!("lim_{side}(c)+2=5"), true);
        check(&mut rt, &format!("lim_{side}(c)=4"), false);
        check(&mut rt, "fn_lim(c,0)=3", false);
    }
}
#[test]
fn infinity_unboundedness_is_not_vacuous() {
    for side in ["pos_inf", "neg_inf"] {
        let mut rt = runtime();
        check(&mut rt, "have fn bounded(x R:0<x,x<1) R=3", true);
        check(
            &mut rt,
            &format!("release thm fn_limit_{side}_constant(bounded,3)"),
            false,
        );
        check(
            &mut rt,
            &format!("by def $has_limit_{side}(bounded,3)"),
            false,
        );
        check(&mut rt, &format!("lim_{side}(bounded)=3"), false);
        check(&mut rt, "bounded(1/2)=3", true);
    }
}
#[test]
fn infinity_direction_scope_and_substitution() {
    for side in ["pos_inf", "neg_inf"] {
        let other = if side == "pos_inf" {
            "neg_inf"
        } else {
            "pos_inf"
        };
        check(&mut runtime(),&format!("forall f fn(x R) R,L R:\n    $has_limit_{side}(f,L)\n    =>:\n        $has_limit_{other}(f,L)"),false);
        check(&mut runtime(),&format!("forall f,g fn(x R) R,L,M R:\n    f=g\n    L=M\n    $has_limit_{side}(f,L)\n    =>:\n        $has_limit_{side}(g,M)\n        lim_{side}(g)=M"),true);
        let mut rt = runtime();
        check(&mut rt, "have fn c(x R) R=3", true);
        check(&mut rt,&format!("claim:\n    ? lim_{side}(c)=3\n    release thm fn_limit_{side}_real_accumulation()\n    release thm fn_limit_{side}_constant(c,3)"),false);
        check(&mut rt, &format!("lim_{side}(c)=3"), false);
    }
}
#[test]
fn infinity_output_and_unsupported_lean() {
    for side in ["pos_inf", "neg_inf"] {
        let source = format!(
            "forall f fn(x R) R,L R:\n    $has_limit_{side}(f,L)\n    =>:\n        lim_{side}(f)=L"
        );
        let mut rt = runtime();
        let result = rt.run_litex_code(&source).unwrap();
        assert!(result.success);
        let json =
            crate::json_output::project_run_detailed(&result, &rt, "eval", None).stringify_pretty();
        assert!(
            json.contains("FunctionLimitSelectedValue") && json.contains(&format!("lim_{side}"))
        );
        let e = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
            .compile_run(&result, "infinity")
            .unwrap_err();
        assert!(e.message.contains("not supported"));
        let latex = crate::compile_to_latex::to_latex_from_source(&source, OutputLanguage::English)
            .unwrap();
        assert!(latex.contains("\\infty") && latex.contains("\\operatorname{dom}"));
    }
}
