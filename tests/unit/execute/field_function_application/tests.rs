use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{CodeSource, RealOrVirtualPath, Runtime};

const OPS: &str = "struct Ops:\n    op fn(x R)R\n    tag N\nhave fn shift(x R)R=x+1\nhave ops &Ops=(shift,0)\n";
const FAMILY: &str = "struct FamilyHolder:\n    fiber fn(idx N+)power_set(R)\n    tag N\n";

fn runtime(source: CodeSource) -> Runtime {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true,
        language: OutputLanguage::English,
    });
    rt.finish_file();
    rt.set_code_source(source);
    rt.begin_file(RealOrVirtualPath::Eval);
    rt
}

fn check(code: &str, expected: bool) -> String {
    let mut detail = String::new();
    for source in [CodeSource::Eval, CodeSource::Repl, CodeSource::RootExport { export_file_id: 0 }] {
        let mut rt = runtime(source);
        let result = rt.run_litex_code(code).expect("valid input must not raise InternalBug");
        detail = crate::json_output::emit_run_detailed(&result, &rt, "field application", None);
        assert_eq!(result.success, expected, "{code}\n{detail}");
        assert!(result.session_error.is_none(), "{code}\n{detail}");
    }
    detail
}

#[test]
fn checked_tuple_function_field_names_valid_preimages() {
    check(&format!("{OPS}have by fn_preimage: a from ops.op(2) $in fn_range(ops.op)\na $in R\nops.op(a)=ops.op(2)\n"), true);
}

#[test]
fn opaque_field_range_members_publish_real_existential_evidence() {
    check(&format!("{OPS}ops.op(2) $in fn_range(ops.op)\nwitness $is_nonempty_set(fn_range(ops.op)) from ops.op(2)\nhave z fn_range(ops.op)\nexist x R st {{z=ops.op(x)}}\nobtain a from exist x R st {{z=ops.op(x)}}\nz=ops.op(a)\n"), true);
    check("struct Ops:\n    op fn(x R)R\n    tag N\nforall ops &Ops,y R:\n    ops.op $in fn(x R)R\n    y $in fn_range(ops.op)\n    =>:\n        exist x R st {y=ops.op(x)}\n", true);
}

#[test]
fn field_family_members_publish_union_and_intersection_consequences() {
    check(&format!("{FAMILY}forall holder &FamilyHolder,x index_union(N+,R,holder.fiber):\n    exist slot N+ st {{x $in holder.fiber(slot)}}\n"), true);
    check(&format!("{FAMILY}forall holder &FamilyHolder,x index_intersect(N+,R,holder.fiber),k N+:\n    x $in holder.fiber(k)\n"), true);
    check(&format!("{FAMILY}forall holder,other &FamilyHolder,x index_union(N+,R,holder.fiber):\n    exist slot N+ st {{x $in other.fiber(slot)}}\n"), false);
    check(&format!("{FAMILY}forall holder &FamilyHolder,x index_intersect({{1}},R,holder.fiber):\n    x $in holder.fiber(2)\n"), false);
}

#[test]
fn field_preimage_preserves_guards_and_multiple_parameter_types() {
    let guarded = "struct Guarded:\n    op fn(x R: x > 0)R\n    tag N\nhave fn positive(x R: x > 0)R=x\nhave ops &Guarded=(positive,0)\n";
    check(&format!("{guarded}have by fn_preimage: a from ops.op(1) $in fn_range(ops.op)\na > 0\nops.op(a)=ops.op(1)\n"), true);
    check(&format!("{guarded}have by fn_preimage: a from ops.op(0) $in fn_range(ops.op)\n"), false);
    let multiple = "struct Multiple:\n    op fn(x R,y R)R\n    tag N\nhave fn add(x R,y R)R=x+y\nhave ops &Multiple=(add,0)\n";
    check(&format!("{multiple}have by fn_preimage: a,b from ops.op(1,2) $in fn_range(ops.op)\na $in R\nb $in R\nops.op(a,b)=ops.op(1,2)\n"), true);
    check(&format!("{multiple}have by fn_preimage: a,b from ops.op(1,{{2}}) $in fn_range(ops.op)\n"), false);
}

#[test]
fn wrong_field_source_owner_arity_and_equation_reject() {
    check("struct Ops:\n    op fn(x R)R\n    tag N\nhave fn zero(x R)R=0\nhave ops &Ops=(zero,0)\nhave by fn_preimage: a from 1 $in fn_range(ops.op)\n", false);
    check(&format!("{OPS}have fn zero(x R)R=0\nhave other &Ops=(zero,0)\nhave by fn_preimage: a from ops.op(2) $in fn_range(other.op)\n"), false);
    check(&format!("{OPS}have by fn_preimage: a,b from ops.op(2) $in fn_range(ops.op)\n"), false);
    check(&format!("{OPS}have by fn_preimage: a from ops.op(2) $in fn_range(ops.op)\nops.op(a)=ops.op(2)+1\n"), false);
}

#[test]
fn failed_field_preimage_discards_names_and_proof_scope_stays_local() {
    let mut rt = runtime(CodeSource::Eval);
    assert!(rt.run_litex_code(OPS).unwrap().success);
    let failed = rt.run_litex_code("have by fn_preimage: a,b from ops.op(2) $in fn_range(ops.op)\n").unwrap();
    assert!(!failed.success && failed.session_error.is_none());
    assert!(rt.run_litex_code("have a N=0\nhave b N=1\na=0\nb=1\n").unwrap().success);
    check(&format!("{OPS}sketch:\n    have by fn_preimage: a from ops.op(2) $in fn_range(ops.op)\n    ops.op(a)=ops.op(2)\nlet a=7\na=7\n"), true);
}

#[test]
fn stored_even_real_powers_infer_positivity_without_positive_base() {
    for code in [
        "have x R*\nhave h R=x^2\nh $in R+\n",
        "have x R-\nhave h R=x^2\nh $in R+\n",
        "have h R=(-2)^(-2)\nh $in R+\n",
        "have x R+\nhave n N\nhave h C=x^n\nh $in R+\n",
    ] { check(code, true); }
    let mut rt = runtime(CodeSource::Eval);
    let result = rt.run_litex_code("have x R*\nhave h R=x^2\n").unwrap();
    assert!(result.success);
    let normal = crate::json_output::emit_run_normal(&result, &rt, "positive power", None);
    assert!(normal.contains("h $in R+"), "the declaration must publish the consequence: {normal}");
}

#[test]
fn zero_unknown_complex_and_negative_odd_powers_do_not_infer_positivity() {
    for code in [
        "have x R\nhave h R=x^2\nh $in R+\n",
        "have h R=0^2\nh $in R+\n",
        "have h C=i^2\nh $in R+\n",
        "have h R=(-2)^3\nh $in R+\n",
        "have h R=0^(-2)\n",
    ] { check(code, false); }
}
