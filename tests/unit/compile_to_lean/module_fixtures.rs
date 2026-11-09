use crate::prelude::*;
use crate::run_module::{load_file_for_lean, LoadLeanSourceResult, LoadedLeanSource};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

// Tiny source projects exercise import and scope contracts without a corpus checkout.
static NEXT_PROJECT: AtomicU64 = AtomicU64::new(0);

pub(super) struct Project(PathBuf);

pub(super) type LoadedProject = (LoadedLeanSource, Project);

impl Drop for Project {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

pub(super) fn load(name: &str) -> LoadedProject {
    let dependencies: &[&str] = match name {
        "module_additive_constant" => &["module_additive_constant"],
        "module_alias_collision" => &["module_alias_collision"],
        "module_coordinate_fields" => &["module_coordinate_fields"],
        "module_coordinate_parameters" => &["module_coordinate_parameters"],
        "module_coordinate_value" => &["module_coordinate_value"],
        "module_cross_file_parameters" => &["module_cross_file_parameters"],
        "module_dependent_function_and_vector" => &["module_dependent_function_and_vector"],
        "module_dependent_predicate" => &["module_dependent_predicate"],
        "module_dependent_record_value" => &["module_dependent_record_value"],
        "module_derivative_parameter" => &["module_derivative_parameter"],
        "module_diamond" => &["module_diamond"],
        "module_export_prefix" => &["module_export_prefix"],
        "module_exported_dependent_record" => &["module_exported_dependent_record"],
        "module_exported_have_body" => &["module_exported_have_body"],
        "module_function_alias_collision" => &["module_function_alias_collision"],
        "module_function_definition" => &["module_function_definition"],
        "module_function_guarded" => &["module_function_guarded"],
        "module_function_import" => &["module_function_definition", "module_function_import"],
        "module_function_local_binder" => &["module_function_local_binder"],
        "module_function_parameter" => &["module_function_parameter"],
        "module_guarded_predicate" => &["module_guarded_predicate"],
        "module_identifier_alias_collision" => &["module_identifier_alias_collision"],
        "module_identifier_chain" => &["module_identifier_chain"],
        "module_identifier_guarded_value" => &["module_identifier_guarded_value"],
        "module_identifier_import" => &["module_identifier_chain", "module_identifier_import"],
        "module_identifier_local_binder" => &["module_identifier_local_binder"],
        "module_identifier_release" => &["module_identifier_release"],
        "module_import_chain" => &["module_import_chain"],
        "module_import_predicates" => &["module_import_predicates", "module_nested_predicates"],
        "module_imported_parameters" => {
            &["module_cross_file_parameters", "module_imported_parameters"]
        }
        "module_imported_structure_fields" => &["module_imported_structure_fields"],
        "module_imported_templates" => &["module_imported_templates"],
        "module_mixed_foundations" => &["module_mixed_foundations"],
        "module_nested_predicates" => &["module_nested_predicates"],
        "module_nonexport_target" => &["module_import_chain", "module_nonexport_target"],
        "module_piecewise_reciprocal" => &["module_piecewise_reciprocal"],
        "module_positive_predicate" => &["module_positive_predicate"],
        "module_predicate_alias_collision" => &["module_predicate_alias_collision"],
        "module_real_parameter" => &["module_real_parameter"],
        "module_recursive_constant" => &["module_recursive_constant"],
        "module_recursive_function_values" => &["module_recursive_function_values"],
        "module_recursive_guarded" => &["module_recursive_guarded"],
        "module_selected_identity" => &["module_selected_identity"],
        "module_set_kind_parameters" => &["module_set_kind_parameters"],
        "module_template_record_fields" => &["module_template_record_fields"],
        "module_template_selected_function" => &["module_template_selected_function"],
        "module_template_values" => &["module_template_values"],
        "module_typed_constant" => &["module_typed_constant"],
        "real_set_bound_citations" => &["real_set_bound_citations"],
        "sequence_range_bounds" => &["sequence_range_bounds"],
        _ => panic!("unknown core module case: {name}"),
    };
    let directory = std::env::temp_dir().join(format!(
        "litex-core-module-{}-{}",
        std::process::id(),
        NEXT_PROJECT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let project = Project(directory);
    for (relative, source) in FILES {
        if !dependencies
            .iter()
            .any(|name| relative.starts_with(&format!("{name}/")))
        {
            continue;
        }
        let file = project.0.join(relative);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, source).unwrap();
    }
    let path = project.0.join(name).join("statement.lit");
    let command = parse_launch_command(&[
        "-lean".into(),
        "-strict".into(),
        "-f".into(),
        path.to_string_lossy().into_owned(),
    ])
    .unwrap();
    let LoadLeanSourceResult::Success(loaded) = load_file_for_lean(command).unwrap() else {
        panic!("core module must verify: {name}");
    };
    (loaded, project)
}

#[test]
fn project_survives_module_compilation_and_cleans_up_afterward() {
    let directory;
    {
        let (loaded, project) = load("module_diamond");
        directory = project.0.clone();
        let compiler = crate::compile_to_lean::LitexToLeanCompiler::new(loaded.runtime);
        compiler
            .compile_module(&loaded.closure, "fixture_lifetime")
            .expect("declaration visibility needs the source files during compilation");
        assert!(directory.is_dir());
    }
    assert!(!directory.exists());
}

const FILES: &[(&str, &str)] = &[
    (
        "module_exported_have_body/base.lit",
        "witness exist q N+ st {q > 0} from 1\nhave positive N+:\n    positive > 0\n",
    ),
    (
        "module_exported_have_body/litex.config",
        "[export]\nbase = \"base.lit\"\nmain = \"statement.lit\"\n",
    ),
    (
        "module_exported_have_body/statement.lit",
        "release obj def base::positive\nbase::positive > 0\n",
    ),
    (
        "module_additive_constant/base.lit",
        r#"# The exported constant denotes the sum of one and one.
let two = 1 + 1
"#,
    ),
    (
        "module_additive_constant/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_additive_constant/statement.lit",
        r#"# The exported additive constant equals two.
base::two = 2
"#,
    ),
    (
        "module_alias_collision/left/base/facts.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    x + 0 = x
"#,
    ),
    (
        "module_alias_collision/left/base/litex.config",
        r#"[export]
facts = "./facts.lit"
"#,
    ),
    (
        "module_alias_collision/left/litex.config",
        r#"[import]
Bottom = "./base"

[export]
main = "./main.lit"
"#,
    ),
    (
        "module_alias_collision/left/main.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    by thm Bottom::facts::replay_add_zero(x) => x + 0 = x
"#,
    ),
    (
        "module_alias_collision/litex.config",
        r#"[import]
Left = "./left"
Right = "./right"

[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_alias_collision/right/base/facts.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    x + 0 = x
"#,
    ),
    (
        "module_alias_collision/right/base/litex.config",
        r#"[export]
facts = "./facts.lit"
"#,
    ),
    (
        "module_alias_collision/right/litex.config",
        r#"[import]
Bottom = "./base"

[export]
main = "./main.lit"
"#,
    ),
    (
        "module_alias_collision/right/main.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    by thm Bottom::facts::replay_add_zero(x) => x + 0 = x
"#,
    ),
    (
        "module_alias_collision/statement.lit",
        r#"by thm Left::main::replay_add_zero(2) => 2 + 0 = 2
by thm Right::main::replay_add_zero(3) => 3 + 0 = 3
"#,
    ),
    (
        "module_coordinate_fields/base.lit",
        r#"# A coordinate pair has two real fields.
struct CoordinatePair:
    x R
    y R
"#,
    ),
    (
        "module_coordinate_fields/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_coordinate_fields/statement.lit",
        r#"# Check coordinate fields through a structure declared in another export.
(2,3) $in &base::CoordinatePair
forall p &base::CoordinatePair:
    p.x $in R
    p.y $in R
struct CoordinatePair:
    x N
    y N
forall p &main::CoordinatePair:
    p.x $in N
    p.y $in N
"#,
    ),
    (
        "module_coordinate_parameters/litex.config",
        r#"[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_coordinate_parameters/statement.lit",
        r#"# Use arbitrary Cartesian points and vectors through their coordinate domains.
have p cart(R, R)
have coordinate_sum R = p(1) + p(2)
have n N+
have v finite_seq(R, n)
v(1) $in R

forall k closed_range(1, n):
    v(k) $in R
"#,
    ),
    (
        "module_coordinate_value/base.lit",
        r#"# A concrete coordinate record exposes two real fields.
struct CoordinatePair:
    x R
    y R
have point &CoordinatePair = (2,3)
"#,
    ),
    (
        "module_coordinate_value/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_coordinate_value/statement.lit",
        r#"# Read the coordinates of a record defined in another export.
base::point.x $in R
release obj def base::point
base::point.x = 2
sketch:
    have point &base::CoordinatePair = (4,5)
    point.x = 4
    base::point.x = 2
"#,
    ),
    (
        "module_cross_file_parameters/base.lit",
        r#"# Declare arbitrary objects shared with a later mathematical source file.

have a R

have A nonempty_set

have f fn(x R) R

thm commute_with_a:
    ? forall x R:
        x + a = a + x
    x + a = a + x
"#,
    ),
    (
        "module_cross_file_parameters/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_cross_file_parameters/statement.lit",
        r#"# Use earlier real, set and function parameters without changing their representations.

base::a = base::a

release obj def base::a

base::a $in C

release obj def base::A

release obj def base::f

have y R = base::f(base::a)

have element base::A

element = element

by thm base::commute_with_a(2) => 2 + base::a = base::a + 2

let shifted = base::a + 1

shifted = 1 + base::a
"#,
    ),
    (
        "module_dependent_function_and_vector/litex.config",
        r#"[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_dependent_function_and_vector/statement.lit",
        r#"# Construct Cartesian and function values over a carrier in a preceding parameter group.
have vector_carrier set, vector cart(vector_carrier,vector_carrier) = R, (4,5)
vector(1) = 4
have function_carrier set, endomap fn(x function_carrier) function_carrier = R, fn(x R) R {x}
endomap(2) = 2
"#,
    ),
    (
        "module_dependent_predicate/base.lit",
        r#"# A predicate's second argument belongs to the nonempty set supplied first.
prop self_member(A nonempty_set, x A):
    x = x
prop finite_self_member(A finite_set, x A):
    x = x
prop set_self_member(A set, x A):
    x = x
"#,
    ),
    (
        "module_dependent_predicate/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_dependent_predicate/statement.lit",
        r#"# The exported dependent predicate accepts the real carrier and the real number one.
by def $base::self_member(R, 1)
by def $base::finite_self_member({1}, 1)
by def $base::set_self_member(R, 1)
"#,
    ),
    (
        "module_dependent_record_value/base.lit",
        r#"# A pair has both coordinates in its set-valued parameter.
struct PairIn<A set>:
    first A
    second A
"#,
    ),
    (
        "module_dependent_record_value/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_dependent_record_value/statement.lit",
        r#"# Define a carrier and a dependent pair in one declaration, then read its first coordinate.
have carrier set, record &base::PairIn<carrier> = R, (2,3)
record.first = 2
"#,
    ),
    (
        "module_derivative_parameter/litex.config",
        r#"[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_derivative_parameter/statement.lit",
        r#"# Select the derivative of an arbitrary real function from its certified candidate.

have f fn(x R) R

forall p, L R:
    $has_derivative_at(f, p, L)
    =>:
        derivative(f, p) = L
        derivative(f, p) $in R
"#,
    ),
    (
        "module_diamond/base/facts.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    x + 0 = x
"#,
    ),
    (
        "module_diamond/base/litex.config",
        r#"[export]
facts = "./facts.lit"
"#,
    ),
    (
        "module_diamond/left/litex.config",
        r#"[import]
Bottom = "../base"

[export]
main = "./main.lit"
"#,
    ),
    (
        "module_diamond/left/main.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    by thm Bottom::facts::replay_add_zero(x) => x + 0 = x
"#,
    ),
    (
        "module_diamond/litex.config",
        r#"[import]
Left = "./left"
Right = "./right"

[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_diamond/right/litex.config",
        r#"[import]
Bottom = "../base"

[export]
main = "./main.lit"
"#,
    ),
    (
        "module_diamond/right/main.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    by thm Bottom::facts::replay_add_zero(x) => x + 0 = x
"#,
    ),
    (
        "module_diamond/statement.lit",
        r#"by thm Left::main::replay_add_zero(2) => 2 + 0 = 2
by thm Right::main::replay_add_zero(3) => 3 + 0 = 3
"#,
    ),
    (
        "module_export_prefix/base.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    x + 0 = x
"#,
    ),
    (
        "module_export_prefix/later.lit",
        r#"thm replay_later_export:
    ? 3 = 3
    3 = 3
"#,
    ),
    (
        "module_export_prefix/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
later = "./later.lit"
"#,
    ),
    (
        "module_export_prefix/statement.lit",
        r#"by thm base::replay_add_zero(2) => 2 + 0 = 2
"#,
    ),
    (
        "module_exported_dependent_record/base.lit",
        r#"# Construct a pair whose fields use an earlier carrier in the same declaration.
struct PairIn<A set>:
    first A
    second A
have carrier set, record &PairIn<carrier> = R, (2,3)
"#,
    ),
    (
        "module_exported_dependent_record/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_exported_dependent_record/statement.lit",
        r#"# Form both fields of an exported dependent pair and reuse them in a tuple.
$is_set(base::record.first)
$is_set(base::record.second)
$is_set((base::record.first, base::record.second))
release obj def base::record
base::record.first = 2
base::record.second = 3
base::record.first + base::record.second = 5
"#,
    ),
    (
        "module_function_alias_collision/left/base.lit",
        r#"have fn value(x R) R = x + 1
"#,
    ),
    (
        "module_function_alias_collision/left/litex.config",
        r#"[export]
base = "./base.lit"
"#,
    ),
    (
        "module_function_alias_collision/litex.config",
        r#"[import]
Left = "./left"
Right = "./right"
[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_function_alias_collision/right/base.lit",
        r#"have fn value(x R) R = x + 2
"#,
    ),
    (
        "module_function_alias_collision/right/litex.config",
        r#"[export]
base = "./base.lit"
"#,
    ),
    (
        "module_function_alias_collision/statement.lit",
        r#"release obj def Left::base::value
release obj def Right::base::value
Left::base::value(1) = 2
Right::base::value(1) = 3
"#,
    ),
    (
        "module_function_definition/base.lit",
        r#"have fn successor(x R) R = x + 1
"#,
    ),
    (
        "module_function_definition/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_function_definition/statement.lit",
        r#"release obj def base::successor
base::successor(1) = 2
forall x R:
    base::successor(x) = x + 1
"#,
    ),
    (
        "module_function_guarded/base.lit",
        r#"have fn reciprocal(x R: x != 0) R = 1 / x
"#,
    ),
    (
        "module_function_guarded/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_function_guarded/statement.lit",
        r#"release obj def base::reciprocal
forall x R:
    x != 0
    =>:
        base::reciprocal(x) = 1 / x
"#,
    ),
    (
        "module_function_import/litex.config",
        r#"[import]
Library = "../module_function_definition"
[alias]
Values = Library::base
[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_function_import/statement.lit",
        r#"release obj def Values::successor
3 = Values::successor(2)
"#,
    ),
    (
        "module_function_local_binder/base.lit",
        r#"have fn successor(x R) R = x + 1
"#,
    ),
    (
        "module_function_local_binder/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_function_local_binder/statement.lit",
        r#"release obj def base::successor
forall successor R:
    2 = base::successor(1)
"#,
    ),
    (
        "module_function_parameter/litex.config",
        r#"[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_function_parameter/statement.lit",
        r#"# Apply an arbitrary real map to fixed and arbitrary real arguments.
have f fn(x R) R
have y R = f(2)

forall x R:
    f(x) $in R
"#,
    ),
    (
        "module_guarded_predicate/base.lit",
        r#"# The reciprocal identity includes the required nonzero real domain.
prop quotient_identity(x R):
    x != 0
    x / x = 1
"#,
    ),
    (
        "module_guarded_predicate/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_guarded_predicate/statement.lit",
        r#"# The exported guarded identity holds for two and retains its division guard.
by def $base::quotient_identity(2)
"#,
    ),
    (
        "module_identifier_alias_collision/left/defs.lit",
        r#"# This package defines two by addition.
let value = 1 + 1
"#,
    ),
    (
        "module_identifier_alias_collision/left/litex.config",
        r#"[export]
defs = "./defs.lit"
"#,
    ),
    (
        "module_identifier_alias_collision/litex.config",
        r#"[import]
Left = "./left"
Right = "./right"

[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_identifier_alias_collision/right/defs.lit",
        r#"# This separate package defines three by addition.
let value = 1 + 2
"#,
    ),
    (
        "module_identifier_alias_collision/right/litex.config",
        r#"[export]
defs = "./defs.lit"
"#,
    ),
    (
        "module_identifier_alias_collision/statement.lit",
        r#"# Equal local names in two packages keep their respective definitions.
Left::defs::value = 2
Right::defs::value = 3
"#,
    ),
    (
        "module_identifier_chain/base.lit",
        r#"# Two exported names denote the same additive constant through an alias.
let two = 1 + 1
let twin = two
"#,
    ),
    (
        "module_identifier_chain/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_identifier_chain/statement.lit",
        r#"# Establish the original constant before unfolding its exported alias.
base::two = 2
base::twin = 2
"#,
    ),
    (
        "module_identifier_guarded_value/base.lit",
        r#"# A reciprocal uses the exported constant and its proved nonzero guard.
let two = 1 + 1
two = 2
two != 0
let reciprocal = 1 / two
"#,
    ),
    (
        "module_identifier_guarded_value/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_identifier_guarded_value/statement.lit",
        r#"# Releasing the reciprocal keeps the original constructor and nonzero evidence.
release obj def base::reciprocal
"#,
    ),
    (
        "module_identifier_import/litex.config",
        r#"[import]
Library = "../module_identifier_chain"

[alias]
Values = Library::base

[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_identifier_import/statement.lit",
        r#"# Imported constants retain their original definitions through the configured namespace.
2 = Values::two
2 = Values::twin
"#,
    ),
    (
        "module_identifier_local_binder/base.lit",
        r#"# The exported additive constant is independent of a caller-local parameter.
let two = 1 + 1
"#,
    ),
    (
        "module_identifier_local_binder/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_identifier_local_binder/statement.lit",
        r#"# A local real parameter with the same spelling does not change the exported constant.
thm independent_constant:
    ? forall two R:
        base::two = 2
    base::two = 2
"#,
    ),
    (
        "module_identifier_release/base.lit",
        r#"# A bare and a typed exported constant each denote the sum of one and one.
let two = 1 + 1
have typed_two R = 1 + 1
"#,
    ),
    (
        "module_identifier_release/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_identifier_release/statement.lit",
        r#"# Explicitly release each exported definition and keep its original publications.
release obj def base::two
release obj def base::typed_two
base::two = 2
base::typed_two = 2
"#,
    ),
    (
        "module_import_chain/base/facts.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    x + 0 = x
"#,
    ),
    (
        "module_import_chain/base/litex.config",
        r#"[export]
facts = "./facts.lit"
"#,
    ),
    (
        "module_import_chain/library/litex.config",
        r#"[import]
Bottom = "../base"

[export]
main = "./main.lit"
"#,
    ),
    (
        "module_import_chain/library/main.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    by thm Bottom::facts::replay_add_zero(x) => x + 0 = x
"#,
    ),
    (
        "module_import_chain/litex.config",
        r#"[import]
Library = "./library"

[alias]
Proof = Library::main

[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_import_chain/statement.lit",
        r#"by thm Proof::replay_add_zero(2) => 2 + 0 = 2
"#,
    ),
    (
        "module_import_predicates/litex.config",
        r#"[import]
Library = "../module_nested_predicates"

[alias]
Defined = Library::base

[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_import_predicates/statement.lit",
        r#"# Imported positive-pair predicates retain their original definition through either alias.
by def $Defined::positive_pair(2, 1)
$Library::base::positive_pair(2, 1)
"#,
    ),
    (
        "module_imported_parameters/litex.config",
        r#"[import]
Parameters = "../module_cross_file_parameters"
[alias]
Original = Parameters::base
[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_imported_parameters/statement.lit",
        r#"# Reuse imported generic parameters, dependent carriers and captured definitions through an alias.

Original::a = Original::a

release obj def Original::a

release obj def Original::A

release obj def Original::f

have value R = Original::f(Original::a)

have a R

a = a

Original::a = Original::a

release obj def Parameters::main::shifted

Parameters::main::shifted = Original::a + 1

by thm Original::commute_with_a(2) => 2 + Original::a = Original::a + 2
"#,
    ),
    (
        "module_imported_structure_fields/left/base.lit",
        r#"# Declare real coordinate records and records with dependent fields and laws.
struct CoordinatePair:
    x R
    y R

struct PositivePoint:
    x R
    y R
    <=>:
        x > 0

struct GenericUniversalEndomap<A set>:
    function fn(y A) A
    base A
    <=>:
        forall z A:
            function(z) = z

struct DependentRecordOfSubsets:
    carrier power_set(R)
    subsets fn(t R) power_set(carrier)
"#,
    ),
    (
        "module_imported_structure_fields/left/litex.config",
        r#"[export]
base = "./base.lit"
"#,
    ),
    (
        "module_imported_structure_fields/litex.config",
        r#"[import]
Left = "./left"
Right = "./right"
[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_imported_structure_fields/right/base.lit",
        r#"# A different coordinate record has natural-number fields.
struct CoordinatePair:
    x N
    y N
"#,
    ),
    (
        "module_imported_structure_fields/right/litex.config",
        r#"[export]
base = "./base.lit"
"#,
    ),
    (
        "module_imported_structure_fields/statement.lit",
        r#"# Check imported record fields, laws and dependent carriers without name collisions.
forall p &Left::base::CoordinatePair:
    p.x $in R
    p.y $in R
forall p &Right::base::CoordinatePair:
    p.x $in N
    p.y $in N
forall p &Left::base::PositivePoint:
    p.x > 0
forall A set, p &Left::base::GenericUniversalEndomap<A>, x A:
    p.function(x) = x
forall p &Left::base::DependentRecordOfSubsets, x R:
    $is_set(p.subsets(x))
(1,2) $in &Left::base::PositivePoint
"#,
    ),
    (
        "module_imported_templates/left/defs.lit",
        r#"# Copy a carrier and translate real inputs by a supplied real offset.
template<S set>:
    have copied set = S

template<offset R>:
    have fn translate(x R) R = x + offset
"#,
    ),
    (
        "module_imported_templates/left/litex.config",
        r#"[export]
defs = "./defs.lit"
"#,
    ),
    (
        "module_imported_templates/litex.config",
        r#"[import]
Left = "./left"
Right = "./right"

[export]
main = "./statement.lit"

[alias]
Left = Left::defs
Right = Right::defs
"#,
    ),
    (
        "module_imported_templates/right/defs.lit",
        r#"# Translate real inputs by subtracting a supplied real offset.
template<offset R>:
    have fn translate(x R) R = x - offset
"#,
    ),
    (
        "module_imported_templates/right/litex.config",
        r#"[export]
defs = "./defs.lit"
"#,
    ),
    (
        "module_imported_templates/statement.lit",
        r#"# Use two imported translations with the same name and a copied real carrier.
\Left::defs::translate<2>(3) = 5
\Right::translate<2>(3) = 1
\Left::copied<R> = R

forall a, x R:
    \Left::translate<a>(x) = x + a
"#,
    ),
    (
        "module_mixed_foundations/litex.config",
        r#"[export]
sets = "./sets.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_mixed_foundations/sets.lit",
        r#"# Distribute union over intersection, including operand permutations and reversed equality.
forall dist_u_A, dist_u_B, dist_u_D set:
    union(dist_u_A, intersect(dist_u_B, dist_u_D)) = intersect(union(dist_u_A, dist_u_B), union(dist_u_A, dist_u_D))
    union(intersect(dist_u_B, dist_u_D), dist_u_A) = intersect(union(dist_u_D, dist_u_A), union(dist_u_A, dist_u_B))

forall dist_ur_A, dist_ur_B, dist_ur_D set:
    intersect(union(dist_ur_B, dist_ur_A), union(dist_ur_D, dist_ur_A)) = union(intersect(dist_ur_B, dist_ur_D), dist_ur_A)
"#,
    ),
    (
        "module_mixed_foundations/statement.lit",
        r#"forall replay_order N, replay_matrix matrix(C, replay_order, replay_order):
    matrix_power(replay_matrix, replay_order, 0) = identity_matrix(replay_order)
"#,
    ),
    (
        "module_nested_predicates/base.lit",
        r#"# Positive pairs require both real coordinates to be positive.
prop positive(x R):
    x > 0
prop positive_pair(first, second R):
    $positive(first)
    $positive(second)
prop positive_witness(value R):
    exist candidate R st {candidate = value, $positive(candidate)}
"#,
    ),
    (
        "module_nested_predicates/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_nested_predicates/statement.lit",
        r#"# Repeated and reordered positive coordinates satisfy the pair predicate.
by def $base::positive_pair(1, 1)
witness exist positive_candidate R st {positive_candidate = 1, $base::positive(positive_candidate)} from 1:
    1 = 1
    by def $base::positive(1)
by def $base::positive_witness(1)
by def $base::positive_pair(1, 2)
by def $base::positive_pair(2, 1)
"#,
    ),
    (
        "module_nonexport_target/base.lit",
        r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    x + 0 = x
"#,
    ),
    (
        "module_nonexport_target/litex.config",
        r#"[import]
Library = "../module_import_chain/library"

[export]
base = "./base.lit"
"#,
    ),
    (
        "module_nonexport_target/statement.lit",
        r#"by thm Library::main::replay_add_zero(2) => 2 + 0 = 2
by thm base::replay_add_zero(3) => 3 + 0 = 3
"#,
    ),
    (
        "module_piecewise_reciprocal/base.lit",
        r#"# Extend real reciprocal by giving it the value zero at zero.
have fn reciprocal(x R) R by cases:
    case x = 0: 0
    case x != 0: 1 / x
"#,
    ),
    (
        "module_piecewise_reciprocal/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_piecewise_reciprocal/statement.lit",
        r#"# Evaluate the exported reciprocal at zero and at a nonzero real.
$is_set(base::reciprocal)
release obj def base::reciprocal
base::reciprocal(2) = 1 / 2
base::reciprocal(0) = 0

forall t R:
    t != 0
    =>:
        base::reciprocal(t) = 1 / t
"#,
    ),
    (
        "module_positive_predicate/base.lit",
        r#"# A positive real number has a strictly positive real value.
prop positive(x R):
    x > 0
"#,
    ),
    (
        "module_positive_predicate/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_positive_predicate/statement.lit",
        r#"# The real number one satisfies the exported positivity predicate.
by def $base::positive(1)
forall positive_argument R:
    positive_argument > 0
    =>:
        $base::positive(positive_argument)
forall positive_assumption R:
    $base::positive(positive_assumption)
    =>:
        positive_assumption > 0
"#,
    ),
    (
        "module_predicate_alias_collision/left/defs.lit",
        r#"# This package's sign predicate describes positive real numbers.
prop signed(x R):
    x > 0
"#,
    ),
    (
        "module_predicate_alias_collision/left/litex.config",
        r#"[export]
defs = "./defs.lit"
"#,
    ),
    (
        "module_predicate_alias_collision/litex.config",
        r#"[import]
Left = "./left"
Right = "./right"

[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_predicate_alias_collision/right/defs.lit",
        r#"# This package's separate sign predicate describes negative real numbers.
prop signed(x R):
    x < 0
"#,
    ),
    (
        "module_predicate_alias_collision/right/litex.config",
        r#"[export]
defs = "./defs.lit"
"#,
    ),
    (
        "module_predicate_alias_collision/statement.lit",
        r#"# Different qualified sign predicates keep their respective mathematical contracts.
by def $Left::defs::signed(1)
by def $Right::defs::signed(-1)
"#,
    ),
    (
        "module_real_parameter/litex.config",
        r#"[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_real_parameter/statement.lit",
        r#"# Preserve one arbitrary real object and its source membership facts.
have a R
a = a
$is_set(a)
a $in C
"#,
    ),
    (
        "module_recursive_constant/base.lit",
        r#"# Define a real sequence that keeps its first value by recursion.
have fn repeat_one(n N) R by induc n from 0:
    case n = 0: 1
    case n > 0: repeat_one(n - 1)
"#,
    ),
    (
        "module_recursive_constant/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_recursive_constant/statement.lit",
        r#"# Evaluate the exported sequence and reuse its released recursive equation.
$is_set(base::repeat_one)
release obj def base::repeat_one
base::repeat_one(0) = 1
base::repeat_one(1) = base::repeat_one(0)
base::repeat_one(1) = 1

forall n N:
    base::repeat_one(n) $in R
"#,
    ),
    (
        "module_recursive_function_values/base.lit",
        r#"# Construct real functions recursively, adding one to the previous function.
have fn translated_functions(n N) fn(x R) R by induc n from 0:
    case n = 0: fn(x R) R {x}
    case n > 0: fn(x R) R {translated_functions(n - 1)(x) + 1}
"#,
    ),
    (
        "module_recursive_function_values/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_recursive_function_values/statement.lit",
        r#"# Use a recursively built translation function from another source file.
release obj def base::translated_functions
have shifted R = base::translated_functions(1)(2)
base::translated_functions(0) = fn(x R) R {x}
base::translated_functions(1) = fn(x R) R {base::translated_functions(1 - 1)(x) + 1}
$is_set(shifted)
"#,
    ),
    (
        "module_recursive_guarded/base.lit",
        r#"# Repeat one from an arbitrary integer lower bound.
have fn constant_from(n, b Z: n >= b) R by induc n from b:
    case n = b: 1
    case n > b: constant_from(n - 1, b)
"#,
    ),
    (
        "module_recursive_guarded/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_recursive_guarded/statement.lit",
        r#"# Evaluate the exported sequence with its lower-bound condition.
$is_set(base::constant_from)
release obj def base::constant_from
base::constant_from(2, 2) = 1
base::constant_from(3, 2) = base::constant_from(2, 2)
base::constant_from(3, 2) = 1

forall n, b Z:
    n >= b
    =>:
        base::constant_from(n, b) $in R
"#,
    ),
    (
        "module_selected_identity/base.lit",
        r#"# Select the real identity from its unique value specification.
thm unique_copy:
    ? forall seed R:
        exist! value R st {value = seed}
    witness exist! value R st {value = seed} from seed

have fn selected by exist!:
    ? forall x R:
        exist! y R st {y = x}
"#,
    ),
    (
        "module_selected_identity/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_selected_identity/statement.lit",
        r#"# Use and release a real identity selected from unique witnesses.
$is_set(base::selected)
release obj def base::selected
base::selected(3) = 3

forall t R:
    base::selected(t) = t
"#,
    ),
    (
        "module_set_kind_parameters/litex.config",
        r#"[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_set_kind_parameters/statement.lit",
        r#"# Preserve arbitrary, finite and nonempty sets in an exported source file.
have A set
have F finite_set
have B nonempty_set
A = A
have count N = finite_set_size(F)
have element B
element = element
"#,
    ),
    (
        "module_template_record_fields/base.lit",
        r#"# Construct a generic pair from two supplied members of a carrier.
struct GenericPair<S set>:
    first S
    second S

template<S set, x, y S>:
    have selected_pair &GenericPair<S> = (x, y)
"#,
    ),
    (
        "module_template_record_fields/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_template_record_fields/statement.lit",
        r#"# Read the fields of an exported generic-pair template.
\base::selected_pair<R, 2, 3>.first = 2
\base::selected_pair<R, 2, 3>.second = 3

forall S set, x, y S:
    \base::selected_pair<S, x, y>.first = x
"#,
    ),
    (
        "module_template_selected_function/litex.config",
        r#"[export]
main = "./statement.lit"
"#,
    ),
    (
        "module_template_selected_function/statement.lit",
        r#"# A function chosen between nonempty sets can be called and composed.
template<A, B nonempty_set>:
    have selected_function fn(x A) B

\selected_function<R, R> $in fn(x R) R
\selected_function<R, R>(2) $in R

have fn chosen_real_value(a R) R = \selected_function<R, R>(a)

chosen_real_value(2) = \selected_function<R, R>(2)
forall a R:
    chosen_real_value(a) = \selected_function<R, R>(a)
"#,
    ),
    (
        "module_template_values/base.lit",
        r#"# Translate a real input and construct a quotient with a nonzero denominator.
template<offset R>:
    have fn translate(x R) R = x + offset

template<x R, y R: y != 0,>:
    have quotient R = x / y
"#,
    ),
    (
        "module_template_values/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_template_values/statement.lit",
        r#"# Instantiate exported numeric templates and retain their argument conditions.
\base::translate<2>(3) = 5

forall a, x R:
    \base::translate<a>(x) = x + a

\base::quotient<6, 2> = 3

forall x, y R:
    y != 0
    =>:
        \base::quotient<x, y> = x / y

template<offset R>:
    have fn translate(x R) R = x - offset

\translate<7>(9) = 2
\base::translate<7>(9) = 16

let shifted = \base::translate<2>
shifted(4) = 6
"#,
    ),
    (
        "module_typed_constant/base.lit",
        r#"# The exported real constant is defined by the sum of one and one.
have typed_two R = 1 + 1
"#,
    ),
    (
        "module_typed_constant/litex.config",
        r#"[export]
base = "./base.lit"
main = "./statement.lit"
"#,
    ),
    (
        "module_typed_constant/statement.lit",
        r#"# Reverse equality retains the exported constant definition and its real carrier.
2 = base::typed_two
"#,
    ),
    (
        "real_set_bound_citations/statement.lit",
        r#"# Real-set bounds and their negations retain ordinary fact citations.
forall A set, b R:
    A $subset R
    $is_real_upper_bound(A,b)
    =>:
        $is_real_upper_bound(A,b)
forall A set, b R:
    A $subset R
    not $is_real_upper_bound(A,b)
    =>:
        not $is_real_upper_bound(A,b)
forall A set, b R:
    A $subset R
    $is_real_lower_bound(A,b)
    =>:
        $is_real_lower_bound(A,b)
forall A set, b R:
    A $subset R
    not $is_real_lower_bound(A,b)
    =>:
        not $is_real_lower_bound(A,b)
forall A set:
    A $subset R
    $is_real_bounded_above(A)
    =>:
        $is_real_bounded_above(A)
forall A set:
    A $subset R
    not $is_real_bounded_above(A)
    =>:
        not $is_real_bounded_above(A)
forall A set:
    A $subset R
    $is_real_bounded_below(A)
    =>:
        $is_real_bounded_below(A)
forall A set:
    A $subset R
    not $is_real_bounded_below(A)
    =>:
        not $is_real_bounded_below(A)
forall A set:
    A $subset R
    $is_real_bounded(A)
    =>:
        $is_real_bounded(A)
forall A set:
    A $subset R
    not $is_real_bounded(A)
    =>:
        not $is_real_bounded(A)
"#,
    ),
    (
        "real_set_bound_citations/substitution.lit",
        r#"# Equal sets and equal real bounds preserve the upper-bound property.
forall A,B set, b,c R:
    A $subset R
    B $subset R
    A = B
    b = c
    $is_real_upper_bound(A,b)
    =>:
        $is_real_upper_bound(B,c)
"#,
    ),
    (
        "sequence_range_bounds/containment.lit",
        r#"# A real sequence's range lies in its declared real codomain.
forall sequence_range_probe seq(R):
    fn_range(sequence_range_probe) $subset R
"#,
    ),
    (
        "sequence_range_bounds/statement.lit",
        r#"# A real sequence is bounded exactly when its range is bounded; retain both witnesses.
thm sequence_range_bounded_above:
    ? forall a seq(R):
        $is_seq_bounded_above(a)
        =>:
            $is_real_bounded_above(fn_range(a))

thm bounded_range_sequence_above:
    ? forall a seq(R):
        $is_real_bounded_above(fn_range(a))
        =>:
            $is_seq_bounded_above(a)

thm sequence_range_bounded_below:
    ? forall a seq(R):
        $is_seq_bounded_below(a)
        =>:
            $is_real_bounded_below(fn_range(a))

thm bounded_range_sequence_below:
    ? forall a seq(R):
        $is_real_bounded_below(fn_range(a))
        =>:
            $is_seq_bounded_below(a)

thm sequence_range_bounded:
    ? forall a seq(R):
        $is_seq_bounded(a)
        =>:
            $is_real_bounded(fn_range(a))

thm bounded_range_sequence:
    ? forall a seq(R):
        $is_real_bounded(fn_range(a))
        =>:
            $is_seq_bounded(a)

forall a seq(R):
    $is_seq_bounded(a)
    =>:
        $is_seq_bounded_above(a)
        $is_seq_bounded_below(a)
        exist u R st {$is_real_upper_bound(fn_range(a),u)}
        exist l R st {$is_real_lower_bound(fn_range(a),l)}

"#,
    ),
];
