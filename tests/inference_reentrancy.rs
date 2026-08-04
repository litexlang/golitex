use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn reentrant_well_definedness_inference_finishes() {
    let fixture = Fixture::new("well-definedness-reentrancy");
    let source = fixture.path("main.lit");
    write_file(
        &fixture.path("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(
        &source,
        r#"struct VectorSpace<s nonempty_set, v nonempty_set>:
    zero v
    add fn(x, y v) v
    smul fn(a s, x v) v
    <=>:
        forall x v:
            add(zero, x) = x

prop generated(s nonempty_set, v nonempty_set, space &VectorSpace<s, v>, value v):
    value = value

template<s nonempty_set, v nonempty_set, space &VectorSpace<s, v>>:
    have carrier power_set(v) = {value v: $generated(s, v, space, value)}

prop spans(s nonempty_set, v nonempty_set, space &VectorSpace<s, v>):
    \carrier<s, v, space> = v

prop basis(s nonempty_set, v nonempty_set, space &VectorSpace<s, v>, value v):
    $generated(s, v, space, value)

axiom spanning_value_gives_basis:
    ? forall s nonempty_set, v nonempty_set, space &VectorSpace<s, v>:
        $spans(s, v, space)
        =>:
            exist value v st {$basis(s, v, space, value)}

thm obtain_basis_without_reentering_space_membership:
    ? forall s nonempty_set, v nonempty_set, space &VectorSpace<s, v>:
        $spans(s, v, space)
        =>:
            exist selected v st {$basis(s, v, space, selected)}
    by def:
        ? $spans(s, v, space)
    by thm spanning_value_gives_basis(s, v, space)
    obtain value from exist value v st {$basis(s, v, space, value)}
    witness exist selected v st {$basis(s, v, space, selected)} from value
"#,
    );

    let output = Command::new(litex_binary())
        .args(["-compact", "-f", path_string(&source).as_str()])
        .output()
        .expect("run Litex reentrant well-definedness fixture");
    assert!(
        output.status.success(),
        "reentrant well-definedness fixture failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn normal_predicate_parameter_inference_registers_struct_function_fields() {
    // A same-fact DFS guard must not turn inference into a global one-layer
    // pass: inferring `idem` still has to expand `h ∈ &HasOp<s>` far enough
    // to register the callable `h.op` field.
    let fixture = Fixture::new("normal-predicate-struct-fields");
    let source = fixture.path("main.lit");
    write_file(
        &fixture.path("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(
        &source,
        r#"struct HasOp<s set>:
    zero s
    op fn(x, y s) s

prop idem(s set, h &HasOp<s>):
    h.op(h.zero, h.zero) = h.zero

have h set
trust $idem(R, h)
h.op(h.zero, h.zero) = h.zero
"#,
    );

    let output = Command::new(litex_binary())
        .args(["-compact", "-f", path_string(&source).as_str()])
        .output()
        .expect("run Litex normal-predicate struct-field fixture");
    assert!(
        output.status.success(),
        "normal predicate parameter inference fixture failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

fn litex_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_litex") {
        return PathBuf::from(path);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/release/litex")
}

fn path_string(path: &Path) -> String {
    fs::canonicalize(path)
        .expect("fixture path should exist")
        .to_str()
        .expect("fixture path should be UTF-8")
        .to_string()
}

fn write_file(path: &Path, source: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("create fixture directory");
    }
    fs::write(path, source).expect("write fixture file");
}

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn new(name: &str) -> Self {
        static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "litex-inference-reentrancy-{name}-{}-{id}",
            std::process::id()
        ));
        if root.exists() {
            fs::remove_dir_all(&root).expect("remove stale fixture");
        }
        fs::create_dir_all(&root).expect("create fixture root");
        Fixture { root }
    }

    fn path(&self, name: &str) -> PathBuf {
        self.root.join(name)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}
