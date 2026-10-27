//! Runnable architecture illustration, not the production Litex verifier.
//!
//! Supported objects: integer literals, addition, and an explicitly unknown name
//! for a negative WD control. Actual arithmetic uses checked i128 evaluation.
//! Compact/Normal/Detailed run the same checks and publish the same fact.
//! Only Detailed constructs successful WD/derivation records.
//!
//! Build and run from the repository root:
//!   rustc --edition=2021 -O examples/result_pipeline_tracer.rs -o <task-dir>/tracer
//!   <task-dir>/tracer normal
//!
//! This does not change Runtime, Env, AST, Lean, reading, or public JSON. Its
//! explicit mode argument is a tracer input, not a proposed production owner.
//! The local fact Vec illustrates publication, not Runtime's transactional
//! scope/rollback implementation. Production integration must retain exec_stmt.
//! The closed-calculation route corresponds to current EqualFactSearchedProof::
//! ByClosedCalculation; the small Rule enum below is local to this illustration.

fn main() {
    let selected = match std::env::args().nth(1).as_deref() {
        Some("compact") => Mode::Compact,
        Some("detailed") => Mode::Detailed,
        Some("normal") | None => Mode::Normal,
        _ => {
            eprintln!("usage: tracer [compact|normal|detailed]");
            std::process::exit(2);
        }
    };
    let equality = example_equality(2);
    let mut facts = Vec::new();
    let mut counts = BuildCounts::default();
    println!("INPUT: {equality}; mode={selected:?}");
    let result = exec_equality(&equality, selected, &mut facts, &mut counts);
    println!("FINAL: {result:#?}");
    println!("COUNTS: {counts:?}");
    if let Ok(Ok(result)) = result {
        describe_result(selected, result).expect("final mode agrees with the request");
    }

    println!("\nCONTROL: ordinary proof failure");
    let rejected = exec_equality(
        &example_equality(3),
        selected,
        &mut facts,
        &mut BuildCounts::default(),
    );
    println!("{rejected:#?}");

    println!("\nCONTROL: nested WD failure");
    let undefined = Equality::new(
        Object::Add(
            Box::new(Object::Unknown("missing".into())),
            Box::new(Object::Integer(1)),
        ),
        Object::Integer(2),
    );
    println!(
        "{:#?}",
        exec_equality(
            &undefined,
            selected,
            &mut facts,
            &mut BuildCounts::default(),
        )
    );

    println!("\nCONTROL: wrong child mode during parent assembly");
    let mut control_counts = BuildCounts::default();
    let wd = verify_equality_wd(&equality, Mode::Detailed, &mut control_counts)
        .expect("control has no operational error")
        .expect("control is WD");
    let search = search_equality(&equality, Mode::Normal, &mut control_counts)
        .expect("control has no operational error")
        .expect("control equality is true");
    println!(
        "{:#?}",
        assemble_verification(Mode::Normal, wd, search, &mut control_counts)
    );
}

// One statement pipeline. Ordinary verification failure returns before storage.
fn exec_equality(
    equality: &Equality,
    mode: Mode,
    facts: &mut Vec<Equality>,
    counts: &mut BuildCounts,
) -> Result<Result<ExecSuccess, Failure>, ExecutionError> {
    let verified = match verify_equality(equality, mode, counts)? {
        Ok(result) => result,
        Err(cause) => {
            return Ok(Err(Failure::Statement {
                goal: equality.to_string(),
                cause: Box::new(cause),
            }))
        }
    };
    let result = match mode {
        Mode::Compact => {
            let _verified = verified.into_compact()?;
            let stored = store_fact(equality, mode, facts, counts).into_compact()?;
            CompactExecSuccess::new(stored).into()
        }
        Mode::Normal => {
            let verified = verified.into_normal()?;
            let stored = store_fact(equality, mode, facts, counts).into_normal()?;
            NormalExecSuccess::new(verified, stored).into()
        }
        Mode::Detailed => {
            let verified = verified.into_detailed()?;
            let stored = store_fact(equality, mode, facts, counts).into_detailed()?;
            DetailedExecSuccess::new(verified, stored, counts).into()
        }
    };
    println!("  statement assembly -> {mode:?}");
    Ok(Ok(result))
}

fn verify_equality(
    equality: &Equality,
    mode: Mode,
    counts: &mut BuildCounts,
) -> Result<Result<VerifySuccess, Failure>, ExecutionError> {
    let wd = match verify_equality_wd(equality, mode, counts)? {
        Ok(result) => result,
        Err(cause) => {
            return Ok(Err(Failure::Verification {
                goal: equality.to_string(),
                cause: Box::new(cause),
            }))
        }
    };
    let search = match search_equality(equality, mode, counts)? {
        Ok(result) => result,
        Err(failed) => return Ok(Err(failed)),
    };
    Ok(Ok(assemble_verification(mode, wd, search, counts)?))
}

// This is the mode boundary requested by the design. Extraction consumes each
// selected variant; it never projects a Detailed child into a Normal child.
fn assemble_verification(
    mode: Mode,
    wd: EqualityWdSuccess,
    search: SearchSuccess,
    counts: &mut BuildCounts,
) -> Result<VerifySuccess, ExecutionError> {
    let result = match mode {
        Mode::Compact => {
            let _wd = wd.into_compact()?;
            let _search = search.into_compact()?;
            CompactVerifySuccess::new().into()
        }
        Mode::Normal => {
            let _wd = wd.into_normal()?;
            let search = search.into_normal()?;
            // The successful WD acknowledgement has finished its job.
            // Normal retains the actual rule/context, not the WD tree.
            NormalVerifySuccess::new(search).into()
        }
        Mode::Detailed => {
            let wd = wd.into_detailed()?;
            let search = search.into_detailed()?;
            DetailedVerifySuccess::new(wd, search, counts).into()
        }
    };
    println!("  verification assembly -> {mode:?}");
    Ok(result)
}

fn verify_equality_wd(
    equality: &Equality,
    mode: Mode,
    counts: &mut BuildCounts,
) -> Result<Result<EqualityWdSuccess, Failure>, ExecutionError> {
    let left = match verify_object_wd(&equality.left, mode, counts)? {
        Ok(result) => result,
        Err(failed) => return Ok(Err(failed)),
    };
    let right = match verify_object_wd(&equality.right, mode, counts)? {
        Ok(result) => result,
        Err(failed) => return Ok(Err(failed)),
    };
    let result = match mode {
        Mode::Compact => {
            let _left = left.into_compact()?;
            let _right = right.into_compact()?;
            CompactEqualityWdSuccess::new().into()
        }
        Mode::Normal => {
            let _left = left.into_normal()?;
            let _right = right.into_normal()?;
            NormalEqualityWdSuccess::new().into()
        }
        Mode::Detailed => {
            DetailedEqualityWdSuccess::new(left.into_detailed()?, right.into_detailed()?, counts)
                .into()
        }
    };
    println!("  equality WD assembly -> {mode:?}");
    Ok(Ok(result))
}

// Children are verified before a parent is assembled. In reduced modes there
// is no Vec of successful child results waiting to be discarded afterwards.
fn verify_object_wd(
    object: &Object,
    mode: Mode,
    counts: &mut BuildCounts,
) -> Result<Result<ObjectWdSuccess, Failure>, ExecutionError> {
    counts.object_wd_checks += 1;
    let result = match object {
        Object::Integer(_) => match mode {
            Mode::Compact => CompactObjectWdSuccess::new().into(),
            Mode::Normal => NormalObjectWdSuccess::new().into(),
            Mode::Detailed => {
                DetailedObjectWdSuccess::new(object.to_string(), Vec::new(), Vec::new(), counts)
                    .into()
            }
        },
        Object::Unknown(name) => return Ok(Err(Failure::UnknownObject { name: name.clone() })),
        Object::Add(left_object, right_object) => {
            let left = match verify_object_wd(left_object, mode, counts)? {
                Ok(result) => result,
                Err(cause) => {
                    return Ok(Err(Failure::ObjectWd {
                        object: object.to_string(),
                        cause: Box::new(cause),
                    }))
                }
            };
            let right = match verify_object_wd(right_object, mode, counts)? {
                Ok(result) => result,
                Err(cause) => {
                    return Ok(Err(Failure::ObjectWd {
                        object: object.to_string(),
                        cause: Box::new(cause),
                    }))
                }
            };
            // In this deliberately restricted model every known object is an
            // integer expression. Child WD establishes both arguments are in
            // Z, hence C; unknown objects were rejected above. All modes check
            // the same two carrier premises. This is not general Litex Obj WD.
            counts.carrier_checks += 2;
            match mode {
                Mode::Compact => {
                    let _left = left.into_compact()?;
                    let _right = right.into_compact()?;
                    CompactObjectWdSuccess::new().into()
                }
                Mode::Normal => {
                    let _left = left.into_normal()?;
                    let _right = right.into_normal()?;
                    NormalObjectWdSuccess::new().into()
                }
                Mode::Detailed => DetailedObjectWdSuccess::new(
                    object.to_string(),
                    vec![left.into_detailed()?, right.into_detailed()?],
                    vec![
                        format!("{left_object} $in C"),
                        format!("{right_object} $in C"),
                    ],
                    counts,
                )
                .into(),
            }
        }
    };
    println!("  WD({object}) -> {mode:?}");
    Ok(Ok(result))
}

fn search_equality(
    equality: &Equality,
    mode: Mode,
    counts: &mut BuildCounts,
) -> Result<Result<SearchSuccess, Failure>, ExecutionError> {
    counts.equality_checks += 1;
    let left_value = evaluate(&equality.left)?;
    let right_value = evaluate(&equality.right)?;
    if left_value != right_value {
        return Ok(Err(Failure::EqualityNotEstablished {
            goal: equality.to_string(),
            left_value,
            right_value,
        }));
    }
    let result = match mode {
        Mode::Compact => CompactSearchSuccess::new().into(),
        Mode::Normal => NormalSearchSuccess::new(Rule::ClosedCalculation, Vec::new()).into(),
        Mode::Detailed => {
            DetailedSearchSuccess::new(Rule::ClosedCalculation, left_value, right_value, counts)
                .into()
        }
    };
    println!("  rule search / ClosedCalculation -> {mode:?}");
    Ok(Ok(result))
}

fn store_fact(
    equality: &Equality,
    mode: Mode,
    facts: &mut Vec<Equality>,
    counts: &mut BuildCounts,
) -> StoreSuccess {
    facts.push(equality.clone());
    counts.stores += 1;
    let fact_id = facts.len();
    let result = match mode {
        Mode::Compact => CompactStoreSuccess::new(fact_id).into(),
        Mode::Normal => NormalStoreSuccess::new(fact_id).into(),
        Mode::Detailed => DetailedStoreSuccess::new(fact_id, equality.to_string(), counts).into(),
    };
    println!("  store fact #{fact_id} -> {mode:?}");
    result
}

fn evaluate(object: &Object) -> Result<i128, ExecutionError> {
    match object {
        Object::Integer(value) => Ok(i128::from(*value)),
        Object::Add(left, right) => evaluate(left)?
            .checked_add(evaluate(right)?)
            .ok_or_else(|| ExecutionError::Unsupported("demo integer evaluator overflow".into())),
        Object::Unknown(_) => Err(ExecutionError::InternalBug(
            "evaluator received an object rejected by WD".into(),
        )),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Compact,
    Normal,
    Detailed,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Rule {
    ClosedCalculation,
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Object {
    Integer(i64),
    Add(Box<Object>, Box<Object>),
    Unknown(String),
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Equality {
    left: Object,
    right: Object,
}
#[derive(Debug, PartialEq, Eq)]
enum Failure {
    UnknownObject {
        name: String,
    },
    ObjectWd {
        object: String,
        cause: Box<Failure>,
    },
    Verification {
        goal: String,
        cause: Box<Failure>,
    },
    EqualityNotEstablished {
        goal: String,
        left_value: i128,
        right_value: i128,
    },
    Statement {
        goal: String,
        cause: Box<Failure>,
    },
}
#[derive(Debug, PartialEq, Eq)]
enum ExecutionError {
    InternalBug(String),
    Unsupported(String),
}
#[derive(Debug, Default, PartialEq, Eq)]
struct BuildCounts {
    object_wd_checks: usize,
    carrier_checks: usize,
    equality_checks: usize,
    stores: usize,
    detailed_records: usize,
}

// Success-only mode enums. Ordinary failure lives outside these enums, so an
// into_normal mismatch can never accidentally classify proof rejection as a bug.
#[derive(Debug)]
struct CompactObjectWdSuccess;
#[derive(Debug)]
struct NormalObjectWdSuccess;
#[derive(Debug)]
struct DetailedObjectWdSuccess {
    object: String,
    children: Vec<DetailedObjectWdSuccess>,
    requirements: Vec<String>,
}
#[derive(Debug)]
enum ObjectWdSuccess {
    Compact(CompactObjectWdSuccess),
    Normal(NormalObjectWdSuccess),
    Detailed(Box<DetailedObjectWdSuccess>),
}

#[derive(Debug)]
struct CompactEqualityWdSuccess;
#[derive(Debug)]
struct NormalEqualityWdSuccess;
#[derive(Debug)]
struct DetailedEqualityWdSuccess {
    left: DetailedObjectWdSuccess,
    right: DetailedObjectWdSuccess,
}
#[derive(Debug)]
enum EqualityWdSuccess {
    Compact(CompactEqualityWdSuccess),
    Normal(NormalEqualityWdSuccess),
    Detailed(Box<DetailedEqualityWdSuccess>),
}

#[derive(Debug)]
struct CompactSearchSuccess;
#[derive(Debug)]
struct NormalSearchSuccess {
    rule: Rule,
    context: Vec<usize>,
}
#[derive(Debug)]
struct DetailedSearchSuccess {
    rule: Rule,
    left_value: i128,
    right_value: i128,
}
#[derive(Debug)]
enum SearchSuccess {
    Compact(CompactSearchSuccess),
    Normal(NormalSearchSuccess),
    Detailed(Box<DetailedSearchSuccess>),
}

#[derive(Debug)]
struct CompactVerifySuccess;
#[derive(Debug)]
struct NormalVerifySuccess {
    search: NormalSearchSuccess,
}
#[derive(Debug)]
struct DetailedVerifySuccess {
    wd: DetailedEqualityWdSuccess,
    search: DetailedSearchSuccess,
}
#[derive(Debug)]
enum VerifySuccess {
    Compact(CompactVerifySuccess),
    Normal(NormalVerifySuccess),
    Detailed(Box<DetailedVerifySuccess>),
}

#[derive(Debug)]
struct CompactStoreSuccess {
    fact_id: usize,
}
#[derive(Debug)]
struct NormalStoreSuccess {
    fact_id: usize,
}
#[derive(Debug)]
struct DetailedStoreSuccess {
    fact_id: usize,
    stored_fact: String,
}
#[derive(Debug)]
enum StoreSuccess {
    Compact(CompactStoreSuccess),
    Normal(NormalStoreSuccess),
    Detailed(Box<DetailedStoreSuccess>),
}

#[derive(Debug)]
struct CompactExecSuccess {
    stored: CompactStoreSuccess,
}
#[derive(Debug)]
struct NormalExecSuccess {
    verified: NormalVerifySuccess,
    stored: NormalStoreSuccess,
}
#[derive(Debug)]
struct DetailedExecSuccess {
    verified: DetailedVerifySuccess,
    stored: DetailedStoreSuccess,
}
#[derive(Debug)]
enum ExecSuccess {
    Compact(CompactExecSuccess),
    Normal(NormalExecSuccess),
    Detailed(Box<DetailedExecSuccess>),
}

impl Equality {
    fn new(left: Object, right: Object) -> Self {
        Self { left, right }
    }
}
impl std::fmt::Display for Object {
    fn fmt(&self, out: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Integer(n) => write!(out, "{n}"),
            Self::Add(left, right) => write!(out, "({left} + {right})"),
            Self::Unknown(name) => write!(out, "{name}"),
        }
    }
}
impl std::fmt::Display for Equality {
    fn fmt(&self, out: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(out, "{} = {}", self.left, self.right)
    }
}

// Constructors and checked variant extraction follow below. They are written
// explicitly: no generic recording framework, string rule registry, or fallback.

// Generated once while authoring the tracer; ordinary Rust implementations.
impl CompactObjectWdSuccess {
    fn new() -> Self {
        Self
    }
}
impl From<CompactObjectWdSuccess> for ObjectWdSuccess {
    fn from(value: CompactObjectWdSuccess) -> Self {
        Self::Compact(value)
    }
}
impl NormalObjectWdSuccess {
    fn new() -> Self {
        Self
    }
}
impl From<NormalObjectWdSuccess> for ObjectWdSuccess {
    fn from(value: NormalObjectWdSuccess) -> Self {
        Self::Normal(value)
    }
}
impl DetailedObjectWdSuccess {
    fn new(
        object: String,
        children: Vec<DetailedObjectWdSuccess>,
        requirements: Vec<String>,
        counts: &mut BuildCounts,
    ) -> Self {
        counts.detailed_records += 1;
        Self {
            object,
            children,
            requirements,
        }
    }
}
impl From<DetailedObjectWdSuccess> for ObjectWdSuccess {
    fn from(value: DetailedObjectWdSuccess) -> Self {
        Self::Detailed(Box::new(value))
    }
}
impl ObjectWdSuccess {
    fn into_compact(self) -> Result<CompactObjectWdSuccess, ExecutionError> {
        match self {
            Self::Compact(result) => Ok(result),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "object WD: expected Compact, got Normal".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "object WD: expected Compact, got Detailed".into(),
            )),
        }
    }
    fn into_normal(self) -> Result<NormalObjectWdSuccess, ExecutionError> {
        match self {
            Self::Normal(result) => Ok(result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "object WD: expected Normal, got Compact".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "object WD: expected Normal, got Detailed".into(),
            )),
        }
    }
    fn into_detailed(self) -> Result<DetailedObjectWdSuccess, ExecutionError> {
        match self {
            Self::Detailed(result) => Ok(*result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "object WD: expected Detailed, got Compact".into(),
            )),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "object WD: expected Detailed, got Normal".into(),
            )),
        }
    }
}
impl CompactEqualityWdSuccess {
    fn new() -> Self {
        Self
    }
}
impl From<CompactEqualityWdSuccess> for EqualityWdSuccess {
    fn from(value: CompactEqualityWdSuccess) -> Self {
        Self::Compact(value)
    }
}
impl NormalEqualityWdSuccess {
    fn new() -> Self {
        Self
    }
}
impl From<NormalEqualityWdSuccess> for EqualityWdSuccess {
    fn from(value: NormalEqualityWdSuccess) -> Self {
        Self::Normal(value)
    }
}
impl DetailedEqualityWdSuccess {
    fn new(
        left: DetailedObjectWdSuccess,
        right: DetailedObjectWdSuccess,
        counts: &mut BuildCounts,
    ) -> Self {
        counts.detailed_records += 1;
        Self { left, right }
    }
}
impl From<DetailedEqualityWdSuccess> for EqualityWdSuccess {
    fn from(value: DetailedEqualityWdSuccess) -> Self {
        Self::Detailed(Box::new(value))
    }
}
impl EqualityWdSuccess {
    fn into_compact(self) -> Result<CompactEqualityWdSuccess, ExecutionError> {
        match self {
            Self::Compact(result) => Ok(result),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "equality WD: expected Compact, got Normal".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "equality WD: expected Compact, got Detailed".into(),
            )),
        }
    }
    fn into_normal(self) -> Result<NormalEqualityWdSuccess, ExecutionError> {
        match self {
            Self::Normal(result) => Ok(result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "equality WD: expected Normal, got Compact".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "equality WD: expected Normal, got Detailed".into(),
            )),
        }
    }
    fn into_detailed(self) -> Result<DetailedEqualityWdSuccess, ExecutionError> {
        match self {
            Self::Detailed(result) => Ok(*result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "equality WD: expected Detailed, got Compact".into(),
            )),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "equality WD: expected Detailed, got Normal".into(),
            )),
        }
    }
}
impl CompactSearchSuccess {
    fn new() -> Self {
        Self
    }
}
impl From<CompactSearchSuccess> for SearchSuccess {
    fn from(value: CompactSearchSuccess) -> Self {
        Self::Compact(value)
    }
}
impl NormalSearchSuccess {
    fn new(rule: Rule, context: Vec<usize>) -> Self {
        Self { rule, context }
    }
}
impl From<NormalSearchSuccess> for SearchSuccess {
    fn from(value: NormalSearchSuccess) -> Self {
        Self::Normal(value)
    }
}
impl DetailedSearchSuccess {
    fn new(rule: Rule, left_value: i128, right_value: i128, counts: &mut BuildCounts) -> Self {
        counts.detailed_records += 1;
        Self {
            rule,
            left_value,
            right_value,
        }
    }
}
impl From<DetailedSearchSuccess> for SearchSuccess {
    fn from(value: DetailedSearchSuccess) -> Self {
        Self::Detailed(Box::new(value))
    }
}
impl SearchSuccess {
    fn into_compact(self) -> Result<CompactSearchSuccess, ExecutionError> {
        match self {
            Self::Compact(result) => Ok(result),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "rule search: expected Compact, got Normal".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "rule search: expected Compact, got Detailed".into(),
            )),
        }
    }
    fn into_normal(self) -> Result<NormalSearchSuccess, ExecutionError> {
        match self {
            Self::Normal(result) => Ok(result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "rule search: expected Normal, got Compact".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "rule search: expected Normal, got Detailed".into(),
            )),
        }
    }
    fn into_detailed(self) -> Result<DetailedSearchSuccess, ExecutionError> {
        match self {
            Self::Detailed(result) => Ok(*result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "rule search: expected Detailed, got Compact".into(),
            )),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "rule search: expected Detailed, got Normal".into(),
            )),
        }
    }
}
impl CompactVerifySuccess {
    fn new() -> Self {
        Self
    }
}
impl From<CompactVerifySuccess> for VerifySuccess {
    fn from(value: CompactVerifySuccess) -> Self {
        Self::Compact(value)
    }
}
impl NormalVerifySuccess {
    fn new(search: NormalSearchSuccess) -> Self {
        Self { search }
    }
}
impl From<NormalVerifySuccess> for VerifySuccess {
    fn from(value: NormalVerifySuccess) -> Self {
        Self::Normal(value)
    }
}
impl DetailedVerifySuccess {
    fn new(
        wd: DetailedEqualityWdSuccess,
        search: DetailedSearchSuccess,
        counts: &mut BuildCounts,
    ) -> Self {
        counts.detailed_records += 1;
        Self { wd, search }
    }
}
impl From<DetailedVerifySuccess> for VerifySuccess {
    fn from(value: DetailedVerifySuccess) -> Self {
        Self::Detailed(Box::new(value))
    }
}
impl VerifySuccess {
    fn into_compact(self) -> Result<CompactVerifySuccess, ExecutionError> {
        match self {
            Self::Compact(result) => Ok(result),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "verification: expected Compact, got Normal".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "verification: expected Compact, got Detailed".into(),
            )),
        }
    }
    fn into_normal(self) -> Result<NormalVerifySuccess, ExecutionError> {
        match self {
            Self::Normal(result) => Ok(result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "verification: expected Normal, got Compact".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "verification: expected Normal, got Detailed".into(),
            )),
        }
    }
    fn into_detailed(self) -> Result<DetailedVerifySuccess, ExecutionError> {
        match self {
            Self::Detailed(result) => Ok(*result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "verification: expected Detailed, got Compact".into(),
            )),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "verification: expected Detailed, got Normal".into(),
            )),
        }
    }
}
impl CompactStoreSuccess {
    fn new(fact_id: usize) -> Self {
        Self { fact_id }
    }
}
impl From<CompactStoreSuccess> for StoreSuccess {
    fn from(value: CompactStoreSuccess) -> Self {
        Self::Compact(value)
    }
}
impl NormalStoreSuccess {
    fn new(fact_id: usize) -> Self {
        Self { fact_id }
    }
}
impl From<NormalStoreSuccess> for StoreSuccess {
    fn from(value: NormalStoreSuccess) -> Self {
        Self::Normal(value)
    }
}
impl DetailedStoreSuccess {
    fn new(fact_id: usize, stored_fact: String, counts: &mut BuildCounts) -> Self {
        counts.detailed_records += 1;
        Self {
            fact_id,
            stored_fact,
        }
    }
}
impl From<DetailedStoreSuccess> for StoreSuccess {
    fn from(value: DetailedStoreSuccess) -> Self {
        Self::Detailed(Box::new(value))
    }
}
impl StoreSuccess {
    fn into_compact(self) -> Result<CompactStoreSuccess, ExecutionError> {
        match self {
            Self::Compact(result) => Ok(result),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "storage: expected Compact, got Normal".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "storage: expected Compact, got Detailed".into(),
            )),
        }
    }
    fn into_normal(self) -> Result<NormalStoreSuccess, ExecutionError> {
        match self {
            Self::Normal(result) => Ok(result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "storage: expected Normal, got Compact".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "storage: expected Normal, got Detailed".into(),
            )),
        }
    }
    fn into_detailed(self) -> Result<DetailedStoreSuccess, ExecutionError> {
        match self {
            Self::Detailed(result) => Ok(*result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "storage: expected Detailed, got Compact".into(),
            )),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "storage: expected Detailed, got Normal".into(),
            )),
        }
    }
}
impl CompactExecSuccess {
    fn new(stored: CompactStoreSuccess) -> Self {
        Self { stored }
    }
}
impl From<CompactExecSuccess> for ExecSuccess {
    fn from(value: CompactExecSuccess) -> Self {
        Self::Compact(value)
    }
}
impl NormalExecSuccess {
    fn new(verified: NormalVerifySuccess, stored: NormalStoreSuccess) -> Self {
        Self { verified, stored }
    }
}
impl From<NormalExecSuccess> for ExecSuccess {
    fn from(value: NormalExecSuccess) -> Self {
        Self::Normal(value)
    }
}
impl DetailedExecSuccess {
    fn new(
        verified: DetailedVerifySuccess,
        stored: DetailedStoreSuccess,
        counts: &mut BuildCounts,
    ) -> Self {
        counts.detailed_records += 1;
        Self { verified, stored }
    }
}
impl From<DetailedExecSuccess> for ExecSuccess {
    fn from(value: DetailedExecSuccess) -> Self {
        Self::Detailed(Box::new(value))
    }
}
impl ExecSuccess {
    fn into_compact(self) -> Result<CompactExecSuccess, ExecutionError> {
        match self {
            Self::Compact(result) => Ok(result),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "statement: expected Compact, got Normal".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "statement: expected Compact, got Detailed".into(),
            )),
        }
    }
    fn into_normal(self) -> Result<NormalExecSuccess, ExecutionError> {
        match self {
            Self::Normal(result) => Ok(result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "statement: expected Normal, got Compact".into(),
            )),
            Self::Detailed(_) => Err(ExecutionError::InternalBug(
                "statement: expected Normal, got Detailed".into(),
            )),
        }
    }
    fn into_detailed(self) -> Result<DetailedExecSuccess, ExecutionError> {
        match self {
            Self::Detailed(result) => Ok(*result),
            Self::Compact(_) => Err(ExecutionError::InternalBug(
                "statement: expected Detailed, got Compact".into(),
            )),
            Self::Normal(_) => Err(ExecutionError::InternalBug(
                "statement: expected Detailed, got Normal".into(),
            )),
        }
    }
}

fn example_equality(right: i64) -> Equality {
    Equality::new(
        Object::Add(Box::new(Object::Integer(1)), Box::new(Object::Integer(1))),
        Object::Integer(right),
    )
}

fn describe_result(mode: Mode, result: ExecSuccess) -> Result<(), ExecutionError> {
    match mode {
        Mode::Compact => {
            let result = result.into_compact()?;
            println!("ACCEPTED: stored fact #{}", result.stored.fact_id);
        }
        Mode::Normal => {
            let result = result.into_normal()?;
            println!(
                "ACCEPTED: rule={:?}; context={:?}; stored fact #{}",
                result.verified.search.rule, result.verified.search.context, result.stored.fact_id
            );
        }
        Mode::Detailed => {
            let result = result.into_detailed()?;
            describe_detailed_wd(&result.verified.wd.left);
            describe_detailed_wd(&result.verified.wd.right);
            println!(
                "ACCEPTED: rule={:?}; values={} / {}; stored fact #{}: {}",
                result.verified.search.rule,
                result.verified.search.left_value,
                result.verified.search.right_value,
                result.stored.fact_id,
                result.stored.stored_fact
            );
        }
    }
    Ok(())
}

fn describe_detailed_wd(wd: &DetailedObjectWdSuccess) {
    println!(
        "WD RECORD: {}; requirements={:?}",
        wd.object, wd.requirements
    );
    for child in &wd.children {
        describe_detailed_wd(child);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn modes_run_identical_checks_and_store_identical_facts() {
        let equality = example_equality(2);
        for mode in [Mode::Compact, Mode::Normal, Mode::Detailed] {
            let mut facts = Vec::new();
            let mut counts = BuildCounts::default();
            let result = exec_equality(&equality, mode, &mut facts, &mut counts)
                .unwrap()
                .unwrap();
            assert_eq!(facts, vec![equality.clone()]);
            assert_eq!(counts.object_wd_checks, 4);
            assert_eq!(counts.carrier_checks, 2);
            assert_eq!(counts.equality_checks, 1);
            assert_eq!(counts.stores, 1);
            match mode {
                Mode::Compact => {
                    assert_eq!(counts.detailed_records, 0);
                    assert_eq!(result.into_compact().unwrap().stored.fact_id, 1);
                }
                Mode::Normal => {
                    assert_eq!(counts.detailed_records, 0);
                    let result = result.into_normal().unwrap();
                    assert_eq!(result.stored.fact_id, 1);
                    assert_eq!(result.verified.search.rule, Rule::ClosedCalculation);
                    assert!(result.verified.search.context.is_empty());
                }
                Mode::Detailed => {
                    assert_eq!(counts.detailed_records, 9);
                    let result = result.into_detailed().unwrap();
                    assert_eq!(result.stored.fact_id, 1);
                    assert_eq!(result.verified.wd.left.children.len(), 2);
                    assert_eq!(result.verified.wd.left.requirements, ["1 $in C", "1 $in C"]);
                    assert_eq!(result.verified.search.left_value, 2);
                    assert_eq!(result.verified.search.right_value, 2);
                }
            }
        }
    }

    #[test]
    fn false_equality_has_the_same_ordinary_failure_and_never_stores() {
        let equality = example_equality(3);
        let expected = Failure::Statement {
            goal: "(1 + 1) = 3".into(),
            cause: Box::new(Failure::EqualityNotEstablished {
                goal: "(1 + 1) = 3".into(),
                left_value: 2,
                right_value: 3,
            }),
        };
        for mode in [Mode::Compact, Mode::Normal, Mode::Detailed] {
            let mut facts = Vec::new();
            let mut counts = BuildCounts::default();
            let failed = exec_equality(&equality, mode, &mut facts, &mut counts)
                .expect("ordinary rejection is not an operational error")
                .unwrap_err();
            assert_eq!(failed, expected);
            assert!(facts.is_empty());
            assert_eq!(counts.stores, 0);
        }
    }

    #[test]
    fn nested_wd_failure_keeps_the_complete_cause_and_stops_before_search() {
        let equality = Equality::new(
            Object::Add(
                Box::new(Object::Unknown("missing".into())),
                Box::new(Object::Integer(1)),
            ),
            Object::Integer(2),
        );
        let expected = Failure::Statement {
            goal: "(missing + 1) = 2".into(),
            cause: Box::new(Failure::Verification {
                goal: "(missing + 1) = 2".into(),
                cause: Box::new(Failure::ObjectWd {
                    object: "(missing + 1)".into(),
                    cause: Box::new(Failure::UnknownObject {
                        name: "missing".into(),
                    }),
                }),
            }),
        };
        for mode in [Mode::Compact, Mode::Normal, Mode::Detailed] {
            let mut facts = Vec::new();
            let mut counts = BuildCounts::default();
            let failed = exec_equality(&equality, mode, &mut facts, &mut counts)
                .unwrap()
                .unwrap_err();
            assert_eq!(failed, expected);
            assert_eq!(counts.equality_checks, 0);
            assert_eq!(counts.stores, 0);
            assert!(facts.is_empty());
        }
    }

    #[test]
    fn parent_rejects_a_detailed_child_instead_of_converting_it() {
        let equality = example_equality(2);
        let mut counts = BuildCounts::default();
        let wd = verify_equality_wd(&equality, Mode::Detailed, &mut counts)
            .unwrap()
            .unwrap();
        let search = search_equality(&equality, Mode::Normal, &mut counts)
            .unwrap()
            .unwrap();
        let error = assemble_verification(Mode::Normal, wd, search, &mut counts).unwrap_err();
        assert_eq!(
            error,
            ExecutionError::InternalBug("equality WD: expected Normal, got Detailed".into(),)
        );
    }
}
