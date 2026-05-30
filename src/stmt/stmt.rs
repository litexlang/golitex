use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum Stmt {
    Fact(Fact),
    DefPropStmt(DefPropStmt),
    DefAbstractPropStmt(DefAbstractPropStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveByExistStmt(HaveByExistStmt),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    HaveFnByInducStmt(HaveFnByInducStmt),
    HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt),
    DefTemplateStmt(DefTemplateStmt),
    DefLetStmt(DefLetStmt),
    DefAlgoStmt(DefAlgoStmt),
    ClaimStmt(ClaimStmt),
    KnowStmt(KnowStmt),
    ProveStmt(ProveStmt),
    ImportStmt(ImportStmt),
    DoNothingStmt(DoNothingStmt),
    ClearStmt(ClearStmt),
    StopImportStmt(StopImportStmt),
    RunFileStmt(RunFileStmt),
    EvalStmt(EvalStmt),
    WitnessExistFact(WitnessExistFact),
    WitnessNonemptySet(WitnessNonemptySet),
    ByCasesStmt(ByCasesStmt),
    ByContraStmt(ByContraStmt),
    ByEnumerateFiniteSetStmt(ByEnumerateFiniteSetStmt),
    ByInducStmt(ByInducStmt),
    ByForStmt(ByForStmt),
    ByExtensionStmt(ByExtensionStmt),
    ByFnAsSetStmt(ByFnAsSetStmt),
    ByTupleAsSetStmt(ByTupleAsSetStmt),
    ByFnSetAsSetStmt(ByFnSetAsSetStmt),
    ByEnumerateRangeStmt(ByEnumerateRangeStmt),
    ByClosedRangeAsCasesStmt(ByClosedRangeAsCasesStmt),
    ByTransitivePropStmt(ByTransitivePropStmt),
    BySymmetricPropStmt(BySymmetricPropStmt),
    ByReflexivePropStmt(ByReflexivePropStmt),
    ByAntisymmetricPropStmt(ByAntisymmetricPropStmt),
    ByThmStmt(ByThmStmt),
    DefThmStmt(DefThmStmt),
    UseStrategyStmt(UseStrategyStmt),
    StopStrategyStmt(StopStrategyStmt),
    DefStrategyStmt(DefStrategyStmt),
    DefStructStmt(DefStructStmt),
    EvalByStmt(EvalByStmt),
}

#[derive(Clone)]
pub struct UseStrategyStmt {
    pub name: AtomicName,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct StopStrategyStmt {
    pub name: AtomicName,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefStrategyStmt {
    pub names: Vec<String>,
    pub forall_fact: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

impl UseStrategyStmt {
    pub fn new(name: AtomicName, line_file: LineFile) -> Self {
        UseStrategyStmt { name, line_file }
    }
}

impl fmt::Display for UseStrategyStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", USE, STRATEGY, self.name)
    }
}

impl StopStrategyStmt {
    pub fn new(name: AtomicName, line_file: LineFile) -> Self {
        StopStrategyStmt { name, line_file }
    }
}

impl fmt::Display for StopStrategyStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", STOP, STRATEGY, self.name)
    }
}

impl DefStrategyStmt {
    pub fn new(
        names: Vec<String>,
        forall_fact: ForallFact,
        prove_process: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        DefStrategyStmt {
            names,
            forall_fact,
            prove_process,
            line_file,
        }
    }
}

impl fmt::Display for DefStrategyStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}\n{}{}\n{}",
            STRATEGY,
            vec_to_string_with_sep(&self.names, ", ".to_string()),
            COLON,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &self.forall_fact.to_string(),
                2
            )
        )?;
        if !self.prove_process.is_empty() {
            write!(
                f,
                "\n{}",
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.prove_process, 1)
            )?;
        }
        Ok(())
    }
}

#[derive(Clone)]
pub struct ByThmStmt {
    pub name: AtomicName,
    pub args: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefThmStmt {
    pub names: Vec<String>,
    pub forall_fact: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ByThmStmt {
    pub fn new(name: AtomicName, args: Vec<Obj>, line_file: LineFile) -> Self {
        ByThmStmt {
            name,
            args,
            line_file,
        }
    }
}

impl fmt::Display for ByThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{}",
            BY,
            THM,
            self.name,
            braced_vec_to_string(&self.args)
        )
    }
}

impl DefThmStmt {
    pub fn new(
        names: Vec<String>,
        forall_fact: ForallFact,
        prove_process: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        DefThmStmt {
            names,
            forall_fact,
            prove_process,
            line_file,
        }
    }
}

impl fmt::Display for DefThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}\n{}{}\n{}",
            THM,
            vec_to_string_with_sep(&self.names, ", ".to_string()),
            COLON,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &self.forall_fact.to_string(),
                2
            )
        )?;
        if !self.prove_process.is_empty() {
            write!(
                f,
                "\n{}",
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.prove_process, 1)
            )?;
        }
        Ok(())
    }
}

#[derive(Clone)]
pub struct EvalByStmt {
    pub lhs: Obj,
    pub rhs: Obj,
    pub line_file: LineFile,
}

impl EvalByStmt {
    pub fn new(lhs: Obj, rhs: Obj, line_file: LineFile) -> Self {
        EvalByStmt {
            lhs,
            rhs,
            line_file,
        }
    }
}

impl fmt::Display for EvalByStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", EVAL, self.lhs, FROM, self.rhs)
    }
}

#[derive(Clone)]
pub struct DefStructStmt {
    pub name: String,
    pub param_def_with_dom: Option<(ParamDefWithType, Vec<OrAndChainAtomicFact>)>,
    pub fields: Vec<(String, Obj)>,
    pub equivalent_facts: Vec<Fact>,
    pub line_file: LineFile,
}

impl DefStructStmt {
    pub fn new(
        name: String,
        param_def_with_dom: Option<(ParamDefWithType, Vec<OrAndChainAtomicFact>)>,
        fields: Vec<(String, Obj)>,
        equivalent_facts: Vec<Fact>,
        line_file: LineFile,
    ) -> Self {
        DefStructStmt {
            name,
            param_def_with_dom,
            fields,
            equivalent_facts,
            line_file,
        }
    }

    pub fn stmt_type_name(&self) -> String {
        "DefStructStmt".to_string()
    }
}

impl fmt::Display for DefStructStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params = match &self.param_def_with_dom {
            Some((param_def, _)) => format!("{}", param_def),
            None => String::new(),
        };
        if params.is_empty() {
            write!(f, "{} {}{}", STRUCT, self.name, COLON)
        } else {
            write!(
                f,
                "{} {}{}{}{}{}",
                STRUCT, self.name, LEFT_BRACE, params, RIGHT_BRACE, COLON
            )
        }
    }
}

#[derive(Clone)]
pub struct ByClosedRangeAsCasesStmt {
    pub element: Obj,
    pub closed_range: ClosedRange,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct ByEnumerateRangeStmt {
    pub element: Obj,
    pub range: ClosedRangeOrRange,
    pub line_file: LineFile,
}

impl fmt::Display for ByEnumerateRangeStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let keyword = match &self.range {
            ClosedRangeOrRange::ClosedRange(_) => CLOSED_RANGE,
            ClosedRangeOrRange::Range(_) => RANGE,
        };
        write!(
            f,
            "{} {} {}{} {} {}{} {}",
            BY, ENUMERATE, keyword, COLON, self.element, FACT_PREFIX, IN, self.range
        )
    }
}

impl ByEnumerateRangeStmt {
    pub fn new(element: Obj, range: ClosedRangeOrRange, line_file: LineFile) -> Self {
        ByEnumerateRangeStmt {
            element,
            range,
            line_file,
        }
    }
}

impl fmt::Display for ByClosedRangeAsCasesStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {}{} {} {}{} {}",
            BY,
            CLOSED_RANGE,
            AS,
            CASES,
            COLON,
            self.element,
            FACT_PREFIX,
            IN,
            Obj::ClosedRange(self.closed_range.clone())
        )
    }
}

impl ByClosedRangeAsCasesStmt {
    pub fn new(element: Obj, closed_range: ClosedRange, line_file: LineFile) -> Self {
        ByClosedRangeAsCasesStmt {
            element,
            closed_range,
            line_file,
        }
    }
}

impl fmt::Debug for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Fact(x) => write!(f, "{}", x),
            Stmt::DefLetStmt(x) => write!(f, "{}", x),
            Stmt::DefPropStmt(x) => write!(f, "{}", x),
            Stmt::DefAbstractPropStmt(x) => write!(f, "{}", x),
            Stmt::HaveObjInNonemptySetStmt(x) => write!(f, "{}", x),
            Stmt::HaveObjEqualStmt(x) => write!(f, "{}", x),
            Stmt::HaveByExistStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnEqualStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnEqualCaseByCaseStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnByInducStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnByForallExistUniqueStmt(x) => write!(f, "{}", x),
            Stmt::DefTemplateStmt(x) => write!(f, "{}", x),
            Stmt::DefAlgoStmt(x) => write!(f, "{}", x),
            Stmt::ClaimStmt(x) => write!(f, "{}", x),
            Stmt::KnowStmt(x) => write!(f, "{}", x),
            Stmt::ProveStmt(x) => write!(f, "{}", x),
            Stmt::ImportStmt(x) => write!(f, "{}", x),
            Stmt::DoNothingStmt(x) => write!(f, "{}", x),
            Stmt::ClearStmt(x) => write!(f, "{}", x),
            Stmt::StopImportStmt(x) => write!(f, "{}", x),
            Stmt::RunFileStmt(x) => write!(f, "{}", x),
            Stmt::EvalStmt(x) => write!(f, "{}", x),
            Stmt::EvalByStmt(x) => write!(f, "{}", x),
            Stmt::WitnessExistFact(x) => write!(f, "{}", x),
            Stmt::WitnessNonemptySet(x) => write!(f, "{}", x),
            Stmt::ByCasesStmt(x) => write!(f, "{}", x),
            Stmt::ByContraStmt(x) => write!(f, "{}", x),
            Stmt::ByEnumerateFiniteSetStmt(x) => write!(f, "{}", x),
            Stmt::ByInducStmt(x) => write!(f, "{}", x),
            Stmt::ByForStmt(x) => write!(f, "{}", x),
            Stmt::ByExtensionStmt(x) => write!(f, "{}", x),
            Stmt::ByFnAsSetStmt(x) => write!(f, "{}", x),
            Stmt::ByTupleAsSetStmt(x) => write!(f, "{}", x),
            Stmt::ByFnSetAsSetStmt(x) => write!(f, "{}", x),
            Stmt::ByEnumerateRangeStmt(x) => write!(f, "{}", x),
            Stmt::ByClosedRangeAsCasesStmt(x) => write!(f, "{}", x),
            Stmt::ByTransitivePropStmt(x) => write!(f, "{}", x),
            Stmt::BySymmetricPropStmt(x) => write!(f, "{}", x),
            Stmt::ByReflexivePropStmt(x) => write!(f, "{}", x),
            Stmt::ByAntisymmetricPropStmt(x) => write!(f, "{}", x),
            Stmt::ByThmStmt(x) => write!(f, "{}", x),
            Stmt::DefThmStmt(x) => write!(f, "{}", x),
            Stmt::UseStrategyStmt(x) => write!(f, "{}", x),
            Stmt::StopStrategyStmt(x) => write!(f, "{}", x),
            Stmt::DefStrategyStmt(x) => write!(f, "{}", x),
            Stmt::DefStructStmt(x) => write!(f, "{}", x),
        }
    }
}

impl Stmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            Stmt::Fact(fact) => fact.line_file(),
            Stmt::DefLetStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefPropStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefAbstractPropStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveObjInNonemptySetStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveObjEqualStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveByExistStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveFnEqualStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveFnByInducStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveFnByForallExistUniqueStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefTemplateStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefAlgoStmt(stmt) => stmt.line_file.clone(),
            Stmt::ClaimStmt(stmt) => stmt.line_file.clone(),
            Stmt::KnowStmt(stmt) => stmt.line_file.clone(),
            Stmt::ProveStmt(stmt) => stmt.line_file.clone(),
            Stmt::ImportStmt(stmt) => stmt.line_file(),
            Stmt::DoNothingStmt(stmt) => stmt.line_file.clone(),
            Stmt::ClearStmt(stmt) => stmt.line_file.clone(),
            Stmt::StopImportStmt(stmt) => stmt.line_file.clone(),
            Stmt::RunFileStmt(stmt) => stmt.line_file.clone(),
            Stmt::EvalStmt(stmt) => stmt.line_file.clone(),
            Stmt::EvalByStmt(stmt) => stmt.line_file.clone(),
            Stmt::WitnessExistFact(stmt) => stmt.line_file.clone(),
            Stmt::WitnessNonemptySet(stmt) => stmt.line_file.clone(),
            Stmt::ByCasesStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByContraStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByEnumerateFiniteSetStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByInducStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByForStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByExtensionStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByFnAsSetStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByTupleAsSetStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByFnSetAsSetStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByEnumerateRangeStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByClosedRangeAsCasesStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByTransitivePropStmt(stmt) => stmt.line_file.clone(),
            Stmt::BySymmetricPropStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByReflexivePropStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByAntisymmetricPropStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByThmStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefThmStmt(stmt) => stmt.line_file.clone(),
            Stmt::UseStrategyStmt(stmt) => stmt.line_file.clone(),
            Stmt::StopStrategyStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefStrategyStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefStructStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            Stmt::Fact(f) => f.fact_type_string(),
            Stmt::DefLetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefPropStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefAbstractPropStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveObjInNonemptySetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveObjEqualStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveByExistStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveFnEqualStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveFnByInducStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveFnByForallExistUniqueStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefTemplateStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefAlgoStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ClaimStmt(stmt) => stmt.stmt_type_name(),
            Stmt::KnowStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ProveStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ImportStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DoNothingStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ClearStmt(stmt) => stmt.stmt_type_name(),
            Stmt::StopImportStmt(stmt) => stmt.stmt_type_name(),
            Stmt::RunFileStmt(stmt) => stmt.stmt_type_name(),
            Stmt::EvalStmt(stmt) => stmt.stmt_type_name(),
            Stmt::EvalByStmt(stmt) => stmt.stmt_type_name(),
            Stmt::WitnessExistFact(stmt) => stmt.stmt_type_name(),
            Stmt::WitnessNonemptySet(stmt) => stmt.stmt_type_name(),
            Stmt::ByCasesStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByContraStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByEnumerateFiniteSetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByInducStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByForStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByExtensionStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByFnAsSetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByTupleAsSetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByFnSetAsSetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByEnumerateRangeStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByClosedRangeAsCasesStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByTransitivePropStmt(stmt) => stmt.stmt_type_name(),
            Stmt::BySymmetricPropStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByReflexivePropStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByAntisymmetricPropStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByThmStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefThmStmt(stmt) => stmt.stmt_type_name(),
            Stmt::UseStrategyStmt(stmt) => stmt.stmt_type_name(),
            Stmt::StopStrategyStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefStrategyStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefStructStmt(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl From<Fact> for Stmt {
    fn from(v: Fact) -> Self {
        Stmt::Fact(v)
    }
}

impl From<DefLetStmt> for Stmt {
    fn from(v: DefLetStmt) -> Self {
        Stmt::DefLetStmt(v)
    }
}

impl From<DefPropStmt> for Stmt {
    fn from(v: DefPropStmt) -> Self {
        Stmt::DefPropStmt(v)
    }
}

impl From<DefAbstractPropStmt> for Stmt {
    fn from(v: DefAbstractPropStmt) -> Self {
        Stmt::DefAbstractPropStmt(v)
    }
}

impl From<HaveObjInNonemptySetOrParamTypeStmt> for Stmt {
    fn from(v: HaveObjInNonemptySetOrParamTypeStmt) -> Self {
        Stmt::HaveObjInNonemptySetStmt(v)
    }
}

impl From<HaveObjEqualStmt> for Stmt {
    fn from(v: HaveObjEqualStmt) -> Self {
        Stmt::HaveObjEqualStmt(v)
    }
}

impl From<HaveByExistStmt> for Stmt {
    fn from(v: HaveByExistStmt) -> Self {
        Stmt::HaveByExistStmt(v)
    }
}

impl From<HaveFnEqualStmt> for Stmt {
    fn from(v: HaveFnEqualStmt) -> Self {
        Stmt::HaveFnEqualStmt(v)
    }
}

impl From<HaveFnEqualCaseByCaseStmt> for Stmt {
    fn from(v: HaveFnEqualCaseByCaseStmt) -> Self {
        Stmt::HaveFnEqualCaseByCaseStmt(v)
    }
}

impl From<HaveFnByInducStmt> for Stmt {
    fn from(v: HaveFnByInducStmt) -> Self {
        Stmt::HaveFnByInducStmt(v)
    }
}

impl From<HaveFnByForallExistUniqueStmt> for Stmt {
    fn from(v: HaveFnByForallExistUniqueStmt) -> Self {
        Stmt::HaveFnByForallExistUniqueStmt(v)
    }
}

impl From<DefTemplateStmt> for Stmt {
    fn from(v: DefTemplateStmt) -> Self {
        Stmt::DefTemplateStmt(v)
    }
}

impl From<DefAlgoStmt> for Stmt {
    fn from(v: DefAlgoStmt) -> Self {
        Stmt::DefAlgoStmt(v)
    }
}

impl From<ClaimStmt> for Stmt {
    fn from(v: ClaimStmt) -> Self {
        Stmt::ClaimStmt(v)
    }
}

impl From<KnowStmt> for Stmt {
    fn from(v: KnowStmt) -> Self {
        Stmt::KnowStmt(v)
    }
}

impl From<ProveStmt> for Stmt {
    fn from(v: ProveStmt) -> Self {
        Stmt::ProveStmt(v)
    }
}

impl From<ImportStmt> for Stmt {
    fn from(v: ImportStmt) -> Self {
        Stmt::ImportStmt(v)
    }
}

impl From<DoNothingStmt> for Stmt {
    fn from(v: DoNothingStmt) -> Self {
        Stmt::DoNothingStmt(v)
    }
}

impl From<ClearStmt> for Stmt {
    fn from(v: ClearStmt) -> Self {
        Stmt::ClearStmt(v)
    }
}

impl From<StopImportStmt> for Stmt {
    fn from(v: StopImportStmt) -> Self {
        Stmt::StopImportStmt(v)
    }
}

impl From<RunFileStmt> for Stmt {
    fn from(v: RunFileStmt) -> Self {
        Stmt::RunFileStmt(v)
    }
}

impl From<EvalStmt> for Stmt {
    fn from(v: EvalStmt) -> Self {
        Stmt::EvalStmt(v)
    }
}

impl From<EvalByStmt> for Stmt {
    fn from(v: EvalByStmt) -> Self {
        Stmt::EvalByStmt(v)
    }
}

impl From<WitnessExistFact> for Stmt {
    fn from(v: WitnessExistFact) -> Self {
        Stmt::WitnessExistFact(v)
    }
}

impl From<WitnessNonemptySet> for Stmt {
    fn from(v: WitnessNonemptySet) -> Self {
        Stmt::WitnessNonemptySet(v)
    }
}

impl From<ByCasesStmt> for Stmt {
    fn from(v: ByCasesStmt) -> Self {
        Stmt::ByCasesStmt(v)
    }
}

impl From<ByContraStmt> for Stmt {
    fn from(v: ByContraStmt) -> Self {
        Stmt::ByContraStmt(v)
    }
}

impl From<ByEnumerateFiniteSetStmt> for Stmt {
    fn from(v: ByEnumerateFiniteSetStmt) -> Self {
        Stmt::ByEnumerateFiniteSetStmt(v)
    }
}

impl From<ByInducStmt> for Stmt {
    fn from(v: ByInducStmt) -> Self {
        Stmt::ByInducStmt(v)
    }
}

impl From<ByForStmt> for Stmt {
    fn from(v: ByForStmt) -> Self {
        Stmt::ByForStmt(v)
    }
}

impl From<ByExtensionStmt> for Stmt {
    fn from(v: ByExtensionStmt) -> Self {
        Stmt::ByExtensionStmt(v)
    }
}

impl From<ByFnAsSetStmt> for Stmt {
    fn from(v: ByFnAsSetStmt) -> Self {
        Stmt::ByFnAsSetStmt(v)
    }
}

impl From<ByTupleAsSetStmt> for Stmt {
    fn from(v: ByTupleAsSetStmt) -> Self {
        Stmt::ByTupleAsSetStmt(v)
    }
}

impl From<ByFnSetAsSetStmt> for Stmt {
    fn from(v: ByFnSetAsSetStmt) -> Self {
        Stmt::ByFnSetAsSetStmt(v)
    }
}

impl From<ByEnumerateRangeStmt> for Stmt {
    fn from(v: ByEnumerateRangeStmt) -> Self {
        Stmt::ByEnumerateRangeStmt(v)
    }
}

impl From<ByClosedRangeAsCasesStmt> for Stmt {
    fn from(v: ByClosedRangeAsCasesStmt) -> Self {
        Stmt::ByClosedRangeAsCasesStmt(v)
    }
}

impl From<ByTransitivePropStmt> for Stmt {
    fn from(v: ByTransitivePropStmt) -> Self {
        Stmt::ByTransitivePropStmt(v)
    }
}

impl From<BySymmetricPropStmt> for Stmt {
    fn from(v: BySymmetricPropStmt) -> Self {
        Stmt::BySymmetricPropStmt(v)
    }
}

impl From<ByReflexivePropStmt> for Stmt {
    fn from(v: ByReflexivePropStmt) -> Self {
        Stmt::ByReflexivePropStmt(v)
    }
}

impl From<ByAntisymmetricPropStmt> for Stmt {
    fn from(v: ByAntisymmetricPropStmt) -> Self {
        Stmt::ByAntisymmetricPropStmt(v)
    }
}

impl From<ByThmStmt> for Stmt {
    fn from(v: ByThmStmt) -> Self {
        Stmt::ByThmStmt(v)
    }
}

impl From<DefThmStmt> for Stmt {
    fn from(v: DefThmStmt) -> Self {
        Stmt::DefThmStmt(v)
    }
}

impl From<UseStrategyStmt> for Stmt {
    fn from(v: UseStrategyStmt) -> Self {
        Stmt::UseStrategyStmt(v)
    }
}

impl From<StopStrategyStmt> for Stmt {
    fn from(v: StopStrategyStmt) -> Self {
        Stmt::StopStrategyStmt(v)
    }
}

impl From<DefStrategyStmt> for Stmt {
    fn from(v: DefStrategyStmt) -> Self {
        Stmt::DefStrategyStmt(v)
    }
}

impl From<DefStructStmt> for Stmt {
    fn from(v: DefStructStmt) -> Self {
        Stmt::DefStructStmt(v)
    }
}
