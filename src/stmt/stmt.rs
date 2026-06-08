use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum Stmt {
    Fact(Fact),
    UnsafeStmt(UnsafeStmt),
    DefObjStmt(DefObjStmt),
    DefInterfaceStmt(DefInterfaceStmt),
    By(ByStmt),
    Witness(WitnessStmt),
    ProofBlock(ProofBlockStmt),
    Command(CommandStmt),
}

#[derive(Clone)]
pub enum UnsafeStmt {
    KnowStmt(KnowStmt),
    DefLetStmt(DefLetStmt),
}

#[derive(Clone)]
pub enum DefObjStmt {
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveObjByExistFactsStmt(HaveObjByExistFactsStmt),
    HaveByExistStmt(HaveByExistStmt),
    HaveByPreimageStmt(HaveByPreimageStmt),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    HaveFnByInducStmt(HaveFnByInducStmt),
    HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt),
}

#[derive(Clone)]
pub enum DefInterfaceStmt {
    DefPropStmt(DefPropStmt),
    DefAbstractPropStmt(DefAbstractPropStmt),
    AliasPropStmt(AliasPropStmt),
    AliasThmStmt(AliasThmStmt),
    DefTemplateStmt(DefTemplateStmt),
    DefAlgoStmt(DefAlgoStmt),
    DefThmStmt(DefThmStmt),
    DefStrategyStmt(DefStrategyStmt),
    DefStructStmt(DefStructStmt),
}

#[derive(Clone)]
pub enum ByStmt {
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
    ByZornLemmaStmt(ByZornLemmaStmt),
    ByAxiomOfChoiceStmt(ByAxiomOfChoiceStmt),
    ByThmStmt(ByThmStmt),
}

#[derive(Clone)]
pub enum WitnessStmt {
    WitnessExistFact(WitnessExistFact),
    WitnessNonemptySet(WitnessNonemptySet),
}

#[derive(Clone)]
pub enum ProofBlockStmt {
    ClaimStmt(ClaimStmt),
    SketchStmt(SketchStmt),
}

#[derive(Clone)]
pub enum CommandStmt {
    ImportStmt(ImportStmt),
    DoNothingStmt(DoNothingStmt),
    ClearStmt(ClearStmt),
    StopImportStmt(StopImportStmt),
    RunFileStmt(RunFileStmt),
    EvalStmt(EvalStmt),
    EvalByStmt(EvalByStmt),
    UseStrategyStmt(UseStrategyStmt),
    StopStrategyStmt(StopStrategyStmt),
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
                STRUCT, self.name, LESS, params, GREATER, COLON
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
            Stmt::UnsafeStmt(x) => write!(f, "{}", x),
            Stmt::DefObjStmt(x) => write!(f, "{}", x),
            Stmt::DefInterfaceStmt(x) => write!(f, "{}", x),
            Stmt::By(x) => write!(f, "{}", x),
            Stmt::Witness(x) => write!(f, "{}", x),
            Stmt::ProofBlock(x) => write!(f, "{}", x),
            Stmt::Command(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for UnsafeStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnsafeStmt::KnowStmt(x) => write!(f, "{}", x),
            UnsafeStmt::DefLetStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for DefObjStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefObjStmt::HaveObjInNonemptySetStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveObjEqualStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveObjByExistFactsStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveByExistStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveByPreimageStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveFnEqualStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveFnEqualCaseByCaseStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveFnByInducStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveFnByForallExistUniqueStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for DefInterfaceStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefInterfaceStmt::DefPropStmt(x) => write!(f, "{}", x),
            DefInterfaceStmt::DefAbstractPropStmt(x) => write!(f, "{}", x),
            DefInterfaceStmt::AliasPropStmt(x) => write!(f, "{}", x),
            DefInterfaceStmt::AliasThmStmt(x) => write!(f, "{}", x),
            DefInterfaceStmt::DefTemplateStmt(x) => write!(f, "{}", x),
            DefInterfaceStmt::DefAlgoStmt(x) => write!(f, "{}", x),
            DefInterfaceStmt::DefThmStmt(x) => write!(f, "{}", x),
            DefInterfaceStmt::DefStrategyStmt(x) => write!(f, "{}", x),
            DefInterfaceStmt::DefStructStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for ByStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ByStmt::ByCasesStmt(x) => write!(f, "{}", x),
            ByStmt::ByContraStmt(x) => write!(f, "{}", x),
            ByStmt::ByEnumerateFiniteSetStmt(x) => write!(f, "{}", x),
            ByStmt::ByInducStmt(x) => write!(f, "{}", x),
            ByStmt::ByForStmt(x) => write!(f, "{}", x),
            ByStmt::ByExtensionStmt(x) => write!(f, "{}", x),
            ByStmt::ByFnAsSetStmt(x) => write!(f, "{}", x),
            ByStmt::ByTupleAsSetStmt(x) => write!(f, "{}", x),
            ByStmt::ByFnSetAsSetStmt(x) => write!(f, "{}", x),
            ByStmt::ByEnumerateRangeStmt(x) => write!(f, "{}", x),
            ByStmt::ByClosedRangeAsCasesStmt(x) => write!(f, "{}", x),
            ByStmt::ByTransitivePropStmt(x) => write!(f, "{}", x),
            ByStmt::BySymmetricPropStmt(x) => write!(f, "{}", x),
            ByStmt::ByReflexivePropStmt(x) => write!(f, "{}", x),
            ByStmt::ByAntisymmetricPropStmt(x) => write!(f, "{}", x),
            ByStmt::ByZornLemmaStmt(x) => write!(f, "{}", x),
            ByStmt::ByAxiomOfChoiceStmt(x) => write!(f, "{}", x),
            ByStmt::ByThmStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for WitnessStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WitnessStmt::WitnessExistFact(x) => write!(f, "{}", x),
            WitnessStmt::WitnessNonemptySet(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for ProofBlockStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofBlockStmt::ClaimStmt(x) => write!(f, "{}", x),
            ProofBlockStmt::SketchStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for CommandStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CommandStmt::ImportStmt(x) => write!(f, "{}", x),
            CommandStmt::DoNothingStmt(x) => write!(f, "{}", x),
            CommandStmt::ClearStmt(x) => write!(f, "{}", x),
            CommandStmt::StopImportStmt(x) => write!(f, "{}", x),
            CommandStmt::RunFileStmt(x) => write!(f, "{}", x),
            CommandStmt::EvalStmt(x) => write!(f, "{}", x),
            CommandStmt::EvalByStmt(x) => write!(f, "{}", x),
            CommandStmt::UseStrategyStmt(x) => write!(f, "{}", x),
            CommandStmt::StopStrategyStmt(x) => write!(f, "{}", x),
        }
    }
}

impl Stmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            Stmt::Fact(fact) => fact.line_file(),
            Stmt::UnsafeStmt(stmt) => stmt.line_file(),
            Stmt::DefObjStmt(stmt) => stmt.line_file(),
            Stmt::DefInterfaceStmt(stmt) => stmt.line_file(),
            Stmt::By(stmt) => stmt.line_file(),
            Stmt::Witness(stmt) => stmt.line_file(),
            Stmt::ProofBlock(stmt) => stmt.line_file(),
            Stmt::Command(stmt) => stmt.line_file(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            Stmt::Fact(fact) => fact.fact_type_string(),
            Stmt::UnsafeStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefObjStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefInterfaceStmt(stmt) => stmt.stmt_type_name(),
            Stmt::By(stmt) => stmt.stmt_type_name(),
            Stmt::Witness(stmt) => stmt.stmt_type_name(),
            Stmt::ProofBlock(stmt) => stmt.stmt_type_name(),
            Stmt::Command(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl UnsafeStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            UnsafeStmt::KnowStmt(stmt) => stmt.line_file.clone(),
            UnsafeStmt::DefLetStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            UnsafeStmt::KnowStmt(stmt) => stmt.stmt_type_name(),
            UnsafeStmt::DefLetStmt(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl DefObjStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            DefObjStmt::HaveObjInNonemptySetStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveObjEqualStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveObjByExistFactsStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveByExistStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveByPreimageStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveFnEqualStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveFnByInducStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveFnByForallExistUniqueStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            DefObjStmt::HaveObjInNonemptySetStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveObjEqualStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveObjByExistFactsStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveByExistStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveByPreimageStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveFnEqualStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveFnByInducStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveFnByForallExistUniqueStmt(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl DefInterfaceStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            DefInterfaceStmt::DefPropStmt(stmt) => stmt.line_file.clone(),
            DefInterfaceStmt::DefAbstractPropStmt(stmt) => stmt.line_file.clone(),
            DefInterfaceStmt::AliasPropStmt(stmt) => stmt.line_file.clone(),
            DefInterfaceStmt::AliasThmStmt(stmt) => stmt.line_file.clone(),
            DefInterfaceStmt::DefTemplateStmt(stmt) => stmt.line_file.clone(),
            DefInterfaceStmt::DefAlgoStmt(stmt) => stmt.line_file.clone(),
            DefInterfaceStmt::DefThmStmt(stmt) => stmt.line_file.clone(),
            DefInterfaceStmt::DefStrategyStmt(stmt) => stmt.line_file.clone(),
            DefInterfaceStmt::DefStructStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            DefInterfaceStmt::DefPropStmt(stmt) => stmt.stmt_type_name(),
            DefInterfaceStmt::DefAbstractPropStmt(stmt) => stmt.stmt_type_name(),
            DefInterfaceStmt::AliasPropStmt(stmt) => stmt.stmt_type_name(),
            DefInterfaceStmt::AliasThmStmt(stmt) => stmt.stmt_type_name(),
            DefInterfaceStmt::DefTemplateStmt(stmt) => stmt.stmt_type_name(),
            DefInterfaceStmt::DefAlgoStmt(stmt) => stmt.stmt_type_name(),
            DefInterfaceStmt::DefThmStmt(stmt) => stmt.stmt_type_name(),
            DefInterfaceStmt::DefStrategyStmt(stmt) => stmt.stmt_type_name(),
            DefInterfaceStmt::DefStructStmt(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl ByStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            ByStmt::ByCasesStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByContraStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByEnumerateFiniteSetStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByInducStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByForStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByExtensionStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByFnAsSetStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByTupleAsSetStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByFnSetAsSetStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByEnumerateRangeStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByClosedRangeAsCasesStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByTransitivePropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::BySymmetricPropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByReflexivePropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByAntisymmetricPropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByZornLemmaStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByAxiomOfChoiceStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByThmStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            ByStmt::ByCasesStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByContraStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByEnumerateFiniteSetStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByInducStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByForStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByExtensionStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByFnAsSetStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByTupleAsSetStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByFnSetAsSetStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByEnumerateRangeStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByClosedRangeAsCasesStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByTransitivePropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::BySymmetricPropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByReflexivePropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByAntisymmetricPropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByZornLemmaStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByAxiomOfChoiceStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByThmStmt(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl WitnessStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            WitnessStmt::WitnessExistFact(stmt) => stmt.line_file.clone(),
            WitnessStmt::WitnessNonemptySet(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            WitnessStmt::WitnessExistFact(stmt) => stmt.stmt_type_name(),
            WitnessStmt::WitnessNonemptySet(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl ProofBlockStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            ProofBlockStmt::ClaimStmt(stmt) => stmt.line_file.clone(),
            ProofBlockStmt::SketchStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            ProofBlockStmt::ClaimStmt(stmt) => stmt.stmt_type_name(),
            ProofBlockStmt::SketchStmt(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl CommandStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            CommandStmt::ImportStmt(stmt) => stmt.line_file(),
            CommandStmt::DoNothingStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::ClearStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::StopImportStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::RunFileStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::EvalStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::EvalByStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::UseStrategyStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::StopStrategyStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            CommandStmt::ImportStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::DoNothingStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::ClearStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::StopImportStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::RunFileStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::EvalStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::EvalByStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::UseStrategyStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::StopStrategyStmt(stmt) => stmt.stmt_type_name(),
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
        UnsafeStmt::DefLetStmt(v).into()
    }
}

impl From<DefPropStmt> for Stmt {
    fn from(v: DefPropStmt) -> Self {
        DefInterfaceStmt::DefPropStmt(v).into()
    }
}

impl From<DefAbstractPropStmt> for Stmt {
    fn from(v: DefAbstractPropStmt) -> Self {
        DefInterfaceStmt::DefAbstractPropStmt(v).into()
    }
}

impl From<AliasPropStmt> for Stmt {
    fn from(v: AliasPropStmt) -> Self {
        DefInterfaceStmt::AliasPropStmt(v).into()
    }
}

impl From<AliasThmStmt> for Stmt {
    fn from(v: AliasThmStmt) -> Self {
        DefInterfaceStmt::AliasThmStmt(v).into()
    }
}

impl From<HaveObjInNonemptySetOrParamTypeStmt> for Stmt {
    fn from(v: HaveObjInNonemptySetOrParamTypeStmt) -> Self {
        DefObjStmt::HaveObjInNonemptySetStmt(v).into()
    }
}

impl From<HaveObjEqualStmt> for Stmt {
    fn from(v: HaveObjEqualStmt) -> Self {
        DefObjStmt::HaveObjEqualStmt(v).into()
    }
}

impl From<HaveObjByExistFactsStmt> for Stmt {
    fn from(v: HaveObjByExistFactsStmt) -> Self {
        DefObjStmt::HaveObjByExistFactsStmt(v).into()
    }
}

impl From<HaveByExistStmt> for Stmt {
    fn from(v: HaveByExistStmt) -> Self {
        DefObjStmt::HaveByExistStmt(v).into()
    }
}

impl From<HaveByPreimageStmt> for Stmt {
    fn from(v: HaveByPreimageStmt) -> Self {
        DefObjStmt::HaveByPreimageStmt(v).into()
    }
}

impl From<HaveFnEqualStmt> for Stmt {
    fn from(v: HaveFnEqualStmt) -> Self {
        DefObjStmt::HaveFnEqualStmt(v).into()
    }
}

impl From<HaveFnEqualCaseByCaseStmt> for Stmt {
    fn from(v: HaveFnEqualCaseByCaseStmt) -> Self {
        DefObjStmt::HaveFnEqualCaseByCaseStmt(v).into()
    }
}

impl From<HaveFnByInducStmt> for Stmt {
    fn from(v: HaveFnByInducStmt) -> Self {
        DefObjStmt::HaveFnByInducStmt(v).into()
    }
}

impl From<HaveFnByForallExistUniqueStmt> for Stmt {
    fn from(v: HaveFnByForallExistUniqueStmt) -> Self {
        DefObjStmt::HaveFnByForallExistUniqueStmt(v).into()
    }
}

impl From<DefTemplateStmt> for Stmt {
    fn from(v: DefTemplateStmt) -> Self {
        DefInterfaceStmt::DefTemplateStmt(v).into()
    }
}

impl From<DefAlgoStmt> for Stmt {
    fn from(v: DefAlgoStmt) -> Self {
        DefInterfaceStmt::DefAlgoStmt(v).into()
    }
}

impl From<ClaimStmt> for Stmt {
    fn from(v: ClaimStmt) -> Self {
        ProofBlockStmt::ClaimStmt(v).into()
    }
}

impl From<KnowStmt> for Stmt {
    fn from(v: KnowStmt) -> Self {
        UnsafeStmt::KnowStmt(v).into()
    }
}

impl From<SketchStmt> for Stmt {
    fn from(v: SketchStmt) -> Self {
        ProofBlockStmt::SketchStmt(v).into()
    }
}

impl From<ImportStmt> for Stmt {
    fn from(v: ImportStmt) -> Self {
        CommandStmt::ImportStmt(v).into()
    }
}

impl From<DoNothingStmt> for Stmt {
    fn from(v: DoNothingStmt) -> Self {
        CommandStmt::DoNothingStmt(v).into()
    }
}

impl From<ClearStmt> for Stmt {
    fn from(v: ClearStmt) -> Self {
        CommandStmt::ClearStmt(v).into()
    }
}

impl From<StopImportStmt> for Stmt {
    fn from(v: StopImportStmt) -> Self {
        CommandStmt::StopImportStmt(v).into()
    }
}

impl From<RunFileStmt> for Stmt {
    fn from(v: RunFileStmt) -> Self {
        CommandStmt::RunFileStmt(v).into()
    }
}

impl From<EvalStmt> for Stmt {
    fn from(v: EvalStmt) -> Self {
        CommandStmt::EvalStmt(v).into()
    }
}

impl From<EvalByStmt> for Stmt {
    fn from(v: EvalByStmt) -> Self {
        CommandStmt::EvalByStmt(v).into()
    }
}

impl From<WitnessExistFact> for Stmt {
    fn from(v: WitnessExistFact) -> Self {
        WitnessStmt::WitnessExistFact(v).into()
    }
}

impl From<WitnessNonemptySet> for Stmt {
    fn from(v: WitnessNonemptySet) -> Self {
        WitnessStmt::WitnessNonemptySet(v).into()
    }
}

impl From<ByCasesStmt> for Stmt {
    fn from(v: ByCasesStmt) -> Self {
        ByStmt::ByCasesStmt(v).into()
    }
}

impl From<ByContraStmt> for Stmt {
    fn from(v: ByContraStmt) -> Self {
        ByStmt::ByContraStmt(v).into()
    }
}

impl From<ByEnumerateFiniteSetStmt> for Stmt {
    fn from(v: ByEnumerateFiniteSetStmt) -> Self {
        ByStmt::ByEnumerateFiniteSetStmt(v).into()
    }
}

impl From<ByInducStmt> for Stmt {
    fn from(v: ByInducStmt) -> Self {
        ByStmt::ByInducStmt(v).into()
    }
}

impl From<ByForStmt> for Stmt {
    fn from(v: ByForStmt) -> Self {
        ByStmt::ByForStmt(v).into()
    }
}

impl From<ByExtensionStmt> for Stmt {
    fn from(v: ByExtensionStmt) -> Self {
        ByStmt::ByExtensionStmt(v).into()
    }
}

impl From<ByFnAsSetStmt> for Stmt {
    fn from(v: ByFnAsSetStmt) -> Self {
        ByStmt::ByFnAsSetStmt(v).into()
    }
}

impl From<ByTupleAsSetStmt> for Stmt {
    fn from(v: ByTupleAsSetStmt) -> Self {
        ByStmt::ByTupleAsSetStmt(v).into()
    }
}

impl From<ByFnSetAsSetStmt> for Stmt {
    fn from(v: ByFnSetAsSetStmt) -> Self {
        ByStmt::ByFnSetAsSetStmt(v).into()
    }
}

impl From<ByEnumerateRangeStmt> for Stmt {
    fn from(v: ByEnumerateRangeStmt) -> Self {
        ByStmt::ByEnumerateRangeStmt(v).into()
    }
}

impl From<ByClosedRangeAsCasesStmt> for Stmt {
    fn from(v: ByClosedRangeAsCasesStmt) -> Self {
        ByStmt::ByClosedRangeAsCasesStmt(v).into()
    }
}

impl From<ByTransitivePropStmt> for Stmt {
    fn from(v: ByTransitivePropStmt) -> Self {
        ByStmt::ByTransitivePropStmt(v).into()
    }
}

impl From<BySymmetricPropStmt> for Stmt {
    fn from(v: BySymmetricPropStmt) -> Self {
        ByStmt::BySymmetricPropStmt(v).into()
    }
}

impl From<ByReflexivePropStmt> for Stmt {
    fn from(v: ByReflexivePropStmt) -> Self {
        ByStmt::ByReflexivePropStmt(v).into()
    }
}

impl From<ByAntisymmetricPropStmt> for Stmt {
    fn from(v: ByAntisymmetricPropStmt) -> Self {
        ByStmt::ByAntisymmetricPropStmt(v).into()
    }
}

impl From<ByZornLemmaStmt> for Stmt {
    fn from(v: ByZornLemmaStmt) -> Self {
        ByStmt::ByZornLemmaStmt(v).into()
    }
}

impl From<ByAxiomOfChoiceStmt> for Stmt {
    fn from(v: ByAxiomOfChoiceStmt) -> Self {
        ByStmt::ByAxiomOfChoiceStmt(v).into()
    }
}

impl From<ByThmStmt> for Stmt {
    fn from(v: ByThmStmt) -> Self {
        ByStmt::ByThmStmt(v).into()
    }
}

impl From<DefThmStmt> for Stmt {
    fn from(v: DefThmStmt) -> Self {
        DefInterfaceStmt::DefThmStmt(v).into()
    }
}

impl From<UseStrategyStmt> for Stmt {
    fn from(v: UseStrategyStmt) -> Self {
        CommandStmt::UseStrategyStmt(v).into()
    }
}

impl From<StopStrategyStmt> for Stmt {
    fn from(v: StopStrategyStmt) -> Self {
        CommandStmt::StopStrategyStmt(v).into()
    }
}

impl From<DefStrategyStmt> for Stmt {
    fn from(v: DefStrategyStmt) -> Self {
        DefInterfaceStmt::DefStrategyStmt(v).into()
    }
}

impl From<DefStructStmt> for Stmt {
    fn from(v: DefStructStmt) -> Self {
        DefInterfaceStmt::DefStructStmt(v).into()
    }
}

impl From<DefObjStmt> for Stmt {
    fn from(v: DefObjStmt) -> Self {
        Stmt::DefObjStmt(v)
    }
}

impl From<DefInterfaceStmt> for Stmt {
    fn from(v: DefInterfaceStmt) -> Self {
        Stmt::DefInterfaceStmt(v)
    }
}

impl From<ByStmt> for Stmt {
    fn from(v: ByStmt) -> Self {
        Stmt::By(v)
    }
}

impl From<WitnessStmt> for Stmt {
    fn from(v: WitnessStmt) -> Self {
        Stmt::Witness(v)
    }
}

impl From<ProofBlockStmt> for Stmt {
    fn from(v: ProofBlockStmt) -> Self {
        Stmt::ProofBlock(v)
    }
}

impl From<CommandStmt> for Stmt {
    fn from(v: CommandStmt) -> Self {
        Stmt::Command(v)
    }
}

impl From<UnsafeStmt> for Stmt {
    fn from(v: UnsafeStmt) -> Self {
        Stmt::UnsafeStmt(v)
    }
}
