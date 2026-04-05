use crate::prelude::*;
use std::fmt;

// view fn set as a subset of a cartesian product set
#[derive(Clone)]
pub struct ByFnDefAxiomStmt {
    pub function: Obj,
    pub line_file: LineFile,
}

// view a cartesian product set as a set (ordered pairs)
#[derive(Clone)]
pub struct ByCartDefAxiomStmt {
    pub cart: Cart,
    pub line_file: LineFile,
}

/// Introduce facts from the built-in ordered-pair / tuple encoding (executor TBD).
#[derive(Clone)]
pub struct ByTupleStmt {
    pub obj: Obj,
    pub line_file: LineFile,
}

// prove that a set is equal to another set by proving that they are subsets of each other
#[derive(Clone)]
pub struct ByExtensionAxiomStmt {
    pub left: Obj,
    pub right: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub enum ClosedRangeOrRange {
    ClosedRange(ClosedRange),
    Range(Range),
}

// prove fact is true for a range of integers
#[derive(Clone)]
pub struct ForAxiomStmt {
    pub params: Vec<String>,
    pub param_sets: Vec<ClosedRangeOrRange>,
    pub dom_facts: Vec<AtomicFact>,
    pub then_facts: Vec<ExistOrAndChainAtomicFact>,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// prove fact is true by induction
#[derive(Clone)]
pub struct ByInducAxiomStmt {
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub param: String,
    pub induc_from: Obj,
    pub line_file: LineFile,
}

// prove fact is true for a set of values by enumeration
#[derive(Clone)]
pub struct EnumerateAxiomStmt {
    pub params: Vec<String>,
    pub param_sets: Vec<ListSet>,
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// prove fact is true case by case
#[derive(Clone)]
pub struct ByCasesAxiomStmt {
    pub cases: Vec<AndChainAtomicFact>,
    pub then_facts: Vec<Fact>,
    pub proofs: Vec<Vec<Stmt>>,
    pub impossible_facts: Vec<Option<AtomicFact>>,
    pub line_file: LineFile,
}

// prove fact is true by contradiction
#[derive(Clone)]
pub struct ByContraAxiomStmt {
    pub to_prove: AtomicFact,
    pub proof: Vec<Stmt>,
    pub impossible_fact: AtomicFact,
    pub line_file: LineFile,
}

impl EnumerateAxiomStmt {
    pub fn new(
        params: Vec<String>,
        param_sets: Vec<ListSet>,
        to_prove: Vec<ExistOrAndChainAtomicFact>,
        proof: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        EnumerateAxiomStmt {
            params,
            param_sets,
            to_prove,
            proof,
            line_file,
        }
    }

    /// Same parameters as `list { ... }` in the header; `dom_facts` empty; `then_facts` are `to_prove`.
    pub fn to_corresponding_forall_fact(&self) -> Result<Fact, String> {
        if self.params.len() != self.param_sets.len() {
            return Err(
                "by enumerate: number of params does not match number of list sets".to_string(),
            );
        }
        let mut params_def_with_type: Vec<ParamGroupWithParamType> = Vec::new();
        for (param_name, list_set_obj) in self.params.iter().zip(self.param_sets.iter()) {
            params_def_with_type.push(ParamGroupWithParamType::new(
                vec![param_name.clone()],
                ParamType::Obj(Obj::ListSet(list_set_obj.clone())),
            ));
        }
        let forall_fact = ForallFact::new(
            params_def_with_type,
            vec![],
            self.to_prove.clone(),
            self.line_file.clone(),
        );
        Ok(Fact::ForallFact(forall_fact))
    }
}

impl ByCasesAxiomStmt {
    pub fn new(
        cases: Vec<AndChainAtomicFact>,
        then_facts: Vec<Fact>,
        proofs: Vec<Vec<Stmt>>,
        impossible_facts: Vec<Option<AtomicFact>>,
        line_file: LineFile,
    ) -> Self {
        ByCasesAxiomStmt {
            cases,
            then_facts,
            proofs,
            impossible_facts,
            line_file,
        }
    }
}

impl fmt::Display for ByCasesAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let case_and_proof_of_each_case = self
            .cases
            .iter()
            .zip(self.proofs.iter())
            .zip(self.impossible_facts.iter())
            .map(|((case, proof), impossible_fact)| {
                if let Some(impossible_fact) = impossible_fact {
                    format!(
                        "{} {}{}\n{}\n{} {}",
                        add_four_spaces_at_beginning(CASE.to_string(), 1),
                        case,
                        COLON,
                        vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2),
                        add_four_spaces_at_beginning(IMPOSSIBLE.to_string(), 2),
                        &impossible_fact.to_string()
                    )
                } else {
                    format!(
                        "{} {}{}\n{}",
                        add_four_spaces_at_beginning(CASE.to_string(), 1),
                        case,
                        COLON,
                        vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2)
                    )
                }
            })
            .collect::<Vec<String>>();

        write!(
            f,
            "{} {}{}\n{}{}\n{}\n{}",
            BY,
            CASES,
            COLON,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1),
            case_and_proof_of_each_case.join("\n")
        )
    }
}

impl ByContraAxiomStmt {
    pub fn new(
        to_prove: AtomicFact,
        proof: Vec<Stmt>,
        impossible_fact: AtomicFact,
        line_file: LineFile,
    ) -> Self {
        ByContraAxiomStmt {
            to_prove,
            proof,
            impossible_fact,
            line_file,
        }
    }
}

impl fmt::Display for ByContraAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}\n{}{}\n{}",
            BY,
            CONTRA,
            COLON,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            add_four_spaces_at_beginning(self.to_prove.to_string(), 2),
        )?;
        if !self.proof.is_empty() {
            write!(
                f,
                "\n{}",
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1),
            )?;
        }
        write!(
            f,
            "\n{} {}",
            add_four_spaces_at_beginning(IMPOSSIBLE.to_string(), 1),
            &self.impossible_fact.to_string()
        )
    }
}

impl fmt::Display for EnumerateAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{}\n{}{}\n{}\n{}",
            BY,
            ENUMERATE,
            vec_pair_to_string(&self.params, &self.param_sets),
            COLON,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2),
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1),
        )
    }
}

impl ByInducAxiomStmt {
    pub fn new(
        fact: Vec<ExistOrAndChainAtomicFact>,
        param: String,
        induc_from: Obj,
        line_file: LineFile,
    ) -> Self {
        ByInducAxiomStmt {
            to_prove: fact,
            param,
            induc_from,
            line_file,
        }
    }
}

impl fmt::Display for ByInducAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {}{}\n{}",
            BY,
            INDUC,
            self.param,
            FROM,
            self.induc_from,
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1),
        )
    }
}

impl fmt::Display for ForAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let head = match self.dom_facts.len() {
            0 => format!(
                "{} {} {}{}\n{}",
                BY,
                FOR,
                vec_pair_to_string(&self.params, &self.param_sets),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1)
            ),
            _ => format!(
                "{} {} {}{}\n{}\n{}{}\n{}",
                BY,
                FOR,
                vec_pair_to_string(&self.params, &self.param_sets),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.dom_facts, 1),
                add_four_spaces_at_beginning(RIGHT_ARROW.to_string(), 1),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 2)
            ),
        };

        match self.proof.len() {
            0 => write!(f, "{}", head),
            _ => write!(
                f,
                "{}\n{}{}\n{}",
                head,
                add_four_spaces_at_beginning(PROVE.to_string(), 1),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2)
            ),
        }
    }
}

impl ForAxiomStmt {
    pub fn to_corresponding_forall_fact(&self) -> Result<Fact, String> {
        if self.params.len() != self.param_sets.len() {
            return Err("by for: number of params does not match number of param sets".to_string());
        }
        let mut params_def_with_type: Vec<ParamGroupWithParamType> = Vec::new();
        for (param_name, param_set) in self.params.iter().zip(self.param_sets.iter()) {
            let param_set_as_obj = match param_set {
                ClosedRangeOrRange::ClosedRange(closed_range) => {
                    Obj::ClosedRange(closed_range.clone())
                }
                ClosedRangeOrRange::Range(range) => Obj::Range(range.clone()),
            };
            params_def_with_type.push(ParamGroupWithParamType::new(
                vec![param_name.clone()],
                ParamType::Obj(param_set_as_obj),
            ));
        }
        Ok(Fact::ForallFact(ForallFact::new(
            params_def_with_type,
            self.dom_facts
                .iter()
                .map(|atomic_fact| ExistOrAndChainAtomicFact::AtomicFact(atomic_fact.clone()))
                .collect(),
            self.then_facts.clone(),
            self.line_file.clone(),
        )))
    }

    pub fn new(
        params: Vec<String>,
        param_sets: Vec<ClosedRangeOrRange>,
        dom_facts: Vec<AtomicFact>,
        then_facts: Vec<ExistOrAndChainAtomicFact>,
        proof: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        ForAxiomStmt {
            params,
            param_sets,
            dom_facts,
            then_facts,
            proof,
            line_file,
        }
    }
}

impl fmt::Display for ClosedRangeOrRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClosedRangeOrRange::ClosedRange(closed_range) => write!(f, "{}", closed_range),
            ClosedRangeOrRange::Range(range) => write!(f, "{}", range),
        }
    }
}

impl fmt::Display for ByExtensionAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.proof.len() {
            0 => write!(
                f,
                "{} {} {} {} {}",
                BY, EXTENSION, self.left, EQUAL, self.right
            ),
            _ => write!(
                f,
                "{} {} {} {} {}{}\n{}",
                BY,
                EXTENSION,
                self.left,
                EQUAL,
                self.right,
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
            ),
        }
    }
}

impl ByExtensionAxiomStmt {
    pub fn new(left: Obj, right: Obj, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByExtensionAxiomStmt {
            left,
            right,
            proof,
            line_file,
        }
    }
}

impl fmt::Display for ByFnDefAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", BY, FN_DEF, self.function)
    }
}

impl ByFnDefAxiomStmt {
    pub fn new(function: Obj, line_file: LineFile) -> Self {
        ByFnDefAxiomStmt {
            function,
            line_file,
        }
    }
}

impl fmt::Display for ByCartDefAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", BY, CART_DEF, self.cart)
    }
}

impl ByCartDefAxiomStmt {
    pub fn new(cart: Cart, line_file: LineFile) -> Self {
        ByCartDefAxiomStmt { cart, line_file }
    }
}

impl fmt::Display for ByTupleStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{} {}", BY, TUPLE, COLON, self.obj)
    }
}

impl ByTupleStmt {
    pub fn new(obj: Obj, line_file: LineFile) -> Self {
        ByTupleStmt { obj, line_file }
    }
}

impl ByInducAxiomStmt {
    pub fn to_corresponding_forall_fact(&self) -> Result<Fact, String> {
        let mut params_def_with_type: Vec<ParamGroupWithParamType> = Vec::new();
        params_def_with_type.push(ParamGroupWithParamType::new(
            vec![self.param.clone()],
            ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
        ));
        let mut dom_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();

        dom_facts.push(ExistOrAndChainAtomicFact::AtomicFact(
            AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                Obj::Identifier(Identifier::new(self.param.clone())),
                self.induc_from.clone(),
                self.line_file.clone(),
            )),
        ));

        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        for fact in self.to_prove.iter() {
            then_facts.push(fact.clone());
        }
        let forall_fact =
            ForallFact::new(params_def_with_type, dom_facts, then_facts, self.line_file.clone());
        Ok(Fact::ForallFact(forall_fact))
    }
}
