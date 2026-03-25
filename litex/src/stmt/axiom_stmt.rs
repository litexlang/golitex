use super::{parameter_def::ParamDefWithParamType, Stmt};
use crate::common::helper::{
    add_four_spaces_at_beginning, vec_pair_to_string,
    vec_to_string_add_four_spaces_at_beginning_of_each_line,
};
use crate::common::keywords::{
    BY_CART_DEF, BY_CASES, BY_CONTRA, BY_EXTENSION, BY_FN_DEF, BY_INDUC, CASE, COLON, ENUMERATE,
    EQUAL, FOR, FROM, IMPOSSIBLE, PROVE, RIGHT_ARROW,
};
use crate::fact::{
    AndChainAtomicFact, AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, GreaterEqualFact,
};
use crate::obj::Identifier;
use crate::obj::{Cart, ClosedRange, ListSet, Obj, Range, ZObj};
use crate::stmt::parameter_def::ParamType;
use std::fmt;

fn fact_to_exist_or_and_chain_atomic_fact_for_forall_then_body(
    fact: &Fact,
) -> Result<ExistOrAndChainAtomicFact, String> {
    match fact {
        Fact::AtomicFact(atomic_fact) => {
            Ok(ExistOrAndChainAtomicFact::AtomicFact(atomic_fact.clone()))
        }
        Fact::AndFact(and_fact) => Ok(ExistOrAndChainAtomicFact::AndFact(and_fact.clone())),
        Fact::ChainFact(chain_fact) => Ok(ExistOrAndChainAtomicFact::ChainFact(chain_fact.clone())),
        Fact::OrFact(or_fact) => Ok(ExistOrAndChainAtomicFact::OrFact(or_fact.clone())),
        Fact::ExistFact(exist_fact) => Ok(ExistOrAndChainAtomicFact::ExistFact(exist_fact.clone())),
        Fact::ForallFact(_) | Fact::ForallFactWithIff(_) => Err(
            "enumerate: a fact in to_prove cannot be a nested forall inside the generated forall"
                .to_string(),
        ),
    }
}

// view fn set as a subset of a cartesian product set
pub struct ByFnDefAxiomStmt {
    pub function: Obj,
    pub line_file: (usize, usize),
}

// view a cartesian product set as a set (ordered pairs)
pub struct ByCartDefAxiomStmt {
    pub cart: Cart,
    pub line_file: (usize, usize),
}

// prove that a set is equal to another set by proving that they are subsets of each other
pub struct ByExtensionAxiomStmt {
    pub left: Obj,
    pub right: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: (usize, usize),
}

pub enum ClosedRangeOrRange {
    ClosedRange(ClosedRange),
    Range(Range),
}

// prove fact is true for a range of integers
pub struct ForAxiomStmt {
    pub params: Vec<String>,
    pub param_sets: Vec<ClosedRangeOrRange>,
    pub dom_facts: Vec<AtomicFact>,
    pub then_facts: Vec<ExistOrAndChainAtomicFact>,
    pub proof: Vec<Stmt>,
    pub line_file: (usize, usize),
}

// prove fact is true by induction
pub struct ByInducAxiomStmt {
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub param: String,
    pub induc_from: Obj,
    pub line_file: (usize, usize),
}

// prove fact is true for a set of values by enumeration
pub struct EnumerateAxiomStmt {
    pub params: Vec<String>,
    pub param_sets: Vec<ListSet>,
    pub to_prove: Vec<Fact>,
    pub proof: Vec<Stmt>,
    pub line_file: (usize, usize),
}

// prove fact is true case by case
pub struct ByCasesAxiomStmt {
    pub cases: Vec<AndChainAtomicFact>,
    pub then_facts: Vec<Fact>,
    pub proofs: Vec<Vec<Stmt>>,
    pub impossible_facts: Vec<Option<AtomicFact>>,
    pub line_file: (usize, usize),
}

// prove fact is true by contradiction
pub struct ByContraAxiomStmt {
    pub to_prove: AtomicFact,
    pub proof: Vec<Stmt>,
    pub impossible_fact: AtomicFact,
    pub line_file: (usize, usize),
}

impl EnumerateAxiomStmt {
    pub fn new(
        params: Vec<String>,
        param_sets: Vec<ListSet>,
        to_prove: Vec<Fact>,
        proof: Vec<Stmt>,
        line_file: (usize, usize),
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
                "enumerate: number of params does not match number of list sets".to_string(),
            );
        }
        let mut params_def_with_type: Vec<ParamDefWithParamType> = Vec::new();
        for (param_name, list_set_obj) in self.params.iter().zip(self.param_sets.iter()) {
            params_def_with_type.push(ParamDefWithParamType(
                vec![param_name.clone()],
                ParamType::Obj(Obj::ListSet(list_set_obj.clone())),
            ));
        }
        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        for fact in self.to_prove.iter() {
            then_facts.push(fact_to_exist_or_and_chain_atomic_fact_for_forall_then_body(
                fact,
            )?);
        }
        let forall_fact = ForallFact::new(params_def_with_type, vec![], then_facts, self.line_file);
        Ok(Fact::ForallFact(forall_fact))
    }

    pub fn stmt_type_name(&self) -> String {
        "EnumerateAxiomStmt".to_string()
    }
}

impl ByCasesAxiomStmt {
    pub fn new(
        cases: Vec<AndChainAtomicFact>,
        then_facts: Vec<Fact>,
        proofs: Vec<Vec<Stmt>>,
        impossible_facts: Vec<Option<AtomicFact>>,
        line_file: (usize, usize),
    ) -> Self {
        ByCasesAxiomStmt {
            cases,
            then_facts,
            proofs,
            impossible_facts,
            line_file,
        }
    }

    pub fn stmt_type_name(&self) -> String {
        "ByCasesAxiomStmt".to_string()
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
            "{}{}\n{}{}\n{}\n{}",
            BY_CASES,
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
        line_file: (usize, usize),
    ) -> Self {
        ByContraAxiomStmt {
            to_prove,
            proof,
            impossible_fact,
            line_file,
        }
    }

    pub fn stmt_type_name(&self) -> String {
        "ByContraAxiomStmt".to_string()
    }
}

impl fmt::Display for ByContraAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}\n{}{}\n{}",
            BY_CONTRA,
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
            "{} {}{}\n{}{}\n{}\n{}",
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
        line_file: (usize, usize),
    ) -> Self {
        ByInducAxiomStmt {
            to_prove: fact,
            param,
            induc_from,
            line_file,
        }
    }

    pub fn stmt_type_name(&self) -> String {
        "ByInducAxiomStmt".to_string()
    }
}

impl fmt::Display for ByInducAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {}{}\n{}",
            BY_INDUC,
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
                "{} {}{}\n{}",
                FOR,
                vec_pair_to_string(&self.params, &self.param_sets),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1)
            ),
            _ => format!(
                "{} {}{}\n{}\n{}{}\n{}",
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
            return Err("for: number of params does not match number of param sets".to_string());
        }
        let mut params_def_with_type: Vec<ParamDefWithParamType> = Vec::new();
        for (param_name, param_set) in self.params.iter().zip(self.param_sets.iter()) {
            let param_set_as_obj = match param_set {
                ClosedRangeOrRange::ClosedRange(closed_range) => {
                    Obj::ClosedRange(closed_range.clone())
                }
                ClosedRangeOrRange::Range(range) => Obj::Range(range.clone()),
            };
            params_def_with_type.push(ParamDefWithParamType(
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
            self.line_file,
        )))
    }

    pub fn new(
        params: Vec<String>,
        param_sets: Vec<ClosedRangeOrRange>,
        dom_facts: Vec<AtomicFact>,
        then_facts: Vec<ExistOrAndChainAtomicFact>,
        proof: Vec<Stmt>,
        line_file: (usize, usize),
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

    pub fn stmt_type_name(&self) -> String {
        "ForAxiomStmt".to_string()
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
            0 => write!(f, "{} {} {} {}", BY_EXTENSION, self.left, EQUAL, self.right),
            _ => write!(
                f,
                "{} {} {} {}{}\n{}",
                BY_EXTENSION,
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
    pub fn new(left: Obj, right: Obj, proof: Vec<Stmt>, line_file: (usize, usize)) -> Self {
        ByExtensionAxiomStmt {
            left,
            right,
            proof,
            line_file,
        }
    }

    pub fn stmt_type_name(&self) -> String {
        "ByExtensionAxiomStmt".to_string()
    }
}

impl fmt::Display for ByFnDefAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", BY_FN_DEF, self.function)
    }
}

impl ByFnDefAxiomStmt {
    pub fn new(function: Obj, line_file: (usize, usize)) -> Self {
        ByFnDefAxiomStmt {
            function,
            line_file,
        }
    }

    pub fn stmt_type_name(&self) -> String {
        "ByFnDefAxiomStmt".to_string()
    }
}

impl fmt::Display for ByCartDefAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", BY_CART_DEF, self.cart)
    }
}

impl ByCartDefAxiomStmt {
    pub fn new(cart: Cart, line_file: (usize, usize)) -> Self {
        ByCartDefAxiomStmt { cart, line_file }
    }

    pub fn stmt_type_name(&self) -> String {
        "ByCartDefAxiomStmt".to_string()
    }
}

impl ByInducAxiomStmt {
    pub fn to_corresponding_forall_fact(&self) -> Result<Fact, String> {
        let mut params_def_with_type: Vec<ParamDefWithParamType> = Vec::new();
        params_def_with_type.push(ParamDefWithParamType(
            vec![self.param.clone()],
            ParamType::Obj(Obj::ZObj(ZObj::new())),
        ));
        let mut dom_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();

        dom_facts.push(ExistOrAndChainAtomicFact::AtomicFact(
            AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                Obj::Identifier(Identifier::new(self.param.clone())),
                self.induc_from.clone(),
                self.line_file,
            )),
        ));

        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        for fact in self.to_prove.iter() {
            then_facts.push(fact.clone());
        }
        let forall_fact =
            ForallFact::new(params_def_with_type, dom_facts, then_facts, self.line_file);
        Ok(Fact::ForallFact(forall_fact))
    }
}
