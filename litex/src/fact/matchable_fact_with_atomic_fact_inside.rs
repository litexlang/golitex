use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct AndFact {
    pub facts: Vec<AtomicFact>,
    pub line_file: (usize, usize),
}

impl AndFact {
    pub fn new(facts: Vec<AtomicFact>, line_file: (usize, usize)) -> Self {
        AndFact { facts, line_file }
    }
    pub fn line_file(&self) -> (usize, usize) {
        self.line_file
    }
}

#[derive(Clone)]
pub struct ChainFact {
    pub objs: Vec<Obj>,
    pub prop_names: Vec<IdentifierOrIdentifierWithMod>,
    pub line_file: (usize, usize),
}

impl ChainFact {
    pub fn new(
        objs: Vec<Obj>,
        prop_names: Vec<IdentifierOrIdentifierWithMod>,
        line_file: (usize, usize),
    ) -> Self {
        ChainFact {
            objs,
            prop_names,
            line_file,
        }
    }
    pub fn line_file(&self) -> (usize, usize) {
        self.line_file
    }

    pub fn facts(&self) -> Result<Vec<AtomicFact>, RuntimeErrorStruct> {
        if self.objs.len() != self.prop_names.len() + 1 {
            return Err(RuntimeErrorStruct::new_with_msg_previous_error(
                format!(
                    "the number of objects ({}) is not equal to the number of property names ({}) + 1",
                    self.objs.len(),
                    self.prop_names.len(),
                ),
                None,
            ));
        }

        let mut facts = Vec::with_capacity(self.prop_names.len());
        for (i, _) in self.prop_names.iter().enumerate() {
            let prop_name = self.prop_names[i].clone();
            let left_obj = self.objs[i].clone();
            let right_obj = self.objs[i + 1].clone();
            let atomic_fact = AtomicFact::to_atomic_fact(
                prop_name,
                true,
                vec![left_obj, right_obj],
                self.line_file,
            );
            facts.push(atomic_fact?);
        }
        Ok(facts)
    }
}

#[derive(Clone)]
pub enum ChainAtomicFact {
    AtomicFact(AtomicFact),
    ChainFact(ChainFact),
}

impl fmt::Display for ChainAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ChainAtomicFact::AtomicFact(a) => write!(f, "{}", a),
            ChainAtomicFact::ChainFact(c) => write!(f, "{}", c),
        }
    }
}

#[derive(Clone)]
pub enum AndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
}

impl AndChainAtomicFact {
    pub fn line_file(&self) -> (usize, usize) {
        match self {
            AndChainAtomicFact::AtomicFact(a) => a.line_file(),
            AndChainAtomicFact::AndFact(a) => a.line_file(),
            AndChainAtomicFact::ChainFact(c) => c.line_file(),
        }
    }
}

impl fmt::Display for AndFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            vec_to_string_with_sep(&self.facts, format!(" {} ", AND))
        )
    }
}

impl AndFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(
            &self.facts.iter().map(|a| a.key()).collect::<Vec<_>>(),
            format!(" {} ", AND),
        )
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        let mut result: Vec<Obj> = Vec::new();
        for atomic_fact in self.facts.iter() {
            let args_from_atomic_fact = atomic_fact.get_args_from_fact();
            for arg in args_from_atomic_fact {
                result.push(arg);
            }
        }
        result
    }
}

impl fmt::Display for ChainFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = self.objs[0].to_string();
        for (i, obj) in self.objs[1..].iter().enumerate() {
            if is_comparison_str(&self.prop_names[i].to_string()) {
                s.push_str(&format!(" {} {}", self.prop_names[i], obj));
            } else {
                s.push_str(&format!(" {}{} {}", FACT_PREFIX, self.prop_names[i], obj));
            }
        }
        write!(f, "{}", s)
    }
}

impl ChainFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(
            &self
                .prop_names
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>(),
            format!(" {} ", AND),
        )
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        let mut result: Vec<Obj> = Vec::new();
        for obj in self.objs.iter() {
            result.push(obj.clone());
        }
        result
    }
}

impl fmt::Display for AndChainAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AndChainAtomicFact::AtomicFact(a) => write!(f, "{}", a),
            AndChainAtomicFact::AndFact(a) => write!(f, "{}", a),
            AndChainAtomicFact::ChainFact(c) => write!(f, "{}", c),
        }
    }
}

impl AndChainAtomicFact {
    pub fn key(&self) -> String {
        match self {
            AndChainAtomicFact::AtomicFact(a) => a.key(),
            AndChainAtomicFact::AndFact(a) => a.key(),
            AndChainAtomicFact::ChainFact(c) => c.key(),
        }
    }

    pub fn to_fact(&self) -> Fact {
        match self {
            AndChainAtomicFact::AtomicFact(atomic_fact) => Fact::AtomicFact(atomic_fact.clone()),
            AndChainAtomicFact::AndFact(and_fact) => Fact::AndFact(and_fact.clone()),
            AndChainAtomicFact::ChainFact(chain_fact) => Fact::ChainFact(chain_fact.clone()),
        }
    }

    pub fn to_exist_or_and_chain_atomic_fact(&self) -> crate::fact::ExistOrAndChainAtomicFact {
        match self {
            AndChainAtomicFact::AtomicFact(atomic_fact) => {
                crate::fact::ExistOrAndChainAtomicFact::AtomicFact(atomic_fact.clone())
            }
            AndChainAtomicFact::AndFact(and_fact) => {
                crate::fact::ExistOrAndChainAtomicFact::AndFact(and_fact.clone())
            }
            AndChainAtomicFact::ChainFact(chain_fact) => {
                crate::fact::ExistOrAndChainAtomicFact::ChainFact(chain_fact.clone())
            }
        }
    }
}

impl AndChainAtomicFact {
    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        match self {
            AndChainAtomicFact::AtomicFact(atomic_fact) => atomic_fact.get_args_from_fact(),
            AndChainAtomicFact::AndFact(and_fact) => and_fact.get_args_from_fact(),
            AndChainAtomicFact::ChainFact(chain_fact) => chain_fact.get_args_from_fact(),
        }
    }
}
