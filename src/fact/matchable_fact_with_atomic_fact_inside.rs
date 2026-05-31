use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct AndFact {
    pub facts: Vec<AtomicFact>,
    pub line_file: LineFile,
}

impl AndFact {
    pub fn new(facts: Vec<AtomicFact>, line_file: LineFile) -> Self {
        AndFact { facts, line_file }
    }
    pub fn line_file(&self) -> LineFile {
        self.line_file.clone()
    }
}

#[derive(Clone)]
pub struct ChainFact {
    pub objs: Vec<Obj>,
    pub prop_names: Vec<AtomicName>,
    pub line_file: LineFile,
}

impl ChainFact {
    pub fn new(objs: Vec<Obj>, prop_names: Vec<AtomicName>, line_file: LineFile) -> Self {
        ChainFact {
            objs,
            prop_names,
            line_file,
        }
    }
    pub fn line_file(&self) -> LineFile {
        self.line_file.clone()
    }

    pub fn facts(&self) -> Result<Vec<AtomicFact>, RuntimeError> {
        if self.objs.len() != self.prop_names.len() + 1 {
            return Err(
                NewFactRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
                        "the number of objects ({}) is not equal to the number of property names ({}) + 1",
                        self.objs.len(),
                        self.prop_names.len(),
                    )))
                .into(),
            );
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
                self.line_file.clone(),
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
    pub fn line_file(&self) -> LineFile {
        match self {
            AndChainAtomicFact::AtomicFact(a) => a.line_file(),
            AndChainAtomicFact::AndFact(a) => a.line_file(),
            AndChainAtomicFact::ChainFact(c) => c.line_file(),
        }
    }

    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        if from == to {
            return self;
        }
        match self {
            AndChainAtomicFact::AtomicFact(a) => {
                AndChainAtomicFact::AtomicFact(a.replace_bound_identifier(from, to))
            }
            AndChainAtomicFact::AndFact(af) => AndChainAtomicFact::AndFact(AndFact::new(
                af.facts
                    .into_iter()
                    .map(|x| x.replace_bound_identifier(from, to))
                    .collect(),
                af.line_file,
            )),
            AndChainAtomicFact::ChainFact(cf) => AndChainAtomicFact::ChainFact(ChainFact::new(
                cf.objs
                    .into_iter()
                    .map(|o| Obj::replace_bound_identifier(o, from, to))
                    .collect(),
                cf.prop_names,
                cf.line_file,
            )),
        }
    }
}

impl From<AtomicFact> for AndChainAtomicFact {
    fn from(atomic_fact: AtomicFact) -> Self {
        AndChainAtomicFact::AtomicFact(atomic_fact)
    }
}

impl From<GreaterEqualFact> for AndChainAtomicFact {
    fn from(f: GreaterEqualFact) -> Self {
        AtomicFact::from(f).into()
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

    pub fn get_args_from_fact_ref(&self) -> Vec<&Obj> {
        let mut result: Vec<&Obj> = Vec::new();
        for atomic_fact in self.facts.iter() {
            result.extend(atomic_fact.get_args_from_fact_ref());
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

    pub fn get_args_from_fact_ref(&self) -> Vec<&Obj> {
        self.objs.iter().collect()
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
}

impl From<AndChainAtomicFact> for ExistOrAndChainAtomicFact {
    fn from(f: AndChainAtomicFact) -> Self {
        match f {
            AndChainAtomicFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
            AndChainAtomicFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
            AndChainAtomicFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
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

    pub fn get_args_from_fact_ref(&self) -> Vec<&Obj> {
        match self {
            AndChainAtomicFact::AtomicFact(atomic_fact) => atomic_fact.get_args_from_fact_ref(),
            AndChainAtomicFact::AndFact(and_fact) => and_fact.get_args_from_fact_ref(),
            AndChainAtomicFact::ChainFact(chain_fact) => chain_fact.get_args_from_fact_ref(),
        }
    }
}
