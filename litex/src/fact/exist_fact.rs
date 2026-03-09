use std::fmt;
use crate::keywords::{AND, COMMA, EXIST, FACT_PREFIX, LEFT_CURLY_BRACE, NOT, OR, RIGHT_CURLY_BRACE, ST, is_comparison_str};
use crate::helper::{curly_braced_vec_to_string_with_sep, vec_to_string_join_by_comma, vec_to_string_with_sep};
use crate::stmt::parameter_type_and_property::ParamDefWithParamType;
use super::atomic_fact::AtomicFact;
use crate::obj::Obj;
use crate::obj::IdentifierOrIdentifierWithMod;

#[derive(Clone)]
pub enum ExistFact {
    TrueExistFact(TrueExistFact),
    NotExistFact(NotExistFact),
}

#[derive(Clone)]
pub struct AndAtomicFact {
    pub facts: Vec<AtomicFact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl AndAtomicFact {
    pub fn new(facts: Vec<AtomicFact>, line_file_index: Option<(usize, usize)>) -> Self {
        AndAtomicFact { facts, line_file_index }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        self.line_file_index
    }
}

#[derive(Clone)]
pub struct ChainAtomicFact {
    pub objs: Vec<Obj>,
    pub prop_names: Vec<IdentifierOrIdentifierWithMod>,
    pub line_file_index: Option<(usize, usize)>,
}

impl ChainAtomicFact {
    pub fn new(
        objs: Vec<Obj>,
        prop_names: Vec<IdentifierOrIdentifierWithMod>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        ChainAtomicFact { objs, prop_names, line_file_index }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        self.line_file_index
    }
}

#[derive(Clone)]
pub enum FactInOrAtomicFact {
    AtomicFact(AtomicFact),
    AndAtomicFact(AndAtomicFact),
    ChainAtomicFact(ChainAtomicFact),
}

#[derive(Clone)]
pub struct OrAtomicFact {
    pub facts: Vec<FactInOrAtomicFact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl OrAtomicFact {
    pub fn new(facts: Vec<FactInOrAtomicFact>, line_file_index: Option<(usize, usize)>) -> Self {
        OrAtomicFact { facts, line_file_index }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        self.line_file_index
    }
}

#[derive(Clone)]
pub enum FactInsideExistFact {
    AtomicFact(AtomicFact),
    AndAtomicFact(AndAtomicFact),
    ChainAtomicFact(ChainAtomicFact),
    OrAtomicFact(OrAtomicFact),
}

#[derive(Clone)]
pub struct TrueExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub facts: Vec<FactInsideExistFact>,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub facts: Vec<FactInsideExistFact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl TrueExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamType>,
        facts: Vec<FactInsideExistFact>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        TrueExistFact { params_def_with_type, facts, line_file_index }
    }
}

impl NotExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamType>,
        facts: Vec<FactInsideExistFact>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        NotExistFact { params_def_with_type, facts, line_file_index }
    }
}

fn exist_fact_string_without_exist_as_prefix(param_defs: &Vec<ParamDefWithParamType>, facts: &Vec<FactInsideExistFact>) -> String {
    format!("{} {} {}", vec_to_string_join_by_comma(param_defs), ST, curly_braced_vec_to_string_with_sep(&facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>(), format!("{} ", COMMA).as_str()))
}

impl TrueExistFact {
    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        exist_fact_string_without_exist_as_prefix(&self.params_def_with_type, &self.facts)
    }
}

impl NotExistFact {
    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        exist_fact_string_without_exist_as_prefix(&self.params_def_with_type, &self.facts)
    }
}

impl fmt::Display for TrueExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        return write!(f, "{} {}", EXIST, self.exist_fact_string_without_exist_as_prefix());
    }
}

impl fmt::Display for NotExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        return write!(f, "{} {} {}", NOT, EXIST, self.exist_fact_string_without_exist_as_prefix());
    }
}

// ---------- Display & key for FactInsideExistFact and related types ----------
impl fmt::Display for AndAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_with_sep(&self.facts, format!(" {} ", AND).as_str()))
    }
}

impl AndAtomicFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(&self.facts.iter().map(|a| a.key()).collect::<Vec<_>>(), format!(" {} ", AND).as_str())
    }
}

impl fmt::Display for ChainAtomicFact {
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

impl ChainAtomicFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(&self.prop_names.iter().map(|p| p.to_string()).collect::<Vec<_>>(), format!(" {} ", AND).as_str())
    }
}

impl fmt::Display for FactInOrAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FactInOrAtomicFact::AtomicFact(a) => write!(f, "{}", a),
            FactInOrAtomicFact::AndAtomicFact(a) => write!(f, "{}", a),
            FactInOrAtomicFact::ChainAtomicFact(c) => write!(f, "{}", c),
        }
    }
}

impl FactInOrAtomicFact {
    pub fn key(&self) -> String {
        match self {
            FactInOrAtomicFact::AtomicFact(a) => a.key(),
            FactInOrAtomicFact::AndAtomicFact(a) => a.key(),
            FactInOrAtomicFact::ChainAtomicFact(c) => c.key(),
        }
    }
}

impl fmt::Display for OrAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_with_sep(&self.facts.iter().map(|x| x.to_string()).collect::<Vec<_>>(), format!(" {} ", OR).as_str()))
    }
}

impl OrAtomicFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(&self.facts.iter().map(|x| x.key()).collect::<Vec<_>>(), format!(" {} ", OR).as_str())
    }
}

impl fmt::Display for FactInsideExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FactInsideExistFact::AtomicFact(a) => write!(f, "{}", a),
            FactInsideExistFact::AndAtomicFact(a) => write!(f, "{}", a),
            FactInsideExistFact::ChainAtomicFact(c) => write!(f, "{}", c),
            FactInsideExistFact::OrAtomicFact(o) => write!(f, "{}", o),
        }
    }
}

impl FactInsideExistFact {
    pub fn key(&self) -> String {
        match self {
            FactInsideExistFact::AtomicFact(a) => a.key(),
            FactInsideExistFact::AndAtomicFact(a) => a.key(),
            FactInsideExistFact::ChainAtomicFact(c) => c.key(),
            FactInsideExistFact::OrAtomicFact(o) => o.key(),
        }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        match self {
            FactInsideExistFact::AtomicFact(_) => None,
            FactInsideExistFact::AndAtomicFact(a) => a.line_file_index(),
            FactInsideExistFact::ChainAtomicFact(c) => c.line_file_index(),
            FactInsideExistFact::OrAtomicFact(o) => o.line_file_index(),
        }
    }
}

// ---------- line_file ----------
pub fn line_file(e: &ExistFact) -> Option<(usize, usize)> {
    match e {
        ExistFact::TrueExistFact(x) => x.line_file_index,
        ExistFact::NotExistFact(x) => x.line_file_index,
    }
}

impl fmt::Display for ExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExistFact::TrueExistFact(x) => write!(f, "{}", x),
            ExistFact::NotExistFact(x) => write!(f, "{}", x),
        }
    }
}

impl ExistFact {
    pub fn is_true(&self) -> bool {
        match self {
            ExistFact::TrueExistFact(_) => true,
            ExistFact::NotExistFact(_) => false,
        }
    }

    pub fn facts(&self) -> &Vec<FactInsideExistFact> {
        match self {
            ExistFact::TrueExistFact(x) => &x.facts,
            ExistFact::NotExistFact(x) => &x.facts,
        }
    }

    pub fn key(&self) -> String {
        format!("{} {}{}{}", EXIST, LEFT_CURLY_BRACE, vec_to_string_join_by_comma(&self.facts().iter().map(|fact| fact.key()).collect::<Vec<String>>()), RIGHT_CURLY_BRACE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fact::{AtomicFact, EqualFact};
    use crate::obj::Identifier;

    fn mk_obj(s: &str) -> Obj {
        Obj::Identifier(Identifier::new(s))
    }

    #[test]
    fn test_and_atomic_fact_new_and_line_file_key() {
        let a1 = AtomicFact::EqualFact(EqualFact::new(mk_obj("a"), mk_obj("b"), Some((1, 0))));
        let a2 = AtomicFact::EqualFact(EqualFact::new(mk_obj("c"), mk_obj("d"), Some((1, 0))));
        let and = AndAtomicFact::new(vec![a1, a2], Some((2, 0)));
        assert_eq!(and.line_file_index(), Some((2, 0)));
        let _k = and.key();
        let _s = and.to_string();
    }

    #[test]
    fn test_chain_atomic_fact_new_and_line_file_key() {
        use crate::obj::IdentifierOrIdentifierWithMod;
        let chain = ChainAtomicFact::new(
            vec![mk_obj("p"), mk_obj("q")],
            vec![IdentifierOrIdentifierWithMod::Identifier(Identifier::new("$eq"))],
            Some((3, 0)),
        );
        assert_eq!(chain.line_file_index(), Some((3, 0)));
        let _k = chain.key();
        let _s = chain.to_string();
    }

    #[test]
    fn test_or_atomic_fact_new_and_line_file_key() {
        let a = AtomicFact::EqualFact(EqualFact::new(mk_obj("p"), mk_obj("q"), Some((1, 0))));
        let inner = vec![FactInOrAtomicFact::AtomicFact(a)];
        let or_fact = OrAtomicFact::new(inner, Some((4, 0)));
        assert_eq!(or_fact.line_file_index(), Some((4, 0)));
        let _k = or_fact.key();
        let _s = or_fact.to_string();
    }

    #[test]
    fn test_fact_inside_exist_fact_key_display() {
        let a = AtomicFact::EqualFact(EqualFact::new(mk_obj("x"), mk_obj("y"), Some((1, 0))));
        let f = FactInsideExistFact::AtomicFact(a);
        let _k = f.key();
        let _s = f.to_string();
    }
}

