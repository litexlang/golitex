//! Shared syntax-preserving representation of a named theorem call.

use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum TheoremCallArguments {
    Bare,
    Parenthesized(Vec<Obj>),
}

impl TheoremCallArguments {
    pub fn is_bare(&self) -> bool {
        matches!(self, Self::Bare)
    }

    pub fn args(&self) -> &[Obj] {
        match self {
            Self::Bare => &[],
            Self::Parenthesized(args) => args,
        }
    }
}

#[derive(Clone)]
pub struct TheoremCall {
    pub name: AtomicName,
    pub arguments: TheoremCallArguments,
}

impl TheoremCall {
    pub fn new(name: AtomicName, arguments: TheoremCallArguments) -> Self {
        Self { name, arguments }
    }

    pub fn parenthesized(name: AtomicName, args: Vec<Obj>) -> Self {
        Self::new(name, TheoremCallArguments::Parenthesized(args))
    }

    pub fn args(&self) -> &[Obj] {
        self.arguments.args()
    }

    pub fn parenthesized_args_mut(&mut self) -> Option<&mut Vec<Obj>> {
        match &mut self.arguments {
            TheoremCallArguments::Bare => None,
            TheoremCallArguments::Parenthesized(args) => Some(args),
        }
    }

    pub fn is_bare(&self) -> bool {
        self.arguments.is_bare()
    }

    pub fn with_instantiated_args(&self, args: Vec<Obj>) -> Self {
        match &self.arguments {
            TheoremCallArguments::Bare => {
                debug_assert!(args.is_empty());
                Self::new(self.name.clone(), TheoremCallArguments::Bare)
            }
            TheoremCallArguments::Parenthesized(_) => Self::parenthesized(self.name.clone(), args),
        }
    }
}

impl fmt::Display for TheoremCall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.name)?;
        if let TheoremCallArguments::Parenthesized(args) = &self.arguments {
            write!(f, "{}", braced_vec_to_string(args))?;
        }
        Ok(())
    }
}
