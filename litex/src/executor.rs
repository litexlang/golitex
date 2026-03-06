use crate::runtime_context::RuntimeContext;
use std::fmt;

pub struct Executor<'a> {
    pub runtime_context: &'a mut RuntimeContext<'a>,
}

impl<'a> Executor<'a> {
    pub fn new(runtime_context: &'a mut RuntimeContext<'a>) -> Self {
        Executor { runtime_context }
    }
}

impl<'a> fmt::Display for Executor<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Executor {{\n")?;
        write!(f, "    runtime_context: {}\n", self.runtime_context)?;
        write!(f, "}}")
    }
}