use std::collections::HashMap;
use std::fmt;
use crate::definition_stmt::DefPropStmt;
use crate::definition_stmt::DefSetTemplateStmt;
use crate::define_algorithm_stmt::DefineAlgorithmStmt;

pub struct Environment {
    pub objs: HashMap<String, ()>,
    pub props: HashMap<String, DefPropStmt>,
    pub set_templates: HashMap<String, DefSetTemplateStmt>,
    pub algorithms: HashMap<String, DefineAlgorithmStmt>,

}

impl Environment {
    pub fn new(objs: HashMap<String, ()>, props: HashMap<String, DefPropStmt>, set_templates: HashMap<String, DefSetTemplateStmt>, algorithms: HashMap<String, DefineAlgorithmStmt>) -> Self {
        Environment {
            objs,
            props,
            set_templates,
            algorithms,
        }
    }
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment {{")?;
        write!(f, "objs: {:?}", self.objs.len())?;
        write!(f, "props: {:?}", self.props.len())?;
        write!(f, "set_templates: {:?}", self.set_templates.len())?;
        write!(f, "algorithms: {:?}", self.algorithms.len())?;
        write!(f, "}}")
    }
}