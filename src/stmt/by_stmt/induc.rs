use crate::prelude::*;
use std::fmt;

/// Prove by induction on an integer (`by induc … from …`).
#[derive(Clone)]
pub struct ByInducStmt {
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub param: String,
    pub induc_from: Obj,
    pub line_file: LineFile,
}

impl ByInducStmt {
    pub fn new(
        fact: Vec<ExistOrAndChainAtomicFact>,
        param: String,
        induc_from: Obj,
        line_file: LineFile,
    ) -> Self {
        ByInducStmt {
            to_prove: fact,
            param,
            induc_from,
            line_file,
        }
    }

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

impl fmt::Display for ByInducStmt {
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
