use crate::prelude::*;
use std::fmt;

/// Anonymous function value: quote + parenthesized param/set (optional domain) + return set + braced body.
#[derive(Clone)]
pub struct AnonymousFn {
    pub params_def_with_set: Vec<ParamGroupWithSet>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub ret_set: Box<Obj>,
    pub equal_to: Box<Obj>,
}

impl AnonymousFn {
    pub fn new(
        params_and_their_sets: Vec<ParamGroupWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
        equal_to: Obj,
    ) -> Self {
        AnonymousFn {
            params_def_with_set: params_and_their_sets,
            dom_facts,
            ret_set: Box::new(ret_set),
            equal_to: Box::new(equal_to),
        }
    }
}

impl fmt::Display for AnonymousFn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params_with_sets_display: Vec<String> = self
            .params_def_with_set
            .iter()
            .map(|g| format!("{} {}", vec_to_string_join_by_comma(&g.params), g.set))
            .collect();
        write!(
            f,
            "{}{} {} {}{}{}",
            ANONYMOUS_FN_PREFIX,
            brace_vec_colon_vec_to_string(&params_with_sets_display, &self.dom_facts),
            self.ret_set,
            LEFT_CURLY_BRACE,
            self.equal_to,
            RIGHT_CURLY_BRACE,
        )
    }
}
