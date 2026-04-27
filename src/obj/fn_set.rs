use std::fmt;

use crate::prelude::*;

#[derive(Clone)]
pub struct FnSetBody {
    pub params_def_with_set: Vec<ParamGroupWithSet>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub ret_set: Box<Obj>,
}

impl FnSetBody {
    pub fn new(
        params_def_with_set: Vec<ParamGroupWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
    ) -> Self {
        Self {
            params_def_with_set,
            dom_facts,
            ret_set: Box::new(ret_set),
        }
    }
}

#[derive(Clone)]
pub struct FnSet {
    pub body: FnSetBody,
}

impl FnSet {
    pub fn new(
        params_and_their_sets: Vec<ParamGroupWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
    ) -> Self {
        FnSet {
            body: FnSetBody::new(params_and_their_sets, dom_facts, ret_set),
        }
    }

    pub fn get_params(&self) -> Vec<String> {
        let mut ret = Vec::with_capacity(ParamGroupWithSet::number_of_params(
            &self.body.params_def_with_set,
        ));
        for param_def_with_set in &self.body.params_def_with_set {
            ret.extend(param_def_with_set.params.iter().cloned());
        }
        ret
    }
}

// Anonymous function value: `FnSetBody` plus braced `equal_to` body.
#[derive(Clone)]
pub struct AnonymousFn {
    pub body: FnSetBody,
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
            body: FnSetBody::new(params_and_their_sets, dom_facts, ret_set),
            equal_to: Box::new(equal_to),
        }
    }
}

// FnSet or AnonymousFn as the current callable space for curried FnObj application checks.
#[derive(Clone)]
pub enum FnSetSpace {
    Set(FnSet),
    Anon(AnonymousFn),
}

impl FnSetSpace {
    pub fn params(&self) -> &Vec<ParamGroupWithSet> {
        match self {
            FnSetSpace::Set(f) => &f.body.params_def_with_set,
            FnSetSpace::Anon(a) => &a.body.params_def_with_set,
        }
    }

    pub fn dom(&self) -> &Vec<OrAndChainAtomicFact> {
        match self {
            FnSetSpace::Set(f) => &f.body.dom_facts,
            FnSetSpace::Anon(a) => &a.body.dom_facts,
        }
    }

    pub fn ret_set_obj(&self) -> Obj {
        match self {
            FnSetSpace::Set(f) => (*f.body.ret_set).clone(),
            FnSetSpace::Anon(a) => (*a.body.ret_set).clone(),
        }
    }

    pub fn binding(&self) -> ParamObjType {
        match self {
            FnSetSpace::Set(_) => ParamObjType::FnSet,
            FnSetSpace::Anon(_) => ParamObjType::FnSet,
        }
    }

    pub fn from_ret_obj(obj: Obj) -> Result<Self, RuntimeError> {
        match obj {
            Obj::FnSet(f) => Ok(FnSetSpace::Set(f)),
            Obj::AnonymousFn(a) => Ok(FnSetSpace::Anon(a)),
            _ => Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                        "expect return set of function space to be `fn` or anonymous fn, got {}",
                        obj
                    )),
            ))),
        }
    }
}

impl fmt::Display for FnSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params_with_sets_display: Vec<String> = self
            .body
            .params_def_with_set
            .iter()
            .map(|g| format!("{} {}", vec_to_string_join_by_comma(&g.params), g.set))
            .collect();
        write!(
            f,
            "{} {} {}",
            FN_LOWER_CASE,
            brace_vec_colon_vec_to_string(&params_with_sets_display, &self.body.dom_facts),
            self.body.ret_set
        )
    }
}

impl fmt::Display for AnonymousFn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params_with_sets_display: Vec<String> = self
            .body
            .params_def_with_set
            .iter()
            .map(|g| format!("{} {}", vec_to_string_join_by_comma(&g.params), g.set))
            .collect();
        write!(
            f,
            "{}{} {} {}{}{}",
            ANONYMOUS_FN_PREFIX,
            brace_vec_colon_vec_to_string(&params_with_sets_display, &self.body.dom_facts),
            self.body.ret_set,
            LEFT_CURLY_BRACE,
            self.equal_to,
            RIGHT_CURLY_BRACE,
        )
    }
}

impl From<FnSet> for Obj {
    fn from(fs: FnSet) -> Self {
        Obj::FnSet(fs)
    }
}

impl From<AnonymousFn> for Obj {
    fn from(af: AnonymousFn) -> Self {
        Obj::AnonymousFn(af)
    }
}
