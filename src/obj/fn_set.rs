use std::fmt;

use crate::prelude::*;

#[derive(Clone)]
pub struct FnSetBody {
    pub params_def_with_set: ParamDefWithSet,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    /// Return sets are intentionally non-dependent: they must not cite this function's parameters.
    pub ret_set: Box<Obj>,
}

impl FnSetBody {
    pub fn new(
        params_def_with_set: impl Into<ParamDefWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
    ) -> Self {
        Self {
            params_def_with_set: params_def_with_set.into(),
            dom_facts,
            ret_set: Box::new(ret_set),
        }
    }

    pub fn get_params(&self) -> Vec<String> {
        let mut ret = Vec::with_capacity(ParamGroupWithSet::number_of_params(
            &self.params_def_with_set,
        ));
        for param_def_with_set in &self.params_def_with_set {
            ret.extend(param_def_with_set.params.iter().cloned());
        }
        ret
    }
}

#[derive(Clone)]
pub struct FnSet {
    pub body: FnSetBody,
}

impl FnSet {
    pub fn new(
        params_and_their_sets: impl Into<ParamDefWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
    ) -> Result<Self, RuntimeError> {
        let params_and_their_sets = params_and_their_sets.into();
        params_and_their_sets.validate_obj_does_not_cite_params(&ret_set, "function return set")?;
        let fn_set = FnSet {
            body: FnSetBody::new(params_and_their_sets, dom_facts, ret_set),
        };
        check_fn_set_has_no_duplicate_fn_set_free_parameter(&fn_set)?;
        Ok(fn_set)
    }

    pub fn from_body(body: FnSetBody) -> Result<Self, RuntimeError> {
        body.params_def_with_set
            .validate_obj_does_not_cite_params(&body.ret_set, "function return set")?;
        let fn_set = FnSet { body };
        check_fn_set_has_no_duplicate_fn_set_free_parameter(&fn_set)?;
        Ok(fn_set)
    }

    pub fn get_params(&self) -> Vec<String> {
        self.body.get_params()
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
        params_and_their_sets: impl Into<ParamDefWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
        equal_to: Obj,
    ) -> Result<Self, RuntimeError> {
        let params_and_their_sets = params_and_their_sets.into();
        params_and_their_sets
            .validate_obj_does_not_cite_params(&ret_set, "anonymous function return set")?;
        let anonymous_fn = AnonymousFn {
            body: FnSetBody::new(params_and_their_sets, dom_facts, ret_set),
            equal_to: Box::new(equal_to),
        };
        check_anonymous_fn_has_no_duplicate_fn_set_free_parameter(&anonymous_fn)?;
        Ok(anonymous_fn)
    }
}

// FnSet or AnonymousFn as the current callable space for curried FnObj application checks.
#[derive(Clone)]
pub enum FnSetSpace {
    Set(FnSet),
    Anon(AnonymousFn),
}

impl FnSetSpace {
    pub fn params(&self) -> &ParamDefWithSet {
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

impl fmt::Display for FnSetBody {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params_with_sets_display: Vec<String> = self
            .params_def_with_set
            .iter()
            .map(|g| g.to_string())
            .collect();
        write!(
            f,
            "{} {} {}",
            FN_LOWER_CASE,
            brace_vec_colon_vec_to_string(&params_with_sets_display, &self.dom_facts),
            self.ret_set
        )
    }
}

impl fmt::Display for FnSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body)
    }
}

impl fmt::Display for AnonymousFn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params_with_sets_display: Vec<String> = self
            .body
            .params_def_with_set
            .iter()
            .map(|g| g.to_string())
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
