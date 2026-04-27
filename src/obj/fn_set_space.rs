use crate::prelude::*;

/// [`FnSet`] or [`AnonymousFn`] as the current callable space when checking curried [`FnObj`] applications.
#[derive(Clone)]
pub enum FnSetSpace {
    Set(FnSet),
    Anon(AnonymousFn),
}

impl FnSetSpace {
    pub fn params(&self) -> &Vec<ParamGroupWithSet> {
        match self {
            FnSetSpace::Set(f) => &f.params_def_with_set,
            FnSetSpace::Anon(a) => &a.params_def_with_set,
        }
    }

    pub fn dom(&self) -> &Vec<OrAndChainAtomicFact> {
        match self {
            FnSetSpace::Set(f) => &f.dom_facts,
            FnSetSpace::Anon(a) => &a.dom_facts,
        }
    }

    pub fn ret_set_obj(&self) -> Obj {
        match self {
            FnSetSpace::Set(f) => (*f.ret_set).clone(),
            FnSetSpace::Anon(a) => (*a.ret_set).clone(),
        }
    }

    pub fn binding(&self) -> ParamObjType {
        match self {
            FnSetSpace::Set(_) => ParamObjType::FnSet,
            FnSetSpace::Anon(_) => ParamObjType::AnonymousFn,
        }
    }

    pub fn from_ret_obj(obj: Obj) -> Result<Self, RuntimeError> {
        match obj {
            Obj::FnSet(f) => Ok(FnSetSpace::Set(f)),
            Obj::AnonymousFn(a) => Ok(FnSetSpace::Anon(a)),
            _ => Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    format!(
                        "expect return set of function space to be `fn` or anonymous fn, got {}",
                        obj
                    ),
                    default_line_file(),
                    None,
                    vec![],
                ),
            ))),
        }
    }
}
