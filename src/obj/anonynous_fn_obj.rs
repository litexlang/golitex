// '(x, y R: x < y) {x + y}
// 'R(x){x}
pub struct AnonymousFn {
    pub params_def_with_set: Vec<ParamGroupWithSet>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub ret_set: Box<Obj>,
    pub equal_to: Box<Obj>,
}

pub struct FnObjWithAnonymousFnAsHead {
    pub head: Box<AnonymousFn>,
    pub body: Vec<Vec<Box<Obj>>>,
}
