use crate::prelude::*;

pub(super) fn kuratowski_pair_tagged_set(left: Obj, right: Obj) -> Obj {
    let singleton = Obj::ListSet(ListSet::new(vec![left.clone()]));
    let unordered_pair = Obj::ListSet(ListSet::new(vec![left, right]));
    Obj::ListSet(ListSet::new(vec![singleton, unordered_pair]))
}

/// Left-associative Kuratowski encoding of a tuple's component list (same as `by tuple`).
pub(super) fn kuratowski_encode_tuple_boxes(args: &[Box<Obj>]) -> Result<Obj, &'static str> {
    if args.len() < 2 {
        return Err("Kuratowski tuple encoding requires at least 2 components");
    }
    let mut acc = (*args[args.len() - 1]).clone();
    for i in (0..args.len() - 1).rev() {
        acc = kuratowski_pair_tagged_set((*args[i]).clone(), acc);
    }
    Ok(acc)
}
