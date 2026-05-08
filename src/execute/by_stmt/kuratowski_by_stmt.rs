use crate::prelude::*;

pub(super) fn kuratowski_pair_tagged_set(left: Obj, right: Obj) -> Obj {
    let singleton = ListSet::new(vec![left.clone()]).into();
    let unordered_pair = ListSet::new(vec![left, right]).into();
    ListSet::new(vec![singleton, unordered_pair]).into()
}

// Left-associative Kuratowski encoding of a tuple's component list.
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
