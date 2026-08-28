//! Environment-owned direct membership and inclusion relations.

use crate::prelude::*;
use std::collections::HashMap;

/// Direct membership and inclusion edges used by set-relation lookup.
#[derive(Clone)]
pub struct SetRelationIndex {
    pub owner_sets: HashMap<ObjString, HashMap<ObjString, InFact>>,
    pub direct_supersets: HashMap<ObjString, HashMap<ObjString, AtomicFact>>,
}

impl SetRelationIndex {
    pub fn new() -> Self {
        Self {
            owner_sets: HashMap::new(),
            direct_supersets: HashMap::new(),
        }
    }

    pub fn merge_from(&mut self, child: Self) {
        for (element_key, child_owner_sets) in child.owner_sets {
            let parent_owner_sets = self.owner_sets.entry(element_key).or_default();
            for (set_key, evidence) in child_owner_sets {
                parent_owner_sets.entry(set_key).or_insert(evidence);
            }
        }
        for (subset_key, child_supersets) in child.direct_supersets {
            let parent_supersets = self.direct_supersets.entry(subset_key).or_default();
            for (superset_key, evidence) in child_supersets {
                parent_supersets.entry(superset_key).or_insert(evidence);
            }
        }
    }
}
