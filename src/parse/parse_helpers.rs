use crate::prelude::*;

/// Top-level `forall` parameters from `facts` (e.g. `prove:` block in `by cases`), deduped by first occurrence.
pub(crate) fn collect_forall_param_names_from_facts(facts: &[Fact]) -> Vec<String> {
    let mut names = Vec::new();
    for f in facts {
        if let Fact::ForallFact(ff) = f {
            for n in ff.params_def_with_type.collect_param_names() {
                if !names.contains(&n) {
                    names.push(n);
                }
            }
        }
    }
    names
}
