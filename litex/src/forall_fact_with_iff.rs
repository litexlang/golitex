use std::fmt;
use crate::consts::{EQUIVALENT_SIGN, COLON};
use crate::helper::{to_string_and_add_four_spaces_at_beginning_of_each_line, vec_to_string_add_four_spaces_at_beginning_of_each_line};
use crate::forall_fact::ForallFact;
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;

pub struct ForallFactWithIff {
    pub forall_fact: ForallFact,
    pub iff_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub line: u32,
    pub file_index: usize,
}

impl ForallFactWithIff {
    pub fn new(forall_fact: ForallFact, iff_facts: Vec<OrFactOrAndFactOrSpecFact>, line: u32, file_index: usize) -> Self {
        ForallFactWithIff { forall_fact, iff_facts, line, file_index }
    }
}

impl fmt::Display for ForallFactWithIff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}{}\n{}", self.forall_fact, to_string_and_add_four_spaces_at_beginning_of_each_line(&EQUIVALENT_SIGN, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.iff_facts, 2))
    }
}

impl ForallFactWithIff {
    /// 拷贝 forall 的 param 和 dom 为两份，构建两个 ForallFact：
    /// - 第一个：dom 并 then 推出 iff（dom + then => iff_facts）
    /// - 第二个：dom 并 iff 推出 then（dom + iff_facts => then_facts）
    pub fn to_two_forall_facts(self) -> (ForallFact, ForallFact) {
        let ForallFact {
            params_def_with_type,
            dom_facts,
            then_facts,
            line,
            file_index,
        } = self.forall_fact;
        let iff_facts = self.iff_facts;

        // 第一个：dom 并 then => iff
        let mut dom_then = dom_facts.clone();
        dom_then.extend(then_facts.clone());
        let forall_then_implies_iff = ForallFact::new(
            params_def_with_type.clone(),
            dom_then,
            iff_facts.clone(),
            line,
            file_index,
        );

        // 第二个：dom 并 iff => then
        let mut dom_iff = dom_facts;
        dom_iff.extend(iff_facts);
        let forall_iff_implies_then = ForallFact::new(
            params_def_with_type,
            dom_iff,
            then_facts,
            line,
            file_index,
        );

        (forall_then_implies_iff, forall_iff_implies_then)
    }
}