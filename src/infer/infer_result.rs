use crate::prelude::*;

#[derive(Clone, Debug)]
pub struct InferResult {
    /// 自由文本（如 warning）与事实的 `Display` 字符串，按语句顺序。
    infer_facts: Vec<String>,
    /// 与 `new_fact` / `push_atomic_fact` 写入的字符串一一对应的结构化事实。
    facts: Vec<Fact>,
}

impl InferResult {
    pub fn new() -> Self {
        InferResult {
            infer_facts: vec![],
            facts: vec![],
        }
    }

    /// 将 `fact` 同时记入展示行与 [`Self::inferred_facts`]。
    pub fn from_fact(fact: &Fact) -> Self {
        let mut r = Self::new();
        r.new_fact(fact);
        r
    }

    pub fn is_empty(&self) -> bool {
        self.infer_facts.is_empty() && self.facts.is_empty()
    }

    /// 用于 CLI / JSON `infer_facts`：按顺序的文本行（含 `new_fact` 写入的事实字符串与 `new_with_msg` 的文本）。
    pub fn infer_lines(&self) -> &[String] {
        &self.infer_facts
    }

    /// 结构化推断事实（与 [`Self::infer_lines`] 中由事实产生的行对应）。
    pub fn inferred_facts(&self) -> &[Fact] {
        &self.facts
    }

    pub fn join_infer_lines(&self, sep: &str) -> String {
        self.infer_facts.join(sep)
    }

    pub fn new_with_msg(&mut self, msg: String) {
        self.infer_facts.push(msg);
    }

    pub fn new_fact(&mut self, fact: &Fact) {
        self.infer_facts.push(fact.to_string());
        self.facts.push(fact.clone());
    }

    pub fn push_atomic_fact(&mut self, atomic_fact: &AtomicFact) {
        self.infer_facts.push(atomic_fact.to_string());
        self.facts.push(Fact::AtomicFact(atomic_fact.clone()));
    }

    pub fn new_infer_result_inside(&mut self, other_infer_result: InferResult) {
        self.infer_facts.extend(other_infer_result.infer_facts);
        self.facts.extend(other_infer_result.facts);
    }
}
