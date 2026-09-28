//! Shared fact references.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn shared_fact(&mut self, result: &Rc<SuccessFactProofNode>) -> JsonValue {
        let pointer = Rc::as_ptr(result) as usize;
        if let Some(id) = self.shared_fact_ids.get(&pointer) {
            return object(vec![string_field("$ref", id.clone())]);
        }
        let id = format!("proof-node-{}", self.next_shared_fact_id);
        self.next_shared_fact_id += 1;
        self.shared_fact_ids.insert(pointer, id.clone());
        object(vec![
            string_field("$id", id),
            ("value".to_string(), self.verify_fact(result)),
        ])
    }
}
