mod infer_atomic_fact;
mod infer_dispatch;
mod infer_equal_and_normal;
mod infer_in_fact;
pub(crate) use infer_in_fact::obj_eligible_for_known_objs_in_fn_sets;
mod infer_not_forall;
mod infer_numeric_order_sign;
mod infer_result;
mod infer_set_relations;

pub use infer_result::InferResult;
