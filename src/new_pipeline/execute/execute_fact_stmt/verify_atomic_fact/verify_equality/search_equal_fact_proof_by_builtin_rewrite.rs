use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{
    Abs, Add, Ceil, Cos, Div, Exp, Factorial, Floor, Ln, Mul, Obj, Pow, Sign, Sin, Sqrt, Sub, Tan,
};
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};
use std::collections::HashSet;

// Builtin rewrite for EqualFact.
//
// Replaces legacy opaque `Runtime::resolve_obj`: object change is an explicit
// rewrite certificate with cites, then residual equality is verified with
// rewrite disabled.
//
// Mathematical property: congruence — if a = b is known, then F[a] = F[b]
// when F is built from the supported constructors below.
//
// Example:
//   trust a = 1
//   a + 1 = 2
// rewrite left `a + 1` → `1 + 1`, then Calculation proves `1 + 1 = 2`.
pub enum EqualitySearchProofByBuiltinRewrite {
    CongruenceSubstitution(CongruenceSubstitutionBuiltinRewriteProof),
}

// Congruence substitution: rewritten sides + cites + residual proof.
pub struct CongruenceSubstitutionBuiltinRewriteProof {
    pub rewritten_left: Obj,
    pub rewritten_right: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
    // Prove rewritten_left = rewritten_right with can_use_rewrite = false.
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    // Builtin equality rewrite by congruence substitution of known equalities.
    // Example: known `a = 1` proves `a + 1 = 2` after rewriting to `1 + 1 = 2`.
    pub fn search_equal_fact_proof_by_builtin_rewrite(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRewrite>> {
        let equalities = self.visible_generating_equal_facts();
        for equality in &equalities {
            for (from, to) in [
                (&equality.left, &equality.right),
                (&equality.right, &equality.left),
            ] {
                let from_ir = from.ir();
                let rewritten_left = replace_obj_matching_ir(&fact.left, &from_ir, to);
                let rewritten_right = replace_obj_matching_ir(&fact.right, &from_ir, to);
                if rewritten_left.ir() == fact.left.ir()
                    && rewritten_right.ir() == fact.right.ir()
                {
                    continue;
                }
                let residual_fact_id = self.ids.allocate_fact_id();
                let residual = EqualFact {
                    fact_id: residual_fact_id,
                    left: rewritten_left.clone(),
                    right: rewritten_right.clone(),
                    line_file: fact.line_file.clone(),
                };
                let residual_state = VerifyState {
                    can_use_forall_fact: verify_state.can_use_forall_fact,
                    can_use_rewrite: false,
                    store_well_defined_fact: false,
                };
                let residual_equal = self.verify_equal_fact(&residual, residual_state)?;
                if residual_equal.is_failed() {
                    continue;
                }
                return Ok(Some(
                    EqualitySearchProofByBuiltinRewrite::CongruenceSubstitution(
                        CongruenceSubstitutionBuiltinRewriteProof {
                            rewritten_left,
                            rewritten_right,
                            cited_equal_fact_ids: vec![equality.fact_id],
                            residual_equal,
                        },
                    ),
                ));
            }
        }
        Ok(None)
    }

    fn visible_generating_equal_facts(&self) -> Vec<EqualFact> {
        let mut seen: HashSet<u64> = HashSet::new();
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            for edges in env.facts.known_equality.generating_edges.values() {
                for (_to_ir, equality) in edges {
                    let id = equality.fact_id.value();
                    if seen.insert(id) {
                        out.push(equality.clone());
                    }
                }
            }
        }
        out
    }
}

// Replace every subtree whose IR equals `from_ir` with `to` (top-down).
// Supported constructors: common arithmetic/unary shapes used by numeric goals.
fn replace_obj_matching_ir(obj: &Obj, from_ir: &ObjIR, to: &Obj) -> Obj {
    if &obj.ir() == from_ir {
        return to.clone();
    }
    match obj {
        Obj::Add(a) => Obj::Add(Add {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Sub(a) => Obj::Sub(Sub {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Mul(a) => Obj::Mul(Mul {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Div(a) => Obj::Div(Div {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Pow(a) => Obj::Pow(Pow {
            base: Box::new(replace_obj_matching_ir(&a.base, from_ir, to)),
            exponent: Box::new(replace_obj_matching_ir(&a.exponent, from_ir, to)),
        }),
        Obj::Abs(a) => Obj::Abs(Abs {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Floor(a) => Obj::Floor(Floor {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Ceil(a) => Obj::Ceil(Ceil {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Exp(a) => Obj::Exp(Exp {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Ln(a) => Obj::Ln(Ln {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Sign(a) => Obj::Sign(Sign {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Factorial(a) => Obj::Factorial(Factorial {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Sqrt(a) => Obj::Sqrt(Sqrt {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Sin(a) => Obj::Sin(Sin {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Cos(a) => Obj::Cos(Cos {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Tan(a) => Obj::Tan(Tan {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        _ => obj.clone(),
    }
}
