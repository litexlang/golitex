use crate::prelude::*;

const FORALL: &str =
    "forall p cart(R, R):\n    p(1) + p(2) = 0\n    =>:\n        p(1) + p(2) = 0\n";
const THEOREM: &str = "thm coordinate_premise:\n    ? forall p cart(R, R):\n        p(1) + p(2) = 0\n        =>:\n            p(1) + p(2) = 0\n";

#[test]
fn quantified_premise_closes_its_original_coordinate_inferences() {
    for (source, named) in [(FORALL, false), (THEOREM, true)] {
        let (mut result, compiler) = super::execute(source);
        let fact = if named {
            let Fact::ForallFact(fact) =
                &super::named_theorem_mut(&mut result.statement_results[0])
                    .statement
                    .fact
            else {
                unreachable!()
            };
            fact
        } else {
            &super::forall_proof_mut(&mut result.statement_results[0]).fact
        };
        let premise = fact.dom_facts[0].fact_id();
        let generated = compiler.compile_run(&result, "coordinate_premise").unwrap();
        let binder = format!("(h_{} : (by\n", premise.value());
        let start = generated
            .find(&binder)
            .expect("premise type owns its required original proofs");
        let exact = generated[start..].find("exact Litex.Same").unwrap() + start;
        assert!(generated[start..exact].contains("FiniteFunction.coordinate_mem_number"));
    }
}
