//! Stage B wave 8: Euclidean / square-sum / odd (-1) power / lcm·gcd leftovers.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::{EqualFact, Fact, InFact};
use crate::ast::obj::{
    Abs, Add, ArithmeticOperator, Gcd, IntegerOperator, Lcm, Literal, Mod, Mul, Neg, Number, Obj,
    Pow, Quot, StandardSet, Sub,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin QuotEuclideanDecomposition: a = d * quot(a, d) + (a % d)
// (also accepts quot(a, d) * d on the product side).
// Example: have a Z; have d N+; a = d * quot(a, d) + (a % d).
pub struct QuotEuclideanDecompositionBuiltinRuleProof {}

// Builtin ModDividendMinusRemainderZero: (a - (a % b)) % b = 0.
// Example: have a Z; have b N+; (a - (a % b)) % b = 0.
pub struct ModDividendMinusRemainderZeroBuiltinRuleProof {}

// Builtin SquareSumComponentZero: a = 0 (or b = 0) from known a^2 + b^2 = 0
// (also accepts a * a squares).
// Example: have a R; have b R; trust a^2 + b^2 = 0; a = 0.
pub struct SquareSumComponentZeroBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin MinusOneOddNaturalPower: (-1)^(2 * m + 1) = -1.
// Example: have m N; (-1)^(2 * m + 1) = -1.
pub struct MinusOneOddNaturalPowerBuiltinRuleProof {}

// Builtin LcmGcdProductAbs: lcm(a, b) * gcd(a, b) = abs(a * b).
// Example: have a Z; have b Z; trust a != 0; trust b != 0;
//          trust lcm(a, b) $in N; trust gcd(a, b) $in N+;
//          lcm(a, b) * gcd(a, b) = abs(a * b).
pub struct LcmGcdProductAbsBuiltinRuleProof {}

pub enum EqualityIdentitiesWave8BuiltinRuleProof {
    QuotEuclideanDecomposition(QuotEuclideanDecompositionBuiltinRuleProof),
    ModDividendMinusRemainderZero(ModDividendMinusRemainderZeroBuiltinRuleProof),
    SquareSumComponentZero(SquareSumComponentZeroBuiltinRuleProof),
    MinusOneOddNaturalPower(MinusOneOddNaturalPowerBuiltinRuleProof),
    LcmGcdProductAbs(LcmGcdProductAbsBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave8(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave8BuiltinRuleProof>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if quot_euclidean_decomposition_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave8BuiltinRuleProof::QuotEuclideanDecomposition(
                        QuotEuclideanDecompositionBuiltinRuleProof {},
                    ),
                ));
            }
            if mod_dividend_minus_remainder_zero_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave8BuiltinRuleProof::ModDividendMinusRemainderZero(
                        ModDividendMinusRemainderZeroBuiltinRuleProof {},
                    ),
                ));
            }
            if minus_one_odd_natural_power_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave8BuiltinRuleProof::MinusOneOddNaturalPower(
                        MinusOneOddNaturalPowerBuiltinRuleProof {},
                    ),
                ));
            }
            if lcm_gcd_product_abs_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave8BuiltinRuleProof::LcmGcdProductAbs(
                        LcmGcdProductAbsBuiltinRuleProof {},
                    ),
                ));
            }
        }
        if let Some(proof) = self.try_square_sum_component_zero(fact, verify_state)? {
            return Ok(Some(
                EqualityIdentitiesWave8BuiltinRuleProof::SquareSumComponentZero(proof),
            ));
        }
        Ok(None)
    }

    fn try_square_sum_component_zero(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SquareSumComponentZeroBuiltinRuleProof>> {
        let target = if is_zero_obj(&fact.left) {
            &fact.right
        } else if is_zero_obj(&fact.right) {
            &fact.left
        } else {
            return Ok(None);
        };
        let zero = zero_obj();
        let adjacency = self.visible_equivalence_class_adjacency();
        for key in self.equivalence_class_keys(&zero) {
            let Some(neighbors) = adjacency.get(&key) else {
                continue;
            };
            for (_, equal_fact) in neighbors.iter() {
                for side in [&equal_fact.left, &equal_fact.right] {
                    let Some((b1, b2)) = square_sum_bases(side) else {
                        continue;
                    };
                    if b1.ir() != target.ir() && b2.ir() != target.ir() {
                        continue;
                    }
                    // Nonnegativity of squares is a real-domain fact. The
                    // enclosing equality's WD also permits complex bases.
                    let mut requirements = Vec::new();
                    for base in [b1, b2] {
                        let membership: Fact = InFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            element: base.clone(),
                            set: Obj::StandardSet(StandardSet::R),
                            line_file: None,
                        }
                        .into();
                        requirements.push(
                            self.verify_builtin_rule_premise(&membership, verify_state.clone())?,
                        );
                        if requirements.last().unwrap().is_failed() {
                            break;
                        }
                    }
                    if requirements.last().unwrap().is_failed() {
                        continue;
                    }
                    // The graph selects a candidate; the proof must cite an
                    // actual checked path from that sum to zero.
                    let sum_zero: Fact = EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: side.clone(),
                        right: zero.clone(),
                        line_file: None,
                    }
                    .into();
                    let sum_zero_proof =
                        self.verify_builtin_rule_premise(&sum_zero, verify_state.clone())?;
                    if sum_zero_proof.is_failed() {
                        continue;
                    }
                    requirements.push(sum_zero_proof);
                    return Ok(Some(SquareSumComponentZeroBuiltinRuleProof {
                        proof_of_requirement_facts: requirements,
                    }));
                }
            }
        }
        Ok(None)
    }
}

fn quot_euclidean_decomposition_shape(dividend: &Obj, decomposition: &Obj) -> bool {
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: product_side,
        right: rem_side,
    })) = decomposition
    else {
        return false;
    };
    let Some((q_left, q_right)) = match_quot_product(product_side.as_ref()) else {
        return false;
    };
    let Some((r_left, r_right)) = match_mod(rem_side.as_ref()) else {
        return false;
    };
    dividend.ir() == q_left.ir() && dividend.ir() == r_left.ir() && q_right.ir() == r_right.ir()
}

fn match_quot_product(obj: &Obj) -> Option<(&Obj, &Obj)> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = obj else {
        return None;
    };
    // d * quot(a, d) or quot(a, d) * d
    if let Some((q_left, q_right)) = match_quot(left.as_ref()) {
        if q_right.ir() == right.as_ref().ir() {
            return Some((q_left, q_right));
        }
    }
    if let Some((q_left, q_right)) = match_quot(right.as_ref()) {
        if q_right.ir() == left.as_ref().ir() {
            return Some((q_left, q_right));
        }
    }
    None
}

fn mod_dividend_minus_remainder_zero_shape(remainder: &Obj, zero: &Obj) -> bool {
    if !is_zero_obj(zero) {
        return false;
    }
    let Some((dividend, modulus)) = match_mod(remainder) else {
        return false;
    };
    let Some((a, inner_mod)) = match_sub(dividend) else {
        return false;
    };
    let Some((inner_a, inner_b)) = match_mod(inner_mod) else {
        return false;
    };
    a.ir() == inner_a.ir() && modulus.ir() == inner_b.ir()
}

fn minus_one_odd_natural_power_shape(pow_side: &Obj, neg_one_side: &Obj) -> bool {
    if !is_neg_one_obj(neg_one_side) {
        return false;
    }
    let Some((base, exponent)) = match_pow(pow_side) else {
        return false;
    };
    if !is_neg_one_obj(base) {
        return false;
    }
    // exponent = 2 * m + 1
    let Some((even_part, one)) = match_add(exponent) else {
        return false;
    };
    if !is_one_obj(one) {
        return false;
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = even_part else {
        return false;
    };
    is_two_obj(left.as_ref()) || is_two_obj(right.as_ref())
}

fn lcm_gcd_product_abs_shape(product: &Obj, abs_product: &Obj) -> bool {
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = product else {
        return false;
    };
    let (lcm_args, gcd_args) = match (left.as_ref(), right.as_ref()) {
        (
            Obj::IntegerOperator(IntegerOperator::Lcm(Lcm { left: a, right: b })),
            Obj::IntegerOperator(IntegerOperator::Gcd(Gcd { left: c, right: d })),
        )
        | (
            Obj::IntegerOperator(IntegerOperator::Gcd(Gcd { left: c, right: d })),
            Obj::IntegerOperator(IntegerOperator::Lcm(Lcm { left: a, right: b })),
        ) => ((a.as_ref(), b.as_ref()), (c.as_ref(), d.as_ref())),
        _ => return false,
    };
    if !(lcm_args.0.ir() == gcd_args.0.ir() && lcm_args.1.ir() == gcd_args.1.ir()) {
        return false;
    }
    let Some(abs_arg) = match_abs(abs_product) else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: p1,
        right: p2,
    })) = abs_arg
    else {
        return false;
    };
    (p1.as_ref().ir() == lcm_args.0.ir() && p2.as_ref().ir() == lcm_args.1.ir())
        || (p1.as_ref().ir() == lcm_args.1.ir() && p2.as_ref().ir() == lcm_args.0.ir())
}

fn square_sum_bases(obj: &Obj) -> Option<(&Obj, &Obj)> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = obj else {
        return None;
    };
    let b1 = square_base(left.as_ref())?;
    let b2 = square_base(right.as_ref())?;
    Some((b1, b2))
}

fn square_base(obj: &Obj) -> Option<&Obj> {
    if let Some((base, exp)) = match_pow(obj) {
        if is_two_obj(exp) {
            return Some(base);
        }
    }
    if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = obj {
        if left.as_ref().ir() == right.as_ref().ir() {
            return Some(left.as_ref());
        }
    }
    None
}

fn match_mod(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Mod(Mod { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_quot(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Quot(Quot { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_pow(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })) => {
            Some((base.as_ref(), exponent.as_ref()))
        }
        _ => None,
    }
}

fn match_add(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_sub(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_abs(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".into(),
    }))
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}

fn is_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "1"
    )
}

fn is_two_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "2"
    )
}

fn is_neg_one_obj(obj: &Obj) -> bool {
    if matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "-1"
    ) {
        return true;
    }
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg })) => is_one_obj(arg.as_ref()),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right }))
            if is_zero_obj(left.as_ref()) =>
        {
            is_one_obj(right.as_ref())
        }
        _ => false,
    }
}

#[cfg(test)]
mod square_sum_real_guard_tests {
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
    use crate::json_output::project_run_detailed;
    use crate::knowledge_base::JsonValue;
    use crate::launch_command::{LaunchCommand, OutputLanguage};
    use crate::runtime::Runtime;
    use crate::tokenize::Tokenizer;

    fn runtime() -> Runtime {
        Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        })
    }

    fn check(rt: &mut Runtime, code: &str, expected: bool) -> JsonValue {
        let run = rt.run_litex_code(code).expect("public Runtime");
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert_eq!(run.success, expected, "{code}");
        project_run_detailed(&run, rt, "eval", None)
    }

    fn find_rule(value: &JsonValue) -> Option<&JsonValue> {
        find_named_rule(value, "SquareSumComponentZero")
    }

    fn find_named_rule<'a>(value: &'a JsonValue, name: &str) -> Option<&'a JsonValue> {
        match value {
            JsonValue::Object(fields) => {
                if fields.get("rule").and_then(|v| v.as_str().ok()) == Some(name) {
                    return Some(value);
                }
                fields
                    .keys_in_order()
                    .into_iter()
                    .find_map(|key| find_named_rule(fields.get(&key).unwrap(), name))
            }
            JsonValue::Array(items) => items.iter().find_map(|item| find_named_rule(item, name)),
            _ => None,
        }
    }

    fn contains_exact_string(value: &JsonValue, expected: &str) -> bool {
        match value {
            JsonValue::String(text) => text == expected,
            JsonValue::Object(fields) => fields
                .keys_in_order()
                .into_iter()
                .any(|key| contains_exact_string(fields.get(&key).unwrap(), expected)),
            JsonValue::Array(items) => items
                .iter()
                .any(|item| contains_exact_string(item, expected)),
            _ => false,
        }
    }

    #[test]
    fn square_sum_real_guard_tracer_preserves_real_forms_and_proof_payload() {
        let source = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/square_sum_zero_real_guard.lit"
        ));
        let json = check(&mut runtime(), source, true);
        let rule = find_rule(&json)
            .expect("actual winning rule")
            .as_object()
            .unwrap();
        let requirements = rule
            .get("proof_of_requirement_facts")
            .unwrap()
            .as_array()
            .unwrap();
        assert_eq!(requirements.len(), 3);
        for (requirement, fact) in
            requirements
                .iter()
                .zip(["a $in R", "b $in R", "a ^ 2 + b ^ 2 = 0"])
        {
            let requirement = requirement.as_object().unwrap();
            assert_eq!(requirement.get("success"), Some(&JsonValue::Bool(true)));
            assert_eq!(requirement.get("fact").unwrap().as_str().unwrap(), fact);
            assert!(requirement.get("searched_proof").is_some());
        }
        for source in [
            "forall a,b Q:\n    a^2+b^2=0\n    =>:\n        a=0\n",
            "forall a,b Z:\n    a^2+b^2=0\n    =>:\n        b=0\n",
            "forall a,b R:\n    0=b^2+a^2\n    =>:\n        0=a\n        0=b\n",
            "forall a,b R:\n    a^2+b*b=0\n    =>:\n        a=0\n",
        ] {
            check(&mut runtime(), source, true);
        }
    }

    #[test]
    fn square_sum_real_guard_rejects_complex_and_wrong_shapes() {
        for source in [
            "forall a,b C:\n    a^2+b^2=0\n    =>:\n        a=0\n",
            "forall a,b C:\n    a*a+b*b=0\n    =>:\n        b=0\n",
            "forall a,b C:\n    a $in R\n    a^2+b^2=0\n    =>:\n        a=0\n",
            "forall a,b C:\n    b $in R\n    a^2+b^2=0\n    =>:\n        a=0\n",
            "forall a,b R:\n    a^2+b^2=1\n    =>:\n        a=0\n",
            "forall a,b,c R:\n    a^2+b^2=0\n    =>:\n        c=0\n",
            "forall a,b R:\n    a*b+b^2=0\n    =>:\n        a=0\n",
            "forall a,b R:\n    a^3+b^3=0\n    =>:\n        a=0\n",
            "forall a,b R:\n    a^2-b^2=0\n    =>:\n        a=0\n",
        ] {
            check(&mut runtime(), source, false);
        }
    }

    #[test]
    fn square_sum_real_guard_retains_actual_assumption_citations() {
        let source =
            "forall a,b C:\n    a $in R\n    b $in R\n    a^2+b^2=0\n    =>:\n        a=0\n";
        let json = check(&mut runtime(), source, true);
        let statement = &json
            .as_object()
            .unwrap()
            .get("statement_results")
            .unwrap()
            .as_array()
            .unwrap()[0];
        let verify = statement
            .as_object()
            .unwrap()
            .get("verify")
            .unwrap()
            .as_object()
            .unwrap();
        let assumptions = verify.get("assumed_dom_facts").unwrap().as_array().unwrap();
        let requirements = find_rule(&json)
            .unwrap()
            .as_object()
            .unwrap()
            .get("proof_of_requirement_facts")
            .unwrap()
            .as_array()
            .unwrap();
        assert_eq!(requirements.len(), 3);
        assert_eq!(assumptions.len(), 3);
        for (requirement, assumption) in requirements.iter().zip(assumptions) {
            let store = &assumption
                .as_object()
                .unwrap()
                .get("store_and_infer")
                .unwrap()
                .as_object()
                .unwrap()
                .get("stores")
                .unwrap()
                .as_array()
                .unwrap()[0];
            let source_id = store
                .as_object()
                .unwrap()
                .get("fact_id")
                .unwrap()
                .as_str()
                .unwrap();
            assert!(
                contains_exact_string(
                    requirement
                        .as_object()
                        .unwrap()
                        .get("searched_proof")
                        .unwrap(),
                    source_id
                ),
                "missing {source_id}"
            );
        }
    }

    #[test]
    fn square_sum_real_guard_respects_parent_search_ceiling() {
        let mut rt = runtime();
        let source = "forall a,b R:\n    a^2+b^2=0\n    =>:\n        a=0\n";
        let tokens = Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("fact")
        };
        for level in [
            VerifyStateLevel::Direct,
            VerifyStateLevel::KnownSpecialProperty,
        ] {
            assert!(rt
                .verify_fact(&goal, VerifyState::new(level))
                .unwrap()
                .is_failed());
        }
        assert!(!rt
            .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
            .unwrap()
            .is_failed());
    }

    #[test]
    fn square_sum_real_guard_false_result_never_publishes_and_valid_reuse_continues() {
        let mut rt = runtime();
        check(&mut rt, "1^2+i^2=0\n", true);
        check(&mut rt, "1=0\n", false);
        check(&mut rt, "i=0\n", false);
        let wrong = "forall a,b C:\n    a^2+b^2=0\n    =>:\n        a=0\n";
        check(&mut rt, wrong, false);
        check(
            &mut rt,
            "forall a,b R:\n    a^2+b^2=0\n    =>:\n        a=0\n        b=0\n",
            true,
        );
        check(&mut rt, wrong, false);
        check(&mut rt, "1!=0\ni!=0\n", true);
        check(&mut rt, "1=0\n", false);
    }

    #[test]
    fn square_sum_real_guard_nonzero_retains_real_and_component_citations() {
        let source =
            "forall a,b C:\n    a $in R\n    b $in R\n    b!=0\n    =>:\n        a*a+b*b!=0\n";
        let json = check(&mut runtime(), source, true);
        let rule = find_named_rule(&json, "SquareSumNonzeroFromComponent")
            .expect("actual rule")
            .as_object()
            .unwrap();
        let requirements = rule
            .get("proof_of_requirement_facts")
            .unwrap()
            .as_array()
            .unwrap();
        assert_eq!(requirements.len(), 2);
        let statement = &json
            .as_object()
            .unwrap()
            .get("statement_results")
            .unwrap()
            .as_array()
            .unwrap()[0];
        let assumptions = statement
            .as_object()
            .unwrap()
            .get("verify")
            .unwrap()
            .as_object()
            .unwrap()
            .get("assumed_dom_facts")
            .unwrap()
            .as_array()
            .unwrap();
        assert_eq!(assumptions.len(), 3);
        let component = rule.get("component_nonzero_proof").unwrap();
        for (proof, assumption) in requirements.iter().chain([component]).zip(assumptions) {
            assert_eq!(
                proof.as_object().unwrap().get("success"),
                Some(&JsonValue::Bool(true))
            );
            let store = &assumption
                .as_object()
                .unwrap()
                .get("store_and_infer")
                .unwrap()
                .as_object()
                .unwrap()
                .get("stores")
                .unwrap()
                .as_array()
                .unwrap()[0];
            let source_id = store
                .as_object()
                .unwrap()
                .get("fact_id")
                .unwrap()
                .as_str()
                .unwrap();
            assert!(contains_exact_string(
                proof.as_object().unwrap().get("searched_proof").unwrap(),
                source_id
            ));
        }
        for source in [
            "forall a,b R:\n    a!=0\n    =>:\n        a^2+b^2!=0\n",
            "forall a,b Q:\n    b!=0\n    =>:\n        a^2+b^2!=0\n",
            "forall a,b C:\n    a^2+b^2!=0\n    =>:\n        a!=0 or b!=0\n",
        ] {
            check(&mut runtime(), source, true);
        }
    }

    #[test]
    fn square_sum_real_guard_nonzero_rejects_complex_and_preserves_failure_state() {
        for source in [
            "forall a,b C:\n    a!=0\n    =>:\n        a^2+b^2!=0\n",
            "forall a,b C:\n    a $in R\n    a!=0\n    =>:\n        a^2+b^2!=0\n",
            "forall a,b C:\n    b $in R\n    b!=0\n    =>:\n        a*a+b*b!=0\n",
            "forall a,b R:\n    a^2+b^2!=0\n",
        ] {
            check(&mut runtime(), source, false);
        }
        let mut rt = runtime();
        check(&mut rt, "1^2+i^2=0\n", true);
        check(&mut rt, "1^2+i^2!=0\n", false);
        check(&mut rt, "1^2+i^2=0\n", true);
        check(&mut rt, "1=0\n", false);
        check(
            &mut rt,
            "forall a,b R:\n    a!=0\n    =>:\n        a^2+b^2!=0\n",
            true,
        );
        check(&mut rt, "1^2+i^2!=0\n", false);
    }
}
