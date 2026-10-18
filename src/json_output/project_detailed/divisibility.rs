use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_divisibility::KnownZeroRemainderProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::dvd::DvdFactSearchProofByBuiltinRule;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_known_zero_remainder(p: &KnownZeroRemainderProof, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("by_known_zero_remainder")),
            ("dividend", string(p.dividend.readable_string())),
            ("divisor", string(p.divisor.readable_string())),
            (
                "zero_remainder",
                super::searched::project_equal_searched(&p.zero_remainder, rt),
            ),
        ],
    )
}

pub(super) fn project_dvd(p: &DvdFactSearchProofByBuiltinRule, rt: &Runtime) -> JsonValue {
    use DvdFactSearchProofByBuiltinRule::*;
    let mut fields = vec![
        ("type", string("builtin_rule")),
        ("family", string("DvdFact")),
        ("rule", string(p.rule_id())),
    ];
    macro_rules! premise {
        ($name:expr, $proof:expr) => {
            fields.push(($name, super::verify::project_verify_fact($proof, rt)))
        };
    }
    match p {
        Zero(_)
        | One(_)
        | SelfDivisor(_)
        | GcdArgument(_)
        | LcmArgument(_)
        | DividendMinusRemainder(_) => {}
        ProductFactor(p) => premise!("multiplier_integer", &p.multiplier_integer),
        GcdCommonDivisor(p) => {
            premise!("divisor_positive", &p.divisor_positive);
            premise!("first_divisibility", &p.first_divisibility);
            premise!("second_divisibility", &p.second_divisibility);
        }
        LcmCommonMultiple(p) => {
            premise!("first_positive", &p.first_positive);
            premise!("second_positive", &p.second_positive);
            premise!("first_divisibility", &p.first_divisibility);
            premise!("second_divisibility", &p.second_divisibility);
        }
        Factorial(p) => {
            premise!("earlier_natural", &p.earlier_natural);
            premise!("later_natural", &p.later_natural);
            premise!("order", &p.order);
        }
    }
    object_for(rt, fields)
}
