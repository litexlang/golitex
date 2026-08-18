use crate::verify::rule_schema::{RuleFingerprint, RuleId};

use super::{LitexToLeanObjectIr, LitexToLeanParameterTypeIr};

pub(crate) const LESS_EQUAL_OF_LESS_RULE_ID: &str = "order.less_equal_of_less";
pub(crate) const LESS_EQUAL_OF_LESS_FINGERPRINT: &str =
    "990acd86094d0a1d3c750541cac271a185c4d399c1277d2fdebac77b98130788";
pub(crate) const ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_RULE_ID: &str =
    "order.add_positive_of_positive_nonnegative";
pub(crate) const ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_FINGERPRINT: &str =
    "ff80e2bc4b7d44084e9c82870dafbe8f51c63a3d5d0f854f9f89a3bda8eb021e";
pub(crate) const ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_RULE_ID: &str =
    "order.add_positive_of_nonnegative_positive";
pub(crate) const ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_FINGERPRINT: &str =
    "a84195ee230f4d19d6d773332a907dac099f941b532d462c18dfdd804fb40553";
pub(crate) const ADD_NONNEGATIVE_RULE_ID: &str = "order.add_nonnegative";
pub(crate) const ADD_NONNEGATIVE_FINGERPRINT: &str =
    "25002877aac825f5b15aef687f3169ebcda7e22fd6f9aeced46397e2a5ae148c";

pub(crate) fn registered_rule_has_lean_adapter(
    rule_id: &RuleId,
    fingerprint: &RuleFingerprint,
) -> bool {
    matches!(
        (rule_id.as_str(), fingerprint.as_hex()),
        (LESS_EQUAL_OF_LESS_RULE_ID, LESS_EQUAL_OF_LESS_FINGERPRINT)
            | (
                ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_RULE_ID,
                ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_FINGERPRINT
            )
            | (
                ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_RULE_ID,
                ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_FINGERPRINT
            )
            | (ADD_NONNEGATIVE_RULE_ID, ADD_NONNEGATIVE_FINGERPRINT)
    )
}

#[derive(Clone, Debug)]
pub struct LitexToLeanTypedBoundObjectIr {
    pub object: LitexToLeanObjectIr,
    pub param_type: LitexToLeanParameterTypeIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanRegisteredRuleApplicationIr {
    pub rule_id: RuleId,
    pub semantic_fingerprint: RuleFingerprint,
    pub bindings: Vec<LitexToLeanTypedBoundObjectIr>,
}
