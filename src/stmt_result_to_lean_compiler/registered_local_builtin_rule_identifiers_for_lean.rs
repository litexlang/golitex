//! Stable verifier rule identifiers accepted by the direct Result compiler.
//!
//! These constants validate typed `RegisteredLocalBuiltinRuleEvidence`; they
//! are not an intermediate representation.

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
pub(crate) const ADD_POSITIVE_RULE_ID: &str = "order.add_positive";
pub(crate) const ADD_POSITIVE_FINGERPRINT: &str =
    "8605e77fc5c5db9072ad675845c010301753bc1452dfe48cb694b6e0e17c8682";
pub(crate) const MUL_NONNEGATIVE_RULE_ID: &str = "order.mul_nonnegative";
pub(crate) const MUL_NONNEGATIVE_FINGERPRINT: &str =
    "029e0c1dfafd0fc02ea4af8de3e41657a71c6bf13668194271474d7be558ed9a";
pub(crate) const MUL_POSITIVE_RULE_ID: &str = "order.mul_positive";
pub(crate) const MUL_POSITIVE_FINGERPRINT: &str =
    "da784594463db9c15a13fa70bc09e25c6e3e0f9fce3afffff28e26d87cc5850b";
pub(crate) const DIV_NONNEGATIVE_RULE_ID: &str = "order.div_nonnegative";
pub(crate) const DIV_NONNEGATIVE_FINGERPRINT: &str =
    "fd665b573e86552a619b77979593d7a4b55b0963071fd56268f4a2624d3e809b";
pub(crate) const DIV_POSITIVE_RULE_ID: &str = "order.div_positive";
pub(crate) const DIV_POSITIVE_FINGERPRINT: &str =
    "d2753d88095aa947c6697b718a807a70c055e4c1f806610cfb1b2003fcad17c4";
pub(crate) const SET_UNION_ASSOCIATIVE_RULE_ID: &str = "set.union_associative";
pub(crate) const SET_UNION_ASSOCIATIVE_FINGERPRINT: &str =
    "35fe9cd0a90fc9a3d4d92de4901ac782a111b3ed21265e336011fe3cb2a9b9ca";
pub(crate) const SET_UNION_COMMUTATIVE_RULE_ID: &str = "set.union_commutative";
pub(crate) const SET_UNION_COMMUTATIVE_FINGERPRINT: &str =
    "e28419529782f4359453954da8392aeaa6bd4442697a070c02ac7ce0663ca37c";
pub(crate) const SET_UNION_EMPTY_LEFT_RULE_ID: &str = "set.union_empty_left";
pub(crate) const SET_UNION_EMPTY_LEFT_FINGERPRINT: &str =
    "e51e206bf0953fe68a9b3557962e396d1ee52c1b891a9eb50d9c5079f5441f04";
pub(crate) const SET_UNION_EMPTY_RIGHT_RULE_ID: &str = "set.union_empty_right";
pub(crate) const SET_UNION_EMPTY_RIGHT_FINGERPRINT: &str =
    "89f800fb417a148e994a81124daaa75a6498356f9e92bfe813f46d600a17d751";
pub(crate) const SET_UNION_IDEMPOTENT_RULE_ID: &str = "set.union_idempotent";
pub(crate) const SET_UNION_IDEMPOTENT_FINGERPRINT: &str =
    "4a5ee3f3b653afd92026e4df5d6a9dcaf3f6828e435ed9f8781fdac381d3faf8";
pub(crate) const SET_UNION_MEMBERSHIP_LEFT_RULE_ID: &str = "set.union_membership_left";
pub(crate) const SET_UNION_MEMBERSHIP_LEFT_FINGERPRINT: &str =
    "db50ee5583f3e8f8fa2815209aa13539980557a7c8d9b6142d31f6839db3879f";
pub(crate) const SET_UNION_MEMBERSHIP_RIGHT_RULE_ID: &str = "set.union_membership_right";
pub(crate) const SET_UNION_MEMBERSHIP_RIGHT_FINGERPRINT: &str =
    "9ec32451ee229c08de0944420df91bfe43e1b3829c1fcbfecc69ad5ff81fe7c5";
pub(crate) const SET_INTERSECT_ASSOCIATIVE_RULE_ID: &str = "set.intersect_associative";
pub(crate) const SET_INTERSECT_ASSOCIATIVE_FINGERPRINT: &str =
    "62775f206eb83fb96299500141ac67cf362fcc7a058bf2367aa4a4ac9ef661a5";
pub(crate) const SET_INTERSECT_COMMUTATIVE_RULE_ID: &str = "set.intersect_commutative";
pub(crate) const SET_INTERSECT_COMMUTATIVE_FINGERPRINT: &str =
    "17432ff7423b202756249d96a051a14eede66e03e314dea9645999fc2dd351e4";
pub(crate) const SET_INTERSECT_MEMBERSHIP_RULE_ID: &str = "set.intersect_membership";
pub(crate) const SET_INTERSECT_MEMBERSHIP_FINGERPRINT: &str =
    "341153e303eb35ad6a5d14034ad32c7124fed0d484d711c7dbf9514091df15df";
pub(crate) const SET_MINUS_MEMBERSHIP_RULE_ID: &str = "set.set_minus_membership";
pub(crate) const SET_MINUS_MEMBERSHIP_FINGERPRINT: &str =
    "e219681b5fab13bc2d1300525cde5e2da9a319cfc42bd25d7c12317206aae835";
pub(crate) const SET_EMPTY_SUBSET_RULE_ID: &str = "set.empty_subset";
pub(crate) const SET_EMPTY_SUBSET_FINGERPRINT: &str =
    "92fccaf585a376765ea16071615a1aeb7820cc13cb4c0eb4b9f8f97e6befa97f";
pub(crate) const SET_INTERSECT_EQ_LEFT_OF_SUBSET_RULE_ID: &str = "set.intersect_eq_left_of_subset";
pub(crate) const SET_INTERSECT_EQ_LEFT_OF_SUBSET_FINGERPRINT: &str =
    "7ad03d7a9172bbb338a3150ec9ea4b1ca67373da3a03299e6b9ec22dad33b3a6";
pub(crate) const SET_INTERSECT_EQ_RIGHT_OF_SUBSET_RULE_ID: &str =
    "set.intersect_eq_right_of_subset";
pub(crate) const SET_INTERSECT_EQ_RIGHT_OF_SUBSET_FINGERPRINT: &str =
    "e54423beff9a9737349e36ff6bcb46ac320fe0c535d6de541160ef01b7883462";
pub(crate) const SET_INTERSECT_FINITE_RULE_ID: &str = "set.intersect_finite";
pub(crate) const SET_INTERSECT_FINITE_FINGERPRINT: &str =
    "5509063c4ceb49e33176b96d0e4034c3ebcaf6461acc840b83cc551bb36f0411";
pub(crate) const SET_INTERSECT_SUBSET_LEFT_RULE_ID: &str = "set.intersect_subset_left";
pub(crate) const SET_INTERSECT_SUBSET_LEFT_FINGERPRINT: &str =
    "8ac50aaa52509a99febd318b7ced83da5f1230e960a2f5edd0e0b067e47af16a";
pub(crate) const SET_INTERSECT_SUBSET_RIGHT_RULE_ID: &str = "set.intersect_subset_right";
pub(crate) const SET_INTERSECT_SUBSET_RIGHT_FINGERPRINT: &str =
    "ef6ac1c794586736a7e8a9254b27cd40056d4fe36338837c766bde863de852d6";
pub(crate) const SET_INTERSECT_UNION_DISTRIBUTIVE_RULE_ID: &str =
    "set.intersect_union_distributive";
pub(crate) const SET_INTERSECT_UNION_DISTRIBUTIVE_FINGERPRINT: &str =
    "09e71f3095db011c27ece4185825cffba1d264ab3d3507a86c1fc142f740d445";
pub(crate) const SET_POWER_SET_FINITE_RULE_ID: &str = "set.power_set_finite";
pub(crate) const SET_POWER_SET_FINITE_FINGERPRINT: &str =
    "24fe0d11ea3b7ca60c77f54c0ace999b18e9d855c6e518b00f2ff6c285caac89";
pub(crate) const SET_POWER_SET_MEMBERSHIP_OF_SUBSET_RULE_ID: &str =
    "set.power_set_membership_of_subset";
pub(crate) const SET_POWER_SET_MEMBERSHIP_OF_SUBSET_FINGERPRINT: &str =
    "69295fecc1ceb1387bde91cc2e811f77d16f12c7b4dd3d79351867b9a1c39538";
pub(crate) const SET_POWER_SET_NONEMPTY_RULE_ID: &str = "set.power_set_nonempty";
pub(crate) const SET_POWER_SET_NONEMPTY_FINGERPRINT: &str =
    "78f62c3515e312c13e5ff781079038dc46ad3bee3354b63c131228265ef30d52";
pub(crate) const SET_MINUS_FINITE_LEFT_RULE_ID: &str = "set.set_minus_finite_left";
pub(crate) const SET_MINUS_FINITE_LEFT_FINGERPRINT: &str =
    "176fa12c544205c1110577452f72b77e40c9ac9764ef6fcf09f7afc085120015";
pub(crate) const SET_MINUS_INTERSECT_DE_MORGAN_RULE_ID: &str = "set.set_minus_intersect_de_morgan";
pub(crate) const SET_MINUS_INTERSECT_DE_MORGAN_FINGERPRINT: &str =
    "daa2291e2c102a102835095bd06377dc0ce2011f4c30fdaa02ca65ec7a063fbe";
pub(crate) const SET_MINUS_RECOVER_SUBSET_RULE_ID: &str = "set.set_minus_recover_subset";
pub(crate) const SET_MINUS_RECOVER_SUBSET_FINGERPRINT: &str =
    "fd9957eadf4543561e313dbed2f74b97e8cbc9453eba9e1a59e7662951da3a46";
pub(crate) const SET_MINUS_SUBSET_LEFT_RULE_ID: &str = "set.set_minus_subset_left";
pub(crate) const SET_MINUS_SUBSET_LEFT_FINGERPRINT: &str =
    "853bef607077556f3e486bf3871b193c8c18561a9b4fccf45e9932817b730207";
pub(crate) const SET_MINUS_UNION_DE_MORGAN_RULE_ID: &str = "set.set_minus_union_de_morgan";
pub(crate) const SET_MINUS_UNION_DE_MORGAN_FINGERPRINT: &str =
    "d3bd452964df44322c84a8d22e9dbbdacb05fe29b771db3a715d25782900a44c";
pub(crate) const SET_SUBSET_EQ_SET_MINUS_RECOVERY_RULE_ID: &str =
    "set.subset_eq_set_minus_recovery";
pub(crate) const SET_SUBSET_EQ_SET_MINUS_RECOVERY_FINGERPRINT: &str =
    "c6ad572ae5a03f309ed0b48dc1343bb3e6990c6904b4198dadd5b6591252796e";
pub(crate) const SET_SUBSET_UNION_LEFT_RULE_ID: &str = "set.subset_union_left";
pub(crate) const SET_SUBSET_UNION_LEFT_FINGERPRINT: &str =
    "a0742d3ee69be3e02184699c732ef1bcf9d3deb2b7fad907e56724c6392194d0";
pub(crate) const SET_SUBSET_UNION_RIGHT_RULE_ID: &str = "set.subset_union_right";
pub(crate) const SET_SUBSET_UNION_RIGHT_FINGERPRINT: &str =
    "89084b25f5256aea6241d1438ac07a7ab530bbd679f65b7dd2eee518335b3f92";
pub(crate) const SET_UNION_FINITE_RULE_ID: &str = "set.union_finite";
pub(crate) const SET_UNION_FINITE_FINGERPRINT: &str =
    "e6e1919698b0f50f8cb599c095c7496058f029d1eb3cf9909cf8b83919b0d64c";
pub(crate) const SET_UNION_NONEMPTY_LEFT_RULE_ID: &str = "set.union_nonempty_left";
pub(crate) const SET_UNION_NONEMPTY_LEFT_FINGERPRINT: &str =
    "e065a62b3ce305702fb3130c1dd4ad4ccda02a798d8a8e82f1dda6fe370a70ed";
pub(crate) const SET_UNION_NONEMPTY_RIGHT_RULE_ID: &str = "set.union_nonempty_right";
pub(crate) const SET_UNION_NONEMPTY_RIGHT_FINGERPRINT: &str =
    "e6cbf3cc72382547d43887ed955055faee19058dd6827dd5e811a5e66b9dec1a";
pub(crate) const SET_UNION_SUBSET_RULE_ID: &str = "set.union_subset";
pub(crate) const SET_UNION_SUBSET_FINGERPRINT: &str =
    "a5e4907694209f659903e84f55b46d7c5a1e320c7d4daf5c56ecc913ee9cb77c";
