//! Statement and fact keyword spellings for new_pipeline parse.
//! Kept local so parse does not import legacy `syntax::keywords`.

pub const PROP: &str = "prop";
pub const ABSTRACT_PROP: &str = "abstract_prop";
pub const LET: &str = "let";
pub const HAVE: &str = "have";
pub const OBTAIN: &str = "obtain";
pub const CLAIM: &str = "claim";
pub const EXAMPLE: &str = "example";
pub const THM: &str = "thm";
pub const AXIOM: &str = "axiom";
pub const STRATEGY: &str = "strategy";
pub const SKETCH: &str = "sketch";
pub const TRY: &str = "try";
pub const QUESTION_GOAL: &str = "?";
pub const TRUST: &str = "trust";
pub const IMPORT: &str = "import";
pub const EVAL: &str = "eval";
pub const WITNESS: &str = "witness";
pub const STRUCT: &str = "struct";
pub const TEMPLATE: &str = "template";
pub const SETTING: &str = "setting";
pub const STRONG_INDUC: &str = "strong_induc";
pub const RELEASE: &str = "release";
pub const BY: &str = "by";
pub const ALGO: &str = "algo";
pub const FOR: &str = "for";
pub const TUPLE: &str = "tuple";
pub const CART: &str = "cart";
pub const SEQ: &str = "seq";
pub const FINITE_SEQ: &str = "finite_seq";
pub const MATRIX: &str = "matrix";
pub const FN: &str = "fn";
pub const PREIMAGE: &str = "preimage";

pub const FORALL: &str = "forall";
pub const EXIST: &str = "exist";
pub const EXIST_BANG: &str = "exist!";
pub const NOT: &str = "not";
pub const AND: &str = "and";
pub const OR: &str = "or";
pub const ST: &str = "st";
pub const SET: &str = "set";
pub const NONEMPTY_SET: &str = "nonempty_set";
pub const FINITE_SET: &str = "finite_set";
pub const RIGHT_ARROW: &str = "=>";
pub const EQUIVALENT_SIGN: &str = "<=>";

pub const EQUAL: &str = "=";
pub const NOT_EQUAL: &str = "!=";
pub const LESS: &str = "<";
pub const GREATER: &str = ">";
pub const LESS_EQUAL: &str = "<=";
pub const GREATER_EQUAL: &str = ">=";
pub const ADD: &str = "+";
pub const SUB: &str = "-";
pub const MUL: &str = "*";
pub const DIV: &str = "/";
pub const LEFT_PAREN: &str = "(";
pub const RIGHT_PAREN: &str = ")";
pub const LEFT_CURLY: &str = "{";
pub const RIGHT_CURLY: &str = "}";
pub const BANG: &str = "!";
pub const COMMA: &str = ",";
pub const COLON: &str = ":";
pub const FACT_PREFIX: &str = "$";
pub const IN: &str = "in";

pub fn is_comparison_op(tok: &str) -> bool {
    matches!(
        tok,
        EQUAL | NOT_EQUAL | LESS | GREATER | LESS_EQUAL | GREATER_EQUAL
    )
}
