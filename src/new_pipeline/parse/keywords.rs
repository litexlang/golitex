//! Statement and fact keyword spellings for new_pipeline parse.
//! Kept local so parse does not import legacy `syntax::keywords`.

pub const PROP: &str = "prop";
pub const ABSTRACT_PROP: &str = "abstract_prop";
pub const LET: &str = "let";
pub const HAVE: &str = "have";
pub const OBTAIN: &str = "obtain";
pub const CLAIM: &str = "claim";
pub const THM: &str = "thm";
pub const AXIOM: &str = "axiom";
pub const STRATEGY: &str = "strategy";
pub const SKETCH: &str = "sketch";
pub const QUESTION_GOAL: &str = "?";
pub const TRUST: &str = "trust";
pub const IMPORT: &str = "import";
pub const EVAL: &str = "eval";
pub const WITNESS: &str = "witness";
pub const STRUCT: &str = "struct";
pub const TEMPLATE: &str = "template";
pub const STRONG_INDUC: &str = "strong_induc";
pub const RELEASE: &str = "release";
pub const EXPAND: &str = "expand";
pub const REGISTER: &str = "register";
pub const OBJ: &str = "obj";
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
pub const FN_PREIMAGE: &str = "fn_preimage";
pub const CASES: &str = "cases";
pub const CASE: &str = "case";
pub const CONTRA: &str = "contra";
pub const DEF: &str = "def";
pub const INDUC: &str = "induc";
pub const IMPOSSIBLE: &str = "impossible";
pub const FROM: &str = "from";
pub const AS: &str = "as";

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
pub const FN_ARROW: &str = "->";
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
pub const MOD_OP: &str = "%";
pub const POW: &str = "^";
pub const DOT_DOT_DOT: &str = "...";
pub const DOT: &str = ".";
pub const MOD_SIGN: &str = "::";
pub const MOD_FLAT_SIGN: &str = ":::";
pub const LEFT_PAREN: &str = "(";
pub const RIGHT_PAREN: &str = ")";
pub const LEFT_CURLY: &str = "{";
pub const RIGHT_CURLY: &str = "}";
pub const LEFT_BRACKET: &str = "[";
pub const RIGHT_BRACKET: &str = "]";
pub const BANG: &str = "!";
pub const COMMA: &str = ",";
pub const COLON: &str = ":";
pub const FACT_PREFIX: &str = "$";
pub const IN: &str = "in";
pub const STRUCT_VIEW_PREFIX: &str = "&";

pub const UNICODE_UNION: &str = "∪";
pub const UNICODE_INTERSECT: &str = "∩";
pub const UNICODE_CART: &str = "×";

pub const ABS: &str = "abs";
pub const SIN: &str = "sin";
pub const COS: &str = "cos";
pub const TAN: &str = "tan";
pub const SQRT: &str = "sqrt";
pub const FLOOR: &str = "floor";
pub const CEIL: &str = "ceil";
pub const EXP: &str = "exp";
pub const LN: &str = "ln";
pub const SIGN: &str = "sign";
pub const FACTORIAL: &str = "factorial";
pub const ARCSIN: &str = "arcsin";
pub const ARCCOS: &str = "arccos";
pub const ARCTAN: &str = "arctan";
pub const ARCCOT: &str = "arccot";
pub const COT: &str = "cot";
pub const RE: &str = "re";
pub const IMG: &str = "img";
pub const C_ABS: &str = "C_abs";
pub const LOG: &str = "log";
pub const I: &str = "i";
pub const E: &str = "e";
pub const PI: &str = "pi";
pub const UNION: &str = "union";
pub const INTERSECT: &str = "intersect";
pub const SET_MINUS: &str = "set_minus";
pub const FAMILY_UNION: &str = "family_union";
pub const FAMILY_INTERSECT: &str = "family_intersect";
pub const INDEX_UNION: &str = "index_union";
pub const INDEX_INTERSECT: &str = "index_intersect";
pub const POWER_SET: &str = "power_set";
pub const INDEX_CART: &str = "index_cart";
pub const MIN: &str = "min";
pub const MAX: &str = "max";
pub const GCD: &str = "gcd";
pub const LCM: &str = "lcm";
pub const QUOT: &str = "quot";
pub const CART_DIM: &str = "cart_dim";
pub const TUPLE_DIM: &str = "tuple_dim";
pub const PROJ: &str = "proj";
pub const FINITE_SET_SIZE: &str = "finite_set_size";
pub const FINITE_SET_MAX: &str = "finite_set_max";
pub const FINITE_SET_MIN: &str = "finite_set_min";
pub const FN_RANGE: &str = "fn_range";
pub const RANGE: &str = "range";
pub const CLOSED_RANGE: &str = "closed_range";
pub const SUM: &str = "sum";
pub const FINITE_SET_SUM: &str = "finite_set_sum";
pub const PRODUCT: &str = "product";
pub const FINITE_SET_PRODUCT: &str = "finite_set_product";
pub const REDUCE: &str = "reduce";
pub const FINITE_SET_REDUCE: &str = "finite_set_reduce";
pub const INTERVAL_LITERAL_PREFIX: &str = "'";
pub const TEMPLATE_INSTANCE_PREFIX: &str = "\\";
pub const DOT_AKA_FIELD_ACCESS_SIGN: &str = ".";
pub const IS_SET: &str = "is_set";
pub const IS_NONEMPTY_SET: &str = "is_nonempty_set";
pub const IS_FINITE_SET: &str = "is_finite_set";
pub const IS_CART: &str = "is_cart";
pub const IS_TUPLE: &str = "is_tuple";
pub const SUBSET: &str = "subset";
pub const SUPERSET: &str = "superset";
pub const PROPER_SUBSET: &str = "proper_subset";
pub const PROPER_SUPERSET: &str = "proper_superset";
pub const FN_EQ_IN: &str = "fn_eq_in";
pub const ENUMERATE: &str = "enumerate";
pub const EXTENSION: &str = "extension";
pub const FN_EXTENSION: &str = "fn_extension";
pub const TRANSITIVE: &str = "transitive";
pub const SYMMETRIC: &str = "symmetric";
pub const REFLEXIVE: &str = "reflexive";
pub const ZORN_LEMMA: &str = "zorn_lemma";
pub const AXIOM_OF_CHOICE: &str = "axiom_of_choice";
pub const REGULARITY_AXIOM: &str = "regularity_axiom";
pub const REPLACEMENT_AXIOM: &str = "replacement_axiom";
pub const IS_CHOICE_FUNCTION_FOR: &str = "is_choice_function_for";

pub const N: &str = "N";
pub const Z: &str = "Z";
pub const Q: &str = "Q";
pub const R: &str = "R";
pub const C: &str = "C";
pub const N_POS: &str = "N+";
pub const Z_POS: &str = "Z+";
pub const Q_POS: &str = "Q+";
pub const R_POS: &str = "R+";
pub const Z_NEG: &str = "Z-";
pub const Q_NEG: &str = "Q-";
pub const R_NEG: &str = "R-";
pub const Z_STAR: &str = "Z*";
pub const Q_STAR: &str = "Q*";
pub const R_STAR: &str = "R*";
pub const C_STAR: &str = "C*";

pub fn is_comparison_op(tok: &str) -> bool {
    matches!(
        tok,
        EQUAL | NOT_EQUAL | LESS | GREATER | LESS_EQUAL | GREATER_EQUAL
    )
}

pub fn is_comparison_str(atom_name: &str) -> bool {
    is_comparison_op(atom_name)
}
