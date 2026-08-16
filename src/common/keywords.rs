use std::collections::HashMap;
use std::sync::OnceLock;

pub const FACT_PREFIX: &str = "$";
pub const STRUCT_VIEW_PREFIX: &str = "&";
pub const TEMPLATE_INSTANCE_PREFIX: &str = "\\";
pub const DOT_AKA_FIELD_ACCESS_SIGN: &str = ".";
/// Infix closed integer interval: `lo ... hi` (same AST as `closed_range(lo, hi)`).
pub const DOT_DOT_DOT: &str = "...";
pub const MOD_SIGN: &str = "::";
pub const ADD: &str = "+";
pub const SUB: &str = "-";
pub const MUL: &str = "*";
pub const DIV: &str = "/";
pub const MOD: &str = "%";
pub const GCD: &str = "gcd";
pub const LCM: &str = "lcm";
pub const FLOOR: &str = "floor";
pub const CEIL: &str = "ceil";
pub const MIN: &str = "min";
pub const MAX: &str = "max";
pub const EXP: &str = "exp";
pub const LN: &str = "ln";
pub const SIGN: &str = "sign";
pub const FACTORIAL: &str = "factorial";
pub const POW: &str = "^";
/// Matrix addition. Example: `A '+ B`.
pub const MATRIX_ADD: &str = "'+";
/// Matrix subtraction. Example: `A '- B`.
pub const MATRIX_SUB: &str = "'-";
/// Matrix multiplication. Example: `A '* B`.
pub const MATRIX_MUL: &str = "'*";
/// Scalar multiplication of a matrix. Example: `c *' A`.
pub const MATRIX_SCALAR_MUL: &str = "*'";
/// Matrix power. Example: `A '^ n`.
pub const MATRIX_POW: &str = "'^";
pub const LEFT_BRACE: &str = "(";
pub const RIGHT_BRACE: &str = ")";
pub const COMMA: &str = ",";
pub const LEFT_CURLY_BRACE: &str = "{";
pub const RIGHT_CURLY_BRACE: &str = "}";
pub const EQUAL: &str = "=";
pub const NOT_EQUAL: &str = "!=";
pub const LESS: &str = "<";
pub const GREATER: &str = ">";
pub const LESS_EQUAL: &str = "<=";
pub const GREATER_EQUAL: &str = ">=";
pub const RIGHT_ARROW: &str = "=>";
pub const EQUIVALENT_SIGN: &str = "<=>";
pub const QUESTION_GOAL: &str = "?";
pub const LEFT_BRACKET: &str = "[";
pub const RIGHT_BRACKET: &str = "]";
pub const DOUBLE_QUOTE: &str = "\"";
pub const COLON: &str = ":";
pub const SETTING: &str = "setting";
pub const UNFOLD: &str = "unfold";

pub const UNION: &str = "union";
pub const INTERSECT: &str = "intersect";
/// Unicode-only infix set union. Canonical rendering remains `union(A, B)`.
pub const UNICODE_UNION: &str = "∪";
/// Unicode-only infix set intersection. Canonical rendering remains `intersect(A, B)`.
pub const UNICODE_INTERSECT: &str = "∩";
/// Unicode-only infix Cartesian product. Canonical rendering remains `cart(A, B)`.
pub const UNICODE_CART: &str = "×";
/// Unicode-only negated membership. Canonical rendering remains `not x $in A`.
pub const UNICODE_NOT_IN: &str = "∉";
pub const SET_MINUS: &str = "set_minus";
pub const BIG_UNION: &str = "big_union";
pub const BIG_INTERSECT: &str = "big_intersect";
pub const POWER_SET: &str = "power_set";
pub const GENERAL_CART: &str = "general_cart";
pub const FN_LOWER_CASE: &str = "fn";
/// Prefix for a real interval literal, such as `'(a, b)`, `'[a,)`, or `'(,b]`.
pub const INTERVAL_LITERAL_PREFIX: &str = "'";
pub const SET: &str = "set";
pub const NONEMPTY_SET: &str = "nonempty_set";
pub const FINITE_SET: &str = "finite_set";
/// Mathematical spellings for signed and nonzero standard sets.
pub const N_POSITIVE: &str = "N+";
pub const Z_POSITIVE: &str = "Z+";
pub const Q_POSITIVE: &str = "Q+";
pub const R_POSITIVE: &str = "R+";
pub const Z_NEGATIVE: &str = "Z-";
pub const Q_NEGATIVE: &str = "Q-";
pub const R_NEGATIVE: &str = "R-";
pub const Z_NOT_ZERO: &str = "Z*";
pub const Q_NOT_ZERO: &str = "Q*";
pub const R_NOT_ZERO: &str = "R*";
pub const C_NOT_ZERO: &str = "C*";
pub const N: &str = "N";
pub const Q: &str = "Q";
pub const Z: &str = "Z";
pub const R: &str = "R";
pub const C: &str = "C";
pub const I: &str = "i";
pub const E: &str = "e";
pub const PI: &str = "pi";
pub const RE: &str = "re";
pub const IMG: &str = "img";
pub const C_ABS: &str = "C_abs";
pub const CART: &str = "cart";
pub const CART_DIM: &str = "cart_dim";
pub const TUPLE_DIM: &str = "tuple_dim";
pub const PROJ: &str = "proj";
pub const FINITE_SET_SIZE: &str = "finite_set_size";
pub const FINITE_SET_MAX: &str = "finite_set_max";
pub const FINITE_SET_MIN: &str = "finite_set_min";
pub const FN_RANGE: &str = "fn_range";
pub const REPLACEMENT: &str = "replacement";
pub const FINITE_SEQ: &str = "finite_seq";
pub const SEQ: &str = "seq";
pub const MATRIX: &str = "matrix";
pub const RANGE: &str = "range";
pub const CLOSED_RANGE: &str = "closed_range";
pub const SUM: &str = "sum";
pub const FINITE_SET_SUM: &str = "finite_set_sum";
pub const PRODUCT: &str = "product";
pub const FINITE_SET_PRODUCT: &str = "finite_set_product";
pub const REDUCE: &str = "reduce";
pub const FINITE_SET_REDUCE: &str = "finite_set_reduce";
pub const EXIST: &str = "exist";
/// User-facing spelling for unique existence (`exist` + `!` as two tokens in the source).
pub const EXIST_BANG: &str = "exist!";
pub const ST: &str = "st";
pub const FORALL: &str = "forall";
pub const NOT: &str = "not";
pub const IS_SET: &str = "is_set";
pub const IS_NONEMPTY_SET: &str = "is_nonempty_set";
pub const IS_FINITE_SET: &str = "is_finite_set";
pub const IS_CART: &str = "is_cart";
pub const IS_TUPLE: &str = "is_tuple";
pub const IN: &str = "in";
pub const OR: &str = "or";
pub const AND: &str = "and";
pub const SUBSET: &str = "subset";
pub const SUPERSET: &str = "superset";
pub const PROPER_SUBSET: &str = "proper_subset";
pub const PROPER_SUPERSET: &str = "proper_superset";
pub const SUCCESS_COLON: &str = "Success:";
pub const UNKNOWN_COLON: &str = "Unknown:";
pub const PROP: &str = "prop";
/// Predicate symbol declared by name and parameter list only (no `:` / definition body); cf. `prop` with iff body.
pub const ABSTRACT_PROP: &str = "abstract_prop";
pub const CLAIM: &str = "claim";
pub const EXAMPLE: &str = "example";
pub const SKETCH: &str = "sketch";
pub const TRY: &str = "try";
pub const THM: &str = "thm";
pub const AXIOM: &str = "axiom";
pub const STOP: &str = "stop";
pub const USE: &str = "use";

pub const BY: &str = "by";
/// Contextual keyword used only after `by`; intentionally not globally reserved.
pub const DEF: &str = "def";
pub const CASES: &str = "cases";
pub const CONTRA: &str = "contra";
pub const ENUMERATE: &str = "enumerate";
pub const INDUC: &str = "induc";
/// Strong (complete) induction on integers: same shape as `by induc`, but the step uses a `forall` band hypothesis.
pub const STRONG_INDUC: &str = "strong_induc";
/// Reserved helper name for older induction-case expansion forms.
pub const INDUC_PARAM_2_NAME: &str = "param_2";
pub const FOR: &str = "for";
pub const EXTENSION: &str = "extension";
pub const TRANSITIVE_PROP: &str = "transitive_prop";
pub const SYMMETRIC_PROP: &str = "symmetric_prop";
pub const REFLEXIVE_PROP: &str = "reflexive_prop";
pub const ANTISYMMETRIC_PROP: &str = "antisymmetric_prop";
pub const ZORN_LEMMA: &str = "zorn_lemma";
pub const AXIOM_OF_CHOICE: &str = "axiom_of_choice";
pub const REGULARITY_AXIOM: &str = "regularity_axiom";
pub const TUPLE: &str = "tuple";

pub const CASE: &str = "case";
pub const TRUST: &str = "trust";
pub const IMPORT: &str = "import";
pub const STD: &str = "std";
pub const AS: &str = "as";
pub const HAVE: &str = "have";
pub const LET: &str = "let";
pub const OBTAIN: &str = "obtain";
pub const CLEAR: &str = "clear";
pub const DO_NOTHING: &str = "do_nothing";
pub const FROM: &str = "from";
pub const EVAL: &str = "eval";
pub const WITNESS: &str = "witness";
pub const PREIMAGE: &str = "preimage";
pub const IMPOSSIBLE: &str = "impossible";
pub const ALGO: &str = "algo";
pub const ABS: &str = "abs";
pub const SIN: &str = "sin";
pub const COS: &str = "cos";
pub const TAN: &str = "tan";
pub const COT: &str = "cot";
pub const SQRT: &str = "sqrt";
pub const LOG: &str = "log";
pub const STRUCT: &str = "struct";
pub const TEMPLATE: &str = "template";
pub const STRATEGY: &str = "strategy";
/// `$fn_eq_in(f, g, S)`: f and g agree on domain set S (encoded as a forall; see verify builtin).
pub const FN_EQ_IN: &str = "fn_eq_in";
/// `$fn_eq(f, g)`: mutual function-space typing and pointwise equality on the shared dom (see verify).
pub const FN_EQ: &str = "fn_eq";
pub const INJECTIVE: &str = "injective";
pub const SURJECTIVE: &str = "surjective";
pub const BIJECTIVE: &str = "bijective";
pub const PRIME: &str = "prime";
pub const COPRIME: &str = "coprime";
pub const IS_CHOICE_FUNCTION_FOR: &str = "is_choice_function_for";

fn build_key_symbols_map() -> HashMap<&'static str, &'static str> {
    let mut m = HashMap::new();
    let symbols = [
        STRUCT_VIEW_PREFIX,
        TEMPLATE_INSTANCE_PREFIX,
        EQUIVALENT_SIGN,
        NOT_EQUAL,
        LESS_EQUAL,
        GREATER_EQUAL,
        RIGHT_ARROW,
        QUESTION_GOAL,
        FACT_PREFIX,
        DOT_AKA_FIELD_ACCESS_SIGN,
        MOD_SIGN,
        N_POSITIVE,
        Z_POSITIVE,
        Q_POSITIVE,
        R_POSITIVE,
        Z_NEGATIVE,
        Q_NEGATIVE,
        R_NEGATIVE,
        Z_NOT_ZERO,
        Q_NOT_ZERO,
        R_NOT_ZERO,
        C_NOT_ZERO,
        ADD,
        SUB,
        MUL,
        DIV,
        MOD,
        POW,
        MATRIX_POW,
        MATRIX_MUL,
        MATRIX_SCALAR_MUL,
        MATRIX_ADD,
        MATRIX_SUB,
        DOT_DOT_DOT,
        LEFT_BRACE,
        RIGHT_BRACE,
        COMMA,
        LEFT_CURLY_BRACE,
        RIGHT_CURLY_BRACE,
        EQUAL,
        LESS,
        GREATER,
        LEFT_BRACKET,
        RIGHT_BRACKET,
        DOUBLE_QUOTE,
        COLON,
        INTERVAL_LITERAL_PREFIX,
        UNICODE_UNION,
        UNICODE_INTERSECT,
        UNICODE_CART,
        UNICODE_NOT_IN,
    ];
    for &s in &symbols {
        m.insert(s, s);
    }
    m
}

fn build_keywords_map() -> HashMap<&'static str, &'static str> {
    let mut m = HashMap::new();
    let words = [
        UNION,
        INTERSECT,
        SET_MINUS,
        BIG_UNION,
        BIG_INTERSECT,
        POWER_SET,
        GENERAL_CART,
        FN_LOWER_CASE,
        SET,
        NONEMPTY_SET,
        FINITE_SET,
        N,
        Q,
        Z,
        R,
        C,
        I,
        E,
        PI,
        RE,
        IMG,
        C_ABS,
        CART,
        CART_DIM,
        TUPLE_DIM,
        PROJ,
        FINITE_SET_SIZE,
        FINITE_SET_MAX,
        FINITE_SET_MIN,
        GCD,
        LCM,
        FLOOR,
        CEIL,
        MIN,
        MAX,
        EXP,
        LN,
        SIGN,
        FACTORIAL,
        FN_RANGE,
        REPLACEMENT,
        SUM,
        FINITE_SET_SUM,
        PRODUCT,
        FINITE_SET_PRODUCT,
        REDUCE,
        FINITE_SET_REDUCE,
        FINITE_SEQ,
        SEQ,
        MATRIX,
        RANGE,
        CLOSED_RANGE,
        EXIST,
        ST,
        FORALL,
        NOT,
        IS_SET,
        IS_NONEMPTY_SET,
        IS_FINITE_SET,
        IS_CART,
        IS_TUPLE,
        IN,
        OR,
        AND,
        SUBSET,
        SUPERSET,
        PROP,
        ABSTRACT_PROP,
        CLAIM,
        EXAMPLE,
        SKETCH,
        TRY,
        THM,
        AXIOM,
        STOP,
        USE,
        BY,
        CASES,
        CONTRA,
        CASE,
        TRUST,
        IMPORT,
        STD,
        AS,
        ENUMERATE,
        HAVE,
        LET,
        OBTAIN,
        CLEAR,
        DO_NOTHING,
        INDUC,
        STRONG_INDUC,
        FROM,
        EVAL,
        FOR,
        WITNESS,
        PREIMAGE,
        EXTENSION,
        TRANSITIVE_PROP,
        ZORN_LEMMA,
        AXIOM_OF_CHOICE,
        IMPOSSIBLE,
        TUPLE,
        ALGO,
        ABS,
        SIN,
        COS,
        TAN,
        COT,
        SQRT,
        LOG,
        STRUCT,
        TEMPLATE,
        SETTING,
        UNFOLD,
        STRATEGY,
        FN_EQ_IN,
        FN_EQ,
        INJECTIVE,
        SURJECTIVE,
        BIJECTIVE,
        PRIME,
        COPRIME,
        PROPER_SUBSET,
        PROPER_SUPERSET,
    ];
    for &s in &words {
        m.insert(s, s);
    }
    m
}

/// Canonical ASCII tokens for supported Unicode mathematical input aliases.
///
/// Unicode spellings are surface syntax only. The parser, stored facts, and
/// rendered diagnostics continue to use the existing ASCII tokens.
pub(crate) fn unicode_alias_tokens(token: &str) -> Option<&'static [&'static str]> {
    match token {
        "∀" => Some(&[FORALL]),
        "∃" => Some(&[EXIST]),
        "≤" => Some(&[LESS_EQUAL]),
        "≥" => Some(&[GREATER_EQUAL]),
        "≠" => Some(&[NOT_EQUAL]),
        "→" => Some(&[RIGHT_ARROW]),
        "↔" => Some(&[EQUIVALENT_SIGN]),
        "∧" => Some(&[AND]),
        "∨" => Some(&[OR]),
        "¬" => Some(&[NOT]),
        "∈" => Some(&[FACT_PREFIX, IN]),
        "⊆" => Some(&[FACT_PREFIX, SUBSET]),
        "⊇" => Some(&[FACT_PREFIX, SUPERSET]),
        "⊊" => Some(&[FACT_PREFIX, PROPER_SUBSET]),
        "⊋" => Some(&[FACT_PREFIX, PROPER_SUPERSET]),
        "⊂" => Some(&[FACT_PREFIX, PROPER_SUBSET]),
        "ℕ" => Some(&[N]),
        "ℤ" => Some(&[Z]),
        "ℚ" => Some(&[Q]),
        "ℝ" => Some(&[R]),
        "ℂ" => Some(&[C]),
        "π" => Some(&[PI]),
        "∅" => Some(&[LEFT_CURLY_BRACE, RIGHT_CURLY_BRACE]),
        _ => None,
    }
}

static KEY_SYMBOLS_MAP: OnceLock<HashMap<&'static str, &'static str>> = OnceLock::new();
static KEYWORDS_MAP: OnceLock<HashMap<&'static str, &'static str>> = OnceLock::new();

fn key_symbols_map() -> &'static HashMap<&'static str, &'static str> {
    KEY_SYMBOLS_MAP.get_or_init(build_key_symbols_map)
}

fn keywords_map() -> &'static HashMap<&'static str, &'static str> {
    KEYWORDS_MAP.get_or_init(build_keywords_map)
}

pub fn key_symbols_sorted_by_len_desc() -> Vec<&'static str> {
    let mut v: Vec<&'static str> = key_symbols_map().keys().copied().collect();
    v.sort_by(|a, b| b.len().cmp(&a.len()));
    v
}

pub fn is_keyword(atom_name: &str) -> bool {
    keywords_map().contains_key(atom_name) || is_builtin_theorem_name(atom_name)
}

pub fn is_builtin_theorem_name(name: &str) -> bool {
    matches!(
        name,
        "fn_set_member"
            | "set_builder_member"
            | "defined_set_member"
            | "struct_member"
            | "cart_member_from_coordinates"
            | "general_cart_member"
            | "general_cart_nonempty_by_choice_from_family"
            | "general_cart_nonempty_by_choice_from_pointwise"
            | "sum_le_sum_from_pointwise"
            | "finite_set_sum_le_from_pointwise"
            | "finite_set_summand_le_sum"
            | "tuple_equal_from_coordinates"
            | "finite_set_sum_substitution"
            | "sum_over_bijective_finite_set_enumerations"
            | "rational_has_unique_reduced_fraction"
            | "subset_of_finite_set_is_finite"
            | "finite_set_has_bijective_index"
    )
}

fn is_key_symbol(atom_name: &str) -> bool {
    key_symbols_map().contains_key(atom_name)
}

pub fn is_key_symbol_or_keyword(atom_name: &str) -> bool {
    is_key_symbol(atom_name) || is_keyword(atom_name)
}

pub fn is_comparison_str(atom_name: &str) -> bool {
    atom_name == EQUAL
        || atom_name == NOT_EQUAL
        || atom_name == LESS
        || atom_name == GREATER
        || atom_name == LESS_EQUAL
        || atom_name == GREATER_EQUAL
}

pub fn is_builtin_predicate(atom_name: &str) -> bool {
    atom_name == EQUAL
        || atom_name == NOT_EQUAL
        || atom_name == LESS
        || atom_name == GREATER
        || atom_name == LESS_EQUAL
        || atom_name == GREATER_EQUAL
        || atom_name == IS_SET
        || atom_name == IS_NONEMPTY_SET
        || atom_name == IS_FINITE_SET
        || atom_name == IS_CART
        || atom_name == IS_TUPLE
        || atom_name == SUBSET
        || atom_name == SUPERSET
        || atom_name == PROPER_SUBSET
        || atom_name == PROPER_SUPERSET
        || atom_name == IN
        || atom_name == FN_EQ_IN
        || atom_name == FN_EQ
        || atom_name == INJECTIVE
        || atom_name == SURJECTIVE
        || atom_name == BIJECTIVE
        || atom_name == PRIME
        || atom_name == COPRIME
        || atom_name == IS_CHOICE_FUNCTION_FOR
}

pub fn is_builtin_identifier_name(atom_name: &str) -> bool {
    atom_name == ADD
        || atom_name == SUB
        || atom_name == MUL
        || atom_name == DIV
        || atom_name == MOD
        || atom_name == POW
        || atom_name == MATRIX_ADD
        || atom_name == MATRIX_SUB
        || atom_name == MATRIX_MUL
        || atom_name == MATRIX_SCALAR_MUL
        || atom_name == MATRIX_POW
        || atom_name == N_POSITIVE
        || atom_name == Z_POSITIVE
        || atom_name == Q_POSITIVE
        || atom_name == R_POSITIVE
        || atom_name == Z_NEGATIVE
        || atom_name == Q_NEGATIVE
        || atom_name == R_NEGATIVE
        || atom_name == Z_NOT_ZERO
        || atom_name == Q_NOT_ZERO
        || atom_name == R_NOT_ZERO
        || atom_name == C_NOT_ZERO
        || atom_name == N
        || atom_name == Q
        || atom_name == Z
        || atom_name == R
        || atom_name == FINITE_SET_SIZE
        || atom_name == FINITE_SET_MAX
        || atom_name == FINITE_SET_MIN
        || atom_name == GCD
        || atom_name == LCM
        || atom_name == FLOOR
        || atom_name == CEIL
        || atom_name == MIN
        || atom_name == MAX
        || atom_name == EXP
        || atom_name == LN
        || atom_name == SIGN
        || atom_name == FACTORIAL
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn output_labels_are_not_source_keywords() {
        assert!(!is_keyword(SUCCESS_COLON));
        assert!(!is_keyword(UNKNOWN_COLON));
    }

    #[test]
    fn by_def_uses_a_contextual_keyword() {
        assert!(!is_keyword(DEF));
    }

    #[test]
    fn let_is_a_source_keyword() {
        assert!(is_keyword(LET));
    }
}
