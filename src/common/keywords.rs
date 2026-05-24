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
pub const POW: &str = "^";
pub const MATRIX_ADD: &str = "++";
pub const MATRIX_SUB: &str = "--";
pub const MATRIX_MUL: &str = "**";
pub const MATRIX_SCALAR_MUL: &str = "*.";
pub const MATRIX_POW: &str = "^^";
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
pub const LEFT_BRACKET: &str = "[";
pub const RIGHT_BRACKET: &str = "]";
pub const DOUBLE_QUOTE: &str = "\"";
pub const COLON: &str = ":";
// Infix operator: one backtick before the name, e.g. A `union B (same role as former A \union B).
pub const INFIX_FN_NAME_SIGN: &str = "`";

pub const UNION: &str = "union";
pub const INTERSECT: &str = "intersect";
pub const SET_MINUS: &str = "set_minus";
pub const SET_DIFF: &str = "set_diff";
pub const CUP: &str = "cup";
pub const CAP: &str = "cap";
pub const POWER_SET: &str = "power_set";
pub const CHOOSE: &str = "choose";
pub const FN_LOWER_CASE: &str = "fn";
/// Prefix for anonymous function literals: `'(x S, …) T { … }` or `'S (x) { … }`.
pub const ANONYMOUS_FN_PREFIX: &str = "'";
pub const SET: &str = "set";
pub const NONEMPTY_SET: &str = "nonempty_set";
pub const FINITE_SET: &str = "finite_set";
pub const N_POS: &str = "N_pos";
pub const N: &str = "N";
pub const Q: &str = "Q";
pub const Z: &str = "Z";
pub const R: &str = "R";
pub const CART: &str = "cart";
pub const CART_DIM: &str = "cart_dim";
pub const TUPLE_DIM: &str = "tuple_dim";
pub const PROJ: &str = "proj";
pub const COUNT: &str = "count";
pub const FINITE_SEQ: &str = "finite_seq";
pub const SEQ: &str = "seq";
pub const MATRIX: &str = "matrix";
pub const RANGE: &str = "range";
pub const CLOSED_RANGE: &str = "closed_range";
pub const OO: &str = "oo";
pub const OC: &str = "oc";
pub const CO: &str = "co";
pub const CC: &str = "cc";
pub const SUM: &str = "sum";
pub const PRODUCT: &str = "product";
pub const EXIST: &str = "exist";
/// User-facing spelling for unique existence (`exist` + `!` as two tokens in the source).
pub const EXIST_BANG: &str = "exist!";
pub const ST: &str = "st";
pub const FORALL: &str = "forall";
/// User-facing spelling for inline universal quantification (`forall` + `!` as two tokens).
pub const FORALL_BANG: &str = "forall!";
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
pub const SUCCESS_COLON: &str = "Success:";
pub const UNKNOWN_COLON: &str = "Unknown:";
pub const LET: &str = "let";
pub const PROP: &str = "prop";
/// Predicate symbol declared by name and parameter list only (no `:` / definition body); cf. `prop` with iff body.
pub const ABSTRACT_PROP: &str = "abstract_prop";
pub const CLAIM: &str = "claim";
pub const PROVE: &str = "prove";

pub const BY: &str = "by";
pub const DECREASING: &str = "decreasing";
pub const CASES: &str = "cases";
pub const CONTRA: &str = "contra";
pub const ENUMERATE: &str = "enumerate";
pub const INDUC: &str = "induc";
/// Strong (complete) induction on integers: same shape as `by induc`, but the step uses a `forall` band hypothesis.
pub const STRONG_INDUC: &str = "strong_induc";
/// 保留名（旧版最后一项 `case` 曾用 `param = param_2 + n`）；当前语法最后一项为 `case >= n:`（n 为特例个数），不再登记此名。
pub const INDUC_PARAM_2_NAME: &str = "param_2";
pub const FOR: &str = "for";
pub const EXTENSION: &str = "extension";
pub const TRANSITIVE_PROP: &str = "transitive_prop";
pub const SYMMETRIC_PROP: &str = "symmetric_prop";
pub const REFLEXIVE_PROP: &str = "reflexive_prop";
pub const ANTISYMMETRIC_PROP: &str = "antisymmetric_prop";
pub const TUPLE: &str = "tuple";

pub const CASE: &str = "case";
pub const IMPORT: &str = "import";
pub const AS: &str = "as";
pub const HAVE: &str = "have";
pub const KNOW: &str = "know";
pub const CLEAR: &str = "clear";
pub const DO_NOTHING: &str = "do_nothing";
pub const RUN_FILE: &str = "run_file";
pub const FROM: &str = "from";
pub const EVAL: &str = "eval";
pub const WITNESS: &str = "witness";
pub const IMPOSSIBLE: &str = "impossible";
pub const ALGO: &str = "algo";
pub const ABS: &str = "abs";
pub const SQRT: &str = "sqrt";
pub const LOG: &str = "log";
pub const MAX: &str = "max";
pub const MIN: &str = "min";
pub const Q_POS: &str = "Q_pos";
pub const R_POS: &str = "R_pos";
pub const Q_NEG: &str = "Q_neg";
pub const Z_NEG: &str = "Z_neg";
pub const R_NEG: &str = "R_neg";
pub const Q_NZ: &str = "Q_nz";
pub const Z_NZ: &str = "Z_nz";
pub const R_NZ: &str = "R_nz";
pub const STRUCT: &str = "struct";
pub const TEMPLATE: &str = "template";
pub const RESTRICT_FN_IN: &str = "restrict_fn_in";
pub const STRATEGY: &str = "strategy";
pub const USE_STRATEGY: &str = "use_strategy";
pub const END_STRATEGY: &str = "end_strategy";
/// `$fn_eq_in(f, g, S)`: f and g agree on domain set S (encoded as a forall; see verify builtin).
pub const FN_EQ_IN: &str = "fn_eq_in";
/// `$fn_eq(f, g)`: mutual function-space typing and pointwise equality on the shared dom (see verify).
pub const FN_EQ: &str = "fn_eq";
pub const INJECTIVE: &str = "injective";
pub const SURJECTIVE: &str = "surjective";
pub const BIJECTIVE: &str = "bijective";

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
        FACT_PREFIX,
        DOT_AKA_FIELD_ACCESS_SIGN,
        MOD_SIGN,
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
        INFIX_FN_NAME_SIGN,
        ANONYMOUS_FN_PREFIX,
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
        SET_DIFF,
        CUP,
        CAP,
        POWER_SET,
        CHOOSE,
        FN_LOWER_CASE,
        SET,
        NONEMPTY_SET,
        FINITE_SET,
        N_POS,
        N,
        Q,
        Z,
        R,
        CART,
        CART_DIM,
        TUPLE_DIM,
        PROJ,
        COUNT,
        SUM,
        PRODUCT,
        FINITE_SEQ,
        SEQ,
        MATRIX,
        RANGE,
        CLOSED_RANGE,
        OO,
        OC,
        CO,
        CC,
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
        SUCCESS_COLON,
        UNKNOWN_COLON,
        LET,
        PROP,
        ABSTRACT_PROP,
        CLAIM,
        PROVE,
        BY,
        DECREASING,
        CASES,
        CONTRA,
        CASE,
        IMPORT,
        AS,
        ENUMERATE,
        HAVE,
        KNOW,
        CLEAR,
        DO_NOTHING,
        RUN_FILE,
        INDUC,
        STRONG_INDUC,
        FROM,
        EVAL,
        FOR,
        WITNESS,
        EXTENSION,
        TRANSITIVE_PROP,
        IMPOSSIBLE,
        TUPLE,
        ALGO,
        ABS,
        SQRT,
        LOG,
        MAX,
        MIN,
        Q_POS,
        R_POS,
        Q_NEG,
        Z_NEG,
        R_NEG,
        Q_NZ,
        Z_NZ,
        R_NZ,
        STRUCT,
        TEMPLATE,
        RESTRICT_FN_IN,
        STRATEGY,
        USE_STRATEGY,
        END_STRATEGY,
        FN_EQ_IN,
        FN_EQ,
    ];
    for &s in &words {
        m.insert(s, s);
    }
    m
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
    keywords_map().contains_key(atom_name)
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
        || atom_name == IN
        || atom_name == RESTRICT_FN_IN
        || atom_name == FN_EQ_IN
        || atom_name == FN_EQ
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
        || atom_name == Q_POS
        || atom_name == R_POS
        || atom_name == Q_NEG
        || atom_name == Z_NEG
        || atom_name == R_NEG
        || atom_name == Q_NZ
        || atom_name == Z_NZ
        || atom_name == R_NZ
        || atom_name == N_POS
        || atom_name == N
        || atom_name == Q
        || atom_name == Z
        || atom_name == R
}
