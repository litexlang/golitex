//! Short spellings share the existing builtin's parser and mathematical contract.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BuiltinAliasKind {
    Object,
    Predicate,
    Theorem,
}

pub(crate) const BUILTIN_ALIASES: &[(&str, &str, BuiltinAliasKind)] = &[
    ("deriv", "derivative", BuiltinAliasKind::Object),
    ("pderiv", "partial_derivative", BuiltinAliasKind::Object),
    ("grad_at", "gradient_at", BuiltinAliasKind::Object),
    ("set_sum", "finite_set_sum", BuiltinAliasKind::Object),
    ("set_prod", "finite_set_product", BuiltinAliasKind::Object),
    ("integ", "integral", BuiltinAliasKind::Object),
    (
        "diff_at",
        "is_differentiable_at",
        BuiltinAliasKind::Predicate,
    ),
    (
        "has_deriv_at",
        "has_derivative_at",
        BuiltinAliasKind::Predicate,
    ),
    ("cont_at", "is_continuous_at", BuiltinAliasKind::Predicate),
    (
        "cont_left",
        "is_continuous_left",
        BuiltinAliasKind::Predicate,
    ),
    (
        "cont_right",
        "is_continuous_right",
        BuiltinAliasKind::Predicate,
    ),
    (
        "unif_cont",
        "is_uniformly_continuous",
        BuiltinAliasKind::Predicate,
    ),
    (
        "deriv_add",
        "fn_derivative_at_add",
        BuiltinAliasKind::Theorem,
    ),
    (
        "deriv_sub",
        "fn_derivative_at_subtract",
        BuiltinAliasKind::Theorem,
    ),
    (
        "deriv_mul",
        "fn_derivative_at_multiply",
        BuiltinAliasKind::Theorem,
    ),
    (
        "deriv_div",
        "fn_derivative_at_divide",
        BuiltinAliasKind::Theorem,
    ),
    (
        "deriv_chain",
        "fn_derivative_at_compose",
        BuiltinAliasKind::Theorem,
    ),
    (
        "deriv_pow",
        "fn_derivative_at_power",
        BuiltinAliasKind::Theorem,
    ),
    (
        "diff_cont",
        "fn_differentiable_at_continuous",
        BuiltinAliasKind::Theorem,
    ),
    ("fn_lim_add", "fn_limit_at_add", BuiltinAliasKind::Theorem),
    (
        "seq_cauchy_convergent",
        "sequence_cauchy_convergent",
        BuiltinAliasKind::Theorem,
    ),
    (
        "integ_add",
        "riemann_integral_add",
        BuiltinAliasKind::Theorem,
    ),
    (
        "integ_sub",
        "riemann_integral_subtract",
        BuiltinAliasKind::Theorem,
    ),
    (
        "integ_scale",
        "riemann_integral_scale",
        BuiltinAliasKind::Theorem,
    ),
    (
        "integ_parts",
        "riemann_integral_by_parts",
        BuiltinAliasKind::Theorem,
    ),
];

pub(crate) fn canonical_builtin_name(name: &str, kind: BuiltinAliasKind) -> &str {
    BUILTIN_ALIASES
        .iter()
        .find(|(short, _, alias_kind)| *short == name && *alias_kind == kind)
        .map_or(name, |(_, canonical, _)| *canonical)
}
