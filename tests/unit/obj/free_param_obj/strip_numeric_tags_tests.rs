use super::strip_free_param_numeric_tags_in_display;

#[test]
fn tilde_digits_removed_suffix_kept() {
    assert_eq!(strip_free_param_numeric_tags_in_display("~2aaa"), "aaa");
    assert_eq!(
        strip_free_param_numeric_tags_in_display(r#""x": "~2foo""#),
        r#""x": "foo""#
    );
}

#[test]
fn tilde_not_followed_by_digit_kept() {
    assert_eq!(
        strip_free_param_numeric_tags_in_display("~/tmp.lit"),
        "~/tmp.lit"
    );
    assert_eq!(strip_free_param_numeric_tags_in_display("~"), "~");
}

#[test]
fn symbol_identity_prefix_is_removed_without_touching_ordinary_hash_text() {
    assert_eq!(
        strip_free_param_numeric_tags_in_display("#17#A::x = #42#y"),
        "A::x = y"
    );
    assert_eq!(
        strip_free_param_numeric_tags_in_display("#abc #12"),
        "#abc #12"
    );
}

#[test]
fn generated_binder_names_are_stable_and_hide_internal_ids() {
    assert_eq!(
        strip_free_param_numeric_tags_in_display(
            "forall #17##binder_17, #42##binder_42: #17##binder_17 = #42##binder_42"
        ),
        "forall _generated_1, _generated_2: _generated_1 = _generated_2"
    );
}
