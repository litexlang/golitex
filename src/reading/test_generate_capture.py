import unittest

from generate_capture import clean, is_result_mode_dispatcher, match_arms, static_text


class RustSourceScanTests(unittest.TestCase):
    def test_block_match_arms_without_commas_preserve_every_rule(self):
        source = 'Self::First(_) => { text("first", "one") } Self::Second(p) => p.copy(), Self::Third { .. } => { text("third", "three") }'
        arms = [source[a:b] for a, b in match_arms(clean(source))]
        self.assertEqual(len(arms), 3)
        self.assertEqual(static_text(arms[0].split('=>', 1)[1]), {'name': 'first', 'message': 'one'})
        self.assertEqual(static_text(arms[2].split('=>', 1)[1]), {'name': 'third', 'message': 'three'})

    def test_self_constructor_in_an_expression_is_not_a_new_arm(self):
        source = 'Self::First(_) => Self::create(), Self::Second(_) => text("two", "second"),'
        self.assertEqual(len(list(match_arms(clean(source)))), 2)

    def test_static_comment_struct_and_qualified_text_keep_exact_copy(self):
        self.assertEqual(static_text('BuiltinRuleText { rule_name: "名称".into(), message: "含义".to_string(), },'), {'name': '名称', 'message': '含义'})
        self.assertEqual(static_text('crate::json_output::explain::text::text("名称", "含义"),'), {'name': '名称', 'message': '含义'})
        self.assertIsNone(static_text('text(self.rule_id(), self.law())'))

    def test_rust_only_literal_escape_is_left_to_the_owning_method(self):
        self.assertIsNone(static_text(r'text("name", "\u{03b1}")'))

    def test_result_modes_are_recognized_by_the_typed_enum_shape(self):
        record = {'kind': 'enum', 'variants': [(name, '(', [('0', name + 'Proof')]) for name in ['Compact', 'Normal', 'Detailed']]}
        self.assertTrue(is_result_mode_dispatcher(record))
        record['variants'].append(('ByKnown', '(', [('0', 'KnownProof')]))
        self.assertFalse(is_result_mode_dispatcher(record))

    def test_continued_string_does_not_hide_following_declarations(self):
        source = 'const SOURCE: &str = "first\\\nsecond";\npub struct Checked { pub id: u64 }\n'
        scanned = clean(source)
        self.assertEqual(len(scanned), len(source))
        self.assertIn('pub struct Checked { pub id: u64 }', scanned)
        self.assertNotIn('second', scanned)

    def test_declarations_inside_strings_and_comments_stay_hidden(self):
        source = 'const SOURCE: &str = "pub struct Fake\\\n{ pub id: u64 }";\n// pub struct Comment;\npub enum Real { A }'
        scanned = clean(source)
        self.assertNotIn('Fake', scanned)
        self.assertNotIn('Comment', scanned)
        self.assertIn('pub enum Real { A }', scanned)


if __name__ == '__main__':
    unittest.main()
