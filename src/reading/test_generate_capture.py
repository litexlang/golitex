import unittest

from generate_capture import clean, is_result_mode_dispatcher


class RustSourceScanTests(unittest.TestCase):
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
