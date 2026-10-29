"""Audit the actual reachable rule inventory, not a hand-maintained rule count."""
import unittest
from generate_capture import Generator


class RuleCommentCoverageTests(unittest.TestCase):
    def test_every_reachable_builtin_owner_has_bilingual_methods_and_capture(self):
        generator = Generator()
        generated = generator.generate()
        rules = [rule for rule in generator.rules if rule['category'] == 'builtin']
        self.assertGreater(len(rules), 600)
        for rule in rules:
            owner, = generator.by_name[rule['family']]
            self.assertTrue({'en', 'zh'}.issubset(generator.comment_languages[owner]), rule['id'])
            self.assertIn('Some("' + rule['id'] + '")', generated)
        self.assertGreaterEqual(generated.count('capture.rule_comments('), len(rules))
        self.assertFalse(generator.unknown)


if __name__ == '__main__':
    unittest.main()
