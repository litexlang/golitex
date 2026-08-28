import csv
import tempfile
import unittest
from collections import Counter
from pathlib import Path

import run_experiment


class ExperimentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.annotations_path = run_experiment.default_annotations_path()
        cls.repository_root = run_experiment.default_repository_root()
        cls.annotations = run_experiment.load_annotations(cls.annotations_path)

    def test_pilot_counts_and_tracer(self):
        self.assertEqual(
            Counter(annotation.label for annotation in self.annotations),
            Counter({"F": 28, "E": 22, "FH": 16, "H": 6}),
        )
        tracer = [
            annotation
            for annotation in self.annotations
            if annotation.slice_id == "addition_induction_proofs"
        ]
        self.assertEqual(len(tracer), 18)
        self.assertEqual(
            Counter(annotation.label for annotation in tracer),
            Counter({"FH": 8, "H": 6, "F": 4}),
        )

    def test_midpoint_metrics(self):
        summary = run_experiment.summarize(self.annotations)
        self.assertEqual(summary.total, 72)
        self.assertEqual(summary.proof_relevant, 50)
        self.assertAlmostEqual(summary.fact_lower, 0.56)
        self.assertAlmostEqual(summary.fact_midpoint, 0.72)
        self.assertAlmostEqual(summary.fact_upper, 0.88)
        self.assertAlmostEqual(summary.how_midpoint, 0.28)

    def test_source_references_and_short_cues(self):
        run_experiment.validate_sources(self.annotations, self.repository_root)
        self.assertTrue(all(len(annotation.cue.split()) <= 12 for annotation in self.annotations))

    def test_invalid_label_is_rejected(self):
        path = self.write_modified_csv(label="UNKNOWN")
        with self.assertRaisesRegex(run_experiment.AnnotationError, "invalid label"):
            run_experiment.load_annotations(path)

    def test_duplicate_id_is_rejected(self):
        path = self.write_modified_csv(duplicate=True)
        with self.assertRaisesRegex(run_experiment.AnnotationError, "duplicate unit_id"):
            run_experiment.load_annotations(path)

    def test_missing_cue_is_rejected_by_source_validation(self):
        annotation = self.annotations[0]
        broken = run_experiment.Annotation(
            **{**annotation.__dict__, "cue": "words absent from the cited source span"}
        )
        with self.assertRaisesRegex(run_experiment.AnnotationError, "cue not found"):
            run_experiment.validate_sources([broken], self.repository_root)

    def test_out_of_range_source_line_is_rejected(self):
        annotation = self.annotations[0]
        broken = run_experiment.Annotation(
            **{**annotation.__dict__, "end_line": 10**9}
        )
        with self.assertRaisesRegex(run_experiment.AnnotationError, "exceeds source length"):
            run_experiment.validate_sources([broken], self.repository_root)

    def write_modified_csv(self, label=None, duplicate=False):
        temporary = tempfile.NamedTemporaryFile(
            mode="w", newline="", encoding="utf-8", suffix=".csv", delete=False
        )
        self.addCleanup(Path(temporary.name).unlink, missing_ok=True)
        with temporary:
            with self.annotations_path.open(newline="", encoding="utf-8") as source:
                reader = csv.DictReader(source)
                rows = list(reader)
                fieldnames = reader.fieldnames
            if label is not None:
                rows[0]["label"] = label
            if duplicate:
                rows[1]["unit_id"] = rows[0]["unit_id"]
            writer = csv.DictWriter(temporary, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)
        return Path(temporary.name)


if __name__ == "__main__":
    unittest.main()
