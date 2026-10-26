#!/usr/bin/env python3
"""Regression cases for missing/duplicate disclosures and output substitution."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("manifests", Path(__file__).with_name("axiom-manifests.py"))
manifest = importlib.util.module_from_spec(spec)
spec.loader.exec_module(manifest)


class ManifestTests(unittest.TestCase):
    def fixture(self, root, entries="ShorECDLP.Sample.a\nShorECDLP.Sample.b\n"):
        (root / "ShorECDLP").mkdir()
        (root / "ShorECDLP/Sample.lean").write_text("")
        (root / "scripts/axioms").mkdir(parents=True)
        path = root / "scripts/axioms/ShorECDLP.Sample.txt"
        path.write_text(entries)
        return path

    def test_exact_set_and_both_output_forms(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            names = manifest.declarations(root)
            output = "'ShorECDLP.Sample.b' depends on axioms: [propext]\n" \
                     "'ShorECDLP.Sample.a' does not depend on any axioms\n"
            self.assertEqual(manifest.check_output(names, output), 2)

    def test_missing_duplicate_and_substituted_output(self):
        names = ["ShorECDLP.Sample.a", "ShorECDLP.Sample.b"]
        for actual in ([names[0]], [names[0], names[0]], [names[0], "ShorECDLP.Sample.c"]):
            with self.subTest(actual=actual), self.assertRaises(ValueError):
                manifest.check_output(names, "\n".join(f"'{n}' depends on axioms: []" for n in actual))

    def test_bad_manifests(self):
        for content in ("", "not-a-name\n", "ShorECDLP.Sample.a\nShorECDLP.Sample.a\n"):
            with self.subTest(content=content), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                self.fixture(root, content)
                with self.assertRaises(ValueError):
                    manifest.declarations(root)

    def test_missing_source_or_manifests(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with self.assertRaises(ValueError):
                manifest.declarations(root)
            self.fixture(root)
            (root / "ShorECDLP/Sample.lean").unlink()
            with self.assertRaises(ValueError):
                manifest.declarations(root)


if __name__ == "__main__":
    unittest.main()
