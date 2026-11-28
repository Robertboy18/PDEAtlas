#!/usr/bin/env python3
"""Regression checks for certified plot cache provenance and visible bounds."""

import contextlib
import importlib.util
import io
import json
import sys
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "certified_plots", Path(__file__).with_name("build-certified-plots.py")
)
plots = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = plots
SPEC.loader.exec_module(plots)


class ProbeCacheTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.cache = Path(self.directory.name) / "intervals.json"
        self.fingerprint = {
            "schemaVersion": 1,
            "probeSha256": "query",
            "sourcesSha256": "current-backend",
        }
        self.intervals = {"panel": ["-1", "1/2"]}

    def read_cache(self, payload):
        self.cache.write_text(json.dumps(payload), encoding="utf8")
        return plots.read_probe_cache(self.cache, self.fingerprint, ["panel"])

    def test_unversioned_cache_is_rejected(self):
        self.assertIsNone(self.read_cache(self.intervals))

    def test_matching_cache_preserves_exact_endpoints(self):
        self.assertEqual(
            self.read_cache({"fingerprint": self.fingerprint, "intervals": self.intervals}),
            {"panel": (Fraction(-1), Fraction(1, 2))},
        )

    def test_changed_query_or_backend_invalidates_cache(self):
        for field in ("probeSha256", "sourcesSha256", "schemaVersion"):
            with self.subTest(field=field):
                stale = dict(self.fingerprint, **{field: "old"})
                self.assertIsNone(
                    self.read_cache({"fingerprint": stale, "intervals": self.intervals})
                )

    def test_missing_or_malformed_intervals_are_rejected(self):
        for intervals in ({}, {"panel": ["1", "-1"]}, {"panel": ["-1", "1/0"]}):
            with self.subTest(intervals=intervals):
                self.assertIsNone(
                    self.read_cache({"fingerprint": self.fingerprint, "intervals": intervals})
                )


class ProbeFingerprintTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.floatlib_root = self.root / ".lake/packages/floatlib/FloatLib"
        self.nested_floatlib_root = self.root / "Blueprint/.lake/packages/floatlib/FloatLib"
        self.files = [
            "generator.py", "lean-toolchain", "lakefile.lean", "lake-manifest.json",
            "Blueprint/lakefile.lean", "Blueprint/lake-manifest.json",
            "PDE/Symbolic/Provider.lean",
        ]
        for name in self.files:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("original", encoding="utf8")
        source_paths = patch.multiple(
            plots, REPO_ROOT=self.root, BLUEPRINT_DIR=self.root / "Blueprint",
            __file__=str(self.root / "generator.py"),
        )
        source_paths.start()
        self.addCleanup(source_paths.stop)

    def add_floatlib_source(self, root):
        root.mkdir(parents=True, exist_ok=True)
        source = root / "Provider.lean"
        source.write_text("original", encoding="utf8")
        self.files.append(str(source.relative_to(self.root)))
        return source

    def test_fingerprint_tracks_queries_pins_and_provider_sources(self):
        self.add_floatlib_source(self.floatlib_root)
        self.add_floatlib_source(self.nested_floatlib_root)
        initial = plots.probe_fingerprint("query")
        self.assertNotEqual(initial, plots.probe_fingerprint("different query"))
        for name in self.files:
            with self.subTest(path=name):
                path = self.root / name
                path.write_text("changed", encoding="utf8")
                self.assertNotEqual(initial, plots.probe_fingerprint("query"))
                path.write_text("original", encoding="utf8")
        self.assertEqual(initial, plots.probe_fingerprint("query"))

    def check_single_floatlib_root(self, root):
        source = self.add_floatlib_source(root)
        initial = plots.probe_fingerprint("query")
        source.write_text("changed", encoding="utf8")
        self.assertNotEqual(initial, plots.probe_fingerprint("query"))

    def test_root_only_floatlib_is_supported(self):
        self.check_single_floatlib_root(self.floatlib_root)

    def test_nested_only_floatlib_is_supported(self):
        self.check_single_floatlib_root(self.nested_floatlib_root)

    def test_neither_floatlib_root_is_rejected(self):
        with self.assertRaisesRegex(SystemExit, "at least one FloatLib source checkout"):
            plots.probe_fingerprint("query")

    def test_symbolic_sources_are_required(self):
        self.add_floatlib_source(self.floatlib_root)
        (self.root / "PDE/Symbolic/Provider.lean").unlink()
        (self.root / "PDE/Symbolic").rmdir()
        with self.assertRaisesRegex(SystemExit, "provider sources"):
            plots.probe_fingerprint("query")

    def test_included_root_paths_change_fingerprint(self):
        self.add_floatlib_source(self.floatlib_root)
        initial = plots.probe_fingerprint("query")
        self.nested_floatlib_root.mkdir(parents=True)
        self.assertNotEqual(initial, plots.probe_fingerprint("query"))
        self.nested_floatlib_root.rmdir()
        self.assertEqual(initial, plots.probe_fingerprint("query"))
        self.floatlib_root.rename(self.nested_floatlib_root)
        self.assertNotEqual(initial, plots.probe_fingerprint("query"))


class DrawingModelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = plots.OUTPUT_PATH.read_text(encoding="utf8")
        cls.data = plots.DATA_PATH.read_text(encoding="utf8")
        match = plots.re.search(r'r(#+)"\n([\s\S]*?)\n"\1', cls.data)
        cls.model = json.loads(match.group(2))

    def check_model(self, model):
        data = plots.DATA_TEMPLATE.format(json=json.dumps(model, indent=1, ensure_ascii=False))
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return plots.check(self.source, data)

    def test_committed_bounds_reproduce_both_outputs(self):
        self.assertEqual(self.check_model(self.model), 0)

    def test_visible_decimal_statement_and_geometry_must_match(self):
        for key, replacement in (
            ("loDecimal", "-999"), ("statement", "stale statement"), ("height", "999"),
        ):
            with self.subTest(field=key):
                model = json.loads(json.dumps(self.model))
                model["families"][0]["curves"][0]["bars"][0][key] = replacement
                self.assertEqual(self.check_model(model), 1)


class ProbeLayoutTests(unittest.TestCase):
    def test_all_queries_fit_the_strict_source_line_limit(self):
        source, order = plots.probe_source()
        self.assertEqual(len(order), 360)
        self.assertEqual(source.count("#cas [enclose"), 360)
        self.assertTrue(all(len(line) <= 100 for line in source.splitlines()))

    def test_overlong_query_is_rejected_before_invoking_lean(self):
        curve = plots.FAMILIES[0].curves[0]
        with patch.object(curve, "tactic_expr", "x" * 101):
            with self.assertRaisesRegex(ValueError, "exceeds 100 columns"):
                plots.probe_source()


if __name__ == "__main__":
    unittest.main()
