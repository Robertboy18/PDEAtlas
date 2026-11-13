#!/usr/bin/env python3
"""Tests of `build-dependency-atlas.py`: `python3 Blueprint/Tools/build-dependency-atlas.test.py`.

Each test writes a small manifest into a temporary directory and runs the
renderer there. The tests need Graphviz `dot`, as the renderer does.
"""

from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

TOOLS = os.path.dirname(os.path.abspath(__file__))
RENDERER = os.path.join(TOOLS, "build-dependency-atlas.py")

FULL = """digraph G {
  subgraph "cluster_g1" {
    label="Group one";
    "a" [label="A", URL="A/#a"];
    "b" [label="B"];
  }
  "c" [label="C"];
  "a" -> "b";
  "b" -> "c" [style=dashed];
}
"""
GROUP = 'digraph G {\n  "g1" [label="Group one"];\n  "c" [label="C"];\n  "g1" -> "c";\n}\n'
PARENT = 'digraph G {\n  "a" [label="A"];\n  "b" [label="B"];\n  "a" -> "b";\n}\n'


def manifest(**changes) -> dict:
    graph = {
        "nodes": [{"label": "«a»"}, {"label": "«b»"}, {"label": "«c»"}],
        "edges": [{"source": "a", "target": "b"}, {"source": "b", "target": "c"}],
        "groups": [{"label": "g1", "children": ["a", "b"]}, {"label": "g2", "children": ["c"]}],
        "variants": [
            {"key": "full", "label": "Full graph", "dot": FULL},
            {"key": "group", "label": "Groups", "dot": GROUP},
            {"key": "parent:«g1»", "label": "Group one", "dot": PARENT},
        ],
    }
    graph.update(changes)
    return {"graphs": [graph]}


def render(directory: str, data: dict) -> subprocess.CompletedProcess:
    path = os.path.join(directory, "blueprint-manifest.json")
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(data, handle, ensure_ascii=False)
    return subprocess.run(
        [sys.executable, "-I", RENDERER, path, os.path.join(directory, "data", "atlas.svg")],
        capture_output=True, text=True, check=False)


def load_renderer():
    spec = importlib.util.spec_from_file_location("atlas", RENDERER)
    atlas = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(atlas)
    return atlas


class AtlasTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="leanpde-atlas-test-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = self.temporary.name

    def read(self, *parts: str) -> str:
        with open(os.path.join(self.directory, "data", *parts), encoding="utf-8") as handle:
            return handle.read()

    def test_views_and_index(self) -> None:
        result = render(self.directory, manifest())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            result.stdout,
            "Dependency atlas: pre-rendered 3 nodes and 2 edges in 1 clusters; 3 views "
            "(1 group views) indexed in atlas.json.\n")
        index = json.loads(self.read("atlas.json"))["variants"]
        self.assertEqual([list(entry) for entry in index],
                         [["key", "label", "file", "nodes", "edges", "clusters", "bytes"]] * 3)
        self.assertEqual([(entry["key"], entry["file"], entry["nodes"], entry["edges"],
                           entry["clusters"]) for entry in index],
                         [("full", "atlas.svg", 3, 2, 1),
                          ("group", "atlas/group.svg", 2, 1, 0),
                          ("parent:«g1»", "atlas/parent_g1_.svg", 2, 1, 0)])
        for entry in index:
            svg = self.read(*entry["file"].split("/"))
            self.assertEqual(len(svg.encode("utf-8")), entry["bytes"])
            self.assertTrue(svg.startswith(
                f'<svg data-node-count="{entry["nodes"]}" data-edge-count="{entry["edges"]}" '
                f'data-cluster-count="{entry["clusters"]}" data-variant-key="{entry["key"]}" '))

    def test_stale_views_are_removed(self) -> None:
        self.assertEqual(render(self.directory, manifest()).returncode, 0)
        data = manifest()
        del data["graphs"][0]["variants"][2]
        self.assertEqual(render(self.directory, data).returncode, 0)
        self.assertEqual(os.listdir(os.path.join(self.directory, "data", "atlas")), ["group.svg"])

    def test_previous_views_path_is_replaced(self) -> None:
        # A file, or a link to nowhere, at the place of the views directory is removed.
        os.makedirs(os.path.join(self.directory, "data"))
        views = os.path.join(self.directory, "data", "atlas")
        for make in (lambda: open(views, "w").close(), lambda: os.symlink("nowhere", views)):
            make()
            self.assertEqual(render(self.directory, manifest()).returncode, 0)
            self.assertEqual(sorted(os.listdir(views)), ["group.svg", "parent_g1_.svg"])
            shutil.rmtree(views)

    def test_refused_manifests(self) -> None:
        full = {"key": "full", "label": "Full graph", "dot": FULL}
        cases = {
            "no leading full DOT variant": manifest(variants=[
                {"key": "group", "label": "Groups", "dot": GROUP}, full]),
            "Duplicate dependency graph variant key: full": manifest(variants=[full, full]),
            "variant group has no DOT source": manifest(variants=[full, {"key": "group"}]),
            "unrendered structured-source metadata": manifest(variants=[
                {"key": "full", "label": "Full graph",
                 "dot": FULL.replace('label="C"', 'label="%%% Source"')}]),
            "contains no statement nodes": manifest(nodes=[]),
            "is incomplete: 3/4 nodes": manifest(
                nodes=[{"label": name} for name in ("«a»", "«b»", "«c»", "«d»")]),
            "has 1 clusters but the manifest lists 0 groups": manifest(groups=[]),
        }
        for message, data in cases.items():
            with self.subTest(message=message):
                result = render(self.directory, data)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(message, result.stderr)

    def test_graphviz_output_limit(self) -> None:
        atlas = load_renderer()
        self.assertIn("<svg ", atlas.render_dot(PARENT, "parent"))
        atlas.MAX_OUTPUT = 512
        with self.assertRaisesRegex(atlas.AtlasError, "Could not run Graphviz dot: its output"):
            atlas.render_dot(PARENT, "parent")

    def test_javascript_pattern_semantics(self) -> None:
        atlas = load_renderer()
        # `^` under JavaScript's `m` flag also matches after a carriage return or U+2028,
        # and `\s` includes U+FEFF but not U+001C.
        self.assertEqual(atlas.count(atlas.DOT_NODE, '"a" [x];\r"b" [x];\u2028\ufeff"c" [x];'), 3)
        self.assertEqual(atlas.count(atlas.DOT_NODE, '"a" [x]; "b" [x];\n\x1c"c" [x];'), 1)
        self.assertEqual(atlas.count(atlas.DOT_EDGE, '"a" -> "b";\n  "b"->"c" [x];\n"a" [x];'), 2)
        self.assertEqual(atlas.count(atlas.DOT_CLUSTER, 'subgraph "cluster_a" {\n subgraph "x" {'), 1)
        # The `i` flag and `\b` are ASCII-only: U+017F does not fold to `s`.
        self.assertTrue(atlas.LEAKED_METADATA[1].search("x SOURCE := {"))
        self.assertFalse(atlas.LEAKED_METADATA[1].search("ſource := {"))
        self.assertFalse(atlas.LEAKED_METADATA[1].search("resource := {"))
        self.assertEqual(atlas.file_name_for_variant("parent:«a.b_c»"), "parent_a.b_c_.svg")


if __name__ == "__main__":
    unittest.main()
