#!/usr/bin/env python3
"""Tests of `build-pages-tree.py`: `python3 Blueprint/Tools/build-pages-tree.test.py`.

Each test copies the script into a temporary checkout with one dependency
package behind a symbolic link, writes a small rendered site whose data files
name sources by absolute path, and runs only the copy.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

TOOLS = os.path.dirname(os.path.abspath(__file__))


class PagesTreeTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="leanpde-pages-test-")
        self.addCleanup(temporary.cleanup)
        self.top = os.path.realpath(temporary.name)
        self.repo = os.path.join(self.top, "checkout", "LeanPDE")
        self.home = os.path.join(self.top, "home", "reader")
        self.dependency = os.path.join(self.top, "shared", "dep")
        self.site = os.path.join(self.repo, "_out", "site", "html-multi")
        self.output = os.path.join(self.repo, "_out", "pages")
        for directory in (os.path.join(self.repo, "Blueprint", "Tools"),
                          os.path.join(self.repo, "Blueprint", ".lake", "packages"),
                          self.home, self.dependency,
                          os.path.join(self.site, "-verso-data"), os.path.join(self.site, "find")):
            os.makedirs(directory)
        os.symlink(self.dependency, os.path.join(self.repo, "Blueprint", ".lake", "packages", "dep"))
        self.script = os.path.join(self.repo, "Blueprint", "Tools", "build-pages-tree.py")
        shutil.copyfile(os.path.join(TOOLS, "build-pages-tree.py"), self.script)

        chapter = f"{self.repo}/Blueprint/../Blueprint/Chapters/A.lean"
        self.manifest = {
            "graphs": [{"nodes": []}],
            "previews": [
                {"key": "a", "codeData": {"externalDecls": [{"sourcePath?": f"{self.repo}/PDE/B.lean"}]},
                 "sourceLocation": {"ok": True, "location": {"path": chapter}}},
                {"key": "b", "codeData": None,
                 "sourceLocation": {"ok": True, "location": {"path": f"{self.dependency}/Dep/C.lean"}},
                 "href": "https://github.com/Robertboy18/PDEAtlas/blob/main/PDE/B.lean#L1"},
            ],
        }
        self.write("-verso-data/blueprint-manifest.json", json.dumps(self.manifest, ensure_ascii=False))
        self.write("xref.json", json.dumps({"a": {"path": chapter}}))
        self.write("find/index.html", f'<script>var x = {{"path":"{self.repo}/PDE/B.lean"}};</script>')
        self.write("index.html", "<html><body>«LeanPDE»</body></html>")

    def write(self, name: str, text: str) -> None:
        with open(os.path.join(self.site, name), "w", encoding="utf-8", newline="") as handle:
            handle.write(text)

    def read(self, name: str) -> str:
        with open(os.path.join(self.output, name), encoding="utf-8") as handle:
            return handle.read()

    def run_script(self) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, "-I", self.script, self.site, self.output],
                              capture_output=True, text=True, check=False,
                              env={**os.environ, "HOME": self.home})

    def test_published_tree(self) -> None:
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(sorted(os.listdir(self.output)),
                         ["-verso-data", ".nojekyll", "find", "index.html", "xref.json"])
        self.assertEqual(os.path.getsize(os.path.join(self.output, ".nojekyll")), 0)
        manifest = json.loads(self.read("-verso-data/blueprint-manifest.json"))
        expected = json.loads(json.dumps(self.manifest))
        expected["previews"][0]["codeData"] = None
        expected["previews"][0]["sourceLocation"]["location"]["path"] = "Blueprint/Chapters/A.lean"
        expected["previews"][1]["sourceLocation"]["location"]["path"] = ".lake/packages/dep/Dep/C.lean"
        self.assertEqual(manifest, expected)
        self.assertEqual(json.loads(self.read("xref.json")), {"a": {"path": "Blueprint/Chapters/A.lean"}})
        self.assertEqual(self.read("find/index.html"), '<script>var x = {"path":"PDE/B.lean"};</script>')
        self.assertEqual(self.read("index.html"), "<html><body>«LeanPDE»</body></html>")
        self.assertIn("codeData set to null in 1 entries", result.stdout)
        self.assertIn("2 in -verso-data/blueprint-manifest.json, 1 in find/index.html, 1 in xref.json",
                      result.stdout)

    def test_refusals(self) -> None:
        def refused(message: str) -> None:
            result = self.run_script()
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn(message, result.stderr)
            shutil.rmtree(self.output, ignore_errors=True)

        os.makedirs(self.output)
        with open(os.path.join(self.output, "kept.txt"), "w") as handle:
            handle.write("not ours to overwrite")
        refused("exists and is not an empty directory")

        # A path the script cannot place, here under the reader's home, stops the publication.
        self.write("index.html", f'<a href="file://{self.home}/notes.html">notes</a>')
        refused(f"index.html still names {self.home}")
        self.write("index.html", f"built in {self.repo} today")
        refused(f"index.html still names {self.repo}")
        self.write("index.html", "<html></html>")

        # Only the source fields of the three data files are rewritten. The same checkout path
        # in prose, in a link, in a key, or in a source field of another file is not touched,
        # so it stops the publication.
        xref = json.dumps({"a": {"path": f"{self.repo}/PDE/B.lean"}})
        cases = {
            "xref.json": [json.dumps({"description": f"{self.repo}/ordinary prose"}),
                          json.dumps({f"{self.repo}/key": "value"})],
            "index.html": [f'<a href="{self.repo}/image.svg">image</a>'],
            "other.json": [xref],
        }
        for name, texts in cases.items():
            for text in texts:
                self.write(name, text)
                refused(f"{name} still names {self.repo}")
            self.write(name, "{}")
        self.write("xref.json", xref)
        self.write("index.html", "<html></html>")
        os.remove(os.path.join(self.site, "other.json"))
        self.assertEqual(self.run_script().returncode, 0)
        shutil.rmtree(self.output)

        with open(os.path.join(self.site, "large.bin"), "wb") as handle:
            handle.truncate(100 * 1024 * 1024 + 1)
        refused("large.bin is 104.9 MB; GitHub refuses files over 100 MB")
        os.remove(os.path.join(self.site, "large.bin"))

        os.remove(os.path.join(self.site, "-verso-data", "blueprint-manifest.json"))
        refused("is not a rendered Blueprint site")


if __name__ == "__main__":
    unittest.main()
