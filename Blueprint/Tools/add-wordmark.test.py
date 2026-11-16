#!/usr/bin/env python3
"""Tests of `add-wordmark.py`: `python3 Blueprint/Tools/add-wordmark.test.py`.

Each test writes a small site with the titles of Verso's page template (a
landing page, a chapter one directory down, and the `find/` page with a title
of its own) and two brand files with known sizes, and runs the script on it.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest

TOOLS = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(TOOLS, "add-wordmark.py")
BRAND = "-verso-data/leanpde-brand"


def page(base: str, title: str) -> str:
    """A page with the two titles as Verso's template writes them."""
    return f"""<!DOCTYPE html>
<html>
  <head>
    <base href="{base}"><meta charset="utf-8">
    <title>{title}</title>
  </head>
  <body>
    <header>
      <div class="header-logo-wrapper"></div>
      <div class="header-title-wrapper">
        <a href="" class="header-title"><h1>
            {title}</h1>
          </a></div>
      </header>
    <nav id="toc">
        <a href="" class="toc-title"><h1>
              {title}</h1>
            </a></nav>
    <main><h1>A heading of the text, with the 🔗 of its permalink</h1></main>
  </body>
</html>
"""


def webp(width: int, height: int) -> bytes:
    """The first 30 bytes of an extended-format WebP file with this canvas."""
    return (b"RIFF" + (22).to_bytes(4, "little") + b"WEBP" + b"VP8X" + (10).to_bytes(4, "little")
            + bytes(4) + (width - 1).to_bytes(3, "little") + (height - 1).to_bytes(3, "little"))


class WordmarkTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="leanpde-wordmark-test-")
        self.addCleanup(temporary.cleanup)
        self.site = os.path.join(os.path.realpath(temporary.name), "html-multi")
        for directory in (BRAND, "Chapter", "find"):
            os.makedirs(os.path.join(self.site, directory))
        self.write("index.html", page("./", "PDEAtlas"))
        self.write("Chapter/index.html", page("./../", "PDEAtlas"))
        self.write("find/index.html", page("./../", "Cross-Reference Redirection"))
        self.write(f"{BRAND}/logo-light.webp", webp(1623, 318))
        self.write(f"{BRAND}/logo-dark.webp", webp(800, 157))

    def write(self, name: str, content: str | bytes) -> None:
        data = content.encode("utf-8") if isinstance(content, str) else content
        with open(os.path.join(self.site, name), "wb") as handle:
            handle.write(data)

    def read(self, name: str) -> str:
        with open(os.path.join(self.site, name), encoding="utf-8", newline="") as handle:
            return handle.read()

    def run_script(self) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, "-I", SCRIPT, self.site],
                              capture_output=True, text=True, check=False)

    def test_wordmark_in_both_titles(self) -> None:
        find_page = self.read("find/index.html")
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("of 2 pages; 0 had it already.", result.stdout)
        self.assertIn("Left with their own title: find/index.html.", result.stdout)
        mark = (
            '<span class="leanpde-brand-name">PDEAtlas</span>'
            '<span class="leanpde-wordmark" aria-hidden="true">'
            f'<img class="leanpde-logo-light" src="{BRAND}/logo-light.webp" '
            'width="1623" height="318" alt="" decoding="async">'
            f'<img class="leanpde-logo-dark" src="{BRAND}/logo-dark.webp" '
            'width="800" height="157" alt="" decoding="async"></span>')
        for name, base in (("index.html", "./"), ("Chapter/index.html", "./../")):
            # Only the two title headings change; the rest of the page is kept byte for byte.
            expected = page(base, "PDEAtlas")
            for title in ("header-title", "toc-title"):
                before = expected.count(f'class="{title}"><h1>')
                self.assertEqual(before, 1)
            expected = expected.replace(
                '<h1>\n            PDEAtlas</h1>', f"<h1>{mark}</h1>").replace(
                '<h1>\n              PDEAtlas</h1>', f"<h1>{mark}</h1>")
            self.assertEqual(self.read(name), expected)
            self.assertEqual(self.read(name).count("leanpde-wordmark"), 2)
        self.assertEqual(self.read("find/index.html"), find_page)

        # A second run changes nothing.
        pages = {name: self.read(name) for name in ("index.html", "Chapter/index.html")}
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("of 0 pages; 2 had it already.", result.stdout)
        for name, text in pages.items():
            self.assertEqual(self.read(name), text)
        self.assertEqual(self.read("find/index.html"), find_page)

    def test_refusals(self) -> None:
        landing = self.read("index.html")
        chapter = self.read("Chapter/index.html")

        def refused(message: str) -> None:
            result = self.run_script()
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn(message, result.stderr)
            # A refused site is left as it was, the pages before the refused one included.
            self.assertEqual(self.read("index.html"), landing)

        # A page without the template's top-bar title.
        self.write("Chapter/index.html", chapter.replace('class="header-title"', 'class="title"'))
        refused("Chapter/index.html: expected one sidebar title (toc-title) and one top-bar title")
        # A page whose base does not lead to the site root: the image paths would not resolve.
        self.write("Chapter/index.html", chapter.replace('<base href="./../">', '<base href="./">'))
        refused('Chapter/index.html: its <base href="./"> does not lead to the site root')
        self.write("Chapter/index.html", chapter)

        # The brand files must be in the site, and be WebP images.
        dark = os.path.join(self.site, BRAND, "logo-dark.webp")
        os.remove(dark)
        refused("logo-dark.webp is missing; copy the brand files into the site first.")
        self.write(f"{BRAND}/logo-dark.webp", b"not an image")
        refused("logo-dark.webp is not a WebP image this script can measure.")
        self.write(f"{BRAND}/logo-dark.webp", webp(800, 157))

        os.remove(os.path.join(self.site, "index.html"))
        result = self.run_script()
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("has no index.html; it is not a rendered Blueprint site.", result.stderr)
        self.assertEqual(self.read("Chapter/index.html"), chapter)

    def test_marked_page_with_wrong_base(self) -> None:
        # A page that already has the wordmark is checked like one that gets it: a later run
        # must not report success when its base no longer leads to the brand files.
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stderr)
        landing = self.read("index.html")
        chapter = self.read("Chapter/index.html")
        moved = chapter.replace('<base href="./../">', '<base href="./">')
        self.assertNotEqual(moved, chapter)
        self.write("Chapter/index.html", moved)
        result = self.run_script()
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn('Chapter/index.html: its <base href="./"> does not lead to the site root',
                      result.stderr)
        self.assertEqual(self.read("index.html"), landing)
        self.assertEqual(self.read("Chapter/index.html"), moved)

    def test_other_image_headers(self) -> None:
        # The lossy and the lossless WebP headers carry the size in other places.
        lossy = (b"RIFF" + bytes(4) + b"WEBP" + b"VP8 " + bytes(4) + bytes(3) + b"\x9d\x01\x2a"
                 + (640).to_bytes(2, "little") + (126).to_bytes(2, "little"))
        bits = (320 - 1) | ((63 - 1) << 14)
        lossless = (b"RIFF" + bytes(4) + b"WEBP" + b"VP8L" + bytes(4) + b"\x2f"
                    + bits.to_bytes(4, "little") + bytes(5))
        self.write(f"{BRAND}/logo-light.webp", lossy)
        self.write(f"{BRAND}/logo-dark.webp", lossless)
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stderr)
        landing = self.read("index.html")
        self.assertIn('logo-light.webp" width="640" height="126"', landing)
        self.assertIn('logo-dark.webp" width="320" height="63"', landing)


if __name__ == "__main__":
    unittest.main()
