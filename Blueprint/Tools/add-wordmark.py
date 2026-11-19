#!/usr/bin/env python3
"""Put the wordmark into the titles of the pages of a rendered Blueprint site.

Verso's page template names the book twice on every page: in the title at the
top of the sidebar, which a wide window shows, and in the title of the top bar,
which replaces it in a narrow one. The landing page names it a third time, in
the heading of its title page. Both build modes use this script to add the
wordmark to those titles.

In each title the `<h1>` keeps the name as text, in a `leanpde-brand-name` span
that the site stylesheet hides from the eye and not from a screen reader, and
gains a `leanpde-wordmark` span with the light and the dark image,
`leanpde-logo-light` and `leanpde-logo-dark`. The images are decorative: the
span is hidden from assistive technology and they have an empty `alt`. The
stylesheet in `Blueprint.lean` shows the image of the current theme and sizes
it by the font size of its place, which is large on the title page.

The images are the brand files that the build copies to
`-verso-data/leanpde-brand/`. Their paths are relative to the site root, which
every page names in its `<base href>`; the script checks that. Their `width`
and `height` attributes are read from the files.

A page whose titles hold another text than the name on the landing page keeps
them: Verso's `find/` page is a redirect with a title of its own. A title with
the wordmark is left as it is, so a second run changes nothing. If any page
lacks one of the two titles, the landing page lacks the heading of its title
page or that heading carries another name, or the `<base href>` of a page that
has or gets the wordmark does not lead to the brand files, the script stops
before it writes anything.

Usage: python3 Blueprint/Tools/add-wordmark.py <html-multi-dir>
"""

from __future__ import annotations

import os
import re
import sys

BRAND_DIRECTORY = "-verso-data/leanpde-brand"
THEMES = ("light", "dark")
# The two titles of Verso's page template, with the heading they wrap.
TITLE = re.compile(
    rb'(<a href="[^"]*" class="(toc-title|header-title)">\s*<h1\b[^>]*>)(.*?)(</h1>)', re.S
)
# The heading of the title page, which only the landing page has: the name, then what Verso
# appends to a heading (its permalink).
LANDING = re.compile(rb'(<div class="titlepage">\s*<h1\b[^>]*>)([^<]*)(.*?</h1>)', re.S)
NO_BREAK_SPACE = "\u00a0".encode()
BASE = re.compile(rb'<base href="([^"]*)"')
NAME = re.compile(rb'<span class="leanpde-brand-name">(.*?)</span>', re.S)
WORDMARK_CLASS = b'class="leanpde-wordmark"'


class WordmarkError(Exception):
    """A site that the script cannot give the wordmark as it is."""


def webp_size(path: str) -> tuple[int, int]:
    """Width and height of a WebP image, from the header of its first chunk."""
    with open(path, "rb") as handle:
        head = handle.read(30)
    if len(head) == 30 and head[:4] == b"RIFF" and head[8:12] == b"WEBP":
        kind = head[12:16]
        if kind == b"VP8X":
            return (int.from_bytes(head[24:27], "little") + 1,
                    int.from_bytes(head[27:30], "little") + 1)
        if kind == b"VP8 " and head[23:26] == b"\x9d\x01\x2a":
            return (int.from_bytes(head[26:28], "little") & 0x3FFF,
                    int.from_bytes(head[28:30], "little") & 0x3FFF)
        if kind == b"VP8L" and head[20] == 0x2F:
            bits = int.from_bytes(head[21:25], "little")
            return (bits & 0x3FFF) + 1, ((bits >> 14) & 0x3FFF) + 1
    raise WordmarkError(f"{path} is not a WebP image this script can measure.")


def wordmark(site: str) -> bytes:
    """The wordmark span, with the sizes of the two brand files of the site."""
    images = []
    for theme in THEMES:
        path = os.path.join(site, BRAND_DIRECTORY, f"logo-{theme}.webp")
        if not os.path.isfile(path):
            raise WordmarkError(f"{path} is missing; copy the brand files into the site first.")
        width, height = webp_size(path)
        images.append(
            f'<img class="leanpde-logo-{theme}" src="{BRAND_DIRECTORY}/logo-{theme}.webp" '
            f'width="{width}" height="{height}" alt="" decoding="async">')
    span = '<span class="leanpde-wordmark" aria-hidden="true">' + "".join(images) + "</span>"
    return span.encode()


def pages(site: str) -> list[str]:
    """The pages of the site, as paths relative to it, the landing page first."""
    found = []
    for directory, _, names in os.walk(site):
        for name in names:
            if name.endswith(".html"):
                found.append(os.path.relpath(os.path.join(directory, name), site))
    return sorted(found, key=lambda page: (page != "index.html", page))


def titles(page: str, html: bytes) -> list[re.Match]:
    """The sidebar title and the top-bar title of a page; the template has one of each."""
    found = list(TITLE.finditer(html))
    if sorted(match.group(2) for match in found) != [b"header-title", b"toc-title"]:
        raise WordmarkError(
            f"{page}: expected one sidebar title (toc-title) and one top-bar title (header-title) "
            f"around an <h1>, found {len(found)}; this is not the page template the script knows.")
    return found


def name_of(heading: bytes) -> bytes:
    """The name a title heading carries, with or without the wordmark."""
    kept = NAME.search(heading)
    return (kept.group(1) if kept else heading).replace(NO_BREAK_SPACE, b" ").strip()


def landing_title(html: bytes) -> re.Match:
    """The heading of the title page of the landing page; the template has one."""
    found = list(LANDING.finditer(html))
    if len(found) != 1:
        raise WordmarkError(
            f"index.html: expected one heading in the title page, found {len(found)}; "
            "this is not the landing page the script knows.")
    return found[0]


def landing_name(match: re.Match) -> bytes:
    """The name the heading of the title page carries, with or without the wordmark."""
    plain = match.group(2).replace(NO_BREAK_SPACE, b" ").strip()
    return plain if plain else name_of(match.group(3))


def check_base(site: str, page: str, html: bytes) -> None:
    """The image paths are relative to `<base href>`, so that must lead to the site root."""
    base = BASE.search(html)
    href = base.group(1).decode() if base else "./"
    brand = os.path.normpath(os.path.join(site, BRAND_DIRECTORY))
    resolved = os.path.normpath(os.path.join(site, os.path.dirname(page), href, BRAND_DIRECTORY))
    if "://" in href or href.startswith("/") or resolved != brand:
        raise WordmarkError(
            f'{page}: its <base href="{href}"> does not lead to the site root, '
            "so the wordmark's image paths would not resolve.")


def with_wordmark(html: bytes, mark: bytes) -> bytes:
    """The page with the wordmark in every title that lacks it."""
    def named(name: bytes) -> bytes:
        return b'<span class="leanpde-brand-name">' + name + b"</span>" + mark

    def title(match: re.Match) -> bytes:
        if WORDMARK_CLASS in match.group(3):
            return match.group(0)
        return match.group(1) + named(name_of(match.group(3))) + match.group(4)

    def landing(match: re.Match) -> bytes:
        if WORDMARK_CLASS in match.group(3):
            return match.group(0)
        return match.group(1) + named(name_of(match.group(2))) + match.group(3)

    return LANDING.sub(landing, TITLE.sub(title, html))


def place(site: str) -> tuple[list[str], list[str], list[str], bool]:
    """Give every page the wordmark. Returns the pages whose two titles changed, those that had
    it there already, those left alone, and whether the title page of the landing page changed."""
    listed = pages(site)
    if "index.html" not in listed:
        raise WordmarkError(f"{site} has no index.html; it is not a rendered Blueprint site.")
    mark = wordmark(site)
    site_name = b""
    todo: list[str] = []
    done: list[str] = []
    other: list[str] = []
    landing_todo = False
    # First pass: read every page and decide, so that nothing is written if any page is refused.
    for page in listed:
        with open(os.path.join(site, page), "rb") as handle:
            html = handle.read()
        found = titles(page, html)
        names = {name_of(match.group(3)) for match in found}
        if page == "index.html":
            if len(names) != 1 or not next(iter(names)):
                raise WordmarkError("index.html: its two titles do not carry one name.")
            site_name = next(iter(names))
            heading = landing_title(html)
            if landing_name(heading) != site_name:
                raise WordmarkError(
                    "index.html: the heading of its title page does not carry the name of the "
                    "site.")
            landing_todo = WORDMARK_CLASS not in heading.group(3)
        marked = [WORDMARK_CLASS in match.group(3) for match in found]
        if names != {site_name}:
            if any(marked):
                raise WordmarkError(
                    f"{page}: a title with the wordmark does not carry the name of the site.")
            other.append(page)
        elif any(marked) and not all(marked):
            raise WordmarkError(f"{page}: only one of its two titles has the wordmark.")
        else:
            # A page that has the wordmark already needs the same base as one that gets it.
            check_base(site, page, html)
            (done if all(marked) else todo).append(page)
    for page in todo + (["index.html"] if landing_todo and "index.html" not in todo else []):
        path = os.path.join(site, page)
        with open(path, "rb") as handle:
            html = handle.read()
        with open(path, "wb") as handle:
            handle.write(with_wordmark(html, mark))
    return todo, done, other, landing_todo


def main(arguments: list[str]) -> int:
    if len(arguments) != 1:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    site = os.path.abspath(arguments[0])
    try:
        changed, done, other, landing = place(site)
    except WordmarkError as error:
        print(f"add-wordmark.py: {error}", file=sys.stderr)
        return 1
    print(f"Wordmark placed in the sidebar title and the top bar of {len(changed)} pages; "
          f"{len(done)} had it already.")
    print("Wordmark placed in the title page of the landing page." if landing
          else "The title page of the landing page had it already.")
    if other:
        print(f"Left with their own title: {', '.join(other)}.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
