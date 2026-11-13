#!/usr/bin/env python3
"""Make the tree that a static host publishes from a rendered Blueprint site.

`build.sh` and `build-no-node.sh` render a site that a local reader can open.
Two things keep that site off a `gh-pages` branch:

* `-verso-data/blueprint-manifest.json` holds, for every statement and proof,
  the `codeData` record of its Lean code. The field makes the file several
  hundred megabytes, and GitHub refuses a file over 100 MB. No module of the
  page runtime reads `codeData`: the rendered code is in the pages and in
  `blueprint-html-cache.json`. The published manifest has `codeData: null`
  in every entry, the value the renderer writes for an entry without code.
* VersoBlueprint records absolute source paths of the machine that rendered
  the site, in the `path` and `sourcePath?` fields of the manifest, of
  `xref.json` and of the data in `find/index.html`. The published files name
  a source by its path in the repository and a dependency's source by
  `.lake/packages/<name>/...`. Nothing but the values of those fields in
  those three files is rewritten.

The script copies the site to a new directory, makes these two changes, adds
an empty `.nojekyll`, and checks the result: no file over 100 MB, and no path
of this checkout, of a dependency or of the home directory anywhere in any
file. A machine path in any other place stops the script. It lists the files
over 50 MB, which GitHub accepts with a warning.

Usage: python3 Blueprint/Tools/build-pages-tree.py <html-multi-dir> <output-dir>
"""

from __future__ import annotations

import json
import os
import re
import shutil
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST = os.path.join("-verso-data", "blueprint-manifest.json")
# Where VersoBlueprint records source paths: these fields of these files.
SOURCE_FILES = (MANIFEST, "xref.json", os.path.join("find", "index.html"))
SOURCE_FIELDS = ("path", "sourcePath?")
REFUSED_BYTES = 100 * 1024 * 1024
WARNED_BYTES = 50 * 1024 * 1024


class PagesError(Exception):
    """A site that must not be published as it is."""


def path_rewrites(repo_root: Path) -> list[tuple[bytes, bytes]]:
    """The absolute prefixes the renderer may have recorded, longest first, with what replaces them.

    Lean resolves symbolic links, so every directory is taken both as it is spelled and resolved.
    The nested Blueprint package names its own sources through `Blueprint/..`.
    """
    rewrites: dict[str, str] = {}
    for packages in (repo_root / "Blueprint" / ".lake" / "packages", repo_root / ".lake" / "packages"):
        if packages.is_dir():
            for package in sorted(packages.iterdir()):
                for spelling in (str(package), os.path.realpath(package)):
                    rewrites[spelling + "/"] = f".lake/packages/{package.name}/"
    for root in (str(repo_root), os.path.realpath(repo_root)):
        if len(Path(root).parts) < 3:
            raise PagesError(
                f"The checkout {root} is too close to the file system root to tell its paths "
                "from URLs; render the site from a deeper directory.")
        rewrites[root + "/Blueprint/../"] = ""
        rewrites[root + "/"] = ""
    return sorted(((old.encode("utf-8"), new.encode("utf-8")) for old, new in rewrites.items()),
                  key=lambda rewrite: -len(rewrite[0]))


def forbidden_paths(rewrites: list[tuple[bytes, bytes]]) -> list[bytes]:
    """What may not occur in a published file: this checkout, a dependency's directory, the home."""
    forbidden = {old.rstrip(b"/") for old, _ in rewrites if not old.endswith(b"/Blueprint/../")}
    home = os.path.expanduser("~")
    if len(Path(home).parts) >= 3:
        forbidden.add(home.encode("utf-8"))
    return sorted(forbidden, key=len)


def rewrite_paths(data: bytes, rewrites: list[tuple[bytes, bytes]]) -> tuple[bytes, int]:
    """Make the recorded source paths relative: the value of a `path` or `sourcePath?` field that
    starts with one of the prefixes. No other text is changed, whatever it contains."""
    fields = b"|".join(re.escape(field.encode("utf-8")) for field in SOURCE_FIELDS)
    count = 0
    for old, new in rewrites:
        if old not in data:
            continue
        opening = re.compile(b'("(?:' + fields + b')"[ \\t\\r\\n]*:[ \\t\\r\\n]*")' + re.escape(old))
        data, found = opening.subn(lambda match: match.group(1) + new, data)
        count += found
    return data, count


def publishable_manifest(data: bytes) -> tuple[bytes, int]:
    """The manifest with `codeData: null` in every entry of `previews`."""
    manifest = json.loads(data)
    previews = manifest.get("previews") if isinstance(manifest, dict) else None
    if not isinstance(previews, list):
        raise PagesError("The Blueprint manifest has no previews array.")
    dropped = 0
    for entry in previews:
        if isinstance(entry, dict) and entry.get("codeData") is not None:
            entry["codeData"] = None
            dropped += 1
    return json.dumps(manifest, ensure_ascii=False, separators=(",", ":")).encode("utf-8"), dropped


def build(site: Path, output: Path, repo_root: Path = REPO_ROOT) -> str:
    """Write the publishable tree; return the summary."""
    if not (site / "index.html").is_file() or not (site / MANIFEST).is_file():
        raise PagesError(f"{site} is not a rendered Blueprint site (no index.html or manifest).")
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        raise PagesError(f"{output} exists and is not an empty directory.")
    if output.resolve() == site.resolve() or site.resolve() in output.resolve().parents:
        raise PagesError("The output directory must be outside the rendered site.")

    rewrites = path_rewrites(repo_root)
    forbidden = forbidden_paths(rewrites)
    files = sorted(path for path in site.rglob("*") if path.is_file())
    rewritten: dict[str, int] = {}
    manifest_sizes = (0, 0)
    dropped = 0
    total = 0
    large: list[tuple[int, str]] = []
    for source in files:
        relative = source.relative_to(site)
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        data = source.read_bytes()
        published = data
        if str(relative) == MANIFEST:
            published, dropped = publishable_manifest(data)
        if str(relative) in SOURCE_FILES:
            published, count = rewrite_paths(published, rewrites)
            if count:
                rewritten[str(relative)] = count
        if str(relative) == MANIFEST:
            manifest_sizes = (len(data), len(published))
        for path in forbidden:
            if path in published:
                raise PagesError(
                    f"{relative} still names {path.decode('utf-8', errors='replace')}, "
                    "outside the source fields this script rewrites.")
        if len(published) > REFUSED_BYTES:
            raise PagesError(
                f"{relative} is {len(published) / 1e6:.1f} MB; GitHub refuses files over 100 MB.")
        if len(published) > WARNED_BYTES:
            large.append((len(published), str(relative)))
        if published is data:
            shutil.copyfile(source, target)
        else:
            target.write_bytes(published)
        total += len(published)
    (output / ".nojekyll").write_bytes(b"")

    lines = [
        f"Pages tree: {len(files)} files and .nojekyll, {total / 1e6:.1f} MB, in {output}.",
        f"Manifest: {manifest_sizes[0] / 1e6:.1f} MB rendered, {manifest_sizes[1] / 1e6:.1f} MB "
        f"published; codeData set to null in {dropped} entries.",
        "Source paths made relative: "
        + (", ".join(f"{count} in {name}" for name, count in sorted(rewritten.items())) or "none") + ".",
    ]
    for size, name in sorted(large, reverse=True):
        lines.append(f"Over 50 MB (GitHub warns): {name}, {size / 1e6:.1f} MB.")
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("Usage: python3 Blueprint/Tools/build-pages-tree.py <html-multi-dir> <output-dir>",
              file=sys.stderr)
        return 2
    try:
        print(build(Path(argv[0]), Path(argv[1])))
    except PagesError as error:
        print(f"build-pages-tree: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
