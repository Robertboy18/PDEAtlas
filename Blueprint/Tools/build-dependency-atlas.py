#!/usr/bin/env python3
"""Pre-render every dependency-graph view of the Blueprint atlas with Graphviz.

The Verso manifest stores one DOT source per render variant: `full` (every
statement, one dashed cluster per group), `group` (the synthetic group
overview) and `parent:<group>` (one focused subgraph per group). Rendering
them offline keeps D3 and Graphviz-WASM out of the browser for a graph with
more than a thousand nodes. The `full` view is written to the requested SVG
path; every other view goes to a sibling directory, and an index JSON maps
variant keys to their files and sizes for the page runtime.

Each view is checked after rendering: the SVG must contain as many nodes,
edges and clusters as its DOT source declares, and the `full` view as many as
the manifest lists. A DOT source that still carries structured-source metadata
is refused.

The script replaces an earlier JavaScript renderer, writes the same files and
fails in the same cases. Its patterns keep JavaScript's meaning: `\\s` is
spelled out (`WS`), `^` under the `m` flag also matches after `\\r`, U+2028 and
U+2029 (`BOL`), and `\\b` and the `i` flag are ASCII-only (`re.ASCII`). Graphviz
output is captured up to 64 MiB per stream (`MAX_OUTPUT`), invalid UTF-8 in it
becomes U+FFFD, and arguments after the second are ignored.

Usage: python3 Blueprint/Tools/build-dependency-atlas.py <manifest.json> <output.svg>
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import threading
from pathlib import Path

# The capture limit of the JavaScript renderer, for each of Graphviz's output streams.
MAX_OUTPUT = 64 * 1024 * 1024

# JavaScript's `\s`, and its `^` under the `m` flag.
WS = "[\\t\\n\\v\\f\\r \\u00a0\\u1680\\u2000-\\u200a\\u2028\\u2029\\u202f\\u205f\\u3000\\ufeff]"
BOL = "(?:^|(?<=[\\n\\r\\u2028\\u2029]))"

DOT_NODE = re.compile(BOL + WS + '*"[^"\\n]+"' + WS + "*\\[")
DOT_EDGE = re.compile(BOL + WS + '*"[^"\\n]+"' + WS + "*->" + WS + '*"[^"\\n]+"')
DOT_CLUSTER = re.compile(BOL + WS + "*subgraph" + WS + '+"cluster_')

LEAKED_METADATA = [
    re.compile("%%%" + WS + "*source", re.ASCII | re.IGNORECASE),
    re.compile("\\bsource" + WS + "*:=" + WS + "*\\{", re.ASCII | re.IGNORECASE),
    re.compile('\\bdocument' + WS + '*:=' + WS + '*"[^"]+"' + WS + "+spans" + WS + "*:=",
               re.ASCII | re.IGNORECASE),
]


class AtlasError(Exception):
    """A manifest or a rendered view that must stop the site build."""


def count(pattern: re.Pattern[str], text: str) -> int:
    return sum(1 for _ in pattern.finditer(text))


def file_name_for_variant(key: str) -> str:
    return re.sub("[^A-Za-z0-9._-]+", "_", key) + ".svg"


def run_dot(dot: str) -> tuple[int, bytes, bytes]:
    """Run `dot -Tsvg` on `dot`; return its status, standard output and standard error."""
    try:
        process = subprocess.Popen(["dot", "-Tsvg"], stdin=subprocess.PIPE,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError as error:
        raise AtlasError(f"Could not run Graphviz dot: {error}") from error
    captured: dict[str, list[bytes]] = {"stdout": [], "stderr": []}
    overflow = threading.Event()

    def capture(name: str) -> None:
        stream = getattr(process, name)
        size = 0
        for chunk in iter(lambda: stream.read(1 << 16), b""):
            size += len(chunk)
            if size > MAX_OUTPUT:
                overflow.set()
                process.kill()
                return
            captured[name].append(chunk)

    with process:
        readers = [threading.Thread(target=capture, args=(name,)) for name in captured]
        for reader in readers:
            reader.start()
        try:
            process.stdin.write(dot.encode("utf-8"))
            process.stdin.close()
        except BrokenPipeError:
            pass
        for reader in readers:
            reader.join()
    if overflow.is_set():
        raise AtlasError(
            f"Could not run Graphviz dot: its output exceeds {MAX_OUTPUT // (1024 * 1024)} MiB.")
    return process.returncode, b"".join(captured["stdout"]), b"".join(captured["stderr"])


def render_dot(dot: str, label: str) -> str:
    if any(pattern.search(dot) for pattern in LEAKED_METADATA):
        raise AtlasError(
            f"The {label} dependency graph contains unrendered structured-source metadata.")
    status, stdout, stderr = run_dot(dot)
    if status != 0:
        raise AtlasError(
            f"Graphviz dot failed for the {label} view with status {status}:\n"
            + stderr.decode("utf-8", errors="replace"))
    output = stdout.decode("utf-8", errors="replace")
    svg_start = output.find("<svg ")
    if svg_start < 0:
        raise AtlasError(f"Graphviz did not produce an SVG document for the {label} view.")
    return output[svg_start:]


def build(manifest_path: Path, output_path: Path) -> str:
    """Write every view and the index; return the summary line."""
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    graphs = manifest.get("graphs") if isinstance(manifest, dict) else None
    if not isinstance(graphs, list) or len(graphs) != 1:
        raise AtlasError("Expected exactly one dependency graph in the Blueprint manifest.")

    graph = graphs[0]
    variants = graph.get("variants") if isinstance(graph.get("variants"), list) else []
    if not variants or variants[0].get("key") != "full":
        raise AtlasError("The global dependency graph has no leading full DOT variant.")

    node_count = len(graph["nodes"]) if isinstance(graph.get("nodes"), list) else 0
    edge_count = len(graph["edges"]) if isinstance(graph.get("edges"), list) else 0
    groups = graph.get("groups") if isinstance(graph.get("groups"), list) else []
    group_count = sum(
        1 for group in groups
        if isinstance(group.get("children"), list) and len(group["children"]) > 1)
    if node_count == 0:
        raise AtlasError("The dependency graph contains no statement nodes.")

    stem = output_path.name[:-len(".svg")] if output_path.name.endswith(".svg") else output_path.name
    variant_dir = output_path.parent / stem
    index_path = output_path.parent / f"{stem}.json"
    if variant_dir.is_symlink() or variant_dir.is_file():
        variant_dir.unlink()
    elif variant_dir.exists():
        shutil.rmtree(variant_dir)
    variant_dir.mkdir(parents=True)

    index = []
    seen_keys = set()
    for variant in variants:
        key = variant.get("key")
        if not isinstance(key, str) or not key:
            raise AtlasError("A dependency graph variant has no key.")
        if key in seen_keys:
            raise AtlasError(f"Duplicate dependency graph variant key: {key}")
        seen_keys.add(key)
        dot = variant.get("dot")
        if not isinstance(dot, str) or not dot:
            raise AtlasError(f"The dependency graph variant {key} has no DOT source.")

        expected_nodes = node_count if key == "full" else count(DOT_NODE, dot)
        expected_edges = edge_count if key == "full" else count(DOT_EDGE, dot)
        expected_clusters = count(DOT_CLUSTER, dot)
        if key == "full" and expected_clusters != group_count:
            raise AtlasError(
                f"The full dependency graph has {expected_clusters} clusters but the manifest "
                f"lists {group_count} groups with several members.")

        svg = render_dot(dot, key)
        rendered_nodes = svg.count('class="node"')
        rendered_edges = svg.count('class="edge"')
        rendered_clusters = svg.count('class="cluster"')
        if (rendered_nodes != expected_nodes or rendered_edges != expected_edges
                or rendered_clusters != expected_clusters):
            raise AtlasError(
                f"Pre-rendered dependency graph view {key} is incomplete: "
                f"{rendered_nodes}/{expected_nodes} nodes, "
                f"{rendered_edges}/{expected_edges} edges and "
                f"{rendered_clusters}/{expected_clusters} clusters.")

        svg = svg.replace(
            "<svg ",
            f'<svg data-node-count="{rendered_nodes:,}" '
            f'data-edge-count="{rendered_edges:,}" '
            f'data-cluster-count="{rendered_clusters:,}" '
            'data-variant-key="' + key.replace('"', "&quot;") + '" ',
            1)

        encoded = svg.encode("utf-8")
        if key == "full":
            target = output_path
            file = output_path.name
        else:
            target = variant_dir / file_name_for_variant(key)
            file = f"{variant_dir.name}/{file_name_for_variant(key)}"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(encoded)

        entry = {"key": key}
        if "label" in variant:
            entry["label"] = variant["label"]
        entry.update(file=file, nodes=rendered_nodes, edges=rendered_edges,
                     clusters=rendered_clusters, bytes=len(encoded))
        index.append(entry)

    index_path.write_text(
        json.dumps({"variants": index}, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    parent_views = sum(1 for entry in index if entry["key"].startswith("parent:"))
    return (f"Dependency atlas: pre-rendered {node_count} nodes and {edge_count} edges "
            f"in {group_count} clusters; {len(index)} views "
            f"({parent_views} group views) indexed in {index_path.name}.")


def main(argv: list[str]) -> int:
    if len(argv) < 2 or not argv[0] or not argv[1]:
        print("Usage: python3 Blueprint/Tools/build-dependency-atlas.py "
              "<manifest.json> <output.svg>", file=sys.stderr)
        return 2
    try:
        print(build(Path(argv[0]), Path(argv[1])))
    except AtlasError as error:
        print(f"build-dependency-atlas: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
