#!/usr/bin/env python3
"""Generate the certified plots of the Blueprint.

Every bar of a certified plot is a theorem: on a small panel ``[a, b]`` of the
horizontal axis the plotted function takes values in a rational interval
``[lo, hi]``, and that enclosure is proved by ``cega`` and checked by Lean's
kernel when the Blueprint package is built. This script writes those theorems
to ``Blueprint/Generated/CertifiedPlots.lean`` and a JSON drawing model to
``Blueprint/Generated/CertifiedPlotsData.lean``, which
``Blueprint.Commands.CertifiedPlots`` turns into inline SVG. The model lives in
its own import-free module, like the ledger data, because the theorem module
imports Mathlib's style linters and the model's lines are long.

The certified endpoints come from the calculator itself: for every panel the
script runs ``#cas [enclose x in [a, b]] (expr)`` through ``lake env lean`` in
the Blueprint package, reads the certified interval, and rounds it outward to
six decimal places. The theorem then states those rounded bounds, which the
tactic proves by weakening its exact certificate, so the statements stay
readable while every stated number is a kernel-checked bound.

``--check`` validates the committed files without running Lean: the JSON model
must list exactly the theorems present in the theorem file with the same
panels and bounds. Regenerating (the default) needs a built ``PDE`` library in the
Blueprint package environment, exactly as ``Blueprint/Tools/build.sh``
has after its ``lake build PDE`` step.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import textwrap
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BLUEPRINT_DIR = REPO_ROOT / "Blueprint"
OUTPUT_PATH = BLUEPRINT_DIR / "Generated" / "CertifiedPlots.lean"
DATA_PATH = BLUEPRINT_DIR / "Generated" / "CertifiedPlotsData.lean"
DEFAULT_PROBE_DIR = REPO_ROOT / "_out" / "certified-plots"
GENERATOR = "Blueprint/Tools/build-certified-plots.py"
ROUNDING = 10**6

# Plot geometry shared by every family (SVG user units).
VIEW_WIDTH = 640
VIEW_HEIGHT = 340
MARGIN_LEFT = 58
MARGIN_RIGHT = 16
MARGIN_TOP = 14
MARGIN_BOTTOM = 40
PLOT_WIDTH = VIEW_WIDTH - MARGIN_LEFT - MARGIN_RIGHT
PLOT_HEIGHT = VIEW_HEIGHT - MARGIN_TOP - MARGIN_BOTTOM

CURVE_COLORS = ["#1d4ed8", "#0f766e", "#b45309"]


def lean_rat(q: Fraction) -> str:
    """Lean source for a rational literal, without parentheses."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def lean_arg(q: Fraction) -> str:
    """Lean source for a rational literal in argument position."""
    text = lean_rat(q)
    if q < 0 or q.denominator != 1:
        return f"({text})"
    return text


def tex_rat(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    sign = "-" if q < 0 else ""
    return f"{sign}\\tfrac{{{abs(q.numerator)}}}{{{q.denominator}}}"


def decimal_text(q: Fraction, places: int = 6) -> str:
    """Fixed-point decimal text of a rational already rounded to ``places``."""
    sign = "-" if q < 0 else ""
    scaled = abs(q) * 10**places
    if scaled.denominator != 1:
        return f"{float(q):.{places}f}"
    integer, frac = divmod(scaled.numerator, 10**places)
    text = f"{integer}.{frac:0{places}d}".rstrip("0").rstrip(".")
    return sign + (text if text else "0")


@dataclass
class Curve:
    slug: str
    param: Fraction
    param_tex: str
    goal_expr: str  # Lean expression in `p 0`
    tactic_expr: str  # the same expression in `x`
    describe: str  # prose description of the curve for docstrings and tooltips


@dataclass
class Family:
    id: str
    title: str
    formula_tex: str
    theorem_prefix: str
    x_min: Fraction
    x_max: Fraction
    panels: int
    x_label: str
    y_label: str
    curves: list[Curve]
    y_min: Fraction | None = None
    y_max: Fraction | None = None
    y_ticks: list[Fraction] = field(default_factory=list)
    x_ticks: list[Fraction] = field(default_factory=list)


def heat_curve(t: Fraction) -> Curve:
    tl = lean_rat(t)
    tl_arg = f"({tl})" if t.denominator != 1 else tl
    goal = (
        f"(4 * Real.pi * {tl_arg}) ^ (-(1:ℝ)/2) * Real.exp (-(p 0 ^ 2 / (4 * {tl_arg})))"
    )
    tactic = (
        f"(4 * Real.pi * {tl_arg}) ^ (-(1:ℝ)/2) * Real.exp (-(x ^ 2 / (4 * {tl_arg})))"
    )
    return Curve(
        slug=f"t{tl.replace('/', '_')}",
        param=t,
        param_tex=f"t = {tex_rat(t)}",
        goal_expr=goal,
        tactic_expr=tactic,
        describe=f"the one-dimensional heat kernel `Φ(x, t) = (4πt)^(-1/2) exp(-x²/(4t))` at `t = {tl}`",
    )


def wave_curve(t: Fraction) -> Curve:
    tl = lean_rat(t)
    return Curve(
        slug=f"t{tl.replace('/', '_')}",
        param=t,
        param_tex=f"t = {tex_rat(t)}",
        goal_expr=f"Real.sin (p 0 - {tl})",
        tactic_expr=f"Real.sin (x - {tl})",
        describe=f"d'Alembert's traveling sine wave `u(x, t) = sin(x - t)` at `t = {tl}`",
    )


def rarefaction_curve(t: Fraction) -> Curve:
    tl = lean_rat(t)
    tl_arg = f"({tl})" if t.denominator != 1 else tl
    return Curve(
        slug=f"t{tl.replace('/', '_')}",
        param=t,
        param_tex=f"t = {tex_rat(t)}",
        goal_expr=f"p 0 / {tl_arg}",
        tactic_expr=f"x / {tl_arg}",
        describe=f"the Burgers rarefaction profile `u(x, t) = x / t` at `t = {tl}`",
    )


FAMILIES = [
    Family(
        id="heat",
        title="One-dimensional heat kernel",
        formula_tex=r"\Phi(x,t) = (4\pi t)^{-1/2} e^{-x^2/(4t)}",
        theorem_prefix="heat_kernel",
        x_min=Fraction(-3),
        x_max=Fraction(3),
        panels=40,
        x_label="x",
        y_label="Φ(x, t)",
        curves=[heat_curve(Fraction(1, 4)), heat_curve(Fraction(1, 2)), heat_curve(Fraction(1))],
        y_min=Fraction(0),
        y_ticks=[Fraction(k, 10) for k in range(0, 7)],
        x_ticks=[Fraction(k) for k in range(-3, 4)],
    ),
    Family(
        id="wave",
        title="Traveling sine wave",
        formula_tex=r"u(x,t) = \sin(x - t)",
        theorem_prefix="traveling_sine",
        x_min=Fraction(-3),
        x_max=Fraction(3),
        panels=40,
        x_label="x",
        y_label="u(x, t)",
        curves=[wave_curve(Fraction(1, 2)), wave_curve(Fraction(1)), wave_curve(Fraction(3, 2))],
        y_min=Fraction(-1),
        y_max=Fraction(1),
        y_ticks=[Fraction(k, 2) for k in range(-2, 3)],
        x_ticks=[Fraction(k) for k in range(-3, 4)],
    ),
    Family(
        id="rarefaction",
        title="Burgers rarefaction profile",
        formula_tex=r"u(x,t) = x/t",
        theorem_prefix="rarefaction",
        x_min=Fraction(-1),
        x_max=Fraction(1),
        panels=40,
        x_label="x",
        y_label="u(x, t)",
        curves=[
            rarefaction_curve(Fraction(1, 2)),
            rarefaction_curve(Fraction(1)),
            rarefaction_curve(Fraction(2)),
        ],
        y_min=Fraction(-2),
        y_max=Fraction(2),
        y_ticks=[Fraction(k) for k in range(-2, 3)],
        x_ticks=[Fraction(k, 2) for k in range(-2, 3)],
    ),
]


def panel_bounds(family: Family) -> list[tuple[Fraction, Fraction]]:
    width = (family.x_max - family.x_min) / family.panels
    return [
        (family.x_min + width * k, family.x_min + width * (k + 1))
        for k in range(family.panels)
    ]


def theorem_name(family: Family, curve: Curve, index: int) -> str:
    return f"{family.theorem_prefix}_{curve.slug}_panel_{index:02d}"


# --- probing -----------------------------------------------------------------

OUTPUT_LINE = re.compile(r"^Output \(certified interval in ℝ\): \[(.*), (.*)\]\s*$")
HEADER_LINE = re.compile(r"^#cas \[enclose x ∈ \[(.*), (.*)\]\]\s*$")


def parse_endpoint(text: str) -> Fraction:
    text = text.strip()
    if re.fullmatch(r"-?[0-9]+", text):
        return Fraction(int(text))
    if re.fullmatch(r"-?[0-9]+/[0-9]+", text):
        return Fraction(text)
    if re.fullmatch(r"-?[0-9]+\.[0-9]+", text):
        return Fraction(text)
    raise ValueError(f"unrecognized certified endpoint {text!r}")


def probe_fingerprint(source: str) -> dict[str, str | int]:
    """Identify the queries, generator, pinned dependencies, and numerical sources."""
    paths = [
        Path(__file__),
        REPO_ROOT / "lean-toolchain",
        REPO_ROOT / "lakefile.lean",
        REPO_ROOT / "lake-manifest.json",
        BLUEPRINT_DIR / "lakefile.lean",
        BLUEPRINT_DIR / "lake-manifest.json",
    ]
    symbolic_root = REPO_ROOT / "PDE" / "Symbolic"
    if not symbolic_root.is_dir():
        raise SystemExit(f"certified plot probe needs the provider sources: {symbolic_root}")
    floatlib_roots = [root for root in (
        REPO_ROOT / ".lake" / "packages" / "floatlib" / "FloatLib",
        BLUEPRINT_DIR / ".lake" / "packages" / "floatlib" / "FloatLib",
    ) if root.is_dir()]
    if not floatlib_roots:
        raise SystemExit("certified plot probe needs at least one FloatLib source checkout")
    digest = hashlib.sha256()
    for root in (symbolic_root, *floatlib_roots):
        digest.update(b"root\0" + str(root.relative_to(REPO_ROOT)).encode("utf8") + b"\0")
        paths.extend(root.rglob("*.lean"))
    for path in sorted(paths):
        digest.update(str(path.relative_to(REPO_ROOT)).encode("utf8") + b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    return {
        "schemaVersion": 1,
        "probeSha256": hashlib.sha256(source.encode("utf8")).hexdigest(),
        "sourcesSha256": digest.hexdigest(),
    }


def read_probe_cache(cache: Path, fingerprint: dict, order: list[str]
                     ) -> dict[str, tuple[Fraction, Fraction]] | None:
    """Reject unversioned, incomplete, or stale endpoint caches."""
    try:
        cached = json.loads(cache.read_text(encoding="utf8"))
        if not isinstance(cached, dict) or cached.get("fingerprint") != fingerprint:
            return None
        raw = cached.get("intervals")
        if not isinstance(raw, dict) or set(raw) != set(order):
            return None
        result = {name: (Fraction(lo), Fraction(hi)) for name, (lo, hi) in raw.items()}
        return result if all(lo <= hi for lo, hi in result.values()) else None
    except (OSError, ValueError, TypeError, ZeroDivisionError):
        return None


def enclosure_query(curve: Curve, a: Fraction, b: Fraction) -> str:
    """Keep the diagnostic command and its expression on separate source lines."""
    return (
        f"#cas [enclose x in [{lean_rat(a)}, {lean_rat(b)}]]\n"
        f"  ({curve.tactic_expr})"
    )


def probe_source() -> tuple[str, list[str]]:
    """Build every query and reject overlong source lines before invoking Lean."""
    lines = [
        "import CAS", "",
        "/-! Certified plot enclosure queries generated for the current calculator. -/", "",
    ]
    order: list[str] = []
    for family in FAMILIES:
        for curve in family.curves:
            for index, (a, b) in enumerate(panel_bounds(family)):
                name = theorem_name(family, curve, index)
                order.append(name)
                lines.append(enclosure_query(curve, a, b))
    source = "\n".join(lines) + "\n"
    overlong = [i for i, line in enumerate(source.splitlines(), 1) if len(line) > 100]
    if overlong:
        raise ValueError(f"certified plot query source exceeds 100 columns on lines {overlong}")
    return source, order


def probe_intervals(probe_dir: Path, cpus: str | None, reuse: bool) -> dict[str, tuple[Fraction, Fraction]]:
    """Run one `#cas` enclosure per panel and return the certified intervals.

    The results are cached in ``probe_dir/intervals.json``; with ``reuse`` a
    complete cache with the same query and source fingerprint is used instead
    of running Lean again.
    """
    source, order = probe_source()
    probe_dir.mkdir(parents=True, exist_ok=True)
    probe = probe_dir / "probe.lean"
    cache = probe_dir / "intervals.json"
    fingerprint = probe_fingerprint(source)
    if reuse:
        cached = read_probe_cache(cache, fingerprint, order)
        if cached is not None:
            return cached
        print("Certified plot cache missing, incomplete, or stale; probing current sources.")
    probe.write_text(source, encoding="utf8")

    command = [
        "lake", "-d", str(BLUEPRINT_DIR), "env", "lean",
        "-Dpp.unicode.fun=true", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
        "-Dweak.linter.mathlibStandardSet=true", "-DwarningAsError=true", str(probe),
    ]
    if cpus:
        command = ["taskset", "-c", cpus] + command
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "8")
    completed = subprocess.run(
        command, cwd=REPO_ROOT, env=env, capture_output=True, text=True, check=False
    )
    output = completed.stdout + completed.stderr
    (probe_dir / "probe.log").write_text(output, encoding="utf8")
    errors = [line for line in output.splitlines() if ": error:" in line]
    if completed.returncode != 0 or errors:
        sys.stderr.write(output)
        raise SystemExit(
            f"certified plot probe failed with exit code {completed.returncode}; "
            f"{len(errors)} error line(s) above"
        )
    intervals: list[tuple[Fraction, Fraction]] = []
    for line in output.splitlines():
        match = OUTPUT_LINE.match(line.strip())
        if match:
            intervals.append((parse_endpoint(match.group(1)), parse_endpoint(match.group(2))))
    if len(intervals) != len(order):
        raise SystemExit(
            f"expected {len(order)} certified intervals from the probe, found {len(intervals)}"
        )
    result = dict(zip(order, intervals))
    if probe_fingerprint(source) != fingerprint:
        raise SystemExit("certified plot sources changed during the probe; rerun on frozen sources")
    cache.write_text(
        json.dumps({
            "fingerprint": fingerprint,
            "intervals": {name: [str(lo), str(hi)] for name, (lo, hi) in result.items()},
        }, indent=0),
        encoding="utf8",
    )
    return result


def round_outward(lo: Fraction, hi: Fraction) -> tuple[Fraction, Fraction]:
    lo_r = Fraction(math.floor(lo * ROUNDING), ROUNDING)
    hi_r = Fraction(math.ceil(hi * ROUNDING), ROUNDING)
    if lo_r > lo or hi_r < hi:
        raise AssertionError("outward rounding produced a tighter interval")
    return lo_r, hi_r


# --- drawing model -------------------------------------------------------------

def scale(value: Fraction, lo: Fraction, hi: Fraction, size: float) -> float:
    if hi == lo:
        return 0.0
    return float((value - lo) / (hi - lo)) * size


def fmt(value: float) -> str:
    return f"{value:.2f}"


def build_model(intervals: dict[str, tuple[Fraction, Fraction]], theorem_lines: dict[str, int]) -> dict:
    families = []
    for family in FAMILIES:
        bounds = panel_bounds(family)
        rounded: dict[str, tuple[Fraction, Fraction]] = {}
        for curve in family.curves:
            for index in range(family.panels):
                name = theorem_name(family, curve, index)
                rounded[name] = round_outward(*intervals[name])
        y_min = family.y_min if family.y_min is not None else min(v[0] for v in rounded.values())
        y_max = family.y_max if family.y_max is not None else max(v[1] for v in rounded.values())
        if family.y_max is None:
            y_max = y_max + (y_max - y_min) / 12
        curves = []
        for color, curve in zip(CURVE_COLORS, family.curves):
            bars = []
            for index, (a, b) in enumerate(bounds):
                name = theorem_name(family, curve, index)
                lo, hi = rounded[name]
                x1 = MARGIN_LEFT + scale(a, family.x_min, family.x_max, PLOT_WIDTH)
                x2 = MARGIN_LEFT + scale(b, family.x_min, family.x_max, PLOT_WIDTH)
                y_top = MARGIN_TOP + PLOT_HEIGHT - scale(hi, y_min, y_max, PLOT_HEIGHT)
                y_bottom = MARGIN_TOP + PLOT_HEIGHT - scale(lo, y_min, y_max, PLOT_HEIGHT)
                bars.append({
                    "a": lean_rat(a),
                    "b": lean_rat(b),
                    "lo": lean_rat(lo),
                    "hi": lean_rat(hi),
                    "loDecimal": decimal_text(lo),
                    "hiDecimal": decimal_text(hi),
                    "name": f"LeanPDE.CertifiedPlots.{name}",
                    "line": theorem_lines[name],
                    "statement": (
                        f"EnclosedOn (fun p : ℝ^1 ↦ {curve.goal_expr}) "
                        f"{{p | {lean_rat(a)} ≤ p 0 ∧ p 0 ≤ {lean_rat(b)}}} "
                        f"{lean_arg(lo)} {lean_arg(hi)}"
                    ),
                    "x": fmt(x1),
                    "width": fmt(max(x2 - x1, 0.5)),
                    "y": fmt(y_top),
                    "height": fmt(max(y_bottom - y_top, 0.75)),
                })
            curves.append({
                "id": f"{family.id}_{curve.slug}",
                "param": lean_rat(curve.param),
                "paramTeX": curve.param_tex,
                "color": color,
                "goal": curve.goal_expr,
                "bars": bars,
            })
        families.append({
            "id": family.id,
            "title": family.title,
            "formulaTeX": family.formula_tex,
            "xLabel": family.x_label,
            "yLabel": family.y_label,
            "xMin": lean_rat(family.x_min),
            "xMax": lean_rat(family.x_max),
            "panels": family.panels,
            "view": {
                "width": VIEW_WIDTH,
                "height": VIEW_HEIGHT,
                "plotLeft": fmt(MARGIN_LEFT),
                "plotTop": fmt(MARGIN_TOP),
                "plotRight": fmt(MARGIN_LEFT + PLOT_WIDTH),
                "plotBottom": fmt(MARGIN_TOP + PLOT_HEIGHT),
            },
            "xTicks": [
                {"label": decimal_text(t), "x": fmt(MARGIN_LEFT + scale(t, family.x_min, family.x_max, PLOT_WIDTH))}
                for t in family.x_ticks
            ],
            "yTicks": [
                {"label": decimal_text(t), "y": fmt(MARGIN_TOP + PLOT_HEIGHT - scale(t, y_min, y_max, PLOT_HEIGHT))}
                for t in family.y_ticks
                if y_min <= t <= y_max
            ],
            "curves": curves,
        })
    return {
        "schemaVersion": 1,
        "generator": GENERATOR,
        "theorems": sum(f.panels * len(f.curves) for f in FAMILIES),
        "families": families,
    }


# --- Lean source ------------------------------------------------------------------

HEADER = """/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import CAS

/-!
# Certified plots

Generated by `Blueprint/Tools/build-certified-plots.py`. Do not edit by hand.

Every theorem below is one bar of a plot in the Certified Plots section of the
Blueprint's computation chapter: on a rational panel `[a, b]` of the horizontal
axis the plotted explicit
solution takes values in the stated rational interval, and `cega` proves the
enclosure from a checked interval certificate. The endpoints are the
calculator's certified bounds rounded outward to six decimal places, so the
statements are readable and the tactic closes them by weakening its exact
certificate. The drawing model consumed by `Blueprint.Commands.CertifiedPlots`
is the JSON literal of `Blueprint.Generated.CertifiedPlotsData`; it lists the
same panels and bounds as the theorems here, which
`Blueprint/Tools/build-certified-plots.py --check` verifies without running Lean.

{summary}
-/

namespace LeanPDE.CertifiedPlots

open CAS.Certificate

"""

FOOTER = """
end LeanPDE.CertifiedPlots
"""

DATA_TEMPLATE = """/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

/-!
# Certified plot data

Generated by `Blueprint/Tools/build-certified-plots.py` together with
`Blueprint.Generated.CertifiedPlots`. Do not edit by hand.

The JSON below is the drawing model of the certified plots: for every shaded
panel its rational bounds, the name and line of the theorem proving them in
`Blueprint/Generated/CertifiedPlots.lean`, and its SVG coordinates. The module
imports nothing so that the long lines of the model stay outside the reach of
the style linters loaded by the theorem module.
-/

namespace LeanPDE.CertifiedPlotsData

/-- Drawing model of the certified plots; see `Blueprint.Commands.CertifiedPlots`. -/
def json : String := r####"
{json}
"####

end LeanPDE.CertifiedPlotsData
"""


def wrap_comment(text: str, width: int = 96) -> str:
    """Wrap prose onto lines of at most ``width`` columns."""
    return "\n".join(textwrap.wrap(text, width=width, break_long_words=False, break_on_hyphens=False))


def theorem_source(family: Family, curve: Curve, index: int, a: Fraction, b: Fraction,
                   lo: Fraction, hi: Fraction) -> str:
    name = theorem_name(family, curve, index)
    doc = wrap_comment(
        f"/-- Panel {index + 1} of {family.panels} for {curve.describe}: "
        f"for `x ∈ [{lean_rat(a)}, {lean_rat(b)}]` the value lies in "
        f"`[{lean_rat(lo)}, {lean_rat(hi)}]`. -/"
    )
    return "\n".join([
        doc,
        f"theorem {name} :",
        "    EnclosedOn",
        f"      (fun p : ℝ^1 ↦ {curve.goal_expr})",
        f"      {{p | {lean_rat(a)} ≤ p 0 ∧ p 0 ≤ {lean_rat(b)}}} {lean_arg(lo)} {lean_arg(hi)} := by",
        f"  cega [enclose x in [{lean_rat(a)}, {lean_rat(b)}]]",
        f"    ({curve.tactic_expr})",
        "",
    ])


def generate(intervals: dict[str, tuple[Fraction, Fraction]]) -> tuple[str, str, dict]:
    summary_lines = []
    for family in FAMILIES:
        summary_lines.append(wrap_comment(
            f"* `{family.id}`: {family.title}, {len(family.curves)} curves at "
            f"{', '.join(f'`t = {lean_rat(c.param)}`' for c in family.curves)}, "
            f"{family.panels} panels each on `x ∈ [{lean_rat(family.x_min)}, {lean_rat(family.x_max)}]`."
        ).replace("\n", "\n  "))
    header = HEADER.format(summary="\n".join(summary_lines))
    body_parts: list[str] = []
    for family in FAMILIES:
        bounds = panel_bounds(family)
        for curve in family.curves:
            for index, (a, b) in enumerate(bounds):
                name = theorem_name(family, curve, index)
                lo, hi = round_outward(*intervals[name])
                body_parts.append(theorem_source(family, curve, index, a, b, lo, hi))
    body = header + "\n".join(body_parts)
    # The JSON model follows the theorems, so their line numbers are final here.
    theorem_lines = {
        match.group(1): body[: match.start()].count("\n") + 1
        for match in re.finditer(r"^theorem (\S+) :", body, re.MULTILINE)
    }
    model = build_model(intervals, theorem_lines)
    json_text = json.dumps(model, indent=1, ensure_ascii=False)
    if '"####' in json_text:
        raise SystemExit("plot JSON contains the raw string terminator sequence")
    return body + FOOTER, DATA_TEMPLATE.format(json=json_text), model


# --- checking ----------------------------------------------------------------------

THEOREM_PATTERN = re.compile(
    r"^theorem (?P<name>\S+) :\n"
    r"    EnclosedOn\n"
    r"      \(fun p : ℝ\^1 ↦ (?P<goal>.*)\)\n"
    r"      \{p \| (?P<a>\S+) ≤ p 0 ∧ p 0 ≤ (?P<b>\S+)\} (?P<lo>\S+) (?P<hi>\S+) := by\n",
    re.MULTILINE,
)


def strip_parens(text: str) -> str:
    return text[1:-1] if text.startswith("(") and text.endswith(")") else text


def check(source: str, data_source: str) -> int:
    match = re.search(r'r(#+)"\n([\s\S]*?)\n"\1', data_source)
    if not match:
        print("certified plots: no JSON literal found", file=sys.stderr)
        return 1
    model = json.loads(match.group(2))
    theorems = {
        m.group("name"): m
        for m in THEOREM_PATTERN.finditer(source)
    }
    problems = []
    seen = set()
    intervals = {}
    for family in model["families"]:
        for curve in family["curves"]:
            for bar in curve["bars"]:
                name = bar["name"].split(".")[-1]
                seen.add(name)
                intervals[name] = (Fraction(bar["lo"]), Fraction(bar["hi"]))
                found = theorems.get(name)
                if not found:
                    problems.append(f"{name}: theorem missing from the file")
                    continue
                expected = (bar["a"], bar["b"], bar["lo"], bar["hi"], curve["goal"])
                actual = (
                    found.group("a"), found.group("b"),
                    strip_parens(found.group("lo")), strip_parens(found.group("hi")),
                    found.group("goal"),
                )
                if expected != actual:
                    problems.append(f"{name}: JSON {expected} differs from theorem {actual}")
                line_index = source[: found.start()].count("\n") + 1
                if line_index != bar["line"]:
                    problems.append(f"{name}: JSON line {bar['line']} but theorem at line {line_index}")
    extra = set(theorems) - seen
    if extra:
        problems.append(f"theorems without a bar: {sorted(extra)}")
    if model["theorems"] != len(seen) or len(theorems) != len(seen):
        problems.append(
            f"theorem count {len(theorems)} and bar count {len(seen)} disagree with the model ({model['theorems']})"
        )
    expected_names = {
        theorem_name(family, curve, index)
        for family in FAMILIES for curve in family.curves for index in range(family.panels)
    }
    if seen != expected_names:
        problems.append("panel names differ from the generator's plot families")
    if not problems:
        expected_source, expected_data, _ = generate(intervals)
        if source != expected_source:
            problems.append("theorem source is not reproduced by the generator")
        if data_source != expected_data:
            problems.append("drawing model is not reproduced by the generator")
    for problem in problems:
        print(f"certified plots: {problem}", file=sys.stderr)
    if problems:
        return 1
    print(
        f"Certified plots are consistent: {len(theorems)} theorems in "
        f"{sum(len(f['curves']) for f in model['families'])} curves across {len(model['families'])} plots."
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--check", action="store_true", help="validate the committed file without running Lean")
    parser.add_argument("--json", metavar="PATH", help="also write the drawing model to PATH")
    parser.add_argument("--probe-dir", metavar="DIR", default=str(DEFAULT_PROBE_DIR),
                        help="scratch directory for the probe file (default: _out/certified-plots)")
    parser.add_argument("--cpus", metavar="LIST", default=None,
                        help="taskset CPU list for the Lean probe (default: unrestricted)")
    parser.add_argument("--reuse-probe", action="store_true",
                        help="reuse a complete intervals.json only when its query/source fingerprint matches")
    args = parser.parse_args()

    if args.check:
        for required in (OUTPUT_PATH, DATA_PATH):
            if not required.exists():
                print(f"certified plots: {required} does not exist", file=sys.stderr)
                return 1
        return check(OUTPUT_PATH.read_text(encoding="utf8"), DATA_PATH.read_text(encoding="utf8"))

    intervals = probe_intervals(Path(args.probe_dir), args.cpus, args.reuse_probe)
    source, data_source, model = generate(intervals)
    if args.json:
        Path(args.json).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json).write_text(json.dumps(model, indent=1, ensure_ascii=False) + "\n", encoding="utf8")
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    for target, text in ((OUTPUT_PATH, source), (DATA_PATH, data_source)):
        existing = target.read_text(encoding="utf8") if target.exists() else None
        if existing != text:
            target.write_text(text, encoding="utf8")
    status = check(source, data_source)
    if status != 0:
        return status
    print(
        f"Certified plots: {model['theorems']} theorems written to {OUTPUT_PATH.relative_to(REPO_ROOT)}, "
        f"drawing model to {DATA_PATH.relative_to(REPO_ROOT)}."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
