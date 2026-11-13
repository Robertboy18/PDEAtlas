#!/usr/bin/env python3
"""Compute the Blueprint's figures and write them as an inline-SVG drawing model.

Every figure of the book is computed here from the mathematics it illustrates,
never drawn by hand and never downloaded: the heat kernel is the Gaussian
``(4 pi t)^(-n/2) exp(-|x|^2/(4t))`` sampled at several times, the mollified
step is a numerical convolution against the standard bump, the harmonic level
curves come out of a marching-squares tracer, the Burgers shock starts from the
characteristics ``x = x0 + t u0(x0)``, and the interval enclosures are computed
by naive interval arithmetic on subdivisions so that the picture shows the
overestimate a reader can reproduce. The output is a JSON drawing model in
``Blueprint/Generated/FiguresData.lean``, which
``Blueprint.Commands.Figures`` turns into inline SVG for
``{leanpde_figure "id"}``.

The model is a flat list of marks per figure: paths, lines, rectangles,
circles and text, each carrying a colour *role* rather than a colour. The
renderer maps the seven roles onto the site's ``--leanpde-fig-*`` custom
properties, so one variable change re-colours every figure in both the light
and the dark theme, and no figure contains a literal colour.

Mathematical labels are text marks with a ``tex`` field and a readable ``t``
fallback. Caption mathematics uses inline ``\\(...\\)`` delimiters. The HTML
build typesets both with KaTeX; this generator never simulates typesetting with
Unicode scripts or displaced SVG text runs.

Several figures move. Their frames are computed here and emitted as SMIL value
lists, so the motion is the mathematics: the diffusion profile spreads as the
Gaussian does at increasing ``t``, the enclosure tightens as the subdivision
refines, the error budget closes to zero at the exact case. Every animated mark
also carries its most informative frame as its static attribute value, which is
what a reader who asked for reduced motion sees.

Two conventions hold throughout. A panel that draws a region of the
plane draws that region's boundary, so the box around the harmonic saddle and
the circle around the harmonic disc are the domain and not decoration; a panel
that draws a graph over an axis draws the axis instead and never a box. Solid
is the object the caption is about, dashed is auxiliary construction, and a
faint thin copy is another frame of the same family.

``--check`` recomputes the model and fails if the committed module differs, so
the figures cannot drift away from the code that drew them. It needs nothing
but the standard library, like ``build-certified-plots.py --check``, and every
coordinate is quantized to two decimals with a rule that does not depend on the
platform's rounding of a tie, so the check is stable across machines.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
from pathlib import Path
from fractions import Fraction

REPO_ROOT = Path(__file__).resolve().parents[2]
DATA_PATH = REPO_ROOT / "Blueprint" / "Generated" / "FiguresData.lean"
GENERATOR = "Blueprint/Tools/build-figures.py"
SCHEMA_VERSION = 1

# Colour roles. The renderer maps each one to a `--leanpde-fig-*` custom
# property; nothing here knows a colour.
ROLES = ("ink", "muted", "accent", "accent2", "band", "warn", "surface")

# Type sizes in SVG user units, with larger labels where a figure needs them.
# At a rendered width of 640 CSS pixels, one unit in a 640-unit viewBox is a
# pixel. On narrow screens the figure scrolls within its own container so
# labels keep a readable size instead of shrinking to fit the whole diagram.
FS_LABEL = 11.0
FS_TITLE = 13.0

# Three stroke widths per figure and no more: reference geometry, secondary
# curve, and the curve the caption is about.
SW_AXIS = 0.75
SW_CURVE2 = 1.4
SW_CURVE = 2.0

# Construction dashes: solid is the object itself, dashed is auxiliary.
DASH = "4 4"
DOT = "2 4"

DUR_SLOW = "9s"
DUR_MED = "8s"


# --- quantization ------------------------------------------------------------

def q2(value: float) -> str:
    """Two-decimal text of ``value``, rounded half up away from ties.

    The nudge keeps the result stable when a platform's ``exp`` or ``log``
    differs in the last bit: a value has to sit within 1e-9 of a tie for the
    nudge to matter, and then both platforms round the same way.
    """
    if not math.isfinite(value):
        raise ValueError(f"non-finite coordinate {value!r}")
    scaled = math.floor(abs(value) * 100.0 + 0.5 + 1e-9)
    if scaled == 0:
        return "0"
    text = f"{scaled // 100}.{scaled % 100:02d}".rstrip("0").rstrip(".")
    return ("-" if value < 0 else "") + text


def q3(value: float) -> str:
    """Three-decimal text, for numbers that appear in labels."""
    scaled = math.floor(abs(value) * 1000.0 + 0.5 + 1e-9)
    if scaled == 0:
        return "0"
    text = f"{scaled // 1000}.{scaled % 1000:03d}".rstrip("0").rstrip(".")
    return ("-" if value < 0 else "") + text


# --- the drawing model -------------------------------------------------------

# The keys of a mark are the SVG attribute names, so the renderer needs no
# translation table and no vocabulary of its own. These few are abbreviated on
# the way out because they occur on nearly every mark.
ATTR = {
    "sw": "stroke-width",
    "dash": "stroke-dasharray",
    "op": "opacity",
    "sop": "stroke-opacity",
    "fop": "fill-opacity",
    "size": "font-size",
    "anchor": "text-anchor",
    "weight": "font-weight",
    "w": "width",
    "h": "height",
}

# Keys the renderer interprets rather than copies: the tag, the text body, the
# colour roles, the clip to wrap the mark in, and the animations.
SPECIAL = frozenset({"k", "t", "tex", "stroke", "fill", "clip", "halo", "anim"})

# Every attribute a mark may carry. A typo in a figure is a build failure here
# rather than a silently dropped attribute in the browser.
ATTRS_ALLOWED = frozenset({
    "d", "x", "y", "width", "height", "rx", "ry", "cx", "cy", "r",
    "x1", "y1", "x2", "y2", "dx", "dy", "transform",
    "stroke-width", "stroke-dasharray", "stroke-linecap", "stroke-opacity",
    "fill-opacity", "opacity", "font-size", "font-weight", "font-style",
    "text-anchor", "letter-spacing",
})


class Scene:
    """One figure: a viewBox, a caption, an accessible label, and marks."""

    def __init__(self, fid: str, title: str, caption: str, alt: str,
                 width: float = 640.0, height: float = 300.0) -> None:
        self.id = fid
        self.title = title
        self.caption = caption
        self.alt = alt
        self.width = width
        self.height = height
        self.marks: list[dict] = []
        self.clips: list[dict] = []
        self.animated = False

    # -- defs

    def clip(self, name: str, x: float, y: float, w: float, h: float) -> str:
        cid = f"leanpde-fig-{self.id}-{name}"
        self.clips.append({"id": cid, "x": q2(x), "y": q2(y), "w": q2(w), "h": q2(h)})
        return cid

    # -- marks

    def add(self, mark: dict) -> dict:
        for key in ("stroke", "fill"):
            role = mark.get(key)
            if role not in (None, "") and role not in ROLES:
                raise SystemExit(f"figure {self.id}: unknown colour role {role!r}")
        out: dict = {}
        for key, value in mark.items():
            name = ATTR.get(key, key)
            if name not in SPECIAL and name not in ATTRS_ALLOWED:
                raise SystemExit(f"figure {self.id}: mark attribute {name!r} is not "
                                 "in the renderer's list")
            out[name] = value
        if out.get("anim"):
            self.animated = True
        self.marks.append(out)
        return out

    def path(self, d: str, stroke: str = "ink", sw: float = SW_CURVE,
             fill: str = "", **kw) -> dict:
        mark = {"k": "path", "d": d}
        if stroke:
            mark["stroke"] = stroke
            mark["sw"] = q2(sw)
        if fill:
            mark["fill"] = fill
        return self.add(_extras(mark, kw))

    def area(self, d: str, fill: str = "band", **kw) -> dict:
        return self.add(_extras({"k": "path", "d": d, "fill": fill}, kw))

    def line(self, x1: float, y1: float, x2: float, y2: float,
             stroke: str = "muted", sw: float = SW_CURVE2, **kw) -> dict:
        mark = {"k": "line", "x1": q2(x1), "y1": q2(y1), "x2": q2(x2), "y2": q2(y2),
                "stroke": stroke, "sw": q2(sw)}
        return self.add(_extras(mark, kw))

    def rect(self, x: float, y: float, w: float, h: float,
             stroke: str = "", fill: str = "band", sw: float = SW_CURVE2, **kw) -> dict:
        mark = {"k": "rect", "x": q2(x), "y": q2(y), "w": q2(max(w, 0.0)),
                "h": q2(max(h, 0.0))}
        if stroke:
            mark["stroke"] = stroke
            mark["sw"] = q2(sw)
        if fill:
            mark["fill"] = fill
        return self.add(_extras(mark, kw))

    def circle(self, cx: float, cy: float, r: float, stroke: str = "",
               fill: str = "ink", sw: float = SW_CURVE2, **kw) -> dict:
        mark = {"k": "circle", "cx": q2(cx), "cy": q2(cy), "r": q2(r)}
        if stroke:
            mark["stroke"] = stroke
            mark["sw"] = q2(sw)
        if fill:
            mark["fill"] = fill
        return self.add(_extras(mark, kw))

    def text(self, x: float, y: float, body: str, anchor: str = "middle",
             size: float = FS_LABEL, fill: str = "ink", italic: bool = False,
             weight: str = "", halo: bool = False, **kw) -> dict:
        """A label. ``halo`` paints the surface colour behind the glyphs, which
        is how a label stays readable where it crosses a curve."""
        mark = {"k": "text", "x": q2(x), "y": q2(y), "t": body, "fill": fill,
                "size": q2(size)}
        if anchor != "start":
            mark["anchor"] = anchor
        if italic:
            mark["font-style"] = "italic"
        if weight:
            mark["weight"] = weight
        if halo:
            mark["halo"] = "1"
        return self.add(_extras(mark, kw))

    def math(self, x: float, y: float, tex: str, t: str | None = None, **kw) -> dict:
        r"""Real TeX for build-time typesetting, on the same anchor as text.

        Supply ``t`` for a readable plain-text fallback when TeX commands are
        needed. Simple labels such as ``x`` and numeric ticks need no fallback.
        Use bare TeX here; only captions use ``\(...\)`` delimiters.
        """
        return self.text(x, y, tex if t is None else t, tex=tex, **kw)

    def label(self, x: float, y: float, body: str, **kw) -> dict:
        kw.setdefault("size", FS_LABEL)
        return self.text(x, y, body, **kw)

    def tick_label(self, x: float, y: float, body: str, **kw) -> dict:
        kw.setdefault("fill", "muted")
        return self.math(x, y, body.replace("−", "-"), **kw)

    def math_title(self, x: float, y: float, tex: str, **kw) -> dict:
        kw.setdefault("size", FS_TITLE)
        kw.setdefault("anchor", "start")
        return self.math(x, y, tex, **kw)

    def panel_title(self, x: float, y: float, body: str, **kw) -> dict:
        kw.setdefault("size", FS_TITLE)
        kw.setdefault("weight", "600")
        kw.setdefault("anchor", "start")
        return self.text(x, y, body, **kw)

    def to_json(self) -> dict:
        figure = {
            "id": self.id,
            "title": self.title,
            "caption": self.caption,
            "alt": self.alt,
            "width": q2(self.width),
            "height": q2(self.height),
            "animated": "1" if self.animated else "",
            "marks": [_element(mark) for mark in self.marks],
        }
        if self.clips:
            figure["clips"] = self.clips
        return figure


def _element(mark: dict) -> dict:
    """One mark as the renderer reads it: a tag, its attributes, its children.

    The keys are SVG attribute names already, so the renderer copies the ones
    it knows and needs no vocabulary of its own. Animations become child
    elements with the same shape.
    """
    out = dict(mark)
    steps = out.pop("anim", None)
    if steps:
        out["anim"] = [dict(step, **{"k": step["kind"]}) for step in steps]
        for step in out["anim"]:
            step.pop("kind", None)
    return out


def _extras(mark: dict, kw: dict) -> dict:
    """Attach the optional keys of a mark, dropping the empty ones."""
    for key, value in kw.items():
        if key == "anim":
            if value:
                mark["anim"] = value
            continue
        if key in ("op", "fop"):
            mark[key] = q3(float(value))
            continue
        if value in (None, "", 0):
            continue
        if key == "sw":
            mark["sw"] = q2(float(value))
        else:
            mark[key] = str(value)
    return mark


class Frame:
    """A mapping from data coordinates to SVG user units inside one panel."""

    def __init__(self, x0: float, y0: float, w: float, h: float,
                 xmin: float, xmax: float, ymin: float, ymax: float) -> None:
        self.x0, self.y0, self.w, self.h = x0, y0, w, h
        self.xmin, self.xmax, self.ymin, self.ymax = xmin, xmax, ymin, ymax

    def X(self, x: float) -> float:
        return self.x0 + (x - self.xmin) / (self.xmax - self.xmin) * self.w

    def Y(self, y: float) -> float:
        return self.y0 + self.h - (y - self.ymin) / (self.ymax - self.ymin) * self.h

    @property
    def right(self) -> float:
        return self.x0 + self.w

    @property
    def bottom(self) -> float:
        return self.y0 + self.h

    def project(self, points) -> list[tuple[float, float]]:
        return [(self.X(x), self.Y(y)) for x, y in points]

    def curve(self, points, tol: float = 0.2) -> str:
        """A polyline through data points, as SVG path data.

        Points that a reader could not tell from the straight line between
        their neighbours are dropped, at a tolerance in SVG user units. The
        drawing is the same and the page is a few kilobytes lighter.
        """
        return poly_path(thin(self.project(points), tol))

    def sample(self, f, xa: float, xb: float, n: int) -> str:
        return self.curve((xa + (xb - xa) * k / n, f(xa + (xb - xa) * k / n))
                          for k in range(n + 1))

    def band(self, points_lo, points_hi, tol: float = 0.2) -> str:
        """A filled region between two sampled curves."""
        lo = thin(self.project(points_lo), tol)
        hi = thin(self.project(points_hi), tol)
        return poly_path(lo + list(reversed(hi))) + "Z"

    def fill_to(self, points, base: float, tol: float = 0.2) -> str:
        """A sampled curve closed down to the horizontal line ``y = base``."""
        pts = thin(self.project(points), tol)
        edge = [(pts[0][0], self.Y(base))]
        return poly_path(edge + pts + [(pts[-1][0], self.Y(base))]) + "Z"

    def curve_frames(self, frames, tol: float = 0.25) -> list[str]:
        """One path per frame of an animation, all with the same point count."""
        projected = [self.project(f) for f in frames]
        mask = common_mask(projected, tol)
        return [poly_path([points[index] for index in mask]) for points in projected]

    def fill_frames(self, frames, base: float, tol: float = 0.25) -> list[str]:
        projected = [self.project(f) for f in frames]
        mask = common_mask(projected, tol)
        out = []
        for points in projected:
            chosen = [points[index] for index in mask]
            out.append(poly_path([(chosen[0][0], self.Y(base))] + chosen
                                 + [(chosen[-1][0], self.Y(base))]) + "Z")
        return out

    def band_frames(self, lows, highs, tol: float = 0.25) -> list[str]:
        plow = [self.project(f) for f in lows]
        phigh = [self.project(f) for f in highs]
        mask = common_mask(plow + phigh, tol)
        return [poly_path([lo[index] for index in mask]
                          + [hi[index] for index in reversed(mask)]) + "Z"
                for lo, hi in zip(plow, phigh)]

    def axes(self, scene: Scene, x_label: str = "", y_label: str = "",
             origin_y: float | None = None, y_tex: str = "") -> None:
        """A left vertical axis and a horizontal axis at ``origin_y``."""
        base = self.ymin if origin_y is None else origin_y
        scene.line(self.x0, self.Y(base), self.right, self.Y(base),
                   stroke="muted", sw=SW_AXIS)
        scene.line(self.x0, self.y0, self.x0, self.bottom,
                   stroke="muted", sw=SW_AXIS)
        if x_label:
            scene.math(self.right + 10, self.Y(base) + 4, x_label, anchor="start",
                       fill="muted")
        if y_tex:
            scene.math(self.x0 - 4, self.y0 - 5, y_tex, t=y_label or y_tex,
                       anchor="start", fill="muted")
        elif y_label:
            scene.text(self.x0 - 4, self.y0 - 5, y_label, anchor="start",
                       fill="muted")


# --- animation ---------------------------------------------------------------

EASE = "0.42 0 0.58 1"


def anim(attr: str, frames: list[str], dur: str = DUR_MED, times=None,
         kind: str = "animate", transform: str = "", ease: bool = True) -> dict:
    """One SMIL animation over precomputed frames.

    Eased between frames by default, which suits a sequence of states. Motion
    at a constant speed, a wave travelling at speed one for instance, must set
    ``ease=False``, because easing it would misstate the speed.
    """
    count = len(frames)
    if count < 2:
        raise SystemExit(f"animation of {attr} needs at least two frames")
    if times is None:
        times = [k / (count - 1) for k in range(count)]
    if len(times) != count:
        raise SystemExit(f"animation of {attr}: {count} frames, {len(times)} key times")
    out = {
        "kind": kind,
        "attributeName": attr,
        "values": ";".join(frames),
        "keyTimes": ";".join(q3(t) for t in times),
        "dur": dur,
        "calcMode": "linear",
    }
    if ease:
        out["calcMode"] = "spline"
        out["keySplines"] = ";".join([EASE] * (count - 1))
    if transform:
        out["type"] = transform
    return out


def loop(frames: list) -> list:
    """A frame list that returns to its first frame, so the loop is seamless."""
    return list(frames) + [frames[0]]


def discrete(attr: str, frames: list[str], dur: str = DUR_SLOW) -> dict:
    """Hold each computed state, with no invented intermediate degree or box."""
    out = anim(attr, frames + [frames[-1]], dur,
               times=[k / len(frames) for k in range(len(frames) + 1)], ease=False)
    out["calcMode"] = "discrete"
    return out


def fade_cycle(count: int, dip: float = 0.06) -> tuple[list[str], list[float]]:
    """Opacity frames that dip to zero at the wrap, hiding the jump back."""
    times = [k / count for k in range(count)]
    values = ["1"] * count
    times = times + [1.0 - dip, 1.0]
    values = values + ["0", "0"]
    return values, times


# --- level curves ------------------------------------------------------------

def contours(f, xmin: float, xmax: float, ymin: float, ymax: float,
             level: float, n: int = 96) -> list[list[tuple[float, float]]]:
    """Marching squares: the segments of ``{f = level}`` on a grid.

    A corner that sits exactly on the level, which happens all along the zero
    set of ``x^2 - y^2`` on a symmetric grid, counts as being just below it.
    Without a definite side a cell reports the same corner twice and the chain
    picks up duplicated points. An ambiguous cell, where the two diagonal pairs of
    corners disagree, is resolved by the sign at the cell centre, so the two
    branches of a saddle stay separate instead of being joined by a spurious
    segment.
    """
    dx = (xmax - xmin) / n
    dy = (ymax - ymin) / n
    def value(x: float, y: float) -> float:
        height = f(x, y) - level
        return height if height != 0.0 else -1e-12

    values = [[value(xmin + i * dx, ymin + j * dy) for j in range(n + 1)]
              for i in range(n + 1)]
    segments: list[list[tuple[float, float]]] = []

    def crossing(pa, va, pb, vb):
        t = va / (va - vb)
        return (pa[0] + t * (pb[0] - pa[0]), pa[1] + t * (pb[1] - pa[1]))

    for i in range(n):
        for j in range(n):
            corners = [
                ((xmin + i * dx, ymin + j * dy), values[i][j]),
                ((xmin + (i + 1) * dx, ymin + j * dy), values[i + 1][j]),
                ((xmin + (i + 1) * dx, ymin + (j + 1) * dy), values[i + 1][j + 1]),
                ((xmin + i * dx, ymin + (j + 1) * dy), values[i][j + 1]),
            ]
            hits: list[tuple[float, float] | None] = []
            for k in range(4):
                (pa, va), (pb, vb) = corners[k], corners[(k + 1) % 4]
                if (va < 0.0) != (vb < 0.0):
                    hits.append(crossing(pa, va, pb, vb))
                else:
                    hits.append(None)
            crossed = [k for k in range(4) if hits[k] is not None]
            if len(crossed) == 2:
                pairs = [(crossed[0], crossed[1])]
            elif len(crossed) == 4:
                centre = f(xmin + (i + 0.5) * dx, ymin + (j + 0.5) * dy) - level
                if (centre < 0.0) == (values[i][j] < 0.0):
                    pairs = [(0, 1), (2, 3)]
                else:
                    pairs = [(3, 0), (1, 2)]
            else:
                pairs = []
            for ka, kb in pairs:
                segments.append([hits[ka], hits[kb]])
    return segments


# --- numerics used by several figures ---------------------------------------

def bump(x: float) -> float:
    """The standard compactly supported bump, scaled to peak at 1."""
    if abs(x) >= 1.0:
        return 0.0
    return math.exp(1.0 - 1.0 / (1.0 - x * x))


def mollifier(x: float, eps: float) -> float:
    """The mollifier ``eta_eps`` of unit mass, from the standard bump."""
    if abs(x) >= eps:
        return 0.0
    return bump(x / eps) / (eps * BUMP_MASS)


def _bump_mass(n: int = 4000) -> float:
    total = 0.0
    for k in range(n + 1):
        x = -1.0 + 2.0 * k / n
        weight = 0.5 if k in (0, n) else 1.0
        total += weight * bump(x)
    return total * (2.0 / n)


BUMP_MASS = _bump_mass()


def convolve(f, x: float, eps: float, n: int = 240) -> float:
    """``(f * eta_eps)(x)`` by the trapezoid rule over the mollifier support."""
    total = 0.0
    for k in range(n + 1):
        y = -eps + 2.0 * eps * k / n
        weight = 0.5 if k in (0, n) else 1.0
        total += weight * f(x - y) * mollifier(y, eps)
    return total * (2.0 * eps / n)


def heat_kernel(x: float, t: float) -> float:
    return math.exp(-x * x / (4.0 * t)) / math.sqrt(4.0 * math.pi * t)


def integrate(f, a: float, b: float, n: int = 2000) -> float:
    total = 0.0
    for k in range(n + 1):
        x = a + (b - a) * k / n
        weight = 0.5 if k in (0, n) else 1.0
        total += weight * f(x)
    return total * ((b - a) / n)


def integrate_mid(f, a: float, b: float, n: int = 400) -> float:
    """The midpoint rule, which never samples an endpoint.

    Splitting first at known jumps avoids assigning endpoint values to a
    discontinuous integrand. Smooth pieces are still integrated numerically;
    the displayed pairings are checks, not proofs of integral identities.
    """
    h = (b - a) / n
    return h * sum(f(a + (k + 0.5) * h) for k in range(n))


def integrate_pieces(f, breaks, n: int = 400) -> float:
    """The midpoint rule on each piece between consecutive breakpoints."""
    return sum(integrate_mid(f, breaks[k], breaks[k + 1], n)
               for k in range(len(breaks) - 1))

# --- diagram furniture -------------------------------------------------------

def arrow_head(x: float, y: float, dx: float, dy: float, size: float = 7.0) -> str:
    """A filled triangle at ``(x, y)`` pointing along ``(dx, dy)``."""
    norm = math.hypot(dx, dy)
    if norm == 0.0:
        raise SystemExit("arrow head needs a direction")
    ux, uy = dx / norm, dy / norm
    px, py = -uy, ux
    bx, by = x - ux * size, y - uy * size
    half = size * 0.38
    return (f"M{q2(x)} {q2(y)}L{q2(bx + px * half)} {q2(by + py * half)}"
            f"L{q2(bx - px * half)} {q2(by - py * half)}Z")


def draw_arrow(scene: Scene, points: list[tuple[float, float]], role: str = "muted",
               dash: str = "", label: str = "", label_at: str = "above",
               sw: float = SW_CURVE2, label_tex: str = "") -> None:
    """An elbow arrow through ``points``, with the head at the last point."""
    trimmed = list(points)
    (hx, hy) = trimmed[-1]
    (px, py) = trimmed[-2]
    dx, dy = hx - px, hy - py
    norm = math.hypot(dx, dy)
    shrink = min(6.0, norm * 0.5)
    trimmed[-1] = (hx - dx / norm * shrink, hy - dy / norm * shrink)
    d = "".join(f"{'M' if k == 0 else 'L'}{q2(x)} {q2(y)}"
                for k, (x, y) in enumerate(trimmed))
    scene.path(d, stroke=role, sw=sw, dash=dash)
    scene.area(arrow_head(hx, hy, dx, dy), fill=role)
    if label:
        def text(x, y, body, **kw):
            if label_tex:
                return scene.math(x, y, label_tex, t=body, **kw)
            return scene.text(x, y, body, **kw)
        mid = len(trimmed) // 2
        mx = (trimmed[mid - 1][0] + trimmed[mid][0]) / 2
        my = (trimmed[mid - 1][1] + trimmed[mid][1]) / 2
        if label_at == "above":
            text(mx, my - 6, label, fill="muted", size=9.5, halo=True)
        elif label_at == "below":
            text(mx, my + 13, label, fill="muted", size=9.5, halo=True)
        elif label_at == "right":
            text(mx + 6, my + 3, label, fill="muted", size=9.5, anchor="start",
                       halo=True)
        else:
            text(mx - 6, my + 3, label, fill="muted", size=9.5, anchor="end",
                       halo=True)


def draw_box(scene: Scene, x: float, y: float, w: float, h: float, head: str,
             note: str = "", role: str = "ink", dash: str = "",
             fill: str = "", note_tex: str = "") -> tuple[float, float]:
    """A labelled box; returns its centre."""
    scene.rect(x, y, w, h, stroke=role, fill=fill, sw=SW_CURVE2, rx="5", dash=dash)
    cx = x + w / 2
    if note:
        scene.text(cx, y + h / 2 - 3, head, fill=role, size=FS_LABEL, weight="600")
        if note_tex:
            scene.math(cx, y + h / 2 + 12, note_tex, t=note, fill="muted", size=9.5)
        else:
            scene.text(cx, y + h / 2 + 12, note, fill="muted", size=9.5)
    else:
        scene.text(cx, y + h / 2 + 4, head, fill=role, size=FS_LABEL, weight="600")
    return (cx, y + h / 2)


# --- phased animation --------------------------------------------------------
#
# A phased animation walks through computed states, holds the last one, then
# returns to the first while the mark is invisible, so a loop that is not a
# palindrome still has no visible jump. Frame 0 is always the most informative
# state, because that is what a reader who asked for reduced motion sees: the
# static attribute of every animated mark is its frame 0, and the reduced-motion
# script pauses the SVG at time zero.

WRAP_HOLD = 0.86
WRAP_JUMP = 0.94


def phase_times(count: int) -> list[float]:
    return [WRAP_HOLD * k / (count - 1) for k in range(count)] + [0.9, WRAP_JUMP, 1.0]


def phased(attr: str, frames: list[str], dur: str = DUR_SLOW, kind: str = "animate",
           transform: str = "") -> dict:
    values = list(frames) + [frames[-1], frames[0], frames[0]]
    return anim(attr, values, dur=dur, times=phase_times(len(frames)), kind=kind,
                transform=transform)


def phase_fade(dur: str = DUR_SLOW) -> dict:
    """Opacity that is zero exactly while a phased attribute jumps back."""
    return anim("opacity", ["1", "1", "0", "0", "1"], dur=dur,
                times=[0.0, 0.88, 0.915, 0.965, 1.0])


def phase_only(index: int, count: int, dur: str = DUR_SLOW) -> dict:
    """Opacity that is one only during phase ``index``, for a per-phase label."""
    values = ["1" if k == index else "0" for k in range(count)]
    values += ["1" if index == count - 1 else "0", "0", "1" if index == 0 else "0"]
    return anim("opacity", values, dur=dur, times=phase_times(count))


def slot(index: int, count: int, dur: str = DUR_SLOW) -> dict:
    """Show exactly one state and its label, including at slot boundaries."""
    return discrete("opacity", ["1" if k == index else "0" for k in range(count)], dur)


def poly_path(points) -> str:
    """A point list as SVG path data."""
    return "".join(f"{'M' if k == 0 else 'L'}{q2(x)} {q2(y)}"
                   for k, (x, y) in enumerate(points))


def thin_indices(points, tol: float = 0.25) -> list[int]:
    """Which points of a projected polyline a reader can actually see.

    Douglas and Peucker's rule: keep whichever point sits furthest from the
    chord, recurse on the two halves, and stop once nothing is further than
    ``tol`` user units from the chord it would be replaced by. Measuring
    against the original points rather than against the survivors is what
    keeps a convex curve, a pole for instance, from being cut into chords
    whose accumulated error nobody checked. A chord longer than 60 units is
    halved even when it is accurate, so a nearly straight run keeps enough
    points to morph against a curved frame of the same animation.
    """
    count = len(points)
    if count <= 2:
        return list(range(count))
    keep = [False] * count
    keep[0] = keep[count - 1] = True
    stack = [(0, count - 1)]
    while stack:
        first, last = stack.pop()
        if last <= first + 1:
            continue
        ax, ay = points[first]
        bx, by = points[last]
        dx, dy = bx - ax, by - ay
        norm = math.hypot(dx, dy)
        worst, at = -1.0, first
        for index in range(first + 1, last):
            px, py = points[index]
            if norm == 0.0:
                offset = math.hypot(px - ax, py - ay)
            else:
                offset = abs(dx * (py - ay) - dy * (px - ax)) / norm
            if offset > worst:
                worst, at = offset, index
        if worst <= tol:
            if norm <= 60.0:
                continue
            at = (first + last) // 2
        keep[at] = True
        stack.append((first, at))
        stack.append((at, last))
    return [index for index in range(count) if keep[index]]


def thin(points, tol: float = 0.25) -> list[tuple[float, float]]:
    return [points[index] for index in thin_indices(points, tol)]


def common_mask(projected, tol: float = 0.25) -> list[int]:
    """One index mask for a family of frames sampled at the same points.

    A morphing path has to have the same number of points in every frame, so
    the frames of an animation are thinned together: a point survives if any
    frame needs it.
    """
    keep: set[int] = set()
    for points in projected:
        keep.update(thin_indices(points, tol))
    return sorted(keep)


def dedupe(points, tol: float = 0.02) -> list[tuple[float, float]]:
    """Drop points that land on their predecessor once projected."""
    out: list[tuple[float, float]] = []
    for point in points:
        if out and math.hypot(point[0] - out[-1][0], point[1] - out[-1][1]) <= tol:
            continue
        out.append(point)
    return out


def chain_path(frame: Frame, chains) -> str:
    """Polylines in data coordinates, projected, deduplicated and thinned."""
    parts = []
    for chain in chains:
        points = dedupe(frame.project(chain))
        if len(points) >= 2:
            parts.append(poly_path(thin(points)))
    return "".join(parts)


def clip_chains(chains, keep):
    """Cut polylines down to the part of the plane that ``keep`` accepts.

    The level curves of a function on a disc are traced on the enclosing
    square, so the arcs outside the disc have to go, and a chain that leaves
    the disc and comes back has to become two chains.
    """
    out = []
    for chain in chains:
        current: list[tuple[float, float]] = []
        for point in chain:
            if keep(point[0], point[1]):
                current.append(point)
            else:
                if len(current) >= 2:
                    out.append(current)
                current = []
        if len(current) >= 2:
            out.append(current)
    return out


def seg_path(frame: Frame, segments) -> str:
    """A computed level set: segments chained into polylines, then thinned."""
    return chain_path(frame, join_segments(segments))


def join_segments(segments) -> list[list[tuple[float, float]]]:
    """Chain marching-squares segments that share an endpoint.

    Neighbouring cells compute a shared crossing from the same two corner
    values, so their endpoints agree to the last bits. Rounding the key to nine
    decimals, far below anything the drawing can show, also joins the staircase
    of cell diagonals that a corner sitting on the level produces.
    """

    def key(point: tuple[float, float]) -> tuple[float, float]:
        return (round(point[0], 9), round(point[1], 9))

    ends: dict[tuple[float, float], list[int]] = {}
    for index, segment in enumerate(segments):
        for point in segment:
            ends.setdefault(key(point), []).append(index)
    used = [False] * len(segments)
    chains = []
    for index in range(len(segments)):
        if used[index]:
            continue
        used[index] = True
        chain = list(segments[index])
        for direction in (0, 1):
            while True:
                tip = chain[-1] if direction == 0 else chain[0]
                nxt = None
                for candidate in ends.get(key(tip), ()):
                    if not used[candidate]:
                        nxt = candidate
                        break
                if nxt is None:
                    break
                used[nxt] = True
                pair = segments[nxt]
                other = pair[1] if key(pair[0]) == key(tip) else pair[0]
                if direction == 0:
                    chain.append(other)
                else:
                    chain.insert(0, other)
        chains.append(chain)
    return chains


# --- the three classical types ----------------------------------------------

def fig_pde_zoo() -> Scene:
    """Elliptic, parabolic and hyperbolic behaviour side by side."""
    scene = Scene(
        "pde-zoo",
        "The three classical types",
        r"Left: the harmonic saddle \(u=x^2-y^2\), with its computed level curves and crossing "
        r"zero set, is a steady spatial balance. Middle: \(u(x,t)=(4\pi t)^{-1/2}e^{-x^2/(4t)}\) "
        r"spreads and flattens. The animation holds eight computed Gaussian snapshots; the faint "
        r"curves retain the later times, and the plotted window omits the tails. Right: "
        r"\(u(x,t)=\sin(x-t)\) carries one shape to the right at speed one. These explicit "
        r"solutions isolate equilibrium, diffusion, and propagation. Nonlinear equations and "
        r"coupled systems can combine these behaviours.",
        "Three panels. A saddle-shaped harmonic field with hyperbolic level "
        "curves and a zero set of two crossing diagonals; a Gaussian profile "
        "spreading and flattening as time increases; a sine wave travelling to "
        "the right at constant speed without changing shape.",
        width=640.0, height=268.0)

    # Elliptic: the level curves of a genuine harmonic function.
    a = Frame(24, 52, 170, 170, -1.0, 1.0, -1.0, 1.0)
    scene.math_title(24, 34, r"\Delta u=0", t='Δu = 0')
    scene.rect(a.x0, a.y0, a.w, a.h, stroke="muted", fill="", sw=SW_AXIS)
    saddle = lambda x, y: x * x - y * y
    for level in (-0.8, -0.5, -0.2, 0.2, 0.5, 0.8):
        scene.path(seg_path(a, contours(saddle, -1.0, 1.0, -1.0, 1.0, level, 88)),
                   stroke="muted", sw=SW_CURVE2, sop=0.6)
    scene.path(seg_path(a, contours(saddle, -1.0, 1.0, -1.0, 1.0, 0.0, 88)),
               stroke="accent", sw=SW_CURVE)
    scene.math(a.X(0.58), a.Y(0.02), r"u > 0", fill="muted", size=9.5, halo=True)
    scene.math(a.X(-0.02), a.Y(0.58), r"u < 0", fill="muted", size=9.5, halo=True)
    scene.text(a.x0 + a.w / 2, 240, "elliptic: steady", fill="ink", size=FS_LABEL)
    scene.math(a.x0 + a.w / 2, 256, r"u=x^2-y^2", t='u = x² − y², zero on the diagonals',
               fill="muted", size=9.5)

    # Parabolic: eight Gaussian snapshots; the plotted window omits the tails.
    b = Frame(234, 52, 190, 170, -2.5, 2.5, 0.0, 1.5)
    scene.math_title(234, 34, r"u_t=u_{xx}", t='uₜ = uₓₓ')
    scene.line(b.x0, b.Y(0.0), b.right, b.Y(0.0), stroke="muted", sw=SW_AXIS)
    times = [0.05 * (0.35 / 0.05) ** (k / 7.0) for k in range(8)]
    profiles = [[(x, heat_kernel(x, t)) for x in
                 (-2.5 + 5.0 * i / 100.0 for i in range(101))] for t in times]
    fills = b.fill_frames(profiles, 0.0)
    curves = b.curve_frames(profiles)
    for ghost in curves[1:]:
        scene.path(ghost, stroke="muted", sw=SW_AXIS, sop=0.5)
    scene.area(fills[0], fill="band", anim=[discrete("d", fills)])
    scene.path(curves[0], stroke="accent", sw=SW_CURVE,
               anim=[discrete("d", curves)])
    scene.text(b.x0 + b.w / 2, 240, "parabolic: diffusing", fill="ink", size=FS_LABEL)
    scene.math(b.x0 + b.w / 2, 256,
               r"u=(4\pi t)^{-1/2}e^{-x^2/(4t)}",
               t="u = Gaussian heat kernel", fill="muted", size=9.5)

    # Hyperbolic: one shape, moved. The translation is the exact period, so the
    # loop closes, and it is linear in time because the speed is one.
    # The window runs from one zero of the sine to the next but one, so the
    # curve begins and ends on the axis instead of being cut mid-descent.
    c = Frame(446, 52, 170, 170, -math.pi, math.pi, -1.4, 1.4)
    scene.math_title(446, 34, r"u_{tt}=u_{xx}", t='uₜₜ = uₓₓ')
    window = scene.clip("wave", c.x0, c.y0, c.w, c.h)
    scene.line(c.x0, c.Y(0.0), c.right, c.Y(0.0), stroke="muted", sw=SW_AXIS)
    period = 2.0 * math.pi
    span = period * c.w / (c.xmax - c.xmin)
    wave = [(-3.0 * math.pi + 4.0 * math.pi * k / 320.0, 0.0) for k in range(321)]
    wave = [(x, math.sin(x)) for x, _ in wave]
    # The drawn sine is two periods wide and the window is one, so there is
    # always more shape to the left of the panel to enter it. Translating the
    # drawing right by one period is what carries sin(x) to sin(x − t) for a
    # whole period of t, and it ends where it started, so the loop is seamless.
    # The static value is no translation, which is the frame u = sin x.
    scene.path(c.curve(wave), stroke="accent", sw=SW_CURVE, clip=window,
               anim=[anim("transform", ["0 0", f"{q2(span)} 0"], dur="6s",
                          kind="animateTransform", transform="translate", ease=False)])
    scene.text(c.x0 + c.w / 2, 240, "hyperbolic: travelling", fill="ink", size=FS_LABEL)
    scene.math(c.x0 + c.w / 2, 256, r"u=\sin(x-t)", t='u = sin(x − t)', fill="muted", size=9.5)
    for frame in (a, b, c):
        base = frame.bottom if frame is a else frame.Y(0)
        scene.math(frame.right + 7, base + 4, r"x", fill="muted", size=9.5)
    scene.math(a.x0 - 8, a.y0 + 4, r"y", fill="muted", size=9.5)
    for frame in (b, c):
        scene.math(frame.x0 + 4, frame.y0 + 12, r"u", fill="muted", size=9.5)
    return scene


# --- the trust boundary ------------------------------------------------------

def fig_cega_pipeline() -> Scene:
    """What CEGA trusts and what it does not."""
    scene = Scene(
        "cega-pipeline",
        "Where the trust boundary runs",
        r"The planner proposes a rewrite, interval, or jet. A closing tactic uses a soundness "
        r"theorem and its hypotheses to turn that candidate into a proof of the original goal. "
        r"Lean's kernel checks the resulting declaration; a failed check leaves the goal "
        r"unchanged. The certificate shown here is ApproxOn: \(\lVert "
        r"f(x)-g(x)\rVert\le\varepsilon\) for every \(x\in\Omega\). At \(\varepsilon=0\), this "
        r"gives pointwise equality on \(\Omega\). Supplied certificates retain their own "
        r"assumptions and axioms.",
        "A diagram in two bands separated by one horizontal line. Above the "
        "line, an untrusted planner produces a candidate. Below the line, the "
        "goal, Lean's kernel checking the proof, a soundness theorem proved "
        "once, and the resulting certificate; a failed check returns to a box "
        "saying the tactic fails and the goal is unchanged.",
        width=640.0, height=302.0)
    warn_note = "a candidate still needs a proof"
    scene.text(624, 30, warn_note, anchor="end", fill="warn", size=9.5)
    planner = draw_box(scene, 24, 40, 226, 56, "Planner",
                       "search, ranking, heuristics", role="warn", dash=DASH)
    candidate = draw_box(scene, 300, 40, 170, 56, "Candidate",
                         "a rewrite, an interval, a jet", role="warn", dash=DASH)
    draw_arrow(scene, [(250, planner[1]), (300, candidate[1])], role="warn")

    scene.line(16, 118, 624, 118, stroke="warn", sw=2.2)
    scene.text(24, 112, "trust boundary", anchor="start", fill="warn", size=9.5)

    goal = draw_box(scene, 24, 140, 226, 56, "Goal", "the statement we wanted")
    kernel = draw_box(scene, 300, 140, 170, 56, "Lean's kernel",
                      "checks the proof")
    sound = draw_box(scene, 500, 140, 124, 56, "Soundness", "proved once")
    draw_arrow(scene, [(137, 140), (137, 96)], role="ink")
    draw_arrow(scene, [(385, 96), (385, 140)], role="ink")
    draw_arrow(scene, [(500, sound[1]), (470, kernel[1])], role="ink")

    draw_box(scene, 300, 224, 324, 50, "Certificate",
             "∀ x ∈ Ω, ‖f(x) − g(x)‖ ≤ ε", role="accent",
             note_tex=r"\forall x\in\Omega,\ \lVert f(x)-g(x)\rVert\le\varepsilon")
    draw_arrow(scene, [(385, 196), (385, 224)], role="accent")
    draw_box(scene, 24, 224, 226, 50, "Rejected",
             "the goal is unchanged", role="muted", dash=DASH)
    draw_arrow(scene, [(330, 196), (330, 210), (137, 210), (137, 224)],
               role="muted", dash=DASH)
    scene.text(16, 292, "soundness connects the computed object to the original goal",
               anchor="start", fill="muted", size=9.5)
    _ = goal, sound
    return scene


# --- the error budget --------------------------------------------------------

def fig_certificate_budget() -> Scene:
    """A tube of radius epsilon around an approximation, closing to zero."""
    frame = Frame(64, 54, 536, 172, 0.0, 1.0, 0.0, 2.95)
    degrees = [1, 2, 3]
    xs = [i / 80.0 for i in range(81)]

    def taylor(degree: int):
        coeffs = [1.0 / math.factorial(k) for k in range(degree + 1)]
        return lambda x: sum(c * x ** k for k, c in enumerate(coeffs))

    approximations = [taylor(d) for d in degrees] + [math.exp]
    # On [0,1], exp − p_d is nonnegative and increasing: its derivative
    # is the nonnegative tail exp − p_(d−1). The supremum is at x=1.
    budgets = [math.e - p(1.0) for p in approximations[:-1]] + [0.0]
    names = [f"degree {d}" for d in degrees] + ["exact"]

    scene = Scene(
        "certificate-budget",
        "The error budget, and the case where it closes",
        r"The solid curve is \(e^x\); the dashed curve is its Taylor polynomial \(p\) at zero, "
        r"of degree one, two, or three. The band is \(p\pm\varepsilon\) on \([0,1]\). The error "
        r"\(e^x-p(x)\) is nonnegative and increasing there, so its maximum is "
        r"\(\varepsilon=e-p(1)\). The animation holds each degree before replacing \(p\) by the "
        r"exponential itself, when \(\varepsilon=0\). This illustrates the uniform inequality "
        r"carried by ApproxOn. The plotted coordinates and decimal labels are numerical "
        r"illustrations; a CAS certificate must prove the inequality throughout the interval.",
        "A plot of the exponential on the unit interval with a Taylor polynomial "
        "inside a shaded tube of half-width epsilon. The tube shrinks from about "
        "0.718 to 0.218 to 0.052 as the degree rises, and closes to zero width when the "
        "approximation is replaced by the function itself.",
        width=640.0, height=272.0)
    frame.axes(scene, x_label="x", y_label="value", origin_y=0.0)
    for tick in (0.0, 0.5, 1.0):
        scene.line(frame.X(tick), frame.Y(0.0), frame.X(tick), frame.Y(0.0) + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(frame.X(tick), frame.Y(0.0) + 16, q2(tick), size=9.5)
    for tick in (1.0, 2.0):
        scene.line(frame.x0 - 4, frame.Y(tick), frame.x0, frame.Y(tick),
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(frame.x0 - 8, frame.Y(tick) + 3.5, q2(tick), anchor="end",
                         size=9.5)

    lows = [[(x, p(x) - eps) for x in xs] for p, eps in zip(approximations, budgets)]
    highs = [[(x, p(x) + eps) for x in xs] for p, eps in zip(approximations, budgets)]
    tubes = frame.band_frames(lows, highs)
    curves = frame.curve_frames([[(x, p(x)) for x in xs] for p in approximations])
    scene.area(tubes[0], fill="band",
               anim=[discrete("d", tubes)])
    scene.path(curves[0], stroke="accent2", sw=SW_CURVE2, dash=DASH,
               anim=[discrete("d", curves)])
    scene.path(frame.curve([(x, math.exp(x)) for x in xs]), stroke="accent", sw=SW_CURVE)
    scene.math(frame.X(0.87), frame.Y(math.exp(0.87)) - 9, r"e^x", t='exp', fill="accent",
               size=FS_LABEL, halo=True)
    for index, (name, eps) in enumerate(zip(names, budgets)):
        text = f"{name}: ε ≈ {q3(eps)}" if eps > 0 else f"{name}: ε = 0"
        formula = (rf"\text{{{name}}}:\ \varepsilon\approx{q3(eps)}"
                   if eps > 0 else rf"\text{{{name}}}:\ \varepsilon=0")
        scene.math(frame.x0 + 8, frame.y0 + 20, formula, t=text, anchor="start", fill="ink",
                   size=FS_LABEL, halo=True, op=1.0 if index == 0 else 0.0,
                   anim=[slot(index, len(names))])
    scene.math(frame.right, frame.y0 - 14,
               r"\lVert\exp-p\rVert_{L^\infty([0,1])}\le\varepsilon", t='‖exp − p‖ ≤ ε on [0, 1]', anchor="end",
               fill="muted", size=FS_LABEL)
    return scene


# --- the heat equation's dependence on its data ------------------------------

def fig_heat_stability() -> Scene:
    """Exact finite sine modes, with the general energy estimate kept separate."""
    delta, mode, end = 0.2, 4, 0.4
    times = (0.0, 0.025, 0.05, 0.1, 0.2, end)
    xs = [math.pi * k / 240 for k in range(241)]

    def base(x: float, t: float) -> float:
        return math.exp(-t) * math.sin(x)

    def difference(x: float, t: float) -> float:
        return delta * math.exp(-mode * mode * t) * math.sin(mode * x)

    # Orthogonality gives this norm exactly. The quadrature is a regression
    # check on the sampled family, not a proof about arbitrary heat solutions.
    initial_norm = delta * math.sqrt(math.pi / 2)
    for t in times:
        squared = integrate_mid(lambda x: difference(x, t) ** 2, 0, math.pi)
        exact = initial_norm ** 2 * math.exp(-2 * mode * mode * t)
        if abs(squared - exact) > 1e-10:
            raise SystemExit("heat-stability: the illustrated mode norm is wrong")

    scene = Scene(
        "heat-stability",
        "A small change in the data stays small",
        r"On the rod \(0<x<\pi\) with zero endpoint temperatures, compare the exact "
        r"solutions \(u_0(t,x)=e^{-t}\sin x\) and "
        r"\(u_\delta(t,x)=u_0(t,x)+\delta e^{-16t}\sin(4x)\), with \(\delta=0.2\). "
        r"Left: the band between them disappears quickly as time advances from "
        r"\(0\) to \(0.4\); the faint curve retains the perturbed initial profile. "
        r"Right: their relative \(L^2(0,\pi)\) difference is exactly "
        r"\(\|u_\delta(t)-u_0(t)\|_2/\|u_\delta(0)-u_0(0)\|_2=e^{-16t}\). "
        r"The slower curve \(e^{-t}\) shows the same ratio for a perturbation "
        r"\(\delta\sin x\) instead. Both stay below one. These finite sums construct "
        r"solutions for the illustrated data; the general contraction estimate comes "
        r"from the heat energy identity for solutions in an appropriate energy class. "
        r"That estimate gives continuous dependence, and uniqueness when the initial "
        r"difference is zero. The sampled picture illustrates these facts without "
        r"certifying the general theorem.",
        "Two exact heat solutions on a rod differ initially by a small fourth sine "
        "mode. The animated perturbed curve quickly approaches the base solution. "
        "A second panel plots the relative error: the fourth-mode error decays as "
        "exp(-16t), faster than the first-mode comparison exp(-t). A horizontal "
        "line at one marks the initial error. The time label and marker advance "
        "together; the initial state is the static frame.",
        width=640, height=398)
    scene.panel_title(28, 34, "two nearby initial temperatures")
    scene.math(28, 58, r"\delta=0.2,\quad u_0(0,x)=\sin x",
               t="delta = 0.2; base initial data sin(x)", anchor="start", size=12)
    scene.panel_title(348, 34, "relative size of the difference")
    scene.math(348, 58, r"\lVert u_\delta(t)-u_0(t)\rVert_2/"
               r"\lVert u_\delta(0)-u_0(0)\rVert_2",
               t="L2 error divided by its initial L2 error", anchor="start", size=11)
    left = Frame(60, 90, 240, 180, 0, math.pi, -0.1, 1.25)
    right = Frame(382, 90, 224, 180, 0, end, 0, 1.15)
    left.axes(scene, x_label="x", origin_y=0)
    right.axes(scene, x_label="t", origin_y=0)
    for x, name in ((0, "0"), (math.pi / 2, r"\pi/2"), (math.pi, r"\pi")):
        scene.tick_label(left.X(x), left.bottom + 19, name, size=11)
    for t in (0, 0.2, end):
        scene.tick_label(right.X(t), right.bottom + 19, q2(t), size=11)
    for frame in (left, right):
        for value in (0.5, 1):
            scene.tick_label(frame.x0 - 10, frame.Y(value) + 4, q2(value),
                             anchor="end", size=11)
    base_profiles = [[(x, base(x, t)) for x in xs] for t in times]
    perturbed = [[(x, base(x, t) + difference(x, t)) for x in xs] for t in times]
    bands = left.band_frames(base_profiles, perturbed)
    base_curves = left.curve_frames(base_profiles)
    curves = left.curve_frames(perturbed)
    scene.path(curves[0], stroke="muted", sw=SW_AXIS, sop=0.5)
    scene.area(bands[0], fill="band", anim=[discrete("d", bands)])
    scene.path(base_curves[0], stroke="accent2", dash=DASH,
               anim=[discrete("d", base_curves)])
    scene.path(curves[0], stroke="accent", anim=[discrete("d", curves)])
    for index, t in enumerate(times):
        scene.math(60, 78, rf"t={q3(t)}", anchor="start", size=11,
                   op=1 if index == 0 else 0, anim=[slot(index, len(times))])
    scene.line(right.x0, right.Y(1), right.right, right.Y(1),
               stroke="muted", sw=SW_AXIS, dash=DASH)
    ts = [end * k / 200 for k in range(201)]
    for rate, role in ((1, "muted"), (16, "accent")):
        scene.path(right.curve([(t, math.exp(-rate * t)) for t in ts]),
                   stroke=role, sw=SW_CURVE)
    scene.math(right.X(0.27), right.Y(math.exp(-0.27)) - 11,
               r"e^{-t}\quad(k=1)", fill="muted", size=11, halo=True)
    scene.math(right.X(0.12) + 5, right.Y(math.exp(-16 * 0.12)) - 10,
               r"e^{-16t}\quad(k=4)", anchor="start", fill="accent", size=11,
               halo=True)
    scene.circle(right.X(0), right.Y(1), 3.5, fill="accent",
                 anim=[discrete("cx", [q2(right.X(t)) for t in times]),
                       discrete("cy", [q2(right.Y(math.exp(-16 * t))) for t in times])])
    scene.line(60, 311, 84, 311, stroke="accent2", dash=DASH)
    scene.math(90, 315, r"u_0", anchor="start", fill="accent2", size=12)
    scene.line(151, 311, 175, 311, stroke="accent")
    scene.math(181, 315, r"u_\delta", anchor="start", fill="accent", size=12)
    scene.text(382, 315, "finer oscillations decay faster", anchor="start",
               fill="muted", size=11)
    scene.math(320, 347, r"u_\delta-u_0=\delta e^{-16t}\sin(4x)",
               t="exact illustrated difference: delta exp(-16t) sin(4x)", size=13)
    scene.math(320, 380, r"\text{energy estimate: }\lVert u(t)-v(t)\rVert_2"
               r"\le\lVert u(0)-v(0)\rVert_2",
               t="general energy estimate: L2 differences cannot increase",
               fill="muted", size=12)
    return scene


# --- what "solves" means -----------------------------------------------------

def fig_formalization_routes() -> Scene:
    """Poisson solution concepts, with the hypotheses of the arrows visible."""
    scene = Scene(
        "formalization-routes",
        "Five formulations of Poisson's equation",
        r"For \(-\Delta u=f\), take a bounded smooth domain \(\Omega\) and continuous \(f\) on "
        r"its closure. A locally integrable distributional solution tests against \(\varphi\in "
        r"C_c^\infty(\Omega)\). If also \(u\in H^1(\Omega)\), density extends the identity to "
        r"every \(v\in H_0^1(\Omega)\). On a fixed trace class, the weak equation is the "
        r"first-variation condition for the convex energy \(E(u)=\tfrac12\int_\Omega|\nabla "
        r"u|^2-\int_\Omega fu\), hence is equivalent to minimizing it. Viscosity solutions use "
        r"smooth functions touching \(u\) from above and below. The dashed arrows need the "
        r"labelled regularity; weak solvability alone does not give \(C^2\). The separate "
        r"semigroup box concerns evolution \(u_t=Au\). PDEAtlas develops semigroup tools as well "
        r"as weak evolution on Gelfand triples.",
        "Five connected boxes for classical, distributional, viscosity, weak "
        "and variational Poisson solutions. Classical implies distributional "
        "by integration by parts; the reverse weak-to-classical arrow requires "
        "regularity. The distributional-to-weak arrow requires H¹ membership. "
        "Weak and variational solutions agree for the displayed convex energy "
        "with fixed trace. An unconnected box shows the separate semigroup "
        "evolution formula u(t)=S(t)u₀.",
        width=640.0, height=274.0)
    scene.math(24, 18, r"\text{Poisson: }-\Delta u=f\text{ on a bounded smooth }\Omega", t='Poisson: −Δu = f on a bounded smooth Ω', anchor="start",
               fill="muted", size=FS_LABEL)
    draw_box(scene, 24, 42, 160, 60, "classical", "u ∈ C², −Δu = f",
             note_tex=r"u\in C^2,\ -\Delta u=f")
    draw_box(scene, 244, 42, 160, 60, "distributional", "∫ u(−Δφ) = ∫ fφ",
             note_tex=r"\int u(-\Delta\varphi)=\int f\varphi")
    draw_box(scene, 464, 42, 160, 60, "semigroup evolution", "u(t) = S(t)u₀",
             role="muted", note_tex=r"u(t)=S(t)u_0")
    scene.math(544, 119, r"u_t=Au\text{; a separate equation}", t='uₜ = Au; a separate equation', fill="muted", size=9.5)
    draw_box(scene, 24, 162, 160, 60, "viscosity", "smooth tests touch u",
             note_tex=r"\text{smooth tests touch }u")
    draw_box(scene, 244, 162, 160, 60, "weak", "u ∈ H¹, ∫ ∇u·∇v = ∫ fv",
             note_tex=r"u\in H^1,\ \int\nabla u\cdot\nabla v=\int fv")
    draw_box(scene, 464, 162, 160, 60, "variational", "minimize E; fixed trace",
             note_tex=r"\text{minimize }E\text{; fixed trace}")
    draw_arrow(scene, [(184, 72), (244, 72)], role="ink", label="by parts")
    draw_arrow(scene, [(300, 102), (300, 162)], role="muted", dash=DASH,
               label="u ∈ H¹", label_tex=r"u\in H^1", label_at="left")
    draw_arrow(scene, [(348, 162), (348, 102)], role="ink", label="restrict tests",
               label_at="right")
    draw_arrow(scene, [(88, 102), (88, 162)], role="ink")
    draw_arrow(scene, [(124, 162), (124, 102)], role="muted", dash=DASH,
               label="u ∈ C²", label_tex=r"u\in C^2", label_at="right")
    draw_arrow(scene, [(464, 186), (404, 186)], role="ink",
               label="δE = 0", label_tex=r"\delta E=0")
    draw_arrow(scene, [(404, 208), (464, 208)], role="ink",
               label="E convex", label_tex=r"E\text{ convex}", label_at="below")
    draw_arrow(scene, [(258, 162), (186, 104)], role="muted", dash=DASH,
               label="regularity", label_at="left")
    scene.line(24, 248, 56, 248, stroke="ink", sw=SW_CURVE2)
    scene.text(62, 252, "under the stated setting", anchor="start", fill="muted", size=9.5)
    scene.line(270, 248, 302, 248, stroke="muted", sw=SW_CURVE2, dash=DASH)
    scene.text(308, 252, "also needs the labelled hypothesis", anchor="start",
               fill="muted", size=9.5)
    return scene


def num(value: float) -> str:
    """A number for a label, with a typographic minus sign."""
    return q3(value).replace("-", "−")


# --- smoothing a rough function ---------------------------------------------

def fig_stokes_circulation() -> Scene:
    """Add the oriented cell boundaries for v(x,y)=(-y,x) on [0,2]²."""
    def edge_integral(start, end):
        dx, dy = end[0] - start[0], end[1] - start[1]
        return integrate_mid(lambda t: -(start[1] + t * dy) * dx
                             + (start[0] + t * dx) * dy, 0.0, 1.0)

    def boundary(x, y, side):
        corners = [(x, y), (x + side, y), (x + side, y + side), (x, y + side)]
        return [edge_integral(corners[k], corners[(k + 1) % 4]) for k in range(4)]

    cells = [sum(boundary(i, j, 1)) for i in range(2) for j in range(2)]
    edges = boundary(0, 0, 2)
    shared = [((1, j), (1, j + 1)) for j in range(2)]
    shared += [((i, 1), (i + 1, 1)) for i in range(2)]
    if (any(abs(v - 2) > 1e-12 for v in cells)
            or abs(sum(cells) - sum(edges)) > 1e-12
            or any(abs(edge_integral(a, b) + edge_integral(b, a)) > 1e-12
                   for a, b in shared)):
        raise SystemExit("stokes-circulation: oriented integrals do not cancel")
    scene = Scene(
        "stokes-circulation",
        "Local curl, outer circulation",
        r"For \(v(x,y)=(-y,x)\), the scalar curl is \(2\). Every unit square contributes \(2\) "
        r"to circulation. A shared edge is traversed in opposite directions, so its two "
        r"integrals cancel. Only the outer boundary remains: \(0+4+4+0=8\). Arrows mark "
        r"integration directions; the circled dot is the normal pointing out of the page. The "
        r"fading pairs show cancellation in the sum. Rotating the field clockwise to \(F=(x,y)\) "
        r"gives the same value as outward flux, since \(\operatorname{div}F=2\). The affine edge "
        r"integrals illustrate Green–Stokes and the divergence theorem; a CAS proof of these "
        r"calculations must still be joined to the theorem's regularity and orientation "
        r"hypotheses.",
        "Two views of the square [0,2] by [0,2] for v(x,y)=(-y,x), whose "
        "curl is 2. On the left, four unit squares each carry the label 2 "
        "and counterclockwise arrows. Paired interior arrows point in opposite "
        "directions. On the right, the outer boundary is counterclockwise: "
        "bottom and left contribute 0, right and top contribute 4. "
        "Both totals are 8. A circled dot denotes the outward-from-page normal.",
        width=640.0, height=392.0)
    local = Frame(42, 88, 210, 210, 0, 2, 0, 2)
    outer = Frame(388, 88, 210, 210, 0, 2, 0, 2)
    fade = anim("opacity", ["1", "1", "0.12", "0.12", "1"],
                dur=DUR_MED, times=[0, 0.25, 0.5, 0.75, 1])

    def edge_arrow(frame, start, end, paired=False):
        """Orient an edge; separate shared copies slightly so both are visible."""
        (sx, sy), (ex, ey) = frame.project([start, end])
        role = "accent2" if paired else "accent"
        motion = [fade] if paired else []
        scene.path(poly_path([(sx, sy), (ex, ey)]), stroke=role,
                   sw=SW_CURVE, anim=motion)
        scene.area(arrow_head(ex, ey, ex - sx, ey - sy),
                   fill=role, anim=motion)

    scene.math(320, 22, r"v(x,y)=(-y,x)\qquad\operatorname{curl}v=2", t='v(x, y) = (−y, x)     curl v = 2', size=14)
    scene.panel_title(42, 53, "Four unit squares", size=14)
    scene.panel_title(388, 53, "One outer boundary", size=14)
    for frame in (local, outer):
        scene.rect(frame.x0, frame.y0, frame.w, frame.h,
                   stroke="accent", fill="band", sw=SW_CURVE)
        for value in (0, 1, 2):
            scene.tick_label(frame.X(value), frame.bottom + 19, str(value), size=12)
        scene.tick_label(frame.x0 - 14, frame.Y(2) + 4, "2", size=12)
        scene.math(frame.right + 18, frame.bottom + 4, r"x", size=12, fill="muted")
        scene.math(frame.x0, frame.y0 - 12, r"y", size=12, fill="muted")

    scene.line(local.X(1), local.Y(0), local.X(1), local.Y(2),
               stroke="muted", sw=SW_AXIS)
    scene.line(local.X(0), local.Y(1), local.X(2), local.Y(1),
               stroke="muted", sw=SW_AXIS)
    for i in range(2):
        for j in range(2):
            scene.math(local.X(i + 0.5), local.Y(j + 0.5) + 5,
                       q2(cells[2 * i + j]), t=q2(cells[2 * i + j]), size=19, weight="600")
            edge_arrow(local, (i + 0.25, j + (0.04 if j == 1 else 0)),
                       (i + 0.75, j + (0.04 if j == 1 else 0)), paired=j == 1)
            edge_arrow(local, (i + 0.75, j + 1 - (0.04 if j == 0 else 0)),
                       (i + 0.25, j + 1 - (0.04 if j == 0 else 0)), paired=j == 0)
            edge_arrow(local, (i + (0.04 if i == 1 else 0), j + 0.75),
                       (i + (0.04 if i == 1 else 0), j + 0.25), paired=i == 1)
            edge_arrow(local, (i + 1 - (0.04 if i == 0 else 0), j + 0.25),
                       (i + 1 - (0.04 if i == 0 else 0), j + 0.75), paired=i == 0)

    scene.text(320, 154, "shared edges", size=12, fill="muted")
    scene.text(320, 173, "cancel", size=12, fill="muted")
    draw_arrow(scene, [(272, 193), (366, 193)], role="ink")
    edge_arrow(outer, (0.5, 0), (1.5, 0))
    edge_arrow(outer, (2, 0.5), (2, 1.5))
    edge_arrow(outer, (1.5, 2), (0.5, 2))
    edge_arrow(outer, (0, 1.5), (0, 0.5))
    for (x, y), value in zip(((1, 0.24), (1.76, 1), (1, 1.76), (0.24, 1)), edges):
        scene.math(outer.X(x), outer.Y(y) + 5, q2(value), t=q2(value), size=16, weight="600")
    scene.circle(outer.X(1), outer.Y(1), 9, fill="surface", stroke="ink")
    scene.circle(outer.X(1), outer.Y(1), 2.5, fill="ink")
    scene.math(outer.X(1), outer.Y(1) + 29, r"\text{normal }+z", t='normal +z', size=12, fill="muted")
    scene.math(147, 344, r"\text{curl}\times\text{area}=2\times4=8", t='curl × area = 2 × 4 = 8', size=14, weight="600")
    scene.math(493, 344, r"\text{circulation}=0+4+4+0=8", t='circulation = 0 + 4 + 4 + 0 = 8', size=13, weight="600")
    scene.math(320, 377, r"F=(x,y):\quad\operatorname{div}F=2,\quad\text{outward flux}=8", t='Rotate to F = (x, y): div F = 2 and outward flux = 8.',
               size=12, fill="muted")
    return scene


def fig_mollification() -> Scene:
    """The standard mollifier, and a step function convolved with it."""
    widths = [0.5, 0.3, 0.18, 0.08]
    shown = [0.6, 0.35, 0.2]
    jumps = [-1.2, -0.2, 0.5, 1.4]

    def rough(x: float) -> float:
        """Four jumps and no derivative at any of them."""
        if x < -1.2:
            return 0.0
        if x < -0.2:
            return 1.0
        if x < 0.5:
            return 0.25
        if x <= 1.4:
            return 0.8
        return 0.0

    scene = Scene(
        "mollification",
        "Smoothing by convolution",
        r"Left: scale the compactly supported bump \(b(x)=\exp(1-1/(1-x^2))\) for \(|x|<1\), "
        r"zero outside, to radius \(\varepsilon\), then divide by its integral. Each kernel "
        r"\(\eta_\varepsilon\) has mass one: a narrower bump must be taller. Right: a function "
        r"with four jumps is convolved with that kernel at \(\varepsilon=0.5,0.3,0.18,0.08\). "
        r"Every plotted value is a numerical integral. The convolution is smooth for each "
        r"\(\varepsilon>0\) and remains between the smallest and largest input values. It agrees "
        r"exactly with the input wherever that input is constant on the whole interval of length "
        r"\(2\varepsilon\) seen by the kernel. Smoothness of the input alone would not imply "
        r"this agreement. The animation holds each computed width, while the first frame already "
        r"shows all three properties.",
        "Two panels. Left, three bell-shaped bumps of equal area and different "
        "widths, the narrowest being the tallest. Right, a step function with "
        "four jumps drawn dashed, and a smooth curve through it that tightens "
        "onto the steps as the mollifier width shrinks from 0.5 to 0.08.",
        width=640.0, height=286.0)

    a = Frame(56, 66, 208, 148, -0.75, 0.75, 0.0, 4.6)
    scene.panel_title(24, 44, "the mollifier")
    a.axes(scene, x_label="x", origin_y=0.0)
    xs_a = [-0.75 + 1.5 * k / 240.0 for k in range(241)]
    for index, eps in enumerate(shown):
        role = ("muted", "accent2", "accent")[index]
        points = [(x, mollifier(x, eps)) for x in xs_a]
        if index == len(shown) - 1:
            scene.area(a.fill_to(points, 0.0), fill="band")
        scene.path(a.curve(points), stroke=role,
                   sw=SW_CURVE if index == len(shown) - 1 else SW_CURVE2)
        peak = mollifier(0.0, eps)
        scene.math(a.X(eps) + 5, a.Y(peak) + 3, rf"\varepsilon={q2(eps)}", t=f"ε = {q2(eps)}", anchor="start",
                   fill=role, size=9.5, halo=True)
    masses = [integrate(lambda x: mollifier(x, eps), -eps, eps, 1600)
              for eps in shown + widths]
    if max(abs(m - 1) for m in masses) > 1e-9:
        raise SystemExit("mollification: a displayed kernel does not have unit mass")
    scene.math(a.right, a.y0 - 8, r"\int_{\mathbb R}\eta_\varepsilon=1", t='unit mass: ∫ ηε = 1', anchor="end",
               fill="muted", size=FS_LABEL)

    b = Frame(348, 66, 268, 148, -1.7, 1.7, -0.14, 1.16)
    scene.panel_title(316, 44, "the convolution")
    b.axes(scene, x_label="x", origin_y=0.0)
    step = [(-1.7, 0.0)]
    for jump in jumps:
        step += [(jump, rough(jump - 1e-9)), (jump, rough(jump + 1e-9))]
    step.append((1.7, 0.0))
    scene.path(b.curve(step), stroke="muted", sw=SW_CURVE2, dash=DASH)
    # Right of the animated width label, which owns the top-left corner.
    scene.text(b.X(-0.3), b.Y(1.0) - 8, "the rough function", anchor="start",
               fill="muted", size=9.5, halo=True)

    xs_b = [-1.7 + 3.4 * k / 200.0 for k in range(201)]
    def smooth_step(x, eps):
        total = 0.0
        for a, b, value in ((-1.2, -0.2, 1.0), (-0.2, 0.5, 0.25), (0.5, 1.4, 0.8)):
            lo, hi = max(-eps, x - b), min(eps, x - a)
            if lo < hi:
                total += value * integrate(lambda y: mollifier(y, eps), lo, hi, 240)
        return total

    profiles = [[(x, smooth_step(x, eps)) for x in xs_b] for eps in widths]
    if any(y < -1e-9 or y > 1 + 1e-9 for profile in profiles for _, y in profile):
        raise SystemExit("mollification: positivity or the sup bound failed")
    curves = b.curve_frames(profiles)
    scene.path(curves[0], stroke="accent", sw=SW_CURVE,
               anim=[discrete("d", curves)])

    marker_y = b.Y(-0.08)
    scene.line(b.X(-0.2 - widths[0]), marker_y, b.X(-0.2 + widths[0]), marker_y,
               stroke="accent2", sw=SW_CURVE2,
               anim=[discrete("x1", [q2(b.X(-0.2 - eps)) for eps in widths]),
                     discrete("x2", [q2(b.X(-0.2 + eps)) for eps in widths])])
    scene.math(b.X(-0.2), 252, r"\text{what the mollifier sees: }2\varepsilon", t='what the mollifier sees: 2ε',
               fill="accent2", size=9.5)
    for index, eps in enumerate(widths):
        scene.math(b.x0 + 8, b.y0 + 14, rf"\varepsilon={q2(eps)}", t=f"ε = {q2(eps)}", anchor="start", fill="ink",
                   size=FS_LABEL, halo=True, op=1.0 if index == 0 else 0.0,
                   anim=[slot(index, len(widths))])
    for frame, ticks in ((a, (-0.5, 0, 0.5)), (b, (-1, 0, 1))):
        for tick in ticks:
            scene.tick_label(frame.X(tick), frame.bottom + 16, q2(tick), size=9.5)
    scene.math(a.x0 + 5, a.y0 + 12, r"\eta_\varepsilon", t='ηε', anchor="start", size=10, fill="muted")
    scene.math(b.x0 - 10, b.Y(1) + 3, r"1", size=9.5, fill="muted")
    return scene


# --- the weak derivative of the absolute value -------------------------------

def fig_weak_derivative() -> Scene:
    """Test |x| against a genuine C∞ bump supported strictly inside (-1,1)."""
    centre, half = 0.2, 0.7
    support = (centre - half, centre + half)

    def phi(x: float) -> float:
        return bump((x - centre) / half)

    def dphi(x: float) -> float:
        z = (x - centre) / half
        if abs(z) >= 1.0:
            return 0.0
        return -2.0 * z * bump(z) / (half * (1.0 - z * z) ** 2)

    def sign(x: float) -> float:
        return 1.0 if x > 0.0 else (-1.0 if x < 0.0 else 0.0)

    breaks = [-1.0, support[0], 0.0, centre, support[1], 1.0]
    pairing = integrate_pieces(lambda x: abs(x) * dphi(x), breaks, 4000)
    tested = -integrate_pieces(lambda x: sign(x) * phi(x), breaks, 4000)
    if abs(pairing - tested) > 1e-8:
        raise SystemExit("weak-derivative: smooth-test pairings disagree")
    if not -1 < support[0] < 0 < support[1] < 1:
        raise SystemExit("weak-derivative: test support leaves the open domain")

    scene = Scene(
        "weak-derivative",
        "A weak derivative across a corner",
        r"On \((-1,1)\), \(u(x)=|x|\) has weak derivative \(\operatorname{sgn}(x)\). The dashed "
        r"test is \(\varphi(x)=b((x-0.2)/0.7)\), supported on \([-0.5,0.9]\), where "
        r"\(b(z)=\exp(1-1/(1-z^2))\) for \(|z|<1\), zero outside. Below, the signed areas of "
        r"\(|x|\varphi'\) and \(-\operatorname{sgn}(x)\varphi\) agree numerically, both "
        r"approximately \(-0.389\). Integration by parts on each side of zero proves the "
        r"identity for every smooth compactly supported test: outer boundary terms vanish with "
        r"\(\varphi\), and terms at zero vanish with \(|x|\). Changing \(\operatorname{sgn}(0)\) "
        r"affects neither integral. Agreement for the plotted test illustrates this argument; it "
        r"does not establish a weak derivative by itself.",
        "Four labelled graphs over x in (−1,1). Above left, |x| and a smooth "
        "bump with support strictly inside the domain. Above right, sign(x) "
        "with open circles at zero. Below, the signed integrands |x|φ′ and "
        "−sign(x)φ have different lobes but equal total areas, approximately "
        f"{num(pairing)}. The displayed identity quantifies over every smooth "
        "compactly supported test, not just the plotted bump.",
        width=640, height=464)
    a = Frame(60, 62, 234, 120, -1.05, 1.05, -0.08, 1.2)
    b = Frame(378, 62, 220, 120, -1.05, 1.05, -1.3, 1.3)
    scene.panel_title(28, 32, "a corner and a smooth test")
    scene.panel_title(346, 32, "the weak derivative")
    a.axes(scene, x_label="x", origin_y=0)
    b.axes(scene, x_label="x", origin_y=0)
    for frame in (a, b):
        for tick in (-1, 0, 1):
            scene.tick_label(frame.X(tick), frame.bottom + 17, num(tick), size=11)
    scene.path(a.sample(abs, -1, 1, 160), stroke="accent")
    scene.path(a.sample(phi, -1, 1, 400), stroke="accent2", dash=DASH)
    scene.math(a.X(-0.65), a.Y(0.9), r"u = |x|", fill="accent", halo=True)
    scene.math(a.X(centre), a.Y(1) - 8, r"\varphi", t='φ', fill="accent2", halo=True)
    for edge in support:
        scene.line(a.X(edge), a.Y(0) - 4, a.X(edge), a.Y(0) + 4,
                   stroke="accent2", sw=SW_AXIS)
    scene.math(60, 220, r"\operatorname{supp}\varphi=[-0.5,0.9]\subset(-1,1)", t='support φ = [−0.5, 0.9] ⊂ (−1,1)', anchor="start",
               fill="muted", size=11)
    for lo, hi, value in ((-1, 0, -1), (0, 1, 1)):
        scene.path(b.curve([(lo, value), (hi, value)]), stroke="accent")
        scene.circle(b.X(0), b.Y(value), 3, stroke="accent", fill="surface")
        scene.tick_label(b.x0 - 8, b.Y(value) + 4, num(value), anchor="end")
    scene.text(378, 220, "the value at 0 does not affect an integral", anchor="start",
               fill="muted", size=11)

    def integrand(x0: float, label: str, role: str, pieces) -> None:
        frame = Frame(x0, 276, 234 if x0 == 60 else 220, 112,
                      -1.05, 1.05, -2.7, 1.1)
        scene.math_title(x0 - 32, 255, label)
        frame.axes(scene, x_label="x", origin_y=0)
        for level in (-2, 1):
            scene.tick_label(frame.x0 - 8, frame.Y(level) + 4, num(level), anchor="end")
        for points in pieces:
            scene.area(frame.fill_to(points, 0), fill="band")
            scene.path(frame.curve(points), stroke=role)
        scene.math(x0, 414, rf"\text{{signed integral}}\approx{q3(pairing)}", t=f"signed integral ≈ {num(pairing)}", anchor="start",
                   fill=role, size=12)

    xs = [-1 + 2 * k / 600 for k in range(601)]
    integrand(60, r"|x|\varphi'", "accent", [[(x, abs(x) * dphi(x)) for x in xs]])
    # Split at zero so sampling does not invent a connecting sloped segment.
    negative = [(-1 + k / 300, phi(-1 + k / 300)) for k in range(301)]
    positive = [(k / 300, -phi(k / 300)) for k in range(301)]
    integrand(378, r"-\operatorname{sgn}(x)\varphi", "accent2", [negative, positive])
    scene.math(320, 447, r"\int_{-1}^1|x|\varphi'\,dx=-\int_{-1}^1\operatorname{sgn}(x)\varphi\,dx\quad(\varphi\in C_c^\infty(-1,1))", t='∫ |x| φ′ = −∫ sign(x) φ for every smooth compactly supported φ',
               size=12)
    return scene


# --- the embedding diagram ---------------------------------------------------


def fig_sobolev_ladder() -> Scene:
    """Which space a Sobolev space embeds into, read off one plane."""
    dim = 3

    def spend(inverse_p: float, derivatives: float) -> float:
        """The exponent 1/q that Gagliardo–Nirenberg–Sobolev gives when
        ``derivatives`` derivatives are spent in dimension ``dim``."""
        return inverse_p - derivatives / dim

    critical = spend(0.5, 1.0)
    q_critical = 1.0 / critical
    holder = 1.0 - dim / q_critical
    if abs(critical - 1.0 / 6.0) > 1e-12 or abs(holder - 0.5) > 1e-12:
        raise SystemExit("sobolev-ladder: the exponents are not the ones labelled")

    scene = Scene(
        "sobolev-ladder",
        "The embedding diagram",
        r"On a bounded smooth domain \(\Omega\subset\mathbb R^3\), place a Sobolev space with "
        r"\(s\) derivatives in \(L^p\) at \((1/p,s)\): integrability across, differentiability "
        r"up. Sobolev's relation \(1/q=1/p-1/3\) gives \(H^1\hookrightarrow L^6\). Applying it "
        r"to a function and its first derivatives gives \(H^2\hookrightarrow W^{1,6}\); Morrey "
        r"then gives \(C^{0,1/2}\), since \(1-3/6=1/2\). The shaded region \(s>3/p\) marks "
        r"continuity. The excess \(s-3/p\) is a Hölder exponent for the function when strictly "
        r"between zero and one; higher regularity needs derivative spaces and endpoint "
        r"qualifications. The dashed Rellich arrow \(H^1\hookrightarrow L^2\) is compact: "
        r"bounded sequences have strongly convergent subsequences in \(L^2\). Boundedness does "
        r"not force the whole sequence to converge. The domain assumptions supply the boundary "
        r"regularity needed here.",
        "An embedding diagram with horizontal coordinate 1/p and vertical "
        "coordinate s, on a bounded smooth three-dimensional domain. Solid "
        "arrows run from H¹ to L⁶ and from H² through first-order Sobolev "
        "regularity with exponent 6 to Hölder regularity with exponent 1/2. A dashed "
        "vertical arrow H¹ to L² denotes compact embedding and convergence of "
        "a subsequence. The region s > 3/p is shaded for continuity.",
        width=640.0, height=292.0)

    frame = Frame(76, 62, 490, 166, -0.02, 1.08, -0.08, 2.16)
    frame.axes(scene, x_label="1/p", y_label="smoothness s",
               y_tex=r"\text{smoothness }s", origin_y=0.0)
    for value, name in ((0.0, "0"), (critical, "1/6"), (0.5, "1/2"), (1.0, "1")):
        scene.line(frame.X(value), frame.Y(0.0), frame.X(value), frame.Y(0.0) + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(frame.X(value), frame.Y(0.0) + 16, name, size=9.5)
    for value in (1.0, 2.0):
        scene.line(frame.x0 - 4, frame.Y(value), frame.x0, frame.Y(value),
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(frame.x0 - 8, frame.Y(value) + 3.5, q2(value),
                         anchor="end", size=9.5)

    top = frame.ymax
    scene.area(poly_path([(frame.X(0.0), frame.Y(0.0)),
                          (frame.X(0.0), frame.Y(top)),
                          (frame.X(top / dim), frame.Y(top))]) + "Z", fill="band")
    scene.path(frame.curve([(0.0, 0.0), (top / dim, top)]), stroke="accent2",
               sw=SW_CURVE2, dash=DASH)
    scene.math(frame.X(top / dim) + 6, frame.Y(top) + 16, r"s=3/p", t='s = n/p', anchor="start",
               fill="accent2", size=9.5, halo=True)
    scene.math(frame.X(0.02), frame.Y(2.06), r"s-3/p>0:", t='s − n/p > 0:', anchor="start",
               fill="accent2", size=9.5)
    scene.text(frame.X(0.02), frame.Y(1.93), "continuous, Hölder", anchor="start",
               fill="accent2", size=9.5)
    scene.math(frame.X(0.02), frame.Y(1.80),
               rf"\alpha=1-{dim}/6=1/2", t=f"here α = 1 − {dim}/6 = 1/2",
               anchor="start", fill="accent2", size=9.5)

    ladder_top = (critical + top / dim, top)
    scene.path(frame.curve([(0.5, 1.0), ladder_top]), stroke="muted", sw=SW_AXIS,
               dash=DOT)
    scene.math(frame.X(ladder_top[0]) + 6, frame.Y(top) + 2, r"1/q=1/p-s/3", t='1/q = 1/p − s/n',
               anchor="start", fill="muted", size=9.5)

    points = [
        ((1.0, 0.0), r"L^1", "above"),
        ((0.5, 0.0), r"L^2", "up-right"),
        ((critical, 0.0), r"L^6", "left"),
        ((0.5, 1.0), r"H^1", "left"),
        ((critical, 1.0), "W^{1,6}", "left"),
        ((0.5, 2.0), r"H^2", "left"),
        ((0.0, holder), r"C^{0,1/2}", "right"),
    ]
    for (x, y), name, where in points:
        scene.circle(frame.X(x), frame.Y(y), 3.2, fill="ink")
        if where == "above":
            scene.math(frame.X(x), frame.Y(y) - 10, name, fill="ink", size=FS_LABEL,
                       halo=True)
        elif where == "right":
            # The Morrey arrow arrives from above and the line s = n/p passes
            # below, so this label sits in the wedge between them.
            scene.math(frame.X(x) + 8, frame.Y(y) + 11, name, anchor="start",
                       fill="ink", size=FS_LABEL, halo=True)
        elif where == "up-right":
            scene.math(frame.X(x) + 8, frame.Y(y) - 8, name, anchor="start",
                       fill="ink", size=FS_LABEL, halo=True)
        else:
            scene.math(frame.X(x) - 8, frame.Y(y) - 8, name, anchor="end",
                  fill="ink", size=FS_LABEL, halo=True)

    def at(x: float, y: float) -> tuple[float, float]:
        return (frame.X(x), frame.Y(y))

    draw_arrow(scene, [at(0.5, 2.0), at(critical, 1.0)], role="accent")
    scene.math(frame.X(0.3) - 6, frame.Y(1.44), r"\text{Sobolev on }\nabla u", t='Sobolev on ∇u', anchor="end",
               fill="muted", size=9.5, halo=True)
    draw_arrow(scene, [at(critical, 1.0), at(0.0, holder)], role="accent2")
    # Halfway between the two parallel lines, and it is the box that has to sit
    # in the corridor, not the baseline, hence the drop.
    corridor = 0.115
    scene.text(frame.X(corridor), frame.Y(holder / 2.0 + dim * corridor) + 2.3,
               "Morrey", anchor="middle", fill="muted", size=9.5, halo=True)
    draw_arrow(scene, [at(0.5, 1.0), at(critical, 0.0)], role="accent")
    # In the triangle between the arrow, the axis and the compactness arrow.
    scene.math(frame.X(0.26), frame.Y(0.13), r"\text{Sobolev: }1/2-1/3=1/6", t='Sobolev: 1/2 − 1/3 = 1/6',
               anchor="start", fill="muted", size=9.5, halo=True)
    draw_arrow(scene, [at(0.5, 1.0), at(0.5, 0.0)], role="muted", dash=DASH,
               label="compact: subsequence", label_at="right")
    scene.math(76, 276, rf"\Omega\subset\mathbb{{R}}^{dim}\text{{ bounded and smooth; dashed arrow: compact embedding}}",
               t=f"Ω bounded and smooth, n = {dim}; dashed arrow: compact embedding", anchor="start",
               fill="muted", size=9.5)
    return scene


# --- the Laplace kernel ------------------------------------------------------

def fig_fundamental_solution() -> Scene:
    """The Laplace kernel in two and three dimensions, pole and all."""
    clip_at = 0.62
    unit_sphere = {2: 2.0 * math.pi, 3: 4.0 * math.pi}
    plane_constant = 1.0 / (2.0 * math.pi)
    ball_volume = 4.0 * math.pi / 3.0
    space_constant = 1.0 / (3.0 * (3.0 - 2.0) * ball_volume)

    def plane(r: float) -> float:
        return -plane_constant * math.log(r)

    def space(r: float) -> float:
        return space_constant / r

    def flux(kernel, r: float, dim: int) -> float:
        """The outward flux of −∇Φ through the sphere of radius ``r``."""
        step = 1e-6
        slope = (kernel(r + step) - kernel(r - step)) / (2.0 * step)
        return -slope * unit_sphere[dim] * r ** (dim - 1)

    fluxes = [flux(plane, r, 2) for r in (0.4, 1.0, 1.7)]
    fluxes += [flux(space, r, 3) for r in (0.4, 1.0, 1.7)]
    if max(abs(value - 1.0) for value in fluxes) > 1e-6:
        raise SystemExit("fundamental-solution: the normalization does not hold")

    scene = Scene(
        "fundamental-solution",
        "The kernel that inverts the Laplacian",
        r"Two radial profiles of the fundamental solution of \(-\Delta\), drawn on the same "
        r"scale: \(\Phi_2(r)=-\log r/(2\pi)\) and \(\Phi_3(r)=1/(4\pi r)\). Both tend to "
        r"\(+\infty\) as \(r\downarrow0\); the curves stop at height \(0.62\), at positive radii "
        r"that are plot cutoffs. Their constants give outward flux one for \(-\nabla\Phi\) "
        r"through every centred circle or sphere. Together with harmonicity away from the "
        r"origin, this yields the normalization \(-\Delta\Phi=\delta_0\). The generator checks "
        r"the flux numerically at three radii per dimension. The planar kernel changes sign at "
        r"\(r=1\); the spatial kernel stays positive and decays to zero. Radial derivative "
        r"calculations alone do not prove the distributional identity: it also needs the "
        r"limiting integration-by-parts argument at the pole.",
        "Two radial plots with horizontal axis r = |x| and vertical axis Φ. "
        "The planar kernel −log(r)/(2π) crosses zero at r = 1; the spatial "
        "kernel 1/(4πr) stays positive. Each curve is cut at height 0.62, "
        "with a label explaining that it continues to infinity as r tends "
        "to zero. The positive-radius endpoints are plot cutoffs, not poles.",
        width=640.0, height=280.0)

    def panel(x0: float, title: str, formula: str, kernel, note: str,
              zero_at: float | None, start: float) -> None:
        frame = Frame(x0, 74, 226, 148, 0.0, 2.2, -0.26, 0.72)
        scene.math_title(x0 - 30, 46, title)
        scene.math(x0 - 30, 62, formula, anchor="start", fill="muted",
                   size=FS_LABEL)
        frame.axes(scene, origin_y=0.0)
        scene.math(frame.right, frame.Y(0.0) + 32, r"r = |x|", anchor="end",
                   fill="muted", italic=True)
        # In the plane the kernel is negative for r > 1, so the line at zero is
        # a reference and not the floor of the panel: the radial ticks hang off
        # the bottom edge, where no curve reaches them.
        for tick in (1.0, 2.0):
            scene.line(frame.X(tick), frame.bottom, frame.X(tick),
                       frame.bottom + 4, stroke="muted", sw=SW_AXIS)
            scene.tick_label(frame.X(tick), frame.bottom + 14, q2(tick), size=9.5)
        for tick in (-0.2, 0.2, 0.4, 0.6):
            scene.line(frame.x0 - 3, frame.Y(tick), frame.x0, frame.Y(tick),
                       stroke="muted", sw=SW_AXIS)
            scene.tick_label(frame.x0 - 7, frame.Y(tick) + 3.5, num(tick),
                             anchor="end", size=9.5)
        scene.line(frame.x0, frame.Y(clip_at), frame.right, frame.Y(clip_at),
                   stroke="muted", sw=SW_AXIS, dash=DOT)
        scene.text(frame.right, frame.Y(clip_at) - 6, f"clipped at {q2(clip_at)}",
                   anchor="end", fill="muted", size=9.0)
        if abs(kernel(start) - clip_at) > 1e-12:
            raise SystemExit("fundamental-solution: the plotted cutoff is misplaced")
        points = [(start + (2.2 - start) * k / 300.0,
                   kernel(start + (2.2 - start) * k / 300.0)) for k in range(301)]
        scene.path(frame.curve(points), stroke="accent", sw=SW_CURVE)
        scene.circle(frame.X(start), frame.Y(clip_at), 2.6, fill="accent")
        scene.math(frame.X(start) + 7, frame.Y(clip_at) + 14, r"\text{continues to }+\infty", t='continues to +∞',
                   anchor="start", fill="accent", size=9.0)
        if zero_at is not None:
            scene.circle(frame.X(zero_at), frame.Y(0.0), 3.0, stroke="accent",
                         fill="surface", sw=1.3)
            scene.text(frame.X(zero_at) + 6, frame.Y(0.0) - 8, "sign change",
                       anchor="start", fill="muted", size=9.0)
        scene.math(x0, 250, note, anchor="start", fill="muted", size=9.5)

    panel(96, "n = 2", r"\Phi(x)=-\log|x|/(2\pi)", plane,
          rf"1/(2\pi)\approx{q3(plane_constant)}\text{{; pole at }}r=0", 1.0,
          math.exp(-clip_at / plane_constant))
    panel(390, "n = 3", r"\Phi(x)=1/(4\pi|x|)", space,
          rf"1/(4\pi)\approx{q3(space_constant)}\text{{; pole at }}r=0", None,
          space_constant / clip_at)
    scene.math(320, 268, r"\text{harmonic off }0\text{ and unit flux of }-\nabla\Phi\ \Longrightarrow\ -\Delta\Phi=\delta_0", t='harmonic away from 0 + unit outward flux of −∇Φ give −ΔΦ = δ₀', fill="muted", size=9.5)
    return scene


# --- the mean value property -------------------------------------------------

def fig_mean_value() -> Scene:
    """A harmonic function, two circles, and the same number three times."""
    centre = (0.4, 0.05)
    radii = (0.5, 0.25)

    def harmonic(x: float, y: float) -> float:
        """The real part of z³, harmonic because z³ is holomorphic."""
        return x ** 3 - 3.0 * x * y * y

    def circle_average(radius: float, n: int = 4000) -> float:
        total = 0.0
        for k in range(n):
            angle = 2.0 * math.pi * k / n
            total += harmonic(centre[0] + radius * math.cos(angle),
                              centre[1] + radius * math.sin(angle))
        return total / n

    def on_ring(angle: float, radius: float = radii[0]) -> float:
        return harmonic(centre[0] + radius * math.cos(angle),
                        centre[1] + radius * math.sin(angle))

    middle = harmonic(*centre)
    averages = [circle_average(radius) for radius in radii]
    if max(abs(value - middle) for value in averages) > 1e-9:
        raise SystemExit("mean-value: the averages do not agree with the centre")
    turn = 2.0 * math.pi
    swing = [on_ring(turn * k / 2000.0) for k in range(2000)]
    above = integrate_mid(lambda a: max(on_ring(a) - middle, 0.0), 0.0, turn, 3000)
    below = integrate_mid(lambda a: max(middle - on_ring(a), 0.0), 0.0, turn, 3000)
    if abs(above - below) > 1e-6:
        raise SystemExit("mean-value: the two shaded areas are not equal")

    scene = Scene(
        "mean-value",
        "The average over a sphere is the value at the centre",
        r"Left: \(u=\operatorname{Re}(z^3)=x^3-3xy^2\) on the unit disc. Its zero set consists "
        r"of the lines at \(30^\circ,90^\circ,150^\circ\); the remaining level curves are traced "
        r"numerically. Both circles have centre \(c=(0.4,0.05)\). Right: the values on the "
        r"circle of radius \(0.5\) range from approximately \(-0.315\) to \(0.726\). The signed "
        r"departures above and below the dashed line balance: their computed integrals agree "
        r"within \(10^{-6}\). The average is \(0.061=u(c)\), also the average on the smaller "
        r"circle of radius \(0.25\). Harmonicity proves this equality for every positive radius "
        r"whose closed disc stays in the domain. The two numerical averages illustrate that "
        r"theorem.",
        "A disc with the level curves of a harmonic function and two circles "
        "drawn inside it around a common centre; beside it, the values of the "
        "function along the larger circle as a function of angle, oscillating "
        "around a dashed horizontal line, with the areas above and below the "
        "line shaded and equal.",
        width=640.0, height=316.0)

    disc = Frame(46, 58, 206, 206, -1.06, 1.06, -1.06, 1.06)
    scene.math_title(24, 42, r"u=x^3-3xy^2\text{ on the disc}", t='u = x³ − 3xy² on the disc')
    scene.math(24, 58, r"\text{harmonic; both circles centred at }c", t=f"harmonic, and both circles are centred at c",
               anchor="start", fill="muted", size=FS_LABEL)
    inside = lambda x, y: x * x + y * y <= 0.9801
    for level in (-0.6, -0.3, -0.1, 0.1, 0.3, 0.6):
        chains = clip_chains(
            join_segments(contours(harmonic, -1.0, 1.0, -1.0, 1.0, level, 104)),
            inside)
        scene.path(chain_path(disc, chains), stroke="muted", sw=SW_CURVE2, sop=0.55)
    zero = clip_chains(
        join_segments(contours(harmonic, -1.0, 1.0, -1.0, 1.0, 0.0, 104)), inside)
    scene.path(chain_path(disc, zero), stroke="accent2", sw=SW_CURVE2)
    scene.circle(disc.X(0.0), disc.Y(0.0),
                 disc.w / (disc.xmax - disc.xmin), stroke="ink", fill="",
                 sw=SW_CURVE2)
    for index, radius in enumerate(radii):
        scene.circle(disc.X(centre[0]), disc.Y(centre[1]),
                     radius * disc.w / (disc.xmax - disc.xmin), stroke="accent",
                     fill="", sw=SW_CURVE if index == 0 else SW_CURVE2,
                     dash="" if index == 0 else DASH)
    scene.line(disc.X(-1), disc.Y(0), disc.X(1), disc.Y(0),
               stroke="muted", sw=SW_AXIS, dash=DOT)
    scene.line(disc.X(0), disc.Y(-1), disc.X(0), disc.Y(1),
               stroke="muted", sw=SW_AXIS, dash=DOT)
    scene.math(disc.X(1) + 10, disc.Y(0) + 4, r"x", size=10, fill="muted")
    scene.math(disc.X(0) + 8, disc.Y(0.9), r"y", size=10, fill="muted", halo=True)
    scene.circle(disc.X(centre[0]), disc.Y(centre[1]), 3.0, fill="accent")
    scene.math(disc.X(centre[0]) + 7, disc.Y(centre[1]) + 12, r"c", anchor="start",
               fill="accent", size=FS_LABEL, italic=True, halo=True)
    scene.math(disc.X(-0.72), disc.Y(0.86), r"u = 0", fill="accent2", size=9.5,
               halo=True)

    angles = Frame(330, 82, 272, 148, 0.0, turn,
                   min(swing) - 0.14, max(swing) + 0.10)
    scene.math_title(304, 42, r"u\text{ along the larger circle}", t='u along the larger circle')
    scene.math(304, 58, rf"r={q2(radii[0])}\text{{, against the angle }}\theta", t=f"radius {q2(radii[0])}, against the angle θ",
               anchor="start", fill="muted", size=FS_LABEL)
    scene.line(angles.x0, angles.bottom, angles.right, angles.bottom,
               stroke="muted", sw=SW_AXIS)
    scene.line(angles.x0, angles.y0, angles.x0, angles.bottom, stroke="muted",
               sw=SW_AXIS)
    for tick, name in ((0.0, "0"), (math.pi, r"\pi"), (turn, r"2\pi")):
        scene.line(angles.X(tick), angles.bottom, angles.X(tick),
                   angles.bottom + 4, stroke="muted", sw=SW_AXIS)
        scene.tick_label(angles.X(tick), angles.bottom + 16, name, size=9.5)
    scene.math(angles.right, angles.bottom + 30, r"\theta", t='θ', anchor="end", fill="muted",
               italic=True)
    for value in (-0.2, 0, 0.6):
        scene.tick_label(angles.x0 - 7, angles.Y(value) + 3, num(value),
                         anchor="end", size=9.5)
    ring = [(turn * k / 240.0, on_ring(turn * k / 240.0)) for k in range(241)]
    for keep in (lambda x, y: y >= middle, lambda x, y: y <= middle):
        for lobe in clip_chains([ring], keep):
            scene.area(angles.fill_to(lobe, middle), fill="band")
    scene.path(angles.curve(ring), stroke="accent", sw=SW_CURVE)
    scene.line(angles.x0, angles.Y(middle), angles.right, angles.Y(middle),
               stroke="accent2", sw=SW_CURVE2, dash=DASH)
    scene.math(angles.X(1.5), angles.Y(middle) - 9,
               rf"\text{{average }}{q3(middle)}=u(c)", t=f"the average, {num(middle)} = u(c)", anchor="start",
               fill="accent2", size=9.5, halo=True)
    scene.text(46, 292, f"the shaded area above the line is {q3(above)}, and so "
               f"is the shaded area below it", anchor="start", fill="muted",
               size=9.5)
    scene.text(46, 306, f"the average over the smaller circle is "
               f"{num(averages[1])}: every radius that fits gives the same "
               "number", anchor="start", fill="muted", size=9.5)
    return scene


# --- diffusion ---------------------------------------------------------------

def fig_heat_kernel() -> Scene:
    """The Gaussian spreading, and the cylinder the maximum principle needs."""
    times = [0.05 * (0.8 / 0.05) ** (k / 5.0) for k in range(6)]
    masses = [integrate(lambda x: heat_kernel(x, t), -12.0, 12.0, 6000)
              for t in times]
    if max(abs(mass - 1.0) for mass in masses) > 5e-4:
        raise SystemExit("heat-kernel: the computed mass is not one")

    scene = Scene(
        "heat-kernel",
        "The heat kernel, and where the maximum principle lives",
        r"Left: \(\Gamma(x,t)=\exp(-x^2/(4t))/\sqrt{4\pi t}\) at six positive times. The active "
        r"curve steps through the computed snapshots while faint curves retain the others. The "
        r"peak falls and the width grows, but the exact mass on \(\mathbb R\) stays one. "
        r"Quadrature on \([-12,12]\), wider than the plotted window, agrees with this mass to "
        r"the displayed precision. Since \(\Gamma(x,t)>0\) for \(t>0\), convolution with "
        r"nonnegative initial data of positive mass is immediately positive everywhere. Right: "
        r"for a homogeneous heat solution continuous on the closed bounded cylinder, the maximum "
        r"is controlled by the initial slice and spatial sides. The final slice \(t=T\) belongs "
        r"to \(\Omega\times(0,T]\), but is not part of the parabolic boundary where comparison "
        r"data are supplied.",
        "Two panels. Left, six Gaussian profiles of decreasing height and "
        "increasing width, the earliest and the latest labelled with their "
        "times. Right, a rectangle in space and time whose bottom edge and two "
        "side edges are drawn as a single thick line, the parabolic boundary, "
        "with the top edge dashed and marked as not part of it.",
        width=640.0, height=290.0)

    frame = Frame(60, 70, 296, 152, -3.0, 3.0, 0.0, 1.42)
    scene.panel_title(24, 46, "the kernel at six times")
    frame.axes(scene, x_label="x", origin_y=0.0)
    scene.math(frame.x0 + 5, frame.y0 + 12, r"\Gamma(x,t)", t='Γ(x,t)', anchor="start", size=10,
               fill="muted")
    for value in (0, 0.5, 1):
        scene.tick_label(frame.x0 - 7, frame.Y(value) + 3, q2(value),
                         anchor="end", size=9.5)
    for tick in (-2.0, 0.0, 2.0):
        scene.line(frame.X(tick), frame.Y(0.0), frame.X(tick), frame.Y(0.0) + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(frame.X(tick), frame.Y(0.0) + 16, num(tick), size=9.5)
    profiles = [[(x, heat_kernel(x, t)) for x in
                 (-3.0 + 6.0 * k / 240.0 for k in range(241))] for t in times]
    fills = frame.fill_frames(profiles, 0.0)
    curves = frame.curve_frames(profiles)
    for curve in curves:
        scene.path(curve, stroke="muted", sw=SW_AXIS, sop=0.5)
    scene.area(fills[0], fill="band", anim=[discrete("d", fills)])
    scene.path(curves[0], stroke="accent", sw=SW_CURVE,
               anim=[discrete("d", curves)])
    for index, t in enumerate(times):
        scene.math(frame.right - 4, frame.y0 + 12, rf"t\approx{q3(t)}", t=f"t ≈ {q3(t)}", anchor="end",
                   fill="accent", size=10, halo=True, op=1 if index == 0 else 0,
                   anim=[slot(index, len(times))])
    scene.math(frame.x0, 256, r"\int_{\mathbb R}\Gamma\,dx=1", t='∫ℝ Γ dx = 1; checked numerically on [−12,12]',
               anchor="start", fill="muted", size=9.5)

    cyl = Frame(430, 70, 152, 152, -0.12, 1.12, -0.1, 1.18)
    scene.panel_title(404, 46, "the parabolic cylinder")
    scene.rect(cyl.X(0.0), cyl.Y(1.0), cyl.X(1.0) - cyl.X(0.0),
               cyl.Y(0.0) - cyl.Y(1.0), fill="band")
    scene.path(poly_path([(cyl.X(0.0), cyl.Y(1.0)), (cyl.X(0.0), cyl.Y(0.0)),
                          (cyl.X(1.0), cyl.Y(0.0)), (cyl.X(1.0), cyl.Y(1.0))]),
               stroke="accent", sw=2.4)
    scene.line(cyl.X(0.0), cyl.Y(1.0), cyl.X(1.0), cyl.Y(1.0), stroke="muted",
               sw=SW_CURVE2, dash=DASH)
    scene.math(cyl.X(0.5), cyl.Y(0.52), r"\Omega\times(0,T]", t='Ω × (0, T]', fill="ink", size=FS_LABEL)
    scene.math(cyl.X(0.5), cyl.Y(1.0) - 8, r"t=T\text{: final slice}", t='t = T: final slice', fill="muted", size=9.0)
    scene.math(cyl.X(1) + 18, cyl.Y(1) + 10, r"t\uparrow", t='t ↑', size=9.5, fill="muted")
    scene.math(cyl.X(1) + 18, cyl.Y(0) + 17, r"x\to", t='x →', size=9.5, fill="muted")
    scene.math(cyl.X(0.5), cyl.Y(0.0) + 15, r"\Omega\times\{0\}", t='Ω × {0}', fill="accent", size=9.5)
    scene.math(cyl.X(0.0) - 6, cyl.Y(0.24), r"\partial\Omega", t='∂Ω', anchor="end", fill="accent",
               size=9.5)
    scene.math(cyl.X(1.0) + 6, cyl.Y(0.24), r"\partial\Omega", t='∂Ω', anchor="start", fill="accent",
               size=9.5)
    scene.text(cyl.X(0.5), 264, "max over the closure",
               fill="muted", size=9.5)
    scene.text(cyl.X(0.5), 277, "= max over the solid line", fill="muted",
               size=9.5)
    return scene


# --- two travelling waves ----------------------------------------------------

def fig_fourier_evolution() -> Scene:
    """Compare the exact heat and wave displacement multipliers."""
    scene = Scene(
        "fourier-evolution",
        "The same frequencies, two evolutions",
        r"Each curve starts with displacement one. With \(\omega=2\pi\|\xi\|\), "
        r"the heat multiplier is \(e^{-\omega^2t}\), while the wave multiplier "
        r"with zero initial velocity is \(\cos(\omega t)\). Solid curves use "
        r"\(\omega=1\); dashed curves use \(\omega=2\). Doubling the frequency "
        r"quadruples the heat decay rate and doubles the wave oscillation rate. "
        r"These plots show individual Fourier multipliers, not a spatial solution.",
        "Two time plots from zero to four. In the heat plot both curves fall "
        "from one toward zero, with frequency two decaying more quickly. "
        "In the wave plot the curves oscillate between minus one and one, "
        "with frequency two making twice as many oscillations.",
        width=640, height=292)
    frames = [
        Frame(48, 70, 245, 164, 0, 4, -1.1, 1.1),
        Frame(367, 70, 245, 164, 0, 4, -1.1, 1.1),
    ]
    for frame, title, multiplier in zip(
            frames, ["heat: decay", "waves: oscillation"],
            [lambda omega, t: math.exp(-omega * omega * t),
             lambda omega, t: math.cos(omega * t)]):
        scene.panel_title(frame.x0, 42, title)
        frame.axes(scene, x_label="t", origin_y=0)
        for value in (-1, 0, 1):
            scene.tick_label(frame.x0 - 10, frame.Y(value) + 3, str(value), size=9)
        for t in (1, 2, 3, 4):
            scene.tick_label(frame.X(t), frame.bottom + 14, str(t), size=9)
        for omega, role, dash in [(1, "accent", ""), (2, "accent2", DASH)]:
            scene.path(frame.sample(lambda t: multiplier(omega, t), 0, 4, 160),
                       stroke=role, sw=SW_CURVE, dash=dash)
    for x, omega, role, dash in [
            (165, 1, "accent", ""), (359, 2, "accent2", DASH)]:
        scene.line(x, 272, x + 28, 272, stroke=role, sw=SW_CURVE, dash=dash)
        scene.math(x + 38, 276, rf"\omega={omega}", anchor="start",
                   fill=role, size=FS_LABEL)
    return scene


def fig_dalembert() -> Scene:
    """d'Alembert's formula, and what the solution at a point depends on."""
    snapshots = [0.0, 0.55, 1.2]

    def initial(x: float) -> float:
        return bump(2.0 * x)

    def half(x: float, t: float, direction: float) -> float:
        return 0.5 * initial(x + direction * t)

    point = (0.55, 1.15)
    dependence = (point[0] - point[1], point[0] + point[1])

    scene = Scene(
        "dalembert",
        "One shape, two halves, one cone",
        r"Left: the unit-speed wave equation with initial displacement \(g\) and zero initial "
        r"velocity has \(u(x,t)=\tfrac12g(x+t)+\tfrac12g(x-t)\). Here \(g\) is a smooth bump "
        r"supported on \([-0.5,0.5]\). At \(t=0\), the coincident halves are dashed at half "
        r"height beneath their sum; they then separate without changing shape. Right: the "
        r"backward characteristic cone from \((x,t)=(0.55,1.15)\) has base \([-0.6,1.7]\). The "
        r"displacement contributes its two endpoint values. Initial velocity \(h\) would add "
        r"\(\tfrac12\int_{x-t}^{x+t}h(y)\,dy\). Changing either datum outside that interval "
        r"cannot change the solution at the apex: d'Alembert's formula makes finite propagation "
        r"explicit.",
        "Three snapshots of a smooth bump splitting into two half-height "
        "copies moving left and right at speed one. Only at time zero are "
        "the coincident halves dashed beneath their solid sum. A neighbouring "
        "space-time plot shows a backward cone with slopes plus and minus "
        "one and a shaded base interval of dependence.",
        width=640.0, height=298.0)

    scene.panel_title(24, 44, "the two halves separating")
    for index, t in enumerate(snapshots):
        frame = Frame(56, 62.0 + index * 78.0, 262, 62, -2.3, 2.3, -0.08, 1.12)
        scene.line(frame.x0, frame.Y(0.0), frame.right, frame.Y(0.0),
                   stroke="muted", sw=SW_AXIS)
        scene.line(frame.x0, frame.y0, frame.x0, frame.Y(0),
                   stroke="muted", sw=SW_AXIS)
        if index == 0:
            scene.math(frame.x0 - 8, frame.y0 - 7, r"u", size=9.5, fill="muted")
        xs = [-2.3 + 4.6 * k / 200.0 for k in range(201)]
        if index == 0:
            # The halves are one curve at t = 0, so draw one, over its support.
            support = [-0.56 + 1.12 * k / 120.0 for k in range(121)]
            scene.path(frame.curve([(x, half(x, 0.0, 1.0)) for x in support]),
                       stroke="muted", sw=SW_CURVE2, dash=DASH)
        scene.path(frame.curve([(x, half(x, t, 1.0) + half(x, t, -1.0))
                                for x in xs]), stroke="accent", sw=SW_CURVE)
        scene.math(frame.x0 + 2, frame.y0 + 12, f"t={q2(t)}", t=f"t = {q2(t)}", anchor="start",
                   fill="ink", size=FS_LABEL, halo=True)
        if index == 0:
            scene.text(frame.X(1.45), frame.Y(0.5), "the halves coincide,",
                       anchor="middle", fill="muted", size=9.0)
            scene.text(frame.X(1.45), frame.Y(0.28), "dashed at half height",
                       anchor="middle", fill="muted", size=9.0)
        scene.math(frame.right + 9, frame.Y(0) + 4, r"x", size=9.5, fill="muted")
        scene.tick_label(frame.X(0), frame.Y(0) + 13, "0", size=9)
        scene.tick_label(frame.x0 - 8, frame.Y(1) + 3, "1", size=9)
        if index == len(snapshots) - 1:
            scene.math(frame.X(-t), frame.Y(0.5) - 10, r"\tfrac12 g(x+t)", t='½g(x + t)', fill="muted",
                       size=9.0, halo=True)
            scene.math(frame.X(t), frame.Y(0.5) - 10, r"\tfrac12 g(x-t)", t='½g(x − t)', fill="muted",
                       size=9.0, halo=True)

    cone = Frame(390, 62, 226, 174, -1.35, 1.85, -0.05, 1.42)
    scene.panel_title(364, 44, "the backward cone")
    cone.axes(scene, x_label="x", y_tex="t", origin_y=0.0)
    scene.area(poly_path([(cone.X(point[0]), cone.Y(point[1])),
                          (cone.X(dependence[0]), cone.Y(0.0)),
                          (cone.X(dependence[1]), cone.Y(0.0))]) + "Z",
               fill="band")
    for edge in dependence:
        scene.path(cone.curve([(point[0], point[1]), (edge, 0.0)]),
                   stroke="accent2", sw=SW_CURVE2)
    scene.line(cone.X(dependence[0]), cone.Y(0.0), cone.X(dependence[1]),
               cone.Y(0.0), stroke="accent", sw=3.0)
    scene.circle(cone.X(point[0]), cone.Y(point[1]), 3.2, fill="ink")
    scene.math(cone.X(point[0]) + 8, cone.Y(point[1]) + 4,
               f"({q2(point[0])}, {q2(point[1])})", anchor="start", fill="ink",
               size=9.5, halo=True)
    # Each edge names the slope it actually has, computed from the apex and the
    # foot, so the two cannot be labelled the wrong way round: the left edge is
    # the line x − t = −0.6 and rises, the right edge is x + t = 1.7 and falls.
    for foot, label_x in zip(dependence, (-0.55, 1.42)):
        rise = point[1] / (point[0] - foot)
        if abs(abs(rise) - 1.0) > 1e-9:
            raise SystemExit("dalembert: a cone edge is not a characteristic")
        scene.math(cone.X(label_x), cone.Y(0.62),
                   rf"\text{{slope }}{'+' if rise > 0.0 else '-'}1", anchor="middle",
                   fill="muted", size=9.0, halo=True)
    scene.text(cone.X(0.25), cone.Y(0.0) + 17, "the data that matters",
               fill="accent", size=9.5)
    # Outside the cone rather than inside it: an edge of slope one runs through
    # the corner where the foot of the cone meets its base.
    scene.math(cone.X(dependence[0]) - 4, cone.Y(0.0) - 7, q3(dependence[0]), t=num(dependence[0]),
               anchor="end", fill="accent", size=9.0)
    scene.math(cone.X(dependence[1]) + 4, cone.Y(0.0) - 7, q3(dependence[1]), t=num(dependence[1]),
               anchor="start", fill="accent", size=9.0)
    scene.math(390, 262, r"x\pm t\text{ is constant on the edges,}", t='x ± t is constant along the two edges,', anchor="start",
               fill="muted", size=9.5)
    scene.text(390, 275, "which is why the halves travel unchanged",
               anchor="start", fill="muted", size=9.5)
    return scene


# --- the shock ---------------------------------------------------------------

def fig_shock_formation() -> Scene:
    """Burgers characteristics, the breaking time, the shock, and the fan."""
    fan_at = 2.0

    def initial(x: float) -> float:
        """One down ramp, which compresses, and one up jump, which fans out."""
        if x < 0.0:
            return 1.0
        if x <= 1.0:
            return 1.0 - x
        if x < fan_at:
            return 0.0
        return 1.0

    ramp_slope = -1.0
    breaking = -1.0 / ramp_slope
    shock_speed = 0.5 * (1.0 + 0.0)

    def shock(t: float) -> float:
        return 1.0 + shock_speed * (t - breaking)

    def solution(x: float, t: float) -> float:
        """The entropy solution before the shock meets the fan at t = 3."""
        if t >= 3:
            raise ValueError("the displayed pre-interaction formula needs t < 3")
        if t <= 0.0:
            return initial(x)
        if t < breaking:
            if x < t:
                return 1.0
            if x <= 1.0:
                return (1.0 - x) / (1.0 - t)
            if x < fan_at:
                return 0.0
        else:
            if x < shock(t):
                return 1.0
            if x < fan_at:
                return 0.0
        if x <= fan_at + t:
            return (x - fan_at) / t
        return 1.0

    if abs(breaking - 1.0) > 1e-6:
        raise SystemExit("shock-formation: the breaking time is not the one drawn")

    t_max = 1.85
    profile_times = [0.0, 0.6, 1.6]
    scene = Scene(
        "shock-formation",
        "Compression and rarefaction in Burgers' equation",
        r"For \(u_t+(u^2/2)_x=0\), a characteristic carries \(u_0(x_0)\) along \(x=x_0+t "
        r"u_0(x_0)\). These piecewise linear initial data have a downward ramp on \([0,1]\) and "
        r"an upward jump at \(x=2\); they are not globally smooth. On the ramp \(u_0'=-1\), so "
        r"characteristics meet at \(t=1\). The entropy solution continues with a downward jump "
        r"from one to zero. Rankine–Hugoniot gives speed \((1/2-0)/(1-0)=1/2\), with "
        r"characteristics entering the shock from both sides. The upward jump instead opens into "
        r"\(u=(x-2)/t\) between \(x=2\) and \(x=2+t\). Every plotted time precedes the shock's "
        r"encounter with the fan at \(t=3\). Compression creates a discontinuity while expansion "
        r"fills a gap.",
        "Two stacked panels sharing a horizontal axis. Above, the solution "
        "profile at three times: a ramp that steepens, then a vertical jump "
        "followed by a rising straight segment. Below, the space-time plane "
        "with straight characteristics converging to a single point at time "
        "one, a thick shock line continuing from it, and a fan of "
        "characteristics spreading from the jump at x = 2.",
        width=640.0, height=346.0)

    top = Frame(62, 54, 500, 92, -0.7, 3.95, -0.12, 1.22)
    scene.panel_title(24, 40, "the profile")
    top.axes(scene, origin_y=0.0)
    scene.math(top.x0 + 5, top.y0 + 10, r"u", anchor="start", size=10, fill="muted")
    for level in (0.0, 1.0):
        scene.line(top.x0 - 3, top.Y(level), top.x0, top.Y(level), stroke="muted",
                   sw=SW_AXIS)
        scene.tick_label(top.x0 - 7, top.Y(level) + 3.5, q2(level), anchor="end",
                         size=9.5)
    for index, t in enumerate(profile_times):
        role = ("muted", "accent2", "accent")[index]
        if t == 0:
            points = [(-0.7, 1), (0, 1), (1, 0), (fan_at, 0),
                      (fan_at, 1), (3.95, 1)]
        elif t < breaking:
            points = [(-0.7, 1), (t, 1), (1, 0), (fan_at, 0),
                      (fan_at + t, 1), (3.95, 1)]
        else:
            points = [(-0.7, 1), (shock(t), 1), (shock(t), 0),
                      (fan_at, 0), (fan_at + t, 1), (3.95, 1)]
        scene.path(top.curve(points), stroke=role, sw=SW_CURVE2 if index else 1.2,
                   dash=DASH if index == 0 else "")
        scene.math(top.right + 8, top.Y(1.0) + 4 + index * 14, f"t={q2(t)}", t=f"t = {q2(t)}",
                   anchor="start", fill=role, size=9.5)

    plane = Frame(62, 176, 500, 128, -0.7, 3.95, 0.0, t_max)
    scene.panel_title(24, 162, "the characteristics")
    plane.axes(scene, x_label="x", origin_y=0.0)
    # Inside the panel, not above the axis: "the characteristics" is set at the
    # left margin and reaches past the axis, and the tick at t = 1.6 takes the
    # place to the left of it. The top left of the plane is empty because every
    # characteristic moves right.
    scene.math(plane.x0 + 6, plane.y0 + 12, r"t", anchor="start", fill="muted",
               italic=True)
    for value in profile_times[1:]:
        scene.line(plane.x0, plane.Y(value), plane.right, plane.Y(value),
                   stroke="muted", sw=SW_AXIS, dash=DOT)
        scene.tick_label(plane.x0 - 6, plane.Y(value) + 3.5, q2(value),
                         anchor="end", size=9.5)
    scene.line(plane.x0, plane.Y(breaking), plane.right, plane.Y(breaking),
               stroke="muted", sw=SW_AXIS, dash=DOT)
    scene.tick_label(plane.x0 - 6, plane.Y(breaking) + 3.5, q2(breaking),
                     anchor="end", size=9.5)
    for tick in (0.0, 1.0, 2.0, 3.0):
        scene.line(plane.X(tick), plane.bottom, plane.X(tick), plane.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(plane.X(tick), plane.bottom + 16, q2(tick), size=9.5)

    def stop(x0: float, speed: float) -> float:
        """Where a characteristic ends: at the shock, or at the top of the panel.

        The ones off the ramp all reach the same point at the breaking time.
        The others run until the shock swallows them, which is the whole content
        of the entropy condition: characteristics enter a shock, never leave it.
        """
        if 0.0 <= x0 <= 1.0:
            return breaking
        gap = speed - shock_speed
        if abs(gap) > 1e-12:
            meeting = (1.0 - shock_speed * breaking - x0) / gap
            if breaking <= meeting <= t_max:
                return meeting
        return t_max

    starts = [-0.6, -0.3, 0.0, 0.15, 0.3, 0.45, 0.6, 0.75, 0.9, 1.0, 1.2, 1.4,
              1.6, 1.8]
    for x0 in starts:
        speed = initial(x0 + 1e-9)
        end = stop(x0, speed)
        scene.path(plane.curve([(x0, 0.0), (x0 + speed * end, end)]),
                   stroke="muted", sw=SW_AXIS)
    for index in range(6):
        speed = index / 5.0
        scene.path(plane.curve([(fan_at, 0.0), (fan_at + speed * t_max, t_max)]),
                   stroke="accent2", sw=SW_AXIS)
    scene.path(plane.curve([(1.0, breaking), (shock(t_max), t_max)]),
               stroke="accent", sw=2.6)
    scene.circle(plane.X(1.0), plane.Y(breaking), 3.4, fill="accent")
    scene.math(plane.X(-0.65), plane.Y(breaking) + 15,
               rf"\text{{first crossing at }}t={q3(breaking)}", t=f"first crossing at t = {q3(breaking)}", anchor="start",
               fill="accent", size=9.5, halo=True)
    scene.math(plane.X(shock(t_max)) + 8, plane.Y(t_max) + 4,
               rf"\text{{shock speed }}{q2(shock_speed)}", t=f"shock, speed {q2(shock_speed)}", anchor="start", fill="accent",
               size=9.5, halo=True)
    # Below the first gridline and to the right of the widest ray, so neither
    # the dotted line at t = 0.6 nor a characteristic crosses the words.
    scene.text(plane.X(fan_at + 0.55) + 4, plane.Y(0.35), "rarefaction fan",
               anchor="start", fill="accent2", size=9.5, halo=True)
    scene.text(62, 338, "the ramp compresses, the jump up spreads: the same "
               "equation, opposite behaviour", anchor="start", fill="muted",
               size=9.5)
    return scene


# --- zooming coordinates -----------------------------------------------------

def fig_axisymmetric_meridional_flow() -> Scene:
    """The exact strain flow from Ψ(s,z)=z: radial contraction preserves volume.

    With zero swirl the Cartesian velocity is (-x,-y,2z). Its flow map is
    diag(exp(-t),exp(-t),exp(2t)), whose determinant is one. Meridional
    trajectories preserve r²z; a material cylinder preserves 2πR²H.
    No time stepping or Euler-profile data enter this illustration.
    """
    duration = "10s"
    end = 0.8
    times = [end * k / 32 for k in range(33)]
    # Move forward, hold the last frame, then restart. Never reverse physical time.
    key_times = [0.86 * k / 32 for k in range(33)] + [1.0]

    def motion(attribute: str, values: list[str]) -> dict:
        return anim(attribute, values + [values[-1]], duration,
                    times=key_times, ease=False)

    def particle(r: float, z: float, t: float) -> tuple[float, float]:
        return r * math.exp(-t), z * math.exp(2 * t)

    radius, half_height = 0.95, 0.34
    for t in times:
        r, h = particle(radius, half_height, t)
        if abs(2 * math.pi * r * r * h
               - 2 * math.pi * radius * radius * half_height) > 1e-12:
            raise SystemExit("axisymmetric-meridional-flow: volume changed")
        if abs(math.exp(-t) ** 2 * math.exp(2 * t) - 1) > 1e-12:
            raise SystemExit("axisymmetric-meridional-flow: Jacobian is not one")
        for r0, z0 in ((0.6, -0.2), (1.13, 0.36), (0.0, 0.1)):
            rt, zt = particle(r0, z0, t)
            if abs(rt * rt * zt - r0 * r0 * z0) > 1e-12:
                raise SystemExit("axisymmetric-meridional-flow: wrong streamline")
            step = 1e-5
            before, after = particle(r0, z0, t - step), particle(r0, z0, t + step)
            if (abs((after[0] - before[0]) / (2 * step) + rt) > 1e-8
                    or abs((after[1] - before[1]) / (2 * step) - 2 * zt) > 1e-8):
                raise SystemExit("axisymmetric-meridional-flow: wrong particle velocity")

    scene = Scene(
        "axisymmetric-meridional-flow",
        "Squeeze the radius, stretch the height",
        r"Take the smooth reduced streamfunction \(\Psi(s,z)=z\), with \(s=r^2\) and zero swirl. "
        r"The meridional velocity is \((-r,2z)\). Dots follow \(r(t)=r_0e^{-t}\) and "
        r"\(z(t)=z_0e^{2t}\); the curves trace their paths. Revolving the cross-section about "
        r"the axis gives the material cylinder at right. Its radius \(R\) shrinks and its "
        r"half-height \(H\) grows, preserving the volume \(2\pi R^2H\). Meridional area alone is "
        r"not volume: the three-dimensional measure carries the radial factor \(2\pi r\). Faint "
        r"outlines retain the initial and final cylinders when motion is paused. "
        r"The three Cartesian stretch factors are \(e^{-t},e^{-t},e^{2t}\), whose "
        r"product is \(\det D\Phi_t=1\). This linear flow illustrates incompressibility; "
        r"it is not the manuscript's profile.",
        "Left: the r,z half-plane, with the symmetry axis vertical. Six particles "
        "move inward and away from z=0 along curves r²z=constant. Right: an "
        "axisymmetric cylinder becomes narrower and taller. Faint outlines show "
        "t=0 and t=0.8. With radius R and half-height H, its volume 2πR²H "
        "does not change. The animation moves "
        "forward, holds, and restarts; the streamlines and both outlines remain visible.",
        width=640, height=444)

    scene.panel_title(28, 34, "follow a ring of particles")
    scene.panel_title(352, 34, "the same material volume")
    frame = Frame(58, 80, 244, 234, 0, 1.35, -2.2, 2.2)
    frame.axes(scene, x_label="r", origin_y=0)
    scene.math(frame.x0 - 9, frame.y0 - 12, r"z", fill="muted", italic=True)
    scene.math(frame.x0, 59, r"\text{axis }r=0", t='axis r = 0', anchor="start", fill="muted", size=12)
    for z in (-2, -1, 1, 2):
        scene.line(frame.x0 - 4, frame.Y(z), frame.x0, frame.Y(z),
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(frame.x0 - 9, frame.Y(z) + 4, str(z),
                         anchor="end", size=12)
    for r in (0.5, 1.0):
        scene.tick_label(frame.X(r), frame.Y(0) + 17, q2(r), size=12)

    for z0 in (-0.36, -0.22, -0.09, 0.09, 0.22, 0.36):
        role = "accent" if z0 > 0 else "accent2"
        path_times = [-0.04 + 0.88 * k / 80 for k in range(81)]
        points = [particle(1.13, z0, t) for t in path_times]
        scene.path(frame.curve(points), stroke=role, sw=SW_CURVE2, sop=0.5)
        a, b = frame.project([particle(1.13, z0, t) for t in (0.66, 0.74)])
        scene.area(arrow_head(*b, b[0] - a[0], b[1] - a[1], size=5), fill=role)
        traced = frame.project([particle(1.13, z0, t) for t in times])
        scene.circle(*traced[-1], 2, fill=role, op=0.35)
        scene.circle(*traced[0], 3.5, fill=role,
                     anim=[motion("cx", [q2(x) for x, _ in traced]),
                           motion("cy", [q2(y) for _, y in traced])])

    # A rectangle in the meridian is the section of the cylinder drawn at right.
    def section(t: float) -> str:
        r, h = particle(radius, half_height, t)
        return poly_path(frame.project([(0, -h), (r, -h), (r, h), (0, h)])) + "Z"

    for t in (0.0, end):
        scene.path(section(t), stroke="muted", sw=SW_AXIS, dash=DASH, sop=0.65)
    sections = [section(t) for t in times]
    scene.path(sections[0], stroke="accent", fill="band", sw=SW_CURVE2,
               anim=[motion("d", sections)])

    cx, cy = 466.0, 196.0
    radial_pixels, axial_pixels, perspective = 86.0, 57.0, 0.26

    def cylinder(t: float) -> tuple[str, str]:
        r, h = particle(radius, half_height, t)
        rx, hy = radial_pixels * r, axial_pixels * h
        ry = perspective * rx
        rings = []
        for y in (cy - hy, cy + hy):
            ring = [(cx + rx * math.cos(2 * math.pi * k / 32),
                     y + ry * math.sin(2 * math.pi * k / 32)) for k in range(33)]
            rings.append(poly_path(ring))
        sides = (poly_path([(cx - rx, cy - hy), (cx - rx, cy + hy)])
                 + poly_path([(cx + rx, cy - hy), (cx + rx, cy + hy)]))
        front_top = [(cx + rx * math.cos(math.pi * k / 24),
                      cy - hy + ry * math.sin(math.pi * k / 24)) for k in range(25)]
        front_bottom = [(x, y + 2 * hy) for x, y in reversed(front_top)]
        return "".join(rings) + sides, poly_path(front_top + front_bottom) + "Z"

    scene.line(cx, 78, cx, 314, stroke="muted", sw=SW_AXIS, dash=DOT)
    for t in (0.0, end):
        wire, _ = cylinder(t)
        scene.path(wire, stroke="muted", sw=SW_AXIS, sop=0.5)
    cylinders = [cylinder(t) for t in times]
    scene.area(cylinders[0][1], fill="band",
               anim=[motion("d", [fill for _, fill in cylinders])])
    scene.path(cylinders[0][0], stroke="accent", sw=SW_CURVE,
               anim=[motion("d", [wire for wire, _ in cylinders])])
    scene.math(570, 196, r"t = 0", anchor="start", fill="muted", size=12)
    scene.math(518, 95, r"t = 0.8", anchor="start", fill="muted", size=12)
    scene.math(564, 256, r"e^{2t}", t="axial stretch e^(2t)",
               fill="accent2", size=13)
    scene.math(466, 322, r"e^{-t}\quad e^{-t}", t="two horizontal factors e^(-t)",
               fill="accent2", size=12)
    scene.math(58, 346, r"\dot r=-r,\quad\dot z=2z", t='radial speed −r; axial speed 2z', anchor="start", size=12)
    scene.math(58, 366, r"r^2z=\text{constant}", t='r^2 z stays constant', anchor="start",
               fill="muted", size=12)
    scene.math(352, 346, r"R=R_0e^{-t}", t='R = R_0 exp(−t)', anchor="start", size=12)
    scene.math(352, 366, r"H=H_0e^{2t}", t='H = H_0 exp(2t)', anchor="start", size=12)
    scene.math(352, 388, r"V=2\pi R^2H=V_0", t='volume = 2πR^2 H', anchor="start", fill="accent", size=13)
    scene.math(58, 430, r"t:0\to0.8\text{, then repeat}", t='t: 0 → 0.8, then repeat', anchor="start",
               fill="muted", size=11)
    scene.math(352, 422, r"\det D\Phi_t=e^{-t}e^{-t}e^{2t}=1",
               t="volume factor = e^(-t) e^(-t) e^(2t) = 1",
               anchor="start", fill="accent", size=12)
    if len(json.dumps(scene.to_json(), ensure_ascii=False).encode("utf8")) > 150_000:
        raise SystemExit("axisymmetric-meridional-flow: drawing model exceeds 150 kB")
    return scene




# --- how a minimizer is obtained ---------------------------------------------

def fig_stability_cost() -> Scene:
    """The bootstrap radius trades nonlinear work against fixed residual work."""
    nonlinear, residual, damping = 1.0, 0.04, 0.5
    discriminant = damping ** 2 - 4 * nonlinear * residual
    roots = ((damping - math.sqrt(discriminant)) / (2 * nonlinear),
             (damping + math.sqrt(discriminant)) / (2 * nonlinear))
    balance = math.sqrt(residual / nonlinear)

    def cost(radius: float) -> float:
        return nonlinear * radius + residual / radius

    if any(abs(cost(r) - damping) > 1e-12 for r in roots):
        raise SystemExit("stability-cost: the threshold intersections are wrong")
    if not roots[0] < balance < roots[1] or abs(cost(balance) - 0.4) > 1e-12:
        raise SystemExit("stability-cost: the balancing radius is wrong")

    scene = Scene(
        "stability-cost",
        "Why a smaller bootstrap radius is not always better",
        r"Suppose the perturbation energy obeys "
        r"\(\tfrac12\,d(E^2)/ds\le-\Lambda_{\mathrm{stab}}E^2+\Lambda_3E^3+\Lambda_R E\). "
        r"At a positive boundary \(E=\delta\), divide by \(\delta^2\): damping must "
        r"exceed the combined cost \(\Lambda_3\delta+\Lambda_R/\delta\). "
        r"The rising line is nonlinear work; the falling dashed curve is the relative cost "
        r"of a fixed reference residual. Their sum has a minimum at "
        r"\(\delta=\sqrt{\Lambda_R/\Lambda_3}\). This teaching example uses "
        r"\(\Lambda_3=1\), \(\Lambda_R=0.04\), and \(\Lambda_{\mathrm{stab}}=0.5\), "
        r"so the minimum is \(0.4\) at \(\delta=0.2\), and the strict inward-pointing "
        r"inequality holds exactly for \(0.1<\delta<0.4\). Equality at the open "
        r"endpoints does not give a strict margin. With initial energy below such a "
        r"radius, continuity and a valid energy estimate exclude a first crossing. "
        r"Every other hypothesis, including radius-dependent estimates and the "
        r"interval of existence, still applies. These coefficients are illustrative; "
        r"they are not certified profile bounds for the De Gregorio application.",
        "The combined cost delta plus 0.04/delta is U-shaped. It falls below the "
        "horizontal damping threshold 0.5 between the open endpoints delta=0.1 "
        "and delta=0.4. The minimum is 0.4 at delta=0.2. Separate rising and "
        "falling curves show the nonlinear and residual contributions. All "
        "coefficients are explicitly labelled as teaching values.",
        width=640, height=424)
    scene.panel_title(28, 32, "a radius must leave room for both costs")
    scene.math(28, 57,
               r"\text{teaching values: }\Lambda_3=1,\quad\Lambda_R=0.04,\quad"
               r"\Lambda_{\mathrm{stab}}=0.5",
               t="teaching values: nonlinear 1, residual 0.04, damping 0.5",
               anchor="start", fill="muted", size=12)
    frame = Frame(66, 110, 526, 190, 0, 0.62, 0, 1.15)
    frame.axes(scene, x_label=r"\delta", y_label="cost", origin_y=0)
    # Shade only between the sum and the threshold, not the entire strip:
    # its vertical thickness is exactly the available damping margin.
    inside = [roots[0] + (roots[1] - roots[0]) * k / 160 for k in range(161)]
    scene.area(frame.band([(r, cost(r)) for r in inside],
                          [(r, damping) for r in inside]), fill="band")
    for value in (0.5, 1):
        scene.tick_label(frame.x0 - 10, frame.Y(value) + 4, q2(value),
                         anchor="end", size=11)
    for value in (0, 0.1, 0.2, 0.4, 0.6):
        scene.line(frame.X(value), frame.bottom, frame.X(value), frame.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(frame.X(value), frame.bottom + 20, q2(value), size=11)
    radii = [0.04 + 0.56 * k / 260 for k in range(261)]
    scene.path(frame.curve([(r, nonlinear * r) for r in (0, 0.6)]),
               stroke="accent2", sw=SW_CURVE2)
    scene.path(frame.curve([(r, residual / r) for r in radii]),
               stroke="warn", sw=SW_CURVE2, dash=DASH)
    scene.path(frame.curve([(r, cost(r)) for r in radii]), stroke="accent")
    for x, role, label in ((66, "accent2", r"\Lambda_3\delta"),
                           (220, "warn", r"\Lambda_R/\delta"),
                           (404, "accent", r"\Lambda_3\delta+\Lambda_R/\delta")):
        scene.line(x, 84, x + 24, 84, stroke=role,
                   dash=DASH if role == "warn" else "")
        scene.math(x + 31, 88, label, anchor="start", fill=role, size=12)
    scene.line(frame.x0, frame.Y(damping), frame.right, frame.Y(damping),
               stroke="ink", sw=SW_CURVE2, dash=DASH)
    scene.math(frame.right, frame.Y(damping) + 19,
               r"\text{damping }=0.5", anchor="end", size=12, halo=True)
    for r in roots:
        scene.line(frame.X(r), frame.Y(damping), frame.X(r), frame.bottom,
                   stroke="muted", sw=SW_AXIS, dash=DOT)
        scene.circle(frame.X(r), frame.Y(damping), 3.5,
                     fill="surface", stroke="accent", sw=SW_CURVE2)
    scene.circle(frame.X(balance), frame.Y(cost(balance)), 3.5, fill="accent")
    scene.math(frame.X(balance) + 10, frame.Y(cost(balance)) + 16,
               r"\min=0.4", anchor="start", fill="accent", size=12, halo=True)
    scene.line(frame.X(roots[0]), 344, frame.X(roots[1]), 344,
               stroke="accent", sw=3)
    for r in roots:
        scene.circle(frame.X(r), 344, 3.5, stroke="accent", fill="surface")
    scene.math(frame.X((roots[0] + roots[1]) / 2), 368,
               r"0.1<\delta<0.4", fill="accent", size=13)
    scene.text(420, 350, "strict inward margin", anchor="start", fill="accent",
               size=11)
    scene.math(320, 403,
               r"\delta_{\mathrm{balance}}=0.2\quad"
               r"\text{(other radius hypotheses still apply)}",
               t="balancing radius 0.2; other radius hypotheses still apply",
               fill="muted", size=12)
    return scene


def fig_direct_method() -> Scene:
    """Coercivity, a minimizing sequence, oscillation, and the inequality."""
    def energy(x: float) -> float:
        return 0.3 * x ** 4 - 0.8 * x * x + 0.12 * x + 0.9

    a, b = -1.5, -1.0
    for _ in range(60):
        c = (a + b) / 2
        if 1.2 * c ** 3 - 1.6 * c + 0.12 < 0:
            a = c
        else:
            b = c
    minimizer = (a + b) / 2
    lowest = energy(minimizer)
    sequence = [minimizer + (-0.62) ** k * 1.15 for k in range(1, 5)]
    values = [energy(x) for x in sequence]
    if values != sorted(values, reverse=True):
        raise SystemExit("direct-method: the sequence is not minimizing")
    level = values[0]
    def outer_crossing(outside, inside):
        for _ in range(60):
            middle = (outside + inside) / 2
            if energy(middle) > level:
                outside = middle
            else:
                inside = middle
        return outside

    # Round outwards for the displayed enclosure; this is numerical geometry,
    # not a Lean certificate for the quartic's sublevel set.
    sublevel = (math.floor(1000 * outer_crossing(-2.4, 0)) / 1000,
                math.ceil(1000 * outer_crossing(2.4, 0)) / 1000)

    def wave(k: int, x: float) -> float:
        return math.sin(2.0 * math.pi * k * x)

    modes = (1, 2, 4)
    pairings = [integrate_mid(lambda x, k=k: x * wave(k, x), 0.0, 1.0, 6000)
                for k in modes]
    norms = [integrate_mid(lambda x, k=k: wave(k, x) ** 2, 0.0, 1.0, 6000)
             for k in modes]
    if max(abs(n - 0.5) for n in norms) > 1e-9:
        raise SystemExit("direct-method: the oscillations are not normalized")
    if max(abs(p + 1.0 / (2.0 * math.pi * k))
           for p, k in zip(pairings, modes)) > 1e-6:
        raise SystemExit("direct-method: the pairings are not the exact ones")

    scene = Scene(
        "direct-method",
        "Coercivity, weak convergence, and the inequality that survives",
        r"Left: four samples approach the global minimum of the displayed coercive quartic "
        r"\(J\). The critical point is located by bisection, and the shaded sublevel enclosure "
        r"is rounded outwards; these numerical values are not a certificate. Coercivity bounds a "
        r"minimizing sequence, allowing a weakly convergent subsequence in a reflexive Banach "
        r"space. Right: a separate energy \(E(v)=\int_0^1v^2\) illustrates what weak convergence "
        r"preserves. The sequence \(u_k(x)=\sin(2\pi kx)\) converges weakly to zero in "
        r"\(L^2(0,1)\). Its pairing against \(x\) is \(-1/(2\pi k)\), shown for \(k=1,2,4\). For "
        r"an arbitrary \(L^2\) test, Bessel's inequality makes the sine coefficients tend to "
        r"zero; one test alone would not prove weak convergence. Yet \(E(u_k)=1/2\), while "
        r"\(E(0)=0\). This is weak lower semicontinuity, \(E(u)\le\liminf_k E(u_k)\), with a "
        r"strict gap. The chain below assumes a nonempty weakly closed admissible class in a "
        r"reflexive space, finite infimum, coercivity, and weak lower semicontinuity.",
        "Left, a quartic energy curve with four marked points of a minimizing "
        "sequence descending toward its lowest point, a dotted line at the "
        "infimum, and a shaded interval on the axis showing that the sublevel "
        "set is bounded. Right, three sine waves of increasing frequency around "
        "a thick line at zero, their weak limit, with the pairings against x "
        "printed and shrinking. Below, four boxes in a row: coercivity, weak "
        "compactness, lower semicontinuity, a minimizer.",
        width=640.0, height=356.0)

    # The frame is taller than the well and wider than the sublevel set, so the
    # energy leaves through the top of the panel on both sides. That is what
    # coercivity says. The curve is sampled between the two points where it
    # crosses the top of the panel, found by bisection, so it ends exactly on
    # the edge instead of running off the drawing.
    left = Frame(52, 76, 244, 150, -2.6, 2.6, lowest - 0.17, level + 0.32)

    def leaves(outside: float, inside: float) -> float:
        """Where the energy crosses the top of the panel, between two points."""
        for _ in range(60):
            middle = 0.5 * (outside + inside)
            if energy(middle) > left.ymax:
                outside = middle
            else:
                inside = middle
        return 0.5 * (outside + inside)

    first, last = leaves(left.xmin, 0.0), leaves(left.xmax, 0.0)
    scene.panel_title(24, 46, "coercivity bounds the sequence")
    scene.math(24, 62, r"J(u)=0.3u^4-0.8u^2+0.12u+0.9", t='J(u) = 0.3u⁴ − 0.8u² + 0.12u + 0.9',
               anchor="start", fill="muted", size=FS_LABEL)
    left.axes(scene, x_label="u")
    scene.math(left.x0 + 5, left.y0 + 11, r"J", anchor="start", fill="muted",
               italic=True, size=FS_LABEL)
    scene.rect(left.X(sublevel[0]), left.bottom - 5,
               left.X(sublevel[1]) - left.X(sublevel[0]), 10, fill="band")
    scene.path(left.curve([(x, energy(x)) for x in
                           (first + (last - first) * k / 400.0
                            for k in range(401))]),
               stroke="accent", sw=SW_CURVE)
    scene.line(left.x0, left.Y(level), left.right, left.Y(level), stroke="muted",
               sw=SW_AXIS, dash=DASH)
    scene.math(left.X(0.0), left.Y(level) - 6, rf"J(u_1)\approx{q3(level)}", t=f"J(u₁) ≈ {q3(level)}",
               fill="muted", size=9.5, halo=True)
    scene.line(left.x0, left.Y(lowest), left.right, left.Y(lowest),
               stroke="accent2", sw=SW_AXIS, dash=DOT)
    scene.math(left.right - 2, left.Y(lowest) - 6, rf"\inf J\approx{q3(lowest)}", t=f"inf J ≈ {q3(lowest)}",
               anchor="end", fill="accent2", size=9.5, halo=True)
    for index, (x, value) in enumerate(zip(sequence, values)):
        scene.circle(left.X(x), left.Y(value), 3.0, fill="ink")
        name = f"u_{index + 1}"
        # On the steep flank the curve runs almost vertically through the space
        # above the point, so the name goes beside the point instead of over it.
        if abs(1.2 * x ** 3 - 1.6 * x + 0.12) > 3.0:
            scene.math(left.X(x) + 6, left.Y(value) - 5, name, anchor="start",
                       fill="ink", size=9.5, halo=True)
        else:
            scene.math(left.X(x), left.Y(value) - 9, name, fill="ink", size=9.5,
                       halo=True)
    scene.circle(left.X(minimizer), left.Y(lowest), 3.6, stroke="accent2",
                 fill="surface", sw=1.4)
    scene.line(left.X(minimizer), left.Y(lowest) + 4, left.X(minimizer),
               left.bottom, stroke="accent2", sw=SW_AXIS, dash=DOT)
    scene.tick_label(left.X(minimizer), left.bottom + 16, r"u_*", fill="accent2",
                     size=9.5)
    scene.math(left.X(0.0), left.bottom + 31,
               rf"\text{{sublevel enclosure: }}[{q3(sublevel[0])},{q3(sublevel[1])}]",
               fill="muted", size=9.5)

    # The waves reach 1, the panel reaches 1.45, and the strip between the two
    # is where the key for the flat line goes: every point of the panel near
    # u = 0 has three sine curves crossing it.
    right = Frame(350, 76, 244, 150, 0.0, 1.0, -1.45, 1.45)
    scene.panel_title(322, 46, "weak limits can lower energy")
    scene.math(322, 62, r"u_k=\sin(2\pi kx),\quad k=1,2,4", t='uₖ = sin(2πkx), k = 1, 2, 4', anchor="start",
               fill="muted", size=FS_LABEL)
    right.axes(scene, x_label="x", origin_y=-1.45)
    for index, k in enumerate(modes):
        scene.path(right.curve([(x, wave(k, x)) for x in
                                (m / 480.0 for m in range(481))]),
                   stroke="muted" if index < 2 else "accent2",
                   sw=SW_AXIS if index < 2 else SW_CURVE2)
    scene.line(right.x0, right.Y(0.0), right.right, right.Y(0.0),
               stroke="accent", sw=SW_CURVE)
    scene.line(right.x0 + 6, right.y0 + 11, right.x0 + 22, right.y0 + 11,
               stroke="accent", sw=SW_CURVE)
    scene.math(right.x0 + 27, right.y0 + 14.5, r"\text{weak limit }u=0", t='the weak limit, u = 0',
               anchor="start", fill="accent", size=9.5)
    scene.math(350, 252, rf"\int_0^1 xu_k\,dx\approx {q3(pairings[0])},"
               rf"{q3(pairings[1])},{q3(pairings[2])}\to0", anchor="start", fill="muted",
               size=9.5)
    scene.math(350, 270, r"E(v)=\int_0^1v^2\,dx,\quad E(u_k)=1/2",
               anchor="start", fill="muted", size=9.5)
    scene.math(350, 288, r"E(u)=0<\liminf_k E(u_k)=1/2", t='E(u) = 0 < lim inf E(u_k) = 1/2',
               anchor="start", fill="accent2", size=9.5)

    chain = [("coercivity", 104.0), ("weak compactness", 136.0),
             ("lower semicontinuity", 152.0), ("a minimizer", 98.0)]
    x = 52.0
    edges = []
    for head, box_width in chain:
        role = "accent" if head == "a minimizer" else "ink"
        draw_box(scene, x, 304, box_width, 26, head, role=role)
        edges.append((x, x + box_width))
        x += box_width + 26.0
    for (_, end), (start, _) in zip(edges, edges[1:]):
        draw_arrow(scene, [(end + 5, 317), (start - 2, 317)], role="muted")
    scene.text(320, 346, "reflexive space; nonempty weakly closed admissible class",
               fill="muted", size=9.5)
    return scene


# --- interval arithmetic -----------------------------------------------------

def rational_bump(x: float) -> float:
    """x/(1 + x²), a rational example with a dependency overestimate."""
    return x / (1.0 + x * x)


def square_interval(lo: float, hi: float) -> tuple[float, float]:
    """The interval square, which is not the interval times itself."""
    if lo >= 0.0:
        return (lo * lo, hi * hi)
    if hi <= 0.0:
        return (hi * hi, lo * lo)
    return (0, max(lo * lo, hi * hi))


def naive_enclosure(lo: float, hi: float) -> tuple[Fraction, Fraction]:
    """Exact rational interval arithmetic for the displayed rational inputs."""
    lo, hi = Fraction(str(lo)), Fraction(str(hi))
    slo, shi = square_interval(lo, hi)
    rlo, rhi = Fraction(1, 1 + shi), Fraction(1, 1 + slo)
    products = (lo * rlo, lo * rhi, hi * rlo, hi * rhi)
    return (min(products), max(products))


def boxes_at(count: int, lo: float = -2.0, hi: float = 2.0):
    """One naive enclosure per piece of a uniform subdivision."""
    out = []
    for index in range(count):
        a = lo + (hi - lo) * index / count
        b = lo + (hi - lo) * (index + 1) / count
        out.append((a, b) + naive_enclosure(a, b))
    return out


def fig_interval_enclosure() -> Scene:
    """The overestimate of interval arithmetic, and what subdivision buys."""
    counts = (4, 8, 16, 32)
    families = [boxes_at(count) for count in counts]
    hulls = [(min(box[2] for box in family), max(box[3] for box in family))
             for family in families]
    single = naive_enclosure(-2.0, 2.0)
    square = square_interval(-2.0, 2.0)
    denominator = (1.0 + square[0], 1.0 + square[1])
    # The range and the two points that attain it come out of the function, so
    # the caption cannot name the wrong end. The derivative
    # (1 - x²)/(1 + x²)² vanishes at ±1, and those are the only interior
    # critical points, so the grid search finds them exactly.
    grid = [-2.0 + 4.0 * k / 20000.0 for k in range(20001)]
    argmin = min(grid, key=rational_bump)
    argmax = max(grid, key=rational_bump)
    sharp = (rational_bump(argmin), rational_bump(argmax))
    if abs(argmin + 1.0) > 1e-9 or abs(argmax - 1.0) > 1e-9:
        raise SystemExit("interval-enclosure: the range is attained away from "
                         "the critical points of x/(1 + x²)")
    if abs(single[0] + 2.0) > 1e-12 or abs(hulls[0][0] + 1.0) > 1e-12:
        raise SystemExit("interval-enclosure: the hulls are not the computed ones")
    if any(hull[0] > sharp[0] + 1e-12 or hull[1] < sharp[1] - 1e-12
           for hull in hulls):
        raise SystemExit("interval-enclosure: an enclosure misses the range")
    widths = [hull[1] - hull[0] for hull in hulls]
    if any(later >= earlier for earlier, later in zip(widths, widths[1:])):
        raise SystemExit("interval-enclosure: the enclosures do not tighten")
    if abs((single[1] - single[0]) / (sharp[1] - sharp[0]) - 4.0) > 1e-12:
        raise SystemExit("interval-enclosure: the naive box is not four times "
                         "the range")

    def enclosure_text(hull):
        # Outward decimal rounding preserves the enclosure printed to readers.
        lo = math.floor(hull[0] * 1000) / 1000
        hi = math.ceil(hull[1] * 1000) / 1000
        return f"[{q3(lo)}, {q3(hi)}]"

    scene = Scene(
        "interval-enclosure",
        "What interval arithmetic overestimates, and what subdivision buys",
        r"The function \(f(x)=x/(1+x^2)\) on \([-2,2]\) has exact range \([-1/2,1/2]\), attained "
        r"at \(x=-1\) and \(x=1\). Left: one interval evaluation gives \([0,4]\) for the square, "
        r"\([1,5]\) for the denominator, and \([-2,2]\) for the quotient, four times the height "
        r"of the true range. The slack comes from treating the two occurrences of \(x\) "
        r"independently. Right: subdivide the input, evaluate each piece, and take the union. At "
        r"four, eight, sixteen, and thirty-two pieces, the enclosing hull tightens from "
        r"\([-1,1]\) to \([-0.567,0.567]\), always containing the dashed range. These interval "
        r"operations use exact rational arithmetic; printed decimal endpoints are rounded "
        r"outwards. Subdivision reduces dependency error here at the cost of more evaluations. A "
        r"checked CAS enclosure additionally supplies a proof connecting the arithmetic bounds "
        r"to every value of the original expression on its domain.",
        "Two panels at the same scale. Left, one tall shaded box containing the "
        "whole graph of a small function, showing how loose a single interval "
        "evaluation is. Right, the same curve under a row of much shorter boxes "
        "that refine in four steps, with the enclosing interval printed and "
        "shrinking toward two dashed lines that mark the true range.",
        width=640.0, height=306.0)

    def panel(x0: float, title: str, subtitle: str) -> Frame:
        frame = Frame(x0, 84, 240, 150, -2.25, 2.25, -2.3, 2.3)
        scene.panel_title(x0 - 28, 46, title)
        scene.text(x0 - 28, 62, subtitle, anchor="start", fill="muted",
                   size=FS_LABEL)
        # The boxes straddle the line y = 0, so the axis goes along the bottom
        # of the panel and the zero level is a tick on the vertical axis. An
        # axis drawn through the middle would be buried under the enclosures.
        frame.axes(scene, x_label="x")
        for tick in (-2.0, -1.0, 0.0, 1.0, 2.0):
            scene.line(frame.X(tick), frame.bottom, frame.X(tick),
                       frame.bottom + 4, stroke="muted", sw=SW_AXIS)
            scene.tick_label(frame.X(tick), frame.bottom + 15, num(tick),
                             size=9.5)
        for level in (-2.0, -1.0, 0.0, 1.0, 2.0):
            scene.line(frame.x0 - 3, frame.Y(level), frame.x0, frame.Y(level),
                       stroke="muted", sw=SW_AXIS)
            scene.tick_label(frame.x0 - 7, frame.Y(level) + 3.5, num(level),
                             anchor="end", size=9.5)
        return frame

    def draw_range(frame: Frame) -> None:
        for edge in sharp:
            scene.line(frame.x0, frame.Y(edge), frame.right, frame.Y(edge),
                       stroke="accent2", sw=SW_AXIS, dash=DASH)

    def draw_curve(frame: Frame) -> None:
        scene.path(frame.curve([(x, rational_bump(x)) for x in
                                (-2.0 + 4.0 * k / 240.0 for k in range(241))]),
                   stroke="accent", sw=SW_CURVE)

    one = panel(80, "one evaluation", "the input taken whole")
    scene.rect(one.X(-2.0), one.Y(single[1]), one.X(2.0) - one.X(-2.0),
               one.Y(single[0]) - one.Y(single[1]), stroke="muted", fill="band",
               sw=SW_CURVE2)
    draw_range(one)
    draw_curve(one)
    scene.math(one.X(0.0), one.Y(1.45), f"[{q3(single[0])},{q3(single[1])}]", t=f"[{num(single[0])}, {num(single[1])}]",
               fill="ink", size=FS_LABEL, halo=True)
    scene.text(one.X(0.0), one.Y(1.45) + 14, "a coarse enclosure", fill="muted",
               size=9.5, halo=True)
    scene.math(one.X(-1.9), one.Y(sharp[0]) + 13,
               rf"\text{{range }}[{q3(sharp[0])},{q3(sharp[1])}]", t=f"the range, [{num(sharp[0])}, {num(sharp[1])}]", anchor="start",
               fill="accent2", size=9.5, halo=True)

    many = panel(360, "subdivided", "the union over the pieces")
    for index, family in enumerate(families):
        pieces = "".join(
            poly_path([(many.X(a), many.Y(hi)), (many.X(b), many.Y(hi)),
                       (many.X(b), many.Y(lo)), (many.X(a), many.Y(lo))]) + "Z"
            for a, b, lo, hi in family)
        scene.path(pieces, stroke="muted", sw=0.6, fill="band",
                   op=1.0 if index == 0 else 0.0,
                   anim=[slot(index, len(families))])
    draw_range(many)
    draw_curve(many)
    for index, (count, hull) in enumerate(zip(counts, hulls)):
        scene.math(many.X(0.0), many.Y(1.55),
                   rf"{count}\text{{ pieces: }}{enclosure_text(hull)}", t=f"{count} pieces: {enclosure_text(hull)}",
                   fill="ink", size=FS_LABEL, halo=True,
                   op=1.0 if index == 0 else 0.0,
                   anim=[slot(index, len(families))])
    scene.math(52, 274, rf"1\text{{ box: }}[{q3(single[0])},{q3(single[1])}]"
               rf"\qquad {counts[-1]}\text{{ boxes: }}{enclosure_text(hulls[-1])}",
               anchor="start",
               fill="muted", size=9.5)
    scene.math(52, 288, rf"\text{{range }}[{q3(sharp[0])},{q3(sharp[1])}]", t=f"and the range is [{num(sharp[0])}, {num(sharp[1])}]",
               anchor="start", fill="muted", size=9.5)
    return scene


# --- Taylor models -----------------------------------------------------------

def fig_taylor_model() -> Scene:
    """A polynomial, an exact remainder, and the interval both live on."""
    reach = 0.6

    def polynomial(x: float) -> float:
        return x - x ** 3 + x ** 5

    def remainder(x: float) -> float:
        """f − p₅, exactly −x⁷/(1 + x²) since (1 + x²)(x − x³ + x⁵) = x + x⁷."""
        return -x ** 7 / (1.0 + x * x)

    drift = max(abs(rational_bump(x) - polynomial(x) - remainder(x))
                for x in (-reach + 2.0 * reach * k / 60.0 for k in range(61)))
    if drift > 1e-14:
        raise SystemExit("taylor-model: the remainder is not the exact one")
    radius = abs(remainder(reach))
    if max(abs(remainder(x)) for x in
           (-reach + 2.0 * reach * k / 600.0 for k in range(601))) > radius:
        raise SystemExit("taylor-model: the radius is not attained at the ends")
    outside = (polynomial(1.0), rational_bump(1.0))

    scene = Scene(
        "taylor-model",
        "A Taylor polynomial with a uniform remainder",
        r"Left: \(f(x)=x/(1+x^2)\) and \(p_5(x)=x-x^3+x^5\). On the shaded domain "
        r"\([-0.6,0.6]\), the narrow tube \(p_5\pm\rho\) encloses \(f\). At \(x=1\), the "
        r"polynomial equals one while \(f(1)=1/2\); this model makes no error claim outside its "
        r"domain. Right: the signed remainder has its own vertical scale. Multiplication gives "
        r"\((1+x^2)p_5=x+x^7\), so \(f-p_5=-x^7/(1+x^2)\). Its absolute value increases with "
        r"\(|x|\); the sharp uniform radius is \(\rho=(0.6)^7/(1+0.6^2)=2187/106250\), "
        r"approximately \(0.021\). The remainder is positive at the left endpoint and negative "
        r"at the right. A CAS can prove the rational identity; an enclosure also needs the "
        r"domain-wide inequality \(|f-p_5|\le\rho\). The generator's numerical spot checks do "
        r"not supply that proof.",
        "Left, a rational function and its dashed Taylor polynomial nearly "
        "coincide on a shaded central domain but separate outside it. A "
        "narrow tube around the polynomial encloses the function on that "
        "domain. Right, the odd signed remainder decreases from plus rho "
        "at x = −0.6 to minus rho at x = 0.6, flattening near zero; dashed "
        "horizontal lines mark the sharp positive and negative bounds.",
        width=640.0, height=302.0)

    left = Frame(60, 78, 236, 150, -1.06, 1.06, -1.28, 1.28)
    scene.panel_title(32, 46, "the function and the polynomial")
    scene.math(32, 62, r"p_5=x-x^3+x^5", t='p₅ = x − x³ + x⁵', anchor="start", fill="muted",
               size=FS_LABEL)
    # The model's interval is shaded across the panel: inside it the two curves
    # agree to within rho, and outside it the polynomial is on its own.
    scene.rect(left.X(-reach), left.y0, left.X(reach) - left.X(-reach), left.h,
               fill="band")
    tube_xs = [-reach + 2 * reach * k / 240 for k in range(241)]
    scene.path(left.band([(x, polynomial(x) - radius) for x in tube_xs],
                         [(x, polynomial(x) + radius) for x in tube_xs]),
               stroke="accent2", sw=0.65, fill="band")
    left.axes(scene, x_label="x", origin_y=0.0)
    for tick in (-reach, reach):
        scene.line(left.X(tick), left.Y(0.0) - 4, left.X(tick), left.Y(0.0) + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(left.X(tick), left.Y(0.0) + 16, num(tick), size=9.5)
    for level in (-1.0, 1.0):
        scene.line(left.x0 - 3, left.Y(level), left.x0, left.Y(level),
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(left.x0 - 7, left.Y(level) + 3.5, num(level),
                         anchor="end", size=9.5)
    wide = [-1.06 + 2.12 * k / 400.0 for k in range(401)]
    scene.path(left.curve([(x, polynomial(x)) for x in wide]), stroke="accent2",
               sw=SW_CURVE2, dash=DASH)
    scene.path(left.curve([(x, rational_bump(x)) for x in wide]), stroke="accent",
               sw=SW_CURVE)
    scene.math(left.X(1.0), left.Y(rational_bump(1.0)) + 15, r"f=x/(1+x^2)", t='f = x/(1 + x²)',
               anchor="end", fill="accent", size=9.5, halo=True)
    scene.math(left.X(0.96), left.Y(1.02), r"p_5", t='p₅', anchor="end", fill="accent2",
               size=9.5, halo=True)
    scene.text(left.X(0.0), left.y0 + 11, "the interval of the model",
               fill="muted", size=9.5)
    scene.math(60, 252, rf"\text{{inside: }}|f-p_5|\le\rho\approx{q3(radius)}", t=f"inside: |f − p₅| ≤ ρ ≈ {q3(radius)}", anchor="start",
               fill="muted", size=9.5)
    scene.math(60, 265, rf"x=1:\quad p_5={q2(outside[0])},\ f={q2(outside[1])}", t=f"at x = 1: p₅ = {q2(outside[0])}, f = {q2(outside[1])}",
               anchor="start", fill="muted", size=9.5)

    right = Frame(376, 78, 224, 150, -0.68, 0.68, -0.029, 0.029)
    scene.panel_title(348, 46, "the remainder, exactly")
    scene.math(348, 62, r"f-p_5=-x^7/(1+x^2)", t='f − p₅ = −x⁷/(1 + x²)', anchor="start", fill="muted",
               size=FS_LABEL)
    right.axes(scene, x_label="x", origin_y=0.0)
    for tick in (-reach, reach):
        scene.line(right.X(tick), right.Y(0.0) - 4, right.X(tick),
                   right.Y(0.0) + 4, stroke="muted", sw=SW_AXIS)
        scene.tick_label(right.X(tick), right.Y(0.0) + 16, num(tick), size=9.5)
    for level in (-0.01, 0.01):
        scene.line(right.x0 - 3, right.Y(level), right.x0, right.Y(level),
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(right.x0 - 7, right.Y(level) + 3.5, num(level),
                         anchor="end", size=9.5)
    for sign in (1.0, -1.0):
        scene.line(right.x0, right.Y(sign * radius), right.right,
                   right.Y(sign * radius), stroke="accent2", sw=SW_AXIS,
                   dash=DASH)
    scene.math(right.right - 2, right.Y(radius) - 6, rf"\rho\approx{q3(radius)}", t=f"ρ ≈ {q3(radius)}",
               anchor="end", fill="accent2", size=9.5, halo=True)
    scene.math(right.right - 2, right.Y(-radius) + 14, rf"-\rho\approx{q3(-radius)}", t=f"−ρ ≈ {num(-radius)}",
               anchor="end", fill="accent2", size=9.5, halo=True)
    xs = [-reach + 2.0 * reach * k / 240.0 for k in range(241)]
    scene.path(right.curve([(x, remainder(x)) for x in xs]), stroke="accent",
               sw=SW_CURVE)
    scene.text(376, 252, "the same interval, its own vertical scale",
               anchor="start", fill="muted", size=9.5)
    scene.text(376, 265, "the radius is attained at both ends", anchor="start",
               fill="muted", size=9.5)
    scene.math(60, 288, r"\rho=2187/106250\text{; the domain is part of the model}", t='exact radius ρ = 2187/106250; the domain is part of the model',
               anchor="start", fill="muted", size=9.5)
    return scene


# --- what a drawing may not do -----------------------------------------------

# How many arguments each path command takes, and where its endpoint sits among
# them. A relative command is folded against the current point, so a lowercase
# segment is never mistaken for an absolute coordinate.
PATH_ARGS = {"M": 2, "L": 2, "H": 1, "V": 1, "C": 6, "S": 4, "Q": 4, "T": 2,
             "A": 7, "Z": 0}
PATH_TOKENS = re.compile(r"[MmLlHhVvCcSsQqTtAaZz]"
                         r"|[-+]?[0-9]*\.?[0-9]+(?:[eE][-+]?[0-9]+)?")

# A coordinate may sit this far outside the viewBox before it counts as escaped.
# Half a unit is less than a stroke width, so nothing that reads as inside the
# drawing is reported, and nothing that would be cut off is missed.
SLACK = 0.5


def path_points(d: str) -> list[tuple[float, float]]:
    """Every point path data ``d`` names, in absolute user units.

    Control points count: a cubic can bulge past its endpoints, so a control
    point outside the viewBox is a curve that leaves it.
    """
    tokens = PATH_TOKENS.findall(d)
    points: list[tuple[float, float]] = []
    x = y = start_x = start_y = 0.0
    command = ""
    index = 0
    while index < len(tokens):
        token = tokens[index]
        if token.isalpha():
            command = token
            index += 1
            if command in "Zz":
                x, y = start_x, start_y
                points.append((x, y))
                continue
        elif not command:
            raise SystemExit(f"path data starts without a command: {d[:32]!r}")
        upper = command.upper()
        needed = PATH_ARGS[upper]
        if index + needed > len(tokens):
            raise SystemExit(f"path data ends inside a {command}: {d[-32:]!r}")
        args = [float(value) for value in tokens[index:index + needed]]
        index += needed
        relative = command.islower()
        if upper == "H":
            x = x + args[0] if relative else args[0]
            points.append((x, y))
        elif upper == "V":
            y = y + args[0] if relative else args[0]
            points.append((x, y))
        elif upper == "A":
            x, y = ((x + args[5], y + args[6]) if relative else (args[5], args[6]))
            points.append((x, y))
        else:
            for k in range(0, needed, 2):
                if relative:
                    points.append((x + args[k], y + args[k + 1]))
                else:
                    points.append((args[k], args[k + 1]))
            x, y = points[-1]
        if upper == "M":
            start_x, start_y = x, y
            # A second pair after an M is a line, not another move.
            command = "l" if relative else "L"
    return points


def mark_offsets(mark: dict) -> list[tuple[float, float]]:
    """Every translation this mark is drawn at, including its animated ones."""
    found = [(0.0, 0.0)]
    for animation in mark.get("anim", []):
        if animation.get("type") == "translate":
            for frame in animation["values"].split(";"):
                numbers = [float(value) for value in
                           frame.replace(",", " ").split()]
                found.append((numbers[0], numbers[1] if len(numbers) > 1 else 0.0))
    return found


def mark_points(mark: dict) -> list[tuple[float, float, str]]:
    """``(x, y, what)`` for every point a mark reaches, animations included."""
    def value(key: str, default: float = 0.0) -> float:
        return float(mark[key]) if key in mark else default

    kind = mark["k"]
    found: list[tuple[float, float, str]] = []
    if kind == "line":
        found.append((value("x1"), value("y1"), "the start of a line"))
        found.append((value("x2"), value("y2"), "the end of a line"))
        for animation in mark.get("anim", []):
            name = animation["attributeName"]
            if name in ("x1", "x2", "y1", "y2"):
                for frame in animation["values"].split(";"):
                    number = float(frame)
                    across = name.startswith("x")
                    found.append((number if across else value("x1"),
                                  value("y1") if across else number,
                                  f"an animated {name}"))
    elif kind == "rect":
        x, y = value("x"), value("y")
        found.append((x, y, "a corner of a rectangle"))
        found.append((x + value("width"), y + value("height"),
                      "a corner of a rectangle"))
    elif kind == "circle":
        cx, cy, r = value("cx"), value("cy"), value("r")
        found.append((cx - r, cy - r, "the rim of a circle"))
        found.append((cx + r, cy + r, "the rim of a circle"))
    elif kind == "text":
        found.append((value("x"), value("y"), f"the anchor of {mark['t'][:28]!r}"))
    elif kind == "path":
        for x, y in path_points(mark["d"]):
            found.append((x, y, "a point of a path"))
        for animation in mark.get("anim", []):
            if animation["attributeName"] != "d":
                continue
            for number, frame in enumerate(animation["values"].split(";")):
                for x, y in path_points(frame):
                    found.append((x, y, f"a point of animation frame {number}"))
    return found


def containment_problems(figure: dict) -> list[str]:
    """Every coordinate of ``figure`` that leaves its own viewBox.

    A curve sampled far outside the drawing looks right and is not: it is one
    edit away from being visible, it inflates the page, and it means the frame
    does not say what the picture shows. The exception is a mark with a clip,
    which cannot draw outside it however far its own coordinates run: the
    travelling wave is two periods of a sine translated across a one-period
    window, and only the window has to be inside the viewBox.
    """
    width, height = float(figure["width"]), float(figure["height"])
    found: list[str] = []
    seen: set[str] = set()
    for window in figure.get("clips", []):
        left, top = float(window["x"]), float(window["y"])
        for axis, low, high, limit in (("x", left, left + float(window["w"]), width),
                                       ("y", top, top + float(window["h"]), height)):
            if -SLACK <= low and high <= limit + SLACK:
                continue
            found.append(f"the clip {window['id']} runs from {axis} = {q2(low)} "
                         f"to {q2(high)}, outside the {q2(width)} by "
                         f"{q2(height)} viewBox")
    for number, mark in enumerate(figure["marks"]):
        if mark.get("clip"):
            continue
        for dx, dy in mark_offsets(mark):
            for x, y, what in mark_points(mark):
                for axis, position, limit in (("x", x + dx, width),
                                              ("y", y + dy, height)):
                    if -SLACK <= position <= limit + SLACK:
                        continue
                    problem = (f"mark {number} ({mark['k']}): {what} is at "
                               f"{axis} = {q2(position)}, outside the "
                               f"{q2(width)} by {q2(height)} viewBox")
                    if problem not in seen:
                        seen.add(problem)
                        found.append(problem)
    return found


CAPTION_MATH = re.compile(r"\\\((.+?)\\\)", re.DOTALL)
MATH_GLYPHS = re.compile(r"[\u0370-\u03ff\u2070-\u209f\u2200-\u22ff²³¹½¼¾]")


def tex_problems(tex: str) -> list[str]:
    """Source checks only; the parent's KaTeX pass checks TeX syntax."""
    found = []
    if not tex.strip():
        found.append("empty TeX")
    if not tex.isascii():
        found.append(f"TeX must use explicit commands, not Unicode: {tex!r}")
    if any(delimiter in tex for delimiter in (r"\(", r"\)", "$")):
        found.append(f"bare TeX expected inside a math label: {tex!r}")
    return found


def caption_problems(caption: str) -> list[str]:
    """Keep formulas inside the inline delimiters the HTML build consumes."""
    found = []
    for formula in CAPTION_MATH.findall(caption):
        found.extend(tex_problems(formula))
    prose = CAPTION_MATH.sub("", caption)
    if any(token in prose for token in (r"\(", r"\)", "^", "_", "$")):
        found.append("unbalanced caption math delimiters or math outside delimiters")
    if MATH_GLYPHS.search(prose):
        found.append("Unicode mathematics outside caption math delimiters")
    return found


def label_problems(figure: dict) -> list[str]:
    """Labels that would print their own source instead of the mathematics."""
    found = []
    for mark in figure["marks"]:
        if "runs" in mark:
            found.append("legacy text runs must be replaced by a tex label")
        if mark["k"] != "text":
            if "tex" in mark:
                found.append("only text marks may carry tex")
            continue
        body = mark["t"]
        if "tex" in mark:
            found.extend(tex_problems(mark["tex"]))
        elif "^" in body or "_" in body or MATH_GLYPHS.search(body):
            found.append(f"mathematical label {body!r} needs Scene.math")
    return found


def fig_kovalevskaya_series() -> Scene:
    """Two Cauchy problems with the same analytic datum: one series converges, one never does."""
    def partial_sum(t: float, n: int) -> float:
        return sum((-1) ** k * t ** (2 * k) for k in range(n + 1))

    def log_term(k: int, t: float) -> float:
        # log10 of (2k)!/k! * t^k, the k-th term of the heat series at x = 0
        return (math.lgamma(2 * k + 1) - math.lgamma(k + 1)) / math.log(10) + k * math.log10(t)

    for t in (0.3, 0.6, 0.9):
        if abs(partial_sum(t, 400) - 1.0 / (1.0 + t * t)) > 1e-9:
            raise SystemExit("kovalevskaya-series: wave partial sums do not converge")
    heat_times = (0.05, 0.02, 0.01)
    kmax = 60
    for t in heat_times:
        logs = [log_term(k, t) for k in range(kmax + 1)]
        kmin = min(range(kmax + 1), key=lambda k: logs[k])
        if abs(kmin - 1.0 / (4.0 * t)) > 1.0 or logs[kmax] < logs[kmin] + 1.0:
            raise SystemExit("kovalevskaya-series: heat terms do not turn around near 1/(4t)")

    scene = Scene(
        "kovalevskaya-series",
        "The same datum, a convergent and a divergent series",
        r"Both problems start from \(g(x)=1/(1+x^2)\), analytic on the whole line. Left: the "
        r"wave equation with \(u_t(0,x)=0\). At \(x=0\) the partial sums "
        r"\(S_N(t)=\sum_{k\le N}(-1)^kt^{2k}\) for \(N=1,2,5,6,15,16\) approach the exact value "
        r"\(1/(1+t^2)\) for \(t<1\). At the dashed line \(t=1\) they alternate between "
        r"\(0\) and \(1\), and beyond it they separate, odd \(N\) downward and even \(N\) upward. Right: the heat "
        r"equation. The \(k\)-th term of its formal series at \(x=0\) has size "
        r"\((2k)!\,t^k/k!\), plotted on a base-ten logarithmic scale for three times. Each "
        r"sequence falls until \(k\) is about \(1/(4t)\) and then grows without bound, crossing "
        r"the dashed line of terms of size one, so the series diverges at every \(t>0\).",
        "Two panels. Left, five thin partial-sum curves that hug a thick decreasing "
        "curve on the interval from zero to one and then peel away above and below it. "
        "Right, three V-shaped sequences of points on a logarithmic scale, each with a "
        "minimum further to the right for smaller time, all rising past the line where "
        "the term size is one.",
        width=640.0, height=264.0)

    left = Frame(56, 64, 236, 170, 0.0, 1.25, -0.25, 1.35)
    scene.panel_title(24, 40, "wave: partial sums converge")
    left.axes(scene, x_label="t", origin_y=0.0)
    for value in (0.0, 0.5, 1.0):
        scene.tick_label(left.x0 - 7, left.Y(value) + 3, q2(value), anchor="end", size=9.5)
    for tick in (0.5, 1.0):
        scene.line(left.X(tick), left.Y(0.0), left.X(tick), left.Y(0.0) + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(left.X(tick), left.Y(0.0) + 16, q2(tick), size=9.5)
    scene.line(left.X(1.0), left.y0, left.X(1.0), left.bottom, stroke="muted",
               sw=SW_AXIS, dash=DASH)
    window = scene.clip("wave", left.x0, left.y0, left.w, left.h)
    for n in (1, 2, 5, 6, 15, 16):
        scene.path(left.sample(lambda t, n=n: partial_sum(t, n), 0.0, 1.25, 250),
                   stroke="muted", sw=SW_CURVE2, clip=window)
    scene.path(left.sample(lambda t: 1.0 / (1.0 + t * t), 0.0, 1.25, 250),
               stroke="accent", sw=SW_CURVE)
    scene.math(left.X(0.42), left.Y(0.6), r"\frac{1}{1+t^2}", t="1/(1+t²)",
               fill="accent", size=10, halo=True)
    scene.math(left.x0 + 8, left.y0 + 12, r"S_N,\ N=1,2,5,6,15,16", t="S_N, N = 1, 2, 5, 6, 15, 16",
               anchor="start", fill="muted", size=10)

    right = Frame(380, 64, 236, 170, 0.0, float(kmax), -12.0, 12.0)
    scene.panel_title(352, 40, "heat: term sizes diverge")
    right.axes(scene, x_label="k", origin_y=-12.0)
    scene.line(right.x0, right.Y(0.0), right.right, right.Y(0.0), stroke="muted",
               sw=SW_AXIS, dash=DASH)
    for value in (-10, 0, 10):
        scene.tick_label(right.x0 - 7, right.Y(value) + 3, num(value), anchor="end", size=9.5)
    for tick in (0, 20, 40, 60):
        scene.line(right.X(tick), right.bottom, right.X(tick), right.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(right.X(tick), right.bottom + 16, str(tick), size=9.5)
    scene.math(right.x0 + 4, right.y0 - 6, r"\log_{10}\frac{(2k)!\,t^k}{k!}",
               t="log10 of (2k)! t^k / k!", anchor="start", fill="muted", size=10)
    heat_window = scene.clip("heat", right.x0, right.y0, right.w, right.h)
    roles = ("accent", "accent2", "ink")
    for t, role in zip(heat_times, roles):
        points = [(k, log_term(k, t)) for k in range(kmax + 1)]
        scene.path(right.curve(points), stroke=role, sw=SW_CURVE2, clip=heat_window)
        for k, value in points:
            if k % 2 == 0 and -12.0 <= value <= 12.0:
                scene.circle(right.X(k), right.Y(value), 1.8, fill=role)
        if points[-1][1] < 8.0:
            anchor_x, anchor_y, side = right.X(kmax) - 4, right.Y(points[-1][1]) - 8, "end"
        else:
            k_up = next(k for k, value in points if k > 1 and value >= 8.0)
            anchor_x, anchor_y, side = right.X(k_up) - 6, right.Y(8.0) + 4, "end"
        scene.math(anchor_x, anchor_y, rf"t={q2(t)}", t=f"t = {q2(t)}", anchor=side,
                   fill=role, size=9.5, halo=True)
    scene.text(right.right - 4, right.Y(0.0) - 5, "term size 1", anchor="end",
               fill="muted", size=9.0)
    return scene


def fig_boundary_chart_normal() -> Scene:
    """Outward normals on a C1 boundary, and the graph chart that defines them."""
    def radius(theta: float) -> float:
        return 1.0 + 0.22 * math.cos(3.0 * theta) + 0.08 * math.sin(2.0 * theta)

    def radius_prime(theta: float) -> float:
        return -0.66 * math.sin(3.0 * theta) + 0.16 * math.cos(2.0 * theta)

    def boundary(theta: float) -> tuple[float, float]:
        r = radius(theta)
        return (r * math.cos(theta), r * math.sin(theta))

    def tangent(theta: float) -> tuple[float, float]:
        r, dr = radius(theta), radius_prime(theta)
        return (dr * math.cos(theta) - r * math.sin(theta),
                dr * math.sin(theta) + r * math.cos(theta))

    def field(x: float, y: float) -> tuple[float, float]:
        return (x + 0.4 * y, 0.3 * x * x)

    # div F = 1, so the volume side is the area; the boundary side is the
    # flux of F through the outward normal, integrated in arc length.
    steps = 20000
    area = 0.0
    flux = 0.0
    for k in range(steps):
        theta = 2.0 * math.pi * (k + 0.5) / steps
        x, y = boundary(theta)
        tx, ty = tangent(theta)
        fx, fy = field(x, y)
        area += 0.5 * (x * ty - y * tx)
        flux += fx * ty - fy * tx
    area *= 2.0 * math.pi / steps
    flux *= 2.0 * math.pi / steps
    if abs(area - flux) > 1e-6:
        raise SystemExit("boundary-chart-normal: divergence and flux disagree")

    scene = Scene(
        "boundary-chart-normal",
        "Outward normals and the graph chart behind them",
        r"Left: a bounded planar domain \(\Omega\) with smooth boundary, outward unit normals "
        r"\(\nu\) at twelve boundary points, and the field \(F(x,y)=(x+0.4y,\,0.3x^2)\) at the "
        r"same points. Here \(\operatorname{div}F=1\), so \(\int_\Omega\operatorname{div}F\) "
        r"is the area of \(\Omega\), and the computed flux \(\int_{\partial\Omega}F\cdot\nu\,"
        r"d\sigma\) agrees with it to six decimals. Right: near a boundary point the domain is "
        r"the region above a \(C^1\) graph \(x_n=\gamma(x')\). The outward normal is "
        r"\((\nabla\gamma,-1)/\sqrt{1+|\nabla\gamma|^2}\), pointing below the graph, and a "
        r"parameter interval of length \(dy\) carries boundary length "
        r"\(\sqrt{1+|\nabla\gamma|^2}\,dy\).",
        "Two panels. Left, a rounded three-lobed region with short thick arrows "
        "pointing straight out of the boundary and thinner arrows showing a vector "
        "field at the same points. Right, a shaded region above a wavy curve, with a "
        "downward normal arrow at one point, a highlighted piece of the curve, and "
        "the parameter interval below it that the piece projects onto.",
        width=640.0, height=290.0)

    left = Frame(48, 50, 208, 208 * 3.0 / 3.2, -1.6, 1.6, -1.5, 1.5)
    scene.panel_title(24, 36, "normals and flux")
    outline = [boundary(2.0 * math.pi * k / 360) for k in range(361)]
    scene.path(left.curve(outline) + "Z", stroke="ink", sw=SW_CURVE, fill="band")
    scene.math(left.X(-0.1), left.Y(0.05), r"\Omega", fill="ink", size=FS_LABEL)
    for k in range(12):
        theta = 2.0 * math.pi * (k + 0.25) / 12
        x, y = boundary(theta)
        tx, ty = tangent(theta)
        norm = math.hypot(tx, ty)
        nx, ny = ty / norm, -tx / norm
        fx, fy = field(x, y)
        draw_arrow(scene, [(left.X(x), left.Y(y)),
                           (left.X(x + 0.38 * fx), left.Y(y + 0.38 * fy))],
                   role="muted", sw=SW_AXIS + 0.25)
        draw_arrow(scene, [(left.X(x), left.Y(y)),
                           (left.X(x + 0.32 * nx), left.Y(y + 0.32 * ny))],
                   role="accent", sw=SW_CURVE2)
    scene.math(24, 276, rf"|\Omega|\approx{q3(area)},\ \int_{{\partial\Omega}}F\cdot\nu\,d\sigma\approx{q3(flux)}",
               t=f"area ≈ {q3(area)}, flux ≈ {q3(flux)}", anchor="start", fill="muted", size=9.5)

    def gamma(s: float) -> float:
        return 0.25 * math.sin(1.6 * s) + 0.12 * s * s

    def gamma_prime(s: float) -> float:
        return 0.4 * math.cos(1.6 * s) + 0.24 * s

    right = Frame(350, 56, 256, 256 * 2.2 / 3.2, -1.6, 1.6, -0.9, 1.3)
    scene.panel_title(330, 36, "one graph chart")
    graph = [(-1.6 + 3.2 * k / 240, gamma(-1.6 + 3.2 * k / 240)) for k in range(241)]
    top = [(x, 1.3) for x, _ in graph]
    scene.area(right.band(graph, top), fill="band")
    scene.path(right.curve(graph), stroke="ink", sw=SW_CURVE)
    base = -0.75
    scene.line(right.x0, right.Y(base), right.right, right.Y(base), stroke="muted", sw=SW_AXIS)
    scene.math(right.right + 8, right.Y(base) + 4, r"x'", t="x'", anchor="start", fill="muted", size=10)
    s0, ds = 0.35, 0.5
    piece = [(s0 + ds * k / 40, gamma(s0 + ds * k / 40)) for k in range(41)]
    scene.path(right.curve(piece), stroke="accent2", sw=SW_CURVE + 1.0)
    scene.line(right.X(s0), right.Y(base), right.X(s0 + ds), right.Y(base),
               stroke="accent2", sw=SW_CURVE + 1.0)
    for s in (s0, s0 + ds):
        scene.line(right.X(s), right.Y(base), right.X(s), right.Y(gamma(s)),
                   stroke="muted", sw=SW_AXIS, dash=DASH)
    scene.math(right.X(s0 + ds / 2), right.Y(base) + 15, r"dy", fill="accent2", size=10)
    sp = -0.75
    slope = gamma_prime(sp)
    norm = math.hypot(slope, 1.0)
    nu = (slope / norm, -1.0 / norm)
    px, py = sp, gamma(sp)
    draw_arrow(scene, [(right.X(px), right.Y(py)),
                       (right.X(px + 0.4 * nu[0]), right.Y(py + 0.4 * nu[1]))],
               role="accent", sw=SW_CURVE2)
    scene.circle(right.X(px), right.Y(py), 2.6, fill="accent")
    scene.math(right.X(px + 0.4 * nu[0]) + 6, right.Y(py + 0.4 * nu[1]), r"\nu",
               anchor="start", fill="accent", size=FS_LABEL)
    scene.math(right.X(-0.2), right.Y(0.85), r"\Omega=\{x_n>\gamma(x')\}",
               t="Ω = {x_n > γ(x')}", fill="ink", size=FS_LABEL)
    scene.math(right.X(1.25), right.Y(gamma(1.25)) - 10, r"\gamma", fill="ink", size=FS_LABEL,
               halo=True)
    scene.math(330, 276, r"d\sigma=\sqrt{1+|\nabla\gamma|^2}\,dy",
               t="dσ = sqrt(1 + |∇γ|²) dy", anchor="start", fill="accent2", size=10)
    return scene


def fig_heaviside_dirac() -> Scene:
    """Mollified Heaviside functions, their derivatives, and the pairing that tends to phi(0)."""
    epsilons = [0.8, 0.56, 0.4, 0.28, 0.2, 0.14, 0.1]

    def heaviside(x: float) -> float:
        return 1.0 if x >= 0.0 else 0.0

    def smoothed(x: float, eps: float) -> float:
        # (H * eta_eps)(x) is the mass of eta_eps on (-inf, x]
        if x <= -eps:
            return 0.0
        if x >= eps:
            return 1.0
        return integrate(lambda y: mollifier(y, eps), -eps, x, 400)

    def phi(x: float) -> float:
        return bump((x - 0.35) / 1.1)

    def phi_prime(x: float) -> float:
        s = (x - 0.35) / 1.1
        if abs(s) >= 1.0:
            return 0.0
        return bump(s) * (-2.0 * s / (1.0 - s * s) ** 2) / 1.1

    pairings = []
    for eps in epsilons:
        direct = integrate(lambda y: mollifier(y, eps) * phi(y), -eps, eps, 2000)
        by_parts = -integrate(lambda y: smoothed(y, eps) * phi_prime(y), -0.75, 1.45, 1500)
        if abs(direct - by_parts) > 2e-3:
            raise SystemExit("heaviside-dirac: the two pairings disagree")
        pairings.append(direct)
    errors = [abs(p - phi(0.0)) for p in pairings]
    if any(b > a for a, b in zip(errors, errors[1:])) or errors[-1] > 0.01:
        raise SystemExit("heaviside-dirac: the pairing does not approach phi(0)")

    scene = Scene(
        "heaviside-dirac",
        "Smoothing the Heaviside function",
        r"The Heaviside function \(H\) convolved with the mollifier \(\eta_\varepsilon\) is the "
        r"smooth step \(H_\varepsilon=H*\eta_\varepsilon\), and its classical derivative is "
        r"\(\eta_\varepsilon\) itself. The animation steps through seven computed values of "
        r"\(\varepsilon\) from \(0.8\) to \(0.1\). Left: \(H_\varepsilon\) against the step "
        r"\(H\). Right: \(\eta_\varepsilon\), whose peak leaves the panel at small "
        r"\(\varepsilon\), together with a fixed test function \(\varphi\). The printed pairing "
        r"\(\int\eta_\varepsilon\varphi\), computed both directly and as "
        r"\(-\int H_\varepsilon\varphi'\), approaches \(\varphi(0)\), which is the value of "
        r"\(\delta_0\) on \(\varphi\).",
        "Two panels. Left, a smooth S-shaped curve that steepens toward a dashed "
        "unit step at the origin. Right, a narrowing bump centred at the origin "
        "beside a wider fixed bump centred slightly to the right, with a line of "
        "text giving the current value of the pairing next to the value of the "
        "wide bump at zero.",
        width=640.0, height=280.0)

    left = Frame(52, 60, 240, 160, -1.5, 1.5, -0.1, 1.2)
    scene.panel_title(24, 38, "the smoothed step")
    left.axes(scene, x_label="x", origin_y=0.0)
    for value in (0.0, 1.0):
        scene.tick_label(left.x0 - 7, left.Y(value) + 3, q2(value), anchor="end", size=9.5)
    for tick in (-1.0, 0.0, 1.0):
        scene.line(left.X(tick), left.Y(0.0), left.X(tick), left.Y(0.0) + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(left.X(tick), left.Y(0.0) + 16, num(tick), size=9.5)
    scene.path(poly_path([(left.X(-1.5), left.Y(0.0)), (left.X(0.0), left.Y(0.0)),
                          (left.X(0.0), left.Y(1.0)), (left.X(1.5), left.Y(1.0))]),
               stroke="muted", sw=SW_CURVE2, dash=DASH)
    xs = [-1.5 + 3.0 * k / 300 for k in range(301)]
    steps = [[(x, smoothed(x, eps)) for x in xs] for eps in epsilons]
    curves = left.curve_frames(steps)
    scene.path(curves[0], stroke="accent", sw=SW_CURVE, anim=[discrete("d", curves)])
    scene.math(left.X(-1.35), left.Y(1.0), r"H_\varepsilon", t="H_ε", anchor="start",
               fill="accent", size=FS_LABEL)
    scene.math(left.X(0.12), left.Y(1.08), r"H", anchor="start", fill="muted", size=FS_LABEL)

    right = Frame(372, 60, 240, 160, -1.5, 1.5, -0.1, 3.0)
    scene.panel_title(344, 38, "its derivative and a test function")
    right.axes(scene, x_label="x", origin_y=0.0)
    for value in (0.0, 1.0, 2.0, 3.0):
        scene.tick_label(right.x0 - 7, right.Y(value) + 3, q2(value), anchor="end", size=9.5)
    for tick in (-1.0, 0.0, 1.0):
        scene.line(right.X(tick), right.Y(0.0), right.X(tick), right.Y(0.0) + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(right.X(tick), right.Y(0.0) + 16, num(tick), size=9.5)
    window = scene.clip("spike", right.x0, right.y0, right.w, right.h)
    spikes = [[(x, mollifier(x, eps)) for x in xs] for eps in epsilons]
    fills = right.fill_frames(spikes, 0.0)
    lines = right.curve_frames(spikes)
    scene.area(fills[0], fill="band", clip=window, anim=[discrete("d", fills)])
    scene.path(lines[0], stroke="accent", sw=SW_CURVE, clip=window,
               anim=[discrete("d", lines)])
    scene.path(right.sample(phi, -1.5, 1.5, 300), stroke="ink", sw=SW_CURVE2)
    scene.circle(right.X(0.0), right.Y(phi(0.0)), 2.8, fill="ink")
    scene.math(right.X(1.05), right.Y(0.75), r"\varphi", anchor="start", fill="ink",
               size=FS_LABEL)
    scene.math(right.X(-0.3), right.Y(2.7), r"\eta_\varepsilon", t="η_ε", anchor="end",
               fill="accent", size=FS_LABEL)
    count = len(epsilons)
    for index, (eps, value) in enumerate(zip(epsilons, pairings)):
        op = 1 if index == 0 else 0
        scene.math(24, 262, rf"\varepsilon={q2(eps)}", t=f"ε = {q2(eps)}", anchor="start",
                   fill="accent", size=10, op=op, anim=[slot(index, count)])
        scene.math(344, 262, rf"\int\eta_\varepsilon\varphi\approx{q3(value)}",
                   t=f"∫ η_ε φ ≈ {q3(value)}", anchor="start", fill="accent", size=10,
                   op=op, anim=[slot(index, count)])
    scene.math(500, 262, rf"\varphi(0)\approx{q3(phi(0.0))}", t=f"φ(0) ≈ {q3(phi(0.0))}",
               anchor="start", fill="ink", size=10)
    return scene


def fig_interval_green_function() -> Scene:
    """The Green function of -u'' on (0,1) and the one-eighth stability bound."""
    def green(x: float, y: float) -> float:
        return min(x, y) * (1.0 - max(x, y))

    def solve(f, x: float) -> float:
        # u_f(x) = int_0^1 G(x, y) f(y) dy, split at the kink y = x
        return integrate(lambda y: green(x, y) * f(y), 0.0, x, 400) + \
            integrate(lambda y: green(x, y) * f(y), x, 1.0, 400)

    def f(y: float) -> float:
        return 1.0

    def g(y: float) -> float:
        return 1.0 + 0.8 * math.sin(math.pi * y) - 0.25 * math.sin(4.0 * math.pi * y)

    xs = [k / 200 for k in range(201)]
    sup = max(abs(f(y) - g(y)) for y in (k / 4000 for k in range(4001)))
    diff = [(x, solve(f, x) - solve(g, x)) for x in xs]
    envelope = [(x, 0.5 * x * (1.0 - x) * sup) for x in xs]
    for (x, d), (_, e) in zip(diff, envelope):
        if abs(d) > e + 1e-9:
            raise SystemExit("interval-green-function: the pointwise bound fails")
    for x in (0.25, 0.5, 0.75):
        if abs(solve(f, x) - 0.5 * x * (1.0 - x)) > 1e-6:
            raise SystemExit("interval-green-function: u_1 is not x(1-x)/2")

    scene = Scene(
        "interval-green-function",
        "The Green function of the interval and the one-eighth bound",
        r"Left: \(G(x,\cdot)\) for \(x=0.2,0.5,0.8\), the tent "
        r"\(G(x,y)=\min(x,y)(1-\max(x,y))\) with its peak \(x(1-x)\) at \(y=x\). Integrating "
        r"each tent in \(y\) gives the solution for \(f=1\), the arch \(x(1-x)/2\), drawn "
        r"thick as a function of \(x\) on the same axis, with maximum \(1/8\) at the midpoint. Right: for \(f=1\) and an oscillating "
        r"forcing \(g\), the computed difference \(u_f-u_g\) stays inside the band "
        r"\(\pm\tfrac12x(1-x)\|f-g\|_\infty\), so its uniform norm is at most "
        r"\(\tfrac18\|f-g\|_\infty\).",
        "Two panels. Left, three triangular tents on the unit interval with peaks at "
        "0.2, 0.5 and 0.8, under a thick parabolic arch. Right, a shaded lens-shaped "
        "band symmetric about the axis, pinched at both endpoints, with a wavy "
        "difference curve lying inside it.",
        width=640.0, height=260.0)

    left = Frame(56, 56, 236, 150, 0.0, 1.0, 0.0, 0.27)
    scene.panel_title(24, 36, "tents and their integral")
    left.axes(scene, x_label="y", origin_y=0.0)
    for value in (0.0, 0.125, 0.25):
        scene.tick_label(left.x0 - 7, left.Y(value) + 3, q3(value), anchor="end", size=9.5)
    for tick in (0.0, 0.5, 1.0):
        scene.line(left.X(tick), left.Y(0.0), left.X(tick), left.Y(0.0) + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(left.X(tick), left.Y(0.0) + 16, q2(tick), size=9.5)
    for x in (0.2, 0.5, 0.8):
        scene.path(left.curve([(0.0, 0.0), (x, green(x, x)), (1.0, 0.0)]),
                   stroke="muted", sw=SW_CURVE2)
        scene.circle(left.X(x), left.Y(green(x, x)), 2.4, fill="muted")
    scene.math(left.X(0.5), left.Y(0.25) - 6, r"G(0.5,\cdot)", t="G(0.5, ·)", fill="muted",
               size=9.5)
    scene.path(left.curve([(x, solve(f, x)) for x in xs]), stroke="accent", sw=SW_CURVE)
    scene.line(left.x0, left.Y(0.125), left.right, left.Y(0.125), stroke="muted",
               sw=SW_AXIS, dash=DASH)
    scene.math(left.X(0.63), left.Y(0.152), r"\tfrac12x(1-x)", t="x(1−x)/2", fill="accent",
               size=10, halo=True)

    right = Frame(380, 56, 236, 150, 0.0, 1.0, -0.13, 0.13)
    scene.panel_title(352, 36, "continuous dependence")
    scene.area(right.band([(x, -e) for x, e in envelope], envelope), fill="band")
    right.axes(scene, x_label="x", origin_y=0.0)
    for value in (-0.1, 0.0, 0.1):
        scene.tick_label(right.x0 - 7, right.Y(value) + 3, num(value), anchor="end", size=9.5)
    for tick in (0.5, 1.0):
        scene.line(right.X(tick), right.Y(0.0), right.X(tick), right.Y(0.0) + 4,
                   stroke="muted", sw=SW_AXIS)
    scene.path(right.curve(diff), stroke="accent", sw=SW_CURVE)
    scene.math(right.X(0.5), right.Y(0.5 * 0.25 * sup) - 6,
               r"\tfrac18\|f-g\|_\infty", t="‖f − g‖/8", fill="muted", size=9.5)
    scene.math(right.X(0.3), right.bottom + 18, rf"u_f-u_g,\ \|f-g\|_\infty\approx{q2(sup)}",
               t=f"u_f − u_g, sup |f − g| ≈ {q2(sup)}", fill="accent", size=10)
    return scene


def _refl_u(t: float) -> float:
    return 0.6 + 0.5 * math.sin(2.2 * t)


def _refl_du(t: float) -> float:
    return 1.1 * math.cos(2.2 * t)


def fig_sobolev_reflection_extension() -> Scene:
    """Even reflection across t = 0 against extension by zero."""
    half = integrate_mid(lambda t: _refl_u(t) ** 2 + _refl_du(t) ** 2, 0.0, 1.0, 4000)

    def eu(t: float) -> float:
        return _refl_u(abs(t))

    def deu(t: float) -> float:
        return _refl_du(t) if t > 0 else -_refl_du(-t)

    full = integrate_pieces(lambda t: eu(t) ** 2 + deu(t) ** 2, [-1.0, 0.0, 1.0], 4000)
    if abs(full - 2.0 * half) > 1e-9:
        raise SystemExit("sobolev-reflection-extension: the reflected norm is not doubled")
    if abs(eu(1e-9) - eu(-1e-9)) > 1e-8:
        raise SystemExit("sobolev-reflection-extension: the reflection jumps at zero")
    jump = _refl_u(0.0)

    scene = Scene(
        "sobolev-reflection-extension",
        "Extension across a flat boundary by reflection",
        r"A function \(u(t)=0.6+0.5\sin(2.2t)\) on \((0,1)\) and two ways to continue it to "
        r"\((-1,1)\). Left: the even reflection \(Eu(t)=u(|t|)\) meets \(u\) at \(t=0\) with the "
        r"same value, while the zero extension (dashed) jumps by \(u(0)=0.6\). Right: the "
        r"derivatives. \((Eu)'\) is the odd reflection of \(u'\); it jumps at zero but is still "
        r"square integrable, so \(Eu\in H^1(-1,1)\). The derivative of the zero extension "
        r"contains the point mass \(0.6\,\delta_0\), drawn as an arrow, and is not a function. "
        r"Each integral in the graph norm doubles: numerically "
        rf"\(\|Eu\|_{{H^1(-1,1)}}^2={q3(full)}=2\times{q3(half)}\).",
        "Two panels over t from minus one to one, with the boundary t = 0 marked by a "
        "vertical line. Left, a smooth curve on the right half and its mirror image on "
        "the left half, meeting at height 0.6; a dashed zero extension drops from 0.6 to "
        "zero at t = 0. Right, the derivative on the right half and its negative mirror "
        "on the left half, which jumps at zero from about minus 1.1 to 1.1, and an "
        "upward arrow at t = 0 for the point mass of the zero extension's derivative.",
        width=640, height=300)
    left = Frame(56, 70, 240, 160, -1.05, 1.05, -0.12, 1.25)
    right = Frame(368, 70, 240, 160, -1.05, 1.05, -1.4, 1.4)
    scene.panel_title(24, 40, "the function")
    scene.panel_title(336, 40, "its derivative")
    left.axes(scene, x_label="t", origin_y=0)
    right.axes(scene, x_label="t", origin_y=0)
    for frame in (left, right):
        scene.line(frame.X(0), frame.y0, frame.X(0), frame.bottom, stroke="muted",
                   sw=SW_AXIS, dash=DOT)
        for tick in (-1, 0, 1):
            scene.tick_label(frame.X(tick), frame.bottom + 16, num(tick), size=10)
    scene.tick_label(left.x0 - 7, left.Y(1) + 4, "1", anchor="end", size=10)
    for level in (-1, 1):
        scene.tick_label(right.x0 - 7, right.Y(level) + 4, num(level), anchor="end",
                         size=10)
    # zero extension: zero on the left, u on the right
    scene.path(left.curve([(-1, 0), (0, 0)]), stroke="accent2", sw=SW_CURVE2, dash=DASH)
    scene.line(left.X(0), left.Y(0), left.X(0), left.Y(jump), stroke="accent2",
               sw=SW_AXIS, dash=DASH)
    scene.path(left.sample(lambda t: eu(t), -1, 0, 120), stroke="accent")
    scene.path(left.sample(_refl_u, 0, 1, 120), stroke="ink")
    scene.circle(left.X(0), left.Y(jump), 3, fill="accent")
    scene.math(left.X(0.5), left.Y(1.12), "u", fill="ink", halo=True)
    scene.math(left.X(-0.55), left.Y(1.12), r"Eu(t)=u(-t)", t="Eu(t) = u(−t)",
               fill="accent", halo=True)
    scene.math(left.X(-0.5), left.Y(0) - 8, r"\text{zero extension}",
               t="zero extension", fill="accent2", size=10, halo=True)
    scene.path(right.sample(lambda t: -_refl_du(-t), -1, -1e-9, 160), stroke="accent")
    scene.path(right.sample(_refl_du, 1e-9, 1, 160), stroke="ink")
    scene.circle(right.X(0), right.Y(-_refl_du(0)), 3, stroke="accent", fill="surface")
    scene.circle(right.X(0), right.Y(_refl_du(0)), 3, stroke="ink", fill="surface")
    scene.math(right.X(0.62), right.Y(1.18), "u'", fill="ink", halo=True)
    scene.math(right.X(-0.6), right.Y(1.18), r"(Eu)'(t)=-u'(-t)", t="(Eu)′(t) = −u′(−t)",
               fill="accent", halo=True)
    draw_arrow(scene, [(right.X(0) + 14, right.Y(-0.2)), (right.X(0) + 14, right.Y(1.05))],
               role="accent2", sw=SW_CURVE2)
    scene.math(right.X(0) + 20, right.Y(-0.45), r"0.6\,\delta_0", t="0.6 δ₀",
               anchor="start", fill="accent2", size=11, halo=True)
    scene.text(24, 272, "reflection keeps the value, so no jump", anchor="start",
               fill="muted", size=11)
    scene.math(336, 272, rf"\|Eu\|_{{H^1}}^2=2\|u\|_{{H^1(0,1)}}^2={q3(full)}",
               t=f"‖Eu‖² = 2‖u‖² = {q3(full)}", anchor="start", fill="muted", size=11)
    return scene


def _height_u(x: float, t: float) -> float:
    return math.exp(-(x - 1.2 * t) ** 2 - t)


def _height_dt(x: float, t: float) -> float:
    return (2.4 * (x - 1.2 * t) - 1.0) * _height_u(x, t)


def fig_trace_height_average() -> Scene:
    """Averages over thin strips converge to the boundary restriction."""
    epsilons = (0.8, 0.4, 0.2, 0.1, 0.05)
    xa, xb = -3.0, 4.0

    def average(x: float, eps: float) -> float:
        return integrate_mid(lambda t: _height_u(x, t), 0.0, eps, 200) / eps

    def g(x: float) -> float:
        return _height_u(x, 0.0)

    # the full half-space energy of the normal derivative
    energy = integrate_mid(
        lambda t: integrate_mid(lambda x: _height_dt(x, t) ** 2, -8.0, 16.0, 600),
        0.0, 12.0, 600)
    xs = [xa + (xb - xa) * k / 280 for k in range(281)]
    errors, bounds, frames = [], [], []
    for eps in epsilons:
        err = math.sqrt(integrate_mid(lambda x: (average(x, eps) - g(x)) ** 2,
                                      -8.0, 12.0, 800))
        bound = math.sqrt(eps * energy)
        if not err < bound:
            raise SystemExit("trace-height-average: the error exceeds the Lean bound")
        errors.append(err)
        bounds.append(bound)
        frames.append([(x, average(x, eps)) for x in xs])
    if any(b >= a for a, b in zip(errors, errors[1:])):
        raise SystemExit("trace-height-average: the error does not decrease with the strip")

    scene = Scene(
        "trace-height-average",
        "Strip averages converge to the trace",
        r"The function \(u(x,t)=e^{-(x-1.2t)^2-t}\) on the half-plane \(t>0\). Left: level "
        r"curves of \(u\) and the strip \(0<t<\varepsilon\). Right: the restriction "
        r"\(u(x,0)=e^{-x^2}\) (dashed) and the strip average "
        r"\(A_\varepsilon u(x)=\varepsilon^{-1}\int_0^\varepsilon u(x,t)\,dt\) for "
        r"\(\varepsilon=0.8,0.4,0.2,0.1,0.05\), all drawn faintly, with one highlighted at a "
        r"time. The average reads \(u\) only inside the half-plane. The labels give the "
        r"computed \(L^2\) distance to the restriction and the bound "
        r"\(\varepsilon^{1/2}\|\partial_tu\|_{L^2}\) from the height-average theorem at "
        r"\(p=2\). The static frame shows \(\varepsilon=0.8\).",
        "Left, a half-plane with t upward and x across, closed level curves of a bump "
        "that drifts to the right as t grows, and a shaded strip along the boundary. "
        "Right, a dashed Gaussian and five fainter curves below it that approach it as "
        "the strip gets thinner; one of them is highlighted, with its strip width, "
        "its distance to the Gaussian and the theoretical bound.",
        width=640, height=300)
    left = Frame(50, 64, 250, 170, xa, xb, 0.0, 2.2)
    right = Frame(370, 64, 240, 170, xa, xb, -0.05, 1.12)
    scene.panel_title(20, 40, "the half-plane and a strip")
    scene.panel_title(340, 40, "strip averages on the boundary")
    left.axes(scene, x_label="x", origin_y=0)
    right.axes(scene, x_label="x", origin_y=0)
    scene.math(left.x0 - 4, left.y0 - 6, "t", anchor="start", fill="muted")
    for frame in (left, right):
        for tick in (-2, 0, 2, 4):
            scene.tick_label(frame.X(tick), frame.bottom + 16, num(tick), size=10)
    for level in (1, 2):
        scene.tick_label(left.x0 - 7, left.Y(level) + 4, num(level), anchor="end", size=10)
    scene.tick_label(right.x0 - 7, right.Y(1) + 4, "1", anchor="end", size=10)
    strips = [left.fill_to([(xa, eps), (xb, eps)], 0.0) for eps in epsilons]
    scene.area(strips[0], fill="band", anim=[discrete("d", strips)])
    for c in (0.8, 0.5, 0.25, 0.15):
        top = -math.log(c)
        ts = [top * (1 - (1 - k / 60) ** 2) for k in range(61)]
        lower = [(1.2 * t - math.sqrt(max(top - t, 0.0)), t) for t in ts]
        upper = [(1.2 * t + math.sqrt(max(top - t, 0.0)), t) for t in reversed(ts)]
        pts = [(x, t) for x, t in lower + upper if t <= 2.2]
        scene.path(left.curve(pts), stroke="muted", sw=SW_CURVE2)
    scene.path(left.curve([(0, 0), (1.2 * 2.2, 2.2)]), stroke="muted",
               sw=SW_AXIS, dash=DOT)
    scene.math(left.X(1.2 * 2.08) - 6, left.Y(2.08) + 4, r"x=1.2t", t="x = 1.2t",
               anchor="end", fill="muted", size=10, halo=True)
    for index, eps in enumerate(epsilons):
        scene.math(left.X(-2.9), left.Y(eps) - 4, rf"\varepsilon={q2(eps)}",
                   t=f"ε = {q2(eps)}", anchor="start", fill="accent", size=10,
                   halo=True, op=1 if index == 0 else 0,
                   anim=[slot(index, len(epsilons))])
    scene.path(right.sample(g, xa, xb, 280), stroke="ink", sw=SW_CURVE2, dash=DASH)
    curves = right.curve_frames(frames)
    for curve in curves:
        scene.path(curve, stroke="muted", sw=SW_AXIS, sop=0.5)
    scene.path(curves[0], stroke="accent", anim=[discrete("d", curves)])
    scene.math(right.X(-0.9), right.Y(1.04), r"u(x,0)", t="u(x,0)", anchor="end",
               fill="ink", size=11, halo=True)
    for index, (eps, err, bound) in enumerate(zip(epsilons, errors, bounds)):
        show = dict(op=1 if index == 0 else 0, anim=[slot(index, len(epsilons))])
        scene.math(right.right, right.Y(0.95), rf"\varepsilon={q2(eps)}",
                   t=f"ε = {q2(eps)}", anchor="end", fill="accent", size=11, halo=True,
                   **show)
        scene.math(right.right, right.Y(0.95) + 16,
                   rf"\|A_\varepsilon u-u(\cdot,0)\|_2={q3(err)}",
                   t=f"distance {q3(err)}", anchor="end", fill="accent", size=10,
                   halo=True, **show)
        scene.math(right.right, right.Y(0.95) + 32,
                   rf"\varepsilon^{{1/2}}\|\partial_tu\|_2={q3(bound)}",
                   t=f"bound {q3(bound)}", anchor="end", fill="muted", size=10,
                   halo=True, **show)
    scene.text(20, 276, "the average never evaluates u on the boundary line",
               anchor="start", fill="muted", size=11)
    scene.text(340, 276, "the distance shrinks with the strip width", anchor="start",
               fill="muted", size=11)
    return scene


def fig_difference_quotient_limit() -> Scene:
    """Difference quotients of a tent converge; those of a jump blow up."""
    hs = (0.5, 0.3, 0.2, 0.125)

    def tent(x: float) -> float:
        return max(0.0, 1.0 - abs(x))

    def dtent(x: float) -> float:
        return 1.0 if -1 < x < 0 else (-1.0 if 0 < x < 1 else 0.0)

    def quotient(f, x: float, h: float) -> float:
        return (f(x + h) - f(x)) / h

    def step(x: float) -> float:
        return 1.0 if 0 < x < 1 else 0.0

    tent_frames, tent_errors, step_frames = [], [], []
    for h in hs:
        breaks = [-1.6, -1 - h, -1.0, -h, 0.0, 1 - h, 1.0, 1.4]
        tent_frames.append([(x, quotient(tent, x, h)) for x in breaks])
        err = math.sqrt(integrate_pieces(
            lambda x, h=h: (quotient(tent, x, h) - dtent(x)) ** 2, breaks, 400))
        tent_errors.append(err)
        jump = [-1.6, -h, 0.0, 1 - h, 1.0, 1.4]
        norm2 = math.sqrt(integrate_pieces(lambda x, h=h: quotient(step, x, h) ** 2,
                                           jump, 400))
        if abs(norm2 - math.sqrt(2.0 / h)) > 1e-9:
            raise SystemExit("difference-quotient-limit: the jump quotient norm is wrong")
        step_frames.append([(-1.6, 0), (-h, 0), (-h, 1 / h), (0, 1 / h), (0, 0),
                            (1 - h, 0), (1 - h, -1 / h), (1, -1 / h), (1, 0), (1.4, 0)])
    # ramps of width h: 0 to 1 at x = -1 and x = 1, 0 to -2 at x = 0, so 2h in total
    for h, err in zip(hs, tent_errors):
        if abs(err - math.sqrt(2 * h)) > 1e-6:
            raise SystemExit("difference-quotient-limit: tent error is not sqrt(2h)")

    scene = Scene(
        "difference-quotient-limit",
        "Difference quotients of a corner and of a jump",
        r"The forward quotient \(D^hu(x)=(u(x+h)-u(x))/h\) for \(h=0.5,0.3,0.2,0.125\), all "
        r"drawn faintly with one highlighted at a time. Left: the tent "
        r"\(u=\max(0,1-|x|)\), whose weak derivative (dashed) is \(\pm1\). The quotients are "
        r"ramps of width \(h\) around each corner and converge in \(L^2\), with "
        r"\(\|D^hu-u'\|_2=(2h)^{1/2}\). Right: the jump \(u=\mathbf 1_{(0,1)}\). The "
        r"quotient is \(1/h\) on \((-h,0]\) and \(-1/h\) on \([1-h,1)\), so "
        r"\(\|D^hu\|_2=(2/h)^{1/2}\) is unbounded as \(h\to0\), while \(\|D^hu\|_1=2\) for "
        r"every \(h\).",
        "Two panels. Left, a dashed step function equal to one on minus one to zero and "
        "minus one on zero to one, with trapezoid-shaped quotient curves whose ramps "
        "narrow towards the step. Right, two rectangular spikes, up just left of zero "
        "and down just left of one, that grow taller and narrower as h shrinks.",
        width=640, height=300)
    left = Frame(56, 64, 236, 170, -1.6, 1.4, -1.35, 1.35)
    right = Frame(370, 64, 236, 170, -1.6, 1.4, -8.8, 8.8)
    scene.panel_title(24, 40, "a corner: quotients converge")
    scene.panel_title(338, 40, "a jump: quotients blow up")
    left.axes(scene, x_label="x", origin_y=0)
    right.axes(scene, x_label="x", origin_y=0)
    for frame in (left, right):
        for tick in (-1, 0, 1):
            scene.tick_label(frame.X(tick), frame.bottom + 16, num(tick), size=10)
    for level in (-1, 1):
        scene.tick_label(left.x0 - 7, left.Y(level) + 4, num(level), anchor="end", size=10)
    for level in (-8, -4, 4, 8):
        scene.tick_label(right.x0 - 7, right.Y(level) + 4, num(level), anchor="end",
                         size=10)
    scene.path(left.sample(tent, -1.6, 1.4, 60), stroke="muted", sw=SW_AXIS)
    scene.path(left.curve([(-1.6, 0), (-1, 0)]), stroke="ink", sw=SW_CURVE2, dash=DASH)
    scene.path(left.curve([(-1, 1), (0, 1)]), stroke="ink", sw=SW_CURVE2, dash=DASH)
    scene.path(left.curve([(0, -1), (1, -1)]), stroke="ink", sw=SW_CURVE2, dash=DASH)
    scene.path(left.curve([(1, 0), (1.4, 0)]), stroke="ink", sw=SW_CURVE2, dash=DASH)
    scene.math(left.X(-0.5), left.Y(1) - 8, "u'", fill="ink", size=11, halo=True)
    scene.math(left.X(0.95), left.Y(0.35), "u", fill="muted", size=11, halo=True)
    curves = left.curve_frames(tent_frames, tol=0.0)
    for curve in curves:
        scene.path(curve, stroke="muted", sw=SW_AXIS, sop=0.5)
    scene.path(curves[0], stroke="accent", anim=[discrete("d", curves)])
    spikes = right.curve_frames(step_frames, tol=0.0)
    for spike in spikes:
        scene.path(spike, stroke="muted", sw=SW_AXIS, sop=0.5)
    scene.path(spikes[0], stroke="accent", anim=[discrete("d", spikes)])
    scene.path(right.curve([(-1.6, 0), (0, 0), (0, 1), (1, 1), (1, 0), (1.4, 0)]),
               stroke="ink", sw=SW_CURVE2, dash=DASH)
    scene.math(right.X(0.5), right.Y(1) - 6, "u", fill="ink", size=11, halo=True)
    for index, (h, err) in enumerate(zip(hs, tent_errors)):
        show = dict(op=1 if index == 0 else 0, anim=[slot(index, len(hs))])
        scene.math(left.X(-1.55), left.Y(-0.7), rf"h={q3(h)}", t=f"h = {q3(h)}",
                   anchor="start", fill="accent", size=11, halo=True, **show)
        scene.math(left.X(-1.55), left.Y(-0.7) + 16, rf"\|D^hu-u'\|_2={q3(err)}",
                   t=f"L2 error {q3(err)}", anchor="start", fill="accent", size=10,
                   halo=True, **show)
        scene.math(right.right, right.Y(7.5), rf"h={q3(h)}", t=f"h = {q3(h)}",
                   anchor="end", fill="accent", size=11, halo=True, **show)
        scene.math(right.right, right.Y(7.5) + 16,
                   rf"\|D^hu\|_2={q3(math.sqrt(2 / h))}",
                   t=f"L2 norm {q3(math.sqrt(2 / h))}", anchor="end", fill="accent",
                   size=10, halo=True, **show)
    scene.text(24, 276, "the error is the square root of 2h", anchor="start",
               fill="muted", size=11)
    scene.math(338, 276, r"\|D^hu\|_1=2\text{ for every }h", t="L1 norm 2 for every h",
               anchor="start", fill="muted", size=11)
    return scene


def _gagliardo_energy(s: float, delta: float) -> float:
    """Energy of the zero extension of 1 on (0,1), pairs within delta of an endpoint cut."""
    if abs(s - 0.5) < 1e-12:
        return 4.0 * math.log(1.0 / delta)
    return (2.0 / s) * (1.0 - delta ** (1.0 - 2.0 * s)) / (1.0 - 2.0 * s)


def fig_gagliardo_boundary_energy() -> Scene:
    """The Gagliardo energy of a jump is finite exactly below order one half."""
    orders = (0.25, 0.4, 0.5, 0.55)
    # check the inner integral and the closed form against quadrature
    for s in orders:
        for x in (0.1, 0.5):
            # y = x - x e^w maps w in (0, inf) onto y in (-inf, 0)
            inner = integrate_mid(lambda w, s=s, x=x: (x * math.exp(w)) ** (-1 - 2 * s)
                                  * x * math.exp(w), 0.0, 40.0 / s, 20000)
            if abs(inner - x ** (-2 * s) / (2 * s)) > 1e-4 * x ** (-2 * s):
                raise SystemExit("gagliardo-boundary-energy: the inner integral is wrong")
        delta = 1e-2
        numeric = 4 * integrate_mid(lambda x, s=s: x ** (-2 * s) / (2 * s), delta, 1.0, 20000)
        if abs(numeric - _gagliardo_energy(s, delta)) > 1e-5 * numeric:
            raise SystemExit("gagliardo-boundary-energy: the truncated energy is wrong")
    scene = Scene(
        "gagliardo-boundary-energy",
        "The Gagliardo energy of a jump",
        r"The zero extension of \(u=1\) on \((0,1)\) to the real line. Left: in the "
        r"\((x,y)\) plane the difference \(|u(x)-u(y)|\) is one on the shaded strips, where "
        r"exactly one of \(x,y\) lies in \((0,1)\), and zero elsewhere. The kernel "
        r"\(|x-y|^{-1-2s}\) is singular on the dashed diagonal, which the strips touch only "
        r"at the corners \((0,0)\) and \((1,1)\). Right: the energy "
        r"\(E_s(\delta)=\frac2s\int_\delta^1x^{-2s}\,dx\) of the strips after removing "
        r"points \(x\) within \(\delta\) of an endpoint, against \(\log_{10}(1/\delta)\). "
        r"For \(s<1/2\) it increases to the dashed limit \(2/(s(1-2s))\); at \(s=1/2\) it "
        r"grows like \(4\log(1/\delta)\), and for \(s>1/2\) like a power of \(1/\delta\).",
        "Left, a square grid picture: the unit square in the middle, four shaded strips "
        "leaving its sides horizontally and vertically, and a dashed diagonal through "
        "two corners of the square. Right, four increasing curves against the logarithm "
        "of one over delta: two level off at dashed horizontal lines, one rises linearly, "
        "and one rises steeply out of the top of the panel.",
        width=640, height=300)
    left = Frame(56, 64, 190, 190, -1.0, 2.0, -1.0, 2.0)
    right = Frame(340, 64, 250, 170, 0.0, 6.0, 0.0, 60.0)
    scene.panel_title(24, 40, "where the difference is nonzero")
    scene.panel_title(310, 40, "the energy near the endpoints")
    for lo, hi in ((-1.0, 0.0), (1.0, 2.0)):
        scene.area(left.fill_to([(lo, 1.0), (hi, 1.0)], 0.0), fill="band")
        scene.area(left.fill_to([(0.0, hi), (1.0, hi)], lo), fill="band")
    scene.rect(left.X(-1), left.Y(2), left.w, left.h, stroke="muted", fill="",
               sw=SW_AXIS)
    scene.rect(left.X(0), left.Y(1), left.X(1) - left.X(0), left.Y(0) - left.Y(1),
               stroke="ink", fill="", sw=SW_CURVE2)
    scene.line(left.X(-1), left.Y(-1), left.X(2), left.Y(2), stroke="accent", sw=SW_CURVE2,
               dash=DASH)
    for x, y in ((0, 0), (1, 1)):
        scene.circle(left.X(x), left.Y(y), 3.5, fill="accent")
    for tick in (0, 1):
        scene.tick_label(left.X(tick), left.bottom + 16, num(tick), size=10)
        scene.tick_label(left.x0 - 7, left.Y(tick) + 4, num(tick), anchor="end", size=10)
    scene.math(left.right + 8, left.Y(-0.5) + 4, "x", anchor="start", fill="muted")
    scene.math(left.X(-0.5), left.y0 - 6, "y", fill="muted")
    scene.math(left.X(1.5), left.Y(0.5) + 4, "1", fill="ink", size=11, halo=True)
    scene.math(left.X(0.5), left.Y(0.5) + 4, "0", fill="muted", size=11, halo=True)
    scene.math(left.X(1.5), left.Y(1.6), r"y=x", t="y = x", fill="accent", size=10,
               halo=True)
    right.axes(scene, origin_y=0)
    scene.math(right.X(3), right.bottom + 34, r"\log_{10}(1/\delta)",
               t="log10(1/δ)", fill="muted", size=11)
    scene.math(right.x0 - 4, right.y0 - 8, r"E_s(\delta)", t="E_s(δ)", anchor="start",
               fill="muted", size=11)
    for tick in (0, 2, 4, 6):
        scene.tick_label(right.X(tick), right.bottom + 16, num(tick), size=10)
    for level in (0, 20, 40, 60):
        scene.tick_label(right.x0 - 7, right.Y(level) + 4, num(level), anchor="end", size=10)
    window = scene.clip("energy", right.x0, right.y0, right.w, right.h)
    roles = {0.25: "accent", 0.4: "accent2", 0.5: "ink", 0.55: "warn"}
    for s in orders:
        pts = [(v, _gagliardo_energy(s, 10 ** (-v))) for v in
               [0.3 + 5.7 * k / 240 for k in range(241)]]
        scene.path(right.curve(pts), stroke=roles[s], clip=window)
        if s < 0.5:
            limit = 2 / (s * (1 - 2 * s))
            scene.line(right.x0, right.Y(limit), right.right, right.Y(limit),
                       stroke=roles[s], sw=SW_AXIS, dash=DASH)
            scene.math(right.right - 4, right.Y(limit) - 5, rf"s={q2(s)}",
                       t=f"s = {q2(s)}", anchor="end", fill=roles[s], size=10, halo=True)
    scene.math(right.X(5.2), right.Y(4 * math.log(10 ** 5.2)) - 8, r"s=0.5",
               t="s = 0.5", anchor="end", fill="ink", size=10, halo=True)
    top_v = next(v for v in [0.3 + 5.7 * k / 2400 for k in range(2401)]
                 if _gagliardo_energy(0.55, 10 ** (-v)) > 60.0)
    scene.math(right.X(top_v) - 6, right.y0 + 12, r"s=0.55", t="s = 0.55", anchor="end",
               fill="warn", size=10, halo=True)
    scene.text(24, 290, "shaded: exactly one point in (0,1)", anchor="start",
               fill="muted", size=11)
    scene.text(310, 290, "finite total energy exactly for s below one half",
               anchor="start", fill="muted", size=11)
    return scene


#
# Five figures for the elliptic chapter. Every helper here carries an `ell_`
# prefix so that no other chapter block can shadow it.

def ell_disc_path(frame: Frame, cx: float, cy: float, r: float, n: int = 96,
                  reverse: bool = False) -> str:
    """A closed polygonal circle in data coordinates."""
    angles = [2.0 * math.pi * k / n for k in range(n)]
    if reverse:
        angles.reverse()
    return poly_path([(frame.X(cx + r * math.cos(a)), frame.Y(cy + r * math.sin(a)))
                      for a in angles]) + "Z"


def ell_level_path(frame: Frame, f, box, level: float, keep, n: int = 110) -> str:
    chains = clip_chains(join_segments(contours(f, *box, level, n)), keep)
    return chain_path(frame, chains)


def fig_ell_hopf_lemma() -> Scene:
    """A strict boundary maximum, the annulus, and the exponential barrier."""
    alpha = 5.0

    def u(x: float, y: float) -> float:
        """Harmonic: the real part of z - 0.2 z^2."""
        return x - 0.2 * (x * x - y * y)

    top = u(1.0, 0.0)

    def barrier(r: float) -> float:
        return math.exp(-alpha * r * r) - math.exp(-alpha)

    def barrier_laplacian(r: float) -> float:
        return (4.0 * alpha * alpha * r * r - 4.0 * alpha) * math.exp(-alpha * r * r)

    if min(barrier_laplacian(0.5 + 0.5 * k / 200) for k in range(201)) <= 0.0:
        raise SystemExit("hopf-lemma: the barrier is not subharmonic on the annulus")
    turn = 2.0 * math.pi
    inner_gap = min(top - u(0.5 * math.cos(turn * k / 2000), 0.5 * math.sin(turn * k / 2000))
                    for k in range(2000))
    eps = inner_gap / barrier(0.5)
    for i in range(1, 60):
        r = 0.5 + 0.5 * i / 60
        for k in range(720):
            a = turn * k / 720
            if top - u(r * math.cos(a), r * math.sin(a)) < eps * barrier(r) - 1e-12:
                raise SystemExit("hopf-lemma: the barrier comparison fails")
    for k in range(1, 720):
        a = turn * k / 720
        if u(math.cos(a), math.sin(a)) >= top:
            raise SystemExit("hopf-lemma: the boundary maximum is not strict")
    h = 1e-6
    slope_u = (u(1.0, 0.0) - u(1.0 - h, 0.0)) / h
    slope_v = eps * 2.0 * alpha * math.exp(-alpha)
    if not slope_u > slope_v > 0.0:
        raise SystemExit("hopf-lemma: the slopes are out of order")
    rs = [0.5 + 0.5 * k / 200 for k in range(201)]
    cross = 0.8
    square = eps * barrier(cross) / (1.0 - cross) ** 2
    if any(square * (1.0 - r) ** 2 >= top - u(r, 0.0) for r in rs[:-1]):
        raise SystemExit("hopf-lemma: the dotted profile should stay below the gap")

    scene = Scene(
        "hopf-lemma",
        "Hopf's lemma: a strict boundary maximum has a nonzero normal slope",
        r"Left: the harmonic function \(u=\operatorname{Re}(z-0.2z^2)\) on the unit disc "
        r"attains its maximum \(0.8\) only at \(x_0=(1,0)\). The shaded annulus "
        r"\(\tfrac12<|x|<1\) is the only region where the Lean statement asks for "
        r"ellipticity, coefficient bounds and \(Lu\le 0\). Right: along the radius "
        r"ending at \(x_0\), the gap \(u(x_0)-u\) stays above \(\varepsilon v\), where "
        r"\(v=e^{-5|x|^2}-e^{-5}\) vanishes on the circle and \(\Delta v>0\) on the "
        r"annulus. The constant \(\varepsilon\approx" + q3(eps) + r"\) is the smallest gap "
        r"on the inner circle divided by \(v\) there, and the inequality is checked on a "
        r"polar grid of the annulus. Both curves vanish at \(x_0\), so the slope of the gap is "
        r"at least the slope of \(\varepsilon v\), which is \(" + q3(slope_v) + r"\); the "
        r"actual normal derivative is \(" + q3(slope_u) + r"\). The dotted profile vanishes "
        r"to second order at \(x_0\) and crosses below the barrier at \(|x|=0.8\), which is "
        r"what the lemma rules out.",
        "A disc with level curves of a harmonic function, an outer annulus shaded, "
        "a marked boundary point with an outward arrow, and a radius drawn to it; "
        "beside it, a graph over the radius of the gap to the maximum, lying above "
        "an exponential barrier curve, with a dotted parabola crossing below the barrier "
        "near the boundary point.",
        width=640.0, height=318.0)

    disc = Frame(34, 64, 214, 214, -1.12, 1.38, -1.25, 1.25)
    unit = disc.w / (disc.xmax - disc.xmin)
    scene.panel_title(22, 30, "a strict maximum on the boundary")
    scene.math(22, 47, r"u=\operatorname{Re}(z-0.2z^2),\ \ \max u=u(x_0)",
               t="u = Re(z − 0.2 z²), max u = u(x₀)", anchor="start", fill="muted")
    scene.area(ell_disc_path(disc, 0, 0, 1.0) + ell_disc_path(disc, 0, 0, 0.5, reverse=True),
               fill="band")
    inside = lambda x, y: x * x + y * y <= 0.995
    for level in (-1.0, -0.6, -0.3, 0.0, 0.3, 0.55, 0.72):
        scene.path(ell_level_path(disc, u, (-1.0, 1.0, -1.0, 1.0), level, inside),
                   stroke="muted", sw=SW_CURVE2, sop=0.6)
    scene.circle(disc.X(0), disc.Y(0), 0.5 * unit, stroke="muted", fill="",
                 sw=SW_CURVE2, dash=DASH)
    scene.circle(disc.X(0), disc.Y(0), unit, stroke="ink", fill="", sw=SW_CURVE2)
    scene.line(disc.X(0.5), disc.Y(0), disc.X(1.0), disc.Y(0), stroke="accent", sw=SW_CURVE)
    scene.circle(disc.X(0), disc.Y(0), 2.5, fill="muted")
    scene.math(disc.X(0) - 5, disc.Y(0) + 13, r"z", anchor="end", fill="muted", halo=True)
    draw_arrow(scene, [(disc.X(1.0), disc.Y(0)), (disc.X(1.32), disc.Y(0))], role="ink")
    scene.math(disc.X(1.2), disc.Y(0) - 8, r"\nu", t="nu", fill="ink", halo=True)
    scene.circle(disc.X(1.0), disc.Y(0), 3.2, fill="accent")
    scene.math(disc.X(1.0) + 6, disc.Y(0) + 16, r"x_0", anchor="start", fill="accent",
               halo=True)
    scene.math(disc.X(0.0), disc.Y(-1.0) + 20, r"\tfrac12<|x-z|<1",
               t="1/2 < |x - z| < 1", fill="muted", halo=True, size=10)

    graph = Frame(338, 76, 262, 176, 0.5, 1.0, 0.0, 0.4)
    scene.panel_title(318, 30, "the gap along the radius")
    scene.math(318, 47, r"u(x_0)-u\ \ge\ \varepsilon v\text{ on the annulus}",
               t="u(x₀) − u ≥ εv on the annulus", anchor="start", fill="muted")
    graph.axes(scene)
    for tick, name in ((0.5, r"\tfrac12"), (0.75, "0.75"), (1.0, r"1")):
        scene.line(graph.X(tick), graph.bottom, graph.X(tick), graph.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(graph.X(tick), graph.bottom + 17, name, size=9.5)
    for value in (0.0, 0.2, 0.4):
        scene.tick_label(graph.x0 - 7, graph.Y(value) + 3, q2(value), anchor="end",
                         size=9.5)
    scene.math(graph.right, graph.bottom + 32, r"|x-z|", t="|x − z|", anchor="end",
               fill="muted")
    gap = [(r, top - u(r, 0.0)) for r in rs]
    lower = [(r, eps * barrier(r)) for r in rs]
    profile = [(r, square * (1.0 - r) ** 2) for r in rs]
    scene.area(graph.band(lower, gap), fill="band")
    scene.path(graph.curve(profile), stroke="warn", sw=SW_CURVE2, dash=DOT)
    scene.path(graph.curve(lower), stroke="accent2", sw=SW_CURVE2)
    scene.path(graph.curve(gap), stroke="accent", sw=SW_CURVE)
    reach = 0.7
    scene.line(graph.X(reach), graph.Y(slope_v * (1.0 - reach)), graph.X(1.0), graph.Y(0),
               stroke="accent2", sw=SW_AXIS, dash=DASH)
    scene.circle(graph.X(cross), graph.Y(eps * barrier(cross)), 3.0, fill="warn")
    scene.math(graph.X(0.66), graph.Y(top - u(0.66, 0)) - 8, r"u(x_0)-u", t="u(x₀) − u",
               anchor="start", fill="accent", halo=True)
    scene.math(graph.X(0.665), graph.Y(eps * barrier(0.665)) - 8, r"\varepsilon v",
               t="εv", anchor="start", fill="accent2", halo=True)
    scene.math(graph.X(0.515), graph.Y(0.12),
               r"c(1-|x|)^2", t="c(1 − |x|)²", anchor="start", fill="warn", size=10,
               halo=True)
    scene.circle(graph.X(1.0), graph.Y(0.0), 3.2, fill="accent")
    scene.math(graph.X(1.0) - 2, graph.Y(0.0) - 9, r"x_0", anchor="end", fill="accent",
               halo=True)
    scene.math(318, 300, rf"\partial_\nu u(x_0)={q3(slope_u)}\ \ge\ \varepsilon\,|\partial_\nu v(x_0)|={q3(slope_v)}>0",
               t=f"normal derivative {q3(slope_u)} ≥ barrier slope {q3(slope_v)} > 0",
               anchor="start", fill="ink", size=10.5)
    return scene


def fig_ell_harnack_disc() -> Scene:
    """Poisson kernels on the disc, all inside the Harnack band."""
    def poisson(x: float, y: float, phi: float) -> float:
        s = 1.0 - x * x - y * y
        d = (x - math.cos(phi)) ** 2 + (y - math.sin(phi)) ** 2
        return s / d

    def upper(r: float) -> float:
        return (1.0 + r) / (1.0 - r)

    for j in range(0, 181):
        phi = math.pi * j / 180
        for i in range(0, 91):
            r = 0.9 * i / 90
            value = poisson(r, 0.0, phi)
            if value > upper(r) * (1 + 1e-12) or value < (1 - 1e-12) / upper(r):
                raise SystemExit("harnack-disc: a Poisson kernel leaves the band")
    mean = sum(poisson(0.4 * math.cos(2 * math.pi * k / 4000), 0.4 * math.sin(2 * math.pi * k / 4000),
                       0.0) for k in range(4000)) / 4000
    if abs(mean - 1.0) > 1e-9:
        raise SystemExit("harnack-disc: the kernel does not average to its centre value")
    rho = 0.5
    ratio = upper(rho) ** 2

    scene = Scene(
        "harnack-disc",
        "Positive harmonic functions on the disc cannot vary too fast inside",
        r"Left: level curves of the Poisson kernel \(P(x,\zeta)=(1-|x|^2)/|x-\zeta|^2\) for "
        r"\(\zeta=(1,0)\). They are circles tangent to the boundary at \(\zeta\). "
        r"Right: \(u(x)/u(0)\) along the segment from \(0\) to \(\zeta\), on a logarithmic scale, "
        r"for the kernels with poles at angles \(0,\pi/4,\pi/2,3\pi/4,\pi\). Every one stays "
        r"in the shaded band \((1-r)/(1+r)\le u/u(0)\le(1+r)/(1-r)\), whose edges are "
        r"the kernels with poles at \(0\) and \(\pi\); the inequality is checked on a grid of "
        r"181 poles. Positive harmonic functions on the disc are averages of these kernels, so "
        r"they all obey the same bound. On the dashed disc \(|x|\le\tfrac12\) this gives "
        r"\(\sup u\le 9\inf u\). The Lean theorem proves that some such constant exists on "
        r"any compact subset, by chaining balls, without computing the sharp value.",
        "A disc with a family of circles tangent at one boundary point and a smaller "
        "dashed disc inside; beside it, on a logarithmic vertical axis, five curves "
        "fanning out from the value one at the origin, all inside a shaded band whose "
        "edges are two of the curves.",
        width=640.0, height=300.0)

    disc = Frame(36, 70, 196, 196, -1.1, 1.1, -1.1, 1.1)
    unit = disc.w / (disc.xmax - disc.xmin)
    scene.panel_title(22, 30, "one positive harmonic function")
    scene.math(22, 47, r"P(\cdot,\zeta)>0,\ \ P(0,\zeta)=1", t="P(·, ζ) > 0, P(0, ζ) = 1",
               anchor="start", fill="muted")
    inside = lambda x, y: x * x + y * y <= 0.995
    logp = lambda x, y: math.log(max(poisson(x, y, 0.0), 1e-9)) if x * x + y * y < 1 else -20.0
    for level in (0.25, 0.5, 1.0, 2.0, 4.0, 8.0):
        scene.path(ell_level_path(disc, logp, (-1.0, 1.0, -1.0, 1.0), math.log(level), inside, 140),
                   stroke="accent" if level == 1.0 else "muted",
                   sw=SW_CURVE2, sop=1 if level == 1.0 else 0.65)
    scene.circle(disc.X(0), disc.Y(0), rho * unit, stroke="accent2", fill="", sw=SW_CURVE2,
                 dash=DASH)
    scene.circle(disc.X(0), disc.Y(0), unit, stroke="ink", fill="", sw=SW_CURVE2)
    scene.line(disc.X(0), disc.Y(0), disc.X(1), disc.Y(0), stroke="ink", sw=SW_AXIS, dash=DOT)
    scene.circle(disc.X(0), disc.Y(0), 2.6, fill="ink")
    scene.math(disc.X(0) - 4, disc.Y(0) + 14, r"0", anchor="end", fill="ink", halo=True)
    scene.circle(disc.X(1), disc.Y(0), 3.0, fill="accent")
    scene.math(disc.X(1) + 6, disc.Y(0) + 4, r"\zeta", t="zeta", anchor="start", fill="accent")
    scene.math(disc.X(-0.35), disc.Y(0.28), r"|x|\le\tfrac12", t="|x| ≤ 1/2", fill="accent2",
               halo=True, size=10)
    scene.math(disc.X(0.18), disc.Y(0.62), r"P=1", fill="accent", halo=True, size=10)

    top = math.log(upper(0.9) * 1.1)
    graph = Frame(334, 64, 262, 196, 0.0, 0.9, -top, top)
    scene.panel_title(318, 30, "the ratio along the radius")
    scene.math(318, 47, r"\frac{1-r}{1+r}\le\frac{u(r)}{u(0)}\le\frac{1+r}{1-r}",
               t="(1 − r)/(1 + r) ≤ u(r)/u(0) ≤ (1 + r)/(1 − r)", anchor="start",
               fill="muted", size=10.5)
    scene.line(graph.x0, graph.y0, graph.x0, graph.bottom, stroke="muted", sw=SW_AXIS)
    scene.line(graph.x0, graph.bottom, graph.right, graph.bottom, stroke="muted", sw=SW_AXIS)
    scene.line(graph.x0, graph.Y(0), graph.right, graph.Y(0), stroke="muted", sw=SW_AXIS,
               dash=DOT)
    for value, name in ((1 / 9, r"\tfrac19"), (1 / 3, r"\tfrac13"), (1.0, "1"), (3.0, "3"),
                        (9.0, "9")):
        scene.line(graph.x0 - 4, graph.Y(math.log(value)), graph.x0, graph.Y(math.log(value)),
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(graph.x0 - 7, graph.Y(math.log(value)) + 3, name, anchor="end",
                         size=9.5)
    rs = [0.9 * k / 180 for k in range(181)]
    hi = [(r, math.log(upper(r))) for r in rs]
    lo = [(r, -math.log(upper(r))) for r in rs]
    scene.area(graph.band(lo, hi), fill="band")
    scene.line(graph.X(rho), graph.y0, graph.X(rho), graph.bottom, stroke="accent2",
               sw=SW_AXIS, dash=DASH)
    for tick in (0.0, 0.5, 0.9):
        scene.line(graph.X(tick), graph.bottom, graph.X(tick), graph.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(graph.X(tick), graph.bottom + 16, q2(tick), size=9.5)
    scene.math(graph.right, graph.bottom + 28, r"r=|x|", t="r = |x|", anchor="end",
               fill="muted")
    for j, phi in enumerate((0.0, math.pi / 4, math.pi / 2, 3 * math.pi / 4, math.pi)):
        points = [(r, math.log(poisson(r, 0.0, phi))) for r in rs]
        edge = j in (0, 4)
        scene.path(graph.curve(points), stroke="accent" if edge else "muted",
                   sw=SW_CURVE if edge else SW_CURVE2)
    scene.math(graph.X(0.72), graph.Y(math.log(upper(0.72))) - 4, r"\text{pole at }0",
               t="pole at 0", anchor="end", fill="accent", halo=True, size=10)
    scene.math(graph.X(0.72), graph.Y(-math.log(upper(0.72))) + 14, r"\text{pole at }\pi",
               t="pole at π", anchor="end", fill="accent", halo=True, size=10)
    scene.math(22, 292, rf"\text{{on the dashed disc: }}\sup_{{|x|\le 1/2}}u\le {q2(ratio)}\,\inf_{{|x|\le 1/2}}u",
               t=f"sup ≤ {q2(ratio)} inf on |x| ≤ 1/2", anchor="start", fill="accent2",
               halo=True, size=10)
    return scene


def fig_ell_green_disc() -> Scene:
    """The disc Green function by reflection, and its Poisson kernel."""
    pole = (0.5, 0.2)
    size2 = pole[0] ** 2 + pole[1] ** 2
    image = (pole[0] / size2, pole[1] / size2)

    def phi(x: float, y: float) -> float:
        return -math.log(math.hypot(x, y)) / (2.0 * math.pi)

    def green(p, q) -> float:
        """G(p, q) = Phi(q - p) - Phi(|p| (q - p*)), with p* = p / |p|^2."""
        s = p[0] ** 2 + p[1] ** 2
        if s == 0.0:
            return phi(q[0], q[1]) - phi(1.0, 0.0)
        star = (p[0] / s, p[1] / s)
        r = math.sqrt(s)
        return phi(q[0] - p[0], q[1] - p[1]) - phi(r * (q[0] - star[0]), r * (q[1] - star[1]))

    turn = 2.0 * math.pi
    for k in range(360):
        a = turn * k / 360
        if abs(green(pole, (math.cos(a), math.sin(a)))) > 1e-12:
            raise SystemExit("green-disc: G does not vanish on the circle")
    samples = [(0.3 * math.cos(1.3 * k), 0.7 * math.sin(0.9 * k)) for k in range(1, 40)]
    for p in samples:
        for q in samples:
            if p != q and abs(green(p, q) - green(q, p)) > 1e-11:
                raise SystemExit("green-disc: G is not symmetric")

    def kernel(rho: float, theta: float) -> float:
        return (1.0 - rho * rho) / (turn * (1.0 - 2.0 * rho * math.cos(theta) + rho * rho))

    h = 1e-6
    for k in range(12):
        a = turn * k / 12
        zeta = (math.cos(a), math.sin(a))
        inward = green(pole, ((1 - h) * zeta[0], (1 - h) * zeta[1])) / h
        dx, dy = pole[0] - zeta[0], pole[1] - zeta[1]
        exact = (1.0 - size2) / (turn * (dx * dx + dy * dy))
        if abs(inward - exact) > 1e-4 * exact:
            raise SystemExit("green-disc: the normal derivative is not the Poisson kernel")
    radii = (0.0, 0.4, 0.6, 0.75)
    for rho in radii:
        if abs(integrate_mid(lambda t: kernel(rho, t), -math.pi, math.pi, 4000) - 1.0) > 1e-9:
            raise SystemExit("green-disc: a Poisson kernel does not have mass one")

    scene = Scene(
        "green-disc",
        "The Green function of the disc, and the Poisson kernel it produces",
        r"Left: level curves of \(G(x,\cdot)\) for the unit disc and the pole "
        r"\(x=(0.5,0.2)\). The corrector is the fundamental solution centred at the "
        r"reflected point \(x^*=x/|x|^2\), scaled by \(|x|\), so the difference vanishes on the "
        r"circle; outside the disc the same formula continues with its second pole at \(x^*\), "
        r"drawn dashed. The generator checks \(G=0\) on the circle and \(G(x,y)=G(y,x)\) on "
        r"1521 pairs. Right: the Poisson kernel \(K(x,\zeta)=-\partial_\nu G(x,\zeta)\) as a "
        r"function of the angle between \(\zeta\) and \(x\), for \(|x|=0,0.4,0.6,0.75\). Each "
        r"has mass one, checked by quadrature, and it concentrates at the angle \(0\) as \(x\) "
        r"approaches the boundary, which is why the Poisson integral takes the boundary values.",
        "A disc containing nested closed curves around an interior point, with a dashed "
        "line through the centre and the point to a second point outside the disc, where "
        "dashed curves circle it; beside it, four bell-shaped curves over an angle axis, "
        "each taller and narrower than the last.",
        width=640.0, height=300.0)

    box = (-1.1, 2.25, -1.1, 1.15)
    disc = Frame(22, 74, 283, 190, *box)
    unit = disc.h / (box[3] - box[2])
    scene.panel_title(22, 30, "the pole and its reflection")
    scene.math(22, 47, r"G(x,y)=\Phi(y-x)-\Phi\big(|x|(y-x^*)\big)",
               t="G(x, y) = Φ(y − x) − Φ(|x|(y − x*))", anchor="start", fill="muted")

    def scaled(x: float, y: float) -> float:
        d1 = math.hypot(x - pole[0], y - pole[1])
        d2 = math.hypot(x - image[0], y - image[1])
        return math.log(max(math.sqrt(size2) * d2, 1e-9) / max(d1, 1e-9))

    inside = lambda x, y: x * x + y * y <= 0.995
    outside = lambda x, y: x * x + y * y >= 1.005
    for level in (0.35, 0.7, 1.2, 2.0):
        scene.path(ell_level_path(disc, scaled, box, level, inside, 150),
                   stroke="accent", sw=SW_CURVE2)
    for level in (-1.9, -2.5, -3.2):
        scene.path(ell_level_path(disc, scaled, box, level, outside, 150),
                   stroke="muted", sw=SW_CURVE2, dash=DASH, sop=0.7)
    scene.circle(disc.X(0), disc.Y(0), unit, stroke="ink", fill="", sw=SW_CURVE)
    scene.line(disc.X(0), disc.Y(0), disc.X(image[0]), disc.Y(image[1]), stroke="muted",
               sw=SW_AXIS, dash=DOT)
    scene.circle(disc.X(0), disc.Y(0), 2.4, fill="muted")
    scene.math(disc.X(0) - 4, disc.Y(0) + 13, r"0", anchor="end", fill="muted", halo=True)
    scene.circle(disc.X(pole[0]), disc.Y(pole[1]), 3.2, fill="accent")
    scene.math(disc.X(pole[0]) - 2, disc.Y(pole[1]) - 9, r"x", fill="accent", halo=True)
    scene.circle(disc.X(image[0]), disc.Y(image[1]), 3.2, fill="muted")
    scene.math(disc.X(image[0] + 0.3), disc.Y(image[1] - 0.45), r"x^*", t="x*", anchor="start",
               fill="muted", halo=True)
    scene.math(22, disc.bottom + 20, r"G(x,\cdot)=0\text{ on }\partial B",
               t="G = 0 on the circle", anchor="start", fill="ink", size=10)

    graph = Frame(362, 70, 240, 180, -math.pi, math.pi, 0.0, 1.2)
    scene.panel_title(348, 30, "the Poisson kernel")
    scene.math(348, 47, r"K(x,\zeta)=\frac{1-|x|^2}{2\pi|x-\zeta|^2}",
               t="K(x, ζ) = (1 − |x|²)/(2π|x − ζ|²)", anchor="start", fill="muted", size=10.5)
    graph.axes(scene)
    for tick, name in ((-math.pi, r"-\pi"), (0.0, "0"), (math.pi, r"\pi")):
        scene.line(graph.X(tick), graph.bottom, graph.X(tick), graph.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(graph.X(tick), graph.bottom + 16, name, size=9.5)
    for value in (0, 0.5, 1):
        scene.tick_label(graph.x0 - 7, graph.Y(value) + 3, q2(value), anchor="end",
                         size=9.5)
    scene.math(graph.right, graph.bottom + 30, r"\text{angle from }x/|x|",
               t="angle from x/|x|", anchor="end", fill="muted")
    angles = [-math.pi + turn * k / 400 for k in range(401)]
    scene.area(graph.fill_to([(t, kernel(radii[-1], t)) for t in angles], 0.0), fill="band")
    for index, rho in enumerate(radii):
        points = [(t, kernel(rho, t)) for t in angles]
        last = index == len(radii) - 1
        scene.path(graph.curve(points), stroke="accent" if last else "muted",
                   sw=SW_CURVE if last else SW_CURVE2)
    scene.math(graph.X(0.0) + 8, graph.Y(kernel(radii[-1], 0.0)) + 4,
               rf"|x|={q2(radii[-1])}", t=f"|x| = {q2(radii[-1])}", anchor="start",
               fill="accent", halo=True, size=9.5)
    scene.math(graph.X(-math.pi) + 8, graph.y0 + 8,
               r"\text{grey: }|x|=" + ",\\,".join(q2(r) for r in radii[:-1]),
               t="grey: |x| = " + ", ".join(q2(r) for r in radii[:-1]), anchor="start",
               fill="muted", size=9.5)
    return scene


def ell_bessel_j0(z: float) -> float:
    total, term, k = 0.0, 1.0, 0
    while abs(term) > 1e-17 or k < 4:
        total += term
        k += 1
        term *= -(z * z / 4.0) / (k * k)
    return total


def fig_ell_moving_planes() -> Scene:
    """A plane moving in from the boundary and the reflected cap staying above."""
    j0 = 2.404825557695773
    if abs(ell_bessel_j0(j0)) > 1e-12:
        raise SystemExit("moving-planes: j0 is not a zero of J0")

    def u(x: float, y: float) -> float:
        return ell_bessel_j0(j0 * math.hypot(x, y))

    lambdas = (0.5, 0.35, 0.2, 0.1, 0.0)
    for lam in lambdas:
        for i in range(1, 40):
            x = lam + (1.0 - lam) * i / 40
            for k in range(-40, 41):
                y = math.sqrt(max(1.0 - x * x, 0.0)) * k / 41
                gap = u(2 * lam - x, y) - u(x, y)
                if gap < -1e-12 or (lam == 0.0 and abs(gap) > 1e-12):
                    raise SystemExit("moving-planes: the reflection comparison fails")
    rs = [k / 200 for k in range(201)]
    if any(ell_bessel_j0(j0 * rs[k + 1]) >= ell_bessel_j0(j0 * rs[k]) for k in range(200)):
        raise SystemExit("moving-planes: the profile is not strictly decreasing")

    count = len(lambdas)
    scene = Scene(
        "moving-planes",
        "Moving planes: the reflected cap stays above the solution",
        r"The positive solution \(u(x)=J_0(j_0|x|)\) of \(-\Delta u=j_0^2u\) on the unit disc, "
        r"with \(u=0\) on the circle, where \(j_0\approx2.405\) is the first zero of \(J_0\). "
        r"Left: the plane \(x_1=\lambda\), the cap \(\Sigma_\lambda=\{x\in B: x_1>\lambda\}\) "
        r"shaded, and its mirror image, dashed, which stays inside the disc. Right: \(u\) along "
        r"the \(x_1\)-axis and, over the cap, the reflected profile \(u(2\lambda-x_1,0)\), "
        r"dashed; the shaded gap is \(w_\lambda=u(x^\lambda)-u\ge0\), checked on a grid of each "
        r"cap. The static frame is \(\lambda=\tfrac12\); the animation moves the plane to "
        r"\(\lambda=0\), where the gap closes. The method starts with \(\lambda\) near \(1\), "
        r"where the boundary behaviour gives \(w_\lambda>0\), and the strong maximum principle "
        r"keeps \(w_\lambda>0\) as long as \(\lambda>0\). Running it from every direction makes "
        r"\(u\) radial and strictly decreasing in \(|x|\).",
        "A disc with concentric level circles, a vertical line cutting off a shaded cap "
        "on the right, and a dashed mirror image of the cap on the other side of the "
        "line; beside it, a bell-shaped profile over an axis, a vertical line, and a "
        "dashed reflected profile above it on the right of the line with the gap shaded.",
        width=640.0, height=300.0)

    disc = Frame(34, 72, 196, 196, -1.1, 1.1, -1.1, 1.1)
    unit = disc.w / 2.2
    scene.panel_title(22, 30, "the cap and its reflection")
    scene.math(22, 47, r"x^\lambda=(2\lambda-x_1,\,x_2)", t="x^λ = (2λ − x₁, x₂)",
               anchor="start", fill="muted")

    def cap(lam: float, mirror: bool) -> str:
        top = math.acos(lam)
        pts = []
        for k in range(49):
            a = -top + 2 * top * k / 48
            x, y = math.cos(a), math.sin(a)
            if mirror:
                x = 2 * lam - x
            pts.append((disc.X(x), disc.Y(y)))
        return poly_path(pts) + "Z"

    caps = [cap(lam, False) for lam in lambdas]
    mirrors = [cap(lam, True) for lam in lambdas]
    planes = [(disc.X(lam), disc.Y(math.sqrt(1 - lam * lam)) - 12,
               disc.Y(-math.sqrt(1 - lam * lam)) + 12) for lam in lambdas]
    scene.area(caps[0], fill="band", anim=[discrete("d", caps)])
    inside = lambda x, y: x * x + y * y <= 0.995
    for level in (0.2, 0.4, 0.6, 0.8):
        scene.path(ell_level_path(disc, u, (-1.0, 1.0, -1.0, 1.0), level, inside, 90),
                   stroke="muted", sw=SW_CURVE2, sop=0.55)
    scene.path(mirrors[0], stroke="accent", sw=SW_CURVE2, dash=DASH,
               anim=[discrete("d", mirrors)])
    scene.circle(disc.X(0), disc.Y(0), unit, stroke="ink", fill="", sw=SW_CURVE2)
    scene.line(planes[0][0], planes[0][1], planes[0][0], planes[0][2], stroke="accent2",
               sw=SW_CURVE, anim=[discrete("x1", [q2(p[0]) for p in planes]),
                                  discrete("x2", [q2(p[0]) for p in planes]),
                                  discrete("y1", [q2(p[1]) for p in planes]),
                                  discrete("y2", [q2(p[2]) for p in planes])])
    scene.math(disc.X(0.72), disc.Y(0.0) + 4, r"\Sigma_\lambda", t="Σ_λ", fill="ink",
               halo=True, anim=[discrete("x", [q2(disc.X((1 + lam) / 2)) for lam in lambdas])])

    graph = Frame(352, 76, 250, 170, -1.0, 1.0, 0.0, 1.1)
    scene.panel_title(338, 30, "the profile and its reflection")
    scene.math(338, 47, r"w_\lambda(x)=u(x^\lambda)-u(x)\ \ge 0\text{ on }\Sigma_\lambda",
               t="w_λ = u(x^λ) − u ≥ 0 on Σ_λ", anchor="start", fill="muted")
    graph.axes(scene)
    for tick in (-1.0, 0.0, 1.0):
        scene.line(graph.X(tick), graph.bottom, graph.X(tick), graph.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(graph.X(tick), graph.bottom + 16, num(tick), size=9.5)
    for value in (0, 1):
        scene.tick_label(graph.x0 - 7, graph.Y(value) + 3, str(value), anchor="end",
                         size=9.5)
    scene.math(graph.right, graph.bottom + 30, r"x_1", anchor="end", fill="muted")
    xs = [-1.0 + 2.0 * k / 200 for k in range(201)]
    gaps, reflected, lines, labels = [], [], [], []
    for lam in lambdas:
        seg = [lam + (1 - lam) * k / 80 for k in range(81)]
        lo = [(x, u(x, 0.0)) for x in seg]
        hi = [(x, u(2 * lam - x, 0.0)) for x in seg]
        gaps.append(poly_path(graph.project(lo) + list(reversed(graph.project(hi)))) + "Z")
        reflected.append(poly_path(graph.project(hi)))
        lines.append(q2(graph.X(lam)))
    scene.area(gaps[0], fill="band", anim=[discrete("d", gaps)])
    scene.path(graph.curve([(x, u(x, 0.0)) for x in xs]), stroke="ink", sw=SW_CURVE)
    scene.path(reflected[0], stroke="accent", sw=SW_CURVE2, dash=DASH,
               anim=[discrete("d", reflected)])
    scene.line(graph.X(lambdas[0]), graph.y0, graph.X(lambdas[0]), graph.bottom,
               stroke="accent2", sw=SW_CURVE2,
               anim=[discrete("x1", lines), discrete("x2", lines)])
    for index, lam in enumerate(lambdas):
        scene.math(graph.right, graph.y0 + 4, rf"\lambda={q2(lam)}", t=f"λ = {q2(lam)}",
                   anchor="end", fill="accent2", halo=True, op=1 if index == 0 else 0,
                   anim=[slot(index, count)])
    return scene


def fig_lax_milgram_projection() -> Scene:
    """Lax-Milgram as a projection in the energy geometry, and Galerkin with Cea."""
    # Left panel: H = R^2, B(v, w) = v^T A w with A symmetric positive definite,
    # and the load f = A u for a chosen solution u. The Galerkin subspace is a
    # line V_1 through 0.
    a11, a12, a22 = 2.0, 0.8, 1.0

    def bform(v, w):
        return (v[0] * (a11 * w[0] + a12 * w[1]) + v[1] * (a12 * w[0] + a22 * w[1]))

    det = a11 * a22 - a12 * a12
    if not (a11 > 0 and det > 0):
        raise SystemExit("lax-milgram-projection: the form is not coercive")
    mean, gap = (a11 + a22) / 2, math.hypot((a11 - a22) / 2, a12)
    lam_hi, lam_lo = mean + gap, mean - gap
    target = (0.7, 0.75)
    load = (a11 * target[0] + a12 * target[1], a12 * target[0] + a22 * target[1])
    u = ((a22 * load[0] - a12 * load[1]) / det, (a11 * load[1] - a12 * load[0]) / det)
    if math.hypot(u[0] - target[0], u[1] - target[1]) > 1e-12:
        raise SystemExit("lax-milgram-projection: solving B(u, v) = f(v) failed")

    def energy(v):
        return 0.5 * bform(v, v) - (load[0] * v[0] + load[1] * v[1])

    norm_d = math.hypot(1.0, -0.3)
    d = (1.0 / norm_d, -0.3 / norm_d)
    t1 = (load[0] * d[0] + load[1] * d[1]) / bform(d, d)
    u1 = (t1 * d[0], t1 * d[1])
    tp = u[0] * d[0] + u[1] * d[1]
    p = (tp * d[0], tp * d[1])
    err1 = (u[0] - u1[0], u[1] - u1[1])
    errp = (u[0] - p[0], u[1] - p[1])
    if abs(bform(err1, d)) > 1e-12:
        raise SystemExit("lax-milgram-projection: the Galerkin error is not B-orthogonal")
    for k in range(-400, 401):
        s = t1 + k / 100.0
        if energy((s * d[0], s * d[1])) < energy(u1) - 1e-14:
            raise SystemExit("lax-milgram-projection: u_1 does not minimize J on V_1")
    for k in range(-30, 31):
        for m in range(-30, 31):
            v = (u[0] + k / 10.0, u[1] + m / 10.0)
            if energy(v) < energy(u) - 1e-14:
                raise SystemExit("lax-milgram-projection: u does not minimize J")
    if bform(err1, err1) > bform(errp, errp) + 1e-14:
        raise SystemExit("lax-milgram-projection: u_1 is not the best B-approximation")
    e1, ep = math.hypot(*err1), math.hypot(*errp)
    if e1 > (lam_hi / lam_lo) * ep + 1e-14:
        raise SystemExit("lax-milgram-projection: the Cea bound fails in the plane")
    if e1 <= ep:
        raise SystemExit("lax-milgram-projection: the two projections coincide")

    # The eigenvector of the small eigenvalue, for the long axis of the ellipses.
    ev_lo = (a12, lam_lo - a11)
    ev_len = math.hypot(*ev_lo)
    ev_lo = (ev_lo[0] / ev_len, ev_lo[1] / ev_len)
    ev_hi = (-ev_lo[1], ev_lo[0])

    def ellipse(level):
        """The level set J(v) = J(u) + level, which is B(v - u, v - u) = 2 level."""
        ra, rb = math.sqrt(2 * level / lam_lo), math.sqrt(2 * level / lam_hi)
        pts = []
        for k in range(181):
            t = 2 * math.pi * k / 180
            v = (u[0] + ra * math.cos(t) * ev_lo[0] + rb * math.sin(t) * ev_hi[0],
                 u[1] + ra * math.cos(t) * ev_lo[1] + rb * math.sin(t) * ev_hi[1])
            if abs(energy(v) - energy(u) - level) > 1e-12:
                raise SystemExit("lax-milgram-projection: an ellipse is off its level")
            pts.append(v)
        return pts

    tangent_level = energy(u1) - energy(u)
    levels = [tangent_level * s for s in (0.12, 0.4)] + [tangent_level]

    # Right panels: -((1 + x) u')' = f on (0, 1), u(0) = u(1) = 0, with the exact
    # solution u = sin(pi x), and P1 finite elements on the nested meshes N = 2^k.
    pi = math.pi

    def coef(x):
        return 1.0 + x

    def exact(x):
        return math.sin(pi * x)

    def dexact(x):
        return pi * math.cos(pi * x)

    def rhs(x):
        return (1.0 + x) * pi * pi * math.sin(pi * x) - pi * math.cos(pi * x)

    for x in (0.1, 0.37, 0.8):
        h = 1e-4
        flux = lambda y: coef(y) * dexact(y)
        if abs(-(flux(x + h) - flux(x - h)) / (2 * h) - rhs(x)) > 1e-5:
            raise SystemExit("lax-milgram-projection: f is not -((1 + x) u')'")
    # Five-point Gauss-Legendre on [-1, 1], exact through degree 9, for the load
    # vector and the error integrals; three points left the N = 2 comparison
    # below at the level of the quadrature error.
    inner = math.sqrt(5 - 2 * math.sqrt(10 / 7)) / 3
    outer = math.sqrt(5 + 2 * math.sqrt(10 / 7)) / 3
    w_in, w_out = (322 + 13 * math.sqrt(70)) / 900, (322 - 13 * math.sqrt(70)) / 900
    gauss = ((-outer, w_out), (-inner, w_in), (0.0, 128 / 225), (inner, w_in),
             (outer, w_out))
    for degree in range(10):
        exact_moment = (1 - (-1) ** (degree + 1)) / (degree + 1)
        if abs(sum(w * z ** degree for z, w in gauss) - exact_moment) > 1e-13:
            raise SystemExit("lax-milgram-projection: the Gauss rule is not exact")

    def galerkin(n):
        h = 1.0 / n
        diag, off, rhs_vec = [0.0] * (n + 1), [0.0] * n, [0.0] * (n + 1)
        for e in range(n):
            xa, xb = e * h, (e + 1) * h
            k_e = (1.0 + (xa + xb) / 2) / h
            diag[e] += k_e
            diag[e + 1] += k_e
            off[e] -= k_e
            for z, w in gauss:
                x = (xa + xb) / 2 + z * h / 2
                rhs_vec[e] += w * h / 2 * rhs(x) * (xb - x) / h
                rhs_vec[e + 1] += w * h / 2 * rhs(x) * (x - xa) / h
        # Thomas algorithm on the interior nodes 1..n-1.
        m = n - 1
        c = [0.0] * m
        g = [0.0] * m
        for i in range(m):
            node = i + 1
            denom = diag[node] - (off[node - 1] * c[i - 1] if i > 0 else 0.0)
            c[i] = off[node] / denom if i < m - 1 else 0.0
            g[i] = (rhs_vec[node] - (off[node - 1] * g[i - 1] if i > 0 else 0.0)) / denom
        vals = [0.0] * (n + 1)
        for i in range(m - 1, -1, -1):
            vals[i + 1] = g[i] - (c[i] * vals[i + 2] if i < m - 1 else 0.0)
        return vals

    def seminorm_errors(n, vals):
        h = 1.0 / n
        err, err_a = 0.0, 0.0
        for e in range(n):
            xa = e * h
            slope = (vals[e + 1] - vals[e]) / h
            for z, w in gauss:
                x = xa + h / 2 + z * h / 2
                diff = dexact(x) - slope
                err += w * h / 2 * diff * diff
                err_a += w * h / 2 * coef(x) * diff * diff
        return math.sqrt(err), math.sqrt(err_a)

    meshes = [2, 4, 8, 16, 32, 64]
    table = []
    solutions = {}
    for n in meshes:
        vals = galerkin(n)
        solutions[n] = vals
        interp = [exact(i / n) for i in range(n + 1)]
        e_gal, e_gal_a = seminorm_errors(n, vals)
        e_int, e_int_a = seminorm_errors(n, interp)
        if e_gal_a > e_int_a * (1 + 1e-9):
            raise SystemExit(f"lax-milgram-projection: at N = {n} the Galerkin energy "
                             "error exceeds the interpolant's")
        if e_gal > 2.0 * e_int:
            raise SystemExit(f"lax-milgram-projection: the Cea bound fails at N = {n}")
        table.append((n, e_gal, e_int))
    for (n0, g0, _), (n1, g1, _) in zip(table, table[1:]):
        if not g1 < g0:
            raise SystemExit("lax-milgram-projection: the error does not decrease")
    slope = math.log(table[-2][1] / table[-1][1]) / math.log(2.0)
    if abs(slope - 1.0) > 0.02:
        raise SystemExit(f"lax-milgram-projection: the observed order is {slope}")

    scene = Scene(
        "lax-milgram-projection",
        "Lax-Milgram as a projection, and Galerkin approximation",
        r"Left: a coercive symmetric form \(B(v,w)=v^{\mathsf T}Aw\) on the plane, "
        r"\(A=\begin{pmatrix}2&0.8\\0.8&1\end{pmatrix}\), and a load \(f\). The ellipses are "
        r"level sets of the energy \(J(v)=\tfrac12B(v,v)-f(v)\), centred at its minimizer, "
        r"the solution \(u\) of \(B(u,v)=f(v)\). On the line \(V_1\) the Galerkin solution "
        r"\(u_1\) solves \(B(u_1,v)=f(v)\) for \(v\in V_1\) only. It is the point where a "
        r"level set touches the line, and its error \(u-u_1\), dashed, is \(B\)-orthogonal to "
        r"\(V_1\). The Euclidean foot of the perpendicular \(\Pi u\), hollow, is a different "
        r"point: Galerkin projects in the geometry of \(B\), not of the ambient inner "
        r"product. Right: \(-((1+x)u')'=f\) on \((0,1)\) with \(u=\sin\pi x\), solved with "
        r"piecewise linear elements on the nested meshes \(h=1/N\). The animation refines "
        r"\(N=4,8,16\); the static frame is \(N=4\). Below, the error \(\|u'-u_h'\|_{L^2}\) "
        r"against \(h\) on logarithmic axes, the interpolation error \(\|u'-(I_hu)'\|_{L^2}\), "
        r"and the dashed bound of Cea's lemma, \(M/c=2\) times the interpolation error, where "
        r"\(1\le 1+x\le 2\). Both errors fall like \(h\). Cea's lemma is the classical "
        r"statement; the figure computes it in floating point, and it is not a PDEAtlas theorem.",
        "Left, a coordinate plane with nested tilted ellipses around a marked point u, a line "
        "through the origin, the point u1 where the largest ellipse touches the line, a dashed "
        "segment from u to u1, and a different hollow point on the line where the "
        "perpendicular from u lands. Right top, a sine arch with a piecewise linear "
        "approximation that refines. Right bottom, two rows of error marks falling along "
        "parallel lines on logarithmic axes, under a dashed bound line.",
        width=640.0, height=356.0)

    # --- left: the plane
    plane = Frame(44, 66, 220, 240, -0.45, 1.75, -0.45, 1.95)
    window = scene.clip("plane", plane.x0, plane.y0, plane.w, plane.h)
    scene.panel_title(22, 28, "the solution minimizes the energy")
    scene.math(22, 46, r"B(u-u_1,v)=0\ \text{for all } v\in V_1",
               t="B(u − u₁, v) = 0 for all v in V₁", anchor="start", fill="muted")
    scene.line(plane.X(plane.xmin), plane.Y(0), plane.right, plane.Y(0), stroke="muted",
               sw=SW_AXIS)
    scene.line(plane.X(0), plane.y0, plane.X(0), plane.bottom, stroke="muted", sw=SW_AXIS)
    for index, level in enumerate(levels):
        pts = ellipse(level)
        for x, y in pts:
            if not (plane.xmin < x < plane.xmax and plane.ymin < y < plane.ymax):
                raise SystemExit("lax-milgram-projection: an ellipse leaves the plane")
        last = index == len(levels) - 1
        scene.path(plane.curve(pts) + "Z", stroke="accent2" if last else "muted",
                   sw=SW_CURVE2 if last else SW_AXIS)
    reach = 3.0
    scene.line(plane.X(-reach * d[0]), plane.Y(-reach * d[1]), plane.X(reach * d[0]),
               plane.Y(reach * d[1]), stroke="ink", sw=SW_CURVE2, clip=window)
    scene.math(plane.X(-0.3 * d[0]), plane.Y(-0.3 * d[1]) - 10, r"V_1", fill="ink",
               halo=True)
    scene.line(plane.X(u[0]), plane.Y(u[1]), plane.X(u1[0]), plane.Y(u1[1]),
               stroke="accent2", sw=SW_CURVE2, dash=DASH)
    scene.line(plane.X(u[0]), plane.Y(u[1]), plane.X(p[0]), plane.Y(p[1]),
               stroke="muted", sw=SW_AXIS, dash=DOT)
    scene.circle(plane.X(0), plane.Y(0), 2.4, fill="muted")
    scene.math(plane.X(0) - 6, plane.Y(0) + 14, "0", anchor="end", fill="muted", size=9.5)
    scene.circle(plane.X(p[0]), plane.Y(p[1]), 3.6, stroke="ink", fill="surface", sw=1.4)
    scene.math(plane.X(p[0]) - 2, plane.Y(p[1]) + 18, r"\Pi u", t="Πu", fill="ink",
               halo=True)
    scene.circle(plane.X(u1[0]), plane.Y(u1[1]), 3.6, fill="accent2")
    scene.math(plane.X(u1[0]) + 4, plane.Y(u1[1]) + 18, r"u_1", fill="accent2",
               anchor="start", halo=True)
    scene.circle(plane.X(u[0]), plane.Y(u[1]), 3.6, fill="accent")
    scene.math(plane.X(u[0]) + 7, plane.Y(u[1]) - 7, "u", fill="accent", anchor="start",
               halo=True)
    scene.math(22, 330, rf"|u-u_1|={q3(e1)}\ \le\ \tfrac{{M}}{{c}}\,|u-\Pi u|"
               rf"={q3(lam_hi / lam_lo)}\cdot{q3(ep)}",
               t=f"|u − u₁| = {q3(e1)} ≤ (M/c)|u − Πu| = {q3(lam_hi / lam_lo)}·{q3(ep)}",
               anchor="start", fill="muted", size=9.5)
    scene.math(22, 346, rf"B(u-u_1,u-u_1)={q3(bform(err1, err1))}\ \le\ "
               rf"B(u-\Pi u,u-\Pi u)={q3(bform(errp, errp))}",
               t="the B-error of u₁ is the smallest on V₁", anchor="start", fill="muted",
               size=9.5)

    # --- right top: the Galerkin solutions on nested meshes
    shown = [4, 8, 16]
    graph = Frame(360, 70, 240, 92, 0.0, 1.0, 0.0, 1.12)
    scene.panel_title(338, 28, "Galerkin on nested meshes")
    scene.math(338, 46, r"-((1+x)u')'=f,\quad u=\sin\pi x", t="−((1+x)u′)′ = f, u = sin πx",
               anchor="start", fill="muted")
    graph.axes(scene, x_label="x")
    scene.path(graph.sample(exact, 0.0, 1.0, 200), stroke="accent", sw=SW_CURVE)
    frames, nodes = [], []
    for n in shown:
        vals = solutions[n]
        pts = []
        for k in range(65):
            x = k / 64
            e = min(int(x * n), n - 1)
            s = x * n - e
            pts.append((x, vals[e] * (1 - s) + vals[e + 1] * s))
        frames.append(poly_path(graph.project(pts)))
        nodes.append(n)
    scene.path(frames[0], stroke="accent2", sw=SW_CURVE2, anim=[discrete("d", frames)])
    for index, n in enumerate(shown):
        scene.math(graph.right, graph.y0 + 4, rf"N={n}", t=f"N = {n}", anchor="end",
                   fill="accent2", halo=True, op=1 if index == 0 else 0,
                   anim=[slot(index, len(shown))])
    scene.math(graph.X(0.5) + 8, graph.Y(1.0) - 6, "u", anchor="start", fill="accent",
               halo=True)
    for tick in (0.0, 1.0):
        scene.tick_label(graph.X(tick), graph.bottom + 14, num(tick), size=9.5)

    # --- right bottom: the errors on logarithmic axes
    lo_e = math.log10(min(e for _, e, _ in table)) - 0.25
    hi_e = math.log10(2.0 * max(e for _, _, e in table)) + 0.1
    err = Frame(360, 206, 240, 104, -6.3, -0.7, lo_e, hi_e)
    scene.line(err.x0, err.bottom, err.right, err.bottom, stroke="muted", sw=SW_AXIS)
    scene.line(err.x0, err.y0, err.x0, err.bottom, stroke="muted", sw=SW_AXIS)
    for n in meshes:
        lx = err.X(-math.log2(n))
        scene.line(lx, err.bottom, lx, err.bottom + 4, stroke="muted", sw=SW_AXIS)
        scene.tick_label(lx, err.bottom + 16, rf"\tfrac1{{{n}}}", t=f"1/{n}", size=9.5)
    scene.math(err.right + 8, err.bottom + 16, "h", anchor="start", fill="muted")
    for power in range(math.ceil(lo_e), math.floor(hi_e) + 1):
        scene.line(err.x0 - 4, err.Y(power), err.x0, err.Y(power), stroke="muted",
                   sw=SW_AXIS)
        scene.tick_label(err.x0 - 7, err.Y(power) + 3, rf"10^{{{power}}}", anchor="end",
                         size=9.5)
    scene.path(err.curve([(-math.log2(n), math.log10(2.0 * e_int))
                          for n, _, e_int in table]), stroke="muted", sw=SW_CURVE2,
               dash=DASH)
    for n, e_gal, e_int in table:
        scene.circle(err.X(-math.log2(n)), err.Y(math.log10(e_int)), 4.4, stroke="ink",
                     fill="surface", sw=1.2)
        scene.circle(err.X(-math.log2(n)), err.Y(math.log10(e_gal)), 2.6, fill="accent2")
    rings = [(q2(err.X(-math.log2(n))), q2(err.Y(math.log10(e))))
             for n, e, _ in table if n in shown]
    scene.circle(float(rings[0][0]), float(rings[0][1]), 6.0, stroke="accent2", fill="",
                 sw=SW_AXIS, anim=[discrete("cx", [r[0] for r in rings]),
                                   discrete("cy", [r[1] for r in rings])])
    scene.circle(err.x0 + 10, err.y0 + 2, 2.6, fill="accent2")
    scene.math(err.x0 + 18, err.y0 + 5.5, r"\|u'-u_h'\|", t="Galerkin error",
               anchor="start", fill="accent2", size=9.5)
    scene.circle(err.x0 + 10, err.y0 + 17, 4.4, stroke="ink", fill="surface", sw=1.2)
    scene.math(err.x0 + 18, err.y0 + 20.5, r"\|u'-(I_hu)'\|", t="interpolation error",
               anchor="start", fill="ink", size=9.5)
    scene.line(err.x0 + 102, err.y0 + 2, err.x0 + 118, err.y0 + 2, stroke="muted",
               sw=SW_CURVE2, dash=DASH)
    scene.math(err.x0 + 122, err.y0 + 5.5, r"\text{Cea: }2\,\|u'-(I_hu)'\|",
               t="Cea bound", anchor="start", fill="muted", size=9.5)
    scene.math(338, 346, rf"\text{{observed order }}{q3(slope)}", t=f"observed order {q3(slope)}",
               anchor="start", fill="muted", size=9.5)
    return scene


def fig_ell_dirichlet_eigenfunctions() -> Scene:
    """Nodal patterns of the first Dirichlet eigenfunctions of the square."""
    pi = math.pi

    def mode(j: int, k: int):
        return lambda x, y: math.sin(j * pi * x) * math.sin(k * pi * y)

    def rayleigh(j: int, k: int, n: int = 120) -> float:
        num_, den = 0.0, 0.0
        for a in range(n):
            x = (a + 0.5) / n
            for b in range(n):
                y = (b + 0.5) / n
                gx = j * pi * math.cos(j * pi * x) * math.sin(k * pi * y)
                gy = k * pi * math.sin(j * pi * x) * math.cos(k * pi * y)
                num_ += gx * gx + gy * gy
                den += math.sin(j * pi * x) ** 2 * math.sin(k * pi * y) ** 2
        return num_ / den

    mixed = lambda x, y: mode(1, 2)(x, y) + mode(2, 1)(x, y)
    panels = [
        ("(1,1)", mode(1, 1), 2, [(0, 0, 1, 1)]),
        ("(2,1)", mode(2, 1), 5, [(0, 0, 0.5, 1)]),
        ("(1,2)", mode(1, 2), 5, [(0, 0, 1, 0.5)]),
        ("(1,2)+(2,1)", mixed, 5, None),
        ("(2,2)", mode(2, 2), 8, [(0, 0, 0.5, 0.5), (0.5, 0.5, 1, 1)]),
        ("(3,1)", mode(3, 1), 10, [(0, 0, 1 / 3, 1), (2 / 3, 0, 1, 1)]),
    ]
    for j, k, total in ((1, 1, 2), (2, 1, 5), (1, 2, 5), (2, 2, 8), (3, 1, 10)):
        if abs(rayleigh(j, k) / (pi * pi) - total) > 1e-6:
            raise SystemExit("dirichlet-eigenfunctions: a Rayleigh quotient is off")
    for _, f, _, rects in panels:
        for a in range(1, 40):
            for b in range(1, 40):
                x, y = a / 40 + 0.003, b / 40 + 0.007
                if rects is None:
                    positive = x + y < 1.0
                else:
                    positive = any(x0 < x < x1 and y0 < y < y1 for x0, y0, x1, y1 in rects)
                if (f(x, y) > 0) != positive:
                    raise SystemExit("dirichlet-eigenfunctions: a sign region is wrong")

    scene = Scene(
        "dirichlet-eigenfunctions",
        "The first Dirichlet eigenfunctions of the unit square",
        r"Eigenfunctions \(\sin(j\pi x)\sin(k\pi y)\) of \(-\Delta\) on \((0,1)^2\) with zero "
        r"boundary values, ordered by the eigenvalue \(\lambda=\pi^2(j^2+k^2)\); each "
        r"eigenvalue is recomputed here as a Rayleigh quotient by quadrature. Shading marks "
        r"where the function is positive, solid curves are the nodal lines, and the thin "
        r"curves are the levels \(\pm\tfrac12\) of the sup norm. Only the first eigenfunction "
        r"keeps one sign, and its eigenvalue \(2\pi^2\) is simple. The eigenvalue \(5\pi^2\) is "
        r"double: the fourth panel is a sum of the two products, a different eigenfunction "
        r"whose nodal line is a diagonal. The last panel shares \(10\pi^2\) with \((1,3)\), "
        r"which is not drawn. Every eigenfunction of a later eigenvalue changes sign, because "
        r"it is \(L^2\)-orthogonal to the positive first one.",
        "Six unit squares in a row, each divided by nodal lines into shaded and unshaded "
        "rectangles or triangles, with the eigenvalue written under each square: one "
        "square without a nodal line, then halves, a diagonal split, quarters, and thirds.",
        width=640.0, height=200.0)

    side, gap, left, top = 88.0, 15.5, 22.0, 46.0
    scene.panel_title(22, 26, "sign patterns, in the order of the eigenvalues")
    for index, (name, f, total, rects) in enumerate(panels):
        x0 = left + index * (side + gap)
        frame = Frame(x0, top, side, side, 0.0, 1.0, 0.0, 1.0)
        if rects is None:
            scene.area(poly_path([(frame.X(0), frame.Y(0)), (frame.X(1), frame.Y(0)),
                                  (frame.X(0), frame.Y(1))]) + "Z", fill="band")
        else:
            for xa, ya, xb, yb in rects:
                scene.rect(frame.X(xa), frame.Y(yb), frame.X(xb) - frame.X(xa),
                           frame.Y(ya) - frame.Y(yb), fill="band")
        peak = 1.0
        if rects is None:
            peak = max(mixed(a / 200, b / 200) for a in range(201) for b in range(201))
        for level in (0.5, -0.5):
            scene.path(ell_level_path(frame, f, (0.0, 1.0, 0.0, 1.0), level * peak,
                                      lambda x, y: True, 80),
                       stroke="accent" if level > 0 else "accent2", sw=SW_AXIS)
        if total > 2:
            nodal = ell_level_path(frame, f, (0.0, 1.0, 0.0, 1.0), 0.0,
                                   lambda x, y: 0.004 < x < 0.996 and 0.004 < y < 0.996, 80)
            scene.path(nodal, stroke="ink", sw=SW_CURVE2)
        scene.rect(frame.x0, frame.y0, side, side, stroke="ink", fill="", sw=SW_CURVE2)
        scene.math(frame.x0 + side / 2, frame.bottom + 18, rf"\lambda={total}\pi^2",
                   t=f"λ = {total}π²", fill="ink" if total != 2 else "accent", size=10.5)
        scene.math(frame.x0 + side / 2, frame.bottom + 34, name, fill="muted", size=9.5)
    scene.math(22, 190, r"\text{only the first keeps one sign; the eigenspace of }5\pi^2"
               r"\text{ is two-dimensional}",
               t="only the first keeps one sign; the eigenspace of 5π² is two-dimensional",
               anchor="start", fill="muted", size=9.5)
    return scene


def _rod_bump(x: float) -> float:
    """Initial temperature for the positivity figure: a bump on [1.95, 2.65]."""
    return bump((x - 2.3) / 0.35)


def _rod_images(x: float, t: float) -> float:
    """Dirichlet heat solution on (0, pi) by the method of images.

    Every image term is a Gaussian of the full line, so a value of size
    1e-20 far from the support is a sum of positive terms and a much smaller
    reflected correction; no cancellation hides it.
    """
    def integrand(y: float) -> float:
        total = 0.0
        for m in range(-2, 3):
            shift = 2.0 * math.pi * m
            total += heat_kernel(x - y - shift, t) - heat_kernel(x + y - shift, t)
        return total * _rod_bump(y)
    return integrate_mid(integrand, 1.95, 2.65, 400)


def _rod_sine(x: float, t: float, coefficients) -> float:
    return sum(b * math.exp(-k * k * t) * math.sin(k * x)
               for k, b in enumerate(coefficients, start=1))


def fig_heat_positivity() -> Scene:
    """A bump on a rod with cold ends is positive everywhere at once."""
    coefficients = [2.0 / math.pi * integrate_mid(
        lambda y, k=k: _rod_bump(y) * math.sin(k * y), 1.95, 2.65, 800)
        for k in range(1, 121)]
    for x in (0.4, 1.2, 2.3, 2.9):
        series, images = _rod_sine(x, 0.1, coefficients), _rod_images(x, 0.1)
        if abs(series - images) > 1e-7:
            raise SystemExit("heat-positivity: images and sine series disagree")
    probe = 0.6
    times = (0.012, 0.03, 0.08, 0.2, 0.45)
    static = 1
    xs = [math.pi * k / 180 for k in range(181)]
    profiles = [[(x, _rod_images(x, t)) for x in xs] for t in times]
    for t, profile in zip(times, profiles):
        if min(value for x, value in profile[1:-1]) <= 0.0:
            raise SystemExit("heat-positivity: a sampled interior value is not positive")
    log_min = -24.0
    ts = [0.006 + (0.6 - 0.006) * (k / 160) ** 2 for k in range(161)]
    logs = [(t, math.log10(_rod_images(probe, t))) for t in ts]
    if any(b[1] <= a[1] for a, b in zip(logs, logs[1:]) if b[0] < 0.1):
        raise SystemExit("heat-positivity: the probe value should rise at early times")
    shown = [(t, v) for t, v in logs if v >= log_min]

    scene = Scene(
        "heat-positivity",
        "Heat reaches every point at once",
        r"The rod \(0<x<\pi\) has ends held at zero. The initial temperature \(g\) (dashed) "
        r"is a smooth bump supported in \([1.95,2.65]\). Left: the solution at five "
        r"times, computed by the method of images and checked against the sine series. "
        r"Right: the value at \(x=0.6\), which lies outside the support of \(g\), on a "
        r"logarithmic scale. It is positive at every positive time, of size about "
        r"\(e^{-d^2/4t}\), where \(d=1.35\) is the distance to the support. By the "
        r"strong principle a nonnegative solution that vanished at an interior point "
        r"at a time \(t>0\) would vanish identically before \(t\).",
        "Left, a rod profile: a narrow dashed bump near x = 2.3 and the solution at "
        "five times, spreading and flattening while it stays zero at both ends. A "
        "dotted vertical line marks x = 0.6. Right, the base-ten logarithm of the "
        "solution at x = 0.6 against time: it rises from below ten to the minus "
        "twenty at very small times towards ten to the minus one. The static frame "
        "shows time 0.03.",
        width=640, height=300)
    left = Frame(52, 70, 250, 160, 0, math.pi, -0.04, 1.08)
    right = Frame(390, 70, 214, 160, 0, 0.6, log_min, 0)
    scene.panel_title(24, 40, "the temperature on the rod")
    scene.panel_title(360, 40, "the temperature at x = 0.6")
    left.axes(scene, x_label="x", origin_y=0)
    right.axes(scene, x_label="t", origin_y=log_min)
    for x, name in ((0, "0"), (probe, "0.6"), (2.3, "2.3"), (math.pi, r"\pi")):
        scene.tick_label(left.X(x), left.bottom + 17, name, size=10)
    scene.tick_label(left.x0 - 8, left.Y(1) + 4, "1", anchor="end", size=10)
    for t in (0, 0.3, 0.6):
        scene.tick_label(right.X(t), right.bottom + 17, q2(t) if t else "0", size=10)
    for power in (-20, -10, 0):
        scene.tick_label(right.x0 - 7, right.Y(power) + 4, rf"10^{{{power}}}",
                         anchor="end", size=10)
    scene.line(left.X(probe), left.y0, left.X(probe), left.Y(0),
               stroke="muted", sw=SW_AXIS, dash=DOT)
    scene.path(left.sample(_rod_bump, 1.95, 2.65, 80), stroke="muted",
               sw=SW_CURVE2, dash=DASH)
    scene.math(left.X(2.3) + 22, left.Y(0.95), "g", anchor="start", fill="muted",
               size=11)
    fills = left.fill_frames(profiles, 0)
    curves = left.curve_frames(profiles)
    for curve in curves:
        scene.path(curve, stroke="muted", sw=SW_AXIS, sop=0.5)
    scene.area(fills[static], fill="band", anim=[discrete("d", fills)])
    scene.path(curves[static], stroke="accent", anim=[discrete("d", curves)])
    for index, t in enumerate(times):
        scene.math(left.right - 4, left.y0 + 4, rf"t={q3(t)}", anchor="end",
                   fill="accent", size=11, halo=True,
                   op=1 if index == static else 0,
                   anim=[slot(index, len(times))])
    scene.path(right.curve(shown), stroke="accent")
    scene.circle(right.X(times[static]),
                 right.Y(math.log10(_rod_images(probe, times[static]))), 3.5,
                 fill="accent",
                 anim=[discrete("cx", [q2(right.X(t)) for t in times]),
                       discrete("cy", [q2(right.Y(math.log10(_rod_images(probe, t))))
                                       for t in times])])
    scene.math(right.X(0.3), right.Y(-4.5), r"u(0.6,t)>0", anchor="start",
               size=11, halo=True)
    scene.text(24, 272, "zero at both ends, positive in between at every t > 0",
               anchor="start", fill="muted", size=11)
    scene.text(360, 272, "logarithmic axis, cut off below at 1e-24",
               anchor="start", fill="muted", size=11)
    return scene


def fig_heat_log_convexity() -> Scene:
    """The energy of a three-mode solution: log-convex, and its frequency falls."""
    modes = ((1, 1.0), (3, 0.7), (7, 0.5))

    def energy(t: float) -> float:
        return math.pi / 2 * sum(c * c * math.exp(-2 * k * k * t) for k, c in modes)

    def dirichlet(t: float) -> float:
        return math.pi / 2 * sum(k * k * c * c * math.exp(-2 * k * k * t)
                                 for k, c in modes)

    def solution(x: float, t: float) -> float:
        return sum(c * math.exp(-k * k * t) * math.sin(k * x) for k, c in modes)

    end = 0.5
    ts = [end * k / 200 for k in range(201)]
    for t in (0.0, 0.05, 0.2):
        numeric = integrate_mid(lambda x: solution(x, t) ** 2, 0, math.pi, 2000)
        if abs(numeric - energy(t)) > 1e-8:
            raise SystemExit("heat-log-convexity: the energy formula is wrong")
    for t in ts:
        first = -2 * dirichlet(t)
        second = 4 * math.pi / 2 * sum(k ** 4 * c * c * math.exp(-2 * k * k * t)
                                       for k, c in modes)
        if first * first > energy(t) * second * (1 + 1e-12):
            raise SystemExit("heat-log-convexity: (E')^2 <= E E'' fails")
    quotients = [dirichlet(t) / energy(t) for t in ts]
    if any(b > a for a, b in zip(quotients, quotients[1:])):
        raise SystemExit("heat-log-convexity: the frequency must not increase")

    scene = Scene(
        "heat-log-convexity",
        "The energy of heat flow is log-convex",
        r"The solution \(u=e^{-t}\sin x+0.7e^{-9t}\sin 3x+0.5e^{-49t}\sin 7x\) on "
        r"\((0,\pi)\) with zero boundary values. Left: \(\log E(t)\) for "
        r"\(E(t)=\int_0^\pi u^2\,dx\), below its chord (dashed). The curve lies under "
        r"the chord because \((E')^2\le EE''\). Right: the frequency "
        r"\(\int_0^\pi u_x^2\,dx\big/\int_0^\pi u^2\,dx=-E'/2E\) decreases from a weighted "
        r"average of \(1,9,49\) toward the lowest eigenvalue \(1\). Log-convexity gives "
        r"\(E(t)\le E(0)^{1-t/b}E(b)^{t/b}\) for \(0\le t\le b\), so \(E(b)=0\) forces "
        r"\(E=0\) on \([0,b]\). That is backward uniqueness.",
        "Two panels over time from 0 to 0.5. Left, the logarithm of the energy "
        "falls steeply at first and then along a line of slope minus two, and it "
        "stays below the dashed chord joining its endpoints. Right, the ratio of "
        "gradient energy to energy falls from about 10 towards the horizontal "
        "dashed line at 1.",
        width=640, height=290)
    logs = [(t, math.log(energy(t))) for t in ts]
    left = Frame(60, 64, 230, 160, 0, end, logs[-1][1] - 0.2, logs[0][1] + 0.2)
    right = Frame(380, 64, 230, 160, 0, end, 0, 12.5)
    scene.panel_title(24, 36, "log of the energy")
    scene.panel_title(344, 36, "frequency of the solution")
    left.axes(scene, x_label="t", origin_y=left.ymin)
    right.axes(scene, x_label="t", origin_y=0)
    for frame in (left, right):
        for t in (0, 0.25, end):
            scene.tick_label(frame.X(t), frame.bottom + 17, q2(t) if t else "0",
                             size=10)
    for value in (-0.5, 0, 0.5, 1):
        scene.tick_label(left.x0 - 7, left.Y(value) + 4, q2(value), anchor="end",
                         size=10)
    for value in (1, 5, 10):
        scene.tick_label(right.x0 - 7, right.Y(value) + 4, str(value), anchor="end",
                         size=10)
    scene.line(left.X(0), left.Y(logs[0][1]), left.X(end), left.Y(logs[-1][1]),
               stroke="accent2", dash=DASH)
    scene.path(left.curve(logs), stroke="accent")
    chord = logs[0][1] + (logs[-1][1] - logs[0][1]) * 0.3 / end
    scene.text(left.X(0.3), left.Y(chord) - 8, "chord", anchor="start",
               fill="accent2", size=11, halo=True)
    scene.math(left.X(0.06) + 4, left.Y(math.log(energy(0.06))) + 16,
               r"\log E(t)", t="log E(t)", anchor="start", fill="accent",
               size=11, halo=True)
    scene.line(right.x0, right.Y(1), right.right, right.Y(1), stroke="muted",
               sw=SW_AXIS, dash=DASH)
    scene.path(right.curve(list(zip(ts, quotients))), stroke="accent")
    scene.math(right.right - 2, right.Y(1) - 7, r"\lambda_1=1", anchor="end",
               fill="muted", size=11, halo=True)
    scene.math(right.X(0.04) + 8, right.Y(quotients[16]) - 6,
               r"-E'/2E", anchor="start", fill="accent", size=11, halo=True)
    scene.math(24, 266, r"(E')^2\le E\,E''", t="(E')^2 <= E E''", anchor="start",
               size=12)
    scene.math(344, 266, r"E(t)\le E(0)^{1-t/b}E(b)^{t/b}",
               t="E(t) <= E(0)^(1-t/b) E(b)^(t/b)", anchor="start", size=12)
    return scene


def _step_coefficient(k: int) -> float:
    """Sine coefficient of the indicator of (pi/4, 3pi/4) on (0, pi)."""
    return 2.0 / (math.pi * k) * (math.cos(k * math.pi / 4) - math.cos(3 * k * math.pi / 4))


def fig_galerkin_sine_convergence() -> Scene:
    """Galerkin solutions of the Dirichlet heat equation in the first N sine modes."""
    later = 0.02
    counts = (1, 3, 5, 9, 17, 33)
    static = 3
    top = 20000
    coefficients = [_step_coefficient(k) for k in range(1, top + 1)]
    mass = math.pi / 2  # the squared L2 norm of the indicator of (pi/4, 3pi/4)
    if abs(math.pi / 2 * sum(b * b for b in coefficients) - mass) > 2e-4:
        raise SystemExit("galerkin-sine-convergence: Parseval check failed")

    def error(count: int, t: float) -> float:
        if t == 0:
            kept = math.pi / 2 * sum(b * b for b in coefficients[:count])
            return math.sqrt(max(mass - kept, 0.0))
        tail = sum(b * b * math.exp(-2 * k * k * t)
                   for k, b in enumerate(coefficients[count:], start=count + 1)
                   if k * k * t < 400)
        return math.sqrt(math.pi / 2 * tail)

    def galerkin(x: float, t: float, count: int) -> float:
        return sum(b * math.exp(-k * k * t) * math.sin(k * x)
                   for k, b in enumerate(coefficients[:count], start=1))

    ns = list(range(1, 41))
    early = [error(n, 0) for n in ns]
    late = [error(n, later) for n in ns]
    if any(b > a + 1e-12 for a, b in zip(early, early[1:])):
        raise SystemExit("galerkin-sine-convergence: errors must not increase")
    if not late[-1] < 1e-6 < early[-1]:
        raise SystemExit("galerkin-sine-convergence: smoothing is not visible")

    scene = Scene(
        "galerkin-sine-convergence",
        "Galerkin approximations in sine modes",
        r"On \((0,\pi)\) the sines are orthogonal both in \(L^2\) and in "
        r"\(H^1_0\), so each Gram threshold space is spanned by the first \(N\) of them. "
        r"The Galerkin solution for \(u_t=u_{xx}\) with initial value the step "
        r"\(g=\mathbf 1_{(\pi/4,3\pi/4)}\) is then the truncated series "
        r"\(u_N=\sum_{k\le N}\hat g_k e^{-k^2t}\sin kx\). Left: \(u_N\) at \(t=0\) (thin) "
        r"and at \(t=0.02\) (thick) for \(N=1,3,5,9,17,33\); the step is dashed. "
        r"Right: the \(L^2\) error \(\|u(t)-u_N(t)\|_2\) against \(N\) on a logarithmic "
        r"scale. At \(t=0\) it decays only like \(N^{-1/2}\). At \(t=0.02\) the "
        r"factor \(e^{-k^2t}\) makes it fall faster than any power of \(N\). The even "
        r"coefficients of this step vanish, so the errors come in equal pairs.",
        "Left, a dashed step on the interval with two approximating curves: an "
        "oscillating truncated sine series at time zero and a smooth curve at time "
        "0.02, both changing as the number of modes increases; the static frame "
        "shows nine modes. Right, two sequences of dots against the number of "
        "modes on a logarithmic error axis: the time-zero errors decrease slowly, "
        "the time-0.02 errors drop steeply below ten to the minus six.",
        width=640, height=300)
    left = Frame(52, 70, 250, 160, 0, math.pi, -0.25, 1.25)
    right = Frame(390, 70, 214, 160, 0, 41, -8, 0)
    scene.panel_title(24, 40, "the first N sine modes")
    scene.panel_title(360, 40, "the L2 error")
    left.axes(scene, x_label="x", origin_y=0)
    right.axes(scene, x_label="N", origin_y=-8)
    for x, name in ((0, "0"), (math.pi / 2, r"\pi/2"), (math.pi, r"\pi")):
        scene.tick_label(left.X(x), left.bottom + 17, name, size=10)
    scene.tick_label(left.x0 - 7, left.Y(1) + 4, "1", anchor="end", size=10)
    for n in (1, 10, 20, 30, 40):
        scene.tick_label(right.X(n), right.bottom + 17, str(n), size=10)
    for power in (-8, -4, 0):
        scene.tick_label(right.x0 - 7, right.Y(power) + 4, rf"10^{{{power}}}",
                         anchor="end", size=10)
    a, b = math.pi / 4, 3 * math.pi / 4
    scene.path(left.curve([(0, 0), (a, 0), (a, 1), (b, 1), (b, 0), (math.pi, 0)]),
               stroke="muted", sw=SW_CURVE2, dash=DASH)
    xs = [math.pi * k / 360 for k in range(361)]
    rough = left.curve_frames([[(x, galerkin(x, 0, n)) for x in xs] for n in counts])
    smooth = left.curve_frames([[(x, galerkin(x, later, n)) for x in xs]
                                for n in counts])
    scene.path(rough[static], stroke="accent2", sw=SW_AXIS + 0.25,
               anim=[discrete("d", rough)])
    scene.path(smooth[static], stroke="accent", anim=[discrete("d", smooth)])
    for index, n in enumerate(counts):
        scene.math(left.right - 4, left.y0 + 4, rf"N={n}", anchor="end", size=11,
                   halo=True, op=1 if index == static else 0,
                   anim=[slot(index, len(counts))])
    for values, role in ((early, "accent2"), (late, "accent")):
        for n, value in zip(ns, values):
            if value > 0 and math.log10(value) >= -8:
                scene.circle(right.X(n), right.Y(math.log10(value)), 2.2, fill=role)
    scene.circle(right.X(counts[static]), right.Y(math.log10(early[counts[static] - 1])),
                 5, stroke="ink", fill="", sw=SW_AXIS,
                 anim=[discrete("cx", [q2(right.X(n)) for n in counts]),
                       discrete("cy", [q2(right.Y(math.log10(early[n - 1])))
                                       for n in counts])])
    scene.math(right.X(22), right.Y(math.log10(early[21])) - 10, r"t=0",
               anchor="start", fill="accent2", size=11, halo=True)
    scene.math(right.X(8) + 6, right.Y(-5), r"t=0.02", anchor="start",
               fill="accent", size=11, halo=True)
    scene.math(24, 272, r"u_N=\sum_{k\le N}\hat g_k\,e^{-k^2t}\sin kx",
               t="u_N = sum over k <= N of g_k exp(-k^2 t) sin(kx)", anchor="start",
               size=12)
    scene.math(360, 272, r"\|u(t)-u_N(t)\|_2^2=\tfrac{\pi}{2}\sum_{k>N}\hat g_k^2e^{-2k^2t}",
               t="squared error = (pi/2) sum over k > N of g_k^2 exp(-2k^2 t)",
               anchor="start", size=12)
    return scene


# --- the classical wave: Huygens in three dimensions, the tail in two ---------

HUYGENS_RADIUS = 0.5


def huygens_velocity(r: float) -> float:
    """Radial initial velocity: the standard bump on the ball of radius 1/2."""
    return bump(r / HUYGENS_RADIUS)


def kirchhoff_radial(r: float, t: float) -> float:
    """Kirchhoff's formula for zero displacement and radial velocity ``h``.

    ``t`` times the mean of ``h`` over the sphere of radius ``t`` about a point
    at distance ``r`` from the origin is ``(1/2r)`` times the integral of
    ``rho h(rho)`` over ``|r - t| < rho < r + t``.
    """
    lo, hi = abs(r - t), min(r + t, HUYGENS_RADIUS)
    if lo >= hi:
        return 0.0
    return integrate_mid(lambda rho: rho * huygens_velocity(rho), lo, hi, 200) / (2.0 * r)


def poisson_radial(r: float, t: float, n: int = 160) -> float:
    """Poisson's formula for zero displacement and the same radial velocity.

    The disc integral of ``h(y) / sqrt(t^2 - |x - y|^2)`` over ``2 pi`` is
    written in polar coordinates about ``x`` and the radius substituted as
    ``s = t sin(phi)``, which removes the singularity at the rim. Only the
    radii and angles that meet the support of ``h`` are integrated.
    """
    a = HUYGENS_RADIUS

    def ring(s: float) -> float:
        if r < 1e-9 or s < 1e-12:
            return 2.0 * math.pi * huygens_velocity(max(r, s))
        c = (r * r + s * s - a * a) / (2.0 * r * s)
        if c >= 1.0:
            return 0.0
        top = math.pi if c <= -1.0 else math.acos(c)
        return 2.0 * integrate_mid(
            lambda th: huygens_velocity(math.sqrt(max(r * r + s * s - 2.0 * r * s * math.cos(th), 0.0))),
            0.0, top, 80)

    s_lo, s_hi = max(0.0, r - a), min(t, r + a)
    if s_lo >= s_hi:
        return 0.0
    p_lo, p_hi = math.asin(s_lo / t), math.asin(min(s_hi / t, 1.0))
    return integrate_mid(lambda ph: t * math.sin(ph) * ring(t * math.sin(ph)),
                         p_lo, p_hi, n) / (2.0 * math.pi)


def fig_wave_huygens() -> Scene:
    """The same radial velocity pulse in three and in two space dimensions."""
    a = HUYGENS_RADIUS
    snapshot = 3.0
    observer = 3.0
    mass = 2.0 * math.pi * integrate_mid(lambda rho: rho * huygens_velocity(rho), 0.0, a, 400)

    radii = [4.2 * k / 210.0 for k in range(1, 211)]
    profile3 = [(r, kirchhoff_radial(r, snapshot)) for r in radii]
    profile2 = [(r, poisson_radial(r, snapshot)) for r in radii]
    times = [0.05 + 8.95 * k / 180.0 for k in range(181)]
    signal3 = [(t, kirchhoff_radial(observer, t)) for t in times]
    signal2 = [(t, poisson_radial(observer, t)) for t in times]

    # Huygens: behind the shell the three-dimensional wave is exactly zero,
    # while the planar one is not, and its tail follows the far-field rate.
    if any(value != 0.0 for t, value in signal3 if t >= observer + a):
        raise SystemExit("wave-huygens: the Kirchhoff pulse did not end at r + a")
    for t in (6.0, 9.0):
        far = mass / (2.0 * math.pi * math.sqrt(t * t - observer * observer))
        if abs(poisson_radial(observer, t) / far - 1.0) > 0.02:
            raise SystemExit("wave-huygens: the planar tail is not the far-field rate")

    top = 1.12 * max(value for _, value in profile2 + signal2)
    scene = Scene(
        "wave-huygens",
        "A pulse in three dimensions and in two",
        r"Both waves have zero initial displacement \(g=0\) and the same radial velocity profile \(h\), a smooth bump "
        r"supported in the ball \(|x|\le 1/2\). The accent curves use Kirchhoff's formula in "
        r"\(\mathbb R^3\), where \(u=t\) times the mean of \(h\) over the sphere of radius \(t\); "
        r"the second curves use Poisson's disc formula in \(\mathbb R^2\), with this radial "
        r"profile in two dimensions. Left: the radial profile at \(t=3\). The "
        r"three-dimensional wave lives on the shell \(2.5\le|x|\le3.5\); the planar wave fills "
        r"the whole disc behind its front. Right: the signal at a point at distance \(3\). In "
        r"three dimensions it is exactly zero once \(t>3.5\). The planar signal stays "
        r"positive after arrival and has leading decay \(M/(2\pi t)\) as \(t\to\infty\), "
        r"where \(M=\int h\). The dashed \(M/(2\pi\sqrt{t^2-9})\) curve is a "
        r"point-source comparison, not the exact bump solution.",
        "Two panels. Left, two radial profiles at time three: a narrow bump "
        "on a thin shell for three dimensions, and a broad profile that is "
        "positive everywhere inside the front for two dimensions. Right, the "
        "signal at distance three against time: a brief pulse that ends "
        "sharply in three dimensions, and in two dimensions a rise followed "
        "by a slowly decaying tail that follows a dashed far-field curve.",
        width=640.0, height=292.0)

    left = Frame(60, 62, 236, 164, 0.0, 4.2, 0.0, top)
    scene.panel_title(24, 42, "the profile at t = 3")
    left.axes(scene, x_label=r"|x|", origin_y=0.0)
    scene.rect(left.X(snapshot - a), left.y0, left.X(snapshot + a) - left.X(snapshot - a),
               left.h, fill="band")
    scene.path(left.curve(profile2), stroke="accent2", sw=SW_CURVE2)
    scene.path(left.curve(profile3), stroke="accent", sw=SW_CURVE)
    for tick in (0.0, 1.0, 2.0, 3.0, 4.0):
        scene.line(left.X(tick), left.bottom, left.X(tick), left.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(left.X(tick), left.bottom + 16, num(tick), size=9.5)
    for value in (0.02, 0.04):
        scene.line(left.x0 - 3, left.Y(value), left.x0, left.Y(value), stroke="muted", sw=SW_AXIS)
        scene.tick_label(left.x0 - 6, left.Y(value) + 3.5, q2(value), anchor="end", size=9)
    scene.math(left.x0 + 6, left.y0 + 10, r"u(x,3)", anchor="start", fill="muted", size=10)
    scene.text(left.X(1.2), left.Y(0.0265), "two dimensions", fill="accent2", size=9.5, halo=True)
    scene.text(left.X(2.25), left.Y(0.0125), "three dimensions", anchor="end", fill="accent",
               size=9.5, halo=True)
    scene.text(left.X(3.0), left.y0 - 6, "the shell", fill="muted", size=9)

    right = Frame(380, 62, 226, 164, 0.0, 9.0, 0.0, top)
    scene.panel_title(344, 42, "the signal at distance 3")
    right.axes(scene, x_label="t", origin_y=0.0)
    scene.rect(right.X(observer - a), right.y0, right.X(observer + a) - right.X(observer - a),
               right.h, fill="band")
    far = [(t, mass / (2.0 * math.pi * math.sqrt(t * t - observer * observer)))
           for t in (4.2 + 4.8 * k / 60.0 for k in range(61))]
    scene.path(right.curve(far), stroke="muted", sw=SW_AXIS, dash=DASH)
    scene.path(right.curve(signal2), stroke="accent2", sw=SW_CURVE2)
    scene.path(right.curve(signal3), stroke="accent", sw=SW_CURVE)
    for tick in (0.0, 3.0, 6.0, 9.0):
        scene.line(right.X(tick), right.bottom, right.X(tick), right.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(right.X(tick), right.bottom + 16, num(tick), size=9.5)
    scene.math(right.x0 + 6, right.y0 + 10, r"u(x,t),\ |x|=3", t="u(x,t), |x| = 3",
               anchor="start", fill="muted", size=10)
    scene.text(right.X(6.4), right.Y(0.0175), "the tail", fill="accent2", size=9.5, halo=True)
    scene.math(right.X(observer + a) + 4, right.Y(0.0028) - 4, r"u=0\text{ for }t>3.5",
               t="u = 0 for t > 3.5", anchor="start", fill="accent", size=9.5, halo=True)
    scene.text(24, 270, "The same data: in three dimensions the wave passes and leaves nothing "
               "behind; in two it leaves a tail.", anchor="start", fill="muted", size=9.5)
    return scene


# --- the classical wave: energy in the backward cone -------------------------

def fig_cone_energy() -> Scene:
    """Energy leaves the shrinking cone and never enters it."""
    centre, width = -0.2, 0.5
    apex = (1.0, 2.2)

    def slope(x: float) -> float:
        s = (x - centre) / width
        if abs(s) >= 1.0:
            return 0.0
        return bump(s) * (-2.0 * s / (1.0 - s * s) ** 2) / width

    def density(x: float, t: float) -> float:
        """``(u_t^2 + u_x^2)/2`` for ``u = (g(x+t) + g(x-t))/2``."""
        return 0.25 * (slope(x + t) ** 2 + slope(x - t) ** 2)

    def cone_energy(t: float) -> float:
        half = apex[1] - t
        return integrate_mid(lambda x: density(x, t), apex[0] - half, apex[0] + half, 800)

    total = integrate_mid(lambda x: density(x, 0.0), centre - width, centre + width, 800)
    times = [apex[1] * k / 110.0 for k in range(111)]
    energies = [cone_energy(t) for t in times]
    if abs(energies[0] - total) > 1e-6 * total:
        raise SystemExit("cone-energy: the base of the cone misses part of the data")
    if any(later > earlier + 1e-9 * total for earlier, later in zip(energies, energies[1:])):
        raise SystemExit("cone-energy: the cone energy increased")
    # When each half leaves: the left-moving half meets the left edge of the
    # cone, x = -1.2 + t, at relative speed two; the right-moving half meets
    # the right edge, x = 3.2 - t.
    base = (apex[0] - apex[1], apex[0] + apex[1])
    exits = [((centre - base[0]) / 2.0), ((base[1] - centre) / 2.0)]

    scene = Scene(
        "cone-energy",
        "Energy in a backward cone",
        r"The one-dimensional wave with a smooth bump as displacement and zero velocity. Left: "
        r"the energy density \(e=\tfrac12(u_t^2+u_x^2)\) is carried by the two half-waves along "
        r"\(x\pm t=\text{const}\), shaded. The backward cone has apex \((1,2.2)\) and base "
        r"\([-1.2,3.2]\), which contains the support of the data. Right: the energy "
        r"\(E(t)=\int_{|x-1|<2.2-t}e\,dx\), computed by quadrature. It starts at the total "
        r"energy and falls in two stages, as the left half crosses the rising edge near "
        r"\(t=0.5\) and the right half crosses the falling edge near \(t=1.7\); each stage "
        r"has two parts because the density of a half-wave, \(\tfrac14g'^2\), vanishes where "
        r"\(g'\) does. It never "
        r"rises: the edges move at the wave speed, so energy can leave the cone but not enter "
        r"it, and zero data on the base would keep it zero.",
        "Two panels. Left, the space-time plane with two shaded diagonal "
        "strips leaving a bump at time zero, one to each side, and a "
        "triangle whose edges have slopes plus and minus one; each strip is "
        "darker where it lies inside the triangle. Right, the energy inside "
        "the triangle against time, a curve that starts at the total energy, "
        "drops to half near time one half and to zero near time 1.7.",
        width=640.0, height=286.0)

    plane = Frame(56, 62, 290, 164, -1.7, 3.7, 0.0, 2.4)
    scene.panel_title(24, 42, "the density and the cone")
    plane.axes(scene, x_label="x", origin_y=0.0)
    scene.math(plane.x0 + 6, plane.y0 + 10, "t", anchor="start", fill="muted")

    def strip(direction: float, inside: bool) -> str:
        lows, highs = [], []
        for k in range(121):
            t = plane.ymax * k / 120.0
            lo = centre - width + direction * t
            hi = centre + width + direction * t
            lo, hi = max(lo, plane.xmin), min(hi, plane.xmax)
            if inside:
                half = apex[1] - t
                lo, hi = max(lo, apex[0] - half), min(hi, apex[0] + half)
            if lo < hi:
                lows.append((lo, t))
                highs.append((hi, t))
        return plane.band(lows, highs)

    for direction in (-1.0, 1.0):
        scene.area(strip(direction, False), fill="band")
    for direction in (-1.0, 1.0):
        scene.area(strip(direction, True), fill="accent", fop=0.35)
    scene.path(poly_path([(plane.X(base[0]), plane.Y(0.0)), (plane.X(apex[0]), plane.Y(apex[1])),
                          (plane.X(base[1]), plane.Y(0.0))]), stroke="accent", sw=SW_CURVE2)
    for t in exits:
        scene.line(plane.x0, plane.Y(t), plane.right, plane.Y(t), stroke="muted", sw=SW_AXIS,
                   dash=DOT)
    for tick in (-1.0, 0.0, 1.0, 2.0, 3.0):
        scene.line(plane.X(tick), plane.bottom, plane.X(tick), plane.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(plane.X(tick), plane.bottom + 16, num(tick), size=9.5)
    scene.math(plane.X(-0.95), plane.Y(1.35), r"x+t", t="x + t constant", fill="muted",
               size=9.5, halo=True)
    scene.math(plane.X(2.55), plane.Y(1.95), r"x-t", t="x - t constant", fill="muted",
               size=9.5, halo=True)
    scene.circle(plane.X(apex[0]), plane.Y(apex[1]), 3.0, fill="accent")

    graph = Frame(420, 62, 180, 164, 0.0, apex[1], 0.0, 1.15 * total)
    scene.panel_title(392, 42, "the energy in the cone")
    graph.axes(scene, x_label="t", origin_y=0.0)
    scene.line(graph.x0, graph.Y(total), graph.right, graph.Y(total), stroke="muted",
               sw=SW_AXIS, dash=DASH)
    scene.text(graph.right, graph.Y(total) - 5, "total energy", anchor="end", fill="muted",
               size=9)
    for t in exits:
        scene.line(graph.X(t), graph.y0, graph.X(t), graph.bottom, stroke="muted", sw=SW_AXIS,
                   dash=DOT)
    scene.path(graph.curve(list(zip(times, energies))), stroke="accent", sw=SW_CURVE)
    for tick in (0.0, 1.0, 2.0):
        scene.line(graph.X(tick), graph.bottom, graph.X(tick), graph.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(graph.X(tick), graph.bottom + 16, num(tick), size=9.5)
    scene.math(graph.x0 + 6, graph.Y(0.5 * total) - 8, r"E(t)", anchor="start", fill="accent",
               size=10, halo=True)
    scene.text(24, 268, "Dotted: the times the two half-waves cross the edges of the cone.",
               anchor="start", fill="muted", size=9.5)
    return scene


# --- Burgers: which weak solution the viscosity picks ------------------------

def log_erfc(z: float) -> float:
    """``log erfc(z)``, with the asymptotic series where ``erfc`` underflows."""
    if z < 25.0:
        return math.log(math.erfc(z))
    inv = 1.0 / (z * z)
    return -z * z - math.log(z * math.sqrt(math.pi)) + math.log(1.0 - 0.5 * inv + 0.75 * inv * inv)


def viscous_burgers_riemann(left: float, right: float, eps: float, x: float, t: float) -> float:
    """The exact Cole-Hopf solution of ``u_t + u u_x = eps u_xx`` with Riemann data.

    With ``phi`` the heat evolution of ``exp(-(1/2eps) int_0^x u_0)`` and
    ``u = -2 eps phi_x / phi``, the two halves of the datum contribute weights
    ``exp(-(u x - u^2 t/2)/(2 eps)) erfc(-+ (x - u t)/sqrt(4 eps t))``, and ``u`` is
    their weighted average of ``left`` and ``right``. Computed in logarithms.
    """
    scale = math.sqrt(4.0 * eps * t)
    log_left = -(left * x - 0.5 * left * left * t) / (2.0 * eps) + log_erfc((x - left * t) / scale)
    log_right = (-(right * x - 0.5 * right * right * t) / (2.0 * eps)
                 + log_erfc(-(x - right * t) / scale))
    top = max(log_left, log_right)
    w_left, w_right = math.exp(log_left - top), math.exp(log_right - top)
    return (left * w_left + right * w_right) / (w_left + w_right)


def fig_entropy_selection() -> Scene:
    """Vanishing viscosity: the fan for expansive data, the shock for compressive."""
    epsilons = [0.16, 0.04, 0.01]
    xs = [-0.8 + 2.6 * k / 260.0 for k in range(261)]

    def fan(x: float) -> float:
        return min(max(x, 0.0), 1.0)

    def shock(x: float) -> float:
        return 1.0 if x < 0.5 else 0.0

    cases = [(0.0, 1.0, fan), (1.0, 0.0, shock)]
    distances = []
    for left, right, limit in cases:
        row = []
        for eps in epsilons:
            row.append(integrate_mid(
                lambda x: abs(viscous_burgers_riemann(left, right, eps, x, 1.0) - limit(x)),
                -3.0, 4.0, 1400))
        distances.append(row)
        if not all(later < 0.6 * earlier for earlier, later in zip(row, row[1:])):
            raise SystemExit("entropy-selection: the viscous solutions do not converge")
    expansion = integrate_mid(
        lambda x: abs(viscous_burgers_riemann(0.0, 1.0, epsilons[-1], x, 1.0) - shock(x) * 0.0
                      - (0.0 if x < 0.5 else 1.0)), -3.0, 4.0, 1400)
    if expansion < 5.0 * distances[0][-1]:
        raise SystemExit("entropy-selection: the viscous solution is near the expansion shock")

    scene = Scene(
        "entropy-selection",
        "What vanishing viscosity selects",
        r"Exact solutions of \(u_t+uu_x=\varepsilon u_{xx}\) with Riemann data, by the Cole-Hopf "
        r"transformation, at \(t=1\) for \(\varepsilon=0.16,0.04,0.01\) (the accent curve is "
        r"the smallest). Left: \(u_L=0<u_R=1\). The expansion shock with a jump at "
        r"\(x=1/2\), dashed, is a weak solution of the inviscid equation, but the viscous "
        r"solutions converge to the fan \(u=x/t\) instead. Right: \(u_L=1>u_R=0\). The "
        r"viscous solutions are smooth fronts of width about \(\varepsilon\) travelling at the "
        r"Rankine-Hugoniot speed \(1/2\), and they converge to the shock. In both cases the "
        r"\(L^1\) distance to the limit at \(t=1\) falls with \(\varepsilon\). The limits "
        r"are the two branches of the entropy Riemann solution.",
        "Two panels of profiles against x. Left, three smooth increasing "
        "curves from zero to one that approach a straight ramp from x = 0 "
        "to x = 1, while a dashed vertical jump at x = one half is not "
        "approached. Right, three smooth decreasing fronts from one to zero "
        "that steepen toward a vertical jump at x = one half.",
        width=640.0, height=272.0)

    panels = [(56, "expansive data: the fan"), (366, "compressive data: the shock")]
    for (x0, title), (left, right, limit) in zip(panels, cases):
        frame = Frame(x0, 62, 240, 150, -0.8, 1.8, -0.1, 1.18)
        scene.panel_title(x0 - 32, 42, title)
        frame.axes(scene, x_label="x", origin_y=0.0)
        for level in (0.0, 1.0):
            scene.line(frame.x0 - 3, frame.Y(level), frame.x0, frame.Y(level), stroke="muted",
                       sw=SW_AXIS)
            scene.tick_label(frame.x0 - 6, frame.Y(level) + 3.5, num(level), anchor="end",
                             size=9.5)
        for tick in (0.0, 0.5, 1.0, 1.5):
            scene.line(frame.X(tick), frame.Y(0.0), frame.X(tick), frame.Y(0.0) + 4,
                       stroke="muted", sw=SW_AXIS)
            scene.tick_label(frame.X(tick), frame.Y(0.0) + 16, num(tick), size=9.5)
        if left < right:
            scene.path(frame.curve([(-0.8, 0.0), (0.5, 0.0), (0.5, 1.0), (1.8, 1.0)]),
                       stroke="warn", sw=SW_CURVE2, dash=DASH)
            scene.text(frame.X(0.47), frame.Y(0.72), "expansion shock", anchor="end",
                       fill="warn", size=9.5, halo=True)
        for index, eps in enumerate(epsilons):
            last = index == len(epsilons) - 1
            scene.path(frame.curve([(x, viscous_burgers_riemann(left, right, eps, x, 1.0))
                                    for x in xs]),
                       stroke="accent" if last else "muted", sw=SW_CURVE if last else SW_AXIS)
        scene.path(frame.curve([(x, limit(x)) for x in (-0.8, 0.0, 0.5, 0.5, 1.0, 1.8)]
                               if left < right else
                               [(-0.8, 1.0), (0.5, 1.0), (0.5, 0.0), (1.8, 0.0)]),
                   stroke="ink", sw=SW_AXIS)
        scene.math(frame.x0 + 6, frame.y0 + 10, r"u^\varepsilon(x,1)", t="u_eps(x, 1)",
                   anchor="start", fill="muted", size=10)
        row = distances[0 if left < right else 1]
        scene.math(frame.x0, frame.bottom + 40,
                   r"\|u^\varepsilon-u\|_{L^1}=" + ",\\ ".join(q3(d) for d in row),
                   t="L1 distance to the limit: " + ", ".join(q3(d) for d in row),
                   anchor="start", fill="muted", size=9.5)
    return scene


# --- the p-system: one rarefaction and one shock ----------------------------

def fig_p_system_riemann_fan() -> Scene:
    """A 0-rarefaction followed by a 1-shock for the stress law p(v) = exp(v)."""

    def sound(v: float) -> float:
        return math.exp(0.5 * v)

    def potential(v: float) -> float:
        """``A(v) = int_0^v c``."""
        return 2.0 * math.exp(0.5 * v) - 2.0

    def quotient(vl: float, vr: float) -> float:
        if abs(vr - vl) < 1e-12:
            return math.exp(vl)
        return (math.exp(vr) - math.exp(vl)) / (vr - vl)

    left = (0.0, 0.0)
    strengths = (-0.8, -1.0)
    middle = (left[0] + strengths[0], left[1] + potential(left[0] + strengths[0]) - potential(left[0]))
    right_v = middle[0] + strengths[1]
    speed = math.sqrt(quotient(middle[0], right_v))
    right = (right_v, middle[1] - speed * (right_v - middle[0]))
    fan_edges = (-sound(left[0]), -sound(middle[0]))
    # Lax: the 1-characteristics on both sides run into the shock.
    if not sound(right[0]) < speed < sound(middle[0]):
        raise SystemExit("p-system-riemann-fan: the shock is not a Lax 1-shock")
    if not fan_edges[0] < fan_edges[1] < 0.0 < speed:
        raise SystemExit("p-system-riemann-fan: the waves are not ordered")
    # The right state is on the family-1 Hugoniot curve: vector Rankine-Hugoniot
    # for F(v, w) = (-w, -p(v)).
    jump_v, jump_w = right[0] - middle[0], right[1] - middle[1]
    if (abs(-jump_w - speed * jump_v) > 1e-12
            or abs(-(math.exp(right[0]) - math.exp(middle[0])) - speed * jump_w) > 1e-12):
        raise SystemExit("p-system-riemann-fan: Rankine-Hugoniot fails")

    def strain(x: float, t: float) -> float:
        if x < fan_edges[0] * t:
            return left[0]
        if x < fan_edges[1] * t:
            return 2.0 * math.log(-x / t)
        if x < speed * t:
            return middle[0]
        return right[0]

    scene = Scene(
        "p-system-riemann-fan",
        "A Riemann problem for the p-system",
        r"The p-system \(v_t-w_x=0\), \(w_t-p(v)_x=0\) with \(p(v)=e^v\), so \(c=e^{v/2}\) and "
        r"\(A(v)=2e^{v/2}-2\). The left state \(u_L=(0,0)\) is joined to \(u_M\) by a "
        r"0-rarefaction of strength \(-0.8\), along which \(w-A(v)\) is constant, and \(u_M\) "
        r"to \(u_R\) by a 1-shock of strength \(-1\) on the Hugoniot curve. Left: the fan of "
        r"0-characteristics \(x/t=-c(v)\) and the shock \(x=st\), \(s\approx"
        + q3(speed) + r"\). The thin curves are 1-characteristics, \(dx/dt=c(v)\): they bend in "
        r"the fan, and the ones ahead of the shock are overtaken by it, the Lax condition "
        r"\(c(v_R)<s<c(v_M)\). Right: the two wave curves in the state plane, the solid parts "
        r"being the ones used. These explicit formulas are total; the Lean theorem concatenates "
        r"the same elementary waves for states close together.",
        "Two panels. Left, the space-time plane with a fan of straight rays "
        "opening to the left of the origin, a thick straight shock line "
        "leaning right, and thin curves that bend through the fan or run "
        "into the shock from the right. Right, the state plane with a "
        "rarefaction curve from the left state down to a middle state and a "
        "shock curve from the middle state to the right state, both "
        "continued as thin curves beyond the parts used.",
        width=640.0, height=300.0)

    plane = Frame(56, 62, 280, 170, -2.2, 1.8, 0.0, 2.0)
    scene.panel_title(24, 42, "the wave fan")
    plane.axes(scene, x_label="x", origin_y=0.0)
    scene.math(plane.x0 + 6, plane.y0 + 10, "t", anchor="start", fill="muted")
    top = plane.ymax
    for start in (-2.1, -1.6, -1.1, -0.6, 0.1, 0.3, 0.6, 0.9, 1.2, 1.5):
        points = [(start, 0.0)]
        x, t, dt = start, 0.0, 0.002
        while t < top:
            if x >= speed * t and start < 0.0:
                break
            if start > 0.0 and x <= speed * t:
                break
            x += sound(strain(x, t + 0.5 * dt)) * dt
            t += dt
            if x > plane.xmax:
                break
            points.append((x, t))
        scene.path(plane.curve(points), stroke="muted", sw=SW_AXIS)
    for k in range(7):
        ray = fan_edges[0] + (fan_edges[1] - fan_edges[0]) * k / 6.0
        scene.path(plane.curve([(0.0, 0.0), (ray * top, top)]), stroke="accent2", sw=SW_CURVE2)
    scene.path(plane.curve([(0.0, 0.0), (speed * top, top)]), stroke="accent", sw=2.6)
    for tick in (-2.0, -1.0, 0.0, 1.0):
        scene.line(plane.X(tick), plane.bottom, plane.X(tick), plane.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(plane.X(tick), plane.bottom + 16, num(tick), size=9.5)
    scene.math(plane.X(-1.95), plane.Y(1.55), r"u_L", fill="ink", size=FS_LABEL, halo=True)
    scene.math(plane.X(-0.35), plane.Y(1.7), r"u_M", fill="ink", size=FS_LABEL, halo=True)
    scene.math(plane.X(1.45), plane.Y(0.9), r"u_R", fill="ink", size=FS_LABEL, halo=True)
    scene.text(plane.X(-1.6), plane.Y(2.0) - 6, "0-rarefaction", fill="accent2", size=9.5)
    scene.text(plane.X(speed * top), plane.Y(2.0) - 6, "1-shock", fill="accent", size=9.5)

    state = Frame(412, 62, 196, 170, -2.4, 0.7, -1.1, 0.5)
    scene.panel_title(392, 42, "the state plane")
    scene.line(state.x0, state.Y(0.0), state.right, state.Y(0.0), stroke="muted", sw=SW_AXIS)
    scene.line(state.X(0.0), state.y0, state.X(0.0), state.bottom, stroke="muted", sw=SW_AXIS)
    scene.math(state.right + 8, state.Y(0.0) + 4, "v", anchor="start", fill="muted")
    scene.math(state.X(0.0) + 5, state.y0 + 8, "w", anchor="start", fill="muted")

    def family0(v: float) -> float:
        if v <= left[0]:
            return left[1] + potential(v) - potential(left[0])
        return left[1] + math.sqrt(quotient(left[0], v)) * (v - left[0])

    def family1(v: float) -> float:
        if v >= middle[0]:
            return middle[1] - (potential(v) - potential(middle[0]))
        return middle[1] - math.sqrt(quotient(middle[0], v)) * (v - middle[0])

    for family, role in ((family0, "accent2"), (family1, "accent")):
        inside = [(v, family(v)) for v in (-2.4 + 3.1 * k / 240.0 for k in range(241))
                  if state.ymin <= family(v) <= state.ymax]
        scene.path(state.curve(inside), stroke=role, sw=SW_AXIS)
    scene.path(state.sample(family0, middle[0], left[0], 60), stroke="accent2", sw=SW_CURVE)
    scene.path(state.sample(family1, right[0], middle[0], 60), stroke="accent", sw=SW_CURVE)
    for point, tex, dx, dy in ((left, "u_L", 6, -6), (middle, "u_M", 4, 16), (right, "u_R", -6, -8)):
        scene.circle(state.X(point[0]), state.Y(point[1]), 3.0, fill="ink")
        scene.math(state.X(point[0]) + dx, state.Y(point[1]) + dy, tex,
                   anchor="end" if dx < 0 else "start", fill="ink", size=FS_LABEL, halo=True)
    scene.math(state.X(-2.3), state.Y(-1.02), r"w-A(v)\text{ const}", t="w - A(v) constant",
               anchor="start", fill="accent2", size=9)
    scene.text(24, 284, "Solid in the state plane: the path taken from the left state to the "
               "right state.", anchor="start", fill="muted", size=9.5)
    return scene


# --- Lax-Oleinik: the N-wave -------------------------------------------------

NWAVE_LEFT = 1.0
NWAVE_RIGHT = 1.6
NWAVE_SHIFT = 0.5


def nwave_lobes(s: float) -> float:
    """``int_0^s`` of ``sin(pi s)`` on [-1, 0] and ``1.6 sin(pi s)`` on [0, 1], zero outside."""
    s = max(-1.0, min(1.0, s))
    scale = NWAVE_LEFT if s < 0.0 else NWAVE_RIGHT
    return scale * (1.0 - math.cos(math.pi * s)) / math.pi


def nwave_potential(y: float) -> float:
    """``h(y) = int_0^y g`` for the lobes shifted right by 1/2.

    The shift puts the minimum of ``h`` at ``y = 1/2`` rather than at the
    origin. Every interior footpoint then tends to ``1/2``, the solution
    to ``(x - 1/2)/t``, and the distance to the N-wave decays exactly at the
    rate ``t^(-1/2)``; with the minimum at the origin it would decay faster
    than the theorem needs.
    """
    return nwave_lobes(y - NWAVE_SHIFT) - nwave_lobes(-NWAVE_SHIFT)


def lax_oleinik_burgers(t: float, xs: list[float]) -> list[float]:
    """The Lax-Oleinik solution of Burgers at time ``t`` on sorted points ``xs``.

    ``u = (x - y*)/t`` where ``y*`` minimizes ``(x - y)^2/(2t) + h(y)``, that is,
    maximizes ``x y - phi(y)`` with ``phi(y) = y^2/2 + t h(y)``. The maximizer
    is a vertex of the lower convex hull of ``phi`` sampled on a grid, and it
    moves monotonically with ``x``, so one pass along the hull serves every
    point.
    """
    reach = max(abs(xs[0]), abs(xs[-1])) + 2.0
    a, b = NWAVE_SHIFT - 1.0, NWAVE_SHIFT + 1.0
    inner = [a + (b - a) * k / 4000.0 for k in range(4001)]
    below = int((reach + a) / 0.005) + 1
    above = int((reach - b) / 0.005) + 1
    grid = ([a - (reach + a) * k / below for k in range(below, 0, -1)] + inner
            + [b + (reach - b) * k / above for k in range(1, above + 1)])
    hull: list[tuple[float, float]] = []
    for y in grid:
        point = (y, 0.5 * y * y + t * nwave_potential(y))
        while len(hull) >= 2:
            (y1, p1), (y2, p2) = hull[-2], hull[-1]
            if (p2 - p1) * (point[0] - y1) >= (point[1] - p1) * (y2 - y1):
                hull.pop()
            else:
                break
        hull.append(point)
    out, k = [], 0
    for x in xs:
        while k + 1 < len(hull) and (hull[k + 1][1] - hull[k][1]) <= x * (hull[k + 1][0] - hull[k][0]):
            k += 1
        out.append((x - hull[k][0]) / t)
    return out


def fig_n_wave() -> Scene:
    """Lax-Oleinik solutions of Burgers approaching the N-wave at rate t^(-1/2)."""
    lobe_neg = 4.0 * NWAVE_LEFT / math.pi
    lobe_pos = 4.0 * NWAVE_RIGHT / math.pi
    lo, hi = -math.sqrt(lobe_neg), math.sqrt(lobe_pos)

    def nwave(x: float, t: float) -> float:
        return x / t if -math.sqrt(lobe_neg * t) < x < math.sqrt(lobe_pos * t) else 0.0

    def l1_error(t: float) -> float:
        reach = math.sqrt(lobe_pos * t) + 3.0
        n = 6000
        xs = [-reach + 2.0 * reach * (k + 0.5) / n for k in range(n)]
        us = lax_oleinik_burgers(t, xs)
        return sum(abs(u - nwave(x, t)) for x, u in zip(xs, us)) * (2.0 * reach / n)

    shown = [1.0, 4.0, 16.0, 64.0]
    profiles = []
    for t in shown:
        xis = [-2.0 + 4.0 * k / 800.0 for k in range(801)]
        us = lax_oleinik_burgers(t, [xi * math.sqrt(t) for xi in xis])
        profiles.append([(xi, math.sqrt(t) * u) for xi, u in zip(xis, us)])
    times = [2.0 ** k for k in range(0, 11)]
    errors = [l1_error(t) for t in times]
    tail = [math.log(errors[k + 1] / errors[k]) / math.log(times[k + 1] / times[k])
            for k in range(len(times) - 4, len(times) - 1)]
    if not all(-0.65 < rate < -0.35 for rate in tail):
        raise SystemExit(f"n-wave: the L1 error does not decay like t^(-1/2): {tail}")

    scene = Scene(
        "n-wave",
        "The N-wave",
        r"Burgers' equation with initial data \(g(y)=\sin\pi(y-\tfrac12)\) on "
        r"\([-\tfrac12,\tfrac12]\) and \(1.6\sin\pi(y-\tfrac12)\) on \([\tfrac12,\tfrac32]\), "
        r"solved by the Lax-Oleinik formula: \(u=(x-y^*)/t\) "
        r"with \(y^*\) minimizing \((x-y)^2/(2t)+\int_0^yg\). The lobe masses are "
        r"\(p=4/\pi\) and \(q=6.4/\pi\). Left: \(\sqrt t\,u\) against \(x/\sqrt t\) at "
        r"\(t=1,4,16,64\), the accent curve being the latest. In these variables the N-wave, "
        r"which equals \(x/t\) for \(-\sqrt{pt}<x<\sqrt{qt}\) and zero outside, is the "
        r"fixed shape drawn thin in ink, with jumps at \(-\sqrt p\) and \(\sqrt q\). Right: the "
        r"computed \(\int|u-N|\,dx\) against \(t\) on logarithmic axes, with a dashed line of "
        r"slope \(-1/2\); the last steps have slopes between "
        + q2(min(tail)) + r" and " + q2(max(tail)) + r". The rate is attained here because "
        r"\(\int_0^yg\) is smallest at \(y=\tfrac12\), so the footpoints tend to "
        r"\(\tfrac12\) and not to the centre of the N-wave.",
        "Two panels. Left, four rescaled solution profiles, each a rising "
        "straight segment between two jumps, the later ones closer to a thin "
        "reference shape with jumps at fixed positions. Right, a log-log plot "
        "of the error against time whose dots follow a dashed line of slope "
        "minus one half.",
        width=640.0, height=282.0)

    frame = Frame(60, 62, 280, 160, -2.0, 2.0, -1.35, 1.65)
    scene.panel_title(24, 42, "the rescaled profile")
    frame.axes(scene, origin_y=0.0)
    scene.math(frame.right + 8, frame.Y(0.0) + 4, r"x/\sqrt t", t="x/sqrt(t)", anchor="start",
               fill="muted", size=10)
    for index, profile in enumerate(profiles):
        last = index == len(profiles) - 1
        scene.path(frame.curve(profile, tol=0.15), stroke="accent" if last else "muted",
                   sw=SW_CURVE if last else SW_AXIS)
    scene.path(frame.curve([(-2.0, 0.0), (lo, 0.0), (lo, lo), (hi, hi), (hi, 0.0), (2.0, 0.0)]),
               stroke="ink", sw=SW_AXIS)
    for tick, tex, plain in ((lo, r"-\sqrt p", "-sqrt(p)"), (hi, r"\sqrt q", "sqrt(q)")):
        scene.line(frame.X(tick), frame.Y(0.0), frame.X(tick), frame.Y(0.0) + 4, stroke="muted",
                   sw=SW_AXIS)
        scene.math(frame.X(tick), frame.Y(0.0) + 17 if tick > 0 else frame.Y(0.0) - 8, tex,
                   t=plain, fill="muted", size=9.5, halo=True)
    scene.math(frame.x0 + 6, frame.y0 + 10, r"\sqrt t\,u", t="sqrt(t) u", anchor="start",
               fill="muted", size=10)

    graph = Frame(430, 62, 176, 160, 0.0, math.log10(times[-1]),
                  math.log10(min(errors)) - 0.15, math.log10(max(errors)) + 0.15)
    scene.panel_title(396, 42, "the L1 error")
    scene.line(graph.x0, graph.bottom, graph.right, graph.bottom, stroke="muted", sw=SW_AXIS)
    scene.line(graph.x0, graph.y0, graph.x0, graph.bottom, stroke="muted", sw=SW_AXIS)
    anchor = (math.log10(times[-1]), math.log10(errors[-1]))
    scene.path(graph.curve([(0.6, anchor[1] + 0.5 * (anchor[0] - 0.6)), anchor]), stroke="muted",
               sw=SW_CURVE2, dash=DASH)
    scene.path(graph.curve([(math.log10(t), math.log10(e)) for t, e in zip(times, errors)]),
               stroke="accent", sw=SW_CURVE2)
    for t, e in zip(times, errors):
        scene.circle(graph.X(math.log10(t)), graph.Y(math.log10(e)), 2.6, fill="accent")
    for power in (0, 1, 2, 3):
        scene.line(graph.X(power), graph.bottom, graph.X(power), graph.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(graph.X(power), graph.bottom + 16, rf"10^{power}", t=f"10^{power}",
                         size=9.5)
    scene.math(graph.right + 8, graph.bottom + 4, "t", anchor="start", fill="muted")
    scene.math(graph.X(1.6), graph.Y(anchor[1] + 0.5 * (anchor[0] - 1.6)) - 10,
               r"\text{slope }-1/2", t="slope -1/2", anchor="start", fill="muted", size=9.5,
               halo=True)
    scene.math(graph.x0 + 6, graph.y0 + 10, r"\int|u-N|\,dx", t="L1 error", anchor="start",
               fill="muted", size=10)
    return scene


# Two figures for the fluid chapter: the planar Taylor-Green vortex and Kovasznay's
# wake, with the fields, pressures and viscosities of PDE/Examples/Research; the
# builders re-derive both Navier-Stokes residuals by finite differences before
# drawing.


def _fb_residual_check(name: str, fields, times, points, nu: float,
                       steady: bool) -> None:
    """Central differences of u_t + (u.grad)u + grad p - nu Lap u and div u."""
    step = 1e-4
    for t in times:
        for x, y in points:
            def comp(i, a=x, b=y, s=t):
                return fields(s, a, b)[i]

            u, v = comp(0), comp(1)
            dudx = (comp(0, x + step) - comp(0, x - step)) / (2 * step)
            dudy = (comp(0, x, y + step) - comp(0, x, y - step)) / (2 * step)
            dvdx = (comp(1, x + step) - comp(1, x - step)) / (2 * step)
            dvdy = (comp(1, x, y + step) - comp(1, x, y - step)) / (2 * step)
            dpdx = (comp(2, x + step) - comp(2, x - step)) / (2 * step)
            dpdy = (comp(2, x, y + step) - comp(2, x, y - step)) / (2 * step)
            lap_u = (comp(0, x + step) + comp(0, x - step) + comp(0, x, y + step)
                     + comp(0, x, y - step) - 4 * u) / step ** 2
            lap_v = (comp(1, x + step) + comp(1, x - step) + comp(1, x, y + step)
                     + comp(1, x, y - step) - 4 * v) / step ** 2
            if steady:
                dudt = dvdt = 0.0
            else:
                dudt = (comp(0, x, y, t + step) - comp(0, x, y, t - step)) / (2 * step)
                dvdt = (comp(1, x, y, t + step) - comp(1, x, y, t - step)) / (2 * step)
            rx = dudt + u * dudx + v * dudy + dpdx - nu * lap_u
            ry = dvdt + u * dvdx + v * dvdy + dpdy - nu * lap_v
            if abs(dudx + dvdy) > 1e-6 or abs(rx) > 1e-4 or abs(ry) > 1e-4:
                raise SystemExit(f"{name}: the Navier-Stokes residual is not zero "
                                 f"at ({x}, {y}, {t}): {rx}, {ry}")


def fig_taylor_green_vortex() -> Scene:
    """The planar Taylor-Green cells and the decay of their energy.

    psi = exp(-2t) sin x sin y, u = psi_y, v = -psi_x, p = -exp(-4t)(sin^2 x
    + sin^2 y)/2 and unit viscosity, exactly the Lean example. Vorticity is
    2 psi, so every cell keeps its shape and loses amplitude at rate 2.
    """
    def fields(t, x, y):
        a = math.exp(-2 * t)
        return (a * math.sin(x) * math.cos(y), -a * math.cos(x) * math.sin(y),
                -(a * a) * (math.sin(x) ** 2 + math.sin(y) ** 2) / 2)

    samples = [(0.3, 1.1), (2.0, -0.7), (4.4, 5.2), (-1.3, 2.9)]
    _fb_residual_check("taylor-green-vortex", fields, (0.0, 0.35, 1.0), samples,
                       1.0, steady=False)
    step = 1e-4
    for x, y in samples:
        vort = ((fields(0, x + step, y)[1] - fields(0, x - step, y)[1])
                - (fields(0, x, y + step)[0] - fields(0, x, y - step)[0])) / (2 * step)
        if abs(vort - 2 * math.sin(x) * math.sin(y)) > 1e-6:
            raise SystemExit("taylor-green-vortex: vorticity is not 2 psi")

    def cell_energy(t: float, n: int = 48) -> float:
        h = 2 * math.pi / n
        total = 0.0
        for i in range(n):
            for j in range(n):
                u, v, _ = fields(t, (i + 0.5) * h, (j + 0.5) * h)
                total += 0.5 * (u * u + v * v) * h * h
        return total

    e0 = cell_energy(0.0)
    if abs(e0 - math.pi ** 2) > 1e-9:
        raise SystemExit("taylor-green-vortex: the period-square energy is not pi^2")
    dots = [0.1 * k for k in range(0, 13, 2)]
    ratios = [cell_energy(t) / e0 for t in dots]
    if any(abs(r - math.exp(-4 * t)) > 1e-12 for r, t in zip(ratios, dots)):
        raise SystemExit("taylor-green-vortex: the energy does not decay like exp(-4t)")

    scene = Scene(
        "taylor-green-vortex",
        "Cells that keep their shape while they decay",
        r"Left: streamlines of the planar Taylor-Green vortex over one period square. "
        r"The streamfunction is \(\psi=e^{-2t}\sin x\sin y\), so "
        r"\(u=e^{-2t}\sin x\cos y\) and \(v=-e^{-2t}\cos x\sin y\). The vorticity "
        r"\(\omega=2\psi\) is positive in the shaded cells, which turn counterclockwise, "
        r"and negative in the others. Because \(\omega\) is a multiple of \(\psi\), "
        r"advection carries vorticity along its own level sets and the nonlinear term is a "
        r"pressure gradient. Only the viscous term is left, and at unit viscosity it removes "
        r"amplitude at the rate \(|k|^2=2\). The drawn curves are the levels "
        r"\(\sin x\sin y=\pm0.2,\pm0.5,\pm0.8\); they are the same at every time. Right: the "
        r"kinetic energy in the period square is \(\pi^2e^{-4t}\). The dots are a midpoint "
        r"quadrature of that energy at seven times, divided by its value at \(t=0\). On the "
        r"whole plane the flow has infinite energy.",
        "Left: a square of side two pi divided into four cells of closed "
        "streamlines, two shaded cells turning counterclockwise and two "
        "unshaded cells turning clockwise, with arrow heads on one streamline "
        "of each cell. Right: two decaying exponential curves, the amplitude "
        "exp(-2t) and the energy ratio exp(-4t), with dots on the energy curve.",
        width=640.0, height=346.0)

    two_pi = 2 * math.pi
    box = Frame(52, 64, 220, 220, 0.0, two_pi, 0.0, two_pi)
    scene.panel_title(24, 38, "streamlines at any time")
    for i in range(2):
        for j in range(2):
            if (i + j) % 2 == 0:
                scene.rect(box.X(i * math.pi), box.Y((j + 1) * math.pi),
                           box.X(math.pi) - box.X(0), box.Y(0) - box.Y(math.pi),
                           fill="band")

    def stream(x: float, y: float) -> float:
        return math.sin(x) * math.sin(y)

    for level in (0.2, 0.5, 0.8, -0.2, -0.5, -0.8):
        segments = contours(stream, 0.0, two_pi, 0.0, two_pi, level, n=120)
        scene.path(seg_path(box, segments),
                   stroke="accent" if level > 0 else "accent2",
                   sw=SW_CURVE if abs(level) == 0.5 else SW_CURVE2)
    # One arrow head per cell, on the level |psi| = 0.5 at the cell's top point.
    rise = math.pi / 2 - math.asin(0.5)
    for i in range(2):
        for j in range(2):
            cx, cy = (i + 0.5) * math.pi, (j + 0.5) * math.pi + rise
            if abs(abs(stream(cx, cy)) - 0.5) > 1e-12:
                raise SystemExit("taylor-green-vortex: an arrow is off its streamline")
            u, v, _ = fields(0.0, cx, cy)
            role = "accent" if stream(cx, cy) > 0 else "accent2"
            scene.area(arrow_head(box.X(cx), box.Y(cy), u, -v, size=7.5), fill=role)
    scene.rect(box.x0, box.y0, box.w, box.h, stroke="ink", fill="", sw=SW_AXIS)
    for value, tex in ((0.0, "0"), (math.pi, r"\pi"), (two_pi, r"2\pi")):
        scene.math(box.X(value), box.bottom + 16, tex, fill="muted", size=10)
        scene.math(box.x0 - 7, box.Y(value) + 4, tex, anchor="end", fill="muted",
                   size=10)
    scene.math(box.right + 10, box.bottom + 4, "x", anchor="start", fill="muted")
    scene.math(box.x0 - 4, box.y0 - 8, "y", anchor="start", fill="muted")
    scene.math(box.X(math.pi / 2), box.Y(math.pi / 2) + 4, r"\omega>0",
               t="omega > 0", size=10, halo=True)
    scene.math(box.X(1.5 * math.pi), box.Y(math.pi / 2) + 4, r"\omega<0",
               t="omega < 0", size=10, halo=True)

    decay = Frame(366, 64, 226, 196, 0.0, 1.3, 0.0, 1.08)
    scene.panel_title(338, 38, "the energy in one period square")
    decay.axes(scene, x_label="t", origin_y=0.0)
    for value in (0.5, 1.0):
        scene.line(decay.x0 - 4, decay.Y(value), decay.x0, decay.Y(value),
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(decay.x0 - 8, decay.Y(value) + 4, q2(value), anchor="end",
                         size=10)
    for value in (0.5, 1.0):
        scene.line(decay.X(value), decay.bottom, decay.X(value), decay.bottom + 4,
                   stroke="muted", sw=SW_AXIS)
        scene.tick_label(decay.X(value), decay.bottom + 16, q2(value), size=10)
    scene.path(decay.sample(lambda t: math.exp(-2 * t), 0.0, 1.3, 130),
               stroke="accent2", sw=SW_CURVE2)
    scene.path(decay.sample(lambda t: math.exp(-4 * t), 0.0, 1.3, 130),
               stroke="accent", sw=SW_CURVE)
    for t, ratio in zip(dots, ratios):
        scene.circle(decay.X(t), decay.Y(ratio), 3.0, fill="accent")
    for row, (role, width, tex, fallback) in enumerate((
            ("accent2", SW_CURVE2, r"e^{-2t}\text{, the amplitude}", "amplitude exp(-2t)"),
            ("accent", SW_CURVE, r"E(t)/E(0)=e^{-4t}\text{, dots by quadrature}",
             "energy ratio exp(-4t), dots by quadrature"))):
        y = 298 + 18 * row
        scene.line(366, y - 4, 388, y - 4, stroke=role, sw=width)
        scene.math(394, y, tex, t=fallback, anchor="start", fill=role, size=10.5)
    scene.math(366, 334 - 0, r"E(0)=\pi^2,\quad \nu=1,\quad |k|^2=2",
               t="E(0) = pi^2, unit viscosity, |k|^2 = 2", anchor="start",
               fill="muted", size=10.5)
    return scene


def fig_kovasznay_flow() -> Scene:
    """Kovasznay's wake with lambda=-1, k=2, nu=1/3, as in the Lean example."""
    nu, lam, wave = 1.0 / 3.0, -1.0, 2.0
    if abs(nu * (lam * lam - wave * wave) - lam) > 1e-15:
        raise SystemExit("kovasznay-flow: the dispersion relation fails")

    def fields(_t, x, y):
        e = math.exp(lam * x)
        return (1 - e * math.cos(wave * y), -(e * math.sin(wave * y) / 2),
                -(e * e / 2))

    def stream(x: float, y: float) -> float:
        return y - math.exp(lam * x) * math.sin(wave * y) / 2

    samples = [(0.2, 0.4), (-0.4, 1.1), (1.7, -0.9), (0.9, 2.6)]
    _fb_residual_check("kovasznay-flow", fields, (0.0,), samples, nu, steady=True)
    step = 1e-5
    for x, y in samples:
        u, v, _ = fields(0, x, y)
        if (abs((stream(x, y + step) - stream(x, y - step)) / (2 * step) - u) > 1e-8
                or abs(-(stream(x + step, y) - stream(x - step, y)) / (2 * step) - v)
                > 1e-8):
            raise SystemExit("kovasznay-flow: psi does not generate the velocity")

    xmin, xmax = -0.5, 2.5
    ymin, ymax = -math.pi / 2, math.pi / 2
    scene = Scene(
        "kovasznay-flow",
        "A steady wake behind a row of obstacles",
        r"Streamlines of Kovasznay's exact solution with \(\lambda=-1\), \(k=2\) and "
        r"\(\nu=1/3\): \(u=1-e^{-x}\cos2y\), \(v=-\tfrac12e^{-x}\sin2y\), "
        r"\(p=-\tfrac12e^{-2x}\). The three numbers satisfy "
        r"\(\nu(\lambda^2-k^2)=\lambda\), which is the whole condition for "
        r"\(e^{\lambda x}\) to balance convection against diffusion. The streamfunction "
        r"is \(\psi=y-\tfrac12e^{-x}\sin2y\), and the curves are its levels "
        r"\(\pm0.1,\pm0.3,\dots,\pm1.5\). The pattern repeats with period \(\pi\) in \(y\), "
        r"and the lines \(y=\pm\pi/2\) are streamlines. In the shaded region "
        r"\(e^{-x}\cos2y>1\), so \(u<0\) and the fluid runs backwards. The boundary of "
        r"that region is where streamlines turn vertical. The dot is the stagnation point "
        r"at the origin. Far downstream the flow tends to the uniform stream \(u=1\); "
        r"upstream it grows like \(e^{-x}\), so its energy on the plane is infinite.",
        "A rectangle in the plane with the flow entering from the left. Closed "
        "and open streamlines bend around a shaded lobe on the left, centred "
        "on the horizontal axis, where the horizontal velocity is negative. A "
        "dot marks the stagnation point at the origin. To the right the "
        "streamlines straighten into horizontal lines.",
        width=640.0, height=318.0)
    frame = Frame(56, 40, 520, 234, xmin, xmax, ymin, ymax)
    # The reversed-flow lobe x < log cos(2y), |y| < pi/4, clipped to the frame.
    lobe_top = []
    for k in range(121):
        y = -math.pi / 4 + (math.pi / 2) * k / 120
        c = math.cos(wave * y)
        x = math.log(c) if c > 0 else -math.inf
        lobe_top.append((max(x, xmin), y))
    lobe = [(xmin, lobe_top[0][1])] + lobe_top + [(xmin, lobe_top[-1][1])]
    scene.area(poly_path(frame.project(lobe)) + "Z", fill="band")
    for x, y in lobe_top[1:-1:10]:
        if x > xmin and abs(fields(0, x, y)[0]) > 1e-12:
            raise SystemExit("kovasznay-flow: the lobe boundary is not u = 0")
    for index in range(16):
        level = -1.5 + 0.2 * index
        segments = contours(stream, xmin, xmax, ymin, ymax, level, n=150)
        scene.path(seg_path(frame, segments), stroke="accent",
                   sw=SW_CURVE2)
    # Arrow heads where each drawn level crosses x = 2.2, pointing with the flow.
    for index in range(16):
        level = -1.5 + 0.2 * index
        lo, hi = ymin, ymax
        for _ in range(60):
            mid = (lo + hi) / 2
            if stream(2.2, mid) < level:
                lo = mid
            else:
                hi = mid
        y = (lo + hi) / 2
        u, v, _ = fields(0, 2.2, y)
        if index % 3 == 1:
            scene.area(arrow_head(frame.X(2.2), frame.Y(y), u, -v, size=7.0),
                       fill="accent")
    # The level psi = 0 through the stagnation point, drawn from its formula.
    scene.line(frame.x0, frame.Y(0.0), frame.right, frame.Y(0.0), stroke="ink",
               sw=SW_CURVE2, dash=DASH)
    for sign in (1.0, -1.0):
        branch = []
        for k in range(1, 200):
            y = sign * (math.pi / 2) * k / 200
            x = math.log(math.sin(wave * y) / (wave * y))
            if x >= xmin:
                branch.append((x, y))
        if any(abs(stream(x, y)) > 1e-12 for x, y in branch):
            raise SystemExit("kovasznay-flow: the dividing streamline is misplaced")
        scene.path(frame.curve([(0.0, 0.0)] + branch), stroke="ink", sw=SW_CURVE2,
                   dash=DASH)
    scene.rect(frame.x0, frame.y0, frame.w, frame.h, stroke="ink", fill="",
               sw=SW_AXIS)
    scene.circle(frame.X(0.0), frame.Y(0.0), 3.6, fill="ink")
    scene.math(frame.X(0.06), frame.Y(0.0) + 15, r"u=v=0", t="stagnation point",
               anchor="start", size=10, halo=True)
    for value in (0.0, 1.0, 2.0):
        scene.tick_label(frame.X(value), frame.bottom + 16, q2(value), size=10)
    scene.tick_label(frame.x0, frame.bottom + 16, "-0.5", size=10)
    for value, tex in ((ymin, r"-\pi/2"), (0.0, "0"), (ymax, r"\pi/2")):
        scene.math(frame.x0 - 7, frame.Y(value) + 4, tex, anchor="end", fill="muted",
                   size=10)
    scene.math(frame.right + 8, frame.bottom + 4, "x", anchor="start", fill="muted")
    scene.math(frame.x0 - 4, frame.y0 - 8, "y", anchor="start", fill="muted")
    scene.rect(56, 296, 18, 11, fill="band")
    scene.math(80, 306, r"u<0", t="u < 0", anchor="start", fill="muted", size=10.5)
    scene.line(140, 302, 162, 302, stroke="ink", sw=SW_CURVE2, dash=DASH)
    scene.math(168, 306, r"\psi=0\text{, through the stagnation point}",
               t="the level psi = 0, through the stagnation point",
               anchor="start", fill="muted", size=10.5)
    return scene






def legendre_value(n: int, x: float) -> tuple[float, float]:
    """``P_n(x)`` and ``P_n'(x)`` by the three-term recurrence, ``P_n(1) = 1``."""
    if n == 0:
        return 1.0, 0.0
    before, current = 1.0, x
    for k in range(1, n):
        before, current = current, ((2 * k + 1) * x * current - k * before) / (k + 1)
    if abs(x) == 1.0:
        return current, (x ** (n + 1)) * n * (n + 1) / 2
    return current, n * (x * current - before) / (x * x - 1.0)


def gauss_legendre(n: int) -> list[tuple[float, float]]:
    """Nodes and weights of the ``n``-point rule on ``[-1, 1]``, ascending.

    Newton's method on ``P_n`` from the classical cosine guesses; the weight at
    a root ``r`` is ``2 / ((1 - r^2) P_n'(r)^2)``. The rule is checked against
    the moments it must reproduce, through degree ``2n - 1``.
    """
    rule = []
    for i in range(1, n + 1):
        x = math.cos(math.pi * (i - 0.25) / (n + 0.5))
        for _ in range(100):
            value, slope = legendre_value(n, x)
            step = value / slope
            x -= step
            if abs(step) < 1e-15:
                break
        _, slope = legendre_value(n, x)
        rule.append((x, 2.0 / ((1.0 - x * x) * slope * slope)))
    rule.sort()
    for k in range(2 * n):
        moment = 2.0 / (k + 1) if k % 2 == 0 else 0.0
        if abs(math.fsum(w * x ** k for x, w in rule) - moment) > 1e-12:
            raise SystemExit(f"gauss-legendre: the {n}-point rule misses degree {k}")
    return rule


def newton_cotes_weights(n: int) -> tuple[list[Fraction], list[Fraction]]:
    """Exact nodes and weights of the closed ``n``-point rule on ``[-1, 1]``.

    Each weight is the integral of a Lagrange basis polynomial, computed in
    rational arithmetic so that the negative weights are not a rounding effect.
    """
    nodes = [Fraction(-1) + Fraction(2 * j, n - 1) for j in range(n)]
    weights = []
    for i in range(n):
        coeffs = [Fraction(1)]
        scale = Fraction(1)
        for j in range(n):
            if j == i:
                continue
            product = [Fraction(0)] * (len(coeffs) + 1)
            for k, c in enumerate(coeffs):
                product[k + 1] += c
                product[k] -= c * nodes[j]
            coeffs = product
            scale *= nodes[i] - nodes[j]
        mass = sum(c * Fraction(2, k + 1) for k, c in enumerate(coeffs) if k % 2 == 0)
        weights.append(mass / scale)
    if sum(weights) != 2:
        raise SystemExit(f"positive-rule-convergence: Newton-Cotes {n} misses constants")
    return nodes, weights


def fig_positive_rule_convergence() -> Scene:
    """Newton-Cotes against Gauss on the Runge function, and why."""
    exact = 0.4 * math.atan(5.0)
    counts = list(range(2, 25))
    nc_error, nc_mass, gauss_error = [], [], []
    for n in counts:
        nodes, weights = newton_cotes_weights(n)
        value = sum(w / (1 + 25 * x * x) for x, w in zip(nodes, weights))
        nc_error.append(abs(float(value) - exact))
        nc_mass.append(float(sum(abs(w) for w in weights)))
        rule = gauss_legendre(n)
        gauss_error.append(abs(math.fsum(w / (1 + 25 * x * x) for x, w in rule) - exact))
    if not (nc_error[-1] > 1.0 and gauss_error[-1] < 1e-4):
        raise SystemExit("positive-rule-convergence: the classical contrast is missing")
    first_negative = next(n for n in counts
                          if min(newton_cotes_weights(n)[1]) < 0)
    if first_negative != 9:
        raise SystemExit("positive-rule-convergence: expected the first negative "
                         "Newton-Cotes weight at nine points")

    scene = Scene(
        "positive-rule-convergence",
        "Positive weights converge, Newton-Cotes need not",
        r"Left: the error of the closed Newton-Cotes rule and of the Gauss-Legendre rule "
        r"with \(n\) points for \(\int_{-1}^1 dx/(1+25x^2)=\tfrac25\arctan 5\), on a "
        r"logarithmic scale. The Newton-Cotes values are exact rational numbers, so their "
        r"growth is not rounding. Right: the sum of the absolute weights. For a rule exact on "
        r"constants with nonnegative weights this sum is the length \(2\), which is what "
        r"the Polya-Steklov bound uses. Newton-Cotes weights turn negative at \(n=9\) and "
        r"from \(n=11\) on, and their absolute sum grows without bound.",
        "Two panels over the number of points n from 2 to 24. Left, logarithmic "
        "error: the Newton-Cotes points oscillate and then climb above one, while "
        "the Gauss points fall steadily to about ten to the minus four and a half. "
        "Right, the sum of absolute weights: Gauss stays on the line at two, "
        "Newton-Cotes rises in a zigzag to above a thousand.",
        width=640.0, height=300.0)

    def log_panel(frame: Frame, lows: list[int], title: str) -> None:
        scene.panel_title(frame.x0 - 36, 36, title)
        frame.axes(scene, x_label="n", origin_y=frame.ymin)
        for tick in (2, 8, 16, 24):
            scene.line(frame.X(tick), frame.bottom, frame.X(tick), frame.bottom + 4,
                       stroke="muted", sw=SW_AXIS)
            scene.tick_label(frame.X(tick), frame.bottom + 16, str(tick), size=9.5)
        for power in lows:
            scene.line(frame.x0 - 4, frame.Y(power), frame.x0, frame.Y(power),
                       stroke="muted", sw=SW_AXIS)
            scene.tick_label(frame.x0 - 7, frame.Y(power) + 3.5, f"10^{{{power}}}",
                             t=f"1e{power}", anchor="end", size=9.5)

    left = Frame(70, 58, 220, 180, 1.0, 25.0, -5.0, 2.0)
    log_panel(left, [-4, -2, 0, 2], "error")
    scene.line(left.x0, left.Y(0.0), left.right, left.Y(0.0), stroke="muted",
               sw=SW_AXIS, dash=DOT)
    scene.path(left.curve([(n, math.log10(e)) for n, e in zip(counts, nc_error)]),
               stroke="warn", sw=SW_CURVE2)
    scene.path(left.curve([(n, math.log10(e)) for n, e in zip(counts, gauss_error)]),
               stroke="accent", sw=SW_CURVE)
    for n, e in zip(counts, nc_error):
        scene.circle(left.X(n), left.Y(math.log10(e)), 2.2, fill="warn")
    for n, e in zip(counts, gauss_error):
        scene.circle(left.X(n), left.Y(math.log10(e)), 2.2, fill="accent")
    scene.text(left.X(20), left.Y(math.log10(nc_error[-2])) - 12, "Newton-Cotes",
               fill="warn", size=10, halo=True)
    scene.text(left.X(19), left.Y(math.log10(gauss_error[-6])) + 18, "Gauss",
               fill="accent", size=10, halo=True)

    right = Frame(390, 58, 220, 180, 1.0, 25.0, 0.0, 4.0)
    log_panel(right, [0, 1, 2, 3, 4], "sum of absolute weights")
    scene.line(right.x0, right.Y(math.log10(2.0)), right.right, right.Y(math.log10(2.0)),
               stroke="accent", sw=SW_CURVE)
    scene.path(right.curve([(n, math.log10(m)) for n, m in zip(counts, nc_mass)]),
               stroke="warn", sw=SW_CURVE2)
    for n, m in zip(counts, nc_mass):
        scene.circle(right.X(n), right.Y(math.log10(m)), 2.2, fill="warn")
    scene.math(right.X(24), right.Y(math.log10(2.0)) + 14, r"\sum_i|w_i|=2",
               t="sum of |w| = 2", anchor="end", fill="accent", size=10, halo=True)
    scene.text(right.X(9), right.Y(math.log10(nc_mass[7])) - 10, "n = 9",
               fill="warn", size=9.5, halo=True)
    scene.text(left.x0 - 36, 280,
               "exact value (2/5) arctan 5, rational Newton-Cotes weights, "
               "floating-point Gauss nodes", anchor="start", fill="muted", size=9.5)
    return scene


def monic_legendre_three(x: float) -> float:
    return x ** 3 - 0.6 * x


def fig_gauss_exactness_limit() -> Scene:
    """Why the three-point rule stops at degree five."""
    nodes = [-math.sqrt(0.6), 0.0, math.sqrt(0.6)]
    rule = gauss_legendre(3)
    if max(abs(x - y) for (x, _), y in zip(rule, nodes)) > 1e-12:
        raise SystemExit("gauss-exactness-limit: the nodes are not the roots of p_3")
    odd = lambda x: monic_legendre_three(x) * x
    even = lambda x: monic_legendre_three(x) ** 2
    # Exact moments of x^4 - (3/5) x^2 and of x^6 - (6/5) x^4 + (9/25) x^2.
    if Fraction(2, 5) - Fraction(3, 5) * Fraction(2, 3) != 0:
        raise SystemExit("gauss-exactness-limit: p_3 is not orthogonal to x")
    if (Fraction(2, 7) - Fraction(6, 5) * Fraction(2, 5) + Fraction(9, 25) * Fraction(2, 3)
            != Fraction(8, 175)
            or abs(integrate(even, -1.0, 1.0, 4000) - 8.0 / 175.0) > 1e-6):
        raise SystemExit("gauss-exactness-limit: the mass of p_3^2 is not 8/175")

    scene = Scene(
        "gauss-exactness-limit",
        "Degree five is exact, degree six is not",
        r"The three-point Gauss-Legendre nodes are the roots \(0,\pm\sqrt{3/5}\) of the monic "
        r"Legendre polynomial \(p_3(x)=x^3-\tfrac35x\). Left: \(p_3(x)\,x\) has degree four and "
        r"vanishes at every node, so the rule returns zero; orthogonality makes the signed "
        r"area zero as well, and the rule is right. Every polynomial of degree at most five "
        r"splits as \(p_3q+r\) with \(q,r\) of degree at most two, so this is the whole "
        r"argument for exactness. Right: \(p_3^2\) has degree six and also vanishes at the "
        r"nodes, but its area is \(8/175>0\). No rule with three nodes integrates it, and "
        r"the same area is the constant in the error formula.",
        "Two panels over the interval from minus one to one, with three dots on the axis "
        "at the nodes. Left, a quartic curve with two shaded lobes above the axis and "
        "two below, labelled integral zero. Right, a nonnegative sextic curve touching "
        "the axis at the three nodes, with its shaded area labelled eight over 175.",
        width=640.0, height=282.0)
    xs = [-1.0 + 2.0 * k / 240 for k in range(241)]
    for frame, f, title, formula, fallback in (
            (Frame(56, 64, 236, 150, -1.0, 1.0, -0.1, 0.42), odd,
             "a degree four integrand", r"\int_{-1}^{1}p_3(x)\,x\,dx=0", "integral of p_3 x = 0"),
            (Frame(368, 64, 236, 150, -1.0, 1.0, -0.03, 0.17), even,
             "the degree six square", r"\int_{-1}^{1}p_3(x)^2\,dx=\tfrac{8}{175}",
             "integral of p_3 squared = 8/175")):
        scene.panel_title(frame.x0 - 32, 36, title)
        frame.axes(scene, x_label="x", origin_y=0.0)
        pieces: list[list[tuple[float, float]]] = [[]]
        for x in xs:
            value = f(x)
            if pieces[-1] and (value > 0) != (pieces[-1][-1][1] > 0) and abs(value) > 1e-12:
                pieces.append([])
            pieces[-1].append((x, value))
        for piece in pieces:
            if len(piece) < 2:
                continue
            positive = piece[len(piece) // 2][1] > 0
            scene.area(frame.fill_to(piece, 0.0), fill="band" if positive else "accent2",
                       fop=1 if positive else 0.35)
        scene.path(frame.curve([(x, f(x)) for x in xs]), stroke="accent", sw=SW_CURVE)
        for x in nodes:
            scene.circle(frame.X(x), frame.Y(0.0), 3.2, fill="ink")
        for tick in (-1.0, 0.0, 1.0):
            scene.tick_label(frame.X(tick), frame.bottom + 14, num(tick), size=9.5)
        scene.math(frame.X(0.0), frame.bottom + 36, formula, t=fallback, size=FS_LABEL)
    scene.text(56 - 32, 272, "dots: the nodes; the rule value is 0 in both panels",
               anchor="start", fill="muted", size=9.5)
    return scene


def fig_gauss_legendre_nodes() -> Scene:
    """The n-point nodes for n = 1..8 and the Legendre polynomial whose roots they are."""
    counts = list(range(1, 9))
    rules = [gauss_legendre(n) for n in counts]
    for rule, nxt in zip(rules, rules[1:]):
        inner = [x for x, _ in rule]
        outer = [x for x, _ in nxt]
        if not all(outer[i] < inner[i] < outer[i + 1] for i in range(len(inner))):
            raise SystemExit("gauss-legendre-nodes: consecutive node sets do not interlace")
    shown = 4  # the static frame: five nodes, large enough to read, small enough to count

    scene = Scene(
        "gauss-legendre-nodes",
        "Gauss-Legendre nodes as the number of points grows",
        r"Left: the nodes of the \(n\)-point Gauss-Legendre rule on \([-1,1]\) for "
        r"\(n=1,\dots,8\). The area of each disc is proportional to its weight; the weights "
        r"of a row are positive and add up to \(2\). The nodes crowd toward the endpoints, "
        r"where the weights are smallest, and the nodes of consecutive rows interlace. Right: "
        r"the Legendre polynomial \(P_n\), normalized by \(P_n(1)=1\), for the highlighted row. "
        r"Its roots are that row's nodes. The animation steps through \(n=1,\dots,8\); the "
        r"still frame is \(n=5\).",
        "Left, eight rows of dots across the interval from minus one to one, one dot in "
        "the top row and eight in the bottom, the dots smaller near the ends. Right, the "
        "graph of a Legendre polynomial oscillating between minus one and one with its "
        "roots marked on the axis; the highlighted row on the left matches it.",
        width=640.0, height=300.0)

    rows = Frame(64, 56, 232, 208, -1.0, 1.0, 8.6, 0.4)
    scene.panel_title(24, 36, "nodes and weights")
    for index, n in enumerate(counts):
        y = rows.Y(n)
        scene.rect(rows.x0 - 8, y - 11, rows.w + 16, 22, fill="band",
                   op=1 if index == shown else 0, anim=[slot(index, len(counts))])
        scene.line(rows.x0, y, rows.right, y, stroke="muted", sw=SW_AXIS)
        scene.math(rows.x0 - 14, y + 4, f"n={n}", t=f"n = {n}", anchor="end",
                   fill="muted", size=9.5)
        for x, w in rules[index]:
            scene.circle(rows.X(x), y, 5.2 * math.sqrt(w), fill="accent")
    for tick in (-1.0, 0.0, 1.0):
        scene.tick_label(rows.X(tick), rows.bottom + 18, num(tick), size=9.5)

    graph = Frame(376, 56, 232, 208, -1.0, 1.0, -1.08, 1.08)
    scene.panel_title(350, 36, "the Legendre polynomial")
    graph.axes(scene, x_label="x", origin_y=0.0)
    for value in (-1.0, 1.0):
        scene.line(graph.x0, graph.Y(value), graph.right, graph.Y(value),
                   stroke="muted", sw=SW_AXIS, dash=DOT)
        scene.tick_label(graph.x0 - 7, graph.Y(value) + 3.5, num(value), anchor="end",
                         size=9.5)
    xs = [-1.0 + 2.0 * k / 320 for k in range(321)]
    curves = graph.curve_frames([[(x, legendre_value(n, x)[0]) for x in xs] for n in counts])
    scene.path(curves[shown], stroke="accent", sw=SW_CURVE, anim=[discrete("d", curves)])
    for index, n in enumerate(counts):
        state = 1 if index == shown else 0
        for x, _ in rules[index]:
            scene.circle(graph.X(x), graph.Y(0.0), 3.0, fill="ink", op=state,
                         anim=[slot(index, len(counts))])
        scene.math(graph.right - 4, graph.y0 + 4, f"P_{{{n}}}", t=f"P{n}", anchor="end",
                   fill="accent", size=FS_LABEL, halo=True, op=state,
                   anim=[slot(index, len(counts))])
    for tick in (-1.0, 0.0, 1.0):
        scene.tick_label(graph.X(tick), graph.bottom + 18, num(tick), size=9.5)
    return scene


def fig_composite_error_decay() -> Scene:
    """Measured composite errors on the exponential against the proved bounds."""
    exact = math.e - 1.0
    panels = [1, 2, 3, 4, 6, 8, 12, 16, 24, 32]
    root = 1.0 / math.sqrt(3.0)

    def composite(rule, count: int) -> float:
        width = 1.0 / count
        return math.fsum(width * w * math.exp((k + t) * width)
                         for k in range(count) for w, t in rule)

    families = [
        ("trapezoid", [(0.5, 0.0), (0.5, 1.0)], 2, 12.0, "accent2", True),
        ("midpoint", [(1.0, 0.5)], 2, 24.0, "accent2", False),
        ("Simpson", [(1 / 6, 0.0), (4 / 6, 0.5), (1 / 6, 1.0)], 4, 2880.0, "accent", True),
        ("Gauss-Legendre 2", [(0.5, 0.5 - root / 2), (0.5, 0.5 + root / 2)], 4, 4320.0,
         "accent", False),
    ]
    data = []
    for name, rule, order, denominator, role, filled in families:
        errors = [abs(composite(rule, count) - exact) for count in panels]
        bounds = [math.e / (denominator * count ** order) for count in panels]
        if any(e > b for e, b in zip(errors, bounds)):
            raise SystemExit(f"composite-error-decay: {name} exceeds its proved bound")
        slope = (math.log(errors[-1]) - math.log(errors[-2])) / (
            math.log(panels[-1]) - math.log(panels[-2]))
        if abs(slope + order) > 0.05:
            raise SystemExit(f"composite-error-decay: {name} decays at rate {slope}")
        data.append((name, errors, bounds, role, filled))

    scene = Scene(
        "composite-error-decay",
        "Composite rules on N panels: measured error and proved bound",
        r"The error of four composite rules for \(\int_0^1e^x\,dx=e-1\) against the number "
        r"of equal panels \(N\), both axes logarithmic. Marks are measured errors; each dashed "
        r"line is the proved panel-rule bound \(C(b-a)^{m+1}/(DN^m)\) with \(C=e\). Left, "
        r"order \(m=2\): \(D=12\) for the trapezoid rule and \(D=24\) for the midpoint "
        r"rule. Right, order \(m=4\): \(D=2880\) for Simpson and \(D=4320\) for two-point "
        r"Gauss-Legendre. The slopes are \(-2\) and \(-4\), and the marks sit a constant "
        r"factor near \((e-1)/e\) below their bounds because \(|f^{(m)}|=e^x\) ranges "
        r"from \(1\) to \(e\) while the bound uses its maximum.",
        "Two log-log panels with the number of panels from 1 to 32 on the horizontal axis. "
        "Left, the trapezoid and midpoint errors fall on parallel straight lines of slope "
        "minus two from about ten to the minus one to ten to the minus four. Right, the "
        "Simpson and two-point Gauss errors fall with slope minus four from about ten to "
        "the minus three to ten to the minus nine and a half. Each series lies just below "
        "a dashed bound line.",
        width=640.0, height=300.0)

    def marker(x: float, y: float, role: str, round_mark: bool) -> None:
        if round_mark:
            scene.circle(x, y, 3.0, fill=role)
        else:
            scene.rect(x - 2.8, y - 2.8, 5.6, 5.6, stroke=role, fill="surface",
                       sw=SW_CURVE2)

    for column, (title, lows, ymin, ymax) in enumerate((
            ("second order", (0, -1, -2, -3, -4), -4.5, 0.0),
            ("fourth order", (-3, -5, -7, -9), -9.9, -2.7))):
        frame = Frame(70 + 320 * column, 52, 220, 200, 0.0, math.log10(32.0), ymin, ymax)
        scene.panel_title(frame.x0 - 46, 30, title)
        frame.axes(scene, x_label="N", origin_y=frame.ymin)
        for count in (1, 2, 4, 8, 16, 32):
            scene.line(frame.X(math.log10(count)), frame.bottom,
                       frame.X(math.log10(count)), frame.bottom + 4, stroke="muted",
                       sw=SW_AXIS)
            scene.tick_label(frame.X(math.log10(count)), frame.bottom + 16, str(count),
                             size=9.5)
        for power in lows:
            scene.line(frame.x0 - 4, frame.Y(power), frame.x0, frame.Y(power),
                       stroke="muted", sw=SW_AXIS)
            scene.tick_label(frame.x0 - 7, frame.Y(power) + 3.5, f"10^{{{power}}}",
                             t=f"1e{power}", anchor="end", size=9.5)
        legend_y = frame.Y(ymin) - 36
        for name, errors, bounds, role, filled in data[2 * column:2 * column + 2]:
            points = [(math.log10(c), math.log10(b)) for c, b in zip(panels, bounds)]
            scene.path(frame.curve(points), stroke=role, sw=SW_CURVE2, dash=DASH)
            for count, error in zip(panels, errors):
                marker(frame.X(math.log10(count)), frame.Y(math.log10(error)), role, filled)
            marker(frame.x0 + 16, legend_y - 4, role, filled)
            scene.text(frame.x0 + 26, legend_y, name, anchor="start", fill="ink", size=10)
            legend_y += 18
    scene.line(30, 286, 46, 286, stroke="muted", sw=SW_CURVE2, dash=DASH)
    scene.text(52, 290, "proved bound; marks are measured errors", anchor="start",
               fill="muted", size=9.5)
    return scene


# --- the catalogue -----------------------------------------------------------

BUILDERS = {
    "heat-stability": fig_heat_stability,
    "pde-zoo": fig_pde_zoo,
    "formalization-routes": fig_formalization_routes,
    "interval-green-function": fig_interval_green_function,
    "kovalevskaya-series": fig_kovalevskaya_series,
    "stokes-circulation": fig_stokes_circulation,
    "boundary-chart-normal": fig_boundary_chart_normal,
    "mollification": fig_mollification,
    "heaviside-dirac": fig_heaviside_dirac,
    "weak-derivative": fig_weak_derivative,
    "sobolev-reflection-extension": fig_sobolev_reflection_extension,
    "trace-height-average": fig_trace_height_average,
    "sobolev-ladder": fig_sobolev_ladder,
    "difference-quotient-limit": fig_difference_quotient_limit,
    "gagliardo-boundary-energy": fig_gagliardo_boundary_energy,
    "fundamental-solution": fig_fundamental_solution,
    "green-disc": fig_ell_green_disc,
    "mean-value": fig_mean_value,
    "hopf-lemma": fig_ell_hopf_lemma,
    "harnack-disc": fig_ell_harnack_disc,
    "moving-planes": fig_ell_moving_planes,
    "lax-milgram-projection": fig_lax_milgram_projection,
    "dirichlet-eigenfunctions": fig_ell_dirichlet_eigenfunctions,
    "heat-kernel": fig_heat_kernel,
    "heat-positivity": fig_heat_positivity,
    "heat-log-convexity": fig_heat_log_convexity,
    "galerkin-sine-convergence": fig_galerkin_sine_convergence,
    "dalembert": fig_dalembert,
    "wave-huygens": fig_wave_huygens,
    "cone-energy": fig_cone_energy,
    "shock-formation": fig_shock_formation,
    "p-system-riemann-fan": fig_p_system_riemann_fan,
    "entropy-selection": fig_entropy_selection,
    "n-wave": fig_n_wave,
    "taylor-green-vortex": fig_taylor_green_vortex,
    "kovasznay-flow": fig_kovasznay_flow,
    "axisymmetric-meridional-flow": fig_axisymmetric_meridional_flow,
    "stability-cost": fig_stability_cost,
    "fourier-evolution": fig_fourier_evolution,
    "direct-method": fig_direct_method,
    "cega-pipeline": fig_cega_pipeline,
    "interval-enclosure": fig_interval_enclosure,
    "certificate-budget": fig_certificate_budget,
    "taylor-model": fig_taylor_model,
    "gauss-legendre-nodes": fig_gauss_legendre_nodes,
    "gauss-exactness-limit": fig_gauss_exactness_limit,
    "positive-rule-convergence": fig_positive_rule_convergence,
    "composite-error-decay": fig_composite_error_decay,
}

# The order the figures appear in the data module, which is the order of the
# book: the landing page first, then the chapters.
FIGURE_IDS = list(BUILDERS)


DATA_TEMPLATE = """/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

/-!
# Figure data

Generated by `Blueprint/Tools/build-figures.py`. Do not edit by hand.

The JSON below is the drawing model of the book's figures: for each one a
caption, a description for a screen reader, and a flat list of marks in SVG
user units. A mark carries a colour *role*, not a colour, and
`Blueprint.Commands.Figures` maps the roles onto the site's `--leanpde-fig-*`
custom properties. The module imports nothing, so the long lines of the model
stay outside the reach of the style linters.
-/

namespace LeanPDE.FiguresData

/-- Drawing model of the book's figures; see `Blueprint.Commands.Figures`. -/
def json : String := r####"
{json}
"####

end LeanPDE.FiguresData
"""


def build_model() -> dict:
    missing = [fid for fid in FIGURE_IDS if fid not in BUILDERS]
    if missing:
        raise SystemExit(f"figures: no builder for {missing}")
    extra = sorted(set(BUILDERS) - set(FIGURE_IDS))
    if extra:
        raise SystemExit(f"figures: builder not listed in FIGURE_IDS: {extra}")
    figures = []
    for fid in FIGURE_IDS:
        scene = BUILDERS[fid]()
        if scene.id != fid:
            raise SystemExit(f"figures: builder for {fid} produced {scene.id}")
        for field in ("title", "caption", "alt"):
            if not getattr(scene, field).strip():
                raise SystemExit(f"figure {fid}: empty {field}")
        if "—" in scene.caption or "—" in scene.title:
            raise SystemExit(f"figure {fid}: em-dash in the prose")
        # The title is the one string `toTeX` interpolates into the PDF, so it
        # has to survive LaTeX without escaping: plain ASCII, no specials.
        if any(not 32 <= ord(ch) <= 126 for ch in scene.title):
            raise SystemExit(f"figure {fid}: the title reaches the PDF through "
                             f"toTeX, so it must be plain ASCII: {scene.title!r}")
        special = sorted(set(scene.title) & set("\\{}$&#^_~%"))
        if special:
            raise SystemExit(f"figure {fid}: LaTeX would choke on {special} in "
                             f"the title")
        figure = scene.to_json()
        problems = (containment_problems(figure) + label_problems(figure)
                    + caption_problems(scene.caption))
        if problems:
            for problem in problems[:6]:
                print(f"figure {fid}: {problem}", file=sys.stderr)
            raise SystemExit(f"figure {fid}: {len(problems)} marks are not fit "
                             f"to draw")
        figures.append(figure)
    return {
        "schemaVersion": SCHEMA_VERSION,
        "generator": GENERATOR,
        "figures": figures,
    }


def render_module(model: dict) -> str:
    json_text = json.dumps(model, indent=1, ensure_ascii=False)
    if '"####' in json_text:
        raise SystemExit("figure JSON contains the raw string terminator sequence")
    return DATA_TEMPLATE.format(json=json_text)


def describe(model: dict) -> str:
    animated = sum(1 for figure in model["figures"] if figure["animated"])
    marks = sum(len(figure["marks"]) for figure in model["figures"])
    return (f"{len(model['figures'])} figures, {animated} of them animated, "
            f"{marks} marks")


def check() -> int:
    if not DATA_PATH.exists():
        print(f"figures: {DATA_PATH} does not exist", file=sys.stderr)
        return 1
    model = build_model()
    expected = render_module(model)
    actual = DATA_PATH.read_text(encoding="utf8")
    if expected != actual:
        print(f"figures: {DATA_PATH.relative_to(REPO_ROOT)} is not what "
              f"{GENERATOR} computes; run it to regenerate", file=sys.stderr)
        expected_lines = expected.splitlines()
        actual_lines = actual.splitlines()
        for index in range(min(len(expected_lines), len(actual_lines))):
            if expected_lines[index] != actual_lines[index]:
                print(f"figures: first difference at line {index + 1}",
                      file=sys.stderr)
                print(f"  committed: {actual_lines[index][:160]}", file=sys.stderr)
                print(f"  computed:  {expected_lines[index][:160]}", file=sys.stderr)
                break
        else:
            print(f"figures: committed file has {len(actual_lines)} lines, "
                  f"computed has {len(expected_lines)}", file=sys.stderr)
        return 1
    print(f"Figures are consistent: {describe(model)}.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--check", action="store_true",
                        help="recompute the figures and fail if the committed "
                             "module differs")
    parser.add_argument("--json", metavar="PATH",
                        help="also write the drawing model to PATH")
    args = parser.parse_args()

    if args.check:
        return check()

    model = build_model()
    text = render_module(model)
    DATA_PATH.parent.mkdir(parents=True, exist_ok=True)
    existing = DATA_PATH.read_text(encoding="utf8") if DATA_PATH.exists() else None
    if existing != text:
        DATA_PATH.write_text(text, encoding="utf8")
    if args.json:
        Path(args.json).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json).write_text(json.dumps(model, indent=1, ensure_ascii=False)
                                   + "\n", encoding="utf8")
    print(f"Figures: {describe(model)}, written to "
          f"{DATA_PATH.relative_to(REPO_ROOT)}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
