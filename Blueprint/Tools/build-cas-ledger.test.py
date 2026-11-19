#!/usr/bin/env python3
"""Tests of `build-cas-ledger.py`: `python3 Blueprint/Tools/build-cas-ledger.test.py`.

Each test copies the generator into a temporary tree, writes the fixture files
there and runs only the copy, whose source roots and output are temporary. The
full-source tests read real `PDE/` files from the repository, or from
`LEANPDE_LEDGER_TEST_SOURCE_ROOT` when it is set.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

TOOLS = os.path.dirname(os.path.abspath(__file__))
SOURCE_ROOT = os.environ.get("LEANPDE_LEDGER_TEST_SOURCE_ROOT",
                             os.path.dirname(os.path.dirname(TOOLS)))


def generate(files: dict[str, str]) -> dict:
    with tempfile.TemporaryDirectory(prefix="leanpde-ledger-test-") as temporary:
        os.makedirs(os.path.join(temporary, "PDE"))
        os.makedirs(os.path.join(temporary, "Blueprint", "Tools"))
        generator = os.path.join(temporary, "Blueprint", "Tools", "build-cas-ledger.py")
        shutil.copyfile(os.path.join(TOOLS, "build-cas-ledger.py"), generator)
        for name, source in files.items():
            path = os.path.join(temporary, name)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8", newline="") as handle:
                handle.write(source)
        output = os.path.join(temporary, "ledger.json")
        subprocess.run([sys.executable, "-I", generator, "--json", output], check=True,
                       capture_output=True)
        with open(output, encoding="utf-8") as handle:
            before = handle.read()
        subprocess.run([sys.executable, "-I", generator, "--check", "--json", output], check=True,
                       capture_output=True)
        with open(output, encoding="utf-8") as handle:
            assert handle.read() == before
        return json.loads(before)


def cas_line(source: str) -> int:
    return next(i for i, line in enumerate(source.split("\n")) if re.search(r"\bcas\b", line)) + 1


ACTUAL = [
    ("PDE/Hyperbolic/HamiltonJacobi/Viscous/InitialValue.lean",
     "initialValueSolution_initial_trace",
     "∃ δ : ℝ, 0 < δ ∧ ∀ x t, ‖x - x₀‖ < δ → 0 < t → t < δ → "
     "|initialValueSolution ν g x t - g x₀| < ε",
     False),
    ("PDE/Spaces/Sobolev/Weighted/Reflection.lean",
     "reflection_memLp_and_integral_le",
     """let reflected := fun x : ℝ^n ↦
      if x i < 0 then sign * f (PDE.Common.coordinateReflection i x) else f x
    MemLp reflected 2 volume ∧
      (∫ x, reflected x ^ 2) ≤
        (2 / c) * ∫ x in {x : ℝ^n | 0 ≤ x i}, f x ^ 2 * w x""",
     True),
    ("PDE/Hyperbolic/ConservationLaw/Burgers/ColeHopf.lean",
     "coleHopf_jet_residual_eq_zero",
     """let k := -2 * ν; let u := k * b / a; let ut := k * (f * a - b * e) / a ^ 2;
      let ux := k * (c * a - b ^ 2) / a ^ 2;
      let uxx := k * (((d * a - b * c) * a ^ 2) - (c * a - b ^ 2) * (2 * a * b)) / a ^ 4; ut + u *
      ux - ν * uxx = 0""",
     False),
]


CONTROLS = [
    ("multiline norm", "theorem norm_control (x : ℝ) :\n    ‖x‖ = ‖x‖ := by\n  cas", "‖x‖ = ‖x‖"),
    ("named argument", "theorem named_control :\n    id (α := ℝ) 0 = 0 := by\n  cas",
     "id (α := ℝ) 0 = 0"),
    ("default binder", "theorem default_control (x : ℝ := 0) : x = x := by\n  cas", "x = x"),
    ("equation definition", """def equation_control : Nat → Nat
  | 0 => by
    have : (0 : ℝ) = 0 := by cas
    exact 0
  | n + 1 => n""", "Nat → Nat"),
    ("multiline equation alternative", """def multiline_equation : Nat → Nat
  | 0
      => by
    have : (0 : ℝ) = 0 := by cas
    exact 0
  | n + 1 => n""", "Nat → Nat"),
    ("shared equation RHS", """def shared_equation : Nat → Nat
  | 0 | 1 => by
    have : (0 : ℝ) = 0 := by cas
    exact 0
  | n + 2 => n""", "Nat → Nat"),
    ("absolute value with lambda", """theorem abs_lambda (x : ℝ) :
    |x| = (fun y : ℝ => y) |x| := by
  cas""", "|x| = (fun y : ℝ => y) |x|"),
    ("multiline absolute value", """theorem abs_multiline (x : ℝ) :
    |x +
      0| = |x| := by
  cas""", "|x + 0| = |x|"),
    ("parenthesized let", """theorem parenthesized_let :
    (let x := (0 : ℝ); x = 0) := by
  cas""", "(let x := (0 : ℝ); x = 0)"),
    ("nested lets and real proof delimiter", """theorem nested_let :
    let x := let y := (0 : ℝ); y
    let z := id (α := ℝ) x
    z = 0
    := by
  let ignored := (1 : ℝ)
  cas""", """let x := let y := (0 : ℝ); y
    let z := id (α := ℝ) x
    z = 0"""),
    ("identifier containing let", """theorem letdown (palette : ℝ) :
    palette = palette := by
  cas""", "palette = palette"),
    ("blank line inside let type", """theorem spaced_let :
    let x := (0 : ℝ)

    x = 0 := by
  cas""", "let x := (0 : ℝ)\n\n    x = 0"),
    ("long header", "theorem long_header :\n" + "    True ∧\n" * 85 + "    (0 : ℝ) = 0 := by\n  cas",
     "True ∧ " * 85 + "(0 : ℝ) = 0"),
]


class LedgerTests(unittest.TestCase):
    def test_roots_and_caches(self) -> None:
        source = "theorem identity : (0 : ℝ) = 0 := by\n  cas\n"
        ledger = generate({
            "PDE/Example.lean": source,
            "PDE/Fluid/Euler/Example.lean": source,
            "PDE/Examples/Example.lean": source,
            "PDE/.lake/Example.lean": source,
            ".lake/packages/Foreign/Example.lean": source,
            "Blueprint/Chapters/Example.lean": source,
        })
        self.assertEqual([row["path"] for row in ledger["rows"]], [
            "PDE/Example.lean",
            "PDE/Fluid/Euler/Example.lean",
            "PDE/Examples/Example.lean",
        ])
        self.assertTrue(all(row["library"] == "PDE" for row in ledger["rows"]))
        self.assertEqual(ledger["rows"][1]["module"], "PDE.Fluid.Euler.Example")
        self.assertEqual([row["scope"] for row in ledger["rows"]],
                         ["production", "production", "examples"])
        self.assertEqual(ledger["schemaVersion"], 1)

    def test_full_source_conclusion(self) -> None:
        for file, name, expected, private in ACTUAL:
            with self.subTest(name):
                with open(os.path.join(SOURCE_ROOT, file), encoding="utf-8") as handle:
                    source = handle.read()
                ledger = generate({file: source})
                rows = [row for row in ledger["rows"]
                        if row["decl"] is not None and row["decl"]["name"] == name]
                self.assertEqual(len(rows), 1)
                row = rows[0]
                self.assertEqual(row["statement"], expected)
                self.assertEqual(row["decl"]["fullName"] is None, private)
                self.assertEqual(row["path"], file)
                source_lines = source.split("\n")
                self.assertRegex(source_lines[row["decl"]["line"] - 1],
                                 rf"theorem {re.escape(name)}\b")
                self.assertRegex(source_lines[row["line"] - 1], r"\bcas\b")

    def test_declaration_parser(self) -> None:
        for name, source, expected in CONTROLS:
            with self.subTest(name):
                ledger = generate({"PDE/Examples/ParserFixture.lean": source + "\n"})
                self.assertEqual(ledger["summary"]["production"]["rows"], 0)
                self.assertEqual(ledger["summary"]["examples"]["rows"], 1)
                row = ledger["rows"][0]
                self.assertEqual(row["statement"], expected)
                self.assertEqual(row["decl"]["line"], 1)
                self.assertEqual(row["line"], cas_line(source))

    def test_fast_mode_labels(self) -> None:
        ledger = generate({"PDE/Examples/FastFixture.lean": """
theorem square_bound_fast : True := by
  cega [fast]
theorem square_bound_kernel : True := by
  cega
theorem fallback_fast : True := by
  cega [fast]
theorem lemma_control : True := by
  cega [known_certificate]
"""})
        self.assertEqual(ledger["summary"]["examples"]["rows"], 4)
        self.assertEqual([row["tactic"] for row in ledger["rows"]],
                         ["cega [fast]", "cega", "cega [fast]", "cega [lemmas]"])
        self.assertEqual([row["form"] for row in ledger["rows"]],
                         ["cega [fast]", "cega", "cega [fast]", "cega [known_certificate]"])


if __name__ == "__main__":
    unittest.main()
