/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Data.Rat.Defs

/-!
# Exact rational replay of Cox–de Boor recurrences

The tables here evaluate spline basis values and fixed polynomial
branches at the origin using exact rational arithmetic. Knot lists, active
cells, and degrees are explicit inputs; no profile data or external bounds
are assumed. The product-rule recurrences also compute first and second
branch derivatives.

`PDE.Analysis.Approximation.Splines.ReplaySemantics` identifies `basisTable`, `branchValues`,
`branchDerivatives`, and `branchSecondDerivatives` with the real Cox–de Boor quantities
whenever the real knot sequence agrees with the supplied rational list.

`derivativeWeights` is the degree-nine derivative stencil applied to a
degree-eight table. Its degree and ten-entry output are fixed.
`dot` contracts two finite rational lists, truncating to the shorter list as
specified by `List.zip`. Their interpretation as real derivatives is not proved
in `ReplaySemantics`.
-/

@[expose] public section

namespace CAS.Splines.RationalReplay

/-- Degree-zero basis values at the origin on a local knot window. -/
def initialTable (knots : List ℚ) : List ℚ :=
  (List.range (knots.length - 1)).map fun i ↦
    if knots.getD i 0 ≤ 0 ∧ 0 < knots.getD (i + 1) 0 then 1 else 0

/-- One Cox–de Boor recurrence step at the origin, with rational arithmetic. -/
def nextTable (knots : List ℚ) (degree : ℕ) (previous : List ℚ) : List ℚ :=
  (List.range (knots.length - degree - 1)).map fun i ↦
    (-(knots.getD i 0)) / (knots.getD (i + degree) 0 - knots.getD i 0) *
        previous.getD i 0 +
      knots.getD (i + degree + 1) 0 /
        (knots.getD (i + degree + 1) 0 - knots.getD (i + 1) 0) *
        previous.getD (i + 1) 0

/-- The full rational Cox–de Boor table obtained from degree zero. -/
def basisTable (knots : List ℚ) : ℕ → List ℚ
  | 0 => initialTable knots
  | degree + 1 => nextTable knots (degree + 1) (basisTable knots degree)

/-- Derivative weights for the degree-nine basis, from the degree-eight table. -/
def derivativeWeights (knots previous : List ℚ) : List ℚ :=
  (List.range 10).map fun i ↦
    9 / (knots.getD (i + 9) 0 - knots.getD i 0) * previous.getD i 0 -
      9 / (knots.getD (i + 10) 0 - knots.getD (i + 1) 0) * previous.getD (i + 1) 0

/-- The finite scalar product used in the tensor contraction. -/
def dot (left right : List ℚ) : ℚ :=
  (left.zip right).foldl (fun total pair ↦ total + pair.1 * pair.2) 0

/-- Degree-zero polynomial branch values at the origin for a selected knot cell.

Unlike `initialTable`, this indicator does not look at where the origin falls. It
selects one cell by hand and then follows the recurrence as if the origin were inside
it, which is exactly the polynomial branch that cell contributes.
-/
def initialBranchValues (knots : List ℚ) (cell : ℕ) : List ℚ :=
  (List.range (knots.length - 1)).map fun i ↦ if i = cell then 1 else 0

/-- Value recurrence for a fixed polynomial branch at the origin. -/
def branchValues (knots : List ℚ) (cell : ℕ) : ℕ → List ℚ
  | 0 => initialBranchValues knots cell
  | degree + 1 => nextTable knots (degree + 1) (branchValues knots cell degree)

/-- One product-rule step for the derivative of the fixed polynomial branch. -/
def nextBranchDerivatives (knots : List ℚ) (degree : ℕ)
    (values derivatives : List ℚ) : List ℚ :=
  (List.range (knots.length - degree - 1)).map fun i ↦
    (1 / (knots.getD (i + degree) 0 - knots.getD i 0) * values.getD i 0 +
      (-(knots.getD i 0)) / (knots.getD (i + degree) 0 - knots.getD i 0) *
        derivatives.getD i 0) +
    ((-1) / (knots.getD (i + degree + 1) 0 - knots.getD (i + 1) 0) *
        values.getD (i + 1) 0 +
      knots.getD (i + degree + 1) 0 /
        (knots.getD (i + degree + 1) 0 - knots.getD (i + 1) 0) *
        derivatives.getD (i + 1) 0)

/-- Product-rule derivatives of the fixed polynomial branch at the origin. -/
def branchDerivatives (knots : List ℚ) (cell : ℕ) : ℕ → List ℚ
  | 0 => List.replicate (knots.length - 1) 0
  | degree + 1 => nextBranchDerivatives knots (degree + 1)
      (branchValues knots cell degree) (branchDerivatives knots cell degree)

/-- One product-rule step for the second derivative of the fixed polynomial branch. -/
def nextSecondDerivatives (knots : List ℚ) (degree : ℕ)
    (first second : List ℚ) : List ℚ :=
  (List.range (knots.length - degree - 1)).map fun i ↦
    ((-(knots.getD i 0)) / (knots.getD (i + degree) 0 - knots.getD i 0) *
        second.getD i 0 +
      (2 * (1 / (knots.getD (i + degree) 0 - knots.getD i 0))) * first.getD i 0) +
    (knots.getD (i + degree + 1) 0 /
        (knots.getD (i + degree + 1) 0 - knots.getD (i + 1) 0) *
        second.getD (i + 1) 0 +
      (2 * ((-1) / (knots.getD (i + degree + 1) 0 - knots.getD (i + 1) 0))) *
        first.getD (i + 1) 0)

/-- Second derivatives of a fixed polynomial branch at the origin. -/
def branchSecondDerivatives (knots : List ℚ) (cell : ℕ) : ℕ → List ℚ
  | 0 => List.replicate (knots.length - 1) 0
  | degree + 1 => nextSecondDerivatives knots (degree + 1)
      (branchDerivatives knots cell degree) (branchSecondDerivatives knots cell degree)

end CAS.Splines.RationalReplay
