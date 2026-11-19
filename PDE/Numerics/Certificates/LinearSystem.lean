/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.LinearAlgebra.DiagonalDominanceBounds

/-!
# Integer certificates for linear systems

Candidate data can use any finite index type and a common positive denominator.
The numerical checker supplies integer row bounds. Exact decoding of the residual
and the dominance margins then gives an error bound against any exact solution.
No mesh, equation, floating-point format, or method of computing the candidate is fixed.
-/

@[expose] public section

namespace CAS.Numerics

/-- Interpret integer data at a common scale, without restricting their index type. -/
noncomputable def rationalVector {ι : Type*} (D : ℕ) (v : ι → ℤ) : ι → ℝ :=
  fun i ↦ (v i : ℝ) / D

/-- A checked integer row budget decodes to a real residual budget after positive scaling. -/
theorem residual_bound_of_integer {D B : ℕ} (hD : 0 < D)
    (numerator margin : ℤ) {scale residual : ℝ} (hscale : 0 < scale)
    (hdecode : residual = (numerator : ℝ) / D / scale)
    (hrow : |numerator| ≤ margin * B) :
    ‖residual‖ ≤ ((margin : ℝ) / scale) * ((B : ℝ) / D) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hcast : |(numerator : ℝ)| ≤ (margin : ℝ) * B := by exact_mod_cast hrow
  rw [hdecode, Real.norm_eq_abs, abs_div, abs_div, abs_of_pos hDreal,
    abs_of_pos hscale]
  calc
    |(numerator : ℝ)| / D / scale ≤ ((margin : ℝ) * B) / D / scale :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hcast hDreal.le) hscale.le
    _ = ((margin : ℝ) / scale) * ((B : ℝ) / D) := by ring

/-- Integer residual checks certify the error of a candidate for any finite real system.
The decoding hypotheses connect the computable rows to the analytic matrix and its margins. -/
theorem norm_sub_le_of_integer_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (margin : ι → ℝ)
    (b exact approximate : ι → ℝ) (hexact : A.mulVec exact = b)
    (D B : ℕ) (hD : 0 < D) (numerator integerMargin : ι → ℤ) (scale : ι → ℝ)
    (hscale : ∀ i, 0 < scale i) (hpositive : ∀ i, 0 < margin i)
    (hmargin : ∀ i, margin i ≤ ‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖)
    (hmarginDecode : ∀ i, margin i = (integerMargin i : ℝ) / scale i)
    (hdecode : ∀ i, A.mulVec approximate i - b i = (numerator i : ℝ) / D / scale i)
    (hrows : ∀ i, |numerator i| ≤ integerMargin i * B) :
    ‖approximate - exact‖ ≤ (B : ℝ) / D := by
  apply PDE.Analysis.norm_sub_le_of_row_residual_bounds A margin ((B : ℝ) / D)
    (by positivity) hpositive hmargin b exact approximate hexact
  intro i
  rw [hmarginDecode i]
  exact residual_bound_of_integer hD (numerator i) (integerMargin i)
    (hscale i) (hdecode i) (hrows i)

end CAS.Numerics
