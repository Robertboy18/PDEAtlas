/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Polyconvexity.Determinant.Classical
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.InnerProductSpace.Calculus
import CAS.ExactTactic

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Concrete determinant densities

The weighted square couples position, value, and determinant and has quartic
growth in the matrix entries. Restricted to the determinant graph, it is not
convex in the gradient.
-/

@[expose] public noncomputable section

open Set PDE.CalculusOfVariations
open scoped Matrix.Norms.Elementwise

namespace PDE.Examples.Polyconvexity

/-- The explicit scalar polynomial underlying the position–value coupling. -/
def weightedSquare (v : ℝ^3) : ℝ :=
  (1 + v 0 ^ 2) * (v 2 - v 1) ^ 2 - 7

/-- `weightedSquare` is `C¹`. -/
theorem weightedSquare_contDiff : ContDiff ℝ 1 weightedSquare := by
  cas

/-- A density convex in the independent determinant, with arbitrary matrix argument. -/
def weightedDeterminantDensity
    (t : (ℝ^2 × ℝ^2) × (Matrix (Fin 2) (Fin 2) ℝ × ℝ)) : ℝ :=
  weightedSquare (WithLp.toLp 2 ![t.1.1 0, t.1.2 0, t.2.2])

/-- The scalar polynomial composed with the coordinate projections is `C¹`. -/
theorem weightedDeterminantDensity_contDiff : ContDiff ℝ 1 weightedDeterminantDensity := by
  apply weightedSquare_contDiff.comp
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp <;> fun_prop

/-- The density is jointly convex in the matrix and the determinant variable. -/
theorem weightedDeterminantDensity_convex (x s : ℝ^2) :
    ConvexOn ℝ univ (fun R : Matrix (Fin 2) (Fin 2) ℝ × ℝ ↦
      weightedDeterminantDensity ((x, s), R)) := by
  let a : (Matrix (Fin 2) (Fin 2) ℝ × ℝ) →ᵃ[ℝ] ℝ :=
    (LinearMap.snd ℝ (Matrix (Fin 2) (Fin 2) ℝ) ℝ).toAffineMap -
      AffineMap.const ℝ _ (s 0)
  have hs : ConvexOn ℝ univ (fun R : Matrix (Fin 2) (Fin 2) ℝ × ℝ ↦
      (R.2 - s 0) ^ 2) := by
    simpa only [a, Function.comp_def, preimage_univ, AffineMap.coe_sub, Pi.sub_apply,
      LinearMap.coe_toAffineMap, LinearMap.snd_apply, AffineMap.const_apply] using
      (Even.convexOn_pow (𝕜 := ℝ) (show Even 2 from ⟨1, rfl⟩)).comp_affineMap a
  change ConvexOn ℝ univ (fun R : Matrix (Fin 2) (Fin 2) ℝ × ℝ ↦
    (1 + x 0 ^ 2) * (R.2 - s 0) ^ 2 - 7)
  convert (hs.smul (by positivity : 0 ≤ 1 + x 0 ^ 2)).add_const (-7) using 1

/-- On the determinant graph the density is at least `-7`. -/
theorem weightedDeterminantDensity_lower (x s : ℝ^2) (P : Matrix (Fin 2) (Fin 2) ℝ) :
    -7 ≤ weightedDeterminantDensity ((x, s), (P, P.det)) := by
  change -7 ≤ (1 + x 0 ^ 2) * (P.det - s 0) ^ 2 - 7
  have h := mul_nonneg (by positivity : 0 ≤ 1 + x 0 ^ 2) (sq_nonneg (P.det - s 0))
  linarith

/-- At zero position and value, the graph density is `(det P)² - 7`. -/
theorem weightedDeterminantDensity_graph (a b c d : ℝ) :
    weightedDeterminantDensity ((0, 0), (!![a, b; c, d], (!![a, b; c, d]).det)) =
      (a * d - b * c) ^ 2 - 7 := by
  change (1 + (0 : ℝ) ^ 2) * ((!![a, b; c, d]).det - 0) ^ 2 - 7 = _
  rw [Matrix.det_fin_two]
  change (1 + (0 : ℝ) ^ 2) * ((a * d - b * c) - 0) ^ 2 - 7 = _
  cas

/-- The graph density is not convex in the gradient: at `diag(1/2, 1/2)`, the midpoint of
the singular matrices `diag(1, 0)` and `diag(0, 1)`, it exceeds the mean of the endpoint
values by `1/16`. -/
theorem weightedDeterminantDensity_midpoint_gap :
    weightedDeterminantDensity ((0, 0),
      (!![(1 / 2 : ℝ), 0; 0, 1 / 2], (!![(1 / 2 : ℝ), 0; 0, 1 / 2]).det)) -
      (weightedDeterminantDensity ((0, 0), (!![(1 : ℝ), 0; 0, 0], 0)) +
        weightedDeterminantDensity ((0, 0), (!![(0 : ℝ), 0; 0, 1], 0))) / 2 =
      1 / 16 := by
  rw [weightedDeterminantDensity_graph]
  change ((1 / 2 * (1 / 2 : ℝ) - 0 * 0) ^ 2 - 7) -
    (((1 + 0 ^ 2) * (0 - 0) ^ 2 - 7) + ((1 + 0 ^ 2) * (0 - 0) ^ 2 - 7)) / 2 = _
  cas

end PDE.Examples.Polyconvexity
