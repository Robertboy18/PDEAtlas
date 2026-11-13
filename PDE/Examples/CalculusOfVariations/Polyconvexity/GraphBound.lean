/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Polyconvexity.Determinant.Classical
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import CAS.ExactTactic

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A lower bound confined to the determinant graph

The convex lift `F(P,r) = |P|² + 2r - 7` has no lower bound on independent
matrix–scalar pairs. On the two-dimensional determinant graph it equals
`(P₀₀ + P₁₁)² + (P₀₁ - P₁₀)² - 7`, which is at least `-7`. This is the
lower-bound hypothesis of the signed-energy theorem.
-/

@[expose] public noncomputable section

open Set
open scoped Matrix.Norms.Elementwise

namespace PDE.Examples.Polyconvexity

/-- The polynomial `v₀² + v₁² + v₂² + v₃² + 2v₄ - 7` on `ℝ⁵`. -/
def graphBoundPolynomial (v : ℝ^5) : ℝ :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + 2 * v 4 - 7

/-- `graphBoundPolynomial` is `C¹`. -/
theorem graphBoundPolynomial_contDiff : ContDiff ℝ 1 graphBoundPolynomial := by
  cas

/-- The density `F(P, r) = ‖P‖² + 2r - 7`, written through the four entries of `P` and
the independent scalar `r`. -/
def graphBoundDensity
    (t : (ℝ^2 × ℝ^2) × (Matrix (Fin 2) (Fin 2) ℝ × ℝ)) : ℝ :=
  graphBoundPolynomial (WithLp.toLp 2
    ![t.2.1 0 0, t.2.1 0 1, t.2.1 1 0, t.2.1 1 1, t.2.2])

/-- The density is `C¹` in all variables. -/
theorem graphBoundDensity_contDiff : ContDiff ℝ 1 graphBoundDensity := by
  apply graphBoundPolynomial_contDiff.comp
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp <;> fun_prop

/-- The density is jointly convex in `(P, r)`. -/
theorem graphBoundDensity_convex (x s : ℝ^2) :
    ConvexOn ℝ univ (fun R : Matrix (Fin 2) (Fin 2) ℝ × ℝ ↦
      graphBoundDensity ((x, s), R)) := by
  have hc (i j : Fin 2) :
      ConvexOn ℝ univ (fun R : Matrix (Fin 2) (Fin 2) ℝ × ℝ ↦ R.1 i j ^ 2) := by
    let a : (Matrix (Fin 2) (Fin 2) ℝ × ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun R ↦ R.1 i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    convert (Even.convexOn_pow (𝕜 := ℝ) (show Even 2 from ⟨1, rfl⟩)).comp_linearMap a
      using 1
    · exact preimage_univ.symm
    · rfl
  have hr := ((LinearMap.snd ℝ (Matrix (Fin 2) (Fin 2) ℝ) ℝ).convexOn
    convex_univ).smul (by norm_num : 0 ≤ (2 : ℝ))
  change ConvexOn ℝ univ (fun R : Matrix (Fin 2) (Fin 2) ℝ × ℝ ↦
    R.1 0 0 ^ 2 + R.1 0 1 ^ 2 + R.1 1 0 ^ 2 + R.1 1 1 ^ 2 + 2 * R.2 - 7)
  convert (((((hc 0 0).add (hc 0 1)).add (hc 1 0)).add (hc 1 1)).add hr).add_const
    (-7) using 1
  funext R
  exact sub_eq_add_neg _ _

/-- On the determinant graph the density is a sum of squares minus seven. -/
theorem graphBoundDensity_graph (x s : ℝ^2) (P : Matrix (Fin 2) (Fin 2) ℝ) :
    graphBoundDensity ((x, s), (P, P.det)) =
      (P 0 0 + P 1 1) ^ 2 + (P 0 1 - P 1 0) ^ 2 - 7 := by
  change P 0 0 ^ 2 + P 0 1 ^ 2 + P 1 0 ^ 2 + P 1 1 ^ 2 + 2 * P.det - 7 = _
  rw [Matrix.det_fin_two]
  cas

/-- The lower bound `-7` holds on the whole determinant graph, singular matrices included. -/
theorem graphBoundDensity_lower (x s : ℝ^2) (P : Matrix (Fin 2) (Fin 2) ℝ) :
    -7 ≤ graphBoundDensity ((x, s), (P, P.det)) := by
  rw [graphBoundDensity_graph]
  have h₁ := sq_nonneg (P 0 0 + P 1 1)
  have h₂ := sq_nonneg (P 0 1 - P 1 0)
  linarith

/-- The density has no lower bound on independent pairs `(P, r)`. -/
theorem graphBoundDensity_no_global_lower_bound (b : ℝ) :
    ∃ r : ℝ, graphBoundDensity (((0 : ℝ^2), 0), ((0 : Matrix (Fin 2) (Fin 2) ℝ), r)) <
      b := by
  refine ⟨(b + 6) / 2, ?_⟩
  change 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 2 * ((b + 6) / 2) - 7 < b
  have h : (0 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 2 * ((b + 6) / 2) - 7 =
      b - 1 := by cas
  rw [h]
  linarith

end PDE.Examples.Polyconvexity
