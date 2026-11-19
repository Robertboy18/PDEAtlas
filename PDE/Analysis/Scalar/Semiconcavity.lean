/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Deriv
import CAS.ExactTactic

/-!
# Scalar consequences of semiconcavity

For a real-valued function `f`, a quadratic semiconcavity bound with constant
`C` is naturally expressed by concavity of

`x ↦ f x - (C / 2) * x ^ 2`.

We prove the corresponding one-sided derivative estimate, with no separate
semiconcavity structure.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Scalar

/-- If subtracting the quadratic `C x² / 2` makes `f` concave, then the
derivative of `f` is one-sided Lipschitz with constant `C`. -/
theorem deriv_sub_deriv_le_of_concaveOn_sub_quadratic
    {f : ℝ → ℝ} {C x y : ℝ}
    (hconcave :
      ConcaveOn ℝ Set.univ
        (fun z : ℝ ↦ f z - C / 2 * z ^ 2))
    (hxy : x ≤ y)
    (hx : DifferentiableAt ℝ f x)
    (hy : DifferentiableAt ℝ f y) :
    deriv f y - deriv f x ≤ C * (y - x) := by
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · simp
  let g : ℝ → ℝ := f - fun z ↦ C / 2 * z ^ 2
  have hquadratic (z : ℝ) :
      HasDerivAt (fun w : ℝ ↦ C / 2 * w ^ 2) (C * z) z := by
    cas
  have hgx : HasDerivAt g (deriv f x - C * x) x := by
    simpa only [g] using hx.hasDerivAt.sub (hquadratic x)
  have hgy : HasDerivAt g (deriv f y - C * y) y := by
    simpa only [g] using hy.hasDerivAt.sub (hquadratic y)
  have hgconcave : ConcaveOn ℝ Set.univ g := by
    have hfun :
        g = fun z : ℝ ↦ f z - C / 2 * z ^ 2 := by
      funext z
      rfl
    rw [hfun]
    exact hconcave
  have hderiv : deriv g y ≤ deriv g x :=
    (hgconcave.deriv_le_slope
      (Set.mem_univ x) (Set.mem_univ y) hxy hgy.differentiableAt).trans
      (hgconcave.slope_le_deriv
        (Set.mem_univ x) (Set.mem_univ y) hxy hgx.differentiableAt)
  rw [hgy.deriv, hgx.deriv] at hderiv
  linarith

end PDE.Analysis.Scalar
