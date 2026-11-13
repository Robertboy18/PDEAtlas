/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Gradient
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lipschitz estimates from gradient bounds

Riesz representation identifies the norm of a real functional's derivative with
the norm of its gradient. The convex mean-value theorem therefore turns gradient
bounds into Lipschitz bounds on the functional. In particular, Lipschitz control of
the gradient on a ball bounds both the gradient and the energy there; no compactness
of that ball is needed.
-/

@[expose] public section

open scoped Gradient

open Metric Set

namespace PDE.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The mean-value estimate expressed in terms of the canonical Hilbert gradient. -/
theorem lipschitzOnWith_of_nnnorm_gradient_le {I : H → ℝ} {s : Set H} {K : NNReal}
    (hI : ∀ x ∈ s, DifferentiableAt ℝ I x)
    (hbound : ∀ x ∈ s, ‖∇ I x‖₊ ≤ K) (hs : Convex ℝ s) :
    LipschitzOnWith K I s := by
  apply hs.lipschitzOnWith_of_nnnorm_fderiv_le hI
  intro x hx
  simpa only [gradient, LinearIsometryEquiv.nnnorm_map] using hbound x hx

/-- A Lipschitz gradient on a ball gives a concrete energy Lipschitz constant on
the same ball. The value of the gradient at the center is the only additional term. -/
theorem lipschitzOnWith_of_gradient_lipschitzOn_closedBall {I : H → ℝ}
    (hI : Differentiable ℝ I) {z : H} {R : NNReal} {K : NNReal}
    (hG : LipschitzOnWith K (∇ I) (closedBall z R)) :
    LipschitzOnWith (‖∇ I z‖₊ + K * R) I (closedBall z R) := by
  apply lipschitzOnWith_of_nnnorm_gradient_le (fun x _ ↦ hI x) ?_ (convex_closedBall z R)
  intro x hx
  have hdist := hG.dist_le_mul x hx z (mem_closedBall_self R.coe_nonneg)
  have hnorm := norm_le_norm_add_norm_sub' (∇ I x) (∇ I z)
  have hx' : dist x z ≤ R := hx
  change ‖∇ I x‖ ≤ ‖∇ I z‖ + (K : ℝ) * R
  exact hnorm.trans (add_le_add (le_refl _)
    (by simpa only [dist_eq_norm] using
      hdist.trans (mul_le_mul_of_nonneg_left hx' K.coe_nonneg)))

end PDE.Analysis
