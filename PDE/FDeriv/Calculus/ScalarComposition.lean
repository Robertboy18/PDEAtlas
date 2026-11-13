/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus

/-!
# Scalar composition and the Laplacian

The second-order chain rule gives
`Δ(g ∘ u) = g'(u) Δu + g''(u) ‖∇u‖²`.
Both regularity hypotheses are local to the point where the identity is evaluated.
The gradient is Mathlib's gradient; the Laplacian is LeanPDE's coordinate Laplacian.
-/

@[expose] public section

open PDE (laplacian)

open Filter
open scoped Gradient Topology

namespace PDE

/-- The gradient chain rule for a scalar function of a scalar Euclidean field. -/
theorem gradient_comp_real {n : ℕ} {g : ℝ → ℝ} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hg : DifferentiableAt ℝ g (u x)) (hu : DifferentiableAt ℝ u x) :
    ∇ (fun y ↦ g (u y)) x = deriv g (u x) • ∇ u x := by
  ext i
  simp only [gradient_apply_eq_partialDeriv, partialDeriv_comp_real i hg hu,
    PiLp.smul_apply, smul_eq_mul, mul_comm]

/-- The Laplacian chain rule for a scalar function of a scalar Euclidean field. -/
theorem laplacian_comp_real {n : ℕ} {g : ℝ → ℝ} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hg : ContDiffAt ℝ 2 g (u x)) (hu : ContDiffAt ℝ 2 u x) :
    laplacian (fun y ↦ g (u y)) x =
      deriv g (u x) * laplacian u x +
        deriv (deriv g) (u x) * ‖∇ u x‖ ^ 2 := by
  have hdu : DifferentiableAt ℝ u x := hu.differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (deriv g) (u x) :=
    (hg.derivWithin (m := 1) (by norm_num)).differentiableAt_one
  have hgNear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 g (u y) :=
    hdu.continuousAt.eventually (hg.eventually (by simp))
  have hsecond (i : Fin n) :
      (∂[i] (∂[i] (fun y ↦ g (u y)))) x =
        deriv g (u x) * (∂[i] (∂[i] u)) x +
          deriv (deriv g) (u x) * ((∂[i] u) x) ^ 2 := by
    have hfirst :
        (∂[i] (fun y ↦ g (u y))) =ᶠ[𝓝 x]
          fun y ↦ (∂[i] u) y * deriv g (u y) := by
      filter_upwards [hu.eventually (by simp), hgNear] with y huy hgy
      exact partialDeriv_comp_real i (hgy.differentiableAt (by norm_num))
        (huy.differentiableAt (by norm_num))
    have hcomp : DifferentiableAt ℝ (fun y ↦ deriv g (u y)) x :=
      hdg.comp x hdu
    rw [partialDeriv_congr_nhds i hfirst,
      partialDeriv_mul
        ((contDiffAt_partialDeriv 1 hu i).differentiableAt_one)
        hcomp,
      partialDeriv_comp_real i hdg hdu]
    ring
  simp only [laplacian, hsecond, Finset.sum_add_distrib, ← Finset.mul_sum,
    EuclideanSpace.real_norm_sq_eq, gradient_apply_eq_partialDeriv]

end PDE
