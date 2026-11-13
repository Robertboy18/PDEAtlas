/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ConvexIntegral.Derivative

/-!
# Integral potentials with an L² gradient

A differentiable convex scalar potential, normalized at its minimum zero,
is integrable whenever both its argument and its derivative belong to `L²`.
The two supporting-line inequalities also control its integral remainder
by the product of the `L²` increments of the argument and gradient.

Consequently a continuous Nemytskii gradient from a normed space into `L²`
is the actual Fréchet gradient of the integral potential. No differentiation
under an integral or finite-measure assumption is needed.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Asymptotics
open scoped Topology InnerProductSpace

namespace PDE.Analysis.Calculus

/-- The tangent line of a differentiable convex scalar function lies below its graph. -/
theorem tangent_le_sub_of_convex {φ g : ℝ → ℝ}
    (hconvex : ConvexOn ℝ univ φ) (hderiv : ∀ x, HasDerivAt φ (g x) x)
    (x y : ℝ) : g x * (y - x) ≤ φ y - φ x := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hconvex.le_slope_of_hasDerivAt (mem_univ x) (mem_univ y) hxy (hderiv x)
    rw [slope_def_field] at h
    exact (le_div_iff₀ (sub_pos.mpr hxy)).mp h
  · simp
  · have h := hconvex.slope_le_of_hasDerivAt (mem_univ y) (mem_univ x) hyx (hderiv x)
    rw [slope_def_field] at h
    have h' := (div_le_iff₀ (sub_pos.mpr hyx)).mp h
    nlinarith

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A convex potential normalized at its minimum is integrable if its argument
and gradient are in `L²`, on an arbitrary measure space. -/
theorem integrable_convex_potential_of_L2_gradient {φ g : ℝ → ℝ}
    (hconvex : ConvexOn ℝ univ φ) (hderiv : ∀ x, HasDerivAt φ (g x) x)
    (hφ0 : φ 0 = 0) (hg0 : g 0 = 0)
    (u p : Lp ℝ 2 μ) (hp : p =ᵐ[μ] fun x ↦ g (u x)) :
    Integrable (fun x ↦ φ (u x)) μ := by
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x ↦
    (hderiv x).continuousAt
  have hprod : Integrable (fun x ↦ p x * u x) μ := by
    simpa only [Real.inner_apply] using
      L2.integrable_inner (𝕜 := ℝ) p u
  apply hprod.norm.mono' (hφ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
  filter_upwards [hp] with x hx
  have hlow := tangent_le_sub_of_convex hconvex hderiv 0 (u x)
  have hupp := tangent_le_sub_of_convex hconvex hderiv (u x) 0
  simp only [hφ0, hg0, zero_mul, sub_zero, zero_sub] at hlow hupp
  rw [Real.norm_of_nonneg hlow, hx]
  exact (by nlinarith : φ (u x) ≤ g (u x) * u x).trans (le_abs_self _)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A continuous `L²` Nemytskii gradient differentiates its integral potential
on any normed space continuously mapped to `L²`. The potential is defined by
the scalar integrand; its derivative is a conclusion. -/
theorem hasFDerivAt_integral_convex_potential
    (J : V →L[ℝ] Lp ℝ 2 μ) {φ g : ℝ → ℝ}
    (hconvex : ConvexOn ℝ univ φ) (hderiv : ∀ x, HasDerivAt φ (g x) x)
    (hφ0 : φ 0 = 0) (hg0 : g 0 = 0)
    (N : V → Lp ℝ 2 μ) (hNae : ∀ v, N v =ᵐ[μ] fun x ↦ g (J v x))
    (v : V) (hN : ContinuousAt N v) :
    HasFDerivAt (fun w ↦ ∫ x, φ (J w x) ∂μ) ((innerSL ℝ (N v)).comp J) v := by
  have hmem (w : V) : Integrable (fun x ↦ φ (J w x)) μ :=
    integrable_convex_potential_of_L2_gradient hconvex hderiv hφ0 hg0
      (J w) (N w) (hNae w)
  apply hasFDerivAt_integral_convex_potential_of_integrable J hconvex
    (fun x ↦ ?_) N hNae hmem v hN
  convert (hderiv x).hasFDerivAt using 1
  ext
  simp only [innerSL_apply_apply, Real.inner_apply]
  exact mul_comm _ _

end PDE.Analysis.Calculus
