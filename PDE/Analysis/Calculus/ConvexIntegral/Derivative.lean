/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Differentiable.Supporting
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Fréchet derivatives of convex integral potentials

Two supporting hyperplanes bound the integral remainder by the product
of the `L²` increments of the field and its pointwise gradient. This
proves differentiability without interchanging a derivative and an
integral. The field may take values in any real inner-product space.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Asymptotics
open scoped Topology InnerProductSpace

namespace PDE.Analysis.Calculus

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Integration preserves the supporting-hyperplane inequality, with the tangent
represented by the `L²` inner product. -/
theorem integral_potential_tangent_le {φ : E → ℝ} {g : E → E}
    (hconvex : ConvexOn ℝ univ φ) (hderiv : ∀ x, HasFDerivAt φ (innerSL ℝ (g x)) x)
    (u v p : Lp E 2 μ) (hp : p =ᵐ[μ] fun x ↦ g (u x))
    (hu : Integrable (fun x ↦ φ (u x)) μ)
    (hv : Integrable (fun x ↦ φ (v x)) μ) :
    ⟪p, v - u⟫_ℝ ≤ (∫ x, φ (v x) ∂μ) - ∫ x, φ (u x) ∂μ := by
  rw [L2.inner_def, ← integral_sub hv hu]
  apply integral_mono_ae (L2.integrable_inner (𝕜 := ℝ) p (v - u)) (hv.sub hu)
  filter_upwards [hp, Lp.coeFn_sub v u] with x hx hsub
  simpa only [hx, hsub, Pi.sub_apply, innerSL_apply_apply] using
    PDE.Analysis.fderiv_apply_sub_le_sub_of_convex hconvex
      (hderiv (u x)) (v x) (mem_univ _) (mem_univ _)

/-- Two tangent inequalities bound the integral remainder by the product of
the argument increment and the gradient increment in `L²`. -/
theorem norm_integral_potential_remainder_le {φ : E → ℝ} {g : E → E}
    (hconvex : ConvexOn ℝ univ φ) (hderiv : ∀ x, HasFDerivAt φ (innerSL ℝ (g x)) x)
    (u v p q : Lp E 2 μ)
    (hp : p =ᵐ[μ] fun x ↦ g (u x)) (hq : q =ᵐ[μ] fun x ↦ g (v x))
    (hu : Integrable (fun x ↦ φ (u x)) μ)
    (hv : Integrable (fun x ↦ φ (v x)) μ) :
    ‖(∫ x, φ (v x) ∂μ) - (∫ x, φ (u x) ∂μ) - ⟪p, v - u⟫_ℝ‖ ≤
      ‖q - p‖ * ‖v - u‖ := by
  have hlo := integral_potential_tangent_le hconvex hderiv u v p hp hu hv
  have hhi := integral_potential_tangent_le hconvex hderiv v u q hq hv hu
  have hreverse : ⟪q, u - v⟫_ℝ = -⟪q, v - u⟫_ℝ := by
    rw [← neg_sub v u, inner_neg_right]
  rw [hreverse] at hhi
  rw [Real.norm_of_nonneg (sub_nonneg.mpr hlo)]
  calc
    (∫ x, φ (v x) ∂μ) - (∫ x, φ (u x) ∂μ) - ⟪p, v - u⟫_ℝ
        ≤ ⟪q - p, v - u⟫_ℝ := by rw [inner_sub_left]; linarith
    _ ≤ ‖q - p‖ * ‖v - u‖ := real_inner_le_norm _ _

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A continuous pointwise gradient in `L²` is the Fréchet derivative
of the signed integral potential. Integrability is stated separately,
so no normalization of the density or its gradient is imposed. -/
theorem hasFDerivAt_integral_convex_potential_of_integrable
    (J : V →L[ℝ] Lp E 2 μ) {φ : E → ℝ} {g : E → E}
    (hconvex : ConvexOn ℝ univ φ)
    (hderiv : ∀ x, HasFDerivAt φ (innerSL ℝ (g x)) x)
    (N : V → Lp E 2 μ) (hNae : ∀ v, N v =ᵐ[μ] fun x ↦ g (J v x))
    (hmem : ∀ w : V, Integrable (fun x ↦ φ (J w x)) μ)
    (v : V) (hN : ContinuousAt N v) :
    HasFDerivAt (fun w ↦ ∫ x, φ (J w x) ∂μ) ((innerSL ℝ (N v)).comp J) v := by
  have hrem :
      (fun w ↦ (∫ x, φ (J w x) ∂μ) - (∫ x, φ (J v x) ∂μ) -
        ⟪N v, J (w - v)⟫_ℝ) =o[𝓝 v] (fun w ↦ J (w - v)) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have hsmall : ∀ᶠ w in 𝓝 v, ‖N w - N v‖ ≤ ε := by
      have hlim : Tendsto (fun w ↦ ‖N w - N v‖) (𝓝 v) (𝓝 ‖N v - N v‖) :=
        (hN.sub (continuousAt_const (y := N v))).norm.tendsto
      simp only [sub_self, norm_zero] at hlim
      exact (hlim.eventually (Iio_mem_nhds hε)).mono fun w hw ↦ hw.le
    filter_upwards [hsmall] with w hw
    rw [map_sub]
    exact (norm_integral_potential_remainder_le hconvex hderiv
      (J v) (J w) (N v) (N w) (hNae v) (hNae w) (hmem v) (hmem w)).trans
        (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
  have hJbig : (fun w ↦ J (w - v)) =O[𝓝 v] (fun w ↦ w - v) := by
    simpa only [map_sub] using (J.hasFDerivAt (x := v)).isBigO_sub
  exact HasFDerivAt.of_isLittleO (hrem.trans_isBigO hJbig)

end PDE.Analysis.Calculus
