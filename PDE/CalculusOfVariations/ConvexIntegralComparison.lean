/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
import PDE.Analysis.Convex.Differentiable.Supporting
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Supporting derivatives compare extended convex energies

A convex density lies above its tangent at a field `u`. If the tangent
pairing against `v - u` is integrable and has nonnegative integral, the shifted
energy of `u` is at most that of `v`.

Both shifted densities are nonnegative, but their integrals may be infinite.
When the competitor has finite energy, the supporting inequality itself proves
integrability at `u`. No derivative of an integral functional or upper growth
bound is needed.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.CalculusOfVariations

/-- The integrated supporting inequality compares two possibly infinite convex
energies. Only the two evaluated densities must be measurable and nonnegative.
The derivative is required at `u(x)` alone, and its pairing with `v(x) - u(x)`
must be integrable with nonnegative integral.

If the competitor has finite energy, domination also gives integrability of the
shifted density at `u`. -/
theorem lintegral_le_of_convex_of_integral_derivative_sub_nonneg
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : α → E → ℝ} {D : α → E →L[ℝ] ℝ} {b : α → ℝ} {u v : α → E}
    (hconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x))
    (hderiv : ∀ᵐ x ∂μ, HasFDerivAt (F x) (D x) (u x))
    (hu_meas : AEStronglyMeasurable (fun x ↦ F x (u x) + b x) μ)
    (hv_meas : AEStronglyMeasurable (fun x ↦ F x (v x) + b x) μ)
    (hu_nonneg : ∀ᵐ x ∂μ, 0 ≤ F x (u x) + b x)
    (hv_nonneg : ∀ᵐ x ∂μ, 0 ≤ F x (v x) + b x)
    (hpair : Integrable (fun x ↦ D x (v x - u x)) μ)
    (hfirst : 0 ≤ ∫ x, D x (v x - u x) ∂μ) :
    (∫⁻ x, ENNReal.ofReal (F x (u x) + b x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (F x (v x) + b x) ∂μ := by
  by_cases hv_top : (∫⁻ x, ENNReal.ofReal (F x (v x) + b x) ∂μ) = ∞
  · rw [hv_top]
    exact le_top
  have hv_int : Integrable (fun x ↦ F x (v x) + b x) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hv_meas hv_nonneg).mp hv_top
  have hsupport : ∀ᵐ x ∂μ,
      F x (u x) + b x ≤ F x (v x) + b x - D x (v x - u x) := by
    filter_upwards [hconvex, hderiv] with x hc hd
    have htangent := PDE.Analysis.fderiv_apply_sub_le_sub_of_convex hc hd (v x)
      (mem_univ (u x)) (mem_univ (v x))
    linarith
  have hu_int : Integrable (fun x ↦ F x (u x) + b x) μ :=
    (hv_int.sub hpair).mono_nonneg hu_meas hu_nonneg hsupport
  have hle := integral_mono_ae hu_int (hv_int.sub hpair) hsupport
  simp only [Pi.sub_apply] at hle
  rw [integral_sub hv_int hpair] at hle
  rw [← ofReal_integral_eq_lintegral_ofReal hu_int hu_nonneg,
    ← ofReal_integral_eq_lintegral_ofReal hv_int hv_nonneg]
  exact ENNReal.ofReal_le_ofReal (hle.trans (sub_le_self _ hfirst))

end PDE.CalculusOfVariations
