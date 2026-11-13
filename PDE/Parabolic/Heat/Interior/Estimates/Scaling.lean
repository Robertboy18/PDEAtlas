/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Estimates.UnitCylinder
public import PDE.Parabolic.Heat.Interior.Rescaling
import PDE.Analysis.MeasureTheory.AffineVolume.Integral

/-!
# Normalized derivative bounds on arbitrary heat cylinders

Classical jets survive parabolic pullback, and the exact Jacobian
converts the unit-cylinder estimate to the physical L1 norm. The smooth
extension is still expressed in normalized coordinates, keeping the spatial
and temporal derivative factors separate.
-/

@[expose] public section

open PDE (laplacian)

open MeasureTheory Metric Set
open scoped ContDiff

namespace HeatEquation

/-- A classical heat field on any closed backward cylinder has a smooth
normalized extension with all derivatives controlled by the physical L1 norm.
The constant does not depend on the cylinder, domain or field. -/
theorem exists_normalized_extension_norm_iteratedFDeriv_le (n j : ℕ) :
    ∃ C > 0, ∀ (Ω : Set (ℝ^n)) (u : ℝ^n → ℝ → ℝ)
      (Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ)
      (Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ)
      (Dt : ℝ^n × ℝ → ℝ) (x : ℝ^n) (t r : ℝ),
      0 < r → IsOpen Ω → closedBall x r ⊆ Ω →
      ContinuousOn u.uncurry (Ω ×ˢ Icc (t - r ^ 2) t) →
      ContinuousOn Dx (Ω ×ˢ Icc (t - r ^ 2) t) →
      ContinuousOn Dxx (Ω ×ˢ Icc (t - r ^ 2) t) →
      ContinuousOn Dt (Ω ×ˢ Icc (t - r ^ 2) t) →
      (∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
        HasFDerivAt (fun y ↦ u y p.2) (Dx p) p.1) →
      (∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
        HasFDerivAt (fun y ↦ Dx (y, p.2)) (Dxx p) p.1) →
      (∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
        HasDerivWithinAt (u p.1) (Dt p) (Icc (t - r ^ 2) t) p.2) →
      (∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
        Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0) →
      ∃ v : ℝ^n × ℝ → ℝ, ContDiff ℝ ∞ v ∧
        (∀ (y : ℝ^n) (s : ℝ), ‖y‖ < 5 / 8 → -3 / 8 < s → s ≤ 0 →
          u (x + r • y) (t + r ^ 2 * s) = v (y, s)) ∧
        ∀ p, ‖iteratedFDeriv ℝ j v p‖ ≤
          C / r ^ (n + 2) * ∫ q in closedBall x r ×ˢ Icc (t - r ^ 2) t,
            ‖u q.1 q.2‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_unit_extension_norm_iteratedFDeriv_le n j
  refine ⟨C, hC, fun Ω u Dx Dxx Dt x t r hr hΩ hball
    hu hDx hDxx hDt hspace hhessian htime hheat ↦ ?_⟩
  let V := (fun y : ℝ^n ↦ x + r • y) ⁻¹' Ω
  let w := fun y s ↦ u (x + r • y) (t + r ^ 2 * s)
  obtain ⟨hw, Vx, Vxx, Vt, hVx, hVxx, hVt, hspace', hhessian', htime', hheat'⟩ :=
    exists_classical_jets_parabolic_pullback x t r hΩ hu hDx hDxx hDt
      hspace hhessian htime hheat
  have hV : IsOpen V := hΩ.preimage (by fun_prop)
  have hVball : closedBall (0 : ℝ^n) 1 ⊆ V := by
    intro y hy
    apply hball
    have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le, mul_one] using mul_le_mul_of_nonneg_left hy' hr.le
  obtain ⟨v, hv, heq, hjet⟩ :=
    hbound V w Vx Vxx Vt hV hVball hw hVx hVxx hVt hspace' hhessian' htime' hheat'
  refine ⟨v, hv, heq, fun p ↦ (hjet p).trans_eq ?_⟩
  rw [PDE.Analysis.setIntegral_closedBall_prod_Icc_space_time_dilation x t hr]
  rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hr.ne')]

end HeatEquation
