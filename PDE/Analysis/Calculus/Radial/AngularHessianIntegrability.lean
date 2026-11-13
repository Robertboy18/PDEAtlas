/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.AngularHessian
public import PDE.Analysis.Calculus.Radial.AngularGradientIntegrability
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Hessian energy of centered radial-angular fields

A radial factor that vanishes at zero gives an inverse-radius Hessian bound
there. A bounded radial factor with decaying first two derivatives gives an
inverse-square Hessian bound at infinity. Both bounds are square integrable
in three dimensions, including when the field is not twice differentiable at zero.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Radial

open Metric NormedSpace MeasureTheory

private theorem exists_near_bounds_of_contDiff_two {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hf0 : f 0 = 0) :
    ∃ A ≥ 0, ∃ D ≥ 0, ∃ K ≥ 0, ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |f r| ≤ A * r ∧ |deriv f r| ≤ D ∧ |deriv (deriv f) r| ≤ K := by
  have hDf : ContDiff ℝ 1 (deriv f) := hf.deriv'
  obtain ⟨A, hA⟩ := hf.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0 : ℝ) 1) isCompact_Icc
  obtain ⟨D, hD, hDbound⟩ :=
    (isCompact_Icc.image hDf.continuous).isBounded.exists_pos_norm_le
  obtain ⟨K, hK, hKbound⟩ :=
    (isCompact_Icc.image hDf.continuous_deriv_one).isBounded.exists_pos_norm_le
  refine ⟨A, A.coe_nonneg, D, hD.le, K, hK.le, fun r hr ↦ ⟨?_, ?_, ?_⟩⟩
  · simpa only [Real.dist_eq, hf0, sub_zero, abs_of_nonneg hr.1] using
      hA.dist_le_mul r hr 0 (by constructor <;> norm_num)
  · simpa only [Real.norm_eq_abs] using hDbound _ (Set.mem_image_of_mem _ hr)
  · simpa only [Real.norm_eq_abs] using hKbound _ (Set.mem_image_of_mem _ hr)

/-- A centered radial factor with bounded value and decaying derivatives gives
inverse-radius near and inverse-square far bounds for the Cartesian Hessian. -/
theorem exists_near_far_hessian_bounds_radial_smul_normalize {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hf0 : f 0 = 0) {H : ℝ^3 → ℝ^3}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hfar : ∃ a ≥ 0, ∃ d ≥ 0, ∃ k ≥ 0, ∀ r : ℝ, 1 ≤ r →
      |f r| ≤ a ∧ |deriv f r| ≤ d / r ^ 2 ∧ |deriv (deriv f) r| ≤ k / r ^ 3) :
    ∃ C₀ ≥ 0, ∃ Cfar ≥ 0, ∀ x : ℝ^3, x ≠ 0 →
      (‖x‖ ≤ 1 →
        ‖fderiv ℝ (fderiv ℝ (fun y ↦ f ‖y‖ • H (NormedSpace.normalize y))) x‖ ≤
          C₀ / ‖x‖) ∧
      (1 ≤ ‖x‖ →
        ‖fderiv ℝ (fderiv ℝ (fun y ↦ f ‖y‖ • H (NormedSpace.normalize y))) x‖ ≤
          Cfar / ‖x‖ ^ 2) := by
  let : NormedSpace ℝ (ℝ^3 →L[ℝ] ℝ^3) := inferInstance
  let : NormedSpace ℝ (ℝ^3 →L[ℝ] ℝ^3 →L[ℝ] ℝ^3) := inferInstance
  obtain ⟨A, hA, hAbound⟩ := exists_norm_comp_normalize_le hH.continuous
  have hDH : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (by simp)
  obtain ⟨D, hD, hDbound⟩ := exists_norm_comp_normalize_le hDH.continuous
  obtain ⟨K, hK, hKbound⟩ := exists_norm_comp_normalize_le
    (hDH.continuous_fderiv (by norm_num))
  obtain ⟨a, ha, d, hd, k, hk, hnear⟩ := exists_near_bounds_of_contDiff_two hf hf0
  obtain ⟨b, hb, e, he, q, hq, htail⟩ := hfar
  let C₀ := a * (4 * K + 6 * D) + 4 * d * D + A * (k + 2 * d)
  let Cfar := b * (4 * K + 6 * D) + 4 * e * D + A * (q + 2 * e)
  refine ⟨C₀, by dsimp [C₀]; positivity, Cfar, by dsimp [Cfar]; positivity,
    fun x hx ↦ ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hH2 : ContDiffAt ℝ 2 H (NormedSpace.normalize x) :=
    (hH.of_le (by simp)).contDiffAt
  have hbound := norm_fderiv_fderiv_radial_smul_normalize_le hx hf.contDiffAt hH2
  refine ⟨?_, ?_⟩
  · intro hsmall
    obtain ⟨hvalue, hfirst, hsecond⟩ := hnear ‖x‖ ⟨hr.le, hsmall⟩
    refine hbound.trans ?_
    calc
      _ ≤ (a * ‖x‖) * (K * (2 / ‖x‖) ^ 2 + D * (6 / ‖x‖ ^ 2)) +
          2 * d * (D * (2 / ‖x‖)) + A * (k + d * (2 / ‖x‖)) := by
        gcongr
        · exact hKbound x
        · exact hDbound x
        · exact hDbound x
        · exact hAbound x
      _ = (a * (4 * K + 6 * D) + 4 * d * D + 2 * A * d) / ‖x‖ + A * k := by
        field_simp
        ring
      _ ≤ C₀ / ‖x‖ := by
        apply (le_div_iff₀ hr).mpr
        dsimp [C₀]
        have hAk : A * k * ‖x‖ ≤ A * k :=
          mul_le_of_le_one_right (mul_nonneg hA.le hk) hsmall
        field_simp
        nlinarith
  · intro hlarge
    obtain ⟨hvalue, hfirst, hsecond⟩ := htail ‖x‖ hlarge
    refine hbound.trans ?_
    calc
      _ ≤ b * (K * (2 / ‖x‖) ^ 2 + D * (6 / ‖x‖ ^ 2)) +
          2 * (e / ‖x‖ ^ 2) * (D * (2 / ‖x‖)) +
          A * (q / ‖x‖ ^ 3 + (e / ‖x‖ ^ 2) * (2 / ‖x‖)) := by
        gcongr
        · exact hKbound x
        · exact hDbound x
        · exact hDbound x
        · exact hAbound x
      _ = b * (4 * K + 6 * D) / ‖x‖ ^ 2 +
          (4 * e * D + A * (q + 2 * e)) / ‖x‖ ^ 3 := by field_simp; ring
      _ ≤ b * (4 * K + 6 * D) / ‖x‖ ^ 2 +
          (4 * e * D + A * (q + 2 * e)) / ‖x‖ ^ 2 := by
        apply add_le_add le_rfl
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        simpa only [mul_one, ← pow_succ] using
          mul_le_mul_of_nonneg_left hlarge (sq_nonneg ‖x‖)
      _ = Cfar / ‖x‖ ^ 2 := by dsimp [Cfar]; ring

/-- The radial-angular Hessian has finite whole-space energy under the actual
near-origin cancellation and scalar tail estimates. -/
theorem memLp_two_hessian_radial_smul_normalize {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hf0 : f 0 = 0) {H : ℝ^3 → ℝ^3}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hfar : ∃ a ≥ 0, ∃ d ≥ 0, ∃ k ≥ 0, ∀ r : ℝ, 1 ≤ r →
      |f r| ≤ a ∧ |deriv f r| ≤ d / r ^ 2 ∧ |deriv (deriv f) r| ≤ k / r ^ 3) :
    MemLp (fderiv ℝ (fderiv ℝ (fun y ↦ f ‖y‖ • H (NormedSpace.normalize y))))
      2 volume := by
  obtain ⟨A, _, C, hC, hbound⟩ :=
    exists_near_far_hessian_bounds_radial_smul_normalize hf hf0 hH hfar
  exact memLp_two_of_near_inv_radius_far_inv_sq
    (measurable_fderiv ℝ _).aestronglyMeasurable (by norm_num) (by norm_num) hC
    (fun x hx ↦ (hbound x hx).1) (fun x hx ↦ (hbound x hx).2)

end PDE.Analysis.Radial
