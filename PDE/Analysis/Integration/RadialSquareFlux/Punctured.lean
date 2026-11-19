/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.RadialSquareFlux.Cutoff
public import PDE.Analysis.Integration.RadialSquareFlux.LocalGauss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Removing the centre cutoff in the radial square flux

For a punctured C¹ function the inverse-square integrability removes the centre
without any assumed pointwise limit there. The Sobolev specialization derives
this integrability from Hardy's inequality. Surface integrals use the angular
measure in `sphereIntegral`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.RadialSquareFlux

open MeasureTheory Metric Set Filter NormedSpace
open scoped Topology RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The exact flux of the cutoff field on the outer sphere. -/
theorem integral_divergence_cutoffField {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    {c : ℝ^n} {w : ℝ^n → ℝ} (hw : ∀ x ∈ closedBall c r, x ≠ c → ContDiffAt ℝ 1 w x) :
    (∫ x in ball c r, ∇· (cutoffField ε c w) x) =
      radialBump (ε / r) * sphereIntegral n (fun x ↦ w x ^ 2) c r := by
  have h := (gauss_of_contDiffAt_closedBall hr
    (fun x hx ↦ contDiffAt_cutoffField hε (hw x hx))).2
  rw [h, ← sphereIntegral_const_mul]
  apply sphereIntegral_congr_on_sphere hr
  intro x hx
  have hn : ‖x - c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hx
  simp only [cutoffField, NormedSpace.normalize, real_inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hn]
  field_simp

/-- Removing the centre cutoff requires inverse-square integrability, but no apex limit.
The H¹ version supplies both integrability hypotheses from the Sobolev graph. -/
theorem integral_radial_sq_eq_sphereIntegral_of_integrable
    {c : ℝ^n} {r : ℝ} (hr : 0 < r) {w : ℝ^n → ℝ}
    (hw : ∀ x ∈ closedBall c r, x ≠ c → ContDiffAt ℝ 1 w x)
    (hD : IntegrableOn (fun x ↦ ((n : ℝ) - 1) * w x ^ 2 / ‖x - c‖ +
      2 * w x * fderiv ℝ w x (normalize (x - c))) (ball c r))
    (hH : IntegrableOn (fun x ↦ w x ^ 2 / ‖x - c‖ ^ 2) (ball c r)) :
    (∫ x in ball c r, ((n : ℝ) - 1) * w x ^ 2 / ‖x - c‖ +
      2 * w x * fderiv ℝ w x (normalize (x - c))) =
      sphereIntegral n (fun x ↦ w x ^ 2) c r := by
  let : Nontrivial (ℝ^n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using (Fact.out : 0 < n))
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεle (j : ℕ) : ε j ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun j : ℕ ↦ (1 : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0))
  obtain ⟨C, hC, hCb⟩ := exists_bound_deriv_radialBump
  let D : ℝ^n → ℝ := fun x ↦ ((n : ℝ) - 1) * w x ^ 2 / ‖x - c‖ +
    2 * w x * fderiv ℝ w x (normalize (x - c))
  let H : ℝ^n → ℝ := fun x ↦ w x ^ 2 / ‖x - c‖ ^ 2
  let F : ℕ → ℝ^n → ℝ := fun j ↦ ∇· (cutoffField (ε j) c w)
  have hc : ∀ᵐ x ∂volume.restrict (ball c r), x ≠ c :=
    ae_restrict_of_ae (volume.ae_ne c)
  have hbound (j : ℕ) : ∀ᵐ x ∂volume.restrict (ball c r),
      ‖F j x‖ ≤ ‖D x‖ + C * H x := by
    filter_upwards [hc, ae_restrict_mem isOpen_ball.measurableSet] with x hx hxb
    have hH0 : 0 ≤ H x := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hb : ‖radialBump (ε j / ‖x - c‖)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg radialBump.nonneg]
      exact radialBump.le_one
    have he : ‖ε j * deriv radialBump (ε j / ‖x - c‖)‖ ≤ C := by
      rw [norm_mul, Real.norm_of_nonneg (hε j).le]
      calc
        ε j * ‖deriv radialBump (ε j / ‖x - c‖)‖ ≤ ε j * C :=
          mul_le_mul_of_nonneg_left (hCb _) (hε j).le
        _ ≤ C := mul_le_of_le_one_left hC (hεle j)
    change ‖∇· (cutoffField (ε j) c w) x‖ ≤ _
    rw [divergence_cutoffField hx
      ((hw x (ball_subset_closedBall hxb) hx).differentiableAt one_ne_zero)]
    change ‖radialBump (ε j / ‖x - c‖) * D x -
      (ε j * deriv radialBump (ε j / ‖x - c‖)) * H x‖ ≤ _
    calc
      _ ≤ ‖radialBump (ε j / ‖x - c‖) * D x‖ +
          ‖(ε j * deriv radialBump (ε j / ‖x - c‖)) * H x‖ := norm_sub_le _ _
      _ ≤ ‖D x‖ + C * H x := by
        rw [norm_mul, norm_mul, Real.norm_of_nonneg hH0]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hb)
          (mul_le_mul_of_nonneg_right he hH0)
  have hblim {s : ℝ} : Tendsto (fun j ↦ radialBump (ε j / s)) atTop (𝓝 1) := by
    have hb0 : radialBump 0 = 1 := radialBump.one_of_mem_closedBall (by simp [radialBump])
    simpa only [Function.comp_def, zero_div, hb0] using
      radialBump.continuous.continuousAt.tendsto.comp (hεlim.div_const s)
  have hlim : ∀ᵐ x ∂volume.restrict (ball c r), Tendsto (fun j ↦ F j x) atTop (𝓝 (D x)) := by
    filter_upwards [hc, ae_restrict_mem isOpen_ball.measurableSet] with x hx hxb
    have hdb := ((radialBump.contDiff (n := 1)).continuous_deriv (by simp)).continuousAt
      (x := 0 / ‖x - c‖)
    have hdlim := hdb.tendsto.comp (hεlim.div_const ‖x - c‖)
    have hz := ((hεlim.mul hdlim).mul_const (H x))
    have ht := ((hblim (s := ‖x - c‖)).mul_const (D x)).sub hz
    simpa only [F, divergence_cutoffField hx
      ((hw x (ball_subset_closedBall hxb) hx).differentiableAt one_ne_zero),
      D, H, Function.comp_def, one_mul, zero_mul, sub_zero] using ht
  have hint := tendsto_integral_of_dominated_convergence (fun x ↦ ‖D x‖ + C * H x)
    (fun j ↦ (gauss_of_contDiffAt_closedBall hr
      (fun x hx ↦ contDiffAt_cutoffField (hε j) (hw x hx))).1.aestronglyMeasurable)
    (hD.norm.add (hH.const_mul C)) hbound hlim
  have hsurface := (hblim (s := r)).mul_const (sphereIntegral n (fun x ↦ w x ^ 2) c r)
  have heq : (fun j ↦ ∫ x in ball c r, F j x) =
      fun j ↦ radialBump (ε j / r) * sphereIntegral n (fun x ↦ w x ^ 2) c r := by
    funext j
    exact integral_divergence_cutoffField (hε j) hr hw
  rw [← heq] at hsurface
  simpa only [one_mul] using tendsto_nhds_unique hint hsurface

end PDE.Analysis.RadialSquareFlux
