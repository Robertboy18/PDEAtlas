/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Constant.GradientBound
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Bounds
import PDE.Elliptic.Regularity.Coefficients.Restriction

/-!
# Mean gradient energy for constant coefficient solutions

Applying De Giorgi local boundedness to the differentiated weak equation
bounds each gradient coordinate by its own outer L² energy. Consequently its
mean energy stays uniformly bounded as the interior radius decreases. This
is the volume-order energy decay used in the coefficient perturbation argument.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open PDE.Elliptic.Regularity.Campanato
open scoped NNReal Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Uniform control of the mean gradient energy on all small normalized balls.
The input is the H¹ solution, and interior H² is derived. -/
theorem exists_gradient_mean_energy_of_constant_coefficients
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) 2))
        (a : Fin n → Fin n → ℝ),
        (∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball (0 : ℝ^n) 2)]
          fun _ ↦ a i j) →
        (∀ i j, ‖A i j‖ ≤ Λ) → AEUniformlyElliptic A α →
      ∀ (u : H¹(ball (0 : ℝ^n) 2)), IsInteriorWeakDivergenceSolution A 0 u →
      ∀ (i : Fin n) (r : ℝ), 0 < r → r ≤ 1 / 2 →
        (⨍ x in ball (0 : ℝ^n) r,
          ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2) ≤
        C * ⨍ x in ball (0 : ℝ^n) 2,
          ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := exists_local_norm_le_sqrt_integral_sq
    (W := ball (0 : ℝ^n) (3 / 2)) isOpen_ball isBounded_ball hq2 hq hα hΛ
    (r := 1 / 2) (R := 1) (by norm_num) (by norm_num)
  have hvol : 0 < volume.real (ball (0 : ℝ^n) 2) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : ℝ^n) (by norm_num)).ne'
      measure_ball_lt_top.ne
  refine ⟨D ^ 2 * volume.real (ball (0 : ℝ^n) 2), by positivity, ?_⟩
  intro A a hrep hAΛ hA u hu i r hr hrR
  have hsub : closure (ball (0 : ℝ^n) (3 / 2)) ⊆ ball (0 : ℝ^n) 2 :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num))
  obtain ⟨W, hW, hlinear⟩ := exists_interior_gradient_solutions_of_constant_coefficients
    A a hrep hA u hu isOpen_ball isBounded_ball.isCompact_closure hsub
  let B (j k : Fin n) : DerivLp n ∞ (ball (0 : ℝ^n) (3 / 2)) :=
    restrictDerivLp (subset_closure.trans hsub) (A j k)
  have hb := hbound B
    (fun j k ↦ (norm_restrictDerivLp_le (subset_closure.trans hsub) (A j k)).trans
      (hAΛ j k)) (hA.restrict (subset_closure.trans hsub)) (∂[i] W) (hlinear i) 0
        (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 3 / 2))
  have hbase : wkpBaseCoordinateCLM (∂[i] W) =
      wkpCoordinateCLM (singleDerivIndex n i)
        (lowerOrderCLM (by omega : 1 ≤ 2) W) := by
    simp only [wkpBaseCoordinateCLM_apply, partialDerivCLM, derivativeWordCLM_apply,
      derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_singleDerivIndex]
    rfl
  have hbaseAE : (wkpBaseCoordinateCLM (∂[i] W) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (ball (0 : ℝ^n) (3 / 2))]
        wkpCoordinateCLM (singleDerivIndex n i) u := by
    rw [hbase, hW]
    exact restrictCLM_apply_ae isOpen_ball.measurableSet
      (subset_closure.trans hsub) u (singleDerivIndex n i)
  let I := ∫ y in ball (0 : ℝ^n) 2, ‖wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2
  have hI :
      (∫ y in ball (0 : ℝ^n) 1, wkpBaseCoordinateCLM (∂[i] W) y ^ 2) ≤ I := by
    calc
      _ = ∫ y in ball (0 : ℝ^n) 1,
          ‖wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2 :=
        integral_congr_ae ((hbaseAE.filter_mono (ae_mono (domainMeasure_le (ball_subset_ball
          (by norm_num : (1 : ℝ) ≤ 3 / 2))))).mono fun y hy ↦ by simp only [hy, sq_abs,
            Real.norm_eq_abs])
      _ ≤ I := setIntegral_mono_set (Lp.memLp _).norm.integrable_sq
        (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
        (Filter.Eventually.of_forall (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)))
  have hpt : ∀ᵐ x ∂volume.restrict (ball (0 : ℝ^n) r),
      ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2 ≤ D ^ 2 * I := by
    filter_upwards [hb.filter_mono (ae_mono (domainMeasure_le (ball_subset_ball hrR))),
      hbaseAE.filter_mono (ae_mono (domainMeasure_le
        (ball_subset_ball (hrR.trans (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)))))]
      with x hx heq
    rw [heq] at hx
    have h := pow_le_pow_left₀ (norm_nonneg _) hx 2
    rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)] at h
    exact h.trans (by gcongr)
  calc
    _ ≤ D ^ 2 * I := setAverage_le_of_ae_bound
      (measure_ball_pos volume (0 : ℝ^n) hr).ne' measure_ball_lt_top.ne
      (((Lp.memLp (wkpCoordinateCLM (singleDerivIndex n i) u)).mono_measure
        (domainMeasure_le (ball_subset_ball (hrR.trans (by norm_num))))).norm.integrable_sq) hpt
    _ = _ := by
      have : IsFiniteMeasure (volume.restrict (ball (0 : ℝ^n) 2)) :=
        isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
      rw [mul_assoc]
      congr 1
      simpa only [measureReal_restrict_apply_univ, smul_eq_mul] using
        (measure_smul_average (μ := volume.restrict (ball (0 : ℝ^n) 2))
          (f := fun x ↦ ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2)).symm

end SobolevSpace.GraphSpace
