/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.LevelSeparation
import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
import PDE.Analysis.MeasureTheory.Lp.WeightedL2

/-!
# The energy form of level separation

For an H¹ function, Cauchy–Schwarz bounds the L¹ gradient in the intervening
strip by its energy times the strip measure. The W¹¹ level-separation
theorem applies after finite-measure exponent restriction; every coordinate
and level set is identified almost everywhere.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Squared level separation for H¹ functions, with the gradient
energy and measure of the intervening strip. The constant is uniform in the
function and both levels. -/
theorem exists_level_separation_sq_le_strip_energy (hconn : IsConnected Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : H¹(Ω)) (a b : ℝ), a ≤ b →
      (b - a) ^ 2 *
        (domainMeasure n Ω).real {x | wkpBaseCoordinateCLM U x ≤ a} ^ 2 *
        (domainMeasure n Ω).real {x | b ≤ wkpBaseCoordinateCLM U x} ^ 2 ≤
      C * (∑ i, ∫ x in {x | a < wkpBaseCoordinateCLM U x ∧ wkpBaseCoordinateCLM U x < b},
        wkpCoordinateCLM (singleDerivIndex n i) U x ^ 2 ∂domainMeasure n Ω) *
        (domainMeasure n Ω).real
          {x | a < wkpBaseCoordinateCLM U x ∧ wkpBaseCoordinateCLM U x < b} := by
  obtain ⟨P, hP, hsep⟩ := exists_level_separation_le_strip_gradient hconn
  refine ⟨P ^ 2 * n, mul_pos (sq_pos_of_pos hP) (Nat.cast_pos.mpr Fact.out), fun U a b hab ↦ ?_⟩
  let μ := domainMeasure n Ω
  let V : W^{1,1}(Ω) := lowerExponentOfFiniteMeasure (by norm_num : (1 : ℝ≥0∞) ≤ 2) U
  have hbase : (wkpBaseCoordinateCLM V : ℝ^n → ℝ) =ᵐ[μ] wkpBaseCoordinateCLM U :=
    lowerExponentOfFiniteMeasure_apply_ae (by norm_num) U (baseIndex n 1)
  have hderiv (i : Fin n) :
      (wkpCoordinateCLM (singleDerivIndex n i) V : ℝ^n → ℝ) =ᵐ[μ]
        wkpCoordinateCLM (singleDerivIndex n i) U :=
    lowerExponentOfFiniteMeasure_apply_ae (by norm_num) U (singleDerivIndex n i)
  let E := {x | a < wkpBaseCoordinateCLM U x ∧ wkpBaseCoordinateCLM U x < b}
  have hlow : μ.real {x | wkpBaseCoordinateCLM V x ≤ a} =
      μ.real {x | wkpBaseCoordinateCLM U x ≤ a} :=
    measureReal_congr (hbase.fun_comp (fun t : ℝ ↦ t ≤ a))
  have hhigh : μ.real {x | b ≤ wkpBaseCoordinateCLM V x} =
      μ.real {x | b ≤ wkpBaseCoordinateCLM U x} :=
    measureReal_congr (hbase.fun_comp (fun t : ℝ ↦ b ≤ t))
  have hstrip (i : Fin n) :
      (∫ x in {x | a < wkpBaseCoordinateCLM V x ∧ wkpBaseCoordinateCLM V x < b},
        ‖wkpCoordinateCLM (singleDerivIndex n i) V x‖ ∂μ) =
      ∫ x in E, ‖wkpCoordinateCLM (singleDerivIndex n i) U x‖ ∂μ :=
    (setIntegral_congr_set (hbase.fun_comp fun t : ℝ ↦ a < t ∧ t < b)).trans
      (integral_congr_ae (((hderiv i).filter_mono (ae_mono Measure.restrict_le_self)).fun_comp
        norm))
  have hs := hsep V a b hab
  change (b - a) * μ.real _ * μ.real _ ≤ P * ∑ i, ∫ x in _,
    ‖wkpCoordinateCLM (singleDerivIndex n i) V x‖ ∂μ at hs
  rw [hlow, hhigh] at hs
  simp_rw [hstrip] at hs
  have hcs (i : Fin n) :
      (∫ x in E, ‖wkpCoordinateCLM (singleDerivIndex n i) U x‖ ∂μ) ^ 2 ≤
        (∫ x in E, wkpCoordinateCLM (singleDerivIndex n i) U x ^ 2 ∂μ) * μ.real E := by
    have ht := integral_abs_mul_le_sqrt_integral_sq
      ((Lp.memLp (wkpCoordinateCLM (singleDerivIndex n i) U)).restrict E)
      (memLp_const (μ := μ.restrict E) (p := 2) (1 : ℝ))
    simp only [mul_one, one_pow, integral_const, smul_eq_mul, Measure.real,
      Measure.restrict_apply_univ] at ht
    have ht' := pow_le_pow_left₀ (integral_nonneg fun _ ↦ abs_nonneg _) ht 2
    rwa [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
      Real.sq_sqrt ENNReal.toReal_nonneg] at ht'
  have hsum := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun (i : Fin n) _ ↦ integral_nonneg
      (μ := μ.restrict E) fun x ↦ sq_nonneg (wkpCoordinateCLM (singleDerivIndex n i) U x))
    (fun (_i : Fin n) _ ↦ (measureReal_nonneg : 0 ≤ μ.real E))
    (fun i _ ↦ hcs i)
  have hs2 := pow_le_pow_left₀
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) measureReal_nonneg)
      measureReal_nonneg) hs 2
  simp only [mul_pow] at hs2
  have ht := hs2.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg P))
  simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_assoc,
    mul_left_comm (n : ℝ)] using ht

end SobolevSpace.GraphSpace
