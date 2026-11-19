/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Constant.Lipschitz
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Quadratic
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Normalization

/-!
# Quadratic oscillation decay for constant coefficient weak solutions

The uniform Lipschitz estimate gives quadratic mean-square oscillation decay
on normalized concentric balls. Subtracting an arbitrary constant preserves
the weak equation, so the outer energy may be centred at any value.

This is a quantitative estimate for the H¹ weak solution. The
comparison matrix may be nonsymmetric and the constant is uniform over its
ellipticity and entrywise bounds.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open PDE.Elliptic.Regularity.Campanato
open scoped NNReal Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Uniform quadratic oscillation decay for the constant coefficient equation
on normalized balls, with the original L² energy on the outer ball. -/
theorem exists_quadratic_oscillation_of_constant_coefficients
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
      ∀ (c r : ℝ), 0 < r → r ≤ 1 / 2 →
        (⨍ x in ball (0 : ℝ^n) r, ‖wkpBaseCoordinateCLM u x -
          ⨍ y in ball (0 : ℝ^n) r, wkpBaseCoordinateCLM u y‖ ^ 2) ≤
          C * r ^ 2 *
            ∫ x in ball (0 : ℝ^n) 2, ‖wkpBaseCoordinateCLM u x - c‖ ^ 2 := by
  obtain ⟨D, hD, hreg⟩ :=
    exists_uniform_lipschitz_representative_of_constant_coefficients hq2 hq hα hΛ
  refine ⟨D ^ 2, sq_pos_of_pos hD, ?_⟩
  intro A a hrep hAΛ hA u hu c r hr hrR
  have := isFiniteMeasure_domainMeasure_of_isBounded
    (isBounded_ball (x := (0 : ℝ^n)) (r := 2))
  let U : H¹(ball (0 : ℝ^n) 2) := u - wkpConstant c
  have hU : IsInteriorWeakDivergenceSolution A 0 U := by
    simpa only [one_smul] using hu.smul_sub_constant 1 c
  have hUbase : (wkpBaseCoordinateCLM U : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (ball (0 : ℝ^n) 2)] fun x ↦ wkpBaseCoordinateCLM u x - c := by
    simpa only [one_smul, one_mul] using wkpBaseCoordinateCLM_smul_sub_constant_ae u 1 c
  obtain ⟨v, _hv, hva, hLip⟩ := hreg A a hrep hAΛ hA U hU
  let I := ∫ x in ball (0 : ℝ^n) 2, wkpBaseCoordinateCLM U x ^ 2
  have hI : 0 ≤ I := integral_nonneg fun _ ↦ sq_nonneg _
  have hIE : I = ∫ x in ball (0 : ℝ^n) 2, ‖wkpBaseCoordinateCLM u x - c‖ ^ 2 :=
    integral_congr_ae (hUbase.mono fun x hx ↦ by simp only [hx, Real.norm_eq_abs, sq_abs])
  have hsub : ball (0 : ℝ^n) r ⊆ ball (0 : ℝ^n) 2 :=
    ball_subset_ball (hrR.trans (by norm_num))
  have hmem : MemLp (wkpBaseCoordinateCLM u) 2 (volume.restrict (ball (0 : ℝ^n) r)) :=
    (Lp.memLp _).mono_measure (domainMeasure_le hsub)
  have hpt : ∀ᵐ x ∂volume.restrict (ball (0 : ℝ^n) r),
      ‖wkpBaseCoordinateCLM u x - (v 0 + c)‖ ^ 2 ≤ (D * Real.sqrt I * r) ^ 2 := by
    filter_upwards [hva.filter_mono (ae_mono (domainMeasure_le hsub)),
      hUbase.filter_mono (ae_mono (domainMeasure_le hsub)),
      ae_restrict_mem measurableSet_ball] with x hx hux hxr
    rw [show wkpBaseCoordinateCLM u x - (v 0 + c) = v x - v 0 by rw [hx, hux]; ring]
    refine pow_le_pow_left₀ (norm_nonneg _) ((hLip x (ball_subset_ball hrR hxr) 0
      (mem_ball_self (by norm_num))).trans ?_) 2
    gcongr
    simpa only [sub_zero, mem_ball_zero_iff] using (mem_ball_zero_iff.mp hxr).le
  have hvol := ENNReal.toReal_pos
    (measure_ball_pos volume (0 : ℝ^n) hr).ne' measure_ball_lt_top.ne
  calc
    _ ≤ ⨍ x in ball (0 : ℝ^n) r, ‖wkpBaseCoordinateCLM u x - (v 0 + c)‖ ^ 2 :=
      setAverage_norm_sub_average_sq_le hmem (v 0 + c)
    _ ≤ (D * Real.sqrt I * r) ^ 2 := by
      have : IsFiniteMeasure (volume.restrict (ball (0 : ℝ^n) r)) :=
        isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
      rw [setAverage_eq, smul_eq_mul]
      calc
        _ ≤ (volume.real (ball (0 : ℝ^n) r))⁻¹ *
            ∫ _x in ball (0 : ℝ^n) r, (D * Real.sqrt I * r) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (integral_mono_ae ((hmem.sub (memLp_const _)).norm.integrable_sq)
              (integrable_const _) hpt) (inv_nonneg.mpr hvol.le)
        _ = _ := by simp only [integral_const, Measure.restrict_apply_univ,
          measureReal_def, smul_eq_mul]; field_simp
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hI, hIE]; ring

end SobolevSpace.GraphSpace
