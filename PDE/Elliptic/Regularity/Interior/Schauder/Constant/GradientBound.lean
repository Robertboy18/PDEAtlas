/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Constant.HigherGradient
public import PDE.Elliptic.Regularity.Interior.DeGiorgi.LocalL2Bound
import PDE.Elliptic.Regularity.Coefficients.Restriction
import PDE.Elliptic.Regularity.Interior.Schauder.Energy.Ball

/-!
# Uniform interior gradient bound for constant coefficient solutions

The differentiated weak equation, Caccioppoli, and De Giorgi local boundedness
give an essential bound for every weak gradient coordinate on the half ball.
The coefficient matrix may be nonsymmetric. The constant is uniform over
matrices with fixed ellipticity and entrywise bounds.

Only H¹ solution data are used. This uniform estimate is the constant
coefficient input to the interior Schauder comparison argument.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open scoped NNReal Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- On normalized balls, the weak gradient of a constant coefficient solution
is essentially bounded by its L² norm. All constants depend only on dimension,
the Sobolev exponent, and the ellipticity bounds. -/
theorem exists_gradient_bound_of_constant_coefficients
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
        ∀ i, ∀ᵐ x ∂volume.restrict (ball (0 : ℝ^n) (1 / 2)),
          ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ≤
            C * Real.sqrt (∫ y in ball (0 : ℝ^n) 2, wkpBaseCoordinateCLM u y ^ 2) := by
  obtain ⟨E, hE, henergy⟩ := exists_ball_gradient_sq_le (n := n) hα hΛ
  obtain ⟨D, hD, hbound⟩ := exists_local_norm_le_sqrt_integral_sq
    (W := ball (0 : ℝ^n) (3 / 2)) isOpen_ball isBounded_ball hq2 hq hα hΛ
    (r := 1 / 2) (R := 1) (by norm_num) (by norm_num)
  refine ⟨D * Real.sqrt E, mul_pos hD (Real.sqrt_pos.mpr hE), ?_⟩
  intro A a hrep hAΛ hA u hu i
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
  have hI :
      (∫ y in ball (0 : ℝ^n) 1, wkpBaseCoordinateCLM (∂[i] W) y ^ 2) ≤
        E * ∫ y in ball (0 : ℝ^n) 2, wkpBaseCoordinateCLM u y ^ 2 := by
    have he := henergy _ A hAΛ hA u hu 0 1 2 (by norm_num) (by norm_num) subset_rfl
    norm_num only [sub_self, show (2 : ℝ) - 1 = 1 by norm_num, one_pow, div_one] at he
    calc
      _ = ∫ y in ball (0 : ℝ^n) 1,
          wkpCoordinateCLM (singleDerivIndex n i) u y ^ 2 :=
        integral_congr_ae ((hbaseAE.filter_mono (ae_mono (domainMeasure_le
          (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 3 / 2))))).fun_comp
            (fun t : ℝ ↦ t ^ 2))
      _ ≤ ∑ j, ∫ y in ball (0 : ℝ^n) 1,
          wkpCoordinateCLM (singleDerivIndex n j) u y ^ 2 :=
        Finset.single_le_sum (f := fun j ↦ ∫ y in ball (0 : ℝ^n) 1,
          wkpCoordinateCLM (singleDerivIndex n j) u y ^ 2)
          (fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) (Finset.mem_univ i)
      _ ≤ _ := he
  filter_upwards [hb, hbaseAE.filter_mono (ae_mono (domainMeasure_le
    (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2))))] with x hx heq
  rw [heq] at hx
  calc
    _ ≤ _ := hx
    _ ≤ D * Real.sqrt (E * ∫ y in ball (0 : ℝ^n) 2, wkpBaseCoordinateCLM u y ^ 2) := by gcongr
    _ = _ := by rw [Real.sqrt_mul hE.le, mul_assoc]

end SobolevSpace.GraphSpace
