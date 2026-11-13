/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Constant.GradientBound
import PDE.Elliptic.Regularity.Interior.DivergenceForm.Smooth
import PDE.Spaces.Sobolev.Calculus.Differentiation.Representative
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# Uniform Lipschitz estimate for the constant coefficient comparison

Smooth interior representatives exist for constant coefficient weak solutions.
The uniform weak gradient estimate bounds their classical derivatives by
uniqueness of weak derivatives. Continuity removes the exceptional null set,
and the mean value estimate gives a Lipschitz bound on the half ball.

The representative and its regularity are derived from H¹ solution data.
The Lipschitz constant is uniform over the prescribed coefficient class.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace PDE
open scoped NNReal Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Constant coefficient H¹ weak solutions have smooth representatives with a
uniform interior Lipschitz bound in terms of their L² norm. -/
theorem exists_uniform_lipschitz_representative_of_constant_coefficients
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
        ∃ v : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 2) ∧
          v =ᵐ[domainMeasure n (ball (0 : ℝ^n) 2)] wkpBaseCoordinateCLM u ∧
          ∀ x ∈ ball (0 : ℝ^n) (1 / 2), ∀ y ∈ ball (0 : ℝ^n) (1 / 2),
            ‖v x - v y‖ ≤
              C * Real.sqrt (∫ z in ball (0 : ℝ^n) 2, wkpBaseCoordinateCLM u z ^ 2) *
                ‖x - y‖ := by
  obtain ⟨D, hD, hbound⟩ := exists_gradient_bound_of_constant_coefficients hq2 hq hα hΛ
  refine ⟨(n : ℝ) * D, mul_pos (by exact_mod_cast Fact.out) hD, ?_⟩
  intro A a hrep hAΛ hA u hu
  have hfull : IsInteriorWeakFullDivergenceSolution A (fun _ ↦ 0) 0 0 u := by
    apply (isInteriorWeakFullDivergenceSolution_iff _ _ _ _ _).mpr
    simpa only [interiorLowerOrderOperator_apply, Lp.zero_smul,
      Finset.sum_const_zero, zero_add, sub_zero] using hu
  obtain ⟨v, hv, hva⟩ := exists_smoothRepresentative_of_interior_full_solution isOpen_ball
    A (fun _ ↦ 0) 0 0 (fun i j _ ↦ a i j) (fun _ _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0)
    (fun _ _ ↦ contDiffOn_const) (fun _ ↦ contDiffOn_const) contDiffOn_const contDiffOn_const
    hrep (fun _ ↦ Lp.coeFn_zero ℝ ∞ _) (Lp.coeFn_zero ℝ ∞ _) (Lp.coeFn_zero ℝ 2 _) hA u hfull
  let I : ℝ := ∫ z in ball (0 : ℝ^n) 2, wkpBaseCoordinateCLM u z ^ 2
  let M : ℝ := D * Real.sqrt I
  have hM : 0 ≤ M := mul_nonneg hD.le (Real.sqrt_nonneg I)
  have hv1 : ContDiffOn ℝ 1 v (ball (0 : ℝ^n) 2) := hv.of_le (by simp)
  have hsmall : ball (0 : ℝ^n) (1 / 2) ⊆ ball (0 : ℝ^n) 2 :=
    ball_subset_ball (by norm_num)
  have hpartial (i : Fin n) (x : ℝ^n) (hx : x ∈ ball (0 : ℝ^n) (1 / 2)) :
      ‖(∂[i] v) x‖ ≤ M := by
    have hca := wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn isOpen_ball u hv1 hva.symm i
    have hba := hbound A a hrep hAΛ hA u hu i
    have hae : (fun x ↦ max ‖(∂[i] v) x‖ M)
        =ᵐ[volume.restrict (ball (0 : ℝ^n) (1 / 2))] fun _ ↦ M := by
      filter_upwards [hba, hca.filter_mono (ae_mono (domainMeasure_le hsmall))]
        with y hy heq
      exact max_eq_right (by rw [← heq]; exact hy)
    have hc : ContinuousOn (∂[i] v) (ball (0 : ℝ^n) (1 / 2)) :=
      (hv1.continuousOn_partialDeriv i isOpen_ball).mono hsmall
    have heq := Measure.eqOn_open_of_ae_eq hae isOpen_ball
      (fun y hy ↦ Filter.Tendsto.max (hc.norm y hy) continuousWithinAt_const)
      continuousOn_const hx
    exact (le_max_left _ _).trans_eq heq
  have hgrad (x : ℝ^n) (hx : x ∈ ball (0 : ℝ^n) (1 / 2)) :
      ‖fderiv ℝ v x‖ ≤ n * M := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg n) hM)
    intro ξ
    rw [fderiv_apply_eq_sum_partialDeriv_mul]
    calc
      _ ≤ ∑ i, ‖(∂[i] v) x * ξ i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, M * ‖ξ‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul (hpartial i x hx) (PiLp.norm_apply_le ξ i) (norm_nonneg _) hM
      _ = _ := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
  refine ⟨v, hv, hva, ?_⟩
  intro x hx y hy
  have h := (convex_ball (0 : ℝ^n) (1 / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ (hv1.contDiffAt (isOpen_ball.mem_nhds (hsmall hz))).differentiableAt
      (by norm_num)) hgrad hy hx
  simpa only [M, mul_assoc] using h

end SobolevSpace.GraphSpace
