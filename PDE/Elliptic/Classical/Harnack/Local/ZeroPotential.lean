/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harnack.Local.UpperBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Local Harnack comparison with zero potential

The upper bound is applied to `(u + ε) / (u(y) + ε)`. The added positive
constant preserves the zero-potential equation. Letting `ε` decrease to zero
includes solutions that vanish; positivity of the original solution is never
required.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum BoxIntegral Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Uniform Harnack comparison for nonnegative solutions on the half unit ball. -/
theorem exists_unit_harnack_comparison
    (hn : 0 < n) {α τ B : ℝ} (hα : 0 < α) (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n),
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), (a x).PosSemidef) →
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), ∀ v : ℝ^n,
          α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫) →
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), (a x).trace ≤ τ) →
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), ‖b x‖ ≤ B) →
        ∀ u : ℝ^n → ℝ,
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), ContDiffAt ℝ 2 u x) →
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), 0 ≤ u x) →
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)),
          matrixOperator a b (fun _ ↦ 0) u x = 0) →
        ∀ x ∈ closedBall (0 : ℝ^n) (1 / 2),
        ∀ y ∈ closedBall (0 : ℝ^n) (1 / 2), u x ≤ C * u y := by
  obtain ⟨C, hC, hbound⟩ := exists_local_upper_bound hn hα hB
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro a b ha hell htrace hdrift u hreg hnonneg hsol x hx y hy
  have hyunit : y ∈ ball (0 : ℝ^n) 1 := closedBall_subset_ball (by norm_num) hy
  have hyambient : y ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)) :=
    ball_subset_ball (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) hyunit
  have hycube : WithLp.ofLp y ∈ (centeredUnitBox n).Icc := by
    apply Box.coe_subset_Icc
    have h := ball_euclideanBoxCenter_subset (centeredUnitBox n)
      (r := 1) (fun _ ↦ by norm_num [centeredUnitBox])
    rw [euclideanBoxCenter_centeredUnitBox] at h
    exact h hyunit
  have hcompare : u x ≤ C * u y := by
    refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    let ε := δ / (C + 1)
    have hε : 0 < ε := div_pos hδ (by positivity)
    have hden : 0 < u y + ε := add_pos_of_nonneg_of_pos (hnonneg y hyambient) hε
    let v := fun z ↦ (u y + ε)⁻¹ * (u z + ε)
    have hvreg : ∀ z ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), ContDiffAt ℝ 2 v z :=
      fun z hz ↦ contDiffAt_const.mul ((hreg z hz).add contDiffAt_const)
    have hvnn : ∀ z ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), 0 ≤ v z :=
      fun z hz ↦ mul_nonneg (inv_nonneg.mpr hden.le) (add_nonneg (hnonneg z hz) hε.le)
    have hvsol : ∀ z ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)),
        matrixOperator a b (fun _ ↦ 0) v z = 0 := by
      intro z hz
      change matrixOperator a b (fun _ ↦ 0)
        (fun z ↦ (u y + ε)⁻¹ * (u z + ε)) z = 0
      rw [matrixOperator_const_mul a b (fun _ ↦ 0)
        (((hreg z hz).add contDiffAt_const).differentiableAt (by norm_num))]
      rw [show (fun z ↦ u z + ε) = fun z ↦ u z - -ε by simp only [sub_neg_eq_add],
        matrixOperator_sub a b (fun _ ↦ 0) (hreg z hz) contDiffAt_const,
        matrixOperator_const, hsol z hz]
      simp
    have hvy : v y = 1 := inv_mul_cancel₀ hden.ne'
    have h := hbound a b ha hell htrace hdrift v hvreg hvnn hvsol y hycube hvy.le x hx
    change (u y + ε)⁻¹ * (u x + ε) ≤ C at h
    have h' := (inv_mul_le_iff₀ hden).mp h
    have hεδ : C * ε ≤ δ := by
      dsimp [ε]
      rw [← mul_div_assoc, div_le_iff₀ (show 0 < C + 1 by positivity)]
      nlinarith
    nlinarith
  exact hcompare.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (hnonneg y hyambient))

/-- The same comparison is uniform under translations and dilations of scale
at most one. The drift bound improves under this dilation. -/
theorem exists_scaled_harnack_comparison
    (hn : 0 < n) {α τ B : ℝ} (hα : 0 < α) (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
        (z : ℝ^n) (r : ℝ), 0 < r → r ≤ 1 →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 1))), (a x).PosSemidef) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 1))), ∀ v : ℝ^n,
          α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 1))), (a x).trace ≤ τ) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 1))), ‖b x‖ ≤ B) →
        ∀ u : ℝ^n → ℝ,
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 1))), ContDiffAt ℝ 2 u x) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 1))), 0 ≤ u x) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 1))),
          matrixOperator a b (fun _ ↦ 0) u x = 0) →
        ∀ x ∈ closedBall z (r / 2), ∀ y ∈ closedBall z (r / 2), u x ≤ C * u y := by
  obtain ⟨C, hC, hcompare⟩ := exists_unit_harnack_comparison hn hα hB
  refine ⟨C, hC, ?_⟩
  intro a b z r hr hr₁ ha hell htrace hdrift u hreg hnonneg hsol x hx y hy
  let Φ : ℝ^n → ℝ^n := fun p ↦ z + r • p
  have hΦ : ContDiff ℝ 2 Φ := contDiff_const.add (contDiff_id.const_smul r)
  have hdist (p : ℝ^n) : dist (Φ p) z = r * ‖p‖ := by
    simp [Φ, dist_eq_norm, norm_smul, abs_of_pos hr]
  have hmaps : MapsTo Φ (ball 0 (16 * ((n : ℝ) + 1))) (ball z (r * (16 * ((n : ℝ) + 1)))) :=
    fun p hp ↦ by
      rw [mem_ball, hdist]
      exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hp) hr
  let a' := fun p ↦ a (Φ p)
  let b' := fun p ↦ r • b (Φ p)
  have hpullsol : ∀ p ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)),
      matrixOperator a' b' (fun _ ↦ 0) (u ∘ Φ) p = 0 := by
    intro p hp
    have hscale := matrixOperator_comp_const_add_smul a b (fun _ ↦ 0) u z p r
    simp only [mul_zero] at hscale
    change matrixOperator a' b' (fun _ ↦ 0) (u ∘ Φ) p =
      r ^ 2 * matrixOperator a b (fun _ ↦ 0) u (Φ p) at hscale
    rw [hscale, hsol _ (hmaps hp), mul_zero]
  let Ψ := fun p : ℝ^n ↦ r⁻¹ • (p - z)
  have hinverse (p : ℝ^n) : Φ (Ψ p) = p := by simp [Φ, Ψ, smul_smul, hr.ne']
  have hsmall (p : ℝ^n) (hp : p ∈ closedBall z (r / 2)) :
      Ψ p ∈ closedBall (0 : ℝ^n) (1 / 2) := by
    rw [mem_closedBall, ← hinverse p, hdist] at hp
    exact mem_closedBall_zero_iff.2
      ((mul_le_mul_iff_right₀ hr).mp (by simpa only [div_eq_mul_inv, one_mul] using hp))
  have h := hcompare a' b'
    (fun p hp ↦ ha _ (hmaps hp)) (fun p hp ↦ hell _ (hmaps hp))
    (fun p hp ↦ htrace _ (hmaps hp))
    (fun p hp ↦ by
      change ‖r • b (Φ p)‖ ≤ B
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left (hdrift _ (hmaps hp)) hr.le).trans
        (mul_le_of_le_one_left hB hr₁))
    (u ∘ Φ) (fun p hp ↦ (hreg _ (hmaps hp)).comp p hΦ.contDiffAt)
    (fun p hp ↦ hnonneg _ (hmaps hp)) hpullsol (Ψ x) (hsmall x hx) (Ψ y) (hsmall y hy)
  simpa only [Function.comp_apply, hinverse] using h

end EllipticHarnack
